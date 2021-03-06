import read, copy
from util import *
from logical_classes import *
verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        if isinstance(fact_or_rule, Fact):
            if fact_or_rule in self.facts:
                # get the actual fact_or_rule from the KB
                fact_or_rule = self._get_fact(fact_or_rule)
                # use that fact to run the helper function
                self.kb_helper(fact_or_rule)

    # helper function to handle all the different cases of fact
    # and recursively call for facts and rules that need to be assessed as a result of removing initial fact
    def kb_helper(self, fact_or_rule):
        if isinstance(fact_or_rule, Fact):
            # must be fact
            if len(fact_or_rule.supported_by) == 0:
                # un-supported fact
                # remove regardless of asserted or not
                # for every fact in the supports facts list
                # for every fact, rule pair in the supported by list fro that fact
                # if the fact_or_rule is in this tuple [fact, rule],
                # remove this tuple from the supported by list
                for f in fact_or_rule.supports_facts:
                    for fr in f.supported_by:
                        if fact_or_rule in fr:
                            f.supported_by.remove(fr)
                    # recursively call helper function for all facts in supports_facts
                    self.kb_helper(f)

                # same logic as above, but for rules instead
                for r in fact_or_rule.supports_rules:
                    for rr in r.supported_by:
                        if fact_or_rule in rr:
                            r.supported_by.remove(rr)
                    # recursively call helper function for all rules in supports_rules
                    self.kb_helper(r)

                    # finally remove the fact_or_rule from the KB
                self.facts.remove(fact_or_rule)
            else:
                # supported fact
                if fact_or_rule.asserted:
                    # asserted and supported
                    fact_or_rule.asserted = False
                # else it is un-asserted, but supported fact
                # do nothing
        else:
            # must be rule
            # get kbrule from kb
            fact_or_rule = self._get_rule(fact_or_rule)
            if not fact_or_rule.asserted:
                # un-asserted rule
                if len(fact_or_rule.supported_by) == 0:
                    # un-supported
                    # use same logic as above to remove from KB
                    for f in fact_or_rule.supports_facts:
                        for fr in f.supported_by:
                            if fact_or_rule in fr:
                                f.supported_by.remove(fr)
                        # recursively call helper function for all facts in supports_facts
                        self.kb_helper(f)

                    for r in fact_or_rule.supports_rules:
                        for rr in r.supported_by:
                            if fact_or_rule in rr:
                                r.supported_by.remove(rr)
                        # recursively call helper function for all rules in supports_rules
                        self.kb_helper(r)

                        # finally remove the rule from the KB
                    self.rules.remove(fact_or_rule)
                else:
                    # un-asserted supported
                    # do nothing
                    return None
            else:
                # asserted rule
                # do nothing
                return None


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        if len(rule.lhs) > 0:
            # get first element of rule.lhs
            rule_1 = rule.lhs[0]
            # using this, check for match with fact.statement
            r_bind = match(fact.statement, rule_1)

            # if match found
            if r_bind:
                item = instantiate(rule.rhs, r_bind)
                # if rule.lhs has length 1, item must be an inferred fact
                if len(rule.lhs) == 1:
                    # must be fact
                    # create a new fact using the lhs generated item with supported by tuple of fact, rule
                    new_fact = Fact(item, [[fact, rule]])
                    # add this new fact to the kb
                    kb.kb_assert(new_fact)
                    # get the kb.fact from the kb
                    new_fact = kb._get_fact(new_fact)

                    # rule and fact supports the new_fact from the kb
                    rule.supports_facts.append(new_fact)
                    fact.supports_facts.append(new_fact)

                else:
                    # len(rule.lhs) is not 0 and 1 so must be greater than 1 since
                    # length cannot be negative
                    # must be rule
                    rules_except_1 = []
                    # create an array of all the other rules in lhs except the 1st one
                    for r in rule.lhs[1:]:
                        # instantiate all the remaining lhs items with the binding we found
                        rules_except_1.append(instantiate(r, r_bind))
                    # create new rules
                    new_rule = Rule([rules_except_1, item], [[fact, rule]])
                    # add this to the KB
                    kb.kb_assert(new_rule)
                    # get the actual kb.rule from the KB
                    new_rule = kb._get_rule(new_rule)

                    # rule and fact supports new_rule from the kb
                    rule.supports_rules.append(new_rule)
                    fact.supports_rules.append(new_rule)
        else:
            return None
