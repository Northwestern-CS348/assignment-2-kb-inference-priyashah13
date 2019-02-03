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

        # check if fact_or_rule is an instance of Fact or Rule
        if isinstance(fact_or_rule, Fact) or isinstance(fact_or_rule, Rule):
            if fact_or_rule.asserted:
                if isinstance(fact_or_rule, Fact):
                    # must be an asserted fact
                    # get_fact for the fact from the KB
                    fact_or_rule = self._get_fact(fact_or_rule)
                    # if length of supported by array is zero, fact is not supported
                    # we can remove this fact
                    if len(fact_or_rule.supported_by) == 0:
                        # asserted but unsupported fact

                        # for every fact in the list of facts that given fact supports,
                        # for every fact rule pair that is supported by fact,
                        # find and remove fact from supported by list
                        for f in fact_or_rule.supports_facts:
                            for fr in f.supported_by:
                                if fact_or_rule in fr:
                                    f.supported_by.remove(fr)
                            # recursively call retract for all facts in supports_facts
                            self.kb_retract(f)

                        # for every rule in the list of rules that given fact supports,
                        # for every fact rule pair that is supported by rule,
                        # find and remove rule from supported by list
                        for r in fact_or_rule.supports_rules:
                            for rr in r.supported_by:
                                if fact_or_rule in rr:
                                    r.supported_by.remove(rr)
                            # recursively call retract for all rules in supports_rules
                            self.kb_retract(r)

                        # finally, remove the main fact from the knowledge base
                        self.facts.remove(fact_or_rule)

                    else:
                        # must be asserted and supported fact
                        # therefore, we do not remove from KB
                        fact_or_rule.asserted = False
                        return None
                else:
                    # must be asserted rule
                    # therefore, we cannot remove from KB
                    return None
            else:
                if isinstance(fact_or_rule, Fact):
                    fact_or_rule = self._get_fact(fact_or_rule)
                    if len(fact_or_rule.supported_by) == 0:
                        # must be un-asserted and un-supported fact,
                        # therefore, can be removed from KB
                        # same logic as above for removing from KB
                        for f in fact_or_rule.supports_facts:
                            for fr in f.supported_by:
                                if fact_or_rule in fr:
                                    f.supported_by.remove(fr)
                            self.kb_retract(f)

                        for r in fact_or_rule.supports_rules:
                            for rr in r.supported_by:
                                if fact_or_rule in rr:
                                    r.supported_by.remove(rr)
                            self.kb_retract(r)

                        self.facts.remove(fact_or_rule)

                    else:
                        # un-asserted, but supported fact, therefore, should not be removed
                        return None

                else:
                    # must be un-asserted rule
                    fact_or_rule = self._get_rule(fact_or_rule)
                    if len(fact_or_rule.supported_by) == 0:
                        # un-asserted and un-supported rule
                        # therefore, can be removed from KB
                        # same logic as above from removing from KB
                        for f in fact_or_rule.supports_facts:
                            for fr in f.supported_by:
                                if fact_or_rule in fr:
                                    f.supported_by.remove(fr)
                            self.kb_retract(f)

                        for r in fact_or_rule.supports_rules:
                            for rr in r.supported_by:
                                if fact_or_rule in rr:
                                    r.supported_by.remove(rr)
                            self.kb_retract(r)
                        self.rules.remove(fact_or_rule)

                    else:
                        # un-asserted, but supported rule, therefore, should not be removed
                        return None

        else:
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
        # get first element of rule.lhs and check for match
        rule_1 = rule.lhs[0]
        r_bind = match(fact.statement, rule_1)

        # if match found
        if r_bind:
            item = instantiate(rule.rhs, r_bind)
            # if rule.lhs has length 1, item must be an inferred fact
            if len(rule.lhs) == 1:
                # create new fact, mention which rule and fact pair support this new fact
                new_fact = Fact(item, supported_by=[[fact, rule]])
                # since fact is inferred, the asserted field must be marked as False
                new_fact.asserted = False
                # rule and fact supports the new_fact
                rule.supports_facts.append(new_fact)
                fact.supports_facts.append(new_fact)
                # finally add this new_fact to the knowledge base
                kb.kb_add(new_fact)

            else:
                # must be an inferred rule
                rules_except_1 = []
                # create an array of all the other rules in lhs except the 1st one
                for r in rule.lhs[1:]:
                    rules_except_1.append(instantiate(r, r_bind))
                # create new rules
                new_rule = Rule([rules_except_1, item], supported_by=[[fact, rule]])
                # since these are inferred, the asserted field must be marked as False
                new_rule.asserted = False
                # rule and fact supports new_rule
                rule.supports_rules.append(new_rule)
                fact.supports_rules.append(new_rule)
                # finally add this new_rule to the knowledge base
                kb.kb_add(new_rule)
        else:
            return None
