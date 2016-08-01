# Pfc -- forward chaining in Prolog

The Pfc system is a package that provides a forward reasoning capability to be used together with conventional Prolog programs.  The Pfc inference rules are Prolog terms which are asserted as clauses into the regular Prolog database.  When new facts or forward reasoning rules are added to the Prolog database (via a special predicate add/1, forward reasoning is triggered and additional facts that can be deduced via the application of the forward chaining rules are also added to the database.  A simple justification-based truth-maintenance system is provided as well as simple predicates to explore the resulting proof trees.

It was originally written circa 1988 at the Unisys Paoli Research Center.  For a description, see

Finin, Tim, Rich Fritzson and Dave Matuszek, [Adding Forward Chaining and Truth Maintenance to Prolog](http://ebiq.org/p/682), IEEE Conf. on Artificial Intelligence Applications, pp. 123-130, Miami, March 1989.

For more information, contact Tim Finin, finin@umbc.edu

