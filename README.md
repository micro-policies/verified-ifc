# verified-ifc
Coq formalization accompanying the paper: A Verified Information-Flow Architecture

Arthur Azevedo de Amorim, Nathan Collins, André DeHon, Delphine Demange, Cătălin Hriţcu, David Pichardie, Benjamin C. Pierce, Randy Pollack, and Andrew Tolmach. A Verified Information-Flow Architecture. In 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL), pages 165-178. ACM, January 2014.
http://www.crash-safe.org/node/29
- Extended version in Journal of Computer Security, 24(6), pages 689-734, Dec. 2016. 
http://content.iospress.com/articles/journal-of-computer-security/jcs15784
http://arxiv.org/abs/1509.06503

There are two subdirectories:

`/basic_machines`         corresponds to the basic model discussed in sections 3-10 of the paper.
`/extended_machines`      corresponds to the machine extensions discussed in section 11

Nearly everything developed in `/basic_machines` reappears in `/extended_machines`,
but sometimes in modified form.

We recommend that you start by exploring `/basic_machines`. Consult the `README`
and the `Main.v` file to get a top-level view of the results.

`/extended_machines` contain a longer `README` that is intended to help
guide you to the important differences in this developments.

The code is known to work with Coq 8.6.   Code for older versions of Coq may be available as github branches.
