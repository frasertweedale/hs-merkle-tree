*merkle-tree*
-------------

The **Merkle tree** (also called a **hash tree**) is a binary tree
where each leaf is a cryptographic digest (of some arbitrary
content), and each combining node is labelled with the digest of the
two subtrees.  They are a useful building block for
cryptographically secure append-only logs, with applications
including blockchain, Certificate Transparency logs and Merkle
signature scheme.

*Inclusion proofs* for a particular leaf, and *consistency proofs*
that show that some tree is a superset of an earlier tree, can be
generated and verified efficiently in *O(log n)* time.

This library implements the Merkle tree construction described at
https://tools.ietf.org/html/draft-ietf-trans-rfc6962-bis-21.
