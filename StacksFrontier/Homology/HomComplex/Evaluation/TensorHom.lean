module

public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.ProjectiveComparison
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.RepresentativeDiagonal
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.BoundedTheta
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.BoundedBelowCase
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.PerfectAndCurrying

/-!
# Invertibility of the derived tensor--Hom diagonal

The canonical derived tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` over a commutative
ring is an isomorphism when `M` is perfect, when `K` is perfect, or when `M` is pseudo-coherent,
`L` is bounded below and `K` has Tor amplitude in `[a, ∞]` ([stacks 0ATK]). The proof is split
into `TensorHom.ProjectiveComparison` (derived Hom out of bounded-above projectives and chain-level
currying), `TensorHom.RepresentativeDiagonal` (the diagonal on representatives),
`TensorHom.BoundedTheta` (retracts, representatives and the bounded comparison),
`TensorHom.BoundedBelowCase` (the bounded-below case) and `TensorHom.PerfectAndCurrying` (the
perfect cases, the main theorem `Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal`
and the transposition of composition of derived internal Homs).
-/
