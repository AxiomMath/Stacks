module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.PseudoCoherentMap.Regular

/-!
# Perfect morphisms over a regular base

A morphism of schemes locally of finite type over a regular scheme is perfect.

## Main results

* `AlgebraicGeometry.perfect_of_isRegular`: Stacks 068B.

## Implementation notes

Regularity of the target is `AlgebraicGeometry.IsRegular`, which is Stacks 02IS: every point has
an affine open neighbourhood whose ring of sections is regular. Those neighbourhoods are an affine
open cover of the target, and the affine opens of the source inside the preimage of each of them
are an affine open cover of that preimage, so Stacks 0686 reduces the statement to its
ring-theoretic form: a finite-type ring map out of a regular ring is perfect, which is Stacks
067K as `RingHom.isPerfectRingMap_of_finiteType_of_isRegularRing`.

The ring of sections of a member of the cover need not have finite Krull dimension — a regular
Noetherian ring of infinite Krull dimension has infinite global dimension — so the source's extra
hypothesis in Stacks 067K is genuinely absent here. It is not needed: see the implementation
notes of `StacksFrontier.RingTheory.PseudoCoherentMap.Regular`, where the bound on the length of the
resolution is obtained from quasi-compactness of a prime spectrum rather than from a global
dimension bound.

## References

* [The Stacks Project, Lemma 37.61.5 (068B)](https://stacks.math.columbia.edu/tag/068B)
* [The Stacks Project, Definition 28.9.1 (02IS)](https://stacks.math.columbia.edu/tag/02IS)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Lemma 15.83.5 (067K)](https://stacks.math.columbia.edu/tag/067K)
-/

public section

open CategoryTheory StacksDraft.TorAmplitude
open scoped AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Stacks 068B.** A morphism of schemes locally of finite type over a regular scheme is
perfect. -/
@[stacks 068B]
public theorem perfect_of_isRegular {X S : Scheme.{u}} (f : X ⟶ S) (hS : IsRegular S)
    [LocallyOfFiniteType f] : Perfect f := by
  rw [perfect_iff_exists_affine_openCover]
  choose U hxU hU using hS
  refine ⟨S, fun s => (U s).1, ?_, fun s => (U s).2, fun s => ?_⟩
  · exact eq_top_iff.mpr fun s _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hxU s⟩
  · refine ⟨{V : X.affineOpens // V.1 ≤ f ⁻¹ᵁ (U s).1}, fun i => i.1.1,
      iSup_affineOpens_subtype_eq _, fun i => i.1.2, fun i => ?_⟩
    intro _ D
    let : Algebra Γ(S, (U s).1) Γ(X, i.1.1) :=
      (f.appLE _ _ ((le_iSup _ i).trans (iSup_affineOpens_subtype_eq _).le)).hom.toAlgebra
    let : IsRegularRing Γ(S, (U s).1) := hU s
    let : Algebra.FiniteType Γ(S, (U s).1) Γ(X, i.1.1) := f.finiteType_appLE (U s).2 i.1.2 _
    exact RingHom.isPerfectRingMap_of_finiteType_of_isRegularRing _ _
      D.tensor D.comparison D.isLeftDerived

end AlgebraicGeometry

end
