module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnconditionalPullbackData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineSystemPerfectColimit
public import StacksFrontier.CategoryTheory.PullbackData.LimitSystemColimShift

/-!
# The affine leaf of Stacks 09RI on the pullback datum the leaf is stated at

The affine leaf of Stacks 09RI — the colimit statement at the structure sheaf over an affine
algebraic space étale over the chosen stage — is stated for
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, whose composition comparison is the
universal comparison of the total left derived functor along a composite.  The machinery that
computes it over a directed system of affine *representables*,
`AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_unitObj` and
`isColim_of_isPerfect`, is stated for `(AlgebraicGeometry.Space.DerivedPullbackComposition`
`.canonical B S hS).toPullbackData`, whose composition comparison is the one of Stacks 0D6D.

This file crosses the two for the *shifted* colimit statement, which is the shape the dévissage
of the leaf consumes, and lands the structure-sheaf case of the leaf on the leaf's own datum.

The crossing itself is `AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomUnconditionalPullbackData.lean`,
which is unconditional.  Two steps were missing: that the datum the represented-affine machinery
uses *is* `AlgebraicGeometry.Space.canonicalPullbackData` — it is, on the nose — and that the
crossing passes through `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`, which
quantifies the statement over every shift of its first argument.

## Main results

* `AlgebraicGeometry.Space.derivedPullbackComposition_canonical_toPullbackData_eq`: the pullback
  pseudofunctor datum of `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` is
  `AlgebraicGeometry.Space.canonicalPullbackData`, by `rfl`.
* `AlgebraicGeometry.Space.shiftedIsColim_canonicalPullbackData_iff`: the colimit statement at
  every shift is the same statement for the two data.
* `AlgebraicGeometry.Space.RepresentedAffineSystem.shiftedIsColim_unitObj`: **the affine case of
  Stacks 09RI for the structure sheaf, at every shift of the first argument, for
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`** — the structure-sheaf case of the
  leaf, on the datum the leaf is stated at.
* `AlgebraicGeometry.Space.exists_iso_representedAffineDerivedAssociated_of_qcohDerived`: on an
  affine representable every object of `D_QCoh(𝒪_{h_U})` is the derived associated module of an
  object of `D(Γ(U))`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Lemma 75.13.6 (Tag 08H1)](https://stacks.math.columbia.edu/tag/08H1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The two spellings of the canonical pseudofunctoriality of derived pullback as a pullback
pseudofunctor datum agree, on the nose.**  `AlgebraicGeometry.Space.canonicalPullbackData` is
built from the same three fields of `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`
as `AlgebraicGeometry.Space.DerivedPullbackComposition.toPullbackData`, over the family
`AlgebraicGeometry.Space.derivedModules` in place of
`AlgebraicGeometry.Space.derivedToposModules`; those two families are definitionally equal.

This is what lets `AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff` be applied to the
statements proved for `DerivedPullbackComposition.canonical`. -/
theorem derivedPullbackComposition_canonical_toPullbackData_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (DerivedPullbackComposition.canonical B S hS).toPullbackData =
      canonicalPullbackData B S hS :=
  rfl

/-- **The colimit statement of Stacks 09RI at every shift of its first argument is the same
statement for the two pullback-pseudofunctor data of derived pullback.**  This is
`AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff` at each shift `A⟦n⟧`; the shift is
taken in the derived category of the base, which the two data share. -/
theorem shiftedIsColim_canonicalPullbackData_iff {b : AlgebraicSpaces B S hS} {J : Type w}
    [Preorder J] (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) b J)
    (A C : derivedModules B S hS b) :
    PullbackData.LimitSystem.ShiftedIsColim Sys (canonicalPullbackData B S hS) A C ↔
      PullbackData.LimitSystem.ShiftedIsColim Sys (smallEtaleDerivedPullbackData B S hS) A C :=
  forall_congr' fun n => isColim_canonicalPullbackData_iff Sys (A⟦n⟧) C

namespace RepresentedAffineSystem

variable {V₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
  {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
  (Sys : RepresentedAffineSystem V₀ J)

/-- **The affine case of Stacks 09RI for the structure sheaf, at every shift, on the datum the
leaf of the tag is stated at.**  Along a directed system of affine representables over `V₀` with
a cone whose rings of global functions form a filtered colimit, and for every `q`,

`Hom(Lk^*(𝒪⟦n⟧), Lk^*𝒪[q]) = colim_j Hom(Lk_j^*(𝒪⟦n⟧), Lk_j^*𝒪[q])` for every `n`,

the derived pullbacks being taken with `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`.

This is `AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_unitObj` — stated for
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` and at the structure sheaf in two
*degrees* — read across `AlgebraicGeometry.Space.shiftedIsColim_canonicalPullbackData_iff` and
`AlgebraicGeometry.Space.representedAffineUnitObjShiftIso`, which identifies the `n`-th shift of
the structure sheaf in degree `0` with the structure sheaf in degree `-n`. -/
theorem shiftedIsColim_unitObj (hring : Sys.IsRingColimit) (q : ℤ) :
    PullbackData.LimitSystem.ShiftedIsColim Sys.toLimitSystem
      (smallEtaleDerivedPullbackData B S hS) (representedAffineUnitObj B S hS V₀ 0)
      (representedAffineUnitObj B S hS V₀ q) := by
  refine (shiftedIsColim_canonicalPullbackData_iff Sys.toLimitSystem _ _).1 fun n => ?_
  exact (Sys.isColim_unitObj hring (-n) q).of_iso_fst
    (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
    (representedAffineUnitObjShiftIso V₀ n).symm

end RepresentedAffineSystem

section Qcoh

variable (B S hS) in
/-- **Every object of `D_QCoh(𝒪_{h_U})` on an affine representable is the derived associated
module of an object of `D(R)`**, `R = Γ(U, 𝒪)`: the counit `Φ(RΓ(E)) ⟶ E` of
`AlgebraicGeometry.Space.representedAffineDerivedAdjunction` is invertible there
(`AlgebraicGeometry.Space.isIso_representedAffineDerivedAdjunction_counit_app`), so `RΓ(E)` is
such an object.

The hypothesis is `AlgebraicGeometry.Space.QcohDerived`, which unfolds to the quasi-coherence of
every cohomology sheaf of `E`. -/
theorem exists_iso_representedAffineDerivedAssociated_of_qcohDerived
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E) :
    ∃ N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)),
      Nonempty ((representedAffineDerivedAssociated B S hS U).obj N ≅ E) :=
  ⟨(representedAffineDerivedSections B S hS U).obj E,
    ⟨@asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U).counit.app E)
      (isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hE)⟩⟩

end Qcoh

end AlgebraicGeometry.Space

end
