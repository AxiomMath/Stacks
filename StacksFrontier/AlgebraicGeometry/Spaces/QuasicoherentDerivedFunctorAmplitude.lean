module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
import StacksCore.Tactic.StacksAttribute

/-!
# A functor on the modules of an algebraic space and the truncations of a complex

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `F : Mod(𝒪_X) ⥤ Ab` be an
additive functor and let `(RF, α)` be a right derived functor of `F` on the unbounded derived
category `D(𝒪_X)`.  This file proves, for `E` in `D_QCoh(𝒪_X)`, the first assertion of
[Stacks, Tag 08F7] — that `H ^ i (RF (τ_{≤ a} E)) ⟶ H ^ i (RF E)` is an isomorphism for
`i ≤ a` — and the half of its third assertion that bounds `RF E` from below.

## Main results

* `AlgebraicGeometry.Space.isIso_homologyFunctor_map_rightDerived_truncLE`: assertion (1) of
  Tag 08F7.
* `AlgebraicGeometry.Space.isZero_homology_rightDerived_of_isZero_lt`: the `i < a` half of
  assertion (3) of Tag 08F7.

## What is not proved, and why

Tag 08F7 has a covering set of three assertions.  The two proved here are assertion (1) and the
lower half of assertion (3); the other two, assertion (2) and the upper bound `b + N - 1` of
assertion (3), rest on Tag 08F6, `E = R lim τ_{≥ -n} E` for `E` in `D_QCoh(𝒪_X)`.  That tag is
carried by `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower`, but with the higher
cohomology vanishing of a quasi-coherent module on an affine étale chart — Stacks 03DW, clause
(1) for `q > 0`, equivalently Descent, Proposition 03DX (2) transported along Cohomology of
Schemes, Lemma 01XB — as a named hypothesis, and that clause of 03DW is carried nowhere in this
repository; only its case `q = 0` is, as
`AlgebraicGeometry.Descent.hZeroBaseAssociatedModuleAddEquiv`.  The two remaining assertions are
therefore left unproved here rather than stated with a hypothesis the library cannot discharge.

Neither assertion proved here uses the source's hypotheses (2) and (3) on `F`, nor the integer
`N`, so neither appears as a binder: the source's own proof of assertion (1) is a citation of
Derived Categories, Lemma [Stacks, Tag 05TC], which has none of them, and the lower half of
assertion (3) is deduced from assertion (1) there.  This matches the scheme analogue of this
lemma, Tag 08D4, whose same two clauses are carried by
`AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι` and
`AlgebraicGeometry.isGE_rightDerivedFunctor_obj`.

## Implementation notes

`Mod(𝒪_X)` is `AlgebraicGeometry.Space.Modules`, the sheaves of modules on the small étale
ringed site of `X`, and quasi-coherence of the cohomology sheaves is
`SheafOfModules.IsQuasicoherentOnSite`, so that membership of `E` in `D_QCoh(𝒪_X)` is spelled as
in `AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, by a hypothesis on each cohomology
sheaf.  That hypothesis is retained although neither proof uses it, so that the statements are
the ones Tag 08F7 makes; this is the convention of the scheme analogue Tag 08D4.

`RF` is a right derived functor in Mathlib's sense, a left Kan extension of
`K(Mod(𝒪_X)) ⥤ D(Ab)` along the localization, so the statements hold for *any* right derived
functor and do not depend on a construction.  The three facts about it that the proofs use are
all library results for a Grothendieck abelian source: the structure map `α` is invertible at
every K-injective complex (`Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso` and
`Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective`, Stacks 070K), `RF` is
triangulated (`Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor`), and
`RF` preserves lower cohomological bounds
(`Stacks.SmallDerivedCategory.isGE_obj_of_isGE`, the content of Stacks 05TC
part (1)).

The two sheafification hypotheses, Grothendieck abelianness and enough injectives of the modules
are instance arguments for the same reason as in
`AlgebraicGeometry.Space.QuasicoherentDerivedLimits`: the library supplies them at module
universe `u` (`SheafOfModules.isGrothendieckAbelianU`, `SheafOfModules.enoughInjectivesU`) and
the statements are given at a free module universe `m`.

## References

* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u m g

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  [HasSheafify (smallEtaleRingedSite B S hS X hX).J AddCommGrpCat.{m}]
  [(smallEtaleRingedSite B S hS X hX).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [IsGrothendieckAbelian.{g} (Modules.{u, m} B S hS X hX)]
  [EnoughInjectives (Modules.{u, m} B S hS X hX)]
  (F : Modules.{u, m} B S hS X hX ⥤ AddCommGrpCat.{m}) [F.Additive]
  (RF : DerivedCategory (Modules.{u, m} B S hS X hX) ⥤ DerivedCategory AddCommGrpCat.{m})
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, m} B S hS X hX) (ComplexShape.up ℤ))]

omit [EnoughInjectives (Modules.{u, m} B S hS X hX)] in
include F α in
/-- The structure map of a right derived functor out of `K(Mod(𝒪_X))` is invertible at every
K-injective complex of `𝒪_X`-modules, the modules of an algebraic space being Grothendieck
abelian so that K-injective resolutions exist. -/
private theorem isIso_app_isKInjective (I : CochainComplex (Modules.{u, m} B S hS X hX) ℤ)
    (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, m} B S hS X hX)
      (ComplexShape.up ℤ)).obj I)) :=
  Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective F RF α
    Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso I hI

include F α in
/-- **Stacks 08F7, the `i < a` half of assertion (3).** Let `S` be a scheme, let `X` be an
algebraic space over `S`, let `F : Mod(𝒪_X) ⥤ Ab` be an additive functor and let `(RF, α)` be a
right derived functor of `F` on `D(𝒪_X)`.  Let `E` be an object of `D_QCoh(𝒪_X)` with
`H ^ j (E) = 0` for `j < a`.  Then `H ^ i (RF E) = 0` for `i < a`.

This is the half of assertion (3) that bounds `RF E` from below.  The source gets it from
assertion (1); here it is the left t-exactness of a right derived functor out of a Grothendieck
abelian category with enough injectives,
`Stacks.SmallDerivedCategory.isGE_obj_of_isGE`, which is Stacks 05TC part (1).

Neither the quasi-coherence of `E`, nor the source's hypotheses (2) and (3) on `F`, nor the
integer `N` is used: `N` governs only the upper bound `b + N - 1`, which is the other half of
assertion (3). -/
@[stacks 08F7 "the i < a half of assertion (3); the upper bound b + N - 1, where the integer N \
and the hypotheses (2), (3) on F enter, is not proved — it needs the clause q > 0 of Stacks \
03DW, which this repository does not carry"]
theorem isZero_homology_rightDerived_of_isZero_lt
    (E : DerivedCategory (Modules.{u, m} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (a : ℤ)
    (hE : ∀ j : ℤ, j < a → IsZero ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS X hX) j).obj E))
    (i : ℤ) (hi : i < a) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} i).obj (RF.obj E)) := by
  have _hqc := hqc
  have hGE : E.IsGE a := (DerivedCategory.isGE_iff E a).2 hE
  have : (RF.obj E).IsGE a :=
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE F RF α
      (isIso_app_isKInjective B S hS X hX F RF α) E a hGE
  exact (RF.obj E).isZero_of_isGE a i hi

include F α in
/-- **Stacks 08F7, assertion (1).** Let `S` be a scheme, let `X` be an algebraic space over `S`,
let `F : Mod(𝒪_X) ⥤ Ab` be an additive functor and let `(RF, α)` be a right derived functor of
`F` on `D(𝒪_X)`.  Then for every object `E` of `D_QCoh(𝒪_X)` and every `i ≤ a` the canonical
truncation map `τ_{≤ a} E ⟶ E` induces an isomorphism
`H ^ i (RF (τ_{≤ a} E)) ⟶ H ^ i (RF E)`.

The argument is the source's, which cites Derived Categories, Lemma [Stacks, Tag 05TC].  The
functor `RF` is triangulated, so it carries the canonical truncation triangle
`τ_{≤ a} E ⟶ E ⟶ τ_{≥ a + 1} E` to a distinguished triangle; its third vertex lies in degrees
`≥ a + 1` by left t-exactness of `RF`, so `H ^ i` and `H ^ (i - 1)` vanish on it for `i ≤ a`,
and the long exact homology sequence makes the first map invertible on `H ^ i`.

Neither the quasi-coherence of `E`, nor the source's hypotheses (2) and (3) on `F`, nor the
integer `N` is used — none of them occurs in Tag 05TC either. -/
@[stacks 08F7 "assertion (1), as the source proves it, by citing Derived Categories 05TC; the \
hypotheses (2), (3) on F and the integer N play no part in that assertion and are not binders"]
theorem isIso_homologyFunctor_map_rightDerived_truncLE
    (E : DerivedCategory (Modules.{u, m} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, m} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} i).map
      (RF.map ((DerivedCategory.TStructure.t.truncLEι a).app E))) := by
  have _hqc := hqc
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, m} B S hS X hX) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF α
  let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E)
  have ht : T ∈ distTriang (DerivedCategory AddCommGrpCat.{m}) :=
    RF.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E)
  have hg : T.obj₃.IsGE (a + 1) :=
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE F RF α
      (isIso_app_isKInjective B S hS X hX F RF α)
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E) (a + 1) inferInstance
  have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} i).obj T.obj₃) :=
    T.obj₃.isZero_of_isGE (a + 1) i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} (i - 1)).obj T.obj₃) :=
    T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} 0).homologySequence_epi_shift_map_mor₁_iff
      T ht i).2 (hz.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} 0).homologySequence_mono_shift_map_mor₁_iff
      T ht (i - 1) i (by omega)).2 (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{m} i).map T.mor₁)

end AlgebraicGeometry.Space

end
