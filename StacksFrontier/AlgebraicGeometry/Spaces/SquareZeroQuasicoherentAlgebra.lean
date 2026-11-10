module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExtAnySite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceObstruction

/-!
# Arbitrarily large quasi-coherent algebras, and the unconditional 081V obstruction

`StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceObstruction` proves two halves
of a size obstruction to `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, this
development's rendering of Stacks 081V.  The source side is bounded
(`AlgebraicGeometry.Space.mk_sections_pushforwardAlgebra_lt_cutoff`), and the target side is
unbounded *at the level of modules*
(`AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_cutoff_le_mk_sections`).  What was owed is
a commutative-ring structure on a large quasi-coherent module, so that the module witness becomes
an *algebra* witness and the obstruction becomes unconditional.

This file supplies it by the **trivial (square-zero) extension** `𝒪_F ⊕ M`.

## The construction

For a sheaf of `𝒪_F`-modules `M` on the small étale site of an algebraic space `F`, the sections
of the square-zero extension over an étale chart `U` are `TrivSqZeroExt 𝒪_F(U) M(U)`: the
commutative ring whose underlying group is `𝒪_F(U) ⊕ M(U)`, with
`(a, m) * (a', m') = (a a', a m' + a' m)`.  The presheaf is Mathlib's `TrivSqZeroExt` sectionwise,
already packaged in this tree as `PresheafOfModules.sqZeroExtPresheafAnySite`, and the
structure-algebra map is `PresheafOfModules.sqZeroExtInlAnySite`, `a ↦ (a, 0)`.

Three things then have to be checked, and they are the three sections below.

1. **The sheaf condition.**  `AlgebraicGeometry.Space.sqZeroExtPresheaf_isSheaf`: the underlying
   presheaf of types is the product of the two underlying sheaves of types, so it glues
   componentwise, and `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget` promotes that to the
   sheaf condition for commutative rings.  (The type-level sheaf condition of the structure sheaf
   is `AlgebraicGeometry.Space.isSheaf_globalSections`, and that of `M` is
   `CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` applied to `SheafOfModules.isSheaf`.)

2. **The underlying module.**  `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` builds the
   `𝒪_F`-module of an algebra sheaf on the algebra's own sections, by restriction of scalars along
   the structure-algebra map.  So the sections of the underlying module of the square-zero
   extension are again `TrivSqZeroExt 𝒪_F(U) M(U)`, with `a • (a', m') = (a a', a m')` —
   the direct sum `𝒪_F(U) ⊕ M(U)` of `𝒪_F(U)`-modules, and
   `AlgebraicGeometry.Space.sqZeroProdEquiv` records exactly that.

3. **Quasi-coherence, for `M` free.**  Over an *affine* chart `W` the sections of
   `SheafOfModules.free I` are the finitely supported families `I →₀ 𝒪_F(W)`
   (`AlgebraicGeometry.Space.freeSectionsIsoOfIsAffine`, resting on Stacks 0935), so the sections
   of the square-zero extension are `𝒪_F(W) ⊕ (I →₀ 𝒪_F(W)) ≅ ((Unit ⊕ I) →₀ 𝒪_F(W))`: the
   square-zero extension of `𝒪_F` by a free module of rank `I` is, over every affine chart, free
   of rank `Unit ⊕ I`.  That is the hypothesis of
   `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_finsuppEquiv`, which then gives
   cartesianness on affine charts, and Stacks 03DX in the shape of
   `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts` gives
   quasi-coherence.

## Main definitions

* `AlgebraicGeometry.Space.sqZeroAlgebraSheaf`: the square-zero extension `𝒪_F ⊕ M` of the
  structure sheaf by a sheaf of `𝒪_F`-modules, as an `AlgebraicGeometry.Space.AlgebraSheaf`.
* `AlgebraicGeometry.Space.HasNonzeroAffineChart`: **the nondegeneracy hypothesis** of the main
  theorem.  The algebraic space has an affine étale chart whose ring of regular functions is not
  the zero ring.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_sqZeroFree`: **the square-zero extension of `𝒪_F` by a
  free module of any rank is a quasi-coherent algebra.**  Unconditional: no hypothesis on `F` and
  none on the rank.
* `AlgebraicGeometry.Space.exists_quasicoherentAlgebra_cutoff_le_mk_sections`: **the target side
  of the anti-equivalence is unbounded at the level of algebras.**  On an algebraic space with one
  affine chart carrying a nonzero ring of functions there is a quasi-coherent `𝒪_X`-algebra with
  at least `B.cutoff` sections over that chart.  This is the algebra witness that
  `AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_cutoff_le_mk_sections` provides only for
  modules.
* `AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`:
  **the obstruction, unconditional.**  If some algebraic space of the site has an affine chart
  whose regular functions are not the zero ring, then `AffineAlgebraAntiEquivalence B S hS` is
  uninhabited, and every result carrying an inhabitant of it as a hypothesis is vacuous.

## Implementation notes

The nondegeneracy hypothesis is necessary and is stated, not hidden: over the empty algebraic
space every sheaf has exactly one section over every chart, so no sheaf of any kind has
`B.cutoff` sections and no obstruction can be derived.  `HasNonzeroAffineChart` asks for a single
affine chart `W` with `(1 : 𝒪_F(W)) ≠ 0`, which is the weakest form in which the witness of
`AlgebraicGeometry.Space.le_mk_sections_free` — the one-point families `Finsupp.single i 1` — are
pairwise distinct.  It is the same side condition
`AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_cutoff_le_mk_sections` already carries,
packaged as a named predicate.

The rank is taken to be `Unit ⊕ I` rather than `Option I` because
`Finsupp.sumFinsuppLEquivProdFinsupp` splits a `Sum`-indexed family into a pair *linearly* and
with `rfl` component lemmas, while `Finsupp.optionEquiv` is only an `Equiv`.

The index universe of `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_finsuppEquiv` is
free, which is what lets `Unit ⊕ I` be used even though `Unit` lives in `Type 0` and the rank in
`Type u`.

The square-zero extension is taken from
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExtAnySite` and not from
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt`.  The latter builds it over a small
site, where the objects, the morphisms and the sections share a single universe, whereas
`PresheafOfModules.sqZeroExtPresheafAnySite` is stated for a site `C : Type u₁` with
`Category.{v₁} C` and sections in an unrelated `Type u`.  The small étale site of an algebraic
space has `C : Type (u + 1)` with `Category.{u} C`, so all three universes are distinct here and
it is the `AnySite` form that applies.  The sheaf condition is
proved here rather than reused from `Stacks.Sheaves.Differentials.isSheaf_sqZeroExtPresheaf`,
which assumes `SmallCategory` and so does not reach this site; the relation between the two is
the relation between `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget` and
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`, whose universe restriction is exactly what
is in the way.

No `@[stacks]` attribute is claimed.  Stacks 081V *asserts* the anti-equivalence; what is proved
here is that this development's rendering of it is uninhabited, which is a fact about the
rendering and not a tag.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal SheafOfModules
open PresheafOfModules (sqZeroExtPresheafAnySite sqZeroExtInlAnySite sqZeroExtFstAnySite
  sqZeroExtSndAnySite sqZeroExtMkAnySite sqZeroExt_ext_anySite)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The square-zero extension as an algebra sheaf -/

/-- **The square-zero extension of the structure sheaf by a sheaf of modules is a sheaf of
commutative rings.**  Its sections over a chart are `TrivSqZeroExt 𝒪_F(U) M(U)`, and on underlying
types that is the product of the sections of the structure sheaf and of `M`, so a compatible
family glues componentwise: the ring component by
`AlgebraicGeometry.Space.isSheaf_globalSections`, the module component by the sheaf condition of
`M`.  `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget` turns gluing in types into the sheaf
condition for commutative rings, with no universe relation between the site and the
coefficients. -/
theorem sqZeroExtPresheaf_isSheaf (M : Modules.{u, u} B S hS F hF) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS F)
      (sqZeroExtPresheafAnySite (R := (structureSheaf B S hS F hF).obj) M.val) := by
  refine Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget _ _ ?_
  have hO : Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (structurePresheaf B S hS F ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    isSheaf_globalSections B S hS F
  have hM : Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf M))
  intro W Sv hSv x hx
  obtain ⟨t₁, ht₁, ht₁'⟩ := hO Sv hSv (fun _ f h => sqZeroExtFstAnySite (M := M.val) (x f h))
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hg =>
      congrArg (sqZeroExtFstAnySite (M := M.val)) (hx g₁ g₂ h₁ h₂ hg))
  obtain ⟨t₂, ht₂, ht₂'⟩ := hM Sv hSv (fun _ f h => sqZeroExtSndAnySite (M := M.val) (x f h))
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hg =>
      congrArg (sqZeroExtSndAnySite (M := M.val)) (hx g₁ g₂ h₁ h₂ hg))
  refine ⟨sqZeroExtMkAnySite t₁ t₂, fun Y f h => ?_, fun y hy => ?_⟩
  · exact sqZeroExt_ext_anySite (ht₁ f h) (ht₂ f h)
  · exact sqZeroExt_ext_anySite
      (ht₁' _ fun _ f h => congrArg (sqZeroExtFstAnySite (M := M.val)) (hy f h))
      (ht₂' _ fun _ f h => congrArg (sqZeroExtSndAnySite (M := M.val)) (hy f h))

/-- **The square-zero extension `𝒪_F ⊕ M`** of the structure sheaf of the small étale site of the
algebraic space `F` by a sheaf of `𝒪_F`-modules `M`, as a sheaf of commutative `𝒪_F`-algebras.
The multiplication is `(a, m) * (a', m') = (a a', a m' + a' m)`, so the `M` part is a square-zero
ideal, and the structure-algebra map is `a ↦ (a, 0)`. -/
def sqZeroAlgebraSheaf (M : Modules.{u, u} B S hS F hF) : AlgebraSheaf.{u, u} B S hS F hF :=
  AlgebraSheaf.ofHom
    (R := ⟨sqZeroExtPresheafAnySite M.val, sqZeroExtPresheaf_isSheaf B S hS F hF M⟩)
    { hom := sqZeroExtInlAnySite M.val }

variable {B S hS F hF}

/-! ### The underlying module is the direct sum -/

/-- The regular function which is the ring component of a section of the square-zero extension
over a chart. -/
def sqZeroSectionFst (M : Modules.{u, u} B S hS F hF) {W : SmallEtale B S hS F}
    (x : (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op W)) :
    chartRing B S hS F hF W :=
  sqZeroExtFstAnySite (M := M.val) (U := op W) x

/-- The section of `M` which is the module component of a section of the square-zero extension
over a chart. -/
def sqZeroSectionSnd (M : Modules.{u, u} B S hS F hF) {W : SmallEtale B S hS F}
    (x : (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op W)) :
    M.val.obj (op W) :=
  sqZeroExtSndAnySite (M := M.val) (U := op W) x

/-- The section of the square-zero extension over a chart with the given regular function as ring
component and the given section of `M` as module component. -/
def sqZeroSectionMk (M : Modules.{u, u} B S hS F hF) {W : SmallEtale B S hS F}
    (r : chartRing B S hS F hF W) (m : M.val.obj (op W)) :
    (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op W) :=
  sqZeroExtMkAnySite (M := M.val) r m

/-- Scaling a section of the square-zero extension by a regular function multiplies its ring
component. -/
theorem sqZeroSectionFst_smul (M : Modules.{u, u} B S hS F hF) {W : SmallEtale B S hS F}
    (r : chartRing B S hS F hF W)
    (x : (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op W)) :
    sqZeroSectionFst M (r • x) = r * sqZeroSectionFst M x := rfl

/-- Scaling a section of the square-zero extension by a regular function scales its module
component: the cross term of the square-zero multiplication is a multiple of the vanishing module
component of `(r, 0)`. -/
theorem sqZeroSectionSnd_smul (M : Modules.{u, u} B S hS F hF) {W : SmallEtale B S hS F}
    (r : chartRing B S hS F hF W)
    (x : (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op W)) :
    sqZeroSectionSnd M (r • x) = r • sqZeroSectionSnd M x := by
  change r • sqZeroSectionSnd M x + sqZeroSectionFst M x • (0 : M.val.obj (op W)) = _
  rw [smul_zero, add_zero]

/-- Restriction of a section of the square-zero extension restricts its ring component. -/
theorem sqZeroSectionFst_restrict (M : Modules.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (x : (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op U)) :
    sqZeroSectionFst M (chartRestrictLinear
        (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule f x) =
      chartRestrict (hF := hF) f (sqZeroSectionFst M x) := rfl

/-- Restriction of a section of the square-zero extension restricts its module component. -/
theorem sqZeroSectionSnd_restrict (M : Modules.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (x : (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op U)) :
    sqZeroSectionSnd M (chartRestrictLinear
        (sqZeroAlgebraSheaf B S hS F hF M).underlyingModule f x) =
      chartRestrictLinear M f (sqZeroSectionSnd M x) := rfl

/-- **The sections of the underlying module of the square-zero extension over a chart are the
direct sum `𝒪_F(W) ⊕ M(W)`.**  The underlying module of an algebra sheaf is the algebra's own
sections with scalars restricted along the structure-algebra map, and `(r, 0) * (a, m)` is
`(r a, r m)`. -/
def sqZeroProdEquiv (M : Modules.{u, u} B S hS F hF) (W : SmallEtale B S hS F) :
    ((sqZeroAlgebraSheaf B S hS F hF M).underlyingModule.val.obj (op W)) ≃ₗ[
        chartRing B S hS F hF W]
      (chartRing B S hS F hF W) × (M.val.obj (op W)) where
  toFun x := (sqZeroSectionFst M x, sqZeroSectionSnd M x)
  map_add' _ _ := rfl
  map_smul' r x :=
    Prod.ext (sqZeroSectionFst_smul M r x) (sqZeroSectionSnd_smul M r x)
  invFun p := sqZeroSectionMk M p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The square-zero extension of a free module is quasi-coherent -/

/-- The sections of a free `𝒪_F`-module over an affine chart, as a linear equivalence with the
finitely supported families of regular functions.  This is
`AlgebraicGeometry.Space.bijective_freeSectionsMap_of_isAffine` read as an equivalence. -/
def freeChartEquiv (I : Type u) (W : SmallEtale B S hS F) (hW : IsAffine (chartScheme W)) :
    (I →₀ chartRing B S hS F hF W) ≃ₗ[chartRing B S hS F hF W]
      ((free (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        ) I).val.obj (op W)) :=
  LinearEquiv.ofBijective (Stacks.Sites.freeSectionsMap
      (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        ) I (op W)).hom
    (bijective_freeSectionsMap_of_isAffine B S hS F hF I W hW)

/-- Read through `AlgebraicGeometry.Space.freeChartEquiv`, restriction of sections of a free
`𝒪_F`-module along a morphism of affine charts is coefficientwise restriction of functions.  This
is `AlgebraicGeometry.Space.freeSectionsMap_restrict` transported across the equivalence. -/
theorem freeChartEquiv_symm_restrict (I : Type u) {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V))
    (y : (free (R :=
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) I).val.obj
        (op U))
    (i : I) :
    (freeChartEquiv I V hV).symm (chartRestrictLinear
        (free (R :=
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) I)
          f y) i =
      chartRestrict (hF := hF) f ((freeChartEquiv I U hU).symm y i) := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p, y = freeChartEquiv I U hU p :=
    ⟨(freeChartEquiv I U hU).symm y, ((freeChartEquiv I U hU).apply_symm_apply y).symm⟩
  rw [(freeChartEquiv I U hU).symm_apply_apply]
  have hy : (freeChartEquiv I V hV).symm (chartRestrictLinear
        (free (R :=
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          ) I) f
        (freeChartEquiv I U hU p))
      = Finsupp.mapRange (chartRestrict (hF := hF) f) (map_zero _) p :=
    (freeChartEquiv I V hV).symm_apply_eq.2 (freeSectionsMap_restrict (hF := hF) I f p)
  rw [hy, Finsupp.mapRange_apply]

/-- **Over an affine chart the square-zero extension of `𝒪_F` by a free module of rank `I` is
free of rank `Unit ⊕ I`.**  The ring component contributes the `Unit`-indexed coefficient and the
module component the `I`-indexed ones, by
`AlgebraicGeometry.Space.sqZeroProdEquiv`, `AlgebraicGeometry.Space.freeChartEquiv` and
`Finsupp.sumFinsuppLEquivProdFinsupp`. -/
def sqZeroFreeChartEquiv (I : Type u) (W : SmallEtale B S hS F)
    (hW : IsAffine (chartScheme W)) :
    ((sqZeroAlgebraSheaf B S hS F hF
          (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
            I)).underlyingModule.val.obj (op W)) ≃ₗ[chartRing B S hS F hF W]
      ((Unit ⊕ I) →₀ chartRing B S hS F hF W) :=
  (sqZeroProdEquiv _ W).trans
    ((LinearEquiv.prodCongr
        (Finsupp.uniqueLinearEquiv (chartRing B S hS F hF W) (chartRing B S hS F hF W)
          (() : Unit)).symm
        (freeChartEquiv I W hW).symm).trans
      (Finsupp.sumFinsuppLEquivProdFinsupp (chartRing B S hS F hF W)).symm)

/-- The `Unit`-indexed coefficient of `AlgebraicGeometry.Space.sqZeroFreeChartEquiv` is the ring
component. -/
theorem sqZeroFreeChartEquiv_inl (I : Type u) (W : SmallEtale B S hS F)
    (hW : IsAffine (chartScheme W))
    (x : (sqZeroAlgebraSheaf B S hS F hF
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        I)).underlyingModule.val.obj (op W)) (t : Unit) :
    sqZeroFreeChartEquiv I W hW x (Sum.inl t) = sqZeroSectionFst _ x := by
  change (Finsupp.uniqueLinearEquiv (chartRing B S hS F hF W) (chartRing B S hS F hF W)
      (() : Unit)).symm (sqZeroSectionFst _ x) t = _
  exact Finsupp.uniqueLinearEquiv_symm_apply_apply _ _ _ _ _

/-- The `I`-indexed coefficients of `AlgebraicGeometry.Space.sqZeroFreeChartEquiv` are those of
the module component. -/
theorem sqZeroFreeChartEquiv_inr (I : Type u) (W : SmallEtale B S hS F)
    (hW : IsAffine (chartScheme W))
    (x : (sqZeroAlgebraSheaf B S hS F hF
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        I)).underlyingModule.val.obj (op W)) (i : I) :
    sqZeroFreeChartEquiv I W hW x (Sum.inr i) =
      (freeChartEquiv I W hW).symm (sqZeroSectionSnd _ x) i := rfl

/-- **The underlying module of the square-zero extension of `𝒪_F` by a free module is cartesian
on affine charts.**  Over affine charts it is free of rank `Unit ⊕ I` with coefficientwise
restriction, which is the hypothesis of
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_finsuppEquiv`. -/
theorem isCartesianOnAffineCharts_sqZeroFree (I : Type u) :
    IsCartesianOnAffineCharts (sqZeroAlgebraSheaf B S hS F hF
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        I)).underlyingModule := by
  intro U V hU hV f
  refine bijective_sectionsBaseChange_of_finsuppEquiv f
    (sqZeroFreeChartEquiv I U hU) (sqZeroFreeChartEquiv I V hV) fun x i => ?_
  cases i with
  | inl t =>
      rw [sqZeroFreeChartEquiv_inl, sqZeroFreeChartEquiv_inl]
      exact sqZeroSectionFst_restrict _ f x
  | inr i =>
      rw [sqZeroFreeChartEquiv_inr, sqZeroFreeChartEquiv_inr, sqZeroSectionSnd_restrict]
      exact freeChartEquiv_symm_restrict I f hU hV (sqZeroSectionSnd _ x) i

/-- **The square-zero extension of `𝒪_F` by a free module of any rank is a quasi-coherent
`𝒪_F`-algebra.**  Unconditional: no hypothesis on the algebraic space and none on the rank.  This
is the commutative-ring structure which
`AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_cutoff_le_mk_sections` leaves to be
supplied. -/
theorem isQuasicoherent_sqZeroFree (I : Type u) :
    (sqZeroAlgebraSheaf B S hS F hF
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        I)).IsQuasicoherent :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ (isCartesianOnAffineCharts_sqZeroFree I)

/-- **The sections of the square-zero extension of `𝒪_F` by a free module are at least as many as
its rank**, over an affine chart whose regular functions are not the zero ring: the sections of
the free module already are, by `AlgebraicGeometry.Space.le_mk_sections_free`, and `m ↦ (0, m)` is
injective. -/
theorem le_mk_sections_sqZeroFree (I : Type u) (W : SmallEtale B S hS F)
    (hW : IsAffine (chartScheme W)) (h1 : (1 : chartRing B S hS F hF W) ≠ 0) :
    #I ≤ #((sqZeroAlgebraSheaf B S hS F hF
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        I)).right.obj.obj (op W)) := by
  refine (le_mk_sections_free B S hS F hF I W hW h1).trans
    (mk_le_of_injective (f := fun m => sqZeroSectionMk
      (free (R :=
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        ) I) 0 m) ?_)
  exact fun _ _ h => congrArg (sqZeroSectionSnd _) h

/-! ### The obstruction, unconditional -/

/-- **The nondegeneracy hypothesis.**  The algebraic space `X` has an affine étale chart whose
ring of regular functions is not the zero ring.

It cannot be dropped: over the empty algebraic space every sheaf has exactly one section over
every chart, so no sheaf has `B.cutoff` sections and no size obstruction exists. -/
def HasNonzeroAffineChart (X : AlgebraicSpaces B S hS) : Prop :=
  ∃ W : SmallEtale B S hS X.1,
    IsAffine (chartScheme W) ∧ (1 : chartRing B S hS X.1 X.2 W) ≠ 0

/-- **A quasi-coherent `𝒪_X`-algebra with at least `B.cutoff` sections over a single chart**, on
any algebraic space with an affine chart carrying a nonzero ring of functions: the square-zero
extension of `𝒪_X` by the free module whose rank is a type of cardinality `B.cutoff`.

This is the algebra half of the obstruction, which
`AlgebraicGeometry.Space.exists_isQuasicoherentOnSite_cutoff_le_mk_sections` supplies only for
modules. -/
theorem exists_quasicoherentAlgebra_cutoff_le_mk_sections (X : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS X.1) (hW : IsAffine (chartScheme W))
    (h1 : (1 : chartRing B S hS X.1 X.2 W) ≠ 0) :
    ∃ A : QuasicoherentAlgebra B S hS X, B.cutoff ≤ #(A.obj.right.obj.obj (op W)) :=
  ⟨⟨sqZeroAlgebraSheaf B S hS X.1 X.2
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        B.cutoff.ord.ToType), isQuasicoherent_sqZeroFree _⟩,
    (mk_ord_toType B.cutoff).symm.le.trans (le_mk_sections_sqZeroFree _ W hW h1)⟩

/-- **The size obstruction to the affine-algebra anti-equivalence, unconditionally.**

If a single algebraic space of the site has a single affine étale chart whose regular functions
are not the zero ring, then `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence B S hS` — this
development's rendering of Stacks 081V — is uninhabited, and therefore every result carrying an
inhabitant of it as a hypothesis is vacuous.

The two sides are bounded differently.  Affine morphisms are representable, so the sections of
`f_* 𝒪_Y` over a chart are the regular functions on a scheme of the site and are fewer than the
cutoff (`AlgebraicGeometry.Space.mk_sections_pushforwardAlgebra_lt_cutoff`, Stacks 03G8), while
quasi-coherent algebras carry no cardinality condition at all: the square-zero extension of `𝒪_X`
by a free module of rank `B.cutoff` is one, by
`AlgebraicGeometry.Space.exists_quasicoherentAlgebra_cutoff_le_mk_sections`.  An
anti-equivalence, being essentially surjective, would identify the two. -/
theorem not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart
    {X : AlgebraicSpaces B S hS} (hX : HasNonzeroAffineChart X) :
    ¬ Nonempty (AffineAlgebraAntiEquivalence B S hS) := by
  obtain ⟨W, hW, h1⟩ := hX
  obtain ⟨A, hA⟩ := exists_quasicoherentAlgebra_cutoff_le_mk_sections X W hW h1
  exact not_nonempty_affineAlgebraAntiEquivalence_of_cutoff_le_mk_sections B S hS W A hA

end AlgebraicGeometry.Space

end
