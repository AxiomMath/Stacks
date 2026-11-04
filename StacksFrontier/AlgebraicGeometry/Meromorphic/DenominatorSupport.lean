module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorRule
public import StacksFrontier.AlgebraicGeometry.Meromorphic.LocalDenominator
public import StacksFrontier.Topology.Sheaves.Modules.Support

/-!
# The two cokernels of the ideal of denominators are supported on a nowhere dense closed set

Let `X` be a scheme, `L` an invertible sheaf of `𝒪_X`-modules and `s` a meromorphic section of
`L`. [Stacks, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0) asserts, of the ideal `I` of
denominators of `s`, that the cokernels of the two maps `I ⟶ 𝒪_X` and `I ⟶ L` are supported on
closed nowhere dense subsets of `X`. This file proves both.

The source argues by shrinking `X` until `L` is trivial and `s = a/b` with `a`, `b`
nonzerodivisors; then `I ⊇ (b)` so the first cokernel dies on `X.basicOpen b`, the image of the
second contains `(a)` so it dies on `X.basicOpen a`, and the vanishing locus of a nonzerodivisor
on an affine open is nowhere dense. That normal form is
`AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator` below, which refines the
local denominator lemma of
`StacksFrontier/AlgebraicGeometry/Meromorphic/LocalDenominator.lean` by also producing the
numerator `a` and a generator of `L` valid on every smaller open.

## Main results

* `AlgebraicGeometry.denominatorIdeal_inclusion_support`: **Tag 02P0**, the support of the
  cokernel of `I ⟶ 𝒪_X`.
* `AlgebraicGeometry.denominatorIdeal_section_support`: **Tag 02P0**, the support of the
  cokernel of `I ⟶ L`, for a regular meromorphic section.
* `AlgebraicGeometry.supp_cokernel_subset`: the general principle both rest on. If every point
  outside a set `Z` has a neighbourhood on each open subset of which `f` is surjective on
  sections, then the support of `cokernel f` lies in `Z`.
* `AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator`: the normal form
  `b · s = a · g` on an affine neighbourhood, with `g` a generator of `L` over every smaller
  open and `b` a nonzerodivisor.
* `AlgebraicGeometry.numerator_mem_nonZeroDivisors`: for a *regular* section the numerator `a`
  of that normal form is a nonzerodivisor. This is the only place regularity is used.
* `AlgebraicGeometry.surjective_denominatorIdealIota_app` and
  `AlgebraicGeometry.surjective_denominatorIdealMul_app`: the two local surjectivity
  statements, the first where `b` is invertible and the second where `a` is.
* `CategoryTheory.Limits.exists_map_pullback_snd_eq_iff`: the second-projection companion of
  `CategoryTheory.Limits.exists_map_pullback_fst_eq_iff`.

## Implementation notes

The support of a sheaf of modules is `AlgebraicGeometry.RingedSpace.ModuleSheaf.supp`, the set
of points with nonzero stalk, and `AlgebraicGeometry.RingedSpace.ModuleSheaf.mem_supp_iff`
(Tag 01AU) turns a point of the support into a section with a nonzero germ. The cokernel
projection is an epimorphism, hence locally surjective by
`Stacks.SheafOfModules.EpiMono.exists_covering_of_epi`, so that section is locally in the image
of the target; intersecting with the neighbourhood on which `f` is surjective makes the section
restrict to zero, and its germ vanishes. That whole step is
`Stacks.Meromorphic.exists_nhds_map_cokernel_eq_zero`, stated for an arbitrary sheaf of rings
on a space: at the scheme-level spelling the elaborator pays a large defeq for each application
of a lemma mentioning `Stacks.Sheaves.Differentials.ringSheaf`, and five such payments in one
theorem exceed the default heartbeat budget. For the same reason each scheme-level lemma here is
kept small and every application is made through a `have` before the result is destructured.

The nowhere dense closed set is the complement of the union, over all points, of
`V ⊓ X.basicOpen b` (respectively `V ⊓ X.basicOpen a`). It is closed because that union is
open, and nowhere dense because the union is dense: on an affine open the basic open set of a
nonzerodivisor meets every nonempty open subset
(`AlgebraicGeometry.inf_basicOpen_ne_bot_of_mem_nonZeroDivisors`).

Scalars are written in the `RingCat` spelling
`(Stacks.Sheaves.Differentials.ringSheaf X.sheaf).obj.obj (op V)` throughout, because the
bridging `Module` instance of `PresheafOfModules` does not fire for a `Γ(X, V)` written as
`X.presheaf.obj (op V)`; restrictions of sections are taken with `PresheafOfModules.restrictₛₗ`,
whose target type is the plain module of sections rather than a restriction of scalars, for the
same reason.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 01AU](https://stacks.math.columbia.edu/tag/01AU)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 03HN](https://stacks.math.columbia.edu/tag/03HN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.RingedToposModules
open scoped nonZeroDivisors

universe v u

namespace PresheafOfModules

/-- Restricting twice is restricting along the composite. -/
theorem restrictₛₗ_restrictₛₗ {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x : M.obj U) :
    M.restrictₛₗ j (M.restrictₛₗ i x) = M.restrictₛₗ (i ≫ j) x :=
  (PresheafOfModules.map_comp_apply M i j x).symm

end PresheafOfModules

namespace CategoryTheory.Limits

open CategoryTheory.ConcreteCategory

/-- The second-projection companion of
`CategoryTheory.Limits.exists_map_pullback_fst_eq_iff`. Let `G` be a functor into a concrete
category which preserves the pullback of `g` and `h`. An element of `G.obj B` is the image of
an element of `G.obj (pullback g h)` under the second projection exactly when it agrees, after
`G.map h`, with the image of some element of `G.obj A` under `G.map g`. -/
theorem exists_map_pullback_snd_eq_iff {C : Type*} [Category C] {D : Type*} [Category.{v} D]
    {FD : D → D → Type*} {DD : D → Type v} [∀ X Y, FunLike (FD X Y) (DD X) (DD Y)]
    [ConcreteCategory.{v} D FD]
    (G : C ⥤ D) {A B S : C} (g : A ⟶ S) (h : B ⟶ S)
    [HasPullback g h] [PreservesLimit (cospan g h) G]
    [HasPullback (G.map g) (G.map h)]
    [PreservesLimit (cospan (G.map g) (G.map h)) (forget D)]
    (b : ToType (G.obj B)) :
    (∃ d : ToType (G.obj (pullback g h)), G.map (pullback.snd g h) d = b) ↔
      ∃ a : ToType (G.obj A), G.map g a = G.map h b := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨G.map (pullback.fst g h) d, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← G.map_comp,
      ← G.map_comp, pullback.condition]
  · rintro ⟨a, hab⟩
    refine ⟨(PreservesPullback.iso G g h).inv (Concrete.pullbackMk _ _ a b hab), ?_⟩
    rw [← ConcreteCategory.comp_apply, PreservesPullback.iso_inv_snd,
      Concrete.pullbackMk_snd]

end CategoryTheory.Limits

namespace Stacks.Meromorphic

section Space

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- **A section of a cokernel dies near every point where the map is locally surjective.** If
`f` is surjective on sections over every open inside `W`, then every section of `cokernel f`
restricts to zero on a neighbourhood of each point of `W`. -/
theorem exists_nhds_map_cokernel_eq_zero (f : M ⟶ N) (W : Opens T)
    (hsurj : ∀ V : Opens T, V ≤ W → Function.Surjective ((f.val.app (op V)).hom))
    (U : Opens T) (t : (cokernel f).val.obj (op U)) (x : T) (hxU : x ∈ U) (hxW : x ∈ W) :
    ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧
      ((cokernel f).val.map (homOfLE hVU).op).hom t = 0 := by
  obtain ⟨S, hS, hSprop⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    (cokernel.π f) (V := U) t
  rw [Opens.mem_grothendieckTopology] at hS
  obtain ⟨V₁, g, hg, hxV₁⟩ := hS x hxU
  obtain ⟨n, hn⟩ := hSprop g hg
  have h21 : V₁ ⊓ W ≤ V₁ := inf_le_left
  have h2U : V₁ ⊓ W ≤ U := h21.trans g.le
  refine ⟨V₁ ⊓ W, h2U, ⟨hxV₁, hxW⟩, ?_⟩
  obtain ⟨d, hd⟩ := hsurj (V₁ ⊓ W) inf_le_right ((N.val.map (homOfLE h21).op).hom n)
  have hnn : ((cokernel.π f).val.app (op V₁)).hom n
      = ((cokernel f).val.map g.op).hom t := hn
  have step1 : ((cokernel f).val.map (homOfLE h21).op).hom
        (((cokernel.π f).val.app (op V₁)).hom n)
      = ((cokernel.π f).val.app (op (V₁ ⊓ W))).hom
          ((N.val.map (homOfLE h21).op).hom n) :=
    (PresheafOfModules.naturality_apply (cokernel.π f).val (homOfLE h21).op n).symm
  have step2 : ((cokernel f).val.map (homOfLE h21).op).hom
        (((cokernel f).val.map g.op).hom t)
      = ((cokernel f).val.map (homOfLE h2U).op).hom t := by
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  have step3 : ((cokernel.π f).val.app (op (V₁ ⊓ W))).hom
      ((f.val.app (op (V₁ ⊓ W))).hom d) = 0 :=
    congrArg (fun (m : M ⟶ cokernel f) => ((m.val.app (op (V₁ ⊓ W))).hom d))
      (cokernel.condition (f := f))
  rw [← step2, ← hnn, step1, ← hd]
  exact step3

end Space

end Stacks.Meromorphic

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The germ of a restricted section is the germ of the section. -/
theorem sectionGerm_val_map (F : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
    {U V : X.Opens} (hle : V ≤ U) (x : X) (hx : x ∈ V)
    (t : F.val.obj (op U)) :
    (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).sectionGerm V x hx
        ((F.val.map (homOfLE hle).op).hom t)
      = (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).sectionGerm U x
          (hle hx) t :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) F.val.presheaf (homOfLE hle) x hx t

/-- **The support of a cokernel is contained in the locus where the map is not locally
surjective.** If every point outside `Z` has a neighbourhood `W` such that `f` is surjective on
sections over every open inside `W`, then the support of `cokernel f` is contained in `Z`. -/
theorem supp_cokernel_subset {M N : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)}
    (f : M ⟶ N) (Z : Set X)
    (h : ∀ x : X, x ∉ Z → ∃ W : X.Opens, x ∈ W ∧
      ∀ V : X.Opens, V ≤ W → Function.Surjective ((f.val.app (op V)).hom)) :
    (⟨(cokernel f).val, (cokernel f).isSheaf⟩ :
      RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆ Z := by
  intro x hx
  rw [RingedSpace.ModuleSheaf.mem_supp_iff] at hx
  obtain ⟨U, t, hxU, hne⟩ := hx
  by_contra hxZ
  obtain ⟨W, hxW, hsurj⟩ := h x hxZ
  obtain ⟨V, hVU, hxV, hzero⟩ := Stacks.Meromorphic.exists_nhds_map_cokernel_eq_zero
    f W hsurj U t x hxU hxW
  refine hne ((sectionGerm_val_map X (cokernel f) hVU x hxV t).symm.trans ?_)
  rw [hzero]
  exact map_zero _

/-- A point of an affine open lies in the closure of the part of it where a nonzerodivisor is
invertible. -/
theorem mem_closure_inf_basicOpen_of_mem_nonZeroDivisors {U : X.Opens} (hU : IsAffineOpen U)
    {b : Γ(X, U)} (hb : b ∈ (Γ(X, U))⁰) {y : X} (hy : y ∈ U) :
    y ∈ closure ((U ⊓ X.basicOpen b : X.Opens) : Set X) := by
  rw [mem_closure_iff]
  intro O hO hyO
  have hWU : (⟨O ∩ (U : Set X), hO.inter U.isOpen⟩ : X.Opens) ≤ U := fun z hz => hz.2
  have hWne : (⟨O ∩ (U : Set X), hO.inter U.isOpen⟩ : X.Opens) ≠ ⊥ :=
    (Opens.ne_bot_iff_nonempty _).mpr ⟨y, hyO, hy⟩
  obtain ⟨z, hzW, hzb⟩ :=
    (Opens.ne_bot_iff_nonempty _).mp
      (inf_basicOpen_ne_bot_of_mem_nonZeroDivisors hU hb hWU hWne)
  exact ⟨z, hzW.1, hzW.2, hzb⟩

/-- The complement of a dense open set is nowhere dense. -/
theorem isNowhereDense_compl_of_dense {Z : Set X} (hZ : IsOpen Z) (hd : Dense Z) :
    IsNowhereDense Zᶜ := by
  rw [(hZ.isClosed_compl).isNowhereDense_iff, interior_compl, hd.closure_eq, Set.compl_univ]

/-- A section is invertible on every open subset of its basic open set. The special case
`V = ⊤` is `Stacks.RelativeSpec.isUnit_res_of_le_basicOpen`
(`StacksFrontier/AlgebraicGeometry/RelativeSpecRepresentability/Basic.lean`), which this
generalizes; the name here differs so that the two do not read as one declaration. -/
theorem isUnit_presheaf_map_of_le_basicOpen {V U : X.Opens} (b : Γ(X, V))
    (hUb : U ≤ X.basicOpen b) (hUV : U ≤ V) :
    IsUnit (X.presheaf.map (homOfLE hUV).op b) := by
  have h0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le b)).op b) :=
    X.toRingedSpace.isUnit_res_basicOpen b
  have h1 := h0.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE hUb).op))
  rwa [← CommRingCat.comp_apply, ← X.presheaf.map_comp] at h1

variable (L : SheafOfModules.{u}
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf))
  (s : MeromorphicSection X.sheaf L)

/-- A denominator of `s` over `V` restricts to a denominator over every smaller open. -/
theorem meromorphicSectionMul_app_res_eq {V U : X.Opens} (hUV : U ≤ V) (b : Γ(X, V))
    (t : L.val.obj (op V))
    (ht : ((meromorphicSectionMul X L s).val.app (op V)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op V)).hom t) :
    ((meromorphicSectionMul X L s).val.app (op U)).hom
        (X.presheaf.map (homOfLE hUV).op b)
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom
          (L.val.restrictₛₗ (homOfLE hUV).op t) :=
  (PresheafOfModules.naturality_apply (meromorphicSectionMul X L s).val
      (homOfLE hUV).op b).trans
    ((congrArg (fun z : (meromorphicSectionSheafAsModule X L).val.obj (op V) =>
        (((meromorphicSectionSheafAsModule X L).val.map (homOfLE hUV).op).hom z)) ht).trans
      (PresheafOfModules.naturality_apply (toMeromorphicSectionSheafAsModule X L).val
        (homOfLE hUV).op t).symm)

/-- A denominator `b` with `b · s = t` gives the denominator `c * b` with `(c * b) · s = c • t`. -/
private theorem meromorphicSectionMul_app_mul_eq (U : X.Opens)
    (b c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op U))
    (t : L.val.obj (op U))
    (heq : ((meromorphicSectionMul X L s).val.app (op U)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom t) :
    ((meromorphicSectionMul X L s).val.app (op U)).hom (c * b)
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom (c • t) := by
  have h1 := ((meromorphicSectionMul X L s).val.app (op U)).hom.map_smul c b
  have h2 := ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom.map_smul c t
  rw [h2, ← heq, ← h1]
  rfl

/-- **Where a denominator of `s` is invertible, the inclusion of the ideal of denominators is
surjective on sections.** -/
theorem surjective_denominatorIdealIota_app (U : X.Opens)
    (b : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op U))
    (hunit : IsUnit b) (t : L.val.obj (op U))
    (heq : ((meromorphicSectionMul X L s).val.app (op U)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom t) :
    Function.Surjective ((denominatorIdealι X L s).val.app (op U)).hom := by
  intro g
  obtain ⟨v, hv⟩ := hunit.exists_left_inv
  obtain ⟨c, hc⟩ : ∃ c : (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op U), c * b =
      show (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.sheaf).obj.obj (op U) from g :=
    ⟨(show (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op U) from g) * v, by rw [mul_assoc, hv, mul_one]⟩
  refine (exists_denominatorIdeal_inclusion_app_eq_iff X L s U g).mpr ⟨c • t, ?_⟩
  rw [← meromorphicSectionMul_app_mul_eq X L s U b c t heq, hc]

/-- `AlgebraicGeometry.surjective_denominatorIdealIota_app` with the denominator given over a
larger open set and the open set taken inside its basic open set. -/
theorem surjective_denominatorIdealIota_app_of_le_basicOpen {V : X.Opens} (b : Γ(X, V))
    (t : L.val.obj (op V))
    (ht : ((meromorphicSectionMul X L s).val.app (op V)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op V)).hom t)
    {U : X.Opens} (hUb : U ≤ X.basicOpen b) :
    Function.Surjective ((denominatorIdealι X L s).val.app (op U)).hom :=
  surjective_denominatorIdealIota_app X L s U
    (X.presheaf.map (homOfLE (hUb.trans (X.basicOpen_le b))).op b)
    (isUnit_presheaf_map_of_le_basicOpen X b hUb _)
    (L.val.restrictₛₗ (homOfLE (hUb.trans (X.basicOpen_le b))).op t)
    (meromorphicSectionMul_app_res_eq X L s (hUb.trans (X.basicOpen_le b)) b t ht)

/-- If a map of sheaves of modules is surjective on sections over every open inside
`V y ⊓ X.basicOpen (c y)`, for affine neighbourhoods `V y` of `y` and nonzerodivisors `c y`, then
its cokernel is supported on a closed nowhere dense set. -/
private theorem exists_isClosed_isNowhereDense_supp_cokernel_subset {M N : SheafOfModules.{u}
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf)}
    (f : M ⟶ N) (V : X → X.Opens) (c : ∀ x, Γ(X, V x)) (hxV : ∀ x, x ∈ V x)
    (hVaff : ∀ x, IsAffineOpen (V x)) (hc : ∀ x, c x ∈ (Γ(X, V x))⁰)
    (hsurj : ∀ (y : X) (U : X.Opens), U ≤ V y ⊓ X.basicOpen (c y) →
      Function.Surjective ((f.val.app (op U)).hom)) :
    ∃ T : Set X, IsClosed T ∧ IsNowhereDense T ∧
      (⟨(cokernel f).val, (cokernel f).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆ T := by
  refine ⟨((⨆ y : X, (V y ⊓ X.basicOpen (c y)) : X.Opens) : Set X)ᶜ,
    (Opens.isOpen _).isClosed_compl, ?_, ?_⟩
  · refine isNowhereDense_compl_of_dense X (Opens.isOpen _) fun y => ?_
    exact closure_mono
      (fun z hz => le_iSup (fun x : X => V x ⊓ X.basicOpen (c x)) y hz)
      (mem_closure_inf_basicOpen_of_mem_nonZeroDivisors X (hVaff y) (hc y) (hxV y))
  · refine supp_cokernel_subset X f _ fun x hx => ?_
    rw [Set.notMem_compl_iff] at hx
    obtain ⟨y, hy⟩ := Opens.mem_iSup.mp hx
    exact ⟨V y ⊓ X.basicOpen (c y), hy, hsurj y⟩

/-- **Stacks Project, Tag 02P0**, the support of the first cokernel. For an invertible sheaf of
modules `L` and a meromorphic section `s` of `L`, the cokernel of the inclusion of the ideal of
denominators of `s` in the structure sheaf is supported on a closed nowhere dense subset.

The set is the complement of the union, over the points of `X`, of the part of the affine
neighbourhood produced by
`AlgebraicGeometry.exists_isAffineOpen_nhds_isNowhereDense_denominator` on which the
denominator `b` found there is invertible. On each such open set the whole structure sheaf
consists of denominators, because `b` lies in the ideal and is a unit, so the cokernel has no
sections there; and the union is dense because the vanishing locus of a nonzerodivisor on an
affine open is nowhere dense. -/
@[stacks 02P0 "support of the first cokernel"]
theorem denominatorIdeal_inclusion_support
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) :
    ∃ T : Set X, IsClosed T ∧ IsNowhereDense T ∧
      (⟨(cokernel (denominatorIdealι X L s)).val,
        (cokernel (denominatorIdealι X L s)).isSheaf⟩ :
          RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆ T := by
  choose V hxV hVaff b hb hnd t ht using fun x : X =>
    exists_isAffineOpen_nhds_isNowhereDense_denominator X L hL s x
  exact exists_isClosed_isNowhereDense_supp_cokernel_subset X (denominatorIdealι X L s) V b hxV
    hVaff hb fun y U hU =>
      surjective_denominatorIdealIota_app_of_le_basicOpen X L s (b y) (t y) (ht y)
        (hU.trans inf_le_right)

/-- `AlgebraicGeometry.oneTmulMeromorphicSectionSheaf_app_apply` on a scalar multiple, with the
multiplicand rewritten along the way. -/
theorem oneTmulMeromorphicSectionSheaf_app_smul (V : (Opens X)ᵒᵖ)
    (c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj V)
    {y y' : L.val.obj V} (hy : y = y') :
    ((oneTmulMeromorphicSectionSheaf X L).app V).hom (c • y)
      = ((toMeromorphicSectionSheafAsModule X L).val.app V).hom (c • y') := by
  subst hy
  exact oneTmulMeromorphicSectionSheaf_app_apply X L V _

/-- **An invertible sheaf of modules on a scheme has a single generator near every point**, one
whose restriction to every smaller open generates there as well. This is the converse half of
Tag 0B8M, read in the spelling the ideal of denominators is stated with; it strengthens
`AlgebraicGeometry.exists_nhds_forall_surjective_smul_of_isInvertible`, whose generators are
chosen separately on each open. -/
theorem exists_nhds_section_forall_surjective_smul_of_isInvertible
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) (x : X) :
    ∃ (W : X.Opens) (_ : x ∈ W) (g : L.val.obj (op W)),
      ∀ (V : X.Opens) (hVW : V ≤ W), Function.Surjective
        (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf).obj.obj
          (op V) => c • (L.val.restrictₛₗ (homOfLE hVW).op g)) := by
  have hloc : ∀ y : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace y) :=
    fun y => X.isLocalRing y
  have hinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  obtain ⟨W, hxW, g, hbij⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (X := X.toRingedSpace) L x
  exact ⟨W, hxW, g, fun V hVW => (hbij V hVW).surjective⟩

/-- A generator of `L` and a representative of `s` in the presheaf `K_X ⊗_{𝒪_X} L`, the second
on a neighbourhood inside the domain of the first. -/
theorem exists_nhds_generator_and_representative
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) (x : X) :
    ∃ (W₀ : X.Opens) (g : L.val.obj (op W₀)),
      (∀ (V : X.Opens) (hVW : V ≤ W₀), Function.Surjective
        (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf).obj.obj
          (op V) => c • (L.val.restrictₛₗ (homOfLE hVW).op g))) ∧
      ∃ (W : X.Opens) (_ : W ≤ W₀), x ∈ W ∧
        ∃ z : (meromorphicTensorPresheaf X L).obj (op W),
          ((toSheafifyMeromorphicTensor X L).app (op W)).hom z = s.eval (op W) := by
  have h1 := exists_nhds_section_forall_surjective_smul_of_isInvertible X L hL x
  have h2 := exists_nhds_toSheafifyMeromorphicTensor_app_eq X L s x
  obtain ⟨W₀, hxW₀, g₀, hsurj⟩ := h1
  obtain ⟨W₁, hxW₁, z, hz⟩ := h2
  have h3 := toSheafifyMeromorphicTensor_app_restrict_eq X L s
    (inf_le_right : W₀ ⊓ W₁ ≤ W₁) z hz
  exact ⟨W₀, g₀, hsurj, W₀ ⊓ W₁, inf_le_left, ⟨hxW₀, hxW₁⟩, _, h3⟩

/-- **The local denominator lemma with its numerator and its generator.** Around every point of
a scheme there is an *affine* open `V` carrying a section `g` of `L` which generates the
sections of `L` over every open inside `V`, a nonzerodivisor `b ∈ Γ(X, V)` and a section
`a ∈ Γ(X, V)` with `b · s = a · g`. This is the normal form `s = a/b` that the proof of Tag
02P0 reduces to; it refines
`AlgebraicGeometry.exists_isAffineOpen_nhds_toMeromorphicSectionSheafAsModule_eq` by keeping
the numerator and the generator. -/
theorem exists_isAffineOpen_nhds_denominator_numerator
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧ ∃ g : L.val.obj (op V),
      (∀ (U : X.Opens) (hUV : U ≤ V), Function.Surjective
        (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf).obj.obj
          (op U) => c • (L.val.restrictₛₗ (homOfLE hUV).op g))) ∧
      ∃ b ∈ (Γ(X, V))⁰,
        ∃ a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf).obj.obj (op V),
          ((meromorphicSectionMul X L s).val.app (op V)).hom b
            = ((toMeromorphicSectionSheafAsModule X L).val.app (op V)).hom (a • g) := by
  have h0 := exists_nhds_generator_and_representative X L s hL x
  obtain ⟨W₀, g₀, hsurj, W, hWW₀, hxW, z, hz⟩ := h0
  have h1 := Stacks.Meromorphic.exists_forall_smul_eval_eq_oneTmul
    (Opens.grothendieckTopology X) X.toTotalQuotientSheaf.hom
    (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).property
    L.val (L.val.restrictₛₗ (homOfLE hWW₀).op g₀) (hsurj W hWW₀) z s hz
  obtain ⟨u, hgen⟩ := h1
  have h2 := X.exists_isAffineOpen_nhds_isFraction_totalQuotientSheaf (U := W) u hxW
  obtain ⟨V, hVW, hVaff, hxV, a, b, hb, hbu, heq⟩ := h2
  refine ⟨V, hxV, hVaff, L.val.restrictₛₗ (homOfLE (hVW.trans hWW₀)).op g₀,
    fun U hUV => ?_, b, hb, a, ?_⟩
  · rw [PresheafOfModules.restrictₛₗ_restrictₛₗ]
    exact hsurj U (hUV.trans (hVW.trans hWW₀))
  · have h3 := hgen (op V) (homOfLE hVW).op b a heq
    have hrest : ((L.val.map (homOfLE hVW).op).hom
          (L.val.restrictₛₗ (homOfLE hWW₀).op g₀) : L.val.obj (op V))
        = L.val.restrictₛₗ (homOfLE (hVW.trans hWW₀)).op g₀ :=
      PresheafOfModules.restrictₛₗ_restrictₛₗ L.val _ _ g₀
    refine ((meromorphicSectionMul_val_app X L s (op V) b).trans
      ((Stacks.Meromorphic.unitHomEquiv_symm_val_app_apply _ _ s (op V) _).trans
        (h3.trans ?_)))
    exact oneTmulMeromorphicSectionSheaf_app_smul X L (op V) a hrest

/-- For a regular meromorphic section, multiplication by it is injective on the sections of the
structure sheaf over every open set. -/
theorem meromorphicSectionMul_app_injective
    (hs : IsRegularMeromorphicSection X.sheaf L s) (V : (Opens X)ᵒᵖ) :
    Function.Injective ((meromorphicSectionMul X L s).val.app V).hom := fun p q hpq =>
  toTotalQuotientSheaf_app_injective X V.unop
    (SheafOfModules.app_injective_of_mono hs V
      ((meromorphicSectionMul_val_app X L s V p).symm.trans
        (hpq.trans (meromorphicSectionMul_val_app X L s V q))))

/-- **The numerator of a regular meromorphic section is a nonzerodivisor.** If `b` is a
nonzerodivisor with `b · s = a · g`, then `a` is a nonzerodivisor: for `c · a = 0` the section
`c · b` multiplies `s` to zero, so `c · b = 0` by regularity and `c = 0` because `b` is a
nonzerodivisor. This is the only use of regularity in this file, and it is the step the source
records by saying that `a` and `b` may both be taken to be nonzerodivisors. -/
theorem numerator_mem_nonZeroDivisors (hs : IsRegularMeromorphicSection X.sheaf L s)
    {V : X.Opens} {b : Γ(X, V)} (hb : b ∈ (Γ(X, V))⁰)
    {a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op V)}
    {g : L.val.obj (op V)}
    (heq : ((meromorphicSectionMul X L s).val.app (op V)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op V)).hom (a • g)) :
    (show Γ(X, V) from a) ∈ (Γ(X, V))⁰ := by
  refine mem_nonZeroDivisors_iff_right.mpr fun c hc => ?_
  refine mem_nonZeroDivisors_iff_right.mp hb c ?_
  refine meromorphicSectionMul_app_injective X L s hs (op V) ?_
  have h3 : ((show (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
    X.sheaf).obj.obj
        (op V) from c) • (a • g) : L.val.obj (op V)) = 0 := by
    rw [smul_smul,
      show (show (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.sheaf).obj.obj
        (op V) from c) * a = 0 from hc, zero_smul]
  refine (meromorphicSectionMul_app_mul_eq X L s V b (show (Stacks.Sheaves.Differentials.ringSheaf
    (J := Opens.grothendieckTopology X) X.sheaf).obj.obj (op V) from c) _ heq).trans ?_
  rw [h3, map_zero]
  exact (map_zero _).symm

/-- A section of `L` over `V` is the product of `s` with a denominator exactly when it is in the
image of multiplication by `s` on the ideal of denominators. This is the second-projection
companion of `AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff`. -/
theorem exists_denominatorIdealMul_app_eq_iff (V : Opens X) (t : L.val.obj (op V)) :
    (∃ d : (denominatorIdeal X L s).val.obj (op V),
      (denominatorIdealMul X L s).val.app (op V) d = t) ↔
    (∃ f : (SheafOfModules.unit
        (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.sheaf)).val.obj (op V),
      (meromorphicSectionMul X L s).val.app (op V) f =
        (toMeromorphicSectionSheafAsModule X L).val.app (op V) t) :=
  exists_map_pullback_snd_eq_iff
    (SheafOfModules.evaluation
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf) (op V))
    (meromorphicSectionMul X L s) (toMeromorphicSectionSheafAsModule X L) t

/-- **Where the numerator is invertible, multiplication by the section is surjective on the
sections of the ideal of denominators.** If `b · s = a · g` with `g` a generator of `L(U)` and
`a` a unit, then every section of `L` over `U` is `d · s` for a denominator `d`: for
`l = e · g` take `d = e a⁻¹ b`. -/
theorem surjective_denominatorIdealMul_app (U : Opens X)
    (b : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op U))
    (a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op U))
    (hau : IsUnit a) (g : L.val.obj (op U))
    (hg : Function.Surjective
      (fun c : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.sheaf).obj.obj (op U)
        => c • g))
    (heq : ((meromorphicSectionMul X L s).val.app (op U)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom (a • g)) :
    Function.Surjective ((denominatorIdealMul X L s).val.app (op U)).hom := by
  intro l
  obtain ⟨e, he⟩ := hg l
  obtain ⟨v, hv⟩ := hau.exists_left_inv
  refine (exists_denominatorIdealMul_app_eq_iff X L s U l).mpr ⟨e * v * b, ?_⟩
  have h3 : ((e * v) • (a • g) : L.val.obj (op U)) = l := by
    rw [smul_smul, mul_assoc, hv, mul_one]
    exact he
  rw [← h3]
  exact meromorphicSectionMul_app_mul_eq X L s U b (e * v) _ heq

/-- `AlgebraicGeometry.meromorphicSectionMul_app_res_eq` in the normal form `b · s = a · g`:
restricting the equation multiplies the restricted generator by the restricted numerator. -/
theorem meromorphicSectionMul_app_res_smul_eq {V U : X.Opens} (hUV : U ≤ V) (b : Γ(X, V))
    (a : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.sheaf).obj.obj (op V))
    (g : L.val.obj (op V))
    (ht : ((meromorphicSectionMul X L s).val.app (op V)).hom b
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op V)).hom (a • g)) :
    ((meromorphicSectionMul X L s).val.app (op U)).hom
        (X.presheaf.map (homOfLE hUV).op b)
      = ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom
          (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.sheaf).obj.map
              (homOfLE hUV).op a) • (L.val.restrictₛₗ (homOfLE hUV).op g)) :=
  (meromorphicSectionMul_app_res_eq X L s hUV b (a • g) ht).trans
    (congrArg (fun y : L.val.obj (op U) =>
        ((toMeromorphicSectionSheafAsModule X L).val.app (op U)).hom y)
      (PresheafOfModules.map_smul L.val (homOfLE hUV).op a g))

/-- **Stacks Project, Tag 02P0**, the support of the second cokernel. For an invertible sheaf of
modules `L` and a *regular* meromorphic section `s` of `L`, the cokernel of multiplication by
`s` on the ideal of denominators of `s` is supported on a closed nowhere dense subset.

The set is the complement of the union, over the points of `X`, of the part of the affine
neighbourhood produced by
`AlgebraicGeometry.exists_isAffineOpen_nhds_denominator_numerator` on which the numerator `a`
found there is invertible. On each such open set every section of `L` is `d · s` for a
denominator `d`, because `L` is generated by `g` and `b · s = a · g` with `a` a unit; and the
union is dense because `a` is a nonzerodivisor
(`AlgebraicGeometry.numerator_mem_nonZeroDivisors`, which is where regularity of `s` enters)
and the vanishing locus of a nonzerodivisor on an affine open is nowhere dense. -/
@[stacks 02P0 "support of the second cokernel"]
theorem denominatorIdeal_section_support
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    ∃ T : Set X, IsClosed T ∧ IsNowhereDense T ∧
      (⟨(cokernel (denominatorIdealMul X L s)).val,
        (cokernel (denominatorIdealMul X L s)).isSheaf⟩ :
          RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆ T := by
  choose V hxV hVaff g hgsurj b hb a heq using fun x : X =>
    exists_isAffineOpen_nhds_denominator_numerator X L s hL x
  have ha : ∀ x : X, (show Γ(X, V x) from a x) ∈ (Γ(X, V x))⁰ := fun x =>
    numerator_mem_nonZeroDivisors X L s hs (hb x) (heq x)
  refine exists_isClosed_isNowhereDense_supp_cokernel_subset X (denominatorIdealMul X L s) V
    (fun x => show Γ(X, V x) from a x) hxV hVaff ha fun y U hU => ?_
  exact surjective_denominatorIdealMul_app X L s U
    (X.presheaf.map (homOfLE (hU.trans inf_le_left)).op (b y))
    (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).obj.map
      (homOfLE (hU.trans inf_le_left)).op) (a y))
    (isUnit_presheaf_map_of_le_basicOpen X (show Γ(X, V y) from a y) (hU.trans inf_le_right)
      (hU.trans inf_le_left))
    (L.val.restrictₛₗ (homOfLE (hU.trans inf_le_left)).op (g y))
    (hgsurj y U (hU.trans inf_le_left))
    (meromorphicSectionMul_app_res_smul_eq X L s (hU.trans inf_le_left)
      (b y) (a y) (g y) (heq y))

end AlgebraicGeometry
