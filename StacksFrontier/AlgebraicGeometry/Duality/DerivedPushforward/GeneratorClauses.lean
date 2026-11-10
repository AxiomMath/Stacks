module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.OpenImmersionConservative
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.PullbackGenerator
public import StacksFrontier.CategoryTheory.Triangulated.GeneratorAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The conditions of the remark hold for an affine morphism, an open immersion, and composites

[Stacks, Tag 0BQT] records three equivalent conditions on a morphism `f : X ⟶ Y` of
quasi-compact and quasi-separated schemes, relative to a generator `E` of `D_QCoh(𝒪_Y)`:

1. an object `K` of `D_QCoh(𝒪_X)` is zero as soon as `Rf_*K` is zero;
2. `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms;
3. `Lf^*E` is a generator of `D_QCoh(𝒪_X)`.

The equivalence is `Stacks.Duality.DerivedPushforward.tfae_isZero_quasiCoherentDerivedPushforward`.
The source then records that the conditions *hold* when `f` is affine, when `f` is an open
immersion, and when `f` is a composition of such. This file proves that clause, for the class of
morphisms `(IsAffineHom ⊔ IsOpenImmersion).multiplicativeClosure`, which is exactly the finite
composites of affine morphisms and open immersions.

For the two generating cases, condition (1) is proved and (3) follows by the equivalence:

* for an affine morphism,
  `Stacks.Duality.isZero_homology_of_isZero_homology_derivedPushforward_of_isAffineHom`;
* for an open immersion,
  `Stacks.Duality.DerivedPushforward.isZero_of_isZero_derivedPushforward_of_isOpenImmersion`.

The composite is an induction on the multiplicative closure, carried out in the form (3): a
generator pulls back to a generator along each factor, and
`Stacks.Duality.derivedPullbackCompIso` identifies the iterated pullback with the pullback along
the composite. The one real point is that the source's hypotheses are about the *endpoints* `X`
and `Y`, while a factorization `f = f' ≫ g` passes through an intermediate scheme on which
nothing is assumed. The induction is therefore strengthened: `f` is factored as `f_W ≫ i` with
`i : W ⟶ Y` an open immersion onto a quasi-compact open, and the conclusion is asserted for
`f_W : X ⟶ W`. Each inner factor is then replaced by its restriction to a quasi-compact open
subscheme, which is quasi-compact and quasi-separated because `W` is — so no hypothesis on an
intermediate scheme is ever needed.

## Main results

* `isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isAffineHom` and
  `..._of_isOpenImmersion`, in the namespace `Stacks.Duality.DerivedPushforward` — condition (3)
  in the two generating cases.
* `Stacks.Duality.DerivedPushforward.conditions_of_multiplicativeClosure` —
  **[Stacks, Tag 0BQT]**, the clause that the three conditions hold when `f` is affine, when `f`
  is an open immersion, and when `f` is a composition of such.

## Implementation notes

*Quasi-compactness and quasi-separatedness are carried on the schemes, not on the morphism.* The
source's hypothesis is that `X` and `Y` are quasi-compact and quasi-separated schemes; from
`[CompactSpace X]`, `[QuasiSeparatedSpace X]` and `[QuasiSeparatedSpace Y]` Mathlib's
`AlgebraicGeometry.quasiCompact_of_compactSpace` and
`AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace` supply `QuasiCompact f` and
`QuasiSeparated f`, which with `[CompactSpace Y]` are the hypotheses under which the three
conditions are stated.

*The model of the derived categories* is the locally small one, as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/PullbackGenerator.lean`.

## References

* [Stacks Project, Tag 0BQT](https://stacks.math.columbia.edu/tag/0BQT)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality.DerivedPushforward

/-! ### Transport along an isomorphism, and the composition isomorphism for `Lf^*` -/

/-- A weak generator stays one along an isomorphism: an isomorphism is in particular a
retraction, and `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_of_retract` applies. -/
theorem isWeakTriangulatedGenerator_of_iso {C : Type*} [Category C] [Preadditive C]
    [HasShift C ℤ] {E F : C} (e : E ≅ F)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton F).IsWeakTriangulatedGenerator :=
  ObjectProperty.isWeakTriangulatedGenerator_of_retract
    ⟨e.hom, e.inv, e.hom_inv_id⟩ hE

/-- **`Lf^*(Lg^*E) ≅ L(f ≫ g)^*E` on the quasi-coherent derived categories.** This is
`Stacks.Duality.derivedPullbackCompIso` read on the full subcategories of complexes with
quasi-coherent cohomology, which it preserves. -/
def quasiCoherentDerivedPullbackCompObjIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : Stacks.Duality.quasiCoherentDerivedCategory Z) :
    (Stacks.Duality.quasiCoherentDerivedPullback' f).obj
        ((Stacks.Duality.quasiCoherentDerivedPullback' g).obj E) ≅
      (Stacks.Duality.quasiCoherentDerivedPullback' (f ≫ g)).obj E :=
  (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).isoMk
    ((Stacks.Duality.derivedPullbackCompIso f g).app E.obj)

/-! ### The two generating cases -/

section Affine

variable {X Y : Scheme.{u}} [CompactSpace Y]

/-- **Condition (1) of [Stacks, Tag 0BQT] for an affine morphism**, on `D_QCoh`. This is
`Stacks.Duality.isZero_homology_of_isZero_homology_derivedPushforward_of_isAffineHom` in every
degree, read through the inclusion `D_QCoh(𝒪_X) ⟶ D(𝒪_X)`, which is additive and fully faithful
and so both preserves and reflects zero objects; an object of the derived category with no
cohomology sheaves is a zero object. -/
theorem isZero_of_isZero_qcqsRestrictedDerivedPushforward_of_isAffineHom (f : X ⟶ Y)
    [IsAffineHom f] (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (h : IsZero ((qcqsRestrictedDerivedPushforward f).obj K)) : IsZero K :=
  IsZero.of_full_of_faithful_of_isZero
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι K
    (Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj K.obj fun n =>
      Stacks.Duality.isZero_homology_of_isZero_homology_derivedPushforward_of_isAffineHom f K.obj
        K.property n ((DerivedCategory.homologyFunctor Y.Modules n).map_isZero
          (Functor.map_isZero (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
            (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι h)))

/-- **Condition (3) of [Stacks, Tag 0BQT] for an affine morphism.** For `f : X ⟶ Y` an affine
morphism of quasi-compact and quasi-separated schemes, `Lf^*` carries a weak generator of
`D_QCoh(𝒪_Y)` to a weak generator of `D_QCoh(𝒪_X)`. -/
theorem isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isAffineHom (f : X ⟶ Y)
    [IsAffineHom f] (E : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton
        ((Stacks.Duality.quasiCoherentDerivedPullback' f).obj E)
      ).IsWeakTriangulatedGenerator :=
  ((tfae_isZero_quasiCoherentDerivedPushforward f E hE).out 1 3).1
    (isZero_of_isZero_qcqsRestrictedDerivedPushforward_of_isAffineHom f)

end Affine

section OpenImmersion

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **Condition (1) of [Stacks, Tag 0BQT] for an open immersion**, on `D_QCoh`. -/
theorem isZero_of_isZero_qcqsRestrictedDerivedPushforward_of_isOpenImmersion (f : X ⟶ Y)
    [IsOpenImmersion f] (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (h : IsZero ((qcqsRestrictedDerivedPushforward f).obj K)) : IsZero K :=
  IsZero.of_full_of_faithful_of_isZero
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι K
    (isZero_of_isZero_derivedPushforward_of_isOpenImmersion f K.obj
      (Functor.map_isZero (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι h))

/-- **Condition (3) of [Stacks, Tag 0BQT] for an open immersion.** For `f : X ⟶ Y` an open
immersion of quasi-compact and quasi-separated schemes, `Lf^*` carries a weak generator of
`D_QCoh(𝒪_Y)` to a weak generator of `D_QCoh(𝒪_X)`. -/
theorem isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isOpenImmersion (f : X ⟶ Y)
    [IsOpenImmersion f] (E : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton
        ((Stacks.Duality.quasiCoherentDerivedPullback' f).obj E)
      ).IsWeakTriangulatedGenerator :=
  ((tfae_isZero_quasiCoherentDerivedPushforward f E hE).out 1 3).1
    (isZero_of_isZero_qcqsRestrictedDerivedPushforward_of_isOpenImmersion f)

end OpenImmersion

/-! ### The composite -/

/-- Every morphism out of a quasi-compact scheme into an open `U` of `Y` factors through a
quasi-compact open of `Y` contained in `U`: cover the (compact) image by affine opens contained
in `U` and take the supremum of a finite subcover. -/
theorem exists_compactSpace_opens_range_subset {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (U : Y.Opens) (hU : ∀ x, f x ∈ U) :
    ∃ V : Y.Opens, CompactSpace V.toScheme ∧ Set.range f ⊆ V ∧ V ≤ U := by
  classical
  choose W hW using fun x => exists_isAffineOpen_mem_and_subset (hU x)
  have hcover : Set.range f ⊆ ⋃ x, (W x : Set Y) := by
    rintro y ⟨x, rfl⟩
    exact Set.mem_iUnion.mpr ⟨x, (hW x).2.1⟩
  obtain ⟨t, ht⟩ := (isCompact_range f.continuous).elim_finite_subcover
    (fun x => (W x : Set Y)) (fun x => (W x).2) hcover
  let V : Y.Opens := ⨆ x : t, W x.1
  have hrange : Set.range f ⊆ V := by
    intro y hy
    obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (ht hy)
    simpa [V, TopologicalSpace.Opens.coe_iSup] using
      (Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hx⟩ : y ∈ ⋃ j : t, (W j.1 : Set Y))
  have hVcompact : IsCompact (V : Set Y) := by
    simpa [V, TopologicalSpace.Opens.coe_iSup] using
      (isCompact_iUnion fun x : t => (hW x.1).1.isCompact)
  have hVU : V ≤ U := iSup_le fun x => (hW x.1).2.2
  exact ⟨V, isCompact_iff_compactSpace.mp hVcompact, hrange, hVU⟩

/-- Condition (3) of [Stacks, Tag 0BQT] for `f_W : X ⟶ W`, where `f = f_W ≫ i` is affine or an
open immersion and `i` is an open immersion: `f_W` is a base change of `f`. -/
private theorem isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_fac
    {X Y W : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace W]
    [QuasiSeparatedSpace W]
    (f : X ⟶ Y) (hf : IsAffineHom f ∨ IsOpenImmersion f) (i : W ⟶ Y) [IsOpenImmersion i]
    (fW : X ⟶ W) (hfac : fW ≫ i = f) (E : Stacks.Duality.quasiCoherentDerivedCategory W)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton
      ((Stacks.Duality.quasiCoherentDerivedPullback' fW).obj E)).IsWeakTriangulatedGenerator := by
  have hrange : Set.range f ⊆ Set.range i :=
    Set.range_subset_iff.mpr fun x => ⟨fW x, by simpa using congrArg (fun q => q x) hfac⟩
  have heq : fW = IsOpenImmersion.lift i f hrange :=
    (cancel_mono i).1 (by rwa [IsOpenImmersion.lift_fac])
  have hp := IsOpenImmersion.isPullback_lift_id f i hrange
  rcases hf with hf | hf
  · have : IsAffineHom fW := by
      rw [heq]
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip hf
    exact isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isAffineHom fW E hE
  · have : IsOpenImmersion fW := by
      rw [heq]
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip hf
    exact isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isOpenImmersion fW E hE

/-- If `f_W ≫ i = f ≫ g` with `i` an open immersion, then `f` lands in the open `g⁻¹(i(W))`. -/
private theorem apply_mem_preimage_opensRange {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : W ⟶ Z) [IsOpenImmersion i] (fW : X ⟶ W) (hfac : fW ≫ i = f ≫ g) (x : X) :
    f x ∈ g ⁻¹ᵁ i.opensRange :=
  ⟨fW x, by simpa using congrArg (fun q : X ⟶ Z => q x) hfac⟩

/-- If `V ⊆ Y` is open with `V ⟶ Y ⟶ Z` factoring as `gV ≫ i` through an open immersion `i`, and
`f` lands in `V`, then `f_W` factors as `X ⟶ V ⟶ W` compatibly with `f`. -/
private theorem exists_lift_comp_eq {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion i] (fW : X ⟶ W) (hfac : fW ≫ i = f ≫ g) (V : Y.Opens)
    (gV : V.toScheme ⟶ W) (hgfac : V.ι ≫ g = gV ≫ i) (hV : ∀ x, f x ∈ V) :
    ∃ fV : X ⟶ V.toScheme, fV ≫ V.ι = f ∧ fV ≫ gV = fW := by
  have hRange : Set.range f ⊆ Set.range V.ι := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨f x, hV x⟩, rfl⟩
  have hfV := IsOpenImmersion.lift_fac V.ι f hRange
  refine ⟨IsOpenImmersion.lift V.ι f hRange, hfV, (cancel_mono i).1 ?_⟩
  rw [Category.assoc, ← hgfac, ← Category.assoc, hfV, hfac]

/-- For `g` affine and `f_W ≫ i = f ≫ g` with `i : W ⟶ Z` an open immersion and `W`
quasi-compact and quasi-separated, `f_W` factors through the open `U = g⁻¹(i(W))` of `Y` as
`X ⟶ U ⟶ W`, with `U ⟶ W` affine and `U` quasi-compact and quasi-separated. -/
private theorem exists_opens_factorization_of_isAffineHom {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [hg : IsAffineHom g] (i : W ⟶ Z) [IsOpenImmersion i] [CompactSpace W]
    [QuasiSeparatedSpace W] (fW : X ⟶ W) (hfac : fW ≫ i = f ≫ g) :
    ∃ (U : Y.Opens) (fU : X ⟶ U.toScheme) (gW : U.toScheme ⟶ W), IsAffineHom gW ∧
      CompactSpace U.toScheme ∧ QuasiSeparatedSpace U.toScheme ∧ fU ≫ U.ι = f ∧
      fU ≫ gW = fW := by
  let O := i.opensRange
  let U := g ⁻¹ᵁ O
  let gU : U.toScheme ⟶ O.toScheme := g.resLE O U le_rfl
  have : IsAffineHom gU := by
    dsimp only [gU]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict g O).flip hg
  let gW : U.toScheme ⟶ W := gU ≫ i.isoOpensRange.inv
  have hgfac : U.ι ≫ g = gW ≫ i := by
    calc U.ι ≫ g = gU ≫ O.ι := (g.resLE_comp_ι (U := O) (V := U) le_rfl).symm
      _ = (gU ≫ i.isoOpensRange.inv) ≫ i := by
          rw [Category.assoc, i.isoOpensRange_inv_comp]
  obtain ⟨fU, hfU, hfUW⟩ := exists_lift_comp_eq f g i fW hfac U gW hgfac
    (apply_mem_preimage_opensRange f g i fW hfac)
  exact ⟨U, fU, gW, inferInstance, QuasiCompact.compactSpace_of_compactSpace gW,
    quasiSeparatedSpace_of_quasiSeparated gW, hfU, hfUW⟩

/-- For `g` an open immersion and `f_W ≫ i = f ≫ g` with `i : W ⟶ Z` an open immersion, `X`
quasi-compact and `W` quasi-separated, `f_W` factors through a quasi-compact open `V` of `Y` as
`X ⟶ V ⟶ W`, with `V ⟶ W` an open immersion and `V` quasi-separated. -/
private theorem exists_opens_factorization_of_isOpenImmersion {X Y Z W : Scheme.{u}}
    [CompactSpace X] (f : X ⟶ Y) (g : Y ⟶ Z) [hg : IsOpenImmersion g] (i : W ⟶ Z)
    [IsOpenImmersion i] [QuasiSeparatedSpace W] (fW : X ⟶ W) (hfac : fW ≫ i = f ≫ g) :
    ∃ (V : Y.Opens) (fV : X ⟶ V.toScheme) (gV : V.toScheme ⟶ W), IsOpenImmersion gV ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧ fV ≫ V.ι = f ∧
      fV ≫ gV = fW := by
  let O := i.opensRange
  let U := g ⁻¹ᵁ O
  obtain ⟨V, hVc, hVrange, hVU⟩ := exists_compactSpace_opens_range_subset f U
    (apply_mem_preimage_opensRange f g i fW hfac)
  have hRangeVG : Set.range (V.ι ≫ g) ⊆ Set.range i := by
    rintro z ⟨v, rfl⟩
    refine ⟨i.isoOpensRange.inv ⟨g v.1, hVU v.2⟩, ?_⟩
    change i (i.isoOpensRange.inv ⟨g v.1, hVU v.2⟩) = O.ι ⟨g v.1, hVU v.2⟩
    exact congrArg (fun q => q ⟨g v.1, hVU v.2⟩) i.isoOpensRange_inv_comp
  let gV : V.toScheme ⟶ W := IsOpenImmersion.lift i (V.ι ≫ g) hRangeVG
  have hgfac : V.ι ≫ g = gV ≫ i := (IsOpenImmersion.lift_fac i (V.ι ≫ g) hRangeVG).symm
  have : IsOpenImmersion gV := by
    dsimp only [gV]
    infer_instance
  obtain ⟨fV, hfV, hfVW⟩ := exists_lift_comp_eq f g i fW hfac V gV hgfac
    fun x => hVrange ⟨x, rfl⟩
  exact ⟨V, fV, gV, inferInstance, hVc, quasiSeparatedSpace_of_quasiSeparated gV, hfV, hfVW⟩

/-- **Condition (3) of [Stacks, Tag 0BQT] for a finite composite of affine morphisms and open
immersions, in the strengthened form the induction needs.** The morphism whose multiplicative
closure membership is being used is `f : X ⟶ Y`; the conclusion is asserted not for `f` but for a
factorization `f = f_W ≫ i` through an open immersion `i : W ⟶ Y` with `W` quasi-compact and
quasi-separated. This is what makes the induction go through: an inner factor is replaced by its
restriction to a quasi-compact open subscheme of `W`, which inherits quasi-compactness and
quasi-separatedness from `W`, so no hypothesis on an intermediate scheme of the factorization is
needed. -/
theorem isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_openFactorization :
    ∀ {X Y : Scheme.{u}} (f₀ f : X ⟶ Y)
      (_ : ((@IsAffineHom) ⊔ (@IsOpenImmersion) :
        MorphismProperty (Scheme.{u})).multiplicativeClosure f) (_ : f = f₀)
      {W : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
      (fW : X ⟶ W) (_ : fW ≫ i = f₀)
      (_ : CompactSpace X) (_ : QuasiSeparatedSpace X)
      (_ : CompactSpace W) (_ : QuasiSeparatedSpace W)
      (E : Stacks.Duality.quasiCoherentDerivedCategory W),
      (ObjectProperty.singleton E).IsWeakTriangulatedGenerator →
      (ObjectProperty.singleton
        ((Stacks.Duality.quasiCoherentDerivedPullback' fW).obj E)
        ).IsWeakTriangulatedGenerator := by
  intro X Y f₀ f hf hEq W i hi fW hfac hXc hXq hWc hWq E hE
  induction hf generalizing W hi hWc hWq E hE with
  | of f hf =>
      cases hEq
      exact isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_fac f hf i fW hfac E hE
  | id X =>
      cases hEq
      exact isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_fac (𝟙 X)
        (Or.inr inferInstance) i fW hfac E hE
  | @comp_of X Y Z f g hf hg ih =>
      cases hEq
      rcases hg with hg | hg
      · obtain ⟨U, fU, gW, _, hUc, hUq, hfU, hpEq⟩ :=
          exists_opens_factorization_of_isAffineHom (hg := hg) f g i fW hfac
        rw [← hpEq]
        exact isWeakTriangulatedGenerator_of_iso (quasiCoherentDerivedPullbackCompObjIso fU gW E)
          (ih f rfl U.ι fU hfU hXc hXq hUc hUq _
            (isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isAffineHom gW E hE))
      · obtain ⟨V, fV, gV, _, hVc, hVq, hfV, hpEq⟩ :=
          exists_opens_factorization_of_isOpenImmersion (hg := hg) f g i fW hfac
        rw [← hpEq]
        exact isWeakTriangulatedGenerator_of_iso (quasiCoherentDerivedPullbackCompObjIso fV gV E)
          (ih f rfl V.ι fV hfV hXc hXq hVc hVq _
            (isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_isOpenImmersion gV E hE))

/-! ### The clause -/

/-- **[Stacks, Tag 0BQT]: the three conditions hold when `f` is affine, when `f` is an open
immersion, and when `f` is a composition of such.** Let `f : X ⟶ Y` be a finite composite of
affine morphisms and open immersions between quasi-compact and quasi-separated schemes, and let
`E` be a weak generator of `D_QCoh(𝒪_Y)`. Then

1. every object `K` of `D_QCoh(𝒪_X)` with `Rf_*K` zero is itself zero;
2. `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` reflects isomorphisms;
3. `Lf^*E` is a weak generator of `D_QCoh(𝒪_X)`.

Condition (3) is
`isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_openFactorization`, applied to the
trivial factorization `f = f ≫ 𝟙 Y`; (1) and (2) follow from it by
`tfae_isZero_quasiCoherentDerivedPushforward`, the equivalence of the three conditions. -/
@[stacks 0BQT "the clause that the three conditions hold when f is affine, when f is an open \
  immersion, and when f is a composition of such"]
theorem conditions_of_multiplicativeClosure {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] {f : X ⟶ Y}
    (hf : ((@IsAffineHom) ⊔ (@IsOpenImmersion) :
      MorphismProperty (Scheme.{u})).multiplicativeClosure f)
    (E : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (∀ K : Stacks.Duality.quasiCoherentDerivedCategory X,
        IsZero ((qcqsRestrictedDerivedPushforward f).obj K) → IsZero K) ∧
      (qcqsRestrictedDerivedPushforward f).ReflectsIsomorphisms ∧
      (ObjectProperty.singleton
        ((Stacks.Duality.quasiCoherentDerivedPullback' f).obj E)
        ).IsWeakTriangulatedGenerator := by
  have h3 : (ObjectProperty.singleton
      ((Stacks.Duality.quasiCoherentDerivedPullback' f).obj E)).IsWeakTriangulatedGenerator :=
    isWeakTriangulatedGenerator_quasiCoherentDerivedPullback_of_openFactorization f f hf rfl
      (𝟙 Y) f (Category.comp_id f) inferInstance inferInstance inferInstance inferInstance E hE
  have h1 := ((tfae_isZero_quasiCoherentDerivedPushforward f E hE).out 3 1).1 h3
  exact ⟨h1, ((tfae_isZero_quasiCoherentDerivedPushforward f E hE).out 1 2).1 h1, h3⟩

end Stacks.Duality.DerivedPushforward

end
