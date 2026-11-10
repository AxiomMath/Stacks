module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSeparation
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Product
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafComapMap
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.ConstructibleCompactImage
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteTypeIdealSheafOfOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Support
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separating two closed subschemes by an admissible blowup

Let `X` be a quasi-compact and quasi-separated scheme and `U ⊆ X` a quasi-compact open.

* If `Z₁, Z₂ ⊆ X` are closed subschemes of finite presentation which do not meet inside `U`, then
  there is a `U`-admissible blowup of `X` on which the strict transforms of `Z₁` and `Z₂` are
  disjoint.
* If `T₁, T₂ ⊆ U` are disjoint constructible closed subsets, then there is a `U`-admissible
  blowup of `X` in which their closures are disjoint.

The construction follows the source. For the first statement, let `Z` be the closed subscheme cut
out by the product `ℐ₁ℐ₂` of the two ideal sheaves. Inside `Z` the two inverse images `ℐ₁·𝒪_Z`
and `ℐ₂·𝒪_Z` have complementary supports over `U`, so the complement of each is a quasi-compact
open of `Z`, and the two complements are disjoint and cover the part of `Z` over `U`. Blowing `Z`
up separates them (Stacks tag 080P): there is a blowup `Z' ⟶ Z` with centre `L` whose source
splits into two disjoint opens `W₁, W₂` containing the preimages of the two complements.
Enlarging the centre to `L·(ℐ₁·𝒪_Z + ℐ₂·𝒪_Z)` changes neither its support over `U` nor the
splitting, but makes its support contain the locus where `Z₁` and `Z₂` meet. Its image in `X` is
a centre of finite presentation disjoint from `U`, so the blowup of `X` in that image is a
`U`-admissible blowup, and the strict transform of `Zᵢ` in it lands in the part lying over `Wᵢ`.
That last step is Stacks tag 080E — the strict transform of a closed subscheme is the blowup of
that subscheme in the inverse image of the centre — together with Stacks tag 080A, which factors
the blowup in a product of ideals through the blowup in either factor.

The second statement is the first applied to the closed subschemes `V(𝒥ᵢ)` for ideal sheaves
`𝒥ᵢ` of finite type with `Supp 𝒥ᵢ = X ∖ (U ∖ Tᵢ)`, which exist by
`AlgebraicGeometry.exists_isFiniteType_support_eq_compl`; the complement of `Tᵢ` in `U` is
quasi-compact because `Tᵢ` is constructible. The closure of the preimage of `Tᵢ` is contained in
the strict transform of `V(𝒥ᵢ)`, which is closed, so the two closures are disjoint.

## Main definitions

* `AlgebraicGeometry.strictTransformToBlowUp`: the strict transform of a scheme over `X` under
  the blowup of `X` in an ideal sheaf, as a morphism to the blowup.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_disjoint_strictTransforms`: part (1) of Stacks tag
  0F3V.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_disjoint_closures`: part (2) of Stacks tag 0F3V.
* `AlgebraicGeometry.preimage_subset_range_strictTransformToBlowUp`: a point of the blowup lying
  over a point of a closed subscheme and away from the centre lies on the strict transform of
  that subscheme. This is what makes a set-theoretic statement about the blowup follow from a
  statement about strict transforms.
* `AlgebraicGeometry.exists_isClosedImmersion_blowUp_of_comap_eq`: the blowup of a closed
  subscheme in the inverse image of a centre is a closed subscheme of the blowup of the ambient
  scheme in that centre.
* `AlgebraicGeometry.exists_hom_blowUp_mul`: the blowup in a product of ideals maps to the blowup
  in either factor, over the base.
* `AlgebraicGeometry.finitePresentation_map_subschemeι`: the image of an ideal sheaf under a
  closed immersion of finite presentation cuts out a closed subscheme of finite presentation.

## Implementation notes

Both statements are about `AlgebraicGeometry.blowUp`, the construction of the blowup whose
universal property (Stacks tag 0806) is `Stacks.Blowup.isTerminal_blowUp`, because tags 080E and
080A are stated for it. `Stacks.Blowup.IsAdmissibleBlowup` is phrased with the second
construction `Stacks.Blowup.blowUp`; `Stacks.Blowup.isAdmissibleBlowup_iff` says the two define
the same predicate, and it is used in both directions here — to read the output of tag 080P and
to produce the admissibility asserted below.

Part (1) does not need `U` to be quasi-compact: that hypothesis of the source is used only to
produce the ideal sheaves of part (2). It is therefore omitted from part (1), which is the same
statement for an arbitrary open.

The existential of part (1) also records that the centre is of finite presentation and misses
`U`, which admissibility only asserts of *some* centre. Every consumer needs it of *this* centre:
it is what says the blowup is an isomorphism over `U`, and part (2) below uses it that way.

## References

* [Stacks Project, Tag 0F3V](https://stacks.math.columbia.edu/tag/0F3V)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Two complementary opens -/

/-- Membership in a supremum of two opens. -/
private theorem mem_opens_sup {A : Type*} [TopologicalSpace A] {V W : Opens A} {x : A} :
    x ∈ V ⊔ W ↔ x ∈ V ∨ x ∈ W := Iff.rfl

/-- An open subscheme disjoint from a second one with which it covers the whole space is closed:
its underlying set is the complement of the other's. -/
private theorem isClosed_coe_of_disjoint_of_sup_eq_top {A : Type*} [TopologicalSpace A]
    {V W : Opens A} (hd : Disjoint V W) (hc : V ⊔ W = ⊤) : IsClosed (V : Set A) := by
  have hunion : (V : Set A) ∪ (W : Set A) = Set.univ := by
    rw [← Opens.coe_sup, hc, Opens.coe_top]
  have hcompl : (V : Set A) = (W : Set A)ᶜ := by
    refine Set.Subset.antisymm
      (fun x hx ↦ Set.disjoint_left.mp (Opens.coe_disjoint.mpr hd) hx) fun x hx ↦ ?_
    rcases Set.eq_univ_iff_forall.mp hunion x with h | h
    · exact h
    · exact absurd h hx
  rw [hcompl]
  exact W.isOpen.isClosed_compl

/-! ### The strict transform inside the blowup -/

/-- The strict transform of a scheme `f : Y ⟶ X` under the blowup of `X` in `I`, as a morphism to
the blowup: the closed subscheme of `Y ×_X X'` cut out by the sections supported on the inverse
image of the exceptional divisor, followed by the projection to the blowup. -/
@[sga "5 VII 9.5"]
abbrev strictTransformToBlowUp {Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) :
    Stacks.StrictTransform.scheme f (blowUpToBase I) (exceptionalIdeal I) ⟶ blowUp I :=
  (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
    pullback.snd f (blowUpToBase I)

/-- The strict transform of a closed subscheme of `X` is a closed subscheme of the blowup of `X`
in `I`. -/
instance isClosedImmersion_strictTransformToBlowUp {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] (I : X.IdealSheafData) :
    IsClosedImmersion (strictTransformToBlowUp f I) :=
  inferInstanceAs (IsClosedImmersion (_ ≫ pullback.snd f (blowUpToBase I)))

/-- **A point of the blowup over a point of a closed subscheme and away from the centre lies on
the strict transform of that subscheme.** Over the complement of the centre the blowup is an
isomorphism, and the strict transform contains every point of the base change away from the
inverse image of the exceptional divisor. -/
theorem preimage_subset_range_strictTransformToBlowUp {Z : Scheme.{u}} (z : Z ⟶ X)
    [IsClosedImmersion z] (I : X.IdealSheafData) (A : Set X) (hA : A ⊆ Set.range z.base)
    (hAI : Disjoint A (I.support : Set X)) :
    (blowUpToBase I).base ⁻¹' A ⊆ Set.range (strictTransformToBlowUp z I).base := by
  intro y hy
  have hyE : y ∉ ((exceptionalIdeal I).support : Set (blowUp I)) := by
    rw [show exceptionalIdeal I = I.comap (blowUpToBase I) from rfl,
      Scheme.IdealSheafData.support_comap]
    exact fun h ↦ Set.disjoint_left.mp hAI hy h
  obtain ⟨p, hp⟩ : y ∈ Set.range (pullback.snd z (blowUpToBase I)).base := by
    rw [Scheme.Pullback.range_snd]
    exact hA hy
  have hpE : p ∉ Stacks.StrictTransform.exceptionalPreimage z (blowUpToBase I)
      (exceptionalIdeal I) := by
    change (pullback.snd z (blowUpToBase I)).base p ∉
      ((exceptionalIdeal I).support : Set (blowUp I))
    rw [hp]
    exact hyE
  obtain ⟨q, hq⟩ : p ∈ Set.range (Stacks.StrictTransform.ideal z (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Stacks.StrictTransform.mem_support_ideal_of_notMem_exceptionalPreimage z
      (blowUpToBase I) (exceptionalIdeal I) hpE
  exact ⟨q, by
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hq] using hp⟩

/-- **The strict transform is contained in any closed subset of the blowup containing the part of
the base change away from the centre.** The strict transform is the scheme-theoretic image of the
complement of the inverse image of the exceptional divisor
(`Stacks.StrictTransform.support_ideal`), so its points lie in the closure of the image of that
complement. -/
private theorem range_strictTransformToBlowUp_subset_of_isClosed {Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) {C : Set (blowUp I)} (hC : IsClosed C)
    (h : ∀ p : Stacks.StrictTransform.baseChange f (blowUpToBase I),
      (blowUpToBase I).base ((pullback.snd f (blowUpToBase I)).base p) ∉ (I.support : Set X) →
        (pullback.snd f (blowUpToBase I)).base p ∈ C) :
    Set.range (strictTransformToBlowUp f I).base ⊆ C := by
  rintro _ ⟨x, rfl⟩
  apply closure_minimal (t := (pullback.snd f (blowUpToBase I)).base ⁻¹' C) ?_
    (hC.preimage (pullback.snd f (blowUpToBase I)).continuous)
    (Stacks.StrictTransform.support_ideal_subset_closure_compl_exceptionalPreimage f
      (blowUpToBase I) (exceptionalIdeal I)
      (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩))
  intro p hp
  refine h p fun hmem ↦ hp ?_
  change (pullback.snd f (blowUpToBase I)).base p ∈
    ((I.comap (blowUpToBase I)).support : Set (blowUp I))
  rw [Scheme.IdealSheafData.support_comap]
  exact hmem

/-! ### Two consequences of the universal property of the blowup -/

/-- **The blowup of a closed subscheme in the inverse image of a centre is a closed subscheme of
the blowup of the ambient scheme in that centre.** By Stacks tag 080E the blowup of `Z` in
`I·𝒪_Z` is the strict transform of `Z` inside `Z ×_X X'`, which is a closed subscheme of it; and
the projection of `Z ×_X X'` to the blowup is a closed immersion because `z` is one. -/
theorem exists_isClosedImmersion_blowUp_of_comap_eq {Z : Scheme.{u}} (z : Z ⟶ X)
    [IsClosedImmersion z] (I : X.IdealSheafData) (T : Z.IdealSheafData) (hT : I.comap z = T) :
    ∃ g : blowUp T ⟶ blowUp I, IsClosedImmersion g ∧
      g ≫ blowUpToBase I = blowUpToBase T ≫ z := by
  subst hT
  refine ⟨((Over.forget Z).mapIso (strictTransformBlowUpIso z I)).inv ≫
    strictTransformToBlowUp z I, inferInstance, ?_⟩
  have hew : ((Over.forget Z).mapIso (strictTransformBlowUpIso z I)).inv ≫
      (Stacks.StrictTransform.ideal z (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
        pullback.fst z (blowUpToBase I) = blowUpToBase (I.comap z) :=
    Over.w (strictTransformBlowUpIso z I).inv
  have hswap : ((Over.forget Z).mapIso (strictTransformBlowUpIso z I)).inv ≫
      strictTransformToBlowUp z I ≫ blowUpToBase I =
      (((Over.forget Z).mapIso (strictTransformBlowUpIso z I)).inv ≫
        (Stacks.StrictTransform.ideal z (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
          pullback.fst z (blowUpToBase I)) ≫ z := by
    simp only [strictTransformToBlowUp, Category.assoc]
    rw [← pullback.condition]
  rw [Category.assoc, hswap, hew]

/-- **The blowup in a product of ideals factors through the blowup in either factor.** This is
the consequence of Stacks tag 080A used below: a scheme identified over `X` with the blowup in
`L` receives a morphism from the blowup in `L * M` over `X`. -/
theorem exists_hom_blowUp_mul {Y : Scheme.{u}} (L M : X.IdealSheafData) (b : Y ⟶ X)
    (e : Y ≅ blowUp L) (he : e.hom ≫ blowUpToBase L = b) :
    ∃ p : blowUp (L * M) ⟶ Y, p ≫ b = blowUpToBase (L * M) := by
  refine ⟨(blowUpMulIso L M).inv.left ≫ blowUpToBase (M.comap (blowUpToBase L)) ≫ e.inv, ?_⟩
  rw [Category.assoc, Category.assoc, ← he, e.inv_hom_id_assoc]
  exact (blowUpMulIso L M).inv.w

/-- **The image of an ideal sheaf under a closed immersion of finite presentation cuts out a
closed subscheme of finite presentation.** That image is the kernel ideal sheaf of the composite
closed immersion, and a closed immersion of finite presentation has a kernel of finite type
(Stacks tag 01TV). -/
theorem finitePresentation_map_subschemeι {Z : Scheme.{u}} (z : Z ⟶ X) [IsClosedImmersion z]
    (hz : FinitePresentation z) (K : Z.IdealSheafData) (hK : FinitePresentation K.subschemeι) :
    FinitePresentation (K.map z).subschemeι := by
  have : LocallyOfFinitePresentation z := hz.1
  have : LocallyOfFinitePresentation K.subschemeι := hK.1
  refine (finitePresentation_subschemeι_iff_isFiniteType (K.map z)).mpr ?_
  rw [show K.map z = (K.subschemeι ≫ z).ker from rfl]
  exact isFiniteType_ker_of_finitePresentation (K.subschemeι ≫ z)
    ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### Separating strict transforms -/

/-- The strict transform of a closed subscheme `V(H)` lies in a prescribed piece of the blowup.
Here `Z = V(J)` contains `V(H)`, the centre `I` of the blowup of `X` is the image of a centre `T`
on `Z`, and `O` is an open of `Z` over which the piece `W` of a blowup `b : Y ⟶ Z` of `Z` sits;
`p` factors the blowup of `Z` in `T` through `Y` and `g` realizes it inside the blowup of `X`.

This is the geometric step of part (1) of Stacks tag 0F3V: away from `T` the blowup of `Z` is
bijective onto `Z`, so a point of the strict transform of `V(H)` away from the centre comes from
a point of `O`, hence lies over `W`. -/
private theorem range_strictTransformToBlowUp_subset_image {Y : Scheme.{u}}
    (J H : X.IdealSheafData) (T : J.subscheme.IdealSheafData) (I : X.IdealSheafData)
    (hI : T.map J.subschemeι = I) (b : Y ⟶ J.subscheme) (p : blowUp T ⟶ Y)
    (hp : p ≫ b = blowUpToBase T) (g : blowUp T ⟶ blowUp I) [IsClosedImmersion g]
    (hg : g ≫ blowUpToBase I = blowUpToBase T ≫ J.subschemeι)
    (O : J.subscheme.Opens) (W : Y.Opens) (hW : IsClosed (W : Set Y)) (hpre : b ⁻¹ᵁ O ≤ W)
    (hHJ : (H.support : Set X) ⊆ (J.support : Set X))
    (hO : ∀ w : J.subscheme, J.subschemeι.base w ∈ (H.support : Set X) →
      w ∉ (T.support : Set J.subscheme) → w ∈ O) :
    Set.range (strictTransformToBlowUp H.subschemeι I).base ⊆
      g.base '' (p.base ⁻¹' (W : Set Y)) := by
  subst hI
  apply range_strictTransformToBlowUp_subset_of_isClosed _ _
    (g.isClosedEmbedding.isClosedMap _ (hW.preimage p.continuous))
  intro y hy
  have hxH : (blowUpToBase (T.map J.subschemeι)).base
      ((pullback.snd H.subschemeι (blowUpToBase (T.map J.subschemeι))).base y) ∈
      (H.support : Set X) := by
    rw [← H.range_subschemeι]
    refine ⟨(pullback.fst H.subschemeι (blowUpToBase (T.map J.subschemeι))).base y, ?_⟩
    exact congrArg (fun k ↦ k.base y) (pullback.condition (f := H.subschemeι)
      (g := blowUpToBase (T.map J.subschemeι)))
  obtain ⟨w, hw⟩ : ∃ w, J.subschemeι.base w =
      (blowUpToBase (T.map J.subschemeι)).base
        ((pullback.snd H.subschemeι (blowUpToBase (T.map J.subschemeι))).base y) := by
    have hxJ := hHJ hxH
    rwa [← J.range_subschemeι] at hxJ
  have hwT : w ∉ (T.support : Set J.subscheme) := by
    intro hwT
    refine hy ?_
    rw [Scheme.IdealSheafData.support_map]
    exact subset_closure ⟨w, hwT, hw⟩
  obtain ⟨t, ht⟩ := exists_blowUpToBase_eq_of_notMem_support T hwT
  have hgt : g.base t =
      (pullback.snd H.subschemeι (blowUpToBase (T.map J.subschemeι))).base y := by
    refine (blowUpToBase_injective_of_notMem_support (T.map J.subschemeι) hy ?_).symm
    have hgt := congrArg (fun k ↦ k.base t) hg
    change (blowUpToBase (T.map J.subschemeι)).base (g.base t) =
      J.subschemeι.base ((blowUpToBase T).base t) at hgt
    rw [hgt, ht, hw]
  refine ⟨t, hpre ?_, hgt⟩
  have hpt : b.base (p.base t) = w := (congrArg (fun k ↦ k.base t) hp).trans ht
  change b.base (p.base t) ∈ O
  rw [hpt]
  exact hO w (by rw [hw]; exact hxH) hwT

/-- The complement of the support of the pullback of a finite presentation ideal sheaf is a compact
open. -/
private theorem exists_isCompact_opens_compl_comap_support {Z : Scheme.{u}} [CompactSpace Z]
    [QuasiSeparatedSpace Z] (f : Z ⟶ X) (I : X.IdealSheafData)
    (K : Z.IdealSheafData) (hK : K = I.comap f) (hI : FinitePresentation I.subschemeι) :
    K.IsFiniteType ∧ (K.support : Set Z) = f.base ⁻¹' (I.support : Set X) ∧
      ∃ O : Z.Opens, IsCompact (O : Set Z) ∧ ∀ w, w ∈ O ↔ w ∉ (K.support : Set Z) := by
  subst hK
  have hft := (finitePresentation_subschemeι_iff_isFiniteType _).mp
    (finitePresentation_comap_subschemeι I f hI)
  exact ⟨hft, by rw [Scheme.IdealSheafData.support_comap]; rfl,
    ⟨_, (I.comap f).support.isClosed.isOpen_compl⟩,
    isCompact_of_isFiniteType_of_support_eq_compl _ _ hft (compl_compl _).symm, fun _ ↦ Iff.rfl⟩

/-- A point of `A` outside `A ∩ B` lies in any `O` whose complement is `B`. -/
private theorem mem_of_mem_of_notMem_inter {α : Type*} {A B O T : Set α} (hT : T = A ∩ B)
    (hO : ∀ w, w ∈ O ↔ w ∉ B) {w : α} (hw : w ∈ A) (hwT : w ∉ T) : w ∈ O := by
  by_contra hc
  exact hwT (hT ▸ ⟨hw, not_not.mp fun h ↦ hc ((hO w).mpr h)⟩)

/-- **Stacks Project, Tag 0F3V, part (1).** Let `X` be a quasi-compact and quasi-separated scheme
and `U ⊆ X` an open. Let `Z₁ = V(ℐ₁)` and `Z₂ = V(ℐ₂)` be closed subschemes of finite
presentation which do not meet inside `U`. Then there is a centre of finite presentation disjoint
from `U` — so that the blowup of `X` in it is a `U`-admissible blowup — on which the strict
transforms of `Z₁` and `Z₂` are disjoint.

Quasi-compactness of `U` is not needed; see the implementation notes of this file. -/
@[stacks 0F3V "separate_strict_transforms"]
theorem exists_isAdmissibleBlowup_disjoint_strictTransforms [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (I₁ I₂ : X.IdealSheafData)
    (h₁ : FinitePresentation I₁.subschemeι) (h₂ : FinitePresentation I₂.subschemeι)
    (hdisj : Disjoint ((U : Set X) ∩ (I₁.support : Set X)) (I₂.support : Set X)) :
    ∃ I : X.IdealSheafData, Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      Disjoint (U : Set X) (I.support : Set X) ∧
        Disjoint (Set.range (strictTransformToBlowUp I₁.subschemeι I).base)
          (Set.range (strictTransformToBlowUp I₂.subschemeι I).base) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : X.IdealSheafData, J = I₁ * I₂ := ⟨_, rfl⟩
  have hJsuppset : (J.support : Set X) = (I₁.support : Set X) ∪ (I₂.support : Set X) := by
    rw [hJ, Scheme.IdealSheafData.support_mul, Closeds.coe_sup]
  have hI₁ft : I₁.IsFiniteType := (finitePresentation_subschemeι_iff_isFiniteType I₁).mp h₁
  have hI₂ft : I₂.IsFiniteType := (finitePresentation_subschemeι_iff_isFiniteType I₂).mp h₂
  have hJfp : FinitePresentation J.subschemeι :=
    (finitePresentation_subschemeι_iff_isFiniteType J).mpr (by rw [hJ]; exact hI₁ft.mul hI₂ft)
  have : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  have : QuasiSeparatedSpace J.subscheme := quasiSeparatedSpace_of_quasiSeparated J.subschemeι
  obtain ⟨K₁, hK₁⟩ : ∃ K : J.subscheme.IdealSheafData, K = I₁.comap J.subschemeι := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K : J.subscheme.IdealSheafData, K = I₂.comap J.subschemeι := ⟨_, rfl⟩
  obtain ⟨hK₁ft, hK₁supp, O₂, hO₂, hmemO₂⟩ :=
    exists_isCompact_opens_compl_comap_support J.subschemeι I₁ K₁ hK₁ h₁
  obtain ⟨hK₂ft, hK₂supp, O₁, hO₁, hmemO₁⟩ :=
    exists_isCompact_opens_compl_comap_support J.subschemeι I₂ K₂ hK₂ h₂
  have hjsupp : ∀ w : J.subscheme, J.subschemeι.base w ∈ (I₁.support : Set X) ∨
      J.subschemeι.base w ∈ (I₂.support : Set X) := by
    intro w
    have hmem : J.subschemeι.base w ∈ (J.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    rwa [hJsuppset, Set.mem_union] at hmem
  have hOdisj : Disjoint O₁ O₂ := by
    refine Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_)
    rcases hjsupp w with hw | hw
    · exact ((hmemO₂ w).mp hw₂) (by rw [hK₁supp]; exact hw)
    · exact ((hmemO₁ w).mp hw₁) (by rw [hK₂supp]; exact hw)
  have hUcover : (J.subschemeι ⁻¹ᵁ U) ≤ O₁ ⊔ O₂ := by
    intro w hw
    by_contra hnot
    have hw₁ : J.subschemeι.base w ∈ (I₁.support : Set X) := by
      rw [← Set.mem_preimage, ← hK₁supp]
      by_contra hc
      exact hnot (mem_opens_sup.mpr (Or.inr ((hmemO₂ w).mpr hc)))
    have hw₂ : J.subschemeι.base w ∈ (I₂.support : Set X) := by
      rw [← Set.mem_preimage, ← hK₂supp]
      by_contra hc
      exact hnot (mem_opens_sup.mpr (Or.inl ((hmemO₁ w).mpr hc)))
    exact Set.disjoint_left.mp hdisj ⟨hw, hw₁⟩ hw₂
  obtain ⟨M, hM⟩ : ∃ M : J.subscheme.IdealSheafData, M = K₁ ⊔ K₂ := ⟨_, rfl⟩
  have hMsupp : (M.support : Set J.subscheme) =
      (K₁.support : Set J.subscheme) ∩ (K₂.support : Set J.subscheme) := by
    rw [hM, Scheme.IdealSheafData.support_sup]
    rfl
  obtain ⟨Z', b, W₁, W₂, hb, hWdisj, hWcover, hpreW₁, hpreW₂⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_disjoint_open_cover J.subscheme O₁ O₂ hO₁ hO₂ hOdisj
  obtain ⟨L, hLfp, hLdisj, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff (O₁ ⊔ O₂) b).mp hb
  have hLsub : (L.support : Set J.subscheme) ⊆ (M.support : Set J.subscheme) := by
    intro w hw
    rw [hMsupp]
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact Set.disjoint_left.mp hLdisj (mem_opens_sup.mpr (Or.inr ((hmemO₂ w).mpr hc))) hw
    · by_contra hc
      exact Set.disjoint_left.mp hLdisj (mem_opens_sup.mpr (Or.inl ((hmemO₁ w).mpr hc))) hw
  obtain ⟨T, hT⟩ : ∃ T : J.subscheme.IdealSheafData, T = L * M := ⟨_, rfl⟩
  have hTsupp : (T.support : Set J.subscheme) = (M.support : Set J.subscheme) := by
    rw [hT, Scheme.IdealSheafData.support_mul, Closeds.coe_sup]
    exact Set.union_eq_self_of_subset_left hLsub
  have hTfp : FinitePresentation T.subschemeι :=
    (finitePresentation_subschemeι_iff_isFiniteType T).mpr (by
      rw [hT, hM]
      exact ((finitePresentation_subschemeι_iff_isFiniteType L).mp hLfp).mul
        (hK₁ft.sup hK₂ft))
  obtain ⟨I, hI⟩ : ∃ I : X.IdealSheafData, I = T.map J.subschemeι := ⟨_, rfl⟩
  have hIfp : FinitePresentation I.subschemeι := by
    rw [hI]
    exact finitePresentation_map_subschemeι J.subschemeι hJfp T hTfp
  have hIsupp : (I.support : Set X) =
      J.subschemeι.base '' (M.support : Set J.subscheme) := by
    rw [hI, Scheme.IdealSheafData.support_map]
    change closure (J.subschemeι.base '' (T.support : Set J.subscheme)) =
      J.subschemeι.base '' (M.support : Set J.subscheme)
    rw [hTsupp]
    exact (J.subschemeι.isClosedEmbedding.isClosedMap _ M.support.isClosed).closure_eq
  have hIdisj : Disjoint (U : Set X) (I.support : Set X) := by
    refine Set.disjoint_left.mpr fun x hxU hxI ↦ ?_
    rw [hIsupp] at hxI
    obtain ⟨w, hwM, rfl⟩ := hxI
    rw [hMsupp] at hwM
    rcases mem_opens_sup.mp (hUcover (show w ∈ J.subschemeι ⁻¹ᵁ U from hxU)) with hw | hw
    · exact ((hmemO₁ w).mp hw) hwM.2
    · exact ((hmemO₂ w).mp hw) hwM.1
  refine ⟨I, (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase I)).mpr
    ⟨I, hIfp, hIdisj, Iso.refl _, Category.id_comp _⟩, hIdisj, ?_⟩
  obtain ⟨p, hp⟩ : ∃ p : blowUp T ⟶ Z', p ≫ b = blowUpToBase T := by
    rw [hT]
    exact exists_hom_blowUp_mul L M b e he
  obtain ⟨g, hgci, hg⟩ : ∃ g : blowUp T ⟶ blowUp I, IsClosedImmersion g ∧
      g ≫ blowUpToBase I = blowUpToBase T ≫ J.subschemeι :=
    exists_isClosedImmersion_blowUp_of_comap_eq J.subschemeι I T
      (by rw [hI]; exact Scheme.IdealSheafData.comap_map_of_isClosedImmersion T J.subschemeι)
  have : IsClosedImmersion g := hgci
  have hHJ₁ : (I₁.support : Set X) ⊆ (J.support : Set X) := by
    rw [hJsuppset]; exact Set.subset_union_left
  have hHJ₂ : (I₂.support : Set X) ⊆ (J.support : Set X) := by
    rw [hJsuppset]; exact Set.subset_union_right
  have hO₁' : ∀ w : J.subscheme, J.subschemeι.base w ∈ (I₁.support : Set X) →
      w ∉ (T.support : Set J.subscheme) → w ∈ O₁ := fun w hw ↦
    mem_of_mem_of_notMem_inter (hTsupp.trans hMsupp) hmemO₁ (by rwa [hK₁supp])
  have hO₂' : ∀ w : J.subscheme, J.subschemeι.base w ∈ (I₂.support : Set X) →
      w ∉ (T.support : Set J.subscheme) → w ∈ O₂ := fun w hw ↦
    mem_of_mem_of_notMem_inter (hTsupp.trans (hMsupp.trans (Set.inter_comm _ _))) hmemO₂
      (by rwa [hK₂supp])
  have hsub₁ := range_strictTransformToBlowUp_subset_image J I₁ T I hI.symm b p hp g hg O₁ W₁
    (isClosed_coe_of_disjoint_of_sup_eq_top hWdisj hWcover) hpreW₁ hHJ₁ hO₁'
  have hsub₂ := range_strictTransformToBlowUp_subset_image J I₂ T I hI.symm b p hp g hg O₂ W₂
    (isClosed_coe_of_disjoint_of_sup_eq_top hWdisj.symm (by rw [sup_comm]; exact hWcover))
    hpreW₂ hHJ₂ hO₂'
  refine Disjoint.mono hsub₁ hsub₂ (Set.disjoint_image_image fun x hx y hy hxy ↦ ?_)
  obtain rfl : x = y := g.isClosedEmbedding.injective hxy
  exact Set.disjoint_left.mp (Opens.coe_disjoint.mpr hWdisj) hx hy


/-! ### Separating closures of constructible closed subsets -/

/-- The preimage along an open immersion of the complement of the image of a complement is the
original subset. -/
private theorem preimage_compl_image_compl (U : X.Opens) (T : Set U.toScheme) :
    U.ι.base ⁻¹' (U.ι.base '' Tᶜ)ᶜ = T := by
  refine Set.ext fun t ↦ ⟨fun ht ↦ ?_, fun ht ⟨s, hs, heq⟩ ↦ ?_⟩
  · by_contra h
    exact ht ⟨t, h, rfl⟩
  · exact hs (U.ι.isOpenEmbedding.injective heq ▸ ht)

/-- **Stacks Project, Tag 0F3V, part (2).** Let `X` be a quasi-compact and quasi-separated scheme,
let `U ⊆ X` be a quasi-compact open and let `T₁, T₂ ⊆ U` be disjoint constructible closed subsets.
Then there is a `U`-admissible blowup `X' ⟶ X` in which the closures of `T₁` and `T₂` are
disjoint.

This is part (1) applied to closed subschemes of `X` cutting out `T₁` and `T₂` on `U`: the closure
of the preimage of `Tᵢ` is contained in the strict transform of the `i`-th subscheme, which is
closed because the subscheme is a closed subscheme of `X`. -/
@[stacks 0F3V "separate_constructible_closures"]
theorem exists_isAdmissibleBlowup_disjoint_closures [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (T₁ T₂ : Set U.toScheme)
    (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) (hc₁ : Topology.IsConstructible T₁)
    (hc₂ : Topology.IsConstructible T₂) (hdisj : Disjoint T₁ T₂) :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup U f ∧
      Disjoint (closure (f.base ⁻¹' (U.ι.base '' T₁)))
        (closure (f.base ⁻¹' (U.ι.base '' T₂))) := by
  classical
  obtain ⟨J₁, hJ₁ft, hJ₁supp⟩ := exists_isFiniteType_support_eq_compl X
    ⟨U.ι.base '' T₁ᶜ, U.ι.isOpenEmbedding.isOpenMap _ (isOpen_compl_iff.mpr hT₁)⟩
    (isCompact_image_compl_of_isConstructible U hU hc₁)
  obtain ⟨J₂, hJ₂ft, hJ₂supp⟩ := exists_isFiniteType_support_eq_compl X
    ⟨U.ι.base '' T₂ᶜ, U.ι.isOpenEmbedding.isOpenMap _ (isOpen_compl_iff.mpr hT₂)⟩
    (isCompact_image_compl_of_isConstructible U hU hc₂)
  have hpre₁ : U.ι.base ⁻¹' (J₁.support : Set X) = T₁ := by
    rw [hJ₁supp]
    exact preimage_compl_image_compl U T₁
  have hpre₂ : U.ι.base ⁻¹' (J₂.support : Set X) = T₂ := by
    rw [hJ₂supp]
    exact preimage_compl_image_compl U T₂
  have hsep : Disjoint ((U : Set X) ∩ (J₁.support : Set X)) (J₂.support : Set X) := by
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ ↦ ?_
    obtain ⟨hxU, hxJ₁⟩ := hx₁
    have hu₁ : (⟨x, hxU⟩ : U.toScheme) ∈ T₁ := by rw [← hpre₁]; exact hxJ₁
    have hu₂ : (⟨x, hxU⟩ : U.toScheme) ∈ T₂ := by rw [← hpre₂]; exact hx₂
    exact Set.disjoint_left.mp hdisj hu₁ hu₂
  obtain ⟨I, hadm, hIdisj, hST⟩ := exists_isAdmissibleBlowup_disjoint_strictTransforms U J₁ J₂
    ((finitePresentation_subschemeι_iff_isFiniteType J₁).mpr hJ₁ft)
    ((finitePresentation_subschemeι_iff_isFiniteType J₂).mpr hJ₂ft) hsep
  have hrange (K : X.IdealSheafData) (T : Set U.toScheme)
      (hKT : U.ι.base ⁻¹' (K.support : Set X) = T) :
      closure ((blowUpToBase I).base ⁻¹' (U.ι.base '' T)) ⊆
        Set.range (strictTransformToBlowUp K.subschemeι I).base := by
    refine closure_minimal (preimage_subset_range_strictTransformToBlowUp K.subschemeι I _
      ?_ ?_) ((strictTransformToBlowUp K.subschemeι I).isClosedEmbedding.isClosed_range)
    · rintro _ ⟨t, htT, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι]
      show U.ι.base t ∈ (K.support : Set X)
      rw [← Set.mem_preimage, hKT]
      exact htT
    · exact hIdisj.mono_left (by rintro _ ⟨t, -, rfl⟩; exact t.2)
  exact ⟨blowUp I, blowUpToBase I, hadm,
    hST.mono (hrange J₁ T₁ hpre₁) (hrange J₂ T₂ hpre₂)⟩

end AlgebraicGeometry

end
