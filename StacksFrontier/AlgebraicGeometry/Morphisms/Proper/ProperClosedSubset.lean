module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.Int.Interval
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed subsets proper over a base

Let `f : X ⟶ S` be a morphism of schemes which is locally of finite type. A closed subset `Z`
of `X` is *proper over `S`* when the reduced induced closed subscheme on `Z` is proper over `S`.
This condition does not depend on the closed subscheme structure chosen on `Z`, it is inherited
by smaller closed subsets, it is preserved by finite unions, and its inverse image is proper
over the new base after any base change.

## Main definitions

* `AlgebraicGeometry.IsProperOver`: properness of a closed subset over the base.
* `AlgebraicGeometry.Scheme.Hom.closedImage`: the image of a closed subset under a universally
  closed morphism, as a closed subset.

## Main results

* `AlgebraicGeometry.isProperOver_iff_exists_isProper` and
  `AlgebraicGeometry.exists_isProper_iff_forall_isProper`: the reduced structure is proper
  exactly when some closed subscheme structure on the same support is, exactly when every one
  is.
* `AlgebraicGeometry.isProperOver_of_le`: a closed subset of a proper closed subset is proper.
* `AlgebraicGeometry.isProperOver_iSup`: a finite union of proper closed subsets is proper.
* `AlgebraicGeometry.exists_isProperOver_of_eventually_empty`: a `ℤ`-indexed family of subsets,
  almost all empty and each inside a proper closed subset, lies inside one proper closed subset.
* `AlgebraicGeometry.isProperOver_preimage_baseChange`: properness of a closed subset is stable
  under base change, and `AlgebraicGeometry.isProperOver_preimage_of_iso` is the special case
  of an isomorphism over the base.
* `AlgebraicGeometry.isProperOver_closedImage`: the image of a proper closed subset under a
  universally closed morphism is proper over the base.

## Implementation notes

The reduced induced structure on `Z` is the subscheme cut out by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Z`, so `IsProperOver` is an `abbrev` for
properness of a composite of scheme morphisms and the existing proper-morphism API applies
to it directly. The hypothesis that `f` is locally of finite type is recorded in the binders of
`IsProperOver`, as in the source, even though the body does not use it: properness of the
composite already forces it.

A closed subscheme structure on `Z` is an ideal sheaf whose support is `Z`. Comparing two such
structures is where separatedness has to be descended along a surjective universally closed
morphism, which is the content of
`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed`.

Finite unions are handled through the coproduct of the two reduced subschemes: its structure
morphism to `S` is proper because the induced morphism of coproducts is, and the union is the
image of that coproduct, so the image statement for universally closed morphisms gives the
result. Base change uses the comparison isomorphism between the pullback ideal sheaf's subscheme
and the fibre product of the subscheme.

## References

* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
* [Stacks Project, Tag 0CYN](https://stacks.math.columbia.edu/tag/0CYN)
* [Stacks Project, Tag 0CYP](https://stacks.math.columbia.edu/tag/0CYP)
* [Stacks Project, Tag 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
* [Stacks Project, Tag 0CYR](https://stacks.math.columbia.edu/tag/0CYR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- **Stacks 0CYM.** A closed subset `Z` of `X` is proper over `S` if its reduced induced closed
subscheme is proper over `S`. -/
@[stacks 0CYM]
public abbrev IsProperOver {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : Closeds X) : Prop :=
  IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f)

section Compare

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (Z : Closeds X)

/-- The support of the vanishing ideal sheaf of a closed subset is that closed subset. -/
private theorem support_vanishingIdeal_eq :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

/-- A morphism `p` is proper if some surjective universally closed `g` has proper composite
`g ≫ p`. -/
private theorem isProper_of_surjective_comp {A B S : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ S)
    [Surjective g] [UniversallyClosed g] [IsProper (g ≫ p)] [LocallyOfFiniteType p] :
    IsProper p := by
  have : UniversallyClosed p := UniversallyClosed.of_comp_surjective g p
  have : IsSeparated (Over.mk (g ≫ p)).hom := IsProper.toIsSeparated (f := g ≫ p)
  let g' : Over.mk (g ≫ p) ⟶ Over.mk p := Over.homMk g
  have : Surjective g'.left := ‹Surjective g›
  have : UniversallyClosed g'.left := ‹UniversallyClosed g›
  have : IsSeparated p := isSeparated_of_surjective_universallyClosed g'
  exact IsProper.mk

/-- Any closed subscheme structure on a closed subset proper over the base is proper over the
base. -/
private theorem isProper_of_isProperOver (J : X.IdealSheafData) (hJ : J.support = Z)
    (hProper : IsProperOver f Z) : IsProper (J.subschemeι ≫ f) := by
  let V := Scheme.IdealSheafData.vanishingIdeal Z
  have hJV : J ≤ V :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal (I := J) (Z := Z)).mp (by rw [hJ])
  let g : V.subscheme ⟶ J.subscheme := Scheme.IdealSheafData.inclusion hJV
  have hSupport : V.support = J.support := (support_vanishingIdeal_eq Z).trans hJ.symm
  have hSurj : Surjective g := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, hx⟩ : J.subschemeι y ∈ Set.range V.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι, hSupport,
        ← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self y
    refine ⟨x, J.subschemeι.isEmbedding.injective ?_⟩
    show (g ≫ J.subschemeι) x = J.subschemeι y
    rw [Scheme.IdealSheafData.inclusion_subschemeι]
    exact hx
  have : IsProper (g ≫ J.subschemeι ≫ f) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    exact hProper
  have : UniversallyClosed g := inferInstance
  exact isProper_of_surjective_comp g _

/-- **Stacks 0CYL, parts (1) and (2).** The reduced closed subscheme on `Z` is proper over `S`
exactly when some closed subscheme structure on `Z` is proper over `S`. -/
@[stacks 0CYL "parts (1) and (2)", ega "II 5.4.10" "indep. of subscheme"]
public theorem isProperOver_iff_exists_isProper :
    IsProperOver f Z ↔ ∃ I : X.IdealSheafData, I.support = Z ∧ IsProper (I.subschemeι ≫ f) := by
  refine ⟨fun hProper => ⟨_, support_vanishingIdeal_eq Z, hProper⟩, ?_⟩
  rintro ⟨I, hI, hProper⟩
  have hIV : I ≤ Scheme.IdealSheafData.vanishingIdeal Z :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal (I := I) (Z := Z)).mp (by rw [hI])
  simpa [Category.assoc] using
    (inferInstance : IsProper (Scheme.IdealSheafData.inclusion hIV ≫ (I.subschemeι ≫ f)))

/-- **Stacks 0CYL, parts (2) and (3).** If one closed subscheme structure on `Z` is proper over
`S`, then every closed subscheme structure on `Z` is proper over `S`. -/
@[stacks 0CYL "parts (2) and (3)", ega "II 5.4.10" "indep. of subscheme"]
public theorem exists_isProper_iff_forall_isProper :
    (∃ I : X.IdealSheafData, I.support = Z ∧ IsProper (I.subschemeι ≫ f)) ↔
      ∀ I : X.IdealSheafData, I.support = Z → IsProper (I.subschemeι ≫ f) :=
  ⟨fun h J hJ => isProper_of_isProperOver f Z J hJ ((isProperOver_iff_exists_isProper f Z).2 h),
    fun hAll => ⟨_, support_vanishingIdeal_eq Z, hAll _ (support_vanishingIdeal_eq Z)⟩⟩

end Compare

/-- **Stacks 0CYN.** A closed subset of a closed subset proper over the base is proper over the
base. -/
@[stacks 0CYN]
public theorem isProperOver_of_le {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {Y Z : Closeds X} (hYZ : Y ≤ Z) (hZ : IsProperOver f Z) : IsProperOver f Y := by
  show IsProper ((Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ≫ f)
  rw [← Scheme.IdealSheafData.inclusion_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal_antimono hYZ), Category.assoc]
  infer_instance

/-- **Stacks 0CYP.** A closed subset proper over the base remains proper after base change. -/
@[stacks 0CYP]
public theorem isProperOver_preimage_baseChange {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (Z : Closeds X) (hZ : IsProperOver f Z) :
    haveI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
    IsProperOver f' (Z.preimage g'.continuous) := by
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let J := I.comap g'
  let m : J.subscheme ⟶ I.subscheme := (I.comapIso g').hom ≫ pullback.snd g' I.subschemeι
  have hcomap : IsPullback J.subschemeι m g' I.subschemeι := by
    refine IsPullback.of_iso_pullback ?_ (I.comapIso g') (by simp [J]) rfl
    exact ⟨by simp [J, m]⟩
  have hpb : IsPullback m (J.subschemeι ≫ f') (I.subschemeι ≫ f) g := by
    simpa only [Category.assoc] using hcomap.flip.paste_vert h
  refine (isProperOver_iff_exists_isProper f' (Z.preimage g'.continuous)).2
    ⟨J, ?_, IsProper.isStableUnderBaseChange.of_isPullback hpb hZ⟩
  rw [show J = I.comap g' from rfl, Scheme.IdealSheafData.support_comap]
  exact Closeds.ext (by simpa using Scheme.IdealSheafData.coe_support_vanishingIdeal Z ▸ rfl)

/-- Properness over a base transports along an isomorphism over that base. -/
public theorem isProperOver_preimage_of_iso {A A' S : Scheme.{u}} (e : A' ≅ A)
    (p : A ⟶ S) (p' : A' ⟶ S) (he : e.hom ≫ p = p') [LocallyOfFiniteType p]
    (Z : Closeds A) (hZ : IsProperOver p Z) :
    haveI : LocallyOfFiniteType p' := he ▸ inferInstance
    IsProperOver p' (Z.preimage e.hom.continuous) := by
  exact isProperOver_preimage_baseChange e.hom p' p (𝟙 S)
    (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩) Z hZ

/-- **Stacks 0CYQ.** The image of a closed subset under a universally closed morphism, as a
closed subset. -/
@[stacks 0CYQ "image_universally_closed"]
public def Scheme.Hom.closedImage {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]
    (Z : Closeds X) : Closeds Y :=
  ⟨f '' (Z : Set X), f.isClosedMap _ Z.isClosed⟩

/-- **Stacks 0CYQ.** The closed image of a closed subset proper over the base is proper over the
base. -/
@[stacks 0CYQ "image_universally_closed"]
public theorem isProperOver_closedImage {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [UniversallyClosed f] [LocallyOfFiniteType (f ≫ g)] [LocallyOfFiniteType g]
    (Z : Closeds X) (hZ : IsProperOver (f ≫ g) Z) :
    IsProperOver g (f.closedImage Z) := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let J := Scheme.IdealSheafData.vanishingIdeal (f.closedImage Z)
  let iX := I.subschemeι
  let iY := J.subschemeι
  let h : I.subscheme ⟶ Y := iX ≫ f
  obtain ⟨q, hq⟩ : ∃ q : I.subscheme ⟶ J.subscheme, q ≫ iY = h := by
    refine (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support J h).2 ?_
    rintro y ⟨a, rfl⟩
    have haZ : iX a ∈ (Z : Set X) := by
      simpa [iX, I, Scheme.IdealSheafData.coe_support_vanishingIdeal] using
        (show iX a ∈ Set.range iX.base from ⟨a, rfl⟩)
    show f (iX a) ∈ (J.support : Set Y)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact ⟨iX a, haZ, rfl⟩
  have : Surjective q := by
    refine ⟨fun b => ?_⟩
    have hbJ : iY b ∈ (J.support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι J]
      exact ⟨b, rfl⟩
    have hb : iY b ∈ (f.closedImage Z : Set Y) := by
      simpa only [J, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hbJ
    obtain ⟨x, hxZ, hxb⟩ := hb
    have hrx : x ∈ Set.range iX.base := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hxZ
    obtain ⟨a, rfl⟩ := hrx
    refine ⟨a, iY.isClosedEmbedding.injective ?_⟩
    have hpoint := congrArg (fun k : I.subscheme ⟶ Y => k a) hq
    change iY (q a) = f (iX a) at hpoint
    exact hpoint.trans hxb
  have : UniversallyClosed (q ≫ iY) := by
    rw [hq]
    infer_instance
  have : UniversallyClosed q := UniversallyClosed.of_comp_of_isSeparated q iY
  have : IsProper (q ≫ iY ≫ g) := by
    rw [← Category.assoc, hq]
    simpa [h] using hZ
  exact isProper_of_surjective_comp q (iY ≫ g)

/-- The empty closed subset is proper over the base. -/
public theorem isProperOver_bot {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    IsProperOver f (⊥ : Closeds X) := by
  show IsProper ((Scheme.IdealSheafData.vanishingIdeal (⊥ : Closeds X)).subschemeι ≫ f)
  rw [Scheme.IdealSheafData.vanishingIdeal_bot]
  infer_instance

/-- **Stacks 0CYR.** The union of two closed subsets proper over the base is proper over the
base. -/
@[stacks 0CYR]
public theorem isProperOver_sup {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z W : Closeds X) (hZ : IsProperOver f Z) (hW : IsProperOver f W) :
    IsProperOver f (Z ⊔ W) := by
  let IZ := Scheme.IdealSheafData.vanishingIdeal Z
  let IW := Scheme.IdealSheafData.vanishingIdeal W
  let A := IZ.subscheme
  let B := IW.subscheme
  let a := IZ.subschemeι
  let b := IW.subschemeι
  let q : A ⨿ B ⟶ X := coprod.desc a b
  let r : A ⨿ B ⟶ S := coprod.desc (a ≫ f) (b ≫ f)
  have hr : IsProper r := by
    let δ : S ⨿ S ⟶ S := coprod.desc (𝟙 S) (𝟙 S)
    let m : A ⨿ B ⟶ S ⨿ S := coprod.map (a ≫ f) (b ≫ f)
    have hm : IsProper m := IsZariskiLocalAtTarget.coprodMap _ _ hZ hW
    have heq : m ≫ δ = r := by apply coprod.hom_ext <;> simp [m, δ, r]
    rw [← heq]
    infer_instance
  have hqf : q ≫ f = r := by apply coprod.hom_ext <;> simp [q, r]
  have hqfOver : IsProperOver (q ≫ f) (⊤ : Closeds (A ⨿ B : Scheme.{u})) := by
    show IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds (A ⨿ B : Scheme.{u}))).subschemeι ≫ (q ≫ f))
    have : IsProper (q ≫ f) := hqf ▸ hr
    infer_instance
  have hImageProper := isProperOver_closedImage q f (⊤ : Closeds (A ⨿ B : Scheme.{u})) hqfOver
  have hImage : (q.closedImage (⊤ : Closeds (A ⨿ B : Scheme.{u})) : Set X) =
      (Z : Set X) ∪ (W : Set X) := by
    show q '' Set.univ = _
    rw [Set.image_univ]
    calc
      Set.range q.base = Set.range (q.base ∘ coprodMk A B) :=
        ((coprodMk A B).surjective.range_comp q.base).symm
      _ = Set.range a.base ∪ Set.range b.base := by
        rw [Sum.range_eq]
        have hL : ((q.base ∘ coprodMk A B) ∘ Sum.inl) = a.base := by
          funext x
          simpa only [Function.comp_apply, coprodMk_inl, ← Scheme.Hom.comp_apply] using
            congrArg (fun h : A ⟶ X => h x) (coprod.inl_desc a b)
        have hR : ((q.base ∘ coprodMk A B) ∘ Sum.inr) = b.base := by
          funext x
          simpa only [Function.comp_apply, coprodMk_inr, ← Scheme.Hom.comp_apply] using
            congrArg (fun h : B ⟶ X => h x) (coprod.inr_desc a b)
        rw [hL, hR]
      _ = _ := by simp [a, b, IZ, IW]
  have hClosedImage : q.closedImage (⊤ : Closeds (A ⨿ B : Scheme.{u})) = Z ⊔ W :=
    Closeds.ext hImage
  simpa [hClosedImage] using hImageProper

/-- **Stacks 0CYR.** A finite union of closed subsets proper over the base is proper over the
base. -/
@[stacks 0CYR]
public theorem isProperOver_iSup {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ι : Type v} [Finite ι] (Z : ι → Closeds X) (hZ : ∀ i, IsProperOver f (Z i)) :
    IsProperOver f (iSup Z) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  suffices h : ∀ t : Finset ι, IsProperOver f (t.sup Z) by
    simpa [Finset.sup_eq_iSup] using h Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty => simpa using isProperOver_bot f
  | @insert i t _ ih =>
      simpa [Finset.sup_insert] using isProperOver_sup f (Z i) (t.sup Z) (hZ i) ih

/-- **A `ℤ`-indexed family of subsets of `X`, almost all empty and each inside a closed subset
proper over `S`, lies inside one closed subset proper over `S`.**

Only the members indexed by the interval `[a, b]` can be nonempty, and that interval contains
finitely many integers, so the supremum of the closed subsets attached to them is a finite
supremum and [Stacks, Tag 0CYR] applies to it in the form
`AlgebraicGeometry.isProperOver_iSup`. -/
public theorem exists_isProperOver_of_eventually_empty {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : ℤ → Set X) (a b : ℤ)
    (hvanish : ∀ i : ℤ, i ∉ Set.Icc a b → s i = ∅)
    (hmem : ∀ i : ℤ, ∃ Z : Closeds X, IsProperOver f Z ∧ s i ⊆ (Z : Set X)) :
    ∃ T : Closeds X, IsProperOver f T ∧ ∀ i : ℤ, s i ⊆ (T : Set X) := by
  classical
  choose Z hZproper hZsub using hmem
  have hfin : Finite (Set.Icc a b : Set ℤ) := (Set.finite_Icc a b).to_subtype
  refine ⟨⨆ j : (Set.Icc a b : Set ℤ), Z j, isProperOver_iSup f _ fun j => hZproper j, fun i => ?_⟩
  by_cases hi : i ∈ Set.Icc a b
  · exact (hZsub i).trans
      (SetLike.coe_subset_coe.mpr (le_iSup (fun j : (Set.Icc a b : Set ℤ) => Z j) ⟨i, hi⟩))
  · simp [hvanish i hi]

end AlgebraicGeometry

end

