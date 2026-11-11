module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Bounded below complexes of injectives compute right derived functors

Let `𝒜` be an abelian category and let `K` be a bounded below complex of injective objects of
`𝒜`, viewed as an object of `K⁺(𝒜)`. Every quasi-isomorphism `s : K ⟶ X` of `K⁺(𝒜)` has a left
inverse ([Stacks, Tag 013P]), and this left inverse is unique, because `K` is K-injective, so that
the localization functor `Q⁺ : K⁺(𝒜) ⥤ D⁺(𝒜)` is bijective on morphisms with target `K`. Sending
the index `s` of the ind-object `K/Qis⁺(𝒜) ⥤ ℋ`, `(s : K ⟶ X) ↦ F(X)`, to `F` of that left
inverse is therefore a cocone with vertex `F(K)`, which is essentially constant with value `F(K)`,
and whose coprojection at `𝟙 K` is the identity. Hence `K` computes `RF` relative to the
quasi-isomorphisms, in the sense of [Stacks, Tag 05SX], for every functor `F` out of `K⁺(𝒜)`.

Applied to `F : 𝒜 ⥤ ℬ` additive and the functor `K⁺(F) ⋙ Q⁺_ℬ : K⁺(𝒜) ⥤ D⁺(ℬ)`, and to the
complex `I[0]` of an injective object `I`, whose terms are `I` and `0`, this says that `I` is right
acyclic for `F` in the sense of [Stacks, Tag 0157](3).

## Main results

* `CategoryTheory.Functor.computesRightDerived_of_injective`: [Stacks, Tag 05TH], part (1).
* `CategoryTheory.Functor.computesRightDerived_single_of_injective`: [Stacks, Tag 05TH], part (2).

## Implementation notes

Part (1) is proved for an arbitrary functor `F : K⁺(𝒜) ⥤ ℋ` into an arbitrary category; the source
states it for an exact functor into a triangulated category, which is a special case, and its
proof does not use exactness either. Neither part assumes that `𝒜` has enough injectives, as in the
source; the derived category `D⁺(𝒜)` enters only the proof, through a model of it.

## References

* [Stacks, Tag 05TH]
* [Stacks, Tag 05SX], objects computing `RF`, and [Stacks, Tag 05S9], `RF` defined at an object
* [Stacks, Tag 0157], right acyclic objects
* [Stacks, Tag 013P], left inverses of quasi-isomorphisms out of complexes of injectives
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- A quasi-isomorphism `s : K ⟶ X` of `K⁺(C)` out of a bounded below complex `K` of injective
objects has a left inverse, and only one. -/
private lemma exists_unique_leftInverse_of_injective (K : HomotopyCategory.Plus C)
    [∀ n : ℤ, Injective (K.obj.as.X n)] {X : HomotopyCategory.Plus C} (s : K ⟶ X)
    (hs : HomotopyCategory.Plus.quasiIso C s) :
    (∃ r : X ⟶ K, s ≫ r = 𝟙 K) ∧ ∀ r r' : X ⟶ K, s ≫ r = 𝟙 K → s ≫ r' = 𝟙 K → r = r' := by
  let := HasDerivedCategory.standard C
  have hK : CochainComplex.IsKInjective K.obj.as := by
    obtain ⟨n, _⟩ := (CochainComplex.plus_iff _ _).1
      ((HomotopyCategory.plus_quotient_obj_iff K.obj.as).1 K.property)
    exact CochainComplex.isKInjective_of_injective _ n
  have hb := DerivedCategory.Plus.Qh_map_bijective_of_isKInjective X K hK
  have : IsIso (DerivedCategory.Plus.Qh.map s) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) s hs
  refine ⟨?_, fun r r' h h' ↦ hb.1 ?_⟩
  · obtain ⟨r, hr⟩ := hb.2 (CategoryTheory.inv (DerivedCategory.Plus.Qh.map s))
    refine ⟨r, (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K K hK).1 ?_⟩
    rw [Functor.map_comp, hr, IsIso.hom_inv_id, Functor.map_id]
  · rw [← cancel_epi (DerivedCategory.Plus.Qh.map s), ← Functor.map_comp, ← Functor.map_comp,
      h, h']

/-- **Stacks 05TH**, part (1). Let `K` be a bounded below complex of injective objects of an
abelian category `C`. Then `K` computes the right derived functor `RF` relative to the
quasi-isomorphisms of `K⁺(C)` (Stacks 05SX), for every functor `F : K⁺(C) ⥤ H`: `RF` is defined
at `K`, and the canonical map `F(K) ⟶ RF(K)` is an isomorphism. The source asks this for exact
functors into triangulated categories; it holds for all functors. -/
@[stacks 05TH "(1); for every functor out of `K⁺(𝒜)`, exact or not. (2) is \
  `CategoryTheory.Functor.computesRightDerived_single_of_injective`"]
theorem computesRightDerived_of_injective {H : Type u₃} [Category.{v₃} H]
    (F : HomotopyCategory.Plus C ⥤ H) (K : HomotopyCategory.Plus C)
    [∀ n : ℤ, Injective (K.obj.as.X n)] :
    F.ComputesRightDerived (HomotopyCategory.Plus.quasiIso C) K := by
  let W := HomotopyCategory.Plus.quasiIso C
  choose r hr using fun s : W.Under ⊤ K ↦ (exists_unique_leftInverse_of_injective K s.hom s.prop).1
  have huniq (s : W.Under ⊤ K) := (exists_unique_leftInverse_of_injective K s.hom s.prop).2
  let c : Cocone (MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ F) :=
    { pt := F.obj K
      ι :=
        { app := fun s ↦ F.map (r s)
          naturality := fun s t u ↦ by
            have h : u.right ≫ r t = r s :=
              huniq s _ _ (by rw [MorphismProperty.Under.w_assoc, hr]) (hr s)
            exact ((F.map_comp _ _).symm.trans (congrArg F.map h)).trans
              (Category.comp_id _).symm } }
  have hr₀ : r (MorphismProperty.Under.mk ⊤ (𝟙 K) (MorphismProperty.id_mem W K)) = 𝟙 K :=
    huniq _ _ _ (hr _) (Category.id_comp _)
  refine ⟨c, ⟨MorphismProperty.Under.mk ⊤ (𝟙 K) (MorphismProperty.id_mem W K), 𝟙 _, ?_,
    fun s ↦ ⟨MorphismProperty.Under.mk ⊤ (𝟙 K) (MorphismProperty.id_mem W K),
      MorphismProperty.Under.homMk (r s) (hr s), 𝟙 _, ?_⟩⟩, ?_⟩
  · change 𝟙 (F.obj K) ≫
        F.map (r (MorphismProperty.Under.mk ⊤ (𝟙 K) (MorphismProperty.id_mem W K))) = 𝟙 (F.obj K)
    rw [hr₀]
    exact (Category.id_comp _).trans (F.map_id K)
  · change F.map (r s) = F.map (r s) ≫ 𝟙 (F.obj K) ≫ F.map (𝟙 K)
    rw [F.map_id, Category.id_comp, Category.comp_id]
  · change IsIso (F.map (r (MorphismProperty.Under.mk ⊤ (𝟙 K) (MorphismProperty.id_mem W K))))
    rw [hr₀]
    exact (F.mapIso (Iso.refl K)).isIso_hom

/-- **Stacks 05TH**, part (2). Let `F : C ⥤ D` be an additive functor between abelian categories
and let `I` be an injective object of `C`. Then `I` is right acyclic for `F` in the sense of
Stacks 0157(3): the complex `I[0]` computes the right derived functor of
`K⁺(F) ⋙ Q⁺ : K⁺(C) ⥤ D⁺(D)` relative to the quasi-isomorphisms of `K⁺(C)` (Stacks 05SX). -/
@[stacks 05TH "(2); right acyclicity is 0157(3) in the 05SX form, with no hypothesis that \
  `𝒜` have enough injectives"]
theorem computesRightDerived_single_of_injective {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w} D] (F : C ⥤ D) [F.Additive] (I : C) [Injective I] :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj I) := by
  have (m : ℤ) : Injective (((HomotopyCategory.Plus.singleFunctor C 0).obj I).obj.as.X m) := by
    rcases eq_or_ne m 0 with rfl | hm
    · exact Injective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm inferInstance
    · exact Injective.of_iso
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I m hm).isoZero.symm
        inferInstance
  exact computesRightDerived_of_injective _ _

end CategoryTheory.Functor
