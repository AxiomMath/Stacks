module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow

/-!
# The canonical base change map of right derived functors on `D⁺`

Let `α : A ⥤ A'` and `β : B ⥤ B'` be exact functors of abelian categories, let `F : A ⥤ B` and
`F' : A' ⥤ B'` be additive, and let `c : F ⋙ β ⟶ α ⋙ F'` be a natural transformation, the
underived base change map. On the bounded below derived categories this induces the canonical
**base change map**

`β ∘ RF ⟶ RF' ∘ α`,

the composite of the identification `β ∘ RF = R(β ∘ F)` (the exact `β` passes through right
derivation), of `R(c) : R(β ∘ F) ⟶ R(F' ∘ α)`, and of the canonical comparison
`R(F' ∘ α) ⟶ RF' ∘ Rα = RF' ∘ α` of [Stacks, Tag 05T2]. Only the last map depends on more than
exactness and functoriality: it is the one Stacks writes `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` in the
situation of Cohomology of Stacks, Lemma 0GR3.

The base change map is invertible as soon as `c` is, and `α` carries injective objects to objects
right acyclic for `F'`: then the comparison of [Stacks, Tag 05T2] is invertible by
[Stacks, Tag 015M].

## Main definitions

* `Stacks.Cohomology.BoundedBelowComplexes.baseChangeMapPlus`: the canonical base change map.

## Main results

* `Stacks.Cohomology.BoundedBelowComplexes.isIso_baseChangeMapPlus`: it is an isomorphism when
  `c` is and `α` carries injectives to `F'`-acyclic objects.

## References

* [Stacks, Tag 05T2], the comparison `R(G ∘ F) ⟶ RG ∘ RF`
* [Stacks, Tag 015M], its invertibility under an acyclicity hypothesis
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA uA vA' uA' vB uB vB' uB' wA wA' wB wB'

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.Cohomology.BoundedBelowComplexes

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  [EnoughInjectives A] [EnoughInjectives A'] [EnoughInjectives B]
  (α : A ⥤ A') [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (β : B ⥤ B') [β.Additive] [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]

/-- `R(c) : RG ⟶ RG'`, the map of right derived functors on `D⁺` induced by a natural
transformation `c : G ⟶ G'` of additive functors. -/
def rightDerivedFunctorPlusMap {G G' : A ⥤ B'} [G.Additive] [G'.Additive] (c : G ⟶ G') :
    G.rightDerivedFunctorPlus ⟶ G'.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatTrans _ _ G.rightDerivedFunctorPlusUnith G'.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans c) DerivedCategory.Plus.Qh)

/-- The map `R(c) : RG ⟶ RG'` is an isomorphism when `c : G ⟶ G'` is. -/
instance isIso_rightDerivedFunctorPlusMap {G G' : A ⥤ B'} [G.Additive] [G'.Additive]
    (c : G ⟶ G') [IsIso c] : IsIso (rightDerivedFunctorPlusMap c) := by
  let e : G ≅ G' := asIso c
  have : rightDerivedFunctorPlusMap c =
      (Functor.rightDerivedFunctorPlusNatIso e).hom := by
    unfold rightDerivedFunctorPlusMap Functor.rightDerivedFunctorPlusNatIso
    rfl
  rw [this]
  infer_instance

/-- **The canonical base change map `β ∘ RF ⟶ RF' ∘ α`** on the bounded below derived categories,
induced by the underived base change map `c : F ⋙ β ⟶ α ⋙ F'`: the identification
`β ∘ RF = R(β ∘ F)` for the exact `β`, then `R(c)`, then the canonical comparison
`R(F' ∘ α) ⟶ RF' ∘ Rα` of [Stacks, Tag 05T2], with `Rα = α` for the exact `α`. -/
def baseChangeMapPlus (c : F ⋙ β ⟶ α ⋙ F') :
    F.rightDerivedFunctorPlus ⋙ β.mapDerivedCategoryPlus ⟶
      α.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus :=
  haveI := Functor.isIso_rightDerivedFunctorPlusComp_of_rightAcyclic F β
    (fun I _ ↦ Functor.rightAcyclic_of_exact β (F.obj I))
  Functor.whiskerLeft F.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus β).inv ≫
    inv (Functor.rightDerivedFunctorPlusComp F β) ≫ rightDerivedFunctorPlusMap c ≫
    Functor.rightDerivedFunctorPlusComp α F' ≫
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus α).hom
      F'.rightDerivedFunctorPlus

/-- **The canonical base change map is an isomorphism** as soon as the underived base change map
`c` is one and `α` carries every injective object to an object right acyclic for `F'`. -/
theorem isIso_baseChangeMapPlus (c : F ⋙ β ⟶ α ⋙ F') [IsIso c]
    (hacyclic : ∀ I : A, Injective I → F'.rightAcyclic (α.obj I)) :
    IsIso (baseChangeMapPlus α β F F' c) := by
  have := Functor.isIso_rightDerivedFunctorPlusComp_of_rightAcyclic F β
    (fun I _ ↦ Functor.rightAcyclic_of_exact β (F.obj I))
  have := Functor.isIso_rightDerivedFunctorPlusComp_of_rightAcyclic α F' hacyclic
  unfold baseChangeMapPlus
  infer_instance

end Stacks.Cohomology.BoundedBelowComplexes

end
