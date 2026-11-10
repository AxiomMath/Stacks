module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# Associativity of the composition isomorphism of derived pullback at the locally small model

The cocycle identity of [Stacks, Tag 0D5S] for the composition isomorphism
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of derived pullback holds at the standard model
(`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc_app`);
it is transported here to the locally small model through the comparison of the two models,
which is compatible with the composition isomorphisms
(`StacksDraft.DerivedModel.derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

namespace StacksDraft.DerivedModel

/-- Two morphisms of functors agree as soon as they agree on the image of an equivalence. -/
theorem natTrans_ext_of_equivalence {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) {F G : D ⥤ E} (α β : F ⟶ G) (h : ∀ K : C, α.app (e.functor.obj K) =
      β.app (e.functor.obj K)) : α = β := by
  ext M
  have hα := α.naturality ((e.counitIso.app M).inv)
  have hβ := β.naturality ((e.counitIso.app M).inv)
  simp only [Functor.id_obj, Functor.comp_obj] at hα hβ
  rw [← cancel_mono (G.map (e.counitIso.app M).inv), ← hα, ← hβ, h]

/-- The chase behind `derivedPullbackCompIsoCanonical_assoc_app_locallySmall`, with every
morphism a variable. -/
private theorem assoc_chase {C : Type*} [Category C] {Oa Ob Oc Od Oe Of Og Oh Oi Oj Ok Ol : C}
    {x₁ : Oa ⟶ Ob} {x₂ : Ob ⟶ Oc} {y₁ : Oa ⟶ Oh} {y₂ : Oh ⟶ Oc} {m : Oc ⟶ Od}
    {p : Ob ⟶ Oe} {q : Oe ⟶ Of} {s₁ : Of ⟶ Od} {u : Oa ⟶ Og} {v : Og ⟶ Oe} {w : Og ⟶ Oi}
    {z : Oi ⟶ Oj} {t : Oj ⟶ Of} {r : Oj ⟶ Ok} {s₃ : Ok ⟶ Od} {k : Oh ⟶ Ol} {z' : Ol ⟶ Ok}
    {ℓ : Oi ⟶ Ol}
    (c₁ : x₂ ≫ m = p ≫ q ≫ s₁) (n₁ : x₁ ≫ p = u ≫ v) (c₂ : v ≫ q = w ≫ z ≫ t)
    (hstd : t ≫ s₁ = r ≫ s₃) (c₃ : y₂ ≫ m = k ≫ z' ≫ s₃) (c₄ : y₁ ≫ k = u ≫ w ≫ ℓ)
    (n₂ : ℓ ≫ z' = z ≫ r) :
    x₁ ≫ x₂ ≫ m = y₁ ≫ y₂ ≫ m := by
  rw [c₁, reassoc_of% n₁, reassoc_of% c₂, hstd, c₃, reassoc_of% c₄, reassoc_of% n₂]

variable {X Y Z W : RingedSpace.{u, u}}

/-- **The cocycle identity of [Stacks, Tag 0D5S] at the locally small model.** The two
identifications of `Lh^* ⋙ Lg^* ⋙ Lf^*` with `L(f ≫ g ≫ h)^*` agree at every object. -/
theorem derivedPullbackCompIsoCanonical_assoc_app_locallySmall (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W)
    (M : @DerivedCategory _ _ _ (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing W)))) :
    (@derivedPullbackCompIsoCanonical _ _ _ f g
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app
          ((@derivedPullback _ _ h
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
            (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
            inferInstance).obj M) ≫
      (@derivedPullbackCompIsoCanonical _ _ _ (f ≫ g) h
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app M =
    (@derivedPullback _ _ f
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        inferInstance).map
        ((@derivedPullbackCompIsoCanonical _ _ _ g h
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app M) ≫
      (@derivedPullbackCompIsoCanonical _ _ _ f (g ≫ h)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app M := by
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
    (SheafOfModules.{u} (structureSheafRing X))
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
    (SheafOfModules.{u} (structureSheafRing Y))
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
    (SheafOfModules.{u} (structureSheafRing Z))
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
    (SheafOfModules.{u} (structureSheafRing W))
  let E := Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing W))
  let EX := Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing X))
  -- both sides are components of morphisms of functors; compare them on the image of `E`
  let α : derivedPullback h ⋙ derivedPullback g ⋙ derivedPullback f ⟶
      derivedPullback ((f ≫ g) ≫ h) :=
    Functor.whiskerLeft (derivedPullback h) (derivedPullbackCompIsoCanonical f g).hom ≫
      (derivedPullbackCompIsoCanonical (f ≫ g) h).hom
  let β : derivedPullback h ⋙ derivedPullback g ⋙ derivedPullback f ⟶
      derivedPullback ((f ≫ g) ≫ h) :=
    Functor.whiskerRight (derivedPullbackCompIsoCanonical g h).hom (derivedPullback f) ≫
      (derivedPullbackCompIsoCanonical f (g ≫ h)).hom
  suffices hαβ : α = β from congr_app hαβ M
  refine natTrans_ext_of_equivalence E α β fun K => ?_
  change (derivedPullbackCompIsoCanonical f g).hom.app ((derivedPullback h).obj (E.functor.obj K)) ≫
      (derivedPullbackCompIsoCanonical (f ≫ g) h).hom.app (E.functor.obj K) =
    (derivedPullback f).map ((derivedPullbackCompIsoCanonical g h).hom.app (E.functor.obj K)) ≫
      (derivedPullbackCompIsoCanonical f (g ≫ h)).hom.app (E.functor.obj K)
  refine (cancel_mono ((derivedPullbackModelIso ((f ≫ g) ≫ h)).inv.app K)).1 ?_
  simp only [Category.assoc]
  have c₁ := derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso (f ≫ g) h K
  have c₂ := derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso f g
    ((@derivedPullback _ _ h (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      inferInstance).obj K)
  have c₃ : (derivedPullbackCompIsoCanonical f (g ≫ h)).hom.app (E.functor.obj K) ≫
      (derivedPullbackModelIso ((f ≫ g) ≫ h)).inv.app K = _ :=
    derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso f (g ≫ h) K
  have c₄ := derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso g h K
  have hstd :=
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc_app
      f g h K
  have n₁ := (derivedPullbackCompIsoCanonical f g).hom.naturality
    ((derivedPullbackModelIso h).inv.app K)
  have n₂ := (derivedPullbackModelIso f).inv.naturality
    ((@derivedPullbackCompIsoCanonical _ _ _ g h (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)).hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂
  have c₄' := ((derivedPullback f).map_comp _ _).symm.trans
    ((congrArg (derivedPullback f).map c₄).trans (((derivedPullback f).map_comp _ _).trans
      (congrArg ((derivedPullback f).map _ ≫ ·) ((derivedPullback f).map_comp _ _))))
  have hstd' := (EX.functor.map_comp _ _).symm.trans
    ((congrArg EX.functor.map hstd).trans (EX.functor.map_comp _ _))
  exact (assoc_chase c₁ n₁.symm c₂ hstd' c₃ c₄' n₂).trans (Category.assoc _ _ _).symm

end StacksDraft.DerivedModel
