module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLerayOverRingMap
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

/-!
# The cocycle condition for the Leray isomorphism over maps of base rings

For a composite `X'' --j--> X' --i--> X` of schemes over a composite `A --ψ--> B --χ--> C` of
base rings, the Leray isomorphism of `AlgebraicGeometry.LerayOver.lerayIso` along `j ≫ i` is the
composite of those along `i` and `j`, read through the composition isomorphism of derived direct
images ([Stacks, Tag 079W]) and the composition isomorphism of restrictions of scalars.

## Main results

* `AlgebraicGeometry.LerayOver.lerayHom_comp`: the cocycle condition.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit derivedPullback derivedAdjunction
    derivedPushforwardCompIso)

universe u

namespace AlgebraicGeometry.LerayOver

attribute [local instance] HasDerivedCategory.standard

section Unit

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))

/-- The underived part of the Leray unit at an object of the homotopy category: the
identification of `Γ_B(X', K)` restricted to `A` with `Γ_A(X, g_* K)`. -/
def lerayUnitIso
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (restrictedSections φ f').obj K ≅
      DerivedCategory.Qh.obj (((baseSections f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
  (homotopyCompBaseIso (baseSections f') (ModuleCat.restrictScalars φ) (compositeSections f g)
      (baseSectionsRestrictIso φ f f' g w)).app K ≪≫
    DerivedCategory.Qh.mapIso
      ((Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f g) (ComplexShape.up ℤ)).app
        K).symm

/-- The Leray unit at an object `K` of the homotopy category: `lerayUnitIso`, followed by the unit
of `RΓ_A(X, -)` at `g_* K` and by `RΓ_A(X, -)` of the unit of `Rg_*` at `K`. -/
theorem lerayUnit_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (lerayUnit φ f f' g w).app K =
      (lerayUnitIso φ f f' g w K).hom ≫
        (sectionsUnit f).app
          (((modulePushforward g.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (sections f).map ((derivedPushforwardUnit g.toLRSHom.toShHom).app K) := by
  simp [lerayUnit, lerayUnitIso]

/-- `lerayHom_fac` at an object of the homotopy category. -/
theorem lerayHom_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (ModuleCat.restrictScalars φ).mapDerivedCategory.map ((sectionsUnit f').app K) ≫
        (lerayHom φ f f' g w).app (DerivedCategory.Qh.obj K) =
      (lerayUnit φ f f' g w).app K :=
  congrArg (fun τ => NatTrans.app τ K) (lerayHom_fac φ f f' g w)

end Unit

section HomotopyHelpers

variable {V W W' : Type*} [Category V] [Category W] [Category W'] [Preadditive V] [Preadditive W]
  [Preadditive W'] {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} [F.Additive] [G.Additive] [H.Additive]

/-- The composition isomorphism on homotopy categories is, at every object, the image of the
composition isomorphism on complexes. -/
theorem mapHomotopyCategoryCompIso_hom_app_as (e : F ⋙ G ≅ H)
    (K : HomotopyCategory V (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K =
      (HomotopyCategory.quotient W' (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K.as) :=
  rfl

/-- The inverse half of `mapHomotopyCategoryCompIso_hom_app_as`. -/
theorem mapHomotopyCategoryCompIso_inv_app_as (e : F ⋙ G ≅ H)
    (K : HomotopyCategory V (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app K =
      (HomotopyCategory.quotient W' (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app K.as) :=
  rfl

end HomotopyHelpers

/-- The forward map of `lerayUnitIso`: the factorization of derived restriction of scalars through
the homotopy category, followed by the localization of the two degreewise identifications. -/
theorem lerayUnitIso_hom {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
    (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (lerayUnitIso φ f f' g w K).hom =
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.hom.app
          (((baseSections f').mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (baseSectionsRestrictIso φ f f' g w)
              (ComplexShape.up ℤ)).hom.app K ≫
            (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f g)
              (ComplexShape.up ℤ)).inv.app K) := by
  simp [lerayUnitIso, homotopyCompBaseIso]

section Ring

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (ψ : A →+* B) (χ : B →+* C)

/-- The composition isomorphism of derived restrictions of scalars of
`StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp` is the one induced by the composition
isomorphism of restrictions of scalars. -/
theorem derivedRestrictScalarsComp_eq :
    StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ) rfl =
      Functor.mapDerivedCategoryCompIsoOfCompIso
        (ModuleCat.restrictScalarsComp'.{u} ψ χ (χ.comp ψ) rfl).symm := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} C) (ComplexShape.up ℤ)) fun E => ?_)
  rw [Functor.mapDerivedCategoryCompIso_hom_app_Q]
  have h := StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_factors.{u, u} ψ χ
    (χ.comp ψ) rfl E
  rw [← cancel_epi ((ModuleCat.restrictScalars ψ).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.restrictScalars χ).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≫
    (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
      ((ModuleCat.restrictScalars χ).mapDerivedCategoryFactors.inv.app E))]
  simp only [Category.assoc]
  rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- **The comparison of derived restrictions of scalars with the localization of the homotopy
category is compatible with composition.** At an object `J` of the homotopy category, the
composition isomorphism of derived restrictions of scalars followed by the two comparisons is the
comparison for the composite followed by the composition isomorphism of restrictions of scalars on
the homotopy category. -/
theorem derivedRestrictScalarsComp_inv_app_Qh
    (J : HomotopyCategory (ModuleCat.{u} C) (ComplexShape.up ℤ)) :
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ) rfl).inv.app
        (DerivedCategory.Qh.obj J) ≫
      (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
        ((ModuleCat.restrictScalars χ).mapDerivedCategoryFactorsh.hom.app J) ≫
      (ModuleCat.restrictScalars ψ).mapDerivedCategoryFactorsh.hom.app
        (((ModuleCat.restrictScalars χ).mapHomotopyCategory (ComplexShape.up ℤ)).obj J) =
    (ModuleCat.restrictScalars (χ.comp ψ)).mapDerivedCategoryFactorsh.hom.app J ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (ModuleCat.restrictScalarsComp'.{u} ψ χ (χ.comp ψ) rfl).symm (ComplexShape.up ℤ)).inv.app
          J) := by
  rw [derivedRestrictScalarsComp_eq, Functor.mapDerivedCategoryCompIso_inv_app_Qh]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc ((ModuleCat.restrictScalars ψ).mapDerivedCategory),
    Iso.inv_hom_id_app]
  simp

end Ring

section RingedSpaceUnit

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The unit of the derived adjunction along a composite of morphisms of ringed spaces**,
followed by the inverse composition isomorphism of derived direct images, is the composite of the
two units and of the composition isomorphism of derived pullbacks. -/
theorem derivedAdjunction_unit_comp_compIso_inv
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (derivedAdjunction (f ≫ g)).unit.app M ≫
        (derivedPushforwardCompIso f g).inv.app ((derivedPullback (f ≫ g)).obj M) =
      (derivedAdjunction g).unit.app M ≫
        (derivedPushforward g).map ((derivedAdjunction f).unit.app ((derivedPullback g).obj M) ≫
          (derivedPushforward f).map
            ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
              M)) := by
  have h := Adjunction.unit_rightAdjointUniq_hom_app
    (((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g))
    (derivedAdjunction (f ≫ g)) M
  rw [← h, Category.assoc]
  change _ ≫ (derivedPushforwardCompIso f g).hom.app _ ≫
    (derivedPushforwardCompIso f g).inv.app _ = _
  rw [Iso.hom_inv_id_app, Category.comp_id]
  simp [Adjunction.ofNatIsoLeft_unit, Adjunction.comp_unit_app]

end RingedSpaceUnit

section Cocycle

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (ψ : A →+* B) (χ : B →+* C)
  {X X' X'' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B))
  (f'' : X'' ⟶ Spec (CommRingCat.of C)) (i : X' ⟶ X) (j : X'' ⟶ X')
  (wi : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom ψ))
  (wj : j ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom χ))

include wi wj in
/-- The square of the composite. -/
theorem comp_w : (j ≫ i) ≫ f = f'' ≫ Spec.map (CommRingCat.ofHom (χ.comp ψ)) := by
  rw [Category.assoc, wi, ← Category.assoc, wj, Category.assoc, ← Spec.map_comp]
  rfl

/-- The degreewise comparison `(j ≫ i)_* ⟶ i_* ∘ j_*` on the homotopy categories, with its source
written along the composite of schemes. -/
def homotopyPushforwardComp :
    (modulePushforward (j ≫ i).toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward i.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Stacks.Cohomology.DerivedPushforwardAssociativity.pushforwardCompHomotopy
    j.toLRSHom.toShHom i.toLRSHom.toShHom

/-- The inverse composition isomorphism `R(j ≫ i)_* ⟶ Ri_* ∘ Rj_*` of derived direct images
([Stacks, Tag 079W]), with its source written along the composite of schemes. -/
def compInv : derivedPushforward (j ≫ i).toLRSHom.toShHom ⟶
    derivedPushforward j.toLRSHom.toShHom ⋙ derivedPushforward i.toLRSHom.toShHom :=
  (derivedPushforwardCompIso j.toLRSHom.toShHom i.toLRSHom.toShHom).inv

/-- The unit of `R(j ≫ i)_*` followed by `compInv`: [Stacks, Tag 0D5T] read backwards at a
complex. -/
theorem derivedPushforwardUnit_comp_compInv
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (j ≫ i).toLRSHom.toShHom).app K ≫
        (compInv i j).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((homotopyPushforwardComp i j).app K) ≫
        (derivedPushforwardUnit i.toLRSHom.toShHom).app
          (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (derivedPushforward i.toLRSHom.toShHom).map
          ((derivedPushforwardUnit j.toLRSHom.toShHom).app K) :=
  Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardUnit_comp_compIso_inv
    j.toLRSHom.toShHom i.toLRSHom.toShHom K

/-- **The underived cocycle, on the homotopy category of `A`-modules.** -/
theorem lerayUnitIso_comp_homotopy
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso
        (baseSectionsRestrictIso (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj))
        (ComplexShape.up ℤ)).hom.app K ≫
      (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f (j ≫ i))
        (ComplexShape.up ℤ)).inv.app K ≫
      ((baseSections f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((homotopyPushforwardComp i j).app K) =
    (Functor.mapHomotopyCategoryCompIso
        (ModuleCat.restrictScalarsComp'.{u} ψ χ (χ.comp ψ) rfl).symm (ComplexShape.up ℤ)).inv.app
        (((baseSections f'').mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.restrictScalars ψ).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (baseSectionsRestrictIso χ f' f'' j wj)
            (ComplexShape.up ℤ)).hom.app K ≫
          (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f' j)
            (ComplexShape.up ℤ)).inv.app K) ≫
      (Functor.mapHomotopyCategoryCompIso (baseSectionsRestrictIso ψ f f' i wi)
        (ComplexShape.up ℤ)).hom.app
          (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f i) (ComplexShape.up ℤ)).inv.app
          (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            K) := by
  simp only [homotopyPushforwardComp, mapHomotopyCategoryCompIso_hom_app_as,
    mapHomotopyCategoryCompIso_inv_app_as]
  refine Stacks.Cohomology.DerivedPushforwardAssociativity.quotient_map_congr ?_
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  ext x
  rfl

/-- **The underived cocycle.** The identifications of the Leray units along `j`, `i` and `j ≫ i`
are compatible with the degreewise comparison `(j ≫ i)_* ⟶ i_* ∘ j_*` and the composition of
restrictions of scalars. -/
theorem lerayUnitIso_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (lerayUnitIso (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj) K).hom ≫
        (homotopyBaseSections f).map
          ((homotopyPushforwardComp i j).app K) =
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ) rfl).inv.app
          (DerivedCategory.Qh.obj
            (((baseSections f'').mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (ModuleCat.restrictScalars ψ).mapDerivedCategory.map (lerayUnitIso χ f' f'' j wj K).hom ≫
        (lerayUnitIso ψ f f' i wi
          (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            K)).hom := by
  rw [lerayUnitIso_hom, lerayUnitIso_hom, lerayUnitIso_hom,
    Functor.map_comp ((ModuleCat.restrictScalars ψ).mapDerivedCategory)]
  have hnat := (ModuleCat.restrictScalars ψ).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso (baseSectionsRestrictIso χ f' f'' j wj)
        (ComplexShape.up ℤ)).hom.app K ≫
      (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso f' j)
        (ComplexShape.up ℤ)).inv.app K)
  simp only [Functor.comp_map] at hnat
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% (derivedRestrictScalarsComp_inv_app_Qh ψ χ
    (((baseSections f'').mapHomotopyCategory (ComplexShape.up ℤ)).obj K))]
  have hK := congrArg DerivedCategory.Qh.map (lerayUnitIso_comp_homotopy ψ χ f f' f'' i j wi wj K)
  simp only [Functor.map_comp] at hK
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc, hK]

/-- The left-hand side of the cocycle condition, after the unit of the derived sections on
`X''`. -/
theorem lerayHom_comp_lhs
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (ModuleCat.restrictScalars (χ.comp ψ)).mapDerivedCategory.map ((sectionsUnit f'').app K) ≫
        (lerayHom (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj)).app
          (DerivedCategory.Qh.obj K) ≫
        (sections f).map ((compInv i j).app (DerivedCategory.Qh.obj K)) =
      (lerayUnitIso (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj) K).hom ≫
        (homotopyBaseSections f).map
          ((homotopyPushforwardComp i j).app K) ≫
        (sectionsUnit f).app
          (((modulePushforward i.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (sections f).map ((derivedPushforwardUnit i.toLRSHom.toShHom).app
            (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (sections f).map ((derivedPushforward i.toLRSHom.toShHom).map
          ((derivedPushforwardUnit j.toLRSHom.toShHom).app K)) := by
  rw [reassoc_of% lerayHom_fac_app, lerayUnit_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp, derivedPushforwardUnit_comp_compInv]
  have hn := (sectionsUnit f).naturality
    ((homotopyPushforwardComp i j).app K)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, reassoc_of% hn.symm]
  rfl

/-- The right-hand side of the cocycle condition, after the unit of the derived sections on
`X''`. -/
theorem lerayHom_comp_rhs
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (ModuleCat.restrictScalars (χ.comp ψ)).mapDerivedCategory.map ((sectionsUnit f'').app K) ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ)
          rfl).inv.app ((sections f'').obj (DerivedCategory.Qh.obj K)) ≫
        (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
          ((lerayHom χ f' f'' j wj).app (DerivedCategory.Qh.obj K)) ≫
        (lerayHom ψ f f' i wi).app
          ((derivedPushforward j.toLRSHom.toShHom).obj (DerivedCategory.Qh.obj K)) =
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ) rfl).inv.app
          (DerivedCategory.Qh.obj
            (((baseSections f'').mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (ModuleCat.restrictScalars ψ).mapDerivedCategory.map (lerayUnitIso χ f' f'' j wj K).hom ≫
        (lerayUnitIso ψ f f' i wi
          (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            K)).hom ≫
        (sectionsUnit f).app
          (((modulePushforward i.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (sections f).map ((derivedPushforwardUnit i.toLRSHom.toShHom).app
            (((modulePushforward j.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (sections f).map ((derivedPushforward i.toLRSHom.toShHom).map
          ((derivedPushforwardUnit j.toLRSHom.toShHom).app K)) := by
  have hc := (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ
    (χ.comp ψ) rfl).inv.naturality ((sectionsUnit f'').app K)
  simp only [Functor.comp_map] at hc
  simp only [reassoc_of% hc]
  rw [← Functor.map_comp_assoc ((ModuleCat.restrictScalars ψ).mapDerivedCategory)
    ((ModuleCat.restrictScalars χ).mapDerivedCategory.map ((sectionsUnit f'').app K)),
    lerayHom_fac_app, lerayUnit_app]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (lerayHom ψ f f' i wi).naturality
    ((derivedPushforwardUnit j.toLRSHom.toShHom).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn, reassoc_of% lerayHom_fac_app, lerayUnit_app]
  simp only [Category.assoc]

/-- **The cocycle condition for the Leray isomorphism.** Along `X'' --j--> X' --i--> X` over
`A --ψ--> B --χ--> C`, the Leray comparison along `j ≫ i`, followed by the inverse composition
isomorphism `R(j ≫ i)_* ≅ Ri_* ∘ Rj_*`, is the inverse composition isomorphism of restrictions of
scalars followed by the Leray comparisons along `j` and along `i`. -/
theorem lerayHom_comp
    (Y : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace))) :
    (lerayHom (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj)).app Y ≫
        (sections f).map ((compInv i j).app Y) =
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ) rfl).inv.app
          ((sections f'').obj Y) ≫
        (ModuleCat.restrictScalars ψ).mapDerivedCategory.map ((lerayHom χ f' f'' j wj).app Y) ≫
        (lerayHom ψ f f' i wi).app ((derivedPushforward j.toLRSHom.toShHom).obj Y) := by
  let τ₁ : sections f'' ⋙ (ModuleCat.restrictScalars (χ.comp ψ)).mapDerivedCategory ⟶
      derivedPushforward j.toLRSHom.toShHom ⋙ derivedPushforward i.toLRSHom.toShHom ⋙
        sections f :=
    lerayHom (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj) ≫
      Functor.whiskerRight (compInv i j) (sections f)
  let τ₂ : sections f'' ⋙ (ModuleCat.restrictScalars (χ.comp ψ)).mapDerivedCategory ⟶
      derivedPushforward j.toLRSHom.toShHom ⋙ derivedPushforward i.toLRSHom.toShHom ⋙
        sections f :=
    Functor.whiskerLeft (sections f'')
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ)
          rfl).inv ≫
      Functor.whiskerRight (lerayHom χ f' f'' j wj)
        (ModuleCat.restrictScalars ψ).mapDerivedCategory ≫
      Functor.whiskerLeft (derivedPushforward j.toLRSHom.toShHom) (lerayHom ψ f f' i wi)
  have key : τ₁ = τ₂ := by
    refine Functor.rightDerived_ext
      (sections f'' ⋙ (ModuleCat.restrictScalars (χ.comp ψ)).mapDerivedCategory)
      (Functor.whiskerRight (sectionsUnit f'')
        (ModuleCat.restrictScalars (χ.comp ψ)).mapDerivedCategory)
      (qis X'') _ τ₁ τ₂ ?_
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, τ₁, τ₂]
    rw [lerayHom_comp_lhs ψ χ f f' f'' i j wi wj K, lerayHom_comp_rhs ψ χ f f' f'' i j wi wj K,
      ← Category.assoc,
      lerayUnitIso_comp ψ χ f f' f'' i j wi wj K]
    simp only [Category.assoc]
  exact congrArg (fun τ => NatTrans.app τ Y) key

/-- The inverse form of the cocycle condition. -/
theorem lerayIso_inv_comp
    (Y : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace))) :
    (lerayIso (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj)).inv.app Y ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ)
          rfl).inv.app ((sections f'').obj Y) =
      (sections f).map ((compInv i j).app Y) ≫
        (lerayIso ψ f f' i wi).inv.app ((derivedPushforward j.toLRSHom.toShHom).obj Y) ≫
        (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
          ((lerayIso χ f' f'' j wj).inv.app Y) := by
  have h := lerayHom_comp ψ χ f f' f'' i j wi wj Y
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom]
  change _ = (lerayHom (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj)).app Y ≫ _
  rw [reassoc_of% h]
  change _ = _ ≫ (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
      ((lerayIso χ f' f'' j wj).hom.app Y) ≫ (lerayIso ψ f f' i wi).hom.app _ ≫
    (lerayIso ψ f f' i wi).inv.app _ ≫ _
  rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  simp

/-- The composition isomorphism of derived pullbacks `Li^* ⋙ Lj^* ≅ L(j ≫ i)^*`
([Stacks, Tag 0D5S]), with its target written along the composite of schemes. -/
def pullbackCompHom : derivedPullback i.toLRSHom.toShHom ⋙ derivedPullback j.toLRSHom.toShHom ⟶
    derivedPullback (j ≫ i).toLRSHom.toShHom :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical j.toLRSHom.toShHom
    i.toLRSHom.toShHom).hom

/-- **The unit of the derived adjunction along a composite**, followed by the inverse composition
isomorphism of derived direct images, is the composite of the two units. -/
theorem derivedAdjunction_unit_comp_compInv
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedAdjunction (j ≫ i).toLRSHom.toShHom).unit.app M ≫
        (compInv i j).app ((derivedPullback (j ≫ i).toLRSHom.toShHom).obj M) =
      (derivedAdjunction i.toLRSHom.toShHom).unit.app M ≫
        (derivedPushforward i.toLRSHom.toShHom).map
          ((derivedAdjunction j.toLRSHom.toShHom).unit.app
            ((derivedPullback i.toLRSHom.toShHom).obj M)) ≫
        (derivedPushforward i.toLRSHom.toShHom).map ((derivedPushforward j.toLRSHom.toShHom).map
          ((pullbackCompHom i j).app M)) := by
  have h := derivedAdjunction_unit_comp_compIso_inv j.toLRSHom.toShHom i.toLRSHom.toShHom M
  rw [Functor.map_comp] at h
  exact h

end Cocycle

/-! ### Pulling derived global sections back -/

section Pullback

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {X X' : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))

/-- Naturality of the inverse Leray isomorphism. -/
private theorem lerayIso_inv_naturality
    {G₁ G₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))}
    (a : G₁ ⟶ G₂) :
    (sections f).map ((derivedPushforward g.toLRSHom.toShHom).map a) ≫
        (lerayIso φ f f' g w).inv.app G₂ =
      (lerayIso φ f f' g w).inv.app G₁ ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map ((sections f').map a) :=
  (lerayIso φ f f' g w).inv.naturality a

/-- **The pullback map is natural.** -/
theorem pullbackSectionsMap_naturality
    {F₁ F₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (a : F₁ ⟶ F₂) :
    (sections f).map a ≫ pullbackSectionsMap φ f f' g w F₂ =
      pullbackSectionsMap φ f f' g w F₁ ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map
          ((sections f').map ((derivedPullback g.toLRSHom.toShHom).map a)) := by
  simp only [pullbackSectionsMap]
  rw [← Functor.map_comp_assoc, ← Adjunction.unit_naturality, Functor.map_comp, Category.assoc,
    lerayIso_inv_naturality φ f f' g w, Category.assoc]

end Pullback

section PullbackCocycle

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (ψ : A →+* B) (χ : B →+* C)
  {X X' X'' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of B))
  (f'' : X'' ⟶ Spec (CommRingCat.of C)) (i : X' ⟶ X) (j : X'' ⟶ X')
  (wi : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom ψ))
  (wj : j ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom χ))

/-- **The cocycle condition for pulling derived global sections back.** Pulling back along
`j ≫ i` is pulling back along `i` and then along `j`, read through the composition isomorphisms
of derived pullbacks and of restrictions of scalars. -/
theorem pullbackSectionsMap_comp
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    pullbackSectionsMap (χ.comp ψ) f f'' (j ≫ i) (comp_w ψ χ f f' f'' i j wi wj) G ≫
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u} ψ χ (χ.comp ψ)
          rfl).inv.app ((sections f'').obj ((derivedPullback (j ≫ i).toLRSHom.toShHom).obj G)) =
      pullbackSectionsMap ψ f f' i wi G ≫
        (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
          (pullbackSectionsMap χ f' f'' j wj ((derivedPullback i.toLRSHom.toShHom).obj G)) ≫
        (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
          ((ModuleCat.restrictScalars χ).mapDerivedCategory.map
            ((sections f'').map ((pullbackCompHom i j).app G))) := by
  simp only [pullbackSectionsMap, Category.assoc]
  rw [lerayIso_inv_comp ψ χ f f' f'' i j wi wj, ← Functor.map_comp_assoc,
    derivedAdjunction_unit_comp_compInv]
  have n3 := congrArg (ModuleCat.restrictScalars ψ).mapDerivedCategory.map
    (lerayIso_inv_naturality χ f' f'' j wj ((pullbackCompHom i j).app G))
  simp only [Functor.map_comp, Category.assoc] at n3 ⊢
  rw [reassoc_of% lerayIso_inv_naturality ψ f f' i wi,
    reassoc_of% lerayIso_inv_naturality ψ f f' i wi, n3]
  rfl

end PullbackCocycle

end AlgebraicGeometry.LerayOver

end
