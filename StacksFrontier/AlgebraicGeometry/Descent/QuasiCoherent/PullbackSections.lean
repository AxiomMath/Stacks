module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback-sections presheaf of a quasi-coherent module

For a quasi-coherent module `F` on a scheme `S`, pulling `F` back to every
scheme over `S` and taking global sections defines an abelian-group-valued
presheaf on the category of schemes over `S`.

## Main definitions

* `AlgebraicGeometry.PullbackSectionsPresheaf` records the functor together with its
  prescribed values on objects and morphisms.
* `AlgebraicGeometry.pullbackSectionsMap` is the canonical pullback map on global
  sections.
* `AlgebraicGeometry.quasiCoherentPresheaf` constructs this functor for a
  quasi-coherent module.
* `AlgebraicGeometry.quasiCoherentPresheafFunctor` is its underlying functor.

## Main results

* `AlgebraicGeometry.pullbackId_unit` and `AlgebraicGeometry.pullbackComp_unit` compute the
  unit of the pullback-pushforward adjunction at an identity and at a composite.

## Implementation notes

The displayed equality in the source is represented by the isomorphisms in
`PullbackSectionsPresheaf.objIso`.  The field `map_objIso` requires its maps to
be the canonical maps induced by the pullback--pushforward adjunction and the
composition isomorphism for pullbacks; thus the construction is not merely an
objectwise assignment.

The functor laws are discharged in `quasiCoherentPresheafConstruction`, separately from
`quasiCoherentPresheaf`, so that the proof terms they generate do not enter the
elaboration of `quasiCoherentPresheafFunctor`.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local simp] Scheme.Modules.pseudofunctor_associativity
  Scheme.Modules.pseudofunctor_left_unitality
  Scheme.Modules.pseudofunctor_right_unitality
  CategoryTheory.Bicategory.toNatTrans_conjugateEquiv
  CategoryTheory.unit_conjugateEquiv
  Scheme.Modules.conjugateEquiv_pullbackId_hom
  CategoryTheory.Bicategory.Adjunction.ofCat_comp
  Scheme.Modules.conjugateEquiv_pullbackComp_inv

/-- **The right unitality of the inverse-image pseudofunctor, componentwise.** Identifying the
inverse image along `𝟙 X ≫ f` with the iterated one and then rewriting the composite is the
identification of the inverse image along the identity. -/
@[simp] lemma pullbackComp_hom_app_comp_pullbackCongr_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (h : 𝟙 X ≫ f = f) :
    (Scheme.Modules.pullbackComp (𝟙 X) f).hom.app M ≫
      (Scheme.Modules.pullbackCongr h).hom.app M =
        (Scheme.Modules.pullbackId X).hom.app
          ((Scheme.Modules.pullback f).obj M) := by
  let e := (Scheme.Modules.pullbackComp (𝟙 X) f).inv.app M
  rw [← cancel_epi e]
  simp only [e, Iso.inv_hom_id_app_assoc]
  have h := CategoryTheory.NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_right_unitality (f := f)) M
  convert h.symm using 1 <;>
    simp only [CategoryTheory.NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app,
      CategoryTheory.Functor.rightUnitor_hom_app,
      Scheme.Modules.pullbackCongr] <;> simp

/-- The unit of the pullback-pushforward adjunction at an identity morphism is the inverse of
the pushforward unitor, transported along `Scheme.Modules.pullbackId`. -/
lemma pullbackId_unit {X : Scheme.{u}} (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
      (Scheme.Modules.pushforward (𝟙 X)).map
        ((Scheme.Modules.pullbackId X).hom.app M) =
      (Scheme.Modules.pushforwardId X).inv.app M := by
  have h := CategoryTheory.unit_conjugateEquiv CategoryTheory.Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom M
  simpa [Scheme.Modules.conjugateEquiv_pullbackId_hom] using h.symm

/-- The unit of the pullback-pushforward adjunction is compatible with composition, transported
along `Scheme.Modules.pullbackComp`. -/
lemma pullbackComp_unit {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
      (Scheme.Modules.pushforward (f ≫ g)).map
        ((Scheme.Modules.pullbackComp f g).inv.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            ((Scheme.Modules.pullback g).obj M)) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          ((Scheme.Modules.pullback f).obj
            ((Scheme.Modules.pullback g).obj M)) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  simpa [CategoryTheory.Adjunction.comp_unit_app,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv] using h.symm

private lemma pullbackComp_congr {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (u : B ⟶ D) (v : A ⟶ D)
    (p : g ≫ h = u) (q : f ≫ u = v) (M : D.Modules) :
    (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
      (Scheme.Modules.pullbackCongr
        (by simp [Category.assoc, p, q] : (f ≫ g) ≫ h = v)).hom.app M =
    (Scheme.Modules.pullbackComp f g).inv.app
        ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackComp g h).hom.app M ≫
          (Scheme.Modules.pullbackCongr p).hom.app M) ≫
      (Scheme.Modules.pullbackComp f u).hom.app M ≫
      (Scheme.Modules.pullbackCongr q).hom.app M := by
  cases p
  cases q
  have hassoc := CategoryTheory.NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [CategoryTheory.NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.associator_hom_app] at hassoc
  simp only [Functor.comp_obj, Category.id_comp, eqToHom_app, Scheme.Modules.pullbackCongr,
    eqToIso.hom, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at hassoc ⊢
  rw [← cancel_epi
    ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
      (Scheme.Modules.pullbackComp f g).hom.app
        ((Scheme.Modules.pullback h).obj M))]
  simp only [← Category.assoc] at hassoc ⊢
  rw [hassoc]
  simp

private noncomputable def sectionMorphism {S : Scheme.{u}}
    (F : S.Modules) {X Y : Over S} (g : X ⟶ Y) :
    (Scheme.Modules.pullback Y.hom).obj F ⟶
      (Scheme.Modules.pushforward g.left).obj
        ((Scheme.Modules.pullback X.hom).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
      ((Scheme.Modules.pullback Y.hom).obj F) ≫
    (Scheme.Modules.pushforward g.left).map
      ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F)

private lemma sectionMorphism_comp {S : Scheme.{u}}
    (F : S.Modules) {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sectionMorphism F (f ≫ g) =
      sectionMorphism F g ≫
        (Scheme.Modules.pushforward g.left).map
          (sectionMorphism F f) ≫
        (Scheme.Modules.pushforwardComp f.left g.left).hom.app
          ((Scheme.Modules.pullback X.hom).obj F) := by
  let A := (Scheme.Modules.pullback Z.hom).obj F
  let B := (Scheme.Modules.pullback Y.hom).obj F
  let C := (Scheme.Modules.pullback X.hom).obj F
  let ag : (Scheme.Modules.pullback g.left).obj A ⟶ B :=
    (Scheme.Modules.pullbackComp g.left Z.hom).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F
  let af : (Scheme.Modules.pullback f.left).obj B ⟶ C :=
    (Scheme.Modules.pullbackComp f.left Y.hom).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Over.w f)).hom.app F
  unfold sectionMorphism
  simp only [Over.comp_left]
  rw [pullbackComp_congr f.left g.left Z.hom Y.hom X.hom
    (Over.w g) (Over.w f) F]
  change (Scheme.Modules.pullbackPushforwardAdjunction
      (f.left ≫ g.left)).unit.app A ≫
    (Scheme.Modules.pushforward (f.left ≫ g.left)).map
      ((Scheme.Modules.pullbackComp f.left g.left).inv.app A ≫
        (Scheme.Modules.pullback f.left).map ag ≫ af) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app A ≫
      (Scheme.Modules.pushforward g.left).map ag) ≫
      (Scheme.Modules.pushforward g.left).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app B ≫
          (Scheme.Modules.pushforward f.left).map af) ≫
      (Scheme.Modules.pushforwardComp f.left g.left).hom.app C
  have hn := (Scheme.Modules.pushforwardComp f.left g.left).hom.naturality
    ((Scheme.Modules.pullback f.left).map ag ≫ af)
  have hf := (Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.naturality ag
  rw [Functor.map_comp, ← Category.assoc, pullbackComp_unit f.left g.left]
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, Category.assoc] at hn hf ⊢
  rw [← hn, ← Functor.map_comp_assoc, ← hf, Functor.map_comp_assoc]

private lemma topMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (N : Y.Modules) (P : X.Modules)
    (b : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (c : N ⟶ (Scheme.Modules.pushforward f).obj P) :
    (b ≫ (Scheme.Modules.pushforward g).map c ≫
      (Scheme.Modules.pushforwardComp f g).hom.app P).app ⊤ ≫
        P.presheaf.map (eqToHom (show ⊤ = (f ≫ g) ⁻¹ᵁ ⊤ by simp)).op =
      (b.app ⊤ ≫ N.presheaf.map (eqToHom (show ⊤ = g ⁻¹ᵁ ⊤ by simp)).op) ≫
        (c.app ⊤ ≫ P.presheaf.map (eqToHom (show ⊤ = f ⁻¹ᵁ ⊤ by simp)).op) := by
  ext x
  simp [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app]
  rfl

/-- The canonical map on global sections induced by a morphism of schemes over
`S`.  It is obtained from the unit of pullback--pushforward adjunction, followed
by the canonical identifications of iterated pullback with pullback along the
composite. -/
noncomputable def pullbackSectionsMap {S : Scheme.{u}}
    (F : S.Modules) {X Y : Over S} (g : X ⟶ Y) :
    Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤) ⟶
      Γ((Scheme.Modules.pullback X.hom).obj F, ⊤) := by
  let M := (Scheme.Modules.pullback Y.hom).obj F
  let a : (Scheme.Modules.pullback g.left).obj M ⟶
      (Scheme.Modules.pullback X.hom).obj F :=
    (Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
      (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F
  let b : M ⟶ (Scheme.Modules.pushforward g.left).obj
      ((Scheme.Modules.pullback X.hom).obj F) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app M ≫
      (Scheme.Modules.pushforward g.left).map a
  exact b.app ⊤ ≫
    ((Scheme.Modules.pullback X.hom).obj F).presheaf.map
      (eqToHom (by simp)).op

private lemma pullbackSectionsMap_eq {S : Scheme.{u}}
    (F : S.Modules) {X Y : Over S} (g : X ⟶ Y) :
    pullbackSectionsMap F g = (sectionMorphism F g).app ⊤ ≫
      ((Scheme.Modules.pullback X.hom).obj F).presheaf.map
        (eqToHom (show ⊤ = g.left ⁻¹ᵁ ⊤ by simp)).op := by
  rfl

private lemma pullbackSectionsMap_id {S : Scheme.{u}}
    (F : S.Modules) (T : Over S) : pullbackSectionsMap F (𝟙 T) = 𝟙 _ := by
  unfold pullbackSectionsMap
  simp only [Over.id_left, pullbackComp_hom_app_comp_pullbackCongr_hom_app, pullbackId_unit,
    Scheme.Modules.pushforwardId_inv_app_app]
  simp only [Scheme.Modules.pushforward_obj_obj, Scheme.Hom.id_base,
    TopologicalSpace.Opens.map_top, Functor.id_obj, Functor.op_obj, Category.id_comp]
  convert ((Scheme.Modules.pullback T.hom).obj F).presheaf.map_id
    (op (⊤ : T.left.Opens)) using 1
  congr 1

private lemma pullbackSectionsMap_comp {S : Scheme.{u}}
    (F : S.Modules) {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackSectionsMap F (f ≫ g) =
      pullbackSectionsMap F g ≫ pullbackSectionsMap F f := by
  rw [pullbackSectionsMap_eq F (f ≫ g), pullbackSectionsMap_eq F g,
    pullbackSectionsMap_eq F f, sectionMorphism_comp F f g]
  exact topMap_comp f.left g.left
    ((Scheme.Modules.pullback Z.hom).obj F)
    ((Scheme.Modules.pullback Y.hom).obj F)
    ((Scheme.Modules.pullback X.hom).obj F)
    (sectionMorphism F g) (sectionMorphism F f)

/-- An abelian presheaf on schemes over `S` whose value on `T ⟶ S` is the
group of global sections of the pullback of `F` to `T`. -/
structure PullbackSectionsPresheaf (S : Scheme.{u})
    (F : S.Modules) where
  /-- The underlying abelian presheaf. -/
  functor : CategoryTheory.Functor (Over S)ᵒᵖ AddCommGrpCat.{u}
  /-- Its value on a scheme `T ⟶ S` is `Γ(T, T.hom⁺ F)`. -/
  objIso (T : (Over S)ᵒᵖ) :
    functor.obj T ≅ Γ((Scheme.Modules.pullback T.unop.hom).obj F, ⊤)
  /-- Under the objectwise identifications, the presheaf map is the canonical
  pullback map on global sections. -/
  map_objIso {T U : (Over S)ᵒᵖ} (g : T ⟶ U) :
    (objIso T).inv ≫ functor.map g ≫ (objIso U).hom =
      pullbackSectionsMap F g.unop

/-- The pullback-sections presheaf of an arbitrary module. -/
noncomputable def quasiCoherentPresheafConstruction (S : Scheme.{u})
    (F : S.Modules) : PullbackSectionsPresheaf S F := by
  let obj (T : (Over S)ᵒᵖ) : AddCommGrpCat.{u} :=
    AddCommGrpCat.of (Γ((Scheme.Modules.pullback T.unop.hom).obj F, ⊤))
  let map {T U : (Over S)ᵒᵖ} (g : T ⟶ U) : obj T ⟶ obj U :=
    pullbackSectionsMap F g.unop
  let functor : CategoryTheory.Functor (Over S)ᵒᵖ AddCommGrpCat.{u} :=
    { obj := obj
      map := map
      map_id := by intro T; exact pullbackSectionsMap_id F T.unop
      map_comp := by intro T U V f g; exact pullbackSectionsMap_comp F g.unop f.unop
    }
  refine { functor := functor, objIso := fun T => Iso.refl _, map_objIso := ?_ }
  intro T U g
  change (𝟙 _) ≫ pullbackSectionsMap F g.unop ≫ (𝟙 _) = _
  simp

/-- The contravariant functor on schemes over `S` which sends `f : T ⟶ S` to
`Γ(T, f⁺ F)`. -/
@[stacks 03DS]
noncomputable def quasiCoherentPresheaf (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] : PullbackSectionsPresheaf S F :=
  quasiCoherentPresheafConstruction S F

/-- The functor `(Sch/S)ᵒᵖ ⟶ Ab` underlying the pullback-sections
presheaf. -/
noncomputable abbrev quasiCoherentPresheafFunctor
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    CategoryTheory.Functor (Over S)ᵒᵖ AddCommGrpCat.{u} :=
  (quasiCoherentPresheaf S F).functor

/-- **The right unitality of the inverse-image pseudofunctor, componentwise.** Identifying the
inverse image along `𝟙 X ≫ f` with the iterated one and then rewriting the composite is the
identification of the inverse image along the identity.

This is `AlgebraicGeometry.pullbackComp_hom_app_comp_pullbackCongr_hom_app`, which is the same
statement without the file-private visibility. -/
@[simp] private alias pullbackComp_id_hom := pullbackComp_hom_app_comp_pullbackCongr_hom_app

end AlgebraicGeometry
