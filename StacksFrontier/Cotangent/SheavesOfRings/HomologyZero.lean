module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivations

/-!
# The zeroth homology of the cotangent complex of a morphism of sheaves of rings

For a morphism `f : A ⟶ B` of sheaves of commutative rings on a site, the cotangent complex of
`f` vanishes in positive degrees, so its zeroth homology is the cokernel of the difference of
the two faces `Ω_{P₁/A} ⊗ B ⇉ Ω_{P₀/A} ⊗ B` of the standard resolution. That cokernel
corepresents the `A`-derivations of `B`, so the zeroth homology is the sheaf of relative
differentials `Ω_{B/A}`.

## Main definitions

* `CategoryTheory.Sheaf.augSection` is the canonical set-theoretic section `B ⟶ P₀` of the
  augmentation of the standard resolution, and `CategoryTheory.Sheaf.augLift` lifts a local
  section of `P₀` to `P₁`.
* `CategoryTheory.Sheaf.descendDerivation` descends an `A`-derivation of `P₀` equalising the
  two faces to an `A`-derivation of `B`.
* `CategoryTheory.Sheaf.homologyZeroProj` is the projection of the degree-zero term of the
  base-changed simplicial module onto the zeroth homology of the cotangent complex, and
  `CategoryTheory.Sheaf.homologyZeroDerivation` is the universal derivation it carries.

## Main results

* `CategoryTheory.Sheaf.existsUnique_homologyZeroDesc`: the zeroth homology is the cokernel of
  the difference of the two faces.
* `CategoryTheory.Sheaf.homologyZeroDerivation_universal` and
  `CategoryTheory.Sheaf.derivationsFunctor_corepresentableBy`: the zeroth homology corepresents
  the functor of relative derivations.
* `CategoryTheory.Sheaf.cotangentComplex_homologyZeroIso`: the zeroth homology of the cotangent
  complex is the sheaf of relative differentials.

## References

* [Stacks Project, Tag 08UR](https://stacks.math.columbia.edu/tag/08UR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe t u v w

namespace CategoryTheory.Sheaf

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J CommRingCat.{max u v w}}

/-- Transport of local sections along an equality of sheaves of `A`-algebras. -/
noncomputable def transportSections {X Y : Under A} (h : X = Y) (U : Cᵒᵖ)
    (x : X.right.obj.obj U) : Y.right.obj.obj U :=
  (eqToHom h).right.hom.app U x

/-- Transport along the identity leaves a local section unchanged. -/
@[simp]
theorem transportSections_rfl {X : Under A} (U : Cᵒᵖ) (x : X.right.obj.obj U) :
    transportSections (rfl : X = X) U x = x := rfl

/-- Transport along a composite of equalities is the composite of the transports. -/
theorem transportSections_trans {X Y Z : Under A} (h : X = Y) (h' : Y = Z) (U : Cᵒᵖ)
    (x : X.right.obj.obj U) :
    transportSections h' U (transportSections h U x) = transportSections (h.trans h') U x := by
  show (((eqToHom h : X ⟶ Y) ≫ (eqToHom h' : Y ⟶ Z)).right.hom.app U) x = _
  rw [eqToHom_trans]
  rfl

/-- Transport and its inverse cancel. -/
@[simp]
theorem transportSections_symm {X Y : Under A} (h : X = Y) (U : Cᵒᵖ)
    (x : X.right.obj.obj U) : transportSections h.symm U (transportSections h U x) = x := by
  rw [transportSections_trans]; rfl

/-- Transport and its inverse cancel in the other order. -/
@[simp]
theorem transportSections_symm' {X Y : Under A} (h : X = Y) (U : Cᵒᵖ)
    (y : Y.right.obj.obj U) : transportSections h U (transportSections h.symm U y) = y := by
  rw [transportSections_trans]; rfl

/-- A morphism applied after a transport is the composite applied directly. -/
theorem apply_transportSections {X Y Z : Under A} (h : X = Y) (g : Y ⟶ Z) (U : Cᵒᵖ)
    (x : X.right.obj.obj U) :
    g.right.hom.app U (transportSections h U x) = ((eqToHom h ≫ g).right.hom.app U) x := rfl

/-- Composition of morphisms of sheaves of algebras is composition on local sections. -/
theorem comp_sections {X Y Z : Under A} (g : X ⟶ Y) (g' : Y ⟶ Z) (U : Cᵒᵖ)
    (x : X.right.obj.obj U) :
    (g ≫ g').right.hom.app U x = g'.right.hom.app U (g.right.hom.app U x) := rfl

/-- Restriction of scalars along a whiskered morphism of presheaves of commutative rings acts
through that morphism. -/
theorem presheafRestrictScalars_smul {C : Type u} [Category.{v} C]
    {R₁ R₂ : Cᵒᵖ ⥤ CommRingCat.{t}} (q : R₁ ⟶ R₂)
    (M : PresheafOfModules.{t} (R₂ ⋙ forget₂ CommRingCat.{t} RingCat.{t}))
    (U : Cᵒᵖ) (p : R₁.obj U) (c : R₂.obj U) (h : (q.app U) p = c) (m : M.obj U) :
    p • (show ((PresheafOfModules.restrictScalars
        (Functor.whiskerRight q (forget₂ CommRingCat.{t} RingCat.{t}))).obj M).obj U from m)
      = c • m := by
  subst h; rfl

end Transport

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ### The two faces of the standard resolution in degree zero -/

/-- The term in degree `n` of the standard resolution is the `(n + 1)`-fold iterate of the
free-forgetful comonad applied to `B`. -/
alias resObjEq := standardResolution_obj

/-- A face `P₁ ⟶ P₀` of the standard resolution is the corresponding Godement face at `Under.mk f`,
up to the identifications of the terms. -/
private theorem delta_eq_godementFace (k : Fin 2) :
    (standardResolution J f).left.δ k =
      eqToHom (resObjEq J f 1) ≫
        (Godement.face (standardResolutionComonad J A).ε 1 k).app (Under.mk f) ≫
        eqToHom (resObjEq J f 0).symm := by
  have h := NatTrans.congr_app (standardResolutionFunctor_face J A 0 k) (Under.mk f)
  simp only [NatTrans.comp_app, eqToHom_app] at h
  exact h

/-- The zeroth face `P₁ ⟶ P₀` is the counit at `P₀`. -/
theorem delta_zero_eq :
    (standardResolution J f).left.δ (0 : Fin 2) =
      eqToHom (resObjEq J f 1) ≫
        (standardResolutionComonad J A).ε.app
          ((standardResolutionComonad J A).obj (Under.mk f)) ≫
        eqToHom (resObjEq J f 0).symm := by
  rw [delta_eq_godementFace, Godement.Prep.face_zero]
  rfl

/-- The first face `P₁ ⟶ P₀` is the comonad applied to the counit at `B`. -/
theorem delta_one_eq :
    (standardResolution J f).left.δ (1 : Fin 2) =
      eqToHom (resObjEq J f 1) ≫
        (standardResolutionComonad J A).map ((standardResolutionComonad J A).ε.app (Under.mk f)) ≫
        eqToHom (resObjEq J f 0).symm := by
  rw [delta_eq_godementFace]
  rfl

/-- The augmentation `P₀ ⟶ B` is the counit at `B`. -/
theorem augmentation_eq :
    (standardResolution J f).hom.app (op ⦋0⦌) =
      eqToHom (resObjEq J f 0) ≫ (standardResolutionComonad J A).ε.app (Under.mk f) := by
  have h := NatTrans.congr_app (standardResolutionFunctor_augmentation J A) (Under.mk f)
  simp only [NatTrans.comp_app, eqToHom_app] at h
  rw [show (standardResolution J f).hom.app (op ⦋0⦌) =
      ((standardResolutionFunctor J A).hom.app (op ⦋0⦌)).app (Under.mk f) ≫
        eqToHom (Functor.congr_obj (standardResolutionFunctor_point J A) (Under.mk f)) from rfl,
    h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl


/-- The unit of the free-forgetful adjunction, on local sections: the variable `[x]`. -/
noncomputable def variableSections (X : Under A) (U : Cᵒᵖ) (x : X.right.obj.obj U) :
    (((standardResolutionComonad J A : Comonad (Under A)) :
      Under A ⥤ Under A).obj X).right.obj.obj U :=
  ((freeAlgebraSheafAdjunction J A).unit.app ((forgetAlgebraSheaf J A).obj X)).hom.app U x

/-- The counit sends the variable `[x]` back to `x`. -/
theorem counit_variableSections (X : Under A) (U : Cᵒᵖ) (x : X.right.obj.obj U) :
    ((standardResolutionComonad J A).ε.app X).right.hom.app U (variableSections J X U x) = x :=
  congrArg (fun (t : (forgetAlgebraSheaf J A).obj X ⟶ (forgetAlgebraSheaf J A).obj X) =>
      t.hom.app U x)
    ((freeAlgebraSheafAdjunction J A).right_triangle_components (Y := X))

/-- The variables are natural in the sheaf of algebras. -/
theorem variableSections_naturality {X Y : Under A} (g : X ⟶ Y) (U : Cᵒᵖ)
    (x : X.right.obj.obj U) :
    (((standardResolutionComonad J A : Comonad (Under A)) :
        Under A ⥤ Under A).map g).right.hom.app U (variableSections J X U x) =
      variableSections J Y U (g.right.hom.app U x) :=
  (congrArg (fun (t : (forgetAlgebraSheaf J A).obj X ⟶ (forgetAlgebraSheaf J A).obj
      (((standardResolutionComonad J A : Comonad (Under A)) :
        Under A ⥤ Under A).obj Y)) => t.hom.app U x)
    ((freeAlgebraSheafAdjunction J A).unit.naturality
      ((forgetAlgebraSheaf J A).map g))).symm

/-- `ε : P₀ ⟶ B` on local sections. -/
noncomputable abbrev augSections (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    B.obj.obj U :=
  (resolutionAugmentation J f (op ⦋0⦌)).hom.app U p

/-- The `k`-th face `P₁ ⟶ P₀` on local sections. -/
noncomputable abbrev faceSections (k : Fin 2) (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) : (resolutionTerm J f (op ⦋0⦌)).obj.obj U :=
  ((standardResolution J f).left.δ k).right.hom.app U x

/-- The canonical set-theoretic section of the augmentation `A[B] ⟶ B`. -/
noncomputable def augSection (U : Cᵒᵖ) (b : B.obj.obj U) :
    (resolutionTerm J f (op ⦋0⦌)).obj.obj U :=
  transportSections (resObjEq J f 0).symm U (variableSections J (Under.mk f) U b)

/-- The canonical lift of a local section of `P₀` to `P₁`. -/
noncomputable def augLift (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (resolutionTerm J f (op ⦋1⦌)).obj.obj U :=
  transportSections (resObjEq J f 1).symm U
    (variableSections J
      (((standardResolutionComonad J A : Comonad (Under A)) :
        Under A ⥤ Under A).obj (Under.mk f)) U (transportSections (resObjEq J f 0) U p))

/-- The canonical section is a section of the augmentation. -/
theorem augSections_augSection (U : Cᵒᵖ) (b : B.obj.obj U) :
    augSections J f U (augSection J f U b) = b := by
  show ((standardResolution J f).hom.app (op ⦋0⦌)).right.hom.app U (augSection J f U b) = b
  rw [show ((standardResolution J f).hom.app (op ⦋0⦌)) =
      eqToHom (resObjEq J f 0) ≫ (standardResolutionComonad J A).ε.app (Under.mk f) from
    augmentation_eq J f]
  show ((eqToHom (resObjEq J f 0) ≫
    (standardResolutionComonad J A).ε.app (Under.mk f)).right.hom.app U) _ = b
  rw [comp_sections]
  show ((standardResolutionComonad J A).ε.app (Under.mk f)).right.hom.app U
      (transportSections (resObjEq J f 0) U (augSection J f U b)) = b
  rw [augSection, transportSections_symm']
  exact counit_variableSections J (Under.mk f) U b

/-- The zeroth face sends the canonical lift of `p` back to `p`. -/
theorem faceSections_zero_augLift (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    faceSections J f 0 U (augLift J f U p) = p := by
  rw [show faceSections J f 0 U (augLift J f U p) =
      ((standardResolution J f).left.δ (0 : Fin 2)).right.hom.app U (augLift J f U p) from rfl,
    delta_zero_eq J f, comp_sections, comp_sections]
  show transportSections (resObjEq J f 0).symm U
      (((standardResolutionComonad J A).ε.app
        ((standardResolutionComonad J A).obj (Under.mk f))).right.hom.app U
          (transportSections (resObjEq J f 1) U (augLift J f U p))) = p
  rw [augLift, transportSections_symm', counit_variableSections]
  exact transportSections_symm _ U p

/-- The first face sends the canonical lift of `p` to the canonical section of its image
in `B`. -/
theorem faceSections_one_augLift (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    faceSections J f 1 U (augLift J f U p) = augSection J f U (augSections J f U p) := by
  rw [show faceSections J f 1 U (augLift J f U p) =
      ((standardResolution J f).left.δ (1 : Fin 2)).right.hom.app U (augLift J f U p) from rfl,
    delta_one_eq J f, comp_sections, comp_sections]
  show transportSections (resObjEq J f 0).symm U
      ((((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).map
        ((standardResolutionComonad J A).ε.app (Under.mk f))).right.hom.app U
          (transportSections (resObjEq J f 1) U (augLift J f U p))) = _
  rw [augLift, transportSections_symm', variableSections_naturality, augSection]
  congr 2
  exact (congrArg (fun (t : (standardResolution J f).left.obj (op ⦋0⦌) ⟶ Under.mk f) =>
    t.right.hom.app U p) (augmentation_eq J f)).symm


/-- The augmentation is additive on local sections. -/
theorem augSections_add (U : Cᵒᵖ) (p q : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    augSections J f U (p + q) = augSections J f U p + augSections J f U q := map_add _ _ _

/-- The augmentation is multiplicative on local sections. -/
theorem augSections_mul (U : Cᵒᵖ) (p q : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    augSections J f U (p * q) = augSections J f U p * augSections J f U q := map_mul _ _ _

/-- The augmentation preserves the zero section. -/
theorem augSections_zero (U : Cᵒᵖ) :
    augSections J f U (0 : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) = 0 := map_zero _

/-- The augmentation commutes with restriction of local sections. -/
theorem augSections_restrict {U V : Cᵒᵖ} (g : U ⟶ V)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    augSections J f V (((resolutionTerm J f (op ⦋0⦌)).obj.map g) p) =
      (B.obj.map g) (augSections J f U p) :=
  NatTrans.naturality_apply (F := (resolutionTerm J f (op ⦋0⦌)).obj) (G := B.obj)
    (resolutionAugmentation J f (op ⦋0⦌)).hom g p

/-- The augmentation composed with the structure map of `P₀` is the given morphism `A ⟶ B`. -/
theorem augSections_resolutionBase (U : Cᵒᵖ) (a : A.obj.obj U) :
    augSections J f U ((resolutionBase J f (op ⦋0⦌)).hom.app U a) = f.hom.app U a :=
  congrArg (fun (t : A ⟶ B) => t.hom.app U a)
    ((standardResolution J f).hom.app (op ⦋0⦌)).w

section Descent

variable {J f} {M : targetModules J B} (D : resolutionDerivations J f (op ⦋0⦌) M)

/-- A derivation of `P₀` with values in a `B`-module `M`, as a derivation with values in the
restriction of scalars of `M` along the augmentation `P₀ ⟶ B`. -/
noncomputable def restrictedDerivation :
    ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight (resolutionAugmentation J f (op ⦋0⦌)).hom
        (forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))).obj M.val).Derivation'
      (resolutionBase J f (op ⦋0⦌)).hom := D

/-- The derivation `restrictedDerivation D` has the same underlying map as `D`. -/
@[simp]
theorem restrictedDerivation_d (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (restrictedDerivation D).d p = D.d p := rfl

variable (hD : ∀ (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U),
    D.d (faceSections J f 0 U x) = D.d (faceSections J f 1 U x))

include hD

/-- A derivation of `P₀` equalising the two faces only depends on the image in `B`. -/
theorem derivation_eq_augSection (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    D.d (augSection J f U (augSections J f U p)) = D.d p := by
  have h := hD U (augLift J f U p)
  rw [faceSections_zero_augLift, faceSections_one_augLift] at h
  exact h.symm

/-- The additive map underlying the descended derivation. -/
noncomputable def descendHom (U : Cᵒᵖ) : B.obj.obj U →+ M.val.obj U where
  toFun b := D.d (augSection J f U b)
  map_zero' := ((congrArg (fun t => D.d (augSection J f U t)) (augSections_zero J f U).symm).trans
    (derivation_eq_augSection D hD U 0)).trans (map_zero D.d)
  map_add' b₁ b₂ := by
    refine Eq.trans ?_ (map_add D.d (augSection J f U b₁) (augSection J f U b₂))
    refine Eq.trans (congrArg (fun t => D.d (augSection J f U t)) ?_)
      (derivation_eq_augSection D hD U (augSection J f U b₁ + augSection J f U b₂))
    rw [augSections_add, augSections_augSection, augSections_augSection]

/-- A derivation of `P₀` equalising the two faces descends along the augmentation `P₀ ⟶ B`. -/
noncomputable def descendDerivation : M.val.Derivation' f.hom where
  d {U} := descendHom D hD U
  d_mul {U} a b := by
    have e₁ := presheafRestrictScalars_smul (resolutionAugmentation J f (op ⦋0⦌)).hom M.val U
      (augSection J f U a) a (augSections_augSection J f U a)
      ((restrictedDerivation D).d (augSection J f U b))
    have e₂ := presheafRestrictScalars_smul (resolutionAugmentation J f (op ⦋0⦌)).hom M.val U
      (augSection J f U b) b (augSections_augSection J f U b)
      ((restrictedDerivation D).d (augSection J f U a))
    refine Eq.trans ?_ (Eq.trans
      ((restrictedDerivation D).d_mul (augSection J f U a) (augSection J f U b))
      (congrArg₂ (fun (x y : M.val.obj U) => x + y) e₁ e₂))
    refine Eq.trans (congrArg (fun t => D.d (augSection J f U t)) ?_)
      (derivation_eq_augSection D hD U (augSection J f U a * augSection J f U b))
    rw [augSections_mul, augSections_augSection, augSections_augSection]
  d_map {U V} g x := by
    change D.d (augSection J f V ((B.obj.map g) x)) = _
    refine Eq.trans ?_ (D.d_map g (augSection J f U x))
    refine Eq.trans (congrArg (fun t => D.d (augSection J f V t)) ?_)
      (derivation_eq_augSection D hD V
        (((resolutionTerm J f (op ⦋0⦌)).obj.map g) (augSection J f U x)))
    rw [augSections_restrict, augSections_augSection]
  d_app {U} a := by
    change D.d (augSection J f U (f.hom.app U a)) = 0
    refine Eq.trans ?_ (D.d_app a)
    refine Eq.trans (congrArg (fun t => D.d (augSection J f U t)) ?_)
      (derivation_eq_augSection D hD U ((resolutionBase J f (op ⦋0⦌)).hom.app U a))
    rw [augSections_resolutionBase]

/-- The descended derivation restricts along the augmentation to the given one. -/
theorem descendDerivation_aug (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (descendDerivation D hD).d (augSections J f U p) = D.d p :=
  derivation_eq_augSection D hD U p

end Descent

/-- Two derivations of `B` agreeing after the augmentation `P₀ ⟶ B` are equal. -/
theorem derivation_ext_of_aug {M : targetModules J B} (D₁ D₂ : M.val.Derivation' f.hom)
    (h : ∀ (U : Cᵒᵖ) (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U),
      D₁.d (augSections J f U p) = D₂.d (augSections J f U p)) : D₁ = D₂ := by
  refine PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext fun b => ?_)
  simpa only [augSections_augSection] using h U (augSection J f U b)




/-- The differential out of degree zero vanishes, the next term being zero. -/
theorem cotangentComplex_d_zero_one : (cotangentComplex J f).d 0 1 = 0 :=
  (cotangentComplex_isZero_pos J f 1 (by decide)).eq_of_tgt _ _

/-- The zeroth homology is the opcycles in degree zero, the cotangent complex vanishing in
positive degrees. -/
noncomputable def homologyZeroIsoOpcycles :
    (cotangentComplex J f).homology 0 ≅ (cotangentComplex J f).opcycles 0 :=
  (cotangentComplex J f).isoHomologyι 0 1 (by simp) (cotangentComplex_d_zero_one J f)

/-- The canonical map from the degree-zero term of the base-changed simplicial module to the
zeroth homology of the cotangent complex. -/
noncomputable def homologyZeroProj :
    (cotangentSimplicialModule J f).object.obj (op ⦋0⦌) ⟶ (cotangentComplex J f).homology 0 :=
  (cotangentComplex_degreeIso J f 0).inv ≫ (cotangentComplex J f).pOpcycles 0 ≫
    (homologyZeroIsoOpcycles J f).inv

/-- The alternating sum of the face maps in simplicial degree zero is the difference of the
two faces. -/
theorem objD_zero :
    AlgebraicTopology.AlternatingFaceMapComplex.objD
        (cotangentSimplicialModule J f).object 0 =
      (cotangentSimplicialModule J f).object.δ 0 -
        (cotangentSimplicialModule J f).object.δ 1 := by
  rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

/-- The difference of the two faces is annihilated by the projection to the zeroth homology. -/
theorem objD_zero_comp_homologyZeroProj :
    AlgebraicTopology.AlternatingFaceMapComplex.objD
        (cotangentSimplicialModule J f).object 0 ≫ homologyZeroProj J f = 0 := by
  have h : (cotangentComplex_degreeIso J f 1).hom ≫
      AlgebraicTopology.AlternatingFaceMapComplex.objD
        (cotangentSimplicialModule J f).object 0 ≫
      (cotangentComplex_degreeIso J f 0).inv = (cotangentComplex J f).d (-1) 0 :=
    (cotangentComplex_d J f 0).symm
  rw [homologyZeroProj, ← Category.assoc, ← Category.assoc,
    ← Iso.inv_hom_id_assoc (cotangentComplex_degreeIso J f 1)
      (AlgebraicTopology.AlternatingFaceMapComplex.objD
        (cotangentSimplicialModule J f).object 0 ≫
        (cotangentComplex_degreeIso J f 0).inv), h]
  simp

/-- The two faces have the same composite with the projection to the zeroth homology. -/
theorem delta_comp_homologyZeroProj :
    (cotangentSimplicialModule J f).object.δ 0 ≫ homologyZeroProj J f =
      (cotangentSimplicialModule J f).object.δ 1 ≫ homologyZeroProj J f := by
  have h := objD_zero_comp_homologyZeroProj J f
  rwa [objD_zero, Preadditive.sub_comp, sub_eq_zero] at h

/-- The projection to the zeroth homology is an epimorphism. -/
instance epi_homologyZeroProj : Epi (homologyZeroProj J f) := by
  rw [homologyZeroProj]
  infer_instance

/-- The differential from degree `-1` to degree `0`, transported through the canonical degree
isomorphisms. -/
theorem cotangentComplex_d_negOne_zero :
    (cotangentComplex J f).d (-1) 0 =
      (cotangentComplex_degreeIso J f 1).hom ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          (cotangentSimplicialModule J f).object 0 ≫
        (cotangentComplex_degreeIso J f 0).inv :=
  cotangentComplex_d J f 0

/-- The zeroth homology of the cotangent complex is the cokernel of the difference of the two
faces: a morphism out of the degree-zero term equalising them factors uniquely through it. -/
theorem existsUnique_homologyZeroDesc {F : targetModules J B}
    (g : (cotangentSimplicialModule J f).object.obj (op ⦋0⦌) ⟶ F)
    (hg : (cotangentSimplicialModule J f).object.δ 0 ≫ g =
      (cotangentSimplicialModule J f).object.δ 1 ≫ g) :
    ∃! φ : (cotangentComplex J f).homology 0 ⟶ F, homologyZeroProj J f ≫ φ = g := by
  have hobjD : AlgebraicTopology.AlternatingFaceMapComplex.objD
      (cotangentSimplicialModule J f).object 0 ≫ g = 0 := by
    rw [objD_zero, Preadditive.sub_comp, hg, sub_self]
  have hd : (cotangentComplex J f).d (-1) 0 ≫
      ((cotangentComplex_degreeIso J f 0).hom ≫ g) = 0 := by
    rw [cotangentComplex_d_negOne_zero J f, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc, hobjD, comp_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : (cotangentComplex J f).homology 0 ⟶ F, homologyZeroProj J f ≫ φ = g :=
    ⟨(homologyZeroIsoOpcycles J f).hom ≫
      (cotangentComplex J f).descOpcycles ((cotangentComplex_degreeIso J f 0).hom ≫ g) (-1)
        (by simp) hd, by
      rw [homologyZeroProj, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
        HomologicalComplex.p_descOpcycles, Iso.inv_hom_id_assoc]⟩
  exact ⟨φ, hφ, fun ψ hψ => (cancel_epi (homologyZeroProj J f)).1 (hψ.trans hφ.symm)⟩



/-! ### The universal property of the zeroth homology -/

/-- Both faces `P₁ ⇉ P₀` have the same composite with the augmentation. -/
theorem face_comp_augmentation (k : Fin 2) :
    (standardResolution J f).left.δ k ≫ (standardResolution J f).hom.app (op ⦋0⦌) =
      (standardResolution J f).hom.app (op ⦋1⦌) := by
  have h := SimplicialObject.δ_naturality (standardResolution J f).hom (n := 0) k
  rwa [show ((SimplicialObject.const (Under A)).obj (standardResolution J f).right).δ k =
    𝟙 _ from rfl, Category.comp_id] at h

/-- Both faces have the same composite with the augmentation, on local sections. -/
theorem augSections_faceSections (k : Fin 2) (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    augSections J f U (faceSections J f k U x) =
      ((standardResolution J f).hom.app (op ⦋1⦌)).right.hom.app U x :=
  congrArg (fun (t : (standardResolution J f).left.obj (op ⦋1⦌) ⟶ Under.mk f) =>
    t.right.hom.app U x) (face_comp_augmentation J f k)

/-- A face of the standard resolution acts on derivations by precomposition. -/
theorem derivationEquiv_faceSections (M : targetModules J B) (k : Fin 2)
    (h : (cotangentSimplicialModule J f).object.obj (op ⦋0⦌) ⟶ M) (U : Cᵒᵖ)
    (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) M
        ((cotangentSimplicialModule J f).object.δ k ≫ h)).d x =
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌) M h).d
        (faceSections J f k U x) :=
  (cotangentSimplicialModule J f).simplex_naturality (SimplexCategory.δ k).op M h U x

/-- An `A`-derivation of `B` restricts along the augmentation to an `A`-derivation of `P₀`. -/
noncomputable def precompAug {F : targetModules J B} (D : F.val.Derivation' f.hom) :
    resolutionDerivations J f (op ⦋0⦌) F :=
  D.precomp (resolutionAugmentation J f (op ⦋0⦌)).hom
    (congrArg (fun (t : A ⟶ B) => t.hom) ((standardResolution J f).hom.app (op ⦋0⦌)).w)

/-- The restricted derivation differentiates a local section of `P₀` through the augmentation. -/
@[simp]
theorem precompAug_d {F : targetModules J B} (D : F.val.Derivation' f.hom) (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (precompAug J f D).d p = D.d (augSections J f U p) := rfl

/-- A derivation restricted along the augmentation equalises the two faces. -/
theorem precompAug_faceSections {F : targetModules J B} (D : F.val.Derivation' f.hom)
    (U : Cᵒᵖ) (x : (resolutionTerm J f (op ⦋1⦌)).obj.obj U) :
    (precompAug J f D).d (faceSections J f 0 U x) =
      (precompAug J f D).d (faceSections J f 1 U x) := by
  rw [precompAug_d, precompAug_d, augSections_faceSections, augSections_faceSections]

/-- The universal `A`-derivation of `B` with values in the zeroth homology of the cotangent
complex. -/
noncomputable def homologyZeroDerivation :
    ((cotangentComplex J f).homology 0).val.Derivation' f.hom :=
  descendDerivation
    ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌)
      ((cotangentComplex J f).homology 0) (homologyZeroProj J f))
    (fun U x => by
      rw [← derivationEquiv_faceSections, ← derivationEquiv_faceSections,
        delta_comp_homologyZeroProj])

/-- The universal derivation of the zeroth homology restricts along the augmentation to the
derivation corepresented by the projection. -/
theorem homologyZeroDerivation_aug (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    (homologyZeroDerivation J f).d (augSections J f U p) =
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌)
        ((cotangentComplex J f).homology 0) (homologyZeroProj J f)).d p :=
  descendDerivation_aug _ _ U p

/-- Postcomposing the universal derivation with a morphism out of the zeroth homology, then
restricting along the augmentation, gives the derivation corepresented by the composite. -/
theorem postcomp_homologyZeroDerivation_aug {F : targetModules J B}
    (ψ : (cotangentComplex J f).homology 0 ⟶ F) (U : Cᵒᵖ)
    (p : (resolutionTerm J f (op ⦋0⦌)).obj.obj U) :
    ((homologyZeroDerivation J f).postcomp ψ.val).d (augSections J f U p) =
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌) F
        (homologyZeroProj J f ≫ ψ)).d p := by
  rw [(cotangentSimplicialModule J f).naturality (op ⦋0⦌) (homologyZeroProj J f) ψ]
  exact congrArg (fun (m : ((cotangentComplex J f).homology 0).val.obj U) =>
    (ψ.val.app U) m) (homologyZeroDerivation_aug J f U p)

/-- Every `A`-derivation of `B` factors uniquely through `homologyZeroDerivation`, the universal
derivation with values in the zeroth homology of the cotangent complex. -/
theorem homologyZeroDerivation_universal (F : targetModules J B)
    (D : F.val.Derivation' f.hom) :
    ∃! φ : (cotangentComplex J f).homology 0 ⟶ F,
      (homologyZeroDerivation J f).postcomp φ.val = D := by
  set g := ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌) F).symm
    (precompAug J f D) with hgdef
  have hgd : ((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌) F) g =
      precompAug J f D := Equiv.apply_symm_apply _ _
  have hg : (cotangentSimplicialModule J f).object.δ 0 ≫ g =
      (cotangentSimplicialModule J f).object.δ 1 ≫ g := by
    refine ((cotangentSimplicialModule J f).derivationEquiv (op ⦋1⦌) F).injective
      (PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext fun x => ?_))
    rw [derivationEquiv_faceSections, derivationEquiv_faceSections, hgd]
    exact precompAug_faceSections J f D U x
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_homologyZeroDesc J f g hg
  refine ⟨φ, ?_, fun ψ hψ => ?_⟩
  · refine derivation_ext_of_aug J f _ _ (fun U p => ?_)
    rw [postcomp_homologyZeroDerivation_aug, hφ, hgd, precompAug_d]
  · refine huniq ψ (((cotangentSimplicialModule J f).derivationEquiv (op ⦋0⦌) F).injective ?_)
    refine Eq.trans (PresheafOfModules.Derivation.ext
      (funext fun U => AddMonoidHom.ext fun p => ?_)) hgd.symm
    rw [← postcomp_homologyZeroDerivation_aug, hψ]
    rfl

/-- The zeroth homology of the cotangent complex corepresents the functor of relative
derivations. -/
noncomputable def derivationsFunctor_corepresentableBy :
    (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{max u v w} A B f).CorepresentableBy
      ((cotangentComplex J f).homology 0) :=
  AlgebraicGeometry.SheafOfModules.universalDerivationCorepresentableBy A B f
    (homologyZeroDerivation J f) (homologyZeroDerivation_universal J f)

/-- The zeroth homology of the cotangent complex of a morphism of sheaves of
commutative rings on a site is its sheaf of relative differentials, the sheaf of modules
corepresenting the relative derivations. -/
@[stacks 08UR]
noncomputable def cotangentComplex_homologyZeroIso :
    (cotangentComplex J f).homology 0 ≅
      (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{max u v w} A B f).coreprX :=
  (derivationsFunctor_corepresentableBy J f).isoCoreprX


end CategoryTheory.Sheaf

end
