module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreFiniteExt
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentBaseChangeDescent
public import StacksFrontier.Deformation.Artin.Infinitesimal.RelativeLiftClasses
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence

/-!
# The data of a lift of the base point of the fibre of `Complexes_{X/Y}`

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k`, `𝒲` the fibre of `Complexes_{X/Y}`
over the point `Spec k ⟶ Y` and `w₀` its base point. A lift `y` of `w₀` over `k[M]` (a
representative of a class of `Deformation.Artin.squareZeroLiftClasses`) carries a test scheme
`T` over `Y` (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftScheme`), the base map
`b : T₀ ⟶ T` of its structure morphism, where `T₀` is the test scheme of `x₀`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftSection`), and a retraction `t : T ⟶ T₀`
given by the second component of `y`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftRetraction`,
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftSection_comp_retraction`). As objects of the
site, `T₀ = Spec k`, `T = Spec k[M]` and `b` is the closed immersion
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftSection_conj`), a square-zero closed
immersion (`AlgebraicGeometry.Space.isSquareZeroClosedImmersion_squareZeroArrow`,
`AlgebraicGeometry.Space.ComplexesSituation.isSquareZeroClosedImmersion_fibreLiftSection`).
These are the inputs of `AlgebraicGeometry.Space.CoherentSituation.testSchemeRetractionRingIso`;
with them the `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]`-modules on the site of `X₀` are the `𝒪_{X_T}`-modules
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftModuleEquivalence`), and so are the derived
categories (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedEquivalence`), at the
coefficient map `AlgebraicGeometry.Space.ComplexesSituation.fieldPointCoefficientMap` of the field
point and in the ringed-site spelling of `Deformation.Artin.CoefficientLiftComparison`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift

universe d u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The closed immersion `Spec A ⟶ Spec A[M]` is a square-zero closed immersion of the site.** -/
theorem isSquareZeroClosedImmersion_squareZeroArrow (A : Type u) [CommRing A]
    (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (M : SiteModule A B) :
    IsSquareZeroClosedImmersion B S hS (squareZeroArrow A B S hS toS hA M) :=
  isFirstOrderThickening_squareZeroArrow A toS hA M

/-- A morphism of the site conjugate by equalities to a square-zero closed immersion is one. -/
theorem isSquareZeroClosedImmersion_of_eqToHom_conj {T₀ T T₀' T' : BigFppfOver B S hS}
    (h₀ : T₀ = T₀') (h : T = T') (b : T₀ ⟶ T) (b' : T₀' ⟶ T')
    (hb : eqToHom h₀.symm ≫ b ≫ eqToHom h = b') (hb' : IsSquareZeroClosedImmersion B S hS b') :
    IsSquareZeroClosedImmersion B S hS b := by
  subst h₀ h hb
  simpa using hb'

/-- A morphism `b` whose composite with equalities is `g` up to an equality of the source: the
transport lemma behind `AlgebraicGeometry.Space.ComplexesSituation.fibreLiftSection_conj`. -/
theorem eqToHom_conj_of_comp_eqToHom {C : Type*} [Category* C] {X X' A P Q Z : C}
    (e₁ : X = A) (e₂ : P = Q) (e₃ : Q = Z) (e₀ : X' = X) (e₁' : X' = A) (bl : X ⟶ P)
    {hb : X' ⟶ Q} {g : A ⟶ Z} (hhb : hb = eqToHom e₀ ≫ bl ≫ eqToHom e₂)
    (h : hb ≫ eqToHom e₃ = eqToHom e₁' ≫ g) :
    eqToHom e₁.symm ≫ bl ≫ eqToHom (e₂.trans e₃) = g := by
  subst e₀ e₁ e₂ e₃ hhb
  simpa using h

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

attribute [local instance] complexesCategory

section FibreLift

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : ComplexesObject D)
  (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hk : B.Contains (Spec (.of k))) {M : SiteModule k B}

/-- A lift of the base point `w₀` of the fibre over `k[M]`. -/
abbrev FibreLift (M : SiteModule k B) : Type _ :=
  (Under.post (TwoFibreProductOver.structureFunctor (complexesFunctor D)
    (Over.map x₀.T.left.hom) (baseProj D.Y) (complexesToBaseObjects D)
    (schemePointToBase D.Y x₀.T.left x₀.T.hom))).Fiber
    (Under.mk (eqToHom (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) ≫
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk M))

include hx₀ in
/-- The test scheme of a field point `x₀` is `Spec k`, as the object
`Deformation.Artin.algebraOver` of the site. -/
theorem fieldPoint_left_eq_algebraOver :
    x₀.T.left = algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk :=
  fieldPoint_left_eq D iΛ x₀ hx₀ hk

variable {D iΛ x₀ hx₀ hk}

/-- The test scheme `T` over `Y` of a lift of `w₀`. -/
abbrev fibreLiftScheme (y : FibreLift D iΛ x₀ hx₀ hk M) : SchemesOver D.Y :=
  y.1.right.x.T

/-- The base map `b : T₀ ⟶ T` of a lift of `w₀`, from the test scheme of `x₀`. -/
abbrev fibreLiftSection (y : FibreLift D iΛ x₀ hx₀ hk M) : x₀.T ⟶ fibreLiftScheme y :=
  y.1.hom.a.base

/-- The retraction `t : T ⟶ T₀` of a lift of `w₀`: the comparison of its two components followed
by the structure morphism of its second component, a scheme over `T₀.left`. -/
def fibreLiftRetraction (y : FibreLift D iΛ x₀ hx₀ hk M) : fibreLiftScheme y ⟶ x₀.T :=
  y.1.right.iso.hom.down ≫ CostructuredArrow.homMk (overMapHom x₀.T.left y.1.right.y) rfl

/-- **The retraction is a retraction of the base map.** -/
theorem fibreLiftSection_comp_retraction (y : FibreLift D iΛ x₀ hx₀ hk M) :
    fibreLiftSection y ≫ fibreLiftRetraction y = 𝟙 x₀.T := by
  have hw : (fibreLiftSection y).left ≫ y.1.right.iso.hom.down.left =
      eqToHom (overMap_obj_mk_id x₀.T.left).symm ≫ (Over.map x₀.T.left.hom).map y.1.hom.b :=
    congrArg (fun f => f.down.left) y.1.hom.w
  have hb : (Over.map x₀.T.left.hom).map y.1.hom.b ≫ overMapHom x₀.T.left y.1.right.y =
      overMapHom x₀.T.left (Over.mk (𝟙 x₀.T.left.left)) :=
    Over.OverMorphism.ext (Over.w y.1.hom.b)
  apply CostructuredArrow.hom_ext
  change (fibreLiftSection y).left ≫ y.1.right.iso.hom.down.left ≫
    overMapHom x₀.T.left y.1.right.y = 𝟙 _
  calc _ = ((fibreLiftSection y).left ≫ y.1.right.iso.hom.down.left) ≫
          overMapHom x₀.T.left y.1.right.y := (Category.assoc _ _ _).symm
    _ = (eqToHom (overMap_obj_mk_id x₀.T.left).symm ≫ (Over.map x₀.T.left.hom).map y.1.hom.b) ≫
          overMapHom x₀.T.left y.1.right.y := congrArg (· ≫ _) hw
    _ = eqToHom (overMap_obj_mk_id x₀.T.left).symm ≫ ((Over.map x₀.T.left.hom).map y.1.hom.b ≫
          overMapHom x₀.T.left y.1.right.y) := Category.assoc _ _ _
    _ = eqToHom (overMap_obj_mk_id x₀.T.left).symm ≫
          overMapHom x₀.T.left (Over.mk (𝟙 x₀.T.left.left)) := congrArg (_ ≫ ·) hb
    _ = 𝟙 _ := eqToHom_comp_overMapHom_mk_id _

/-- The test scheme of a lift of `w₀` over `k[M]` is `Spec k[M]`, as an object of the site. -/
theorem fibreLiftScheme_left_eq (y : FibreLift D iΛ x₀ hx₀ hk M) :
    (fibreLiftScheme y).left =
      squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) M :=
  y.1.right.hx.trans (congrArg Under.right y.2)

/-- **The base map of a lift of `w₀` over `k[M]` is the closed immersion `Spec k ⟶ Spec k[M]`.** -/
theorem fibreLiftSection_conj (y : FibreLift D iΛ x₀ hx₀ hk M) :
    eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ (fibreLiftSection y).left ≫
        eqToHom (fibreLiftScheme_left_eq y) =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk M := by
  have h := Under.w (eqToHom y.2)
  simp only [Under.eqToHom_right] at h
  exact eqToHom_conj_of_comp_eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
    y.1.right.hx (congrArg Under.right y.2) _ _ _ (TwoFibreProductOver.Hom.hbase_eq y.1.hom) h

/-- The base map of a lift of `w₀` is a square-zero closed immersion. -/
theorem isSquareZeroClosedImmersion_fibreLiftSection (y : FibreLift D iΛ x₀ hx₀ hk M) :
    IsSquareZeroClosedImmersion B S hS (fibreLiftSection y).left :=
  isSquareZeroClosedImmersion_of_eqToHom_conj
    (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)
    (fibreLiftScheme_left_eq y) _ _ (fibreLiftSection_conj y)
    (isSquareZeroClosedImmersion_squareZeroArrow k _ hk M)

/-- The coefficient map of the structure sheaf of `X_T` on the site of `X₀` is the coefficient map
`AlgebraicGeometry.Space.ComplexesSituation.fieldPointCoefficientMap` of the field point. -/
theorem squareZeroCoefficientMap_eq_fieldPointCoefficientMap :
    squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((D.projection x₀.T).hom ≫
          yoneda.map (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk))) =
      fieldPointCoefficientMap D iΛ x₀ hx₀ hk :=
  rfl

variable {V : FGModuleCat.{u} k}

/-- The square-zero extension `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` at the coefficient map of the structure sheaf
of `X_T`, in the ringed-site spelling. -/
abbrev fibreLiftRing (V : FGModuleCat.{u} k) :=
  coefficientRing (C := (smallEtaleRingedSite B S hS (D.space x₀.T).1 (D.space x₀.T).2).C)
    (J := (smallEtaleRingedSite B S hS (D.space x₀.T).1 (D.space x₀.T).2).J)
    (O₀ := (smallEtaleRingedSite B S hS (D.space x₀.T).1 (D.space x₀.T).2).O)
    (squareZeroCoefficientMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((D.projection x₀.T).hom ≫
        yoneda.map (eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk)))) V

/-- **The `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]`-modules on the site of `X₀` are the `𝒪_{X_T}`-modules**, for the
test scheme `T = Spec k[V]` of a lift of `w₀` over `k[V]`
(`AlgebraicGeometry.Space.CoherentSituation.testSchemeModuleEquivalence`), at the coefficient map
of the field point. -/
def fibreLiftModuleEquivalence (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)) ≌
      Modules.{u, u} B S hS (D.space (fibreLiftScheme y)).1 (D.space (fibreLiftScheme y)).2 := by
  let e := D.testSchemeModuleEquivalence (fibreLiftSection_comp_retraction y)
      (isSquareZeroClosedImmersion_fibreLiftSection y)
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) (fibreLiftScheme_left_eq y)
      (fibreLiftSection_conj y)
  change SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (fibreLiftRing (D := D) (iΛ := iΛ) (x₀ := x₀) (hx₀ := hx₀) (hk := hk) V)) ≌ _
  change _ ≌ SheafOfModules.{u} (smallEtaleRingSheaf B S hS
    (D.space (fibreLiftScheme y)).1 (D.space (fibreLiftScheme y)).2)
  exact e

/-- The module equivalence of a lift of `w₀` is additive. -/
instance fibreLiftModuleEquivalence_functor_additive
    (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V)) :
    (fibreLiftModuleEquivalence y).functor.Additive :=
  D.testSchemeModuleEquivalence_functor_additive (fibreLiftSection_comp_retraction y)
    (isSquareZeroClosedImmersion_fibreLiftSection y)
    (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) (fibreLiftScheme_left_eq y)
    (fibreLiftSection_conj y)

/-- **The derived equivalence `D(𝒪_{X₀}[𝒪_{X₀} ⊗_k V]) ≌ D(𝒪_{X_T})` of a lift of `w₀` over
`k[V]`**: `AlgebraicGeometry.Space.ComplexesSituation.fibreLiftModuleEquivalence` on derived
categories. The source has any model, the target is `AlgebraicGeometry.Space.derivedModules`. -/
def fibreLiftDerivedEquivalence (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))] :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V))) ≌
      derivedModules B S hS (D.space (fibreLiftScheme y)) :=
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (D.space (fibreLiftScheme y)).1 (D.space (fibreLiftScheme y)).2)
  @Stacks.DerivedQCoh.Equivalence.mapDerivedCategory _ _ _ _ _ _ _ _
    (fibreLiftModuleEquivalence y) (fibreLiftModuleEquivalence_functor_additive y)

end FibreLift

end ComplexesSituation

end AlgebraicGeometry.Space

end
