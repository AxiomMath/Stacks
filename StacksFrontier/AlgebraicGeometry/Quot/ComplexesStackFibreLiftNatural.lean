module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftDerived

/-!
# Naturality of the lift of `E₀` attached to a lift of the fibre base point

Let `x₀` be a field point of `Complexes_{X/Y}` over `Spec k` and `y` a lift of the base point
`w₀` of the fibre over `k[V]`. The lift
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift y` of `E₀` to
`𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` only depends on the complex `E_y` of `y` on `X_T`, the morphism
`w₀ ⟶ y` of `Complexes_{X/Y}` and the retraction `T ⟶ T₀`; this file states it for such data
(`AlgebraicGeometry.Space.ComplexesSituation.fibreDataDerivedLift`) and shows that a morphism of
lifts of `w₀` in the fibre over `k[V]` gives isomorphic lifts of `E₀`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift_isomorphic`), so that the class
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass` of a class of lifts of `w₀` is the
class of the lift of any representative
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass_mk`). This is the naturality `c3 (a)`
of the proof of Stacks 0DLL.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d u

/-- **Cancelling a unit law in a composite of comparisons.** Let `τ : L_{ab} ≅ L_b ⋙ L_a` be a
composition comparison, `ι : L_b ≅ 𝟭` a unit law and `ρ : L_{ab} ≅ L_a` with
`τ ≫ (ι ▷ L_a) ≫ λ = ρ`. For `n : L_b E' ⟶ E` invertible and `ε : E ≅ E'` with
`ε = n⁻¹ ≫ ι_{E'}`, the composite `L_a ε ≫ ρ⁻¹_{E'} ≫ (τ, m, n)` is `m`: the comparison
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataDerivedLift_isomorphic_of_id` needs, stated
for abstract functors so that it is checked once. -/
theorem _root_.CategoryTheory.Functor.fibreComp_unit_cancel {C₀ C₁ : Type*} [Category* C₀]
    [Category* C₁] {La : C₁ ⥤ C₀} {Lb : C₁ ⥤ C₁} {Lab : C₁ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La)
    (ι : Lb ≅ 𝟭 C₁) (ρ : Lab ≅ La)
    (hfac : τ ≪≫ Functor.isoWhiskerRight ι La ≪≫ La.leftUnitor = ρ) {M : C₀} {E E' : C₁}
    (mf : La.obj E ⟶ M) (nf : Lb.obj E' ⟶ E) [IsIso nf] (ε : E ≅ E')
    (hε : ε.hom = inv nf ≫ ι.hom.app E') :
    La.map ε.hom ≫ ρ.inv.app E' ≫ Functor.fibreComp τ mf nf = mf := by
  subst hfac
  simp [Functor.fibreComp, hε]

/-- An identification `eqToIso h` of functors, after a transport, is cancelled. -/
theorem _root_.CategoryTheory.Functor.eqToHom_comp_eqToIso_inv_app {C D : Type*} [Category* C]
    [Category* D] {F G : C ⥤ D} (h : F = G) (X : C) (p : F.obj X = G.obj X) {W : D}
    (f : F.obj X ⟶ W) : eqToHom p ≫ (eqToIso h).inv.app X ≫ f = f := by
  subst h
  simp

/-- A morphism equal to an `eqToHom`, conjugated by `eqToHom`s, is an `eqToHom`. -/
theorem _root_.CategoryTheory.eqToHom_comp_comp_eqToHom_of_eq {C : Type*} [Category* C]
    {X Y Z W : C} (p : X = Y) (a : Y = Z) (q : Z = W) (r : X = W) (f : Y ⟶ Z)
    (hf : f = eqToHom a) : eqToHom p ≫ f ≫ eqToHom q = eqToHom r := by
  subst hf p a q
  simp

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] HasDerivedCategory.standard

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

attribute [local instance] complexesCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : ComplexesObject D}
  {hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {hk : B.Contains (Spec (.of k))} {V : FGModuleCat.{u} k}

/-! ### The lift of `E₀` attached to a morphism `x₀ ⟶ A` with a retraction -/

section Data

variable (T : SchemesOver D.Y) (b : x₀.T ⟶ T) (t : T ⟶ x₀.T)
  (hbt : b ≫ t = 𝟙 x₀.T) (hb : IsSquareZeroClosedImmersion B S hS b.left)
  (hT : T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    ((fgSiteModule B hk).obj V))
  (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ b.left ≫ eqToHom hT =
    squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((fgSiteModule B hk).obj V))

/-- The module equivalence of
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftModuleEquivalence`, for a test scheme
`T = Spec k[V]` over `Y` with a section `b : T₀ ⟶ T` and a retraction `t`. -/
def fibreDataModuleEquivalence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)) ≌
      Modules.{u, u} B S hS (D.space T).1 (D.space T).2 := by
  let e := D.testSchemeModuleEquivalence hbt hb
      (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hT hβ
  change SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (fibreLiftRing (D := D)
    (iΛ := iΛ) (x₀ := x₀) (hx₀ := hx₀) (hk := hk) V)) ≌ _
  change _ ≌ SheafOfModules.{u} (smallEtaleRingSheaf B S hS (D.space T).1 (D.space T).2)
  exact e

/-- The module equivalence of a section with a retraction is additive. -/
instance fibreDataModuleEquivalence_functor_additive :
    (fibreDataModuleEquivalence (hx₀ := hx₀) T b t hbt hb hT hβ).functor.Additive :=
  D.testSchemeModuleEquivalence_functor_additive hbt hb
    (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hT hβ

variable [hDer : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- The derived equivalence of
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedEquivalence`, for a section with a
retraction. -/
def fibreDataDerivedEquivalence :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V))) ≌
      derivedModules B S hS (D.space T) :=
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
  @Stacks.DerivedQCoh.Equivalence.mapDerivedCategory _ _ _ _ _ _ _ _
    (fibreDataModuleEquivalence T b t hbt hb hT hβ)
    (fibreDataModuleEquivalence_functor_additive T b t hbt hb hT hβ)

/-- The derived base change of
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedExtensionOfScalars`, for a section
with a retraction. -/
def fibreDataDerivedExtensionOfScalars :
    DerivedExtensionOfScalars.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)) := by
  let e := D.testSchemeDerivedExtensionOfScalars (hDer := hDer) hbt hb
    (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk) hT hβ
  exact e

/-- `c2` (`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedPullbackIso`) for a section
with a retraction. -/
def fibreDataDerivedPullbackIso
    (R : DerivedExtensionOfScalars.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))) :
    R.baseChange ≅ (fibreDataDerivedEquivalence T b t hbt hb hT hβ).functor ⋙
      derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap b) :=
  DerivedExtensionOfScalars.baseChangeIso R
    (fibreDataDerivedExtensionOfScalars T b t hbt hb hT hβ)

end Data

section Lift

variable [hDer : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]
  (A : ComplexesObject D) (m : x₀ ⟶ A) (t : A.T ⟶ x₀.T)
  (hbt : m.base ≫ t = 𝟙 x₀.T) (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
  (hT : A.T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    ((fgSiteModule B hk).obj V))
  (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
      eqToHom hT =
    squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      ((fgSiteModule B hk).obj V))

/-- The identification of
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftIdentification`, for a morphism
`m : x₀ ⟶ A` of `Complexes_{X/Y}` onto a test scheme `Spec k[V]` with a retraction. -/
def fibreDataIdentification
    (R : DerivedExtensionOfScalars.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))) :
    R.baseChange.obj
        ((fibreDataDerivedEquivalence A.T m.base t hbt hb hT hβ).inverse.obj A.E) ≅ x₀.E :=
  (fibreDataDerivedPullbackIso A.T m.base t hbt hb hT hβ R).app _ ≪≫
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (D.relativeMap m.base)).mapIso
        ((fibreDataDerivedEquivalence A.T m.base t hbt hb hT hβ).counitIso.app A.E) ≪≫
    @asIso _ _ _ _ m.fibre m.isIso_fibre

/-- **The lift of `E₀` to `𝒪_{X₀}[𝒪_{X₀} ⊗_k V]` attached to a morphism `m : x₀ ⟶ A` of
`Complexes_{X/Y}` onto a test scheme `Spec k[V]` with a retraction**: the complex of `A`, carried
to the site of `X₀` by the derived equivalence, with the identification
`AlgebraicGeometry.Space.ComplexesSituation.fibreDataIdentification`. -/
def fibreDataDerivedLift (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    DerivedLift (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))) ⟨x₀.E, hK⟩ where
  K := ⟨(fibreDataDerivedEquivalence A.T m.base t hbt hb hT hβ).inverse.obj A.E, by
    obtain ⟨n, hn⟩ := hK
    have : x₀.E.IsLE n := hn
    exact ⟨n, isLE_of_isLE_baseChange_sqZeroExt _ n _
      (DerivedCategory.TStructure.t.isLE_of_iso
        (fibreDataIdentification A m t hbt hb hT hβ _).symm n)⟩⟩
  identification := fibreDataIdentification A m t hbt hb hT hβ _

end Lift

variable [hDer : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- The lift of `E₀` attached to a lift `y` of `w₀` is the lift attached to the morphism
`w₀ ⟶ y` with the retraction of `y`. -/
theorem fibreLiftDerivedLift_eq (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    fibreLiftDerivedLift y hK = fibreDataDerivedLift (x₀ := x₀) (hx₀ := hx₀) (hDer := hDer)
      y.1.right.x y.1.hom.a
      (fibreLiftRetraction y) (fibreLiftSection_comp_retraction y)
      (isSquareZeroClosedImmersion_fibreLiftSection y) (fibreLiftScheme_left_eq y)
      (fibreLiftSection_conj y) hK :=
  rfl

/-! ### Naturality -/

/-- Equal morphisms `x₀ ⟶ A` give isomorphic lifts of `E₀`. -/
theorem fibreDataDerivedLift_congr {A : ComplexesObject D} {m m' : x₀ ⟶ A} (h : m = m')
    {t : A.T ⟶ x₀.T} (hbt : m.base ≫ t = 𝟙 x₀.T)
    (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
    (hT : A.T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))
    (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hbt' : m'.base ≫ t = 𝟙 x₀.T) (hb' : IsSquareZeroClosedImmersion B S hS m'.base.left)
    (hβ' : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m'.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    DerivedLift.Isomorphic (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK)
      (fibreDataDerivedLift (hDer := hDer) A m' t hbt' hb' hT hβ' hK) := by
  subst h
  exact DerivedLift.Isomorphic.refl (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK)

/-- Two morphisms `x₀ ⟶ A`, `x₀ ⟶ A'` with the same base map, onto objects with the same test
scheme, give isomorphic lifts of `E₀` as soon as an isomorphism of the complexes carries the
comparison of the second to that of the first. -/
theorem fibreDataDerivedLift_isomorphic_of_iso {T : SchemesOver D.Y}
    {E E' : derivedModules B S hS (D.space T)} {rp : D.IsRelativelyPerfect T E}
    {nn : D.HasNoNegativeFibreExt T E} {rp' : D.IsRelativelyPerfect T E'}
    {nn' : D.HasNoNegativeFibreExt T E'} (m : x₀ ⟶ ⟨T, E, rp, nn⟩)
    (φ' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj E' ⟶ x₀.E)
    [IsIso φ'] {t : T ⟶ x₀.T} (hbt : m.base ≫ t = 𝟙 x₀.T)
    (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
    (hT : T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))
    (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (ε : E ≅ E')
    (hε : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map ε.hom ≫ φ' =
      m.fibre)
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    DerivedLift.Isomorphic (fibreDataDerivedLift (hDer := hDer) ⟨T, E, rp, nn⟩ m t hbt hb hT hβ hK)
      (fibreDataDerivedLift (hDer := hDer) ⟨T, E', rp', nn'⟩
        (⟨m.base, φ', inferInstance⟩ : ComplexesHom x₀ ⟨T, E', rp', nn'⟩) t hbt hb hT hβ hK) := by
  refine ⟨(fibreDataDerivedEquivalence (hx₀ := hx₀) T m.base t hbt hb hT hβ).inverse.mapIso ε, ?_⟩
  have key := (fibreDataDerivedEquivalence (hx₀ := hx₀) T m.base t hbt hb hT hβ).counitIso.hom
    |>.naturality ε.hom
  simp only [fibreDataDerivedLift, fibreDataIdentification, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.comp_map, Functor.id_map] at key ⊢
  rw [(fibreDataDerivedPullbackIso (hx₀ := hx₀) T m.base t hbt hb hT hβ _).hom.naturality_assoc]
  congr 1
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, key, Functor.map_comp_assoc]
  exact congrArg (_ ≫ ·) hε

/-- `CategoryTheory.Functor.fibreComp_unit_cancel` for the derived pullbacks along the morphisms
of base changes, at `𝟙 T`. -/
theorem fibreComp_idComparison_cancel {T₀ T : SchemesOver D.Y} (b : T₀ ⟶ T)
    {E E' : derivedModules B S hS (D.space T)}
    {Z : derivedModules B S hS (D.space T₀)}
    (mf : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj E ⟶ Z)
    (nf : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (𝟙 T))).obj E' ⟶ E)
    [IsIso nf] (ε : E ≅ E') (hε : ε.hom = inv nf ≫ (D.idComparison T).hom.app E') :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map ε.hom ≫
      (D.relativeMapComparison (Category.comp_id b)).inv.app E' ≫
        Functor.fibreComp (D.compComparison b (𝟙 T)) mf nf = mf :=
  Functor.fibreComp_unit_cancel _ _ _ (D.comp_idComparison_fac b) mf nf ε hε

/-- A comparison equal to the composite of the comparison of `m` with one over `𝟙 T`, read back
along `m.base ≫ 𝟙 = m.base` and the isomorphism `E ≅ E'` of the second one and the unit law, is
the comparison of `m`. -/
theorem fibreComp_id_fibre_cancel {T₀ T : SchemesOver D.Y} (b : T₀ ⟶ T)
    {E E' : derivedModules B S hS (D.space T)} {Z : derivedModules B S hS (D.space T₀)}
    (mf : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj E ⟶ Z)
    (nf : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (𝟙 T))).obj E' ⟶ E)
    (hnf : IsIso nf)
    (φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (b ≫ 𝟙 T))).obj E' ⟶ Z)
    (hφ : φ = Functor.fibreComp (D.compComparison b (𝟙 T)) mf nf) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).map
        ((@asIso _ _ _ _ nf hnf).symm ≪≫ (D.idComparison T).app E').hom ≫
      (D.relativeMapComparison (Category.comp_id b)).inv.app E' ≫ φ = mf := by
  subst hφ
  exact D.fibreComp_idComparison_cancel b mf nf _
    (by rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom])

/-- The naturality of the lift of `E₀` along a morphism `A ⟶ A'` over the identity of the test
scheme. -/
theorem fibreDataDerivedLift_isomorphic_of_id {T : SchemesOver D.Y}
    {E E' : derivedModules B S hS (D.space T)} {rp : D.IsRelativelyPerfect T E}
    {nn : D.HasNoNegativeFibreExt T E} {rp' : D.IsRelativelyPerfect T E'}
    {nn' : D.HasNoNegativeFibreExt T E'} (m : x₀ ⟶ ⟨T, E, rp, nn⟩)
    (n : ComplexesHom ⟨T, E, rp, nn⟩ ⟨T, E', rp', nn'⟩) (hn : n.base = 𝟙 T) {t : T ⟶ x₀.T}
    (hbt : m.base ≫ t = 𝟙 x₀.T)
    (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
    (hT : T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))
    (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hbt' : (m.comp n).base ≫ t = 𝟙 x₀.T)
    (hb' : IsSquareZeroClosedImmersion B S hS (m.comp n).base.left)
    (hβ' : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫
        (m.comp n).base.left ≫ eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    DerivedLift.Isomorphic (fibreDataDerivedLift (hDer := hDer) ⟨T, E, rp, nn⟩ m t hbt hb hT hβ hK)
      (fibreDataDerivedLift (hDer := hDer) ⟨T, E', rp', nn'⟩ (m.comp n) t hbt' hb' hT
        hβ' hK) := by
  obtain ⟨nb, nf, hnf⟩ := n
  change nb = 𝟙 T at hn
  subst hn
  let χ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj E' ⟶ x₀.E :=
    (D.relativeMapComparison (Category.comp_id m.base)).inv.app E' ≫
      (m.comp (A'' := ⟨T, E', rp', nn'⟩) ⟨𝟙 T, nf, hnf⟩).fibre
  have hχi : IsIso χ := @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (m.comp (A'' := ⟨T, E', rp', nn'⟩) ⟨𝟙 T, nf, hnf⟩).isIso_fibre
  have hχ : (⟨m.base, χ, hχi⟩ : ComplexesHom x₀ ⟨T, E', rp', nn'⟩) =
      m.comp (A'' := ⟨T, E', rp', nn'⟩) ⟨𝟙 T, nf, hnf⟩ :=
    ComplexesHom.ext (Category.comp_id m.base).symm
      (Functor.eqToHom_comp_eqToIso_inv_app _ E' _ _)
  let ε : E ≅ E' := (@asIso _ _ _ _ nf hnf).symm ≪≫ (D.idComparison T).app E'
  have hε' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map ε.hom ≫ χ =
      m.fibre :=
    D.fibreComp_id_fibre_cancel m.base m.fibre nf hnf _ (ComplexesHom.comp_fibre _ _)
  exact (fibreDataDerivedLift_isomorphic_of_iso m χ hbt hb hT hβ ε hε' hK).trans
    (fibreDataDerivedLift_congr hχ hbt hb hT hβ hbt' hb' hβ' hK)

/-- **Naturality of the lift of `E₀`.** A morphism `n : A ⟶ A'` of `Complexes_{X/Y}` whose
base map is an identity of test schemes (up to an equality of the underlying objects of the
site), compatible with morphisms `m : x₀ ⟶ A`, `m' : x₀ ⟶ A'` and with retractions, gives
isomorphic lifts of `E₀`. -/
theorem fibreDataDerivedLift_isomorphic {A A' : ComplexesObject D} (m : x₀ ⟶ A) (n : A ⟶ A')
    (m' : x₀ ⟶ A') (hm : m ≫ n = m') {t : A.T ⟶ x₀.T} {t' : A'.T ⟶ x₀.T}
    (htn : t = n.base ≫ t') (h : A.T.left = A'.T.left) (hn : n.base.left = eqToHom h)
    (hbt : m.base ≫ t = 𝟙 x₀.T) (hb : IsSquareZeroClosedImmersion B S hS m.base.left)
    (hT : A.T.left = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      ((fgSiteModule B hk).obj V))
    (hβ : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m.base.left ≫
        eqToHom hT =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hbt' : m'.base ≫ t' = 𝟙 x₀.T) (hb' : IsSquareZeroClosedImmersion B S hS m'.base.left)
    (hT' : A'.T.left =
      squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).obj V))
    (hβ' : eqToHom (fieldPoint_left_eq_algebraOver D iΛ x₀ hx₀ hk).symm ≫ m'.base.left ≫
        eqToHom hT' =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        ((fgSiteModule B hk).obj V))
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    DerivedLift.Isomorphic (fibreDataDerivedLift (hDer := hDer) A m t hbt hb hT hβ hK)
      (fibreDataDerivedLift (hDer := hDer) A' m' t' hbt' hb' hT' hβ' hK) := by
  subst hm
  obtain ⟨⟨Tl, ⟨⟨⟩⟩, Th⟩, E, rp, nn⟩ := A
  obtain ⟨⟨Tl', ⟨⟨⟩⟩, Th'⟩, E', rp', nn'⟩ := A'
  change Tl = Tl' at h
  subst h
  have hTh : Th = Th' := by
    have hw := CostructuredArrow.w n.base
    change _ = eqToHom rfl at hn
    rw [hn, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] at hw
    exact hw.symm
  subst hTh
  have hnb : n.base = 𝟙 _ := CostructuredArrow.hom_ext _ _ (by simpa using hn)
  have htt : t = t' := by rw [htn, hnb, Category.id_comp]
  subst htt
  exact fibreDataDerivedLift_isomorphic_of_id m n hnb hbt hb hT hβ hbt' hb' hβ' hK

/-- The retraction of the source of a morphism of lifts of `w₀` factors through its base map and
the retraction of the target. -/
theorem fibreLiftRetraction_eq_comp {M : SiteModule k B} {y y' : FibreLift D iΛ x₀ hx₀ hk M}
    (φ : y.1 ⟶ y'.1) :
    fibreLiftRetraction y = φ.right.a.base ≫ fibreLiftRetraction y' := by
  have hw : φ.right.a.base ≫ y'.1.right.iso.hom.down =
      y.1.right.iso.hom.down ≫
        ((schemePointToBase D.Y x₀.T.left x₀.T.hom).map φ.right.b).down :=
    congrArg ULift.down φ.right.w
  have hb : ((schemePointToBase D.Y x₀.T.left x₀.T.hom).map φ.right.b).down ≫
      CostructuredArrow.homMk (overMapHom x₀.T.left y'.1.right.y) rfl =
        CostructuredArrow.homMk (overMapHom x₀.T.left y.1.right.y) rfl := by
    exact CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (Over.w φ.right.b))
  unfold fibreLiftRetraction
  exact ((congrArg (y.1.right.iso.hom.down ≫ ·) hb.symm).trans
    (Category.assoc _ _ _).symm).trans
    ((congrArg (· ≫ CostructuredArrow.homMk (overMapHom x₀.T.left y'.1.right.y) rfl)
      hw.symm).trans (Category.assoc _ _ _))

/-- The base map of a morphism of lifts of `w₀` in the fibre over `k[M]` is an identity of test
schemes, up to the equality of their underlying objects of the site. -/
theorem fibreLift_hom_base_left {M : SiteModule k B} {y y' : FibreLift D iΛ x₀ hx₀ hk M}
    (φ : y ⟶ y') :
    φ.1.right.a.base.left = eqToHom ((fibreLiftScheme_left_eq y).trans
      (fibreLiftScheme_left_eq y').symm) := by
  have h2 := φ.2
  have e1 := congrArg CommaMorphism.right (IsHomLift.fac' (Under.post
    (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
      (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom)))
    (𝟙 (Under.mk (eqToHom (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) ≫
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk M))) φ.1)
  simp only [Under.post_map, Under.eqToHom_right, TwoFibreProductOver.structureFunctor_map,
    Category.id_comp, eqToHom_trans] at e1
  have h3 := φ.1.right.ha
  have e4 := IsHomLift.fac' (complexesFunctor D) φ.1.right.hbase φ.1.right.a
  show (complexesFunctor D).map φ.1.right.a = _
  exact e4.trans (eqToHom_comp_comp_eqToHom_of_eq _ _ _ _ _ e1)

/-- **Stacks 0DLL, `c3 (a)`: naturality of the lift of `E₀` along morphisms of lifts of `w₀`.**
A morphism `y ⟶ y'` of lifts of `w₀` in the fibre over `k[V]` gives isomorphic lifts
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift` of `E₀`. -/
theorem fibreLiftDerivedLift_isomorphic
    {y y' : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V)} (φ : y ⟶ y')
    (hK : DerivedCategory.TStructure.t.minus x₀.E) :
    DerivedLift.Isomorphic (fibreLiftDerivedLift (hDer := hDer) y hK)
      (fibreLiftDerivedLift (hDer := hDer) y' hK) := by
  rw [fibreLiftDerivedLift_eq, fibreLiftDerivedLift_eq]
  exact fibreDataDerivedLift_isomorphic (x₀ := x₀) (hx₀ := hx₀) (hDer := hDer)
    y.1.hom.a φ.1.right.a y'.1.hom.a
    ((TwoFibreProductOver.comp_a _ _).symm.trans
      (congrArg TwoFibreProductOver.Hom.a (Under.w φ.1)))
    (fibreLiftRetraction_eq_comp φ.1) _ (fibreLift_hom_base_left φ) _ _ _ _ _ _ _ _ hK

/-- **The class of lifts of `E₀⟦m⟧` of a class of lifts of `w₀` is computed on any
representative**: `AlgebraicGeometry.Space.ComplexesSituation.fibreLiftClass` of the class of `y`
is the shift of the class of
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftDerivedLift y`. -/
theorem fibreLiftClass_mk (hK : DerivedCategory.TStructure.t.minus x₀.E) (m : ℤ)
    (hKm : DerivedCategory.TStructure.t.minus (x₀.E⟦m⟧))
    (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V)) :
    fibreLiftClass (hDer := hDer) hK m hKm (Quotient.mk _ y) =
      DerivedLift.classShift.{d, u + 1, u, u, u + 1}
        (T := derivedExtensionOfScalarsData.{d, u + 1}
          (sqZeroExtSheafAnySiteProj
            ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V)))
        (K₀ := ⟨x₀.E, hK⟩) m (Iso.refl _)
        (Quotient.mk _ (fibreLiftDerivedLift (hDer := hDer) y hK)) := by
  obtain ⟨e⟩ := Quotient.mk_out (s := isIsomorphicSetoid _) y
  unfold fibreLiftClass
  congr 1
  exact Quotient.sound (fibreLiftDerivedLift_isomorphic e.hom hK)

end ComplexesSituation

end AlgebraicGeometry.Space

end
