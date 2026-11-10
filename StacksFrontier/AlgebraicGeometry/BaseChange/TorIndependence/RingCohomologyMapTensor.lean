module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapFirstSquare
public import StacksFrontier.Homology.TorAmplitude.TermwiseTensorSingleIsoApp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapLocal
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence
public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorProjectionLeft
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# The comparison of Stacks 065Z computed by a resolution of the new ring

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of commutative rings and
`F → R'` a K-flat resolution of `R'` over `R`.  For a K-flat complex `P` of `A`-modules, the
comparison `P|_R ⊗ᴸ_R R' ⟶ (P ⊗ᴸ_A A')|_{R'}` of Stacks 065Z, restricted to `R` and read through
the identification `(P|_R ⊗ᴸ_R R')|_R ≅ P|_R ⊗_R F`, is the class of the chain map
`P|_R ⊗_R F ⟶ P|_R ⊗_R R' ⟶ (A' ⊗_A P)|_R`.

This is the chain-level handle on the comparison through which its invertibility can be compared
for `P` and for `E ⊗_A P`, as in the proof of Stacks 0DKI (1).

## Main results

* `RingTheory.TorIndependence.resolutionTensorToDerived_comp_ringHomSquareComparison`: the
  formula above.
* `RingTheory.TorIndependence.isIso_ringHomSquareComparison_comp_iff`: the comparison followed
  by a morphism `φ` is invertible exactly when its chain-level model over `R` is.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

section Resolution

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']

/-- The comparison of the chosen model of derived extension of scalars, with target spelled as
termwise extension followed by the localization. -/
abbrev extensionComparison {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T) :
    DerivedCategory.Q ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor ⟶
      (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).comparison

/-- The chosen model of derived extension of scalars along `φ` is a left derived functor of
termwise extension of scalars, with comparison `extensionComparison φ`. -/
instance {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      φ).functor.IsLeftDerivedFunctor (extensionComparison φ)
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).isLeftDerived

/-- Extension of scalars along `φ` is a left adjoint, with right adjoint restriction of
scalars. -/
instance {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T) :
    (ModuleCat.extendScalars.{u, u, u} φ).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} φ).isLeftAdjoint

/-- For a K-flat complex `P`, the component of `extensionComparison φ` at `P` is an
isomorphism. -/
theorem isIso_extensionComparison_app {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T)
    (P : CochainComplex (ModuleCat.{u} S) ℤ) (hP : P.KFlat) :
    IsIso ((extensionComparison φ).app P) :=
  CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u} φ _
    (extensionComparison φ) P hP

variable (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : F.KFlat)
  (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))

/-- The underived comparison of Stacks 065Z, `R' ⊗_R M|_R ⟶ (A' ⊗_A M)|_{R'}`. -/
abbrev underivedSquareComparison :
    ModuleCat.restrictScalars.{u} f ⋙ ModuleCat.extendScalars.{u, u, u} g ⟶
      ModuleCat.extendScalars.{u, u, u} h ⋙ ModuleCat.restrictScalars.{u} i :=
  (derivedBaseChangeComparison.{u, u, u, u, u} f g h i sq
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor
    (extensionComparison g) (extensionComparison h)).1

/-- **The comparison of Stacks 065Z through a resolution of `R'`.** For a K-flat complex `P` of
`A`-modules, the comparison at `P`, restricted to `R` and precomposed with the identification
of `(P|_R ⊗ᴸ_R R')|_R` with the descent of `- ⊗_R F`, is the comparison induced by `F → R'`,
followed by the underived comparison and the inverse of the K-flat comparison of `P ⊗ᴸ_A A'`. -/
theorem resolutionTensorToDerived_comp_ringHomSquareComparison
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    haveI := isIso_extensionComparison_app h P hP
    (resolutionTensorToDerived g F hF q).app
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
          ((ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj P)) =
      (resolutionTensorLift F hF).map
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app P) ≫
        (resolutionTensorComparison g F hF q).app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (underivedSquareComparison f g h i sq) (ComplexShape.up ℤ)).app P) ≫
          inv ((ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
              ((extensionComparison h).app P) ≫
            (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))) := by
  have := isIso_extensionComparison_app h P hP
  let Dg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let ρg := (ModuleCat.restrictScalars.{u} g).mapDerivedCategory
  let γ := resolutionTensorToDerived g F hF q
  let facf := (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
  let Pf := ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hsnd := derivedBaseChangeComparison_snd_app_eq.{u, u, u, u, u} f g h i sq
    Dg.functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor
    (extensionComparison g) (extensionComparison h) P
  have hnat : γ.app ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) ≫ ρg.map (Dg.functor.map (facf.hom.app P)) =
      (resolutionTensorLift F hF).map (facf.hom.app P) ≫ γ.app (DerivedCategory.Q.obj Pf) :=
    (γ.naturality (facf.hom.app P)).symm
  have hfac : γ.app (DerivedCategory.Q.obj Pf) ≫ ρg.map ((extensionComparison g).app Pf) =
      (resolutionTensorComparison g F hF q).app Pf :=
    (congrArg (γ.app (DerivedCategory.Q.obj Pf) ≫ ·) (Category.id_comp _).symm).trans
      (resolutionTensorToDerived_fac g F hF q Pf)
  change γ.app _ ≫ ρg.map ((derivedBaseChangeComparison.{u, u, u, u, u} f g h i sq _ _
    (extensionComparison g) (extensionComparison h)).2.1.app (DerivedCategory.Q.obj P)) = _
  rw [hsnd]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hfac]

/-- **The invertibility criterion through a resolution of `R'`.** For a K-flat complex `P` of
`A`-modules and `φ : P ⊗ᴸ_A A' ⟶ N`, the comparison of Stacks 065Z followed by `φ` is invertible
exactly when its chain-level model over `R`, the comparison induced by `F → R'` followed by the
underived comparison, the inverse K-flat comparison and `φ`, is invertible. -/
theorem isIso_ringHomSquareComparison_comp_iff [QuasiIso q]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)
    {N : DerivedCategory (ModuleCat.{u} A')}
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).functor.obj (DerivedCategory.Q.obj P) ⟶ N) :
    haveI := isIso_extensionComparison_app h P hP
    IsIso ((ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map φ) ↔
      IsIso ((resolutionTensorComparison g F hF q).app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (underivedSquareComparison f g h i sq) (ComplexShape.up ℤ)).app P) ≫
          inv ((ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
              ((extensionComparison h).app P) ≫
            (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map φ)) := by
  have := isIso_extensionComparison_app h P hP
  let ρg := (ModuleCat.restrictScalars.{u} g).mapDerivedCategory
  let γ := resolutionTensorToDerived g F hF q
  let L := (resolutionTensorLift F hF).map
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app P)
  let x := (ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj P) ≫
    (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map φ
  have hX := resolutionTensorToDerived_comp_ringHomSquareComparison f g h i sq F hF q P hP
  have key : γ.app ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) ≫ ρg.map x =
      L ≫ ((resolutionTensorComparison g F hF q).app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        ρg.map
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (underivedSquareComparison f g h i sq) (ComplexShape.up ℤ)).app P) ≫
          inv ((ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
              ((extensionComparison h).app P) ≫
            (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map φ)) := by
    simp only [x, Functor.map_comp] at hX ⊢
    rw [reassoc_of% hX]
  have := CompleteRestrictScalarsEquivalence.reflectsIsomorphisms_mapDerivedCategory
    (ModuleCat.restrictScalars.{u} g)
  rw [← isIso_iff_of_reflects_iso x ρg, ← isIso_comp_left_iff (γ.app _), key,
    isIso_comp_left_iff]

end Resolution

/-! ### The `A`-linear model of the comparison -/

section Model

open CochainComplex.ExtendScalars MonoidalCategory

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  (f : R →+* A) (g : R →+* R') (h : A →+* A')

/-- The `R`-linear map `R' ⟶ A'` of the square. -/
def squareLinearMap (i : R' →+* A') (sq : h.comp f = i.comp g) :
    (ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R') ⟶
      (ModuleCat.restrictScalars.{u} f).obj
        ((ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of A' A')) :=
  ModuleCat.ofHom (X := ↑((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
    (Y := ↑((ModuleCat.restrictScalars.{u} f).obj
        ((ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of A' A'))))
    { toFun := fun x => i x
      map_add' := i.map_add
      map_smul' := fun r x => by
        change i (g r * (show R' from x)) = h (f r) * i (show R' from x)
        rw [map_mul, ← RingHom.comp_apply i g, ← sq, RingHom.comp_apply] }

/-- The `A`-linear map `A ⊗_R R' ⟶ A'`, `a ⊗ r' ↦ h(a) i(r')`, of the square. -/
def squareModuleMap (i : R' →+* A') (sq : h.comp f = i.comp g) :
    (ModuleCat.extendScalars.{u, u, u} f).obj
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')) ⟶
      (ModuleCat.restrictScalars.{u} h).obj (ModuleCat.of A' A') :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv _ _).symm
    (squareLinearMap f g h i sq)

/-- The `A`-linear map of complexes `A ⊗_R R'[0] ⟶ A'[0]` of the square. -/
def singleUnitMap (i : R' →+* A') (sq : h.comp f = i.comp g) :
    (mapCochainComplex f).obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) ⟶
      (CochainComplex.restrictScalarsLarge.{u, u, u} h).obj
        (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) :=
  (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} f)
      (ComplexShape.up ℤ) 0).hom.app _ ≫
    (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).map
      (squareModuleMap f g h i sq) ≫
    (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{u} h)
      (ComplexShape.up ℤ) 0).inv.app (ModuleCat.of A' A')

/-- The `A`-linear map of complexes `A ⊗_R F ⟶ A'[0]` induced by `F ⟶ R'[0]`. -/
def resolutionUnitMap (i : R' →+* A') (sq : h.comp f = i.comp g)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) :
    (mapCochainComplex f).obj F ⟶
      (CochainComplex.restrictScalarsLarge.{u, u, u} h).obj
        (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) :=
  (mapCochainComplex f).map q ≫ singleUnitMap f g h i sq

/-- **The `A`-linear model of the comparison of Stacks 065Z**, the map of complexes of
`A`-modules `P ⊗_A (A ⊗_R F) ⟶ (A' ⊗_A P)|_A`, `p ⊗ (a ⊗ x) ↦ h(a) i(q(x)) (1 ⊗ p)`. -/
def resolutionModelMap (i : R' →+* A') (sq : h.comp f = i.comp g)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    P ⊗ (mapCochainComplex f).obj F ⟶
      (CochainComplex.restrictScalarsLarge.{u, u, u} h).obj ((mapCochainComplex h).obj P) :=
  (P ◁ resolutionUnitMap f g h i sq F q) ≫
    leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) ≫
    (CochainComplex.restrictScalarsLarge.{u, u, u} h).map (ρ_ ((mapCochainComplex h).obj P)).hom

/-- The two ways of restricting scalars from `A'` to `R` along the square. -/
def squareRestrictScalarsIso (i : R' →+* A') (sq : h.comp f = i.comp g) :
    ModuleCat.restrictScalars.{u} h ⋙ ModuleCat.restrictScalars.{u} f ≅
      ModuleCat.restrictScalars.{u} i ⋙ ModuleCat.restrictScalars.{u} g :=
  (ModuleCat.restrictScalarsComp' f h (h.comp f) rfl).symm ≪≫
    ModuleCat.restrictScalarsComp' g i (h.comp f) sq

end Model

section ModelEquation

open MonoidalCategory in
/-- Whiskering on the left, read on an antidiagonal summand. -/
theorem ιTensorObj_whiskerLeft_f {T : Type u} [CommRing T]
    (K : CochainComplex (ModuleCat.{u} T) ℤ) {L L' : CochainComplex (ModuleCat.{u} T) ℤ}
    (φ : L ⟶ L') (a b n : ℤ) (hab : a + b = n) :
    HomologicalComplex.ιTensorObj K L a b n hab ≫ (K ◁ φ).f n =
      (K.X a ◁ φ.f b) ≫ HomologicalComplex.ιTensorObj K L' a b n hab := by
  change HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat.{u} T))
      (ComplexShape.up ℤ) a b n hab ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 K) φ (curriedTensor (ModuleCat.{u} T))
      (ComplexShape.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

open MonoidalCategory in
/-- The right unitor, read on the summand `(n, 0)`. -/
theorem ιTensorObj_rightUnitor_hom_f {T : Type u} [CommRing T]
    (X : CochainComplex (ModuleCat.{u} T) ℤ) (n : ℤ) :
    HomologicalComplex.ιTensorObj X (𝟙_ (CochainComplex (ModuleCat.{u} T) ℤ)) n 0 n
        (add_zero n) ≫ (ρ_ X).hom.f n =
      (X.X n ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{u} T))).hom) ≫ (ρ_ (X.X n)).hom := by
  have hinv : (ρ_ X).inv.f n = (ρ_ (X.X n)).inv ≫
      (X.X n ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{u} T))).inv) ≫ HomologicalComplex.ιTensorObj X
          (𝟙_ (CochainComplex (ModuleCat.{u} T) ℤ)) n 0 n (add_zero n) :=
    HomologicalComplex.rightUnitor'_inv X n
  rw [← cancel_mono ((ρ_ X).inv.f n), Category.assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f, hinv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact Category.comp_id _

open CochainComplex.ExtendScalars MonoidalCategory ChangeOfRings

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)

/-- The comparison `R' ⊗_R M ⟶ A' ⊗_A M` of `underivedSquareComparison` sends `r' ⊗ m` to
`i r' ⊗ m`. -/
theorem underivedSquareComparison_app_tmul (M : ModuleCat.{u} A) (r' : R') (m : M) :
    ((underivedSquareComparison f g h i sq).app M).hom (r' ⊗ₜ[R,g] m) = (i r') ⊗ₜ[A,h] m :=
  (derivedBaseChangeComparison.{u, u, u, u, u} f g h i sq
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor
    (extensionComparison g) (extensionComparison h)).2.2.1 M r' m

/-- The projection formula, read on the summand `(n, 0)`. -/
theorem ιTensorObj_projectionMap_f (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (S : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P)
        S n 0 n (add_zero n) ≫ (projectionMap f P S).f n =
      (CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso.{u, u, u} f (P.X n)
          (S.X 0)).inv ≫
        (ModuleCat.restrictScalars.{u} f).map
          (HomologicalComplex.ιTensorObj P ((mapCochainComplex f).obj S) n 0 n (add_zero n)) := by
  rw [projectionMap, ← baseChange_tensor_iso_inv_eq]
  exact CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_isoX_inv_ι f S P n n 0
    (add_zero n)

/-- The termwise model of `termwiseComparison_eq_model` in degree `n`: the projection formula
followed by the restriction to `R` of the module map on the summand `(n, 0)`. -/
theorem termwiseModel_f_eq (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ((StacksDraft.TorAmplitude.termwiseTensorSingleIso
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).hom.app
        ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P) ≫
      projectionMap f P ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) ≫
      (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
        ((P ◁ singleUnitMap f g h i sq) ≫
          leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} h).map
            (ρ_ ((mapCochainComplex h).obj P)).hom)).f n =
      (CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso.{u, u, u} f (P.X n)
          (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).X 0)).inv ≫
        (ModuleCat.restrictScalars.{u} f).map ((P.X n ◁ (singleUnitMap f g h i sq).f 0) ≫
          CochainComplex.ExtendScalars.leftProjectionModuleMap h (P.X n)
            ((𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)).X 0) ≫
          (ModuleCat.restrictScalars.{u} h).map
            ((((mapCochainComplex h).obj P).X n ◁
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (𝟙_ (ModuleCat.{u} A'))).hom) ≫
              (ρ_ (((mapCochainComplex h).obj P).X n)).hom)) := by
  have L1 := ιTensorObj_projectionMap_f f P ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) n
  have L2 := ιTensorObj_whiskerLeft_f P (singleUnitMap f g h i sq) n 0 n (add_zero n)
  have L4 := CochainComplex.ExtendScalars.ιTensorObj_leftProjectionMap_f h P
    (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) n 0 n (add_zero n)
  have hT : ((StacksDraft.TorAmplitude.termwiseTensorSingleIso
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).hom.app
      ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P)).f n =
      HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P)
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) n 0 n (add_zero n) := by
    rw [StacksDraft.TorAmplitude.termwiseTensorSingleIso_hom_app]
    rfl
  have hM : ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map
      ((P ◁ singleUnitMap f g h i sq) ≫
        leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} h).map
          (ρ_ ((mapCochainComplex h).obj P)).hom)).f n =
      (ModuleCat.restrictScalars.{u} f).map ((P ◁ singleUnitMap f g h i sq).f n ≫
        (leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))).f n ≫
        (ModuleCat.restrictScalars.{u} h).map ((ρ_ ((mapCochainComplex h).obj P)).hom.f n)) :=
    rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hT, hM]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (ModuleCat.restrictScalars.{u} f).map
    ((P ◁ singleUnitMap f g h i sq).f n ≫
      (leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))).f n ≫
      (ModuleCat.restrictScalars.{u} h).map ((ρ_ ((mapCochainComplex h).obj P)).hom.f n)))
    L1).trans ?_)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Functor.map_comp _ _ _).symm.trans (congrArg (ModuleCat.restrictScalars.{u} f).map ?_)
  refine (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ _) L2)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)))
  refine (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ _) L4)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)))
  exact (Functor.map_comp _ _ _).symm.trans (congrArg (ModuleCat.restrictScalars.{u} h).map
    (ιTensorObj_rightUnitor_hom_f ((mapCochainComplex h).obj P) n))

/-- **The comparison of Stacks 065Z is the restriction of its `A`-linear model**, at the level of
the single complex `R'[0]`: the termwise comparison `P|_R ⊗_R R' ⟶ (A' ⊗_A P)|_R` is the
projection formula followed by the restriction to `R` of the `A`-linear map
`P ⊗_A (A ⊗_R R'[0]) ⟶ (A' ⊗_A P)|_A`. -/
theorem termwiseComparison_eq_model (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (Functor.mapHomologicalComplexCompIso (restrictExtendScalarsTensorIso g)
        (ComplexShape.up ℤ)).inv.app
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (underivedSquareComparison f g h i sq)
          (ComplexShape.up ℤ)).app P) ≫
      (NatIso.mapHomologicalComplex (squareRestrictScalarsIso f g h i sq)
        (ComplexShape.up ℤ)).inv.app ((mapCochainComplex h).obj P) =
    (StacksDraft.TorAmplitude.termwiseTensorSingleIso
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).hom.app
        ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P) ≫
      projectionMap f P ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) ≫
      (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
        ((P ◁ singleUnitMap f g h i sq) ≫
          leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} h).map
            (ρ_ ((mapCochainComplex h).obj P)).hom) := by
  let X := (mapCochainComplex h).obj P
  let O := 𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)
  let u' := singleUnitMap f g h i sq
  ext n : 1
  rw [termwiseModel_f_eq f g h i sq P n]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro p r'
  have hl := underivedSquareComparison_app_tmul f g h i sq (P.X n) r' p
  refine (show _ = ((underivedSquareComparison f g h i sq).app (P.X n)).hom (r' ⊗ₜ[R,g] p)
    from rfl).trans (hl.trans ?_)
  change (i r') ⊗ₜ[A,h] (show P.X n from p) = (ρ_ (X.X n)).hom.hom
    ((X.X n ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{u} A'))).hom).hom
      ((CochainComplex.ExtendScalars.leftProjectionModuleMap h (P.X n) (O.X 0)).hom
        ((show P.X n from p) ⊗ₜ[A] ((u'.f 0).hom ((1 : A) ⊗ₜ[R,f] r')))))
  refine Eq.trans ?_ (congrArg ((ρ_ (X.X n)).hom.hom ∘
    (X.X n ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{u} A'))).hom).hom)
    (CochainComplex.ExtendScalars.leftProjectionModuleMap_tmul h (P.X n) (O.X 0) p
      ((u'.f 0).hom ((1 : A) ⊗ₜ[R,f] r')))).symm
  calc (i r') ⊗ₜ[A,h] (show P.X n from p)
      = ((h 1 * i r') * 1) ⊗ₜ[A,h] (show P.X n from p) := by rw [map_one, one_mul, mul_one]
    _ = _ := rfl

/-- The projection formula is natural in the complex of modules over the smaller ring. -/
theorem projectionMap_naturality_right {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T)
    (L : CochainComplex (ModuleCat.{u} T) ℤ) {K K' : CochainComplex (ModuleCat.{u} S) ℤ}
    (v : K ⟶ K') :
    ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ◁ v) ≫ projectionMap φ L K' =
      projectionMap φ L K ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
          (L ◁ (mapCochainComplex φ).map v) := by
  have h1 := restrictScalarsLaxTensor_naturality φ (𝟙 L) ((mapCochainComplex φ).map v)
  rw [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at h1
  have h2 : ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ◁ v) ≫
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ◁
        (extendRestrictScalarsComplexAdj φ).unit.app K') =
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ◁
        (extendRestrictScalarsComplexAdj φ).unit.app K) ≫
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ◁
        (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map ((mapCochainComplex φ).map v)) := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
    exact congrArg _ ((extendRestrictScalarsComplexAdj φ).unit.naturality v).symm
  simp only [projectionMap, id_tensorHom]
  rw [reassoc_of% h2, h1, Category.assoc]

/-- **The comparison of Stacks 065Z through a resolution of `R'` is the restriction of its
`A`-linear model**: the chain map `P|_R ⊗_R F ⟶ P|_R ⊗_R R' ⟶ (A' ⊗_A P)|_R` is the projection
formula followed by the restriction to `R` of `resolutionModelMap`. -/
theorem resolutionComparison_eq_model (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P ◁ q) ≫
      (StacksDraft.TorAmplitude.termwiseTensorSingleIso
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).inv.app
        ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P) ≫
      (Functor.mapHomologicalComplexCompIso (restrictExtendScalarsTensorIso g)
        (ComplexShape.up ℤ)).inv.app
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (underivedSquareComparison f g h i sq)
          (ComplexShape.up ℤ)).app P) ≫
      (NatIso.mapHomologicalComplex (squareRestrictScalarsIso f g h i sq)
        (ComplexShape.up ℤ)).inv.app ((mapCochainComplex h).obj P) =
    projectionMap f P F ≫
      (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
        (resolutionModelMap f g h i sq F q P) := by
  refine (congrArg (((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P ◁ q) ≫
      (StacksDraft.TorAmplitude.termwiseTensorSingleIso
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).inv.app
        ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P) ≫ ·)
    (termwiseComparison_eq_model f g h i sq P)).trans ?_
  refine (congrArg (((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P ◁ q) ≫ ·)
    (Iso.inv_hom_id_app_assoc _ _ _)).trans ?_
  have hR : projectionMap f P F ≫ (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
        (resolutionModelMap f g h i sq F q P) =
      ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj P ◁ q) ≫
        projectionMap f P ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          ((P ◁ singleUnitMap f g h i sq) ≫
            leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) ≫
            (CochainComplex.restrictScalarsLarge.{u, u, u} h).map
              (ρ_ ((mapCochainComplex h).obj P)).hom) := by
    rw [resolutionModelMap, resolutionUnitMap, whiskerLeft_comp, Category.assoc,
      Functor.map_comp, ← reassoc_of% (projectionMap_naturality_right f P q)]
  exact hR.symm

/-- **The `A`-linear model on a tensor product** (the chain identity behind Stacks 0DKI (1)): the
model of `E ⊗_A P` is, up to the associator, the model of `P` tensored with `E`, followed by the
projection formula and the monoidality of extension of scalars. -/
theorem resolutionModelMap_tensor (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
    (E P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (α_ E P ((mapCochainComplex f).obj F)).inv ≫ resolutionModelMap f g h i sq F q (E ⊗ P) =
      (E ◁ resolutionModelMap f g h i sq F q P) ≫
        leftProjectionMap h E ((mapCochainComplex h).obj P) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} h).map
          (extendScalarsMonoidalIso h E P).hom := by
  have h1 := leftProjectionMap_tensor h E P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))
  have h1' : leftProjectionMap h (E ⊗ P) (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) =
      (α_ E P ((CochainComplex.restrictScalarsLarge.{u, u, u} h).obj
          (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)))).hom ≫
        (E ◁ leftProjectionMap h P (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))) ≫
        leftProjectionMap h E ((mapCochainComplex h).obj P ⊗
          𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ)) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} h).map
          ((α_ ((mapCochainComplex h).obj E) ((mapCochainComplex h).obj P)
            (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))).inv ≫
            ((extendScalarsMonoidalIso h E P).hom ▷ 𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))) := by
    rw [Functor.map_comp, ← reassoc_of% h1, ← Functor.map_comp, ← comp_whiskerRight,
      Iso.inv_hom_id, id_whiskerRight, CategoryTheory.Functor.map_id, Category.comp_id]
  have h2 : ((α_ ((mapCochainComplex h).obj E) ((mapCochainComplex h).obj P)
        (𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))).inv ≫
        ((extendScalarsMonoidalIso h E P).hom ▷ 𝟙_ (CochainComplex (ModuleCat.{u} A') ℤ))) ≫
        (ρ_ ((mapCochainComplex h).obj (E ⊗ P))).hom =
      ((mapCochainComplex h).obj E ◁ (ρ_ ((mapCochainComplex h).obj P)).hom) ≫
        (extendScalarsMonoidalIso h E P).hom := by
    rw [Category.assoc, rightUnitor_naturality, rightUnitor_tensor_hom_assoc,
      Iso.inv_hom_id_assoc]
  have h3 := associator_naturality_right E P (resolutionUnitMap f g h i sq F q)
  have h4 := leftProjectionMap_naturality_right h E ((ρ_ ((mapCochainComplex h).obj P)).hom)
  simp only [resolutionModelMap]
  rw [h1', Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp, h2,
    reassoc_of% h3, Iso.inv_hom_id_assoc, Functor.map_comp, ← reassoc_of% h4]
  simp only [whiskerLeft_comp, Category.assoc]

end ModelEquation

section Criterion

open CochainComplex.ExtendScalars MonoidalCategory Stacks.DerivedCategoryComparisons

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)

/-- The two ways of restricting scalars from `D(A')` to `D(R)` along the square. -/
def squareDerivedRestrictIso (i : R' →+* A') (sq : h.comp f = i.comp g) :
    (ModuleCat.restrictScalars.{u} h).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} g).mapDerivedCategory :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (squareRestrictScalarsIso f g h i sq) ≪≫
    mapDerivedCategoryCompIso _ _

/-- On the image of a complex `L` of `A'`-modules in `D(A')`, the isomorphism
`squareDerivedRestrictIso` is, through the identifications of derived restriction of scalars of
a complex with termwise restriction, the class of the termwise isomorphism
`squareRestrictScalarsIso` at `L`. -/
theorem squareDerivedRestrictIso_hom_app_Q (L : CochainComplex (ModuleCat.{u} A') ℤ) :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.restrictScalars.{u} h).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app L) ≫
      (squareDerivedRestrictIso f g h i sq).hom.app (DerivedCategory.Q.obj L) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (squareRestrictScalarsIso f g h i sq)
        (ComplexShape.up ℤ)).hom.app L) ≫
      (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.restrictScalars.{u} i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
      (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
        ((ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.inv.app L) := by
  simp only [squareDerivedRestrictIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← cancel_mono ((mapDerivedCategoryCompIso (ModuleCat.restrictScalars.{u} i)
    (ModuleCat.restrictScalars.{u} g)).inv.app (DerivedCategory.Q.obj L)),
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id, mapDerivedCategoryCompIso_inv_app_Q, mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    mapDerivedCategoryCompIso_inv_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

/-- The bookkeeping behind `isIso_ringHomSquareComparison_comp_iff_model`, for arbitrary functors
and natural isomorphisms: a composite through `ρ_g` is invertible exactly when a composite through
`ρ_f` is, given the identifications `h3`, `h4`, `hλ` relating the two. -/
theorem isIso_comp_iff_of_squareIso {DR DA DA' DR' : Type*} [Category DR] [Category DA]
    [Category DA'] [Category DR'] (ρf : DA ⥤ DR) (ρg : DR' ⥤ DR) (ρh : DA' ⥤ DA)
    (ρi : DA' ⥤ DR') (c : ρh ⋙ ρf ≅ ρi ⋙ ρg) [ρf.ReflectsIsomorphisms]
    {d₁ d₂ n : DA'} (κh : d₂ ⟶ d₁) (hκh : IsIso κh) (φ : d₂ ⟶ n)
    {b₀ e₁ : DR'} (τ : b₀ ⟶ e₁) (φi : ρi.obj d₁ ≅ e₁)
    {a₀ g₁ : DA} (k : a₀ ⟶ g₁) (φh : g₁ ⟶ ρh.obj d₁)
    {s t t' t'' : DR} (l : s ⟶ ρg.obj b₀) (p₁ : s ⟶ t) (hp₁ : IsIso p₁) (ψa : t ⟶ ρf.obj a₀)
    (hψa : IsIso ψa) (rk : t ⟶ t') (ψf : t' ⟶ ρf.obj g₁) (ε : t' ⟶ t'') (ψg : t'' ⟶ ρg.obj e₁)
    (h3 : ψa ≫ ρf.map k = rk ≫ ψf)
    (h4 : ψf ≫ ρf.map φh ≫ c.hom.app d₁ = ε ≫ ψg ≫ ρg.map φi.inv)
    (hl : l ≫ ρg.map τ = p₁ ≫ rk ≫ ε ≫ ψg) :
    IsIso (l ≫ ρg.map (τ ≫ inv (ρi.map κh ≫ φi.hom) ≫ ρi.map φ)) ↔
      IsIso (k ≫ φh ≫ ρh.map (inv κh ≫ φ)) := by
  have := hκh
  have := hp₁
  have := hψa
  have key : l ≫ ρg.map (τ ≫ inv (ρi.map κh ≫ φi.hom) ≫ ρi.map φ) =
      p₁ ≫ ψa ≫ ρf.map (k ≫ φh ≫ ρh.map (inv κh ≫ φ)) ≫ c.hom.app n := by
    have hinv : inv (ρi.map κh ≫ φi.hom) ≫ ρi.map φ = φi.inv ≫ ρi.map (inv κh ≫ φ) := by
      rw [IsIso.inv_comp, Functor.map_comp, Functor.map_inv, IsIso.Iso.inv_hom, Category.assoc]
    rw [hinv]
    generalize inv κh ≫ φ = x
    have hc := c.hom.naturality x
    simp only [Functor.comp_map] at hc
    simp only [Functor.map_comp, Category.assoc]
    rw [hc, reassoc_of% h3, reassoc_of% h4, ← reassoc_of% hl]
  rw [key, isIso_comp_left_iff, isIso_comp_left_iff, ← isIso_iff_of_reflects_iso _ ρf,
    isIso_comp_right_iff]

/-- A chain identity `a ≫ b ≫ c ≫ G(t) = p ≫ r ≫ β`, read through localizations and a natural
transformation `ψ : G ⋙ Q ⟶ Q' ⋙ ρ`. -/
theorem comp_map_eq_of_chain {C C' D D' : Type*} [Category C] [Category C'] [Category D]
    [Category D'] (G : C' ⥤ C) (Q : C ⥤ D) (Q' : C' ⥤ D') (ρ : D' ⥤ D) (ψ : G ⋙ Q ⟶ Q' ⋙ ρ)
    {s : D} {x₀ x₁ x₂ z₁ z₂ : C} {y y' : C'} (fac : s ⟶ Q.obj x₀) (a : x₀ ⟶ x₁) (b : x₁ ⟶ x₂)
    (c : x₂ ⟶ G.obj y) (t : y ⟶ y') (p : x₀ ⟶ z₁) (r : z₁ ⟶ z₂) (β : z₂ ⟶ G.obj y')
    (hch : a ≫ b ≫ c ≫ G.map t = p ≫ r ≫ β) :
    (fac ≫ Q.map a ≫ Q.map b ≫ Q.map c ≫ ψ.app y) ≫ ρ.map (Q'.map t) =
      (fac ≫ Q.map p) ≫ Q.map r ≫ Q.map β ≫ ψ.app y' := by
  have hψ := ψ.naturality t
  simp only [Functor.comp_map] at hψ
  have hQ := congrArg Q.map hch
  simp only [Functor.map_comp] at hQ
  simp only [Category.assoc]
  rw [← hψ, reassoc_of% hQ]

/-- **The invertibility criterion in `D(A)`.** For a K-flat complex `P` of `A`-modules and
`φ : P ⊗ᴸ_A A' ⟶ N`, the comparison of Stacks 065Z followed by `φ` is invertible exactly when
the class of the `A`-linear model `P ⊗_A (A ⊗_R F) ⟶ (A' ⊗_A P)|_A`, followed by `φ` restricted
to `A`, is invertible in `D(A)`. -/
theorem isIso_ringHomSquareComparison_comp_iff_model (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : F.KFlat) (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) [QuasiIso q]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)
    {N : DerivedCategory (ModuleCat.{u} A')}
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).functor.obj (DerivedCategory.Q.obj P) ⟶ N) :
    haveI := isIso_extensionComparison_app h P hP
    IsIso ((ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map φ) ↔
      IsIso (DerivedCategory.Q.map (resolutionModelMap f g h i sq F q P) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app
          ((mapCochainComplex h).obj P) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map
          (inv ((extensionComparison h).app P) ≫ φ)) := by
  have hcmp := isIso_extensionComparison_app h P hP
  rw [isIso_ringHomSquareComparison_comp_iff f g h i sq F hF q P hP φ]
  have := CompleteRestrictScalarsEquivalence.reflectsIsomorphisms_mapDerivedCategory
    (ModuleCat.restrictScalars.{u} f)
  have hfac : IsIso ((Localization.fac (tensorRight F ⋙ DerivedCategory.Q)
      (tensorRight_inverts_of_kFlat F hF) DerivedCategory.Q).hom.app
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    ((Localization.fac (tensorRight F ⋙ DerivedCategory.Q)
      (tensorRight_inverts_of_kFlat F hF) DerivedCategory.Q).app _).isIso_hom
  have hQp : IsIso (DerivedCategory.Q.map (projectionMap f P F)) :=
    Functor.map_isIso DerivedCategory.Q (projectionMap f P F)
  refine isIso_comp_iff_of_squareIso _ _ _ _ (squareDerivedRestrictIso f g h i sq)
    ((extensionComparison h).app P) hcmp φ _
    ((ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.app ((mapCochainComplex h).obj P))
    (DerivedCategory.Q.map (resolutionModelMap f g h i sq F q P))
    ((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app
      ((mapCochainComplex h).obj P)) _
    ((Localization.fac (tensorRight F ⋙ DerivedCategory.Q) (tensorRight_inverts_of_kFlat F hF)
      DerivedCategory.Q).hom.app
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (projectionMap f P F)) (@IsIso.comp_isIso _ _ _ _ _ _ _ hfac hQp)
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
      (P ⊗ (mapCochainComplex f).obj F))
    (((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.app _).isIso_inv)
    (DerivedCategory.Q.map ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map
      (resolutionModelMap f g h i sq F q P)))
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app
      ((CochainComplex.restrictScalarsLarge.{u, u, u} h).obj ((mapCochainComplex h).obj P)))
    (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (squareRestrictScalarsIso f g h i sq)
      (ComplexShape.up ℤ)).hom.app ((mapCochainComplex h).obj P)))
    ((ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.restrictScalars.{u} i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((mapCochainComplex h).obj P)))
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.naturality _).symm
    (squareDerivedRestrictIso_hom_app_Q f g h i sq ((mapCochainComplex h).obj P)) ?_
  refine comp_map_eq_of_chain ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q _
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv _ _ _ _ _ _ _ _ ?_
  refine Eq.trans ?_ (congrArg (· ≫ (NatIso.mapHomologicalComplex
    (squareRestrictScalarsIso f g h i sq) (ComplexShape.up ℤ)).hom.app
      ((mapCochainComplex h).obj P)) (resolutionComparison_eq_model f g h i sq F q P))
  simp only [Category.assoc]
  rfl

end Criterion

end RingTheory.TorIndependence

end
