module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapLocal

/-!
# The base-change map on cohomology for a flat square

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of commutative rings with `A`
flat over `R` and `A'` flat over `A ⊗_R R'`. For every `Y ∈ D(A)` the base-change map of
Stacks 0DJ7 attached to the identity of `Y ⊗ᴸ_A A'` is an isomorphism

`A' ⊗_{A ⊗_R R'} Hⁿ(Y ⊗ᴸ_R R') ≅ Hⁿ(Y ⊗ᴸ_A A')`.

The comparison of Stacks 065Z factors through the tensor square `A ⊗_R R'`, where it is invertible
because `A` is flat over `R` (Stacks 0661), followed by flat base change along
`A ⊗_R R' → A'`, which on cohomology is extension of scalars.

## Main results

* `RingTheory.TorIndependence.homology_ringHomSquareComparison_paste`: on cohomology, the
  comparison of Stacks 065Z for a square with corner `A'` factored through `P → A'` is the
  comparison for the corner `P` followed by the unit of derived base change along `P → A'`.
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_of_flat_of_flat_tensor`: the
  base-change map of a flat square at the identity is an isomorphism.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-! ### The pasted comparison on cohomology -/

section PasteHomology

variable {R A R' P A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing P]
  [CommRing A']

/-- **The pasted comparison on cohomology.** For a commutative square `R → A`, `R → R'`,
`A → P`, `R' → P` and `σ : P → A'`, the map `Hⁿ(K ⊗ᴸ_R R') ⟶ Hⁿ(K ⊗ᴸ_A A')` induced by the
comparison of Stacks 065Z for the corner `A'` is the one for the corner `P`, followed by the unit
`Hⁿ(Z) ⟶ Hⁿ(Z ⊗ᴸ_P A')` at `Z = K ⊗ᴸ_A P` and the composition isomorphism of derived extension
of scalars. -/
theorem homology_ringHomSquareComparison_paste (f : R →+* A) (g : R →+* R') (h₀ : A →+* P)
    (i₀ : R' →+* P) (sq₀ : h₀.comp f = i₀.comp g) (σ : P →+* A')
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((ringHomSquareComparison f g (σ.comp h₀) (σ.comp i₀)
          (by rw [RingHom.comp_assoc, sq₀, ← RingHom.comp_assoc])).app K) ≫
      ((ModuleCat.restrictScalars.{u} (σ.comp i₀)).mapDerivedCategoryHomologyIso n).hom.app
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (σ.comp h₀)).functor.obj K) =
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((ringHomSquareComparison f g h₀ i₀ sq₀).app K) ≫
      ((ModuleCat.restrictScalars.{u} i₀).mapDerivedCategoryHomologyIso n).hom.app
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          h₀).functor.obj K)) ≫
    (ModuleCat.restrictScalars.{u} i₀).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P) n).map
          ((totalDerivedExtensionScalarsAdjunction σ).unit.app
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h₀).functor.obj K)) ≫
        ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryHomologyIso n).hom.app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            σ).functor.obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h₀).functor.obj K))) ≫
    (ModuleCat.restrictScalars.{u} (σ.comp i₀)).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          h₀ σ).hom.app K)) := by
  let T₀ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h₀
  let Tσ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} σ
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (σ.comp h₀)
  let r₀ := ModuleCat.restrictScalars.{u} i₀
  let rσ := ModuleCat.restrictScalars.{u} σ
  let rc := ModuleCat.restrictScalars.{u} (σ.comp i₀)
  let D₀ := r₀.mapDerivedCategory
  let Dσ := rσ.mapDerivedCategory
  let Di := rc.mapDerivedCategory
  let HR := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let HP := DerivedCategory.homologyFunctor (ModuleCat.{u} P) n
  let HA := DerivedCategory.homologyFunctor (ModuleCat.{u} A') n
  let ι₀ := (r₀.mapDerivedCategoryHomologyIso n).hom
  let ισ := (rσ.mapDerivedCategoryHomologyIso n).hom
  let ιc := (rc.mapDerivedCategoryHomologyIso n).hom
  let E := StacksDraft.Perfect.derivedRestrictScalarsComp.{u, u} i₀ σ
  let Cmp := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u} h₀ σ
  let adj := totalDerivedExtensionScalarsAdjunction σ
  let Z : DerivedCategory (ModuleCat.{u} P) := T₀.functor.obj K
  let Z' : DerivedCategory (ModuleCat.{u} A') := Tσ.functor.obj Z
  let c₀ : _ ⟶ D₀.obj Z := (ringHomSquareComparison f g h₀ i₀ sq₀).app K
  let η : Z ⟶ Dσ.obj Z' := adj.unit.app Z
  let e : D₀.obj (Dσ.obj Z') ⟶ Di.obj Z' := E.hom.app Z'
  let cm : Z' ⟶ Th.functor.obj K := Cmp.hom.app K
  have hpaste : (ringHomSquareComparison f g (σ.comp h₀) (σ.comp i₀)
      (by rw [RingHom.comp_assoc, sq₀, ← RingHom.comp_assoc])).app K =
      c₀ ≫ D₀.map η ≫ e ≫ Di.map cm :=
    ringHomSquareComparison_paste f g h₀ i₀ sq₀ σ K
  have n1 : HR.map (Di.map cm) ≫ ιc.app (Th.functor.obj K) = ιc.app Z' ≫ rc.map (HA.map cm) :=
    ιc.naturality cm
  have n2 : HR.map e ≫ ιc.app Z' = ι₀.app (Dσ.obj Z') ≫ r₀.map (ισ.app Z') :=
    homology_derivedRestrictScalarsComp i₀ σ Z' n
  have n3 : HR.map (D₀.map η) ≫ ι₀.app (Dσ.obj Z') = ι₀.app Z ≫ r₀.map (HP.map η) :=
    ι₀.naturality η
  have key : HR.map (D₀.map η) ≫ HR.map e ≫ HR.map (Di.map cm) ≫ ιc.app (Th.functor.obj K) =
      ι₀.app Z ≫ r₀.map (HP.map η) ≫ r₀.map (ισ.app Z') ≫ rc.map (HA.map cm) := by
    let X := rc.map (HA.map cm)
    calc HR.map (D₀.map η) ≫ HR.map e ≫ HR.map (Di.map cm) ≫ ιc.app (Th.functor.obj K)
        = HR.map (D₀.map η) ≫ (HR.map e ≫ ιc.app Z') ≫ X :=
          congrArg (fun t => HR.map (D₀.map η) ≫ HR.map e ≫ t) n1 |>.trans
            (congrArg (fun t => HR.map (D₀.map η) ≫ t) (Category.assoc _ _ _).symm)
      _ = HR.map (D₀.map η) ≫ (ι₀.app (Dσ.obj Z') ≫ r₀.map (ισ.app Z')) ≫ X :=
          congrArg (fun t => HR.map (D₀.map η) ≫ t ≫ X) n2
      _ = (HR.map (D₀.map η) ≫ ι₀.app (Dσ.obj Z')) ≫ r₀.map (ισ.app Z') ≫ X :=
          (congrArg (fun t => HR.map (D₀.map η) ≫ t) (Category.assoc _ _ _)).trans
            (Category.assoc _ _ _).symm
      _ = (ι₀.app Z ≫ r₀.map (HP.map η)) ≫ r₀.map (ισ.app Z') ≫ X :=
          congrArg (fun t => t ≫ r₀.map (ισ.app Z') ≫ X) n3
      _ = _ := Category.assoc _ _ _
  rw [hpaste]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (HR.map c₀ ≫ ·) key

/-- **The pasted comparison on cohomology, elementwise, for any factorization.** For ring maps
`h : A → A'` and `i : R' → A'` that factor as `σ ∘ h₀` and `σ ∘ i₀`, the map
`Hⁿ(K ⊗ᴸ_R R') ⟶ Hⁿ(K ⊗ᴸ_A A')` induced by the comparison of Stacks 065Z sends `m` to the image
of `m` under the comparison for the corner `P`, the unit along `σ` and the composition
isomorphism. The factorizations are equations rather than definitional, so the statement is
made on elements, whose types do not see the module structures. -/
theorem homology_ringHomSquareComparison_apply (f : R →+* A) (g : R →+* R') (h₀ : A →+* P)
    (i₀ : R' →+* P) (sq₀ : h₀.comp f = i₀.comp g) (σ : P →+* A') (h : A →+* A')
    (i : R' →+* A') (sq : h.comp f = i.comp g) (hh : σ.comp h₀ = h) (hi : σ.comp i₀ = i)
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor.obj ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K))) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((ringHomSquareComparison f g h i sq).app K) ≫
      ((ModuleCat.restrictScalars.{u} i).mapDerivedCategoryHomologyIso n).hom.app
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          h).functor.obj K)).hom m =
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          h₀ σ).hom.app K ≫
          eqToHom (congrArg (fun φ : A →+* A' =>
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj K) hh))).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} P) n).map
          ((totalDerivedExtensionScalarsAdjunction σ).unit.app
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h₀).functor.obj K)) ≫
        ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryHomologyIso n).hom.app
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            σ).functor.obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h₀).functor.obj K))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            ((ringHomSquareComparison f g h₀ i₀ sq₀).app K) ≫
          ((ModuleCat.restrictScalars.{u} i₀).mapDerivedCategoryHomologyIso n).hom.app
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h₀).functor.obj K)).hom m)) := by
  subst hh hi
  have key := congrArg (fun φ => φ.hom m)
    (homology_ringHomSquareComparison_paste f g h₀ i₀ sq₀ σ K n)
  rw [eqToHom_refl, Category.comp_id]
  exact key

end PasteHomology

/-! ### The flat square -/

section FlatSquare

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A']
  [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `A ⊗_R R' → A'` restricted to `A` is the structure map of `A'`. -/
theorem baseChangeTensorRingMap_comp_algebraMap_left :
    (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).comp
      (algebraMap A (A ⊗[R] R')) = algebraMap A A' :=
  RingHom.ext fun a => by
    change baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') (a ⊗ₜ[R] 1) = _
    rw [baseChangeTensorRingMap_tmul, map_one, mul_one]

/-- `A ⊗_R R' → A'` restricted to `R'` is the structure map of `A'`. -/
theorem baseChangeTensorRingMap_comp_algebraMap_right :
    (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).comp
      (algebraMap R' (A ⊗[R] R')) = algebraMap R' A' :=
  RingHom.ext fun r => by
    change baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') (1 ⊗ₜ[R] r) = _
    rw [baseChangeTensorRingMap_tmul, map_one, one_mul]

/-- For the tensor square itself, `A ⊗_R R' → A ⊗_R R'` is the identity. -/
theorem baseChangeTensorRingMap_tensor_apply (t : A ⊗[R] R') :
    baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A ⊗[R] R') t = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul a r =>
    rw [baseChangeTensorRingMap_tmul]
    change (a ⊗ₜ[R] (1 : R')) * ((1 : A) ⊗ₜ[R] r) = a ⊗ₜ[R] r
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Postcomposing with the image of an identity does not change a map. -/
private theorem homologyFunctor_map_comp_map_id_comp {B D E : Type*} [Category B] [Category D]
    [Category E] {X : D} {Z : B} (D₀ : B ⥤ D) (H : D ⥤ E) (c : X ⟶ D₀.obj Z) {W : E}
    (θ : H.obj (D₀.obj Z) ⟶ W) :
    H.map (c ≫ D₀.map (𝟙 Z)) ≫ θ = H.map c ≫ θ := by
  simp

/-- **The base-change map of a flat square (Stacks 0DJ8, flat case).** If `A` is flat over `R`
and `A'` is flat over `A ⊗_R R'`, then for every `Y ∈ D(A)` the base-change map
`A' ⊗_{A ⊗_R R'} Hⁿ(Y ⊗ᴸ_R R') ⟶ Hⁿ(Y ⊗ᴸ_A A')` attached to the identity is an isomorphism. -/
theorem isIso_ringBaseChangeCohomologyMap_of_flat_of_flat_tensor [Module.Flat R A]
    (hA' : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      Module.Flat (A ⊗[R] R') A')
    (Y : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') Y
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A A')).functor.obj Y) (𝟙 _) n) := by
  let C := A ⊗[R] R'
  let σ := baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
  letI : Algebra C A' := σ.toAlgebra
  letI := baseChangeCohomologyModule (R := R) (R' := R') Y n
  let h₀ : A →+* C := algebraMap A C
  let i₀ : R' →+* C := algebraMap R' C
  let T₀ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h₀
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A A')
  let Z : DerivedCategory (ModuleCat.{u} C) := T₀.functor.obj Y
  let H := baseChangeCohomologyCat (R := R) (R' := R') Y n
  let HZ := (DerivedCategory.homologyFunctor (ModuleCat.{u} C) n).obj Z
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj (Th.functor.obj Y)
  let HσZ := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      σ).functor.obj Z)
  letI : Module C H' := Module.compHom _ σ
  letI : IsScalarTower C A' H' := IsScalarTower.of_compHom _ _ _
  letI : Module C HσZ := Module.compHom _ σ
  letI : IsScalarTower C A' HσZ := IsScalarTower.of_compHom _ _ _
  -- the comparison of the tensor square
  let c₀ := (ringHomSquareComparison (algebraMap R A) (algebraMap R R') h₀ i₀
    tensorSquare_comm).app Y
  let e₀ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R R')).functor.obj
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj Y)) ⟶
      (ModuleCat.restrictScalars i₀).obj HZ :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map c₀ ≫
      ((ModuleCat.restrictScalars.{u} i₀).mapDerivedCategoryHomologyIso n).hom.app Z
  have he₀ : e₀ = cohomologyComparisonMap (R := R) (A := A) (R' := R') (A' := C) Y Z (𝟙 _) n :=
    (homologyFunctor_map_comp_map_id_comp (ModuleCat.restrictScalars i₀).mapDerivedCategory
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n)
      ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := C)).app Y)
      (((ModuleCat.restrictScalars.{u} i₀).mapDerivedCategoryHomologyIso n).hom.app Z)).symm
  have hc₀ : IsIso c₀ := by
    haveI := isIso_ringHomSquareComparison_tensor (R := R) (A := A) (R' := R')
    exact inferInstance
  have hbij : Function.Bijective e₀.hom := ConcreteCategory.bijective_of_isIso e₀
  have hlin : ∀ (t : C) (m : H), e₀.hom (t • m) = t • (show HZ from e₀.hom m) := by
    intro t m
    have := (cohomologyComparisonLinearMap (R := R) (A := A) (R' := R') (A' := C)
      Y Z (𝟙 _) n).hom.map_smul t m
    rw [he₀]
    refine this.trans ?_
    exact congrArg (· • (show HZ from (cohomologyComparisonMap (R := R) (A := A) (R' := R')
      (A' := C) Y Z (𝟙 _) n).hom m)) (baseChangeTensorRingMap_tensor_apply t)
  let e₀L : H ≃ₗ[C] HZ := LinearEquiv.ofBijective
    { toFun := fun m => e₀.hom m
      map_add' := fun x y => e₀.hom.map_add x y
      map_smul' := hlin } hbij
  -- the unit of flat base change along `σ`
  have hu := isBaseChange_derivedUnitHomologyMap (S := C) (T := A') hA' Z n
  let u : HZ →ₗ[C] HσZ := (derivedUnitHomologyMap (T := A') Z n).hom
  -- the composition isomorphism
  have hh := baseChangeTensorRingMap_comp_algebraMap_left (R := R) (A := A) (R' := R') (A' := A')
  have hi := baseChangeTensorRingMap_comp_algebraMap_right (R := R) (A := A) (R' := R') (A' := A')
  let Ψi := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).mapIso
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
      h₀ σ).app Y ≪≫ eqToIso (congrArg (fun φ : A →+* A' =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj Y) hh))
  let Ψ : HσZ ≃ₗ[A'] H' := Ψi.toLinearEquiv
  let l : H →ₗ[C] H' := (cohomologyComparisonLinearMap (R := R) (R' := R') Y
    (Th.functor.obj Y) (𝟙 _) n).hom
  have hcomm : l.comp e₀L.symm.toLinearMap = (Ψ.toLinearMap.restrictScalars C).comp u := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, rfl⟩ := e₀L.surjective x
    change l (e₀L.symm (e₀L m)) = Ψ (u (e₀L m))
    rw [LinearEquiv.symm_apply_apply]
    have hmor := homologyFunctor_map_comp_map_id_comp
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n)
      ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app Y)
      (((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n).hom.app
        (Th.functor.obj Y))
    refine (congrArg (fun φ => φ.hom m) hmor).trans ?_
    exact homology_ringHomSquareComparison_apply (algebraMap R A) (algebraMap R R') h₀ i₀
      tensorSquare_comm σ (algebraMap A A') (algebraMap R' A') baseChangeSquare hh hi Y n m
  rw [isIso_ringBaseChangeCohomologyMap_iff_isBaseChange_compHom]
  exact (IsBaseChange.iff_of_equiv_comm e₀L.symm Ψ hcomm).mp hu

end FlatSquare

end RingTheory.TorIndependence

end
