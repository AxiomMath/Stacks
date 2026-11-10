module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerivedComp
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower

/-!
# Restriction of scalars of the compactly supported cohomology of the geometric fibre

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings.  For a bounded below complex `K` of
sheaves of `Λ'`-modules on `X_étale`, the complex `RΓ_c(X_k̄, K)` of
`Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`, viewed as a complex of `Λ`-modules, is
`RΓ_c(X_k̄, K|_Λ)`, compatibly with the canonical geometric Frobenius `π_X^*` of
`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`.  Every step of the construction
(extension by zero, inverse image to `X̄_k̄`, derived direct image to `Spec k̄`, derived global
sections) commutes with restriction of scalars, and so do the ingredients of `π_X^*`.

This is the comparison of the cohomology of a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules with that of the same
sheaf viewed as a sheaf of `ℤ_ℓ`-modules used in [Tag 03V2].

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-! ### Restriction to the geometric fibre -/

section Restriction

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ' Y.left))

/-- The restriction to `Y_k̄` of a bounded below complex commutes with `res_ρ`, degreewise. -/
def inverseImageRestrictScalarsComplexIso :
    (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ'
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N) ≅
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N) :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
    (etaleModuleInverseImageRestrictScalars ρ (fieldBaseChangeProj Y kbar)).symm
        (ComplexShape.up ℤ)).app N.obj)

/-- **The restriction `C|_{Y_k̄}` commutes with `res_ρ`** in the bounded below derived
category. -/
def fieldBaseChangeRestrictionRestrictScalarsIso :
    (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.obj
        (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) ≅
      fieldBaseChangeRestriction.{u, 0} Λ Y kbar
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N) :=
  (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar))).app
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N) ≪≫ DerivedCategory.Plus.Q.mapIso
      (inverseImageRestrictScalarsComplexIso ρ Y kbar N)

/-- The forward map of `fieldBaseChangeRestrictionRestrictScalarsIso` is the comparison
`res_ρ ∘ Q ⟶ Q ∘ res_ρ` followed by `Q` applied to `inverseImageRestrictScalarsComplexIso`. -/
theorem fieldBaseChangeRestrictionRestrictScalarsIso_hom :
    (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom =
      (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
          (fieldBaseChange Y kbar))).hom.app ((etaleModuleInverseImage.{u, 0} Λ'
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N) ≫ DerivedCategory.Plus.Q.map
          ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom) :=
  rfl

end Restriction

/-- A bookkeeping identity in a category: a composite `a ≫ b ≫ t ≫ r ≫ s` is rewritten along
a round trip `hπ ≫ iπ = 𝟙` and four commutative squares. -/
theorem comp_eq_of_roundTrip {C : Type*} [Category* C] {A B B' D E E' F A' H G : C}
    (a : A ⟶ B) (b : B ⟶ D) (t : D ⟶ E) (r : E ⟶ E') (s : E' ⟶ G) (hπ : B ⟶ B')
    (iπ : B' ⟶ B) (h₀ : A ⟶ A') (x : A' ⟶ B') (d : B' ⟶ E') (r' : E' ⟶ E) (y : B' ⟶ H)
    (d₂ : H ⟶ G) (c : A' ⟶ F) (w : F ⟶ H) (hA : a ≫ hπ = h₀ ≫ x) (hB : iπ ≫ b ≫ t = d ≫ r')
    (hC : d ≫ s = y ≫ d₂) (hD : x ≫ y = c ≫ w) (hhi : hπ ≫ iπ = 𝟙 _) (hih : r' ≫ r = 𝟙 _) :
    a ≫ b ≫ t ≫ r ≫ s = (h₀ ≫ c) ≫ w ≫ d₂ := by
  calc a ≫ b ≫ t ≫ r ≫ s = a ≫ (hπ ≫ iπ) ≫ b ≫ t ≫ r ≫ s := by rw [hhi, Category.id_comp]
    _ = (a ≫ hπ) ≫ (iπ ≫ b ≫ t) ≫ r ≫ s := by simp only [Category.assoc]
    _ = h₀ ≫ x ≫ d ≫ (r' ≫ r) ≫ s := by rw [hA, hB]; simp only [Category.assoc]
    _ = h₀ ≫ (x ≫ y) ≫ d₂ := by rw [hih, Category.id_comp, hC]; simp only [Category.assoc]
    _ = (h₀ ≫ c) ≫ w ≫ d₂ := by rw [hD]; simp only [Category.assoc]

/-- A bookkeeping identity in a category: four commutative squares pasted along a composite. -/
theorem comp_eq_of_four_squares {C : Type*} [Category* C] {D B E G H F I : C}
    (m₁ : D ⟶ B) (m₂ : B ⟶ D) (θ : D ⟶ E) (θ' : B ⟶ G) (a : E ⟶ G) (b : G ⟶ H) (e : H ⟶ E)
    (r : E ⟶ F) (s : H ⟶ I) (e₂ : I ⟶ F) (l : F ⟶ I)
    (h₁ : m₁ ≫ θ' = θ ≫ a) (h₂ : m₂ ≫ θ = θ' ≫ b ≫ e) (h₃ : e ≫ r = s ≫ e₂)
    (h₄ : a ≫ b ≫ s = r ≫ l) :
    (m₁ ≫ m₂) ≫ θ ≫ r = θ ≫ r ≫ l ≫ e₂ := by
  rw [Category.assoc, ← Category.assoc m₂ θ r, h₂]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, h₃, reassoc_of% h₄]

/-! ### The Frobenius twist -/

section Frobenius

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ' Y.left))

/-- The Frobenius base change twist applied degreewise commutes with `res_ρ`. -/
theorem restrictScalars_frobeniusTwist_complex :
    (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapCochainComplexPlus.map
        (ObjectProperty.homMk (X := ((etaleModuleInverseImage.{u, 0} Λ'
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) (Y :=
        (etaleModuleDirectImage.{u, 0} Λ'
        (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ'
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) ((NatTrans.mapHomologicalComplex
        (frobeniusBaseChangeTwist.{u, 0} Λ' Y kbar p q hcard) (ComplexShape.up ℤ)).app N.obj)) ≫
        (etaleModuleDirectImage.{u, 0} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
        ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom) =
        ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom) ≫ (ObjectProperty.homMk (X :=
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) (Y :=
        (etaleModuleDirectImage.{u, 0} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)))
        ((NatTrans.mapHomologicalComplex (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
        (ComplexShape.up ℤ)).app
        ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N).obj)) := by
  ext n : 2
  have h := frobeniusBaseChangeTwist_restrictScalars ρ Y kbar p q hcard (N.obj.X n)
  have e : inverseImageRestrictScalarsApp ρ (fieldBaseChangeProj Y kbar) (N.obj.X n) =
      (etaleModuleInverseImageRestrictScalars ρ (fieldBaseChangeProj Y kbar)).hom.app
          (N.obj.X n) := rfl
  rw [e] at h
  change (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).map
      ((frobeniusBaseChangeTwist.{u, 0} Λ' Y kbar p q hcard).app (N.obj.X n)) ≫
      (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          ((etaleModuleInverseImageRestrictScalars ρ (fieldBaseChangeProj Y kbar)).inv.app
          (N.obj.X n)) =
    (etaleModuleInverseImageRestrictScalars ρ (fieldBaseChangeProj Y kbar)).inv.app (N.obj.X n) ≫
      (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
          ((etaleModuleRestrictScalars ρ Y.left).obj (N.obj.X n))
  refine (Iso.eq_inv_comp ((etaleModuleInverseImageRestrictScalars ρ
      (fieldBaseChangeProj Y kbar)).app (N.obj.X n))).2 ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (((etaleModuleDirectImage.{u, 0} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard)).map_comp _ _).symm.trans
      ((congrArg (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).map (Iso.hom_inv_id_app _ _)).trans
          ((etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).map_id _)))).trans
        (Category.comp_id _))))

/-- The image under `Q` of `restrictScalars_frobeniusTwist_complex`: the Frobenius base change
twist commutes with `res_ρ` in the bounded below derived category. -/
theorem restrictScalars_frobeniusTwist_Q :
    DerivedCategory.Plus.Q.map ((etaleModuleRestrictScalars ρ
        (fieldBaseChange Y kbar)).mapCochainComplexPlus.map (ObjectProperty.homMk (X :=
        ((etaleModuleInverseImage.{u, 0} Λ'
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) (Y :=
        (etaleModuleDirectImage.{u, 0} Λ'
        (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ'
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) ((NatTrans.mapHomologicalComplex
        (frobeniusBaseChangeTwist.{u, 0} Λ' Y kbar p q hcard) (ComplexShape.up ℤ)).app N.obj))) ≫
        DerivedCategory.Plus.Q.map ((etaleModuleDirectImage.{u, 0} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
        ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom)) =
      DerivedCategory.Plus.Q.map ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom) ≫
          DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := (etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) (Y :=
          (etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)))
          ((NatTrans.mapHomologicalComplex (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
          (ComplexShape.up ℤ)).app
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N).obj)) :=
  (DerivedCategory.Plus.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Plus.Q.map
    (restrictScalars_frobeniusTwist_complex ρ Y kbar p q hcard N)).trans
        (DerivedCategory.Plus.Q.map_comp _ _))

/-- The derived unit of `π̄_*` at the restricted complex, after the comparison. -/
theorem restrictScalars_frobenius_derivedUnit :
    (Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, 0} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard))).app ((etaleModuleRestrictScalars ρ
        (fieldBaseChange Y kbar)).mapCochainComplexPlus.obj ((etaleModuleInverseImage.{u, 0} Λ'
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
            (DerivedCategory.Plus.Q.map ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom)) =
      DerivedCategory.Plus.Q.map ((etaleModuleDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
          ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom)) ≫
        (Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard))).app ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) :=
  ((Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard))).naturality
      ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom)).symm

/-- **The canonical map `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})` commutes with `res_ρ`.** -/
theorem restrictScalars_frobeniusRestrictionDerivedMap :
    (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.map
        (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N) ≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).hom.app
          (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
        (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom =
    (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom ≫
      frobeniusRestrictionDerivedMap.{u, 0} Λ Y kbar p q hcard
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N) := by
  let R := etaleModuleDerivedDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
  let a := (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.map
      (DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) (Y :=
      (etaleModuleDirectImage.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} Λ' Y kbar p q hcard) (ComplexShape.up ℤ)).app N.obj)))
  let b := (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.map
      ((Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard))).app ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N))
  let t := (etaleModuleDerivedDirectImageRestrictScalars ρ
      (geometricFrobeniusBaseChange Y kbar p q hcard)).hom.app (DerivedCategory.Plus.Q.obj
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N))
  let h₀ := (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar))).hom.app ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)
  let i₀ := (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar))).inv.app ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)
  let hπ := (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar))).hom.app ((etaleModuleDirectImage.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N))
  let iπ := (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar))).inv.app ((etaleModuleDirectImage.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N))
  let x := DerivedCategory.Plus.Q.map ((etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar)).mapCochainComplexPlus.map (ObjectProperty.homMk (X :=
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) (Y :=
      (etaleModuleDirectImage.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} Λ' Y kbar p q hcard) (ComplexShape.up ℤ)).app N.obj)))
  let d := (Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard))).app ((etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar)).mapCochainComplexPlus.obj ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N))
  let cβ := DerivedCategory.Plus.Q.map ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom)
  let yβ := DerivedCategory.Plus.Q.map ((etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
      ((inverseImageRestrictScalarsComplexIso ρ Y kbar N).hom))
  let w := DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) (Y :=
      (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)))
      ((NatTrans.mapHomologicalComplex (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
      (ComplexShape.up ℤ)).app
      ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N).obj))
  let d₂ := (Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard))).app ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
      ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N))
  have hA : a ≫ hπ = h₀ ≫ x := (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar))).hom.naturality (ObjectProperty.homMk (X :=
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) (Y :=
      (etaleModuleDirectImage.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)) ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} Λ' Y kbar p q hcard) (ComplexShape.up ℤ)).app N.obj))
  have hB : iπ ≫ b ≫ t = d ≫ R.map i₀ := restrictScalars_directImage_derivedUnit ρ
      (geometricFrobeniusBaseChange Y kbar p q hcard) ((etaleModuleInverseImage.{u, 0} Λ'
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)
  have hC : d ≫ R.map cβ = yβ ≫ d₂ := restrictScalars_frobenius_derivedUnit ρ Y kbar p q hcard N
  have hD : x ≫ yβ = cβ ≫ w := restrictScalars_frobeniusTwist_Q ρ Y kbar p q hcard N
  have hhi : hπ ≫ iπ = 𝟙 _ := Iso.hom_inv_id_app _ _
  have hih : R.map i₀ ≫ R.map h₀ = 𝟙 _ :=
    (R.map_comp _ _).symm.trans ((congrArg R.map (Iso.inv_hom_id_app _ _)).trans (R.map_id _))
  have hL : (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.map
      (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N) = a ≫ b :=
    (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.map_comp _ _
  have hR : R.map (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom =
      R.map h₀ ≫ R.map cβ := R.map_comp _ _
  have key := comp_eq_of_roundTrip a b t (R.map h₀) (R.map cβ) hπ iπ h₀ x d (R.map i₀) yβ d₂ cβ w
    hA hB hC hD hhi hih
  exact ((congrArg (· ≫ t ≫ R.map (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom)
    hL).trans ((Category.assoc _ _ _).trans (congrArg (fun z => a ≫ b ≫ t ≫ z) hR))).trans key

/-- **`RΓ(Y_k̄, C|_{Y_k̄})` commutes with `res_ρ`.** -/
def fieldBaseChangeCohomologyRestrictScalarsIso :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ' (Spec (.of kbar))).obj
            ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd Y.hom
            (specAlgebraMap k kbar))).obj (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N))) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N))) :=
  (etaleModuleDerivedGlobalSectionsRestrictScalars ρ (Spec (.of kbar))).app
      ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
      (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) ≪≫ (etaleModuleDerivedGlobalSections.{u, 0} Λ
      (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
        (specAlgebraMap k kbar))).app (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) ≪≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N))

/-- The endomorphism of `Rf_*(C|_{Y_k̄})` induced by the geometric Frobenius commutes with
`res_ρ`, where `f : Y_k̄ ⟶ Spec k̄`. -/
theorem restrictScalars_frobeniusDirectImageEndo :
    (etaleModuleRestrictScalars ρ (Spec (.of kbar))).mapDerivedCategoryPlus.map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd Y.hom (specAlgebraMap k kbar))).map
        (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N) ≫
        (etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ'
        (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
        (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
            (specAlgebraMap k kbar))).hom.app (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) ≫
            (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom
            (specAlgebraMap k kbar))).map
            (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom =
      (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
          (specAlgebraMap k kbar))).hom.app (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) ≫
          (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom ≫
          (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          (frobeniusRestrictionDerivedMap.{u, 0} Λ Y kbar p q hcard
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) ≫
          (etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom
          (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) := by
  have h₁ : (etaleModuleRestrictScalars ρ (Spec (.of kbar))).mapDerivedCategoryPlus.map
      ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd Y.hom (specAlgebraMap k kbar))).map
      (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N)) ≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
          (specAlgebraMap k kbar))).hom.app ((etaleModuleDerivedDirectImage.{u, 0} Λ'
          (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
          (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) =
      (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
          (specAlgebraMap k kbar))).hom.app (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) ≫
          (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.map
          (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N)) :=
    (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
        (specAlgebraMap k kbar))).hom.naturality
        (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N)
  have h₂ : (etaleModuleRestrictScalars ρ (Spec (.of kbar))).mapDerivedCategoryPlus.map
      ((etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
      (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) ≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
      (specAlgebraMap k kbar))).hom.app (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) =
      (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd Y.hom
          (specAlgebraMap k kbar))).hom.app ((etaleModuleDerivedDirectImage.{u, 0} Λ'
          (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
          (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
            ((etaleModuleDerivedDirectImageRestrictScalars ρ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).hom.app
            (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) ≫
            (etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom
            (specAlgebraMap k kbar))
            (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
            ((etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.obj
            (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) :=
    restrictScalars_derivedDirectImageComp_inv ρ (geometricFrobeniusBaseChange Y kbar p q hcard)
        (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
        (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)
  have h₃ : (etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
      ((etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.obj
      (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) ≫ (etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd Y.hom (specAlgebraMap k kbar))).map
      (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom =
      (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom) ≫
          (etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom
          (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) :=
    ((etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ
        (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.naturality
        (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom).symm
  have h₄ : (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom
      (specAlgebraMap k kbar))).map ((etaleModuleRestrictScalars ρ
      (fieldBaseChange Y kbar)).mapDerivedCategoryPlus.map
      (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N)) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((etaleModuleDerivedDirectImageRestrictScalars ρ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).hom.app
          (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N)) ≫ (etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd Y.hom (specAlgebraMap k kbar))).map ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom) =
      (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom ≫
          (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          (frobeniusRestrictionDerivedMap.{u, 0} Λ Y kbar p q hcard
          ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      restrictScalars_frobeniusRestrictionDerivedMap ρ Y kbar p q hcard N]
  rw [Functor.map_comp]
  exact comp_eq_of_four_squares _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

/-- **The canonical endomorphism of `RΓ(Y_k̄, C|_{Y_k̄})` commutes with `res_ρ`.** -/
theorem restrictScalars_frobeniusRestrictionCohomologyEndo :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ' Y kbar p q hcard N) ≫
        (fieldBaseChangeCohomologyRestrictScalarsIso ρ Y kbar N).hom =
      (fieldBaseChangeCohomologyRestrictScalarsIso ρ Y kbar N).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
            ((etaleModuleRestrictScalars ρ Y.left).mapCochainComplexPlus.obj N) := by
  have hn := (etaleModuleDerivedGlobalSectionsRestrictScalars ρ (Spec (.of kbar))).hom.naturality
      ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd Y.hom (specAlgebraMap k kbar))).map
      (frobeniusRestrictionDerivedMap.{u, 0} Λ' Y kbar p q hcard N) ≫
      (etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ'
      (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.app
      (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N))
  simp only [Functor.comp_map] at hn
  simp only [fieldBaseChangeCohomologyRestrictScalarsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, frobeniusRestrictionCohomologyEndo]
  have key := (restrictScalars_frobeniusDirectImageEndo ρ Y kbar p q hcard N).trans
    (Category.assoc _ _ _).symm
  rw [reassoc_of% hn]
  exact (whisker_eq _ (((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map_comp _
    _).symm.trans ((congrArg (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
      key).trans ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map_comp _
        _)))).trans (Category.assoc _ _ _).symm

/-- The canonical endomorphism of `RΓ(Y_k̄, C|_{Y_k̄})` is natural in the complex `C` on `Y`. -/
theorem frobeniusRestrictionCohomologyEndo_naturality {N₁ N₂ : CochainComplex.Plus
    (EtaleModules.{u, 0} Λ Y.left)} (φ : N₁ ⟶ N₂) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
            ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ)) ≫
        frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard N₂ =
      frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard N₁ ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
              ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ)) := by
  have hn := frobeniusRestrictionDerivedMap_naturality.{u, 0} Λ Y kbar p q hcard φ
  have hc := (etaleModuleDerivedDirectImageEndomorphismComp.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard)).inv.naturality
      ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ)
  dsimp only [fieldBaseChangeRestrictionFunctor, Functor.comp_map, Functor.comp_obj] at hn hc
  dsimp only [frobeniusRestrictionCohomologyEndo, fieldBaseChangeRestrictionFunctor,
    Functor.comp_map, Functor.comp_obj]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, hn, Functor.map_comp, Category.assoc,
    Category.assoc, hc]

end Frobenius

/-! ### Cohomology with compact support -/

section CompactSupport

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X))

/-- Extension by zero along the compactification commutes with `res_ρ`, degreewise. -/
def extensionByZeroRestrictScalarsComplexIso :
    (etaleModuleRestrictScalars ρ (Over.mk j.toBase).left).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ' j.immersion).mapCochainComplexPlus.obj K) ≅
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K)) :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
    (etaleModuleExtensionByZeroRestrictScalars ρ j.immersion).symm (ComplexShape.up ℤ)).app K.obj)

/-- **`RΓ_c(X_k̄, K)` commutes with restriction of scalars**: the complex
`RΓ_c(X_k̄, K)` of `Λ'`-modules, viewed as a complex of `Λ`-modules, is `RΓ_c(X_k̄, res_ρ K)`. -/
def compactSupportFrobeniusCohomologyRestrictScalarsIso :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K) ≅
      compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
          ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K) :=
  fieldBaseChangeCohomologyRestrictScalarsIso ρ (Over.mk j.toBase) kbar
      ((etaleModuleExtensionByZero.{u, 0} Λ' j.immersion).mapCochainComplexPlus.obj K) ≪≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom
      (specAlgebraMap k kbar))).mapIso
    ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).mapIso
      (extensionByZeroRestrictScalarsComplexIso ρ f j K)))

/-- **The comparison `RΓ_c(X_k̄, K)|_Λ ≅ RΓ_c(X_k̄, res_ρ K)` commutes with the canonical
geometric Frobenius `π_X^*`.** -/
theorem restrictScalars_canonicalCompactSupportFrobenius :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        (canonicalCompactSupportFrobenius.{u, 0} Λ' f j kbar p q hcard K) ≫
        (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K).hom =
      (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K).hom ≫
        canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
          ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K) := by
  have h₁ := restrictScalars_frobeniusRestrictionCohomologyEndo ρ (Over.mk j.toBase) kbar p q hcard
      ((etaleModuleExtensionByZero.{u, 0} Λ' j.immersion).mapCochainComplexPlus.obj K)
  have h₂ := frobeniusRestrictionCohomologyEndo_naturality (Over.mk j.toBase) kbar p q hcard
    (extensionByZeroRestrictScalarsComplexIso ρ f j K).hom
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₁)).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ h₂.symm).trans (Category.assoc _ _ _).symm))

end CompactSupport

section CompactSupportGroup

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')
  {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X))

/-- **`H^i_c(X_k̄, K)` commutes with restriction of scalars**: the `Λ'`-module
`H^i_c(X_k̄, K)`, viewed as a `Λ`-module, is `H^i_c(X_k̄, res_ρ K)`. -/
def compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} ρ).obj
        (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ' f j kbar K i) ≅
      compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
        ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K) i :=
  ((Stacks.InverseSystem.restrictHomologyIsoOfHom.{u + 1} ρ i).app
      (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
      (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K)

/-- **The comparison `H^i_c(X_k̄, K)|_Λ ≅ H^i_c(X_k̄, res_ρ K)` commutes with `π_X^*`.** -/
theorem restrictScalars_canonicalCompactSupportFrobeniusGroup (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} ρ).map
        (canonicalCompactSupportFrobeniusGroup.{u, 0} Λ' f j kbar p q hcard K i) ≫
        (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar K i).hom =
      (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar K i).hom ≫
        canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar p q hcard
          ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K) i := by
  have hn := (Stacks.InverseSystem.restrictHomologyIsoOfHom.{u + 1} ρ i).inv.naturality
    (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} Λ' f j kbar p q hcard K))
  have hc := restrictScalars_canonicalCompactSupportFrobenius ρ f j kbar p q hcard K
  have hH := congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map hc
  simp only [Functor.map_comp] at hH
  simp only [compactSupportFrobeniusCohomologyGroupRestrictScalarsIso]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hn)).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ hH))

end CompactSupportGroup

end Stacks.EtaleCohomology

end
