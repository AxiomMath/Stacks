module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineFormsMapMono
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHomQcohSource

/-!
# Factoring multiplication by a scalar through the canonical map on forms of affine schemes

Let `R ⟶ A ⟶ C` be a tower of commutative rings and consider the commutative square of affine
schemes

```
Spec C --> Spec A
  |          |
  v          v
Spec R === Spec R
```

all of whose arrows are `Spec` of the structure maps. This file shows that multiplication by
`f : C` on `Ω^a_{Spec C/Spec R}` factors through the canonical map

`(Spec C → Spec A)^* Ω^a_{Spec A/Spec R} ⟶ Ω^a_{Spec C/Spec R}`

of [Stacks, Tag 0FL5] as soon as multiplication by `f` on `⋀^a_C Ω[C⁄R]` factors through
`exteriorPower.map a (KaehlerDifferential.mapBaseChange R A C)`, that is, as soon as the purely
ring-theoretic statement holds.

## Main results

* `exists_comp_relativeDifferentialFormsMap_of_comp`: the abstract criterion, for arbitrary
  comparisons `T` and `E` on the two sides.
* `exists_comp_relativeDifferentialFormsMap_specTower`: for a tower of rings, multiplication by
  `f` on `a`-forms of the square above factors through the canonical map as soon as it factors
  through `exteriorPower.map a (KaehlerDifferential.mapBaseChange R A C)`.

## References

* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AffineExteriorPower (quasicoherentExteriorPowerΓIso)
open Stacks.AlgebraicGeometry.ModuleLimits (moduleSpecHomOfΓMap
  moduleSpecΓFunctor_map_moduleSpecHomOfΓMap)
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialForms

section Criterion

variable {R A C : CommRingCat.{u}} [Algebra ↥R ↥A] [Algebra ↥A ↥C] [Algebra ↥R ↥C]
  [IsScalarTower ↥R ↥A ↥C] {p : Spec A ⟶ Spec R} {p' : Spec C ⟶ Spec R}
  (f : Spec C ⟶ Spec A) (hf : f = Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C)))
  (hcomm : f ≫ p = p' ≫ 𝟙 (Spec R)) (a : ℕ)
  (T : ↥C ⊗[↥A] Ω[↥A⁄↥R] →ₗ[↥C]
    ↥(moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p))))
  (E : Ω[↥C⁄↥R] ≃ₗ[↥C] ↥(moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials p')))
  (hT : ∀ b : ↥A, T ((1 : ↥C) ⊗ₜ KaehlerDifferential.D ↥R ↥A b) =
    pullbackSectionHom f (Scheme.Hom.relativeDifferentials p) ⊤ ⊤ le_top
      ((Scheme.Hom.universalRelativeDerivation p).d ((Scheme.ΓSpecIso A).inv.hom b)))
  (hE : ∀ c : ↥C, E (KaehlerDifferential.D ↥R ↥C c) =
    (Scheme.Hom.universalRelativeDerivation p').d ((Scheme.ΓSpecIso C).inv.hom c))

include hf hcomm hT hE in
/-- In the situation of the global-sections dictionary
`relativeDifferentialFormsMap_Γ_comp_eq_exteriorPower_map_mapBaseChange`, if multiplication by
`c` on `⋀^a_C Ω[C⁄R]` factors through
`exteriorPower.map a (KaehlerDifferential.mapBaseChange R A C)`, then multiplication by `c` on
`Ω^a_{Spec C/Spec R}` factors through the canonical map on `a`-forms. -/
theorem exists_comp_relativeDifferentialFormsMap_of_comp (c : ↥C)
    (ψ : (⋀[↥C]^a Ω[↥C⁄↥R]) →ₗ[↥C] (⋀[↥C]^a (↥C ⊗[↥A] Ω[↥A⁄↥R])))
    (hψ : exteriorPower.map a (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C) ∘ₗ ψ =
      c • LinearMap.id) :
    ∃ Θ : Scheme.Hom.relativeDifferentialForms p' (a : ℤ) ⟶
        (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms p (a : ℤ)),
      ∀ s : ↥(moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentialForms p' (a : ℤ))),
        (moduleSpecΓFunctor.map (Scheme.Hom.relativeDifferentialFormsMap f p p'
              (𝟙 (Spec R)) hcomm (a : ℤ))).hom
            ((moduleSpecΓFunctor.map Θ).hom s) = c • s := by
  have : (Scheme.Hom.relativeDifferentialForms p' (a : ℤ)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_exteriorPower (Scheme.Hom.relativeDifferentials p') a
  set Qt := quasicoherentExteriorPowerΓIso (Scheme.Hom.relativeDifferentials p')
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) a
  set Pi := formsPullbackΓIso f p a
  set V := Qt.hom ≫ ModuleCat.ofHom (exteriorPower.map a E.symm.toLinearMap) ≫
    ModuleCat.ofHom ψ ≫ ModuleCat.ofHom (exteriorPower.map a T) ≫ Pi.inv
  have hEE (w) : exteriorPower.map a E.toLinearMap (exteriorPower.map a E.symm.toLinearMap w) =
      w := by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearEquiv.comp_symm,
      exteriorPower.map_id, LinearMap.id_apply]
  set Phi := moduleSpecΓFunctor.map (Scheme.Hom.relativeDifferentialFormsMap f p p'
    (𝟙 (Spec R)) hcomm (a : ℤ))
  have hpt (z) : Qt.hom.hom (Phi.hom (Pi.inv.hom (exteriorPower.map a T z))) =
      exteriorPower.map a E.toLinearMap
        (exteriorPower.map a (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C) z) :=
    LinearMap.congr_fun
      (relativeDifferentialFormsMap_Γ_comp_eq_exteriorPower_map_mapBaseChange f hcomm a hf T
        E.toLinearMap hT hE) z
  refine ⟨moduleSpecHomOfΓMap V, fun s => (ConcreteCategory.bijective_of_isIso Qt.hom).1 ?_⟩
  have hΘ : (moduleSpecΓFunctor.map (moduleSpecHomOfΓMap V)).hom s =
      Pi.inv.hom (exteriorPower.map a T (ψ
        (exteriorPower.map a E.symm.toLinearMap (Qt.hom.hom s)))) :=
    congrArg (fun k : moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentialForms p' (a : ℤ)) ⟶
        moduleSpecΓFunctor.obj ((Scheme.Modules.pullback f).obj
          (Scheme.Hom.relativeDifferentialForms p (a : ℤ))) => k.hom s)
      (moduleSpecΓFunctor_map_moduleSpecHomOfΓMap V)
  have hz : exteriorPower.map a (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C)
        (ψ (exteriorPower.map a E.symm.toLinearMap (Qt.hom.hom s))) =
      c • exteriorPower.map a E.symm.toLinearMap (Qt.hom.hom s) :=
    LinearMap.congr_fun hψ _
  exact (congrArg (fun y => Qt.hom.hom (Phi.hom y)) hΘ).trans
    ((hpt _).trans
      ((congrArg (exteriorPower.map a E.toLinearMap) hz).trans
        ((map_smul (exteriorPower.map a E.toLinearMap) c _).trans
          ((congrArg (fun y => c • y) (hEE (Qt.hom.hom s))).trans
            (map_smul Qt.hom.hom c s).symm))))

end Criterion

section SpecTower

variable (R A C : CommRingCat.{u}) [Algebra ↥R ↥A] [Algebra ↥A ↥C] [Algebra ↥R ↥C]
  [IsScalarTower ↥R ↥A ↥C]

/-- Multiplication by `c : C` on the `a`-forms of the square attached to a tower of rings
factors through the canonical map on `a`-forms as soon as it factors through
`exteriorPower.map a (KaehlerDifferential.mapBaseChange R A C)`. -/
theorem exists_comp_relativeDifferentialFormsMap_specTower (a : ℕ) (c : ↥C)
    (ψ : (⋀[↥C]^a Ω[↥C⁄↥R]) →ₗ[↥C] (⋀[↥C]^a (↥C ⊗[↥A] Ω[↥A⁄↥R])))
    (hψ : exteriorPower.map a (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C) ∘ₗ ψ =
      c • LinearMap.id) :
    ∃ Θ : Scheme.Hom.relativeDifferentialForms (specTowerBase R C) (a : ℤ) ⟶
        (Scheme.Modules.pullback (specTowerTop A C)).obj
          (Scheme.Hom.relativeDifferentialForms (specTowerMid R A) (a : ℤ)),
      ∀ s : ↥(moduleSpecΓFunctor.obj
          (Scheme.Hom.relativeDifferentialForms (specTowerBase R C) (a : ℤ))),
        (moduleSpecΓFunctor.map (Scheme.Hom.relativeDifferentialFormsMap (specTowerTop A C)
              (specTowerMid R A) (specTowerBase R C) (𝟙 (Spec R)) (specTowerComm R A C)
              (a : ℤ))).hom
            ((moduleSpecΓFunctor.map Θ).hom s) = c • s := by
  obtain ⟨T, -, hT⟩ := exists_pullbackDifferentialsΓBaseChange R A C
  obtain ⟨eC, heC⟩ :=
    AffineDifferentials.exists_specKaehlerEquiv (CommRingCat.ofHom (algebraMap ↥R ↥C)) rfl
  exact exists_comp_relativeDifferentialFormsMap_of_comp _ rfl (specTowerComm R A C) a T eC hT
    heC c ψ hψ

end SpecTower

end Stacks.AlgebraicGeometry.AffineDifferentialForms

end
