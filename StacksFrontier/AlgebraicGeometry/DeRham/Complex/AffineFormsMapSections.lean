module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.QuasicoherentNatural
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison

/-!
# The canonical map on differential forms of an affine morphism, on global sections

Let `R`, `A`, `C` be commutative rings with `A` an `R`-algebra and `C` an `A`-algebra, and
consider the commutative square of affine schemes

```
Spec C --f--> Spec A
  |             |
  p'            p
  v             v
Spec R ====== Spec R
```

with `f = Spec (A ⟶ C)` and identity bottom edge. This file identifies the global sections of the
canonical map on relative differential `a`-forms of that square with the `a`-th exterior power of
`KaehlerDifferential.mapBaseChange R A C`.

The identification is read through two comparisons. On the target it is the global-sections
comparison `Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso` of Tag 01I8, which turns
`Γ(Spec C, Ω^a_{Spec C/Spec R})` into `⋀^a_C Γ(Spec C, Ω_{Spec C/Spec R})`. On the source it is
the same comparison preceded by the pullback comparison of Tag 01CI, which turns
`Γ(Spec C, f^*Ω^a_{Spec A/Spec R})` into `⋀^a_C Γ(Spec C, f^*Ω_{Spec A/Spec R})`; that composite
is `formsPullbackΓIso` below. Both comparisons are isomorphisms with no further hypothesis.

What is left after those two comparisons is the degree-one dictionary: the global sections of the
canonical map of Tag 01UV, read through comparisons of
`Γ(Spec C, f^*Ω_{Spec A/Spec R})` with `C ⊗[A] Ω[A⁄R]` and of
`Γ(Spec C, Ω_{Spec C/Spec R})` with `Ω[C⁄R]`, are `KaehlerDifferential.mapBaseChange R A C`.
Those two comparisons are parameters, taken as `C`-linear maps pinned by their values on
universal differentials.

## Main definitions

* `pullbackFormsIso`: the comparison of Tag 01CI in degree `n` for the exterior algebra of
  relative differentials, `f^*Ω^n_{X/S} ≅ ⋀^n(f^*Ω_{X/S})`, i.e. the first factor of
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`.
* `formsPullbackΓIso`: the resulting comparison
  `Γ(Spec C, f^*Ω^a_{X/S}) ≅ ⋀^a_C Γ(Spec C, f^*Ω_{X/S})` on global sections.

## Main results

* `relativeDifferentialsMap_Γ_comp_eq_mapBaseChange`: the global sections of the canonical map
  of Tag 01UV, precomposed with a comparison of `C ⊗[A] Ω[A⁄R]` with
  `Γ(Spec C, f^*Ω_{Spec A/Spec R})`, are `KaehlerDifferential.mapBaseChange R A C` postcomposed
  with a comparison of `Ω[C⁄R]` with `Γ(Spec C, Ω_{Spec C/Spec R})`.
* `relativeDifferentialFormsMap_Γ_conj_eq_exteriorPower_map`: conjugating the global sections of
  the canonical map on `a`-forms by the two comparisons gives `exteriorPower.map a` of the
  global sections of the canonical map on relative differentials.
* `relativeDifferentialFormsMap_Γ_comp_eq_exteriorPower_map_mapBaseChange`: the global sections
  of the canonical map on `a`-forms, read through the two comparisons, are
  `exteriorPower.map a (KaehlerDifferential.mapBaseChange R A C)`.

## References

* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AffineExteriorPower (quasicoherentExteriorPowerΓIso)
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialForms

/-! ### Quasi-coherence of the modules involved -/

/-- The sheaf of relative differentials of a morphism of schemes is quasi-coherent. -/
instance isQuasicoherent_relativeDifferentials {X S : Scheme.{u}} (p : X ⟶ S) :
    (Scheme.Hom.relativeDifferentials p).IsQuasicoherent :=
  Scheme.Hom.isQuasicoherent_relativeDifferentials p

/-- The inverse image of the sheaf of relative differentials is quasi-coherent. -/
instance isQuasicoherent_pullback_relativeDifferentials {X' X S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) :
    ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f _

/-! ### A cancellation in an arbitrary category -/

/-- An isomorphism in the middle of a four-fold composite cancels:
`(u ≫ e.inv) ≫ (e.hom ≫ d) ≫ v = u ≫ d ≫ v`. -/
theorem comp_inv_hom_cancel {D : Type*} [Category D] {W X Y Z₁ Z₂ : D} (u : W ⟶ X) (e : Y ≅ X)
    (d : X ⟶ Z₁) (v : Z₁ ⟶ Z₂) :
    (u ≫ e.inv) ≫ (e.hom ≫ d) ≫ v = u ≫ d ≫ v := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

/-! ### The comparison of Tag 01CI for differential forms -/

/-- **The comparison of Stacks Tag 01CI in degree `n` for relative differential forms.** For
`f : X' ⟶ X` and `p : X ⟶ S` this is the isomorphism `f^*Ω^n_{X/S} ≅ ⋀^n(f^*Ω_{X/S})` obtained
from `Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso`: it is the first of the two
factors of `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`. -/
def pullbackFormsIso {X' X S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (n : ℤ) :
    (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms p n) ≅
      Scheme.Modules.exteriorPower
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)) n :=
  (Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso f.toLRSHom.toShHom
    (Scheme.Hom.relativeDifferentialFormsAlgebra p)
    (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p))
    (Scheme.Modules.exteriorAlgebra
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)))
    (Scheme.Modules.exteriorGenerator
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (Scheme.Hom.relativeDifferentials p))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)).app n

/-- The canonical map `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` on `n`-forms is
the comparison of Tag 01CI followed by the degree-`n` component of the canonical homomorphism of
exterior algebras. -/
theorem relativeDifferentialFormsMap_eq_pullbackFormsIso_comp {X' X S' S : Scheme.{u}}
    (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    Scheme.Hom.relativeDifferentialFormsMap f p p' g hcomm n =
      (pullbackFormsIso f p n).hom ≫
        (Scheme.Hom.relativeDifferentialFormsComparison f p p' g hcomm).app n :=
  rfl

/-- **The comparison of the global sections of `f^*Ω^a_{X/S}` with an exterior power.** For
`f : Spec C ⟶ Spec A` and `p : Spec A ⟶ S` this is the composite of the comparison of Tag 01CI
with the global-sections comparison of Tag 01I8:

`Γ(Spec C, f^*Ω^a_{X/S}) ≅ ⋀^a_C Γ(Spec C, f^*Ω_{X/S})`. -/
def formsPullbackΓIso {A C : CommRingCat.{u}} {S : Scheme.{u}} (f : Spec C ⟶ Spec A)
    (p : Spec A ⟶ S) (a : ℕ) :
    moduleSpecΓFunctor.obj
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms p (a : ℤ))) ≅
      ModuleCat.of ↥C (⋀[↥C]^a ↥(moduleSpecΓFunctor.obj
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p)))) :=
  moduleSpecΓFunctor.mapIso (pullbackFormsIso f p (a : ℤ)) ≪≫
    quasicoherentExteriorPowerΓIso
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p))
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) a

/-! ### The degree-one dictionary over the rings themselves -/

section PullbackSection

variable {R A C : CommRingCat.{u}} [Algebra ↥A ↥C] {p : Spec A ⟶ Spec R}
  {p' : Spec C ⟶ Spec R}

/-- **The map on global sections of the structure sheaves induced by `Spec` of a ring map,
read through `AlgebraicGeometry.Scheme.ΓSpecIso`.** For `f = Spec (A ⟶ C)` the map
`Γ(Spec A, ⊤) ⟶ Γ(Spec C, ⊤)` carries the image of `a : A` to the image of its image in `C`. -/
theorem specMap_appLE_ΓSpecIso_inv (f : Spec C ⟶ Spec A)
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C))) (a : ↥A) :
    (f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso A).inv.hom a) =
      (Scheme.ΓSpecIso C).inv.hom (algebraMap ↥A ↥C a) := by
  have htop : f.appLE ⊤ ⊤ le_top = f.appTop := (Scheme.Hom.app_eq_appLE f).symm
  rw [htop, hf]
  have happ := congrArg (fun k : A ⟶ Γ(Spec C, ⊤) => k.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ↥A ↥C)))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at happ
  exact happ.symm

variable (f : Spec C ⟶ Spec A) (hf : f = Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C)))
  (hcomm : f ≫ p = p' ≫ 𝟙 (Spec R))

include hf hcomm in
/-- **The canonical map of Tag 01UV on a pulled-back universal differential.** It carries the
pullback of the universal relative differential of the image of `a : A` to the universal
relative differential of the image of `a` in `C`. -/
theorem relativeDifferentialsMap_Γ_pullbackSection (a : ↥A) :
    (moduleSpecΓFunctor.map
          (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 (Spec R)) hcomm)).hom
        (pullbackSectionHom f (Scheme.Hom.relativeDifferentials p) ⊤ ⊤ le_top
          ((Scheme.Hom.universalRelativeDerivation p).d ((Scheme.ΓSpecIso A).inv.hom a))) =
      (Scheme.Hom.universalRelativeDerivation p').d
        ((Scheme.ΓSpecIso C).inv.hom (algebraMap ↥A ↥C a)) :=
  (Scheme.Hom.relativeDifferentialsMap_pullbackSection f p p' (𝟙 (Spec R)) hcomm ⊤ ⊤ le_top
      ((Scheme.ΓSpecIso A).inv.hom a)).trans
    (congrArg (fun z => (Scheme.Hom.universalRelativeDerivation p').d z)
      (specMap_appLE_ΓSpecIso_inv f hf a))

end PullbackSection

section DegreeOne

variable {R A C : CommRingCat.{u}} [Algebra ↥R ↥A] [Algebra ↥A ↥C] [Algebra ↥R ↥C]
  [IsScalarTower ↥R ↥A ↥C] {p : Spec A ⟶ Spec R} {p' : Spec C ⟶ Spec R}
  (f : Spec C ⟶ Spec A) (hf : f = Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C)))
  (hcomm : f ≫ p = p' ≫ 𝟙 (Spec R))
  (T : ↥C ⊗[↥A] Ω[↥A⁄↥R] →ₗ[↥C]
    ↥(moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p))))
  (E : Ω[↥C⁄↥R] →ₗ[↥C] ↥(moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials p')))
  (hT : ∀ a : ↥A, T ((1 : ↥C) ⊗ₜ KaehlerDifferential.D ↥R ↥A a) =
    pullbackSectionHom f (Scheme.Hom.relativeDifferentials p) ⊤ ⊤ le_top
      ((Scheme.Hom.universalRelativeDerivation p).d ((Scheme.ΓSpecIso A).inv.hom a)))
  (hE : ∀ c : ↥C, E (KaehlerDifferential.D ↥R ↥C c) =
    (Scheme.Hom.universalRelativeDerivation p').d ((Scheme.ΓSpecIso C).inv.hom c))

/-- A pure tensor `c ⊗ x` in `C ⊗[A] M` is `c • (1 ⊗ x)`. -/
private theorem tmul_eq_smul_one_tmul {A C M : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup M] [Module A M] (c : C) (x : M) : c ⊗ₜ[A] x = c • ((1 : C) ⊗ₜ[A] x) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hf hcomm hT hE in
/-- The global sections of the canonical map of Tag 01UV, read through `T` on the source and `E`
on the target, agree with `KaehlerDifferential.mapBaseChange R A C` on a pure tensor `1 ⊗ x`. -/
theorem relativeDifferentialsMap_Γ_one_tmul (x : Ω[↥A⁄↥R]) :
    (moduleSpecΓFunctor.map
          (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 (Spec R)) hcomm)).hom
        (T ((1 : ↥C) ⊗ₜ x)) =
      E (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C ((1 : ↥C) ⊗ₜ x)) := by
  have hx : x ∈ Submodule.span ↥A (Set.range (KaehlerDifferential.D ↥R ↥A)) :=
    KaehlerDifferential.span_range_derivation ↥R ↥A ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [hT a, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul, hE]
      exact relativeDifferentialsMap_Γ_pullbackSection f hf hcomm a
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add y z _ _ ihy ihz => simp only [TensorProduct.tmul_add, map_add, ihy, ihz]
  | smul a y _ ihy =>
      have hsmul : (1 : ↥C) ⊗ₜ[↥A] (a • y) =
          algebraMap ↥A ↥C a • ((1 : ↥C) ⊗ₜ[↥A] y) := by
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, tmul_eq_smul_one_tmul]
      simp only [hsmul, map_smul, ihy]

include hf hcomm hT hE in
/-- **The degree-one dictionary, on an element.** The global sections of the canonical map of
Tag 01UV, read through `T` on the source and `E` on the target, are
`KaehlerDifferential.mapBaseChange R A C`. -/
theorem relativeDifferentialsMap_Γ_apply_eq_mapBaseChange (t : ↥C ⊗[↥A] Ω[↥A⁄↥R]) :
    (moduleSpecΓFunctor.map
          (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 (Spec R)) hcomm)).hom (T t) =
      E (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
      simp only [tmul_eq_smul_one_tmul c x, map_smul,
        relativeDifferentialsMap_Γ_one_tmul f hf hcomm T E hT hE]
  | add t₁ t₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

include hf hcomm hT hE in
/-- **The degree-one square.** Let

```
Spec C --f--> Spec A
  |             |
  p'            p
  v             v
Spec R ====== Spec R
```

be a commutative square with `f = Spec (A ⟶ C)` and identity bottom edge, let `T` be a
`C`-linear map from `C ⊗[A] Ω[A⁄R]` to the global sections of `f^*Ω_{Spec A/Spec R}` carrying
`1 ⊗ d a` to the pullback of the universal differential of `a`, and let `E` be a `C`-linear map
from `Ω[C⁄R]` to the global sections of `Ω_{Spec C/Spec R}` carrying `d c` to the universal
differential of `c`. Then the square

`C ⊗[A] Ω[A⁄R] → Γ(f^*Ω_{Spec A/Spec R}) → Γ(Ω_{Spec C/Spec R})`
`= C ⊗[A] Ω[A⁄R] → Ω[C⁄R] → Γ(Ω_{Spec C/Spec R})`

commutes, the right-hand bottom edge being `KaehlerDifferential.mapBaseChange R A C`. -/
theorem relativeDifferentialsMap_Γ_comp_eq_mapBaseChange :
    (moduleSpecΓFunctor.map
          (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 (Spec R)) hcomm)).hom ∘ₗ T =
      E ∘ₗ KaehlerDifferential.mapBaseChange ↥R ↥A ↥C :=
  LinearMap.ext (relativeDifferentialsMap_Γ_apply_eq_mapBaseChange f hf hcomm T E hT hE)

end DegreeOne

/-! ### The canonical map on `a`-forms, on global sections -/

section Forms

variable {R A C : CommRingCat.{u}} {p : Spec A ⟶ Spec R} {p' : Spec C ⟶ Spec R}
  (f : Spec C ⟶ Spec A) (hcomm : f ≫ p = p' ≫ 𝟙 (Spec R)) (a : ℕ)

include hcomm in
/-- Conjugating the global sections of the canonical map on `a`-forms by the two comparisons
gives `exteriorPower.map a` of the canonical map on relative differentials. -/
theorem relativeDifferentialFormsMap_Γ_conj_eq_exteriorPower_map :
    (formsPullbackΓIso f p a).inv ≫
        moduleSpecΓFunctor.map
            (Scheme.Hom.relativeDifferentialFormsMap f p p' (𝟙 (Spec R)) hcomm (a : ℤ)) ≫
          (quasicoherentExteriorPowerΓIso (Scheme.Hom.relativeDifferentials p')
            (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) a).hom =
      ModuleCat.ofHom (exteriorPower.map a
        (moduleSpecΓFunctor.map
          (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 (Spec R)) hcomm)).hom) := by
  have hmap : moduleSpecΓFunctor.map
        (Scheme.Hom.relativeDifferentialFormsMap f p p' (𝟙 (Spec R)) hcomm (a : ℤ)) =
      moduleSpecΓFunctor.map (pullbackFormsIso f p (a : ℤ)).hom ≫
        moduleSpecΓFunctor.map
          ((Scheme.Hom.relativeDifferentialFormsComparison f p p' (𝟙 (Spec R)) hcomm).app
            (a : ℤ)) :=
    CategoryTheory.Functor.map_comp _ _ _
  have hstep := congrArg
    (fun z => (formsPullbackΓIso f p a).inv ≫ z ≫
      (quasicoherentExteriorPowerΓIso (Scheme.Hom.relativeDifferentials p')
        (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) a).hom) hmap
  refine hstep.trans ((comp_inv_hom_cancel
    (quasicoherentExteriorPowerΓIso
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p))
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) a).inv
    (moduleSpecΓFunctor.mapIso (pullbackFormsIso f p (a : ℤ)))
    (moduleSpecΓFunctor.map
      ((Scheme.Hom.relativeDifferentialFormsComparison f p p' (𝟙 (Spec R)) hcomm).app (a : ℤ)))
    (quasicoherentExteriorPowerΓIso (Scheme.Hom.relativeDifferentials p')
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) a).hom).trans
    (Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_conj_desc
      (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 (Spec R)) hcomm)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) _ a))

variable [Algebra ↥R ↥A] [Algebra ↥A ↥C] [Algebra ↥R ↥C] [IsScalarTower ↥R ↥A ↥C]
  (hf : f = Spec.map (CommRingCat.ofHom (algebraMap ↥A ↥C)))
  (T : ↥C ⊗[↥A] Ω[↥A⁄↥R] →ₗ[↥C]
    ↥(moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials p))))
  (E : Ω[↥C⁄↥R] →ₗ[↥C] ↥(moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials p')))
  (hT : ∀ b : ↥A, T ((1 : ↥C) ⊗ₜ KaehlerDifferential.D ↥R ↥A b) =
    pullbackSectionHom f (Scheme.Hom.relativeDifferentials p) ⊤ ⊤ le_top
      ((Scheme.Hom.universalRelativeDerivation p).d ((Scheme.ΓSpecIso A).inv.hom b)))
  (hE : ∀ c : ↥C, E (KaehlerDifferential.D ↥R ↥C c) =
    (Scheme.Hom.universalRelativeDerivation p').d ((Scheme.ΓSpecIso C).inv.hom c))

include hf hcomm hT hE in
/-- **The canonical map on differential `a`-forms of an affine morphism over an affine base is,
on global sections, the `a`-th exterior power of `KaehlerDifferential.mapBaseChange`.** Let

```
Spec C --f--> Spec A
  |             |
  p'            p
  v             v
Spec R ====== Spec R
```

be a commutative square with `f = Spec (A ⟶ C)` and identity bottom edge, and let `T` and `E` be
the two degree-one comparisons of `relativeDifferentialsMap_Γ_comp_eq_mapBaseChange`. Then the
square

`⋀^a_C (C ⊗[A] Ω[A⁄R]) → ⋀^a_C Γ(f^*Ω_{Spec A/Spec R}) → Γ(f^*Ω^a) → Γ(Ω^a) → ⋀^a_C Γ(Ω)`
`= ⋀^a_C (C ⊗[A] Ω[A⁄R]) → ⋀^a_C Ω[C⁄R] → ⋀^a_C Γ(Ω_{Spec C/Spec R})`

commutes, the bottom-left edge being `exteriorPower.map a (mapBaseChange R A C)`: this is the
assertion that, modulo the comparisons `formsPullbackΓIso` and
`Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso`, the global sections of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` are
`exteriorPower.map a (KaehlerDifferential.mapBaseChange R A C)`. -/
theorem relativeDifferentialFormsMap_Γ_comp_eq_exteriorPower_map_mapBaseChange :
    (quasicoherentExteriorPowerΓIso (Scheme.Hom.relativeDifferentials p')
            (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) a).hom.hom ∘ₗ
        (moduleSpecΓFunctor.map
            (Scheme.Hom.relativeDifferentialFormsMap f p p' (𝟙 (Spec R)) hcomm (a : ℤ))).hom ∘ₗ
          (formsPullbackΓIso f p a).inv.hom ∘ₗ exteriorPower.map a T =
      exteriorPower.map a E ∘ₗ
        exteriorPower.map a (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C) := by
  have hconj := congrArg ModuleCat.Hom.hom
    (relativeDifferentialFormsMap_Γ_conj_eq_exteriorPower_map f hcomm a)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] at hconj
  refine LinearMap.ext fun ω => ?_
  have hdeg : exteriorPower.map a
        (moduleSpecΓFunctor.map
          (Scheme.Hom.relativeDifferentialsMap f p p' (𝟙 (Spec R)) hcomm)).hom
          (exteriorPower.map a T ω) =
      exteriorPower.map a E
        (exteriorPower.map a (KaehlerDifferential.mapBaseChange ↥R ↥A ↥C) ω) := by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
      relativeDifferentialsMap_Γ_comp_eq_mapBaseChange f hf hcomm T E hT hE,
      exteriorPower.map_comp, LinearMap.comp_apply]
  exact (LinearMap.congr_fun hconj (exteriorPower.map a T ω)).trans hdeg

end Forms

end Stacks.AlgebraicGeometry.AffineDifferentialForms

end
