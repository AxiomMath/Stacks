module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalizationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpTraceIdentity

/-!
# The finite case of [Stacks, Tag 0AXL]

Let `A → B` be a finite map of domains with `A` normal, let `f : X ⟶ Spec A` and
`g : Y ⟶ Spec B` be birational with `X` normal and `X, Y` integral, and let `π : Y ⟶ X` be a
finite surjective morphism over `Spec B ⟶ Spec A`. Given the trace identity
`d σ = ∑ⱼ Trace(bⱼ σ) eⱼ` of `Stacks.Trace.exists_traceIdentity`, the length of `H¹(Y, 𝒪_Y)` over
`A` is at most `n · length_A H¹(X, 𝒪_X)` plus the length of its `d`-torsion.

This is the case "`Y` finite over a modification `X` of `Spec A`" to which the source's proof
of [Stacks, Tag 0AXL] reduces.

## Main definitions

* `AlgebraicGeometry.SeparableGoUp.baseFunctionFieldAlgebra`: the function field of a scheme
  over `Spec R` as an `R`-algebra.

## Main results

* `AlgebraicGeometry.SeparableGoUp.isFractionRing_of_isBirational`: the function field of an
  integral scheme birational over `Spec R` is a fraction field of `R`.
* `AlgebraicGeometry.SeparableGoUp.length_firstCohomology_le_of_isFinite`: the bound above.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SeparableGoUp

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The function field of a scheme over `Spec R`, as an `R`-algebra: `r` goes to the germ at the
generic point of its image among the global functions. -/
abbrev baseFunctionFieldAlgebra [IrreducibleSpace X] : Algebra R X.functionField :=
  ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom).toAlgebra

/-- Under `baseFunctionFieldAlgebra f`, the image of `r : R` in the function field of `X` is the
germ at the generic point of the global section `baseSection X f r`. -/
theorem baseFunctionFieldAlgebra_algebraMap [IrreducibleSpace X] (r : R) :
    letI := baseFunctionFieldAlgebra f
    algebraMap R X.functionField r = X.presheaf.germ ⊤ (genericPoint X) trivial
      (baseSection X f r) := rfl

/-- **The function field of an integral scheme birational over `Spec R` is a fraction field of
`R`.** The function field map of the birational morphism is an isomorphism onto the function
field of `Spec R`, which is the fraction field of `R`. -/
theorem isFractionRing_of_isBirational' {R : CommRingCat.{u}} [IsDomain R] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec R) (hf : IsBirational f) :
    letI : Algebra R X.functionField := ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom).toAlgebra
    IsFractionRing R X.functionField := by
  let : Algebra R X.functionField := ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom).toAlgebra
  have : IsDominant f := hf.isDominant
  have hψ : ∀ r : R, dominantFunctionFieldMap f (algebraMap R (Spec R).functionField r) =
      algebraMap R X.functionField r := fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact dominantFunctionFieldMap_germ f ⊤ trivial ((Scheme.ΓSpecIso R).inv r)
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R)
    { RingEquiv.ofBijective (dominantFunctionFieldMap f)
        (Stacks.Chow.bijective_dominantFunctionFieldMap_of_isBirational f hf) with
      commutes' := hψ : (Spec R).functionField ≃ₐ[R] X.functionField }

/-- **The function field of an integral scheme birational over `Spec R` is a fraction field of
`R`**, for the algebra structure `baseFunctionFieldAlgebra`. -/
theorem isFractionRing_of_isBirational [IsDomain R] [IsIntegral X] (hf : IsBirational f) :
    letI := baseFunctionFieldAlgebra f
    IsFractionRing R X.functionField := by
  have : IsDomain (CommRingCat.of R) := ‹IsDomain R›
  exact isFractionRing_of_isBirational' (R := CommRingCat.of R) f hf

/-! ### The finite case -/

/-- Linearly equivalent modules have torsion submodules of the same length. -/
theorem length_torsionBy_eq_of_linearEquiv {S M N : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (E : M ≃ₗ[S] N) (d : S) :
    Module.length S (Submodule.torsionBy S M d) = Module.length S (Submodule.torsionBy S N d) :=
  LinearEquiv.length_eq (E.ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_torsionBy_iff, Submodule.mem_torsionBy_iff,
      ← map_smul, map_eq_zero_iff _ E.symm.injective]))

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The map `A ⟶ Γ(Y, 𝒪_Y)` through `Spec B` is the map through `X`, for a commutative square
`π ≫ f = g ≫ Spec(A → B)`. -/
theorem baseSection_comp {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A)) (g : Y ⟶ Spec (.of B))
    (π : Y ⟶ X) (hcomm : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (a : A) :
    baseSection Y (π ≫ f) a = baseSection Y g (algebraMap A B a) := by
  simp only [baseSection, hcomm, Scheme.Hom.comp_appTop]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- `H¹(Y, 𝒪_Y)` over `A` through `X` is `H¹(Y, 𝒪_Y)` over `B`, with scalars restricted. -/
def firstCohomologyRestrictEquiv {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (g : Y ⟶ Spec (.of B)) (π : Y ⟶ X)
    (hcomm : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (firstCohomologyAsBaseModule Y g) ≃ₗ[A]
      firstCohomologyAsBaseModule Y (π ≫ f) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    let x' : ((Scheme.sectionsFunctor Y).rightDerived 1).obj
        (SheafOfModules.unit Y.ringCatSheaf) := x
    change baseSection Y g (algebraMap A B a) • x' = baseSection Y (π ≫ f) a • x'
    rw [baseSection_comp f g π hcomm]

/-- **The finite case of [Stacks, Tag 0AXL].** Let `A → B` be a finite map of domains with `A`
normal, `f : X ⟶ Spec A` and `g : Y ⟶ Spec B` birational with `X` normal, and `π : Y ⟶ X` finite
surjective over `Spec B ⟶ Spec A`. If `b, e : Fin n → B` and `d ∈ A` satisfy the trace identity
`d σ = ∑ⱼ Trace(bⱼ σ) eⱼ` in every pair of fraction fields, then over `A`
`length H¹(Y, 𝒪_Y) ≤ n · length H¹(X, 𝒪_X) + length H¹(Y, 𝒪_Y)[d]`. -/
theorem length_firstCohomology_le_of_isFinite [IsDomain A] [IsDomain B] {n : ℕ}
    (b e : Fin n → B) (d : A)
    (hid : ∀ (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
        [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
        [IsScalarTower A B L] (σ : L),
        algebraMap A L d * σ =
          ∑ j, algebraMap K L (Algebra.trace K L (algebraMap B L (b j) * σ)) *
            algebraMap B L (e j))
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A)) (g : Y ⟶ Spec (.of B)) (π : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y] [IsNormal X] [IsFinite π] [Surjective π]
    (hf : IsBirational f) (hg : IsBirational g)
    (hcomm : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) :
    Module.length A ((ModuleCat.restrictScalars (algebraMap A B)).obj
        (firstCohomologyAsBaseModule Y g)) ≤
      n * Module.length A (firstCohomologyAsBaseModule X f) +
        Module.length A (Submodule.torsionBy A ((ModuleCat.restrictScalars
          (algebraMap A B)).obj (firstCohomologyAsBaseModule Y g)) d) := by
  let E := firstCohomologyRestrictEquiv f g π hcomm
  let : Algebra A X.functionField := baseFunctionFieldAlgebra f
  let : Algebra B Y.functionField := baseFunctionFieldAlgebra g
  let : Algebra X.functionField Y.functionField := functionFieldAlgebra π
  let : Algebra A Y.functionField :=
    ((algebraMap B Y.functionField).comp (algebraMap A B)).toAlgebra
  have : IsFractionRing A X.functionField := isFractionRing_of_isBirational f hf
  have : IsFractionRing B Y.functionField := isFractionRing_of_isBirational g hg
  have : IsScalarTower A B Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A X.functionField Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    change Y.presheaf.germ ⊤ (genericPoint Y) trivial (baseSection Y g (algebraMap A B a)) =
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f a))
    rw [← baseSection_comp f g π hcomm]
    exact (dominantFunctionFieldMap_germ π ⊤ trivial _).symm
  rw [E.length_eq, length_torsionBy_eq_of_linearEquiv E d]
  exact length_firstCohomology_le f π (fun j => baseSection Y g (b j))
    (fun j => baseSection Y g (e j)) d (fun σ => by
      have hd : dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial
          (baseSection X f d)) = algebraMap A Y.functionField d := by
        rw [IsScalarTower.algebraMap_apply A X.functionField Y.functionField]
        rfl
      rw [hd, hid X.functionField Y.functionField σ]
      rfl)

end AlgebraicGeometry.SeparableGoUp

end
