module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Trace.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.GenericStalk
public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a finite morphism onto a normal integral scheme

Let `π : Y ⟶ X` be a finite surjective morphism of integral schemes with `X` normal, and write
`K` and `L` for the function fields of `X` and `Y`. Then `L / K` is a finite extension, and the
field trace `Trace_{L/K}` carries sections of `π_* 𝒪_Y` to sections of `𝒪_X`: a section `s` of
`𝒪_Y` over `π⁻¹ U` is integral over every local ring `𝒪_{X, x}` with `x ∈ U`, hence so is its
trace, which therefore lies in each `𝒪_{X, x}` and so is a section of `𝒪_X` over `U`.

This is the map `Trace : π_* 𝒪_Y ⟶ 𝒪_X` of the source's proof of [Stacks, Tag 0AXL]; it is
built here with a coefficient, `s ↦ Trace(b s)` for a global function `b` of `Y`, which is the
form in which the proof uses it.

## Main definitions

* `AlgebraicGeometry.SeparableGoUp.functionFieldAlgebra`: the extension of function fields of a
  dominant morphism of integral schemes, as an algebra.
* `AlgebraicGeometry.SeparableGoUp.traceHom`: the morphism `π_* 𝒪_Y ⟶ 𝒪_X`,
  `s ↦ Trace_{L/K}(b s)`, of sheaves of `𝒪_X`-modules.
* `AlgebraicGeometry.SeparableGoUp.mulHom`: the morphism `𝒪_X ⟶ π_* 𝒪_Y`, `t ↦ t e`, for a
  global function `e` of `Y`.

## Main results

* `AlgebraicGeometry.SeparableGoUp.finiteDimensional_functionField`: the extension of function
  fields of a finite surjective morphism of integral schemes is finite.
* `AlgebraicGeometry.SeparableGoUp.germ_traceHom_app`: the germ at the generic point of the
  value of `traceHom` is the field trace.
* `AlgebraicGeometry.SeparableGoUp.sum_traceHom_comp_mulHom`: an identity
  `d s = ∑ᵢ Trace(bᵢ s) eᵢ` in the function field of `Y` gives the identity
  `∑ᵢ traceHom bᵢ ≫ mulHom eᵢ = d` of endomorphisms of `π_* 𝒪_Y`.

## Implementation notes

A section of `𝒪_X` over a nonempty open is determined by its germ at the generic point, and
over the empty open there is only one section; every identity below is checked that way. The
value of the trace on an open is chosen from the characterization of `Γ(X, U)` as the
intersection of the local rings at the points of `U` inside the function field,
`AlgebraicGeometry.exists_germToFunctionField_eq_of_forall_mem_range`.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SeparableGoUp

variable {X Y : Scheme.{u}} (π : Y ⟶ X)

/-- The extension of function fields induced by a dominant morphism of integral schemes, as an
algebra. -/
abbrev functionFieldAlgebra [IsIntegral X] [IsIntegral Y] [IsDominant π] :
    Algebra X.functionField Y.functionField :=
  (dominantFunctionFieldMap π).toAlgebra

/-- A dominant morphism of integral schemes sends the generic point to the generic point. -/
theorem map_genericPoint [IsIntegral X] [IsIntegral Y] [IsDominant π] :
    π (genericPoint Y) = genericPoint X :=
  ((tfae_isDominant_of_isIntegral π).out 1 2).mp ‹IsDominant π›

/-- The inverse image of an open containing the generic point contains the generic point. -/
theorem genericPoint_mem_preimage [IsIntegral X] [IsIntegral Y] [IsDominant π] (U : X.Opens)
    (hU : genericPoint X ∈ U) : genericPoint Y ∈ π ⁻¹ᵁ U := by
  change π (genericPoint Y) ∈ U
  rwa [map_genericPoint π]

/-- An open whose inverse image contains the generic point contains the generic point. -/
theorem genericPoint_mem_of_mem_preimage [IsIntegral X] [IsIntegral Y] [IsDominant π]
    (U : X.Opens) (hU : genericPoint Y ∈ π ⁻¹ᵁ U) : genericPoint X ∈ U := by
  rwa [← map_genericPoint π]

/-- The function field map sends the germ of a section to the germ of its pullback. -/
theorem dominantFunctionFieldMap_germ [IsIntegral X] [IsIntegral Y] [IsDominant π]
    (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    dominantFunctionFieldMap π (X.presheaf.germ U (genericPoint X) hU s) =
      Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) (genericPoint_mem_preimage π U hU)
        (π.app U s) := by
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, genericPoint_mem_preimage π U hU⟩⟩
  have h := dominantFunctionFieldMap_germToFunctionField_of_mem π (genericPoint Y) U
    (genericPoint_mem_preimage π U hU) (π ⁻¹ᵁ U) (genericPoint_mem_preimage π U hU) le_rfl s
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- Two sections of the structure sheaf of an integral scheme with the same germ at the generic
point are equal; over the empty open there is nothing to check. -/
theorem sections_ext [IsIntegral X] {U : X.Opens} (s t : Γ(X, U))
    (h : ∀ hU : genericPoint X ∈ U,
      X.presheaf.germ U (genericPoint X) hU s = X.presheaf.germ U (genericPoint X) hU t) :
    s = t := by
  by_cases hU : genericPoint X ∈ U
  · exact germ_injective_of_isIntegral X (genericPoint X) hU (h hU)
  · obtain rfl : U = ⊥ := by
      refine SetLike.ext' (Set.eq_empty_iff_forall_notMem.2 fun x hx => hU ?_)
      have : Nonempty U := ⟨⟨x, hx⟩⟩
      exact Stacks.Divisors.genericPoint_mem_of_nonempty U
    exact Subsingleton.elim _ _

/-- **The extension of function fields of a finite surjective morphism of integral schemes is
finite.** Over a nonempty affine open `V` of `X` the ring `Γ(Y, π⁻¹ V)` is a finite
`Γ(X, V)`-algebra, and the two function fields are the fraction fields of these rings. -/
@[sga "1 I 10.1" "partial"]
theorem finiteDimensional_functionField [IsIntegral X] [IsIntegral Y] [IsFinite π]
    [Surjective π] :
    letI := functionFieldAlgebra π
    FiniteDimensional X.functionField Y.functionField := by
  let := functionFieldAlgebra π
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, genericPoint_mem_preimage π U hηU⟩⟩
  let A := Γ(X, U)
  let B := Γ(Y, π ⁻¹ᵁ U)
  have : IsDomain A := IsIntegral.component_integral U
  have : IsDomain B := IsIntegral.component_integral (π ⁻¹ᵁ U)
  let : Algebra A B := (π.app U).hom.toAlgebra
  have : Module.Finite A B := π.finite_app U hU
  have hcompat : ∀ a : A, dominantFunctionFieldMap π (X.germToFunctionField U a) =
      Y.germToFunctionField (π ⁻¹ᵁ U) (π.app U a) :=
    dominantFunctionFieldMap_germ π U hηU
  have hmap : Function.Injective (π.app U).hom := fun a b hab =>
    X.germToFunctionField_injective U <| (dominantFunctionFieldMap π).injective <| by
      rw [hcompat a, hcompat b]
      exact congrArg _ hab
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hmap
  let K := X.functionField
  let L := Y.functionField
  let : Algebra A L := ((dominantFunctionFieldMap π).comp (X.germToFunctionField U).hom).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' (RingHom.ext hcompat)
  have : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsFractionRing B L :=
    functionField_isFractionRing_of_isAffineOpen Y (π ⁻¹ᵁ U) (hU.preimage π)
  apply Module.rank_lt_aleph0_iff.mp
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing A K B L]
  exact Module.rank_lt_aleph0 A B

section Trace

variable [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π]

/-- The germ at the generic point of a section of `𝒪_Y` over `π⁻¹ U`. -/
abbrev germY (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(Y, π ⁻¹ᵁ U)) : Y.functionField :=
  Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) (genericPoint_mem_preimage π U hU) s

/-- **The trace of a section of `π_* 𝒪_Y` is integral over the local rings of `X`.** A section
`s` of `𝒪_Y` over `π⁻¹ U` restricts, over an affine open `V ⊆ U` containing `x`, to an element
of the finite `Γ(X, V)`-algebra `Γ(Y, π⁻¹ V)`; so its germ is integral over `Γ(X, V)`, hence so
is its trace, and hence the trace is integral over `𝒪_{X, x}`. -/
theorem isIntegral_trace_germY (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(Y, π ⁻¹ᵁ U))
    (x : X) (hx : x ∈ U) :
    letI := functionFieldAlgebra π
    _root_.IsIntegral (X.presheaf.stalk x)
      (Algebra.trace X.functionField Y.functionField (germY π U hU s)) := by
  let := functionFieldAlgebra π
  have := finiteDimensional_functionField π
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hηV : genericPoint X ∈ V := Stacks.Divisors.genericPoint_mem_of_nonempty V
  let A := Γ(X, V)
  let B := Γ(Y, π ⁻¹ᵁ V)
  let : Algebra A B := (π.app V).hom.toAlgebra
  have : Module.Finite A B := π.finite_app V hV
  let K := X.functionField
  let L := Y.functionField
  let : Algebra A L :=
    ((dominantFunctionFieldMap π).comp (X.germToFunctionField V).hom).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  have hpre : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U := fun _ h => hVU h
  let sV : B := Y.presheaf.map (homOfLE hpre).op s
  let g : B →ₐ[A] L :=
    { toRingHom := (Y.presheaf.germ (π ⁻¹ᵁ V) (genericPoint Y)
        (genericPoint_mem_preimage π V hηV)).hom
      commutes' := fun a => (dominantFunctionFieldMap_germ π V hηV a).symm }
  have hg : g sV = germY π U hU s := Y.presheaf.germ_res_apply _ _ _ _
  have h1 : _root_.IsIntegral A (germY π U hU s) := hg ▸ (IsIntegral.of_finite A sV).map g
  have h2 : _root_.IsIntegral A (Algebra.trace K L (germY π U hU s)) := Algebra.isIntegral_trace h1
  let : Algebra A (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have : IsScalarTower A (X.presheaf.stalk x) K :=
    functionField_isScalarTower X V ⟨x, hxV⟩
  exact h2.tower_top

variable [IsNormal X]

/-- **The trace of a section of `π_* 𝒪_Y` over `U` is a section of `𝒪_X` over `U`.** -/
theorem exists_trace_section (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) :
    letI := functionFieldAlgebra π
    ∃ t : Γ(X, U), ∀ hU : genericPoint X ∈ U,
      X.presheaf.germ U (genericPoint X) hU t =
        Algebra.trace X.functionField Y.functionField (germY π U hU s) := by
  let := functionFieldAlgebra π
  by_cases hU : genericPoint X ∈ U
  · have : Nonempty U := ⟨⟨_, hU⟩⟩
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range X U
      (Algebra.trace X.functionField Y.functionField (germY π U hU s)) fun x => by
        have : IsIntegrallyClosed (X.presheaf.stalk x.1) := IsNormal.stalk_normal x.1
        exact IsIntegrallyClosed.isIntegral_iff.mp
          (isIntegral_trace_germY π U hU s x.1 x.2)
    exact ⟨a, fun _ => ha⟩
  · exact ⟨0, fun h => absurd h hU⟩

/-- The value of the trace on sections over `U`. -/
def traceApp (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) : Γ(X, U) :=
  (exists_trace_section π U s).choose

/-- The germ of the value of the trace is the field trace of the germ. -/
theorem germ_traceApp (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(Y, π ⁻¹ᵁ U)) :
    letI := functionFieldAlgebra π
    X.presheaf.germ U (genericPoint X) hU (traceApp π U s) =
      Algebra.trace X.functionField Y.functionField (germY π U hU s) :=
  (exists_trace_section π U s).choose_spec hU

/-- The value of the trace on sections is additive. -/
theorem traceApp_add (U : X.Opens) (s t : Γ(Y, π ⁻¹ᵁ U)) :
    traceApp π U (s + t) = traceApp π U s + traceApp π U t := by
  let := functionFieldAlgebra π
  refine sections_ext _ _ fun hU => ?_
  rw [map_add, germ_traceApp, germ_traceApp, germ_traceApp, germY, map_add, map_add]

/-- The value of the trace on sections is `Γ(X, U)`-linear. -/
theorem traceApp_mul (U : X.Opens) (r : Γ(X, U)) (s : Γ(Y, π ⁻¹ᵁ U)) :
    traceApp π U (π.app U r * s) = r * traceApp π U s := by
  let := functionFieldAlgebra π
  refine sections_ext _ _ fun hU => ?_
  rw [map_mul, germ_traceApp, germ_traceApp, germY, map_mul,
    ← dominantFunctionFieldMap_germ π U hU r]
  change Algebra.trace X.functionField Y.functionField
    ((X.presheaf.germ U (genericPoint X) hU r) • germY π U hU s) = _
  rw [map_smul, smul_eq_mul]

/-- The value of the trace on sections commutes with restriction. -/
theorem traceApp_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(Y, π ⁻¹ᵁ U)) :
    traceApp π V (Y.presheaf.map ((Opens.map π.base).map i).op s) =
      X.presheaf.map i.op (traceApp π U s) := by
  let := functionFieldAlgebra π
  refine sections_ext _ _ fun hV => ?_
  rw [germ_traceApp, X.presheaf.germ_res_apply, germ_traceApp π U (i.le hV), germY, germY,
    Y.presheaf.germ_res_apply]

/-- The trace as an additive map on the sections over an open. -/
def traceAddHom (U : X.Opens) : Γ(Y, π ⁻¹ᵁ U) →+ Γ(X, U) where
  toFun := traceApp π U
  map_zero' := by
    let := functionFieldAlgebra π
    refine sections_ext _ _ fun hU => ?_
    rw [germ_traceApp, germY, map_zero, map_zero, map_zero]
  map_add' := traceApp_add π U

/-- **The trace `π_* 𝒪_Y ⟶ 𝒪_X`** of a finite surjective morphism of integral schemes onto a
normal scheme: on sections over `U` it is the field trace `Trace_{R(Y)/R(X)}`, which carries
`Γ(Y, π⁻¹ U)` into `Γ(X, U)`. -/
def traceHom : (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (traceAddHom π U.unop)
      naturality {U V} i := by
        ext s
        exact traceApp_res π i.unop s }
    (fun U r m => traceApp_mul π U.unop r m)⟩

/-- The trace on sections over `U`. -/
@[simp] theorem traceHom_app (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) :
    (traceHom π).app U s = traceApp π U s := rfl

end Trace

section Multiplication

variable [IsIntegral X] [IsIntegral Y] [IsDominant π]

/-- The restriction of a global function to an open. -/
abbrev resTop (Z : Scheme.{u}) (V : Z.Opens) (e : Γ(Z, ⊤)) : Γ(Z, V) :=
  Z.presheaf.map (homOfLE le_top).op e

/-- The germ at the generic point of a restricted global function is its global germ. -/
theorem germ_resTop (Z : Scheme.{u}) (V : Z.Opens) (e : Γ(Z, ⊤)) (x : Z) (hx : x ∈ V) :
    Z.presheaf.germ V x hx (resTop Z V e) = Z.presheaf.germ ⊤ x trivial e :=
  Z.presheaf.germ_res_apply _ _ _ _

/-- Sections of `𝒪_Y` over an open of `Y` with the same germ at the generic point are equal. -/
theorem sections_ext_Y {V : Y.Opens} (s t : Γ(Y, V))
    (h : ∀ hV : genericPoint Y ∈ V,
      Y.presheaf.germ V (genericPoint Y) hV s = Y.presheaf.germ V (genericPoint Y) hV t) :
    s = t :=
  sections_ext (X := Y) s t h

/-- The values of `𝒪_X ⟶ π_* 𝒪_Y`, `t ↦ t e`. -/
def mulApp (e : Γ(Y, ⊤)) (U : X.Opens) (t : Γ(X, U)) : Γ(Y, π ⁻¹ᵁ U) :=
  π.app U t * resTop Y (π ⁻¹ᵁ U) e

/-- The values of `π_* 𝒪_Y ⟶ π_* 𝒪_Y`, `s ↦ b s`. -/
def pushMulApp (b : Γ(Y, ⊤)) (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) : Γ(Y, π ⁻¹ᵁ U) :=
  resTop Y (π ⁻¹ᵁ U) b * s

/-- The germ of a pullback is the image of the germ under the function field map, for any
open of `X` containing the generic point (the inverse image then contains that of `Y`). -/
theorem germ_app (U : X.Opens) (hU : genericPoint X ∈ U) (t : Γ(X, U))
    (hV : genericPoint Y ∈ π ⁻¹ᵁ U) :
    Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hV (π.app U t) =
      dominantFunctionFieldMap π (X.presheaf.germ U (genericPoint X) hU t) :=
  (dominantFunctionFieldMap_germ π U hU t).symm

/-- `t ↦ t e` commutes with restriction along an inclusion of opens of `X`. -/
theorem mulApp_res (e : Γ(Y, ⊤)) {U V : X.Opens} (i : V ⟶ U) (t : Γ(X, U)) :
    mulApp π e V (X.presheaf.map i.op t) =
      Y.presheaf.map ((Opens.map π.base).map i).op (mulApp π e U t) := by
  refine sections_ext_Y _ _ fun hV => ?_
  have hXV := genericPoint_mem_of_mem_preimage π V hV
  rw [Y.presheaf.germ_res_apply, mulApp, mulApp, map_mul, map_mul, germ_resTop, germ_resTop,
    germ_app π V hXV, germ_app π U (i.le hXV), X.presheaf.germ_res_apply]

omit [IsIntegral X] [IsDominant π] in
/-- `s ↦ b s` commutes with restriction along an inclusion of opens of `X`. -/
theorem pushMulApp_res (b : Γ(Y, ⊤)) {U V : X.Opens} (i : V ⟶ U) (s : Γ(Y, π ⁻¹ᵁ U)) :
    pushMulApp π b V (Y.presheaf.map ((Opens.map π.base).map i).op s) =
      Y.presheaf.map ((Opens.map π.base).map i).op (pushMulApp π b U s) := by
  refine sections_ext_Y _ _ fun hV => ?_
  rw [Y.presheaf.germ_res_apply, pushMulApp, pushMulApp, map_mul, map_mul, germ_resTop,
    germ_resTop, Y.presheaf.germ_res_apply]

omit [IsIntegral X] [IsIntegral Y] [IsDominant π] in
/-- `t ↦ t e` is linear over the sections of `𝒪_X`. -/
theorem mulApp_mul (e : Γ(Y, ⊤)) (U : X.Opens) (r t : Γ(X, U)) :
    mulApp π e U (r * t) = π.app U r * mulApp π e U t := by
  rw [mulApp, mulApp, map_mul, mul_assoc]

omit [IsIntegral X] [IsIntegral Y] [IsDominant π] in
/-- `s ↦ b s` is linear over the sections of `𝒪_X`. -/
theorem pushMulApp_mul (b : Γ(Y, ⊤)) (U : X.Opens) (r : Γ(X, U)) (s : Γ(Y, π ⁻¹ᵁ U)) :
    pushMulApp π b U (π.app U r * s) = π.app U r * pushMulApp π b U s := by
  rw [pushMulApp, pushMulApp, mul_left_comm]

/-- The additive map `t ↦ t e` on sections over an open. -/
def mulAddHom (e : Γ(Y, ⊤)) (U : X.Opens) : Γ(X, U) →+ Γ(Y, π ⁻¹ᵁ U) where
  toFun := mulApp π e U
  map_zero' := by simp [mulApp]
  map_add' a c := by simp [mulApp, add_mul]

/-- The additive map `s ↦ b s` on sections over an open. -/
def pushMulAddHom (b : Γ(Y, ⊤)) (U : X.Opens) : Γ(Y, π ⁻¹ᵁ U) →+ Γ(Y, π ⁻¹ᵁ U) where
  toFun := pushMulApp π b U
  map_zero' := by simp [pushMulApp]
  map_add' a c := by simp [pushMulApp, mul_add]

/-- **Multiplication by a global function of `Y`, `𝒪_X ⟶ π_* 𝒪_Y`, `t ↦ t e`.** -/
def mulHom (e : Γ(Y, ⊤)) : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
    (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (mulAddHom π e U.unop)
      naturality {U V} i := by
        ext t
        exact mulApp_res π e i.unop t }
    (fun U r m => mulApp_mul π e U.unop r m)⟩

/-- **Multiplication by a global function of `Y` on `π_* 𝒪_Y`.** -/
def pushMulHom (b : Γ(Y, ⊤)) :
    (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (pushMulAddHom π b U.unop)
      naturality {U V} i := by
        ext t
        exact pushMulApp_res π b i.unop t }
    (fun U r m => pushMulApp_mul π b U.unop r m)⟩

/-- On sections over `U`, `mulHom π e` sends `t` to `t e`. -/
@[simp] theorem mulHom_app (e : Γ(Y, ⊤)) (U : X.Opens) (t : Γ(X, U)) :
    Scheme.Modules.Hom.app (mulHom π e) U t = π.app U t * resTop Y (π ⁻¹ᵁ U) e := rfl

omit [IsIntegral X] [IsDominant π] in
/-- On sections over `U`, `pushMulHom π b` sends `s` to `b s`. -/
@[simp] theorem pushMulHom_app (b : Γ(Y, ⊤)) (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) :
    Scheme.Modules.Hom.app (pushMulHom π b) U s = resTop Y (π ⁻¹ᵁ U) b * s := rfl

end Multiplication

section Identity

variable [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π] [IsNormal X]

omit [IsIntegral X] [IsNormal X] in
/-- The value on sections of a finite sum of morphisms of `𝒪_X`-modules is the sum of the values.
-/
theorem sum_app {M N : X.Modules} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (U : X.Opens)
    (x : Γ(M, U)) :
    Scheme.Modules.Hom.app (∑ i ∈ s, f i) U x = ∑ i ∈ s, Scheme.Modules.Hom.app (f i) U x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app,
      AddCommGrpCat.hom_add_apply, ih]

/-- **The trace identity on `π_* 𝒪_Y`.** If global functions `bᵢ, eᵢ` of `Y` and `d` of `X`
satisfy `d σ = ∑ᵢ Trace(bᵢ σ) eᵢ` for every `σ` in the function field of `Y`, then
`∑ᵢ (s ↦ bᵢ s) ≫ Trace ≫ (t ↦ t eᵢ)` is multiplication by `d` on `π_* 𝒪_Y`. -/
theorem sum_traceHom_comp_mulHom {n : ℕ} (b e : Fin n → Γ(Y, ⊤)) (d : Γ(X, ⊤))
    (h : letI := functionFieldAlgebra π
      ∀ σ : Y.functionField,
        dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial d) * σ =
          ∑ i, dominantFunctionFieldMap π (Algebra.trace X.functionField Y.functionField
            (Y.presheaf.germ ⊤ (genericPoint Y) trivial (b i) * σ)) *
              Y.presheaf.germ ⊤ (genericPoint Y) trivial (e i)) :
    ∑ i, pushMulHom π (b i) ≫ traceHom π ≫ mulHom π (e i) =
      (Scheme.smulEnd X d).app ((Scheme.Modules.pushforward π).obj
        (SheafOfModules.unit Y.ringCatSheaf)) := by
  let := functionFieldAlgebra π
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s₀
  rw [sum_app]
  let s : Γ(Y, π ⁻¹ᵁ U) := s₀
  change ∑ i, π.app U (traceApp π U (resTop Y (π ⁻¹ᵁ U) (b i) * s)) *
      resTop Y (π ⁻¹ᵁ U) (e i) = π.app U (resTop X U d) * s
  refine sections_ext_Y _ _ fun hV => ?_
  have hU := genericPoint_mem_of_mem_preimage π U hV
  simp only [map_sum, map_mul, germ_app π U hU, germ_traceApp π U hU, germ_resTop, germY]
  exact (h _).symm

end Identity

end AlgebraicGeometry.SeparableGoUp

end
