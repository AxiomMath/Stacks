module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.OpenCurvePicardRestriction
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass

/-!
# The divisor of an invertible function on an open subcurve

Let `S ⊆ C` be a nonempty open subscheme of a curve `C`. An invertible function `u` on `S` is a
rational function on `C`, and its divisor `div(u)` on the closed points of `C` is supported on
`C ∖ S`. If `div(u) = 0` and `C` is normal, `u` is the restriction of an invertible global
function (algebraic Hartogs). For an automorphism `σ` of `C` restricting to an automorphism of
`S` and fixing the points of `C ∖ S`, `div(σ^* u) = div(u)`: the order of vanishing is invariant
under transport along an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.openUnitDivisor`: `u ↦ div(u)`.
* `Stacks.EtaleCohomology.boundaryUnitDivisor`: the orders of vanishing of `u` at the points of
  `C ∖ S`.

## Main results

* `Stacks.EtaleCohomology.openUnitDivisor_apply_eq_zero_of_mem_range`: `div(u)` vanishes on `S`.
* `Stacks.EtaleCohomology.exists_units_map_appTop_eq_of_openUnitDivisor_eq_zero`: units with
  trivial divisor are global.
* `Stacks.EtaleCohomology.openUnitDivisor_units_map_appTop`: invariance under an automorphism
  fixing the points at infinity.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Order

universe u

namespace Stacks.EtaleCohomology

variable {C S : Scheme.{u}} (j : S ⟶ C) [IsOpenImmersion j] [IsIntegral C] [IsIntegral S]
  [IsLocallyNoetherian C] [IsLocallyNoetherian S] [NoetherianSpace C]

attribute [local instance] AlgebraicGeometry.isDominant_of_isOpenImmersion_of_isIntegral

/-- **An invertible function on `S` as a rational function on `C`.** -/
def openUnitRationalFunction : Γ(S, ⊤)ˣ →* C.functionFieldˣ :=
  haveI : Nonempty (⊤ : S.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  Units.map ((Stacks.Chow.functionFieldEquiv_openImmersion j).symm.toRingHom.comp
    (S.germToFunctionField ⊤).hom).toMonoidHom

omit [IsLocallyNoetherian C] [IsLocallyNoetherian S] [NoetherianSpace C] in
/-- The image of `openUnitRationalFunction j u` under the function field map of `j` is the germ
of `u` in the function field of `S`. -/
theorem dominantFunctionFieldMap_openUnitRationalFunction (u : Γ(S, ⊤)ˣ) :
    haveI : Nonempty (⊤ : S.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    dominantFunctionFieldMap j (openUnitRationalFunction j u : C.functionField) =
      (S.germToFunctionField ⊤).hom (u : Γ(S, ⊤)) := by
  rw [← Stacks.Chow.functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap]
  exact RingEquiv.apply_symm_apply _ _

/-- The function field map of a dominant morphism sends the germ of a global section to the germ
of its pullback. -/
private theorem dominantFunctionFieldMap_germToFunctionField_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [Nonempty (⊤ : X.Opens)]
    [Nonempty (⊤ : Y.Opens)] (s : Γ(Y, ⊤)) :
    dominantFunctionFieldMap f ((Y.germToFunctionField ⊤).hom s) =
      (X.germToFunctionField ⊤).hom (f.appTop.hom s) := by
  obtain ⟨y⟩ : Nonempty X := inferInstance
  have h2 : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f (U := ⊤)
  have h3 := dominantFunctionFieldMap_germToFunctionField_of_mem f y ⊤ trivial ⊤ trivial le_top s
  rwa [h2] at h3

/-- **The divisor of an invertible function on an open subcurve**, on the closed points of the
curve. -/
def openUnitDivisor : Additive Γ(S, ⊤)ˣ →+ (closedPoints C →₀ ℤ) :=
  (closedPointDivisorOfUnit C).comp (openUnitRationalFunction j).toAdditive

omit [IsLocallyNoetherian S] in
/-- The coefficient of `div(u)` at a closed point `b` is the order of vanishing of `u` at `b`. -/
theorem openUnitDivisor_apply (u : Γ(S, ⊤)ˣ) (b : closedPoints C) :
    openUnitDivisor j (Additive.ofMul u) b =
      C.ord (openUnitRationalFunction j u : C.functionField) b.1 := rfl

omit [NoetherianSpace C] in
/-- **`div(u)` vanishes at the points of `S`.** -/
theorem ord_openUnitRationalFunction_base (u : Γ(S, ⊤)ˣ) (y : S) :
    C.ord (openUnitRationalFunction j u : C.functionField) (j.base y) = 0 := by
  have : Nonempty (⊤ : S.Opens) := ⟨⟨y, trivial⟩⟩
  rw [← Stacks.Chow.ord_dominantFunctionFieldMap_of_isPreimmersion j,
    dominantFunctionFieldMap_openUnitRationalFunction]
  exact Scheme.ord_of_isUnit u.isUnit trivial

/-- The coefficient of `div(u)` at a closed point of `C` lying in `S` is zero. -/
theorem openUnitDivisor_apply_eq_zero_of_mem_range (u : Γ(S, ⊤)ˣ) (b : closedPoints C)
    (hb : b.1 ∈ Set.range j.base) : openUnitDivisor j (Additive.ofMul u) b = 0 := by
  obtain ⟨y, hy⟩ := hb
  rw [openUnitDivisor_apply, ← hy, ord_openUnitRationalFunction_base]

/-- **Invertible functions on `S` with trivial divisor are restrictions of invertible global
functions** of the normal curve `C` (algebraic Hartogs). -/
theorem exists_units_map_appTop_eq_of_openUnitDivisor_eq_zero {K : Type u} [Field K]
    (g : C ⟶ Spec (.of K)) [IsCurve K g] [IsNormal C] (u : Γ(S, ⊤)ˣ)
    (hu : openUnitDivisor j (Additive.ofMul u) = 0) :
    ∃ s : Γ(C, ⊤)ˣ, Units.map j.appTop.hom.toMonoidHom s = u := by
  have : Nonempty (⊤ : S.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  have hord : ∀ y : C, coheight y = 1 →
      C.ord (openUnitRationalFunction j u : C.functionField) y = 0 := by
    intro y hy
    by_cases hyr : y ∈ Set.range j.base
    · obtain ⟨y', rfl⟩ := hyr
      exact ord_openUnitRationalFunction_base j u y'
    · have h := DFunLike.congr_fun hu ⟨y, isClosed_singleton_of_coheight_eq_one g hy⟩
      rwa [openUnitDivisor_apply] at h
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero
      (X := C) (openUnitRationalFunction j u) hord
  refine ⟨s, Units.ext (Scheme.germToFunctionField_injective S ⊤ ?_)⟩
  rw [Units.coe_map, ← dominantFunctionFieldMap_openUnitRationalFunction (j := j), ← hs]
  have hη : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
  exact (dominantFunctionFieldMap_germToFunctionField_top j (s : Γ(C, ⊤))).symm

/-- **The divisor of an invertible function on `S` is invariant under an automorphism of `C`
that restricts to `S` and fixes the points of `C ∖ S`.** -/
theorem openUnitDivisor_units_map_appTop (σ : C ⟶ C) (σS : S ⟶ S) [IsIso σ] [IsIso σS]
    (hcomm : σS ≫ j = j ≫ σ)
    (hfix : ∀ b : closedPoints C, b.1 ∉ Set.range j.base → σ.base b.1 = b.1) (u : Γ(S, ⊤)ˣ) :
    openUnitDivisor j (Additive.ofMul (Units.map σS.appTop.hom.toMonoidHom u)) =
      openUnitDivisor j (Additive.ofMul u) := by
  have : Nonempty (⊤ : S.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  ext b
  by_cases hb : b.1 ∈ Set.range j.base
  · rw [openUnitDivisor_apply_eq_zero_of_mem_range j _ b hb,
      openUnitDivisor_apply_eq_zero_of_mem_range j _ b hb]
  have hf : (openUnitRationalFunction j (Units.map σS.appTop.hom.toMonoidHom u) :
      C.functionField) = dominantFunctionFieldMap σ (openUnitRationalFunction j u) := by
    apply (Stacks.Chow.functionFieldEquiv_openImmersion j).injective
    have hc : dominantFunctionFieldMap (j ≫ σ) = dominantFunctionFieldMap (σS ≫ j) := by
      congr 1
      exact hcomm.symm
    rw [Stacks.Chow.functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap,
      Stacks.Chow.functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap,
      dominantFunctionFieldMap_openUnitRationalFunction, ← RingHom.comp_apply,
      ← Stacks.Chow.dominantFunctionFieldMap_comp, hc,
      Stacks.Chow.dominantFunctionFieldMap_comp, RingHom.comp_apply,
      dominantFunctionFieldMap_openUnitRationalFunction, Units.coe_map]
    exact (dominantFunctionFieldMap_germToFunctionField_top σS (u : Γ(S, ⊤))).symm
  rw [openUnitDivisor_apply, openUnitDivisor_apply, hf,
    Stacks.Chow.ord_dominantFunctionFieldMap_of_isPreimmersion σ, hfix b hb]

/-- **The divisor at infinity** of an invertible function on `S`: its orders of vanishing at the
closed points of `C ∖ S`. -/
def boundaryUnitDivisor :
    Additive Γ(S, ⊤)ˣ →+ ({b : closedPoints C // b.1 ∉ Set.range j.base} → ℤ) :=
  Pi.addMonoidHom fun b => (Finsupp.applyAddHom b.1).comp (openUnitDivisor j)

/-- An invertible function on `S` whose divisor at infinity vanishes has trivial divisor. -/
theorem openUnitDivisor_eq_zero_of_boundaryUnitDivisor_eq_zero (x : Additive Γ(S, ⊤)ˣ)
    (hx : boundaryUnitDivisor j x = 0) : openUnitDivisor j x = 0 := by
  ext b
  by_cases hb : b.1 ∈ Set.range j.base
  · exact openUnitDivisor_apply_eq_zero_of_mem_range j _ b hb
  · exact congrFun hx ⟨b, hb⟩

/-- The divisor at infinity of an invertible function on `S` is invariant under an automorphism
of `C` that restricts to `S` and fixes the points of `C ∖ S`. -/
theorem boundaryUnitDivisor_units_map_appTop (σ : C ⟶ C) (σS : S ⟶ S) [IsIso σ] [IsIso σS]
    (hcomm : σS ≫ j = j ≫ σ)
    (hfix : ∀ b : closedPoints C, b.1 ∉ Set.range j.base → σ.base b.1 = b.1) (u : Γ(S, ⊤)ˣ) :
    boundaryUnitDivisor j (Additive.ofMul (Units.map σS.appTop.hom.toMonoidHom u)) =
      boundaryUnitDivisor j (Additive.ofMul u) := by
  funext b
  show openUnitDivisor j _ b.1 = openUnitDivisor j _ b.1
  rw [openUnitDivisor_units_map_appTop j σ σS hcomm hfix u]

end Stacks.EtaleCohomology
