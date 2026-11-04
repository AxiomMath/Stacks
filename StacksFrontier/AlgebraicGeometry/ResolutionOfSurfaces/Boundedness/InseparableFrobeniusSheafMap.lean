module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpTrace

/-!
# The `p`-th power map `π_* 𝒪_Y ⟶ 𝒪_X` of a purely inseparable finite morphism

Let `π : Y ⟶ X` be a finite surjective morphism of integral schemes with `X` normal, whose
function fields `K ⊆ L` have characteristic `p` and satisfy `Lᵖ ⊆ K`. Then `s ↦ sᵖ` carries
sections of `π_* 𝒪_Y` to sections of `𝒪_X`: the germ of `sᵖ` lies in `K` and is integral over
every local ring of `X` at a point of the open, which is integrally closed. The result is a
morphism of the underlying sheaves of abelian groups `π_* 𝒪_Y ⟶ 𝒪_X`; it is `p`-linear, not
linear, which is why it is a morphism of abelian sheaves.

This is the first map of the factorization `c = R ∘ Θ ∘ P` of the Frobenius route to
[Stacks, Tag 0B4U]: since it factors through `𝒪_X`, and `H¹(X, 𝒪_X) = 0` when `X` is a normal
modification of the spectrum of a regular local ring of dimension two ([Stacks, Tag 0B4Q]), it
kills `H¹(X, π_* 𝒪_Y) = H¹(Y, 𝒪_Y)`.

## Main definitions

* `AlgebraicGeometry.SeparableGoUp.frobeniusApp`: the value of `s ↦ sᵖ` on sections over `U`.
* `AlgebraicGeometry.SeparableGoUp.frobeniusHom`: the morphism of underlying abelian sheaves
  `π_* 𝒪_Y ⟶ 𝒪_X`.

## Main results

* `AlgebraicGeometry.SeparableGoUp.germ_frobeniusApp`: on germs at the generic point it is the
  `p`-th power.
* `AlgebraicGeometry.SeparableGoUp.frobeniusApp_mul`: `(π^♯ r · s)ᵖ = rᵖ sᵖ`.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SeparableGoUp

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (p : ℕ) [Fact p.Prime]
  [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π] [IsNormal X]
  [CharP X.functionField p]
  (hpow : ∀ y : Y.functionField, ∃ k : X.functionField, dominantFunctionFieldMap π k = y ^ p)

include hpow in
omit [Fact p.Prime] [CharP X.functionField p] in
/-- **The `p`-th power of a section of `π_* 𝒪_Y` over `U` is a section of `𝒪_X` over `U`.** -/
theorem exists_frobenius_section (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) :
    ∃ t : Γ(X, U), ∀ hU : genericPoint X ∈ U,
      dominantFunctionFieldMap π (X.presheaf.germ U (genericPoint X) hU t) =
        germY π U hU s ^ p := by
  let := functionFieldAlgebra π
  by_cases hU : genericPoint X ∈ U
  · have : Nonempty U := ⟨⟨_, hU⟩⟩
    obtain ⟨k, hk⟩ := hpow (germY π U hU s)
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range X U k fun x => by
      have : IsIntegrallyClosed (X.presheaf.stalk x.1) := IsNormal.stalk_normal x.1
      refine IsIntegrallyClosed.isIntegral_iff.mp ?_
      let : Algebra (X.presheaf.stalk x.1) Y.functionField :=
        ((dominantFunctionFieldMap π).comp
          (algebraMap (X.presheaf.stalk x.1) X.functionField)).toAlgebra
      have hy : _root_.IsIntegral (X.presheaf.stalk x.1) (germY π U hU s) := by
        obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open x.2 U.isOpen
        have : Nonempty V := ⟨⟨x.1, hxV⟩⟩
        have hηV : genericPoint X ∈ V := Stacks.Divisors.genericPoint_mem_of_nonempty V
        have hηV' := genericPoint_mem_preimage π V hηV
        let A := Γ(X, V)
        let B := Γ(Y, π ⁻¹ᵁ V)
        let : Algebra A B := (π.app V).hom.toAlgebra
        have : Module.Finite A B := π.finite_app V hV
        let : Algebra A Y.functionField :=
          ((dominantFunctionFieldMap π).comp (X.germToFunctionField V).hom).toAlgebra
        have : IsScalarTower A X.functionField Y.functionField :=
          IsScalarTower.of_algebraMap_eq' rfl
        have hpre : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U := fun _ h => hVU h
        let sV : B := Y.presheaf.map (homOfLE hpre).op s
        let g : B →ₐ[A] Y.functionField :=
          { toRingHom := (Y.presheaf.germ (π ⁻¹ᵁ V) (genericPoint Y) hηV').hom
            commutes' := fun a => (dominantFunctionFieldMap_germ π V hηV a).symm }
        have hg : g sV = germY π U hU s := by
          change Y.presheaf.germ (π ⁻¹ᵁ V) (genericPoint Y) hηV'
            (Y.presheaf.map (homOfLE hpre).op s) = _
          rw [Y.presheaf.germ_res_apply]
        have h1 : _root_.IsIntegral A (germY π U hU s) :=
          hg ▸ (IsIntegral.of_finite A sV).map g
        let : Algebra A (X.presheaf.stalk x.1) :=
          TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x.1, hxV⟩ : V)
        have : IsScalarTower A (X.presheaf.stalk x.1) X.functionField :=
          functionField_isScalarTower X V ⟨x.1, hxV⟩
        have : IsScalarTower A (X.presheaf.stalk x.1) Y.functionField :=
          IsScalarTower.of_algebraMap_eq' (by
            ext a
            change _ = dominantFunctionFieldMap π (algebraMap _ X.functionField
              (algebraMap A (X.presheaf.stalk x.1) a))
            rw [← IsScalarTower.algebraMap_apply]
            rfl)
        exact h1.tower_top
      have hyp : _root_.IsIntegral (X.presheaf.stalk x.1) (germY π U hU s ^ p) := hy.pow p
      have : IsScalarTower (X.presheaf.stalk x.1) X.functionField Y.functionField :=
        IsScalarTower.of_algebraMap_eq' rfl
      rw [← hk] at hyp
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (X.presheaf.stalk x.1)
        X.functionField Y.functionField) (dominantFunctionFieldMap π).injective).mp hyp
    refine ⟨a, fun hU' => ?_⟩
    rw [← hk, ← ha]
  · exact ⟨0, fun h => absurd h hU⟩

/-- The value of `s ↦ sᵖ` on sections over `U`. -/
def frobeniusApp (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) : Γ(X, U) :=
  (exists_frobenius_section π p hpow U s).choose

omit [Fact p.Prime] [CharP X.functionField p] in
/-- On germs at the generic point, `frobeniusApp` is the `p`-th power. -/
theorem germ_frobeniusApp (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(Y, π ⁻¹ᵁ U)) :
    dominantFunctionFieldMap π (X.presheaf.germ U (genericPoint X) hU
      (frobeniusApp π p hpow U s)) = germY π U hU s ^ p :=
  (exists_frobenius_section π p hpow U s).choose_spec hU

omit [IsFinite π] [IsNormal X] in
/-- Sections of `𝒪_X` are determined by the images of their generic germs in `L`. -/
theorem sections_ext_of_map {U : X.Opens} (t t' : Γ(X, U))
    (h : ∀ hU : genericPoint X ∈ U,
      dominantFunctionFieldMap π (X.presheaf.germ U (genericPoint X) hU t) =
        dominantFunctionFieldMap π (X.presheaf.germ U (genericPoint X) hU t')) : t = t' :=
  sections_ext t t' fun hU => (dominantFunctionFieldMap π).injective (h hU)

/-- `s ↦ sᵖ` is additive: `(s + t)ᵖ = sᵖ + tᵖ`. -/
theorem frobeniusApp_add (U : X.Opens) (s t : Γ(Y, π ⁻¹ᵁ U)) :
    frobeniusApp π p hpow U (s + t) = frobeniusApp π p hpow U s + frobeniusApp π p hpow U t := by
  let := functionFieldAlgebra π
  have : CharP Y.functionField p :=
    charP_of_injective_algebraMap (dominantFunctionFieldMap π).injective p
  refine sections_ext_of_map π _ _ fun hU => ?_
  rw [map_add, map_add, germ_frobeniusApp, germ_frobeniusApp, germ_frobeniusApp, germY,
    map_add, add_pow_char]

omit [CharP X.functionField p] in
/-- `s ↦ sᵖ` sends `0` to `0`. -/
theorem frobeniusApp_zero (U : X.Opens) : frobeniusApp π p hpow U 0 = 0 := by
  refine sections_ext_of_map π _ _ fun hU => ?_
  rw [germ_frobeniusApp, germY, map_zero, map_zero, map_zero,
    zero_pow (Fact.out : p.Prime).ne_zero]

omit [Fact p.Prime] [CharP X.functionField p] in
/-- `s ↦ sᵖ` is `p`-linear: `(π^♯ r · s)ᵖ = rᵖ sᵖ`. -/
theorem frobeniusApp_mul (U : X.Opens) (r : Γ(X, U)) (s : Γ(Y, π ⁻¹ᵁ U)) :
    frobeniusApp π p hpow U (π.app U r * s) = r ^ p * frobeniusApp π p hpow U s := by
  refine sections_ext_of_map π _ _ fun hU => ?_
  rw [germ_frobeniusApp, map_mul, map_mul, map_pow, germ_frobeniusApp, germY, map_mul,
    ← dominantFunctionFieldMap_germ π U hU r, mul_pow, map_pow]

omit [Fact p.Prime] [CharP X.functionField p] in
/-- `s ↦ sᵖ` commutes with restriction of sections along `V ⟶ U`. -/
theorem frobeniusApp_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(Y, π ⁻¹ᵁ U)) :
    frobeniusApp π p hpow V (Y.presheaf.map ((Opens.map π.base).map i).op s) =
      X.presheaf.map i.op (frobeniusApp π p hpow U s) := by
  refine sections_ext_of_map π _ _ fun hV => ?_
  have hU : genericPoint X ∈ U := i.le hV
  rw [germ_frobeniusApp, X.presheaf.germ_res_apply, germ_frobeniusApp π p hpow U hU, germY, germY,
    Y.presheaf.germ_res_apply]

/-- `s ↦ sᵖ` as an additive map on sections over `U`. -/
def frobeniusAddHom (U : X.Opens) : Γ(Y, π ⁻¹ᵁ U) →+ Γ(X, U) where
  toFun := frobeniusApp π p hpow U
  map_zero' := frobeniusApp_zero π p hpow U
  map_add' := frobeniusApp_add π p hpow U

/-- **The `p`-th power map `π_* 𝒪_Y ⟶ 𝒪_X`** as a morphism of the underlying sheaves of abelian
groups. -/
def frobeniusHom :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj
        ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)) ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨{ app U := AddCommGrpCat.ofHom (frobeniusAddHom π p hpow U.unop)
     naturality {U V} i := by
       ext s
       exact frobeniusApp_res π p hpow i.unop s }⟩

/-- The component of `frobeniusHom` over `U` is `frobeniusApp`. -/
@[simp] theorem frobeniusHom_app (U : X.Opens) (s : Γ(Y, π ⁻¹ᵁ U)) :
    (frobeniusHom π p hpow).hom.app (op U) s = frobeniusApp π p hpow U s := rfl

end AlgebraicGeometry.SeparableGoUp

end
