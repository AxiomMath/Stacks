module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistCompatible
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistUnit

/-!
# The logarithmic differential of a unit on the punctured line bundle

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle. For an invertible function `u` on
the inverse image of an open `U` of `X` the **logarithmic differential**

`d log u = u⁻¹ d u`

is a relative one-form on `π⁻¹U`, read here as a section of the pushforward
`(L^⋆ → X)_* Ω^1_{L^⋆/S}` over `U`. It is additive in `u`, so the map `u ↦ d log u` is a
homomorphism from the unit group of the functions on `π⁻¹U` to the one-forms.

The point of the construction is the case where `u` is the homogeneous function of a local
generator `s` of `L`: the proof of [Stacks, Tag 0FUF] constructs the residue
`Res : Ω^•_{L^⋆/S, 0} ⟶ Ω^•_{X/S}[-1]` over an open trivializing `L` by declaring that `1` and
`d log s` freely generate `Ω^•_{L^⋆/S, 0}` as a right module over `Ω^•_{X/S}`, and then shows
that the resulting map does not depend on the choice of `s` because two choices differ by a unit
of `𝒪_X(U)`, whose logarithmic differential is pulled back from `X`.

Both halves of that are proved here at the sheaf level and for an arbitrary invertible module:
`d log s` is a *homogeneous one-form of degree zero*, hence a section of `Ω^1_{L^⋆/S, 0}`, and
for two trivializations over the same open the two logarithmic differentials differ by the
logarithmic differential of a homogeneous function of degree zero — a function pulled back from
`X`.

## Main definitions

* `Stacks.LineBundle.Situation.laurentDlog`: **the logarithmic differential `d log u = u⁻¹ d u`**
  of an invertible function on the inverse image of an open of `X`.
* `Stacks.LineBundle.Situation.laurentTrivUnit`: **the invertible function of a trivialization**
  of `L` over an open of `X`: the homogeneous function of degree one attached to the degree-one
  generator, whose inverse is the homogeneous function of degree `-1`.

## Main results

* `Stacks.LineBundle.Situation.laurentDlog_mul`: **`d log (u v) = d log u + d log v`**, together
  with `Situation.laurentDlog_one` and `Situation.laurentDlog_inv`.
* `Stacks.LineBundle.Situation.laurentDlog_map`: the logarithmic differential commutes with
  restriction to a smaller open of `X`.
* `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_laurentDlog_trivUnit` and
  `Situation.laurentDlog_trivUnit_mem_gradedLaurentForms`: **`d log s` is a homogeneous one-form
  of degree zero, hence a section of `Ω^1_{L^⋆/S, 0}`** over a trivializing affine open. This is
  the assertion of the proof of Tag 0FUF that `d log s` "is an element of
  `Ω^1_{L^⋆/S, 0}(U)`".
* `Stacks.LineBundle.Situation.exists_laurentFunctionOfOpen_trivUnit_mul_inv`: the quotient of
  the invertible functions of two trivializations over the same open is a homogeneous function of
  degree zero.
* `Stacks.LineBundle.Situation.laurentDlog_trivUnit_change`: **the change-of-trivialization rule
  `d log s' = d log g + d log s`**, with `g` the degree-zero homogeneous function above. This is
  the well-definedness input the gluing of the residue needs; it is the sheaf-level counterpart
  of `LaurentDeRham.residue_eq_residueOfUnit` of
  `StacksFrontier.RingTheory.DeRham.LaurentResidueTrivialization`, which states the corresponding
  independence for the affine chart.

## Implementation notes

The logarithmic differential is written with `Situation.gradedSmul` and `Situation.gradedD`, the
`Γ(X, ·)` spellings of multiplication by a function on `π⁻¹U` and of the relative de Rham
differential, so that its value is typed as a section of `Situation.gradedAmbient` — the type the
degree-`n` parts `Situation.gradedLaurentForms` are submodules of. No statement here needs the
differential as a morphism of sheaves, only its Leibniz rule
`Situation.gradedD_mul` on sections, which is why no restriction of scalars to `f^{-1}𝒪_S`
appears: `d log u` is one *section*, not a map.

`Situation.gradedWedge_gradedOne_left` records that the constant form `1` is a left unit for
wedging with a one-form. It is the `one_mul` field of the sheaf of graded algebras
`Situation.laurentFormsAlgebra`, whose heterogeneous equality becomes an equality because the
degree `(0 : ℤ) + 1` of the product is the degree `1` of the one-form on the nose.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF), whose proof constructs
  the residue from `d log s`
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the grading of the de
  Rham complex of a graded algebra
* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), clause (1), which the
  generator family used here was produced for
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.TwistGenerator

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### The constant form `1` is a unit for wedging -/

/-- **The constant form `1` is a left unit for wedging with a one-form.** This is the `one_mul`
field of the sheaf of graded algebras of relative forms of `L^⋆`; the heterogeneous equality
there becomes an equality because the degree `(0 : ℤ) + 1` of the product is the degree `1` of
the one-form on the nose. -/
theorem Situation.gradedWedge_gradedOne_left (U : D.X.Opens) (ξ : Γ(D.gradedAmbient 1, U)) :
    D.gradedWedge 0 U (D.gradedOne U) ξ = ξ :=
  eq_of_heq (D.laurentFormsAlgebra.one_mul 1 (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ξ)

/-! ### The logarithmic differential -/

/-- **The logarithmic differential `d log u = u⁻¹ d u`** of an invertible function on the inverse
image of an open `U` of `X` in `L^⋆`, as a section over `U` of the pushed-forward relative
one-forms. -/
def Situation.laurentDlog (U : D.X.Opens)
    (u : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ) :
    Γ(D.gradedAmbient 1, U) :=
  D.gradedSmul 1 U ((↑u⁻¹ : D.laurentSpectrum.sheaf.obj.obj
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))) (D.gradedD U (↑u))

/-- The logarithmic differential is the inverse of the function times its differential. -/
theorem Situation.laurentDlog_eq (U : D.X.Opens)
    (u : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ) :
    D.laurentDlog U u =
      D.gradedSmul 1 U ((↑u⁻¹ : D.laurentSpectrum.sheaf.obj.obj
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))) (D.gradedD U (↑u)) :=
  rfl

/-- **The logarithmic differential of the constant function `1` vanishes.** -/
theorem Situation.laurentDlog_one (U : D.X.Opens) : D.laurentDlog U 1 = 0 := by
  rw [Situation.laurentDlog, Units.val_one, show D.gradedD U 1 = 0 from D.laurentDifferential_one _]
  exact D.gradedSmul_zero 1 U _

/-- **The logarithmic differential is additive in the function**: `d log (u v) = d log u +
d log v`. The Leibniz rule expands `d (u v)` and the inverse of the product distributes over the
two terms. -/
theorem Situation.laurentDlog_mul (U : D.X.Opens)
    (u v : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ) :
    D.laurentDlog U (u * v) = D.laurentDlog U u + D.laurentDlog U v := by
  have key : ∀ a b : (D.laurentSpectrum.sheaf.obj.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ, (a * b)⁻¹ * a = b⁻¹ := fun a b => by
    rw [mul_inv_rev, inv_mul_cancel_right]
  rw [Situation.laurentDlog, Units.val_mul, D.gradedD_mul U (↑u) (↑v), D.gradedSmul_add,
    ← D.gradedSmul_mul, ← D.gradedSmul_mul, ← Units.val_mul, ← Units.val_mul, key,
    mul_comm u v, key]
  exact add_comm (D.laurentDlog U v) (D.laurentDlog U u)

/-- **The logarithmic differential of an inverse is the negative** of the logarithmic
differential. -/
theorem Situation.laurentDlog_inv (U : D.X.Opens)
    (u : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ) :
    D.laurentDlog U u⁻¹ = -D.laurentDlog U u := by
  rw [eq_neg_iff_add_eq_zero, ← D.laurentDlog_mul U, inv_mul_cancel, D.laurentDlog_one]

/-- **The logarithmic differential commutes with restriction** to a smaller open of `X`. -/
theorem Situation.laurentDlog_map {U W : D.X.Opens} (hWU : W ≤ U)
    (u : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))ˣ) :
    (D.gradedAmbient 1).presheaf.map (homOfLE hWU).op (D.laurentDlog U u) =
      D.laurentDlog W (Units.map
        (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom hWU).op).hom.toMonoidHom u) := by
  rw [Situation.laurentDlog, D.gradedSmul_map 1 hWU, D.gradedD_map hWU]
  rfl

/-! ### The invertible function of a trivialization -/

variable {W : D.X.Opens}
  (e : D.L.over W ≅ SheafOfModules.unit (D.X.ringCatSheaf.over W))

/-- **The invertible function of a trivialization of `L` over an open `W` of `X`**: the
homogeneous function of degree one attached to the degree-one generator of the trivialization,
whose inverse is the homogeneous function of degree `-1` attached to the degree `-1` generator.
It is the function the proof of Tag 0FUF calls `s`, read on `π⁻¹W`. -/
def Situation.laurentTrivUnit :
    (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ W)))ˣ :=
  Units.map (D.laurentFunctionHom W).hom.toMonoidHom (D.laurentGenUnit e)

/-- The invertible function of a trivialization is the homogeneous function of degree one of the
degree-one generator. -/
theorem Situation.laurentTrivUnit_val :
    ((D.laurentTrivUnit e : (D.laurentSpectrum.sheaf.obj.obj
        (op (D.laurentSpectrumToBase ⁻¹ᵁ W)))ˣ) :
        D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ W))) =
      D.laurentFunctionOfOpen 1 W (genOne D.L e) :=
  rfl

/-- The inverse of the invertible function of a trivialization is the homogeneous function of
degree `-1` of the degree `-1` generator. -/
theorem Situation.laurentTrivUnit_inv :
    (((D.laurentTrivUnit e)⁻¹ : (D.laurentSpectrum.sheaf.obj.obj
        (op (D.laurentSpectrumToBase ⁻¹ᵁ W)))ˣ) :
        D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ W))) =
      D.laurentFunctionOfOpen (-1) W (genNegOne D.L e) :=
  rfl

/-! ### `d log s` is a homogeneous one-form of degree zero -/

/-- **`d log s` is a homogeneous one-form of degree zero**, for `s` the invertible function of a
trivialization of `L` over an affine open `U` of `X`. The two factors are homogeneous functions
of degrees `-1` and `1`, so the degree of the product `s⁻¹ d s` is `-1 + 1 = 0`: this is the
assertion of the proof of Tag 0FUF that `d log s` is an element of `Ω^1_{L^⋆/S, 0}(U)`. -/
theorem Situation.isHomogeneousLaurentForm_laurentDlog_trivUnit (U : D.X.affineOpens)
    (eU : D.L.over U.1 ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U.1)) :
    D.IsHomogeneousLaurentForm U 1 0 (D.laurentDlog U.1 (D.laurentTrivUnit eU)) := by
  have h1 : D.IsHomogeneousLaurentForm U 1 1
      (D.gradedWedge 0 U.1 (D.gradedOne U.1)
        (D.gradedD U.1 (D.laurentFunction 1 U (genOne D.L eU)))) :=
    D.isHomogeneousLaurentForm_gradedWedge 0 0 1 1 (zero_add 1) U
      (D.isHomogeneousLaurentForm_gradedOne U) (genOne D.L eU)
  rw [D.gradedWedge_gradedOne_left] at h1
  rw [Situation.laurentDlog, D.laurentTrivUnit_val eU, D.laurentTrivUnit_inv eU,
    D.laurentFunctionOfOpen_affine 1 U (genOne D.L eU),
    D.laurentFunctionOfOpen_affine (-1) U (genNegOne D.L eU)]
  exact D.isHomogeneousLaurentForm_gradedSmul 1 (-1) 1 0 (neg_add_cancel 1) U
    (genNegOne D.L eU) h1

/-- **`d log s` is a section of `Ω^1_{L^⋆/S, 0}`** over a trivializing affine open of `X`. -/
theorem Situation.laurentDlog_trivUnit_mem_gradedLaurentForms (U : D.X.affineOpens)
    (eU : D.L.over U.1 ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U.1)) :
    D.laurentDlog U.1 (D.laurentTrivUnit eU) ∈ (D.gradedLaurentForms 1 0).obj (op U.1) :=
  D.mem_gradedLaurentForms U (D.isHomogeneousLaurentForm_laurentDlog_trivUnit U eU)

/-! ### Independence of the trivialization -/

/-- **The quotient of the invertible functions of two trivializations of `L` over the same open
is a homogeneous function of degree zero**, that is, a function pulled back from `X`: the two
functions have degrees `1` and `-1`, which add to `0`. This is the statement that two choices of
local generator of `L` differ by an invertible function on `X`, read on `π⁻¹W`. -/
theorem Situation.exists_laurentFunctionOfOpen_trivUnit_mul_inv
    (e' : D.L.over W ≅ SheafOfModules.unit (D.X.ringCatSheaf.over W)) :
    ∃ x : (D.laurentAlgebra.piece 0).val.obj (op W),
      ((D.laurentTrivUnit e' * (D.laurentTrivUnit e)⁻¹ :
          (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ W)))ˣ) :
          D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ W))) =
        D.laurentFunctionOfOpen 0 W x :=
  ⟨(D.laurentAlgebra.mul 1 (-1)).app (op W) (genOne D.L e') (genNegOne D.L e),
    D.laurentFunctionOfOpen_mul 1 (-1) W (genOne D.L e') (genNegOne D.L e)⟩

/-- **The change-of-trivialization rule for `d log`**: for two trivializations of `L` over the
same open of `X` the two logarithmic differentials differ by the logarithmic differential of a
homogeneous function of degree zero, that is, of a function pulled back from `X`.

This is the independence the proof of Tag 0FUF needs in order to glue the local residues: it is
the identity `d log (g s) = g⁻¹ d g + d log s` of that proof, with `g` the transition function of
the two trivializations. -/
theorem Situation.laurentDlog_trivUnit_change
    (e' : D.L.over W ≅ SheafOfModules.unit (D.X.ringCatSheaf.over W)) :
    ∃ (g : (D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ W)))ˣ)
      (x : (D.laurentAlgebra.piece 0).val.obj (op W)),
      ((g : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ W))) =
          D.laurentFunctionOfOpen 0 W x) ∧
        D.laurentDlog W (D.laurentTrivUnit e') =
          D.laurentDlog W g + D.laurentDlog W (D.laurentTrivUnit e) := by
  obtain ⟨x, hx⟩ := D.exists_laurentFunctionOfOpen_trivUnit_mul_inv e e'
  refine ⟨D.laurentTrivUnit e' * (D.laurentTrivUnit e)⁻¹, x, hx, ?_⟩
  rw [← D.laurentDlog_mul W, mul_assoc, inv_mul_cancel, mul_one]

end Stacks.LineBundle

end
