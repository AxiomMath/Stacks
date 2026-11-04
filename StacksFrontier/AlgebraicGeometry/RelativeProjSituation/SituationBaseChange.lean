module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartsCartesian

/-!
# The irrelevant ideal and the degree-zero square of a relative `Proj` situation

Let `s` be a relative `Proj` situation with graded algebra `𝒜` on the base `S`, and let `U ≤ V`
be affine opens of `S`. Quasi-coherence of the homogeneous pieces `𝒜ₙ` gives
`𝒜ₙ(U) = Γ(S, U) ⊗_{Γ(S, V)} 𝒜ₙ(V)`. From it, the irrelevant ideal of `𝒜(U)` is covered by that
of `𝒜(V)`, and `Spec (𝒜(U)₀)` is the base change of `Spec (𝒜(V)₀)` along `U ⟶ V`. Consequently
Tag 01NO for `s` follows from the chart condition `Stacks.Proj.IsBaseChangeOnCharts` alone.

## Main definitions

* `Stacks.RelativeProj.Situation.pieceNat` is the homogeneous piece of nonnegative degree `n` as a
  module over the structure sheaf, so that `Γ(s.pieceNat n, U)` is
  `Stacks.RelativeProj.Situation.sectionPieces`.
* `Stacks.RelativeProj.Situation.onePiece` is the unit of the graded algebra over an open.
* `Stacks.RelativeProj.Situation.gradeZeroAlgebra` is the `Γ(S, U)`-algebra structure on `𝒜(U)₀`
  given by the degree-zero identification `Stacks.RelativeProj.Situation.baseHom`.
* `Stacks.RelativeProj.Situation.gradeZeroLinearEquiv`: **the degree-zero summand of the graded
  ring of sections is the sections of `𝒜₀`,** `Γ(S, U)`-linearly.

## Main results

* `Stacks.RelativeProj.Situation.of_smul`: the inclusion of a homogeneous summand turns the action
  of `Γ(S, U)` into multiplication by its image under the degree-zero identification.
* `Stacks.RelativeProj.Situation.irrelevant_le_map`: the irrelevant ideal of `𝒜(U)` is covered by
  that of `𝒜(V)` for affine opens `U ≤ V`.
* `Stacks.RelativeProj.Situation.isPullback_specMap_baseHom` and
  `Stacks.RelativeProj.Situation.chartZero_isPullback`: `Spec (𝒜(U)₀)` is the base change of
  `Spec (𝒜(V)₀)` along `U ⟶ V`.
* `Stacks.RelativeProj.Situation.ChartsCartesian.of_isBaseChangeOnCharts`: Tag 01NO for a
  situation, from the chart condition `Stacks.Proj.IsBaseChangeOnCharts` alone.

## Implementation notes

`Stacks.RelativeProj.Situation.of_smul` is stated with the scalar multiplied on the right.
`DirectSum.of_mul_of` in degrees `(n, 0)` produces a summand in degree `n + 0`, which is
definitionally `n`; in degrees `(0, n)` it produces one in degree `0 + n`, which is not
definitionally `n` for a variable `n`.

The `Γ(S, U)`-algebra structure on `𝒜(U)₀` is an instance here, unlike the restriction-of-scalars
structures used inside the proofs: it depends only on `s` and `U`, both of which appear in its
type, and it is the only such structure on that carrier. The structures that compare two different
opens depend on the inclusion `U ≤ V`, which does not appear in the type of an `Algebra` or
`Module`, so they are local to the proofs that build them.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open HomogeneousIdeal

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-! ### The homogeneous pieces in nonnegative degrees -/

/-- The homogeneous piece of degree `n ≥ 0` of the graded algebra, as a module over the structure
sheaf of the base. Its sections `Γ(s.pieceNat n, U)` are
`Stacks.RelativeProj.Situation.sectionPieces`. -/
public def pieceNat (n : ℕ) : s.base.Modules := s.algebra.piece (n : ℤ)

/-- The homogeneous pieces of nonnegative degree are quasi-coherent. -/
public instance isQuasicoherent_pieceNat (n : ℕ) : (s.pieceNat n).IsQuasicoherent :=
  s.isQuasicoherent n

/-- The unit of the graded algebra, as a degree-zero section over an open. -/
public def onePiece (U : s.base.Opens) : ↥Γ(s.pieceNat 0, U) := s.algebra.one.eval (op U)

/-- The unit is a right identity for the homogeneous multiplication. -/
public theorem mul_onePiece (U : s.base.Opens) (n : ℕ) (a : ↥Γ(s.pieceNat n, U)) :
    (s.algebra.mul (n : ℤ) 0).app (op U) a (s.onePiece U) = a :=
  eq_of_heq (s.algebra.mul_one (n : ℤ) (op U) a)

/-- Multiplying a homogeneous section by a multiple of the unit is the action of the scalar. -/
public theorem gmul_onePiece_smul (U : s.base.Opens) (n : ℕ) (r : ↥Γ(s.base, U))
    (a : ↥Γ(s.pieceNat n, U)) :
    (GradedMonoid.GMul.mul (A := s.sectionPieces U) (i := n) (j := 0) a (r • s.onePiece U)
      : s.sectionPieces U (n + 0)) = r • a := by
  rw [eq_of_heq ((sectionRingStructure s).mul_homogeneous U n 0 a (r • s.onePiece U))]
  rw (transparency := .default) [(s.algebra.mul (n : ℤ) 0).map_smul_right]
  rw [s.mul_onePiece U n a]
  rfl

/-- The degree-zero identification, read inside the section ring: `Γ(S, U) ⟶ 𝒜(U)₀` sends `r` to
the degree-zero summand of `r` times the unit. -/
public theorem coe_baseHom (U : s.base.Opens) (r : ↥Γ(s.base, U)) :
    ((s.baseHom U) r : s.sectionRing U)
      = DirectSum.of (s.sectionPieces U) 0 (r • s.onePiece U) := by
  rw [baseHom_apply_coe]
  exact (sectionRingStructure s).baseMap_apply U r

/-- **The inclusion of a homogeneous summand carries the action of `Γ(S, U)` to multiplication by
its degree-zero image.** -/
public theorem of_smul (U : s.base.Opens) (n : ℕ) (r : ↥Γ(s.base, U))
    (a : ↥Γ(s.pieceNat n, U)) :
    DirectSum.of (s.sectionPieces U) n (r • a)
      = DirectSum.of (s.sectionPieces U) n a * ((s.baseHom U) r : s.sectionRing U) := by
  rw [coe_baseHom]
  rw (transparency := .default) [DirectSum.of_mul_of]
  exact (congrArg (DirectSum.of (s.sectionPieces U) (n + 0)) (s.gmul_onePiece_smul U n r a)).symm

/-! ### The degree-zero part as an algebra over the base -/

/-- The `Γ(S, U)`-algebra structure on the degree-zero part of the graded ring of sections, given
by the degree-zero identification `Stacks.RelativeProj.Situation.baseHom`. -/
public instance gradeZeroAlgebra (U : s.base.Opens) :
    Algebra ↥Γ(s.base, U) ↥(s.sectionRingGrading U 0) := (s.baseHom U).hom.toAlgebra

/-- **The degree-zero summand of the graded ring of sections is the sections of `𝒜₀`,** and
`Γ(S, U)`-linearly so. -/
public def gradeZeroLinearEquiv (U : s.base.Opens) :
    ↥Γ(s.pieceNat 0, U) ≃ₗ[↥Γ(s.base, U)] ↥(s.sectionRingGrading U 0) where
  __ := AddMonoidHom.ofInjective (DirectSum.of_injective (β := s.sectionPieces U) 0)
  map_smul' r a := Subtype.ext ((s.of_smul U 0 r a).trans (_root_.mul_comm _ _))

/-- `Stacks.RelativeProj.Situation.gradeZeroLinearEquiv` sends a section of `𝒜₀` to its
degree-zero summand in the section ring. -/
@[simp] public theorem coe_gradeZeroLinearEquiv (U : s.base.Opens) (a : ↥Γ(s.pieceNat 0, U)) :
    ((s.gradeZeroLinearEquiv U a : ↥(s.sectionRingGrading U 0)) : s.sectionRing U)
      = DirectSum.of (s.sectionPieces U) 0 a :=
  AddMonoidHom.ofInjective_apply (DirectSum.of_injective (β := s.sectionPieces U) 0)

/-- Graded restriction sends the summand `m` in degree `n` to the restriction of `m`. -/
private theorem gradedRestrict_of {U V : s.base.Opens} (h : U ≤ V) (n : ℕ)
    (m : ↥Γ(s.pieceNat n, V)) :
    s.gradedRestrict h (DirectSum.of (s.sectionPieces V) n m)
      = DirectSum.of (s.sectionPieces U) n ((s.pieceNat n).presheaf.map (homOfLE h).op m) := by
  rw [gradedRestrict_apply, sectionRingRestrict, (sectionRingStructure s).restrict_of U V h n m]
  rfl

/-- The degree-zero identifications are compatible with restriction: the degree-zero part of
`Stacks.RelativeProj.Situation.gradedRestrict` is restriction of sections of `𝒜₀`. -/
public theorem gradedZeroRingHom_gradeZeroLinearEquiv {U V : s.base.Opens} (h : U ≤ V)
    (b : ↥Γ(s.pieceNat 0, V)) :
    (s.gradedRestrict h).gradedZeroRingHom (s.gradeZeroLinearEquiv V b)
      = s.gradeZeroLinearEquiv U ((s.pieceNat 0).presheaf.map (homOfLE h).op b) := by
  refine Subtype.ext ?_
  show s.gradedRestrict h ((s.gradeZeroLinearEquiv V b : ↥(s.sectionRingGrading V 0)) :
      s.sectionRing V) = _
  rw [coe_gradeZeroLinearEquiv, gradedRestrict_of, coe_gradeZeroLinearEquiv]

/-! ### The second hypothesis of Tag 01NO: the degree-zero square -/

/-- **`Spec (𝒜(V)₀)` is the base change of `Spec (𝒜(U)₀)` along `Spec Γ(S, V) ⟶ Spec Γ(S, U)`**
for affine opens `V ≤ U`, read through the degree-zero identifications. -/
public theorem isPullback_specMap_baseHom {U V : s.base.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    IsPullback (Spec.map (s.baseHom V))
      (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom))
      (Spec.map (s.base.presheaf.map (homOfLE h).op)) (Spec.map (s.baseHom U)) := by
  let aUV : Algebra ↥Γ(s.base, U) ↥Γ(s.base, V) :=
    (s.base.presheaf.map (homOfLE h).op).hom.toAlgebra
  let mUV : Module ↥Γ(s.base, U) ↥Γ(s.pieceNat 0, V) :=
    Module.compHom _ (s.base.presheaf.map (homOfLE h).op).hom
  let tUV : IsScalarTower ↥Γ(s.base, U) ↥Γ(s.base, V) ↥Γ(s.pieceNat 0, V) :=
    ⟨fun x y z => mul_smul ((s.base.presheaf.map (homOfLE h).op).hom x) y z⟩
  let aAB : Algebra ↥(s.sectionRingGrading U 0) ↥(s.sectionRingGrading V 0) :=
    ((s.gradedRestrict h).gradedZeroRingHom).toAlgebra
  let aUB : Algebra ↥Γ(s.base, U) ↥(s.sectionRingGrading V 0) :=
    (((s.gradedRestrict h).gradedZeroRingHom).comp (s.baseHom U).hom).toAlgebra
  let tAB : IsScalarTower ↥Γ(s.base, U) ↥(s.sectionRingGrading U 0)
      ↥(s.sectionRingGrading V 0) := IsScalarTower.of_algebraMap_eq' rfl
  let tB : IsScalarTower ↥Γ(s.base, U) ↥Γ(s.base, V) ↥(s.sectionRingGrading V 0) :=
    IsScalarTower.of_algebraMap_eq' (CommRingCat.hom_ext_iff.1 (s.baseHom_gradedRestrict h)).symm
  let rho : ↥Γ(s.pieceNat 0, U) →ₗ[↥Γ(s.base, U)] ↥Γ(s.pieceNat 0, V) :=
    { toFun := fun a => (s.pieceNat 0).presheaf.map (homOfLE h).op a
      map_add' := fun a b => map_add _ _ _
      map_smul' := fun r a => Scheme.Modules.map_smul (s.pieceNat 0) (homOfLE h) r a }
  exact isPullback_SpecMap_sections_of_isAffineOpen (s.pieceNat 0) hU hV h (fun _ => rfl) rho
    (fun _ => rfl) (s.gradeZeroLinearEquiv U).symm (s.gradeZeroLinearEquiv V).symm
    (fun a => by
      have hb : s.gradeZeroLinearEquiv U ((s.gradeZeroLinearEquiv U).symm a) = a :=
        (s.gradeZeroLinearEquiv U).apply_symm_apply a
      set b := (s.gradeZeroLinearEquiv U).symm a with hbdef
      have key : (algebraMap ↥(s.sectionRingGrading U 0) ↥(s.sectionRingGrading V 0)) a
          = s.gradeZeroLinearEquiv V ((s.pieceNat 0).presheaf.map (homOfLE h).op b) := by
        rw [← hb]
        exact s.gradedZeroRingHom_gradeZeroLinearEquiv h b
      rw [key, LinearEquiv.symm_apply_apply])

/-- **The degree-zero chart square is cartesian.** For affine opens `U ≤ V` of the base, the
degree-zero chart `Spec (𝒜(U)₀) ⟶ U` is the base change of `Spec (𝒜(V)₀) ⟶ V` along the
inclusion. -/
public theorem chartZero_isPullback {U V : s.base.affineOpens} (h : U ≤ V) :
    IsPullback (s.chartZero U)
      (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom))
      (s.base.homOfLE h) (s.chartZero V) :=
  (s.isPullback_specMap_baseHom (isAffineOpen V) (isAffineOpen U) h).of_iso
    (Iso.refl _) (isAffineOpen U).isoSpec.symm (Iso.refl _) (isAffineOpen V).isoSpec.symm
    (by simp [chartZero]) (by simp)
    (isoSpec_inv_homOfLE (isAffineOpen U) (isAffineOpen V) h).symm
    (by simp [chartZero])

/-! ### The first hypothesis of Tag 01NO: degreewise surjectivity -/

/-- **The irrelevant ideal of `𝒜(U)` is covered by that of `𝒜(V)`.** For affine opens `U ≤ V`
of the base, the irrelevant ideal of `𝒜(U)` is contained in the ideal generated by the
restrictions of the irrelevant ideal of `𝒜(V)`. -/
public theorem irrelevant_le_map {U V : s.base.affineOpens} (h : U ≤ V) :
    (s.chartGrading U)₊ ≤ ((s.chartGrading V)₊).map (s.gradedRestrict h) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  obtain ⟨a, rfl⟩ : ∃ a, DirectSum.of (s.sectionPieces U.1) i a = x := hx
  let aUV : Algebra ↥Γ(s.base, V.1) ↥Γ(s.base, U.1) :=
    (s.base.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom.toAlgebra
  let mUV : Module ↥Γ(s.base, V.1) ↥Γ(s.pieceNat i, U.1) :=
    Module.compHom _ (s.base.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom
  let tUV : IsScalarTower ↥Γ(s.base, V.1) ↥Γ(s.base, U.1) ↥Γ(s.pieceNat i, U.1) :=
    ⟨fun x y z => mul_smul
      ((s.base.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom x) y z⟩
  let rho : ↥Γ(s.pieceNat i, V.1) →ₗ[↥Γ(s.base, V.1)] ↥Γ(s.pieceNat i, U.1) :=
    { toFun := fun b => (s.pieceNat i).presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op b
      map_add' := fun b c => map_add _ _ _
      map_smul' := fun r b =>
        Scheme.Modules.map_smul (s.pieceNat i) (homOfLE (show U.1 ≤ V.1 from h)) r b }
  have hbc : IsBaseChange ↥Γ(s.base, U.1) rho :=
    isBaseChange_restrict_of_isAffineOpen (s.pieceNat i) (isAffineOpen V) (isAffineOpen U)
      h (fun _ => rfl) rho (fun _ => rfl)
  refine hbc.inductionOn a
    (fun b => DirectSum.of (s.sectionPieces U.1) i b ∈
      (((s.chartGrading V)₊).map (s.gradedRestrict h)).toAddSubmonoid) ?_ ?_ ?_ ?_
  · exact map_zero (DirectSum.of (s.sectionPieces U.1) i) ▸ zero_mem _
  · intro m
    show DirectSum.of (s.sectionPieces U.1) i
        ((s.pieceNat i).presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op m) ∈ _
    rw [← s.gradedRestrict_of h i m]
    exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi ⟨m, rfl⟩)
  · intro r n ih
    rw [s.of_smul U.1 i r n]
    exact Ideal.mul_mem_right _ _ ih
  · intro n₁ n₂ h₁ h₂
    exact map_add (DirectSum.of (s.sectionPieces U.1) i) n₁ n₂ ▸ add_mem h₁ h₂

/-! ### Tag 01NO from the chart hypothesis alone -/

/-- **Tag 01NO for a situation, from the chart condition alone.** If for every inclusion `U ≤ V`
of affine opens of the base the graded restriction map `𝒜(V) ⟶ 𝒜(U)` satisfies
`Stacks.Proj.IsBaseChangeOnCharts`, then the situation satisfies
`Stacks.RelativeProj.Situation.ChartsCartesian`. -/
public theorem ChartsCartesian.of_isBaseChangeOnCharts
    (hcharts : ∀ {U V : s.base.affineOpens} (h : U ≤ V),
      Stacks.Proj.IsBaseChangeOnCharts (s.gradedRestrict h)) :
    s.ChartsCartesian :=
  ChartsCartesian.of_isPullback s (fun h => s.irrelevant_le_map h)
    (fun h => s.chartZero_isPullback h) hcharts

end Stacks.RelativeProj.Situation

end
