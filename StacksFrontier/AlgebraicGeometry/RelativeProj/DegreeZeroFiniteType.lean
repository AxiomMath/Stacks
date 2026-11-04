module

public import StacksFrontier.AlgebraicGeometry.Coherent.IdealSheafFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Projective

/-!
# Stacks 0800: relative `Proj` of a finite type graded algebra

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra and
`p : X = Proj_S(𝒜) ⟶ S` its relative homogeneous spectrum. Stacks 0800 says that the conditions

1. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒜_0`-algebra,
2. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒪_S`-algebra

are equivalent, and that under them `p` is locally projective, in particular proper. This file
states and proves all three assertions with the condition on `𝒜_0` read on the sheaf:
`SheafOfModules.IsFiniteType (s.algebra.piece 0)`.

The chart-by-chart argument of `StacksFrontier/AlgebraicGeometry/RelativeProj/Projective.lean`
consumes the affine-local form `Stacks.RelativeProj.Situation.IsDegreeZeroFiniteType` of that
condition: over every affine open `U` of the base, `Γ(S, U) → 𝒜_0(U)` is a finite ring map. The
two are equivalent (`Stacks.RelativeProj.Situation.isDegreeZeroFiniteType_iff_isFiniteType`).
The degree-zero piece is quasi-coherent, so finite type of it is finiteness of its sections over
every affine open (`AlgebraicGeometry.moduleFinite_sections_on_affine` and
`Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections`), and those sections
are, `Γ(S, U)`-linearly, the degree-zero summand of the graded ring of sections, because the
structure-sheaf map lands in degree zero and multiplies the unit section
(`Stacks.RelativeProj.Situation.degreeZero_mul_of`).

## Main results

* `Stacks.RelativeProj.Situation.isDegreeZeroFiniteType_iff_isFiniteType` — the affine-local
  degree-zero condition is finite type of the sheaf `𝒜_0`.
* `Stacks.RelativeProj.Situation.relativeProj_finiteType_iff_and_isLocallyProjective_isProper` —
  **Stacks 0800**, both assertions in one statement: conditions (1) and (2) are equivalent, and
  under them `p` is locally projective and proper.
* `Stacks.RelativeProj.Situation.isFiniteType_and_isFiniteTypeOverDegreeZero_iff`,
  `Stacks.RelativeProj.Situation.isLocallyProjective_relativeProjToBase_of_pieceZero` and
  `Stacks.RelativeProj.Situation.isProper_relativeProjToBase_of_pieceZero` — the three
  conclusions separately, for use.

## Implementation notes

The finite type conditions on the algebra are the source's: a quasi-coherent `𝒪_S`-algebra is of
finite type when its algebra of sections over every affine open `Spec(R) ⊆ S` is a finite type
`R`-algebra (Properties, the definition preceding Tag 05JT), and likewise over `𝒜_0`. These are
`Stacks.RelativeProj.Situation.IsFiniteTypeOverBase` and
`Stacks.RelativeProj.Situation.IsFiniteTypeOverDegreeZero`, the algebra of sections being the
graded ring of sections `Stacks.RelativeProj.Situation.sectionRing`. Locally projective is
`AlgebraicGeometry.IsLocallyProjective`, Definition 01W8 (3). The algebra is an arbitrary
quasi-coherent graded `𝒪_S`-algebra over an arbitrary scheme, `Stacks.RelativeProj.Situation`;
the registrations of this tag on projective bundles are its special case `𝒜 = Sym(ℰ)`.

`AlgebraicGeometry.Scheme.Modules` and the sheaf of rings carried by a relative `Proj` situation
are two definitionally equal presentations of the same data, and instance search sees only the
first, so the degree-zero piece is retyped by a local `let` where the `Γ(S, U)`-module structure
on its sections is needed. For the same reason the scalar of
`Stacks.RelativeProj.Situation.degreeZero_mul_of` is typed at the ringed-site spelling, which is
the one the graded multiplication of the algebra is stated at.

## References

* [Stacks Project, Tag 0800](https://stacks.math.columbia.edu/tag/0800)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}}

/-- **The structure-sheaf map acts by scalars in degree zero.** The image of a function on an
open under the map from the structure sheaf to the graded ring of sections, times a degree-zero
homogeneous section, is the degree-zero homogeneous section got by acting with that function on
it. This is what makes the degree-zero summand of the graded ring of sections a `Γ(S, U)`-linear
image of the sections of the degree-zero piece. -/
theorem degreeZero_mul_of (U : s.base.Opens) (r : s.base.ringCatSheaf.obj.obj (op U))
    (x : (s.algebra.piece 0).val.obj (op U)) :
    s.sectionRingBaseMap U r * DirectSum.of (s.sectionPieces U) 0 x =
      DirectSum.of (s.sectionPieces U) 0 (r • x) := by
  show (s.sectionRingStructure).baseMap U r * _ = _
  rw [(s.sectionRingStructure).baseMap_apply U r, DirectSum.of_mul_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (Nat.zero_add 0)
  have hsmul {a b : s.sectionPieces U 0} (hab : HEq a b) : HEq (r • a) (r • b) := by
    cases hab; rfl
  exact ((s.sectionRingStructure).mul_homogeneous U 0 0
      (r • s.algebra.one.eval (op U)) x).trans
    ((heq_of_eq ((s.algebra.mul 0 0).map_smul_left (op U) r
          (s.algebra.one.eval (op U)) x)).trans
      (hsmul (s.algebra.one_mul 0 (op U) x)))

/-- **The sections of the degree-zero piece are the degree-zero summand of the graded ring of
sections.** Over an affine open `U` of the base, the sections of `𝒜_0` over `U` form a finite
`Γ(S, U)`-module exactly when `Γ(S, U) → 𝒜_0(U)` is finite, the degree-zero summand of the graded
ring of sections being the image of those sections under the inclusion of the summand, which is
injective and `Γ(S, U)`-linear. -/
theorem finite_sectionRingZeroMap_iff (U : s.base.Opens) :
    let F : s.base.Modules := s.algebra.piece 0
    (show Γ(s.base, U) →+* s.sectionRingGrading U 0 from (s.sectionRingZeroMap U).hom).Finite ↔
      Module.Finite Γ(s.base, U) Γ(F, U) := by
  intro F
  set φ : Γ(s.base, U) →+* s.sectionRingGrading U 0 := (s.sectionRingZeroMap U).hom
  let : Algebra Γ(s.base, U) (s.sectionRingGrading U 0) := φ.toAlgebra
  have hcoe (r : Γ(s.base, U)) : (φ r).val = s.sectionRingBaseMap U r :=
    congrArg Subtype.val (GradedRing.projZeroRingHom'_apply_coe (s.sectionRingGrading U)
      ⟨_, sectionRingBaseMap_mem_zero s U r⟩)
  let z : Γ(F, U) →ₗ[Γ(s.base, U)] s.sectionRingGrading U 0 :=
    { toFun := fun x => ⟨DirectSum.of (s.sectionPieces U) 0 x, ⟨x, rfl⟩⟩
      map_add' := fun x y => Subtype.ext ((DirectSum.of (s.sectionPieces U) 0).map_add x y)
      map_smul' := fun r x => by
        refine Subtype.ext ?_
        show DirectSum.of (s.sectionPieces U) 0 (r • x) =
          (r • (⟨DirectSum.of (s.sectionPieces U) 0 x, ⟨x, rfl⟩⟩ :
            s.sectionRingGrading U 0)).val
        rw [Algebra.smul_def]
        show DirectSum.of (s.sectionPieces U) 0 (r • x) =
          (φ r).val * DirectSum.of (s.sectionPieces U) 0 x
        rw [hcoe]
        exact (degreeZero_mul_of U r x).symm }
  have hz : Function.Bijective z := by
    refine ⟨fun x y hxy => DirectSum.of_injective (β := s.sectionPieces U) 0
      (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let e := LinearEquiv.ofBijective z hz
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Module.Finite Γ(s.base, U) (s.sectionRingGrading U 0) := h
    exact Module.Finite.equiv e.symm
  · have : Module.Finite Γ(s.base, U) Γ(F, U) := h
    exact Module.Finite.equiv e

/-- **A finite type degree-zero piece is finite over the structure sheaf on every affine open.**
The degree-zero piece of the graded algebra of a relative `Proj` situation is quasi-coherent, so
if it is of finite type then its sections over an affine open are a finite module over the
functions there; that module is the degree-zero summand of the graded ring of sections. -/
theorem isDegreeZeroFiniteType_of_isFiniteType
    (h : SheafOfModules.IsFiniteType (s.algebra.piece 0)) : s.IsDegreeZeroFiniteType := by
  intro U hU
  let F : s.base.Modules := s.algebra.piece 0
  let : F.IsFiniteType := h
  let : F.IsQuasicoherent := s.isQuasicoherent 0
  exact (finite_sectionRingZeroMap_iff U).mpr
    (AlgebraicGeometry.moduleFinite_sections_on_affine _ U hU)

/-- **The affine-local degree-zero condition is finite type of the sheaf `𝒜_0`.** For the
quasi-coherent degree-zero piece of a relative `Proj` situation, finiteness of
`Γ(S, U) → 𝒜_0(U)` over every affine open `U` of the base is the same as `𝒜_0` being a finite
type `𝒪_S`-module, which is the condition on `𝒜_0` in both conditions of Stacks 0800. -/
theorem isDegreeZeroFiniteType_iff_isFiniteType :
    s.IsDegreeZeroFiniteType ↔ SheafOfModules.IsFiniteType (s.algebra.piece 0) := by
  refine ⟨fun h => ?_, isDegreeZeroFiniteType_of_isFiniteType (s := s)⟩
  let F : s.base.Modules := s.algebra.piece 0
  let : F.IsQuasicoherent := s.isQuasicoherent 0
  exact Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections F
    fun V => (finite_sectionRingZeroMap_iff V.1).mp (h V.1 V.2)

/-! ### Stacks 0800 -/

/-- **Stacks 0800, the equivalence of conditions (1) and (2).** For a quasi-coherent graded
`𝒪_S`-algebra `𝒜` over an arbitrary scheme `S`, the following are equivalent:

1. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒜_0`-algebra;
2. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒪_S`-algebra.

Finite type of `𝒜_0` is `SheafOfModules.IsFiniteType`, local generation by finitely many
sections. Finite type of the quasi-coherent algebra `𝒜` over `𝒪_S`, resp. over `𝒜_0`, is the
source's definition: over every affine open `U` of `S` the algebra `𝒜(U)` of sections is a finite
type `𝒪_S(U)`-algebra, resp. a finite type `𝒜_0(U)`-algebra; these are
`Stacks.RelativeProj.Situation.IsFiniteTypeOverBase` and
`Stacks.RelativeProj.Situation.IsFiniteTypeOverDegreeZero`. -/
theorem isFiniteType_and_isFiniteTypeOverDegreeZero_iff :
    SheafOfModules.IsFiniteType (s.algebra.piece 0) ∧ s.IsFiniteTypeOverDegreeZero ↔
      SheafOfModules.IsFiniteType (s.algebra.piece 0) ∧ s.IsFiniteTypeOverBase := by
  have htfae := (properFiniteType_tfae s).out 1 2
  exact ⟨fun ⟨h₀, hdeg⟩ => ⟨h₀, (htfae.mp ⟨isDegreeZeroFiniteType_of_isFiniteType h₀, hdeg⟩).2⟩,
    fun ⟨h₀, hb⟩ => ⟨h₀, (htfae.mpr ⟨isDegreeZeroFiniteType_of_isFiniteType h₀, hb⟩).2⟩⟩

/-- **Stacks 0800, local projectivity.** If `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of
finite type as an `𝒜_0`-algebra (condition (1)), then the structure morphism
`p : Proj_S(𝒜) ⟶ S` of the relative homogeneous spectrum is locally projective, in the sense of
Stacks 01W8. By `Stacks.RelativeProj.Situation.isFiniteType_and_isFiniteTypeOverDegreeZero_iff`
condition (2) gives the same, which is
`isLocallyProjective_relativeProjToBase_of_pieceZero_of_isFiniteTypeOverBase`. -/
theorem isLocallyProjective_relativeProjToBase_of_pieceZero
    (h₀ : SheafOfModules.IsFiniteType (s.algebra.piece 0))
    (hft : s.IsFiniteTypeOverDegreeZero) :
    IsLocallyProjective (relativeProjToBase s) :=
  isLocallyProjective_relativeProjToBase s (isDegreeZeroFiniteType_of_isFiniteType h₀) hft

/-- **Stacks 0800, properness.** If `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite
type as an `𝒜_0`-algebra (condition (1)), then the structure morphism of the relative homogeneous
spectrum is proper, a locally projective morphism being proper (Stacks 01WC). -/
theorem isProper_relativeProjToBase_of_pieceZero
    (h₀ : SheafOfModules.IsFiniteType (s.algebra.piece 0))
    (hft : s.IsFiniteTypeOverDegreeZero) :
    IsProper (relativeProjToBase s) :=
  isProper_of_isLocallyProjective (isLocallyProjective_relativeProjToBase_of_pieceZero h₀ hft)

/-- **Stacks 0800.** Let `𝒜` be a quasi-coherent graded `𝒪_S`-algebra over a scheme `S` and
`p : Proj_S(𝒜) ⟶ S` its relative homogeneous spectrum. The conditions

1. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒜_0`-algebra,
2. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒪_S`-algebra

are equivalent, and under them `p` is locally projective and in particular proper.

Each condition is written out as the source defines it: finite type of `𝒜_0` is
`SheafOfModules.IsFiniteType`, and a quasi-coherent algebra is of finite type over `𝒜_0`, resp.
over `𝒪_S`, when over every affine open `U` of `S` its algebra of sections `𝒜(U)` is a finite type
`𝒜_0(U)`-algebra, resp. a finite type `𝒪_S(U)`-algebra. -/
@[stacks 0800]
theorem relativeProj_finiteType_iff_and_isLocallyProjective_isProper :
    ((SheafOfModules.IsFiniteType (s.algebra.piece 0) ∧
        ∀ U : s.base.Opens, IsAffineOpen U →
          Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U)) ↔
      (SheafOfModules.IsFiniteType (s.algebra.piece 0) ∧
        ∀ U : s.base.Opens, IsAffineOpen U →
          (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U).FiniteType)) ∧
    ((SheafOfModules.IsFiniteType (s.algebra.piece 0) ∧
        ∀ U : s.base.Opens, IsAffineOpen U →
          Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U)) →
      IsLocallyProjective (relativeProjToBase s) ∧ IsProper (relativeProjToBase s)) :=
  ⟨isFiniteType_and_isFiniteTypeOverDegreeZero_iff, fun ⟨h₀, hft⟩ =>
    ⟨isLocallyProjective_relativeProjToBase_of_pieceZero h₀ hft,
      isProper_relativeProjToBase_of_pieceZero h₀ hft⟩⟩

/-- **The local projectivity of Stacks 0800 from condition (2).** If `𝒜_0` is a finite type
`𝒪_S`-module and `𝒜` is of finite type as an `𝒪_S`-algebra, then the structure morphism of the
relative homogeneous spectrum is locally projective. -/
theorem isLocallyProjective_relativeProjToBase_of_pieceZero_of_isFiniteTypeOverBase
    (h₀ : SheafOfModules.IsFiniteType (s.algebra.piece 0)) (hb : s.IsFiniteTypeOverBase) :
    IsLocallyProjective (relativeProjToBase s) :=
  isLocallyProjective_relativeProjToBase_of_pieceZero h₀
    (isFiniteType_and_isFiniteTypeOverDegreeZero_iff.mpr ⟨h₀, hb⟩).2

/-- **The properness of Stacks 0800 from condition (2).** -/
theorem isProper_relativeProjToBase_of_pieceZero_of_isFiniteTypeOverBase
    (h₀ : SheafOfModules.IsFiniteType (s.algebra.piece 0)) (hb : s.IsFiniteTypeOverBase) :
    IsProper (relativeProjToBase s) :=
  isProper_of_isLocallyProjective
    (isLocallyProjective_relativeProjToBase_of_pieceZero_of_isFiniteTypeOverBase h₀ hb)

end Stacks.RelativeProj.Situation

end
