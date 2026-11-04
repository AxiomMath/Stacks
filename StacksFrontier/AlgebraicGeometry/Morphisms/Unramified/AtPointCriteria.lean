module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksFrontier.AlgebraicGeometry.FiberCotangentAssembly.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Numerical
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Criteria for unramifiedness at a point

For a morphism of schemes locally of finite type, unramifiedness at a point is equivalent to
unramifiedness of the scheme-theoretic fibre there, to the vanishing of the stalk of the sheaf of
relative differentials, to the vanishing of that stalk computed on the fibre, to the vanishing of
either of the two canonically identified residue-field fibres of those stalks, and to the
condition that the maximal ideal of the base generates the maximal ideal of the source and that
the residue field extension is finite separable.

## Main results

* `AlgebraicGeometry.unramifiedAt_tfae` gives the six characterizations of unramifiedness at a
  point.
* `AlgebraicGeometry.unramifiedAt_iff_subsingleton_relativeDifferentialStalk` isolates the
  equivalence of the first and third, and
  `AlgebraicGeometry.unramifiedAt_of_subsingleton_relativeDifferentialStalk` its backward
  implication, which is the form consumed by the local criteria for étaleness.

## Implementation notes

The entries of `List.TFAE` follow the source's order, except that the two canonically identified
cotangent spaces of the source's condition (5) are separate entries, so that either one alone
gives the criterion. Their canonical identification is
`Stacks.FiberCotangentAssembly.fiberDifferentialsTensorIdentification`. Conditions (3) and (4)
use `Stacks.SmoothAtJacobian.relativeDifferentialStalk`, the actual stalk of the sheaf of
relative differentials, the second one for the structure morphism of the scheme-theoretic fibre.

Unramifiedness of the fibre is read at `AlgebraicGeometry.Scheme.Hom.asFiber`, the point of the
scheme-theoretic fibre determined by the given point, and transfers to unramifiedness of the
morphism itself by `AlgebraicGeometry.unramifiedAt_iff_of_isPullback` applied to the cartesian
square defining the fibre. That the structure morphism of the fibre is again locally of finite
type is the base change of that property along `Spec κ(s) ⟶ S`.

The vanishing of a stalk of a sheaf of modules is expressed as `Subsingleton` of its carrier
type, and the passage between a stalk and its residue-field fibre is Nakayama's lemma in the form
`IsLocalRing.subsingleton_tensorProduct`, which applies because the stalk of the relative
differentials of a morphism locally of finite type is a finite module over the local ring
(`Stacks.RelativeDifferentialStalkMap.finite_relativeDifferentialStalk`).

The source's condition (6) is Mathlib's `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq` for
the stalk map, whose finiteness hypothesis is supplied by
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`; the residue-field extension is read through
`AlgebraicGeometry.Scheme.Hom.residueFieldMap` rather than through the residue field of the
local ring, and the two agree.

The G-unramified variant of the source, where `f` is assumed locally of finite presentation, is
`AlgebraicGeometry.gUnramifiedAt_tfae`, in
`StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.GUnramifiedLocusBaseChange`; it is this list
with G-unramifiedness at `x` prepended, the two heads being equivalent under local finite
presentation by `AlgebraicGeometry.gUnramifiedAt_iff_unramifiedAt`.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
-/

@[expose] public section

open CategoryTheory
open Stacks.SmoothAtJacobian
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### Vanishing of the relative differentials at a point -/

/-- **The relative differentials at a point vanish exactly when the stalk map is formally
unramified.** The stalk of the sheaf of relative differentials is the module of Kähler
differentials of the stalk map. -/
@[ega "IV 17.4.1" "equivalence c)⇔e)"]
private theorem subsingleton_relativeDifferentialStalk_iff_formallyUnramified
    (f : X ⟶ S) (x : X) :
    Subsingleton (relativeDifferentialStalk f x) ↔
      (f.stalkMap x).hom.FormallyUnramified := by
  classical
  let := Stacks.RelativeDifferentialStalkMap.algebraStalkMap f x
  show Subsingleton (relativeDifferentialStalk f x) ↔
    Algebra.FormallyUnramified (ToType (S.presheaf.stalk (f x)))
      (ToType (X.sheaf.presheaf.stalk x))
  rw [Algebra.formallyUnramified_iff]
  exact Equiv.subsingleton_congr
    (Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv f x).toEquiv

/-- **The relative differentials at a point vanish exactly when their residue-field fibre
does.** Nakayama's lemma, the stalk being a finite module over the local ring. -/
private theorem subsingleton_relativeDifferentialStalk_iff_relativeCotangentSpace
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    Subsingleton (relativeDifferentialStalk f x) ↔
      Subsingleton (relativeCotangentSpace f x) := by
  classical
  let := relativeDifferentialStalkModule f x
  let : Algebra ↥(X.presheaf.stalk x) ↥(X.residueField x) := (X.residue x).hom.toAlgebra
  have hfin := Stacks.RelativeDifferentialStalkMap.finite_relativeDifferentialStalk f x
  show _ ↔ Subsingleton (↥(X.residueField x) ⊗[↥(X.presheaf.stalk x)]
    relativeDifferentialStalk f x)
  exact (IsLocalRing.subsingleton_tensorProduct
    (R := ↥(X.presheaf.stalk x)) (M := relativeDifferentialStalk f x)).symm

/-- **The two residue-field fibres of the relative differentials vanish together**, through their
canonical identification. -/
private theorem subsingleton_relativeCotangentSpace_iff_fiberRelativeCotangentSpace
    (f : X ⟶ S) (x : X) :
    Subsingleton (relativeCotangentSpace f x) ↔
      Subsingleton (fiberRelativeCotangentSpace f x) := by
  classical
  let e := (Stacks.FiberCotangentAssembly.fiberDifferentialsTensorIdentification f x).equiv
  exact Equiv.subsingleton_congr
    (Equiv.ofBijective e.hom.hom ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance))

/-- **Formal unramifiedness of the stalk map is the local criterion of the source**: the maximal
ideal of the base generates the maximal ideal of the source, and the residue field extension is
finite separable. -/
@[ega "0 21.7.4" "a ⇔ b", ega "IV 17.4.1.2" "partial"]
private theorem formallyUnramified_stalkMap_iff_residueCriterion
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    (f.stalkMap x).hom.FormallyUnramified ↔
      Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        (letI := (f.residueFieldMap x).hom.toAlgebra
         Module.Finite (S.residueField (f x)) (X.residueField x) ∧
           Algebra.IsSeparable (S.residueField (f x)) (X.residueField x)) := by
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType A B :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f x)
  have h := Algebra.FormallyUnramified.iff_map_maximalIdeal_eq (R := A) (S := B)
  have key : (f.residueFieldMap x).hom.toAlgebra =
      (inferInstance : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) := by
    refine Algebra.algebra_ext _ _ fun y ↦ ?_
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    rfl
  constructor
  · intro hu
    have h' := h.mp hu
    refine ⟨?_, ?_⟩
    · have hmax := h'.2
      change (IsLocalRing.maximalIdeal A).map (algebraMap A B) = _ at hmax
      convert hmax using 1
      rfl
    · let := (f.residueFieldMap x).hom.toAlgebra
      have hsep : Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) := by
        convert! h'.1
      have : Algebra.EssFiniteType (S.residueField (f x)) (X.residueField x) := by
        have : Algebra.EssFiniteType A (IsLocalRing.ResidueField B) :=
          Algebra.EssFiniteType.comp A B (IsLocalRing.ResidueField B)
        have hess : Algebra.EssFiniteType (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField B) :=
          Algebra.EssFiniteType.of_comp A (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField B)
        convert! hess
      have : Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x) :=
        Algebra.IsSeparable.isAlgebraic _ _
      exact ⟨Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep⟩
  · rintro ⟨hmax, hres⟩
    refine h.mpr ⟨?_, ?_⟩
    · have hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B) := by
        convert! hres.2
        exact key.symm
      exact hsep
    · show (IsLocalRing.maximalIdeal A).map (algebraMap A B) = _
      convert hmax using 1
      rfl

/-! ### The characterizations of unramifiedness at a point -/

/-- **Unramifiedness at a point is the vanishing of the relative differentials there.** For a
morphism locally of finite type, this is the equivalence of parts (1) and (3) of
[Stacks, Tag 02GF]: unramifiedness at `x` is formal unramifiedness of the stalk map, and the
stalk of the sheaf of relative differentials is the module of Kähler differentials of that
stalk map. -/
@[ega "IV 17.4.1" "more general", sga "3 XI 1.3" "(i)(a)⇔(c)"]
public theorem unramifiedAt_iff_subsingleton_relativeDifferentialStalk
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    UnramifiedAt f x ↔ Subsingleton (relativeDifferentialStalk f x) :=
  (unramifiedAt_iff_formallyUnramified_stalkMap f x).trans
    (subsingleton_relativeDifferentialStalk_iff_formallyUnramified f x).symm

/-- **The scheme-theoretic fibre detects unramifiedness at a point.** The fibre is the base change
of `f` along the canonical morphism from the spectrum of the residue field of the image point.
This is the equivalence of parts (1) and (2) of [Stacks, Tag 02GF]. -/
@[ega "IV 17.4.1" "more general",
  ega "IV 17.8.1" "case Y = S",
  sga "1 I 5.8" "Net clause, special case"]
public theorem unramifiedAt_iff_unramifiedAt_fiberToSpecResidueField
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    UnramifiedAt f x ↔
      UnramifiedAt (f.fiberToSpecResidueField (f x)) (f.asFiber x) := by
  have hsq : IsPullback (f.fiberι (f x))
      (f.fiberToSpecResidueField (f x)) f (S.fromSpecResidueField (f x)) :=
    IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))
  have h := unramifiedAt_iff_of_isPullback hsq (f.asFiber x)
  rwa [f.fiberι_asFiber x] at h

/-- **Stacks Project, Tag 02GF.** For a morphism of schemes `f : X ⟶ S` locally of finite type
and a point `x` of `X` with image `s = f x`, the following are equivalent: `f` is unramified at
`x`; the fibre `X_s` is unramified over `κ(s)` at `x`; the `𝒪_{X,x}`-module `Ω_{X/S,x}` is zero;
the `𝒪_{X_s,x}`-module `Ω_{X_s/s,x}` is zero; the `κ(x)`-vector space
`Ω_{X_s/s,x} ⊗ κ(x) = Ω_{X/S,x} ⊗ κ(x)` is zero, in either of its two canonically identified
spellings; and `𝔪_s 𝒪_{X,x} = 𝔪_x` with `κ(x)/κ(s)` finite separable. -/
@[stacks 02GF]
public theorem unramifiedAt_tfae (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    List.TFAE [
      UnramifiedAt f x,
      UnramifiedAt (f.fiberToSpecResidueField (f x)) (f.asFiber x),
      Subsingleton (relativeDifferentialStalk f x),
      Subsingleton (relativeDifferentialStalk (f.fiberToSpecResidueField (f x))
        (f.asFiber x)),
      Subsingleton (fiberRelativeCotangentSpace f x),
      Subsingleton (relativeCotangentSpace f x),
      Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        (letI := (f.residueFieldMap x).hom.toAlgebra
         Module.Finite (S.residueField (f x)) (X.residueField x) ∧
           Algebra.IsSeparable (S.residueField (f x)) (X.residueField x))] := by
  have hfib : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x))))
  have h12 := unramifiedAt_iff_unramifiedAt_fiberToSpecResidueField f x
  have h13 := unramifiedAt_iff_subsingleton_relativeDifferentialStalk f x
  have h14 : UnramifiedAt f x ↔
      Subsingleton (relativeDifferentialStalk (f.fiberToSpecResidueField (f x))
        (f.asFiber x)) :=
    h12.trans (unramifiedAt_iff_subsingleton_relativeDifferentialStalk _ _)
  have h16 := h13.trans
    (subsingleton_relativeDifferentialStalk_iff_relativeCotangentSpace f x)
  have h15 := h16.trans
    (subsingleton_relativeCotangentSpace_iff_fiberRelativeCotangentSpace f x)
  have h17 := (unramifiedAt_iff_formallyUnramified_stalkMap f x).trans
    (formallyUnramified_stalkMap_iff_residueCriterion f x)
  refine List.tfae_of_forall (b := UnramifiedAt f x) ?_
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact h12.symm
  · exact h13.symm
  · exact h14.symm
  · exact h15.symm
  · exact h16.symm
  · exact h17.symm

/-- **Vanishing of the relative differentials at a point makes a morphism locally of finite type
unramified there.** This is the implication (3) ⟹ (1) of [Stacks, Tag 02GF], the direction used
by the local criteria for étaleness. -/
public theorem unramifiedAt_of_subsingleton_relativeDifferentialStalk
    (f : X ⟶ S) [LocallyOfFiniteType f] {x : X}
    (h : Subsingleton (relativeDifferentialStalk f x)) :
    UnramifiedAt f x :=
  (unramifiedAt_iff_subsingleton_relativeDifferentialStalk f x).mpr h

end AlgebraicGeometry

end
