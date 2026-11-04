module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# From sheaf-level graded algebra data to the graded algebra of relative Proj

Situation 01NN fixes a scheme `S` together with a quasi-coherent graded `𝒪_S`-algebra. Its
sheaf-theoretic form is `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`: an
integer-indexed family of quasi-coherent `𝒪_S`-modules with an `𝒪_S`-bilinear multiplication
and a unit. The form the relative Proj construction of this repository consumes is
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra`: the graded *rings of sections over the
affine opens* of `S`, with restriction maps and the localization property on basic opens. This
file builds the second from the first.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resPiece`,
  `resRingHom`, `res`: restriction of homogeneous sections along an inclusion of opens, of the
  graded rings of sections as a ring homomorphism, and of the internally graded rings as a
  graded ring homomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.toGradedAlgebra`: **the
  bridge.** Sheaf-level graded algebra data on `S` gives a
  `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra S`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.isLocalization_strHom`:
  **the localization property.** For `U` an affine open of `S` and `f : 𝒪_S(U)`, the graded ring
  of sections over the basic open `D(f)` is the localization of the graded ring of sections over
  `U` away from the degree-`0` section attached to `f`.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.exists_resPiece_eq` and
  `exists_pow_smul_eq_zero`: the two degreewise consequences of quasi-coherence that the
  localization property rests on.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resRingHom_id`,
  `resRingHom_comp`, `resRingHom_strHom`: functoriality of restriction and its compatibility
  with the structure map.

## Implementation notes

**The shape of the input, and why.** The source states Situation 01NN over a ringed site, with
the graded algebra of Tag 0FQW. This repository has no form of Tag 0FQW and none of Tag 062R, so
the input vocabulary is introduced here, in the shape Mathlib already supports: the homogeneous
pieces are objects of `AlgebraicGeometry.Scheme.Modules`, quasi-coherence of a piece is Mathlib's
`SheafOfModules.IsQuasicoherent`, and sections are written with the `Γ(M, U)` notation of
`AlgebraicGeometry.Scheme.Modules.presheaf`. That choice is not cosmetic: it is exactly the shape
in which this repository states the localization property of the sections of a quasi-coherent
module, `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`, which is
the one geometric input of the whole file.

**Where quasi-coherence enters, and what it is not reduced to.** Quasi-coherence is used
*degreewise* and only through `isLocalizedModule_restrictₗ`. It is not routed through a
"localization commutes with direct sums" lemma: Mathlib has no such statement for an infinite
index (`IsLocalizedModule.pi` and `IsLocalizedModule.prodMap` are the finite cases), and the
ring-level statement wanted here is about `IsLocalization.Away` of a degree-`0` element rather
than about a module map. The three clauses of `IsLocalization` are therefore checked directly:
units come from `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`, surjectivity is a
`DirectSum.induction_on` over the section (zero, a homogeneous summand, a sum, with a common
denominator in the last case), and the annihilation clause needs a uniform exponent over the
finitely many degrees where the section is nonzero.

**Finite support without decidability.** The homogeneous pieces are arbitrary modules, so
`DFinsupp.support` is unavailable — it asks for `Decidable (x ≠ 0)` in every degree.
`exists_finset_support` replaces it: every section vanishes outside *some* finite set of degrees,
proved by `DirectSum.induction_on`, which is all the uniform-exponent argument needs. The
annihilation clause genuinely needs this and cannot itself be proved by induction: the
hypothesis "the restriction vanishes" does not split along a sum.

**Transparency.** `AlgebraicGeometry.Scheme.Modules` is a `def` with its own category instance,
so the `val` projection of a sheaf of modules is not reachable by dot notation through it; the
unit of the algebra is therefore recorded as a restriction-compatible family of local sections
rather than as a `PresheafOfModules.sections`, which is the same data. The scalar action of
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE` is *definitionally* the action of
the restricted function, so the statements here mention only the latter and the
`IsLocalizedModule` facts are transferred by `exact`. Inside the `SheafGradedAlgebra` namespace
the structure fields `mul_comm`, `mul_one` and `one_mul` shadow the root lemmas of those names,
so commutativity of the section ring must be written `_root_.mul_comm`. The local module and
algebra instances are introduced with `let` and `have`, not with their instance-inlining
variants, matching the pattern of `isLocalizedModule_restrictₗ` itself; instance search does
find them.

**Universes.** Monomorphic in the scheme universe `u`, forced on both sides:
`SheafOfModules.IsQuasicoherent` is stated for module sheaves in the universe of the base ring
sheaf, and `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra S` records its rings of sections
in `CommRingCat.{u}`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)

## Not done here

Tag 01NN labels two assertions, each its own covering set, and both are carried here. The
unlabelled one is on `SheafGradedAlgebra`, the library form of the situation's data.

The labelled one, for the graded rings of local sections, is on a **covering set of eight
declarations**, not on one. The tagged assertion is the existence of a ten-field structure, and
`instGCommRing` is only its first field: the two homogeneous-multiplication equations come free
from `gMul_def` and `gOne_def` by `rfl`, but the structure map and its defining equation are
`strHom` and `strHom_apply`, and the restriction map with its four laws are `resRingHom`,
`resRingHom_of`, `resRingHom_id`, `resRingHom_comp` and `resRingHom_strHom`. The label sat on
`instGCommRing` alone for a time, which claimed the whole assertion while stating one field of
it; all eight now carry it.

Nothing of Tags 01NO, 01NQ or 01NR is claimed: this supplies their input.

The vanishing of the negative homogeneous pieces is part of the input data, as in the source, but
it is used nowhere: the construction reads only the nonnegative degrees. An input weakened by
dropping that field would still give the bridge.

Nothing here glues the charts. The relative Proj construction over the resulting graded algebra,
its charts and their transitions are in
`StacksDraft/AlgebraicGeometry/F3/RelativeProj/`, `RelativeProjGeneral/` and
`RelativeProjGlue/`; this file only supplies their input. Morphisms of sheaf-level graded
algebras, which Tag 0FQW also defines, are not introduced, and nothing is proved about how the
bridge behaves on them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### Restriction -/

/-- Restriction of homogeneous sections of degree `n` along an inclusion of opens. -/
public noncomputable def resPiece {U V : S.Opens} (h : U ≤ V) (n : ℕ) :
    A.sectionPieces V n →+ A.sectionPieces U n where
  toFun := (A.piece (n : ℤ)).presheaf.map (homOfLE h).op
  map_zero' := map_zero _
  map_add' := map_add _

/-- `resPiece` is the presheaf restriction map of the degree-`n` piece. -/
public theorem resPiece_apply {U V : S.Opens} (h : U ≤ V) (n : ℕ) (y : A.sectionPieces V n) :
    A.resPiece h n y = (A.piece (n : ℤ)).presheaf.map (homOfLE h).op y := rfl

/-- Restriction of homogeneous sections is semilinear over the restriction of functions. -/
public theorem resPiece_smul {U V : S.Opens} (h : U ≤ V) (n : ℕ) (r : Γ(S, V))
    (y : A.sectionPieces V n) :
    A.resPiece h n (r • y) = S.presheaf.map (homOfLE h).op r • A.resPiece h n y :=
  (A.piece (n : ℤ)).map_smul (homOfLE h) r y

/-- Restriction in degree `0` sends the unit section to the unit section. -/
public theorem resPiece_one {U V : S.Opens} (h : U ≤ V) :
    A.resPiece h 0 (A.one V) = A.one U := A.one_res h

/-- Restriction of the graded rings of sections, as a ring homomorphism. -/
@[stacks 01NN "graded rings of local sections"]
public noncomputable def resRingHom {U V : S.Opens} (h : U ≤ V) :
    A.sectionRing V →+* A.sectionRing U :=
  DirectSum.toSemiring (fun n => (DirectSum.of (A.sectionPieces U) n).comp (A.resPiece h n))
    ((congrArg (DirectSum.of (A.sectionPieces U) 0) (A.resPiece_one h)).trans
      (DirectSum.one_def _).symm)
    (fun {i j} a b => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [DirectSum.of_mul_of]
      exact congrArg (DirectSum.of (A.sectionPieces U) (i + j))
        ((A.mul (i : ℤ) (j : ℤ)).naturality h a b))

/-- On a homogeneous summand, `resRingHom` is restriction of homogeneous sections. -/
@[stacks 01NN "graded rings of local sections"]
public theorem resRingHom_of {U V : S.Opens} (h : U ≤ V) {n : ℕ} (y : A.sectionPieces V n) :
    A.resRingHom h (DirectSum.of (A.sectionPieces V) n y) =
      DirectSum.of (A.sectionPieces U) n (A.resPiece h n y) :=
  DirectSum.toSemiring_of _ _ _ n y

/-- Two ring homomorphisms out of a graded ring of sections agreeing on the homogeneous
summands are equal. -/
public theorem resRingHom_ext {U V : S.Opens} {φ ψ : A.sectionRing V →+* A.sectionRing U}
    (h : ∀ (n : ℕ) (y : A.sectionPieces V n),
      φ (DirectSum.of (A.sectionPieces V) n y) = ψ (DirectSum.of (A.sectionPieces V) n y)) :
    φ = ψ := by
  refine DFunLike.ext _ _ fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n y => exact h n y
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Restriction along the identity of an open is the identity. -/
@[stacks 01NN "graded rings of local sections"]
public theorem resRingHom_id (U : S.Opens) : A.resRingHom (le_refl U) = RingHom.id _ := by
  refine A.resRingHom_ext fun n y => ?_
  rw [A.resRingHom_of, RingHom.id_apply, A.resPiece_apply,
    show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl]
  simp

/-- Restriction along a composite of inclusions is the composite of the restrictions. -/
@[stacks 01NN "graded rings of local sections"]
public theorem resRingHom_comp {U V W : S.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    A.resRingHom (hUV.trans hVW) = (A.resRingHom hUV).comp (A.resRingHom hVW) := by
  refine A.resRingHom_ext fun n y => ?_
  rw [A.resRingHom_of, RingHom.comp_apply, A.resRingHom_of, A.resRingHom_of]
  congr 1
  rw [A.resPiece_apply, A.resPiece_apply, A.resPiece_apply, ← Functor.map_comp_apply]
  rfl

/-- Restriction is compatible with the structure maps from the functions on the opens. -/
@[stacks 01NN "graded rings of local sections"]
public theorem resRingHom_strHom {U V : S.Opens} (h : U ≤ V) (r : Γ(S, V)) :
    A.resRingHom h (A.strHom V r) = A.strHom U (S.presheaf.map (homOfLE h).op r) := by
  rw [A.strHom_apply, A.resRingHom_of, A.resPiece_smul, A.resPiece_one, A.strHom_apply]

/-- Restriction, read on the homogeneous components. -/
public theorem resRingHom_apply {U V : S.Opens} (h : U ≤ V) (w : A.sectionRing V) (n : ℕ) :
    A.resRingHom h w n = A.resPiece h n (w n) := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of m y =>
    rw [A.resRingHom_of, DirectSum.of_apply, DirectSum.of_apply]
    rcases eq_or_ne m n with rfl | hmn
    · simp
    · simp [hmn]
  | add x y hx hy => rw [map_add]; simp [hx, hy]

/-- Restriction of the graded rings of sections, as a graded ring homomorphism. -/
public noncomputable def res {U V : S.Opens} (h : U ≤ V) : A.grading V →+*ᵍ A.grading U where
  __ := A.resRingHom h
  map_mem := fun {_ _} hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (A.resRingHom_of h y).symm⟩

/-- The ring homomorphism underlying `res` is `resRingHom`. -/
public theorem res_toRingHom {U V : S.Opens} (h : U ≤ V) :
    (A.res h).toRingHom = A.resRingHom h := rfl

/-! ### Quasi-coherence and the localization property -/

variable {U V : S.Opens}

/-- Quasi-coherence in one degree: the localization property of `restrictₗ`, stated with powers of
`f` in place of elements of `Submonoid.powers f`. -/
private theorem resPiece_localization (A : SheafGradedAlgebra S) (hU : IsAffineOpen U)
    (f : Γ(S, U)) (hV : V = S.basicOpen f) (hVU : V ≤ U) (n : ℕ) :
    (∀ y : A.sectionPieces V n, ∃ (a : A.sectionPieces U n) (k : ℕ),
      S.presheaf.map (homOfLE hVU).op (f ^ k) • y = A.resPiece hVU n a) ∧
    (∀ a : A.sectionPieces U n, A.resPiece hVU n a = 0 → ∃ k : ℕ, f ^ k • a = 0) := by
  let := moduleOfLE (A.piece (n : ℤ)) hVU
  have := isLocalizedModule_restrictₗ (A.piece (n : ℤ)) hU f hV hVU
  refine ⟨fun y => ?_, fun a ha => ?_⟩
  · obtain ⟨⟨a, m⟩, hm⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (restrictₗ (A.piece (n : ℤ)) hVU) y
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
    exact ⟨a, k, by rw [hk]; exact hm⟩
  · obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers f) (f := restrictₗ (A.piece (n : ℤ)) hVU) (x₁ := a) (x₂ := 0)
      (by rw [map_zero]; exact ha)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    exact ⟨k, by rw [hk]; exact hc.trans (smul_zero _)⟩

/-- **Degreewise surjectivity.** A homogeneous section over a basic open becomes, after
multiplication by a power of `f`, the restriction of a homogeneous section of the *same*
degree. -/
public theorem exists_resPiece_eq (hU : IsAffineOpen U) (f : Γ(S, U)) (hV : V = S.basicOpen f)
    (hVU : V ≤ U) (n : ℕ) (y : A.sectionPieces V n) :
    ∃ (a : A.sectionPieces U n) (k : ℕ),
      S.presheaf.map (homOfLE hVU).op (f ^ k) • y = A.resPiece hVU n a :=
  (resPiece_localization A hU f hV hVU n).1 y

/-- **Degreewise annihilation.** A homogeneous section whose restriction to a basic open
vanishes is killed by a power of `f`. -/
public theorem exists_pow_smul_eq_zero (hU : IsAffineOpen U) (f : Γ(S, U))
    (hV : V = S.basicOpen f) (hVU : V ≤ U) (n : ℕ) (a : A.sectionPieces U n)
    (ha : A.resPiece hVU n a = 0) : ∃ k : ℕ, f ^ k • a = 0 :=
  (resPiece_localization A hU f hV hVU n).2 a ha

/-- Every section of the graded ring of sections vanishes outside a finite set of degrees. -/
public theorem exists_finset_support (w : A.sectionRing U) :
    ∃ s : Finset ℕ, ∀ n, n ∉ s → w n = 0 := by
  induction w using DirectSum.induction_on with
  | zero => exact ⟨∅, fun _ _ => rfl⟩
  | of m y =>
    refine ⟨{m}, fun n hn => ?_⟩
    rw [DirectSum.of_apply, dite_eq_right_iff]
    exact fun hmn => absurd (hmn ▸ Finset.mem_singleton_self m) hn
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun n hn => ?_⟩
    rw [DFinsupp.add_apply, hs n fun hns => hn (Finset.mem_union_left _ hns),
      ht n fun hnt => hn (Finset.mem_union_right _ hnt), add_zero]

/-- A section of the graded ring of sections that restricts to zero on a basic open is killed by
a power of the degree-`0` section attached to `f`. -/
public theorem exists_pow_strHom_mul_eq_zero (hU : IsAffineOpen U) (f : Γ(S, U))
    (hV : V = S.basicOpen f) (hVU : V ≤ U) (w : A.sectionRing U)
    (hw : A.resRingHom hVU w = 0) : ∃ k : ℕ, A.strHom U (f ^ k) * w = 0 := by
  have hcomp : ∀ n : ℕ, ∃ k : ℕ, f ^ k • w n = 0 := by
    intro n
    refine A.exists_pow_smul_eq_zero hU f hV hVU n (w n) ?_
    rw [← A.resRingHom_apply hVU w n, hw]
    rfl
  choose κ hκ using hcomp
  obtain ⟨s, hs⟩ := A.exists_finset_support w
  refine ⟨s.sup κ, ?_⟩
  ext n
  rw [A.strHom_mul_apply, DFinsupp.zero_apply]
  by_cases hn : n ∈ s
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := κ) hn)
    rw [hd, pow_add, _root_.mul_comm (f ^ κ n) (f ^ d), mul_smul, hκ n, smul_zero]
  · rw [hs n hn, smul_zero]

/-- **The localization property of Situation 01NN.** For an affine open `U` of `S` and
`f : 𝒪_S(U)`, the graded ring of sections of `A` over the basic open `D(f)` is the localization
of the graded ring of sections over `U` away from the degree-`0` section attached to `f`.

This is where quasi-coherence of the homogeneous pieces is used, through
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`. -/
@[ega "II 3.2.1" "special case"]
public theorem isLocalization_strHom (hU : IsAffineOpen U) (f : Γ(S, U))
    (hV : V = S.basicOpen f) (hVU : V ≤ U) :
    letI := (A.resRingHom hVU).toAlgebra
    IsLocalization.Away (A.strHom U f) (A.sectionRing V) := by
  let := (A.resRingHom hVU).toAlgebra
  have halg : ∀ x : A.sectionRing U,
      algebraMap (A.sectionRing U) (A.sectionRing V) x = A.resRingHom hVU x := fun _ => rfl
  have hfu : IsUnit (S.presheaf.map (homOfLE hVU).op f) := by
    subst hV
    exact RingedSpace.isUnit_res_basicOpen _ f
  have hsurj : ∀ z : A.sectionRing V, ∃ (x : A.sectionRing U) (k : ℕ),
      z * A.resRingHom hVU (A.strHom U f ^ k) = A.resRingHom hVU x := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | of n y =>
      obtain ⟨a, k, hak⟩ := A.exists_resPiece_eq hU f hV hVU n y
      refine ⟨DirectSum.of (A.sectionPieces U) n a, k, ?_⟩
      rw [← map_pow, A.resRingHom_strHom,
        _root_.mul_comm (DirectSum.of (A.sectionPieces V) n y), A.strHom_mul_of, hak,
        A.resRingHom_of]
    | add z w hz hw =>
      obtain ⟨x, k, hk⟩ := hz
      obtain ⟨y, l, hl⟩ := hw
      refine ⟨x * A.strHom U f ^ l + y * A.strHom U f ^ k, k + l, ?_⟩
      rw [map_add, map_mul, map_mul, ← hk, ← hl, pow_add (A.strHom U f) k l, map_mul]
      ring
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, k, rfl⟩
    rw [halg, map_pow, A.resRingHom_strHom]
    exact (hfu.map (A.strHom V)).pow k
  · intro z
    obtain ⟨x, k, hk⟩ := hsurj z
    exact ⟨⟨x, A.strHom U f ^ k, k, rfl⟩, by rw [halg, halg]; exact hk⟩
  · intro x y hxy
    rw [halg, halg] at hxy
    obtain ⟨k, hk⟩ := A.exists_pow_strHom_mul_eq_zero hU f hV hVU (x - y)
      (by rw [map_sub, hxy, sub_self])
    refine ⟨⟨A.strHom U f ^ k, k, rfl⟩, ?_⟩
    rw [map_pow] at hk
    exact sub_eq_zero.mp (by rw [← mul_sub]; exact hk)

/-! ### The bridge -/

/-- **The bridge of Situation 01NN.** Sheaf-level graded algebra data on a scheme `S` gives a
quasi-coherent graded `𝒪_S`-algebra in the affine-open form that the relative Proj construction
consumes. -/
public noncomputable def toGradedAlgebra : RelativeProj.GradedAlgebra S where
  ring U := CommRingCat.of (A.sectionRing U.toOpens)
  grading U := A.grading U.toOpens
  gradedRing U := A.instGradedRing U.toOpens
  str U := CommRingCat.ofHom (A.strHom U.toOpens)
  str_mem U r := A.strHom_mem U.toOpens r
  res h := A.res h
  res_id U := by
    refine GradedRingHom.ext fun x => ?_
    change A.resRingHom (le_refl U.toOpens) x = x
    rw [A.resRingHom_id]
    rfl
  res_comp hUV hVW := by
    refine GradedRingHom.ext fun x => ?_
    change A.resRingHom (hUV.trans hVW) x = A.resRingHom hUV (A.resRingHom hVW x)
    rw [A.resRingHom_comp hUV hVW]
    rfl
  res_str h r := A.resRingHom_strHom h r
  isLocalization U f := A.isLocalization_strHom U.2 f rfl (S.basicOpen_le f)

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
