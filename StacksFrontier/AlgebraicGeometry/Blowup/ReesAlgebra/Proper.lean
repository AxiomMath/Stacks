module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionRings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properness of the blowup morphism

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on it whose ideal is finitely generated
on every affine open. The blowup morphism `AlgebraicGeometry.blowUpToBase` is then proper.

The blowup is the relative `Proj` of the Rees algebra, and
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionRings.lean` reduces properness of the
structure morphism of a relative `Proj` to two facts about the graded ring of sections over each
affine open `U` of the base: that `Γ(X, U)` is carried isomorphically onto the degree-zero part,
and that the section ring is a finite-type algebra over that degree-zero part. This file supplies
both for the Rees algebra, from the affine-local identification
`AlgebraicGeometry.ReesAlgebraData.pieceEquiv` of its degree-`n` piece with `Iⁿ`.

Each of the two facts is one line of mathematics read through that identification. The degree-zero
piece is `I⁰ = Γ(X, U)`, so multiplying the algebra unit by a function on the base is a bijection
onto the degree-zero sections; and `Iⁿ⁺¹ = I · Iⁿ` says the algebra is generated in degree one, so
a finite generating set of `I` over `U` gives a finite spanning set in degree one.

## Main results

* `AlgebraicGeometry.isIso_sectionRingZeroMap_reesSituation`: the degree-zero identification of the
  chart of the Rees algebra over an affine open is an isomorphism.
* `AlgebraicGeometry.ReesAlgebraData.isGeneratedInDegreeOne` and
  `AlgebraicGeometry.reesSituation_isGeneratedInDegreeOne`: the Rees algebra is generated in degree
  one over every affine open.
* `AlgebraicGeometry.finiteType_sectionRing_reesSituation`: the section ring of the Rees algebra
  over an affine open is a finite-type algebra over its degree-zero part, as soon as the ideal is
  finitely generated there.
* `AlgebraicGeometry.isProper_blowUpToBase_of_fg`: **the blowup morphism is proper** when the ideal
  is finitely generated on every affine open.
* `AlgebraicGeometry.isProper_blowUpToBase`: the same for a locally Noetherian scheme, where finite
  generation is automatic.

## Implementation notes

The sections of the structure sheaf appear with two carriers: `Γ(X, U)`, a `CommRingCat`, which is
what an ideal of the ideal sheaf lives in, and `X.ringCatSheaf.obj.obj (op U)`, a `RingCat`, which
is what acts on a homogeneous piece. They are definitionally equal and `ReesAlgebraData.pieceEquiv`
is stated across the two with a `show`, so the transfers below do the same rather than inserting a
coercion.

`AlgebraicGeometry.ReesAlgebraData.pieceEquiv` is only an `AddEquiv`, with multiplicativity,
compatibility with the unit and compatibility with the base action recorded as separate fields. The
two transfer arguments are therefore phrased as "every element of the target is the image of an
element of the source subgroup", which needs only additivity and injectivity, rather than as
transport along a graded ring isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The degree-zero identification -/

/-- Multiplying the unit of the Rees algebra by a function on the base is a bijection onto the
degree-zero homogeneous sections over an affine open: the degree-zero piece is `I⁰`, the unit
section corresponds to `1`, and the base action corresponds to multiplication. -/
theorem reesSituation_bijective_smul_one (U : X.affineOpens) :
    Function.Bijective
      (fun r : X.ringCatSheaf.obj.obj (op U.1) =>
        r • (reesSituation I).algebra.one.eval (op U.1)) := by
  set e := (reesAlgebraData I).pieceEquiv 0 (le_refl 0) U with he
  have key (r : X.ringCatSheaf.obj.obj (op U.1)) :
      ((e (r • (reesSituation I).algebra.one.eval (op U.1)) :
        ↥(I.ideal U ^ (0 : ℤ).toNat)) : X.presheaf.obj (op U.1)) =
        (show X.presheaf.obj (op U.1) from r) := by
    rw [he, (reesAlgebraData I).pieceEquiv_smul 0 (le_refl 0) U r
      ((reesAlgebraData I).algebra.one.eval (op U.1)),
      (reesAlgebraData I).pieceEquiv_one U, mul_one]
  refine ⟨fun r r' hr => ?_, fun a => ?_⟩
  · have := congrArg (fun x => ((e x : ↥(I.ideal U ^ (0 : ℤ).toNat)) :
      X.presheaf.obj (op U.1))) hr
    rwa [key r, key r'] at this
  · exact ⟨(e a : X.presheaf.obj (op U.1)), e.injective (Subtype.ext (key _))⟩

/-- The degree-zero identification of the chart of the Rees algebra over an affine open is an
isomorphism. This is the hypothesis `hb` of the transfer results of
`StacksFrontier/AlgebraicGeometry/RelativeProj/LocalAtBase.lean`. -/
theorem isIso_sectionRingZeroMap_reesSituation (U : X.affineOpens) :
    IsIso ((reesSituation I).sectionRingZeroMap U.1) :=
  (reesSituation I).isIso_sectionRingZeroMap U.1 (reesSituation_bijective_smul_one I U)

/-! ### Generation in degree one -/

/-- An additive subgroup of `M` all of whose elements' images cover an ideal `J` under an additive
equivalence `M ≃+ J` is everything. -/
private theorem mem_of_forall_exists_coe_eq {M A : Type*} [AddCommGroup M] [CommRing A]
    {J : Ideal A} (e : M ≃+ J) (P : AddSubgroup M) (h : ∀ v ∈ J, ∃ p ∈ P, (e p : A) = v)
    (z : M) : z ∈ P := by
  obtain ⟨p, hp, hpz⟩ := h _ (e z).2
  exact e.injective (Subtype.ext hpz) ▸ hp

/-- **A Rees algebra datum of a quasi-coherent ideal sheaf is generated in degree one over an
affine open.** Through `AlgebraicGeometry.ReesAlgebraData.pieceEquiv` this is `Iⁿ⁺¹ = I · Iⁿ`, so
every element of degree `n + 1` is a sum of products of a degree-one section with a degree-`n`
one.

Nothing in the argument is about the particular datum `AlgebraicGeometry.reesAlgebraData`, which
is chosen opaquely: it runs on the affine-local identification alone. Stating it for an arbitrary
datum is therefore free, and it is what lets the transparently constructed
`Stacks.Blowup.reesAlgebraData` be fed to it too — needed to put generation in degree one on the
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` substrate. -/
theorem ReesAlgebraData.isGeneratedInDegreeOne (d : ReesAlgebraData I) (U : X.affineOpens) :
    d.algebra.IsGeneratedInDegreeOne (op U.1) := by
  intro n P hP
  have hn1 : ((1 : ℤ) + (n : ℤ)).toNat = n + 1 := by omega
  set e1 := d.pieceEquiv 1 (by norm_num) U with he1
  set en := d.pieceEquiv (n : ℤ) (by positivity) U with hen
  set e := d.pieceEquiv ((1 : ℤ) + (n : ℤ)) (by positivity) U with he
  refine (AddSubgroup.eq_top_iff' _).mpr (mem_of_forall_exists_coe_eq e P fun v hv => ?_)
  rw [hn1, pow_succ', ← pow_one (I.ideal U)] at hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro a ha b hb
    refine ⟨(d.algebra.mul 1 (n : ℤ)).app (op U.1)
      (e1.symm ⟨a, ha⟩) (en.symm ⟨b, by simpa using hb⟩), hP _ _, ?_⟩
    rw [he, d.pieceEquiv_mul 1 (n : ℤ) (by norm_num) (by positivity) U, he1, hen]
    simp
  · rintro x y ⟨p, hp, hpx⟩ ⟨q, hq, hqy⟩
    exact ⟨p + q, AddSubgroup.add_mem _ hp hq, by rw [map_add]; push_cast [hpx, hqy]; ring⟩

/-- **The Rees algebra is generated in degree one over an affine open.** Through
`AlgebraicGeometry.ReesAlgebraData.pieceEquiv` this is `Iⁿ⁺¹ = I · Iⁿ`, so every element of degree
`n + 1` is a sum of products of a degree-one section with a degree-`n` one. -/
theorem reesSituation_isGeneratedInDegreeOne (U : X.affineOpens) :
    (reesSituation I).algebra.IsGeneratedInDegreeOne (op U.1) :=
  ReesAlgebraData.isGeneratedInDegreeOne I (reesAlgebraData I) U

/-- A finite generating set of the ideal over an affine open gives a finite family of degree-one
homogeneous sections spanning the degree-one sections over the structure-sheaf sections. -/
theorem exists_finset_span_reesSituation_degreeOne (U : X.affineOpens)
    (hfg : (I.ideal U).FG) :
    ∃ g : Finset ((reesSituation I).sectionPieces U.1 1),
      Submodule.span (X.ringCatSheaf.obj.obj (op U.1))
        (g : Set ((reesSituation I).sectionPieces U.1 1)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := hfg
  set e1 := (reesAlgebraData I).pieceEquiv 1 (by norm_num) U with he1
  have hmem : ∀ a ∈ s, a ∈ I.ideal U ^ (1 : ℤ).toNat := fun a ha => by
    simpa using hs ▸ Submodule.subset_span ha
  set g : Finset ((reesSituation I).sectionPieces U.1 1) :=
    s.attach.image fun a => e1.symm ⟨a.1, hmem a.1 a.2⟩ with hg
  refine ⟨g, top_unique fun z _ => mem_of_forall_exists_coe_eq e1
    (Submodule.span (X.ringCatSheaf.obj.obj (op U.1))
      (g : Set ((reesSituation I).sectionPieces U.1 1))).toAddSubgroup (fun v hv => ?_) z⟩
  rw [Int.toNat_one, pow_one, ← hs] at hv
  induction hv using Submodule.span_induction with
  | mem a ha =>
      refine ⟨e1.symm ⟨a, hmem a ha⟩, Submodule.subset_span ?_, by simp⟩
      rw [hg]
      exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨p, hp, hpx⟩ := hx
      obtain ⟨q, hq, hqy⟩ := hy
      exact ⟨p + q, Submodule.add_mem _ hp hq, by rw [map_add]; push_cast [hpx, hqy]; ring⟩
  | smul r x _ hx =>
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨(show X.ringCatSheaf.obj.obj (op U.1) from r) • p,
        Submodule.smul_mem _ _ hp, ?_⟩
      rw [he1, (reesAlgebraData I).pieceEquiv_smul 1 (by norm_num) U
        (show X.ringCatSheaf.obj.obj (op U.1) from r) p, ← he1, hpx]
      exact (smul_eq_mul _ _).symm

/-- The section ring of the Rees algebra over an affine open is a finite-type algebra over its
degree-zero part, as soon as the ideal is finitely generated there. This is the hypothesis `hft`
of the transfer results of `StacksFrontier/AlgebraicGeometry/RelativeProj/LocalAtBase.lean`. -/
theorem finiteType_sectionRing_reesSituation (U : X.affineOpens) (hfg : (I.ideal U).FG) :
    Algebra.FiniteType ((reesSituation I).sectionRingGrading U.1 0)
      ((reesSituation I).sectionRing U.1) := by
  obtain ⟨g, hg⟩ := exists_finset_span_reesSituation_degreeOne I U hfg
  exact (reesSituation I).finiteType_sectionRing U.1
    (reesSituation_isGeneratedInDegreeOne I U) g hg

/-! ### Properness -/

/-- **The blowup morphism is proper** when the ideal sheaf is finitely generated on every affine
open. -/
theorem isProper_blowUpToBase_of_fg (hfg : ∀ U : X.affineOpens, (I.ideal U).FG) :
    IsProper (blowUpToBase I) :=
  (reesSituation I).isProper_relativeProjToBase
    (isIso_sectionRingZeroMap_reesSituation I)
    fun U => finiteType_sectionRing_reesSituation I U (hfg U)

/-- **The blowup morphism of a locally Noetherian scheme is proper.** Finite generation of the
ideal on an affine open is automatic there, and compactness of the whole space — the remaining
half of `AlgebraicGeometry.IsNoetherian` — is not needed. -/
@[ega "IV 19.4.10" "more general"]
instance isProper_blowUpToBase [IsLocallyNoetherian X] :
    IsProper (blowUpToBase I) :=
  isProper_blowUpToBase_of_fg I fun U =>
    have := IsLocallyNoetherian.component_noetherian U
    Ideal.fg_of_isNoetherianRing _

end AlgebraicGeometry

end
