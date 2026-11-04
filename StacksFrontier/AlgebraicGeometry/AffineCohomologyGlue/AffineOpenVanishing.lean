module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.CategoryTheory.CechReindex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher cohomology of a quasi-coherent module on an affine open

Let `X` be a scheme, `F` a quasi-coherent `𝒪_X`-module and `U ⊆ X` an affine open. Then
`Hᵖ(U, F) = 0` for every `p > 0`. This is [Stacks, Tag 01XB].

The proof is the one in the source, and both of its halves are already available:

* [Stacks, Tag 01EW] (`Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis`)
  reduces the vanishing of sheaf cohomology over the members of a basis `B` to the vanishing of
  Čech cohomology for a collection `Cov` of coverings, provided the finite intersections
  occurring in the Čech complexes of the coverings in `Cov` again lie in `B` and provided every
  covering of a member of `B` is refined by one in `Cov`.
* [Stacks, Tag 01X9] (`Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover`)
  supplies the Čech vanishing for the finite standard coverings of an affine open by basic
  opens.

So `B` is the set of affine opens and `Cov` the set of finite standard coverings, and what this
file owes is the verification of the hypotheses of the first from the second. Two of the three
are formal; the third, cofinality, is the only one with content and is
`exists_standardCover_refines`.

## Main definitions

* `Stacks.Cohomology.AffineOpen.standardCovers`: the collection `Cov`, the finite standard open
  coverings of the affine opens of `X`.

## Main results

* `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen` is [Stacks, Tag 01XB]:
  `Hᵖ(U, F) = 0` for `p > 0`, `F` quasi-coherent and `U` an affine open.
* `Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine`: the case `U = ⊤` of an affine
  scheme.
* `Stacks.Cohomology.AffineOpen.exists_standardCover_refines`: every open covering of an affine
  open is refined by a finite standard one. This is the cofinality hypothesis of
  [Stacks, Tag 01EW], and the only hypothesis of it with mathematical content.
* `Stacks.Cohomology.AffineOpen.standardCovers_mem_affineOpens`: the members of a finite standard
  covering, and the finite intersections occurring in its Čech complex, are affine opens.
* `Stacks.Cohomology.AffineOpen.cechCohomologyIsZero_of_mem_standardCovers`: the Čech vanishing
  hypothesis of [Stacks, Tag 01EW] for the finite standard coverings.

## Implementation notes

**The reindexing.** `Stacks.Cohomology.Basis.OpenCover` requires its index type to live in the
universe of the ambient space, while [Stacks, Tag 01X9] is stated for a family indexed by
`Fin n : Type 0`. The two Čech complexes are products over different index types and are not
interchangeable, so `cechCohomologyIsZero_of_mem_standardCovers` goes through
`Stacks.CategoryTheory.CechReindex.isZero_homology_of_reindex`. Accordingly a covering is
recorded as belonging to `standardCovers` together with an *equivalence* of its index type with
some `Fin n`, rather than with an index type that is literally `Fin n`; the coverings built in
`exists_standardCover_refines` use `ULift (Fin n)` and `Equiv.ulift`.

**Universes.** [Stacks, Tag 01EW] carries the module universe independently of the universe of
the space, as `AddCommGrpCat.{max u w}`, so applying it to a scheme requires solving
`max u w = u`. The universe arguments of
`Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis` are therefore given
explicitly as `.{u, u, u}` rather than left to unification. The three instances it needs —
`HasSheafify`, `GrothendieckTopology.WEqualsLocallyBijective` and `EnoughInjectives` for
`SheafOfModules.{u} X.ringCatSheaf` — are all found by instance search at the scheme's own
universe; no `letI` is required.

**The cofinality argument.** Given a covering `V` of the affine open `U`, the sections
`f : Γ(X, U)` whose ambient basic open `X.basicOpen f` is contained in some member of `V` have
basic opens covering `U`: this is `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` applied at
each point. By `AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff` those sections
generate the unit ideal, and `Ideal.span_eq_top_iff_finite` cuts the generating set down to a
finite one — this is where quasi-compactness of the affine open enters, in its algebraic form.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.CategoryTheory
open Stacks.Cohomology Stacks.Cohomology.Basis
open Stacks.RingTheory.CechAcyclicity

universe u

namespace Stacks.Cohomology.AffineOpen

variable (X : Scheme.{u})

/-- **The finite standard open coverings of the affine opens of `X`.** A cover belongs to this
collection when its carrier is an affine open `U` and its members are the ambient basic opens
`X.basicOpen (g i)` of a finite family `g` of sections over `U` whose basic opens cover
`Spec Γ(X, U)`, read along an equivalence of its index type with `Fin n`.

The equivalence is part of the data because the index type of a
`Stacks.Cohomology.Basis.OpenCover` must live in the universe of the space, whereas the family
`g` is indexed by `Fin n`; see the implementation notes. -/
def standardCovers : Set (OpenCover ↥X) :=
  {W | IsAffineOpen W.carrier ∧ ∃ (n : ℕ) (g : Fin n → Γ(X, W.carrier)) (e : W.ι ≃ Fin n),
    PrimeSpectrum.IsStandardOpenCoverOfSpectrum g ∧ W.obj = fun i ↦ X.basicOpen (g (e i))}

/-- **The members and the Čech intersections of a finite standard covering are affine opens.**
The members are the basic opens `X.basicOpen (g i)`, and the intersection selected by a tuple is
the basic open of the product of the corresponding sections, by
`Stacks.Cohomology.Cech.basicOpen_tupleProd`. This is the hypothesis `hCovBasis` of
[Stacks, Tag 01EW]. -/
theorem standardCovers_mem_affineOpens {W : OpenCover ↥X} (hW : W ∈ standardCovers X) :
    W.carrier ∈ X.affineOpens ∧ (∀ i, W.obj i ∈ X.affineOpens) ∧
      ∀ (p : ℕ) (s : Fin (p + 1) → W.ι), (⨅ k, W.obj (s k)) ∈ X.affineOpens := by
  obtain ⟨hU, n, g, e, -, hobj⟩ := hW
  refine ⟨hU, fun i ↦ ?_, fun p s ↦ ?_⟩
  · show IsAffineOpen (W.obj i)
    rw [hobj]
    exact hU.basicOpen _
  · show IsAffineOpen (⨅ k, W.obj (s k))
    rw [hobj, ← Cech.basicOpen_tupleProd g fun k ↦ e (s k)]
    exact hU.basicOpen _

/-- **Every open covering of an affine open is refined by a finite standard one.** This is the
cofinality hypothesis `hCovCofinal` of [Stacks, Tag 01EW], and the only hypothesis of it with
mathematical content.

Each point of the affine open `U` lies in some member of the given covering `V`, hence — by
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` — in a basic open of `U` contained in that
member. Those basic opens cover `U`, so the corresponding sections generate the unit ideal of
`Γ(X, U)`, and finitely many of them already do. The basic opens of such a finite subfamily are
the required refinement. -/
theorem exists_standardCover_refines (U : X.Opens) (hU : IsAffineOpen U)
    (V : OpenCover ↥X) (hV : V.carrier = U) :
    ∃ W ∈ standardCovers X, W.carrier = U ∧ W.Refines V := by
  classical
  -- The sections of `U` whose basic open is contained in a member of `V`.
  set S : Set Γ(X, U) := {f | ∃ j, X.basicOpen f ≤ V.obj j}
  have hcover : U ≤ ⨆ f : S, X.basicOpen (f : Γ(X, U)) := by
    intro x hx
    have hxV : x ∈ ⨆ j, V.obj j := by rw [V.iSup_eq, hV]; exact hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxV
    obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basicOpen_le (⟨x, hj⟩ : V.obj j) hx
    exact Opens.mem_iSup.mpr ⟨⟨f, ⟨j, hf₁⟩⟩, hf₂⟩
  obtain ⟨t, htS, ht⟩ :=
    (Ideal.span_eq_top_iff_finite S).mp (hU.self_le_iSup_basicOpen_iff.mp hcover)
  -- Enumerate the finite generating set.
  set g : Fin t.card → Γ(X, U) := fun i ↦ (t.equivFin.symm i : Γ(X, U))
  have hmem : ∀ i, g i ∈ t := fun i ↦ (t.equivFin.symm i).2
  have hrange : Set.range g = (t : Set Γ(X, U)) :=
    (EquivLike.range_comp (Subtype.val : t → Γ(X, U)) t.equivFin.symm).trans Subtype.range_coe
  have hgstd : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g :=
    show ⨆ i, PrimeSpectrum.basicOpen (g i) = PrimeSpectrum.basicOpen (1 : Γ(X, U)) from
      (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (hrange ▸ ht)).trans
        PrimeSpectrum.basicOpen_one.symm
  refine ⟨{ ι := ULift.{u} (Fin t.card)
            carrier := U
            obj := fun i ↦ X.basicOpen (g i.down)
            iSup_eq := ?_ },
          ⟨hU, t.card, g, Equiv.ulift, hgstd, rfl⟩, rfl, hV.symm, fun i ↦ ?_⟩
  · refine le_antisymm (iSup_le fun i ↦ X.basicOpen_le _) ?_
    refine le_trans (hU.self_le_iSup_basicOpen_iff.mpr (hrange ▸ ht)) (iSup_le ?_)
    rintro ⟨f, hf⟩
    obtain ⟨i, rfl⟩ : ∃ i, g i = f := hf
    exact le_iSup_of_le (ULift.up i) le_rfl
  · exact htS (hmem i.down)

/-- **Positive-degree Čech cohomology of a quasi-coherent module vanishes for every finite
standard covering.** This is the hypothesis `hCech` of [Stacks, Tag 01EW]; it is
[Stacks, Tag 01X9] transported along the reindexing of the index type of the covering. -/
theorem cechCohomologyIsZero_of_mem_standardCovers (F : X.Modules) [F.IsQuasicoherent]
    {W : OpenCover ↥X} (hW : W ∈ standardCovers X) (p : ℕ) (hp : 0 < p) :
    CechCohomologyIsZero.{u, u, u} X.ringCatSheaf F W p := by
  obtain ⟨hU, n, g, e, hgstd, hobj⟩ := hW
  show IsZero (((cechComplexFunctor W.obj).obj
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj).homology p)
  rw [hobj]
  exact CechReindex.isZero_homology_of_reindex (fun i : Fin n ↦ X.basicOpen (g i)) _ e p
    (Cech.isZero_cechCohomology_of_isStandardOpenCover X F W.carrier hU g hgstd p hp)

-- Stacks 01XB, the higher cohomology of a quasi-coherent module on an affine open, is
-- `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`.  This is an alias spelling of that
-- declaration, not a second copy of it.
export Stacks.Cohomology.Cech (isZero_hgroup_of_isAffineOpen)

/-- **The higher cohomology of a quasi-coherent module on an affine scheme vanishes.** The case
`U = ⊤` of [Stacks, Tag 01XB]. -/
theorem isZero_hgroup_of_isAffine [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p) : IsZero (Hgroup X.ringCatSheaf ⊤ p F) :=
  Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊤ (isAffineOpen_top X) p hp

end Stacks.Cohomology.AffineOpen

end
