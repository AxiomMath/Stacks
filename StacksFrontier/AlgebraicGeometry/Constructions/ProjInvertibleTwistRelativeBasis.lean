module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativePowers
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Trivialization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# Tag 02NC over a base scheme: a basis of the topology of the base trivializing `ℒ`

Tag 02NC's proof is *"choose an open covering of `S` such that `ℒ` is trivialized over the pieces
and glue the corresponding maps"*. The glueing tool the development uses,
`AlgebraicGeometry.Scheme.BasisGluingData.existsUnique_isoOver` (Tag 01LH, uniqueness), asks for
a **basis** of the topology of `S` rather than a covering, so that the chart transitions of the
relative homogeneous spectra are available on every nesting of two members. This file produces
that basis: the affine opens of `S` over which `ℒ` carries a section whose powers trivialize the
powers of `ℒ`.

Invertibility of `ℒ` gives a *covering* by trivializing opens and no more; what makes the
trivializing affine opens a basis is that a trivialization **restricts**, so inside any open and
around any point one may shrink a trivializing open to an affine one.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.trivializingOpens`: the set of affine opens
  of the base carrying a section of `ℒ` that trivializes it there.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.powSecAt_one_eq`: the first power of a local
  section of `ℒ` is the section itself. This is what makes a trivializing *section* out of a
  trivializing *isomorphism*: the canonical generator of any trivialization of `ℒ` over `V` is a
  section whose first power trivializes `ℒ` there.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.trivializesPower_of_le`: a trivializing
  section restricts to a trivializing section.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isBasis_trivializingOpens`: **the trivializing
  affine opens form a basis of the topology of the base.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.exists_trivializesPower_of_mem`: a member of
  the basis carries a section whose powers trivialize the powers of `ℒ` in **every** positive
  degree, which is the hypothesis the chart comparison of Tag 02NC takes.

## Implementation notes

Three spellings of the same trivialization occur and are crossed in term mode, each pair being
equal by `rfl`:

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.TrivializesPower` is phrased with
  `Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf`, and the canonical generator of
  the trivialization is `Stacks.SheafOfModules.TensorGenerator.generator`.
* `Stacks.SheafOfModules.overIsoRestrict` and its restriction law
  `Stacks.SheafOfModules.overIsoSection_restrict` are stated for a ringed space with the
  structure sheaf spelled `Stacks.SheafOfModules.structureSheaf`, and the generator spelled
  `Stacks.SheafOfModules.overIsoSection` — which is `generator` on the nose.
* `Stacks.SheafOfModules.Invertible.IsLocallyTrivial` names the ring sheaf through the module's
  own type.

An earlier note in this file family said that *nothing* in the tree assembles an
`TopologicalSpace.Opens.IsBasis` from a trivialization. That was only half right: the restriction
of a trivialization is `Stacks.SheafOfModules.overIsoRestrict`, with its generator law, and the
same basis argument is already carried out for a finite locally free module of rank `r` in
`Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.isBasis_trivializing`. What was missing is
this instance of it, for the degree-one tensor power, with the trivializing *section* extracted.

Local triviality of the tensor power is
`Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible` applied to
`Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower`; the two invertibility classes are
named at different spellings of the structure sheaf, which instance search does not cross, so the
application is explicit.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorGenerator

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-! ### The first power of a section is the section -/

/-- **The first power of a local section of the twisting module is the section itself.**

`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.powSecAt` in degree one is the product of the
unit of the Laurent algebra with the section, reindexed from degree `0 + 1` to degree `1`; the
unit is a left identity (`Stacks.SheafOfModules.TensorPower.mulBilinear_one_mul`) and the
reindexing is the identity up to the degree cast (`heq_reix`). -/
alias powSecAt_one_eq := powSecAt_one

/-- **The canonical generator of a trivialization of `ℒ` over an open trivializes `ℒ` there in
degree one.** So a trivializing *isomorphism* yields a trivializing *section*, which is the shape
the chart comparison of Tag 02NC consumes. -/
theorem trivializesPower_one_of_overIso {V : S.Opens}
    (e : (tp L 1).over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V)) :
    TrivializesPower L V (generator S.sheaf.obj S.ringCatSheaf.property V (tp L 1) e) 1 :=
  ⟨e, (powSecAt_one_eq L (op V) _).symm⟩

/-! ### Restriction -/

/-- **The canonical generator of a trivialization restricts to the canonical generator of the
restricted trivialization**, at the `Stacks.SheafOfModules.TensorGenerator.generator` spelling.
`Stacks.SheafOfModules.overIsoSection` is `generator` on the nose, so this is
`Stacks.SheafOfModules.overIsoSection_restrict` read at the other spelling. -/
theorem generator_overIsoRestrict {V W : S.Opens} (h : W ≤ V) (M : S.Modules)
    (e : M.over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V)) :
    generator S.sheaf.obj S.ringCatSheaf.property W M
        (Stacks.SheafOfModules.overIsoRestrict M h e) =
      M.val.map (homOfLE h).op (generator S.sheaf.obj S.ringCatSheaf.property V M e) :=
  (Stacks.SheafOfModules.overIsoSection_restrict M h e).symm

/-- **A trivializing section restricts to a trivializing section.** This is what makes the
trivializing opens a basis rather than merely a covering, and it is also what lets the chart
comparisons of Tag 02NC be compared on a nesting of two members of the basis: the comparison over
the smaller member attached to the restricted section is the one
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projInclusionMap_comp_projMap_psiSectionAt`
speaks about. -/
theorem trivializesPower_of_le {V W : S.Opens} (h : W ≤ V) {x : (tp L 1).val.obj (op V)}
    (hx : TrivializesPower L V x 1) :
    TrivializesPower L W ((tp L 1).val.map (homOfLE h).op x) 1 := by
  obtain ⟨e, he⟩ := hx
  refine ⟨Stacks.SheafOfModules.overIsoRestrict (tp L 1) h e, ?_⟩
  refine (generator_overIsoRestrict h (tp L 1) e).trans ?_
  refine ((congrArg ((tp L 1).val.map (homOfLE h).op) he).trans ?_)
  exact (congrArg ((tp L 1).val.map (homOfLE h).op) (powSecAt_one_eq L (op V) x)).trans
    (powSecAt_one_eq L (op W) ((tp L 1).val.map (homOfLE h).op x)).symm

/-! ### The basis -/

/-- **The affine opens of the base over which the twisting module is trivialized by a section.**

This is the index set of the glueing of Tag 02NC: over each of these the comparison of the tag is
defined, is an isomorphism of homogeneous spectra, and is a morphism over the open. -/
def trivializingOpens : Set S.Opens :=
  {V : S.Opens | IsAffineOpen V ∧ ∃ x : (tp L 1).val.obj (op V), TrivializesPower L V x 1}

/-- A member of the basis is an affine open. -/
theorem isAffineOpen_of_mem_trivializingOpens {V : S.Opens} (hV : V ∈ trivializingOpens L) :
    IsAffineOpen V := hV.1

/-- **A member of the basis carries a section whose powers trivialize the powers of `ℒ` in every
positive degree.** The degree-one trivialization of the definition suffices, by
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.trivializesPower_of_one`; this is the exact
hypothesis of `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt`. -/
theorem exists_trivializesPower_of_mem {V : S.Opens} (hV : V ∈ trivializingOpens L) :
    ∃ x : (tp L 1).val.obj (op V), ∀ d : ℕ, 0 < d → TrivializesPower L V x d :=
  ⟨hV.2.choose, trivializesPower_of_one L hV.2.choose_spec⟩

/-- **The degree-one tensor power of an invertible module on a scheme is locally trivial.** -/
theorem isLocallyTrivial_tp (n : ℤ) :
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial (tp L n) :=
  @Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible S.toRingedSpace (tp L n)
    inferInstance
    (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower S.sheaf.obj
      S.ringCatSheaf.property L n)

/-- **The affine opens of the base trivializing `ℒ` form a basis of its topology.**

`ℒ` is locally trivial, so every point has a trivializing neighbourhood; the affine opens are a
basis, so inside the intersection of that neighbourhood with any given open there is an affine
open around the point; and a trivialization restricts to it. This is the basis that Tag 02NC's
glueing runs over. -/
theorem isBasis_trivializingOpens : Opens.IsBasis (trivializingOpens L) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U s hs
  obtain ⟨I, Y, hY, e⟩ :=
    (isLocallyTrivial_tp L 1).exists_trivializing_cover
  have hcov : iSup Y = ⊤ := (Opens.coversTop_iff _ Y).mp hY
  obtain ⟨i, hi⟩ : ∃ i, s ∈ Y i := by
    refine Opens.mem_iSup.mp ?_
    rw [hcov]
    exact Opens.mem_top s
  obtain ⟨W, hWmem, hsW, hWle⟩ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (U := U ⊓ Y i) (x := s) ⟨hs, hi⟩
  refine ⟨W, ⟨hWmem, ?_⟩, hsW, hWle.trans inf_le_left⟩
  refine ⟨generator S.sheaf.obj S.ringCatSheaf.property W (tp L 1)
    (Stacks.SheafOfModules.overIsoRestrict (tp L 1) (hWle.trans inf_le_right) (e i).some), ?_⟩
  exact trivializesPower_one_of_overIso L _

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
