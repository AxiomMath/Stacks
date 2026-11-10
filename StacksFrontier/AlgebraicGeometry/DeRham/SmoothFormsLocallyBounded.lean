module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocallyStrictlyPerfectComplex
import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator

/-!
# The relative de Rham complex of a smooth morphism is locally bounded

Let `f : X ⟶ Y` be a smooth morphism of schemes. The sheaf of relative differentials `Ω_{X/Y}`
is finite locally free ([Stacks, Tag 02G1]), so over an open neighbourhood `U` of any point of
`X` it is free on a finite index type `γ`; there the degree-`n` relative differential forms are
free on the `n`-element subsets of `γ`, of which there are none once `n` exceeds the cardinality
of `γ`. Hence `Ω^n_{X/Y}|_U = 0` for `n > #γ`, and the relative de Rham complex `Ω^•_{X/Y}` is
**locally bounded** in the sense of
`Stacks.SheafOfModules.OnSpace.IsLocallyBounded`.

This is the hypothesis `hF` of the projection formula
`relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent`
([Stacks, Tag 0FML] conclusion (4)) at the complex `Ω^•_{X/Y}`, which is the shape in which
[Stacks, Tag 0FMM] uses that conclusion.

**Local, not global.** The rank of `Ω_{X/Y}` is constant on connected components but may be
unbounded across them: for `Y = ⨆_{n} Spec k` and `X = ⨆_n 𝔸^n_k` the complex `Ω^•_{X/Y}` has
nonzero terms in every degree, so there is no global `Finset` of degrees outside which it
vanishes and `Stacks.SheafOfModules.OnSpace.isLocallyBounded_of_bound` does not apply. This is
exactly why conclusion (4) of Tag 0FML was proved at the locally bounded hypothesis.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isZero_relativeDifferentialForms_over_of_smooth`: **the
  local degree bound** — every point of `X` has an open neighbourhood `U` and a degree `N` with
  `Ω^n_{X/Y}|_U = 0` for every `n > N`.
* `Stacks.DeRhamDirectImage.isLocallyBounded_deRhamCochainComplex`: **`Ω^•_{X/Y}` is locally
  bounded**, as a complex of `f^{-1}𝒪_Y`-modules on `X`.
* `Stacks.SheafOfModules.isZero_restrictScalars_over_of_isZero_over`: restriction of scalars
  carries a module whose restriction to an open vanishes to one whose restriction to that open
  vanishes.

## Implementation notes

The local trivialisation is taken from the *local generators data* form of finite local freeness,
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, rather than from the open-subscheme form
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`: the generators data gives the
trivialisation of `Ω_{X/Y}` already restricted to the *slice site* over the open, which is the
shape `Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree` consumes, and which is also the
shape `Stacks.SheafOfModules.OnSpace.IsBoundedOn` asks its vanishing in. Going through the open
subscheme would mean crossing between the two descriptions twice for nothing.

The de Rham complex lives over `f^{-1}𝒪_Y` while its terms are exterior powers over `𝒪_X`, so
the vanishing has to be carried along restriction of scalars. That the two commute with
restriction to an open is not available in the tree in this form; it is proved here on sections,
where both sides have the same underlying abelian groups and the identity of one is the identity
of the other. The existing `Stacks.SheafOfModules.isZero_over_restrictScalars` is a different
statement: it concludes the vanishing from triviality of the *ring* of sections.

The degree bookkeeping crosses from the `ℕ`-indexed de Rham complex to the `ℤ`-indexed one the
derived category uses: the negative degrees vanish outright by
`HomologicalComplex.isZero_extend_X`, and the nonnegative ones are the `ℕ`-indexed terms by
`HomologicalComplex.extendXIso`.

## References

* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v w u₁ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{w}}

/-- **Restriction of scalars does not change the vanishing of a restriction to an open.** If the
restriction of a sheaf of `R'`-modules `M` to the site localised at `U` is a zero object, then so
is the restriction of the sheaf of `R`-modules `M|_R` obtained from it by restriction of scalars
along `α : R ⟶ R'`.

Both restrictions have the same modules of sections, and the identity morphism of one has the
same action on sections as the identity morphism of the other, so one identity vanishes exactly
when the other does.

This is not `Stacks.SheafOfModules.isZero_over_restrictScalars`, which concludes the same
vanishing from triviality of the ring of sections of `R'` over `U` and says nothing when the
module merely vanishes. -/
theorem isZero_restrictScalars_over_of_isZero_over (α : R ⟶ R')
    (M : _root_.SheafOfModules.{w} R') (U : C) (h : IsZero (M.over U)) :
    IsZero (((_root_.SheafOfModules.restrictScalars α).obj M).over U) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  ext V m
  exact congrArg (fun t : M.over U ⟶ M.over U => t.val.app V m) h

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The local degree bound on the relative forms of a smooth morphism.** Every point of `X` has
an open neighbourhood `U` and a degree `N` such that `Ω^n_{X/Y}|_U = 0` for every `n > N`.

The sheaf of relative differentials of a smooth morphism is finite locally free
([Stacks, Tag 02G1]), so the point lies in a member `U` of a cover over which `Ω_{X/Y}` is free
on a finite index type `γ`. There the degree-`n` exterior power is free on the `n`-element
subsets of `γ` (`Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree`), and there are no such
subsets once `n > #γ`, so `N = #γ` works.

The bound genuinely depends on the point: the rank of `Ω_{X/Y}` need not be bounded on `X`. -/
theorem exists_isZero_relativeDifferentialForms_over_of_smooth [Smooth f] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (N : ℕ), ∀ n : ℕ, N < n →
      IsZero ((Scheme.Hom.relativeDifferentialForms f (n : ℤ)).over U) := by
  classical
  have h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat (_root_.Opens.grothendieckTopology ↥X) X.sheaf)
      (Scheme.Hom.relativeDifferentials f) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  have hc := q.coversTop
  rw [_root_.Opens.coversTop_iff] at hc
  have hx : x ∈ ⨆ i, q.X i := by rw [hc]; trivial
  rw [Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  have : Finite ((q.generators i).I) := (hfin.isFiniteType i).finite
  let : LinearOrder ((q.generators i).I) := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨q.X i, hi, Nat.card ((q.generators i).I), fun n hn => ?_⟩
  have e : (Scheme.Hom.relativeDifferentials f).over (q.X i) ≅
      _root_.SheafOfModules.free
        (R := (Sheaf.toRingCat (_root_.Opens.grothendieckTopology ↥X) X.sheaf).over (q.X i))
        ((q.generators i).I) :=
    have := hq.isIso i
    (asIso (q.generators i).π).symm
  have hempty : IsEmpty ↥(Set.powersetCard ((q.generators i).I) n) :=
    Set.isEmpty_coe_sort.2 (Set.powersetCard.eq_empty_iff.2 hn)
  exact IsZero.of_iso
    (Stacks.SheafOfModules.isZero_free_of_isEmpty
      (R := (Sheaf.toRingCat (_root_.Opens.grothendieckTopology ↥X) X.sheaf).over (q.X i))
      ↥(Set.powersetCard ((q.generators i).I) n))
    (Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree
      (Scheme.Hom.deRhamAlgebras f) (q.X i) n ((q.generators i).I) e)

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRhamDirectImage

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The relative de Rham complex of a smooth morphism is locally bounded.** For `f : X ⟶ Y`
smooth, every point of `X` has an open neighbourhood outside finitely many degrees of which the
complex `Ω^•_{X/Y}` of `f^{-1}𝒪_Y`-modules vanishes.

Over such a neighbourhood the relative forms vanish above a degree `N`
(`AlgebraicGeometry.Scheme.Hom.exists_isZero_relativeDifferentialForms_over_of_smooth`), and the
`ℤ`-indexed complex vanishes in negative degrees because it is the extension by zero of the
`ℕ`-indexed one; so the degrees `0, …, N` are the only ones left.

This is the hypothesis `hF` of conclusion (4) of [Stacks, Tag 0FML] at the complex
`Ω^•_{X/Y}`. It is not deducible from a global bound: see the module documentation. -/
theorem isLocallyBounded_deRhamCochainComplex [Smooth f] :
    Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f)
      (deRhamCochainComplex f) := by
  classical
  intro x
  obtain ⟨U, hxU, N, hN⟩ :=
    Scheme.Hom.exists_isZero_relativeDifferentialForms_over_of_smooth f x
  refine ⟨U, hxU, (Finset.range (N + 1)).image (fun n : ℕ => (n : ℤ)), fun i hi => ?_⟩
  rcases lt_or_ge i 0 with hneg | hpos
  · exact Stacks.SheafOfModules.OnSpace.isZero_over_of_isZero (inverseImageBase f)
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
        (fun n => by simpa using (hneg.trans_le (Int.natCast_nonneg n)).ne')) U
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    have hn : N < n := by
      by_contra hcon
      exact hi (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)
    refine IsZero.of_iso ?_
      ((_root_.SheafOfModules.overFunctor (structureSheafRing (inverseImageBase f)) U).mapIso
        (HomologicalComplex.extendXIso
          (show CochainComplex (Modules (inverseImageBase f)) ℕ from Scheme.Hom.deRhamComplex f)
          ComplexShape.embeddingUpNat (i := n) rfl))
    exact Stacks.SheafOfModules.isZero_restrictScalars_over_of_isZero_over _ _ U (hN n hn)

end Stacks.DeRhamDirectImage

end
