module

public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.AffineBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniCommonZeroSet

/-!
# The hypotheses of the Bertini irreducibility theorem

This module states the hypotheses of [Stacks, Tag 0G4F] in the standing situation of the
Bertini theorems ([Stacks, Tag 0G47]) and reads them on trivializing affine charts. The
hypotheses are:

1. `X` is of finite type over `k`;
2. `X` is geometrically irreducible over `k`;
3. there are `v₁, v₂, v₃ ∈ V` and an irreducible component `Z` of `H_{v₂} ∩ H_{v₃}` with
   `Z ⊄ H_{v₁}` and `codim(Z, X) = 2`;
4. every irreducible component `Y` of `⋂_{v ∈ V} H_v` has `codim(Y, X) ≥ 2`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.Chart` is a trivializing affine chart: a nonempty affine open
  `U` of `X` together with a trivialization of `L` over `U`.
* `Stacks.Bertini.FamilyDivisors.Hypotheses` is the bundle (1)–(4).

## Main results

* `Stacks.Bertini.FamilyDivisors.exists_chart_le`: the trivializing affine charts form a basis of
  the topology of `X`.
* `Stacks.Bertini.FamilyDivisors.iSup_chart_eq_top` and
  `Stacks.Bertini.FamilyDivisors.exists_chart_le_inf`: the trivializing affine charts cover `X`
  and the family is closed under refining intersections.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.exists_not_isNilpotent_chartEquation`: hypothesis (3)
  gives, on every chart, a basis vector whose representing function is not nilpotent.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.two_le_height_chartEquation`: hypothesis (4) gives
  `2 ≤ Ideal.height` on every minimal prime of `(f₁, …, f_r)` in every chart ring.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.isIrreducible_supportSet_universalDivisor` and
  `Stacks.Bertini.FamilyDivisors.Hypotheses.irreducibleSpace_universalDivisorScheme`: under
  the hypotheses, `H_univ` is irreducible.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

namespace Stacks.Bertini.FamilyDivisors

/-! ### Trivializing affine charts -/

/-- **A trivializing affine chart of the family**: a nonempty affine open `U` of `X` together
with a trivialization of `L` over `U`. -/
structure Chart (D : FamilyDivisors.{u, v}) where
  /-- The affine open of `X`. -/
  U : D.X.Opens
  /-- The open is affine. -/
  isAffine : IsAffine U.toScheme
  /-- The open is nonempty. -/
  nonempty : Nonempty U.toScheme
  /-- A trivialization of `L` over the open. -/
  triv : D.restrictedModule U ≅ SheafOfModules.unit U.toScheme.ringCatSheaf

attribute [instance] Chart.isAffine Chart.nonempty

variable (D : FamilyDivisors.{u, v})

/-- **The trivializing affine charts form a basis of the topology of `X`.** Every open
neighbourhood of a point of `X` contains a trivializing affine chart containing that point. -/
theorem exists_chart_le (W : D.X.Opens) (x : D.X) (hx : x ∈ W) :
    ∃ c : D.Chart, c.U ≤ W ∧ x ∈ c.U := by
  obtain ⟨V, hV, hxV, hVW, ⟨e⟩⟩ :=
    Stacks.Modules.exists_affineOpen_pullback_iso_unit_of_isInvertible D.L hx
  exact ⟨⟨V, hV, ⟨⟨x, hxV⟩⟩, e⟩, hVW, hxV⟩

/-- **The trivializing affine charts cover `X`.** -/
theorem iSup_chart_eq_top : ⨆ c : D.Chart, c.U = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨c, -, hx⟩ := D.exists_chart_le ⊤ x trivial
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c, hx⟩

/-- A nonempty `X` has a trivializing affine chart. -/
theorem nonempty_chart [Nonempty D.X] : Nonempty D.Chart :=
  ⟨(D.exists_chart_le ⊤ (Classical.arbitrary D.X) trivial).choose⟩

/-- In an irreducible `X`, a chart meets every nonempty open set. -/
private theorem inter_nonempty_chart [IrreducibleSpace D.X] (c : D.Chart) {O : Set D.X}
    (hO : IsOpen O) (hne : O.Nonempty) : ((c.U : Set D.X) ∩ O).Nonempty :=
  nonempty_preirreducible_inter c.U.isOpen hO ⟨_, (Nonempty.some c.nonempty).2⟩ hne

/-- **The family of trivializing affine charts is closed under refining intersections.** If `X`
is irreducible, the intersection of two charts contains a chart. -/
theorem exists_chart_le_inf [IrreducibleSpace D.X] (c c' : D.Chart) :
    ∃ c'' : D.Chart, c''.U ≤ c.U ⊓ c'.U := by
  obtain ⟨x, hx⟩ := D.inter_nonempty_chart c c'.U.isOpen ⟨_, (Nonempty.some c'.nonempty).2⟩
  exact (D.exists_chart_le (c.U ⊓ c'.U) x hx).imp fun _ h ↦ h.1

/-- **A chart of an irreducible `X` is irreducible.** -/
theorem irreducibleSpace_chart [IrreducibleSpace D.X] (c : D.Chart) :
    IrreducibleSpace c.U.toScheme :=
  (Scheme.Hom.isOpenEmbedding c.U.ι).irreducibleSpace

/-- **The nilradical of a chart ring is prime when `X` is irreducible.** -/
theorem isPrime_nilradical_chart [IrreducibleSpace D.X] (c : D.Chart) :
    (nilradical Γ(c.U.toScheme, ⊤)).IsPrime :=
  have := D.irreducibleSpace_chart c
  Scheme.isPrime_nilradical_of_isAffine c.U.toScheme

/-- The ring of a chart of an integral `X` is a domain. -/
instance isDomain_chart [IsIntegral D.X] (c : D.Chart) : IsDomain Γ(c.U.toScheme, ⊤) :=
  haveI : IsIntegral c.U.toScheme := isIntegral_of_isOpenImmersion c.U.ι
  inferInstance

/-- The ring of a chart of a locally Noetherian `X` is Noetherian. -/
instance isNoetherianRing_chart [IsLocallyNoetherian D.X] (c : D.Chart) :
    IsNoetherianRing Γ(c.U.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top c.U.toScheme⟩

/-! ### The hypothesis bundle -/

/-- **The hypotheses of the Bertini irreducibility theorem** on the standing situation of the
Bertini theorems: `X` of finite type and geometrically irreducible over `k`, an irreducible
component `Z` of `H_{v₂} ∩ H_{v₃}` of codimension exactly two not contained in `H_{v₁}`, and a
codimension-two condition on the common zero locus of the linear system. -/
@[stacks 0G4F "the hypotheses"]
structure Hypotheses (D : FamilyDivisors.{u, v}) where
  /-- (1) `X → Spec k` is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType D.toBase
  /-- (1) `X → Spec k` is quasi-compact; with the previous clause, `X` is of finite type. -/
  quasiCompact : QuasiCompact D.toBase
  /-- (2) `X` is geometrically irreducible over `k`. -/
  geometricallyIrreducible : GeometricallyIrreducible D.toBase
  /-- (3) The first of the three distinguished vectors of the linear system. -/
  v₁ : D.V
  /-- (3) The second of the three distinguished vectors of the linear system. -/
  v₂ : D.V
  /-- (3) The third of the three distinguished vectors of the linear system. -/
  v₃ : D.V
  /-- (3) An irreducible closed subset of `X`. -/
  Z : IrreducibleCloseds D.X
  /-- (3) `Z` is an irreducible component of `H_{v₂} ∩ H_{v₃}`. -/
  Z_component : Maximal (fun W : IrreducibleCloseds D.X =>
    (W : Set D.X) ⊆ D.divisorSet v₂ ∩ D.divisorSet v₃) Z
  /-- (3) `Z ⊄ H_{v₁}`. -/
  Z_not_subset : ¬ (Z : Set D.X) ⊆ D.divisorSet v₁
  /-- (3) `codim(Z, X) = 2`. -/
  Z_codimension : codimension Z = 2
  /-- (4) Every irreducible closed subset of `X` contained in the common zero locus
  `⋂_{v ∈ V} H_v` has codimension at least two in `X`. -/
  commonZeroSet_codimension : ∀ Y : IrreducibleCloseds D.X,
    (Y : Set D.X) ⊆ D.commonZeroSet → 2 ≤ codimension Y

namespace Hypotheses

variable {D} (h : D.Hypotheses)

include h

/-- `X` is irreducible. -/
theorem irreducibleSpace : IrreducibleSpace D.X :=
  have := h.geometricallyIrreducible
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := D.toBase)

/-- `X` is locally Noetherian. -/
theorem isLocallyNoetherian : IsLocallyNoetherian D.X :=
  have := h.locallyOfFiniteType
  LocallyOfFiniteType.isLocallyNoetherian D.toBase

/-- `X` is integral once it is reduced. -/
theorem isIntegral [IsReduced D.X] : IsIntegral D.X :=
  have := h.irreducibleSpace
  isIntegral_of_irreducibleSpace_of_isReduced D.X

/-- **Hypothesis (4), read on a chart.** Every minimal prime over the ideal `(f₁, …, f_r)`
generated by the functions representing the sections `ψ(vᵢ)` on a trivializing affine chart has
height at least two. -/
@[stacks 0G4F "hypothesis (4) read on a trivializing affine chart"]
theorem two_le_height_chartEquation (c : D.Chart)
    {q : Ideal Γ(c.U.toScheme, ⊤)}
    (hq : q ∈ (Ideal.span (Set.range (D.chartEquation c.triv))).minimalPrimes) :
    2 ≤ q.height :=
  Scheme.le_height_of_mem_minimalPrimes_of_isAffineOpen c.U D.isClosed_commonZeroSet
    h.commonZeroSet_codimension (image_zeroLocus_subset_commonZeroSet c.triv) hq

/-- **Hypothesis (3), read on a chart.** On every trivializing affine chart some basis vector is
represented by a function that is not nilpotent. -/
@[stacks 0G4F "hypothesis (3) read on a trivializing affine chart"]
theorem exists_not_isNilpotent_chartEquation (c : D.Chart) :
    ∃ j, ¬ IsNilpotent (D.chartEquation c.triv j) := by
  have := h.irreducibleSpace
  by_contra! hcon
  have hspan : Ideal.span (Set.range (D.chartEquation c.triv)) ≤
      nilradical Γ(c.U.toScheme, ⊤) :=
    Ideal.span_le.mpr <| Set.range_subset_iff.mpr fun j ↦ mem_nilradical.mpr (hcon j)
  have hnilp : IsNilpotent (chartFunction c.triv h.v₁) :=
    mem_nilradical.mp (hspan (chartFunction_mem_span_chartEquation c.triv h.v₁))
  have hbot : c.U.toScheme.basicOpen (chartFunction c.triv h.v₁) = ⊥ :=
    c.U.toScheme.toLocallyRingedSpace.basicOpen_eq_bot_of_isNilpotent ⊤ _ hnilp
  have hsub : (c.U : Set D.X) ⊆ D.divisorSet h.v₁ := by
    rintro y hy
    refine (mem_divisorSet_iff c.triv h.v₁ ⟨y, hy⟩).mpr ?_
    refine (c.U.toScheme.mem_zeroLocus_iff _ _).mpr ?_
    rintro f rfl
    rw [hbot]
    exact id
  have huniv : D.divisorSet h.v₁ = Set.univ := by
    by_contra hne
    obtain ⟨z, hz⟩ : (D.divisorSet h.v₁)ᶜ.Nonempty := Set.nonempty_compl.mpr hne
    obtain ⟨w, hw⟩ :=
      D.inter_nonempty_chart c (D.isClosed_divisorSet h.v₁).isOpen_compl ⟨z, hz⟩
    exact hw.2 (hsub hw.1)
  exact h.Z_not_subset (by simp [huniv])

/-- **`H_univ` is irreducible under the hypotheses of the Bertini irreducibility theorem.** -/
@[stacks 0G4F "the irreducibility of the universal divisor, from the tag's own hypotheses"]
theorem isIrreducible_supportSet_universalDivisor :
    IsIrreducible D.universalDivisor.supportSet := by
  have := h.irreducibleSpace
  have := h.isLocallyNoetherian
  have : Nonempty D.Chart := D.nonempty_chart
  exact D.isIrreducible_supportSet_universalDivisor_of_directed (fun c : D.Chart ↦ c.U)
    D.iSup_chart_eq_top D.exists_chart_le_inf D.isPrime_nilradical_chart (fun c ↦ c.triv)
    h.exists_not_isNilpotent_chartEquation fun c _ hq ↦ h.two_le_height_chartEquation c hq

/-- **`H_univ` is an irreducible scheme under the hypotheses of the Bertini irreducibility
theorem.** -/
@[stacks 0G4F "the universal divisor as an irreducible scheme, from the tag's own hypotheses"]
theorem irreducibleSpace_universalDivisorScheme :
    IrreducibleSpace D.universalDivisor.subscheme :=
  D.irreducibleSpace_universalDivisor_subscheme h.isIrreducible_supportSet_universalDivisor

end Hypotheses

end Stacks.Bertini.FamilyDivisors

end
