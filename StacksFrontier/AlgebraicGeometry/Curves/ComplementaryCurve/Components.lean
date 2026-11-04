module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.WeilDivisors
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.IrreducibleDimensionOne
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Irreducible.ComponentSubfamily

/-!
# Components of a reduced closed subcurve and of its complement

Let `X` be an equidimensional curve of dimension one, locally of finite type over a field, and
let `Y ⊆ X` be a reduced equidimensional closed subscheme of dimension one. Then `Y` is
scheme-theoretically the union of the irreducible components of `X` it contains, and the
scheme-theoretic closure of the open complement of `Y` is the reduced union of the remaining
components.

Both follow from the fact that a one-dimensional closed irreducible subset of a one-dimensional
irreducible space is everything: every irreducible component of `Y` is therefore an irreducible
component of `X`, and conversely each component of `X` meeting the complement of `Y` is already
contained in the closure of that complement.

## Main results

* `Stacks.Curves.eq_union_irreducibleComponents`: the closed subcurve is the union of the
  ambient components it contains.
* `Stacks.Curves.complementaryCurveIdeal_eq_union_irreducibleComponents`: the scheme-theoretic
  closure of the complement is the reduced union of the other components.
* `Stacks.Curves.complementaryCurveIdeal_complementaryCurveIdeal`: on a reduced curve, the
  scheme-theoretic closure of the complement of the closure of the complement of the subcurve is
  the subcurve itself.

## Implementation notes

Closed subschemes are represented by `AlgebraicGeometry.Scheme.IdealSheafData`, and a union of
closed subsets is the supremum of their closures in the lattice of closed sets, which describes
the union even for an infinite family of components. The scheme-theoretic closure of the
complement is `AlgebraicGeometry.complementaryCurveIdeal`, the kernel of the inclusion of the open
complement. Reducedness of the ambient curve, needed for the second statement, comes from
nodality through `Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities`; the equidimensionality
and dimension hypotheses are not used for it.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-- **On an equidimensional scheme of finite type over a field, the local dimension is the
global one at every point.** The local dimension at a point is the dimension of some component
through it, and all components have the same dimension. -/
theorem topologicalKrullDimAt_eq_one_of_equidimensional {k : Type u} [Field k]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (heq : Equidimensional X) (hdim : topologicalKrullDim X = 1) (x : X) :
    topologicalKrullDimAt X x = 1 := by
  obtain ⟨Z, hZ, _, hZdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X p x
  have hconstant : ∀ y : X, topologicalKrullDimAt X y = topologicalKrullDim Z := by
    intro y
    obtain ⟨W, hW, _, hWdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X p y
    exact hWdim.symm.trans (heq W hW Z hZ)
  have hglobal : topologicalKrullDim X = topologicalKrullDim Z := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    simp_rw [← topologicalKrullDimAt_eq_localKrullDim, hconstant]
    exact le_antisymm (iSup_le fun _ => le_rfl) (le_iSup_of_le x le_rfl)
  exact hZdim.symm.trans (hglobal.symm.trans hdim)

/-- **Every irreducible component of an equidimensional one-dimensional scheme of finite type
over a field has dimension one.** -/
theorem topologicalKrullDim_irreducibleComponent_eq_one {k : Type u} [Field k]
    {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (heq : Equidimensional S) (hdim : topologicalKrullDim S = 1)
    (C : Set S) (hC : C ∈ irreducibleComponents S) : topologicalKrullDim C = 1 := by
  obtain ⟨x, -⟩ := hC.1.nonempty
  obtain ⟨D, hD, -, hDdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k S f x
  exact (heq D hD C hC).symm.trans
    (hDdim.trans (topologicalKrullDimAt_eq_one_of_equidimensional S f heq hdim x))

/-- **Every point of a one-dimensional reduced equidimensional closed subscheme of a
one-dimensional equidimensional curve lies on an ambient irreducible component contained in that
subscheme.** The component of the subscheme through the point is a one-dimensional closed
irreducible subset of an ambient component, hence is all of it. -/
theorem exists_component_subset_support_of_mem
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hXeq : Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (I : X.IdealSheafData) (hYeq : Equidimensional I.subscheme)
    (hYdim : topologicalKrullDim I.subscheme = 1) {x : X}
    (hx : x ∈ (I.support : Set X)) :
    ∃ C ∈ irreducibleComponents X, x ∈ C ∧ C ⊆ (I.support : Set X) := by
  classical
  let fX : X ⟶ Spec (.of k) := X ↘ Spec (.of k)
  let fY : I.subscheme ⟶ Spec (.of k) := I.subschemeι ≫ fX
  have : LocallyOfFiniteType fY := by
    dsimp [fY, fX]
    infer_instance
  let y : I.subscheme := Classical.choose (I.range_subschemeι ▸ hx)
  have hy : I.subschemeι.base y = x := Classical.choose_spec (I.range_subschemeι ▸ hx)
  let D : Set I.subscheme := irreducibleComponent y
  have hD : D ∈ irreducibleComponents I.subscheme :=
    irreducibleComponent_mem_irreducibleComponents y
  have hDdim := topologicalKrullDim_irreducibleComponent_eq_one fY hYeq hYdim D hD
  let E : Set X := I.subschemeι '' D
  have hEirr : IsIrreducible E := hD.1.image I.subschemeι I.subschemeι.continuous.continuousOn
  have hEclosed : IsClosed E :=
    I.subschemeι.isClosedEmbedding.isClosedMap D
      (isClosed_of_mem_irreducibleComponents D hD)
  let eD : D ≃ₜ E := I.subschemeι.isClosedEmbedding.homeomorphImage D
  have hEdim : topologicalKrullDim E = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ eD.isHomeomorph).symm.trans hDdim
  obtain ⟨C, hC, hEC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible E hEirr
  have hCdim := topologicalKrullDim_irreducibleComponent_eq_one fX hXeq hXdim C hC
  let A : Set C := {z | (z : X) ∈ E}
  have hAclosed : IsClosed A := hEclosed.preimage continuous_subtype_val
  have hErange : E ⊆ Set.range (fun z : C => (z : X)) := fun z hz => ⟨⟨z, hEC hz⟩, rfl⟩
  let eA : A ≃ₜ E := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hErange
  have hAdim : topologicalKrullDim A = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ eA.isHomeomorph).trans hEdim
  have hBirr : IsIrreducible (Set.univ : Set C) := by
    have : IrreducibleSpace C := Subtype.irreducibleSpace hC.1
    exact ⟨Set.univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩
  have hAeq := Stacks.Topology.Dimension.closed_irreducible_subset_eq_of_dim_one
    hAclosed hBirr hAdim hCdim
  have hCE : C ⊆ E := fun z hz => (hAeq.symm ▸ Set.mem_univ (⟨z, hz⟩ : C) : (⟨z, hz⟩ : C) ∈ A)
  have hEsupport : E ⊆ (I.support : Set X) := by
    rintro z ⟨w, -, rfl⟩
    rw [← I.range_subschemeι]
    exact ⟨w, rfl⟩
  exact ⟨C, hC, hEC ⟨y, mem_irreducibleComponent, hy⟩, fun z hz => hEsupport (hCE hz)⟩

/-- Any union of irreducible components of a locally noetherian scheme is closed. -/
private theorem isClosed_iUnion_irreducibleComponents {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : Set X → Prop) :
    IsClosed (⋃ C : {C : Set X // C ∈ irreducibleComponents X ∧ P C}, (C.1 : Set X)) := by
  have hcomponents : LocallyFinite (fun C : irreducibleComponents X => (C : Set X)) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  exact (locallyFinite_component_subfamily hcomponents P).isClosed_iUnion fun C =>
    isClosed_of_mem_irreducibleComponents C.1 C.2.1

/-- The supremum of the closures of a family of irreducible components is their union. -/
private theorem coe_iSup_closure_irreducibleComponents {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : Set X → Prop) :
    (↑(⨆ C : {C : Set X // C ∈ irreducibleComponents X ∧ P C}, Closeds.closure C.1) : Set X) =
      ⋃ C : {C : Set X // C ∈ irreducibleComponents X ∧ P C}, (C.1 : Set X) :=
  coe_iSup_closure_eq_iUnion_of_isClosed _
    (fun C => isClosed_of_mem_irreducibleComponents C.1 C.2.1)
    (isClosed_iUnion_irreducibleComponents P)

/-- **A reduced closed subcurve of a one-dimensional equidimensional curve is
scheme-theoretically the union of the ambient irreducible components contained in its
support.** -/
theorem eq_union_irreducibleComponents
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (_hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) :
    I = Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : {C : Set X // C ∈ irreducibleComponents X ∧ C ⊆ (I.support : Set X)},
        Closeds.closure C.1) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let Csub := {C : Set X // C ∈ irreducibleComponents X ∧ C ⊆ (I.support : Set X)}
  have hsupport : (I.support : Set X) = (↑(⨆ C : Csub, Closeds.closure C.1) : Set X) := by
    rw [coe_iSup_closure_irreducibleComponents]
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun C => C.2.2)
    obtain ⟨C, hC, hxC, hCI⟩ := exists_component_subset_support_of_mem
      (k := k) (X := X) hX_equidimensional hX_dimension I hY_equidimensional hY_dimension hx
    exact Set.mem_iUnion.mpr ⟨⟨C, hC, hCI⟩, hxC⟩
  calc
    I = Scheme.IdealSheafData.vanishingIdeal I.support :=
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I I.support rfl
    _ = Scheme.IdealSheafData.vanishingIdeal (⨆ C : Csub, Closeds.closure C.1) :=
      congrArg Scheme.IdealSheafData.vanishingIdeal (SetLike.coe_injective hsupport)

/-- **The scheme-theoretic closure of the complement of a closed subscheme of a reduced curve is
the reduced union of the irreducible components not contained in it.** Neither the dimension nor
the equidimensionality of the ambient curve or of the subscheme is needed: nodality enters only
through reducedness of the ambient curve. -/
theorem complementaryCurveIdeal_eq_union_irreducibleComponents
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_nodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData) :
    let U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
    U.ι.ker = Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : {C : Set X // C ∈ irreducibleComponents X ∧ ¬ C ⊆ (I.support : Set X)},
        Closeds.closure C.1) := by
  classical
  intro U
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hX_nodal
  let Zcomps := {C : Set X // C ∈ irreducibleComponents X ∧ ¬ C ⊆ (I.support : Set X)}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hclosure : closure (I.supportᶜ : Set X) =
      (↑(⨆ C : Zcomps, Closeds.closure C.1) : Set X) := by
    rw [coe_iSup_closure_irreducibleComponents]
    refine Set.Subset.antisymm
      (closure_minimal (fun x hx => ?_) (isClosed_iUnion_irreducibleComponents _))
      (fun x hx => ?_)
    · obtain ⟨C, hC, hxC, _⟩ :=
        exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
          k X (X ↘ Spec (.of k)) x
      exact Set.mem_iUnion.mpr ⟨⟨C, hC, fun hCsub => hx (hCsub hxC)⟩, hxC⟩
    · obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hyC, hyU⟩ := Set.not_subset.mp C.2.2
      have hCclosure : C.1 ⊆ closure (C.1 ∩ (I.support : Set X)ᶜ) :=
        subset_closure_inter_of_isPreirreducible_of_isOpen C.2.1.1.2 U.isOpen ⟨y, hyC, hyU⟩
      exact closure_mono Set.inter_subset_right (hCclosure hxC)
  have hkerAsVanishing : U.ι.ker =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range U.ι)) := by
    calc
      U.ι.ker = (⊥ : U.toScheme.IdealSheafData).map U.ι := by
        symm
        simpa [Scheme.IdealSheafData.map] using
          Scheme.Hom.ker_comp_of_isIso ((⊥ : U.toScheme.IdealSheafData).subschemeι) U.ι
      _ = (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds U.toScheme)).map U.ι := by
        rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
      _ = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range U.ι)) := by
        simpa using Scheme.IdealSheafData.map_vanishingIdeal U.ι (⊤ : Closeds U.toScheme)
  rw [hkerAsVanishing]
  congr 1
  apply SetLike.coe_injective
  calc
    (↑(Closeds.closure (Set.range U.ι)) : Set X) = closure (I.supportᶜ : Set X) := by
      simp [U, Scheme.Opens.range_ι]
    _ = (↑(⨆ C : Zcomps, Closeds.closure C.1) : Set X) := hclosure

/-- **The closure of the complement of the closure of the complement of a subcurve is the
subcurve.** Let `X` be a reduced equidimensional curve of dimension one, locally of finite type
over a field, and `C` a reduced equidimensional closed subscheme of dimension one. Then the
scheme-theoretic closure of the complement of `Z`, the scheme-theoretic closure of the complement
of `C`, is `C` itself. -/
theorem complementaryCurveIdeal_complementaryCurveIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsReduced X]
    (hXeq : Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (C : X.IdealSheafData) [IsReduced C.subscheme] (hYeq : Equidimensional C.subscheme)
    (hYdim : topologicalKrullDim C.subscheme = 1) :
    complementaryCurveIdeal (complementaryCurveIdeal C) = C := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  set J := complementaryCurveIdeal C
  set S : Set X := (C.support : Set X)ᶜ
  -- the support of `J` is the closure of the complement of the support of `C`
  have hJsupp : (J.support : Set X) = closure S := by
    have h := Scheme.Hom.support_ker_eq_closure_range (Scheme.Opens.ι C.support.compl)
    rw [Scheme.Opens.range_ι] at h
    exact congrArg (fun T : Closeds X => (T : Set X)) h
  -- the closure of `S` is covered by the components meeting `S`
  have hclosure : closure S ⊆
      ⋃ D : {D : Set X // D ∈ irreducibleComponents X ∧ (D ∩ S).Nonempty}, D.1 := by
    refine closure_minimal (fun z hz => ?_) (isClosed_iUnion_irreducibleComponents _)
    exact Set.mem_iUnion.mpr ⟨⟨irreducibleComponent z,
      irreducibleComponent_mem_irreducibleComponents z, z, mem_irreducibleComponent, hz⟩,
      mem_irreducibleComponent⟩
  rw [show J = complementaryCurveIdeal C from rfl, complementaryCurveIdeal,
    Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme C C.support rfl]
  congr 1
  apply SetLike.coe_injective
  rw [Closeds.coe_closure, Scheme.Opens.range_ι]
  refine Set.Subset.antisymm (closure_minimal (fun z hz => ?_) C.support.isClosed)
    (fun x hx => ?_)
  · -- off the support of `J` lies the support of `C`
    by_contra hzC
    exact hz (hJsupp ▸ subset_closure hzC)
  · obtain ⟨C₀, hC₀, hxC₀, hC₀C⟩ :=
      exists_component_subset_support_of_mem (k := k) hXeq hXdim C hYeq hYdim hx
    have hgen := hC₀.1.isGenericPoint_genericPoint_closure
    rw [(isClosed_of_mem_irreducibleComponents C₀ hC₀).closure_eq] at hgen
    set η := hC₀.1.genericPoint
    have hηJ : η ∉ (J.support : Set X) := by
      intro hη
      rw [hJsupp] at hη
      obtain ⟨⟨D, hD, z, hzD, hzS⟩, hηD⟩ := Set.mem_iUnion.mp (hclosure hη)
      have hC₀D : C₀ ⊆ D := by
        rw [← hgen.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr hηD)
          (isClosed_of_mem_irreducibleComponents D hD)
      have hDC₀ : D ⊆ C₀ := hC₀.2 hD.1 hC₀D
      exact hzS (hC₀C (hDC₀ hzD))
    have : x ∈ closure ({η} : Set X) := hgen.def ▸ hxC₀
    exact closure_mono (Set.singleton_subset_iff.mpr hηJ) this

end Stacks.Curves

end
