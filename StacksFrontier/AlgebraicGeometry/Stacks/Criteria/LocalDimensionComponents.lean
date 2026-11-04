module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Properties.Jacobson
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.ConstancyOfDimension
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The local dimension of a Jacobson catenary scheme along an irreducible component

On a Jacobson, catenary, locally Noetherian scheme `X` the local dimension at a point `x` is the
dimension of a nonempty open *irreducible* subset whose closure contains `x`, and that open subset
carries the same local dimension at each of its own points.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_inter_eq_of_isIrreducible_isClosed`: **Stacks 0DRT** at an
  irreducible closed subset — a nonempty open piece of it has its dimension.
* `AlgebraicGeometry.exists_isOpen_isIrreducible_topologicalKrullDimAt_eq_of_noetherianSpace`: the
  purely topological statement, on a quasi-sober Noetherian space whose irreducible components
  satisfy the conclusion of the previous theorem.
* `AlgebraicGeometry.exists_isOpen_isIrreducible_topologicalKrullDimAt_eq`: the statement for a
  Jacobson, catenary, locally Noetherian scheme.

## Implementation notes

The reduced induced structure on a closed subset is
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` followed by
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme`.

The topological statement is stated separately, for a quasi-sober Noetherian space, with the
property of its irreducible components as a hypothesis.

## References

* [Stacks Project, Tag 0DRT](https://stacks.math.columbia.edu/tag/0DRT)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks 0DRT at an irreducible closed subset.** On a Jacobson, catenary, locally Noetherian
scheme, a nonempty open piece `Z ∩ O` of an irreducible closed subset `Z` has the dimension of
`Z`. -/
@[ega "IV 10.6.3" "special case", sga "3 VIB 1.5" "more general"]
theorem topologicalKrullDim_inter_eq_of_isIrreducible_isClosed
    (X : Scheme.{u}) [JacobsonSpace X] [IsLocallyNoetherian X]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace X)
    {Z : Set X} (hZ : IsIrreducible Z) (hZc : IsClosed Z)
    {O : Set X} (hO : IsOpen O) (hne : (Z ∩ O).Nonempty) :
    topologicalKrullDim (Z ∩ O : Set X) = topologicalKrullDim (Z : Set X) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZc⟩ : Closeds X) with hIdef
  have hrange : Set.range I.subschemeι = Z :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal (⟨Z, hZc⟩ : Closeds X)
  have hemb : Topology.IsEmbedding (I.subschemeι.base) := I.subschemeι.isEmbedding
  have : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by rw [hrange]; exact hZ)
  have : JacobsonSpace I.subscheme :=
    JacobsonSpace.of_isClosedEmbedding I.subschemeι.isClosedEmbedding
  have : IsLocallyNoetherian I.subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme I
  have hcatI : IrreducibleClosedsCodim.IsCatenarySpace I.subscheme :=
    IsCatenarySpace.of_isImmersion I.subschemeι hcat
  have hprene : (I.subschemeι.base ⁻¹' O).Nonempty := by
    obtain ⟨z, hzZ, hzO⟩ := hne
    rw [← hrange] at hzZ
    obtain ⟨y, rfl⟩ := hzZ
    exact ⟨y, hzO⟩
  have h1 := topologicalKrullDim_isOpen_eq_of_catenary I.subscheme hcatI
    (I.subschemeι.base ⁻¹' O) (hO.preimage I.subschemeι.continuous) hprene
  have himg : I.subschemeι.base '' (I.subschemeι.base ⁻¹' O) = Z ∩ O := by
    rw [Set.image_preimage_eq_inter_range, hrange, Set.inter_comm]
  have h2 : topologicalKrullDim (I.subschemeι.base ⁻¹' O : Set I.subscheme) =
      topologicalKrullDim (Z ∩ O : Set X) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (((hemb.homeomorphImage (I.subschemeι.base ⁻¹' O)).trans
        (Homeomorph.setCongr himg)).isHomeomorph)
  have h3 : topologicalKrullDim I.subscheme = topologicalKrullDim (Z : Set X) :=
    IsHomeomorph.topologicalKrullDim_eq _
      ((hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph)
  rw [← h2, h1, h3]

/-- **The local dimension of a quasi-sober Noetherian space along a component of maximal
dimension.** Suppose every nonempty open piece of an irreducible component has the dimension of
that component. Then the local dimension at a point `x` is the dimension of a nonempty open
irreducible set whose closure contains `x`, and the local dimension at each point of that open set
is the same. -/
theorem exists_isOpen_isIrreducible_topologicalKrullDimAt_eq_of_noetherianSpace
    {X : Type*} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X]
    (hcomp : ∀ Z ∈ irreducibleComponents X, ∀ O : Set X, IsOpen O → (Z ∩ O).Nonempty →
      topologicalKrullDim (Z ∩ O : Set X) = topologicalKrullDim (Z : Set X))
    (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ closure V ∧
      topologicalKrullDimAt X x = topologicalKrullDim (V : Set X) ∧
      ∀ v ∈ V, topologicalKrullDimAt X v = topologicalKrullDim (V : Set X) := by
  classical
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  set S := {Z ∈ irreducibleComponents X | x ∈ Z} with hSdef
  have hSfin : S.Finite := hfin.subset fun _ hZ => hZ.1
  have hSne : S.Nonempty := ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x, mem_irreducibleComponent⟩
  obtain ⟨Z₀, hZ₀S, hZ₀max⟩ :=
    Set.exists_max_image S (fun Z => topologicalKrullDim (Z : Set X)) hSfin hSne
  have hZ₀ : Z₀ ∈ irreducibleComponents X := hZ₀S.1
  have hxZ₀ : x ∈ Z₀ := hZ₀S.2
  have hZ₀irr : IsIrreducible Z₀ := hZ₀.1
  have hopen : ∀ T ⊆ irreducibleComponents X, IsOpen (⋃₀ T)ᶜ := fun T hT =>
    isOpen_compl_iff.2 <| (hfin.subset hT).isClosed_sUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents W (hT hW)
  set V := (⋃₀ (irreducibleComponents X \ {Z₀}))ᶜ with hVdef
  have hVopen : IsOpen V := hopen _ Set.sdiff_subset
  have hVclosure : closure V = Z₀ :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z₀ hZ₀
  have hVZ₀ : V ⊆ Z₀ := hVclosure ▸ subset_closure
  have hVne : V.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h =>
    hZ₀irr.nonempty.ne_empty (by rw [← hVclosure, h, closure_empty])
  have hVirr : IsIrreducible V := ⟨hVne, hZ₀irr.isPreirreducible.open_subset hVopen hVZ₀⟩
  have hVZ₀eq : Z₀ ∩ V = V := Set.inter_eq_self_of_subset_right hVZ₀
  have hdimV : topologicalKrullDim (V : Set X) = topologicalKrullDim (Z₀ : Set X) := by
    have h := hcomp Z₀ hZ₀ V hVopen (by rw [hVZ₀eq]; exact hVne)
    rwa [hVZ₀eq] at h
  have hlower : ∀ z ∈ Z₀, topologicalKrullDim (V : Set X) ≤ topologicalKrullDimAt X z := by
    intro z hz
    rw [topologicalKrullDimAt]
    refine le_iInf fun U => ?_
    have h := hcomp Z₀ hZ₀ U.1 U.2.2 ⟨z, hz, U.2.1⟩
    calc topologicalKrullDim (V : Set X) = topologicalKrullDim (Z₀ ∩ U.1 : Set X) := by
          rw [hdimV, h]
      _ ≤ topologicalKrullDim (U.1 : Set X) :=
          topologicalKrullDim_le_of_subset Set.inter_subset_right
  set O₀ := (⋃₀ (irreducibleComponents X \ S))ᶜ with hO₀def
  have hO₀open : IsOpen O₀ := hopen _ Set.sdiff_subset
  have hxO₀ : x ∈ O₀ := by
    rw [hO₀def, Set.mem_compl_iff]
    rintro ⟨W, ⟨hW, hWS⟩, hxW⟩
    exact hWS ⟨hW, hxW⟩
  have : QuasiSober (O₀ : Set X) :=
    Topology.IsOpenEmbedding.quasiSober hO₀open.isOpenEmbedding_subtypeVal
  have hupper : topologicalKrullDim (O₀ : Set X) ≤ topologicalKrullDim (V : Set X) := by
    rw [← topologicalKrullDim_univ]
    refine topologicalKrullDim_le_of_forall_closure isClosed_univ fun w _ => ?_
    have hZw : irreducibleComponent (w : X) ∈ irreducibleComponents X :=
      irreducibleComponent_mem_irreducibleComponents _
    have hwZ : (w : X) ∈ irreducibleComponent (w : X) := mem_irreducibleComponent
    have hZS : irreducibleComponent (w : X) ∈ S := by
      refine ⟨hZw, ?_⟩
      by_contra hxZ
      have hwO : (w : X) ∉ ⋃₀ (irreducibleComponents X \ S) := w.2
      exact hwO ⟨irreducibleComponent (w : X), ⟨hZw, fun h => hxZ h.2⟩, hwZ⟩
    have hsub : closure ({w} : Set (O₀ : Set X)) ⊆
        (Subtype.val ⁻¹' irreducibleComponent (w : X) : Set (O₀ : Set X)) :=
      ((isClosed_irreducibleComponent).preimage continuous_subtype_val).closure_subset_iff.mpr
        (by simpa using hwZ)
    have hpv : (Subtype.val ⁻¹' irreducibleComponent (w : X) : Set (O₀ : Set X)) =
        (Subtype.val ⁻¹' (irreducibleComponent (w : X) ∩ O₀) : Set (O₀ : Set X)) := by
      ext y
      simp
    calc topologicalKrullDim (closure ({w} : Set (O₀ : Set X)))
        ≤ topologicalKrullDim (Subtype.val ⁻¹' irreducibleComponent (w : X) :
            Set (O₀ : Set X)) := topologicalKrullDim_le_of_subset hsub
      _ = topologicalKrullDim (irreducibleComponent (w : X) ∩ O₀ : Set X) := by
          rw [hpv]
          exact topologicalKrullDim_preimage_val O₀ _ Set.inter_subset_right
      _ ≤ topologicalKrullDim (irreducibleComponent (w : X) : Set X) :=
          topologicalKrullDim_le_of_subset Set.inter_subset_left
      _ ≤ topologicalKrullDim (Z₀ : Set X) := hZ₀max _ hZS
      _ = topologicalKrullDim (V : Set X) := hdimV.symm
  have hxV : x ∈ closure V := by rw [hVclosure]; exact hxZ₀
  refine ⟨V, hVopen, hVirr, hxV, ?_, ?_⟩
  · refine le_antisymm ?_ (hlower x hxZ₀)
    rw [topologicalKrullDimAt]
    exact le_trans (iInf_le _ (⟨O₀, hxO₀, hO₀open⟩ :
      {U : Set X // x ∈ U ∧ IsOpen U})) hupper
  · intro v hv
    refine le_antisymm ?_ (hlower v (hVZ₀ hv))
    rw [topologicalKrullDimAt]
    exact iInf_le _ (⟨V, hv, hVopen⟩ : {U : Set X // v ∈ U ∧ IsOpen U})

/-- **The local dimension of a Jacobson, catenary, locally Noetherian scheme is the dimension of a
nearby open irreducible subset.** At every point `x` there is a nonempty open irreducible `V` whose
closure contains `x` with `dim_x(X) = dim(V)`, and with `dim_v(X) = dim(V)` at every `v ∈ V`. -/
theorem exists_isOpen_isIrreducible_topologicalKrullDimAt_eq
    (X : Scheme.{u}) [JacobsonSpace X] [IsLocallyNoetherian X]
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace X) (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ closure V ∧
      topologicalKrullDimAt X x = topologicalKrullDim (V : Set X) ∧
      ∀ v ∈ V, topologicalKrullDimAt X v = topologicalKrullDim (V : Set X) := by
  obtain ⟨W, hWaff, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have : IsAffine W.toScheme := hWaff
  have : IsNoetherian W.toScheme := ⟨⟩
  have : JacobsonSpace W.toScheme := jacobsonSpace_open ‹JacobsonSpace X› W
  have hcatW : IrreducibleClosedsCodim.IsCatenarySpace W.toScheme :=
    IsCatenarySpace.of_isImmersion W.ι hcat
  obtain ⟨x', hx'⟩ : ∃ x' : W.toScheme, W.ι.base x' = x := ⟨⟨x, hxW⟩, rfl⟩
  obtain ⟨V', hV'open, hV'irr, hxV', hdimx', hdimv'⟩ :=
    exists_isOpen_isIrreducible_topologicalKrullDimAt_eq_of_noetherianSpace
      (X := W.toScheme)
      (fun Z hZ O hO hne => topologicalKrullDim_inter_eq_of_isIrreducible_isClosed
        W.toScheme hcatW hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ) hO hne) x'
  have hemb : Topology.IsOpenEmbedding (W.ι.base) := W.ι.isOpenEmbedding
  have hdim : topologicalKrullDim (V' : Set W.toScheme) =
      topologicalKrullDim (W.ι.base '' V' : Set X) :=
    IsHomeomorph.topologicalKrullDim_eq _ (hemb.isEmbedding.homeomorphImage V').isHomeomorph
  refine ⟨W.ι.base '' V', hemb.isOpenMap _ hV'open,
    hV'irr.image _ W.ι.continuous.continuousOn, ?_, ?_, ?_⟩
  · rw [← hx']
    exact image_closure_subset_closure_image W.ι.continuous ⟨x', hxV', rfl⟩
  · rw [← hx', hemb.topologicalKrullDimAt_eq x', hdimx', hdim]
  · rintro v ⟨v', hv', rfl⟩
    rw [hemb.topologicalKrullDimAt_eq v', hdimv' v' hv', hdim]

end AlgebraicGeometry

end
