module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedIdealSheafOfClosedSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedGlobalSections

/-!
# Separating the support of a coherent module on an algebraic space into two closed pieces

Let `X` be a Noetherian algebraic space over a scheme `S` and let `F` be a coherent
`𝒪_X`-module whose support is a union `Z ∪ Z'` of two closed subsets of `|X|`.  Then `F` is an
extension of coherent modules supported on the two pieces.

## Main results

* `AlgebraicGeometry.Space.mem_supportedSectionsSubmodule_of_range_subset_compl`: over a chart
  whose image misses `Z`, every section of `F` is supported in `Z'`.
* `AlgebraicGeometry.Space.subsingleton_cokernel_val_obj_of_forall_mem`: the quotient of a
  module by a submodule containing all sections over every chart below a given one has no
  sections over that chart.
* `AlgebraicGeometry.Space.supportOfSheaf_cokernel_supportedSections_subset`: the quotient of
  `F` by the subsheaf of sections supported in `Z'` is supported in `Z`.
* `AlgebraicGeometry.Space.exists_shortExact_coherent_supportOfSheaf_subset`: **Stacks 07UP** —
  a coherent module whose support is a union of two closed subsets is an extension of a
  coherent module supported on one of them by a coherent module supported on the other.

## Implementation notes

The submodule exhibited is the canonical one: `𝒢' ⊆ F` is the subsheaf of sections supported
in `Z'`, `AlgebraicGeometry.Space.supportedSectionsSubmodule` of Stacks 0859.  Its support lies
in `Z'` with no hypothesis, by
`AlgebraicGeometry.Space.supportOfSheaf_supportedSectionsSubmodule_subset`.

That the quotient is supported in `Z` is where the hypothesis on the support of `F` enters, and
it needs no sheaf of ideals acting on `F`: over a chart whose image misses `Z` the support of
any section of `F` lies in the preimage of `Supp F = Z ∪ Z'`, hence in the preimage of `Z'`, so
every section is already a section of `𝒢'` and the quotient has no sections there.  The charts
on which that applies are exactly the charts carrying the unit ideal of the sheaf of ideals
cutting out `Z`, which is what
`AlgebraicGeometry.Space.supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton` consumes;
the sheaf of ideals is `AlgebraicGeometry.Space.reducedIdealSheaf`.

The module universe is pinned to the universe of the schemes because that is where the
`𝒪_X`-modules are abelian, hence where the cokernel of the inclusion exists.

## References

* [Stacks Project, Tag 07UP](https://stacks.math.columbia.edu/tag/07UP)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The support of a section lies over the support of the module -/

/-- **The support of a section over a chart lies in the preimage of the support of the
module.**  The support of the module is the union of the images of the supports of all its
sections. -/
theorem supportOfSection_subset_preimage_supportOfSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)) :
    supportOfSection B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) W s ⊆
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.obj.hom ⁻¹'
        supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) := by
  intro y hy
  rw [Set.mem_preimage,
    supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X.1 X.2
      (moduleAddSheaf B S hS X.1 X.2 F)]
  exact Set.mem_iUnion.2 ⟨W, Set.mem_iUnion.2 ⟨s, ⟨y, hy, rfl⟩⟩⟩

/-! ### Sections over a chart missing one piece of the support -/

/-- **Over a chart whose image misses `Z`, every section of `F` is supported in `Z'`.**  The
support of a section lies in the preimage of `Supp F = Z ∪ Z'`, and the preimage of `Z` is
empty because the image of the chart misses `Z`. -/
theorem mem_supportedSectionsSubmodule_of_range_subset_compl
    (F : Modules.{u, u} B S hS X.1 X.2) (Z Z' : Set (points B S hS X.1))
    (hF : supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) = Z ∪ Z')
    (W : SmallEtale B S hS X.1)
    (hW : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.obj.hom) ⊆ Zᶜ)
    (s : F.val.obj (op W)) :
    s ∈ (supportedSectionsSubmodule B S hS X.1 X.2 Z' F).toSubmodule.obj (op W) := by
  rw [mem_supportedSectionsSubmodule_iff]
  intro y hy
  have hmem := supportOfSection_subset_preimage_supportOfSheaf B S hS X F W s hy
  rw [Set.mem_preimage, hF] at hmem
  rcases hmem with h | h
  · exact absurd h (hW ⟨y, rfl⟩)
  · exact h

/-! ### The quotient has no sections where the submodule is everything -/

/-- **The quotient of a module by a submodule which contains every section over every chart
below a given one has no sections over that chart.**  A section of the quotient is locally the
image of a section of the module, which lies in the submodule and therefore dies in the
quotient; the quotient is a sheaf, so the section itself is zero. -/
theorem subsingleton_cokernel_val_obj_of_forall_mem (F : Modules.{u, u} B S hS X.1 X.2)
    (N : F.Submodule) (W : SmallEtale B S hS X.1)
    (h : ∀ (W' : SmallEtale B S hS X.1), (W' ⟶ W) →
      ∀ s : F.val.obj (op W'), s ∈ N.toSubmodule.obj (op W')) :
    Subsingleton ((cokernel (C := Modules.{u, u} B S hS X.1 X.2) N.ι).val.obj (op W)) := by
  have hzero : ∀ t : (cokernel (C := Modules.{u, u} B S hS X.1 X.2) N.ι).val.obj (op W),
      t = 0 := by
    intro t
    obtain ⟨Sv, hSv, hcov⟩ :=
      Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
        (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) N.ι) t
    refine (Presheaf.IsSheaf.isSeparated
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) N.ι).isSheaf) W Sv hSv t 0 ?_
    intro Y f hf
    obtain ⟨s, hs⟩ := hcov f hf
    have hz : (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) N.ι).val.app (op Y) s = 0 :=
      (cokernel_π_app_eq_zero_iff B S hS X.1 X.2 N (op Y) s).2 (h Y f s)
    rw [map_zero]
    exact hs.symm.trans hz
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-! ### The support of the quotient -/

/-- **The quotient of `F` by the subsheaf of sections supported in `Z'` is supported in `Z`.**
A chart carrying the unit ideal of the sheaf of ideals cutting out `Z` has image missing `Z`,
and so does every chart below it; over such charts every section of `F` is supported in `Z'`,
so the quotient has no sections there. -/
theorem supportOfSheaf_cokernel_supportedSections_subset
    (F : Modules.{u, u} B S hS X.1 X.2) (Z Z' : Set (points B S hS X.1)) (hZ : IsClosed Z)
    (hF : supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) = Z ∪ Z') :
    supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2
        (cokernel (C := Modules.{u, u} B S hS X.1 X.2)
          (supportedSectionsSubmodule B S hS X.1 X.2 Z' F).ι)) ⊆ Z := by
  have hI := idealZeroLocus_reducedIdealSheaf B S hS X Z hZ
  rw [← hI]
  refine supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS X _
    (reducedIdealSheaf B S hS X Z hZ) fun V hV W g => ?_
  refine subsingleton_cokernel_val_obj_of_forall_mem B S hS X F _ W fun W' g' s => ?_
  refine mem_supportedSectionsSubmodule_of_range_subset_compl B S hS X F Z Z' hF W' ?_ s
  intro x hx
  rw [← hI, Set.mem_compl_iff, mem_idealZeroLocus_iff]
  intro hcon
  obtain ⟨y, hy⟩ := hx
  exact hcon V hV
    ⟨pointsMap B S hS _ (yoneda.map ((SmallEtale.toOver B S hS X.1).map (g' ≫ g))) y,
      (pointsMap_chart_hom B S hS X.1 (g' ≫ g) y).trans hy⟩

/-! ### Stacks 07UP -/

/-- **Stacks 07UP.** Let `X` be a Noetherian algebraic space over a scheme `S` and let `F` be a
coherent `𝒪_X`-module whose support is the union `Z ∪ Z'` of two closed subsets of `|X|`.  Then
there is a short exact sequence `0 → 𝒢' → F → 𝒢 → 0` of coherent `𝒪_X`-modules with `𝒢'`
supported in `Z'` and `𝒢` supported in `Z`.

The sequence produced is the canonical one: `𝒢'` is the subsheaf of sections of `F` supported
in `Z'` and `𝒢` is the quotient of `F` by it.  Quasi-coherence of `𝒢'` is part (3) of
Stacks 0859, whose hypotheses hold because the complement of `Z'` is an open subspace of `X`
and its inclusion is quasi-compact, `X` being Noetherian; `𝒢'` is then coherent by Stacks 07UD
and `𝒢` by Stacks 07UC. -/
@[stacks 07UP]
theorem exists_shortExact_coherent_supportOfSheaf_subset
    (hTop : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hTop X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (Z Z' : Set (points B S hS X.1)) (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (hsupp : supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) = Z ∪ Z') :
    ∃ (G' G : Modules.{u, u} B S hS X.1 X.2) (i : G' ⟶ F) (p : F ⟶ G) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ IsCoherent B S hS X.1 X.2 G' ∧
        IsCoherent B S hS X.1 X.2 G ∧
        supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 G') ⊆ Z' ∧
        supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 G) ⊆ Z := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  have hO : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X.1 Z'ᶜ) :=
    isOpenSubspace_openSubspaceOfPoints B S hS X.2 Z'ᶜ hZ'.isOpen_compl
  have hqc := isQuasicoherentOnSite_supportedSectionsSubmodule B S hS X.2 F
    hF.toIsQuasicoherentOnSite hZ' hO (range_pointsMap_ι_openSubspaceOfPoints B S hS Z'ᶜ)
    (isQuasiCompact_ι_of_isNoetherian B S hS hTop X.2 hN hO)
  have hG' := isCoherent_of_mono_of_isQuasicoherentOnSite B S hS X.1 X.2
    (supportedSectionsSubmodule B S hS X.1 X.2 Z' F).ι hqc hF
  exact ⟨(supportedSectionsSubmodule B S hS X.1 X.2 Z' F).toSheafOfModules,
    cokernel (C := Modules.{u, u} B S hS X.1 X.2)
      (supportedSectionsSubmodule B S hS X.1 X.2 Z' F).ι,
    (supportedSectionsSubmodule B S hS X.1 X.2 Z' F).ι,
    cokernel.π (C := Modules.{u, u} B S hS X.1 X.2)
      (supportedSectionsSubmodule B S hS X.1 X.2 Z' F).ι,
    cokernel.condition _,
    shortExact_submoduleQuotientShortComplex B S hS X F
      (supportedSectionsSubmodule B S hS X.1 X.2 Z' F),
    hG', isCoherent_cokernel B S hS X.1 X.2 hG' hF _,
    supportOfSheaf_supportedSectionsSubmodule_subset B S hS X Z' F,
    supportOfSheaf_cokernel_supportedSections_subset B S hS X F Z Z' hZ hsupp⟩

end AlgebraicGeometry.Space

end
