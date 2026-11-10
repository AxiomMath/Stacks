module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections of an invertible module of nonpositive degree on a connected curve

Let `k` be a field and `X` a proper scheme over `k` which is reduced, connected and
equidimensional of dimension one, and let `ℒ` be an invertible `𝒪_X`-module whose restriction to
every irreducible component of `X` has degree `≤ 0`. Then either `H⁰(X, ℒ) = 0` or `ℒ ≅ 𝒪_X`.

## Main definitions

* `AlgebraicGeometry.VanishingSectionDegreePos`: part (2) of [Stacks, Tag 0B40] as a
  proposition about `k`, quantified over every proper integral scheme of dimension at most one
  over `k` and every invertible module on it.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `nonvanishingLocus_sectionsOfTop_eq`: the two spellings of the nonvanishing locus of a global
  section agree.
* `eval_top_ne_zero_of_mem_nonvanishingLocus`: a section with a nonempty nonvanishing locus is
  nonzero.
* `nonempty_nonvanishingLocus_of_ne_zero`: on a reduced scheme the nonvanishing locus of a
  nonzero global section of an invertible module is nonempty.
* `isTrivial_of_nonvanishingLocus_eq_univ`: an invertible module with a nowhere vanishing global
  section is isomorphic to the structure sheaf.
* `vanishingSectionDegreePos`: part (2) of [Stacks, Tag 0B40], i.e. the proposition
  `VanishingSectionDegreePos k` for every field `k`.
* `subset_nonvanishingLocus_of_mem_nonvanishingLocus`: an irreducible component on which the
  degree is nonpositive and which meets the nonvanishing locus of a global section is contained
  in it.
* `subsingleton_globalSections_or_isTrivial_of_invertibleCurveDegree_nonpos`: if `ℒ` has
  nonpositive degree on every irreducible component of a reduced connected proper curve, then
  either `H⁰(X, ℒ) = 0` or `ℒ ≅ 𝒪_X`.

## References

* [Stacks Project, Tag 0E22](https://stacks.math.columbia.edu/tag/0E22)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules (nonvanishingLocus nonvanishingOpen sectionsOfTop
  modulePullbackSection)
open Stacks.SheafOfModules.TensorStalkRingedSpace (grpGerm grpStalk ringStalk)

universe u

namespace AlgebraicGeometry

/-! ### Elementary facts about the nonvanishing locus of a global section -/

section Locus

variable {X : Scheme.{u}}

/-- **The two spellings of the nonvanishing locus agree.** The locus computed in the stalk
module of [Stacks, Tag 01CB] for the compatible family of restrictions of a global section `s` is
the locus `Stacks.Ample.nonvanishingLocus` of `s` itself. -/
theorem nonvanishingLocus_sectionsOfTop_eq (L : X.Modules) (s : Γ(L, ⊤)) :
    nonvanishingLocus (X := X.toRingedSpace) L (sectionsOfTop L s)
      = Stacks.Ample.nonvanishingLocus L s := by
  have h : ((Stacks.NonvanishingSpelling.sectionsEquiv X L).symm s).eval (op ⊤) = s :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X L).apply_symm_apply s
  calc nonvanishingLocus (X := X.toRingedSpace) L (sectionsOfTop L s)
      = nonvanishingLocus (X := X.toRingedSpace) L (sectionsOfTop L
          (((Stacks.NonvanishingSpelling.sectionsEquiv X L).symm s).eval (op ⊤))) := by rw [h]
    _ = nonvanishingLocus (X := X.toRingedSpace) L
          ((Stacks.NonvanishingSpelling.sectionsEquiv X L).symm s) :=
        Stacks.SheafOfModules.nonvanishingLocus_sectionsOfTop_eval _ _
    _ = Stacks.Ample.nonvanishingLocus L s :=
        Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X L s

/-- **A global section that fails to vanish somewhere is nonzero.** -/
theorem eval_top_ne_zero_of_mem_nonvanishingLocus (L : X.Modules) (s : L.sections) {x : X}
    (hx : x ∈ nonvanishingLocus (X := X.toRingedSpace) L s) : s.eval (op ⊤) ≠ 0 := by
  intro h
  refine hx ?_
  rw [show grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) = 0 from by
    rw [h]; exact map_zero _]
  exact Submodule.zero_mem _

/-- **On a reduced scheme the nonvanishing locus of a nonzero global section of an invertible
module is nonempty.** -/
theorem nonempty_nonvanishingLocus_of_ne_zero [IsReduced X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    (nonvanishingLocus (X := X.toRingedSpace) L (sectionsOfTop L s)).Nonempty := by
  rw [nonvanishingLocus_sectionsOfTop_eq, Set.nonempty_iff_ne_empty]
  intro hempty
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  have hres : ∀ x : X, L.presheaf.map (homOfLE (le_top (a := V x))).op s = 0 := by
    intro x
    obtain ⟨t⟩ := htriv x
    have hb : X.basicOpen (Stacks.NonvanishingOpen.trivTop t s) = ⊥ := by
      refine TopologicalSpace.Opens.ext ?_
      rw [← Stacks.NonvanishingOpen.nonvanishingLocus_inter t s, hempty, Set.empty_inter]
      rfl
    rw [show L.presheaf.map (homOfLE (le_top (a := V x))).op s
        = Stacks.NonvanishingOpen.trivTop t s • Stacks.NonvanishingOpen.basis t from
      Stacks.NonvanishingOpen.eq_triv_smul_basis t _, (basicOpen_eq_bot_iff _).mp hb, zero_smul]
  refine hs (TopCat.Sheaf.eq_of_locally_eq'
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj L) V ⊤ (fun x => homOfLE le_top)
    (by rw [hV]) s 0 fun x => ?_)
  exact (hres x).trans (map_zero _).symm

/-- **An invertible module with a nowhere vanishing global section is isomorphic to the structure
sheaf.** -/
theorem isTrivial_of_nonvanishingLocus_eq_univ (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (s : L.sections)
    (hs : nonvanishingLocus (X := X.toRingedSpace) L s = Set.univ) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.2 L := by
  have _ : ∀ x : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace x) :=
    fun x => X.isLocalRing x
  have hLs : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hle : ∀ V : X.Opens, V ≤ nonvanishingOpen (X := X.toRingedSpace) L s := by
    intro V x _
    change x ∈ nonvanishingLocus (X := X.toRingedSpace) L s
    rw [hs]
    exact Set.mem_univ x
  have hiso : IsIso (L.unitHomEquiv.symm s) :=
    Stacks.SheafOfModules.isIso_of_isIso_val_app _ fun A => by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen
        (X := X.toRingedSpace) L s A.unop (hle A.unop)
  exact ⟨(@asIso _ _ _ _ (L.unitHomEquiv.symm s) hiso).symm⟩

end Locus

/-! ### Part (2) of Stacks Tag 0B40, in the form the argument below uses -/

/-- **Part (2) of [Stacks, Tag 0B40] as a proposition about the field `k`**: on every proper
integral scheme of dimension at most one over `k`, a nonzero global section of an invertible
module which vanishes at some point forces the degree of that module to be positive. -/
def VanishingSectionDegreePos (k : Type u) [Field k] : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) (hg : IsProper g) (_ : IsIntegral Y)
    (hd : topologicalKrullDim (Y : Type u) ≤ 1) (M : Y.Modules)
    (hM : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M) (t : M.sections),
    t.eval (op ⊤) ≠ 0 →
    (∃ y : Y, y ∉ nonvanishingLocus (X := Y.toRingedSpace) M t) →
    0 < @invertibleCurveDegree k _ Y g hg hd M hM

/-- **Part (2) of [Stacks, Tag 0B40] holds**, in the quantified form
`AlgebraicGeometry.VanishingSectionDegreePos`. -/
theorem vanishingSectionDegreePos (k : Type u) [Field k] : VanishingSectionDegreePos k :=
  fun _Y g hg hint hd M hM t ht hzero =>
    @invertibleCurveDegree_pos_of_eval_top_ne_zero k _ _ g hg hint hd M hM t ht hzero

/-! ### Stacks Tag 0E22 -/

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **An irreducible component meeting the nonvanishing locus of a global section is contained in
it**, provided the degree of the module on that component is nonpositive. -/
theorem subset_nonvanishingLocus_of_mem_nonvanishingLocus
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {C : Set X} (hC : C ∈ irreducibleComponents (X : Type u))
    (hdeg :
      haveI : SheafOfModules.IsInvertible
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subscheme.presheaf
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subscheme.ringCatSheaf.2
          ((RingedSpaceModuleAdjunction.modulePullback
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι.toLRSHom.toShHom).obj
            L) :=
        RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ L
      invertibleCurveDegree k
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι ≫ f)
          ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι).trans hdim)
          ((RingedSpaceModuleAdjunction.modulePullback
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι.toLRSHom.toShHom).obj
            L) ≤ 0)
    (s : L.sections) {x : X} (hxC : x ∈ C)
    (hx : x ∈ nonvanishingLocus (X := X.toRingedSpace) L s) :
    C ⊆ nonvanishingLocus (X := X.toRingedSpace) L s := by
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
  have hrange : Set.range I.subschemeι = C :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  have hint : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hC.1
  have hMinv : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback I.subschemeι.toLRSHom.toShHom).obj L) :=
    RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ L
  set S := nonvanishingLocus (X := I.subscheme.toRingedSpace)
    ((RingedSpaceModuleAdjunction.modulePullback I.subschemeι.toLRSHom.toShHom).obj L)
    (modulePullbackSection I.subschemeι.toLRSHom L s)
  have hpre : I.subschemeι.base ⁻¹' nonvanishingLocus (X := X.toRingedSpace) L s = S :=
    Stacks.SheafOfModules.preimage_nonvanishingLocus I.subschemeι.toLRSHom L s
  obtain ⟨y, hy⟩ : x ∈ Set.range I.subschemeι := hrange ▸ hxC
  have hynv : y ∈ S := by
    rw [← hpre]
    simpa only [Set.mem_preimage, hy] using hx
  have hall : ∀ z : I.subscheme, z ∈ S := by
    intro z
    by_contra hz
    exact absurd (vanishingSectionDegreePos k I.subscheme (I.subschemeι ≫ f) inferInstance hint
      ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion I.subschemeι).trans hdim) _
      hMinv _ (eval_top_ne_zero_of_mem_nonvanishingLocus _ _ hynv) ⟨z, hz⟩) (not_lt.mpr hdeg)
  intro w hw
  obtain ⟨z, rfl⟩ : w ∈ Set.range I.subschemeι := hrange ▸ hw
  exact (Set.ext_iff.1 hpre z).2 (hall z)

/-- Let `k` be a field and `X` a proper scheme over `k` which is reduced, connected and
equidimensional of dimension one, and let `ℒ` be an invertible `𝒪_X`-module whose restriction to
every irreducible component of `X` has degree `≤ 0`. Then either `H⁰(X, ℒ) = 0` or `ℒ ≅ 𝒪_X`. -/
@[stacks 0E22]
theorem subsingleton_globalSections_or_isTrivial_of_invertibleCurveDegree_nonpos [IsReduced X]
    [ConnectedSpace X] (_hequi : TopologicalSpace.Equidimensional (X : Type u))
    (hdim : topologicalKrullDim (X : Type u) = 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : ∀ (C : Set X) (hC : C ∈ irreducibleComponents (X : Type u)),
      haveI : SheafOfModules.IsInvertible
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subscheme.presheaf
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subscheme.ringCatSheaf.2
          ((RingedSpaceModuleAdjunction.modulePullback
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι.toLRSHom.toShHom).obj
            L) :=
        RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ L
      invertibleCurveDegree k
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι ≫ f)
          ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι).trans hdim.le)
          ((RingedSpaceModuleAdjunction.modulePullback
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι.toLRSHom.toShHom).obj
            L) ≤ 0) :
    Subsingleton Γ(L, ⊤) ∨ SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.2 L := by
  classical
  by_cases hsub : Subsingleton Γ(L, ⊤)
  · exact Or.inl hsub
  right
  have _ : Nontrivial Γ(L, ⊤) := not_subsingleton_iff_nontrivial.mp hsub
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(L, ⊤))
  have _ : ∀ x : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace x) :=
    fun x => X.isLocalRing x
  have hLs : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  set sf : L.sections := sectionsOfTop L s
  set U : Set X := nonvanishingLocus (X := X.toRingedSpace) L sf
  have hUopen : IsOpen U := Stacks.SheafOfModules.isOpen_nonvanishingLocus
    (X := X.toRingedSpace) L sf
  have hUne : U.Nonempty := nonempty_nonvanishingLocus_of_ne_zero L s hs
  have hcov : ∀ x : X, ∀ C ∈ irreducibleComponents (X : Type u), x ∈ C → x ∈ U → C ⊆ U :=
    fun x C hC hxC hxU => subset_nonvanishingLocus_of_mem_nonvanishingLocus k f hdim.le L hC
      (hdeg C hC) sf hxC hxU
  have hfin : (irreducibleComponents (X : Type u)).Finite := by
    have _ : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
    have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have _ : IsNoetherian X := {}
    exact finite_irreducibleComponents_of_isNoetherian
  have hUeq : U = ⋃₀ {C | C ∈ irreducibleComponents (X : Type u) ∧ C ⊆ U} := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp
        (show x ∈ ⋃₀ irreducibleComponents (X : Type u) by
          rw [sUnion_irreducibleComponents]; exact Set.mem_univ x)
      exact Set.mem_sUnion.mpr ⟨C, ⟨hC, hcov x C hC hxC hx⟩, hxC⟩
    · obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
      exact hC.2 hxC
  have hUclosed : IsClosed U := by
    rw [hUeq, Set.sUnion_eq_biUnion]
    exact (hfin.subset fun C hC => hC.1).isClosed_biUnion fun C hC =>
      isClosed_of_mem_irreducibleComponents C hC.1
  exact isTrivial_of_nonvanishingLocus_eq_univ L sf (IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne)

end AlgebraicGeometry

end
