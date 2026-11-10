module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedBasicOpenNonempty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# The support of a nonzero sheaf of ideals on a reduced irreducible algebraic space

Let `Z` be an algebraic space over a scheme `S` which is étale-locally reduced and whose space
of points is irreducible, and let `I ⊆ 𝒪_Z` be a nonzero sheaf of ideals of finite type on the
small étale site.  Then the support of `I` is all of `|Z|`.

## Main results

* `AlgebraicGeometry.Space.idealUnitLocus_subset_supportOfSheaf`: the unit locus of a sheaf of
  ideals, the set of points lying on a chart over which it is the whole structure sheaf, is
  contained in its support.
* `AlgebraicGeometry.Space.isReduced_chartScheme`: every étale chart of an étale-locally
  reduced algebraic space is a reduced scheme, and
  `AlgebraicGeometry.Space.isUnit_chartRestrict_basicOpenChart`: a regular function on a chart
  restricts to a unit on the chart cut out by its non-vanishing locus, with no affineness
  hypothesis.
* `AlgebraicGeometry.Space.idealUnitLocus_nonempty_of_exists_section_ne_zero` and
  `AlgebraicGeometry.Space.idealUnitLocus_nonempty_of_ne_bot`: on a reduced algebraic space the
  unit locus of a nonzero sheaf of ideals is nonempty.
* `AlgebraicGeometry.Space.dense_supportOfSheaf_of_exists_section_ne_zero`: on a reduced
  algebraic space with irreducible space of points the support of a nonzero sheaf of ideals is
  dense.
* `AlgebraicGeometry.Space.supportOfSheaf_eq_univ_of_ne_bot`: **the support of a nonzero sheaf
  of ideals of finite type on a reduced algebraic space with irreducible space of points is
  everything.**
* `AlgebraicGeometry.Space.supportOfSheaf_quasicoherentIdeal_eq_univ` and
  `AlgebraicGeometry.Space.supportOfSheaf_quasicoherentIdeal_closedSubspace_eq_univ`: the same
  statement for a `AlgebraicGeometry.Space.QuasicoherentIdeals` on a locally Noetherian space,
  and for a quasi-coherent sheaf of ideals on a reduced closed subspace with irreducible space
  of points.
* `SheafOfModules.Submodule.toSubmodule_bot` and `SheafOfModules.Submodule.obj_eq_bot`: the
  bottom submodule of a sheaf of modules is the zero family of submodules.
* `SheafOfModules.Submodule.mono_ι_via_forget`: the inclusion of a submodule of a sheaf of
  modules is a monomorphism.

## References

* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SheafOfModules.Submodule

/-- The bottom submodule of a sheaf of modules is the zero family of submodules. -/
theorem toSubmodule_bot {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) :
    (⊥ : M.Submodule).toSubmodule = ⊥ := by
  let N : M.Submodule :=
    { toSubmodule := ⊥
      isSheaf := by
        intro V s hs
        refine (((isSheaf_iff_isSheaf_of_type J
            (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u})).mp
          (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)) _ hs).isSeparatedFor.ext
          fun V' g hg ↦ ?_
        have hsection : M.val.map g.op s ∈ (⊥ : M.val.Submodule).obj (op V') := hg
        have hzero : M.val.map g.op s = 0 := (_root_.Submodule.mem_bot _).1 hsection
        change M.val.map g.op s = M.val.map g.op 0
        simpa using hzero }
  exact le_antisymm (SheafOfModules.Submodule.le_iff.1 (bot_le (a := N))) bot_le

/-- The inclusion of a submodule of a sheaf of modules is a monomorphism. -/
theorem mono_ι_via_forget {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R} (N : M.Submodule) : Mono N.ι :=
  (SheafOfModules.forget R).mono_of_mono_map (inferInstanceAs (Mono N.toSubmodule.ι))

/-- The bottom submodule of a sheaf of modules has no nonzero section over any object. -/
theorem obj_eq_bot {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) (V : Cᵒᵖ) :
    (⊥ : M.Submodule).obj V = ⊥ :=
  congrFun (congrArg PresheafOfModules.Submodule.obj (toSubmodule_bot M)) V

end SheafOfModules.Submodule

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### A chart with a point has a nonzero ring of regular functions -/

/-- The regular functions on an étale chart which has a point do not form the zero ring. -/
private theorem one_ne_zero_chartRing_of_point (V : SmallEtale B S hS X.1)
    (w : chartScheme V) : (1 : (structureRingSheaf B S hS X).obj.obj (op V)) ≠ 0 := by
  intro h
  have h' : (1 : Γ(chartScheme V, ⊤)) = 0 := h
  have h2 := congrArg ((chartScheme V).presheaf.germ ⊤ w trivial) h'
  simp at h2

/-- A sheaf of ideals containing the unit section over a chart is the whole structure sheaf
there. -/
theorem unit_obj_eq_top_of_one_mem
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {V : (SmallEtale B S hS X.1)ᵒᵖ}
    (h : SheafOfModules.unitOf (1 : (structureRingSheaf B S hS X).obj.obj V) ∈ I.obj V) :
    I.obj V = ⊤ :=
  Ideal.eq_top_of_isUnit_mem (I.obj V) h isUnit_one

/-- A sheaf of ideals containing a section which is a unit over a chart is the whole structure
sheaf there. -/
theorem unit_obj_eq_top_of_isUnit
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {V : (SmallEtale B S hS X.1)ᵒᵖ} {t : (structureRingSheaf B S hS X).obj.obj V}
    (ht : SheafOfModules.unitOf t ∈ I.obj V) (hu : IsUnit t) : I.obj V = ⊤ :=
  Ideal.eq_top_of_isUnit_mem (I.obj V) ht hu

/-! ### The unit locus is contained in the support -/

/-- **The unit locus of a sheaf of ideals is contained in its support.** -/
theorem idealUnitLocus_subset_supportOfSheaf
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) :
    idealUnitLocus B S hS X I ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj I.toSheafOfModules) := by
  rintro x ⟨V, hV, y, rfl⟩
  rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X.1 X.2
    ((SheafOfModules.toSheaf _).obj I.toSheafOfModules)]
  have hone : SheafOfModules.unitOf (1 : (structureRingSheaf B S hS X).obj.obj (op V)) ∈
      I.obj (op V) := hV.ge _root_.Submodule.mem_top
  refine Set.mem_iUnion.2 ⟨V, Set.mem_iUnion.2 ⟨⟨_, hone⟩, ⟨y, ?_, rfl⟩⟩⟩
  rintro ⟨W, g, hzero, z, -⟩
  exact one_ne_zero_chartRing_of_point B S hS X W (pointsToScheme B S hS _ z)
    ((PresheafOfModules.unit_map_one _ g.op).symm.trans (congrArg Subtype.val hzero))

/-! ### A nonzero sheaf of ideals has a nonempty unit locus -/

/-- Every étale chart of an étale-locally reduced algebraic space is a reduced scheme, by
Stacks 03E8. -/
theorem isReduced_chartScheme
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (V : SmallEtale B S hS X.1) : IsReduced (chartScheme V) :=
  (exists_atlas_iff_forall_etale B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y) X.2).mp hred
    V.obj.left V.obj.hom V.property

/-- **The restriction of a regular function to the étale chart cut out by its non-vanishing
locus is a unit.** -/
theorem isUnit_chartRestrict_basicOpenChart (V : SmallEtale B S hS X.1)
    (t : (structureRingSheaf B S hS X).obj.obj (op V)) :
    IsUnit (chartRestrict (hF := X.2)
      (openChartInclusion B S hS X.1 V ((chartScheme V).basicOpen t)) t) := by
  rw [chartRestrict_eq_appTop, toScheme_map_toOver_map_openChartInclusion]
  exact isUnit_appTop_basicOpen (chartScheme V) t

/-- **On a reduced algebraic space a sheaf of ideals with a nonzero section has a nonempty unit
locus.** -/
theorem idealUnitLocus_nonempty_of_exists_section_ne_zero
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (V : SmallEtale B S hS X.1) (t : (structureRingSheaf B S hS X).obj.obj (op V))
    (ht : SheafOfModules.unitOf t ∈ I.obj (op V)) (ht0 : t ≠ 0) :
    (idealUnitLocus B S hS X I).Nonempty := by
  have _ : IsReduced (chartScheme V) := isReduced_chartScheme B S hS X hred V
  set O : (chartScheme V).Opens := (chartScheme V).basicOpen t with hO
  obtain ⟨c, hc⟩ : ((O : (chartScheme V).Opens) : Set (chartScheme V)).Nonempty :=
    nonempty_basicOpen_of_ne_zero (chartScheme V) ht0
  set W : SmallEtale B S hS X.1 := openChart B S hS X.1 V O with hW
  have htop : I.obj (op W) = ⊤ := by
    refine unit_obj_eq_top_of_isUnit B S hS X I
      (t := chartRestrict (hF := X.2) (openChartInclusion B S hS X.1 V O) t) ?_
      (isUnit_chartRestrict_basicOpenChart B S hS X V t)
    exact I.map_mem (openChartInclusion B S hS X.1 V O).op ht
  obtain ⟨p, -⟩ := surjective_pointsToScheme B S hS
    ((SmallEtale.toOver B S hS X.1).obj W) (⟨c, hc⟩ : (O : Type u))
  exact ⟨_, W, htop, p, rfl⟩

/-- A sheaf of ideals which is not the zero sheaf of ideals has a nonzero section over some
chart. -/
theorem exists_section_ne_zero_of_ne_bot
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) (hI : I ≠ ⊥) :
    ∃ (V : SmallEtale B S hS X.1) (t : (structureRingSheaf B S hS X).obj.obj (op V)),
      SheafOfModules.unitOf t ∈ I.obj (op V) ∧ t ≠ 0 := by
  by_contra hcon
  refine hI (le_bot_iff.1 ?_)
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 fun V ↦ ?_)
  rw [SheafOfModules.Submodule.obj_eq_bot]
  exact fun s hs ↦ (_root_.Submodule.mem_bot _).2 (of_not_not fun hs0 ↦ hcon ⟨V.unop, s, hs, hs0⟩)

/-- **On a reduced algebraic space the unit locus of a nonzero sheaf of ideals is nonempty.** -/
theorem idealUnitLocus_nonempty_of_ne_bot
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule) (hI : I ≠ ⊥) :
    (idealUnitLocus B S hS X I).Nonempty := by
  obtain ⟨V, t, ht, ht0⟩ := exists_section_ne_zero_of_ne_bot B S hS X I hI
  exact idealUnitLocus_nonempty_of_exists_section_ne_zero B S hS X hred I V t ht ht0

/-! ### Density, and the support of a nonzero sheaf of ideals of finite type -/

/-- **On a reduced algebraic space with irreducible space of points the support of a nonzero
sheaf of ideals is dense.** -/
theorem dense_supportOfSheaf_of_exists_section_ne_zero
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (V : SmallEtale B S hS X.1) (t : (structureRingSheaf B S hS X).obj.obj (op V))
    (ht : SheafOfModules.unitOf t ∈ I.obj (op V)) (ht0 : t ≠ 0) :
    Dense (supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf _).obj I.toSheafOfModules)) :=
  ((isOpen_idealUnitLocus B S hS X I).dense
    (idealUnitLocus_nonempty_of_exists_section_ne_zero B S hS X hred I V t ht ht0)).mono
    (idealUnitLocus_subset_supportOfSheaf B S hS X I)

/-- **The support of a nonzero sheaf of ideals of finite type on a reduced algebraic space with
irreducible space of points is everything.** -/
theorem supportOfSheaf_eq_univ_of_exists_section_ne_zero
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hft : SheafOfModules.IsFiniteTypeOnSite I.toSheafOfModules)
    (V : SmallEtale B S hS X.1) (t : (structureRingSheaf B S hS X).obj.obj (op V))
    (ht : SheafOfModules.unitOf t ∈ I.obj (op V)) (ht0 : t ≠ 0) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj I.toSheafOfModules) =
      Set.univ := by
  have hclosed : IsClosed (supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf _).obj I.toSheafOfModules)) :=
    @isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 I.toSheafOfModules hft
  exact hclosed.closure_eq ▸
    (dense_supportOfSheaf_of_exists_section_ne_zero B S hS X hred hirr I V t ht ht0).closure_eq

/-- **The support of a nonzero sheaf of ideals of finite type on a reduced algebraic space with
irreducible space of points is everything.** -/
theorem supportOfSheaf_eq_univ_of_ne_bot
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hft : SheafOfModules.IsFiniteTypeOnSite I.toSheafOfModules) (hI : I ≠ ⊥) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj I.toSheafOfModules) =
      Set.univ := by
  obtain ⟨V, t, ht, ht0⟩ := exists_section_ne_zero_of_ne_bot B S hS X I hI
  exact supportOfSheaf_eq_univ_of_exists_section_ne_zero B S hS X hred hirr I hft V t ht ht0

/-! ### Quasi-coherent sheaves of ideals -/

/-- A quasi-coherent sheaf of ideals on a locally Noetherian algebraic space is of finite type
on the small étale site. -/
theorem isFiniteTypeOnSite_quasicoherentIdeal
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (I : QuasicoherentIdeals B S hS X) :
    SheafOfModules.IsFiniteTypeOnSite I.1.toSheafOfModules := by
  have hcoh : IsCoherent B S hS X.1 X.2 I.1.toSheafOfModules :=
    @isCoherent_of_mono_of_isQuasicoherentOnSite B S hS X.1 X.2 ⟨hN⟩ _ _ I.1.ι
      (SheafOfModules.Submodule.mono_ι_via_forget I.1) I.2
      (@isCoherent_structureSheaf B S hS X.1 X.2 ⟨hN⟩)
  exact @isFiniteTypeOnSite_of_isCoherentOnSite B S hS X I.1.toSheafOfModules
    hcoh.toIsCoherentOnSite

/-- **The support of a nonzero quasi-coherent sheaf of ideals on a locally Noetherian, reduced
algebraic space with irreducible space of points is everything.** -/
theorem supportOfSheaf_quasicoherentIdeal_eq_univ
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hred : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsReduced V))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (I : QuasicoherentIdeals B S hS X) (hI : I.1 ≠ ⊥) :
    supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf _).obj I.1.toSheafOfModules) = Set.univ :=
  supportOfSheaf_eq_univ_of_ne_bot B S hS X hred hirr I.1
    (isFiniteTypeOnSite_quasicoherentIdeal B S hS X hN I) hI

/-! ### Quasi-coherent sheaves of ideals on a closed subspace -/

section ClosedSubspace

variable {W : AlgebraicSpaces B S hS}

/-- Let `Z ⊆ W` be a closed subspace of an algebraic space which is reduced with irreducible
space of points and locally Noetherian. Then the support of a nonzero quasi-coherent sheaf of
ideals `I ⊆ 𝒪_Z` is the whole of `|Z|`. -/
theorem supportOfSheaf_quasicoherentIdeal_closedSubspace_eq_univ {Z : Subfunctor W.1}
    (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (hN : HasEtaleLocalProperty B S hS Z.toFunctor
      (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)) (hI : I.1 ≠ ⊥) :
    supportOfSheaf B S hS Z.toFunctor
      ((SheafOfModules.toSheaf _).obj I.1.toSheafOfModules) = Set.univ :=
  supportOfSheaf_quasicoherentIdeal_eq_univ B S hS (closedSubfunctorSpace B S hS hZ) hN
    hint.1 hint.2 I hI

end ClosedSubspace

end AlgebraicGeometry.Space

end
