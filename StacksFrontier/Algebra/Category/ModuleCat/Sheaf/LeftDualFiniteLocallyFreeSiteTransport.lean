module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Finite local freeness transported to a small model of a site, and the dual of Stacks 0FNY

Let `e : C' ≌ C` be an equivalence of sites, with independent universes for `C` and `C'`, as for
a site and a small model of it. A sheaf of modules on `(C, J)` which is finite locally free,
`SheafOfModules.IsFiniteLocallyFreeOnSite`, has a transport along `e` which is locally a direct
summand of a finite free module on `(C', J')`, and it has a right dual.

## Main definitions

* `Stacks.SheafOfModules.freeIsoOfIsColimitCofan`: the isomorphism of the point of a colimiting
  cofan of `n` copies of the structure sheaf with `SheafOfModules.free (ULift (Fin n))`.
* `Stacks.SheafOfModules.hasRightDualOfIsFiniteLocallyFreeOnSite`: a finite locally free sheaf
  of modules has a right dual, through an equivalence with a site at other universes.

## Main results

* `Stacks.SheafOfModules.exists_retract_free_of_isFiniteFree`: a finite free sheaf of modules is
  a retract of `SheafOfModules.free I` for a finite `I`.
* `Stacks.SheafOfModules.exists_retract_free_over_reindex`: the same on a slice `C'/V` for the
  transported module, when the module is finite free on `C/e(V)`.
* `Stacks.SheafOfModules.exists_coveringSieve_retract_free_reindex`: the sieve-shaped transport
  of finite local freeness, for an arbitrary sheaf of rings.
* `Stacks.SheafOfModules.isLocallyDirectSummandOfFiniteFree_reindex`: the transported module is
  locally a direct summand of a finite free module.

## References

* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE) — finite freeness.
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL) (2) — finite local
  freeness.
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM) — intrinsicness of the
  local conditions.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the monoidal structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace Stacks.SheafOfModules

/-! ### A finite free sheaf of modules is a retract of a finite free one -/

section FiniteFree

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R : Sheaf J RingCat.{w}}

/-- A colimiting cofan of `n` copies of the structure sheaf with point `F` identifies `F` with
the free sheaf of modules on `ULift (Fin n)`. -/
noncomputable def freeIsoOfIsColimitCofan {F : _root_.SheafOfModules.{w} R} {n : ℕ}
    (ι : Fin n → (_root_.SheafOfModules.unit R ⟶ F)) (hc : IsColimit (Cofan.mk F ι)) :
    F ≅ _root_.SheafOfModules.free.{w} (R := R) (ULift.{w} (Fin n)) :=
  (Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk F ι) hc).coconePointUniqueUpToIso
    (_root_.SheafOfModules.isColimitFreeCofan (R := R) (ULift.{w} (Fin n)))

/-- **A finite free sheaf of modules is a retract of `SheafOfModules.free I` for a finite index
type `I`** (finite freeness as in Stacks 03DE (2)). -/
theorem exists_retract_free_of_isFiniteFree (F : _root_.SheafOfModules.{w} R)
    (h : _root_.SheafOfModules.IsFiniteFree R F) :
    ∃ I : Type w, Finite I ∧
      Nonempty (Retract F (_root_.SheafOfModules.free.{w} (R := R) I)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R F).1 h
  exact ⟨ULift.{w} (Fin n), inferInstance, ⟨Retract.ofIso (freeIsoOfIsColimitCofan ι hc)⟩⟩

end FiniteFree

/-! ### The transport along an equivalence of sites, at independent universes -/

section Reindex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})
  [∀ V : C', HasWeakSheafify (J'.over V) AddCommGrpCat.{w}]
  [∀ V : C', (J'.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- If the restriction of `M` to `e.functor.obj V` is finite free, then the restriction to `V`
of the reindexing of `M` is a retract of a free sheaf of modules on a finite index type. -/
theorem exists_retract_free_over_reindex (M : _root_.SheafOfModules.{w} R) (V : C')
    (h : _root_.SheafOfModules.IsFiniteFree (R.over (e.functor.obj V))
      (M.over (e.functor.obj V))) :
    ∃ I : Type w, Finite I ∧ Nonempty (Retract
      (((_root_.SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V)
      (_root_.SheafOfModules.free.{w} (R := (reindexRing J' e R).over V) I)) := by
  refine exists_retract_free_of_isFiniteFree _ ?_
  rw [_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit] at h ⊢
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  exact ⟨n, _, ⟨isColimitCofanTransport
    (reindexEquivalence (J' := J'.over V) (Over.postEquiv (X := V) e) (R.over (e.functor.obj V)))
    (Iso.refl _) (Iso.refl _) ι hc⟩⟩

variable [e.functor.IsCocontinuous J' J]

/-- **The transport of finite local freeness to a sieve-shaped local hypothesis, at independent
site universes.**  If `M` is finite locally free on `(C, J)` in the sense of Stacks 03DL (2),
then every object `U` of `C'` carries a covering sieve on whose members the reindexing of `M`
is a retract of a free sheaf of modules on a finite index type. -/
theorem exists_coveringSieve_retract_free_reindex (M : _root_.SheafOfModules.{w} R)
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) (U : C') :
    ∃ S : Sieve U, S ∈ J' U ∧ ∀ (V : C') (i : V ⟶ U), S i →
      ∃ I : Type w, Finite I ∧ Nonempty (Retract
        (((_root_.SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V)
        (_root_.SheafOfModules.free.{w} (R := (reindexRing J' e R).over V) I)) := by
  obtain ⟨I, W, g, hcov, hfree⟩ := hM (e.functor.obj U)
  refine ⟨(Sieve.ofArrows W g).functorPullback e.functor,
    e.functor.cover_lift J' J hcov, fun V i hi ↦ ?_⟩
  obtain ⟨j, a, -⟩ := (Sieve.mem_ofArrows_iff W g (e.functor.map i)).1 hi
  exact exists_retract_free_over_reindex e R M V
    ((_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2
      (exists_isColimitCofan_over_of_le M a
        ((_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).1 (hfree j))))

end Reindex

/-! ### The local hypothesis of Stacks 0FNY, and the dual -/

section LocalSummand

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (O : Cᵒᵖ ⥤ CommRingCat.{max u' v'})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsCocontinuous J' J]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  [HasWeakSheafify J AddCommGrpCat.{max u' v'}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  [HasWeakSheafify J' AddCommGrpCat.{max u' v'}]
  [∀ V : C', HasWeakSheafify (J'.over V) AddCommGrpCat.{max u' v'}]
  [∀ V : C', (J'.over V).WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  (hO' : Presheaf.IsSheaf J' (TensorSheafification.structureRingPresheaf
    (ReindexLeftDual.reindexRingPresheaf O e)))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  [HasWeakSheafify J AddCommGrpCat.{max u' v'}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  [HasWeakSheafify J' AddCommGrpCat.{max u' v'}] in
/-- **Finite local freeness on `(C, J)` makes the reindexed module locally a direct summand of a
finite free module on `(C', J')`**, at independent site universes. -/
theorem isLocallyDirectSummandOfFiniteFree_reindex
    (M : _root_.SheafOfModules.{max u' v'} (TensorSheafification.structureSheaf O hO))
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    IsLocallyDirectSummandOfFiniteFree (ReindexLeftDual.reindexRingPresheaf O e) hO'
      ((TensorPower.whiskerRestriction (J' := J') O hO e.functor).obj M) :=
  fun U ↦ exists_coveringSieve_retract_free_reindex e
    (TensorSheafification.structureSheaf O hO) M hM U

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u' v'} RingCat.{max u' v'})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{max u' v'} RingCat.{max u' v'})]

/-- **A finite locally free sheaf of modules has a right dual.** Let `e : C' ≌ C` be an
equivalence of sites, continuous in both directions and cocontinuous in the forward one, with the
rings and modules living at `max u' v'`. Then a sheaf of `O`-modules which is finite locally free
in the sense of Stacks 03DL (2) has a right dual in `Stacks.SheafOfModules.monoidalCategory`, the
monoidal structure of Stacks 01CA. -/
@[instance_reducible]
noncomputable def hasRightDualOfIsFiniteLocallyFreeOnSite
    (M : _root_.SheafOfModules.{max u' v'} (TensorSheafification.structureSheaf O hO))
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    letI := Stacks.SheafOfModules.monoidalCategory O hO
    HasRightDual M :=
  ReindexLeftDual.hasRightDualOfReindexLocalSummandExplicit O hO e hO' M
    (isLocallyDirectSummandOfFiniteFree_reindex O hO e hO' M hM)

end LocalSummand

end Stacks.SheafOfModules

end
