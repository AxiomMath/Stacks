module

public import Mathlib.RingTheory.Flat.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.Topology.Sheaves.Module
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of a sheaf of modules is flatness with finite presentation

A sheaf of modules on a scheme is finite locally free exactly when it is flat and of finite
presentation. This is the equivalence of entries (1) and (4) of Stacks Tag 05P2, at sheaf level
on an arbitrary scheme.

## Main results

* `AlgebraicGeometry.SheafOfModules.free_stalk_of_isFlat`: the stalks of a flat sheaf of modules
  of finite presentation are free over the local rings of the scheme.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFlat`: the implication (1) ⟹ (4)
  of Stacks Tag 05P2.
* `AlgebraicGeometry.SheafOfModules.free_stalk_of_isLocallyFreeData` and
  `AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree`: the flatness half of the
  implication (4) ⟹ (1).
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation`:
  the equivalence.

## Implementation notes

The implication (1) ⟹ (4) is the argument in the source, run at the stalks. A sheaf of modules
of finite presentation has finitely generated stalks (`SheafOfModules.finite_stalk`), flatness
of a sheaf of modules on a ringed space is flatness of all of its stalks
(`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`), and a finitely generated flat module
over a local ring is free, so each stalk is free of some finite rank. Tag 0B8J
(`Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free`) then trivialises the sheaf on a
neighbourhood of the point, and those trivialisations assemble into local generators data
indexed by the points of the scheme, which is locally free data of finite type.

The converse is read off the same identification in the other direction. Finite presentation is
`Stacks.FiniteLocallyFree.isFinitePresentation`, restated here for the class of Tag 01C6 part
(2); `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` is a reducible spelling of that class, so
the restatement is its constructor, applied with its ring sheaf and its module named. Flatness
is flatness of all stalks again, and the
stalks are free because a member of the covering underlying the locally free data trivialises
the sheaf near the point. The
identification of the stalk of a free sheaf of modules is Tag 01C9's
`LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp`, whose `Trivialization` is a free
presentation of the genuine restriction `LocallyFreeRank.restrictMod` to an open rather than of
`SheafOfModules.over` on the slice site; `trivializationOfIsLocallyFreeData` converts between
the two along `TopologicalSpace.Opens.sheafOfModulesEquivOver`, using that an equivalence
carrying the structure sheaf to the structure sheaf carries free sheaves to free sheaves
(`SheafOfModules.mapFreeIso`).

The module docstring of `StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFree.lean` records
that the remaining implications of Tag 05P2 are not proved there because the stalk of a free
sheaf of modules is not identified with a free module over the stalk of the sheaf of rings.
That identification is in fact available, for the restriction of a sheaf of rings to an open,
as Tag 01C9's `LocallyFreeRank.Trivialization.stalk_free_linearEquiv`; that docstring is
accurate about its own file but its account of the obstruction is out of date, and correcting
it is left as a note here, since that file is not part of this development.

Two spellings of the stalk of the sheaf of rings occur. The module structure produced by
`SheafOfModules.finite_stalk` and by `isFlat_iff_stalk_flat` is over the `CommRingCat`-valued
stalk `X.presheaf.stalk x`, whereas Tag 0B8J, which is stated over an arbitrary sheaf of
not-necessarily-commutative rings, uses the `RingCat`-valued stalk of
`AlgebraicGeometry.Scheme.ringCatSheaf`. The two rings are identified by
`SemilinearStalk.commStalkRingEquiv`, which matches the two actions on a stalk
(`SemilinearStalk.comm_smul_eq`); transporting a basis along that ring
isomorphism is what `nonempty_stalk_linearEquiv_finsupp` does.

The local generators data is indexed by the points of the scheme rather than by a chosen cover,
which keeps the index type in the universe of the site, as `SheafOfModules.LocalGeneratorsData`
requires. The two auxiliary lemmas on generating sections are stated over an arbitrary site,
since neither uses anything about schemes: a sheaf of modules isomorphic to a free sheaf is
generated by the images of the canonical global basis of the latter, and those generators are
finite in number as soon as the index type is.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v₁ u₁

namespace AlgebraicGeometry.SheafOfModules

section Site

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The images of the canonical global basis of a free sheaf of modules under an isomorphism
with another sheaf of modules generate the latter freely: the induced epimorphism from the free
sheaf on the same index type is the isomorphism itself. -/
theorem isIso_free_generatingSections_ofEpi_π {N : _root_.SheafOfModules.{u} R} (I : Type u)
    (e : _root_.SheafOfModules.free (R := R) I ≅ N) :
    IsIso ((_root_.SheafOfModules.free.generatingSections (R := R) I).ofEpi e.hom).π := by
  have h : ((_root_.SheafOfModules.free.generatingSections (R := R) I).ofEpi e.hom).π
      = e.hom := by
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
      _root_.SheafOfModules.free.generatingSections_π]
    exact Category.id_comp _
  rw [h]
  exact e.isIso_hom

/-- The generating sections transported from a free sheaf of modules on a finite index type are
finite in number. -/
theorem isFiniteType_free_generatingSections_ofEpi {N : _root_.SheafOfModules.{u} R} (I : Type u)
    [Finite I] (e : _root_.SheafOfModules.free (R := R) I ≅ N) :
    ((_root_.SheafOfModules.free.generatingSections (R := R) I).ofEpi e.hom).IsFiniteType :=
  ⟨inferInstanceAs (Finite I)⟩

end Site

/-- A sheaf of modules on a scheme which is, near every point, isomorphic to a free sheaf of
modules on a finite index type over the restricted structure sheaf is finite locally free. The
local generators data is indexed by the points of the scheme. -/
theorem isFiniteLocallyFree_of_forall_exists_iso_free_over {X : Scheme.{u}} (F : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (I : Type u) (_ : Finite I),
      Nonempty (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
        (F : _root_.SheafOfModules.{u} X.ringCatSheaf).over U)) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F := by
  choose U hU I hI e using h
  constructor
  refine ⟨{ I := (X : Type u)
            X := U
            coversTop := by
              rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, eq_top_iff]
              intro x _
              simp only [TopologicalSpace.Opens.mem_iSup]
              exact ⟨x, hU x⟩
            generators := fun x => (_root_.SheafOfModules.free.generatingSections
              (R := X.ringCatSheaf.over (U x)) (I x)).ofEpi (e x).some.hom }, ?_, ?_⟩
  · constructor
    intro x
    exact isIso_free_generatingSections_ofEpi_π (I x) (e x).some
  · constructor
    intro x
    have : Finite (I x) := hI x
    exact isFiniteType_free_generatingSections_ofEpi (I x) (e x).some

/-- The stalks of a flat sheaf of modules of finite presentation on a scheme are free modules
over the local rings of the scheme: they are finitely generated and flat over a local ring. This
is the stalkwise half of the implication (1) ⟹ (4) of Stacks Tag 05P2. -/
theorem free_stalk_of_isFlat {X : Scheme.{u}} (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlat.{u, u, u, u} (O := X.sheaf) F) (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u} F :=
    _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F x
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    (isFlat_iff_stalk_flat X.sheaf F).mp hflat x
  exact Module.free_of_flat_of_isLocalRing

/-- A finitely generated free stalk of a sheaf of modules on a scheme, read over the
`RingCat`-valued stalk of the structure sheaf: this is the shape in which Tag 0B8J consumes
freeness of a stalk. -/
theorem nonempty_stalk_linearEquiv_finsupp {X : Scheme.{u}} (F : X.Modules) (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) →
      Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) →
      ∃ r : ℕ, Nonempty
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)
          ≃ₗ[ToType (X.ringCatSheaf.presheaf.stalk x)]
          (ULift.{u} (Fin r) →₀ ToType (X.ringCatSheaf.presheaf.stalk x))) := by
  classical
  intro hfree hfin
  let A := ToType (X.presheaf.stalk x)
  let B := ToType (X.ringCatSheaf.presheaf.stalk x)
  let M := ToType (TopCat.Presheaf.stalk F.val.presheaf x)
  let eR : B ≃+* A := SemilinearStalk.commStalkRingEquiv X.presheaf x
  have hsmul : ∀ (s : B) (m : M), eR s • m = s • m := fun s m =>
    SemilinearStalk.comm_smul_eq X.presheaf x
      (F.val : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})) s m
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  have : Module.Free A M := hfree
  have : Module.Finite A M := hfin
  let ι := Module.Free.ChooseBasisIndex A M
  let : Fintype ι := Fintype.ofFinite _
  let e : ι ≃ ULift.{u} (Fin (Fintype.card ι)) := (Fintype.equivFin ι).trans Equiv.ulift.symm
  let b' : Module.Basis (ULift.{u} (Fin (Fintype.card ι))) A M :=
    (Module.Free.chooseBasis A M).reindex e
  exact ⟨Fintype.card ι, ⟨(b'.mapCoeffs eR.symm fun c m =>
    (hsmul (eR.symm c) m).symm.trans (by rw [RingEquiv.apply_symm_apply])).repr⟩⟩

/-- **Stacks Project, Tag 05P2**, the implication (1) ⟹ (4): a flat sheaf of modules of finite
presentation on a scheme is finite locally free. -/
@[ega "IV 2.1.12" "(a) ⇒ (b), special case"]
theorem isFiniteLocallyFree_of_isFlat {X : Scheme.{u}} (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F := by
  refine isFiniteLocallyFree_of_forall_exists_iso_free_over F fun x => ?_
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  have hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} F :=
    _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  obtain ⟨r, hr⟩ := nonempty_stalk_linearEquiv_finsupp F x
    (free_stalk_of_isFlat F hflat x) (_root_.SheafOfModules.finite_stalk X.sheaf F x)
  obtain ⟨U, hxU, hiso⟩ :=
    Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free F ‹_› x r hr
  exact ⟨U, hxU, ULift.{u} (Fin r), inferInstance, ⟨hiso.some.symm⟩⟩

/-- The trivialisation of `F` on a member of a cover underlying locally free data, in the form
Tag 01C9 consumes: the free presentation over the slice site at an open is transported to the
genuine restriction of `F` to that open along `TopologicalSpace.Opens.sheafOfModulesEquivOver`,
which carries the structure sheaf to the structure sheaf and hence free sheaves to free
sheaves. -/
noncomputable def trivializationOfIsLocallyFreeData {X : Scheme.{u}} (F : X.Modules)
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u, u, u, u} (R := X.ringCatSheaf) F)
    (hq : q.IsLocallyFreeData) (i : q.I) :
    LocallyFreeRank.Trivialization (X : TopCat.{u})
      (LocallyFreeRank.toRingSheaf (X : TopCat.{u}) X.sheaf) F (q.X i) := by
  let U := q.X i
  let R := LocallyFreeRank.toRingSheaf (X : TopCat.{u}) X.sheaf
  let E := U.sheafOfModulesEquivOver R
  have hπ : IsIso (q.generators i).π := hq.isIso i
  let e : _root_.SheafOfModules.free (q.generators i).I ≅
      (F : _root_.SheafOfModules.{u} X.ringCatSheaf).over U := asIso (q.generators i).π
  let eFree : _root_.SheafOfModules.free (q.generators i).I ≅
      E.functor.obj (_root_.SheafOfModules.free (q.generators i).I) :=
    _root_.SheafOfModules.mapFreeIso E.functor (q.generators i).I
      (U.sheafOfModulesEquivOverUnit R)
  exact ⟨(q.generators i).I, (eFree ≪≫ E.functor.mapIso e ≪≫
    (show E.functor.obj ((F : _root_.SheafOfModules.{u} X.ringCatSheaf).over U) ≅
      LocallyFreeRank.restrictMod (X : TopCat.{u}) U R F from Iso.refl _)).symm⟩

/-- The stalks of a sheaf of modules carrying locally free data are free modules over the local
rings of the scheme: the trivialisation near a point identifies the stalk with a finitely
supported function type over the local ring, by Tag 01C9. -/
theorem free_stalk_of_isLocallyFreeData {X : Scheme.{u}} (F : X.Modules)
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u, u, u, u} (R := X.ringCatSheaf) F)
    (hq : q.IsLocallyFreeData) (x : X) :
    letI : Module (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
      LocallyFreeRank.instModuleStalkF (X : TopCat.{u}) X.sheaf F x
    Module.Free (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) := by
  let : Module (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    LocallyFreeRank.instModuleStalkF (X : TopCat.{u}) X.sheaf F x
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    (X : TopCat.{u}) X.sheaf F x hxi (trivializationOfIsLocallyFreeData F q hq i)
  exact Module.Free.of_equiv e.symm

/-- **Stacks Project, Tag 05P2**, the flatness half of the implication (4) ⟹ (1): a finite
locally free sheaf of modules on a scheme is flat. Only local freeness is used. -/
theorem isFlat_of_isFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules)
    (h : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    IsFlat.{u, u, u, u} (O := X.sheaf) F := by
  obtain ⟨q, hq, -⟩ := h.exists_isFiniteLocallyFreeData
  apply (isFlat_iff_stalk_flat X.sheaf F).mpr
  intro x
  let : Module (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    LocallyFreeRank.instModuleStalkF (X : TopCat.{u}) X.sheaf F x
  have : Module.Free (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) := free_stalk_of_isLocallyFreeData F q hq x
  change Module.Flat (ToType (TopCat.Presheaf.stalk X.sheaf.obj x))
    (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
  exact Module.Flat.of_free

/-- A finite locally free sheaf of modules on a scheme is of finite presentation. This restates
`Stacks.FiniteLocallyFree.isFinitePresentation` for the class of Tag 01C6 part (2). -/
theorem isFinitePresentation_of_isFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules)
    (h : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    _root_.SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  -- `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` is a reducible spelling of this class, so the
  -- restatement is the constructor; the ring sheaf and module are named explicitly.
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} (R := X.ringCatSheaf) (M := F)
      h.exists_isFiniteLocallyFreeData
  exact Stacks.FiniteLocallyFree.isFinitePresentation
    (F : _root_.SheafOfModules.{u} X.ringCatSheaf)

/-- **Stacks Project, Tag 05P2**, the equivalence of entries (1) and (4): a sheaf of modules on
a scheme is finite locally free if and only if it is flat and of finite presentation. -/
@[ega "IV 2.1.12" "special case"]
theorem isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation {X : Scheme.{u}}
    (F : X.Modules) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F ↔
      IsFlat.{u, u, u, u} (O := X.sheaf) F ∧
        _root_.SheafOfModules.IsFinitePresentation.{u, u, u} F :=
  ⟨fun h => ⟨isFlat_of_isFiniteLocallyFree F h, isFinitePresentation_of_isFiniteLocallyFree F h⟩,
    fun ⟨hflat, _⟩ => isFiniteLocallyFree_of_isFlat F hflat⟩

end AlgebraicGeometry.SheafOfModules

end
