module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.Comparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree decomposition of a finite locally free morphism

A finite locally free morphism of schemes has locally constant degree, so its target is the
disjoint union of open and closed subschemes on each of which the morphism has one fixed
degree: for `f : X ⟶ S` finite locally free there are opens `S_d ⊆ S`, one for each `d : ℕ`,
which are pairwise disjoint, cover `S`, and are such that `f ∣_ S_d` is finite locally free of
degree `d`.

## Main results

* `Stacks.Morphisms.exists_isClopenDecomposition_isFiniteLocallyFreeOfRank`: the decomposition
  of the target of a finite locally free morphism by the degree.
* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.rank_eq_of_point`: a morphism whose target has a
  point has at most one degree.

## Implementation notes

The piece `S_d` is the union of all opens over which `f_* 𝒪_X` is free of rank `d`; it is open
by construction and closed because the pieces are pairwise disjoint and cover `S`, which is
`Stacks.Chow.IsClopenDecomposition.isClopen`. The restriction of `f` to `S_d` is Mathlib's
`AlgebraicGeometry.Scheme.Hom.morphismRestrict`, written `f ∣_ S_d`.

That the pieces are pairwise disjoint is well-definedness of the rank of a locally free sheaf
of modules, Stacks Tag 01C9: two free presentations of `f_* 𝒪_X` over opens through one point
have index sets of the same cardinality. That is
`LocallyFreeRank.Trivialization.rank_eq_of_mem`, stated for the presentation of local
trivialisations by `LocallyFreeRank.Trivialization`; the bridge to the free presentations of
Stacks Tag 01C6 is `Stacks.StalkFreeBridge.trivializationOfGeneratingSections`, and the
nontriviality of every stalk of the structure sheaf that the rank theorem needs holds because
those stalks are local rings.

Finite local freeness of a fixed rank is used throughout in the pointwise form
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank`, which is manifestly local, and
transported to the morphism by `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_pointwise`
together with `Stacks.Morphisms.pushforwardStructureSheafRestrictIso`, the compatibility of
`f_* 𝒪_X` with restriction to an open of the target. No base-change comparison of direct
images is needed, so Stacks Tag 02KG does not enter.

## References

* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 04MH](https://stacks.math.columbia.edu/tag/04MH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Morphisms

/-- Every stalk of the structure sheaf of a scheme is a nonzero ring, which is the full-support
hypothesis of the rank theorem for locally free sheaves of modules. -/
private theorem stalksNontrivial (S : Scheme.{u}) :
    LocallyFreeRank.StalksNontrivial S.toTopCat S.sheaf := by
  intro x
  have : IsLocalRing (S.presheaf.stalk x) := S.isLocalRing x
  show Nontrivial (S.presheaf.stalk x)
  infer_instance

/-- Reindexing a free sheaf of modules along an equivalence of index sets. -/
private def freeIsoFreeOfEquiv {S : Scheme.{u}} {I J : Type u} (e : I ≃ J) :
    SheafOfModules.free.{u} (R := S.ringCatSheaf) I ≅ SheafOfModules.free.{u} J :=
  Sigma.whiskerEquiv (f := fun _ : I ↦ SheafOfModules.unit S.ringCatSheaf)
    (g := fun _ : J ↦ SheafOfModules.unit S.ringCatSheaf) e fun _ ↦ Iso.refl _

/-- **Well-definedness of the degree.** Two free presentations of ranks `d` and `e` of a sheaf
of modules on a scheme, over opens through a common point, have `d = e`. -/
private theorem eq_of_restrict_iso_free {S : Scheme.{u}} (M : S.Modules) {x : S}
    {U V : S.Opens} (hU : x ∈ U) (hV : x ∈ V) {d e : ℕ}
    (εU : M.restrict U.ι ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin d)))
    (εV : M.restrict V.ι ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin e))) :
    d = e := by
  obtain ⟨σU, hσU, ⟨qU⟩⟩ :=
    Scheme.Modules.exists_generatingSections_of_restrict_iso_of_rank M U d εU
  obtain ⟨σV, hσV, ⟨qV⟩⟩ :=
    Scheme.Modules.exists_generatingSections_of_restrict_iso_of_rank M V e εV
  have := hσU
  have := hσV
  have hrank := LocallyFreeRank.Trivialization.rank_eq_of_mem S.toTopCat S.sheaf
    (stalksNontrivial S) M x hU hV
    (Stacks.StalkFreeBridge.trivializationOfGeneratingSections U M σU)
    (Stacks.StalkFreeBridge.trivializationOfGeneratingSections V M σV)
  have hU' : Cardinal.mk σU.I = (d : Cardinal.{u}) := Cardinal.mk_eq_nat_iff.mpr ⟨qU⟩
  have hV' : Cardinal.mk σV.I = (e : Cardinal.{u}) := Cardinal.mk_eq_nat_iff.mpr ⟨qV⟩
  have : (d : Cardinal.{u}) = (e : Cardinal.{u}) := by
    rw [← hU', ← hV']
    exact hrank
  exact Nat.cast_injective this

/-- **Well-definedness of the degree.** A morphism of schemes whose target has a point is finite
locally free of at most one degree. -/
theorem IsFiniteLocallyFreeOfRank.rank_eq_of_point {X S : Scheme.{u}} (f : X ⟶ S) (x : S)
    {d e : ℕ} (hd : IsFiniteLocallyFreeOfRank f d) (he : IsFiniteLocallyFreeOfRank f e) :
    d = e := by
  obtain ⟨U, hU, ⟨εU⟩⟩ := ((isFiniteLocallyFreeOfRank_iff_pointwise f d).mp hd).2 x
  obtain ⟨V, hV, ⟨εV⟩⟩ := ((isFiniteLocallyFreeOfRank_iff_pointwise f e).mp he).2 x
  exact eq_of_restrict_iso_free _ hU hV εU εV

/-- The largest open subset of `S` over which a sheaf of modules is locally free of rank `d`:
the union of all opens carrying a free presentation of rank `d`. -/
@[sga "5 VII 3.2"]
private def freeOfRankLocus {S : Scheme.{u}} (M : S.Modules) (d : ℕ) : S.Opens :=
  ⨆ W : {W : S.Opens //
    Nonempty (M.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin d)))}, W.1

private theorem mem_freeOfRankLocus_iff {S : Scheme.{u}} (M : S.Modules) (d : ℕ) (x : S) :
    x ∈ freeOfRankLocus M d ↔ ∃ W : S.Opens, x ∈ W ∧
      Nonempty (M.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin d))) := by
  rw [freeOfRankLocus, Opens.mem_iSup]
  exact ⟨fun ⟨W, hW⟩ ↦ ⟨W.1, hW, W.2⟩, fun ⟨W, hW, hfree⟩ ↦ ⟨⟨W, hfree⟩, hW⟩⟩

/-- On the locus where a pointwise finite locally free sheaf of modules is free of rank `d`,
its restriction is finite locally free of rank `d`. -/
private theorem isFiniteLocallyFreeOfRank_restrict_freeOfRankLocus {S : Scheme.{u}}
    (M : S.Modules) (d : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (M.restrict (freeOfRankLocus M d).ι) d := by
  intro x
  obtain ⟨W, hW, ⟨ε⟩⟩ := (mem_freeOfRankLocus_iff M d x.1).mp x.2
  refine ⟨(freeOfRankLocus M d).ι ⁻¹ᵁ W, hW, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorComp
      ((freeOfRankLocus M d).ι ⁻¹ᵁ W).ι (freeOfRankLocus M d).ι).app M).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr
      (morphismRestrict_ι (freeOfRankLocus M d).ι W)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp ((freeOfRankLocus M d).ι ∣_ W) W.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor ((freeOfRankLocus M d).ι ∣_ W)).mapIso ε ≪≫
    (Scheme.Modules.restrictFreeIso ((freeOfRankLocus M d).ι ∣_ W)
      (ULift.{u, 0} (Fin d))).symm

/-- **Stacks Project, Tag 04MH.** The target of a finite locally free morphism of schemes
decomposes as a disjoint union of open and closed subschemes indexed by the degree: there is a
family `S_d`, `d : ℕ`, of opens of `S` which are pairwise disjoint and cover `S` — hence open
and closed, by `Stacks.Chow.IsClopenDecomposition.isClopen` — and such that the restriction
`f ∣_ S_d` is finite locally free of degree `d` for every `d`. -/
theorem exists_isClopenDecomposition_isFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFiniteLocallyFree f] :
    ∃ U : ℕ → S.Opens, Stacks.Chow.IsClopenDecomposition U ∧
      ∀ d, IsFiniteLocallyFreeOfRank (f ∣_ U d) d := by
  obtain ⟨hfAff, hM⟩ := (isFiniteLocallyFree_iff_pointwise f).mp ‹_›
  set M := pushforwardStructureSheaf f with hMdef
  refine ⟨freeOfRankLocus M, ⟨fun d e hde ↦ ?_, ?_⟩, fun d ↦ ?_⟩
  · refine disjoint_iff_inf_le.2 fun x hx ↦ ?_
    obtain ⟨W, hW, ⟨εW⟩⟩ := (mem_freeOfRankLocus_iff M d x).mp hx.1
    obtain ⟨W', hW', ⟨εW'⟩⟩ := (mem_freeOfRankLocus_iff M e x).mp hx.2
    exact absurd (eq_of_restrict_iso_free M hW hW' εW εW') hde
  · refine le_antisymm le_top fun x _ ↦ ?_
    obtain ⟨W, hW, I, hIfin, ⟨ε⟩⟩ := hM x
    have : Finite I := hIfin
    obtain ⟨n, ⟨q⟩⟩ := Finite.exists_equiv_fin I
    rw [Opens.mem_iSup]
    exact ⟨n, (mem_freeOfRankLocus_iff M n x).mpr
      ⟨W, hW, ⟨ε ≪≫ freeIsoFreeOfEquiv (q.trans Equiv.ulift.symm)⟩⟩⟩
  · have : IsAffineHom (f ∣_ freeOfRankLocus M d) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback
        (isPullback_morphismRestrict f (freeOfRankLocus M d)).flip hfAff
    rw [isFiniteLocallyFreeOfRank_iff_pointwise]
    exact ⟨‹_›, Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
      (pushforwardStructureSheafRestrictIso f (freeOfRankLocus M d))
      (isFiniteLocallyFreeOfRank_restrict_freeOfRankLocus M d)⟩

end Stacks.Morphisms

end
