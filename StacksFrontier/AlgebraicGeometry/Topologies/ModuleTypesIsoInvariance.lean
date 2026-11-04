module

public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The local types of modules are invariant under isomorphism

Each condition of Stacks 03DL on a sheaf of modules on a ringed site is a property of the
isomorphism class of the module: it asks of every object of the site a covering on whose members
the restricted module has a property of Stacks 03DE, and both the covering and that property
travel along an isomorphism.  This file proves that for local freeness (03DL (1)), finite local
freeness (03DL (2)) and local generation by sections (03DL (3)), together with the global finite
freeness of 03DE (2) that the second of them is built from.

The counterparts for the other clauses are `SheafOfModules.IsQuasicoherentOnSite.of_iso` for
quasi-coherence (03DL (6)) and `Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso`,
`Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso` and
`Stacks.SheafOfModules.Intrinsic.isLocallyGeneratedByOnSite_of_iso` for 03DL (7), (5) and (4).

## Main definitions

* `Stacks.SheafOfModules.Intrinsic.isoSectionsLinearEquiv`: an isomorphism of sheaves of modules
  evaluated at an object of the site, read as a linear equivalence of the modules of sections.

## Main results

* `Stacks.SheafOfModules.Intrinsic.exists_isColimit_cofan_of_iso`: a family of global sections
  exhibiting a sheaf of modules as a coproduct of copies of the structure sheaf — that is,
  freeness in the sense of Stacks 03DE (1) — travels along an isomorphism, on the same index
  type.
* `Stacks.SheafOfModules.Intrinsic.isFiniteFree_of_iso`: finite freeness, Stacks 03DE (2), is
  invariant under isomorphism of sheaves of modules.
* `Stacks.SheafOfModules.Intrinsic.isLocallyFreeOnSite_of_iso`,
  `.isFiniteLocallyFreeOnSite_of_iso` and `.isLocallyGeneratedBySectionsOnSite_of_iso`: local
  freeness, finite local freeness and local generation by sections are invariant under
  isomorphism of sheaves of modules.

## Implementation notes

`isFiniteFree_of_iso` is stated at a module universe independent of the ring universe, as
`SheafOfModules.IsFiniteFree` and `SheafOfModules.IsFiniteLocallyFreeOnSite` are.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.Intrinsic

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **An isomorphism of sheaves of modules evaluated at an object of the site**, as a linear
equivalence of the modules of sections over that object.  Its inverse is the evaluation of the
inverse isomorphism. -/
noncomputable def isoSectionsLinearEquiv {M N : _root_.SheafOfModules.{m} R} (e : M ≅ N)
    (U : Cᵒᵖ) : M.val.obj U ≃ₗ[R.obj.obj U] N.val.obj U :=
  Iso.toLinearEquiv
    { hom := e.hom.val.app U
      inv := e.inv.val.app U
      hom_inv_id := by
        rw [← PresheafOfModules.comp_app, ← _root_.SheafOfModules.comp_val, e.hom_inv_id]; rfl
      inv_hom_id := by
        rw [← PresheafOfModules.comp_app, ← _root_.SheafOfModules.comp_val, e.inv_hom_id]; rfl }

/-- `isoSectionsLinearEquiv e U` is the component of `e.hom` at `U`. -/
@[simp]
lemma isoSectionsLinearEquiv_apply {M N : _root_.SheafOfModules.{m} R} (e : M ≅ N) (U : Cᵒᵖ)
    (x : M.val.obj U) : isoSectionsLinearEquiv e U x = e.hom.val.app U x :=
  rfl

/-- **Freeness travels along an isomorphism of sheaves of modules.**  If a family of global
sections exhibits a sheaf of modules as a coproduct of copies of the structure sheaf, which is
Stacks 03DE (1), then so does a family on the same index type for an isomorphic module. -/
theorem exists_isColimit_cofan_of_iso {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (h : ∃ (B : Type w) (ι : ∀ _ : B, _root_.SheafOfModules.unit R ⟶ M),
          Nonempty (IsColimit (Cofan.mk M ι))) :
    ∃ (B : Type w) (ι : ∀ _ : B, _root_.SheafOfModules.unit R ⟶ N),
      Nonempty (IsColimit (Cofan.mk N ι)) := by
  obtain ⟨B, ι, ⟨hc⟩⟩ := h
  exact ⟨B, fun b ↦ ι b ≫ e.hom, ⟨hc.ofIsoColimit (Cocone.ext e (fun _ ↦ rfl))⟩⟩

/-- **Finite freeness is invariant under isomorphism of sheaves of modules.**  This is the
condition of Stacks 03DE (2). -/
theorem isFiniteFree_of_iso {M N : _root_.SheafOfModules.{m} R} (e : M ≅ N)
    (h : _root_.SheafOfModules.IsFiniteFree R M) :
    _root_.SheafOfModules.IsFiniteFree R N := by
  obtain ⟨n, P, ι, hc, φ, hφ⟩ := h
  refine ⟨n, P, ι, hc, fun U ↦ (φ U).trans (isoSectionsLinearEquiv e U), fun {U V} f x ↦ ?_⟩
  show isoSectionsLinearEquiv e V (φ V (P.val.map f x)) =
    N.val.map f (isoSectionsLinearEquiv e U (φ U x))
  rw [isoSectionsLinearEquiv_apply, isoSectionsLinearEquiv_apply, hφ f x]
  exact PresheafOfModules.naturality_apply e.hom.val f _

/-- **Local freeness is invariant under isomorphism of sheaves of modules.**  This is the
condition of Stacks 03DL (1). -/
theorem isLocallyFreeOnSite_of_iso {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (hM : M.IsLocallyFreeOnSite) : N.IsLocallyFreeOnSite := fun U ↦ by
  obtain ⟨I, V, f, hf, hV⟩ := hM U
  exact ⟨I, V, f, hf, fun i ↦ exists_isColimit_cofan_of_iso
    ((_root_.SheafOfModules.overFunctor R (V i)).mapIso e) (hV i)⟩

/-- **Finite local freeness is invariant under isomorphism of sheaves of modules.**  This is the
condition of Stacks 03DL (2). -/
theorem isFiniteLocallyFreeOnSite_of_iso {M N : _root_.SheafOfModules.{m} R} (e : M ≅ N)
    (hM : M.IsFiniteLocallyFreeOnSite) : N.IsFiniteLocallyFreeOnSite := fun U ↦ by
  obtain ⟨I, V, f, hf, hV⟩ := hM U
  exact ⟨I, V, f, hf, fun i ↦ isFiniteFree_of_iso
    ((_root_.SheafOfModules.overFunctor R (V i)).mapIso e) (hV i)⟩

section LocallyGenerated

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Local generation by sections is invariant under isomorphism of sheaves of modules.**  This
is the condition of Stacks 03DL (3). -/
theorem isLocallyGeneratedBySectionsOnSite_of_iso {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (hM : M.IsLocallyGeneratedBySectionsOnSite) : N.IsLocallyGeneratedBySectionsOnSite :=
  fun U ↦ by
    obtain ⟨I, V, hcov, hV⟩ := hM U
    exact ⟨I, V, hcov, fun i ↦ (hV i).map (_root_.SheafOfModules.GeneratingSections.equivOfIso
      ((_root_.SheafOfModules.overFunctor R (V i).left).mapIso e))⟩

end LocallyGenerated

end Stacks.SheafOfModules.Intrinsic

end
