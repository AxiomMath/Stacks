module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Quasi-coherence descends along a covering arrow of a slice site

Let `C` be a site, `X` an object of `C`, `R` a sheaf of rings on the slice site `C/X` and `M` a
sheaf of `R`-modules. For an arrow `f : V ⟶ X`, restriction of `M` along the localization functor
`Over.map f : C/V ⥤ C/X` is the restriction `M|_{V/X}` of `M` to the slice of `C/X` at `V/X`,
read through the equivalence `(C/X)/(V/X) ≌ C/V`. Hence if the restrictions of `M` along the
members of a family `{V_i ⟶ X}` covering `C/X` are quasi-coherent, so is `M` (Stacks 03DN).

## Main results

All in the namespace `Stacks.SheafOfModules`.

* `isQuasicoherentOnSite_over_of_pushforward_overMap_quasicoherenceOverMapDescent`:
  quasi-coherence of the restriction along `Over.map f` gives quasi-coherence of `M|_{V/X}`.
* `coversTop_over_mk_of_generate_singleton_mem_quasicoherenceOverMapDescent`: a covering arrow
  `f : V ⟶ X` covers the final object of `C/X`.
* `isQuasicoherentOnSite_of_pushforward_overMap_quasicoherenceOverMapDescent`: **quasi-coherence
  descends along a covering family of `X`.**
* `isQuasicoherentOnSite_of_restrictScalars_of_isIso_quasicoherenceOverMapDescent` and
  `isQuasicoherentOnSite_pushforward_of_comp_eq_quasicoherenceOverMapDescent`: quasi-coherence
  is reflected by restriction of scalars along an isomorphism, and restriction along a composite.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {X : C}

/-- **Restriction along `Over.map f` detects quasi-coherence of the restriction to `V/X`.** The
restriction of `M` along `Over.map f : C/V ⥤ C/X` is the reindexing of `M|_{V/X}` along the
equivalence `C/V ≌ (C/X)/(V/X)`, which reflects quasi-coherence. -/
theorem isQuasicoherentOnSite_over_of_pushforward_overMap_quasicoherenceOverMapDescent
    (R : Sheaf (J.over X) RingCat.{w})
    (M : SheafOfModules.{w} R) {V : C} (f : V ⟶ X)
    (hM : ((SheafOfModules.pushforward.{w} (F := Over.map f)
      (𝟙 (((Over.map f).sheafPushforwardContinuous RingCat.{w} (J.over V) (J.over X)).obj
        R))).obj M).IsQuasicoherentOnSite) :
    (M.over (Over.mk f)).IsQuasicoherentOnSite := by
  let e : Over V ≌ Over (Over.mk f) := (Over.mk f).iteratedSliceEquiv.symm
  have : e.functor.IsContinuous (J.over V) ((J.over X).over (Over.mk f)) :=
    inferInstanceAs ((Over.mk f).iteratedSliceBackward.IsContinuous (J.over (Over.mk f).left) _)
  have : e.inverse.IsContinuous ((J.over X).over (Over.mk f)) (J.over V) :=
    inferInstanceAs ((Over.mk f).iteratedSliceForward.IsContinuous _ (J.over (Over.mk f).left))
  have : e.inverse.IsDenseSubsite ((J.over X).over (Over.mk f)) (J.over V) :=
    inferInstanceAs ((Over.mk f).iteratedSliceEquiv.functor.IsDenseSubsite _
      (J.over (Over.mk f).left))
  exact isQuasicoherentOnSite_of_reindex e (R.over (Over.mk f)) (M.over (Over.mk f)) hM

/-- A covering arrow `f : V ⟶ X` covers the final object of the slice site `C/X`. -/
theorem coversTop_over_mk_of_generate_singleton_mem_quasicoherenceOverMapDescent {V : C} (f : V ⟶ X)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J X) :
    (J.over X).CoversTop (fun _ : PUnit.{max u v + 1} ↦ Over.mk f) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ (Over.mk (𝟙 X)) Over.mkIdTerminal,
    GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ((Sieve.generate_le_iff _ _).2 ?_) hf
  rintro _ _ ⟨⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨PUnit.unit, ⟨Over.homMk (𝟙 V) (by simp)⟩⟩

/-- **Quasi-coherence descends along a covering family of `X`** (Stacks 03DN): a sheaf of
modules on the slice site `C/X` is quasi-coherent as soon as its restrictions along the
localization functors `Over.map f_i : C/V_i ⥤ C/X` of a family covering `C/X` are. -/
theorem isQuasicoherentOnSite_of_pushforward_overMap_quasicoherenceOverMapDescent
    (R : Sheaf (J.over X) RingCat.{w})
    (M : SheafOfModules.{w} R) {I : Type (max u v)} {V : I → C} (f : ∀ i, V i ⟶ X)
    (hf : (J.over X).CoversTop (fun i ↦ Over.mk (f i)))
    (hM : ∀ i, ((SheafOfModules.pushforward.{w} (F := Over.map (f i))
      (𝟙 (((Over.map (f i)).sheafPushforwardContinuous RingCat.{w} (J.over (V i))
        (J.over X)).obj R))).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite M).2
    ⟨I, fun i ↦ Over.mk (f i), hf,
      fun i ↦ isQuasicoherentOnSite_over_of_pushforward_overMap_quasicoherenceOverMapDescent R M
        (f i) (hM i)⟩

/-- **Quasi-coherence is reflected by restriction of scalars along an isomorphism**: restricting
back along the inverse returns the module. -/
theorem isQuasicoherentOnSite_of_restrictScalars_of_isIso_quasicoherenceOverMapDescent
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) [IsIso α]
    (M : SheafOfModules.{w} S)
    (hM : ((SheafOfModules.restrictScalars.{w} α).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId α (inv α)
      (IsIso.inv_hom_id α)).app M)
    (isQuasicoherentOnSite_restrictScalars_of_isIso (inv α) _ hM)

/-- Restriction of a sheaf of modules along `G₂` and then `G₁` is restriction along any functor
equal to `G₁ ⋙ G₂`, as far as quasi-coherence is concerned. -/
theorem isQuasicoherentOnSite_pushforward_of_comp_eq_quasicoherenceOverMapDescent
    {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {D : Type*} [Category* D] {K : GrothendieckTopology D}
    {E : Type*} [Category* E] {L : GrothendieckTopology E}
    (R : Sheaf J RingCat.{w}) (G₁ : D ⥤ E) (G₂ : E ⥤ C) (G : D ⥤ C) [G₁.IsContinuous K L]
    [G₂.IsContinuous L J] [G.IsContinuous K J] (hG : G₁ ⋙ G₂ = G) (M : SheafOfModules.{w} R)
    (hM : ((SheafOfModules.pushforward.{w} (F := G₁)
      (𝟙 ((G₁.sheafPushforwardContinuous RingCat.{w} K L).obj
        ((G₂.sheafPushforwardContinuous RingCat.{w} L J).obj R)))).obj
        ((SheafOfModules.pushforward.{w} (F := G₂)
          (𝟙 ((G₂.sheafPushforwardContinuous RingCat.{w} L J).obj R))).obj
            M)).IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{w} (F := G)
      (𝟙 ((G.sheafPushforwardContinuous RingCat.{w} K J).obj R))).obj M).IsQuasicoherentOnSite := by
  subst hG
  exact hM

end Stacks.SheafOfModules

end
