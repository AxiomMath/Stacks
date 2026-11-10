module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# Quasi-coherence restricts along an arrow between two slices of a site

Let `C` be a site, let `R` be a sheaf of rings on it and let `f : U ⟶ V` be an arrow of `C`.
Restriction of sheaves of modules from the slice site `C/V` to the slice site `C/U` along `f` is
`SheafOfModules.overMap`. It carries quasi-coherence: the restriction of a quasi-coherent
`R.over V`-module is a quasi-coherent `R.over U`-module.

## Main results

* `Stacks.SheafOfModules.post_overMap_isContinuous`: `Over.post (Over.map f)` is continuous for
  the iterated slice topologies.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_overMap`: quasi-coherence restricts along an
  arrow between two slices of a site.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v r m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **`Over.post (Over.map f)` is continuous for the iterated slice topologies.**  For an arrow
`f : U ⟶ V` of a site and an object `W` of the slice `C/U`, the functor `Over.post (Over.map f)`
from `(C/U)/W` to `(C/V)/((Over.map f).obj W)` is continuous. -/
theorem post_overMap_isContinuous {U V : C} (f : U ⟶ V) (W : Over U) :
    (Over.post (X := W) (Over.map f)).IsContinuous
      ((J.over U).over W) ((J.over V).over ((Over.map f).obj W)) := by
  let G := Over.map (Y := V) f
  let W' : Over V := Over.mk (W.hom ≫ f)
  let e := W.iteratedSliceEquiv.functor ⋙ W'.iteratedSliceEquiv.inverse
  have he : (Over.post (X := W) G) ≅ e :=
    NatIso.ofComponents (fun A ↦ Over.isoMk
      (Over.isoMk (Iso.refl _) (by
        simp [e, W', G, Over.iteratedSliceEquiv, Over.iteratedSliceBackward,
          Over.iteratedSliceForward, Over.map, Over.post]))
        (by
          ext
          simp only [Over.map, Over.post, Over.mk_left, Comma.mapRight_obj_left,
            Over.iteratedSliceEquiv, Over.iteratedSliceForward, Over.iteratedSliceBackward,
            Functor.id_obj, Functor.comp_obj, Over.mk_hom, Over.comp_left, Over.isoMk_hom_left,
            Iso.refl_hom, Over.homMk_left, Category.id_comp, e, W', G]
          exact rfl))
      (by
        intro A A' g
        ext
        simp only [Over.map, Over.post, Over.mk_left, Comma.mapRight_obj_left,
          Over.iteratedSliceEquiv, Over.iteratedSliceForward, Over.iteratedSliceBackward,
          Functor.id_obj, Functor.comp_obj, Over.mk_hom, Over.comp_left, Over.homMk_left,
          Over.isoMk_hom_left, Iso.refl_hom, Category.comp_id, Functor.comp_map,
          Category.id_comp, e, W', G]
        exact rfl)
  have : W.iteratedSliceEquiv.functor.IsContinuous
      ((J.over U).over W) (J.over W.left) := inferInstance
  have : W'.iteratedSliceEquiv.inverse.IsContinuous
      (J.over W.left) ((J.over V).over W') := by
    have : W'.iteratedSliceEquiv.inverse.IsDenseSubsite
        (J.over W.left) ((J.over V).over W') := by
      refine { functorPushforward_mem_iff := ?_ }
      intro Y T
      simp only [GrothendieckTopology.mem_over_iff, Sieve.overEquiv,
        RelIso.coe_fn_mk, Equiv.coe_fn_mk]
      rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
      change Sieve.functorPushforward
          (W'.iteratedSliceBackward ⋙ Over.forget W' ⋙ Over.forget V) T ∈ J _ ↔
        Sieve.functorPushforward (Over.forget W.left) T ∈ J _
      rw [Over.iteratedSliceBackward_forget_forget]
      rfl
    exact Functor.IsDenseSubsite.instIsContinuous _ _ _
  have : e.IsContinuous ((J.over U).over W) ((J.over V).over (G.obj W)) := by
    change (W.iteratedSliceEquiv.functor ⋙ W'.iteratedSliceEquiv.inverse).IsContinuous
      ((J.over U).over W) ((J.over V).over W')
    exact Functor.isContinuous_comp _ _ _ (J.over W.left) _
  exact Functor.isContinuous_of_iso he.symm _ _

/-- **Quasi-coherence restricts along an arrow between two slices of a site.**  Let `R` be a sheaf
of rings on a site `C`, let `f : U ⟶ V` be an arrow of `C` and let `F` be a quasi-coherent sheaf of
`R.over V`-modules on the slice site `C/V`.  Then the restriction of `F` to the slice site `C/U`
along `f` is a quasi-coherent sheaf of `R.over U`-modules. -/
theorem isQuasicoherentOnSite_overMap (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V)
    (F : SheafOfModules.{m} (R.over V)) (hF : F.IsQuasicoherentOnSite) :
    ((SheafOfModules.overMap.{m} R f).obj F).IsQuasicoherentOnSite := by
  have hpost : ∀ W : Over U, (Over.post (X := W) (Over.map f)).IsContinuous
      ((J.over U).over W) ((J.over V).over ((Over.map f).obj W)) :=
    post_overMap_isContinuous f
  exact isQuasicoherentOnSite_pushforward
    (Over.map f) (Sheaf.pushforwardOverMapIso R f).inv (fun X Y g ↦ by
      let G' := Over.post (X := X) (Over.map f) ⋙ Over.map g
      have h1 : HasSheafify ((J.over U).over X) AddCommGrpCat.{max u v r m} :=
        GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, max u v} _
      have h2 : ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
        AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m,
          max u v, v} _
      have h3 : HasSheafify ((J.over V).over Y) AddCommGrpCat.{max u v r m} :=
        GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, max u v} _
      have h4 : ((J.over V).over Y).WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
        AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m,
          max u v, v} _
      have hc : G'.IsCocontinuous ((J.over U).over X) ((J.over V).over Y) :=
        isCocontinuous_comp (Over.post (Over.map f)) (Over.map g)
          ((J.over U).over X) ((J.over V).over ((Over.map f).obj X))
      exact pushforward_preservesColimits G' _) F hF

end Stacks.SheafOfModules

end
