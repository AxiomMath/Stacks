module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.BaseChangeFibrewiseSoft

/-!
# The base change of a proper morphism of the locally quasi-compact Zariski site is proper

Let `S` be a locally quasi-compact Zariski situation, `f : X ⟶ Y` a morphism of its site whose
underlying continuous map is proper, and `j : U ⟶ Y` another morphism. The first projection
`U ×_Y X ⟶ U` is again proper in `_root_.IsProperMap`'s sense, hence closed with quasi-compact
fibres.

Writing `Σ = {(a, x) ∈ U × X | j a = f x}`, the space `Y` being Hausdorff makes `Σ` closed in
`U × X`, so `id × f` stays proper when restricted to `Σ`; the graph map `a ↦ (a, j a)` composed
with `pr₁ : Σ ⟶ U` is that restriction, so `pr₁` is proper, `U` being Hausdorff.

## Main results

* `Stacks.Topology.isProperMap_subtype_fst`: the first projection of
  `{(a, x) | j a = f x} ⊆ U × X` is proper when `f` is.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isProperMap_pullback_fst`: the same for the
  fibre product of the site.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology

universe uU uX uY

/-- For Hausdorff spaces `U` and `Y`, a continuous map `j : U → Y` and a proper map `f : X → Y`,
the first projection from `{(a, x) ∈ U × X | j a = f x}` to `U` is proper. -/
theorem isProperMap_subtype_fst {U : Type uU} {X : Type uX} {Y : Type uY} [TopologicalSpace U]
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space U] [T2Space Y] {j : U → Y} {f : X → Y}
    (hj : Continuous j) (hf : IsProperMap f) :
    IsProperMap (fun w : {w : U × X // j w.1 = f w.2} => (w : U × X).1) := by
  have hres : IsProperMap
      (fun w : {w : U × X // j w.1 = f w.2} => Prod.map (id : U → U) f (w : U × X)) :=
    (isProperMap_id.prodMap hf).restrict
      (isClosed_eq (hj.comp continuous_fst) (hf.continuous.comp continuous_snd))
  have heq : (fun a : U => (a, j a)) ∘ (fun w : {w : U × X // j w.1 = f w.2} => (w : U × X).1)
      = fun w : {w : U × X // j w.1 = f w.2} => Prod.map (id : U → U) f (w : U × X) :=
    funext fun w => Prod.ext rfl w.2
  have hγ : Continuous (fun a : U => (a, j a)) := continuous_id.prodMk hj
  refine isProperMap_of_comp_of_t2 (continuous_fst.comp continuous_subtype_val) hγ ?_
  rwa [heq]

namespace LocallyQuasiCompactZariskiSituation

universe u w

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
variable {X Y : S.category} (f : X ⟶ Y) {U : S.category} (j : U ⟶ Y)

/-- If the continuous map underlying a morphism `f : X ⟶ Y` of the site is proper, then so is
the map underlying the first projection `U ×_Y X ⟶ U` of the base change along `j : U ⟶ Y`. -/
theorem isProperMap_pullback_fst
    (hf : _root_.IsProperMap (((siteToTop S).map f).hom :
      (siteToTop S).obj X → (siteToTop S).obj Y)) :
    _root_.IsProperMap (((siteToTop S).map (Limits.pullback.fst j f)).hom :
      (siteToTop S).obj (Limits.pullback j f) → (siteToTop S).obj U) := by
  obtain ⟨e, he⟩ := exists_sitePullback_homeo S f j
  have hsub : _root_.IsProperMap (fun w : {p : U.obj × X.obj //
      (j : U.obj → Y.obj) p.1 = (f : X.obj → Y.obj) p.2} => (w : U.obj × X.obj).1) :=
    isProperMap_subtype_fst (by fun_prop) hf
  have hcomp : (((siteToTop S).map (Limits.pullback.fst j f)).hom :
        (siteToTop S).obj (Limits.pullback j f) → (siteToTop S).obj U) =
      (fun w : {p : U.obj × X.obj //
        (j : U.obj → Y.obj) p.1 = (f : X.obj → Y.obj) p.2} => (w : U.obj × X.obj).1) ∘ e :=
    funext fun q => (congrArg Prod.fst (he q)).symm
  rw [hcomp]
  exact hsub.comp e.isProperMap

end LocallyQuasiCompactZariskiSituation

end Stacks.Topology

end
