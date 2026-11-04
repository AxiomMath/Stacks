module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ConstructingInvariantOpens
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram

/-!
# An invariant open inside a quasi-compact open

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` quasi-compact and flat and with `U`
quasi-separated, and let `W ⊆ U` be a quasi-compact open. Then `W` lies in an invariant open `V`
which is contained in a quasi-compact open `W'`.

## Main results

* `AlgebraicGeometry.exists_specializes_of_mem_closure_range` and
  `AlgebraicGeometry.exists_specializes_mem_of_mem_closure_image` : a point in the closure of
  the range of a quasi-compact morphism, respectively of the image of a closed subset under one,
  is a specialization of a point of that range, respectively of the image of a point of that
  closed subset.
* `AlgebraicGeometry.GroupoidScheme.isInvariantSet_closure_target_image_source_preimage` : the
  closure of the saturation of a closed set is invariant, when the source map is flat and the
  target map quasi-compact.
* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isCompact_between`: an invariant open
  `V` and a quasi-compact open `W'` with `W ⊆ V ⊆ W'`.

## References

* [Stacks Project, Tag 0APB](https://stacks.math.columbia.edu/tag/0APB)
* [Stacks Project, Tag 0APA](https://stacks.math.columbia.edu/tag/0APA)
* [Stacks Project, Tag 03LO](https://stacks.math.columbia.edu/tag/03LO)
* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A point in the closure of the range of a quasi-compact morphism of schemes is a
specialization of a point of the range. -/
theorem exists_specializes_of_mem_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {ξ : Y} (hξ : ξ ∈ closure (Set.range (fun x => f.base x))) :
    ∃ x : X, f.base x ⤳ ξ := by
  rw [← Scheme.Hom.support_ker f, ← Scheme.IdealSheafData.range_subschemeι] at hξ
  obtain ⟨z, hz⟩ := hξ
  obtain ⟨x, hx⟩ := exists_specializes_of_image_point f z
  exact ⟨x, hz ▸ hx⟩

/-- A point in the closure of the image of a closed subset under a quasi-compact morphism of
schemes is a specialization of the image of a point of that closed subset. -/
theorem exists_specializes_mem_of_mem_closure_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {C : Set X} (hC : IsClosed C) {ξ : Y}
    (hξ : ξ ∈ closure (f.base '' C)) :
    ∃ x : X, x ∈ C ∧ f.base x ⤳ ξ := by
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : Closeds X) with hI
  have hIsupp : (I.support : Set X) = C :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨C, hC⟩ : Closeds X)
  have hIrange : Set.range (fun z => I.subschemeι.base z) = C := by
    rw [show (fun z => I.subschemeι.base z) = (I.subschemeι.base : I.subscheme → X) from rfl,
      Scheme.IdealSheafData.range_subschemeι, hIsupp]
  set g : I.subscheme ⟶ Y := I.subschemeι ≫ f with hg
  have hgrange : Set.range (fun z => g.base z) = f.base '' C := by
    rw [show (fun z => g.base z) =
        (fun x => f.base x) ∘ (fun z => I.subschemeι.base z) from funext fun z => by simp [hg],
      Set.range_comp, hIrange]
  obtain ⟨z, hz⟩ := exists_specializes_of_mem_closure_range g (by rwa [hgrange])
  exact ⟨I.subschemeι.base z, by rw [← hIrange]; exact ⟨z, rfl⟩, hz⟩

namespace GroupoidScheme

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)

/-- The closure of the saturation of a closed subset of the object scheme is invariant, provided
the source map is flat and the target map quasi-compact. -/
theorem isInvariantSet_closure_target_image_source_preimage
    [Flat G.source.left] [QuasiCompact G.target.left] {Z : Set G.objects.left}
    (hZ : IsClosed Z) :
    IsInvariantSet G (closure (G.target.left.base '' (G.source.left.base ⁻¹' Z))) := by
  have hTinv := isInvariantSet_target_image_source_preimage G Z
  intro r hr
  obtain ⟨a, haC, hspec⟩ :=
    exists_specializes_mem_of_mem_closure_image G.target.left
      (hZ.preimage G.source.left.continuous) hr
  obtain ⟨r', hr'r, hr'a⟩ := Flat.generalizingMap G.source.left hspec
  have hmem : G.target.left.base r' ∈
      G.target.left.base '' (G.source.left.base ⁻¹' Z) :=
    hTinv r' (by rw [hr'a]; exact ⟨a, haC, rfl⟩)
  exact closure_mono (Set.singleton_subset_iff.mpr hmem)
    (specializes_iff_mem_closure.mp (hr'r.map G.target.left.continuous))

/-- Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t`
quasi-compact and flat and with `U` quasi-separated, and let `W ⊆ U` be a quasi-compact open.
Then there is an invariant open `V` and a quasi-compact open `W'` with `W ⊆ V ⊆ W' ⊆ U`. -/
@[stacks 0APB]
theorem exists_isInvariantOpen_isCompact_between
    [QuasiCompact G.source.left] [Flat G.source.left]
    [QuasiCompact G.target.left] [Flat G.target.left]
    [QuasiSeparatedSpace G.objects.left]
    (W : G.objects.left.Opens) (hW : IsCompact (W : Set G.objects.left)) :
    ∃ V W' : G.objects.left.Opens,
      IsInvariantOpen G V ∧ IsCompact (W' : Set G.objects.left) ∧
        (W : Set G.objects.left) ⊆ (V : Set G.objects.left) ∧
        (V : Set G.objects.left) ⊆ (W' : Set G.objects.left) := by
  classical
  set E : Set G.objects.left :=
    G.target.left.base '' (G.source.left.base ⁻¹' (W : Set G.objects.left)) with hEdef
  have hEinv : IsInvariantSet G E := isInvariantSet_target_image_source_preimage G _
  have hWE : (W : Set G.objects.left) ⊆ E := subset_target_image_source_preimage G _
  have hEgen : StableUnderGeneralization E :=
    (Flat.generalizingMap G.target.left).stableUnderGeneralization_image
      (W.2.stableUnderGeneralization.preimage G.source.left.continuous)
  obtain ⟨Idx, hIdx, V, hV, hEV⟩ :=
    target_image_source_preimage_eq_iInter_compact_open G W hW
  obtain ⟨i₀⟩ := hIdx
  set W' : G.objects.left.Opens := ⟨V i₀, (hV i₀).1⟩ with hW'def
  have hEW' : E ⊆ (W' : Set G.objects.left) := by
    rw [hEdef, hEV]
    exact Set.iInter_subset _ i₀
  set Z : Set G.objects.left := (W' : Set G.objects.left)ᶜ with hZdef
  have hZclosed : IsClosed Z := (W' : G.objects.left.Opens).2.isClosed_compl
  set T : Set G.objects.left :=
    G.target.left.base '' (G.source.left.base ⁻¹' Z) with hTdef
  have hZT : Z ⊆ T := subset_target_image_source_preimage G Z
  have hET : ∀ x, x ∈ E → x ∉ T := by
    rintro x hxE ⟨r, hrZ, hrx⟩
    have hrt : r ∈ G.target.left.base ⁻¹' E := by rwa [Set.mem_preimage, hrx]
    exact hrZ (hEW' ((Set.ext_iff.mp (source_preimage_eq_target_preimage G hEinv) r).mpr hrt))
  have hTclosureInv : IsInvariantSet G (closure T) :=
    isInvariantSet_closure_target_image_source_preimage G hZclosed
  have hEclosureT : ∀ x, x ∈ E → x ∉ closure T := by
    intro x hxE hxT
    obtain ⟨a, haC, hspec⟩ :=
      exists_specializes_mem_of_mem_closure_image G.target.left
        (hZclosed.preimage G.source.left.continuous) hxT
    exact hET _ (hEgen hspec hxE) ⟨a, haC, rfl⟩
  refine ⟨⟨(closure T)ᶜ, (isClosed_closure (s := T)).isOpen_compl⟩, W',
    isInvariantSet_compl G hTclosureInv, (hV i₀).2, fun x hx => hEclosureT x (hWE hx), ?_⟩
  exact Set.compl_subset_comm.mp (hZT.trans subset_closure)

end GroupoidScheme

end AlgebraicGeometry

end
