module

public import StacksFrontier.Topology.Maps.Proper
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CompactSections

/-!
# Sections of a direct image near a point, for a closed map with quasi-compact fibres

Let `g : X ⟶ Y` be a continuous map of topological spaces which is closed and has quasi-compact
fibres, with `X` Hausdorff, and let `F` be a sheaf on `X` with values in a concrete category. This
file proves the two statements which together say that the sections of `g_*F` near a point `y` of
`Y` are the sections of `F` along the fibre `g⁻¹(y)`:

* two sections of `F` over `g⁻¹U` which agree near every point of the fibre already agree over
  `g⁻¹U₀` for some open neighbourhood `U₀ ⊆ U` of `y`;
* sections of `F` on opens covering the fibre, which agree near every point of the fibre, glue to
  a section over `g⁻¹U₀` for some open neighbourhood `U₀` of `y`.

Equivalently, with `i : g⁻¹(y) → X` the inclusion, the canonical map

`(g_*F)_y = colim_{U ∋ y open} F(g⁻¹U) ⟶ Γ(g⁻¹(y), i⁻¹F)`

is injective by the first statement and surjective by the second. This is the topological input to
proper base change for sheaves of sets, and it is where properness is used: quasi-compactness of
the fibre to glue finitely many local sections, and closedness of `g` to convert an open
neighbourhood of the fibre in `X` into the preimage of an open neighbourhood of `y` in `Y`.

## Main results

* `Stacks.Topology.exists_isOpen_preimage_subset_of_isClosedMap`: for a closed map, an open set
  containing a fibre contains the preimage of an open neighbourhood of the point.
* `Stacks.Topology.exists_opens_preimage_restrict_eq_of_locallyEqOn_fibre`: two sections agreeing
  near every point of a fibre agree over the preimage of a neighbourhood of the point.
* `Stacks.Topology.exists_opens_preimage_glue_of_isCompact_fibre_of_pairwiseSeparated`: local
  sections covering a quasi-compact fibre whose distinct points are separated by disjoint opens,
  and agreeing near each of its points, glue over the preimage of a neighbourhood of the point;
  `Stacks.Topology.exists_opens_preimage_glue_of_isCompact_fibre` is its `T2Space X` corollary.
* `Stacks.Topology.isProperMap_of_isProperMap`: a continuous map which is proper in the sense of
  Stacks 005O (5) is proper in the sense of Mathlib's `IsProperMap`, and hence closed with
  quasi-compact fibres.

## Implementation notes

Everything is stated **without stalks and without germs**, by `Stacks.Topology.CompactSections`'s
convention: "two sections have the same germ at `x`" is replaced by "two sections agree on some
open neighbourhood of `x`". That is not a stylistic choice. Mathlib's `TopCat.Presheaf.stalk` is
declared for `X : TopCat.{v}` with `[Category.{v} C]`, so for a space in `Type u` it only admits
coefficient categories whose morphisms live in universe `u`; the localized Zariski site of Stacks
0DCU produces sheaves of `Type (max (u + 1) v)` on a space in `Type u`, where that is
unsatisfiable. The three universes here — the objects of the coefficient category, its morphisms,
and the space — are therefore kept independent, which is exactly the generality the two results of
`CompactSections` are stated in.

The bridge `isProperMap_of_isProperMap` base changes `g` along the second projection
`Z × Y ⟶ Y`: the fibre product `(Z × Y) ×_Y X` is homeomorphic to `Z × X` by the graph map, under
which the projection to `Z × Y` becomes `Prod.map id g`. That is Bourbaki's definition of
properness, which `StacksDraft.Topology.isProperMap_iff_isBourbakiProperMap` identifies with
Mathlib's.

These declarations carry no tag: Stacks 0DCU has seven clauses and its covering set is not
complete until all of them are in the library.

## References

* [Stacks Project, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

namespace Stacks.Topology

universe v u w

section ClosedMap

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {g : X → Y}

/-- For a closed map `g`, an open set containing the fibre over `y` contains the preimage of an
open neighbourhood of `y`. -/
theorem exists_isOpen_preimage_subset_of_isClosedMap (hg : IsClosedMap g) {y : Y} {W : Set X}
    (hW : IsOpen W) (hfib : ∀ x : X, g x = y → x ∈ W) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ g ⁻¹' U ⊆ W := by
  refine ⟨(g '' Wᶜ)ᶜ, (hg _ hW.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx (hfib x rfl)
  · intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩

end ClosedMap

section Opens

variable {X Y : TopCat.{v}} {g : X ⟶ Y}

/-- For a closed map `g`, an open `W ⊆ X` containing the fibre over `y ∈ U` contains the
preimage of an open neighbourhood of `y` inside `U`. -/
theorem exists_opens_preimage_le_of_isClosedMap (hg : IsClosedMap (g : X → Y))
    {y : Y} (W : Opens X) (hfib : ∀ x : X, (g : X → Y) x = y → x ∈ W) (U : Opens Y)
    (hy : y ∈ U) :
    ∃ (U₀ : Opens Y) (_ : y ∈ U₀) (_ : U₀ ≤ U), (Opens.map g).obj U₀ ≤ W := by
  obtain ⟨V, hV, hyV, hVW⟩ :=
    exists_isOpen_preimage_subset_of_isClosedMap hg W.2 hfib
  refine ⟨⟨V ∩ (U : Set Y), hV.inter U.2⟩, ⟨hyV, hy⟩, fun z hz => hz.2, fun x hx => ?_⟩
  exact hVW (Opens.mem_map.1 hx).1

/-- Sections that agree on `A` agree on any open `N ⊆ A`, whichever restriction maps are used. -/
private theorem map_eq_map_of_restrict_eq {C : Type u} [Category.{w} C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    (F : TopCat.Presheaf C X) {A P Q N : Opens X}
    {s : ToType (F.obj (op P))} {t : ToType (F.obj (op Q))} {iP : A ⟶ P} {iQ : A ⟶ Q}
    (h : F.map iP.op s = F.map iQ.op t) (a : N ⟶ A) (b : N ⟶ P) (c : N ⟶ Q) :
    F.map b.op s = F.map c.op t := by
  rw [← map_op_comp_apply F a iP b, ← map_op_comp_apply F a iQ c, h]

variable {C : Type u} [Category.{w} C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable [HasLimitsOfSize.{v, v} C] [(forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{v, v} (forget C)]

/-- **Separatedness of the proper direct image.** Let `g : X → Y` be closed, let `F` be a sheaf
on `X` and let `s, t` be sections of `F` over `g⁻¹U`. If `s` and `t` agree on some open
neighbourhood of every point of the fibre over `y ∈ U`, then they agree over `g⁻¹U₀` for some
open neighbourhood `U₀ ⊆ U` of `y`.

Together with `exists_opens_preimage_glue_of_isCompact_fibre` this is the statement that the
sections of `g_*F` near `y` are the sections of `F` along the fibre over `y`. -/
theorem exists_opens_preimage_restrict_eq_of_locallyEqOn_fibre
    (hg : IsClosedMap (g : X → Y)) (F : TopCat.Sheaf C X) {U : Opens Y} {y : Y} (hy : y ∈ U)
    (s t : ToType (F.presheaf.obj (op ((Opens.map g).obj U))))
    (hloc : ∀ x : X, (g : X → Y) x = y →
      ∃ (N : Opens X) (_ : x ∈ N) (iN : N ⟶ (Opens.map g).obj U),
        F.presheaf.map iN.op s = F.presheaf.map iN.op t) :
    ∃ (U₀ : Opens Y) (_ : y ∈ U₀) (h₀ : U₀ ≤ U),
      F.presheaf.map ((Opens.map g).map (homOfLE h₀)).op s =
        F.presheaf.map ((Opens.map g).map (homOfLE h₀)).op t := by
  obtain ⟨A, hTA, iAU, iAV, heq⟩ :=
    exists_opens_restrict_eq_of_locallyEqOn F s t
      (T := (g : X → Y) ⁻¹' {y})
      (fun x hx => by
        obtain ⟨N, hxN, iN, hN⟩ := hloc x hx
        exact ⟨N, hxN, iN, iN, hN⟩)
  obtain ⟨U₀, hyU₀, hU₀U, hU₀A⟩ :=
    exists_opens_preimage_le_of_isClosedMap hg A (fun x hx => hTA hx) U hy
  refine ⟨U₀, hyU₀, hU₀U, ?_⟩
  exact map_eq_map_of_restrict_eq F.presheaf heq (homOfLE hU₀A) _ _

/-- **Gluing along the fibre of a proper map, separation assumed only in the fibre.** Let
`g : X → Y` be a closed map, let the fibre over `y` be quasi-compact and have its distinct points
separated by disjoint opens of `X`, let `F` be a sheaf on `X`, and let `sec i` be sections of `F`
on opens `W i` which cover the fibre over `y` and which agree near every point of the fibre on
which two of them are both defined. Then there is an open neighbourhood `U₀` of `y` and a section
of `F` over `g⁻¹U₀` agreeing near every point of the fibre with one of the `sec i`.

The separation hypothesis is what a *separated* `g` supplies in its fibres ([Stacks, Tag 0CY2]
(3)) with no assumption on `X`, and separatedness of `g` rather than Hausdorffness of `X` is the
hypothesis of [Stacks, Tag 09V5]. `exists_opens_preimage_glue_of_isCompact_fibre` is the
`T2Space X` corollary. -/
theorem exists_opens_preimage_glue_of_isCompact_fibre_of_pairwiseSeparated
    (hg : IsClosedMap (g : X → Y)) (F : TopCat.Sheaf C X) {y : Y}
    (hK : IsCompact ((g : X → Y) ⁻¹' {y}))
    (hsep : ∀ x : X, (g : X → Y) x = y → ∀ x' : X, (g : X → Y) x' = y → x ≠ x' →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ x' ∈ B ∧ Disjoint A B)
    (U : Opens Y) (hy : y ∈ U)
    {ι : Type*} (W : ι → Opens X) (sec : ∀ i, ToType (F.presheaf.obj (op (W i))))
    (hcover : ∀ x : X, (g : X → Y) x = y → ∃ i, x ∈ W i)
    (hloc : ∀ i j : ι, ∀ x : X, (g : X → Y) x = y → x ∈ W i → x ∈ W j →
      ∃ (N : Opens X) (_ : x ∈ N) (iNi : N ⟶ W i) (iNj : N ⟶ W j),
        F.presheaf.map iNi.op (sec i) = F.presheaf.map iNj.op (sec j)) :
    ∃ (U₀ : Opens Y) (_ : y ∈ U₀) (_ : U₀ ≤ U)
      (r : ToType (F.presheaf.obj (op ((Opens.map g).obj U₀)))),
      ∀ x : X, (g : X → Y) x = y →
        ∃ (i : ι) (N : Opens X) (_ : x ∈ N) (iN₀ : N ⟶ (Opens.map g).obj U₀)
          (iNi : N ⟶ W i),
          F.presheaf.map iN₀.op r = F.presheaf.map iNi.op (sec i) := by
  obtain ⟨V, iVW, hKV, s, hs⟩ :=
    exists_opens_glue_of_isCompact_of_pairwiseSeparated F hK
      (fun x hx x' hx' hne => hsep x hx x' hx' hne) W sec
      (fun x hx => Set.mem_iUnion.2 (hcover x hx))
      (fun i j x hx => hloc i j x hx.1.1 hx.1.2 hx.2)
  obtain ⟨U₀, hyU₀, hU₀U, hU₀V⟩ :=
    exists_opens_preimage_le_of_isClosedMap hg (⨆ i, V i) (fun x hx => hKV hx) U hy
  refine ⟨U₀, hyU₀, hU₀U, F.presheaf.map (homOfLE hU₀V).op s, fun x hx => ?_⟩
  have hxU₀ : x ∈ (Opens.map g).obj U₀ := Opens.mem_map.2 (hx ▸ hyU₀)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU₀V hxU₀)
  refine ⟨i, V i ⊓ (Opens.map g).obj U₀, ⟨hi, hxU₀⟩, homOfLE inf_le_right,
    homOfLE (le_trans inf_le_left (iVW i).le), ?_⟩
  rw [map_op_comp_apply F.presheaf _ _ (homOfLE (le_trans inf_le_left (Opens.leSupr V i).le))]
  exact map_eq_map_of_restrict_eq F.presheaf (hs i) (homOfLE inf_le_left) _ _

/-- **Gluing along the fibre of a proper map with Hausdorff source**: the case of
`exists_opens_preimage_glue_of_isCompact_fibre_of_pairwiseSeparated` in which the separation of
the points of the fibre comes from Hausdorffness of the source. -/
theorem exists_opens_preimage_glue_of_isCompact_fibre [T2Space X]
    (hg : IsClosedMap (g : X → Y)) (F : TopCat.Sheaf C X) {y : Y}
    (hK : IsCompact ((g : X → Y) ⁻¹' {y})) (U : Opens Y) (hy : y ∈ U)
    {ι : Type*} (W : ι → Opens X) (sec : ∀ i, ToType (F.presheaf.obj (op (W i))))
    (hcover : ∀ x : X, (g : X → Y) x = y → ∃ i, x ∈ W i)
    (hloc : ∀ i j : ι, ∀ x : X, (g : X → Y) x = y → x ∈ W i → x ∈ W j →
      ∃ (N : Opens X) (_ : x ∈ N) (iNi : N ⟶ W i) (iNj : N ⟶ W j),
        F.presheaf.map iNi.op (sec i) = F.presheaf.map iNj.op (sec j)) :
    ∃ (U₀ : Opens Y) (_ : y ∈ U₀) (_ : U₀ ≤ U)
      (r : ToType (F.presheaf.obj (op ((Opens.map g).obj U₀)))),
      ∀ x : X, (g : X → Y) x = y →
        ∃ (i : ι) (N : Opens X) (_ : x ∈ N) (iN₀ : N ⟶ (Opens.map g).obj U₀)
          (iNi : N ⟶ W i),
          F.presheaf.map iN₀.op r = F.presheaf.map iNi.op (sec i) :=
  exists_opens_preimage_glue_of_isCompact_fibre_of_pairwiseSeparated hg F hK
    (fun _ _ _ _ hne => by
      obtain ⟨a, b, ha, hb, hxa, hyb, hab⟩ := t2_separation hne
      exact ⟨a, b, ha, hb, hxa, hyb, hab⟩) U hy W sec hcover hloc

end Opens

section Proper

/-- The Stacks notion of a proper map of topological spaces (separated and universally closed,
Stacks 005O (5)) implies Mathlib's `IsProperMap` for a continuous map: base changing along the
second projection `Z × Y → Y` turns the universal closedness of `g` into closedness of
`Prod.map id g`, which is Bourbaki's definition. -/
theorem isProperMap_of_isProperMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : Continuous g) (h : StacksDraft.Topology.IsProperMap.{u, u, u} g) :
    _root_.IsProperMap g := by
  rw [StacksDraft.Topology.isProperMap_iff_isBourbakiProperMap]
  refine ⟨hg, fun Z _ => ?_⟩
  let e : Z × X ≃ₜ Function.Pullback (Prod.snd : Z × Y → Y) g :=
    { toFun := fun p => ⟨((p.1, g p.2), p.2), rfl⟩
      invFun := fun p => (p.val.1.1, p.val.2)
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨z, y⟩, x⟩, (hp : y = g x)⟩
        exact Subtype.ext (Prod.ext (Prod.ext rfl hp.symm) rfl)
      continuous_toFun := continuous_induced_rng.2
        ((continuous_fst.prodMk (hg.comp continuous_snd)).prodMk continuous_snd)
      continuous_invFun :=
        (continuous_subtype_val.fst.fst).prodMk continuous_subtype_val.snd }
  have key : (Prod.map (id : Z → Z) g) = Function.Pullback.fst ∘ e := by
    funext p
    rfl
  rw [key]
  exact (h.2 (Z × Y) Prod.snd continuous_snd).comp e.isClosedMap

end Proper

end Stacks.Topology

end
