module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.Topology.Spectral.LimitNonempty

/-!
# Cofiltered limits of spectral spaces indexed by a slice category

Let `J` be a cofiltered category, `F : J ⥤ TopCat` a diagram and `j : J` an object. The slice
category `Over j` is again cofiltered (`CategoryTheory.IsCofiltered.over`), and the forgetful
functor `Over.forget j` is initial, so a compatible family indexed by `Over j` is the same thing as
a compatible family indexed by all of `J`.

## Main results

* `SpectralLimits.eq_of_over_compatible`: for a family `y` of points `y B ∈ F(B.left)` compatible
  along all morphisms of `Over j`, the point `F.map u (y (Over.mk v))` of `F.obj m` does not
  depend on the pair `(u : n ⟶ m, v : n ⟶ j)`.
* `SpectralLimits.exists_mem_limitSet_of_over_compatible`: such a family is the restriction to
  `Over j` of a point of `limitSet F`.
* `SpectralLimits.nonempty_limitSet_inter_over`: a compatible system of nonempty constructibly
  closed subsets `Z B ⊆ F(B.left)` indexed only by the slice `Over j` already has a point of
  `limitSet F` meeting every `Z B`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v w
universe v'

namespace SpectralLimits

variable {J : Type v} [Category.{v'} J] [IsCofiltered J]

/-- A family `y` of points indexed by the slice category `Over j` and compatible along all
morphisms of `Over j` determines a well-defined point of `F.obj m` for every `m : J`: the point
`F.map u (y (Over.mk v))` is independent of the choice of the object `n` and the pair of morphisms
`u : n ⟶ m`, `v : n ⟶ j`. -/
theorem eq_of_over_compatible {j : J} (F : J ⥤ TopCat.{w}) (y : ∀ B : Over j, F.obj B.left)
    (hy : ∀ {B B' : Over j} (f : B' ⟶ B), F.map f.left (y B') = y B)
    {m n n' : J} (u : n ⟶ m) (v : n ⟶ j) (u' : n' ⟶ m) (v' : n' ⟶ j) :
    F.map u (y (Over.mk v)) = F.map u' (y (Over.mk v')) := by
  obtain ⟨q, a, b, hu, hv⟩ := IsCofiltered.bowtie u u' v v'
  have h : F.map a (y (Over.mk (a ≫ v))) = y (Over.mk v) :=
    hy (B := Over.mk v) (B' := Over.mk (a ≫ v)) (Over.homMk a rfl)
  have h' : F.map b (y (Over.mk (a ≫ v))) = y (Over.mk v') :=
    hy (B := Over.mk v') (B' := Over.mk (a ≫ v)) (Over.homMk b hv.symm)
  rw [← h, ← h']
  simpa using congrArg (fun w : q ⟶ m ↦ F.map w (y (Over.mk (a ≫ v)))) hu

/-- A compatible family of points indexed by the slice category `Over j` extends to a compatible
family indexed by all of `J`, that is, to a point of `limitSet F` whose `B.left`-coordinate is
`y B` for every `B : Over j`. -/
theorem exists_mem_limitSet_of_over_compatible {j : J} (F : J ⥤ TopCat.{w})
    (y : ∀ B : Over j, F.obj B.left)
    (hy : ∀ {B B' : Over j} (f : B' ⟶ B), F.map f.left (y B') = y B) :
    ∃ x : ∀ m : J, F.obj m, x ∈ limitSet F ∧ ∀ B : Over j, x B.left = y B := by
  have key : ∀ (m : J) {n : J} (u : n ⟶ m) (v : n ⟶ j),
      F.map (IsCofiltered.minToLeft m j) (y (Over.mk (IsCofiltered.minToRight m j)))
        = F.map u (y (Over.mk v)) := fun m _ u v ↦ eq_of_over_compatible F y hy _ _ u v
  refine ⟨fun m ↦ F.map (IsCofiltered.minToLeft m j)
    (y (Over.mk (IsCofiltered.minToRight m j))), ?_, ?_⟩
  · intro n m c
    dsimp only
    rw [key m (IsCofiltered.minToLeft n j ≫ c) (IsCofiltered.minToRight n j), F.map_comp]
    rfl
  · intro B
    dsimp only
    rw [key B.left (𝟙 B.left) B.hom, F.map_id]
    rfl

/-- For a spectral diagram `F : J ⥤ TopCat` over a cofiltered `J` and an object `j : J`, a
compatible system of nonempty constructibly closed subsets indexed by the slice category `Over j`
already produces a point of `limitSet F` lying in every member of the system. -/
theorem nonempty_limitSet_inter_over {F : J ⥤ TopCat.{w}} (hF : IsSpectralDiagram F) (j : J)
    (Z : ∀ B : Over j, Set (F.obj B.left)) (hZ_ne : ∀ B, (Z B).Nonempty)
    (hZ_cl : ∀ B, @IsClosed (F.obj B.left) (constructibleTopology (F.obj B.left)) (Z B))
    (hZ_comp : ∀ {B B' : Over j} (f : B' ⟶ B), F.map f.left '' Z B' ⊆ Z B) :
    ∃ x : ∀ m : J, F.obj m, x ∈ limitSet F ∧ ∀ B : Over j, x B.left ∈ Z B := by
  have hF' : IsSpectralDiagram (Over.forget j ⋙ F) :=
    { spectral_obj := fun B ↦ hF.spectral_obj B.left
      spectral_map := fun {_ _} f ↦ hF.spectral_map f.left }
  obtain ⟨y, hy_lim, hy_mem⟩ :=
    nonempty_limitSet_inter_of_isClosed_constructible hF' Z hZ_ne hZ_cl fun {_ _} f ↦ hZ_comp f
  obtain ⟨x, hx_lim, hx⟩ := exists_mem_limitSet_of_over_compatible F y fun {_ _} f ↦ hy_lim f
  exact ⟨x, hx_lim, fun B ↦ (hx B).symm ▸ hy_mem B⟩

end SpectralLimits
