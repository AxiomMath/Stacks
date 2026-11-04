module

public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending a regular immersion through a smooth morphism

An immersion whose composite with a smooth morphism is regular is itself regular, and likewise for
Koszul-regular, `H₁`-regular and quasi-regular immersions. The immersion is recovered from its
graph, which is a section of a smooth projection and hence a regular immersion, composed with a
flat base change of the given composite.

## Main definitions

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.graph`: the graph of `i` relative to `f`, a section
  of the first projection of the fibre product of `i ≫ f` with `f`.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isRegularImmersion_of_comp_of_smooth`,
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_comp_of_smooth`,
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isH1RegularImmersion_of_comp_of_smooth` and
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegularImmersion_of_comp_of_smooth` are
  Stacks 067S for regular, Koszul-regular, `H₁`-regular and quasi-regular immersions.

## References

* [Stacks Project, Tag 067S](https://stacks.math.columbia.edu/tag/067S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Y X S : Scheme.{u}}

/-- The graph of `i : Y ⟶ X` relative to `f : X ⟶ S`, as a morphism into the fibre product of
`i ≫ f` and `f`. It is a section of the first projection. -/
@[ega "I 5.3.11"]
noncomputable def graph (i : Y ⟶ X) (f : X ⟶ S) : Y ⟶ pullback (i ≫ f) f :=
  pullback.lift (𝟙 Y) i (by simp)

/-- The graph is a section of the first projection. -/
@[simp]
theorem graph_fst (i : Y ⟶ X) (f : X ⟶ S) :
    graph i f ≫ pullback.fst (i ≫ f) f = 𝟙 Y :=
  pullback.lift_fst _ _ _

/-- The graph followed by the second projection is the original morphism. -/
@[simp]
theorem graph_snd (i : Y ⟶ X) (f : X ⟶ S) :
    graph i f ≫ pullback.snd (i ≫ f) f = i :=
  pullback.lift_snd _ _ _

/-- Regularity transports along an equality of immersions. The instance argument of
`IsRegularImmersion` makes the corresponding rewrite fail on the motive. -/
private theorem isRegularImmersion_congr {i j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
    (h : i = j) (hi : IsRegularImmersion i) : IsRegularImmersion j := by
  subst h; exact hi

/-- The graph of an immersion relative to a smooth morphism is a regular immersion. -/
private theorem isRegularImmersion_graph (i : Y ⟶ X) (f : X ⟶ S) [Smooth f] :
    letI : IsImmersion (graph i f) :=
      Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id _ _ (graph_fst i f)
    IsRegularImmersion (graph i f) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
    (pullback.fst (i ≫ f) f) (graph i f) (graph_fst i f)

/-- **Stacks 067S** for regular immersions. If the composite of an immersion with a smooth
morphism is regular, the immersion is regular. -/
@[stacks 067S "regular"]
theorem isRegularImmersion_of_comp_of_smooth
    (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i] [IsImmersion (i ≫ f)] [Smooth f]
    (hj : IsRegularImmersion (i ≫ f)) : IsRegularImmersion i := by
  have hΓim : IsImmersion (graph i f) :=
    Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id _ _ (graph_fst i f)
  have hΓ : IsRegularImmersion (graph i f) :=
    isRegularImmersion_graph i f
  have hsnd : IsRegularImmersion (pullback.snd (i ≫ f) f) :=
    Stacks.AlgebraicGeometry.isRegularImmersion_pullback_snd_of_flat (i ≫ f) f hj
  exact isRegularImmersion_congr (graph_snd i f)
    (Stacks.AlgebraicGeometry.isRegularImmersion_comp
      (graph i f) (pullback.snd (i ≫ f) f) hΓ hsnd)

/-- Koszul-regularity transports along an equality of immersions. The instance argument of
`IsKoszulRegularImmersion` makes the corresponding rewrite fail on the motive. -/
private theorem isKoszulRegularImmersion_congr {i j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
    (h : i = j) (hi : IsKoszulRegularImmersion i) : IsKoszulRegularImmersion j := by
  subst h; exact hi

/-- **Stacks 067S** for Koszul-regular immersions. If the composite of an immersion with a smooth
morphism is Koszul-regular, the immersion is Koszul-regular. -/
@[stacks 067S "koszul_regular"]
theorem isKoszulRegularImmersion_of_comp_of_smooth
    (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i] [IsImmersion (i ≫ f)] [Smooth f]
    (hj : IsKoszulRegularImmersion (i ≫ f)) : IsKoszulRegularImmersion i := by
  have hΓim : IsImmersion (graph i f) :=
    Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id _ _ (graph_fst i f)
  have hΓ : IsKoszulRegularImmersion (graph i f) :=
    isKoszulRegularImmersion_of_isRegularImmersion _
      (isRegularImmersion_graph i f)
  have hsnd : IsKoszulRegularImmersion (pullback.snd (i ≫ f) f) :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_pullback_snd_of_flat (i ≫ f) f hj
  exact isKoszulRegularImmersion_congr (graph_snd i f)
    (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp
      (graph i f) (pullback.snd (i ≫ f) f) hΓ hsnd)

/-- `H₁`-regularity transports along an equality of immersions. -/
private theorem isH1RegularImmersion_congr {i j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
    (h : i = j) (hi : IsH1RegularImmersion i) : IsH1RegularImmersion j := by
  subst h; exact hi

/-- Quasi-regularity transports along an equality of immersions. -/
private theorem isQuasiRegularImmersion_congr {i j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
    (h : i = j) (hi : IsQuasiRegularImmersion i) : IsQuasiRegularImmersion j := by
  subst h; exact hi

/-- **Stacks 067S** for `H₁`-regular immersions. If the composite of an immersion with a smooth
morphism is `H₁`-regular, the immersion is `H₁`-regular. -/
@[stacks 067S "h1_regular"]
theorem isH1RegularImmersion_of_comp_of_smooth
    (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i] [IsImmersion (i ≫ f)] [Smooth f]
    (hj : IsH1RegularImmersion (i ≫ f)) : IsH1RegularImmersion i := by
  have hΓim : IsImmersion (graph i f) :=
    Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id _ _ (graph_fst i f)
  have hΓ : IsH1RegularImmersion (graph i f) :=
    isH1RegularImmersion_of_isKoszulRegularImmersion _
      (isKoszulRegularImmersion_of_isRegularImmersion _ (isRegularImmersion_graph i f))
  have hsnd : IsH1RegularImmersion (pullback.snd (i ≫ f) f) :=
    Stacks.AlgebraicGeometry.isH1RegularImmersion_pullback_snd_of_flat (i ≫ f) f hj
  exact isH1RegularImmersion_congr (graph_snd i f)
    (Stacks.AlgebraicGeometry.isH1RegularImmersion_comp
      (graph i f) (pullback.snd (i ≫ f) f) hΓ hsnd)

/-- **Stacks 067S** for quasi-regular immersions. If the composite of an immersion with a smooth
morphism is quasi-regular, the immersion is quasi-regular. -/
@[stacks 067S "quasi_regular"]
theorem isQuasiRegularImmersion_of_comp_of_smooth
    (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i] [IsImmersion (i ≫ f)] [Smooth f]
    (hj : IsQuasiRegularImmersion (i ≫ f)) : IsQuasiRegularImmersion i := by
  have hΓim : IsImmersion (graph i f) :=
    Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id _ _ (graph_fst i f)
  have hΓ : IsH1RegularImmersion (graph i f) :=
    isH1RegularImmersion_of_isKoszulRegularImmersion _
      (isKoszulRegularImmersion_of_isRegularImmersion _ (isRegularImmersion_graph i f))
  have hsnd : IsQuasiRegularImmersion (pullback.snd (i ≫ f) f) :=
    Stacks.AlgebraicGeometry.isQuasiRegularImmersion_pullback_snd_of_flat (i ≫ f) f hj
  exact isQuasiRegularImmersion_congr (graph_snd i f)
    (Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comp_of_isH1RegularImmersion
      (graph i f) (pullback.snd (i ≫ f) f) hΓ hsnd)

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
