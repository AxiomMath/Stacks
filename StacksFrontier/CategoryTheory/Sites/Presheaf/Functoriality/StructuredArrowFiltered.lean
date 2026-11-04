module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import StacksCore.Tactic.EgaSgaAttribute

/-! # The index categories of a functor are filtered

For a functor `u : C ⥤ D` and an object `V : D`, the index category `I_V^u` of Stacks 07 §5 is the
comma category `StructuredArrow V u`. This file shows that its opposite is filtered as soon as `C`
has a terminal object and fibre products which `u` preserves.

## Main results

* `isFiltered_op_structuredArrow`: `(StructuredArrow V u)ᵒᵖ` is filtered (Stacks 00X3).

Tags covered: 00X3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor preserving the terminal object sends `⊤_ C` to a terminal object. -/
private noncomputable abbrev isTerminal_obj_terminal
    (u : C ⥤ D) [HasTerminal C] [PreservesLimitsOfShape (Discrete PEmpty.{1}) u] :
    IsTerminal (u.obj (⊤_ C)) :=
  IsTerminal.isTerminalObj u _ terminalIsTerminal

/-- `StructuredArrow V u` is non-empty when `C` has a terminal object and `u`
preserves it: the unique map `V ⟶ u (⊤_ C)` gives an object. -/
private lemma structuredArrow_nonempty
    (u : C ⥤ D) [HasTerminal C]
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) u] (V : D) :
    Nonempty (StructuredArrow V u) := by
  exact ⟨StructuredArrow.mk ((isTerminal_obj_terminal u).from V)⟩

/-- Given two structured arrows over `V`, the pullback in `C` of the unique maps
to the terminal object lifts to a common predecessor in `StructuredArrow V u`. -/
private lemma structuredArrow_cone_objs
    (u : C ⥤ D) [HasTerminal C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) u]
    [PreservesLimitsOfShape WalkingCospan u] (V : D)
    (X Y : StructuredArrow V u) :
    ∃ (W : StructuredArrow V u) (_ : W ⟶ X) (_ : W ⟶ Y), True := by
  let tX : X.right ⟶ (⊤_ C) := terminal.from X.right
  let tY : Y.right ⟶ (⊤_ C) := terminal.from Y.right
  have hP : IsLimit (PullbackCone.mk
      (u.map (Limits.pullback.fst tX tY))
      (u.map (Limits.pullback.snd tX tY))
      (by rw [← u.map_comp, ← u.map_comp, Limits.pullback.condition])) :=
    (PullbackCone.isLimitMapConeEquiv (Limits.pullback.cone tX tY) u)
      (isLimitOfPreserves u (Limits.pullback.isLimit tX tY))
  obtain ⟨ψ, hψ₁, hψ₂⟩ := PullbackCone.IsLimit.lift' hP X.hom Y.hom
    ((isTerminal_obj_terminal u).hom_ext _ _)
  refine ⟨StructuredArrow.mk ψ,
    StructuredArrow.homMk (Limits.pullback.fst tX tY) hψ₁,
    StructuredArrow.homMk (Limits.pullback.snd tX tY) hψ₂, trivial⟩

/-- Given two parallel arrows `f g : X ⟶ Y` of structured arrows over `V`, the
equalizer of their underlying maps in `C` lifts to a coequalizing predecessor.
The equalizers in `C` and their `u`-preservation come from
`hasEqualizers_of_hasPullbacks_and_binary_products` and
`preservesEqualizers_of_preservesPullbacks_and_binaryProducts`. -/
private lemma structuredArrow_cone_maps
    (u : C ⥤ D) [HasTerminal C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) u]
    [PreservesLimitsOfShape WalkingCospan u] (V : D)
    ⦃X Y : StructuredArrow V u⦄ (f g : X ⟶ Y) :
    ∃ (W : StructuredArrow V u) (h : W ⟶ X), h ≫ f = h ≫ g := by
  have : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  have : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products
  have : PreservesLimitsOfShape (Discrete WalkingPair) u :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks u
  have : PreservesLimitsOfShape WalkingParallelPair u :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts u
  have he : equalizer.ι f.right g.right ≫ f.right
            = equalizer.ι f.right g.right ≫ g.right :=
    equalizer.condition f.right g.right
  have hxEq : X.hom ≫ u.map f.right = X.hom ≫ u.map g.right := by
    rw [StructuredArrow.w f, StructuredArrow.w g]
  obtain ⟨φE, hφE⟩ := Fork.IsLimit.lift'
    (isLimitForkMapOfIsLimit u he (equalizerIsEqualizer f.right g.right)) X.hom hxEq
  refine ⟨StructuredArrow.mk φE,
    StructuredArrow.homMk (equalizer.ι f.right g.right)
      (by simpa [Fork.ofι, Fork.ι] using hφE),
    StructuredArrow.hom_ext _ _ ?_⟩
  simpa using he

/-- **Stacks 00X3.** Let `u : C ⥤ D` be a functor. Suppose `C` has a terminal
object whose image under `u` is terminal in `D`, and `C` has fibre products
which `u` preserves. Then for every `V : D` the opposite of the comma category
`StructuredArrow V u` is filtered. -/
@[stacks 00X3, sga "5 V 2.3.3" "special case"]
theorem isFiltered_op_structuredArrow
    (u : C ⥤ D) [HasTerminal C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) u]
    [PreservesLimitsOfShape WalkingCospan u] (V : D) :
    IsFiltered (StructuredArrow V u)ᵒᵖ := by
  have : Nonempty (StructuredArrow V u) := structuredArrow_nonempty u V
  have : IsCofilteredOrEmpty (StructuredArrow V u) :=
    { cone_objs := structuredArrow_cone_objs u V
      cone_maps := structuredArrow_cone_maps u V }
  have : IsCofiltered (StructuredArrow V u) := ⟨⟩
  exact (isFiltered_op_iff_isCofiltered (StructuredArrow V u)).mpr inferInstance
