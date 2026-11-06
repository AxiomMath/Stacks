module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap

/-!
# The vanishing of the universal derivation, chartwise

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let
`d_{X/Y} : 𝒪_X ⟶ Ω_{X/Y}` be the universal `Y`-derivation of Stacks 04CT. This file shows that, on
an étale chart `W` of `X` lying over an étale chart `V` of `Y`, `d_{X/Y}` kills the pullback to `W`
of every regular function on `V`, and that `Ω_{X/Y}` is a zero object exactly when `d_{X/Y}`
vanishes.

## Main results

* `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_iff`: `Ω_{X/Y}` is a zero object exactly
  when `d_{X/Y}` vanishes on every section of `𝒪_X` over every étale chart of `X`.
* `AlgebraicGeometry.Space.universalDerivation_d_chartPullback`: `d_{X/Y}` kills the pullback to
  an étale chart of `X` of a regular function on an étale chart of `Y`.

## References

* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal derivation.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces and its structure map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- **The sheaf of differentials is a zero object exactly when the universal derivation
vanishes** on every local section. -/
theorem isZero_sheafOfDifferentials_iff (f : X ⟶ Y) :
    IsZero (sheafOfDifferentials B S hS f) ↔
      ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
        (a : (structureRingSheaf B S hS X).obj.obj W),
        (universalDerivation B S hS f).d a = 0 := by
  constructor
  · intro h W a
    exact PresheafOfModulesOfCommRing.Derivation.congr_d (congrArg
      (fun g : sheafOfDifferentials B S hS f ⟶ sheafOfDifferentials B S hS f =>
        (universalDerivation B S hS f).postcomp g.val) ((IsZero.iff_id_eq_zero _).mp h)) a
  · intro h
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    obtain ⟨g, hg, huniq⟩ := universalDerivation_isUniversal B S hS f
      (sheafOfDifferentials B S hS f)
      ((universalDerivation B S hS f).postcomp (0 : sheafOfDifferentials B S hS f ⟶
        sheafOfDifferentials B S hS f).val)
    rw [huniq _ rfl, huniq (𝟙 _) ?_]
    ext W a
    exact h W a

/-- **The universal derivation kills the functions pulled back from the base.** Let `V` be an
étale chart of `Y` and let `W` be an étale chart of `X` above `X ×_Y V`. Then `d_{X/Y}`
annihilates the pullback to `W` of every regular function on `V`. -/
theorem universalDerivation_d_chartPullback (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    (universalDerivation B S hS f).d (chartPullback B S hS f V j b) = 0 := by
  set D := universalDerivationHom B S hS f
  set Z := zeroDerivationHom (structureRingSheaf B S hS X) (sheafOfDifferentials B S hS f)
  have key := structureSharpSet_comp_universalDerivationHom B S hS f (𝟙 Y) f
    (Category.comp_id f).symm
  have hiD := (smallEtaleDirectImageRanIso B S hS f).hom.naturality D
  have hiZ := (smallEtaleDirectImageRanIso B S hS f).hom.naturality Z
  have keyRan : structureSharpRanSet B S hS f ≫ (smallEtaleDirectImageRan B S hS f).map D =
      structureSharpRanSet B S hS f ≫ (smallEtaleDirectImageRan B S hS f).map Z := by
    rw [← structureSharpSet_comp_ranIso B S hS f, Category.assoc, Category.assoc,
      ← hiD, ← hiZ, ← Category.assoc, ← Category.assoc, key]
  have hsec := congrArg
    (fun m : structureSetSheaf B S hS Y ⟶
        (smallEtaleDirectImageRan B S hS f).obj
          (moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
            (sheafOfDifferentials B S hS f)) => m.hom.app (op V) b) keyRan
  have hsecc : (directImageSections B S hS f V).map D (structureMapApp B S hS f V b) =
      (directImageSections B S hS f V).map Z (structureMapApp B S hS f V b) := hsec
  have hn := fun E : type_of% D => natTrans_app_map_apply (chartProjection B S hS f V j) E
    (structureMapApp B S hS f V b)
  have hfinal : (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map D
        (chartPullback B S hS f V j b) =
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map Z
        (chartPullback B S hS f V j b) := by
    rw [← chartProjection_structureMapApp B S hS f V j b, ← hn D, ← hn Z, hsecc]
  exact hfinal.trans (map_zeroDerivationHom (structureRingSheaf B S hS X)
    (sheafOfDifferentials B S hS f) (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) j.right)
    (chartPullback B S hS f V j b))

end AlgebraicGeometry.Space

end
