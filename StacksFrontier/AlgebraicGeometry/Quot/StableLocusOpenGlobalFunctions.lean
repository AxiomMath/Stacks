module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpGlobalFunctionsInjective

/-!
# `f_*𝒪 = 𝒪` universally passes to the target of a universal structure contraction

Let `f : X → S` and `g : Y → S` be families of curves over the same base and `c : X → Y` a
morphism over `S` such that `𝒪_Y = c_*𝒪_X`, and this remains true after every base change by a
scheme `T → S` (part of condition (1) of Stacks 0E8A, as produced by Stacks 0E88). If
`f_*𝒪_X = 𝒪_S` universally then `g_*𝒪_Y = 𝒪_S` universally.

## Main results

* `AlgebraicGeometry.Space.bijective_globalFunctionsMap_fiberProduct_of_isIso_structureSharp`:
  the statement for morphisms of algebraic spaces over an algebraic space `Z`.
* `CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp_baseChange`:
  the statement for families of curves, with the hypothesis on `c` in the shape of condition (1)
  of Stacks 0E8A (`AlgebraicGeometry.CurveFamily.IsUniversalStructureContraction`).

## Implementation notes

Pullback of global functions along `Y_T → T` is bijective once it is so along `X_T → T` and the
structure map of `X_T → Y_T` is an isomorphism, because then `Γ(Y_T) → Γ(X_T)` is injective
(`AlgebraicGeometry.Space.injective_globalFunctionsMap_of_isIso_structureSharp`). Base changes
along algebraic spaces are reduced to base changes along schemes by
`AlgebraicGeometry.Space.bijective_globalFunctionsMap_of_forall_schemeSpace`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`g_*𝒪_Y = 𝒪_Z` universally, from the same for `f` along a morphism with universally
invertible structure map.** Let `f : X ⟶ Z` and `g : Y ⟶ Z` be morphisms of algebraic spaces and
`c : X ⟶ Y` a morphism over `Z`. Suppose that for every scheme `T` and morphism `φ : T ⟶ Z`, the
morphism `c' : X ×_Z T ⟶ Y ×_Z T` induced by `c` on any pair of fibre products has invertible
structure map, and that pullback of global functions along every base change `X ×_Z Z' ⟶ Z'` of
`f` by an algebraic space `Z'` is bijective. Then the same holds for `g`. -/
theorem bijective_globalFunctionsMap_fiberProduct_of_isIso_structureSharp
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) (c : X ⟶ Y) (hc : c ≫ g = f)
    (h : ∀ (T : BigFppfOver B S hS) (φ : schemeSpace T ⟶ Z)
      (X' Y' : AlgebraicSpaces B S hS) (pX' : X' ⟶ X) (fX' : X' ⟶ schemeSpace T)
      (pY' : Y' ⟶ Y) (fY' : Y' ⟶ schemeSpace T) (c' : X' ⟶ Y'),
      IsPullback pX' fX' f φ → IsPullback pY' fY' g φ →
      c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' → IsIso (structureSharp B S hS c'))
    (hX : ∀ (Z' : AlgebraicSpaces B S hS) (ψ : Z' ⟶ Z),
      Function.Bijective (globalFunctionsMap B S hS
        (ObjectProperty.homMk (pullback.snd f.hom ψ.hom) :
          AlgebraicSpaces.fiberProduct B S hS f ψ ⟶ Z')))
    (Z' : AlgebraicSpaces B S hS) (ψ : Z' ⟶ Z) :
    Function.Bijective (globalFunctionsMap B S hS
      (ObjectProperty.homMk (pullback.snd g.hom ψ.hom) :
        AlgebraicSpaces.fiberProduct B S hS g ψ ⟶ Z')) := by
  refine bijective_globalFunctionsMap_of_forall_schemeSpace _ fun T t => ?_
  let π : AlgebraicSpaces.fiberProduct B S hS g ψ ⟶ Z' :=
    ObjectProperty.homMk (pullback.snd g.hom ψ.hom)
  have sqP := (AlgebraicSpaces.isPullback_fiberProduct B S hS π t).paste_horiz
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g ψ)
  have sqQ := AlgebraicSpaces.isPullback_fiberProduct B S hS f (t ≫ ψ)
  have hw : ((ObjectProperty.homMk (pullback.fst f.hom (t ≫ ψ).hom) :
      AlgebraicSpaces.fiberProduct B S hS f (t ≫ ψ) ⟶ X) ≫ c) ≫ g =
      (ObjectProperty.homMk (pullback.snd f.hom (t ≫ ψ).hom) :
        AlgebraicSpaces.fiberProduct B S hS f (t ≫ ψ) ⟶ schemeSpace T) ≫ (t ≫ ψ) := by
    rw [Category.assoc, hc]
    exact sqQ.w
  let c' := sqP.lift _ _ hw
  have hc' : IsIso (structureSharp B S hS c') :=
    h T (t ≫ ψ) _ _ _ _ _ _ c' sqQ sqP (sqP.lift_fst _ _ _) (sqP.lift_snd _ _ _)
  refine bijective_globalFunctionsMap_of_comp_of_isIso_structureSharp B S hS c' _ hc' ?_
  rw [sqP.lift_snd]
  exact hX (schemeSpace T) (t ≫ ψ)

end Space

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`f_*𝒪_X = 𝒪_S` universally passes along a universal structure contraction.** Let `X` and
`Y` be families of curves over the same base `S` (`hb : Y.base = X.base`) and `c : X ⟶ Y` a
morphism over `S` such that, for every scheme `T` of the site over `S` and every pair of
fibre products `X' = X ×_S T`, `Y' = Y ×_S T`, the morphism `c' : X' ⟶ Y'` induced by `c` has
invertible structure map `𝒪_{Y'} ⟶ c'_*𝒪_{X'}`. If `X` has `f_*𝒪_X = 𝒪_S` universally, so
does `Y`. -/
theorem hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp_baseChange
    {X Y : CurveFamily B hZ} (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    (h : ∀ (T : BigFppfOver B integerBase hZ) (t : T ⟶ X.base)
      (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total) (fX' : X' ⟶ schemeSpace T)
      (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T) (c' : X' ⟶ Y'),
      IsPullback pX' fX' X.toBase (schemeSpaceMap t) →
      IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap t) →
      c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
      IsIso (Space.structureSharp B integerBase hZ c'))
    (hX : HasUniversallyBijectiveGlobalFunctions B hZ X) :
    HasUniversallyBijectiveGlobalFunctions B hZ Y := by
  revert hb c hc h
  obtain ⟨Yb, Yt, Yf, h1, h2, h3, h4⟩ := Y
  intro hb c hc h
  dsimp only at hb
  subst hb
  simp only [eqToHom_refl, Category.comp_id] at hc h
  intro Z' ψ
  refine Space.bijective_globalFunctionsMap_fiberProduct_of_isIso_structureSharp B integerBase hZ
    X.toBase Yf c hc (fun T φ X' Y' pX' fX' pY' fY' c' hX' hY' e1 e2 => ?_) hX Z' ψ
  obtain ⟨t, rfl⟩ : ∃ t : T ⟶ X.base, schemeSpaceMap t = φ :=
    ⟨yoneda.preimage φ.hom, ObjectProperty.hom_ext _ (yoneda.map_preimage φ.hom)⟩
  exact h T t X' Y' pX' fX' pY' fY' c' hX' hY' e1 e2

end CurveFamily

end AlgebraicGeometry

end
