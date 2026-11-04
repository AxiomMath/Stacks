module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilCohomologyTheory
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.PushforwardCalculus.Chow
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.PushforwardCalculus.IsoTrace

/-!
# The Gysin pullback of the diagonal along `x × id` is the class of the point

In the proof of Axiom (A6) for the de Rham cohomology of an irreducible smooth projective `X` of
dimension `d` over a field `k` (Stacks 0FWD), the source takes a closed point `x ∈ X` and the
cartesian square

  `x ⟶ X` (top), `x ⟶ X` (left), `Δ : X ⟶ X ×_k X` (right), `x × id : X ⟶ X ×_k X` (bottom),

and concludes from the compatibility of `γ` with pullbacks that `γ([Δ])` maps to `γ([x])`. The
Chow-theoretic content is that the Gysin pullback along `x × id` of the class of the diagonal is
the class of the point:

  `(x × id)^! [Δ] = [x]`   in `CH^d(X)`.

This file proves it for a `k`-rational point `x` of a scheme `X` smooth and separated over `k` of
constant dimension `d`, for any fibre product `P = X ×_k X` with projections `p`, `q`, diagonal
`δ` and `j = x × id`.

The proof is the transversality of the square. The Gysin map `j^!` of Stacks 0FF3 is formed on the
pieces `X_{d,e} = X_d ∩ j⁻¹(P_e)` (`Stacks.Chow.codimensionGysin`); as `X` has dimension `d` and
`P` dimension `2d`, all pieces but `X_{d,2d} = X` are empty. On `X_{d,2d}` the class `[Δ]` is
`δ_*[X]_d`, and `j^!` commutes with proper pushforward (Stacks 0B76 (1)), so `j^![Δ]` is the
pushforward of `j^![X]_d` computed at the test scheme `Δ : X ⟶ P`. There Stacks 0FF7 applies:
`X`, `P`, the test scheme `X` are pure of dimensions `d`, `2d`, `d`, the local rings of `X` are
Cohen–Macaulay, and the scheme-theoretic intersection `Z = X ×_{j, P, δ} X` is the reduced point
`Spec k`, of the expected dimension `0`; hence `j^![X]_d = [Z]_0`. Pushing `[Z]_0 = [Spec k]_0`
forward to `X` is `x_*[Spec k]_0 = [x]`.

## Main results

* `Stacks.WeilDeRham.codimensionGysin_diagonal_eq_point` — `(x × id)^! [Δ] = [x]` in
  `CH^d(X)`.
* `Stacks.WeilDeRham.dimPartPieceGysin_diagonal_eq_point` — the same identity on the piece
  `X_{d,2d}`, where the computation happens.
* `Stacks.WeilDeRham.dimPart_eq_top_of_relativeDimension` — for a smooth morphism of relative
  dimension `d` the part of dimension `d` is everything.
* `Stacks.WeilDeRham.closedSubschemeClass_eq_chowCodimPushforward` — the class of a closed
  subscheme of pure dimension is the pushforward of its fundamental class; for the diagonal, the
  base's `[Δ]` (`Stacks.WeilCohomology.SmoothProjectiveScheme.diagonalClass`) is `δ_*[X]`.

## Implementation notes

The classes `[Δ] = δ_*[X]` and `[x] = x_*[Spec k]` are read in codimension `d` as in the
definition of a Weil cohomology theory: `Stacks.WeilCohomology.chowCodimPushforward` of
`Stacks.WeilCohomology.chowCodimFundamental` (proper pushforward of Stacks 02R4 in each dimension,
then the codimension-`d` part); for the diagonal of a smooth projective scheme this is the base's
class `Stacks.WeilCohomology.SmoothProjectiveScheme.diagonalClass` of the closed subscheme `Δ`
(`Stacks.WeilDeRham.closedSubschemeClass_eq_chowCodimPushforward`). These classes lie in
`Stacks.Chow.codimensionChowGroup k sX d`, so the Gysin map of the base,
`Stacks.Chow.codimensionGysin`, applies to them.

The point `x` is a section of `X ⟶ Spec k`; the source's closed point of an irreducible
projective `X` over an algebraically closed field is such a point. Neither irreducibility nor
properness nor `k` algebraically closed is used: separatedness makes `δ` and `x` closed immersions,
hence proper.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.WeilDeRham

open Stacks.Chow
open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart chowCodimTotal chowCodimFundamental chowCodimPushforward
  eq_of_mem_dimPart isEmpty_dimPart_of_ne)

/-! ### The parts of a smooth morphism of constant relative dimension -/

section Parts

variable {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX]

/-- For a smooth morphism of relative dimension `d`, the part of dimension `d` is everything
(an alias of `Stacks.WeilCohomology.dimPart_self_eq_top`). -/
alias dimPart_eq_top_of_relativeDimension := Stacks.WeilCohomology.dimPart_self_eq_top

/-- For a smooth morphism of relative dimension `d`, the inclusion of the part of dimension `d` is
an isomorphism. -/
alias isIso_dimPart_ι_of_relativeDimension := Stacks.WeilCohomology.isIso_dimPart_self_ι

end Parts

/-- A section `g` of a separated morphism `f` is proper: `g ≫ f = 𝟙` is proper and `f` is
separated. -/
theorem isProper_of_comp_eq_id {X Y : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ X} [IsSeparated f]
    (h : g ≫ f = 𝟙 Y) : IsProper g := by
  have : IsProper (g ≫ f) := h ▸ inferInstance
  exact IsProper.of_comp g f

/-- **Restricting a proper pushforward along an isomorphism.** For `g : Z ⟶ W` proper and an
isomorphism `w : U ⟶ W` over the base, the restriction of `g_* α` along `w` is the pushforward of
`α` along `g ≫ w⁻¹`. -/
theorem chowGroupRestrict_properChowPushforward_of_isIso (C : ChowSituation.{u})
    {Z W U : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (g : Z ⟶ W) [IsProper g]
    (hg : g ≫ sW = sZ) (w : U ⟶ W) [IsIso w] (hw : w ≫ sW = sU) (n : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sZ sW g hg n)
    (α : chowGroup C sZ n) :
    chowGroupRestrict C sW sU w hw n (properChowPushforward C sZ sW g hg n hfac α) =
      properChowPushforward C sZ sU (g ≫ inv w)
        (by rw [← hw, Category.assoc, IsIso.inv_hom_id_assoc, hg]) n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ n) α := by
  rw [chowGroupRestrict_of_isIso C sW sU n w hw]
  exact DFunLike.congr_fun (properChowPushforward_comp C sZ sW sU g (inv w) hg
    (by rw [IsIso.inv_comp_eq, hw]) n hfac
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ n)) α

variable {k : Type u} [Field k]

/-- **The class of a closed subscheme of pure dimension is the pushforward of its fundamental
class.** For a closed immersion `f : X ⟶ Y` of schemes smooth over `k`, `X` of constant dimension
`a`, the class `[X] ∈ CH^c(Y)` of the closed subscheme `X`
(`Stacks.WeilCohomology.closedSubschemeClass`) is `f_*[X]` read in codimension `c`
(`Stacks.WeilCohomology.chowCodimPushforward` of `Stacks.WeilCohomology.chowCodimFundamental`).
For the diagonal `δ : X ⟶ X ×_k X` this identifies the class `[Δ]` of the base
(`Stacks.WeilCohomology.SmoothProjectiveScheme.diagonalClass`) with `δ_*[X]`. -/
theorem closedSubschemeClass_eq_chowCodimPushforward {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S)
    [Smooth sY] (f : X ⟶ Y) [IsClosedImmersion f] (hf : f ≫ sY = sX) {a : ℕ}
    (hX : RelativeDimension sX a) (c : ℕ) :
    Stacks.WeilCohomology.closedSubschemeClass sY f c =
      chowCodimPushforward k sX sY f hf 0 c (chowCodimFundamental k sX) := by
  subst hf
  funext d
  rw [Stacks.WeilCohomology.closedSubschemeClass_apply]
  simp only [chowCodimPushforward, Stacks.WeilCohomology.chowCodimPart]
  rw [chowCodimTotal_chowCodimFundamental _ hX,
    Stacks.WeilCohomology.properChowPushforward_fundamentalChowClass_eq_mk]
  rfl

/-- **`(x × id)^![Δ] = [x]` on the piece `X_{d,2d}`.** In the situation of
`Stacks.WeilDeRham.codimensionGysin_diagonal_eq_point`, the Gysin map of `j = x × id` on the piece
`X_{d,2d} = X_d ∩ j⁻¹(P_{2d})` carries the part of `[Δ]` on `P_{2d}` to the restriction of `[x]`.

By Stacks 0B76 (1) the Gysin map commutes with the pushforward along `Δ`, and by Stacks 0FF7 at the
test scheme `Δ : X ⟶ P` it carries `[X]_d` to `[Z]_0` for `Z = X ×_{j, P, Δ} X`, which is
`Spec k` mapping to `X` by `x`. -/
theorem dimPartPieceGysin_diagonal_eq_point {X P : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] {d : ℕ}
    (hd : RelativeDimension sX d) (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ sX = 𝟙 _)
    {p q : P ⟶ X} (hP : IsPullback p q sX sX) {δ j : X ⟶ P} (hδp : δ ≫ p = 𝟙 X)
    (hδq : δ ≫ q = 𝟙 X) (hjp : j ≫ p = sX ≫ x) (hjq : j ≫ q = 𝟙 X) :
    haveI : Smooth p := MorphismProperty.of_isPullback hP.flip ‹Smooth sX›
    haveI : IsSeparated p := MorphismProperty.of_isPullback hP.flip ‹IsSeparated sX›
    haveI : IsProper δ := isProper_of_comp_eq_id hδp
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI : LocallyOfFiniteType j := by
      have : LocallyOfFiniteType (j ≫ q) := by rw [hjq]; infer_instance
      exact locallyOfFiniteType_of_comp j q
    dimPartPieceGysin sX (p ≫ sX)
        (show j ≫ p ≫ sX = sX by rw [← Category.assoc, hjp, Category.assoc, hx, Category.comp_id])
        d (d + d) (d : ℤ)
        (chowCodimPushforward k sX (p ≫ sX) δ
          (by rw [← Category.assoc, hδp, Category.id_comp]) 0 d (chowCodimFundamental k sX)
          (d + d)) =
      chowGroupRestrict (fieldChowSituation k) (partBase sX d)
        (dimPartPieceBase sX (p ≫ sX) j d (d + d)) (dimPartPiece sX (p ≫ sX) j d (d + d)).ι rfl
        ((d : ℤ) - d)
        (chowCodimPushforward k (𝟙 _) sX x hx 0 d (chowCodimFundamental k (𝟙 _)) d) := by
  have : Smooth p := MorphismProperty.of_isPullback hP.flip ‹Smooth sX›
  have : IsSeparated p := MorphismProperty.of_isPullback hP.flip ‹IsSeparated sX›
  have : IsProper δ := isProper_of_comp_eq_id hδp
  have : IsProper x := isProper_of_comp_eq_id hx
  have : LocallyOfFiniteType j := by
    have : LocallyOfFiniteType (j ≫ q) := by rw [hjq]; infer_instance
    exact locallyOfFiniteType_of_comp j q
  have hj : j ≫ p ≫ sX = sX := by rw [← Category.assoc, hjp, Category.assoc, hx, Category.comp_id]
  have hδ : δ ≫ p ≫ sX = sX := by rw [← Category.assoc, hδp, Category.id_comp]
  -- `P` has dimension `2d`, so its part `P_{2d}` is everything
  have hPd : RelativeDimension (p ≫ sX) (d + d) :=
    RelativeDimension.comp_of_flat p sX (RelativeDimension.of_isPullback hP.flip hd) hd
  have : IsIso (dimPart (p ≫ sX) (d + d)).ι := isIso_dimPart_ι_of_relativeDimension _ hPd
  obtain ⟨δU, hδU⟩ : ∃ δU : X ⟶ (dimPart (p ≫ sX) (d + d)).toScheme,
      δU ≫ (dimPart (p ≫ sX) (d + d)).ι = δ :=
    ⟨δ ≫ inv (dimPart (p ≫ sX) (d + d)).ι, by simp⟩
  have : IsProper δU := by
    have : IsProper (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) := by rw [hδU]; infer_instance
    exact IsProper.of_comp δU (dimPart (p ≫ sX) (d + d)).ι
  have hm : ((d + d : ℕ) : ℤ) - (d : ℤ) = d := by push_cast; ring
  have hdimX := Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension sX hd
  -- the part of `[Δ]` on `P_{2d}` is `(δ : X ⟶ P_{2d})_* [X]_d`
  have h1 : chowCodimPushforward k sX (p ≫ sX) δ hδ 0 d (chowCodimFundamental k sX) (d + d) =
      properChowPushforward (fieldChowSituation k)
        ((δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ p ≫ sX)
        ((dimPart (p ≫ sX) (d + d)).ι ≫ p ≫ sX) δU (by simp [Category.assoc]) _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k)
          ((δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ p ≫ sX) (((d + d : ℕ) : ℤ) - (d : ℤ))) := by
    show chowGroupRestrict (fieldChowSituation k) (p ≫ sX)
        ((dimPart (p ≫ sX) (d + d)).ι ≫ p ≫ sX) (dimPart (p ≫ sX) (d + d)).ι rfl _
        (properChowPushforward (fieldChowSituation k) sX (p ≫ sX) δ hδ _
          (properPushforwardDescends _ _ _ _ _ _)
          (chowCodimTotal k sX 0 _ (chowCodimFundamental k sX))) = _
    rw [chowCodimTotal_chowCodimFundamental sX hd,
      chowGroupRestrict_properChowPushforward (fieldChowSituation k) sX (p ≫ sX)
        ((δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ p ≫ sX)
        ((dimPart (p ≫ sX) (d + d)).ι ≫ p ≫ sX) δ hδ (𝟙 X)
        (by rw [hδU, Category.id_comp, hδ]) (dimPart (p ≫ sX) (d + d)).ι rfl δU
        (by simp [Category.assoc]) (IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hδU]⟩)
        _ _ (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _),
      chowGroupRestrict_fundamentalChowClass (fieldChowSituation k) sX _ (𝟙 X) _ _
        (by rw [hm]; exact hdimX)]
  rw [h1]
  -- the Gysin map on the piece is the cap with `j^!` at the test scheme `P_{2d} ⟶ P`, restricted
  show chowGroupDegreeEquiv _ _ _
    ((dimPartPieceGysinClass sX (p ≫ sX) hj d (d + d)).capTargetHom _ _ _ _ _ _ _ _ _) = _
  rw [chowGroupDegreeEquiv_eq_iff_heq, BivariantClass.capTargetHom_apply]
  refine (dimPartPieceGysinClass_capTarget_heq sX (p ≫ sX) hj d (d + d) _ _).trans ?_
  -- Stacks 0B76 (1): `j^!` commutes with the pushforward along `δ`
  rw [(smoothGysinClass (fieldChowSituation k) sX (p ≫ sX) hj _).cap_properPushforward
    (dimPart (p ≫ sX) (d + d)).ι δU (bivariantBaseChangeMap j (dimPart (p ≫ sX) (d + d)).ι δU)
    (isPullback_bivariantBaseChangeMap j (dimPart (p ≫ sX) (d + d)).ι δU)
    (by simp [bivariantBaseChangeMap]) _ _]
  -- the scheme-theoretic intersection `Z = X ×_{j, P, δ} X` is the point `x`
  have hxjδ : x ≫ j = x ≫ δ :=
    hP.hom_ext (by simp [hjp, hδp, reassoc_of% hx]) (by simp [hjq, hδq])
  have hab : pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ j =
      pullback.snd j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ δ :=
    pullback.condition.trans
      (congrArg (fun t ↦ pullback.snd j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ t) hδU)
  have hc : ∀ r : P ⟶ X, pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ j ≫ r =
      pullback.snd j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ δ ≫ r := fun r ↦ by
    rw [← Category.assoc, hab, Category.assoc]
  have hb : pullback.snd j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) =
      pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX ≫ x := by
    simpa [hδp, hjp] using (hc p).symm
  have hab' : pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) =
      pullback.snd j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) := by
    simpa [hδq, hjq] using hc q
  have ha : pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX ≫ x =
      pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) := by
    rw [← hb, hab']
  have hψφ : (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) ≫
      pullback.lift x x (by rw [hδU, hxjδ]) = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp, ha]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      rw [ha, hab']
  have hφψ : pullback.lift x x (by rw [hδU, hxjδ]) ≫
      (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) = 𝟙 _ := by
    rw [pullback.lift_fst_assoc, hx]
  have : IsIso (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) := ⟨_, hψφ, hφψ⟩
  -- Stacks 0FF7 at the test scheme `δ : X ⟶ P`: `j^![X]_d = [Z]_0`
  have hrelT : RelativeDimension ((δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ p ≫ sX) d := by
    have key : ∀ (s : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType s], s = sX →
        RelativeDimension s d := by
      rintro s _ rfl
      exact hd
    exact key _ (by rw [hδU, hδ])
  have hdim : ∀ ξ : (pullback j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction
          (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) ξ ≤
        ((d + d : ℕ) : ℤ) - (d : ℤ) - (((d + d : ℕ) : ℤ) - (d : ℤ)) := by
    intro ξ
    have h := relativeDimension_comp_isOpenImmersion (fieldChowSituation k).dimensionFunction
      (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) (𝟙 _) ξ
    rw [Category.comp_id] at h
    rw [h, sub_self]
    exact (relativeDimension_le_of_schemeDeltaDimension_le' (fieldChowSituation k) (𝟙 _)
      (Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension (𝟙 _)
        (relativeDimension_of_isOpenImmersion (𝟙 _))) _).trans (by simp)
  rw [cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass
    (fieldChowSituation k) sX (p ≫ sX) hj
    (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth j (p ≫ sX) sX hj)
    (GysinMapExists.of_smooth_source j (p ≫ sX) sX hj) (δU ≫ (dimPart (p ≫ sX) (d + d)).ι)
    (n := d) (m := ((d + d : ℕ) : ℤ)) (m' := ((d + d : ℕ) : ℤ) - (d : ℤ))
    (fun W ↦ Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k sX
      d hd W)
    (fun W ↦ Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
      (p ≫ sX) (d + d) hPd W)
    (fun W ↦ (Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k _
      d hrelT W).trans hm.symm)
    hdim (fun ξ _ ↦ Stacks.WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth k sX _)]
  -- the piece `X_{d,2d}` is all of `X`, and all of `X ×_P P_{2d}`
  have : IsIso (dimPartPieceToPreimage sX (p ≫ sX) j d (d + d)) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι_morphismRestrict, dimPart_eq_top_of_relativeDimension sX hd]
    simp
  have : IsIso (dimPartPieceToPullback sX (p ≫ sX) j d (d + d)) := by
    dsimp only [dimPartPieceToPullback]
    infer_instance
  have : IsIso (dimPart sX d).ι := isIso_dimPart_ι_of_relativeDimension sX hd
  have : IsIso (dimPartPiece sX (p ≫ sX) j d (d + d)).ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι]
    show (dimPart sX d).ι ⁻¹ᵁ (j ⁻¹ᵁ dimPart (p ≫ sX) (d + d)) = ⊤
    rw [dimPart_eq_top_of_relativeDimension (p ≫ sX) hPd]
    simp
  rw [chowGroupRestrict_properChowPushforward_of_isIso (fieldChowSituation k) _ _ _ _ _
    (dimPartPieceToPullback sX (p ≫ sX) j d (d + d))]
  -- the class of the point is `x_*[Spec k]_0`
  have h2 : chowCodimPushforward k (𝟙 _) sX x hx 0 d (chowCodimFundamental k (𝟙 _)) d =
      chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl
        ((d : ℤ) - d)
        (properChowPushforward (fieldChowSituation k) (𝟙 _) sX x hx ((d : ℤ) - d)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) ((d : ℤ) - d))) := by
    show chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl _
      (properChowPushforward (fieldChowSituation k) (𝟙 _) sX x hx _
        (properPushforwardDescends _ _ _ _ _ _)
        (chowCodimTotal k (𝟙 _) 0 _ (chowCodimFundamental k (𝟙 _)))) = _
    rw [chowCodimTotal_chowCodimFundamental (𝟙 _) (relativeDimension_of_isOpenImmersion (𝟙 _))]
  rw [h2, chowGroupRestrict_comp,
    chowGroupRestrict_properChowPushforward_of_isIso (fieldChowSituation k) _ _ _ _ _
      ((dimPartPiece sX (p ≫ sX) j d (d + d)).ι ≫ (dimPart sX d).ι)]
  -- `Z ⟶ X_{d,2d}` is `x` through `Z ≅ Spec k`
  have hmor : bivariantBaseChangeMap j (dimPart (p ≫ sX) (d + d)).ι δU ≫
        inv (dimPartPieceToPullback sX (p ≫ sX) j d (d + d)) =
      (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) ≫
        x ≫ inv ((dimPartPiece sX (p ≫ sX) j d (d + d)).ι ≫ (dimPart sX d).ι) := by
    rw [IsIso.comp_inv_eq]
    apply pullback.hom_ext
    · simp [bivariantBaseChangeMap, ha]
    · rw [← cancel_mono (dimPart (p ≫ sX) (d + d)).ι]
      simp only [Category.assoc, ← pullback.condition, dimPartPieceToPullback_fst_assoc]
      simp [bivariantBaseChangeMap, reassoc_of% ha]
  have hxπ : (x ≫ inv ((dimPartPiece sX (p ≫ sX) j d (d + d)).ι ≫ (dimPart sX d).ι)) ≫
      dimPartPieceBase sX (p ≫ sX) j d (d + d) = 𝟙 _ := by
    simp [hx]
  rw [properChowPushforward_congr_hom (fieldChowSituation k) _ _ hmor _
      (by rw [Category.assoc, hxπ, Category.comp_id]) _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _),
    ← DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k)
      (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) (𝟙 _)
      (dimPartPieceBase sX (p ≫ sX) j d (d + d))
      (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX)
      (x ≫ inv ((dimPartPiece sX (p ≫ sX) j d (d + d)).ι ≫ (dimPart sX d).ι))
      (Category.comp_id _) hxπ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso _ _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)),
    AddMonoidHom.comp_apply,
    properChowPushforward_eq_chowPushforwardOfIso (fieldChowSituation k)
      (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX) (𝟙 _)
      (pullback.fst j (δU ≫ (dimPart (p ≫ sX) (d + d)).ι) ≫ sX),
    chowPushforwardOfIso_fundamentalChowClass]
  -- both sides are `x_*[Spec k]_0`, in degrees written differently
  have key : ∀ a b : ℤ, a = b →
      properChowPushforward (fieldChowSituation k) (𝟙 _)
          (dimPartPieceBase sX (p ≫ sX) j d (d + d))
          (x ≫ inv ((dimPartPiece sX (p ≫ sX) j d (d + d)).ι ≫ (dimPart sX d).ι)) hxπ a
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) a) ≍
        properChowPushforward (fieldChowSituation k) (𝟙 _)
          (dimPartPieceBase sX (p ≫ sX) j d (d + d))
          (x ≫ inv ((dimPartPiece sX (p ≫ sX) j d (d + d)).ι ≫ (dimPart sX d).ι)) hxπ b
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (𝟙 _) b) := by
    rintro a _ rfl
    rfl
  exact key _ _ (by ring)

/-- **The Gysin pullback of the diagonal along `x × id` is the class of the point**, the
Chow-theoretic step of the proof of Axiom (A6) in Stacks 0FWD. Let `X` be smooth and separated over
a field `k`, of constant dimension `d`, let `x : Spec k ⟶ X` be a `k`-rational point, and let
`P = X ×_k X` with projections `p`, `q`, diagonal `δ` and `j = x × id : X ⟶ P`
(`p ∘ j = x ∘ s_X`, `q ∘ j = id`). Then

  `j^! [Δ] = [x]`   in `CH^d(X)`,

for `j^!` the Gysin map of Stacks 0FF3 (`Stacks.Chow.codimensionGysin`), `[Δ] = δ_*[X]` and
`[x] = x_*[Spec k]`, read in codimension `d`.

The square `x, x, j, Δ` is cartesian and transversal: `X ×_{j, P, Δ} X` is the reduced point, of
the expected dimension `0`, so the Gysin pullback is the class of the intersection (Stacks 0FF7).
Every piece of `X` but `X_{d,2d}` is empty, and on `X_{d,2d}` this is
`Stacks.WeilDeRham.dimPartPieceGysin_diagonal_eq_point`. -/
theorem codimensionGysin_diagonal_eq_point {X P : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] [IsSeparated sX] {d : ℕ}
    (hd : RelativeDimension sX d) (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ sX = 𝟙 _)
    {p q : P ⟶ X} (hP : IsPullback p q sX sX) {δ j : X ⟶ P} (hδp : δ ≫ p = 𝟙 X)
    (hδq : δ ≫ q = 𝟙 X) (hjp : j ≫ p = sX ≫ x) (hjq : j ≫ q = 𝟙 X) :
    haveI : Smooth p := MorphismProperty.of_isPullback hP.flip ‹Smooth sX›
    haveI : IsSeparated p := MorphismProperty.of_isPullback hP.flip ‹IsSeparated sX›
    haveI : IsProper δ := isProper_of_comp_eq_id hδp
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI : LocallyOfFiniteType j := by
      have : LocallyOfFiniteType (j ≫ q) := by rw [hjq]; infer_instance
      exact locallyOfFiniteType_of_comp j q
    codimensionGysin sX (p ≫ sX)
        (show j ≫ p ≫ sX = sX by rw [← Category.assoc, hjp, Category.assoc, hx, Category.comp_id])
        (d : ℤ)
        (chowCodimPushforward k sX (p ≫ sX) δ
          (by rw [← Category.assoc, hδp, Category.id_comp]) 0 d (chowCodimFundamental k sX)) =
      chowCodimPushforward k (𝟙 _) sX x hx 0 d (chowCodimFundamental k (𝟙 _)) := by
  have : Smooth p := MorphismProperty.of_isPullback hP.flip ‹Smooth sX›
  have : IsSeparated p := MorphismProperty.of_isPullback hP.flip ‹IsSeparated sX›
  have : IsProper δ := isProper_of_comp_eq_id hδp
  have : IsProper x := isProper_of_comp_eq_id hx
  have : LocallyOfFiniteType j := by
    have : LocallyOfFiniteType (j ≫ q) := by rw [hjq]; infer_instance
    exact locallyOfFiniteType_of_comp j q
  have hPd : RelativeDimension (p ≫ sX) (d + d) :=
    RelativeDimension.comp_of_flat p sX (RelativeDimension.of_isPullback hP.flip hd) hd
  funext e
  -- the parts `X_e`, `e ≠ d`, are empty
  by_cases he : e = d
  swap
  · have := isEmpty_dimPart_of_ne sX hd he
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _
  subst he
  apply (chowGroupDimPartPieceEquiv sX (p ≫ sX) (f := j) e ((e : ℤ) - (e : ℕ))).injective
  funext ⟨e'⟩
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  -- the pieces `X_{d,e'}`, `e' ≠ 2d`, are empty
  by_cases he' : e' = e + e
  swap
  · have : IsEmpty (dimPartPiece sX (p ≫ sX) j e e').toScheme :=
      ⟨fun y ↦ he' (eq_of_mem_dimPart (p ≫ sX) hPd y.2)⟩
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _
  subst he'
  exact dimPartPieceGysin_diagonal_eq_point sX hd x hx hP hδp hδq hjp hjq

end Stacks.WeilDeRham
