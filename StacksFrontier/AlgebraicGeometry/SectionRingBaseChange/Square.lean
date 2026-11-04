module

public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.TailMap

/-!
# The section ring of a tail truncation along a commutative square

Let

```
Y' --q--> Y
|g'       |g
v         v
T' --h--> T
```

be a commutative square of schemes with `g`, `g'` quasi-compact and quasi-separated, let `ℳ`,
`ℳ'` be invertible modules on `Y`, `Y'` and `ε : q^*ℳ ≅ ℳ'`.  For cuts `0 < d ≤ e`, opens
`V ⊆ T`, `V' ≤ h⁻¹V` of `T'`, pulling sections back along `q` is a homomorphism of graded rings

`Γ(V, 𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n}) ⟶ Γ(V', 𝒪_{T'} ⊕ ⨁_{n ≥ d} g'_*(ℳ')^{⊗ n})`

lying over `h^♯ : Γ(T, V) ⟶ Γ(T', V')`.  These are the truncated section algebras of
[Stacks, Tag 0D4F] (3).

## Main definitions

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailAlgebra`: the tail truncation
  `𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n}`.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.squareRingHom`: the homomorphism above.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.squareRingHom_of` and
  `squareRingHom_strHom`: its value on homogeneous elements and on the image of the base.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SectionAlgebra

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

/-- **The tail truncation `𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n}`** of the direct image of the Laurent
algebra of an invertible module along a quasi-compact quasi-separated morphism. -/
abbrev tailAlgebra {Y T : Scheme.{u}} (g : Y ⟶ T) [QuasiCompact g] [QuasiSeparated g]
    (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (e : ℕ) (he : 0 < e) :
    SheafGradedAlgebra T :=
  tailSheafGradedAlgebra
    (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
      (Stacks.RelativeAmple.laurentPowers M)) e he
    (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.isCommutative_pushforwardGradedAlgebra _ _
      (Stacks.RelativeAmple.isCommutative_laurentPowers M))
    (Stacks.RelativeAmple.isQuasicoherent_pushforward_laurentPowers g M)

variable {Y' Y T' T : Scheme.{u}} (q : Y' ⟶ Y) (g : Y ⟶ T) (g' : Y' ⟶ T') (h : T' ⟶ T)
  (w : q ≫ g = g' ≫ h) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M')
  (e d : ℕ) (he : 0 < e) (hd : 0 < d) (hde : d ≤ e) (V : T.Opens) (V' : T'.Opens)
  (hV : V' ≤ h ⁻¹ᵁ V)

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
include w hV in
/-- If `V' ≤ h⁻¹V`, then `g'⁻¹V' ≤ q⁻¹(g⁻¹V)`. -/
theorem preimage_le_preimage : g' ⁻¹ᵁ V' ≤ q ⁻¹ᵁ (g ⁻¹ᵁ V) := by
  intro x hx
  have h1 : g'.base x ∈ h ⁻¹ᵁ V := hV hx
  show g.base (q.base x) ∈ V
  have h2 : g.base (q.base x) = h.base (g'.base x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, w]
  rw [h2]
  exact h1

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
include w in
/-- The two composites `Γ(T, V) ⟶ Γ(Y', g'⁻¹V')` around the square agree: `g^♯` followed by
`q^♯` equals `h^♯` followed by `g'^♯`. -/
theorem appLE_comp_eq :
    g.app V ≫ q.appLE (g ⁻¹ᵁ V) (g' ⁻¹ᵁ V') (preimage_le_preimage q g g' h w V V' hV) =
      h.appLE V V' hV ≫ g'.app V' := by
  have key : ∀ (f₁ f₂ : Y' ⟶ T) (hf : f₁ = f₂) (e₁ : g' ⁻¹ᵁ V' ≤ f₁ ⁻¹ᵁ V)
      (e₂ : g' ⁻¹ᵁ V' ≤ f₂ ⁻¹ᵁ V), f₁.appLE V (g' ⁻¹ᵁ V') e₁ = f₂.appLE V (g' ⁻¹ᵁ V') e₂ := by
    rintro f₁ f₂ rfl e₁ e₂
    rfl
  refine (Scheme.Hom.comp_appLE q g V (g' ⁻¹ᵁ V') _).symm.trans ?_
  rw [g'.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact key _ _ w _ _

/-- **The pullback of sections in every degree**, read on the pieces of the direct images. -/
def squarePieceMap (n : ℤ) :
    ((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
        (Stacks.RelativeAmple.laurentPowers M)).piece n).val.obj (op V) →+
      ((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g'
        (Stacks.RelativeAmple.laurentPowers M')).piece n).val.obj (op V') :=
  sectionPull q M M' ε n (g ⁻¹ᵁ V) (g' ⁻¹ᵁ V') (preimage_le_preimage q g g' h w V V' hV)

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- `squarePieceMap` is semilinear over `h^♯ : Γ(T, V) ⟶ Γ(T', V')`. -/
theorem squarePieceMap_smul (n : ℤ) (r : T.ringCatSheaf.obj.obj (op V))
    (x : ((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
        (Stacks.RelativeAmple.laurentPowers M)).piece n).val.obj (op V)) :
    squarePieceMap q g g' h w M M' ε V V' hV n (r • x) =
      (show T'.ringCatSheaf.obj.obj (op V') from h.appLE V V' hV r) •
        squarePieceMap q g g' h w M M' ε V V' hV n x := by
  have h1 := sectionPull_smul q M M' ε n (g ⁻¹ᵁ V) (g' ⁻¹ᵁ V')
    (preimage_le_preimage q g g' h w V V' hV) (show Y.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from
      g.app V r) x
  refine h1.trans ?_
  have h2 : q.appLE (g ⁻¹ᵁ V) (g' ⁻¹ᵁ V') (preimage_le_preimage q g g' h w V V' hV)
      (g.app V r) = g'.app V' (h.appLE V V' hV r) :=
    congrArg (fun φ : Γ(T, V) ⟶ Γ(Y', g' ⁻¹ᵁ V') => φ.hom r) (appLE_comp_eq q g g' h w V V' hV)
  exact congrArg (fun z : Y'.ringCatSheaf.obj.obj (op (g' ⁻¹ᵁ V')) => z •
    sectionPull q M M' ε n (g ⁻¹ᵁ V) (g' ⁻¹ᵁ V') (preimage_le_preimage q g g' h w V V' hV) x) h2

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] in
/-- `squarePieceMap` is multiplicative: it sends the product of sections of degrees `n` and `m`
to the product of their images. -/
theorem squarePieceMap_mul (n m : ℤ)
    (x : ((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
        (Stacks.RelativeAmple.laurentPowers M)).piece n).val.obj (op V))
    (y : ((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
        (Stacks.RelativeAmple.laurentPowers M)).piece m).val.obj (op V)) :
    squarePieceMap q g g' h w M M' ε V V' hV (n + m)
        (((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
          (Stacks.RelativeAmple.laurentPowers M)).mul n m).app (op V) x y) =
      ((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g'
          (Stacks.RelativeAmple.laurentPowers M')).mul n m).app (op V')
        (squarePieceMap q g g' h w M M' ε V V' hV n x)
        (squarePieceMap q g g' h w M M' ε V V' hV m y) :=
  sectionPull_mul q M M' ε n m (g ⁻¹ᵁ V) (g' ⁻¹ᵁ V') (preimage_le_preimage q g g' h w V V' hV) x y

/-- **The homomorphism of truncated section rings along a commutative square.** -/
def squareRingHom :
    (tailAlgebra g M e he).sectionRing V →+* (tailAlgebra g' M' d hd).sectionRing V' :=
  tailMapRingHom (hde := hde) (ρ := (h.appLE V V' hV).hom)
    (Φ := squarePieceMap q g g' h w M M' ε V V' hV)
    (fun n r x => squarePieceMap_smul q g g' h w M M' ε V V' hV n r x)
    (fun n m _ _ x y => squarePieceMap_mul q g g' h w M M' ε V V' hV n m x y) _ _ _ _

/-- On a homogeneous element of degree `n`, `squareRingHom` acts by the pullback of sections in
degree `n`. -/
theorem squareRingHom_of {n : ℕ} (a : (tailAlgebra g M e he).sectionPieces V n) :
    squareRingHom q g g' h w M M' ε e d he hd hde V V' hV (DirectSum.of _ n a) =
      DirectSum.of _ n (tailMapApp _ _ e d he hd hde V V' (h.appLE V V' hV).hom
        (squarePieceMap q g g' h w M M' ε V V' hV) (n : ℤ) a) :=
  tailMapRingHom_of _ _ _ _ _ _ a

/-- `squareRingHom` lies over `h^♯ : Γ(T, V) ⟶ Γ(T', V')`. -/
theorem squareRingHom_strHom (r : Γ(T, V)) :
    squareRingHom q g g' h w M M' ε e d he hd hde V V' hV ((tailAlgebra g M e he).strHom V r) =
      (tailAlgebra g' M' d hd).strHom V' (h.appLE V V' hV r) :=
  tailMapRingHom_strHom _ _ _ _ _ _ r

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
