module

public import StacksFrontier.AlgebraicGeometry.RelativeCech.Basic

/-!
# The coefficient presheaf of [Stacks, Tag 01XL] under a change of the ambient scheme

Let `k : X' ⟶ X` and `c : X ⟶ S` be morphisms of schemes and let `ℱ` be a quasi-coherent
`𝒪_X`-module.  The coefficient presheaf of [Stacks, Tag 01XL] attached to `c` lives on
`Over X`; restricting it along `Over.map k : Over X' ⥤ Over X` gives a presheaf on `Over X'`
whose value at `B`, with structure morphism `b`, is `((b ≫ k) ≫ c)_* (b ≫ k)^*ℱ`.  That is the
value at `B` of the coefficient presheaf attached to `k ≫ c` and the module `k^*ℱ`, because
`(b ≫ k)^*ℱ ≅ b^* k^*ℱ`.  [Stacks, Tag 01XM] needs that identification for `k = g'`, the base
change of `g : S' ⟶ S`, to compare `g^* Č ⁼(𝒰, f, ℱ)` with the relative Čech complex of the
inverse-image cover.

This file proves the *naturality* input for that identification:  the compatibility of the
canonical restriction map `Stacks.AlgebraicGeometry.RelativeCech.relativeUnit` with composing
the structure morphism of an object of `Over X'` with `k`.  All of its statements are about
`relativeUnit`, `pullbackComp` and the unit of `u^* ⊣ u_*` only, with the schemes and morphisms
as variables.

## Main results

* `pullbackComp_hom_comp_inv`: the associativity coherence of the pullback pseudofunctor, in the
  shape that moves the comparison for `b ≫ k` across the comparison for `u ≫ b`.
* `homEquiv_pullbackComp_comp`: the same identity transposed under `u^* ⊣ u_*`.
* `pushforward_homEquiv_pullbackComp_comp`: that identity pushed forward along `b ≫ k`.
* `relativeUnit_comp_pullbackComp`: **the compatibility of the restriction map with composing
  the structure morphism with `k`.**

## Implementation notes

The two bracketings `u ≫ (b ≫ k)` and `(u ≫ b) ≫ k` of a triple composite are definitionally
equal but not syntactically so, and `pushforward` of a composite unfolds to a composite of
pushforwards only at default transparency.  Every statement here is therefore written at one
fixed bracketing and carries the crossing as an explicit `eqToHom` argument the caller supplies
by `rfl`;  and the proofs compose `congrArg`s in term mode rather than rewriting the goal,
because `rewrite` re-checks the goal at `implicit` transparency and rejects exactly these
crossings.  Routing them through `rw` instead costs more than the heartbeat ceiling.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 01XM](https://stacks.math.columbia.edu/tag/01XM)
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCech

variable {W Y X X' S : Scheme.{u}}

/-! ### The associativity coherence in the shape the restriction maps need -/

/-- **The associativity coherence of the pullback pseudofunctor**, in the shape needed to move
the comparison for `b ≫ k` across the comparison for `u ≫ b`. -/
public theorem pullbackComp_hom_comp_inv (u : W ⟶ Y) (b : Y ⟶ X') (k : X' ⟶ X)
    (M : X.Modules) (e : (pullback ((u ≫ b) ≫ k)).obj M = (pullback (u ≫ b ≫ k)).obj M) :
    (pullbackComp u (b ≫ k)).hom.app M ≫ eqToHom e.symm ≫
        (pullbackComp (u ≫ b) k).inv.app M =
      (pullback u).map ((pullbackComp b k).inv.app M) ≫
        (pullbackComp u b).hom.app ((pullback k).obj M) := by
  have h := pullbackComp_assoc_app u b k M e
  have hA : (pullback u).map ((pullbackComp b k).inv.app M) ≫
      (pullback u).map ((pullbackComp b k).hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hD : (pullbackComp (u ≫ b) k).hom.app M ≫ eqToHom e ≫
      eqToHom e.symm ≫ (pullbackComp (u ≫ b) k).inv.app M = 𝟙 _ := by
    rw [← Category.assoc (eqToHom e), eqToHom_trans, eqToHom_refl,
      Category.id_comp, Iso.hom_inv_id_app]
  have step : (pullback u).map ((pullbackComp b k).inv.app M) ≫
      (pullbackComp u b).hom.app ((pullback k).obj M) =
        (pullback u).map ((pullbackComp b k).inv.app M) ≫
          ((pullback u).map ((pullbackComp b k).hom.app M) ≫
            (pullbackComp u (b ≫ k)).hom.app M) ≫
            eqToHom e.symm ≫ (pullbackComp (u ≫ b) k).inv.app M := by
    rw [h]
    simp only [Category.assoc]
    rw [hD]
    simp only [Functor.comp_obj, Category.comp_id]
  rw [step]
  simp only [Category.assoc]
  rw [← Category.assoc ((pullback u).map ((pullbackComp b k).inv.app M))
    ((pullback u).map ((pullbackComp b k).hom.app M)), hA, Category.id_comp]

/-! ### The restriction maps under a change of the ambient scheme -/

/-- **The canonical restriction map of the coefficient system is compatible with composing the
structure morphism with a further morphism `k`.**  Both sides are maps
`(b ≫ k)_* (b ≫ k)^*M ⟶ k_*(u ≫ b)_* (u ≫ b)^* k^* M`:  on the left one restricts along `u`
over `X` and then compares `((u ≫ b) ≫ k)^*` with `(u ≫ b)^*k^*`, on the right one compares
`(b ≫ k)^*` with `b^*k^*` first and then restricts along `u` over `X'`.

Here `e` identifies the pullbacks along the two bracketings `(u ≫ b) ≫ k` and `u ≫ b ≫ k`. -/
public theorem homEquiv_pullbackComp_comp (u : W ⟶ Y) (b : Y ⟶ X') (k : X' ⟶ X)
    (M : X.Modules) (e : (pullback ((u ≫ b) ≫ k)).obj M = (pullback (u ≫ b ≫ k)).obj M) :
    (pullbackPushforwardAdjunction u).homEquiv _ _ ((pullbackComp u (b ≫ k)).hom.app M) ≫
        (pushforward u).map (eqToHom e.symm ≫ (pullbackComp (u ≫ b) k).inv.app M) =
      (pullbackComp b k).inv.app M ≫ (pullbackPushforwardAdjunction u).homEquiv _ _
        ((pullbackComp u b).hom.app ((pullback k).obj M)) := by
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
    pullbackComp_hom_comp_inv u b k M e]
  rfl

/-- The identity of `homEquiv_pullbackComp_comp` pushed forward along `b ≫ k`:  both sides are
written through `(b ≫ k)_*`, so no crossing of the two bracketings of `u ≫ b ≫ k` is left
implicit. -/
public theorem pushforward_homEquiv_pullbackComp_comp (u : W ⟶ Y) (b : Y ⟶ X') (k : X' ⟶ X)
    (M : X.Modules) (e : (pullback ((u ≫ b) ≫ k)).obj M = (pullback (u ≫ b ≫ k)).obj M) :
    (pushforward (b ≫ k)).map ((pullbackPushforwardAdjunction u).homEquiv _ _
          ((pullbackComp u (b ≫ k)).hom.app M)) ≫
        (pushforward (u ≫ b ≫ k)).map (eqToHom e.symm ≫
          (pullbackComp (u ≫ b) k).inv.app M) =
      (pushforward (b ≫ k)).map ((pullbackComp b k).inv.app M ≫
        (pullbackPushforwardAdjunction u).homEquiv _ _
          ((pullbackComp u b).hom.app ((pullback k).obj M))) :=
  (congrArg (fun t ↦ (pushforward (b ≫ k)).map ((pullbackPushforwardAdjunction u).homEquiv _ _
        ((pullbackComp u (b ≫ k)).hom.app M)) ≫ t)
      (pushforward_comp_map u (b ≫ k)
        (eqToHom e.symm ≫ (pullbackComp (u ≫ b) k).inv.app M))).trans
    ((((pushforward (b ≫ k)).map_comp _ _).symm).trans
      (congrArg ((pushforward (b ≫ k)).map) (homEquiv_pullbackComp_comp u b k M e)))

/-- **The canonical restriction map of the coefficient system is compatible with composing the
structure morphism with a further morphism `k`.**  For `u : W ⟶ Y`, `b : Y ⟶ X'` and
`k : X' ⟶ X`, restricting along `u` over `X` and then comparing `((u ≫ b) ≫ k)^*` with
`(u ≫ b)^*k^*` is the comparison of `(b ≫ k)^*` with `b^*k^*` followed by the restriction along
`u` taken over `X'` — the latter written out through the unit of `u^* ⊣ u_*`.

This is the naturality input for identifying the coefficient presheaf of [Stacks, Tag 01XL]
attached to `c : X ⟶ S`, restricted along `Over.map k`, with the coefficient presheaf attached
to `k ≫ c` and the module `k^*ℱ`.

The transport `e` is the two bracketings of `u ≫ b ≫ k`; the caller supplies it by `rfl`. -/
public theorem relativeUnit_comp_pullbackComp (u : W ⟶ Y) (b : Y ⟶ X') (k : X' ⟶ X)
    (M : X.Modules) (e : (pullback ((u ≫ b) ≫ k)).obj M = (pullback (u ≫ b ≫ k)).obj M) :
    (relativeUnit u (b ≫ k)).app M ≫
        (pushforward (u ≫ b ≫ k)).map (eqToHom e.symm ≫
          (pullbackComp (u ≫ b) k).inv.app M) =
      (pushforward (b ≫ k)).map ((pullbackComp b k).inv.app M ≫
        (pullbackPushforwardAdjunction u).homEquiv _ _
          ((pullbackComp u b).hom.app ((pullback k).obj M))) :=
  (congrArg (fun t ↦ t ≫ (pushforward (u ≫ b ≫ k)).map (eqToHom e.symm ≫
      (pullbackComp (u ≫ b) k).inv.app M)) (relativeUnit_app' u (b ≫ k) M)).trans
    (pushforward_homEquiv_pullbackComp_comp u b k M e)

end Stacks.AlgebraicGeometry.RelativeCech

end
