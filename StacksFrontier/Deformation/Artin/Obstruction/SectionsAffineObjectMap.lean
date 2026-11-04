module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsAffineObjectGlue
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsObstructionMap

/-!
# The obstruction modules and their map, indexed by affine objects

`Deformation.Artin.SectionsSheaf.obstructionLinearEndofunctor` and
`Deformation.Artin.SectionsSheaf.obstructionMap` are the data of clauses (1) and (2) of
Stacks 07YG for the example of Stacks 07YH, indexed by a morphism `t : Spec A → S` and a ring
map `ψ : A → A₁`. The fields `obstruction` and `map` of `Deformation.Artin.ObstructionTheory`
ask for them indexed by a `Deformation.Artin.AffineObject` and a morphism of such. This file
re-indexes them, which is what makes `map_id`, `map_comp` and `map_local` statable at all.

## Main definitions

* `Deformation.Artin.SectionsSheaf.obstructionMapOf` — the map of obstruction modules with the
  base of its target carried as a *variable* identified with `Spec ψ ≫ t` by an equality
  hypothesis.
* `Deformation.Artin.SectionsSheaf.affineObstruction` — **clause (1) at an affine object**:
  the `A`-linear endofunctor `M ↦ H¹(W_A, 𝓕_A ⊗_A M)` of `Mod_A` at `P`, in the indexing the
  `obstruction` field asks for.
* `Deformation.Artin.SectionsSheaf.affineObstructionMap` — **clause (2) at a morphism of affine
  objects**: the induced `H¹(W_A, 𝓕_A ⊗_A M) ⟶ H¹(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N)`, with the target
  carrying its `A`-structure by restriction of scalars, in the indexing the `map` field asks
  for.

## Main results

* `Deformation.Artin.SectionsSheaf.botProj_eq_topProj` and its companions — the `bot` half of
  the base-change data of Stacks 07YH is the `top` half at the composite base `Spec ψ ≫ t`, on
  the nose. These are what let the re-indexing be a transport of a *variable* rather than a
  transport along a fixed equality.
* `Deformation.Artin.SectionsSheaf.obstructionMapOf_rfl` — the re-indexed map at the
  reflexivity witness is the original map.

## Implementation notes

`botScheme`, `botProj` and `botSheaf` are `topScheme`, `topProj` and `topSheaf` at the base
`Spec ψ ≫ t`, by `rfl` — all six are `pullback`s or `Scheme.Modules.pullback`s of the structure
morphism of `quotOver ψ t`, which is `Over.mk (Spec ψ ≫ t)`. So the *only* difference between
the map `obstructionMap` constructs and the map clause (2) asks for is the morphism
`Spec ψ ≫ t` against the structure morphism of the target object, and those are equal by
`Deformation.Artin.SiteAlgebra.Hom.specMap_comp_toScheme`.

`obstructionMapOf` therefore takes the base of its target as a variable with that equality as a
hypothesis and eliminates it by `match`, rather than conjugating the original map by an
`eqToHom`. At a morphism of affine objects the hypothesis is discharged by
`specMap_comp_toScheme`, and `affineObstructionMap`'s type is literally the type of the `map`
field of `Deformation.Artin.ObstructionTheory` read through `affineObstruction` — up to the
packaging of a morphism of `ModuleCat` as a `LinearMap` for the `Module.compHom` structure,
which the field states its conclusion in.

**`map_id` and `map_local` of the coherence are proved**, in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`: there the `match` of
`obstructionMapOf` at an identity morphism of affine objects is evaluated
(`..obstructionMapOf_eq_comp_eqToHom`) and cancelled against the transport the base-change
immersion contributes. `map_comp` is not. See the "what is not done" of
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMap.lean`.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Deformation.Artin.SectionsSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The `bot` half of the base-change data is the `top` half at the composite base -/

section Bridge

variable {S : Scheme.{u}} {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) (t : Spec A ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- `W_{A₁}` is `W_T` at the base `T = Spec A₁ → Spec A → S`. -/
theorem botScheme_eq_topScheme : botScheme ψ t q = topScheme (Spec.map ψ ≫ t) q := rfl

/-- The structure morphism `W_{A₁} → Spec A₁` is the one of `W_T` at `T = Spec A₁ → Spec A → S`.
This is the identification that makes the re-indexing of the map of obstruction modules a
transport of a variable. -/
theorem botProj_eq_topProj : botProj ψ t q = topProj (Spec.map ψ ≫ t) q := rfl

/-- `𝓕_{A₁}` is `𝓕_T` at the base `T = Spec A₁ → Spec A → S`. -/
theorem botSheaf_eq_topSheaf : botSheaf ψ t q 𝓕 = topSheaf (Spec.map ψ ≫ t) q 𝓕 := rfl

end Bridge

/-! ### The map of obstruction modules with the base of its target as a variable -/

section Reindex

variable {S : Scheme.{u}} {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) (t : Spec A ⟶ S)
  (t₁ : Spec A₁ ⟶ S) {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **The map of obstruction modules of clause (2), with the base of its target as a variable.**
For a morphism `t₁ : Spec A₁ → S` identified with `Spec ψ ≫ t`, this is
`Deformation.Artin.SectionsSheaf.obstructionMap` with its target read over `t₁`:
```
Hⁿ(W_A, 𝓕_A ⊗_A M) ⟶ Hⁿ(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N),
```
both sides in the `top` spelling of the base-change data, the target carrying its `A`-module
structure by restriction of scalars along `ψ`.

The equality is eliminated by `match`, so nothing is conjugated by an `eqToHom`; at the
reflexivity witness the map is `obstructionMap` itself, by `obstructionMapOf_rfl`. -/
def obstructionMapOf (e : Spec.map ψ ≫ t = t₁) (n : ℕ) {M : ModuleCat.{u} A}
    {N : ModuleCat.{u} A₁} (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    ((cohomologyDeltaFunctor (topProj t q)).functor n).obj
        ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj M) ⟶
      (ModuleCat.restrictScalars ψ.hom).obj
        (((cohomologyDeltaFunctor (topProj t₁ q)).functor n).obj
          ((tensorSheafFunctor (topProj t₁ q) (topSheaf t₁ q 𝓕)).obj N)) :=
  match t₁, e with
  | _, rfl => obstructionMap ψ t q 𝓕 n α

/-- At its reflexivity witness the re-indexed map of obstruction modules is the original one. -/
theorem obstructionMapOf_rfl (n : ℕ) {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N) :
    obstructionMapOf ψ t (Spec.map ψ ≫ t) q 𝓕 rfl n α = obstructionMap ψ t q 𝓕 n α :=
  rfl

end Reindex

/-! ### Clauses (1) and (2) in the indexing the structure's fields ask for -/

section AffineObjectMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : Type v}
  [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **Clause (1) of Stacks 07YG at an affine object**, for the example of Stacks 07YH: the
`A`-linear endofunctor `M ↦ H¹(W_A, 𝓕_A ⊗_A M)` of `Mod_A` attached to an object `x` over
`Spec A`. This is `obstructionLinearEndofunctor` at the base of the affine object, which is the
indexing the `obstruction` field of `Deformation.Artin.ObstructionTheory` asks for. -/
def affineObstruction (P : AffineObject B S hS p) :
    Deformation.Artin.LinearEndofunctor P.alg.carrier :=
  obstructionLinearEndofunctor (topProj P.alg.toScheme q) (topSheaf P.alg.toScheme q 𝓕)

/-- **Clause (2) of Stacks 07YG at a morphism of affine objects**, for the example of Stacks
07YH: a morphism `(x, A) → (y, A₁)` and a map `A₁ ⊗_A M → N` induce
```
H¹(W_A, 𝓕_A ⊗_A M) ⟶ H¹(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N),
```
the target carrying its `A`-module structure by restriction of scalars along the ring map, as
clause (2) requires. This is `obstructionMap` re-indexed along
`Deformation.Artin.SiteAlgebra.Hom.specMap_comp_toScheme`, which identifies the base of the
target object with the base change of the base of the source.

`map_id` and `map_local` are proved for this map, in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMapId.lean`
(`Deformation.Artin.SectionsSheaf.affineObstructionMap_id` and `..affineObstructionMap_id_eq`,
with their element-wise forms); `map_comp` is not, and what it waits on is recorded in the "what
is not done" of `StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMap.lean`. -/
def affineObstructionMap {P Q : AffineObject B S hS p} (h : AffineObject.Hom P Q)
    {M : ModuleCat.{u} (CommRingCat.of P.alg.carrier)}
    {N : ModuleCat.{u} (CommRingCat.of Q.alg.carrier)}
    (α : (ModuleCat.extendScalars h.alg.ringMap).obj M ⟶ N) :
    (affineObstruction q 𝓕 P).functor.obj M ⟶
      (ModuleCat.restrictScalars h.alg.ringMap).obj ((affineObstruction q 𝓕 Q).functor.obj N) :=
  obstructionMapOf (CommRingCat.ofHom h.alg.ringMap) P.alg.toScheme Q.alg.toScheme q 𝓕
    h.alg.specMap_comp_toScheme 1 α

end AffineObjectMap

end Deformation.Artin.SectionsSheaf

end
