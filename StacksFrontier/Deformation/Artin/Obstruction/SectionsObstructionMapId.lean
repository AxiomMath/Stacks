module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsAffineObjectMap
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsCoefficientIdentity

/-!
# `map_id` and `map_local` of clause (2) of Stacks 07YG for the example of Stacks 07YH

`Deformation.Artin.SectionsSheaf.obstructionMapGen_id_of_semilinear` is the identity case of the
map of obstruction modules in the spelling in which the base-change morphism of schemes is a
parameter: at `g = 𝟙 X` and the identity ring map that map is `Hⁿ(X, 𝓕_A ⊗_A f)`. The coherence
conditions of clause (2) are, however, conditions on
`Deformation.Artin.SectionsSheaf.affineObstructionMap`, and two transports stand between the two.
This file builds both and proves `map_id` and `map_local`.

## Main results

* `Deformation.Artin.SectionsSheaf.obstructionMapGen_eqToHom` — **the map of obstruction modules
  along a base-change morphism that is a transport.** When the target base change is *equal* to
  the source one, its two structure morphisms are the transports of the source's and the
  base-change morphism is the transport itself, the map is the identity case followed by the
  transport of the target.
* `Deformation.Artin.SectionsSheaf.obstructionMapOf_eq_comp_eqToHom` — **the re-indexed map is
  the original one followed by a transport**: `obstructionMapOf` eliminates the equality
  `Spec ψ ≫ t = t₁` by `match`, which does not reduce when neither side is a variable, and this
  is what it is instead.
* `Deformation.Artin.SectionsSheaf.obstructionMapOf_id_eq` — the two transports composed and
  cancelled: at the identity ring map the re-indexed map of obstruction modules is
  `Hⁿ(W_A, 𝓕_A ⊗_A f)`.
* `Deformation.Artin.SectionsSheaf.affineObstructionMap_id_eq` — **`map_local`**: at an identity
  morphism of affine objects the map of obstruction modules of clause (2) is the map of the
  obstruction functor of clause (1).
* `Deformation.Artin.SectionsSheaf.affineObstructionMap_id` — **`map_id`**: at an identity
  morphism of affine objects and the identity of a module it is the identity.
* `..affineObstructionMap_id_eq_apply` and `..affineObstructionMap_id_apply` — the same two,
  element-wise, which is the form the `map_local` and `map_id` fields of
  `Deformation.Artin.ObstructionTheory` state their conclusions in.

## Implementation notes

**The semilinear datum at an identity.** The `map` field of `Deformation.Artin.ObstructionTheory`
quantifies over an `A`-linear map `M → N` for the `Module.compHom` structure on `N` along the
ring map; at an identity morphism of affine objects that ring map is `RingHom.id`, so
`ModuleCat.restrictScalars` of it is the identity functor on the nose and the datum is a plain
morphism `f : M ⟶ N` of `Mod_A`. That is how `f` is taken here, and `ofSemilinear` reads it as the
map `A ⊗_A M → N` that `affineObstructionMap` asks for. For the same reason the two sides of
`affineObstructionMap_id_eq` are typeable against each other at all: the target of the map field
is `restrictScalars (𝟙 A) ∘ 𝒪(-)` where the obstruction functor's value is `𝒪(-)`.

**Why the transports are stated with the equality quantified.** `obstructionMapGen_eqToHom` takes
its three hypotheses in the form `∀ h : X₁ = X, …` rather than at a fixed proof. That is not
generality for its own sake: the equality is eliminated by `subst` in the proof, and a hypothesis
*mentioning* the proof term would have to be transported along it; with the proof quantified the
substitution is free and the hypothesis is applied at `rfl` afterwards. It also happens to be
exactly the form the three facts come in —
`Deformation.Artin.SectionsSheaf.baseChangeMap_quotHom_id` and the two projection transports
below all take the equality of fibre products as an argument.

**`restrictScalars (𝟙 A)` is kept at the top of every statement.** The inner lemmas are stated at
`ψ = 𝟙 A` syntactically and not at a variable `ψ` with `hψ : ψ = 𝟙 A`: for a variable `ψ` the two
sides of the conclusion are not typeable against each other, since
`(restrictScalars ψ).obj (Hⁿ(X, 𝓕 ⊗ N))` and `Hⁿ(X, 𝓕 ⊗ (restrictScalars ψ).obj N)` agree only
when `restrictScalars ψ` is the identity. At an identity morphism of affine objects the ring map
is `CommRingCat.ofHom (RingHom.id _)`, which *is* `𝟙` by `rfl`, so the application needs no
substitution.

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

/-! ### Transports, in the abstract -/

/-- **A morphism followed by the transport along an equality of one object with itself is the
morphism.** Stated with the two ends of the equality *the same* term, so that an application
unifies the object first and compares the two spellings of it once. -/
theorem comp_eqToHom_of_eq {C : Type*} [Category C] {P T : C} (a : P ⟶ T) (E : T = T) :
    a ≫ eqToHom E = a := by
  rw [eqToHom_refl, Category.comp_id]

/-- **Two transports in opposite directions cancel.** This is the shape the identity case of the
map of obstruction modules has: the re-indexing of `obstructionMapOf` contributes a transport
along `Spec ψ ≫ t = t₁` and the base-change morphism contributes its inverse, and what is left
between them is the identity case itself. -/
theorem eq_of_eqToHom_cancel {C : Type*} [Category C] {P T T' : C} {u : P ⟶ T} {a : P ⟶ T'}
    {b c : P ⟶ T} (E : T = T') (E₁ : T' = T)
    (h3 : u = a ≫ eqToHom E₁) (h2 : a = b ≫ eqToHom E) (h1 : b = c) : u = c := by
  rw [h3, h2, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, h1]

/-! ### The two projections of a fibre product along equal morphisms -/

section Pullback

variable {S W : Scheme.{u}} (q : W ⟶ S)

/-- The first projection of the fibre product of two equal morphisms with `q` is the second,
read through the transport. -/
theorem pullback_fst_eqToHom {Y : Scheme.{u}} {v t : Y ⟶ S} (hv : v = t)
    (h : pullback v q = pullback t q) :
    pullback.fst v q = eqToHom h ≫ pullback.fst t q := by
  subst hv
  simp

/-- The second projection of the fibre product of two equal morphisms with `q` is the second,
read through the transport. -/
theorem pullback_snd_eqToHom {Y : Scheme.{u}} {v t : Y ⟶ S} (hv : v = t)
    (h : pullback v q = pullback t q) :
    pullback.snd v q = eqToHom h ≫ pullback.snd t q := by
  subst hv
  simp

end Pullback

/-! ### The map of obstruction modules along a base-change morphism that is a transport -/

/-- **The map of obstruction modules when the base-change morphism of schemes is a transport.**
If the target base change is equal to the source one, its structure morphism to `Spec A` and its
morphism to `W` are the source's read through that equality, and the base-change morphism is the
transport itself, then the map of obstruction modules is its identity case followed by the
transport of the target.

This transport is what carries the identity case of clause (2) of Stacks 07YG back to
`Deformation.Artin.SectionsSheaf.obstructionMap`, where the base-change immersion attached to an
identity morphism of affine objects is `eqToHom` of an equality of two fibre products and not
`𝟙`, by `Deformation.Artin.SectionsSheaf.baseChangeMap_quotHom_affineHom_id`.

The equality of the target with the source appears both as `hX` and as the argument of the three
hypotheses, which is what lets the proof eliminate it by `subst` with nothing to transport: a
hypothesis mentioning the proof term would itself have to be carried along. -/
theorem obstructionMapGen_eqToHom {A : CommRingCat.{u}} (ψ : A ⟶ A) {W X X₁ : Scheme.{u}}
    (π : X ⟶ Spec A) (s : X ⟶ W) (π₁ : X₁ ⟶ Spec A) (s₁ : X₁ ⟶ W) (𝓕 : W.Modules)
    (g : X₁ ⟶ X) (hX : X₁ = X)
    (hg : ∀ h : X₁ = X, g = eqToHom h)
    (hπ : ∀ h : X₁ = X, π₁ = eqToHom h ≫ π)
    (hs : ∀ h : X₁ = X, s₁ = eqToHom h ≫ s)
    (hfst : g ≫ π = π₁ ≫ Spec.map ψ) (hsnd : g ≫ s = s₁)
    (hfst' : (𝟙 X : X ⟶ X) ≫ π = π ≫ Spec.map ψ) (hsnd' : (𝟙 X : X ⟶ X) ≫ s = s)
    (n : ℕ) {M N : ModuleCat.{u} A}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N)
    (E : (ModuleCat.restrictScalars ψ.hom).obj
          (((cohomologyDeltaFunctor π).functor n).obj
            ((tensorSheafFunctor π ((Scheme.Modules.pullback s).obj 𝓕)).obj N)) =
        (ModuleCat.restrictScalars ψ.hom).obj
          (((cohomologyDeltaFunctor π₁).functor n).obj
            ((tensorSheafFunctor π₁ ((Scheme.Modules.pullback s₁).obj 𝓕)).obj N))) :
    obstructionMapGen ψ π s π₁ s₁ 𝓕 g hfst hsnd n α =
      obstructionMapGen ψ π s π s 𝓕 (𝟙 X) hfst' hsnd' n α ≫ eqToHom E := by
  subst hX
  obtain rfl : g = 𝟙 _ := by rw [hg rfl, eqToHom_refl]
  obtain rfl : π₁ = π := by rw [hπ rfl, eqToHom_refl, Category.id_comp]
  obtain rfl : s₁ = s := by rw [hs rfl, eqToHom_refl, Category.id_comp]
  exact (comp_eqToHom_of_eq _ E).symm

/-! ### The re-indexed map, and the transport its `match` hides -/

section Reindex

variable {S : Scheme.{u}} {A A₁ : CommRingCat.{u}} (ψ : A ⟶ A₁) (t : Spec A ⟶ S)
  (t₁ : Spec A₁ ⟶ S) {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **The re-indexed map of obstruction modules is the original one followed by a transport.**
`Deformation.Artin.SectionsSheaf.obstructionMapOf` carries the base of its target as a variable
and eliminates the equality `Spec ψ ≫ t = t₁` by `match`; that `match` reduces only at the
reflexivity witness, and at an identity morphism of affine objects the equality is
`Spec (𝟙 A) ≫ t = t`, neither side of which is a variable. This says what the map is there: the
original one, followed by the transport of its target along the equality. -/
theorem obstructionMapOf_eq_comp_eqToHom (e : Spec.map ψ ≫ t = t₁) (n : ℕ)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₁}
    (α : (ModuleCat.extendScalars ψ.hom).obj M ⟶ N)
    (E₁ : (ModuleCat.restrictScalars ψ.hom).obj
          (((cohomologyDeltaFunctor (botProj ψ t q)).functor n).obj
            ((tensorSheafFunctor (botProj ψ t q) (botSheaf ψ t q 𝓕)).obj N)) =
        (ModuleCat.restrictScalars ψ.hom).obj
          (((cohomologyDeltaFunctor (topProj t₁ q)).functor n).obj
            ((tensorSheafFunctor (topProj t₁ q) (topSheaf t₁ q 𝓕)).obj N))) :
    obstructionMapOf ψ t t₁ q 𝓕 e n α = obstructionMap ψ t q 𝓕 n α ≫ eqToHom E₁ := by
  subst e
  exact (obstructionMapOf_rfl ψ t q 𝓕 n α).trans
    (comp_eqToHom_of_eq (obstructionMap ψ t q 𝓕 n α) E₁).symm

end Reindex

/-! ### The identity law for the map of obstruction modules -/

section Identity

variable {S : Scheme.{u}} {A : CommRingCat.{u}} (t : Spec A ⟶ S) {W : Scheme.{u}} (q : W ⟶ S)
  (𝓕 : W.Modules)

/-- **The map of obstruction modules of clause (2) at the identity ring map is `Hⁿ` of the
coefficient map.** This is `map_local` of clause (2) of Stacks 07YG for the example of Stacks
07YH, in the `(ψ, t)` indexing of the base-change data: at `ψ = 𝟙 A` the re-indexed map
`obstructionMapOf` is `Hⁿ(W_A, 𝓕_A ⊗_A f)`, which is the map of the obstruction functor of
clause (1).

The two transports the record of
`StacksFrontier/Deformation/Artin/Obstruction/SectionsObstructionMap.lean` listed as what stood
between `obstructionMapGen_id` and the coherence conditions are both here, and they cancel: the
`match` of `obstructionMapOf` contributes the transport along `Spec (𝟙 A) ≫ t = t`, the
base-change immersion contributes its inverse through `obstructionMapGen_eqToHom`, and
`eq_of_eqToHom_cancel` composes them to the identity. -/
theorem obstructionMapOf_id_eq (e : Spec.map (𝟙 A) ≫ t = t) (n : ℕ)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    obstructionMapOf (𝟙 A) t t q 𝓕 e n (ofSemilinear (𝟙 A) f) =
      ((cohomologyDeltaFunctor (topProj t q)).functor n).map
        ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).map f) := by
  have hfst' : (𝟙 (topScheme t q) : topScheme t q ⟶ topScheme t q) ≫ topProj t q =
      topProj t q ≫ Spec.map (𝟙 A) := by
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  let F : (Spec A ⟶ S) → ModuleCat.{u} A := fun u =>
    (ModuleCat.restrictScalars (𝟙 A : A ⟶ A).hom).obj
      (((cohomologyDeltaFunctor (topProj u q)).functor n).obj
        ((tensorSheafFunctor (topProj u q) (topSheaf u q 𝓕)).obj N))
  exact eq_of_eqToHom_cancel (congrArg F e.symm) (congrArg F e)
    (obstructionMapOf_eq_comp_eqToHom (𝟙 A) t t q 𝓕 e n (ofSemilinear (𝟙 A) f) _)
    (obstructionMapGen_eqToHom (𝟙 A) (topProj t q) (pullback.snd (Over.mk t).hom q)
      (botProj (𝟙 A) t q) (pullback.snd (quotOver (𝟙 A) t).hom q) 𝓕
      (baseChangeMap q (quotHom (𝟙 A) t)) (baseChangeObj_congr q (quotOver_eq (𝟙 A) e))
      (fun h => baseChangeMap_quotHom_id q (𝟙 A) (Spec.map_id A) t (quotOver_eq (𝟙 A) e) h)
      (fun h => pullback_fst_eqToHom q e h) (fun h => pullback_snd_eqToHom q e h)
      (commSqBase (𝟙 A) t q) (baseChangeMap_comp_snd q (quotHom (𝟙 A) t)) hfst'
      (Category.id_comp (pullback.snd (Over.mk t).hom q)) n (ofSemilinear (𝟙 A) f) _)
    (obstructionMapGen_id_of_semilinear (topProj t q) (pullback.snd (Over.mk t).hom q) 𝓕 n
      hfst' (Category.id_comp (pullback.snd (Over.mk t).hom q)) f)

end Identity

/-! ### `map_id` and `map_local` at an affine object -/

section AffineObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : Type v}
  [Category.{w} Y] {p : Y ⥤ BigFppfOver B S hS} {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- **`map_local` of clause (2) of Stacks 07YG for the example of Stacks 07YH**: at an identity
morphism of affine objects, the map of obstruction modules induced by a morphism `f : M ⟶ N` of
`A`-modules is the map `𝒪(f)` of the obstruction functor of clause (1).

The semilinear datum the `map` field quantifies over is, at an identity morphism, a plain
morphism of `Mod_A`: the ring map is `RingHom.id`, so `ModuleCat.restrictScalars` of it is the
identity functor on the nose, and `ofSemilinear` reads `f` as the map `A ⊗_A M → N` the map of
obstruction modules takes as input. -/
theorem affineObstructionMap_id_eq (P : AffineObject B S hS p)
    {M N : ModuleCat.{u} (CommRingCat.of P.alg.carrier)} (f : M ⟶ N) :
    affineObstructionMap q 𝓕 (AffineObject.Hom.id P)
        (ofSemilinear (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap) f) =
      (affineObstruction q 𝓕 P).functor.map f :=
  obstructionMapOf_id_eq P.alg.toScheme q 𝓕
    (AffineObject.Hom.id P).alg.specMap_comp_toScheme 1 f

/-- **`map_id` of clause (2) of Stacks 07YG for the example of Stacks 07YH**: at an identity
morphism of affine objects and the identity of a module, the map of obstruction modules is the
identity. This is `affineObstructionMap_id_eq` at `f = 𝟙 M` together with the functoriality of
the obstruction functor of clause (1). -/
theorem affineObstructionMap_id (P : AffineObject B S hS p)
    (M : ModuleCat.{u} (CommRingCat.of P.alg.carrier)) :
    affineObstructionMap q 𝓕 (AffineObject.Hom.id P)
        (ofSemilinear (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap) (𝟙 M)) =
      𝟙 ((affineObstruction q 𝓕 P).functor.obj M) :=
  (affineObstructionMap_id_eq q 𝓕 P (𝟙 M)).trans
    ((affineObstruction q 𝓕 P).functor.map_id M)

/-- `affineObstructionMap_id_eq` element-wise, which is the form the `map_local` field of
`Deformation.Artin.ObstructionTheory` states its conclusion in. -/
theorem affineObstructionMap_id_eq_apply (P : AffineObject B S hS p)
    {M N : ModuleCat.{u} (CommRingCat.of P.alg.carrier)} (f : M ⟶ N)
    (o : ((affineObstruction q 𝓕 P).functor.obj M : Type u)) :
    affineObstructionMap q 𝓕 (AffineObject.Hom.id P)
        (ofSemilinear (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap) f) o =
      ((affineObstruction q 𝓕 P).functor.map f) o := by
  rw [affineObstructionMap_id_eq]
  rfl

/-- `affineObstructionMap_id` element-wise, which is the form the `map_id` field of
`Deformation.Artin.ObstructionTheory` states its conclusion in. -/
theorem affineObstructionMap_id_apply (P : AffineObject B S hS p)
    (M : ModuleCat.{u} (CommRingCat.of P.alg.carrier))
    (o : ((affineObstruction q 𝓕 P).functor.obj M : Type u)) :
    affineObstructionMap q 𝓕 (AffineObject.Hom.id P)
        (ofSemilinear (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap) (𝟙 M)) o = o := by
  rw [affineObstructionMap_id]
  rfl

end AffineObject

end Deformation.Artin.SectionsSheaf

end
