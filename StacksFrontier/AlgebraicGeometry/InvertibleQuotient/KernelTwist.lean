module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria

/-!
# Twisting by an invertible sheaf does not change left exactness of a pullback

Tag 0B3V's base-change clause for the kernel of an invertible quotient `q : E ⟶ L` asks that
the canonical comparison `g^*(\ker q) ⟶ \ker q'` be invertible.
`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/Basic.lean` reduces that, with no
hypothesis, to the single statement

`Mono ((Scheme.Modules.pullback g).map (kernel.ι q))`

(`Stacks.Divisors.mono_quotientKernelBaseChangeMap_iff`), the comparison being an epimorphism
always. This file removes the line bundle `L` from that statement: whether pullback carries a
monomorphism of module sheaves to a monomorphism is unchanged by tensoring it with **any**
invertible sheaf. The Tag 01CD input enters once, as the comparison
`g^*(A ⊗ N) ≅ g^*A ⊗ g^*N` being invertible.

Mathematically this is the identity `L_1 g^*(M ⊗ N) ≅ L_1 g^*(M) ⊗ g^* N` for invertible `N`,
read at the single degree that matters. Its use is that, taking `N = L^{⊗ -1}`, the kernel
clause of Tag 0B3V for an arbitrary invertible quotient becomes the same clause for a quotient
whose target is the **structure sheaf** — where the stalkwise argument needs no local
triviality of `L` at all, the structure sheaf being free of rank one over itself at every
point.

## Main results

* `Stacks.mono_iff_of_isIso_sq`: in a commuting square whose two vertical maps are invertible,
  the two horizontal maps are monomorphisms together.
* `Stacks.mono_map_iff_of_isEquivalence`: an equivalence both preserves and reflects
  monomorphisms.
* `Stacks.Divisors.mono_pullback_map_tensorRight_iff`: **the main result.** For a morphism of
  schemes `g : X' ⟶ X`, an invertible `N` on `X` and any `φ : A ⟶ A'` of `𝒪_X`-modules,
  `g^*(φ ⊗ N)` is a monomorphism if and only if `g^* φ` is. The hypothesis is the stalk formula
  of Tag 0098 for the pullback, which is the single remaining input of Tag 01CD.
* `Stacks.Divisors.mono_quotientKernelBaseChangeMap_iff_tensorRight`: consequently Tag 0B3V's
  kernel base-change clause holds if and only if pullback carries the twisted inclusion
  `(\ker q) ⊗ N ⟶ E ⊗ N` to a monomorphism, for one (hence any) invertible `N`.

## Implementation notes

The proof is the naturality of `Stacks.RingedSpace.comparisonNatTrans` in its **first** variable
at the morphism `(φ, 𝟙 N)`, both of whose components are invertible by
`Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula`, together with
`(Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj N` being an equivalence on both
sides — on `X'` because `g^* N` is invertible, which is Tag 0B8L.

Tensoring on the right by `N` is written in the canonical spelling
`(Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj N`, the functor
`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence` is stated about, whereas
`Stacks.RingedSpace.comparisonNatTrans` is stated about the uncurried bifunctor
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)`. The two are crossed on
each side of the naturality square by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` followed by
`Stacks.SheafOfModules.Tensor.sheafTensor_map_app`, which identify the uncurried action on
`(φ, 𝟙 N)` with the right-tensor action on `φ`.

Two further spellings cross by `rfl`, so nothing is transported:
`Scheme.Modules.pullback g = RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom`
(recorded in `StacksFrontier/AlgebraicGeometry/Modules/QuasicoherentPullbackScheme.lean`) and
`(Stacks.RingedSpace.comparisonNatTrans f).app (A, B) = Stacks.RingedSpace.comparison f A B`.
The one step that is *not* definitional is `g^*(𝟙 N) = 𝟙 (g^* N)` — `Functor.map_id` for a
pullback functor obtained from an adjunction is a proof, not a reduction — and it is the only
rewrite in the proof. Writing the square out in the spelling the statement uses and then
closing it by `exact` is what keeps the `isDefEq` work bounded; asking
`comparisonNatTrans.naturality` to elaborate directly against that spelling exhausts the
heartbeat budget, and `rw`-ing the definitional identifications into the naturality statement
fails to find its patterns, the two sides printing identically while differing in the
`Category` instance behind `𝟙`.

**An instance that is not found and must be applied by hand.**
`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence` is an `instance`, but
`infer_instance` does not find `((Tensor.sheafTensor ⟨O, _⟩).flip.obj L).IsEquivalence` even
with `AlgebraicGeometry.SheafOfModules.IsInvertible O hO L` in the local context; applying the
instance explicitly works. `Functor.flip` carries `@[implicit_reducible]`, which is the likely
cause.

To instantiate `N` as `L^{⊗ -1}` use
`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`
(`StacksFrontier/AlgebraicGeometry/Ample/AmpleCriteria.lean`), which supplies invertibility of
every integer tensor power.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks

/-- In a commuting square whose two vertical maps are invertible, the two horizontal maps are
monomorphisms together: each is the other conjugated by isomorphisms. -/
theorem mono_iff_of_isIso_sq {C : Type*} [Category C] {a b a' b' : C}
    (u : a ⟶ a') (v : b ⟶ b') [IsIso u] [IsIso v] {f : a ⟶ b} {f' : a' ⟶ b'}
    (h : f ≫ v = u ≫ f') : Mono f ↔ Mono f' := by
  have h1 : f' = inv u ≫ f ≫ v := by rw [h, IsIso.inv_hom_id_assoc]
  have h2 : f = u ≫ f' ≫ inv v := by
    rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  constructor
  · intro _; rw [h1]; infer_instance
  · intro _; rw [h2]; infer_instance

/-- An equivalence preserves and reflects monomorphisms. -/
theorem mono_map_iff_of_isEquivalence {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [F.IsEquivalence] {a b : C} (f : a ⟶ b) : Mono (F.map f) ↔ Mono f :=
  ⟨fun h => F.mono_of_mono_map h, fun _ => F.map_mono f⟩

end Stacks

namespace Stacks.Divisors

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- The uncurried tensor action on `(φ, 𝟙 N)` is the right-tensor action on `φ`. -/
private theorem uncurry_map_id_eq_flip_map (S : Scheme.{u}) {A A' : S.Modules} (φ : A ⟶ A')
    (N : S.Modules) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} S.sheaf)).map
        (X := (A, N)) (Y := (A', N)) (φ, 𝟙 N) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} S.sheaf).flip.obj N).map φ :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map S.sheaf φ (𝟙 N)).trans
    (Stacks.SheafOfModules.Tensor.sheafTensor_map_app S.sheaf φ N).symm

/-- **Twisting by an invertible sheaf does not change whether a pullback preserves a
monomorphism.** For `N` an invertible `𝒪_X`-module and `φ : A ⟶ A'` a morphism of
`𝒪_X`-modules, `g^*(φ ⊗ N)` is a monomorphism exactly when `g^* φ` is.

The hypothesis `hg` is the stalk formula of Tag 0098 for the pullback of sheaves of modules
along `g`, the single remaining input of Tag 01CD; it is used only through
`Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula`, so this statement closes
together with every other consumer of Tag 01CD.

Taking `N = L^{⊗ -1}` for the quotient line `L` of Tag 0B3V turns that tag's kernel
base-change clause into the same clause for a quotient onto the structure sheaf; see
`Stacks.Divisors.mono_quotientKernelBaseChangeMap_iff_tensorRight`. -/
theorem mono_pullback_map_tensorRight_iff
    (hg : Stacks.RingedSpace.PullbackStalkFormula g.toLRSHom.toShHom)
    (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    {A A' : X.Modules} (φ : A ⟶ A') :
    Mono ((Scheme.Modules.pullback g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj N).map
          φ)) ↔
      Mono ((Scheme.Modules.pullback g).map φ) := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj N) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback g.toLRSHom.toShHom N
  have hcA := Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula _ hg A N
  have hcA' := Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula _ hg A' N
  have hnat := (Stacks.RingedSpace.comparisonNatTrans g.toLRSHom.toShHom).naturality
    ((φ, 𝟙 N) : ((A, N) :
      SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) ×
      SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)) ⟶ (A', N))
  have hnat2 : (Scheme.Modules.pullback g).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          X.sheaf)).map (X := (A, N)) (Y := (A', N)) (φ, 𝟙 N)) ≫
      Stacks.RingedSpace.comparison g.toLRSHom.toShHom A' N =
    Stacks.RingedSpace.comparison g.toLRSHom.toShHom A N ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        X'.sheaf)).map
        (X := ((Scheme.Modules.pullback g).obj A, (Scheme.Modules.pullback g).obj N))
        (Y := ((Scheme.Modules.pullback g).obj A', (Scheme.Modules.pullback g).obj N))
        ((Scheme.Modules.pullback g).map φ, (Scheme.Modules.pullback g).map (𝟙 N)) := hnat
  rw [CategoryTheory.Functor.map_id] at hnat2
  have hsq : (Scheme.Modules.pullback g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj N).map
          φ) ≫
      Stacks.RingedSpace.comparison g.toLRSHom.toShHom A' N =
    Stacks.RingedSpace.comparison g.toLRSHom.toShHom A N ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X'.sheaf).flip.obj
        ((Scheme.Modules.pullback g).obj N)).map ((Scheme.Modules.pullback g).map φ) :=
    (congrArg (fun morphism => (Scheme.Modules.pullback g).map morphism ≫
        Stacks.RingedSpace.comparison g.toLRSHom.toShHom A' N)
        (uncurry_map_id_eq_flip_map X φ N)).symm.trans
      (hnat2.trans (congrArg (fun morphism =>
        Stacks.RingedSpace.comparison g.toLRSHom.toShHom A N ≫ morphism)
        (uncurry_map_id_eq_flip_map X' ((Scheme.Modules.pullback g).map φ) _)))
  refine (Stacks.mono_iff_of_isIso_sq
    (Stacks.RingedSpace.comparison g.toLRSHom.toShHom A N)
    (Stacks.RingedSpace.comparison g.toLRSHom.toShHom A' N) hsq).trans ?_
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X'.sheaf).flip.obj
      ((Scheme.Modules.pullback g).obj N)).IsEquivalence :=
    tensorRightFunctor_isEquivalence X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj N)
  exact Stacks.mono_map_iff_of_isEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X'.sheaf).flip.obj
      ((Scheme.Modules.pullback g).obj N)) _

/-- **Tag 0B3V's kernel base-change clause, with the quotient line twisted away.** The
canonical comparison `g^*(\ker q) ⟶ \ker q'` is a monomorphism — equivalently, by
`Stacks.Divisors.epi_quotientKernelBaseChangeMap` and
`Stacks.Divisors.isIso_quotientKernelBaseChangeMap_of_mono`, an isomorphism, which is what the
tag asserts — if and only if pullback carries the inclusion `\ker q ⟶ E` **tensored with an
arbitrary invertible sheaf `N`** to a monomorphism.

With `N = Q.L^{⊗ -1}` (invertible by
`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`) the right-hand side is a statement
about a quotient whose target is isomorphic to the structure sheaf, which is where the
remaining stalkwise argument becomes available without any local triviality input. -/
theorem mono_quotientKernelBaseChangeMap_iff_tensorRight
    (hg : Stacks.RingedSpace.PullbackStalkFormula g.toLRSHom.toShHom)
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)
    (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    Mono (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq) ↔
      Mono ((Scheme.Modules.pullback g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj N).map
          (kernel.ι Q.q))) :=
  (mono_quotientKernelBaseChangeMap_iff g E E' hE Q Q' hL hq).trans
    (mono_pullback_map_tensorRight_iff g hg N (kernel.ι Q.q)).symm

/-- **Tag 0B3V's kernel base-change clause reduced to a quotient onto the structure sheaf.**
`mono_quotientKernelBaseChangeMap_iff_tensorRight` at `N = Q.L^{⊗ -1}`.

What the reduction buys: the morphism `Q.q ⊗ Q.L^{⊗ -1}` whose kernel inclusion appears on the
right is an epimorphism onto `Q.L ⊗ Q.L^{⊗ -1}`, and that object is the structure sheaf, by
`Stacks.SheafOfModules.Invertible.tensorProductBraiding` followed by
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso` in degree `-1`. So the clause has been
reduced to left exactness of pullback on the kernel sequence of an epimorphism **onto
`𝒪_X`** — and a surjection onto the structure sheaf splits at every stalk with no local
triviality input, the structure sheaf being free of rank one over itself there. -/
theorem mono_quotientKernelBaseChangeMap_iff_tensorPowerNegOne
    (hg : Stacks.RingedSpace.PullbackStalkFormula g.toLRSHom.toShHom)
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q) :
    letI := Q.invertible
    Mono (quotientKernelBaseChangeMap g E E' hE Q Q' hL hq) ↔
      Mono ((Scheme.Modules.pullback g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj
          (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))).map (kernel.ι Q.q))) :=
  let := Q.invertible
  have := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 Q.L (-1)
  mono_quotientKernelBaseChangeMap_iff_tensorRight g hg E E' hE Q Q' hL hq _

end Stacks.Divisors

end
