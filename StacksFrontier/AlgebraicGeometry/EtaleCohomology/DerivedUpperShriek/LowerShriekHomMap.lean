module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.Compactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageCompositionUnbounded
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map `Rf_*RHom_Λ(K, L) ⟶ RHom_Λ(Rf_!K, Rf_!L)` on étale derived categories

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y`
(an open immersion followed by a proper morphism, `AlgebraicGeometry.CompactificationOf`), so
that `Rf_! = Rf̄_* ∘ j_!` (`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`), and let `Λ` be
a commutative ring. For `K`, `L` in `D(X_étale, Λ)` this file constructs the canonical map of
[Stacks, Tag 0GL7]

`α : Rf_*RHom_Λ(K, L) ⟶ RHom_Λ(Rf_!K, Rf_!L)`

and proves that it is functorial in `K` and `L`.

The construction is the source's, carried out on the étale derived categories themselves. The
three derived categories `D(X_étale, Λ)`, `D(X̄_étale, Λ)` and `D(Y_étale, Λ)` carry their derived
tensor products and derived internal Homs with the tensor–internal-Hom adjunction of
[Stacks, Tag 08J8] (`Stacks.EtaleCohomology.etaleTensorHomAdjunction`); the source of `β'` is
identified with `j_!(RHom_Λ(K, L) ⊗^L_Λ K)` by the projection formula [Stacks, Tag 0GL1] for `j`
together with `j^{-1}Rj_* = id` (`Stacks.EtaleCohomology.etaleDerivedPushforwardProjectionIso`);
`γ` is the canonical map of [Stacks, Tag 0B6D] for `f̄`, built from the relative cup product of
[Stacks, Tag 0B6C] (`Stacks.EtaleCohomology.etaleRelativeCupProduct`); and `Rf_* = Rf̄_* ∘ Rj_*`
is Leray (`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedLerayIso`). These are
packaged as `Stacks.EtaleCohomology.etaleCompactificationData`, an instance of the construction
`Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData` of `β`, `γ` and `α = γ ∘ Rf̄_*β`.

## Main definitions

* `Stacks.EtaleCohomology.etaleCompactificationData`: the data of the construction for the
  étale derived categories of a compactification.
* `Stacks.EtaleCohomology.etaleLowerShriekHomMap`: **the canonical map `α` of
  [Stacks, Tag 0GL7]**.
* `Stacks.EtaleCohomology.etaleLowerShriekHomNatTrans`: `α` as a natural transformation of
  bifunctors in `(K, L)`.

## Main results

* `Stacks.EtaleCohomology.etaleLowerShriekHomMap_eq`: `α = γ ∘ Rf̄_*β`, preceded by Leray.
* `Stacks.EtaleCohomology.etaleLowerShriekHomMap_naturality_source` and `..._target`: `α` is
  contravariant in `K` and covariant in `L`.

## Implementation notes

The source states the construction for `f` separated of finite type between quasi-compact and
quasi-separated schemes and `Λ` a torsion coefficient ring; these hypotheses make `Rf_!`
independent of the compactification ([Stacks, Tag 0F7I]) and are not used by the construction
of `α` for a chosen compactification, which is given here for an arbitrary morphism with an
arbitrary compactification and an arbitrary commutative ring. The compactification is an explicit
argument, as it is for `Stacks.EtaleCohomology.derivedLowerShriekUnbounded`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.DerivedUpperShriek

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f))

/-- **The data of the construction of [Stacks, Tag 0GL7] for étale derived categories**: the
derived tensor products, derived internal Homs and tensor–internal-Hom adjunctions of
`D(X_étale, Λ)`, `D(X̄_étale, Λ)`, `D(Y_étale, Λ)`, the functors `j_!`, `Rj_*`, `Rf̄_*`, the
projection isomorphism `Rj_*M ⊗^L j_!B ≅ j_!(M ⊗^L B)` and the relative cup product of `f̄`. -/
def etaleCompactificationData :
    CompactificationData (DerivedCategory (EtaleModules.{u, r} Λ X))
      (DerivedCategory (EtaleModules.{u, r} Λ j.space))
      (DerivedCategory (EtaleModules.{u, r} Λ Y)) where
  tensorU := etaleDerivedTensor.{u, r} Λ X
  homU := etaleDerivedHom.{u, r} Λ X
  adjU := etaleTensorHomAdjunction.{u, r} Λ X
  tensorX := etaleDerivedTensor.{u, r} Λ j.space
  homX := etaleDerivedHom.{u, r} Λ j.space
  adjX := etaleTensorHomAdjunction.{u, r} Λ j.space
  tensorY := etaleDerivedTensor.{u, r} Λ Y
  homY := etaleDerivedHom.{u, r} Λ Y
  adjY := etaleTensorHomAdjunction.{u, r} Λ Y
  shriek := etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion
  pushforwardJ := etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.immersion
  pushforwardFbar := etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  projIso := etaleDerivedPushforwardProjectionIso.{u, r} Λ j.immersion
  cup := etaleRelativeCupProduct.{u, r} Λ j.toBase

/-- `Rf_!` of the data is the derived lower shriek through the compactification. -/
theorem etaleCompactificationData_derivedLowerShriek :
    (etaleCompactificationData.{u, r} Λ f j).derivedLowerShriek =
      derivedLowerShriekUnbounded.{u, r} f j Λ :=
  rfl

/-- **Leray**, `Rf_* ≅ Rf̄_* ∘ Rj_*`, for the factorization `f = f̄ ∘ j` of a compactification. -/
def etaleCompactificationLerayIso :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ≅
      (etaleCompactificationData.{u, r} Λ f j).derivedPushforward :=
  etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ j.immersion j.toBase f
    (Over.w j.obj.hom).symm

/-- **The canonical map `α` of [Stacks, Tag 0GL7]**,

`α : Rf_*RHom_Λ(K, L) ⟶ RHom_Λ(Rf_!K, Rf_!L)`,

for `K`, `L` in `D(X_étale, Λ)`, with `Rf_! = Rf̄_* ∘ j_!` computed through the compactification
`j`: Leray `Rf_* = Rf̄_* ∘ Rj_*`, followed by `Rf̄_*β` and by the map `γ` of
[Stacks, Tag 0B6D] for `f̄`. -/
@[stacks 0GL7 "the canonical map α on étale derived categories, for a compactification of f;
  β is built from 08J8, 0GL1 and j^{-1}Rj_* = id, γ from 0B6C/0B6D, Rf_* = Rf̄_* Rj_* by Leray"]
def etaleLowerShriekHomMap (K L : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
        (((etaleDerivedHom.{u, r} Λ X).obj (op K)).obj L) ⟶
      ((etaleDerivedHom.{u, r} Λ Y).obj (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K))).obj
        ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L) :=
  (etaleCompactificationLerayIso.{u, r} Λ f j).hom.app _ ≫
    (etaleCompactificationData.{u, r} Λ f j).lowerShriekHomMap K L

/-- **`α = γ ∘ Rf̄_*β`**, preceded by Leray `Rf_* = Rf̄_* ∘ Rj_*`: the factorization of the
canonical map of [Stacks, Tag 0GL7] along the compactification, with `β` the open-immersion map
and `γ` the direct-image map of [Stacks, Tag 0B6D]. -/
@[stacks 0GL7 "α = γ ∘ Rf̄_*β (after Leray), on étale derived categories"]
theorem etaleLowerShriekHomMap_eq (K L : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    etaleLowerShriekHomMap.{u, r} Λ f j K L =
      (etaleCompactificationLerayIso.{u, r} Λ f j).hom.app _ ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).map
          ((etaleCompactificationData.{u, r} Λ f j).openImmersionHomMap K L) ≫
        (etaleCompactificationData.{u, r} Λ f j).pushforwardHomMap
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K)
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj L) :=
  rfl

/-- Pasting a naturality square of `e` with a square that starts at the target of `e`. -/
private theorem map_comp_app_comp_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ⟶ G) {a b : C} {g : a ⟶ b} {P Q : D} {s : G.obj a ⟶ P} {s' : G.obj b ⟶ Q} {u : P ⟶ Q}
    (h : G.map g ≫ s' = s ≫ u) : F.map g ≫ e.app b ≫ s' = (e.app a ≫ s) ≫ u := by
  rw [Category.assoc, ← h, e.naturality_assoc]

/-- **The canonical map of [Stacks, Tag 0GL7] is covariant in `L`.** -/
@[stacks 0GL7 "functoriality of α in L, on étale derived categories"]
theorem etaleLowerShriekHomMap_naturality_target (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    {L L' : DerivedCategory (EtaleModules.{u, r} Λ X)} (l : L ⟶ L') :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).map
        (((etaleDerivedHom.{u, r} Λ X).obj (op K)).map l) ≫
          etaleLowerShriekHomMap.{u, r} Λ f j K L' =
      etaleLowerShriekHomMap.{u, r} Λ f j K L ≫
        ((etaleDerivedHom.{u, r} Λ Y).obj
            (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj K))).map
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).map l) := by
  dsimp only [etaleLowerShriekHomMap]
  exact map_comp_app_comp_eq (etaleCompactificationLerayIso.{u, r} Λ f j).hom
    (etaleCompactificationData.{u, r} Λ f j |>.lowerShriekHomMap_naturality_target K l)

/-- **The canonical map of [Stacks, Tag 0GL7] is contravariant in `K`.** -/
@[stacks 0GL7 "functoriality of α in K, on étale derived categories"]
theorem etaleLowerShriekHomMap_naturality_source {K K' : DerivedCategory (EtaleModules.{u, r} Λ X)}
    (k : K' ⟶ K) (L : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).map
        (((etaleDerivedHom.{u, r} Λ X).map k.op).app L) ≫ etaleLowerShriekHomMap.{u, r} Λ f j K' L =
      etaleLowerShriekHomMap.{u, r} Λ f j K L ≫
        ((etaleDerivedHom.{u, r} Λ Y).map ((derivedLowerShriekUnbounded.{u, r} f j Λ).map k).op).app
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L) := by
  dsimp only [etaleLowerShriekHomMap]
  exact map_comp_app_comp_eq (etaleCompactificationLerayIso.{u, r} Λ f j).hom
    (etaleCompactificationData.{u, r} Λ f j |>.lowerShriekHomMap_naturality_source k L)

/-- **The canonical map of [Stacks, Tag 0GL7], functorial in `K` and `L`**: `α` as a natural
transformation between the bifunctors `(K, L) ↦ Rf_*RHom_Λ(K, L)` and
`(K, L) ↦ RHom_Λ(Rf_!K, Rf_!L)` on `D(X_étale, Λ)ᵒᵖ × D(X_étale, Λ)`. -/
@[stacks 0GL7 "the canonical map α : Rf_*RHom(K, L) ⟶ RHom(Rf_!K, Rf_!L) on étale derived
  categories, functorial in K and L, for a compactification of f"]
def etaleLowerShriekHomNatTrans :
    etaleDerivedHom.{u, r} Λ X ⋙
        (Functor.whiskeringRight _ _ _).obj (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f) ⟶
      (derivedLowerShriekUnbounded.{u, r} f j Λ).op ⋙ etaleDerivedHom.{u, r} Λ Y ⋙
        (Functor.whiskeringLeft _ _ _).obj (derivedLowerShriekUnbounded.{u, r} f j Λ) where
  app K :=
    { app := fun L => etaleLowerShriekHomMap.{u, r} Λ f j K.unop L
      naturality := fun _ _ l => etaleLowerShriekHomMap_naturality_target.{u, r} Λ f j K.unop l }
  naturality _ _ k := by
    ext L
    exact etaleLowerShriekHomMap_naturality_source.{u, r} Λ f j k.unop L

/-- The `(K, L)` component of `etaleLowerShriekHomNatTrans` is `etaleLowerShriekHomMap K L`. -/
theorem etaleLowerShriekHomNatTrans_app_app (K L : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ((etaleLowerShriekHomNatTrans.{u, r} Λ f j).app (op K)).app L =
      etaleLowerShriekHomMap.{u, r} Λ f j K L :=
  rfl

end Stacks.EtaleCohomology

end
