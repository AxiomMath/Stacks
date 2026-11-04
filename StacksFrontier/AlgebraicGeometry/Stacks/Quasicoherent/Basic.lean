module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Pushforward
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Morphisms of quasi-coherent modules over a scheme

Fix a big fppf site containing a scheme `S`. An object of the category of quasi-coherent
modules over `S` is a scheme over `S` in that site together with a quasi-coherent module on
it, and a morphism is a morphism of schemes over `S` together with an `f`-map of modules,
that is, a morphism from the target module into the pushforward of the source module. By the
pullback–pushforward adjunction such a morphism is equivalently a morphism from the pullback
of the target module to the source module, so the hom-sets decompose as a disjoint union over
the morphisms of the base.

## Main definitions

* `Stacks.QCoh.Object`: a scheme in the big fppf site over `S` together with a quasi-coherent
  module on it.
* `Stacks.QCoh.FMap`: a morphism over `S` together with an `f`-map of modules.
* `Stacks.QCoh.CategoryData`: the category of these pairs, its projection to the big fppf
  slice, and the identification of its homs, identities and composition with those of
  `f`-maps.
* `Stacks.QCoh.projection`: the projection to the big fppf slice.
* `Stacks.QCoh.homEquivPullbackHom`: the hom-sets as a disjoint union of pullback homs.

## Main results

* `Stacks.QCoh.exists_categoryData`: the category exists, with the displayed description of
  its hom-sets, identities and composition.

## Implementation notes

The category is produced as data rather than as a bundled structure instance so that its
hom-sets can be *stated* to be the `f`-map type: `CategoryData` pins the identity and the
composition to the canonical `f`-map operations, the left-hand side of each equation being
the actual hom-set of a category over the big fppf slice. The category instance on
`Object` is then obtained by choice from `exists_categoryData`, which is why it is
noncomputable.

An `f`-map is represented as a morphism into the module pushforward; the adjoint
description in `homEquivPullbackHom` uses the canonical module pullback. Quasi-coherence is
Mathlib's `SheafOfModules.IsQuasicoherent`.

The identity and the composition of `f`-maps carry the coherence comparisons of pushforward
along an identity and along a composite. Because pushforward of modules on a scheme is
strictly functorial, those comparisons are identities; the category axioms reduce to that
observation, recorded in `Stacks.Modules`.

## References

* [Stacks Project, Tag 04U2](https://stacks.math.columbia.edu/tag/04U2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme over `S` in the chosen big fppf site, equipped with a quasi-coherent module. -/
public structure Object where
  /-- The underlying object of the big fppf category over `S`. -/
  base : BigFppfOver B S hS
  /-- The module on the underlying scheme. -/
  module : ((BigFppfOver.toScheme B S hS).obj base).Modules
  /-- The module is quasi-coherent. -/
  quasicoherent : module.IsQuasicoherent

variable {B S hS}

/-- The morphism of schemes underlying a morphism of the big fppf category over `S`. -/
public abbrev Object.schemeMap {A C : Object B S hS} (f : A.base ⟶ C.base) :
    (BigFppfOver.toScheme B S hS).obj A.base ⟶ (BigFppfOver.toScheme B S hS).obj C.base :=
  (BigFppfOver.toScheme B S hS).map f

/-- An `f`-map of quasi-coherent modules, together with its morphism of schemes over `S`:
a morphism of the base and a morphism from the target module into the pushforward of the
source module. -/
public abbrev FMap (A C : Object B S hS) : Type u :=
  Σ f : A.base ⟶ C.base,
    C.module ⟶ (Scheme.Modules.pushforward (Object.schemeMap f)).obj A.module

/-- The identity `f`-map, built from the canonical identification of the pushforward along an
identity. -/
public noncomputable def FMap.id (A : Object B S hS) : FMap A A :=
  ⟨𝟙 A.base,
    (Scheme.Modules.pushforwardId
      ((BigFppfOver.toScheme B S hS).obj A.base)).inv.app A.module ≫
    (Scheme.Modules.pushforwardCongr rfl).inv.app A.module⟩

/-- Composition of `f`-maps, built from the canonical isomorphism comparing the pushforward
along a composite with the composite of pushforwards. -/
public noncomputable def FMap.comp {A C D : Object B S hS}
    (m : FMap A C) (n : FMap C D) : FMap A D :=
  ⟨m.1 ≫ n.1,
    n.2 ≫ (Scheme.Modules.pushforward (Object.schemeMap n.1)).map m.2 ≫
    (Scheme.Modules.pushforwardComp
      (Object.schemeMap m.1) (Object.schemeMap n.1)).hom.app A.module ≫
    (Scheme.Modules.pushforwardCongr rfl).inv.app A.module⟩

/-- The identity `f`-map is a left unit for composition. -/
public theorem FMap.id_comp {A C : Object B S hS} (f : FMap A C) :
    FMap.comp (FMap.id A) f = f := by
  have hb : (FMap.id A).1 ≫ f.1 = f.1 := by simp [FMap.id]
  refine Sigma.ext hb ?_
  dsimp [FMap.comp, FMap.id] at hb ⊢
  cases hb
  simp [Stacks.Modules.pushforwardId_inv_app, Stacks.Modules.pushforwardComp_hom_app,
    Stacks.Modules.pushforwardCongr_rfl_inv_app, Stacks.Modules.pushforward_id_obj,
    Stacks.Modules.pushforward_comp_obj]

/-- The identity `f`-map is a right unit for composition. -/
public theorem FMap.comp_id {A C : Object B S hS} (f : FMap A C) :
    FMap.comp f (FMap.id C) = f := by
  have hb : f.1 ≫ (FMap.id C).1 = f.1 := by simp [FMap.id]
  refine Sigma.ext hb ?_
  dsimp [FMap.comp, FMap.id] at hb ⊢
  cases hb
  simp [Stacks.Modules.pushforwardId_inv_app, Stacks.Modules.pushforwardComp_hom_app,
    Stacks.Modules.pushforwardCongr_rfl_inv_app, Stacks.Modules.pushforward_id_map,
    Stacks.Modules.pushforward_id_obj, Stacks.Modules.pushforward_comp_obj]

/-- Composition of `f`-maps is associative. -/
public theorem FMap.assoc {A C D E : Object B S hS} (f : FMap A C) (g : FMap C D)
    (h : FMap D E) : FMap.comp (FMap.comp f g) h = FMap.comp f (FMap.comp g h) := by
  have hb : (f.1 ≫ g.1) ≫ h.1 = f.1 ≫ (g.1 ≫ h.1) := by simp
  refine Sigma.ext hb ?_
  dsimp [FMap.comp] at hb ⊢
  cases hb
  simp [Stacks.Modules.pushforwardComp_hom_app, Stacks.Modules.pushforwardCongr_rfl_inv_app,
    Stacks.Modules.pushforward_comp_map, Stacks.Modules.pushforward_comp_obj]

/-- A category of quasi-coherent pairs over the big fppf slice: a category structure on
`Object`, a projection to the slice, and the identifications of its hom-sets, identities,
composition and projection with the canonical `f`-map data. -/
public structure CategoryData (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The category structure. -/
  category : Category.{u} (Object B S hS)
  /-- The projection to the big fppf category over `S`. -/
  projection : letI : Category.{u} (Object B S hS) := category
    Object B S hS ⥤ BigFppfOver B S hS
  /-- The projection forgets the module. -/
  projection_obj : ∀ A : Object B S hS, projection.obj A = A.base
  /-- The hom-sets are the `f`-maps. -/
  hom_type : letI : Category.{u} (Object B S hS) := category
    ∀ A C : Object B S hS, (A ⟶ C) = FMap A C
  /-- The identity is the identity `f`-map. -/
  identity : letI : Category.{u} (Object B S hS) := category
    ∀ A : Object B S hS, (Equiv.cast (hom_type A A)) (𝟙 A) = FMap.id A
  /-- Composition is composition of `f`-maps. -/
  composition : letI : Category.{u} (Object B S hS) := category
    ∀ {A C D : Object B S hS} (m : A ⟶ C) (n : C ⟶ D),
      (Equiv.cast (hom_type A D)) (m ≫ n) =
        FMap.comp ((Equiv.cast (hom_type A C)) m) ((Equiv.cast (hom_type C D)) n)
  /-- The projection takes a morphism to the morphism of bases underlying its `f`-map. -/
  projection_map : letI : Category.{u} (Object B S hS) := category
    ∀ {A C : Object B S hS} (m : A ⟶ C),
      (projection.map m) =
        eqToHom (projection_obj A) ≫ ((Equiv.cast (hom_type A C)) m).1 ≫
          eqToHom (projection_obj C).symm

/-- **Stacks 04U2.** The category of quasi-coherent pairs over `S` exists together with its
projection to the big fppf slice, and its morphisms are exactly the pairs of a morphism of
schemes over `S` and an `f`-map of modules. The description of a hom-set as a disjoint union
of pullback homs then follows by the pullback–pushforward adjunction. -/
@[stacks 04U2 "quasi-coherent category and f-map homs"]
public theorem exists_categoryData : Nonempty (CategoryData B S hS) :=
  let cat : Category.{u} (Object B S hS) :=
    { Hom A C := FMap A C
      id A := FMap.id A
      comp m n := FMap.comp m n
      id_comp _ := FMap.id_comp _
      comp_id _ := FMap.comp_id _
      assoc _ _ _ := FMap.assoc _ _ _ }
  ⟨{ category := cat
     projection :=
      { obj A := A.base
        map f := f.1
        map_id _ := rfl
        map_comp _ _ := rfl }
     projection_obj _ := rfl
     hom_type _ _ := rfl
     identity _ := rfl
     composition _ _ := rfl
     projection_map _ := rfl }⟩

/-- The category structure on quasi-coherent pairs supplied by Stacks 04U2. -/
public noncomputable instance : Category.{u} (Object B S hS) :=
  (Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))).category

/-- The projection of the category of quasi-coherent pairs to the big fppf slice. -/
public noncomputable def projection : Object B S hS ⥤ BigFppfOver B S hS :=
  (Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))).projection

/-- **Stacks 04U2.** A hom-set of the category of quasi-coherent pairs is the disjoint union,
over the morphisms `f` of the base, of the morphisms from the pullback of the target module
along `f` to the source module. -/
@[stacks 04U2 "pullback hom equation"]
public noncomputable def homEquivPullbackHom (A C : Object B S hS) :
    (A ⟶ C) ≃
      Σ f : A.base ⟶ C.base,
        (Scheme.Modules.pullback (Object.schemeMap f)).obj C.module ⟶ A.module :=
  (Equiv.cast ((Classical.choice
      (exists_categoryData (B := B) (S := S) (hS := hS))).hom_type A C)).trans
    (Equiv.sigmaCongrRight fun f ↦
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Object.schemeMap f)).homEquiv C.module A.module |>.symm)

end Stacks.QCoh

end
