module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the sheaf of relative differentials on a site

A commutative square
```
O₁ ──a──▸ O₂
│          │
f₁         f₂
▼          ▼
O₁' ─a'─▸ O₂'
```
of morphisms of sheaves of commutative rings on a site induces a canonical morphism
`Ω_{O₂/O₁} ⟶ Ω_{O₂'/O₁'}` of sheaves of modules, linear over `O₂` once the target is restricted
along `f₂`. It carries the universal differential of a local section `x` to the differential of
its image `f₂(x)`, and this property determines it. These maps respect identities and
composition of squares.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite`: a morphism of sheaves of
  commutative rings, regarded as a morphism of the underlying sheaves of rings.
* `AlgebraicGeometry.SheafOfModules.DifferentialsMapData`: the data of the induced derivation,
  the induced morphism of sheaves of differentials, and the universal property that pins it
  down.
* `AlgebraicGeometry.SheafOfModules.functorialDifferentials`: that data, for every commutative
  square.
* `AlgebraicGeometry.SheafOfModules.mapDifferentials`: the induced morphism itself.

## Main results

* `AlgebraicGeometry.SheafOfModules.mapDifferentials_id_apply`: the morphism attached to an
  identity square is the identity on every local section.
* `AlgebraicGeometry.SheafOfModules.mapDifferentials_comp_apply`: the morphism attached to a
  composite of two squares is the composite of the two morphisms, on every local section.

## Implementation notes

The sheaf of relative differentials is `moduleOfDifferentialsOfSite`, the corepresenting object
of the functor of relative derivations, with `universalDerivationOfSite` its universal
derivation; nothing is constructed here that is not forced by that universal property. The
target sheaf of differentials is restricted along the upper horizontal morphism `f₂`, so the
canonical map is a morphism of modules over the source structure sheaf. Packaging the induced
derivation, the map, the factorisation and the uniqueness as one structure records the full
universal property rather than only the existence of a map.

The two functor laws are stated on local sections. This is deliberate: a bare equality of
morphisms would have to compare two iterated restrictions of scalars, which are equal only up
to the canonical comparison isomorphism, and choosing that identification would obscure the
assertion. Evaluated on sections, no such identification is needed and the full content of
functoriality is retained.

A closely related statement for *small* sites is
`Stacks.Sheaves.DifferentialsFunctorial.differentialMap` and its surrounding lemmas; those are
the chapter 17 form of this result and carry the Stacks 08RS tag.

## References

* [Stacks Project, Tag 08TR](https://stacks.math.columbia.edu/tag/08TR)
-/

@[expose] public section

open CategoryTheory

universe v u w m

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The morphism of underlying sheaves of rings associated to a morphism of sheaves of
commutative rings. -/
noncomputable abbrev underlyingRingHomOfSite {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O') :
    Stacks.SheafOfModules.Tensor.ringSheaf O ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O' :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f

/-- The data and universal characterisation of the morphism on relative differentials induced
by a commutative square of sheaves of commutative rings. -/
structure DifferentialsMapData {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{w}}
    (a : O₁ ⟶ O₂) (a' : O₁' ⟶ O₂') (f₁ : O₁ ⟶ O₁') (f₂ : O₂ ⟶ O₂')
    (sq : a ≫ f₂ = f₁ ≫ a') where
  /-- The composite of the upper horizontal map with the target universal derivation, regarded
  as a derivation over the lower-left sheaf. -/
  inducedDerivation :
    PresheafOfModulesOfCommRing.Derivation'
      ((_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite f₂)).obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' a')).val a.hom
  /-- On local sections, the induced derivation is the differential of the image. -/
  inducedDerivation_apply (X : Cᵒᵖ) (x : O₂.obj.obj X) :
    inducedDerivation.d x =
      (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d (f₂.hom.app X x)
  /-- The induced morphism of sheaves of modules. -/
  map : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a ⟶
    (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite f₂)).obj
      (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' a')
  /-- The morphism sends the universal derivation to the induced derivation. -/
  fac : (universalDerivationOfSite.{v, u, w, m} O₁ O₂ a).postcomp map.val = inducedDerivation
  /-- This property characterises the induced morphism uniquely. -/
  unique (g : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a ⟶
      (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite f₂)).obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' a'))
      (hg : (universalDerivationOfSite.{v, u, w, m} O₁ O₂ a).postcomp g.val =
        inducedDerivation) : g = map

/-- **Stacks 08TR.** The canonical morphism on sheaves of relative differentials associated to a
commutative square, together with its characterisation on local differentials. -/
@[stacks 08TR "the canonical map and uniqueness"]
noncomputable def functorialDifferentials {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{w}}
    (a : O₁ ⟶ O₂) (a' : O₁' ⟶ O₂') (f₁ : O₁ ⟶ O₁') (f₂ : O₂ ⟶ O₂')
    (sq : a ≫ f₂ = f₁ ≫ a') :
    DifferentialsMapData.{v, u, w, m} a a' f₁ f₂ sq := by
  let D : PresheafOfModulesOfCommRing.Derivation'
      ((_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite f₂)).obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' a')).val a.hom :=
    { d := fun {X} ↦ (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d.comp
          (f₂.hom.app X).hom.toAddMonoidHom
      d_mul := by
        intro X x y
        change (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d
            (f₂.hom.app X (x * y)) =
          (f₂.hom.app X x) •
              (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d (f₂.hom.app X y) +
            (f₂.hom.app X y) •
              (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d (f₂.hom.app X x)
        rw [map_mul, (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d_mul]
      d_map := by
        intro X Y g x
        change (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d
            (f₂.hom.app Y (O₂.obj.map g x)) =
          (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' a').val.map g
            ((universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d (f₂.hom.app X x))
        rw [f₂.hom.naturality_apply g x]
        exact (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d_map g (f₂.hom.app X x)
      d_app := by
        intro X x
        change (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d
          (f₂.hom.app X (a.hom.app X x)) = 0
        have h := congrArg (fun t : O₁ ⟶ O₂' ↦ t.hom.app X x) sq
        change f₂.hom.app X (a.hom.app X x) = a'.hom.app X (f₁.hom.app X x) at h
        rw [h]
        exact (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d_app (f₁.hom.app X x) }
  let e := (derivationsFunctor.{m} O₁ O₂ a).corepresentableBy
  have he (h : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a ⟶
      (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite f₂)).obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂' a')) :
      e.homEquiv h = (universalDerivationOfSite.{v, u, w, m} O₁ O₂ a).postcomp h.val := by
    rw [e.homEquiv_eq]
    rfl
  let mm := e.homEquiv.symm D
  exact
    { inducedDerivation := D
      inducedDerivation_apply := fun _ _ ↦ rfl
      map := mm
      fac := (he mm).symm.trans (e.homEquiv.apply_symm_apply D)
      unique := fun g hg ↦ e.homEquiv.injective
        ((he g).trans (hg.trans (e.homEquiv.apply_symm_apply D).symm)) }

/-- The canonical morphism on relative differentials associated to a commutative square. -/
noncomputable abbrev mapDifferentials {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{w}}
    (a : O₁ ⟶ O₂) (a' : O₁' ⟶ O₂') (f₁ : O₁ ⟶ O₁') (f₂ : O₂ ⟶ O₂')
    (sq : a ≫ f₂ = f₁ ≫ a') :=
  (functorialDifferentials.{v, u, w, m} a a' f₁ f₂ sq).map

/-- The induced map sends the differential of a local section to the differential of its image. -/
private theorem map_universalDerivation_apply {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{w}}
    {a : O₁ ⟶ O₂} {a' : O₁' ⟶ O₂'} {f₁ : O₁ ⟶ O₁'} {f₂ : O₂ ⟶ O₂'} {sq : a ≫ f₂ = f₁ ≫ a'}
    (d : DifferentialsMapData.{v, u, w, m} a a' f₁ f₂ sq) (Y : Cᵒᵖ) (y : O₂.obj.obj Y) :
    d.map.val.app Y ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ a).d y) =
      (universalDerivationOfSite.{v, u, w, m} O₁' O₂' a').d (f₂.hom.app Y y) := by
  rw [← d.inducedDerivation_apply]
  exact congrArg (fun D ↦ D.d y) d.fac

/-- The canonical map on differentials associated to the identity square is the identity on
every local section. -/
@[stacks 08TR "identity law"]
theorem mapDifferentials_id_apply {O₁ O₂ : Sheaf J CommRingCat.{w}} (a : O₁ ⟶ O₂)
    (X : Cᵒᵖ) (x : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a).val.obj X) :
    (mapDifferentials.{v, u, w, m} a a (𝟙 O₁) (𝟙 O₂) (by simp)).val.app X x = x := by
  let d := functorialDifferentials.{v, u, w, m} a a (𝟙 O₁) (𝟙 O₂) (by simp)
  have h : d.map = 𝟙 _ := by
    symm
    apply d.unique
    ext Y y
    show (universalDerivationOfSite.{v, u, w, m} O₁ O₂ a).d y = d.inducedDerivation.d y
    rw [d.inducedDerivation_apply]
    simp
  exact congrArg
    (fun f : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a ⟶ _ ↦ f.val.app X x) h

/-- Canonical maps on differentials respect composition of commutative squares, on every local
section. -/
@[stacks 08TR "composition law"]
theorem mapDifferentials_comp_apply {O₁ O₂ O₁' O₂' O₁'' O₂'' : Sheaf J CommRingCat.{w}}
    (a : O₁ ⟶ O₂) (a' : O₁' ⟶ O₂') (a'' : O₁'' ⟶ O₂'')
    (f₁ : O₁ ⟶ O₁') (f₂ : O₂ ⟶ O₂') (g₁ : O₁' ⟶ O₁'') (g₂ : O₂' ⟶ O₂'')
    (sqf : a ≫ f₂ = f₁ ≫ a') (sqg : a' ≫ g₂ = g₁ ≫ a'')
    (X : Cᵒᵖ) (x : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a).val.obj X) :
    (mapDifferentials.{v, u, w, m} a a'' (f₁ ≫ g₁) (f₂ ≫ g₂)
      (by
        calc
          a ≫ (f₂ ≫ g₂) = (a ≫ f₂) ≫ g₂ := (Category.assoc _ _ _).symm
          _ = (f₁ ≫ a') ≫ g₂ := by rw [sqf]
          _ = f₁ ≫ (a' ≫ g₂) := Category.assoc _ _ _
          _ = f₁ ≫ (g₁ ≫ a'') := by rw [sqg]
          _ = (f₁ ≫ g₁) ≫ a'' := (Category.assoc _ _ _).symm)).val.app X x =
      (mapDifferentials.{v, u, w, m} a' a'' g₁ g₂ sqg).val.app X
        ((mapDifferentials.{v, u, w, m} a a' f₁ f₂ sqf).val.app X x) := by
  let sf := functorialDifferentials.{v, u, w, m} a a' f₁ f₂ sqf
  let sg := functorialDifferentials.{v, u, w, m} a' a'' g₁ g₂ sqg
  let sc := functorialDifferentials.{v, u, w, m} a a'' (f₁ ≫ g₁) (f₂ ≫ g₂)
    (by rw [← Category.assoc, sqf, Category.assoc, sqg, ← Category.assoc])
  let h : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a ⟶
      (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite (f₂ ≫ g₂))).obj
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁'' O₂'' a'') :=
    sf.map ≫ (_root_.SheafOfModules.restrictScalars
      (underlyingRingHomOfSite f₂)).map sg.map
  have he : h = sc.map := by
    apply sc.unique
    ext Y y
    show (sg.map.val.app Y) ((sf.map.val.app Y)
      ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ a).d y)) = sc.inducedDerivation.d y
    rw [map_universalDerivation_apply, map_universalDerivation_apply, sc.inducedDerivation_apply]
    rfl
  exact (congrArg
    (fun t : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ a ⟶ _ ↦ t.val.app X x) he).symm

end AlgebraicGeometry.SheafOfModules

end
