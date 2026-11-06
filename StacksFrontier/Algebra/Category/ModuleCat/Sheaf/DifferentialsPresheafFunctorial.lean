module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of differentials of presheaves of rings on a space

Let `X` be a topological space. A commutative square of presheaves of commutative rings on
the site of opens of `X` induces a canonical morphism between the associated modules of
differentials, characterized by `d f ↦ d (φ f)` on local sections, and these morphisms
respect identities and composition of squares.

## Main definitions

* `SheafDifferentials.IsDerivation` and `SheafDifferentials.IsModuleOfDifferentials` name the
  Mathlib notions of a relative derivation and of a universal one.
* `SheafDifferentials.RingArrow` is the category of arrows of presheaves of commutative rings.
* `SheafDifferentials.compDeriv` composes a derivation with the upper horizontal morphism of a
  square.
* `SheafDifferentials.inducedMap` is the induced morphism of modules of differentials.

## Main results

* `SheafDifferentials.inducedMap_comp_d` and `SheafDifferentials.inducedMap_unique`: the
  induced morphism is the unique one sending `d f` to `d (φ f)`.
* `SheafDifferentials.inducedMap_id` and `SheafDifferentials.inducedMap_comp`: the identity
  and composition laws.

## Implementation notes

Everything here is at the level of *presheaves* of modules: the universal property used is
`PresheafOfModulesOfCommRing.Derivation.Universal`, which factors derivations with values in an
arbitrary presheaf of modules.

A presheaf of rings on `X` is a presheaf of commutative rings on the site of opens,
`(Opens X)ᵒᵖ ⥤ CommRingCat`; the sheaf condition is available as the predicate
`IsRingSheaf` but is nowhere used. A homomorphism `φ : O₁ → O₂` is recorded in the shape
`O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂` that `PresheafOfModulesOfCommRing.Derivation` expects; since
`(𝟭 _).op ⋙ O₂ = O₂`, this is a morphism of presheaves of commutative rings.
-/


@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace SheafDifferentials

variable {X : Type*} [TopologicalSpace X]

/-- The presheaves of commutative rings on the site of opens of `X`. -/
@[sga "3 I 3.1" "special case"]
abbrev PreRing (X : Type*) [TopologicalSpace X] := (Opens X)ᵒᵖ ⥤ CommRingCat

/-- The sheaf condition on a presheaf of commutative rings on the opens of `X`. -/
@[sga "4 II 6.3.2" "special case"]
abbrev IsRingSheaf (O : PreRing X) : Prop :=
  Presheaf.IsSheaf (Opens.grothendieckTopology X) O

/-- For a homomorphism of presheaves of rings `φ : O₁ ⟶ O₂` (here `O₁ ⟶ (𝟭 _).op ⋙ O₂`) and an
`O₂`-module `M`, an `O₁`-derivation `O₂ → M` is `M.Derivation φ`: a morphism of presheaves of
sets `D : O₂ → M` that is additive, satisfies the Leibniz rule, and annihilates the image
of `O₁`. -/
@[ega "IV 16.5.1" "more general",
  sga "3 VIIA 1.2.0" "more general",
  sga "3 VIIA 5.2" "more general"]
abbrev IsDerivation {O₁ O₂ : PreRing X} (φ : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂)
    (M : PresheafOfModules (O₂ ⋙ forget₂ CommRingCat RingCat)) : Type _ :=
  PresheafOfModulesOfCommRing.Derivation M φ

/-- `Ω` (with derivation `d : Ω.Derivation φ`) is *the* module of differentials of `O₂` over
`O₁` exactly when `d` is universal, i.e. `d.Universal`: every `O₁`-derivation
`D : M.Derivation φ` factors uniquely through `d` via a module homomorphism `Ω ⟶ M`. This
is the representability of the functor `M ↦ Der_{O₁}(O₂, M)`. -/
abbrev IsModuleOfDifferentials {O₁ O₂ : PreRing X} {φ : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂}
    {Ω : PresheafOfModules (O₂ ⋙ forget₂ CommRingCat RingCat)}
    (d : PresheafOfModulesOfCommRing.Derivation Ω φ) : Type _ :=
  d.Universal

/-- The category of arrows of `PreRing X`: objects are homomorphisms `φ : O₁ ⟶ O₂` of presheaves
of rings, and a morphism `(φ) ⟶ (φ')` is a commutative square, i.e. a pair `(ψ₁, ψ₂)` with
`ψ₂ ∘ φ = φ' ∘ ψ₁`. -/
abbrev RingArrow (X : Type*) [TopologicalSpace X] := CategoryTheory.Arrow (PreRing X)

/-- A morphism of presheaves of commutative rings, whiskered with the forgetful functor to
`RingCat`, as a morphism of `RingCat`-valued presheaves. -/
abbrev φR {A B : PreRing X} (φ : A ⟶ B) := Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

/-- Restriction of scalars: an `O₂'`-module `Ω'` viewed as an `O₂`-module along
`φ : O₂ ⟶ O₂'`. The underlying objects and restriction maps are unchanged; only the module
structure is pulled back along `φ`. -/
@[sga "4 IV 11.1.4" "special case"]
abbrev Ωres {A B : PreRing X} (φ : A ⟶ B)
    (Ω : PresheafOfModules (B ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules (A ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.restrictScalars (φR φ)).obj Ω

/-- Given a commutative square of presheaves of rings
```
  O₂ --φ--> O₂'
  ↑ι        ↑ι'
  O₁ --ψ--> O₁'
```
(commutativity: `ι ≫ φ = ψ ≫ ι'`), and the `O₁'`-derivation `d' : Ω'.Derivation ι'`, the
composite `d' ∘ φ : O₂ → Ω'` (with `Ω'` viewed as an `O₂`-module via `φ`, i.e. `Ωres φ Ω'`)
is an `O₁`-derivation. -/
def compDeriv {O₁ O₂ O₁' O₂' : PreRing X}
    {ι : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂} {ι' : O₁' ⟶ (𝟭 (Opens X)).op ⋙ O₂'}
    {Ω' : PresheafOfModules (O₂' ⋙ forget₂ CommRingCat RingCat)}
    (d' : PresheafOfModulesOfCommRing.Derivation Ω' ι') (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁')
    (hcomm : ι ≫ φ = ψ ≫ ι') : PresheafOfModulesOfCommRing.Derivation (Ωres φ Ω') ι where
  d {U} := (d'.d (X := U)).comp ((φ.app U).hom : (O₂.obj U) →+* (O₂'.obj U)).toAddMonoidHom
  d_mul {U} a b :=
    (congrArg (fun z => d'.d z) (map_mul (φ.app U).hom a b)).trans (d'.d_mul _ _)
  d_map {U V} f x := by
    have heq : (φ.app V).hom ((O₂.map f).hom x) = (O₂'.map f).hom ((φ.app U).hom x) := by
      simpa only [CommRingCat.comp_apply] using
        congrArg (fun (g : O₂.obj U ⟶ O₂'.obj V) => g.hom x) (φ.naturality f)
    exact (congrArg (fun z => d'.d z) heq).trans (d'.d_map _ _)
  d_app {U} a := by
    have hc : (φ.app U).hom ((ι.app U).hom a) = (ι'.app U).hom ((ψ.app U).hom a) := by
      simpa only [NatTrans.comp_app, CommRingCat.comp_apply] using
        congrArg (fun (g : O₁.obj U ⟶ O₂'.obj U) => g.hom a)
          (congrFun (congrArg NatTrans.app hcomm) U)
    exact (congrArg (fun z => d'.d z) hc).trans (d'.d_app _)

/-- The additive map underlying `compDeriv` is exactly `f ↦ d'(φ f)`. -/
theorem compDeriv_d {O₁ O₂ O₁' O₂' : PreRing X}
    {ι : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂} {ι' : O₁' ⟶ (𝟭 (Opens X)).op ⋙ O₂'}
    {Ω' : PresheafOfModules (O₂' ⋙ forget₂ CommRingCat RingCat)}
    (d' : PresheafOfModulesOfCommRing.Derivation Ω' ι') (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁')
    (hcomm : ι ≫ φ = ψ ≫ ι') {U : (Opens X)ᵒᵖ} (f : O₂.obj U) :
    (compDeriv d' φ ψ hcomm).d f = d'.d ((φ.app U).hom f) := rfl

/-- The canonical `O₂`-module homomorphism `Ω(ψ,φ) : Ω_{O₂/O₁} ⟶ Ω_{O₂'/O₁'}` (the latter
viewed as an `O₂`-module via `φ`), obtained from the universal property of `Ω_{O₂/O₁}`
applied to the derivation `SheafDifferentials.compDeriv d' φ ψ hcomm`. -/
@[ega "0 21.3.2" "more general"]
def inducedMap {O₁ O₂ O₁' O₂' : PreRing X}
    {ι : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂} {ι' : O₁' ⟶ (𝟭 (Opens X)).op ⋙ O₂'}
    {Ω : PresheafOfModules (O₂ ⋙ forget₂ CommRingCat RingCat)}
    {Ω' : PresheafOfModules (O₂' ⋙ forget₂ CommRingCat RingCat)}
    {d : PresheafOfModulesOfCommRing.Derivation Ω ι} (hΩ : d.Universal)
    (d' : PresheafOfModulesOfCommRing.Derivation Ω' ι')
    (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι') :
    Ω ⟶ Ωres φ Ω' :=
  hΩ.desc (compDeriv d' φ ψ hcomm)

/-- The induced map `Ω(ψ,φ)` satisfies `Ω(ψ,φ)(d f) = d'(φ f)` for every local section `f`
of `O₂`. -/
theorem inducedMap_comp_d {O₁ O₂ O₁' O₂' : PreRing X}
    {ι : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂} {ι' : O₁' ⟶ (𝟭 (Opens X)).op ⋙ O₂'}
    {Ω : PresheafOfModules (O₂ ⋙ forget₂ CommRingCat RingCat)}
    {Ω' : PresheafOfModules (O₂' ⋙ forget₂ CommRingCat RingCat)}
    {d : PresheafOfModulesOfCommRing.Derivation Ω ι} (hΩ : d.Universal)
    (d' : PresheafOfModulesOfCommRing.Derivation Ω' ι')
    (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι')
    {U : (Opens X)ᵒᵖ} (f : O₂.obj U) :
    (ConcreteCategory.hom ((inducedMap hΩ d' φ ψ hcomm).app U)) (d.d f)
      = d'.d ((φ.app U).hom f) :=
  congrArg (fun (D : PresheafOfModulesOfCommRing.Derivation (Ωres φ Ω') ι) => D.d (X := U) f)
    (hΩ.fac (compDeriv d' φ ψ hcomm))

/-- Any `O₂`-module homomorphism `β : Ω ⟶ Ωres φ Ω'`
satisfying the characterizing equation `β(d f) = d'(φ f)` equals the induced map. -/
theorem inducedMap_unique {O₁ O₂ O₁' O₂' : PreRing X}
    {ι : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂} {ι' : O₁' ⟶ (𝟭 (Opens X)).op ⋙ O₂'}
    {Ω : PresheafOfModules (O₂ ⋙ forget₂ CommRingCat RingCat)}
    {Ω' : PresheafOfModules (O₂' ⋙ forget₂ CommRingCat RingCat)}
    {d : PresheafOfModulesOfCommRing.Derivation Ω ι} (hΩ : d.Universal)
    (d' : PresheafOfModulesOfCommRing.Derivation Ω' ι')
    (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι')
    (β : Ω ⟶ Ωres φ Ω')
    (hβ : ∀ {U : (Opens X)ᵒᵖ} (f : O₂.obj U),
      (ConcreteCategory.hom (β.app U)) (d.d f) = d'.d ((φ.app U).hom f)) :
    β = inducedMap hΩ d' φ ψ hcomm := by
  apply hΩ.postcomp_injective
  rw [inducedMap, hΩ.fac]
  ext U f
  exact hβ f

/-- For the identity morphism `(id, id)` of an object `ι : O₁ ⟶ O₂`, the induced map is the
identity on `Ω_{O₂/O₁}`. (Here `φ = 𝟙 O₂`, `ψ = 𝟙 O₁`, and `Ωres (𝟙 O₂) Ω = Ω`.) -/
theorem inducedMap_id {O₁ O₂ : PreRing X}
    {ι : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂}
    {Ω : PresheafOfModules (O₂ ⋙ forget₂ CommRingCat RingCat)}
    {d : PresheafOfModulesOfCommRing.Derivation Ω ι} (hΩ : d.Universal)
    (hcomm : ι ≫ 𝟙 O₂ = 𝟙 O₁ ≫ ι) :
    inducedMap hΩ d (𝟙 O₂) (𝟙 O₁) hcomm = 𝟙 Ω :=
  (inducedMap_unique hΩ d (𝟙 O₂) (𝟙 O₁) hcomm (𝟙 Ω) fun _ => rfl).symm

/-- Given two composable morphisms of arrows
```
  (ι : O₁ → O₂) --(ψ,φ)--> (ι' : O₁' → O₂') --(ψ',φ')--> (ι'' : O₁'' → O₂'')
```
the induced maps satisfy `Ω(ψ' ∘ ψ, φ' ∘ φ) = Ω(ψ', φ') ∘ Ω(ψ, φ)` as maps
`Ω_{O₂/O₁} ⟶ Ω_{O₂''/O₁''}`.

Because `Ω(ψ', φ')` is an `O₂'`-module map and `Ω(ψ, φ)` an `O₂`-module map, the right-hand
side composes them after restricting `Ω(ψ', φ')` along `φ` (functor
`PresheafOfModules.restrictScalars (φR φ)`); note `Ωres φ (Ωres φ' Ω'') = Ωres (φ ≫ φ') Ω''`
definitionally, so the composite has the same target as the left-hand side. -/
theorem inducedMap_comp {O₁ O₂ O₁' O₂' O₁'' O₂'' : PreRing X}
    {ι : O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂} {ι' : O₁' ⟶ (𝟭 (Opens X)).op ⋙ O₂'}
    {ι'' : O₁'' ⟶ (𝟭 (Opens X)).op ⋙ O₂''}
    {Ω : PresheafOfModules (O₂ ⋙ forget₂ CommRingCat RingCat)}
    {Ω' : PresheafOfModules (O₂' ⋙ forget₂ CommRingCat RingCat)}
    {Ω'' : PresheafOfModules (O₂'' ⋙ forget₂ CommRingCat RingCat)}
    {d : PresheafOfModulesOfCommRing.Derivation Ω ι} (hΩ : d.Universal)
    {d' : PresheafOfModulesOfCommRing.Derivation Ω' ι'} (hΩ' : d'.Universal)
    (d'' : PresheafOfModulesOfCommRing.Derivation Ω'' ι'')
    (ψ : O₁ ⟶ O₁') (φ : O₂ ⟶ O₂') (hcomm : ι ≫ φ = ψ ≫ ι')
    (ψ' : O₁' ⟶ O₁'') (φ' : O₂' ⟶ O₂'') (hcomm' : ι' ≫ φ' = ψ' ≫ ι'')
    (hcomm'' : ι ≫ (φ ≫ φ') = (ψ ≫ ψ') ≫ ι'') :
    inducedMap hΩ d'' (φ ≫ φ') (ψ ≫ ψ') hcomm''
      = inducedMap hΩ d' φ ψ hcomm ≫
          (PresheafOfModules.restrictScalars (φR φ)).map (inducedMap hΩ' d'' φ' ψ' hcomm') := by
  symm
  refine inducedMap_unique hΩ d'' (φ ≫ φ') (ψ ≫ ψ') hcomm'' _ ?_
  intro U f
  have h1 := inducedMap_comp_d hΩ d' φ ψ hcomm (U := U) f
  have h2 := inducedMap_comp_d hΩ' d'' φ' ψ' hcomm' (U := U) ((φ.app U).hom f)
  show (ConcreteCategory.hom ((inducedMap hΩ' d'' φ' ψ' hcomm').app U))
      ((ConcreteCategory.hom ((inducedMap hΩ d' φ ψ hcomm).app U)) (d.d f)) = _
  rw [h1, h2]
  rfl

end SheafDifferentials
