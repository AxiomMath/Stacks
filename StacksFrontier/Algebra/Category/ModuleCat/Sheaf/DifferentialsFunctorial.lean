module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Comma.Arrow
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsRepresentable
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the sheaf of relative differentials

Given a commutative square of morphisms of sheaves of commutative rings on a small site,
there is a canonical morphism between the associated sheaves of relative differentials.

## Main definitions

* `compDeriv` composes a relative derivation with a morphism of sheaves of commutative rings
  to produce a relative derivation for the other side of the square.
* `differentialMap` is the canonical morphism of sheaves of modules between the sheaves of
  relative differentials attached to the two sides of a commutative square.
* `sheafOfModulesFunctor` and `arrowModulesFunctor` are the categories of sheaves of modules
  over a varying sheaf of rings, as contravariant functors to `Cat`, and `ArrowModules` is
  the total category of the second one.
* `differentialsArrowFunctor` is the functor on the category of arrows of sheaves of
  commutative rings sending an arrow to its sheaf of relative differentials.

## Main results

* `differentialMap_comp_d` is the characterizing property of `differentialMap`.
* `differentialMap_unique` says that property determines `differentialMap`.
* `differentialMap_id` and `differentialMap_comp` are the identity and composition laws,
  from which `differentialsArrowFunctor` is assembled.

## Implementation notes

The construction is driven by the universal property of the sheaf of relative differentials
proved in `Stacks.Sheaves.Differentials.universalDerivation_isUniversal`. That universal
property only descends derivations with values in a *sheaf* of modules, so the
presheaf-level construction of `SheafDifferentials.inducedMap` cannot be reused; the
structure of the argument is the same, but every factorization goes through
`universalDerivation_isUniversal`.

This file carries [Stacks Project, Tag 08RS](https://stacks.math.columbia.edu/tag/08RS)
(Lemma 17.28.8), for genuine sheaves of modules on an arbitrary small site, which is the
level at which `Stacks.Sheaves.Differentials.moduleOfDifferentials` — the `Ω_{O₂/O₁}` of the
chapter — is defined. `SheafDifferentials.inducedMap` is the same construction for
*presheaves* of modules, whose universal property quantifies over presheaves only, so it
does not give the statement for that `Ω`; it is an untagged helper.

Tag 08RS is one of the two inputs to
[Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU) (Lemma 17.28.12), but
it is not that lemma: 08RU is about a commutative diagram of ringed spaces and produces the
comparison map `f^*Ω_{X/S} ⟶ Ω_{X'/S'}`, which additionally needs the pushforward/pullback
adjunction along a continuous map.

The functor of the last sentence of 08RS cannot have a single module category as target,
because the ring over which `Ω` is linear is the upper-right corner of the arrow and so
varies with the object. The target is therefore the total category of the pseudofunctor
sending an arrow `ι : O₁ ⟶ O₂` to the category of sheaves of `O₂`-modules, with restriction
of scalars for its contravariant functoriality: `CategoryTheory.Pseudofunctor.CoGrothendieck`
of that pseudofunctor, whose morphisms `(ι, M) ⟶ (ι', M')` are a morphism of arrows together
with a morphism `M ⟶ M'` of modules over the source — exactly the shape of
`differentialMap`.

Restriction of scalars for sheaves of modules is in fact *strictly* functorial, so the
pseudofunctor is obtained from an honest functor to `Cat` by `Functor.toPseudofunctor'` and
its unitors are definitionally identities; that is why the two functor laws reduce to
`differentialMap_id` and `differentialMap_comp` followed by `rfl`. The fiber object and the
fiber morphism are given names, `arrowDifferentials` and `arrowDifferentialsMap`, carrying
the types the total category expects: `Pseudofunctor.obj` does not unfold at reduced
transparency, so without them the functor-law goals are not type-correct for `rw` and `simp`.

## References

* [Stacks Project, Tag 08RS](https://stacks.math.columbia.edu/tag/08RS)
* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Sheaves.DifferentialsFunctorial

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- A morphism of sheaves of commutative rings, regarded as a morphism of sheaves of rings. -/
noncomputable abbrev ringMap {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O') :
    Differentials.underlyingRingSheaf O ⟶ Differentials.underlyingRingSheaf O' :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

/-- Restriction of scalars along `φ : O ⟶ O'`: a sheaf of `O'`-modules regarded as a sheaf
of `O`-modules. The underlying presheaf of abelian groups is unchanged. -/
noncomputable abbrev restrictAlong {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (F : SheafOfModules.{u} (Differentials.underlyingRingSheaf O')) :
    SheafOfModules.{u} (Differentials.underlyingRingSheaf O) :=
  (SheafOfModules.restrictScalars (ringMap φ)).obj F

section CompDeriv

variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{u}} {ι : O₁ ⟶ O₂} {ι' : O₁' ⟶ O₂'}

/-- Given a commutative square of sheaves of commutative rings
```
  O₂ --φ--> O₂'
  ↑ι        ↑ι'
  O₁ --ψ--> O₁'
```
and a relative `ι'`-derivation `d'` with values in a sheaf of `O₂'`-modules `F`, the
composite `d' ∘ φ` is a relative `ι`-derivation with values in `F` regarded as a sheaf of
`O₂`-modules by restriction of scalars along `φ`. -/
@[stacks 08RS "the composite of O_2 -> O_2' with d is an O_1-derivation"]
noncomputable def compDeriv {F : SheafOfModules.{u} (Differentials.underlyingRingSheaf O₂')}
    (d' : Differentials.SheafDerivation O₁' O₂' ι' F) (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁')
    (hcomm : ι ≫ φ = ψ ≫ ι') :
    Differentials.SheafDerivation O₁ O₂ ι (restrictAlong φ F) where
  d {U} := (d'.d (X := U)).comp
    ((φ.hom.app U).hom : (O₂.obj.obj U) →+* (O₂'.obj.obj U)).toAddMonoidHom
  d_mul {U} a b := by
    change d'.d ((φ.hom.app U).hom (a * b)) = _
    rw [map_mul, d'.d_mul]
    rfl
  d_map {U V} f x := by
    change d'.d ((φ.hom.app V).hom ((O₂.obj.map f).hom x)) = _
    have heq : (φ.hom.app V).hom ((O₂.obj.map f).hom x)
        = (O₂'.obj.map f).hom ((φ.hom.app U).hom x) := by
      simpa only [CommRingCat.comp_apply] using
        congrArg (fun (g : O₂.obj.obj U ⟶ O₂'.obj.obj V) => g.hom x) (φ.hom.naturality f)
    rw [heq]
    exact d'.d_map f _
  d_app {U} a := by
    change d'.d ((φ.hom.app U).hom ((ι.hom.app U).hom a)) = 0
    have hc : (φ.hom.app U).hom ((ι.hom.app U).hom a)
        = (ι'.hom.app U).hom ((ψ.hom.app U).hom a) := by
      simpa only [NatTrans.comp_app, CommRingCat.comp_apply] using
        congrArg (fun (g : O₁.obj.obj U ⟶ O₂'.obj.obj U) => g.hom a)
          (congrFun (congrArg NatTrans.app
            (Sheaf.hom_ext_iff.mp hcomm : ι.hom ≫ φ.hom = ψ.hom ≫ ι'.hom)) U)
    rw [hc]
    exact d'.d_app _

/-- The additive map underlying `compDeriv` is exactly `a ↦ d' (φ a)`. -/
theorem compDeriv_d {F : SheafOfModules.{u} (Differentials.underlyingRingSheaf O₂')}
    (d' : Differentials.SheafDerivation O₁' O₂' ι' F) (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁')
    (hcomm : ι ≫ φ = ψ ≫ ι') {U : Cᵒᵖ} (a : O₂.obj.obj U) :
    (compDeriv d' φ ψ hcomm).d a = d'.d ((φ.hom.app U).hom a) := rfl

end CompDeriv

section DifferentialMap

variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{u}}

/-- The universal property of the sheaf of relative differentials, applied to the derivation
`compDeriv`: there is a unique morphism of sheaves of modules from `Ω_{O₂/O₁}` to
`Ω_{O₂'/O₁'}` (restricted along `φ`) compatible with the universal derivations. -/
theorem existsUnique_differentialMap (ι : O₁ ⟶ O₂) (ι' : O₁' ⟶ O₂') (φ : O₂ ⟶ O₂')
    (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι') :
    ∃! f : Differentials.moduleOfDifferentials O₁ O₂ ι ⟶
        restrictAlong φ (Differentials.moduleOfDifferentials O₁' O₂' ι'),
      (Differentials.universalDerivation O₁ O₂ ι).postcomp f.val
        = compDeriv (Differentials.universalDerivation O₁' O₂' ι') φ ψ hcomm :=
  Differentials.universalDerivation_isUniversal O₁ O₂ ι _
    (compDeriv (Differentials.universalDerivation O₁' O₂' ι') φ ψ hcomm)

/-- The canonical morphism of sheaves of modules between the sheaves of relative
differentials attached to a commutative square
```
  O₂ --φ--> O₂'
  ↑ι        ↑ι'
  O₁ --ψ--> O₁'
```
of sheaves of commutative rings. It goes from `Ω_{O₂/O₁}` to `Ω_{O₂'/O₁'}` regarded as a
sheaf of `O₂`-modules by restriction of scalars along `φ`, and is characterized by
`differentialMap_comp_d`. -/
@[stacks 08RS "the canonical map of O_2-modules Omega_{O_2/O_1} -> Omega_{O_2'/O_1'}",
  ega "0 20.5.2" "(20.5.2.3) map u''"]
noncomputable def differentialMap (ι : O₁ ⟶ O₂) (ι' : O₁' ⟶ O₂') (φ : O₂ ⟶ O₂')
    (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι') :
    Differentials.moduleOfDifferentials O₁ O₂ ι ⟶
      restrictAlong φ (Differentials.moduleOfDifferentials O₁' O₂' ι') :=
  Exists.choose (existsUnique_differentialMap ι ι' φ ψ hcomm)

/-- `differentialMap` turns the universal derivation of `Ω_{O₂/O₁}` into the composite of
the universal derivation of `Ω_{O₂'/O₁'}` with `φ`. -/
theorem universalDerivation_postcomp_differentialMap (ι : O₁ ⟶ O₂) (ι' : O₁' ⟶ O₂')
    (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι') :
    (Differentials.universalDerivation O₁ O₂ ι).postcomp
        (differentialMap ι ι' φ ψ hcomm).val
      = compDeriv (Differentials.universalDerivation O₁' O₂' ι') φ ψ hcomm :=
  (Exists.choose_spec (existsUnique_differentialMap ι ι' φ ψ hcomm)).1

/-- The characterizing property of `differentialMap`: on local sections it sends `d a` to
`d' (φ a)`, where `d` and `d'` are the universal derivations of `Ω_{O₂/O₁}` and
`Ω_{O₂'/O₁'}`. -/
@[stacks 08RS "the characterizing property d(f) |-> d(phi f) on local sections"]
theorem differentialMap_comp_d (ι : O₁ ⟶ O₂) (ι' : O₁' ⟶ O₂') (φ : O₂ ⟶ O₂')
    (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι') {U : Cᵒᵖ} (a : O₂.obj.obj U) :
    ((differentialMap ι ι' φ ψ hcomm).val.app U).hom
        ((Differentials.universalDerivation O₁ O₂ ι).d a)
      = (Differentials.universalDerivation O₁' O₂' ι').d ((φ.hom.app U).hom a) :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (universalDerivation_postcomp_differentialMap ι ι' φ ψ hcomm) a

/-- Uniqueness: a morphism of sheaves of modules satisfying the characterizing property of
`differentialMap` is `differentialMap`. -/
@[stacks 08RS "the canonical map is uniquely characterized by that property"]
theorem differentialMap_unique (ι : O₁ ⟶ O₂) (ι' : O₁' ⟶ O₂') (φ : O₂ ⟶ O₂')
    (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι')
    (β : Differentials.moduleOfDifferentials O₁ O₂ ι ⟶
      restrictAlong φ (Differentials.moduleOfDifferentials O₁' O₂' ι'))
    (hβ : ∀ {U : Cᵒᵖ} (a : O₂.obj.obj U), (β.val.app U).hom
        ((Differentials.universalDerivation O₁ O₂ ι).d a)
      = (Differentials.universalDerivation O₁' O₂' ι').d ((φ.hom.app U).hom a)) :
    β = differentialMap ι ι' φ ψ hcomm := by
  refine (Exists.choose_spec (existsUnique_differentialMap ι ι' φ ψ hcomm)).2 β ?_
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U a
  exact hβ a

/-- Functoriality, identities: the canonical map attached to the identity square of
`ι : O₁ ⟶ O₂` is the identity of `Ω_{O₂/O₁}`. -/
theorem differentialMap_id (ι : O₁ ⟶ O₂) (hcomm : ι ≫ 𝟙 O₂ = 𝟙 O₁ ≫ ι) :
    differentialMap ι ι (𝟙 O₂) (𝟙 O₁) hcomm
      = 𝟙 (Differentials.moduleOfDifferentials O₁ O₂ ι) :=
  (differentialMap_unique ι ι (𝟙 O₂) (𝟙 O₁) hcomm (𝟙 _) (fun _ ↦ rfl)).symm

/-- Functoriality, composition: the canonical map attached to a composite of two
commutative squares is the composite of the canonical maps. -/
theorem differentialMap_comp {O₁'' O₂'' : Sheaf J CommRingCat.{u}}
    (ι : O₁ ⟶ O₂) (ι' : O₁' ⟶ O₂') (ι'' : O₁'' ⟶ O₂'')
    (φ : O₂ ⟶ O₂') (ψ : O₁ ⟶ O₁') (hcomm : ι ≫ φ = ψ ≫ ι')
    (φ' : O₂' ⟶ O₂'') (ψ' : O₁' ⟶ O₁'') (hcomm' : ι' ≫ φ' = ψ' ≫ ι'')
    (hcomm'' : ι ≫ (φ ≫ φ') = (ψ ≫ ψ') ≫ ι'') :
    differentialMap ι ι'' (φ ≫ φ') (ψ ≫ ψ') hcomm''
      = differentialMap ι ι' φ ψ hcomm ≫
        (SheafOfModules.restrictScalars (ringMap φ)).map
          (differentialMap ι' ι'' φ' ψ' hcomm') := by
  symm
  refine differentialMap_unique ι ι'' (φ ≫ φ') (ψ ≫ ψ') hcomm'' _ ?_
  intro U a
  show ((differentialMap ι' ι'' φ' ψ' hcomm').val.app U).hom
      (((differentialMap ι ι' φ ψ hcomm).val.app U).hom
        ((Differentials.universalDerivation O₁ O₂ ι).d a)) = _
  rw [differentialMap_comp_d ι ι' φ ψ hcomm a,
    differentialMap_comp_d ι' ι'' φ' ψ' hcomm' ((φ.hom.app U).hom a)]
  rfl

end DifferentialMap

section ArrowFunctor

/-- Sheaves of modules over a varying sheaf of rings, as a contravariant functor to `Cat`.
Restriction of scalars is *strictly* functorial — `restrictScalars (𝟙 R) = 𝟭` and
`restrictScalars (α ≫ β) = restrictScalars β ⋙ restrictScalars α` hold by definition — so
this is a genuine functor, not merely a pseudofunctor. -/
@[ega "0 4.2.5" "more general", sga "4 XVIII 3.1.12.1"]
noncomputable def sheafOfModulesFunctor :
    (Sheaf J RingCat.{u})ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj R := Cat.of (SheafOfModules.{u} R.unop)
  map α := (SheafOfModules.restrictScalars α.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sheaves of modules over the target of an arrow of sheaves of commutative rings, as a
contravariant functor to `Cat`. Its total category is where the relative differentials take
their values. -/
noncomputable abbrev arrowModulesFunctor :
    (CategoryTheory.Arrow (Sheaf J CommRingCat.{u}))ᵒᵖ ⥤ Cat.{u, u + 1} :=
  (Arrow.rightFunc ⋙ sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).op ⋙
    sheafOfModulesFunctor

/-- The total category of `arrowModulesFunctor`: an object is an arrow `ι : O₁ ⟶ O₂` of
sheaves of commutative rings together with a sheaf of `O₂`-modules, and a morphism
`(ι, M) ⟶ (ι', M')` is a commutative square `(ψ, φ)` of sheaves of rings together with a
morphism `M ⟶ M'` of sheaves of `O₂`-modules, the scalars of `M'` being restricted along
`φ`. -/
noncomputable abbrev ArrowModules (K : GrothendieckTopology C)
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] :=
  Pseudofunctor.CoGrothendieck (arrowModulesFunctor (J := K)).toPseudofunctor'

/-- `Ω_{O₂/O₁}` read as an object of the fiber of `arrowModulesFunctor` over the arrow
`ι : O₁ ⟶ O₂`. Giving the fiber object this type, rather than the type
`SheafOfModules (underlyingRingSheaf O₂)` that `moduleOfDifferentials` has on the nose, is
what makes the functor laws below statable: `Pseudofunctor.obj` does not unfold at reduced
transparency, so a goal mentioning the fiber has to be type-correct already. -/
noncomputable def arrowDifferentials (a : CategoryTheory.Arrow (Sheaf J CommRingCat.{u})) :
    arrowModulesFunctor.toPseudofunctor'.obj ⟨Opposite.op a⟩ :=
  Differentials.moduleOfDifferentials a.left a.right a.hom

/-- `differentialMap` read as a morphism in the fiber of `arrowModulesFunctor` over the
source arrow. -/
noncomputable def arrowDifferentialsMap
    {a b : CategoryTheory.Arrow (Sheaf J CommRingCat.{u})} (u : a ⟶ b) :
    arrowDifferentials a ⟶
      (arrowModulesFunctor.toPseudofunctor'.map u.op.toLoc).toFunctor.obj
        (arrowDifferentials b) :=
  differentialMap a.hom b.hom u.right u.left u.w.symm

/-- The identity law for `arrowDifferentialsMap`, from `differentialMap_id`. -/
theorem arrowDifferentialsMap_id (a : CategoryTheory.Arrow (Sheaf J CommRingCat.{u})) :
    arrowDifferentialsMap (𝟙 a) = 𝟙 (arrowDifferentials a) :=
  differentialMap_id a.hom _

/-- The composition law for `arrowDifferentialsMap`, from `differentialMap_comp`. -/
theorem arrowDifferentialsMap_comp {a b c : CategoryTheory.Arrow (Sheaf J CommRingCat.{u})}
    (u : a ⟶ b) (v : b ⟶ c) :
    arrowDifferentialsMap (u ≫ v) = arrowDifferentialsMap u ≫
      (arrowModulesFunctor.toPseudofunctor'.map u.op.toLoc).toFunctor.map
        (arrowDifferentialsMap v) :=
  differentialMap_comp a.hom b.hom c.hom u.right u.left u.w.symm v.right v.left v.w.symm _

/-- **Stacks Project, Tag 08RS.** The relative differentials as a functor on the category of
arrows of sheaves of commutative rings: an arrow `ι : O₁ ⟶ O₂` is sent to `Ω_{O₂/O₁}` and a
commutative square to the canonical map `differentialMap`, the identity and composition laws
being `differentialMap_id` and `differentialMap_comp`.

The target is the total category `ArrowModules` rather than a fixed category of modules,
because the sheaf of rings over which `Ω_{O₂/O₁}` is linear is `O₂`, which varies with the
arrow. -/
@[stacks 08RS "a functor on the category of arrows of sheaves of rings"]
noncomputable def differentialsArrowFunctor :
    CategoryTheory.Arrow (Sheaf J CommRingCat.{u}) ⥤ ArrowModules J where
  obj a := { base := a, fiber := arrowDifferentials a }
  map u := { base := u, fiber := arrowDifferentialsMap u }
  map_id a := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
    rw [arrowDifferentialsMap_id]
    rfl
  map_comp u v := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
    rw [arrowDifferentialsMap_comp]
    rfl

end ArrowFunctor

end Stacks.Sheaves.DifferentialsFunctorial

end
