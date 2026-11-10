module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Quasi-coherent modules on a category fibred in groupoids representable by an algebraic space

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`X`. Restriction to the small étale site of `X` (equation 075K of Stacks 073M, read on sheaves of
modules) carries quasi-coherent modules on `𝒳`, under a hypothesis, to quasi-coherent modules on
`X`. This file shows that the resulting functor

```
QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X),   ℱ ↦ ℱ|_{X_étale}
```

is an equivalence with quasi-inverse `𝒢 ↦ π_X^*𝒢`, given that the counit of `π_X^* ⊣ i_X^*` is
an isomorphism at the quasi-coherent modules, and that the equivalence is compatible with
pullback along a 1-morphism, given the comparison of the two direct images (Stacks 0GQD).

## Main definitions

* `AlgebraicGeometry.Space.restrictionStructureHom`: the identification `i_X^{-1}𝒪_𝒳 = 𝒪_X` of
  structure sheaves, as a homomorphism of sheaves of (not necessarily commutative) rings.
* `AlgebraicGeometry.Space.moduleRestriction`: the restriction `ℱ ↦ ℱ|_{X_étale}` of an
  `𝒪_𝒳`-module on the inherited étale site of `𝒳` to an `𝒪_X`-module on the small étale site of
  `X`.
* `AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent`: the assertion that restriction
  carries quasi-coherent modules to quasi-coherent modules.
* `AlgebraicGeometry.Space.quasicoherentRestriction`: the comparison functor
  `QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.isIso_restrictionStructureHom`: the identification of structure
  sheaves is an isomorphism.
* `AlgebraicGeometry.Space.moduleRestriction_obj_val_presheaf_obj`: the sections of
  `ℱ|_{X_étale}` over an étale chart `U` of `X` are the sections of `ℱ` over the object `u_X U`
  of `𝒳`.
* `AlgebraicGeometry.Space.quasicoherentRestriction_comp_ι`: the comparison functor followed by
  the inclusion of the quasi-coherent modules is restriction.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction`: the comparison functor is an
  equivalence, given a left adjoint of restriction whose unit and counit are isomorphisms at the
  quasi-coherent modules.
* `AlgebraicGeometry.Space.nonempty_inv_iso_quasicoherentInverse`: its quasi-inverse is
  `𝒢 ↦ π_X^*𝒢`.
* `AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction`: restriction is a right adjoint at
  the module universe `max (u + 1) w m`.
* `AlgebraicGeometry.Space.isIso_unit_moduleRestriction`: the unit of every adjunction
  `P ⊣ i_X^*` is an isomorphism at that module universe.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_hcounit`: the comparison
  functor is an equivalence at that module universe, given that the counit is an isomorphism at
  the quasi-coherent modules.
* `AlgebraicGeometry.Space.nonempty_projectionPullback_comp_iso`: the quasi-inverses commute with
  pullback, given the comparison of the two direct images.

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Equation 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
-/


@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.FibredSite

universe u v w m

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : SiteKind)

/-- The functor `toSiteModules`, reading a quasi-coherent fppf module as a sheaf of modules for
the associated topology of kind `τ`, is fully faithful. -/
noncomputable def toSiteModulesFullyFaithful :
    (toSiteModules.{u, v, w, m} B S hS p hp τ).FullyFaithful where
  preimage f := ⟨⟨f.val⟩⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The functor `toSiteModules` is full. -/
instance : (toSiteModules.{u, v, w, m} B S hS p hp τ).Full :=
  (toSiteModulesFullyFaithful B S hS p hp τ).full

/-- The functor `toSiteModules` is faithful. -/
instance : (toSiteModules.{u, v, w, m} B S hS p hp τ).Faithful :=
  (toSiteModulesFullyFaithful B S hS p hp τ).faithful

end AlgebraicGeometry.FibredSite

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)

/-- A right adjoint is bijective on the morphisms out of an object at which the counit is an
isomorphism. -/
theorem bijective_map_of_isIso_counit {Y Y' : D} (h : IsIso (adj.counit.app Y)) :
    Function.Bijective (fun f : Y ⟶ Y' => R.map f) := by
  have key : (fun f : Y ⟶ Y' => R.map f) =
      (fun g => adj.homEquiv (R.obj Y) Y' g) ∘ (fun f : Y ⟶ Y' => adj.counit.app Y ≫ f) := by
    funext f; simp [Adjunction.homEquiv_unit]
  rw [key]
  exact (adj.homEquiv (R.obj Y) Y').bijective.comp
    ⟨fun a b hab => (cancel_epi (adj.counit.app Y)).mp hab,
      fun g => ⟨inv (adj.counit.app Y) ≫ g, by simp⟩⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

universe u v w m v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-- The quasi-coherence property on the `𝒪_X`-modules of an algebraic space `X`, that is, the
object property whose full subcategory is the category `QCoh(𝒪_X)` of Stacks 03G9. -/
abbrev quasicoherentModulesProperty :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-! ### Restriction of modules to the small étale site of the representing space -/

/-- The identification of the structure sheaf of the small étale site of the algebraic space `X`
with the restriction along `u_X : X_étale ⥤ 𝒳` of the structure sheaf of `𝒳`, as a homomorphism
of sheaves of (not necessarily commutative) rings. -/
noncomputable def restrictionStructureHom :
    letI := restrictionFunctor_isContinuous B S hS X.1 p hp e
    structureRingSheaf B S hS X ⟶
      ((restrictionFunctor B S hS X.1 p e).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS X.1)
        (BigFppfOver.associatedTopology B S hS p .etale)).obj
          (FibredSite.ringStructureSheafCore B S hS p hp .etale) :=
  letI := restrictionFunctor_isContinuous B S hS X.1 p hp e
  ⟨Functor.whiskerRight (NatTrans.op (eqToHom (restrictionFunctor_comp B S hS X.1 p e)))
    (BigFppfOver.structureSheaf B S hS).obj⟩

/-- The identification `restrictionStructureHom` of structure sheaves is an isomorphism. -/
theorem isIso_restrictionStructureHom :
    letI := restrictionFunctor_isContinuous B S hS X.1 p hp e
    IsIso (restrictionStructureHom B S hS X p hp e) := by
  let _ := restrictionFunctor_isContinuous B S hS X.1 p hp e
  let _ : IsIso ((sheafToPresheaf (SmallEtale.topology B S hS X.1) RingCat.{u}).map
      (restrictionStructureHom B S hS X p hp e)) := by
    change IsIso (Functor.whiskerRight
      (NatTrans.op (eqToHom (restrictionFunctor_comp B S hS X.1 p e)))
      (BigFppfOver.structureSheaf B S hS).obj)
    infer_instance
  exact isIso_of_reflects_iso _ (sheafToPresheaf (SmallEtale.topology B S hS X.1) RingCat.{u})

/-- The restriction `ℱ|_{X_étale} = i_X^*ℱ = π_{X,*}ℱ` of an `𝒪_𝒳`-module on the inherited étale
site of a category fibred in groupoids representable by the algebraic space `X`, as an
`𝒪_X`-module on the small étale site of `X`: the pushforward along the continuous functor
`u_X : X_étale ⥤ 𝒳` of Stacks 073M, with coefficient homomorphism
`AlgebraicGeometry.Space.restrictionStructureHom`. -/
@[stacks 075K "the restriction of a module to the small étale site of the representing space"]
noncomputable def moduleRestriction :
    SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale) ⥤
      Modules.{u, m} B S hS X.1 X.2 :=
  letI := restrictionFunctor_isContinuous B S hS X.1 p hp e
  (SheafOfModules.pushforward (restrictionStructureHom B S hS X p hp e) :
    SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale) ⥤
      SheafOfModules.{m} (structureRingSheaf B S hS X))

/-- The sections of `ℱ|_{X_étale}` over an étale chart `U` of `X` are the sections of `ℱ` over
the object `u_X U` of `𝒳`. -/
@[simp]
theorem moduleRestriction_obj_val_presheaf_obj
    (M : SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale))
    (U : SmallEtale B S hS X.1) :
    ((moduleRestriction B S hS X p hp e).obj M).val.presheaf.obj (op U) =
      M.val.presheaf.obj (op ((restrictionFunctor B S hS X.1 p e).obj U)) :=
  rfl

/-! ### The comparison functor on quasi-coherent modules -/

/-- The assertion that the restriction `ℱ|_{X_étale}` of every quasi-coherent module `ℱ` on `𝒳`
is quasi-coherent on the small étale site of `X`. -/
abbrev RestrictionPreservesQuasicoherent : Prop :=
  ∀ M : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp,
    quasicoherentModulesProperty.{u, m} B S hS X
      ((moduleRestriction B S hS X p hp e).obj
        ((FibredSite.toSiteModules B S hS p hp .etale).obj M))

/-- The comparison functor `QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_X)`, `ℱ ↦ ℱ|_{X_étale}`, of a category fibred in
groupoids representable by the algebraic space `X`: a quasi-coherent module on the inherited fppf
site, read as a sheaf of modules on the inherited étale site by
`AlgebraicGeometry.FibredSite.toSiteModules`, is restricted to the small étale site of `X`. -/
noncomputable def quasicoherentRestriction
    (hres : RestrictionPreservesQuasicoherent.{u, v, w, m} B S hS X p hp e) :
    FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp ⥤
      QuasicoherentSheaves.{u, m} B S hS X.1 X.2 :=
  ObjectProperty.lift _
    (FibredSite.toSiteModules B S hS p hp .etale ⋙ moduleRestriction B S hS X p hp e) hres

/-- The comparison functor followed by the inclusion of the quasi-coherent modules on `X` is the
restriction `AlgebraicGeometry.Space.moduleRestriction` of the underlying module. -/
theorem quasicoherentRestriction_comp_ι
    (hres : RestrictionPreservesQuasicoherent.{u, v, w, m} B S hS X p hp e) :
    quasicoherentRestriction B S hS X p hp e hres ⋙
        (quasicoherentModulesProperty.{u, m} B S hS X).ι =
      FibredSite.toSiteModules B S hS p hp .etale ⋙ moduleRestriction B S hS X p hp e :=
  rfl

/-! ### The equivalence -/

section Equivalence

variable (hres : RestrictionPreservesQuasicoherent.{u, v, w, m} B S hS X p hp e)
  {P : Modules.{u, m} B S hS X.1 X.2 ⥤
    SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
  (adj : P ⊣ moduleRestriction B S hS X p hp e)

/-- The unit of `π_X^* ⊣ i_X^*` at the quasi-coherent `𝒪_X`-modules, as a natural isomorphism,
given that each of its components there is an isomorphism. -/
noncomputable def quasicoherentUnitIso
    (hunit : ∀ G : QuasicoherentSheaves.{u, m} B S hS X.1 X.2,
      IsIso (adj.unit.app ((quasicoherentModulesProperty.{u, m} B S hS X).ι.obj G))) :
    (quasicoherentModulesProperty.{u, m} B S hS X).ι ≅
      (quasicoherentModulesProperty.{u, m} B S hS X).ι ⋙
        P ⋙ moduleRestriction B S hS X p hp e :=
  NatIso.ofComponents
    (fun G => letI := hunit G
      asIso (adj.unit.app ((quasicoherentModulesProperty.{u, m} B S hS X).ι.obj G)))
    fun {_ _} h =>
      adj.unit.naturality ((quasicoherentModulesProperty.{u, m} B S hS X).ι.map h)

/-- The comparison functor is bijective on morphisms, given that the counit of `π_X^* ⊣ i_X^*`
is an isomorphism at every quasi-coherent module. -/
theorem bijective_quasicoherentRestriction_map
    (hcounit : ∀ M : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp,
      IsIso (adj.counit.app ((FibredSite.toSiteModules B S hS p hp .etale).obj M)))
    (M M' : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp) :
    Function.Bijective
      (fun f : M ⟶ M' => (quasicoherentRestriction B S hS X p hp e hres).map f) := by
  have hb := adj.bijective_map_of_isIso_counit
    (Y' := (FibredSite.toSiteModules B S hS p hp .etale).obj M') (hcounit M)
  refine ⟨fun f g h => (FibredSite.toSiteModules B S hS p hp .etale).map_injective
    (hb.1 (congrArg (fun k => (quasicoherentModulesProperty.{u, m} B S hS X).ι.map k) h)),
    fun h => ?_⟩
  obtain ⟨k, hk⟩ := hb.2 ((quasicoherentModulesProperty.{u, m} B S hS X).ι.map h)
  obtain ⟨f, hf⟩ := (FibredSite.toSiteModules B S hS p hp .etale).map_surjective k
  refine ⟨f, (quasicoherentModulesProperty.{u, m} B S hS X).ι.map_injective ?_⟩
  change (moduleRestriction B S hS X p hp e).map
      ((FibredSite.toSiteModules B S hS p hp .etale).map f) = _
  rwa [hf]

/-- Restriction to the small étale site of `X` is an equivalence `QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X)` for a
category fibred in groupoids representable by the algebraic space `X`, given that restriction
preserves quasi-coherence (`hres`), a left adjoint `P` of restriction with a corestriction `Pq` to
the quasi-coherent subcategories, and that the unit (`hunit`) and the counit (`hcounit`) of the
adjunction are isomorphisms at the quasi-coherent modules. -/
theorem isEquivalence_quasicoherentRestriction
    (Pq : QuasicoherentSheaves.{u, m} B S hS X.1 X.2 ⥤
      FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp)
    (hPq : Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, m} B S hS X).ι ⋙ P)
    (hunit : ∀ G : QuasicoherentSheaves.{u, m} B S hS X.1 X.2,
      IsIso (adj.unit.app ((quasicoherentModulesProperty.{u, m} B S hS X).ι.obj G)))
    (hcounit : ∀ M : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp,
      IsIso (adj.counit.app ((FibredSite.toSiteModules B S hS p hp .etale).obj M))) :
    (quasicoherentRestriction B S hS X p hp e hres).IsEquivalence := by
  have hff (M M' : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp) :=
    bijective_quasicoherentRestriction_map B S hS X p hp e hres adj hcounit M M'
  have hfaithful : (quasicoherentRestriction B S hS X p hp e hres).Faithful :=
    ⟨fun {M M'} => (hff M M').1⟩
  have hfull : (quasicoherentRestriction B S hS X p hp e hres).Full :=
    ⟨fun {M M'} g => (hff M M').2 g⟩
  have hess : (quasicoherentRestriction B S hS X p hp e hres).EssSurj := by
    refine ⟨fun G => ⟨Pq.obj G, ⟨(quasicoherentModulesProperty.{u, m} B S hS X).fullyFaithfulι
      |>.preimageIso ?_⟩⟩⟩
    exact (moduleRestriction B S hS X p hp e).mapIso (hPq.app G) ≪≫
      ((quasicoherentUnitIso B S hS X p hp e adj hunit).app G).symm
  exact ⟨hfaithful, hfull, hess⟩

/-- The corestriction `Pq` of `π_X^*` to the quasi-coherent modules, followed by restriction, is
isomorphic to the identity, given that the unit of `π_X^* ⊣ i_X^*` is an isomorphism at every
quasi-coherent `𝒪_X`-module. -/
noncomputable def quasicoherentInverse_comp_iso
    (Pq : QuasicoherentSheaves.{u, m} B S hS X.1 X.2 ⥤
      FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp)
    (hPq : Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, m} B S hS X).ι ⋙ P)
    (hunit : ∀ G : QuasicoherentSheaves.{u, m} B S hS X.1 X.2,
      IsIso (adj.unit.app ((quasicoherentModulesProperty.{u, m} B S hS X).ι.obj G))) :
    Pq ⋙ quasicoherentRestriction B S hS X p hp e hres ≅
      𝟭 (QuasicoherentSheaves.{u, m} B S hS X.1 X.2) :=
  Functor.fullyFaithfulCancelRight (quasicoherentModulesProperty.{u, m} B S hS X).ι
    ((Iso.refl _ : (Pq ⋙ quasicoherentRestriction B S hS X p hp e hres) ⋙
          (quasicoherentModulesProperty.{u, m} B S hS X).ι ≅
        (Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale) ⋙
          moduleRestriction B S hS X p hp e) ≪≫
      Functor.isoWhiskerRight hPq (moduleRestriction B S hS X p hp e) ≪≫
      (quasicoherentUnitIso B S hS X p hp e adj hunit).symm ≪≫
      (Functor.leftUnitor _).symm)

/-- The quasi-inverse of the equivalence is `𝒢 ↦ π_X^*𝒢`: the corestriction `Pq` of the left
adjoint `P` of restriction is isomorphic to the inverse of the equivalence, under the hypotheses
of `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction`. -/
theorem nonempty_inv_iso_quasicoherentInverse
    (Pq : QuasicoherentSheaves.{u, m} B S hS X.1 X.2 ⥤
      FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp)
    (hPq : Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, m} B S hS X).ι ⋙ P)
    (hunit : ∀ G : QuasicoherentSheaves.{u, m} B S hS X.1 X.2,
      IsIso (adj.unit.app ((quasicoherentModulesProperty.{u, m} B S hS X).ι.obj G)))
    (hcounit : ∀ M : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp,
      IsIso (adj.counit.app ((FibredSite.toSiteModules B S hS p hp .etale).obj M))) :
    letI := isEquivalence_quasicoherentRestriction B S hS X p hp e hres adj Pq hPq hunit hcounit
    Nonempty ((quasicoherentRestriction B S hS X p hp e hres).inv ≅ Pq) := by
  let _ := isEquivalence_quasicoherentRestriction B S hS X p hp e hres adj Pq hPq hunit hcounit
  refine ⟨Iso.symm ?_⟩
  refine (Functor.rightUnitor Pq).symm ≪≫ ?_
  refine Functor.isoWhiskerLeft Pq
    (quasicoherentRestriction B S hS X p hp e hres).asEquivalence.unitIso ≪≫ ?_
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  refine Functor.isoWhiskerRight
    (quasicoherentInverse_comp_iso B S hS X p hp e hres adj Pq hPq hunit)
    (quasicoherentRestriction B S hS X p hp e hres).inv ≪≫ ?_
  exact Functor.leftUnitor _

end Equivalence

/-! ### The quasi-inverse exists, and the unit of the adjunction is an isomorphism

The statements of this section are at the module universe `max (u + 1) w m`.
-/

section Adjoint

/-- Restriction of modules to the small étale site of the algebraic space `X` representing `𝒳`
is a right adjoint, at the module universe `max (u + 1) w m`. -/
theorem isRightAdjoint_moduleRestriction :
    (moduleRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e).IsRightAdjoint := by
  let _ := restrictionFunctor_isContinuous B S hS X.1 p hp e
  let _ : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS X.1 p e
  let _ : EssentiallySmall.{max (u + 1) w m} 𝒳 :=
    (essentiallySmall_congr (equivSmallModel.{u} 𝒳)).mpr inferInstance
  let _ : HasWeakSheafify (BigFppfOver.associatedTopology B S hS p .etale)
      AddCommGrpCat.{max (u + 1) w m} :=
    (hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) w m} _ _).1
  let _ : (BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) w m} :=
    .ofEssentiallySmall.{_, _, _, _, max (u + 1) w m} _
  exact inferInstanceAs (SheafOfModules.pushforward.{max (u + 1) w m}
    (restrictionStructureHom B S hS X p hp e)).IsRightAdjoint

/-- For every left adjoint `P` of restriction to the small étale site of `X`, the unit of
`P ⊣ i_X^*` is an isomorphism at every `𝒪_X`-module. -/
theorem isIso_unit_moduleRestriction
    {P : Modules.{u, max (u + 1) w m} B S hS X.1 X.2 ⥤
      SheafOfModules.{max (u + 1) w m} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
    (adj : P ⊣ moduleRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e) :
    IsIso adj.unit := by
  let _ := restrictionFunctor_isContinuous B S hS X.1 p hp e
  let _ := restrictionFunctor_isCocontinuous B S hS X.1 p hp e
  let _ := isIso_restrictionStructureHom B S hS X p hp e
  exact SheafOfModules.isIso_unit_of_isIso_coefficient.{u, m, u, w, u + 1, v}
    (restrictionFunctor B S hS X.1 p e) (SmallEtale.topology B S hS X.1)
    (BigFppfOver.associatedTopology B S hS p .etale)
    (FibredSite.ringStructureSheafCore B S hS p hp .etale)
    (restrictionStructureHom B S hS X p hp e) adj

/-- At the module universe `max (u + 1) w m`, restriction to the small étale site of `X` is an
equivalence `QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X)`, given that restriction preserves quasi-coherence (`hres`),
a left adjoint `P` of restriction with a corestriction `Pq` to the quasi-coherent subcategories,
and that the counit of the adjunction is an isomorphism at the quasi-coherent modules
(`hcounit`). -/
theorem isEquivalence_quasicoherentRestriction_of_hcounit
    (hres : RestrictionPreservesQuasicoherent.{u, v, w, max (u + 1) w m} B S hS X p hp e)
    {P : Modules.{u, max (u + 1) w m} B S hS X.1 X.2 ⥤
      SheafOfModules.{max (u + 1) w m} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
    (adj : P ⊣ moduleRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e)
    (Pq : QuasicoherentSheaves.{u, max (u + 1) w m} B S hS X.1 X.2 ⥤
      FibredSite.quasicoherentModules.{u, v, w, max (u + 1) w m} B S hS p hp)
    (hPq : Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, max (u + 1) w m} B S hS X).ι ⋙ P)
    (hcounit : ∀ M : FibredSite.quasicoherentModules.{u, v, w, max (u + 1) w m} B S hS p hp,
      IsIso (adj.counit.app ((FibredSite.toSiteModules B S hS p hp .etale).obj M))) :
    (quasicoherentRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e hres).IsEquivalence :=
  let := isIso_unit_moduleRestriction.{u, v, w, m} B S hS X p hp e adj
  isEquivalence_quasicoherentRestriction B S hS X p hp e hres adj Pq hPq
    (fun _ => NatIso.isIso_app_of_isIso _ _) hcounit

end Adjoint

/-! ### Compatibility with pullback -/

/-- The equivalence is compatible with pullback for 1-morphisms between categories fibred in
groupoids representable by algebraic spaces: the quasi-inverses `π_X^*` and `π_Y^*` of the two
equivalences commute with the inverse image of modules along the 1-morphism and with the inverse
image of modules along the induced morphism of algebraic spaces, given the comparison `cmp` of
the two direct images (equation 075M).

Here `fStar ⊣ fPush` are the inverse and direct images along the 1-morphism, `gStar ⊣ gPush`
those along the induced morphism of algebraic spaces, and `PX`, `PY` are `π_X^*` and `π_Y^*`. -/
theorem nonempty_projectionPullback_comp_iso
    (Y : AlgebraicSpaces B S hS)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hq : q.IsFiberedInGroupoids)
    (eY : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p)
    {fStar : SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS q hq .etale) ⥤
      SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
    {fPush : SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale) ⥤
      SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS q hq .etale)}
    (adjf : fStar ⊣ fPush)
    {gStar : Modules.{u, m} B S hS Y.1 Y.2 ⥤ Modules.{u, m} B S hS X.1 X.2}
    {gPush : Modules.{u, m} B S hS X.1 X.2 ⥤ Modules.{u, m} B S hS Y.1 Y.2}
    (adjg : gStar ⊣ gPush)
    {PX : Modules.{u, m} B S hS X.1 X.2 ⥤
      SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS p hp .etale)}
    (adjX : PX ⊣ moduleRestriction B S hS X p hp e)
    {PY : Modules.{u, m} B S hS Y.1 Y.2 ⥤
      SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS q hq .etale)}
    (adjY : PY ⊣ moduleRestriction B S hS Y q hq eY)
    (cmp : fPush ⋙ moduleRestriction B S hS Y q hq eY ≅
      moduleRestriction B S hS X p hp e ⋙ gPush) :
    Nonempty (gStar ⋙ PX ≅ PY ⋙ fStar) :=
  ⟨(conjugateIsoEquiv (adjY.comp adjf) (adjg.comp adjX)).symm cmp⟩

end AlgebraicGeometry.Space

end
