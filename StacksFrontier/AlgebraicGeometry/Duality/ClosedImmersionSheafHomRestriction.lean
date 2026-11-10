module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcision
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.IsoTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategorySquare
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaf Hom out of a closed subscheme: restriction to opens and dualizing complexes

Let `i : Z ⟶ W` be a closed immersion of schemes, let `V ⊆ W` be open and let `U = i⁻¹V`, with
`i_V = i|_U : U ⟶ V`. This file proves that `R ℰom(𝒪_Z, -)` commutes with restriction to `V`,

`R ℰom(𝒪_Z, K)|_U ≅ R ℰom(𝒪_U, K|_V)`,

and deduces that `R ℰom(𝒪_Z, -)`, hence the twisted inverse image `i^×` of [Stacks, Tag 0A9E],
carries dualizing complexes to dualizing complexes when `W` is locally Noetherian. This is the
closed-immersion case of [Stacks, Tag 0AA3]; in the source it is read off the affine description
of [Stacks, Tag 0A78] part (2) together with [Stacks, Tag 0AX0].

The restriction isomorphism is not obtained by comparing internal Homs. Both sides are right
adjoints: `R ℰom(𝒪_Z, -)|_U` of `Ri_* ∘ j_{U!}` and `R ℰom(𝒪_U, (-)|_V)` of `j_{V!} ∘ R(i_V)_*`,
by [Stacks, Tag 0A76] and [Stacks, Tag 08BT]. So it suffices to compare the left adjoints, and
`j_{V!} (i_V)_* M ≅ i_* j_{U!} M` holds already for sheaves of modules: both sides vanish on
stalks off `V` — outside the image of `i` by [Stacks, Tag 00AE], at `i(z)` with `z ∉ U` because
the stalk there is that of `j_{U!} M` at `z` — and they agree after restriction to `V`. The
comparison is the mate of the base change `(i_* -)|_V ≅ (i_V)_*((-)|_U)` of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.

## Main results

All in the namespace `Stacks.Duality.ClosedImmersionRestriction`:

* `pushforwardJShriekIso` — `(i_V)_* ⋙ j_{V!} ≅ j_{U!} ⋙ i_*`.
* `derivedSheafHomRestrictIso` — `R ℰom(𝒪_Z, -) ⋙ (-)|_U ≅ (-)|_V ⋙ R ℰom(𝒪_U, -)`.
* `derivedSheafHomTransportIso` — the transport of `R ℰom(𝒪, -)` along isomorphisms of closed
  immersions.
* `hasDualizingModelOn_derivedSheafHom` and `isDualizingComplex_derivedSheafHom` —
  `R ℰom(𝒪_Z, K)` of a dualizing complex is dualizing.
* `isDualizingComplex_rightAdjoint_of_isClosedImmersion` — the twisted inverse image of a
  bounded-below dualizing complex along a closed immersion is dualizing, and
  `isDualizingComplex_twistedInverseImage_comp_of_isClosedImmersion` its consequence for a
  composite `i ≫ p`.

## Implementation notes

The restriction and transport isomorphisms, and the dualizing statement, are stated at
`CategoryTheory.HasDerivedCategory.standard`, the model sealed inside
`Stacks.Duality.HasDualizingModelOn` and the one at which [Stacks, Tag 0A78] part (2) is proved.
The twisted inverse image lives at the locally small model; the passage is
`Stacks.Duality.AnyModel.derivedSheafHomExactSupportModelIso` together with the model
independence of dualizing complexes, `Stacks.Duality.isDualizingComplex_modelEquiv_iff`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Duality.ClosedImmersionRestriction

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i] (V : W.Opens)

/-- Extension by zero of modules along the inclusion of an open subscheme, as a functor between
the categories of modules of the two schemes. -/
abbrev jShriek (U : Z.Opens) : U.toScheme.Modules ⥤ Z.Modules :=
  ExtensionByZeroModules.jShriek (X := Z.toRingedSpace.carrier) U
    (structureSheafRing Z.toRingedSpace)

/-- **The stalks of `i_* j_{U!} M` vanish off `V`.** -/
theorem isZero_stalk_pushforward_jShriek (M : (i ⁻¹ᵁ V).toScheme.Modules) (x : W) (hx : x ∉ V) :
    IsZero (TopCat.Presheaf.stalk (X := W.toRingedSpace.carrier)
      ((Scheme.Modules.pushforward i).obj ((jShriek (i ⁻¹ᵁ V)).obj M)).val.presheaf x) := by
  by_cases hrange : x ∈ Set.range (ConcreteCategory.hom i.base)
  · obtain ⟨z, rfl⟩ := hrange
    have hz : z ∉ i ⁻¹ᵁ V := hx
    have h0 := ExtensionByZeroModules.isZero_stalk_jShriek (X := Z.toRingedSpace.carrier)
      (i ⁻¹ᵁ V) (structureSheafRing Z.toRingedSpace) M z hz
    have hiso := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing (C := Ab.{u})
      (IsClosedImmersion.isClosedEmbedding i).isInducing
      ((jShriek (i ⁻¹ᵁ V)).obj M).val.presheaf z
    exact h0.of_iso (@asIso _ _ _ _ _ hiso)
  · have := subsingleton_stalk_pushforward_of_notMemRange' i ((jShriek (i ⁻¹ᵁ V)).obj M) x
      hrange
    exact AddCommGrpCat.isZero_of_subsingleton _

/-- The counit of an adjunction transported along an isomorphism of right adjoints is invertible
wherever the original counit is. -/
theorem isIso_ofNatIsoRight_counit_app {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (Y : D) (hY : IsIso (adj.counit.app Y)) :
    IsIso ((adj.ofNatIsoRight iso).counit.app Y) := by
  have e : (adj.ofNatIsoRight iso).counit.app Y = F.map (iso.inv.app Y) ≫ adj.counit.app Y := by
    have h1 := Adjunction.homEquiv_counit (adj.ofNatIsoRight iso) (g := 𝟙 (H.obj Y))
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.homEquiv_counit,
      Category.id_comp] at h1
    rw [h1, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [e]
  infer_instance

/-- **Extension by zero is left adjoint to restriction to an open subscheme**: the adjunction
`j_! ⊣ j^*` of [Stacks, Tag 00A7], with its right adjoint written as Mathlib's restriction
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. The two restrictions are equal by
`Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_eq_jStar`. -/
def jShriekAdjunction (U : Z.Opens) : jShriek U ⊣ Scheme.Modules.restrictFunctor U.ι :=
  (ExtensionByZeroModules.jShriekAdjunction (X := Z.toRingedSpace.carrier) U
    (structureSheafRing Z.toRingedSpace)).ofNatIsoRight
      (eqToIso (Stacks.Perfect.LocalCohomologyExcision.restrictFunctor_eq_jStar U).symm)

/-- The unit of `j_! ⊣ j^*` is invertible: extension by zero is fully faithful. -/
instance isIso_jShriekAdjunction_unit (U : Z.Opens) : IsIso (jShriekAdjunction U).unit := by
  have : (jShriek U).Full := (ExtensionByZeroModules.jShriekFullyFaithful
    (X := Z.toRingedSpace.carrier) U (structureSheafRing Z.toRingedSpace)).full
  have : (jShriek U).Faithful := (ExtensionByZeroModules.jShriekFullyFaithful
    (X := Z.toRingedSpace.carrier) U (structureSheafRing Z.toRingedSpace)).faithful
  infer_instance

/-- **The counit `j_! j^* G ⟶ G` is invertible at a module whose stalks vanish off the open.** -/
theorem isIso_jShriekAdjunction_counit_app (U : Z.Opens) (G : Z.Modules)
    (hG : ∀ x : Z, x ∉ U → IsZero (TopCat.Presheaf.stalk (X := Z.toRingedSpace.carrier)
      G.val.presheaf x)) :
    IsIso ((jShriekAdjunction U).counit.app G) :=
  isIso_ofNatIsoRight_counit_app _ _ G
    (ExtensionByZeroModules.counit_isIso_of_stalk_isZero (X := Z.toRingedSpace.carrier)
      U (structureSheafRing Z.toRingedSpace) G hG)

/-- **Pushforward along a closed immersion commutes with extension by zero**, as a transformation
`(i_V)_* ⋙ j_{V!} ⟶ j_{U!} ⋙ i_*`: the mate, under the two adjunctions `j_! ⊣ j^*`, of the base
change `(i_*-)|_V ≅ (i_V)_*((-)|_U)` of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`. -/
def pushforwardJShriekTwoSquare :
    TwoSquare (Scheme.Modules.pushforward (i ∣_ V)) (jShriek (i ⁻¹ᵁ V)) (jShriek V)
      (Scheme.Modules.pushforward i) :=
  (mateEquiv (jShriekAdjunction (i ⁻¹ᵁ V)) (jShriekAdjunction V)).symm
    (TwoSquare.mk _ _ _ _
      (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i V).inv)

omit [IsClosedImmersion i] in
/-- The component of `pushforwardJShriekTwoSquare` at `M` is the composite of `j_{V!} (i_V)_*`
applied to the unit `M ⟶ j_U^* j_{U!} M`, of `j_{V!}` applied to the base change
`(i_V)_* j_U^* j_{U!} M ⟶ (i_* j_{U!} M)|_V`, and of the counit `j_{V!} ((i_* j_{U!} M)|_V) ⟶
i_* j_{U!} M`. -/
theorem pushforwardJShriekTwoSquare_app (M : (i ⁻¹ᵁ V).toScheme.Modules) :
    (pushforwardJShriekTwoSquare i V).app M =
      (jShriek V).map ((Scheme.Modules.pushforward (i ∣_ V)).map
          ((jShriekAdjunction (i ⁻¹ᵁ V)).unit.app M)) ≫
        (jShriek V).map ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso
          i V).inv.app ((jShriek (i ⁻¹ᵁ V)).obj M)) ≫
        (jShriekAdjunction V).counit.app
          ((Scheme.Modules.pushforward i).obj ((jShriek (i ⁻¹ᵁ V)).obj M)) := by
  simp [pushforwardJShriekTwoSquare, mateEquiv]

/-- The transformation `(i_V)_* ⋙ j_{V!} ⟶ j_{U!} ⋙ i_*` is an isomorphism. -/
instance isIso_pushforwardJShriekTwoSquare : IsIso (pushforwardJShriekTwoSquare i V) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M => ?_
  rw [pushforwardJShriekTwoSquare_app]
  have := isIso_jShriekAdjunction_counit_app V
    ((Scheme.Modules.pushforward i).obj ((jShriek (i ⁻¹ᵁ V)).obj M))
    (isZero_stalk_pushforward_jShriek i V M)
  infer_instance

/-- **`(i_V)_* ⋙ j_{V!} ≅ j_{U!} ⋙ i_*`.** -/
def pushforwardJShriekIso :
    Scheme.Modules.pushforward (i ∣_ V) ⋙ jShriek V ≅
      jShriek (i ⁻¹ᵁ V) ⋙ Scheme.Modules.pushforward i :=
  asIso (pushforwardJShriekTwoSquare i V)

/-- Extension by zero of modules is additive. -/
instance jShriek_additive (U : Z.Opens) : (jShriek U).Additive :=
  inferInstanceAs (ExtensionByZeroModules.jShriek (X := Z.toRingedSpace.carrier) U
    (structureSheafRing Z.toRingedSpace)).Additive

/-- Extension by zero of modules is left exact. -/
instance jShriek_preservesFiniteLimits (U : Z.Opens) : PreservesFiniteLimits (jShriek U) :=
  inferInstanceAs (PreservesFiniteLimits (ExtensionByZeroModules.jShriek
    (X := Z.toRingedSpace.carrier) U (structureSheafRing Z.toRingedSpace)))

/-- Extension by zero of modules is right exact. -/
@[sga "4 IV 11.3.1" "partial"]
instance jShriek_preservesFiniteColimits (U : Z.Opens) : PreservesFiniteColimits (jShriek U) :=
  inferInstanceAs (PreservesFiniteColimits (ExtensionByZeroModules.jShriek
    (X := Z.toRingedSpace.carrier) U (structureSheafRing Z.toRingedSpace)))

/-! ### Derived sheaf Hom with exact support and restriction to an open -/

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

/-- The closed immersion `i`, read as a closed quotient morphism of ringed spaces. -/
abbrev cq {Z' W' : Scheme.{u}} (i' : Z' ⟶ W') [IsClosedImmersion i'] :
    RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.{u} :=
  Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i'

/-- **[Stacks, Tag 0A76]** for a closed immersion of schemes, with its left adjoint written as
Mathlib's direct image of modules on schemes. -/
def derivedPushforwardSheafHomAdjunction {Z' W' : Scheme.{u}} (i' : Z' ⟶ W')
    [IsClosedImmersion i'] :
    (Scheme.Modules.pushforward i').mapDerivedCategory ⊣ (cq i').derivedSheafHomExactSupport :=
  (cq i').derivedModulePushforwardSheafHomExactSupportAdjunction

/-- **[Stacks, Tag 08BT]**: derived extension by zero is left adjoint to derived restriction to
an open subscheme. -/
def derivedJShriekAdjunction {X : Scheme.{u}} (U : X.Opens) :
    (jShriek U).mapDerivedCategory ⊣ (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  Adjunction.mapDerivedCategory (jShriekAdjunction U)

/-- **Derived pushforward along a closed immersion commutes with derived extension by zero.** -/
def derivedPushforwardJShriekIso :
    (Scheme.Modules.pushforward (i ∣_ V)).mapDerivedCategory ⋙ (jShriek V).mapDerivedCategory ≅
      (jShriek (i ⁻¹ᵁ V)).mapDerivedCategory ⋙ (Scheme.Modules.pushforward i).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (pushforwardJShriekIso i V)

/-- **`R ℰom(𝒪_Z, -)` commutes with restriction to an open.** For a closed immersion
`i : Z ⟶ W` and an open `V ⊆ W` with `U = i⁻¹V`,

`R ℰom(𝒪_Z, K)|_U ≅ R ℰom(𝒪_U, K|_V)`,

naturally in `K ∈ D(𝒪_W)`. Both sides are right adjoint, by [Stacks, Tag 0A76] and
[Stacks, Tag 08BT], to the two sides of `derivedPushforwardJShriekIso`, and an isomorphism of
left adjoints is conjugate to one of right adjoints. -/
def derivedSheafHomRestrictIso :
    (cq i).derivedSheafHomExactSupport ⋙
        (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory ⋙
        (cq (i ∣_ V)).derivedSheafHomExactSupport :=
  conjugateIsoEquiv
    ((derivedJShriekAdjunction (i ⁻¹ᵁ V)).comp (derivedPushforwardSheafHomAdjunction i))
    ((derivedPushforwardSheafHomAdjunction (i ∣_ V)).comp (derivedJShriekAdjunction V))
    (derivedPushforwardJShriekIso i V)

/-! ### Transport along isomorphisms of schemes -/

/-- Derived direct image along an isomorphism of schemes is left adjoint to derived direct image
along its inverse. -/
def derivedPushforwardIsoAdjunction {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pushforward e.hom).mapDerivedCategory ⊣
      (Scheme.Modules.pushforward e.inv).mapDerivedCategory :=
  Adjunction.mapDerivedCategory (Scheme.Modules.pushforwardEquivOfIso e).toAdjunction

/-- **`R ℰom(𝒪, -)` is transported along isomorphisms of closed immersions.** For closed
immersions `g : U ⟶ V`, `g' : U' ⟶ V'` and isomorphisms `eU : U ≅ U'`, `eV : V ≅ V'` with
`g ≫ eV = eU ≫ g'`, reading an object along `eV` and then applying `R ℰom(𝒪_U, -)` is applying
`R ℰom(𝒪_{U'}, -)` and then reading the result along `eU`. -/
def derivedSheafHomTransportIso {U V U' V' : Scheme.{u}} (g : U ⟶ V) [IsClosedImmersion g]
    (g' : U' ⟶ V') [IsClosedImmersion g'] (eU : U ≅ U') (eV : V ≅ V')
    (w : g ≫ eV.hom = eU.hom ≫ g') :
    (Scheme.Modules.pushforward eV.inv).mapDerivedCategory ⋙ (cq g).derivedSheafHomExactSupport ≅
      (cq g').derivedSheafHomExactSupport ⋙
        (Scheme.Modules.pushforward eU.inv).mapDerivedCategory :=
  conjugateIsoEquiv
    ((derivedPushforwardSheafHomAdjunction g).comp (derivedPushforwardIsoAdjunction eV))
    ((derivedPushforwardIsoAdjunction eU).comp (derivedPushforwardSheafHomAdjunction g'))
    (Functor.mapDerivedCategorySquareIso
      (Scheme.Modules.pushforwardComp eU.hom g' ≪≫ Scheme.Modules.pushforwardCongr w.symm ≪≫
        (Scheme.Modules.pushforwardComp g eV.hom).symm))

end Derived

/-! ### `R ℰom(𝒪_Z, -)` of a dualizing complex is dualizing -/

section Dualizing

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The chart square of a closed immersion over an affine open.** For an affine open `V ⊆ W`,
the restriction `i|_{i⁻¹V}` is `Spec` of the ring map `Γ(W, V) ⟶ Γ(Z, i⁻¹V)`, read along the two
canonical isomorphisms `i⁻¹V ≅ Spec Γ(Z, i⁻¹V)` and `V ≅ Spec Γ(W, V)`. -/
theorem morphismRestrict_comp_isoSpec_hom {V : W.Opens} (hV : IsAffineOpen V) :
    (i ∣_ V) ≫ hV.isoSpec.hom =
      (hV.preimage i).isoSpec.hom ≫ Spec.map (i.appLE V (i ⁻¹ᵁ V) le_rfl) := by
  have h : (hV.preimage i).isoSpec.inv ≫ (i ∣_ V) =
      Spec.map (i.appLE V (i ⁻¹ᵁ V) le_rfl) ≫ hV.isoSpec.inv := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
      IsAffineOpen.SpecMap_appLE_fromSpec i hV (hV.preimage i) le_rfl]
  rw [← cancel_epi (hV.preimage i).isoSpec.inv, ← Category.assoc, h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- Derived sheafification followed by reading along an isomorphism `e`, written as restriction
along `e.hom` or as direct image along `e.inv`. -/
def tildeRestrictIsoSpecIso {X : Scheme.{u}} {R : CommRingCat.{u}} (e : X ≅ Spec R) :
    (tilde.functor R ⋙ Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory ≅
      (tilde.functor R).mapDerivedCategory ⋙
        (Scheme.Modules.pushforward e.inv).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Functor.isoWhiskerLeft (tilde.functor R)
        (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv e)) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- **A dualizing model is carried by `R ℰom(𝒪_Z, -)` at the preimage of an affine open.** If
`K|_V` is the associated sheaf of a dualizing complex `ω` over `Γ(W, V)`, then
`R ℰom(𝒪_Z, K)|_{i⁻¹V}` is the associated sheaf of `R Hom_{Γ(W, V)}(Γ(Z, i⁻¹V), ω)`, which is a
dualizing complex over `Γ(Z, i⁻¹V)` by [Stacks, Tag 0AX0]. The identification is the restriction
isomorphism `derivedSheafHomRestrictIso`, the transport `derivedSheafHomTransportIso` along the
chart square `morphismRestrict_comp_isoSpec_hom`, and the affine comparison of
[Stacks, Tag 0A78] part (2). -/
theorem hasDualizingModelOn_derivedSheafHom [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    (K : DerivedCategory W.Modules) {V : W.Opens} (hV : IsAffineOpen V)
    (hK : HasDualizingModelOn K V hV) :
    HasDualizingModelOn ((cq i).derivedSheafHomExactSupport.obj K) (i ⁻¹ᵁ V) (hV.preimage i) := by
  have hVn : IsNoetherianRing Γ(W, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUn : IsNoetherianRing Γ(Z, i ⁻¹ᵁ V) :=
    IsLocallyNoetherian.component_noetherian ⟨i ⁻¹ᵁ V, hV.preimage i⟩
  obtain ⟨ω, hω, ⟨e⟩⟩ := hK
  set φ : Γ(W, V) ⟶ Γ(Z, i ⁻¹ᵁ V) := i.appLE V (i ⁻¹ᵁ V) le_rfl with hφ
  have w := morphismRestrict_comp_isoSpec_hom i hV
  have : IsClosedImmersion (Spec.map φ) := by
    rw [show Spec.map φ = (hV.preimage i).isoSpec.inv ≫ (i ∣_ V) ≫ hV.isoSpec.hom by
      rw [w, Iso.inv_hom_id_assoc]]
    infer_instance
  have hsurj : Function.Surjective φ := by
    rw [hφ, Scheme.Hom.appLE_eq_app]
    exact Scheme.Hom.app_surjective i V hV
  have := isIso_affineDerivedSheafHomComparison_app_of_noetherian _ _ φ ω
    (Dualizing.isBoundedBelow_of_bounded.{u, u} ω hω.bounded)
  refine ⟨(Dualizing.derivedHom.{u, u, u} φ.hom).obj ω,
    Dualizing.isDualizingComplex_derivedHom_of_finite.{u, u} φ.hom
      (RingHom.Finite.of_surjective _ hsurj) ω hω, ⟨?_⟩⟩
  exact (derivedSheafHomRestrictIso i V).app K ≪≫
    (cq (i ∣_ V)).derivedSheafHomExactSupport.mapIso
      (e ≪≫ (tildeRestrictIsoSpecIso hV.isoSpec).app ω) ≪≫
    (derivedSheafHomTransportIso (i ∣_ V) (Spec.map φ) (hV.preimage i).isoSpec hV.isoSpec w).app
      ((tilde.functor Γ(W, V)).mapDerivedCategory.obj ω) ≪≫
    (Scheme.Modules.pushforward (hV.preimage i).isoSpec.inv).mapDerivedCategory.mapIso
      (asIso ((affineDerivedSheafHomComparison _ _ φ).app ω)).symm ≪≫
    ((tildeRestrictIsoSpecIso (hV.preimage i).isoSpec).app
      ((Dualizing.derivedHom.{u, u, u} φ.hom).obj ω)).symm

/-- **`R ℰom(𝒪_Z, K)` of a dualizing complex `K` is dualizing**, for a closed immersion
`i : Z ⟶ W` into a locally Noetherian scheme. The preimages `i⁻¹V` of the affine opens `V ⊆ W`
form an affine open cover of `Z`, each carries a dualizing model by
`hasDualizingModelOn_derivedSheafHom`, and [Stacks, Tag 0A86] concludes. -/
theorem isDualizingComplex_derivedSheafHom [IsLocallyNoetherian W] (K : DerivedCategory W.Modules)
    (hK : IsDualizingComplex K) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    IsDualizingComplex ((cq i).derivedSheafHomExactSupport.obj K) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  refine isDualizingComplex_of_hasDualizingModelOn_cover (fun V : W.affineOpens => i ⁻¹ᵁ V.1)
    (fun V => V.2.preimage i) ?_ (fun V => hasDualizingModelOn_derivedSheafHom i K V.2 (hK V.1 V.2))
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
  rfl

end Dualizing

/-! ### The twisted inverse image of a dualizing complex along a closed immersion -/

section TwistedInverseImage

open StacksDraft.DerivedModel

/-- **`R ℰom(𝒪_Z, K)` of a dualizing complex is dualizing, at the locally small model.** This is
`isDualizingComplex_derivedSheafHom` carried across the comparison of the locally small and the
standard model of the derived categories, along which both `R ℰom(𝒪_Z, -)` and being a
dualizing complex are invariant. -/
theorem isDualizingComplex_locallySmall_derivedSheafHom [IsLocallyNoetherian W]
    (K : DerivedCategory W.Modules) (hK : IsDualizingComplex K) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    IsDualizingComplex ((LocallySmall.derivedSheafHomExactSupport i).obj K) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let Q := cq i
  let hW₁ : HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing Q.X)) := inferInstance
  let hZ₁ : HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing Q.Z)) := inferInstance
  let hW₂ := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Q.X))
  let hZ₂ := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Q.Z))
  let D₁ := @AnyModel.derivedSheafHomExactSupport Q hW₁ hZ₁
  let D₂ := @AnyModel.derivedSheafHomExactSupport Q hW₂ hZ₂
  let e : (modelEquiv hZ₁ hZ₂).functor.obj (D₁.obj K) ≅
      D₂.obj ((modelEquiv hW₁ hW₂).functor.obj K) :=
    (AnyModel.derivedSheafHomExactSupportModelIso Q hW₁ hZ₁ hW₂ hZ₂).app K
  have h₁ : @IsDualizingComplex W _ hW₂ ((modelEquiv hW₁ hW₂).functor.obj K) :=
    (isDualizingComplex_modelEquiv_iff hW₁ hW₂ K).2 hK
  have h₂ : @IsDualizingComplex Z _ hZ₂ (D₂.obj ((modelEquiv hW₁ hW₂).functor.obj K)) :=
    isDualizingComplex_derivedSheafHom i _ h₁
  have h₃ : @IsDualizingComplex Z _ hZ₂ ((modelEquiv hZ₁ hZ₂).functor.obj (D₁.obj K)) :=
    @isDualizingComplex_of_iso Z _ hZ₂ _ _ e.symm h₂
  exact (isDualizingComplex_modelEquiv_iff hZ₁ hZ₂ (D₁.obj K)).1 h₃

/-- **The twisted inverse image of a dualizing complex along a closed immersion is dualizing.**
Let `i : Z ⟶ W` be a closed immersion into a locally Noetherian scheme, and let `a` be a right
adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` ([Stacks, Tag 0A9E]). If `K ∈ D⁺_QCoh(𝒪_W)` is a
dualizing complex, then so is `a(K)`.

On bounded-below objects `a = R ℰom(𝒪_Z, -)` by [Stacks, Tag 0A9X], and `R ℰom(𝒪_Z, K)` is
dualizing by `isDualizingComplex_locallySmall_derivedSheafHom`. This is [Stacks, Tag 0AA3] for a
closed immersion. -/
theorem isDualizingComplex_rightAdjoint_of_isClosedImmersion [IsLocallyNoetherian W]
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : quasiCoherentDerivedPushforward i hpush ⊣ a)
    (K : quasiCoherentDerivedCategory W) (hKb : DerivedCategoryB.IsBoundedBelow K.obj)
    (hK : IsDualizingComplex K.obj) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    IsDualizingComplex (a.obj K).obj := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have := LocallySmall.isIso_rightAdjointToDerivedSheafHom_app i hpush a adj
    ((pseudoCoherent_iff_locallyOfFiniteType i).2 inferInstance) ⟨K, hKb⟩
  exact isDualizingComplex_of_iso
    (asIso ((LocallySmall.rightAdjointToDerivedSheafHom i hpush a adj).app K)).symm
    (isDualizingComplex_locallySmall_derivedSheafHom i K.obj hK)

/-- **The twisted inverse image along `i ≫ p`, for a closed immersion `i`, of an object whose
twisted inverse image along `p` is a bounded-below dualizing complex, is dualizing.** Both
twisted inverse images are those of [Stacks, Tag 0A9E]; `(i ≫ p)^× ≅ i^× ⋙ p^×` because both are
right adjoint to `R(i ≫ p)_* = Rp_* ∘ Ri_*`, and `i^×` preserves dualizing complexes by
`isDualizingComplex_rightAdjoint_of_isClosedImmersion`. -/
theorem isDualizingComplex_twistedInverseImage_comp_of_isClosedImmersion {X P Y : Scheme.{u}}
    (i : X ⟶ P) [IsClosedImmersion i] (p : P ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    [CompactSpace P] [CompactSpace Y] [IsLocallyNoetherian P]
    (K : quasiCoherentDerivedCategory Y)
    (hb : letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward p
      DerivedCategoryB.IsBoundedBelow
        ((twistedInverseImage p (isQuasicoherent_homology_derivedPushforward_of_qcqs p)).obj K).obj)
    (hK : letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward p
      IsDualizingComplex
        ((twistedInverseImage p
          (isQuasicoherent_homology_derivedPushforward_of_qcqs p)).obj K).obj) :
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (i ≫ p)
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
    IsDualizingComplex ((twistedInverseImage (i ≫ p)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (i ≫ p))).obj K).obj := by
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward i
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward p
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (i ≫ p)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  refine isDualizingComplex_of_iso
    ((ObjectProperty.ι _).mapIso ((twistedInverseImageCompIsoOfQcqs i p).app K)).symm ?_
  exact isDualizingComplex_rightAdjoint_of_isClosedImmersion i
    (isQuasicoherent_homology_derivedPushforward_of_qcqs i) _
    (twistedInverseImageAdjunction i (isQuasicoherent_homology_derivedPushforward_of_qcqs i))
    _ hb hK

/-- Being a dualizing complex of the twisted inverse image is insensitive to rewriting the
morphism along an equality. -/
theorem isDualizingComplex_twistedInverseImage_congr {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    {f g : X ⟶ Y} (h : f = g)
    (hf : ∀ (K : quasiCoherentDerivedCategory X) (n : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules n).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (hg : ∀ (K : quasiCoherentDerivedCategory X) (n : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules n).obj
        ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward f hf).IsLeftAdjoint]
    [(quasiCoherentDerivedPushforward g hg).IsLeftAdjoint] (K : quasiCoherentDerivedCategory Y) :
    IsDualizingComplex ((twistedInverseImage f hf).obj K).obj ↔
      IsDualizingComplex ((twistedInverseImage g hg).obj K).obj := by
  subst h
  rfl

end TwistedInverseImage

end Stacks.Duality.ClosedImmersionRestriction

end
