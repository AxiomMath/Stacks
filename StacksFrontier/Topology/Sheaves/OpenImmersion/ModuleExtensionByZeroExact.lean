module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero of modules is exact

Let `(X, 𝒪)` be a ringed space, let `U ⊆ X` be open with inclusion `j : U → X`, and let
`j_! : Mod(𝒪|_U) ⥤ Mod(𝒪)` be the extension-by-zero functor of Stacks 00AB
(`ExtensionByZeroModules.jShriek`). This file proves that `j_!` is exact, and so is the restriction
`j^*`.

## Main results

* `TopCat.Presheaf.mono_stalkFunctor_map_of_mono_whiskerLeft`: a morphism of presheaves on `X` is
  a monomorphism on the stalk at `j u` as soon as its naive restriction to `U` is one on the
  stalk at `u`.
* `SheafOfModules.mono_stalkFunctor_map_of_mono`: a monomorphism of sheaves of modules on a
  topological space is a monomorphism on every stalk.
* `ExtensionByZeroModules.stalkJShriekIso`: the stalk of `j_! F` at a point of `U` is the stalk
  of `F` there.
* `ExtensionByZeroModules.jShriek_preservesMonomorphisms`: `j_!` preserves monomorphisms.
* `ExtensionByZeroModules.jShriek_preservesFiniteLimits` and
  `ExtensionByZeroModules.jShriek_preservesColimitsOfSize`: `j_!` is exact.
* `ExtensionByZeroModules.shortExact_map_jShriek`: `j_!` carries short exact sequences to short
  exact sequences.
* `ExtensionByZeroModules.jStar_preservesFiniteLimits` and
  `ExtensionByZeroModules.jStar_preservesFiniteColimits`: `j^*` is exact.
* `ExtensionByZeroModules.jPush_additive`: `j_*` is additive.

## Implementation notes

`ExtensionByZeroModules.preservesFiniteLimits_jStar` and
`ExtensionByZeroModules.preservesFiniteColimits_jStar` state the exactness of `j^*` again as lemmas
rather than instances, for use at a chosen instantiation of `O`. They fix
`PreservesLimitsOfSize.{0, 0}` where the instances fix `.{u, u}`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits

universe u w

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (U : Opens X)
variable {C : Type w} [Category.{u} C] [HasColimits C]

/-- A morphism `φ` of presheaves on `X` whose naive restriction to `U` is a monomorphism on the
stalk at a point `u` of `U` is a monomorphism on the stalk at `j u`. -/
lemma mono_stalkFunctor_map_of_mono_whiskerLeft (P Q : TopCat.Presheaf C X) (φ : P ⟶ Q)
    (u : (Opens.toTopCat X).obj U)
    (h : Mono ((stalkFunctor C u).map (Functor.whiskerLeft (imF U).op φ))) :
    Mono ((stalkFunctor C (U.inclusion' u)).map φ) :=
  ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (stalkRestrictIso U P u) (stalkRestrictIso U Q u)
      (stalkRestrictIso_naturality U P Q φ u).symm)).mp h

end TopCat.Presheaf

namespace SheafOfModules

/-- A monomorphism of sheaves of modules over a sheaf of rings on a topological space is a
monomorphism on every stalk of the underlying sheaves of abelian groups. -/
lemma mono_stalkFunctor_map_of_mono {Y : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) {M N : SheafOfModules.{u} R}
    (g : M ⟶ N) [Mono g] (y : Y) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map g)) := by
  have hmono : Mono ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map g) :=
    Functor.map_mono _ g
  refine ConcreteCategory.mono_of_injective _
    (TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (fun V => ?_) y)
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
    ((NatTrans.mono_iff_mono_app _).mp hmono (op V))

end SheafOfModules

namespace ExtensionByZeroModules

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

variable {X : TopCat.{u}} (U : Opens X)
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The stalk of `j_! F` at a point `x ∈ U` is the stalk of `F` at `x`, viewed as a point of
`U`. -/
noncomputable def stalkJShriekIso (F : SheafOfModules.{u} (resRing U O)) (x : X) (hx : x ∈ U) :
    TopCat.Presheaf.stalk (X := X) ((jShriek U O).obj F).val.presheaf x ≅
      TopCat.Presheaf.stalk (X := Usp U) F.val.presheaf ⟨x, hx⟩ :=
  haveI := isIso_jShriekAdjunction_unit U O
  have e : (TopCat.Presheaf.imF U).op ⋙ ((jShriek U O).obj F).val.presheaf ≅ F.val.presheaf :=
    ((toAb (resRing U O)).mapIso (asIso ((jShriekAdjunction U O).unit.app F))).symm
  (TopCat.Presheaf.stalkRestrictIso U ((jShriek U O).obj F).val.presheaf ⟨x, hx⟩).symm ≪≫
    eqToIso (TopCat.Presheaf.stalkFunctor_obj
      ((TopCat.Presheaf.imF U).op ⋙ ((jShriek U O).obj F).val.presheaf)
      (⟨x, hx⟩ : Usp U)).symm ≪≫
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : Usp U)).mapIso e ≪≫
    eqToIso (TopCat.Presheaf.stalkFunctor_obj F.val.presheaf (⟨x, hx⟩ : Usp U))

/-- `j_!` preserves colimits: extension by zero is right exact. -/
instance jShriek_preservesColimitsOfSize :
    PreservesColimitsOfSize.{u, u} (jShriek U O) :=
  (jShriekAdjunction U O).leftAdjoint_preservesColimits

/-- `j_!` preserves colimits indexed by small categories such as `WalkingParallelPair`. -/
instance jShriek_preservesColimitsOfSizeZero :
    PreservesColimitsOfSize.{0, 0} (jShriek U O) :=
  (jShriekAdjunction U O).leftAdjoint_preservesColimits

/-- `j^* j_!` preserves monomorphisms. -/
lemma mono_jStar_jShriek_map {M N : SheafOfModules.{u} (resRing U O)} (g : M ⟶ N) [Mono g] :
    Mono ((jStar U O).map ((jShriek U O).map g)) := by
  have := isIso_jShriekAdjunction_unit U O
  have e : Arrow.mk g ≅ Arrow.mk ((jStar U O).map ((jShriek U O).map g)) :=
    Arrow.isoMk (asIso ((jShriekAdjunction U O).unit.app M))
      (asIso ((jShriekAdjunction U O).unit.app N))
      (by rw [asIso_hom, asIso_hom]
          exact ((jShriekAdjunction U O).unit.naturality g).symm)
  exact ((MorphismProperty.monomorphisms
    (SheafOfModules.{u} (resRing U O))).arrow_mk_iso_iff e).mp ‹Mono g›

/-- The stalk of `j_!` of a monomorphism is a monomorphism. -/
lemma mono_stalk_jShriek_map {M N : SheafOfModules.{u} (resRing U O)} (g : M ⟶ N) [Mono g]
    (x : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toAb O).map ((jShriek U O).map g))) := by
  by_cases hx : x ∈ U
  · have := mono_jStar_jShriek_map U O g
    have h1 : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : Usp U)).map
        (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
          ((toAb O).map ((jShriek U O).map g)))) := by
      rw [← toAb_jStar_map U O ((jShriek U O).map g)]
      exact SheafOfModules.mono_stalkFunctor_map_of_mono (resRing U O)
        ((jStar U O).map ((jShriek U O).map g)) ⟨x, hx⟩
    simpa using TopCat.Presheaf.mono_stalkFunctor_map_of_mono_whiskerLeft U _ _ _ _ h1
  · refine ⟨fun g₁ g₂ _ => ?_⟩
    exact (isZero_stalk_jShriek U O M x hx).eq_of_tgt g₁ g₂

/-- Extension by zero preserves monomorphisms. -/
@[sga "4 IV 11.3.1" "partial"]
instance jShriek_preservesMonomorphisms : (jShriek U O).PreservesMonomorphisms where
  preserves {M N} g _ := by
    have : ∀ x : X, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((SheafOfModules.toSheaf O).map ((jShriek U O).map g)).hom)) :=
      fun x => mono_stalk_jShriek_map U O g x
    exact (SheafOfModules.toSheaf O).mono_of_mono_map
      (TopCat.Presheaf.mono_of_stalk_mono ((SheafOfModules.toSheaf O).map ((jShriek U O).map g)))

/-! ### Exactness -/

/-- Restriction `j^*` is additive. -/
noncomputable instance jStar_additive : (jStar U O).Additive := by
  constructor
  intro M N f g
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  ext : 1
  rfl

/-- `j_!` is additive. -/
noncomputable instance jShriek_additive : (jShriek U O).Additive :=
  Adjunction.left_adjoint_additive (jShriekAdjunction U O)

/-- Restriction to an open subspace is left exact. -/
noncomputable instance jStar_preservesFiniteLimits : PreservesFiniteLimits (jStar U O) :=
  haveI : PreservesLimitsOfSize.{u, u} (jStar U O) :=
    (jShriekAdjunction U O).rightAdjoint_preservesLimits
  inferInstance

/-- Restriction to an open subspace is right exact. -/
noncomputable instance jStar_preservesFiniteColimits : PreservesFiniteColimits (jStar U O) :=
  haveI : PreservesColimitsOfSize.{u, u} (jStar U O) :=
    (jStarAdjunction U O).leftAdjoint_preservesColimits
  inferInstance

/-- Pushforward along an open immersion is additive. -/
noncomputable instance jPush_additive : (jPush U O).Additive :=
  haveI : (jPush U O).IsRightAdjoint := (jStarAdjunction U O).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- `j_!` preserves homology. -/
noncomputable instance jShriek_preservesHomology : (jShriek U O).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (jShriek U O)

/-- Extension by zero is left exact. -/
noncomputable instance jShriek_preservesFiniteLimits : PreservesFiniteLimits (jShriek U O) :=
  (jShriek U O).preservesFiniteLimits_of_preservesHomology

/-- Restriction to an open subspace is left exact. -/
lemma preservesFiniteLimits_jStar : PreservesFiniteLimits (jStar U O) :=
  inferInstance

/-- Restriction to an open subspace is right exact. -/
lemma preservesFiniteColimits_jStar : PreservesFiniteColimits (jStar U O) :=
  inferInstance

/-- **Extension by zero is exact.** A short exact sequence of sheaves of `𝒪|_U`-modules stays
short exact after applying `j_!`. -/
lemma shortExact_map_jShriek (S : ShortComplex (SheafOfModules.{u} (resRing U O)))
    (hS : S.ShortExact) : (S.map (jShriek U O)).ShortExact :=
  hS.map_of_exact (jShriek U O)

end ExtensionByZeroModules

end
