module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Stalk
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# The normalization quotient of a scheme

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components and let
`ν : X^ν ⟶ X` be its normalization.  The ring map `𝒪_X ⟶ ν_* 𝒪_{X^ν}` makes `ν_* 𝒪_{X^ν}` a
sheaf of `𝒪_X`-modules, and this file introduces the cokernel of the resulting module map
together with its stalks.  That cokernel is the sheaf whose structure
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)(2) describes.

Everything here is stated over the library's own names — `AlgebraicGeometry.Scheme.normalization`
for the normalization and `Stacks.NormalizationStalkAmbient.normalizationPushforwardStalk` for
the stalk of its pushforward — rather than over a self-contained restatement.

## Main definitions

* `normalizationModuleMap` is the module map `𝒪_X ⟶ ν_* 𝒪_{X^ν}`.
* `normalizationQuotient` is its cokernel `ν_* 𝒪_{X^ν} / 𝒪_X`, an `𝒪_X`-module.
* `normalizationQuotientStalk` is the stalk of that cokernel at a point.
* `skyscraperModule` is the skyscraper `𝒪_X`-module with a prescribed stalk module at a point.

## Main results

* `normalizationModuleStalkMap_epi_iff_ringStalkMap_surjective` converts an epimorphism of the
  additive stalk of the module map into surjectivity of the stalk of the ring map.
* `normalizationPushforwardStalk_map_injective`: on a reduced scheme the stalk of the ring map
  is injective.
* `stalk_isNagataRing`: the local rings of a Nagata scheme are Nagata rings.
* `ringKrullDim_stalk_le_topologicalKrullDim` bounds the dimension of a local ring by the
  dimension of the scheme.
* `normalizationStalkAlgEquivIntegralClosureSelf` specialises
  [Stacks, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)(2) to a reduced scheme, where the
  reduction plays no role and the ambient algebra is the total ring of fractions of the local
  ring itself.

## Implementation notes

The stalk of the module map is taken with the additive stalk functor
  `Stacks.SheafOfModules.FlatShortExact.stalkF`, whose
exactness is what makes the cokernel's stalk computable; the stalk of the ring map is taken with
`TopCat.Presheaf.stalkFunctor CommRingCat`.  The two agree because the additive stalk of a sheaf
of rings is the stalk of its underlying sheaf of abelian groups: that is
`commRingStalkToAddStalkIso`, which is an instance of commuting a colimit with a forgetful
functor that preserves it, and `normalizationModuleMap_stalkMap_eq_addStalkMap` records that the
module map's additive stalk is literally the ring map's.

`normalizationStalkAlgEquivIntegralClosureSelf` is part (2) of Tag 0C3B composed with
the identification `Frac(A ⧸ nilradical A) ≅ Frac A` available when `A` is reduced, which is
what the one-dimensional statement is applied through: the delta invariant of Tag 0C3T is
defined with `FractionRing A` as the ambient algebra.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NormalizationQuotient

open Stacks.NormalizationStalkAmbient

/-- The canonical module map from the structure sheaf to the pushforward of the structure sheaf
of the normalization. -/
public noncomputable abbrev normalizationModuleMap (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :=
  SheafOfModules.unitToPushforwardObjUnit
    (Scheme.Hom.toRingCatSheafHom (Scheme.normalization X hX))

/-- The module quotient `ν_* 𝒪_{X^ν} / 𝒪_X`. -/
public noncomputable abbrev normalizationQuotient (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    X.Modules :=
  cokernel (normalizationModuleMap X hX)

/-- The stalk at `x` of the normalization quotient. -/
public noncomputable abbrev normalizationQuotientStalk (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : ModuleCat.{u} (X.presheaf.stalk x) :=
  OXModule.stalk (normalizationQuotient X hX) x

/-- The skyscraper `𝒪_X`-module at `x` with stalk module `N`. -/
public noncomputable abbrev skyscraperModule (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules :=
  OXModule.sheafify.obj (OXModule.skyscraperPOM x N)

/-- The additive stalk of a sheaf of rings is the stalk of its underlying sheaf of abelian
groups, because the forgetful functor to abelian groups preserves the filtered colimit
computing the stalk. -/
public noncomputable def commRingStalkToAddStalkIso {X : TopCat.{u}} (x : X)
    (F : TopCat.Presheaf CommRingCat X) :
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj F)) ≅
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj
        (F ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) :=
  preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ F)

/-- `commRingStalkToAddStalkIso` is natural in the sheaf of rings. -/
public theorem commRingStalkToAddStalkIso_naturality {X : TopCat.{u}} (x : X)
    {F H : TopCat.Presheaf CommRingCat X} (f : F ⟶ H) :
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f)) ≫
      (commRingStalkToAddStalkIso x H).hom =
    (commRingStalkToAddStalkIso x F).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (Functor.whiskerRight f
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) := by
  let G := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let η := preservesColimitNatIso (J := (TopologicalSpace.OpenNhds x)ᵒᵖ)
    (C := CommRingCat) (D := AddCommGrpCat) G
  exact η.hom.naturality (Functor.whiskerLeft (TopologicalSpace.OpenNhds.inclusion x).op f)

/-- The additive stalk of the module map is the additive stalk of the ring map. -/
public theorem normalizationModuleMap_stalkMap_eq_addStalkMap (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    (Stacks.SheafOfModules.FlatShortExact.stalkF (X := X.toRingedSpace) x).map
      (normalizationModuleMap X hX) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (Functor.whiskerRight (Scheme.normalization X hX).c
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) :=
  rfl

/-- The additive stalk of the module map is an epimorphism exactly when the stalk of the ring
map is surjective. -/
public theorem normalizationModuleStalkMap_epi_iff_ringStalkMap_surjective (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    Epi ((Stacks.SheafOfModules.FlatShortExact.stalkF (X := X.toRingedSpace) x).map
      (normalizationModuleMap X hX)) ↔
      Function.Surjective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Scheme.normalization X hX).c)) := by
  let ν := Scheme.normalization X hX
  let N := Scheme.normalizationScheme X hX
  let G := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let f := (TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c
  let g := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (Functor.whiskerRight ν.c G)
  let e₀ := commRingStalkToAddStalkIso x X.presheaf
  let e₁ := commRingStalkToAddStalkIso x
    ((TopCat.Presheaf.pushforward CommRingCat ν.base).obj N.presheaf)
  have hsquare : G.map f ≫ e₁.hom = e₀.hom ≫ g :=
    commRingStalkToAddStalkIso_naturality x ν.c
  have hpoint : ⇑(ConcreteCategory.hom e₁.hom) ∘ ⇑(ConcreteCategory.hom (G.map f)) =
      ⇑(ConcreteCategory.hom g) ∘ ⇑(ConcreteCategory.hom e₀.hom) :=
    funext fun a => by
      simpa only [Function.comp_apply, ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom hsquare a
  rw [normalizationModuleMap_stalkMap_eq_addStalkMap]
  refine (AddCommGrpCat.epi_iff_surjective g).trans ?_
  rw [← Function.Surjective.of_comp_iff _ e₀.addCommGroupIsoToAddEquiv.surjective]
  exact (iff_of_eq (congrArg Function.Surjective hpoint.symm)).trans
    (Function.Surjective.of_comp_iff' e₁.addCommGroupIsoToAddEquiv.bijective _)

/-- For a reduced ring the reduction is the ring itself, so the total ring of fractions of the
reduction is the total ring of fractions. -/
public noncomputable def reductionFractionRingAlgEquivSelf (A : Type u) [CommRing A]
    [IsReduced A] :
    letI : Algebra A (FractionRing (A ⧸ nilradical A)) := (reductionFractionRingHom A).toAlgebra
    FractionRing (A ⧸ nilradical A) ≃ₐ[A] FractionRing A :=
  letI : Algebra A (FractionRing (A ⧸ nilradical A)) := (reductionFractionRingHom A).toAlgebra
  let hq : A ⧸ nilradical A ≃+* A :=
    (Ideal.quotEquivOfEq (nilradical_eq_bot_iff.2 inferInstance)).trans (RingEquiv.quotientBot A)
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv hq) fun a => by
    change IsFractionRing.ringEquivOfRingEquiv hq
        (algebraMap (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))
          (Ideal.Quotient.mk (nilradical A) a)) = algebraMap A (FractionRing A) a
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap hq]
    simp [hq]

/-- **Stacks Project, Tag 0C3B(2)** for a reduced scheme: the stalk of the pushforward of the
structure sheaf of the normalization is the integral closure of the local ring in its own total
ring of fractions, the reduction being the local ring itself. -/
public noncomputable def normalizationStalkAlgEquivIntegralClosureSelf (X : Scheme.{u})
    [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    normalizationPushforwardStalk X hX x ≃ₐ[X.presheaf.stalk x]
      integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)) :=
  letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  letI : IsReduced (X.presheaf.stalk x) := AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  letI : Algebra (X.presheaf.stalk x)
      (FractionRing (X.presheaf.stalk x ⧸ nilradical (X.presheaf.stalk x))) :=
    (reductionFractionRingHom (X.presheaf.stalk x)).toAlgebra
  (normalizationStalkAlgEquivIntegralClosureFractionRing X hX x).trans
    (reductionFractionRingAlgEquivSelf (X.presheaf.stalk x)).mapIntegralClosure

/-- On a reduced scheme the stalk of the ring map to the normalization is injective: it is the
inclusion of a local ring into its integral closure in its total ring of fractions. -/
public theorem normalizationPushforwardStalk_map_injective (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Scheme.normalization X hX).c)) := by
  let : IsReduced (X.presheaf.stalk x) := AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let A := X.presheaf.stalk x
  let A' := normalizationPushforwardStalk X hX x
  let e := normalizationStalkAlgEquivIntegralClosureSelf X hX x
  have hic : Function.Injective (algebraMap A (integralClosure A (FractionRing A))) :=
    fun _ _ hab => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hab)
  change Function.Injective (algebraMap A A')
  intro a b hab
  apply hic
  calc
    algebraMap A (integralClosure A (FractionRing A)) a = e (algebraMap A A' a) :=
      (e.commutes a).symm
    _ = e (algebraMap A A' b) := congrArg e hab
    _ = algebraMap A (integralClosure A (FractionRing A)) b := e.commutes b

/-- The Krull dimension of a local ring of a scheme is at most the dimension of the scheme. -/
public theorem ringKrullDim_stalk_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, topologicalKrullDim,
    Order.krullDim_eq_iSup_coheight]
  let e := (irreducibleSetEquivPoints (α := X)).toEquiv
  calc
    (Order.coheight x : WithBot ℕ∞) = (Order.coheight (e.symm x) : WithBot ℕ∞) := by
      simpa [e] using congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞))
        (Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)) (e.symm x))
    _ ≤ ⨆ a : TopologicalSpace.IrreducibleCloseds X, (Order.coheight a : WithBot ℕ∞) :=
      le_iSup (fun a : TopologicalSpace.IrreducibleCloseds X =>
        (Order.coheight a : WithBot ℕ∞)) (e.symm x)

/-- The local rings of a Nagata scheme are Nagata rings, being localizations of the Nagata rings
of sections on the affine opens witnessing the hypothesis. -/
public theorem stalk_isNagataRing (X : Scheme.{u}) (hX : IsNagataScheme X) (x : X) :
    IsNagataRing (X.presheaf.stalk x) := by
  obtain ⟨U, hx, hU⟩ := hX x
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let p := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  have : IsLocalization p.primeCompl (X.presheaf.stalk x) :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  exact isNagata_of_isLocalization Γ(X, U.1) p.primeCompl (X.presheaf.stalk x) hU

end Stacks.AlgebraicGeometry.NormalizationQuotient

end
