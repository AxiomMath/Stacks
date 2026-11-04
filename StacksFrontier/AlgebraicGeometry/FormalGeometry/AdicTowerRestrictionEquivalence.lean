module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemTheorem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicThickeningProperEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureBridges

/-!
# Grothendieck existence along a tower algebraized by a proper scheme

Let `A` be a Noetherian ring complete with respect to `I`, let `fX : X ⟶ Spec A` be proper and let
`kₙ : Xₙ ⟶ X` exhibit a tower `(Xₙ, iₙ)` as the adic base changes `X ×_{Spec A} Sₙ`. Then
restriction along the tower is an equivalence from the coherent `𝒪_X`-modules onto the systems of
coherent modules along the tower ([Stacks, Tag 088F], in the case where the support conditions may
be omitted).

The library states 088F for the completion functor
`AlgebraicGeometry.adicThickeningTransitionCompletionFunctor` into
`AlgebraicGeometry.AdicCoherentTransitionSystem`, on the canonical tower `X ×_{Spec A} Sₙ`. That
functor and restriction along the canonical tower have the same objects, morphisms and transition
isomorphisms; this file transfers fullness, faithfulness and essential surjectivity from one to
the other, comparing only the morphism components of the transition isomorphisms
(`restriction_transitionIso_hom`). The passage from the canonical tower to an arbitrary tower
isomorphic to it is
`Stacks.AmpleFormalSystemTheorem.adicTowerModuleAlgebraization_of_canonicalTower`.

## Main results

* `Stacks.AdicTowerRestriction.isEquivalence_canonicalRestriction`: restriction along the canonical
  tower is an equivalence of categories.
* `Stacks.AdicTowerRestriction.adicCanonicalTowerModuleAlgebraization`: the input
  `Stacks.AmpleFormalSystemTheorem.AdicCanonicalTowerModuleAlgebraization` holds.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.CoherentTower

universe u

namespace Stacks.AdicTowerRestriction

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) [IsProper fX]
  [∀ n : ℕ, IsLocallyNoetherian (adicBaseChange A I fX n)]

/-- The restriction functor along the canonical tower. -/
abbrev canonicalRestriction :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      ModuleSystem (adicBaseChangeSucc A I fX) :=
  restriction (adicBaseChangeSucc A I fX) (fun n => pullback.fst fX (adicThickeningι A I n))
    (adicBaseChangeSucc_fst A I fX)

omit [IsNoetherianRing A] [IsProper fX] [∀ n : ℕ, IsLocallyNoetherian (adicBaseChange A I fX n)] in
/-- The transitions of a completion and of a restriction along the canonical tower are the same
natural isomorphism. -/
lemma completionNatIso_eq (n : ℕ) : adicThickeningCompletionNatIso A I fX n =
    restrictionNatIso (adicBaseChangeSucc A I fX)
      (fun n => pullback.fst fX (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I fX) n := rfl

omit [IsNoetherianRing A] [IsProper fX] in
/-- The transition isomorphisms of a restricted system along the canonical tower are the components
of `restrictionNatIso`. -/
lemma restriction_transitionIso_hom' (F : AlgebraicGeometry.SheafOfModules.CoherentModules
    X.ringCatSheaf) (n : ℕ) :
    (((canonicalRestriction A I fX).obj F).transitionIso n).hom =
      ((restrictionNatIso (adicBaseChangeSucc A I fX)
        (fun n => pullback.fst fX (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I fX) n).app
          F.obj).hom := rfl

omit [∀ n : ℕ, IsLocallyNoetherian (adicBaseChange A I fX n)] in
/-- The transition isomorphisms of a completed system are the components of
`adicThickeningCompletionNatIso`. -/
lemma completion_transitionIso_hom' (F : AlgebraicGeometry.SheafOfModules.CoherentModules
    X.ringCatSheaf) (n : ℕ) :
    (((adicThickeningTransitionCompletionFunctor A I fX).obj F).transitionIso n).hom =
      ((adicThickeningCompletionNatIso A I fX n).app F.obj).hom := rfl

/-- **The transition isomorphisms of the restricted and of the completed system agree.** -/
lemma restriction_transitionIso_hom (F : AlgebraicGeometry.SheafOfModules.CoherentModules
    X.ringCatSheaf) (n : ℕ) :
    (((canonicalRestriction A I fX).obj F).transitionIso n).hom =
      (((adicThickeningTransitionCompletionFunctor A I fX).obj F).transitionIso n).hom := by
  rw [restriction_transitionIso_hom', completion_transitionIso_hom', completionNatIso_eq]

/-- A morphism of restricted systems, read as a morphism of completed systems. -/
def toCompletionHom {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (φ : (canonicalRestriction A I fX).obj F ⟶ (canonicalRestriction A I fX).obj G) :
    (adicThickeningTransitionCompletionFunctor A I fX).obj F ⟶
      (adicThickeningTransitionCompletionFunctor A I fX).obj G where
  app := φ.app
  comm n := by
    have h := φ.comm n
    rwa [restriction_transitionIso_hom, restriction_transitionIso_hom] at h

/-- A morphism into a completed system, read as a morphism into the restricted one. -/
def ofCompletionHom {F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {S : ModuleSystem (adicBaseChangeSucc A I fX)}
    (φ : (adicThickeningTransitionCompletionFunctor A I fX).obj F ⟶ ⟨S.obj, S.isCoherent,
      S.transitionIso⟩) : (canonicalRestriction A I fX).obj F ⟶ S where
  app := φ.app
  comm n := by
    rw [restriction_transitionIso_hom]
    exact φ.comm n

/-- A morphism out of a completed system, read as a morphism out of the restricted one. -/
def ofCompletionHom' {F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {S : ModuleSystem (adicBaseChangeSucc A I fX)}
    (φ : (⟨S.obj, S.isCoherent, S.transitionIso⟩ : AdicCoherentTransitionSystem A I fX) ⟶
      (adicThickeningTransitionCompletionFunctor A I fX).obj F) :
    S ⟶ (canonicalRestriction A I fX).obj F where
  app := φ.app
  comm n := by
    rw [restriction_transitionIso_hom]
    exact φ.comm n

variable [IsAdicComplete I A]

/-- Restriction along the canonical tower is faithful. -/
instance faithful_canonicalRestriction : (canonicalRestriction A I fX).Faithful := by
  have := isEquivalence_adicThickeningTransitionCompletionFunctor A I fX
  exact ⟨fun h => (adicThickeningTransitionCompletionFunctor A I fX).map_injective
    (AdicCoherentTransitionSystem.Hom.ext (congrArg ModuleSystem.Hom.app h))⟩

/-- Restriction along the canonical tower is full. -/
instance full_canonicalRestriction : (canonicalRestriction A I fX).Full := by
  have := isEquivalence_adicThickeningTransitionCompletionFunctor A I fX
  refine ⟨fun {F G} φ => ?_⟩
  obtain ⟨a, ha⟩ := (adicThickeningTransitionCompletionFunctor A I fX).map_surjective
    (toCompletionHom A I fX φ)
  exact ⟨a, ModuleSystem.Hom.ext (congrArg AdicCoherentTransitionSystem.Hom.app ha)⟩

/-- Restriction along the canonical tower is essentially surjective. -/
instance essSurj_canonicalRestriction : (canonicalRestriction A I fX).EssSurj := by
  have := isEquivalence_adicThickeningTransitionCompletionFunctor A I fX
  refine ⟨fun S => ?_⟩
  let T : AdicCoherentTransitionSystem A I fX := ⟨S.obj, S.isCoherent, S.transitionIso⟩
  let e := (adicThickeningTransitionCompletionFunctor A I fX).objObjPreimageIso T
  exact ⟨(adicThickeningTransitionCompletionFunctor A I fX).objPreimage T,
    ⟨Iso.mk (ofCompletionHom A I fX e.hom) (ofCompletionHom' A I fX e.inv)
      (ModuleSystem.Hom.ext (congrArg AdicCoherentTransitionSystem.Hom.app e.hom_inv_id))
      (ModuleSystem.Hom.ext (congrArg AdicCoherentTransitionSystem.Hom.app e.inv_hom_id))⟩⟩

/-- **Restriction along the canonical tower is an equivalence**, [Stacks, Tag 088F] for a proper
`fX`. -/
theorem isEquivalence_canonicalRestriction : (canonicalRestriction A I fX).IsEquivalence := { }

omit [∀ n : ℕ, IsLocallyNoetherian (adicBaseChange A I fX n)] [IsProper fX] in
/-- **Grothendieck existence along the canonical adic tower holds**: the input
`Stacks.AmpleFormalSystemTheorem.AdicCanonicalTowerModuleAlgebraization` of the sheaf half of
[Stacks, Tag 089A] is a theorem. -/
theorem adicCanonicalTowerModuleAlgebraization :
    Stacks.AmpleFormalSystemTheorem.AdicCanonicalTowerModuleAlgebraization A I := by
  intro X fX hfX
  have := isProper_of_isProjectiveMorphism fX hfX
  exact isEquivalence_canonicalRestriction A I fX

end Stacks.AdicTowerRestriction

end
