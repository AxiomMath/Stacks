module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Compatible systems of flat sheaves with proper support over an inverse limit of rings

Situation [Stacks, Tag 0CX4]: an inverse system of rings `(Aₙ)` with surjective transition maps
whose kernels are locally nilpotent, `A = lim Aₙ`, an algebraic space `X` separated and of finite
presentation over `A`, its infinitesimal base changes `Xₙ = X ×_{Spec A} Spec Aₙ`, viewed as closed
subspaces of `X`, and a system `(Fₙ, φₙ)` of finitely presented `𝒪_{Xₙ}`-modules, flat over `Aₙ`,
with support proper over `Aₙ`, with isomorphisms `φₙ : Fₙ ⊗_{𝒪_{Xₙ}} 𝒪_{Xₙ₋₁} ≅ Fₙ₋₁`.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation`: **Situation 0CX4**.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stage`,
  `…closedImmersion`, `…transition`, `…stageToBase`: the space `Xₙ`, the closed immersion
  `iₙ : Xₙ → X`, the closed immersion `tₙ : Xₙ → Xₙ₊₁` and the structure morphism
  `Xₙ → Spec Aₙ`.

## Implementation notes

The geometric vocabulary (the inverse-limit base, the affine bases, the base changes and their
transition morphisms) is that of Situation [Stacks, Tag 0DIK],
`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/DerivedExistence.lean`, which is imported and
not restated. As there, the index `n : ℕ` stands for the level `n + 1` of the source, and
membership of `Spec A` and of every `Spec Aₙ` in the chosen big fppf site is recorded as two
fields, since `AlgebraicGeometry.BigFppfSite.Contains` is a size condition which no geometric
hypothesis supplies.

The tensor product `Fₙ ⊗_{𝒪_{Xₙ}} 𝒪_{Xₙ₋₁}` of the source is, by the equivalence of
[Stacks, Tag 04CJ] which it cites, the inverse image of `Fₙ` along the closed immersion
`Xₙ₋₁ → Xₙ`; it is written here as `AlgebraicGeometry.Space.modulePullback` along
`AlgebraicGeometry.Space.transitionSpace`.

Support proper over `Aₙ` is `AlgebraicGeometry.Space.HasProperSupport` for the structure morphism
`Xₙ → Spec Aₙ`, whose local finiteness of type witness is derived from the finite presentation of
`X` over `A`, not assumed.

## References

* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

/-- The structure morphism `Xₙ → Spec Aₙ` of an infinitesimal base change of an algebraic space of
finite presentation over the inverse-limit base is locally of finite type. -/
theorem isLocallyOfFiniteType_spaceBaseProjection_of_isFinitePresentation
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase F)) (hSn : ∀ n : ℕ, B.Contains (baseAt F n))
    (X : Over (schemeSpace (limitBaseObject F B hS)))
    (hX : IsFinitePresentation B (limitBase F) hS X.hom.hom) (n : ℕ) :
    IsLocallyOfFiniteType B (limitBase F) hS (spaceBaseProjection F B hS hSn X n).hom :=
  isLocallyOfFiniteType_spaceBaseProjection F B hS hSn X
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation _ _ _ hX.1) n

/-- **Situation [Stacks, Tag 0CX4].** An inverse system of rings `(Aₙ)` with surjective
transition maps whose kernels are locally nilpotent; an algebraic space `X` separated and of finite
presentation over `A = lim Aₙ`; and a system `(Fₙ, φₙ)` of finitely presented `𝒪_{Xₙ}`-modules on
the infinitesimal base changes `Xₙ = X ×_{Spec A} Spec Aₙ`, each flat over `Aₙ` with support proper
over `Aₙ`, together with isomorphisms `φₙ` from the restriction of `Fₙ₊₁` to `Xₙ` to `Fₙ`. -/
@[stacks 0CX4 "the situation as stated: nothing is granted or assumed beyond the source's data \
and hypotheses; the two containment fields only say that Spec A and Spec Aₙ are schemes of the \
chosen big fppf site"]
structure FlatSheafExistenceSituation where
  /-- The inverse system of rings `(Aₙ)`. -/
  system : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- Its transition maps are surjective. -/
  transition_surjective (n : ℕ) :
    Function.Surjective (system.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of its transition maps are locally nilpotent. -/
  transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (system.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The big fppf site in which the algebraic spaces are taken. -/
  B : BigFppfSite.{u}
  /-- The inverse-limit base `Spec A` belongs to the site. -/
  containsLimitBase : B.Contains (limitBase system)
  /-- Every affine base `Spec Aₙ` belongs to the site. -/
  containsBaseAt (n : ℕ) : B.Contains (baseAt system n)
  /-- The algebraic space `X` over `Spec A`. -/
  X : Over (schemeSpace (limitBaseObject system B containsLimitBase))
  /-- `X` is separated over `A`. -/
  separated : IsSeparated B (limitBase system) containsLimitBase X.hom.hom
  /-- `X` is of finite presentation over `A`. -/
  finitePresentation : IsFinitePresentation B (limitBase system) containsLimitBase X.hom.hom
  /-- The module `Fₙ` on `Xₙ`. -/
  F (n : ℕ) : Modules.{u, u} B (limitBase system) containsLimitBase
    (spaceAt system B containsLimitBase containsBaseAt X n).1
    (spaceAt system B containsLimitBase containsBaseAt X n).2
  /-- `Fₙ` is a finitely presented `𝒪_{Xₙ}`-module. -/
  finitelyPresented (n : ℕ) : (F n).IsFinitePresentationOnSite
  /-- `Fₙ` is flat over `Aₙ`. -/
  flat (n : ℕ) : IsFlatOver B (limitBase system) containsLimitBase
    (spaceAt system B containsLimitBase containsBaseAt X n).2
    (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom (F n)
  /-- `Fₙ` has support proper over `Aₙ`. -/
  properSupport (n : ℕ) : HasProperSupport B (limitBase system) containsLimitBase
    (spaceAt system B containsLimitBase containsBaseAt X n).2
    (schemeSpace (baseObjectAt system B containsLimitBase containsBaseAt n)).2
    (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom
    (isLocallyOfFiniteType_spaceBaseProjection_of_isFinitePresentation system B
      containsLimitBase containsBaseAt X finitePresentation n)
    ((SheafOfModules.toSheaf _).obj (F n))
  /-- The isomorphism `φ : Fₙ₊₁ ⊗ 𝒪_{Xₙ} ≅ Fₙ`. -/
  φ (n : ℕ) : (modulePullback B (limitBase system) containsLimitBase
    (transitionSpace system B containsLimitBase containsBaseAt X n)).obj (F (n + 1)) ≅ F n

/-- The direct image along a closed immersion of algebraic spaces preserves epimorphisms: it is
right exact. -/
theorem epi_modulePushforward_map_of_isClosedImmersion {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N : Modules.{u, u} B S hS Z.1 Z.2} (f : M ⟶ N)
    [Epi f] : Epi ((modulePushforward B S hS i).map f) := by
  have := preservesFiniteColimits_modulePushforward_of_isClosedImmersion B S hS i hi
  exact preserves_epi_of_preservesColimit _ f

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The base scheme `Spec A` of the situation. -/
abbrev S : Scheme.{u} := limitBase D.system

/-- The algebraic space `Xₙ = X ×_{Spec A} Spec Aₙ` (index `n` standing for level `n + 1`). -/
abbrev stage (n : ℕ) : AlgebraicSpaces D.B D.S D.containsLimitBase :=
  spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- The closed immersion `iₙ : Xₙ → X`. -/
abbrev closedImmersion (n : ℕ) : D.stage n ⟶ D.X.left :=
  spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- The closed immersion `tₙ : Xₙ → Xₙ₊₁`. -/
abbrev transition (n : ℕ) : D.stage n ⟶ D.stage (n + 1) :=
  transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- The structure morphism `Xₙ → Spec Aₙ`. -/
abbrev stageToBase (n : ℕ) :
    D.stage n ⟶ schemeSpace (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n) :=
  spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- The closed immersions satisfy `iₙ₊₁ ∘ tₙ = iₙ`. -/
@[reassoc (attr := simp)]
lemma transition_closedImmersion (n : ℕ) :
    D.transition n ≫ D.closedImmersion (n + 1) = D.closedImmersion n :=
  transitionSpace_spaceProjection _ _ _ _ _ n

/-- `iₙ : Xₙ → X` is a closed immersion. -/
theorem isClosedImmersion_closedImmersion (n : ℕ) :
    IsClosedImmersion D.B D.S D.containsLimitBase (D.closedImmersion n).hom :=
  isClosedImmersion_spaceProjection _ _ _ _ _ D.transition_surjective n

/-- `tₙ : Xₙ → Xₙ₊₁` is a closed immersion. -/
theorem isClosedImmersion_transition (n : ℕ) :
    IsClosedImmersion D.B D.S D.containsLimitBase (D.transition n).hom :=
  isClosedImmersion_transitionSpace _ _ _ _ _ D.transition_surjective n

/-- `iₙ : Xₙ → X` is an affine morphism. -/
theorem isAffineHom_closedImmersion (n : ℕ) :
    IsAffineHom D.B D.S D.containsLimitBase (D.closedImmersion n).hom :=
  isAffineHom_of_isClosedImmersion _ _ _ _ (D.isClosedImmersion_closedImmersion n)

/-! ### The inverse system `(iₙ,* Fₙ)` on `X` -/

/-- The direct image `iₙ,* Fₙ` of `Fₙ` along the closed immersion `iₙ : Xₙ → X`; the source
writes it simply `Fₙ`. -/
abbrev pushforwardModule (n : ℕ) :
    Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 :=
  (modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)).obj (D.F n)

/-- The map `Fₙ₊₁ ⟶ tₙ,* Fₙ` adjoint to `φₙ`. -/
def transitionAdjoint (n : ℕ) :
    D.F (n + 1) ⟶ (modulePushforward D.B D.S D.containsLimitBase (D.transition n)).obj (D.F n) :=
  (modulePullbackAdjunction D.B D.S D.containsLimitBase (D.transition n)).unit.app (D.F (n + 1)) ≫
    (modulePushforward D.B D.S D.containsLimitBase (D.transition n)).map (D.φ n).hom

/-- The identification `iₙ₊₁,* tₙ,* Fₙ ≅ iₙ,* Fₙ`, from `iₙ₊₁ ∘ tₙ = iₙ`. -/
def pushforwardCompIso (n : ℕ) :
    (modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion (n + 1))).obj
      ((modulePushforward D.B D.S D.containsLimitBase (D.transition n)).obj (D.F n)) ≅
      D.pushforwardModule n :=
  (modulePushforwardCompIso D.B D.S D.containsLimitBase (D.transition n)
      (D.closedImmersion (n + 1))).app (D.F n) ≪≫
    eqToIso (by rw [transition_closedImmersion])

/-- The transition map `iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ`: the direct image along `iₙ₊₁` of the adjoint
`Fₙ₊₁ ⟶ tₙ,* Fₙ` of `φₙ`, followed by `iₙ₊₁,* tₙ,* = iₙ,*`. -/
def pushforwardTransition (n : ℕ) : D.pushforwardModule (n + 1) ⟶ D.pushforwardModule n :=
  (modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion (n + 1))).map
      (D.transitionAdjoint n) ≫ (D.pushforwardCompIso n).hom

/-- **The inverse system `(iₙ,* Fₙ)` of `𝒪_X`-modules of Situation [Stacks, Tag 0CX4]**, whose
derived limit is the object `K` of [Stacks, Tag 0CX5]. -/
def pushforwardSystem : ℕᵒᵖ ⥤ Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 :=
  Functor.ofOpSequence (X := D.pushforwardModule) D.pushforwardTransition

/-- The `n`-th term of the inverse system is `iₙ,* Fₙ`. -/
@[simp]
lemma pushforwardSystem_obj (n : ℕ) : D.pushforwardSystem.obj (op n) = D.pushforwardModule n :=
  rfl

/-- The map from the `(n + 1)`-st to the `n`-th term of the inverse system is the transition map
`iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ`. -/
@[simp]
lemma pushforwardSystem_map_succ (n : ℕ) :
    D.pushforwardSystem.map (homOfLE (Nat.le_succ n)).op = D.pushforwardTransition n :=
  Functor.ofOpSequence_map_homOfLE_succ _ _

/-- `Fₙ` is quasi-coherent, being of finite presentation. -/
theorem isQuasicoherentOnSite_F (n : ℕ) : (D.F n).IsQuasicoherentOnSite :=
  have := D.finitelyPresented n
  inferInstance

/-- **The terms of the system are quasi-coherent**: `Fₙ` is, and `iₙ` is a closed immersion, hence
affine, so `iₙ,* Fₙ` is ([Stacks, Tag 07U8]). -/
theorem isQuasicoherentOnSite_pushforwardModule (n : ℕ) :
    (D.pushforwardModule n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_isAffineHom _ _ _ _ (D.isAffineHom_closedImmersion n)
    _ (D.isQuasicoherentOnSite_F n)

/-- The unit `Fₙ₊₁ ⟶ tₙ,* tₙ^* Fₙ₊₁` of a closed immersion is an epimorphism. -/
theorem epi_transitionAdjoint (n : ℕ) : Epi (D.transitionAdjoint n) := by
  have hi := D.isClosedImmersion_transition n
  have : Epi ((modulePullbackAdjunction D.B D.S D.containsLimitBase (D.transition n)).unit.app
      (D.F (n + 1))) :=
    epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated _ _ _ _ hi
      (fun M hM => (essImage_modulePushforward_iff _ _ _ _ hi M).2 hM) _
  unfold transitionAdjoint
  infer_instance

/-- The direct image along `iₙ₊₁` of the map `Fₙ₊₁ ⟶ tₙ,* Fₙ` adjoint to `φₙ` is an epimorphism. -/
theorem epi_map_transitionAdjoint (n : ℕ) :
    Epi ((modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion (n + 1))).map
      (D.transitionAdjoint n)) :=
  have := D.epi_transitionAdjoint n
  epi_modulePushforward_map_of_isClosedImmersion _ (D.isClosedImmersion_closedImmersion (n + 1)) _

/-- **The transition maps of the system are surjective.** -/
theorem epi_pushforwardTransition (n : ℕ) : Epi (D.pushforwardTransition n) := by
  have h := D.epi_map_transitionAdjoint n
  exact epi_comp' h inferInstance

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
