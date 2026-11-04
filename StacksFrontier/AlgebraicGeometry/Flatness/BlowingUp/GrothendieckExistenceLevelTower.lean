module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceCoheratorLimit
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLeray
public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect

/-!
# The level tower of Grothendieck's existence theorem twisted by a perfect complex

In Situation [Stacks, Tag 0CTC], write `fₙ : Xₙ ⟶ Spec Aₙ` for the structure morphism of the base
change at level `n`, `iₙ : Xₙ ⟶ X` for the closed immersion and `tₙ : Xₙ ⟶ Xₙ₊₁` for the
transition. For an object `E` of `D(𝒪_X)` with derived restrictions `Eₙ = Liₙ^* E`, this file
builds the tower of [Stacks, Tag 0CTE] (1):

* the level objects `Mₙ = RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` of `D(Aₙ)`;
* the transition maps `Mₙ₊₁ ⟶ Mₙ` over `Aₙ₊₁`, read as maps into the restriction of scalars of
  `Mₙ` along `Aₙ₊₁ ⟶ Aₙ`. Each is `RΓ_{Aₙ₊₁}(Xₙ₊₁, -)` of the unit
  `ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁ ⟶ Rtₙ,* Ltₙ^*(ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁)`, followed by `Rtₙ,*` of the comparison
  `Ltₙ^*(ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁) ⟶ ℱₙ ⊗^𝐋 Eₙ` (the pullback–tensor comparison, the derived-to-ordinary
  comparison `Ltₙ^*ℱₙ₊₁ ⟶ tₙ^*ℱₙ₊₁ ≅ ℱₙ` of the situation, and `Ltₙ^* Eₙ₊₁ ≅ Eₙ`), and then the
  linear Leray identification `RΓ_{Aₙ₊₁}(Xₙ₊₁, Rtₙ,* -) = RΓ_{Aₙ}(Xₙ, -)` read over `Aₙ₊₁`.

## Implementation notes

The derived pullback and pushforward of ringed spaces and the derived tensor product used here
are those of [Stacks, Tag 0A1H] in this library, which exist only at
`CategoryTheory.HasDerivedCategory.standard`. Each declaration that needs them is scoped to that
model with `attribute [local instance 10000] HasDerivedCategory.standard in`.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0CTC](https://stacks.math.columbia.edu/tag/0CTC)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex
  derivedPullbackTensorIso)

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

/-! ### The squares of the situation -/

/-- The structure morphism `fₙ : Xₙ ⟶ Spec Aₙ` of the base change at level `n`. -/
abbrev levelStructure (n : ℕ) : schemeAt S.system S.X n ⟶ Spec (.of ↑(S.system.obj (op n))) :=
  pullback.snd S.X.hom (baseProjection S.system n)

/-- The ring map `A ⟶ Aₙ` out of the inverse limit. -/
abbrev limitProjection (n : ℕ) : ↑(limit S.system) →+* ↑(S.system.obj (op n)) :=
  (limit.π S.system (op n)).hom

/-- The transition `Aₙ₊₁ ⟶ Aₙ` of the rings. -/
abbrev ringTransition (n : ℕ) : ↑(S.system.obj (op (n + 1))) →+* ↑(S.system.obj (op n)) :=
  (S.system.map (homOfLE (Nat.le_succ n)).op).hom

/-- The square `iₙ ≫ (X ⟶ Spec A) = fₙ ≫ Spec (A ⟶ Aₙ)`. -/
theorem closedImmersion_comp_hom (n : ℕ) :
    S.closedImmersion n ≫ S.X.hom =
      S.levelStructure n ≫ Spec.map (CommRingCat.ofHom (S.limitProjection n)) :=
  pullback.condition

/-- The square `tₙ ≫ fₙ₊₁ = fₙ ≫ Spec (Aₙ₊₁ ⟶ Aₙ)`. -/
theorem transitionScheme_comp_levelStructure (n : ℕ) :
    S.transitionScheme n ≫ S.levelStructure (n + 1) =
      S.levelStructure n ≫ Spec.map (CommRingCat.ofHom (S.ringTransition n)) :=
  S.transition_snd n

/-- The ring maps `A ⟶ Aₙ₊₁ ⟶ Aₙ` compose to `A ⟶ Aₙ`. -/
theorem ringTransition_comp_limitProjection (n : ℕ) :
    S.limitProjection n = (S.ringTransition n).comp (S.limitProjection (n + 1)) :=
  (congrArg CommRingCat.Hom.hom ((limit.cone S.system).w (homOfLE (Nat.le_succ n)).op)).symm

/-- `Spec (Aₙ₊₁ ⟶ Aₙ)` followed by `Spec (A ⟶ Aₙ₊₁)` is `Spec (A ⟶ Aₙ)`. -/
theorem baseTransition_comp_baseProjection (n : ℕ) :
    baseTransition S.system n ≫ baseProjection S.system (n + 1) = baseProjection S.system n := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map ((limit.cone S.system).w (homOfLE (Nat.le_succ n)).op)

/-- **The base change at level `n` is the base change of the one at level `n + 1`**: the square
`tₙ ≫ fₙ₊₁ = fₙ ≫ Spec (Aₙ₊₁ ⟶ Aₙ)` is cartesian, by pasting with the cartesian square defining
`Xₙ₊₁`. -/
theorem isPullback_transitionScheme (n : ℕ) :
    IsPullback (S.transitionScheme n) (S.levelStructure n) (S.levelStructure (n + 1))
      (baseTransition S.system n) := by
  refine IsPullback.of_right ?_ (S.transition_snd n)
    (IsPullback.of_hasPullback S.X.hom (baseProjection S.system (n + 1)))
  rw [S.transition_fst n, S.baseTransition_comp_baseProjection n]
  exact IsPullback.of_hasPullback S.X.hom (baseProjection S.system n)

/-! ### The level objects -/

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `E ↦ Eₙ = Liₙ^* E`, the derived restriction of an object of `D(𝒪_X)` to `Xₙ`. -/
def levelPullback (n : ℕ) :
    DerivedCategory S.X.left.Modules ⥤ DerivedCategory (schemeAt S.system S.X n).Modules :=
  derivedPullback (S.closedImmersion n).toLRSHom.toShHom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The sheaf `ℱₙ` of the situation, read in `D(𝒪_{Xₙ})` in degree zero, at the standard model. -/
def levelSheafStandard (n : ℕ) : DerivedCategory (schemeAt S.system S.X n).Modules :=
  (DerivedCategory.singleFunctor (schemeAt S.system S.X n).Modules 0).obj (S.F n)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `ℱₙ ⊗^𝐋 Eₙ` in `D(𝒪_{Xₙ})`. -/
def levelTensorSheaf (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (schemeAt S.system S.X n).Modules :=
  ((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
    (S.levelSheafStandard n)).obj ((S.levelPullback n).obj E)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The level object `Mₙ = RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` of [Stacks, Tag 0CTE] (1)**, an object of
`D(Aₙ)`. -/
def levelTensor (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n))) :=
  (derivedGlobalSectionsOver (S.levelStructure n)).obj (S.levelTensorSheaf n E)

/-! ### The transition maps -/

/-- `tₙ ≫ iₙ₊₁ = iₙ` at the level of morphisms of ringed spaces. -/
theorem transitionScheme_toShHom_comp (n : ℕ) :
    (S.transitionScheme n).toLRSHom.toShHom ≫ (S.closedImmersion (n + 1)).toLRSHom.toShHom =
      (S.closedImmersion n).toLRSHom.toShHom :=
  congrArg (fun h : schemeAt S.system S.X n ⟶ S.X.left => h.toLRSHom.toShHom)
    (S.transition_fst n)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `Ltₙ^* Eₙ₊₁ ≅ Eₙ`: the derived pullbacks along `tₙ` and `iₙ₊₁` compose to the one along
`iₙ = tₙ ≫ iₙ₊₁`. -/
def levelPullbackTransitionIso (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    (derivedPullback (S.transitionScheme n).toLRSHom.toShHom).obj
        ((S.levelPullback (n + 1)).obj E) ≅
      (S.levelPullback n).obj E :=
  let e := Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (S.transitionScheme n).toLRSHom.toShHom (S.closedImmersion (n + 1)).toLRSHom.toShHom
  e.app E ≪≫ eqToIso (by
    rw [S.transitionScheme_toShHom_comp n]
    rfl)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `tₙ^* ℱₙ₊₁[0] ≅ ℱₙ[0]`: the degreewise pullback of the single complex is the single complex of
the pullback, followed by the comparison isomorphism `φₙ : tₙ^* ℱₙ₊₁ ≅ ℱₙ` of the situation. -/
def levelSheafPullbackComplexIso (n : ℕ) :
    DerivedCategory.Q.obj ((pullbackComplex (S.transitionScheme n).toLRSHom.toShHom).obj
      ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj
        (S.F (n + 1)))) ≅ S.levelSheafStandard n :=
  DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (StacksDraft.KFlat.modulePullback (S.transitionScheme n).toLRSHom.toShHom)
        (ComplexShape.up ℤ) 0).app (S.F (n + 1)) ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso (S.φ n)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (schemeAt S.system S.X n).Modules 0).app (S.F n)).symm

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `Ltₙ^* ℱₙ₊₁ ⟶ ℱₙ`: the comparison of the derived with the ordinary pullback of `ℱₙ₊₁` in
degree zero, followed by the comparison isomorphism `φₙ : tₙ^* ℱₙ₊₁ ≅ ℱₙ` of the situation. -/
def levelSheafTransition (n : ℕ) :
    (derivedPullback (S.transitionScheme n).toLRSHom.toShHom).obj (S.levelSheafStandard (n + 1)) ⟶
      S.levelSheafStandard n :=
  (derivedPullback (S.transitionScheme n).toLRSHom.toShHom).map
      ((DerivedCategory.singleFunctorIsoCompQ (schemeAt S.system S.X (n + 1)).Modules 0).hom.app
        (S.F (n + 1))) ≫
    (derivedPullbackNatTrans (S.transitionScheme n).toLRSHom.toShHom).app
      ((CochainComplex.singleFunctor (schemeAt S.system S.X (n + 1)).Modules 0).obj (S.F (n + 1))) ≫
    (S.levelSheafPullbackComplexIso n).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `Ltₙ^*(ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁) ⟶ ℱₙ ⊗^𝐋 Eₙ`: the pullback–tensor comparison of [Stacks, Tag 079U]
followed by `levelSheafTransition` and `levelPullbackTransitionIso` in the two factors. -/
def levelTensorSheafPullbackMap (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    (derivedPullback (S.transitionScheme n).toLRSHom.toShHom).obj (S.levelTensorSheaf (n + 1) E) ⟶
      S.levelTensorSheaf n E :=
  (derivedPullbackTensorIso (S.transitionScheme n).toLRSHom.toShHom).hom.app
      (S.levelSheafStandard (n + 1), (S.levelPullback (n + 1)).obj E) ≫
    ((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).map
      (S.levelSheafTransition n)).app _ ≫
    ((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
      (S.levelSheafStandard n)).map (S.levelPullbackTransitionIso n E).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁ ⟶ Rtₙ,*(ℱₙ ⊗^𝐋 Eₙ)` on `Xₙ₊₁`: the unit of `Ltₙ^* ⊣ Rtₙ,*` followed by
`Rtₙ,*` of `levelTensorSheafPullbackMap`. -/
def levelTensorSheafTransition (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    S.levelTensorSheaf (n + 1) E ⟶
      (derivedPushforward (S.transitionScheme n).toLRSHom.toShHom).obj (S.levelTensorSheaf n E) :=
  (derivedAdjunction (S.transitionScheme n).toLRSHom.toShHom).unit.app _ ≫
    (derivedPushforward (S.transitionScheme n).toLRSHom.toShHom).map
      (S.levelTensorSheafPullbackMap n E)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The transition `Mₙ₊₁ ⟶ Mₙ` of the level tower of [Stacks, Tag 0CTE] (1)**, over `Aₙ₊₁`:
`RΓ_{Aₙ₊₁}(Xₙ₊₁, -)` of `levelTensorSheafTransition`, followed by the linear Leray identification
`RΓ_{Aₙ₊₁}(Xₙ₊₁, Rtₙ,* -) = RΓ_{Aₙ}(Xₙ, -)` read over `Aₙ₊₁`. -/
def levelTensorTransition (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    S.levelTensor (n + 1) E ⟶
      (ModuleCat.restrictScalars (S.ringTransition n)).mapDerivedCategory.obj (S.levelTensor n E) :=
  (derivedGlobalSectionsOver (S.levelStructure (n + 1))).map (S.levelTensorSheafTransition n E) ≫
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.transitionScheme n)
      (S.levelStructure (n + 1)) (S.levelStructure n) (S.ringTransition n)
      (S.transitionScheme_comp_levelStructure n)).hom.app (S.levelTensorSheaf n E)

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
