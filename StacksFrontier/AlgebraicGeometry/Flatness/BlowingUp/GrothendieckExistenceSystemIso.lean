module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardSingle
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLerayComp
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelTower
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistencePerfectTwist
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceTransitionSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaAdjunctionUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaLocalStrictlyPerfect

/-!
# The pushed-forward system of Grothendieck's existence theorem twisted by a perfect complex

In Situation [Stacks, Tag 0CTC], let `E` be a perfect object of `D(𝒪_X)`. The `n`-th term of the
system `(iₙ,* ℱₙ)` of [Stacks, Tag 0CTD], twisted by `E` and pushed to `D(A)`, is the `n`-th level
object `Mₙ = RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` of [Stacks, Tag 0CTE] (1) read over `A`:

`RΓ_A(X, iₙ,* ℱₙ ⊗^𝐋 E) ≅ RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* E)`,

by `(iₙ,* ℱₙ)[0] ≅ Riₙ,*(ℱₙ[0])`, the projection formula [Stacks, Tag 0B54] and the linear Leray
identification. This is the identification through which the source writes
`R Γ(X, E ⊗^𝐋 K) = R lim R Γ(X_n, E_n ⊗^𝐋 K_n)` in the proof of [Stacks, Tag 0CTE].

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelTensorRestrictionIso` — the
  identification above.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelTensorMap` — functoriality of
  the level objects in `E`.

## Main results

* `...levelTensorRestrictionIso_naturality` — naturality in `E`.
* `...levelTensorRestrictionIso_comm_of` — the compatibility with the transitions of the system
  and of the level tower, reduced to a square in `D(𝒪_X)`.
* `...levelPushforwardTensorMap_comm` — that square, from
  `AlgebraicGeometry.GrothendieckExistence.tensor_pushforwardTransition_comp_projectionFormula`.
* `...levelTensorRestrictionIso_comm` — the compatibility with the transitions.

## Implementation notes

All declarations that mention the derived pushforward, pullback or tensor product of ringed spaces
are at the standard model `HasDerivedCategory.standard`, scoped to the declaration, since those
functors exist only there. The diagram chases are carried out in bare categories
(`chase_comm`) and instantiated once: the scheme spelling `X.Modules` of the derived global
sections and the ringed-space spelling of the other functors are definitionally but not reducibly
equal, which defeats rewriting in the mixed goals.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- The inclusion `iₙ : Xₙ ⟶ X` of the base change at level `n` is a closed immersion. -/
instance isClosedImmersion_closedImmersion (n : ℕ) : IsClosedImmersion (S.closedImmersion n) :=
  S.closedSchemeProjection n

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ_A(X, Riₙ,* ℱₙ ⊗^𝐋 E) ≅ RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)` read over `A`, for `E` perfect: the
projection formula, then the linear Leray identification. -/
def levelPushforwardTensorIso (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    (derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
          ((derivedPushforward (S.closedImmersion n).toLRSHom.toShHom).obj
            (S.levelSheafStandard n))).obj E) ≅
      S.towerRestriction (fun m => S.levelTensor m E) n :=
  (derivedGlobalSectionsOver S.X.hom).mapIso
      (@asIso _ _ _ _ (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        (S.closedImmersion n).toLRSHom.toShHom (S.levelSheafStandard n) E)
        (Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isPerfect
          (S.closedImmersion n).toLRSHom.toShHom (S.levelSheafStandard n) E hE)) ≪≫
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n) S.X.hom
      (S.levelStructure n) (S.limitProjection n) (S.closedImmersion_comp_hom n)).app
        (S.levelTensorSheaf n E)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The `n`-th term of the pushed-forward system, twisted by a perfect `E`, is the `n`-th level
object read over `A`:** `RΓ_A(X, iₙ,* ℱₙ ⊗^𝐋 E) ≅ RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Eₙ)`. It is
`(iₙ,* ℱₙ)[0] ≅ Riₙ,*(ℱₙ[0])` (`closedImmersionDerivedPushforwardSingleIso`), the projection
formula of [Stacks, Tag 0B54], and the linear Leray identification. -/
def levelTensorRestrictionIso (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    (derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
          (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E) ≅
      S.towerRestriction (fun m => S.levelTensor m E) n :=
  (derivedGlobalSectionsOver S.X.hom).mapIso
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).mapIso
        ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).app (S.F n))).app E) ≪≫
    S.levelPushforwardTensorIso n E hE

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The three factors of `levelTensorRestrictionIso`. -/
theorem levelTensorRestrictionIso_hom (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    (S.levelTensorRestrictionIso n E hE).hom =
      (derivedGlobalSectionsOver S.X.hom).map
          (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
            ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).hom.app
              (S.F n))).app E) ≫
        (derivedGlobalSectionsOver S.X.hom).map
          (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
            (S.closedImmersion n).toLRSHom.toShHom (S.levelSheafStandard n) E) ≫
        (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n)
          S.X.hom (S.levelStructure n) (S.limitProjection n)
            (S.closedImmersion_comp_hom n)).hom.app (S.levelTensorSheaf n E) :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The level objects are functorial in `E`: `RΓ_{Aₙ}(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* u)`. -/
def levelTensorMap (n : ℕ) {E E' : DerivedCategory S.X.left.Modules} (u : E ⟶ E') :
    S.levelTensor n E ⟶ S.levelTensor n E' :=
  (derivedGlobalSectionsOver (S.levelStructure n)).map
    (((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
      (S.levelSheafStandard n)).map ((S.levelPullback n).map u))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`levelTensorRestrictionIso` is natural in the perfect object `E`.** -/
theorem levelTensorRestrictionIso_naturality (n : ℕ) {E E' : DerivedCategory S.X.left.Modules}
    (u : E ⟶ E')
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E)
    (hE' : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E') :
    (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
          (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).map u) ≫
      (S.levelTensorRestrictionIso n E' hE').hom =
    (S.levelTensorRestrictionIso n E hE).hom ≫
      (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map
        (S.levelTensorMap n u) := by
  have h₁ := ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
    ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).hom.app
      (S.F n))).naturality u
  have h₂ := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
    (S.closedImmersion n).toLRSHom.toShHom (S.levelSheafStandard n) u
  have h₃ := (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n)
    S.X.hom (S.levelStructure n) (S.limitProjection n)
    (S.closedImmersion_comp_hom n)).hom.naturality
      (((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
        (S.levelSheafStandard n)).map ((S.levelPullback n).map u))
  have key : ∀ {P Q R T : DerivedCategory S.X.left.Modules} {a : P ⟶ Q} {b : Q ⟶ T} {c : P ⟶ R}
      {d : R ⟶ T}, a ≫ b = c ≫ d →
      (derivedGlobalSectionsOver S.X.hom).map a ≫ (derivedGlobalSectionsOver S.X.hom).map b =
        (derivedGlobalSectionsOver S.X.hom).map c ≫ (derivedGlobalSectionsOver S.X.hom).map d :=
    fun h => by rw [← Functor.map_comp, h, Functor.map_comp]
  have S1 := key h₁
  have S2 := key h₂
  rw [levelTensorRestrictionIso_hom, levelTensorRestrictionIso_hom]
  exact ((reassoc_of% S1) _).trans ((congrArg _ (((reassoc_of% S2) _).trans
    (congrArg _ h₃))).trans
      ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).symm)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The `D(𝒪_X)`-level part of `levelTensorRestrictionIso`:
`iₙ,* ℱₙ ⊗^𝐋 E ⟶ Riₙ,*(ℱₙ ⊗^𝐋 Eₙ)`, the single-object comparison followed by the projection
formula. -/
def levelPushforwardTensorMap (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
        (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E ⟶
      (derivedPushforward (S.closedImmersion n).toLRSHom.toShHom).obj (S.levelTensorSheaf n E) :=
  ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
      ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).hom.app (S.F n))).app E ≫
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      (S.closedImmersion n).toLRSHom.toShHom (S.levelSheafStandard n) E

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `levelTensorRestrictionIso` is `RΓ_A(X, -)` of `levelPushforwardTensorMap` followed by the
linear Leray identification. -/
theorem levelTensorRestrictionIso_hom_eq (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    (S.levelTensorRestrictionIso n E hE).hom =
      (derivedGlobalSectionsOver S.X.hom).map (S.levelPushforwardTensorMap n E) ≫
        (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.closedImmersion n)
          S.X.hom (S.levelStructure n) (S.limitProjection n)
            (S.closedImmersion_comp_hom n)).hom.app (S.levelTensorSheaf n E) :=
  (S.levelTensorRestrictionIso_hom n E hE).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((derivedGlobalSectionsOver S.X.hom).map_comp _ _).symm))

/-- The diagram chase behind `levelTensorRestrictionIso_comm_of`, in bare categories. -/
private theorem chase_comm {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    (F : 𝒞 ⥤ 𝒟) (G : ℰ ⥤ 𝒟)
    {P Q C D W W' : 𝒞} {U₀ Y₀ Y₁ : ℰ} {T : 𝒟} (x : P ⟶ Q) (a : Q ⟶ W') (a' : P ⟶ C)
    (g : C ⟶ D) (c : D ⟶ W) (e : W ⟶ W') (L : F.obj W' ⟶ T) (L₁ : F.obj C ⟶ G.obj U₀)
    (L₂ : F.obj D ⟶ G.obj Y₀) (h : U₀ ⟶ Y₀) (l : Y₀ ⟶ Y₁) (r : G.obj Y₁ ⟶ T)
    (L₃ : F.obj W ⟶ T)
    (hN : F.map g ≫ L₂ = L₁ ≫ G.map h) (hC : L₂ ≫ G.map l ≫ r = F.map c ≫ L₃)
    (hK : L₃ = F.map e ≫ L) (hS : x ≫ a = a' ≫ g ≫ c ≫ e) :
    F.map x ≫ F.map a ≫ L = (F.map a' ≫ L₁) ≫ G.map (h ≫ l) ≫ r := by
  rw [← F.map_comp_assoc, hS]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hK, ← hC, reassoc_of% hN]

/-- `(tₙ ≫ iₙ₊₁) ≫ (X ⟶ Spec A) = fₙ ≫ Spec (A ⟶ Aₙ)`. -/
theorem transitionScheme_comp_closedImmersion_comp_hom (n : ℕ) :
    (S.transitionScheme n ≫ S.closedImmersion (n + 1)) ≫ S.X.hom =
      S.levelStructure n ≫ Spec.map (CommRingCat.ofHom (S.limitProjection n)) := by
  rw [S.transition_fst n]
  exact S.closedImmersion_comp_hom n

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Reduction of the compatibility of `levelTensorRestrictionIso` with the transitions to
`D(𝒪_X)`.** If the sheaf-level square `hS` commutes, then `levelTensorRestrictionIso` carries the
transition of the pushed-forward system to the transition of the restricted level tower. The
passage uses the naturality of the linear Leray identification, its compatibility with the
composite `tₙ ≫ iₙ₊₁` and its transport along `tₙ ≫ iₙ₊₁ = iₙ`. -/
theorem levelTensorRestrictionIso_comm_of (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E)
    (hS : ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
          (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)).app E ≫
        S.levelPushforwardTensorMap n E =
      S.levelPushforwardTensorMap (n + 1) E ≫
        (derivedPushforward (S.closedImmersion (n + 1)).toLRSHom.toShHom).map
          (S.levelTensorSheafTransition n E) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          (S.transitionScheme n).toLRSHom.toShHom
            (S.closedImmersion (n + 1)).toLRSHom.toShHom).hom.app (S.levelTensorSheaf n E) ≫
        eqToHom (by rw [← S.transitionScheme_toShHom_comp n])) :
    (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
          (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)).app E) ≫
      (S.levelTensorRestrictionIso n E hE).hom =
    (S.levelTensorRestrictionIso (n + 1) E hE).hom ≫
      S.towerTransition (fun m => S.levelTensor m E) (fun m => S.levelTensorTransition m E) n := by
  have hC := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_comp
    (S.transitionScheme n) (S.closedImmersion (n + 1)) S.X.hom (S.levelStructure (n + 1))
    (S.levelStructure n) (S.limitProjection (n + 1)) (S.ringTransition n) (S.limitProjection n)
    (S.ringTransition_comp_limitProjection n) (S.closedImmersion_comp_hom (n + 1))
    (S.transitionScheme_comp_levelStructure n) (S.transitionScheme_comp_closedImmersion_comp_hom n)
    (S.levelTensorSheaf n E)
  have hK := derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso_congr S.X.hom
    (S.levelStructure n) (S.limitProjection n) (S.transition_fst n).symm
    (S.closedImmersion_comp_hom n) (S.transitionScheme_comp_closedImmersion_comp_hom n)
    (S.levelTensorSheaf n E)
  have hN := (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso
    (S.closedImmersion (n + 1)) S.X.hom (S.levelStructure (n + 1)) (S.limitProjection (n + 1))
    (S.closedImmersion_comp_hom (n + 1))).hom.naturality (S.levelTensorSheafTransition n E)
  rw [levelTensorRestrictionIso_hom_eq, levelTensorRestrictionIso_hom_eq]
  have hC' := ((Iso.eq_inv_comp ((derivedGlobalSectionsOver S.X.hom).mapIso
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
        (S.transitionScheme n).toLRSHom.toShHom
          (S.closedImmersion (n + 1)).toLRSHom.toShHom).app (S.levelTensorSheaf n E)))).mp hC).symm
  exact chase_comm (derivedGlobalSectionsOver S.X.hom)
    (ModuleCat.restrictScalars (S.limitProjection (n + 1))).mapDerivedCategory
    _ _ _ _ _ _ _ _ _ _ _ _ _ hN hC' hK hS

/-- The transition `tₙ : Xₙ ⟶ Xₙ₊₁` is a closed immersion: `tₙ ≫ iₙ₊₁ = iₙ` with `iₙ` and
`iₙ₊₁` closed immersions. -/
instance isClosedImmersion_transitionScheme (n : ℕ) : IsClosedImmersion (S.transitionScheme n) :=
  haveI : IsClosedImmersion (S.transitionScheme n ≫ S.closedImmersion (n + 1)) := by
    rw [S.transition_fst n]
    exact S.closedSchemeProjection n
  IsClosedImmersion.of_comp_isClosedImmersion _ (S.closedImmersion (n + 1))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `levelSheafTransition` is the comparison `Ltₙ^*(ℱₙ₊₁[0]) ⟶ ℱₙ[0]` induced by `φₙ`. -/
theorem levelSheafTransition_eq (n : ℕ) :
    S.levelSheafTransition n = derivedSingleTransitionOf (S.transitionScheme n) (S.φ n) :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The `D(𝒪_X)`-square of `levelTensorRestrictionIso_comm_of`.** `levelPushforwardTensorMap`
carries the transition of the pushed-forward system, tensored with `E`, to `Riₙ₊₁,*` of
`levelTensorSheafTransition` followed by the composition isomorphism along `tₙ ≫ iₙ₊₁ = iₙ`. This
is `tensor_pushforwardTransition_comp_projectionFormula` at `tₙ`, `iₙ₊₁`, `iₙ` and `φₙ`. -/
theorem levelPushforwardTensorMap_comm (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
          (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)).app E ≫
        S.levelPushforwardTensorMap n E =
      S.levelPushforwardTensorMap (n + 1) E ≫
        (derivedPushforward (S.closedImmersion (n + 1)).toLRSHom.toShHom).map
          (S.levelTensorSheafTransition n E) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          (S.transitionScheme n).toLRSHom.toShHom
            (S.closedImmersion (n + 1)).toLRSHom.toShHom).hom.app (S.levelTensorSheaf n E) ≫
        eqToHom (by rw [← S.transitionScheme_toShHom_comp n]) :=
  (congrArg (fun f => ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map f).app E ≫
      S.levelPushforwardTensorMap n E)
    (congrArg (DerivedCategory.singleFunctor S.X.left.Modules 0).map
      (S.pushforwardSystem_map_succ n))).trans
    (tensor_pushforwardTransition_comp_projectionFormula (S.transitionScheme n) (S.φ n)
      (S.closedImmersion (n + 1)) (S.closedImmersion n) (S.transition_fst n) E
      (S.levelSheafTransition n) (S.levelSheafTransition_eq n))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`levelTensorRestrictionIso` is compatible with the transitions.** For `E` perfect,
`RΓ_A(X, iₙ₊₁,* ℱₙ₊₁ ⊗^𝐋 E) ≅ RΓ_{Aₙ₊₁}(Xₙ₊₁, ℱₙ₊₁ ⊗^𝐋 Eₙ₊₁)` and the same identification at `n`
carry the transition of the pushed-forward system of [Stacks, Tag 0CTD], twisted by `E`, to the
transition of the level tower of [Stacks, Tag 0CTE] (1) read over `A`. -/
theorem levelTensorRestrictionIso_comm (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) :
    (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
          (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)).app E) ≫
      (S.levelTensorRestrictionIso n E hE).hom =
    (S.levelTensorRestrictionIso (n + 1) E hE).hom ≫
      S.towerTransition (fun m => S.levelTensor m E) (fun m => S.levelTensorTransition m E) n :=
  S.levelTensorRestrictionIso_comm_of n E hE (S.levelPushforwardTensorMap_comm n E)

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
