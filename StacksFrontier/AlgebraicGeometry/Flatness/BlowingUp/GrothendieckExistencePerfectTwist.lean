module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceDerivedLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

/-!
# Twisting the derived limit by a perfect complex: perfectness and base change

In Situation [Stacks, Tag 0CTC], let `K` be a derived limit in `D(𝒪_X)` of the system
`(iₙ,* ℱₙ)` of [Stacks, Tag 0CTD] and let `E` be a perfect object of `D(𝒪_X)`. Writing
`A = lim Aₙ`, the two objects

* `M = RΓ(X, K ⊗^𝐋 E)` and
* `N = RHom_X(E, K) = RΓ(X, R𝓗om(E, K))`

of `D(A)` are perfect, and their formation commutes with the base change `A → Aₙ`:
`M ⊗_A^𝐋 Aₙ = RΓ(Xₙ, ℱₙ ⊗^𝐋 E|_{Xₙ})` and `N ⊗_A^𝐋 Aₙ = RHom_{Xₙ}(E|_{Xₙ}, ℱₙ)`. Here
`E|_{Xₙ}` is the derived pullback of `E` to `Xₙ`, as the source prescribes. That is
[Stacks, Tag 0CTE]; both parts are proved unconditionally in
`GrothendieckExistencePerfectTensor.lean` and `GrothendieckExistencePerfectSheafHom.lean`.

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.globalSectionsTensor` and
  `...globalSectionsSheafHom` — the objects `M` and `N` of `D(A)`.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelGlobalSectionsTensor` and
  `...levelGlobalSectionsSheafHom` — the objects `RΓ(Xₙ, ℱₙ ⊗^𝐋 E|_{Xₙ})` and
  `RHom_{Xₙ}(E|_{Xₙ}, ℱₙ)` of `D(Aₙ)`.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.PerfectTwistData` — a perfect
  object `E` of `D(𝒪_X)` together with an object `K` as in [Stacks, Tag 0CTD].
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitTower` — a tower of
  objects of the `D(Aₙ)` which is perfect level by level, whose transitions become isomorphisms
  after derived base change, and which presents a given object of `D(A)` as its derived limit.

## Main results

* `...DerivedLimitTower.isPerfect_and_isIso_baseChange`
  — [Stacks, Tag 0CQG] applied to a tower over the rings of the situation.

## The shape of the proof

The source argues: each `Nₙ = RHom_{Xₙ}(E|_{Xₙ}, ℱₙ)` is perfect over `Aₙ` and its formation
commutes with base change (Derived Categories of Schemes, Lemma 36.30.7), so the transition maps
`Nₙ ⊗_{Aₙ}^𝐋 Aₙ₋₁ → Nₙ₋₁` are isomorphisms; `RHom_X(E, -)` commutes with products and hence with
derived limits, so `N = R lim Nₙ`; and then More on Algebra, Lemma 15.99.3 — which is
[Stacks, Tag 0CQG] — makes `R lim Nₙ` perfect with base change back to each `Nₙ`. Part (1) is
the same argument for the tower `Mₙ = RΓ(Xₙ, ℱₙ ⊗^𝐋 E|_{Xₙ})`.

The step carried out here is the last one, the one the source names: a tower over the rings of the
situation which is perfect level by level, whose transitions become isomorphisms after derived
base change, and which presents a given object of `D(A)` as its derived limit, is bundled as
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitTower`, and
[Stacks, Tag 0CQG] is applied to it, with the two hypotheses it makes on the tower of rings
discharged from the fields
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.transition_surjective` and
`...transition_locallyNilpotent` of Situation [Stacks, Tag 0CTC]. The derived limit is recorded in
the shape [Stacks, Tag 0CQG] states it — a map into the countable product, a connecting map, and
the requirement that the resulting triangle be distinguished.

The clauses of the tower are supplied, and [Stacks, Tag 0CTE] is proved, in the two files named
above: part (1) is
`...ExistenceSituation.DerivedLimitQCoh.isPerfect_and_isIso_tensorBaseChange`
and part (2) is
`...ExistenceSituation.DerivedLimitQCoh.isPerfect_and_isIso_sheafHomBaseChange`.

## Implementation notes

The derived category of `𝒪_X`-modules is taken at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model
[Stacks, Tag 0CTD] is stated at, so that its conclusion about `K` can be used verbatim. The
derived category of `A`-modules is taken at `HasDerivedCategory.standard`, which is the model
[Stacks, Tag 0CQG] is stated at; `AlgebraicGeometry.derivedGlobalSectionsOver` has a free
`HasDerivedCategory` binder for its target, so both choices can be met at once.

As in Situation [Stacks, Tag 0CTC], the index `n : ℕ` stands for the level `n + 1` of the source.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0CTC](https://stacks.math.columbia.edu/tag/0CTC)
* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
* [Stacks Project, Tag 0CQG](https://stacks.math.columbia.edu/tag/0CQG)
* [Stacks Project, Tag 0A1J](https://stacks.math.columbia.edu/tag/0A1J)
* [Stacks Project, Tag 0DID](https://stacks.math.columbia.edu/tag/0DID)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open StacksDraft.DerivedInverseLimit

universe u

namespace AlgebraicGeometry.GrothendieckExistence

namespace ExistenceSituation

local instance (priority := 10000) hasDerivedCategoryModuleCatStandard (R : Type u) [Ring R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

variable (S : ExistenceSituation.{u})

/-! ### The objects of the lemma -/

/-- The sheaf `ℱₙ` of the situation, read in `D(𝒪_{Xₙ})` in degree zero. -/
public def levelSheaf (n : ℕ) : DerivedCategory (schemeAt S.system S.X n).Modules :=
  (DerivedCategory.singleFunctor (schemeAt S.system S.X n).Modules 0).obj (S.F n)

/-- `E|_{Xₙ}`, the derived pullback of an object of `D(𝒪_X)` along `iₙ : Xₙ ⟶ X`. This is the
meaning the source fixes for the notation: the derived, not the naive, pullback. -/
public def levelRestriction (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (schemeAt S.system S.X n).Modules :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    (S.closedImmersion n).toLRSHom.toShHom).obj E

/-- `M = RΓ(X, K ⊗^𝐋 E)`, an object of `D(A)` for `A = lim Aₙ`. -/
public def globalSectionsTensor (K E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (ModuleCat.{u} ↑(limit S.system)) :=
  (derivedGlobalSectionsOver S.X.hom).obj
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      S.X.left.toRingedSpace.sheaf).obj K).obj E)

/-- `RΓ(Xₙ, ℱₙ ⊗^𝐋 E|_{Xₙ})`, an object of `D(Aₙ)`. -/
public def levelGlobalSectionsTensor (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n))) :=
  (derivedGlobalSectionsOver (pullback.snd S.X.hom (baseProjection S.system n))).obj
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (schemeAt S.system S.X n).toRingedSpace.sheaf).obj (S.levelSheaf n)).obj
        (S.levelRestriction n E))

/-- `N = RHom_X(E, K)`, an object of `D(A)`. It is realized as `RΓ(X, R𝓗om(E, K))`, the
`A`-linear derived global sections of the derived internal Hom, as in Cohomology, Section
20.44. -/
public def globalSectionsSheafHom (K E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (ModuleCat.{u} ↑(limit S.system)) :=
  (derivedGlobalSectionsOver S.X.hom).obj
    (((Stacks.SheafOfModules.derivedSheafHom S.X.left.sheaf).obj (op E)).obj K)

/-- `RHom_{Xₙ}(E|_{Xₙ}, ℱₙ)`, an object of `D(Aₙ)`, realized as
`RΓ(Xₙ, R𝓗om(E|_{Xₙ}, ℱₙ))`. -/
public def levelGlobalSectionsSheafHom (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n))) :=
  (derivedGlobalSectionsOver (pullback.snd S.X.hom (baseProjection S.system n))).obj
    (((Stacks.SheafOfModules.derivedSheafHom (schemeAt S.system S.X n).sheaf).obj
      (op (S.levelRestriction n E))).obj (S.levelSheaf n))

/-- A perfect object `E` of `D(𝒪_X)` together with an object `K` of `D(𝒪_X)` as in
[Stacks, Tag 0CTD], namely a derived limit of the system `(iₙ,* ℱₙ)`. These are the two data the
statement of [Stacks, Tag 0CTE] quantifies over. -/
public structure PerfectTwistData where
  /-- The perfect object `E` of `D(𝒪_X)`. -/
  E : DerivedCategory S.X.left.Modules
  /-- `E` is perfect, in the sense of [Stacks, Tag 08CM] for the ringed space `X`. -/
  isPerfect_E : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E
  /-- The object `K` of [Stacks, Tag 0CTD]. -/
  K : DerivedCategory S.X.left.Modules
  /-- `K` is a derived limit of the system `(iₙ,* ℱₙ)` in `D(𝒪_X)`, which is what
  [Stacks, Tag 0CTD] says about it. -/
  isDerivedLimit_K : IsDerivedLimit S.derivedPushforwardSystem K

/-! ### Towers over the rings of the situation -/

/-- A term `Lₙ` of a tower over the rings `Aₙ`, restricted along `A ⟶ Aₙ` to an object of
`D(A)`. -/
public def towerRestriction
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n)))) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} ↑(limit S.system)) :=
  (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj (L n)

/-- The transition `Lₙ₊₁ ⟶ Lₙ` of such a tower, read over `A`: the given transition over
`Aₙ₊₁`, followed by the comparison identifying successive restrictions of scalars with the
restriction along their composite. -/
public def towerTransition
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n))))
    (t : ∀ n : ℕ, L (n + 1) ⟶ (ModuleCat.restrictScalars
      (S.system.map (homOfLE (Nat.le_succ n)).op).hom).mapDerivedCategory.obj (L n))
    (n : ℕ) : S.towerRestriction L (n + 1) ⟶ S.towerRestriction L n :=
  (ModuleCat.restrictScalars (limit.π S.system (op (n + 1))).hom).mapDerivedCategory.map (t n) ≫
    (derivedRestrictScalarsComp (limit.π S.system (op (n + 1))).hom
      (S.system.map (homOfLE (Nat.le_succ n)).op).hom (limit.π S.system (op n)).hom
      (congrArg CommRingCat.Hom.hom
        ((limit.cone S.system).w (homOfLE (Nat.le_succ n)).op)).symm).hom.app (L n)

variable (Lv : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n))))
  (L : DerivedCategory (ModuleCat.{u} ↑(limit S.system)))

/-- A tower `(Lₙ)` of objects over the rings `Aₙ` of the situation which is perfect level by
level, whose transitions become isomorphisms after derived base change, and which presents a
given object `L` of `D(A)` as its derived limit.

The derived limit is recorded in the shape [Stacks, Tag 0CQG] consumes: a map `L ⟶ ∏ Lₙ`, a
connecting map, and the requirement that the resulting triangle be distinguished. -/
public structure DerivedLimitTower [HasProduct (S.towerRestriction Lv)] where
  /-- The transition `Lₙ₊₁ ⟶ Lₙ`, as a map over `Aₙ₊₁` into the restriction of `Lₙ`. -/
  transition : ∀ n : ℕ, Lv (n + 1) ⟶ (ModuleCat.restrictScalars
    (S.system.map (homOfLE (Nat.le_succ n)).op).hom).mapDerivedCategory.obj (Lv n)
  /-- Every term of the tower is perfect over its ring. -/
  isPerfect : ∀ n : ℕ, StacksDraft.Perfect.IsPerfect (Lv n)
  /-- Each transition becomes an isomorphism `Lₙ₊₁ ⊗_{Aₙ₊₁}^𝐋 Aₙ ⟶ Lₙ` after derived base
  change, which is the statement that the formation of `Lₙ` commutes with base change. -/
  comparison_isIso : ∀ n : ℕ, IsIso (derivedBaseChangeComparison
    (S.system.map (homOfLE (Nat.le_succ n)).op).hom (transition n))
  /-- The map from `L` into the countable product of the restricted terms. -/
  p : L ⟶ ∏ᶜ S.towerRestriction Lv
  /-- The connecting map of the derived-limit triangle. -/
  δ : ∏ᶜ S.towerRestriction Lv ⟶ L⟦(1 : ℤ)⟧
  /-- The derived-limit triangle is distinguished, which is what exhibits `L` as `R lim Lₙ`. -/
  triangle : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (S.towerRestriction Lv) n -
      Pi.π (S.towerRestriction Lv) (n + 1) ≫ S.towerTransition Lv transition n) δ ∈
    distTriang (DerivedCategory (ModuleCat.{u} ↑(limit S.system)))

/-- **[Stacks, Tag 0CQG] applied to a tower over the rings of Situation [Stacks, Tag 0CTC].**
The derived limit of such a tower is perfect over `A = lim Aₙ`, and its canonical derived
base-change map to each term of the tower is an isomorphism.

The two hypotheses Tag 0CQG makes on the tower of rings — that the transitions are surjective
with locally nilpotent kernels — are the fields `transition_surjective` and
`transition_locallyNilpotent` of the situation. -/
public theorem DerivedLimitTower.isPerfect_and_isIso_baseChange
    [HasProduct (S.towerRestriction Lv)] (T : S.DerivedLimitTower Lv L) :
    StacksDraft.Perfect.IsPerfect L ∧ ∀ n : ℕ, IsIso (derivedBaseChangeComparison
      (limit.π S.system (op n)).hom (T.p ≫ Pi.π (S.towerRestriction Lv) n)) :=
  derivedLimit_isPerfect_and_baseChange_iso.{u, u} S.system (limit.cone S.system)
    (limit.isLimit S.system) Lv T.transition S.transition_surjective S.transition_locallyNilpotent
    (Or.inl T.isPerfect) T.comparison_isIso L T.p T.δ T.triangle

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
