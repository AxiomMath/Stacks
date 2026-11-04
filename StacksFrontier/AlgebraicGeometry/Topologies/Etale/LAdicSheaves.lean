module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# ℓ-adic sheaves on the small étale site

An ℓ-adic sheaf on a Noetherian scheme is a compatible inverse system of constructible sheaves
of modules over the successive quotients `ℤ/ℓⁿℤ`. It is lisse when every finite-level sheaf is
locally constant.

## Main definitions

* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf`: the sheaf category at level `n`, with
  coefficients `ℤ/ℓⁿ⁺¹ℤ`.
* `AlgebraicGeometry.SmallEtale.finiteLevelRingHom`: the quotient map between consecutive
  coefficient rings.
* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.restrictScalars` and
  `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.scalarReduction`: the two directions of change
  of coefficients between consecutive levels.
* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.scalarReductionMap`: the map on scalar
  reductions canonically induced by a transition map.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf` and
  `AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom`: Tag 03UM's ℓ-adic sheaves and their morphisms.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.IsLisse`: local constancy at every finite level.

## Main results

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.category`: ℓ-adic sheaves form a category.
* `AlgebraicGeometry.SmallEtale.FiniteLevelSheaf.scalarReductionMap_comp`: the induced map on
  scalar reductions is the adjoint of the transition map.

## Implementation notes

Levels are indexed by `n : ℕ`, with level `n` carrying coefficients in `ℤ/ℓⁿ⁺¹ℤ`. Each
transition is a map to the restriction of scalars of the next level. Scalar reduction is
sheafified extension of scalars along `ℤ/ℓⁿ⁺²ℤ → ℤ/ℓⁿ⁺¹ℤ`, i.e.
`Sheaf.composeAndSheafify` of `ModuleCat.extendScalars`. The sheaf-level
extension/restriction adjunction canonically induces the reduction map out of the reduction of
the next level; the compatibility condition of the source says that this induced map is an
isomorphism. Morphisms are compatible families of module-sheaf morphisms.

The module universe is left free. The coefficient rings are `ZMod _`, which live in `Type 0`, so
`ModuleCat.extendRestrictScalarsAdj` — whose module universe is `max v u₂` for a target ring in
`Type u₂` — imposes no constraint here.

## References

* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.obj X.property)
  (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))]

/-- The small étale sheaf category at coefficients `ℤ/ℓⁿ⁺¹ℤ`. -/
public abbrev FiniteLevelSheaf (n : ℕ) :=
  Sheaf (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))

/-- The quotient homomorphism between consecutive coefficient rings. -/
public abbrev finiteLevelRingHom (n : ℕ) :
    ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (n + 1)) :=
  ZMod.castHom (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 2)) _

/-- Restriction of scalars from level `n` to level `n + 1`. -/
public abbrev FiniteLevelSheaf.restrictScalars (n : ℕ)
    (G : FiniteLevelSheaf.{u, m} B X ℓ n) : FiniteLevelSheaf.{u, m} B X ℓ (n + 1) :=
  (sheafCompose (SmallEtale.topology B X.obj X.property)
    (ModuleCat.restrictScalars.{m, 0, 0} (finiteLevelRingHom ℓ n))).obj G

/-- Sheafified scalar extension along the canonical quotient of coefficient rings. -/
public abbrev FiniteLevelSheaf.scalarReduction (n : ℕ)
    (F : FiniteLevelSheaf.{u, m} B X ℓ (n + 1)) : FiniteLevelSheaf.{u, m} B X ℓ n :=
  (Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
    (ModuleCat.extendScalars.{0, 0, m} (finiteLevelRingHom ℓ n))).obj F

/-- The map on scalar reductions canonically induced by a transition map, by the
extension/restriction adjunction on sheaves of modules. -/
public def FiniteLevelSheaf.scalarReductionMap (n : ℕ)
    (F : FiniteLevelSheaf.{u, m} B X ℓ (n + 1))
    (G : FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : F ⟶ G.restrictScalars B X ℓ n) :
    F.scalarReduction B X ℓ n ⟶ G :=
  ((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
    (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0}
      (finiteLevelRingHom ℓ n))).homEquiv F G).symm t

/-- The induced map on scalar reductions corresponds to the transition map under the
adjunction. -/
@[simp]
public theorem FiniteLevelSheaf.scalarReductionMap_comp (n : ℕ)
    (F : FiniteLevelSheaf.{u, m} B X ℓ (n + 1))
    (G : FiniteLevelSheaf.{u, m} B X ℓ n)
    (t : F ⟶ G.restrictScalars B X ℓ n) :
    (Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
      (ModuleCat.extendRestrictScalarsAdj.{m, 0, 0}
        (finiteLevelRingHom ℓ n))).homEquiv F G
      (scalarReductionMap B X ℓ n F G t) = t := by
  simp [scalarReductionMap]

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
  HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
    (ModuleCat.{m} (ZMod (ℓ ^ (n + 1))))]

/-- **Stacks 03UM.** An ℓ-adic sheaf is an inverse system of constructible `ℤ/ℓⁿℤ`-module
sheaves whose successive scalar reductions are isomorphisms. -/
@[stacks 03UM "objects",
  sga "5 V 3.1" "ℓ-adic étale case",
  sga "4½ Rapport 2.1" "Z_ℓ-sheaf definition",
  sga "5 V 3.1.1" "A=Z_ℓ, J=(ℓ), étale site",
  sga "5 VI 1.1.1", sga "5 VI 1.2" "Z_ℓ-sheaf definition"]
public structure LAdicSheaf [IsNoetherian X.obj] [Fact ℓ.Prime] where
  /-- The sheaf at each finite level. -/
  level : (n : ℕ) → FiniteLevelSheaf.{u, m} B X ℓ n
  /-- Every finite level is constructible. -/
  constructible : ∀ n, IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (level n)
  /-- The transition map from each level to the restriction of scalars of the previous one. -/
  transition : ∀ n, level (n + 1) ⟶ (level n).restrictScalars B X ℓ n
  /-- The induced map on scalar reductions is an isomorphism. -/
  reduction_isIso : ∀ n, IsIso
    (FiniteLevelSheaf.scalarReductionMap B X ℓ n (level (n + 1)) (level n)
      (transition n))

/-- **Stacks 03UM.** A morphism of ℓ-adic sheaves is a compatible family of morphisms at the
finite levels. -/
@[stacks 03UM "morphisms",
  sga "5 V 3.1" "morphisms, ℓ-adic case",
  sga "5 VI 1.1.1" "morphisms",
  sga "5 VI 1.2" "morphisms", sga "4½ Rapport 2.6" "hom(F,G)"]
public structure LAdicSheaf.Hom [IsNoetherian X.obj] [Fact ℓ.Prime]
    (F G : LAdicSheaf.{u, m} B X ℓ) where
  /-- The morphism at each finite level. -/
  app : ∀ n, F.level n ⟶ G.level n
  /-- The morphisms commute with the transition maps. -/
  naturality : ∀ n, app (n + 1) ≫ G.transition n =
    F.transition n ≫ (sheafCompose (SmallEtale.topology B X.obj X.property)
      (ModuleCat.restrictScalars.{m, 0, 0} (finiteLevelRingHom ℓ n))).map (app n)

/-- Two morphisms of ℓ-adic sheaves agreeing at every finite level are equal. -/
@[ext]
public theorem LAdicSheaf.Hom.ext [IsNoetherian X.obj] [Fact ℓ.Prime]
    {F G : LAdicSheaf.{u, m} B X ℓ} {f g : LAdicSheaf.Hom B X ℓ F G}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr
  funext n
  exact h n

/-- ℓ-adic sheaves form the category of compatible inverse systems. -/
public instance LAdicSheaf.category [IsNoetherian X.obj] [Fact ℓ.Prime] :
    Category (LAdicSheaf.{u, m} B X ℓ) where
  Hom := LAdicSheaf.Hom B X ℓ
  id F := ⟨fun _ => 𝟙 _, by intro n; simp⟩
  comp f g := ⟨fun n => f.app n ≫ g.app n, by
    intro n
    rw [Category.assoc, g.naturality n, ← Category.assoc, f.naturality n,
      Category.assoc, ← Functor.map_comp]⟩
  id_comp f := by ext n; simp
  comp_id f := by ext n; simp
  assoc f g h := by ext n; simp [Category.assoc]

/-- **Stacks 03UM.** A lisse ℓ-adic sheaf has locally constant sheaves at every finite
level. -/
@[stacks 03UM "lisse"]
public abbrev LAdicSheaf.IsLisse [IsNoetherian X.obj] [Fact ℓ.Prime]
    (F : LAdicSheaf.{u, m} B X ℓ) : Prop :=
  ∀ n, Stacks.ConstantSheaf.IsLocallyConstant
    (SmallEtale.topology B X.obj X.property) (F.level n)

end AlgebraicGeometry.SmallEtale

end
