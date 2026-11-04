module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeDifferential
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsSquare
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTowerSquare
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget

/-!
# The stalk of the comparison map of two towers of sheaves of rings

Let `R ⟶ A ⟶ C` and `R ⟶ B ⟶ C` be two towers of sheaves of commutative rings on a topological
space `T` with the same composite `R ⟶ C`, say `p ≫ q = bc ≫ s`.  Composing the base-change map
`NL_{A/R} ⊗_A C ⟶ NL_{C/R}` of Stacks 0E1Y for the first tower with the relative map
`NL_{C/R} ⟶ NL_{C/B}` of Stacks 0E1Y for the second gives

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`,

the map a base-change statement about a square of schemes is built from.  This file computes its
stalk at a point `x` of `T` and deduces that the stalk is a quasi-isomorphism from the
corresponding ring-level statement about the stalk rings.

Both complexes vanish outside degrees `-1` and `0`, and all four of their nonzero stalks are
identified with the four terms of the ring-level comparison
`NaiveCotangent.nlExtensionBaseChangeMap`: the source by
`Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivNegOne` and its degree `0`
companion, the target by `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and
`stalkLegZeroLinear` (Stacks 0D09).  Through those four identifications the stalk of the map is
the comparison attached to the composite `Rₓ[Aₓ] ⟶ Rₓ[Cₓ] ⟶ Bₓ[Cₓ]` of morphisms of canonical
presentations of the stalk rings, and `CochainComplex.quasiIso_of_isZero_X_of_addEquiv` turns the
ring-level quasi-isomorphy into quasi-isomorphy of the stalk of the map of sheaves.

The ring-level hypothesis is asked for in the form "*every* morphism of extensions
`Rₓ[Aₓ] ⟶ Bₓ[Cₓ]` induces a quasi-isomorphism".  That is no stronger than asking it for the one
morphism the geometry produces: any two morphisms of extensions induce homotopic chain maps
(`NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_congr`).

## Main definitions

* `Stacks.NaiveCotangentTowerStalk.homCongrEq`: a morphism of extensions read against equal
  comparison algebra structures on the two base rings.
* `Stacks.NaiveCotangentTowerStalk.stalkTowerHomBase`,
  `Stacks.NaiveCotangentTowerStalk.stalkTowerHomRel` and
  `Stacks.NaiveCotangentTowerStalk.stalkTowerHom`: the two morphisms of canonical presentations of
  the stalk rings attached to the two factors of the map, and their composite.
* `Stacks.NaiveCotangentTowerStalk.towerComposite`: the map
  `NL_{A/R} ⊗_A C ⟶ NL_{C/B}` itself, the base-change map followed by the canonical map of the
  square with vertical morphisms `bc` and `𝟙 C`.

## Main results

* `Stacks.NaiveCotangentTowerStalk.algebraStalk_id`: the algebra structure a stalk gets from the
  identity morphism of a sheaf of rings is the identity algebra structure.
* `Stacks.NaiveCotangentTowerStalk.cotangentMap_homCongrEq`,
  `cotangentSpaceMap_homCongrEq`, `nlExtensionBaseChangeMap_f₁_homCongrEq` and
  `nlExtensionBaseChangeMap_f₀_homCongrEq`: the functorial maps of a morphism of extensions do not
  change when the comparison algebra structures are replaced by equal ones.
* `Stacks.NaiveCotangentTowerStalk.stalkLegNegOneLinear_towerComposite` and
  `stalkLegZeroLinear_towerComposite`: **the stalk of the map**, in degrees `-1` and `0`.
* `Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite`: **the stalk of the
  map is a quasi-isomorphism** as soon as the ring-level comparison of the stalks is one.

## Implementation notes

**The identity instances.**  The base-change factor is the canonical map of the square whose left
vertical morphism is `𝟙 R`, and the relative factor is the canonical map of the square whose
right vertical morphism is `𝟙 C`.  Accordingly
`Stacks.NaiveCotangentAffineStalkLegs.generatorsSelfStalkHomOfSquare` presents the two morphisms
of extensions against the algebra structures `Rₓ`-over-`Rₓ` and `Cₓ`-over-`Cₓ` that the *stalks
of those identity morphisms* define, and those are not the identity algebra structures: the stalk
functor does not preserve identities definitionally, since it is a colimit.  Every ring-level
lemma about a composite of morphisms of extensions is stated against the identity algebra
structures, so the two presentations have to be reconciled.  `algebraStalk_id` proves the two
algebra structures *equal*, and `homCongrEq` moves a morphism of extensions along such an
equality; the four `_homCongrEq` lemmas say that the functorial maps are unchanged, each by
substituting the equality and `rfl`.  An equality of instances is what is needed and what is
available: the two structures are not definitionally equal, so no amount of unfolding reconciles
them, and a mere agreement of their `algebraMap`s does not suffice either —
`Algebra.Extension.CotangentSpace.map` is a base change over the comparison and changes with it.

**Why the proof is split.**  The two degreewise identifications and the deduction of
quasi-isomorphy are separate declarations rather than steps of one proof: each of them elaborates a
statement mentioning both complexes of sheaves, all four stalk identifications and the ring-level
comparison, and three such elaborations in a single declaration exhaust the heartbeat budget.

**The instance demotion.**  `CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat`,
`hasSheafifyAddCommGrpCat` and `wEqualsLocallyBijectiveAddCommGrpCat` are declared for an
arbitrary site and therefore outrank, wherever they are in scope, the instances Mathlib provides
directly for a small site; they reach sheafification through an essentially small model, hence
through a choice of left adjoint, and reducing a term that mentions them unfolds
`Classical.indefiniteDescription`.  The topology of opens of a space is small, so the
`attribute [local instance 1]` block below demotes them for this file, exactly as in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeSpace`.

**Term-mode proofs.**  `rw` is unusable on the goals below: the pure tensors of
`ModuleCat.ExtendScalars` carry a `Module.compHom` instance which is not type-correct at
`implicit` transparency against the `Module` of the `restrictScalars` object, so `kabstract`
rejects the target outright.  The identifications are therefore chains of `Eq.trans` and
`congrArg`.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change and
  relative maps of naive cotangent complexes of a tower of sheaves of rings.
* [Stacks Project, Tag 08TK](https://stacks.math.columbia.edu/tag/08TK), the canonical map
  attached to a square of sheaves of rings on a space.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 0FJZ](https://stacks.math.columbia.edu/tag/0FJZ), flat base change for the
  naive cotangent complex, which consumes this statement at every point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.NaiveCotangentAffineStalkLegs
open Stacks.NaiveCotangentStalkBaseChange
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareBase stalkIsScalarTowerSquareTarget)

universe u

noncomputable section

namespace Stacks.NaiveCotangentTowerStalk

/-! ### Reading a morphism of extensions against equal comparison algebra structures -/

/-- **A morphism of extensions read against equal comparison algebra structures.**  The type
`Algebra.Extension.Hom P P'` depends on the two comparison algebra structures `Algebra R R'` and
`Algebra S S'`, so a morphism presented against one pair has to be transported before it can be
fed to a lemma stated against another; when the two pairs are equal, the transport is a
substitution. -/
def homCongrEq {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S'] {P : Algebra.Extension R S} {P' : Algebra.Extension R' S'}
    (i₁ i₂ : Algebra R R') (j₁ j₂ : Algebra S S') (hi : i₁ = i₂) (hj : j₁ = j₂)
    (h : @Algebra.Extension.Hom R S _ _ _ P R' S' _ _ _ P' i₁ j₁) :
    @Algebra.Extension.Hom R S _ _ _ P R' S' _ _ _ P' i₂ j₂ := hi ▸ hj ▸ h

/-- The conormal map of a morphism of extensions does not change when the comparison algebra
structures are replaced by equal ones. -/
theorem cotangentMap_homCongrEq {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [Algebra R S] [Algebra R' S'] {P : Algebra.Extension R S}
    {P' : Algebra.Extension R' S'}
    (i₁ i₂ : Algebra R R') (j₁ j₂ : Algebra S S') (hi : i₁ = i₂) (hj : j₁ = j₂)
    (h : @Algebra.Extension.Hom R S _ _ _ P R' S' _ _ _ P' i₁ j₁) (k : Algebra R S')
    (t₁ : @IsScalarTower R R' S' (@Algebra.toSMul R R' _ _ i₁) _ (@Algebra.toSMul R S' _ _ k))
    (t₂ : @IsScalarTower R R' S' (@Algebra.toSMul R R' _ _ i₂) _ (@Algebra.toSMul R S' _ _ k))
    (y : P.Cotangent) :
    @Algebra.Extension.Cotangent.map R S _ _ _ P R' S' _ _ _ P' i₁ j₁ k t₁ h y
      = @Algebra.Extension.Cotangent.map R S _ _ _ P R' S' _ _ _ P' i₂ j₂ k t₂
          (homCongrEq i₁ i₂ j₁ j₂ hi hj h) y := by
  subst hi; subst hj; rfl

/-- The cotangent-space map of a morphism of extensions does not change when the comparison
algebra structures are replaced by equal ones. -/
theorem cotangentSpaceMap_homCongrEq {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [Algebra R S] [Algebra R' S'] {P : Algebra.Extension R S}
    {P' : Algebra.Extension R' S'}
    (i₁ i₂ : Algebra R R') (j₁ j₂ : Algebra S S') (hi : i₁ = i₂) (hj : j₁ = j₂)
    (h : @Algebra.Extension.Hom R S _ _ _ P R' S' _ _ _ P' i₁ j₁) (k : Algebra R S')
    (t₁ : @IsScalarTower R R' S' (@Algebra.toSMul R R' _ _ i₁) _ (@Algebra.toSMul R S' _ _ k))
    (t₂ : @IsScalarTower R R' S' (@Algebra.toSMul R R' _ _ i₂) _ (@Algebra.toSMul R S' _ _ k))
    (y : P.CotangentSpace) :
    @Algebra.Extension.CotangentSpace.map R S _ _ _ P R' S' _ _ _ P' i₁ j₁ k t₁ h y
      = @Algebra.Extension.CotangentSpace.map R S _ _ _ P R' S' _ _ _ P' i₂ j₂ k t₂
          (homCongrEq i₁ i₂ j₁ j₂ hi hj h) y := by
  subst hi; subst hj; rfl

/-- The degree `-1` component of the comparison `NL(α) ⊗ T ⟶ NL(β)` does not change when the
comparison algebra structure of the base rings is replaced by an equal one. -/
theorem nlExtensionBaseChangeMap_f₁_homCongrEq {R S T R' : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing R'] [Algebra R S] [Algebra S T] [Algebra R' T] [Algebra R T]
    {P : Algebra.Extension R S} {Q : Algebra.Extension R' T}
    (i₁ i₂ : Algebra R R') (hi : i₁ = i₂)
    (h : @Algebra.Extension.Hom R S _ _ _ P R' T _ _ _ Q i₁ _)
    (t₁ : @IsScalarTower R R' T (@Algebra.toSMul R R' _ _ i₁) _ _)
    (t₂ : @IsScalarTower R R' T (@Algebra.toSMul R R' _ _ i₂) _ _)
    (m : (NaiveCotangent.nlExtensionBaseChange P T).X₁) :
    (@NaiveCotangent.nlExtensionBaseChangeMap R S T _ _ _ _ _ R' _ i₁ _ _ t₁ P Q h).f₁ m =
      (@NaiveCotangent.nlExtensionBaseChangeMap R S T _ _ _ _ _ R' _ i₂ _ _ t₂ P Q
        (homCongrEq i₁ i₂ _ _ hi rfl h)).f₁ m := by
  subst hi; rfl

/-- The degree `0` component of the comparison `NL(α) ⊗ T ⟶ NL(β)` does not change when the
comparison algebra structure of the base rings is replaced by an equal one. -/
theorem nlExtensionBaseChangeMap_f₀_homCongrEq {R S T R' : Type u} [CommRing R] [CommRing S]
    [CommRing T] [CommRing R'] [Algebra R S] [Algebra S T] [Algebra R' T] [Algebra R T]
    {P : Algebra.Extension R S} {Q : Algebra.Extension R' T}
    (i₁ i₂ : Algebra R R') (hi : i₁ = i₂)
    (h : @Algebra.Extension.Hom R S _ _ _ P R' T _ _ _ Q i₁ _)
    (t₁ : @IsScalarTower R R' T (@Algebra.toSMul R R' _ _ i₁) _ _)
    (t₂ : @IsScalarTower R R' T (@Algebra.toSMul R R' _ _ i₂) _ _)
    (m : (NaiveCotangent.nlExtensionBaseChange P T).X₀) :
    (@NaiveCotangent.nlExtensionBaseChangeMap R S T _ _ _ _ _ R' _ i₁ _ _ t₁ P Q h).f₀ m =
      (@NaiveCotangent.nlExtensionBaseChangeMap R S T _ _ _ _ _ R' _ i₂ _ _ t₂ P Q
        (homCongrEq i₁ i₂ _ _ hi rfl h)).f₀ m := by
  subst hi; rfl

/-! ### The stalk of the identity -/

/-- **The algebra structure a stalk gets from the identity morphism of a sheaf of rings is the
identity algebra structure.**  It is not that structure definitionally: the stalk functor is a
colimit, so it does not preserve identities on the nose. -/
theorem algebraStalk_id {T : TopCat.{u}}
    (D : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (z : T) :
    algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 D)) z =
      Algebra.id (ToType (TopCat.Presheaf.stalk D.obj z)) :=
  congrArg RingHom.toAlgebra (by
    rw [show CategoryTheory.InducedCategory.Hom.hom (𝟙 D) = 𝟙 D.obj from rfl,
      CategoryTheory.Functor.map_id]
    rfl)

attribute [local instance 1]
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable {T : TopCat.{u}}
  (R A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (p : R ⟶ A) (q : A ⟶ C) (bc : R ⟶ B) (s : B ⟶ C) (z : T)

/-- The morphism `Rₓ[Aₓ] ⟶ Rₓ[Cₓ]` of canonical presentations of the stalks attached to the
base-change factor of the tower, with `Algebra Rₓ Rₓ` the identity. -/
def stalkTowerHomBase :
    letI := algebraStalk p.hom z
    letI := algebraStalk (p ≫ q).hom z
    letI := algebraStalk q.hom z
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
        (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension.Hom
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension :=
  letI := algebraStalk p.hom z
  letI := algebraStalk (p ≫ q).hom z
  letI := algebraStalk q.hom z
  homCongrEq (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 R)) z) (Algebra.id _)
    (algebraStalk q.hom z) (algebraStalk q.hom z) (algebraStalk_id R z) rfl
    (generatorsSelfStalkHomOfSquare R R A C p (p ≫ q) (𝟙 R) q z (Category.id_comp (p ≫ q)).symm)

/-- The morphism `Rₓ[Cₓ] ⟶ Bₓ[Cₓ]` of canonical presentations of the stalks attached to the
relative factor of the tower, with `Algebra Cₓ Cₓ` the identity. -/
def stalkTowerHomRel (hbc : p ≫ q = bc ≫ s) :
    letI := algebraStalk (p ≫ q).hom z
    letI := algebraStalk bc.hom z
    letI := algebraStalk s.hom z
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension.Hom
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension :=
  letI := algebraStalk (p ≫ q).hom z
  letI := algebraStalk bc.hom z
  letI := algebraStalk s.hom z
  homCongrEq (algebraStalk bc.hom z) (algebraStalk bc.hom z)
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) (Algebra.id _) rfl
    (algebraStalk_id C z)
    (generatorsSelfStalkHomOfSquare R B C C (p ≫ q) s bc (𝟙 C) z
      (comp_id_eq_of_tower R A B C p q bc s hbc))

/-- The composite morphism `Rₓ[Aₓ] ⟶ Bₓ[Cₓ]` of canonical presentations of the stalks. -/
def stalkTowerHom (hbc : p ≫ q = bc ≫ s) :
    letI := algebraStalk p.hom z
    letI := algebraStalk (p ≫ q).hom z
    letI := algebraStalk q.hom z
    letI := algebraStalk bc.hom z
    letI := algebraStalk s.hom z
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
        (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension.Hom
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
        (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension :=
  letI := algebraStalk p.hom z
  letI := algebraStalk (p ≫ q).hom z
  letI := algebraStalk q.hom z
  letI := algebraStalk bc.hom z
  letI := algebraStalk s.hom z
  (stalkTowerHomRel R A B C p q bc s z hbc).comp (stalkTowerHomBase R A C p q z)

section Composite
variable (hbc : p ≫ q = bc ≫ s)

/-- The map of complexes of sheaves `NL_{A/R} ⊗_A C ⟶ NL_{C/B}`: the base-change map of the tower
`R ⟶ A ⟶ C` followed by the canonical map of the square with vertical morphisms `bc` and `𝟙 C`,
which is the relative map of `R ⟶ B ⟶ C` with its transport absorbed. -/
abbrev towerComposite : spaceBaseChangeNaiveCotangentComplex R A C p q ⟶
    naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) B C s :=
  spaceBaseChangeNaiveCotangentMap R A C p q ≫
    spaceNaiveCotangentComplexMapOfSquare R B C C (p ≫ q) s bc (𝟙 C)
      (comp_id_eq_of_tower R A B C p q bc s hbc)

/-- The stalk of `towerComposite` in degree `n` is the stalk of the second factor applied to the
stalk of the first. -/
private theorem towerComposite_stalk_map_apply (n : ℤ)
    (ξ : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex R A C p q).X n))) :
    (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((towerComposite R A B C p q bc s hbc).f n)).hom ξ) =
      ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceNaiveCotangentComplexMapOfSquare R B C C (p ≫ q) s bc (𝟙 C)
            (comp_id_eq_of_tower R A B C p q bc s hbc)).f n)).hom
        (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((spaceBaseChangeNaiveCotangentMap R A C p q).f n)).hom ξ) :=
  congrArg (fun m => (ModuleCat.Hom.hom m) ξ)
    (CategoryTheory.Functor.map_comp
      (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z)
      ((spaceBaseChangeNaiveCotangentMap R A C p q).f n)
      ((spaceNaiveCotangentComplexMapOfSquare R B C C (p ≫ q) s bc (𝟙 C)
        (comp_id_eq_of_tower R A B C p q bc s hbc)).f n))

include hbc in
/-- In degree `-1`, the stalk at `z` of `towerComposite` agrees, under the identifications
`stalkBaseChangeAddEquivNegOne` and `stalkLegNegOneLinear`, with the degree `-1` component `f₁` of
the ring-level comparison `NaiveCotangent.nlExtensionBaseChangeMap` along `stalkTowerHom`. -/
theorem stalkLegNegOneLinear_towerComposite
    (ξ : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex R A C p q).X (-1)))) :
    letI := algebraStalk p.hom z
    letI := algebraStalk (p ≫ q).hom z
    letI := algebraStalk q.hom z
    letI := algebraStalk bc.hom z
    letI := algebraStalk s.hom z
    letI := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
    letI := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
    stalkLegNegOneLinear B C s z
        (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((towerComposite R A B C p q bc s hbc).f (-1))).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (T := ToType (TopCat.Presheaf.stalk C.obj z))
          (stalkTowerHom R A B C p q bc s z hbc)).f₁
        (stalkBaseChangeAddEquivNegOne R A C p q z ξ) := by
  let := algebraStalk p.hom z
  let := algebraStalk (p ≫ q).hom z
  let := algebraStalk q.hom z
  let := algebraStalk bc.hom z
  let := algebraStalk s.hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 R)) z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z
  let := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
  let := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
  let := stalkIsScalarTowerSquareBase R R C (p ≫ q) (p ≫ q) (𝟙 R) z (Category.id_comp (p ≫ q))
  have e1 := towerComposite_stalk_map_apply R A B C p q bc s z hbc (-1) ξ
  refine Eq.trans (congrArg (stalkLegNegOneLinear B C s z) e1) ?_
  refine Eq.trans (stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_negOne R B C C (p ≫ q) s
    bc (𝟙 C) z (comp_id_eq_of_tower R A B C p q bc s hbc) (p ≫ q) hbc.symm _) ?_
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map
    (generatorsSelfStalkHomOfSquare R B C C (p ≫ q) s bc (𝟙 C) z
      (comp_id_eq_of_tower R A B C p q bc s hbc)))
    (stalkLegNegOneLinear_spaceBaseChangeNaiveCotangentMap R A C p q z ξ)) ?_
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map
    (generatorsSelfStalkHomOfSquare R B C C (p ≫ q) s bc (𝟙 C) z
      (comp_id_eq_of_tower R A B C p q bc s hbc)))
    (nlExtensionBaseChangeMap_f₁_homCongrEq
      (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 R)) z) (Algebra.id _)
      (algebraStalk_id R z)
      (generatorsSelfStalkHomOfSquare R R A C p (p ≫ q) (𝟙 R) q z
        (Category.id_comp (p ≫ q)).symm) _ (IsScalarTower.left _) _)) ?_
  refine Eq.trans (cotangentMap_homCongrEq (algebraStalk bc.hom z) (algebraStalk bc.hom z)
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) (Algebra.id _) rfl
    (algebraStalk_id C z)
    (generatorsSelfStalkHomOfSquare R B C C (p ≫ q) s bc (𝟙 C) z
      (comp_id_eq_of_tower R A B C p q bc s hbc)) _ _
    (stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm) _) ?_
  exact DFunLike.congr_fun (NaiveCotangent.cotangentMap_comp_liftBaseChange_cotangentMap
    (stalkTowerHomBase R A C p q z) (stalkTowerHomRel R A B C p q bc s z hbc)) _

include hbc in
/-- In degree `0`, the stalk at `z` of `towerComposite` agrees, under the identifications
`stalkBaseChangeAddEquivZero` and `stalkLegZeroLinear`, with the degree `0` component `f₀` of
the ring-level comparison `NaiveCotangent.nlExtensionBaseChangeMap` along `stalkTowerHom`. -/
theorem stalkLegZeroLinear_towerComposite
    (ξ : ToType ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      ((spaceBaseChangeNaiveCotangentComplex R A C p q).X 0))) :
    letI := algebraStalk p.hom z
    letI := algebraStalk (p ≫ q).hom z
    letI := algebraStalk q.hom z
    letI := algebraStalk bc.hom z
    letI := algebraStalk s.hom z
    letI := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
    letI := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
    stalkLegZeroLinear B C s z
        (((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((towerComposite R A B C p q bc s hbc).f 0)).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (T := ToType (TopCat.Presheaf.stalk C.obj z))
          (stalkTowerHom R A B C p q bc s z hbc)).f₀
        (stalkBaseChangeAddEquivZero R A C p q z ξ) := by
  let := algebraStalk p.hom z
  let := algebraStalk (p ≫ q).hom z
  let := algebraStalk q.hom z
  let := algebraStalk bc.hom z
  let := algebraStalk s.hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 R)) z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z
  let := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
  let := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
  let := stalkIsScalarTowerSquareBase R R C (p ≫ q) (p ≫ q) (𝟙 R) z (Category.id_comp (p ≫ q))
  have e1 := towerComposite_stalk_map_apply R A B C p q bc s z hbc 0 ξ
  refine Eq.trans (congrArg (stalkLegZeroLinear B C s z) e1) ?_
  refine Eq.trans (stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_zero R B C C (p ≫ q) s
    bc (𝟙 C) z (comp_id_eq_of_tower R A B C p q bc s hbc) (p ≫ q) hbc.symm _) ?_
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
    (generatorsSelfStalkHomOfSquare R B C C (p ≫ q) s bc (𝟙 C) z
      (comp_id_eq_of_tower R A B C p q bc s hbc)))
    (stalkLegZeroLinear_spaceBaseChangeNaiveCotangentMap R A C p q z ξ)) ?_
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
    (generatorsSelfStalkHomOfSquare R B C C (p ≫ q) s bc (𝟙 C) z
      (comp_id_eq_of_tower R A B C p q bc s hbc)))
    (nlExtensionBaseChangeMap_f₀_homCongrEq
      (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 R)) z) (Algebra.id _)
      (algebraStalk_id R z)
      (generatorsSelfStalkHomOfSquare R R A C p (p ≫ q) (𝟙 R) q z
        (Category.id_comp (p ≫ q)).symm) _ (IsScalarTower.left _) _)) ?_
  refine Eq.trans (cotangentSpaceMap_homCongrEq (algebraStalk bc.hom z) (algebraStalk bc.hom z)
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) (Algebra.id _) rfl
    (algebraStalk_id C z)
    (generatorsSelfStalkHomOfSquare R B C C (p ≫ q) s bc (𝟙 C) z
      (comp_id_eq_of_tower R A B C p q bc s hbc)) _ _
    (stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm) _) ?_
  exact DFunLike.congr_fun (NaiveCotangent.cotangentSpaceMap_comp_liftBaseChange_cotangentSpaceMap
    (stalkTowerHomBase R A C p q z) (stalkTowerHomRel R A B C p q bc s z hbc)) _

include hbc in
/-- **The stalk of the tower composite is a quasi-isomorphism** as soon as every comparison map
of the stalk extensions is one.  The two complexes vanish outside degrees `-1` and `0`, their
four nonzero stalks are identified with the four terms of the ring-level comparison, and the
stalk of the map is that comparison. -/
theorem quasiIso_stalkFunctor_map_towerComposite
    (hring : letI := algebraStalk p.hom z
      letI := algebraStalk (p ≫ q).hom z
      letI := algebraStalk q.hom z
      letI := algebraStalk bc.hom z
      letI := algebraStalk s.hom z
      letI := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
      letI := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
      ∀ h : (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
            (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension.Hom
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
            (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension,
        NaiveCotangent.IsQuasiIso
          (NaiveCotangent.nlExtensionBaseChangeMap
            (T := ToType (TopCat.Presheaf.stalk C.obj z)) h)) :
    letI : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).Additive :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
    QuasiIso (((stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (towerComposite R A B C p q bc s hbc)) := by
  let : (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z
  let := algebraStalk p.hom z
  let := algebraStalk (p ≫ q).hom z
  let := algebraStalk q.hom z
  let := algebraStalk bc.hom z
  let := algebraStalk s.hom z
  let := stalkIsScalarTowerSquareBase R B C s (p ≫ q) bc z hbc.symm
  let := stalkIsScalarTowerSquareTarget R A C p (p ≫ q) q z rfl
  let := moduleRingStalkCotangent B C s z
  let := moduleRingStalkCotangentSpace B C s z
  refine CochainComplex.quasiIso_of_isZero_X_of_addEquiv _ ?_ ?_
    (stalkBaseChangeAddEquivNegOne R A C p q z) (stalkBaseChangeAddEquivZero R A C p q z)
    (stalkLegNegOneLinear B C s z).toAddEquiv (stalkLegZeroLinear B C s z).toAddEquiv
    (NaiveCotangent.nlExtensionBaseChange
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk R.obj z))
        (ToType (TopCat.Presheaf.stalk A.obj z))).toExtension
      (ToType (TopCat.Presheaf.stalk C.obj z))).d
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk B.obj z))
      (ToType (TopCat.Presheaf.stalk C.obj z))).toExtension.cotangentComplex
    (NaiveCotangent.nlExtensionBaseChangeMap
      (T := ToType (TopCat.Presheaf.stalk C.obj z))
      (stalkTowerHom R A B C p q bc s z hbc)).f₁
    (NaiveCotangent.nlExtensionBaseChangeMap
      (T := ToType (TopCat.Presheaf.stalk C.obj z))
      (stalkTowerHom R A B C p q bc s z hbc)).f₀ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi h0
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (CategoryTheory.Functor.map_isZero
        (towerExtendScalars (Opens.grothendieckTopology T) A C q)
        (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) R A p i hi h0))
  · intro i hi h0
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ z _
      (naiveCotangentComplex_isZero_X.{u, u, u, u} (Opens.grothendieckTopology T) B C s i hi h0)
  · intro ζ
    exact (AddEquiv.eq_symm_apply _).mpr (stalkBaseChangeAddEquiv_d R A C p q z ζ)
  · intro ω
    exact (AddEquiv.eq_symm_apply _).mpr (stalkLegLinear_d B C s z ω)
  · intro ζ
    exact (AddEquiv.eq_symm_apply _).mpr
      (stalkLegNegOneLinear_towerComposite R A B C p q bc s z hbc ζ)
  · intro ζ
    exact (AddEquiv.eq_symm_apply _).mpr
      (stalkLegZeroLinear_towerComposite R A B C p q bc s z hbc ζ)
  · exact NaiveCotangent.IsQuasiIso.eq_zero_of_d_eq_zero (hring _)
  · exact NaiveCotangent.IsQuasiIso.exists_of_d_eq_zero (hring _)
  · exact NaiveCotangent.IsQuasiIso.exists_d_eq (hring _)
  · exact NaiveCotangent.IsQuasiIso.exists_add_d_eq (hring _)

end Composite

end Stacks.NaiveCotangentTowerStalk

end

end
