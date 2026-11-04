module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible étale sheaves

A sheaf on the small étale site of a scheme is constructible if, on every affine open,
there is a finite partition by constructible locally closed subschemes on which its
inverse image is finite locally constant (for sets and abelian groups), or locally
constant with finitely generated values (for modules over a Noetherian ring).

## Main definitions

* `AlgebraicGeometry.ConstructibleStratification` is the finite partition of an open
  subscheme by constructible locally closed subschemes.
* `AlgebraicGeometry.IsConstructibleSetSheaf` and
  `AlgebraicGeometry.IsConstructibleAbelianSheaf` are the definitions for sheaves of sets
  and of abelian groups.
* `Stacks.ConstantSheaf.IsLocallyConstantWith` and
  `AlgebraicGeometry.IsStratifiedLocallyConstantWith` are local constancy, and stratumwise
  local constancy, with constant values satisfying a given property of modules.
* `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant` is local constancy with finitely
  generated values, for a sheaf of modules on an arbitrary site.
* `AlgebraicGeometry.IsConstructibleModuleSheaf` is the definition for sheaves of modules
  over a Noetherian ring.

## Implementation notes

The small étale site is that of Tag 021B, `AlgebraicGeometry.SmallEtale.topology`. A stratum
is recorded by its immersion into the scheme, not merely by its underlying subset, so inverse
image along it is unambiguous. Its image is constructible in the affine open itself. Sets and
abelian groups specialize a common concrete-category predicate, whose coefficient universe is
independent of the scheme universe. Local finite generation of module values is stated on the
same trivializing covers as local constancy, so it is placed next to
`Stacks.ConstantSheaf.IsFiniteLocallyConstant` rather than in the geometric namespace. These
predicates are transparent abbreviations, so users can apply the defining witnesses directly.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w v c r t

namespace AlgebraicGeometry

/-- A finite partition of an open subscheme by constructible locally closed subschemes. -/
public structure ConstructibleStratification (B : BigEtaleSite.{u})
    (X : B.Scheme) (U : X.obj.Opens) where
  /-- The number of strata. -/
  n : ℕ
  /-- The strata, as objects of the big étale site. -/
  piece : Fin n → B.Scheme
  /-- The structure morphism of each stratum to `X`. -/
  inclusion : ∀ i, piece i ⟶ X
  /-- Each stratum is immersed in `X`. -/
  isImmersion : ∀ i, IsImmersion (B.inclusion.map (inclusion i))
  /-- Each stratum lies inside `U`. -/
  contained : ∀ i, Set.range (B.inclusion.map (inclusion i)).base ⊆ (U : Set X.obj)
  /-- Each stratum is constructible as a subset of `U`. -/
  constructible : ∀ i, Topology.IsConstructible
    (U.ι.base ⁻¹' Set.range (B.inclusion.map (inclusion i)).base)
  /-- Distinct strata are disjoint. -/
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint
    (Set.range (B.inclusion.map (inclusion i)).base)
    (Set.range (B.inclusion.map (inclusion j)).base)
  /-- The strata cover `U`. -/
  covers : (U : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (inclusion i)).base

/-- A finite locally constant sheaf after inverse image to every stratum of a
constructible partition of each affine open. This applies to both sets and
abelian groups. -/
public abbrev IsConstructibleFiniteSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    {D : Type w} [Category.{v} D]
    {FD : D → D → Type*} {CD : D → Type t}
    [∀ A A', FunLike (FD A A') (CD A) (CD A')]
    [ConcreteCategory.{t} D FD]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) : Prop :=
  ∀ U : X.obj.affineOpens, ∃ s : ConstructibleStratification B X U.1,
    ∀ i, Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback D
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)

/-- A constructible sheaf of sets on the small étale site. -/
@[stacks 03RW "part (1)", sga "4 IX 2.3" "sheaves of sets"]
public abbrev IsConstructibleSetSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) : Prop :=
  IsConstructibleFiniteSheaf B X F

/-- A constructible sheaf of abelian groups on the small étale site. -/
@[stacks 03RW "part (2)", sga "4½ Arcata 4.3.2" "(i)", sga "4 IX 2.3" "sheaves of groups"]
public abbrev IsConstructibleAbelianSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{w}]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}) : Prop :=
  IsConstructibleFiniteSheaf B X F

end AlgebraicGeometry

namespace Stacks.ConstantSheaf

/-- A locally constant module sheaf whose constant values satisfy `Q`, on a covering of every
object of a site. -/
public abbrev IsLocallyConstantWith (R : Type r) [Ring R]
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    (Q : ModuleCat.{w} R → Prop) (F : Sheaf J (ModuleCat.{w} R)) : Prop :=
  ∀ U : C, ∃ (I : Type (max c v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i,
      ∃ E : ModuleCat.{w} R, Q E ∧
        Nonempty ((constantSheaf (J.over (V i)) (ModuleCat.{w} R)).obj E ≅
          (J.overPullback (ModuleCat.{w} R) (V i)).obj F)

/-- A locally constant module sheaf with finitely generated constant values
on a covering of every object of a site. -/
public abbrev IsFiniteTypeLocallyConstant (R : Type r) [Ring R]
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    (F : Sheaf J (ModuleCat.{w} R)) : Prop :=
  ∀ U : C, ∃ (I : Type (max c v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i,
      ∃ E : ModuleCat.{w} R, ModuleCat.isFG R E ∧
        Nonempty ((constantSheaf (J.over (V i)) (ModuleCat.{w} R)).obj E ≅
          (J.overPullback (ModuleCat.{w} R) (V i)).obj F)

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

/-- A sheaf of modules which on a finite constructible stratification of every affine open is
locally constant with constant values satisfying `Q`. -/
public abbrev IsStratifiedLocallyConstantWith (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [Ring R]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]
    (Q : ModuleCat.{w} R → Prop)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)) : Prop :=
  ∀ U : X.obj.affineOpens, ∃ s : ConstructibleStratification B X U.1,
    ∀ i, Stacks.ConstantSheaf.IsLocallyConstantWith R
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property) Q
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)

/-- A constructible sheaf of modules over a Noetherian ring: on a finite
constructible stratification of every affine open, it is locally constant of
finite type. -/
@[stacks 03RW "part (3)", sga "4 IX 2.3" "A-modules, A noetherian"]
public abbrev IsConstructibleModuleSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [Ring R]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)) : Prop :=
  ∀ U : X.obj.affineOpens, ∃ s : ConstructibleStratification B X U.1,
    ∀ i, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)

end AlgebraicGeometry

end
