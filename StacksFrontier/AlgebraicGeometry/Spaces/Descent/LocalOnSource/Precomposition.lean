module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Precomposing a source-local property with a covering morphism

Let `S` be a scheme contained in a big fppf site `B`, let `τ` be one of the five topologies of
Stacks 03YH, and let `P` be a property of morphisms of algebraic spaces over `S` which is local
on the source for `τ`. Then `P` is stable under precomposition with a morphism of the kind `τ`
admits as a member of a covering family — flat for fpqc, flat and locally of finite presentation
for fppf, syntomic, smooth, étale for the other three. This is **Stacks 06EQ**. No surjectivity
is required of the morphism precomposed.

## Main definitions

* `AlgebraicGeometry.Space.Topology.IsMember`: the property that `τ` requires of each member of
  a covering family, as a single predicate of a morphism of presheaves indexed by `τ`.

## Main results

* `AlgebraicGeometry.Space.Topology.isMember_id`: the identity has that property, for every `τ`.
* `AlgebraicGeometry.Space.mem_precoverage_idPair`: adjoining the identity of `Y` to a morphism
  `f : X ⟶ Y` with that property gives a `τ`-covering family of `Y`.
* `AlgebraicGeometry.Space.comp_of_isMember`: **Stacks 06EQ**, uniformly in `τ`.
* `AlgebraicGeometry.Space.comp_isFlat`, `comp_isFlat_isLocallyOfFinitePresentation`,
  `comp_isSyntomic`, `comp_isSmooth`, `comp_isEtale`: its five cases.

## Implementation notes

Source locality is Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtSource` for the
precoverage `AlgebraicGeometry.Space.Topology.precoverage` of Stacks 03YH (Stacks 06EP). Its
`comp` field is the half used here.

`Topology.IsMember` is definitionally the member clause of each of the five covering predicates,
so the five named corollaries state the corresponding property of Stacks 03ML, 03XP, 03Z7, 03ZC
or 03FR directly.

The index type of a covering family is a free universe parameter of `Topology.precoverage`, and
is left free here. `AlgebraicGeometry.Space.mem_precoverage_pair_etale` and
`AlgebraicGeometry.Space.mem_precoverage_pair_smooth` are the `τ = .etale` and `τ = .smooth`
cases of `mem_precoverage_idPair` pinned at `v = u + 1`, and
`AlgebraicGeometry.Space.comp_of_isEtale` is `comp_isEtale` pinned the same way.

## References

* [Stacks Project, Tag 06EQ](https://stacks.math.columbia.edu/tag/06EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The member condition of a topology -/

/-- The property that the topology `τ` of Stacks 03YH requires of every member of a covering
family: flatness for the fpqc topology, flatness together with local finite presentation for
the fppf topology, and syntomicity, smoothness or étaleness for the other three. -/
def Topology.IsMember (τ : Topology) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    Prop :=
  match τ with
  | .fpqc => IsFlat B S hS f
  | .fppf => IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f
  | .syntomic => IsSyntomic B S hS f
  | .smooth => IsSmooth B S hS f
  | .etale => IsEtale B S hS f

/-- The identity of a presheaf on the big fppf site of `S` is a member for every one of the
five topologies. -/
theorem Topology.isMember_id (τ : Topology) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    τ.IsMember B S hS (𝟙 F) := by
  have hflat : IsFlat B S hS (𝟙 F) :=
    holdsOnEveryEtaleChart_id_presheaf B S hS
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
      (fun _ _ g hg => have := hg; inferInstance) F
  have hlfp : IsLocallyOfFinitePresentation B S hS (𝟙 F) :=
    holdsOnEveryEtaleChart_id_presheaf B S hS
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (fun _ _ g hg => have := hg; inferInstance) F
  cases τ with
  | fpqc => exact hflat
  | fppf => exact ⟨hflat, hlfp⟩
  | syntomic => exact isSyntomic_of_isSmooth B S hS (𝟙 F) (isSmooth_id_presheaf B S hS F)
  | smooth => exact isSmooth_id_presheaf B S hS F
  | etale => exact isEtale_id B S hS F

/-! ### Adjoining the identity to a single morphism -/

variable {B S hS}

/-- The two-object family consisting of `X` and of `Y`, indexed by `ULift Bool`. -/
abbrev idPairObj (X Y : AlgebraicSpaces B S hS) :
    ULift.{v, 0} Bool → AlgebraicSpaces B S hS :=
  fun i => bif i.down then X else Y

/-- The two-member family over `Y` consisting of `f : X ⟶ Y` and of the identity of `Y`. -/
abbrev idPairMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ∀ i, idPairObj.{u, v} X Y i ⟶ Y :=
  fun i => match i with
    | ⟨true⟩ => f
    | ⟨false⟩ => 𝟙 Y

/-- Adjoining the identity of `Y` to a morphism `f : X ⟶ Y` which is a member for `τ` gives a
`τ`-covering family of `Y`. -/
theorem mem_precoverage_idPair (τ : Topology) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : τ.IsMember B S hS f.hom) :
    Presieve.ofArrows (idPairObj.{u, v} X Y) (idPairMap.{u, v} f) ∈
      (Topology.precoverage.{u, v} τ B S hS) Y := by
  refine ⟨ULift.{v, 0} Bool, _, _, rfl, Y.property, ?_, ?_⟩
  · rintro ⟨(_ | _)⟩
    · exact Y.property
    · exact X.property
  have hid : ∀ i, τ.IsMember B S hS (idPairMap.{u, v} f i).hom := by
    rintro ⟨(_ | _)⟩
    · exact Topology.isMember_id B S hS τ Y.obj
    · exact hf
  have hsurj :
      (⋃ i, Set.range (pointsMap B S hS (idPairObj.{u, v} X Y i).obj
        (idPairMap.{u, v} f i).hom)) = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr
      ⟨⟨false⟩, x, congrFun (pointsMap_id B S hS Y.obj) x⟩
  cases τ with
  | fpqc =>
      refine ⟨hid, fun T h => ?_⟩
      refine ⟨PreZeroHypercover.singleton (𝟙 T), inferInstance, ?_, ?_⟩
      · simp [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
      · rintro ⟨⟩
        refine ⟨⟨false⟩, h, ?_⟩
        calc
          h ≫ (idPairMap.{u, v} f (⟨false⟩ : ULift.{v, 0} Bool)).hom = h := by
            simp [idPairMap]
          _ = yoneda.map ((BigAffineFppf.inclusion B S hS).map (𝟙 T)) ≫ h := by simp
  | fppf => exact ⟨Y.property, fun i => (idPairObj.{u, v} X Y i).property,
      fun i => (hid i).1, fun i => (hid i).2, hsurj⟩
  | syntomic | smooth | etale =>
      exact ⟨Y.property, fun i => (idPairObj.{u, v} X Y i).property, hid, hsurj⟩

/-! ### Stacks 06EQ -/

variable {P : MorphismProperty (AlgebraicSpaces B S hS)}

/-- **Stacks 06EQ**, uniformly in the topology. A property of morphisms of algebraic spaces over
`S` which is local on the source for `τ` is stable under precomposition with a morphism which
`τ` admits as a member of a covering family. -/
theorem comp_of_isMember (τ : Topology)
    [P.IsLocalAtSource (Topology.precoverage.{u, v} τ B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (f : Y ⟶ Z)
    (ha : τ.IsMember B S hS a.hom) (hf : P f) : P (a ≫ f) :=
  MorphismProperty.IsLocalAtSource.comp (mem_precoverage_idPair.{u, v} τ a ha) a
    (.mk (ULift.up true)) hf

/-- **Stacks 06EQ**, the fpqc case. A property fpqc local on the source is stable under
precomposition with a flat morphism. -/
@[stacks 06EQ "fpqc"]
theorem comp_isFlat [P.IsLocalAtSource (Topology.precoverage.{u, v} .fpqc B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (f : Y ⟶ Z)
    (ha : IsFlat B S hS a.hom) (hf : P f) : P (a ≫ f) :=
  comp_of_isMember.{u, v} .fpqc a f ha hf

/-- **Stacks 06EQ**, the fppf case. A property fppf local on the source is stable under
precomposition with a flat morphism which is locally of finite presentation. -/
@[stacks 06EQ "fppf"]
theorem comp_isFlat_isLocallyOfFinitePresentation
    [P.IsLocalAtSource (Topology.precoverage.{u, v} .fppf B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (f : Y ⟶ Z)
    (hflat : IsFlat B S hS a.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS a.hom) (hf : P f) : P (a ≫ f) :=
  comp_of_isMember.{u, v} .fppf a f ⟨hflat, hlfp⟩ hf

/-- **Stacks 06EQ**, the syntomic case. A property syntomic local on the source is stable under
precomposition with a syntomic morphism. -/
@[stacks 06EQ "syntomic"]
theorem comp_isSyntomic [P.IsLocalAtSource (Topology.precoverage.{u, v} .syntomic B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (f : Y ⟶ Z)
    (ha : IsSyntomic B S hS a.hom) (hf : P f) : P (a ≫ f) :=
  comp_of_isMember.{u, v} .syntomic a f ha hf

/-- **Stacks 06EQ**, the smooth case. A property smooth local on the source is stable under
precomposition with a smooth morphism. -/
@[stacks 06EQ "smooth"]
theorem comp_isSmooth [P.IsLocalAtSource (Topology.precoverage.{u, v} .smooth B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (f : Y ⟶ Z)
    (ha : IsSmooth B S hS a.hom) (hf : P f) : P (a ≫ f) :=
  comp_of_isMember.{u, v} .smooth a f ha hf

/-- **Stacks 06EQ**, the étale case. A property étale local on the source is stable under
precomposition with an étale morphism. -/
@[stacks 06EQ "étale"]
theorem comp_isEtale [P.IsLocalAtSource (Topology.precoverage.{u, v} .etale B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (f : Y ⟶ Z)
    (ha : IsEtale B S hS a.hom) (hf : P f) : P (a ≫ f) :=
  comp_of_isMember.{u, v} .etale a f ha hf

end AlgebraicGeometry.Space

end
