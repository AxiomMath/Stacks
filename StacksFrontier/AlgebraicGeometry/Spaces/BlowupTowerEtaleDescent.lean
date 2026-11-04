module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerEtaleRestriction
import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsProperties

/-!
# Descending a sequence of blowings up at closed points from the étale neighborhoods

Let `S` be a scheme, let `X` be a decent algebraic space over `S`, let `x₁, …, xₙ ∈ |X|` be
pairwise distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the elementary étale
neighborhoods chosen in Stacks 0BH9, as packaged by
`AlgebraicGeometry.Space.ClosedPointNeighborhoods`.

The complement `X ∖ {x₁, …, xₙ}` together with the neighborhoods `U₁, …, Uₙ` is an fppf
covering family of `X`: the first member is an open subspace and the others are étale, hence
all are flat and locally of finite presentation, and jointly they reach every point of `X` —
a point outside `{x₁, …, xₙ}` lies in the complement and `xᵢ` is the image of `uᵢ`.  Being an
isomorphism is local on the base for the fppf topology (**Stacks 041Y**), so a morphism
`f : Y ⟶ X` which is an isomorphism over the complement and over every `Uᵢ` is an
isomorphism.

This is the **base case of the "if" direction of Stacks 0BHF**: a morphism `f` in
`C_{X, {x₁, …, xₙ}}` all of whose restrictions `gᵢ` factor as the *empty* sequence of blowings
up is an isomorphism, hence itself factors as the empty sequence.

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.coverSpace` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.coverSpaceHom`: the covering family
  `{X ∖ {x₁, …, xₙ}, U₁, …, Uₙ}` of `X`, indexed by `Option (Fin n)`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_forall_isIso_pullback_snd`: **Stacks 041Y** in the form a
  covering family consumes — a morphism of algebraic spaces whose base change to every member
  of an fppf covering family of its target is an isomorphism is an isomorphism.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isFppfCovering_coverHom`: the family
  `{X ∖ {x₁, …, xₙ}, U₁, …, Uₙ}` is an fppf covering family of `X`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_of_isIso_pullback_snd_toSpaceHom`: a
  morphism to `X` which is an isomorphism over `X ∖ {x₁, …, xₙ}` and over every `Uᵢ` is an
  isomorphism.
* `AlgebraicGeometry.Space.BlowupFactorization.isIso_of_length_eq_zero`: a morphism factored by
  the empty sequence of blowings up is an isomorphism.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods`'s
  `nonempty_globalBlowupFactorization_of_forall_length_eq_zero`: the base case of the "if"
  direction of Stacks 0BHF.

## Implementation notes

### Why only the base case is here

The source proves the "if" direction of Stacks 0BHF by the same induction as the "only if"
direction, assembling the tower over `X` from the given local towers.  That induction is run as
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_of_isPullback`
in `StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerGlobalConverse.lean`; its inductive step needs
the blowing up of an intermediate space at a closed point
(`AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint_unconditional`, which takes
`[HasSheafify (BigFppfOver.topology B S hS) (Type u)]` as an instance argument, supplied there
by `AlgebraicGeometry.BigFppfOver.hasSheafify_type`), the global centre realizing a
prescribed local one
(`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_isBlowupAtClosedPoint_restricting`),
and at the end the identification of the top of the assembled tower with `Y`, which is the full
faithfulness of the functor `F` of Stacks 0BHA — the half of Stacks 0BHB the source omits,
proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModificationsAtClosedPointsFullyFaithful.lean`.

What is proved *here* is the statement that needs none of those: a morphism in
`C_{X, {x₁, …, xₙ}}` whose restrictions are all isomorphisms is an isomorphism, which is fppf
locality of isomorphisms on the covering family assembled below, so a morphism all of whose
restrictions factor as the empty sequence is factored by the empty sequence.  That covering
family is also what the proof of full faithfulness descends along.

### The index type of the covering family

The family is indexed by `Option (Fin n)`, the complement being the `none` member.  Indexing by
a type in `Type 0` rather than in `Type u` is why
`AlgebraicGeometry.Space.Topology.precoverage` and the locality instance for isomorphisms are
instantiated below at the universe of the index type.

### Transferring the base change between the two categories

A hypothesis of the form "`f` is an isomorphism over `V`" is recorded throughout this
development as `IsIso (pullback.snd f.hom v)` for the *underlying presheaf* morphisms — that is
the shape `AlgebraicGeometry.Space.IsModification` and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.restrictionComponent` use — whereas the
locality of isomorphisms speaks of the chosen pullback in the category of algebraic spaces.
`AlgebraicGeometry.Space.isIso_pullback_snd_of_isIso_pullback_snd_hom` moves between the two:
the full subcategory inclusion is fully faithful, so it reflects the pullback, and the two
pullbacks are then canonically isomorphic over the cospan.

## References

* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Towers of length zero -/

namespace BlowupTower

variable {B S hS} {X : AlgebraicSpaces B S hS}

/-- **A tower of blowings up with no steps has invertible projection.**  The only tower of
length zero is the empty one, whose projection is the identification `Z₀ ≅ X`. -/
theorem isIso_proj_of_length_eq_zero {Z : AlgebraicSpaces B S hS}
    (t : BlowupTower B S hS X Z) (h : t.length = 0) : IsIso t.proj := by
  cases t with
  | base e =>
    rw [proj_base]
    exact inferInstanceAs (IsIso e.hom)
  | step t b z hz hb =>
    rw [length_step] at h
    exact absurd h (Nat.succ_ne_zero _)

end BlowupTower

namespace BlowupFactorization

variable {B S hS} {X Y : AlgebraicSpaces B S hS}

/-- **A morphism factored by the empty sequence of blowings up is an isomorphism.**  It is the
identification `Y ≅ Zₘ` followed by the projection of a tower of length zero. -/
theorem isIso_of_length_eq_zero {T : Set (points B S hS X.obj)} {f : Y ⟶ X}
    (F : BlowupFactorization B S hS T f) (h : F.length = 0) : IsIso f := by
  have ht : IsIso F.tower.proj := F.tower.isIso_proj_of_length_eq_zero h
  rw [← F.iso_proj]
  exact inferInstanceAs (IsIso (F.iso.hom ≫ F.tower.proj))

end BlowupFactorization

/-! ### Isomorphisms are fppf local on the base, in covering-family form -/

/-- **Transfer of a base change between the presheaves and the algebraic spaces.**  If the
chosen pullback of the underlying presheaf morphisms has invertible second projection, so does
the chosen pullback in the category of algebraic spaces over `S`: the full subcategory
inclusion is fully faithful, hence reflects the pullback, and two pullbacks of one cospan are
canonically isomorphic. -/
theorem isIso_pullback_snd_of_isIso_pullback_snd_hom {X Y Z : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (c : Z ⟶ X) (h : IsIso (pullback.snd f.hom c.hom)) :
    IsIso (pullback.snd f c) := by
  have hP : IsAlgebraicSpace B S hS (pullback f.hom c.hom) :=
    isAlgebraicSpace_pullback B S hS f.hom c.hom Y.property Z.property X.property
  have h' : IsPullback
      (ObjectProperty.homMk (pullback.fst f.hom c.hom) :
        (⟨pullback f.hom c.hom, hP⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (ObjectProperty.homMk (pullback.snd f.hom c.hom)) f c :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS T))
      (IsPullback.of_hasPullback f.hom c.hom)
  have hsq : IsPullback (pullback.fst f c) (pullback.snd f c) f c :=
    IsPullback.of_hasPullback f c
  have hhom : IsIso (ObjectProperty.homMk (pullback.snd f.hom c.hom) :
      (⟨pullback f.hom c.hom, hP⟩ : AlgebraicSpaces B S hS) ⟶ Z) :=
    (ObjectProperty.isIso_hom_iff _).mp h
  rw [← hsq.isoIsPullback_hom_snd _ _ h']
  exact inferInstanceAs (IsIso ((hsq.isoIsPullback _ _ h').hom ≫ _))

/-- **Stacks 041Y in covering-family form.**  A morphism of algebraic spaces over `S` whose
base change to every member of an fppf covering family of its target is an isomorphism is an
isomorphism.

Being an isomorphism is local on the base for the fppf topology of Stacks 03YH, which is
`AlgebraicGeometry.Space.isomorphisms_isLocalAtTarget_fppf`; the covering family presents a
member of the fppf precoverage of its target. -/
theorem isIso_of_forall_isIso_pullback_snd {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    {I : Type} (V : I → AlgebraicSpaces B S hS) (c : ∀ i, V i ⟶ X)
    (hcov : IsFppfCovering B S hS (fun i => (V i).obj) (fun i => (c i).hom))
    (hiso : ∀ i, IsIso (pullback.snd f (c i))) : IsIso f := by
  let K := Topology.precoverage.{u, 0} .fppf B S hS
  let _ : (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget K :=
    isomorphisms_isLocalAtTarget_fppf.{u, 0} B S hS
  have hmem : Presieve.ofArrows V c ∈ K X :=
    ⟨I, V, c, rfl, X.property, fun i => (V i).property, hcov⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)) hmem ?_
  rintro W g _ ⟨i⟩
  exact hiso i

/-! ### The covering family of a configuration of closed points -/

namespace ClosedPointNeighborhoods

variable {B S hS} {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The members of the covering family `{X ∖ {x₁, …, xₙ}, U₁, …, Uₙ}` of `X`: the open
complement of the chosen points at `none` and the `i`th chosen neighborhood at `some i`. -/
def coverSpace : Option (Fin n) → AlgebraicSpaces B S hS
  | none => ⟨D.openAwayFromPoints.toFunctor, D.isOpenSubspace_openAwayFromPoints.1⟩
  | some i => D.neighborhoodSpace i

/-- The morphisms of the covering family `{X ∖ {x₁, …, xₙ}, U₁, …, Uₙ}` of `X`: the inclusion of
the open complement at `none` and the étale morphism `Uᵢ ⟶ X` at `some i`. -/
def coverSpaceHom : ∀ j, D.coverSpace j ⟶ D.space
  | none => ObjectProperty.homMk D.openAwayFromPoints.ι
  | some i => D.toSpaceHom i

/-- Every member of the family `{X ∖ {x₁, …, xₙ}, U₁, …, Uₙ}` is étale: the first is an open
immersion and the others are étale by the choice of neighborhoods. -/
theorem isEtale_coverHom (j : Option (Fin n)) : IsEtale B S hS (D.coverSpaceHom j).hom := by
  cases j with
  | none => exact isEtale_of_isOpenImmersion B S hS D.isOpenSubspace_openAwayFromPoints.2
  | some i => exact D.isEtale_toSpaceHom i

/-- **The family `{X ∖ {x₁, …, xₙ}, U₁, …, Uₙ}` is an fppf covering family of `X`.**  Every
member is étale, hence flat and locally of finite presentation, and the family is jointly
surjective on points: a point outside `{x₁, …, xₙ}` is a point of the complement, and `xᵢ` is
the image of the distinguished point `uᵢ` of the `i`th neighborhood. -/
theorem isFppfCovering_coverHom :
    IsFppfCovering B S hS (fun j => (D.coverSpace j).obj) (fun j => (D.coverSpaceHom j).hom) where
  target_isAlgebraicSpace := D.space.property
  source_isAlgebraicSpace j := (D.coverSpace j).property
  flat j := isFlat_of_isEtale B S hS (D.isEtale_coverHom j)
  locallyOfFinitePresentation j :=
    isLocallyOfFinitePresentation_of_isEtale B S hS (D.isEtale_coverHom j)
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ Set.range D.point
    · obtain ⟨i, hi⟩ := hx
      exact ⟨some i, D.neighborhoodPoint i, by
        simpa [coverSpaceHom, toSpaceHom] using hi ▸ (D.neighborhood i).map_point⟩
    · refine ⟨none, ?_⟩
      change x ∈ Set.range (pointsMap B S hS D.openAwayFromPoints.toFunctor
        D.openAwayFromPoints.ι)
      rwa [D.range_pointsMap_ι_openAwayFromPoints]

/-- **A morphism to `X` which is an isomorphism over `X ∖ {x₁, …, xₙ}` and over every `Uᵢ` is
an isomorphism.**  The complement and the neighborhoods form an fppf covering family of `X`
and being an isomorphism is local on the base for the fppf topology (**Stacks 041Y**).

Both hypotheses are stated for the chosen pullbacks of the underlying presheaf morphisms, which
is the shape in which `AlgebraicGeometry.Space.IsModification` records the first and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.restrictionComponent` the others. -/
theorem isIso_of_isIso_pullback_snd_toSpaceHom {Y : AlgebraicSpaces B S hS} (f : Y ⟶ D.space)
    (h₀ : IsIso (pullback.snd f.hom D.openAwayFromPoints.ι))
    (h : ∀ i, IsIso (pullback.snd f.hom (D.toSpaceHom i).hom)) : IsIso f := by
  refine isIso_of_forall_isIso_pullback_snd B S hS f D.coverSpace D.coverSpaceHom
    D.isFppfCovering_coverHom fun j => ?_
  refine isIso_pullback_snd_of_isIso_pullback_snd_hom B S hS f (D.coverSpaceHom j) ?_
  cases j with
  | none => exact h₀
  | some i => exact h i

/-! ### The base case of the "if" direction of Stacks 0BHF -/

/-- **The base case of the "if" direction of Stacks 0BHF.**  Let `X, xᵢ, Uᵢ ⟶ X, uᵢ` be as in
Stacks 0BH9 and let `f : Y ⟶ X` be an object of `C_{X, {x₁, …, xₙ}}` corresponding to
`gᵢ : Yᵢ ⟶ Uᵢ` under the functor `F` of Stacks 0BHA.  If every `gᵢ` factors as the *empty*
sequence of blowings up at closed points lying over `uᵢ`, then `f` factors as the empty
sequence of blowings up at closed points lying over `{x₁, …, xₙ}`.

Each `gᵢ` is then an isomorphism, so `f` is an isomorphism over every `Uᵢ`; it is one over
`X ∖ {x₁, …, xₙ}` because it is a modification away from that open subspace, so it is an
isomorphism by
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_of_isIso_pullback_snd_toSpaceHom`, and
an isomorphism is factored by the empty sequence.

This is only the base case: the inductive step of the source's proof needs the existence of the
blowing up of an intermediate space at a closed point and the fullness of `F`, and is run in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerGlobalConverse.lean`.  See the implementation
notes of this file. -/
theorem nonempty_globalBlowupFactorization_of_forall_length_eq_zero
    (M : D.modificationsAwayFromPoints)
    (G : ∀ i, D.LocalBlowupFactorization i (ObjectProperty.homMk
      ((D.restrictionComponent i).obj M).obj.hom :
      (⟨((D.restrictionComponent i).obj M).obj.left,
          ((D.restrictionComponent i).obj M).property.1⟩ : AlgebraicSpaces B S hS) ⟶
        D.neighborhoodSpace i))
    (hlen : ∀ i, (G i).length = 0) :
    Nonempty (D.GlobalBlowupFactorization (ObjectProperty.homMk M.obj.hom :
      (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) := by
  have hiso : IsIso (ObjectProperty.homMk M.obj.hom :
      (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space) :=
    D.isIso_of_isIso_pullback_snd_toSpaceHom _ M.property.2 fun i =>
      (ObjectProperty.isIso_hom_iff _).mpr ((G i).isIso_of_length_eq_zero (hlen i))
  exact ⟨BlowupFactorization.ofIso _ (@asIso _ _ _ _ _ hiso)⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
