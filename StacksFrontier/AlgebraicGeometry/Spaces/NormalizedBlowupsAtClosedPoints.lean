module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# The normalized blowing up of an algebraic space at a closed point

Let `S` be a scheme and let `X` be a decent algebraic space over `S` all of whose étale scheme
charts have finitely many irreducible components over each quasi-compact open, so that `X` and
its blowings up have normalizations.  For a closed point `z ∈ |X|` the *normalized blowing up of
`X` at `z`* is the composition `X'' ⟶ X' ⟶ X` of the blowing up `X' ⟶ X` of `X` at `z`
(**Stacks 0BHE**) with the normalization `X'' ⟶ X'` of `X'`.  This is **Stacks 0BHJ**.

A *tower of normalized blowings up at closed points over `X`* is a finite chain

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

in which each `Z_{j+1} ⟶ Z_j` is the normalized blowing up of `Z_j` at a closed point
`z_j ∈ |Z_j|`.  A morphism `f : Y ⟶ X` *factors as a sequence of normalized blowings up at
closed points lying over a set `T ⊆ |X|`* when there is such a tower whose centres `z_j` all map
into `T` and whose top `Zₘ` is identified with `Y` compatibly with `f`.  This is the condition
appearing on both sides of **Stacks 0BHL**, with `T = {x₁, …, xₙ}` on the one side and
`T = {uᵢ}` on the other; see
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.GlobalNormalizedBlowupFactorization` and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.LocalNormalizedBlowupFactorization`.

## Main definitions

* `AlgebraicGeometry.Space.normalizationSpace` and
  `AlgebraicGeometry.Space.normalizationHom` read the normalization datum of Stacks 07U4 as an
  object and a morphism of the category of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.IsNormalizedBlowupAtClosedPoint` is **Stacks 0BHJ**.
* `AlgebraicGeometry.Space.NormalizedBlowupTower` is the chain `Zₘ ⟶ … ⟶ Z₀ = X` as data, with
  `AlgebraicGeometry.Space.NormalizedBlowupTower.proj` the composite `Z_j ⟶ X`,
  `AlgebraicGeometry.Space.NormalizedBlowupTower.length` the number `m` of steps and
  `AlgebraicGeometry.Space.NormalizedBlowupTower.CentersOver` the condition that every centre
  lies over a given set of points.
* `AlgebraicGeometry.Space.NormalizedBlowupFactorization` is the factorization of a given
  morphism by such a tower, again as data.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.GlobalNormalizedBlowupFactorization` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.LocalNormalizedBlowupFactorization` are the
  two conditions compared by **Stacks 0BHL**.

## Main results

* `AlgebraicGeometry.Space.isNormalizedBlowupAtClosedPoint_comp`: the normalization of a blowing
  up of `X` at a closed point, followed by that blowing up, is the normalized blowing up of `X`
  at the point.
* `AlgebraicGeometry.Space.IsNormalizedBlowupAtClosedPoint.comp_iso`: precomposing a normalized
  blowing up with an isomorphism gives again one, and
  `AlgebraicGeometry.Space.IsNormalizedBlowupAtClosedPoint.exists_blowup_normalizationData`
  recovers the intermediate blowing up together with the normalization data producing its
  normalization.
* `AlgebraicGeometry.Space.IsNormalizedBlowupAtClosedPoint.isNormal`: the source of a normalized
  blowing up is a normal algebraic space, by the normality assertion of Stacks 07U4.
* `AlgebraicGeometry.Space.NormalizedBlowupTower.comap` and
  `AlgebraicGeometry.Space.NormalizedBlowupTower.append` transport a tower along an isomorphism
  of its top and concatenate two towers; the latter is the step by which the induction behind
  Stacks 0BHL lengthens a sequence of normalized blowings up.
* `AlgebraicGeometry.Space.NormalizedBlowupFactorization.ofIso`,
  `AlgebraicGeometry.Space.NormalizedBlowupFactorization.ofBlowup`,
  `AlgebraicGeometry.Space.NormalizedBlowupFactorization.comp` and
  `AlgebraicGeometry.Space.NormalizedBlowupFactorization.mono` are the closure properties of the
  factorization condition: an isomorphism is factored by the empty sequence, a single normalized
  blowing up at a closed point over `T` by a sequence of length one, a composite of two factored
  morphisms is factored, and the condition grows with `T`.

## Implementation notes

### Being the normalized blowing up at a point

Stacks 0BHJ defines the normalized blowing up as a *composition* of two morphisms, each of them
determined only up to isomorphism over its target: the blowing up of an algebraic space is not
constructed in this library, and the normalization is carried by the datum
`AlgebraicGeometry.Space.NormalizationData` rather than built.  Accordingly
`AlgebraicGeometry.Space.IsNormalizedBlowupAtClosedPoint` is a predicate, exactly as
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint` is: it says that the given morphism is, up to an
isomorphism of its source, the normalization morphism of some blowing up of `X` at the point
followed by that blowing up.  Carrying the isomorphism explicitly is what makes
`AlgebraicGeometry.Space.IsNormalizedBlowupAtClosedPoint.comp_iso` available, and that in turn
is what lets a tower be transported along an isomorphism of its top.

The decency of `X` and the finiteness condition
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents` — condition (2) of Stacks 0BB1 —
are taken as hypotheses, as the source takes them, and their names are underscored because the
predicate does not consume them: decency enters Stacks 0BHE only to produce the closed immersion
representing the point, which
`AlgebraicGeometry.Space.closedPointSubspace` dispenses with, and the finiteness condition
enters only to produce the normalization, which here is supplied as data.  They are kept so that
the predicate is stated on the class of spaces the source states it on, and so that a tower of
normalized blowings up records them at every stage, where they are genuinely new information:
nothing in this library propagates either condition from `Z_j` to `Z_{j+1}`.

### Towers as data

As for `AlgebraicGeometry.Space.BlowupTower`, the chain `Zₘ ⟶ … ⟶ Z₀ = X` is an inductive type
whose bottom step `Z₀ = X` is carried as an isomorphism `Z₀ ≅ X`, equality of objects of a
category not being the available notion; the composite `Z_j ⟶ X` and the number of steps are
definitions by recursion, and the condition on the centres is a predicate on the tower.  Each
step additionally carries the decency and finiteness of the space being blown up, these being
the standing hypotheses of Stacks 0BHJ at that stage.

### What is not here

The equivalence of Stacks 0BHL itself — that `f` is factored by such a sequence exactly when
every `gᵢ` is — is **not proved**, and the tag sits on the two conditions it compares.  The
source proves it by "the exact same argument as used to prove Lemma 0BHF", and that argument
*is* in this library, in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerEtaleRestriction.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerGlobalConverse.lean`: what it consumes of
Stacks 0BHB is the full faithfulness of the functor of Stacks 0BHA, rather than the whole
equivalence
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isEquivalence_restrictionFunctor`.
What is missing for the
normalized case is any comparison of a normalization with an étale base change of it, which is
what would let the normalization step of a tower be restricted to an étale neighborhood.

## References

* [Stacks Project, Tag 0BHJ](https://stacks.math.columbia.edu/tag/0BHJ)
* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Normality of an algebraic space transports along an isomorphism of the underlying
presheaves: a surjective étale chart of the one, followed by the isomorphism, is a surjective
étale chart of the other. -/
private theorem isNormal_of_iso_presheaf {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (h : IsNormal B S hS G) : IsNormal B S hS F := by
  obtain ⟨U, g, hgs, hge, hU⟩ := h
  have harrow : Arrow.mk g ≅ Arrow.mk (g ≫ e.inv) :=
    Arrow.isoMk (Iso.refl (yoneda.obj U)) e.symm (by simp)
  exact ⟨U, g ≫ e.inv, (MorphismProperty.arrow_mk_iso_iff _ harrow).mp hgs,
    (MorphismProperty.arrow_mk_iso_iff _ harrow).mp hge, hU⟩

/-! ### The normalized blowing up of an algebraic space at a closed point -/

section

variable {B S hS}

/-- The normalization of an algebraic space over `S` carrying normalization data, as an object
of the category of algebraic spaces over `S`. -/
def normalizationSpace {X : AlgebraicSpaces B S hS} (N : NormalizationData B S hS X.obj) :
    AlgebraicSpaces B S hS :=
  ⟨N.space, N.isAlgebraicSpace⟩

/-- The normalization morphism of an algebraic space over `S` carrying normalization data, as a
morphism in the category of algebraic spaces over `S`. -/
def normalizationHom {X : AlgebraicSpaces B S hS} (N : NormalizationData B S hS X.obj) :
    normalizationSpace N ⟶ X :=
  ObjectProperty.homMk N.hom

end

/-- **Stacks 0BHJ.** A morphism `f : X'' ⟶ X` of algebraic spaces **is the normalized blowing up
of `X` at the closed point `z`** when it is the composition of the normalization of a blowing up
of `X` at `z` with that blowing up: there are an algebraic space `X'`, a blowing up `b : X' ⟶ X`
of `X` at `z`, normalization data on `X'`, and an identification of `X''` with the normalization
carrying `f` to the normalization morphism followed by `b`.

The blowing up at `z` is `AlgebraicGeometry.Space.IsBlowupAtClosedPoint`, and the normalization
is the datum `AlgebraicGeometry.Space.NormalizationData`.  The decency hypothesis and the
finiteness condition of Stacks 0BB1 are those of the source. -/
@[stacks 0BHJ]
def IsNormalizedBlowupAtClosedPoint {X Y : AlgebraicSpaces B S hS}
    (_hX : IsDecentSpace B S hS X.obj)
    (_hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj)
    (z : points B S hS X.obj) (hz : IsClosed ({z} : Set (points B S hS X.obj)))
    (f : Y ⟶ X) : Prop :=
  ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X),
    IsBlowupAtClosedPoint B S hS z hz b ∧
      ∃ (N : NormalizationData B S hS X'.obj) (e : Y ≅ normalizationSpace N),
        e.hom ≫ (normalizationHom N ≫ b) = f

variable {B S hS}

/-- The normalization of a blowing up of `X` at a closed point, followed by that blowing up, is
the normalized blowing up of `X` at the point. -/
theorem isNormalizedBlowupAtClosedPoint_comp {X X' : AlgebraicSpaces B S hS}
    (hX : IsDecentSpace B S hS X.obj)
    (hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj)
    {z : points B S hS X.obj} {hz : IsClosed ({z} : Set (points B S hS X.obj))} {b : X' ⟶ X}
    (hb : IsBlowupAtClosedPoint B S hS z hz b) (N : NormalizationData B S hS X'.obj) :
    IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz (normalizationHom N ≫ b) :=
  ⟨X', b, hb, N, Iso.refl _, Category.id_comp _⟩

namespace IsNormalizedBlowupAtClosedPoint

/-- Precomposing the normalized blowing up at a closed point with an isomorphism gives again the
normalized blowing up at that point. -/
theorem comp_iso {X Y Y' : AlgebraicSpaces B S hS} {hX : IsDecentSpace B S hS X.obj}
    {hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz f) (e : Y' ≅ Y) :
    IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz (e.hom ≫ f) := by
  obtain ⟨X', b, hb, N, d, hd⟩ := h
  exact ⟨X', b, hb, N, e ≪≫ d, by rw [Iso.trans_hom, Category.assoc, hd]⟩

/-- **Stacks 0BHJ in the source's own words.**  A normalized blowing up of `X` at a closed point
exhibits its intermediate blowing up `X' ⟶ X` of `X` at that point and the normalization data on
`X'` whose normalization morphism it is, up to an isomorphism of its source. -/
theorem exists_blowup_normalizationData {X Y : AlgebraicSpaces B S hS}
    {hX : IsDecentSpace B S hS X.obj}
    {hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz f) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (N : NormalizationData B S hS X'.obj),
      IsBlowupAtClosedPoint B S hS z hz b ∧
        ∃ e : Y ≅ normalizationSpace N, e.hom ≫ (normalizationHom N ≫ b) = f := by
  obtain ⟨X', b, hb, N, e, he⟩ := h
  exact ⟨X', b, N, hb, e, he⟩

/-- **The source of a normalized blowing up is normal.**  It is isomorphic to the normalization
of the intermediate blowing up, and that normalization is a normal algebraic space by the
normality assertion of part (1) of Stacks 07U4. -/
theorem isNormal {X Y : AlgebraicSpaces B S hS} {hX : IsDecentSpace B S hS X.obj}
    {hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz f) :
    Space.IsNormal B S hS Y.obj := by
  obtain ⟨X', -, -, N, e, -⟩ := h
  exact isNormal_of_iso_presheaf B S hS ((ObjectProperty.ι _).mapIso e)
    (N.isNormal X'.property)

end IsNormalizedBlowupAtClosedPoint

/-! ### Towers of normalized blowups at closed points -/

/-- A **tower of normalized blowings up at closed points over `X`**: the chain

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

in which each `Z_{j+1} ⟶ Z_j` is the normalized blowing up of `Z_j` at a closed point of `Z_j`,
indexed by its top `Zₘ`.  The bottom identification `Z₀ = X` is carried as an isomorphism
`Z₀ ≅ X`, and each step carries the standing hypotheses of Stacks 0BHJ on the space it blows
up. -/
inductive NormalizedBlowupTower (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) : AlgebraicSpaces B S hS → Type (u + 1)
  /-- The empty tower: `Z₀` together with its identification with `X`. -/
  | base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X) : NormalizedBlowupTower B S hS X Z
  /-- Extend a tower with top `Z` by the normalized blowing up of `Z` at a closed point of
  `Z`. -/
  | step {Z Z' : AlgebraicSpaces B S hS} (t : NormalizedBlowupTower B S hS X Z)
      (hZ : IsDecentSpace B S hS Z.obj)
      (hZfin : HasLocallyFiniteIrreducibleComponents B S hS Z.obj) (b : Z' ⟶ Z)
      (z : points B S hS Z.obj) (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
      (hb : IsNormalizedBlowupAtClosedPoint B S hS hZ hZfin z hz b) :
      NormalizedBlowupTower B S hS X Z'

namespace NormalizedBlowupTower

variable {X X' : AlgebraicSpaces B S hS}

/-- The composite `Z_j ⟶ X` of a tower of normalized blowings up. -/
def proj : {Z : AlgebraicSpaces B S hS} → NormalizedBlowupTower B S hS X Z → (Z ⟶ X)
  | _, .base e => e.hom
  | _, .step t _ _ b _ _ _ => b ≫ proj t

/-- The number `m` of normalized blowings up in a tower. -/
def length : {Z : AlgebraicSpaces B S hS} → NormalizedBlowupTower B S hS X Z → ℕ
  | _, .base _ => 0
  | _, .step t _ _ _ _ _ _ => length t + 1

/-- Every centre of a tower of normalized blowings up lies over the set of points `T`. -/
def CentersOver : {Z : AlgebraicSpaces B S hS} → NormalizedBlowupTower B S hS X Z →
    Set (points B S hS X.obj) → Prop
  | _, .base _, _ => True
  | _, .step t _ _ _ z _ _, T => CentersOver t T ∧ pointsMap B S hS _ (proj t).hom z ∈ T

/-- The composite of the empty tower `base e` is `e.hom`. -/
@[simp]
theorem proj_base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X) :
    (NormalizedBlowupTower.base e : NormalizedBlowupTower B S hS X Z).proj = e.hom := rfl

/-- The composite of the tower `step t … b …` is `b` followed by the composite of `t`. -/
@[simp]
theorem proj_step {Z Z' : AlgebraicSpaces B S hS} (t : NormalizedBlowupTower B S hS X Z)
    (hZ : IsDecentSpace B S hS Z.obj)
    (hZfin : HasLocallyFiniteIrreducibleComponents B S hS Z.obj) (b : Z' ⟶ Z)
    (z : points B S hS Z.obj) (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
    (hb : IsNormalizedBlowupAtClosedPoint B S hS hZ hZfin z hz b) :
    (NormalizedBlowupTower.step t hZ hZfin b z hz hb).proj = b ≫ t.proj := rfl

/-- The empty tower `base e` has length `0`. -/
@[simp]
theorem length_base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X) :
    (NormalizedBlowupTower.base e : NormalizedBlowupTower B S hS X Z).length = 0 := rfl

/-- The tower `step t … b …` has length one more than that of `t`. -/
@[simp]
theorem length_step {Z Z' : AlgebraicSpaces B S hS} (t : NormalizedBlowupTower B S hS X Z)
    (hZ : IsDecentSpace B S hS Z.obj)
    (hZfin : HasLocallyFiniteIrreducibleComponents B S hS Z.obj) (b : Z' ⟶ Z)
    (z : points B S hS Z.obj) (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
    (hb : IsNormalizedBlowupAtClosedPoint B S hS hZ hZfin z hz b) :
    (NormalizedBlowupTower.step t hZ hZfin b z hz hb).length = t.length + 1 := rfl

/-- The empty tower `base e` has its centres over every set `T`, having none. -/
@[simp]
theorem centersOver_base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X)
    (T : Set (points B S hS X.obj)) :
    (NormalizedBlowupTower.base e : NormalizedBlowupTower B S hS X Z).CentersOver T ↔ True :=
  Iff.rfl

/-- The centres of the tower `step t … z …` lie over `T` exactly when those of `t` do and the
image of `z` in `X` under the composite of `t` lies in `T`. -/
@[simp]
theorem centersOver_step {Z Z' : AlgebraicSpaces B S hS} (t : NormalizedBlowupTower B S hS X Z)
    (hZ : IsDecentSpace B S hS Z.obj)
    (hZfin : HasLocallyFiniteIrreducibleComponents B S hS Z.obj) (b : Z' ⟶ Z)
    (z : points B S hS Z.obj) (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
    (hb : IsNormalizedBlowupAtClosedPoint B S hS hZ hZfin z hz b)
    (T : Set (points B S hS X.obj)) :
    (NormalizedBlowupTower.step t hZ hZfin b z hz hb).CentersOver T ↔
      t.CentersOver T ∧ pointsMap B S hS Z.obj t.proj.hom z ∈ T := Iff.rfl

/-- The condition that every centre lies over `T` grows with `T`. -/
theorem CentersOver.mono {Z : AlgebraicSpaces B S hS} {t : NormalizedBlowupTower B S hS X Z}
    {T T' : Set (points B S hS X.obj)} (hTT' : T ⊆ T') (h : t.CentersOver T) :
    t.CentersOver T' := by
  induction t with
  | base e => exact trivial
  | step t hZ hZfin b z hz hb ih => exact ⟨ih h.1, hTT' h.2⟩

/-- Transport a tower along an isomorphism of its top: a tower with top `Z` and an isomorphism
`Z' ≅ Z` give a tower with top `Z'`, with the same centres. -/
def comap : {Z Z' : AlgebraicSpaces B S hS} → (Z' ≅ Z) → NormalizedBlowupTower B S hS X Z →
    NormalizedBlowupTower B S hS X Z'
  | _, _, e, .base f => .base (e ≪≫ f)
  | _, _, e, .step t hZ hZfin b z hz hb =>
      .step t hZ hZfin (e.hom ≫ b) z hz (hb.comp_iso e)

/-- The composite of `comap e t` is `e.hom` followed by the composite of `t`. -/
@[simp]
theorem proj_comap {Z Z' : AlgebraicSpaces B S hS} (e : Z' ≅ Z)
    (t : NormalizedBlowupTower B S hS X Z) : (comap e t).proj = e.hom ≫ t.proj := by
  cases t <;> simp [comap]

/-- Transporting a tower along an isomorphism of its top does not change its length. -/
@[simp]
theorem length_comap {Z Z' : AlgebraicSpaces B S hS} (e : Z' ≅ Z)
    (t : NormalizedBlowupTower B S hS X Z) : (comap e t).length = t.length := by
  cases t <;> rfl

/-- The centres of `comap e t` lie over `T` exactly when those of `t` do. -/
@[simp]
theorem centersOver_comap {Z Z' : AlgebraicSpaces B S hS} (e : Z' ≅ Z)
    (t : NormalizedBlowupTower B S hS X Z) (T : Set (points B S hS X.obj)) :
    (comap e t).CentersOver T ↔ t.CentersOver T := by
  cases t <;> simp [comap]

/-- Concatenate a tower over the base `X'` with a tower over `X` whose top is `X'`: this is the
step by which the induction behind Stacks 0BHL lengthens a sequence of normalized blowings
up. -/
def append : {Z : AlgebraicSpaces B S hS} → NormalizedBlowupTower B S hS X' Z →
    NormalizedBlowupTower B S hS X X' → NormalizedBlowupTower B S hS X Z
  | _, .base e, s => comap e s
  | _, .step t hZ hZfin b z hz hb, s => .step (append t s) hZ hZfin b z hz hb

/-- The composite of `t.append s` is the composite of `t` followed by that of `s`. -/
@[simp]
theorem proj_append : {Z : AlgebraicSpaces B S hS} → (t : NormalizedBlowupTower B S hS X' Z) →
    (s : NormalizedBlowupTower B S hS X X') → (t.append s).proj = t.proj ≫ s.proj
  | _, .base e, s => by simp [append]
  | _, .step t hZ hZfin b z hz hb, s => by simp [append, proj_append t s]

/-- The length of `t.append s` is the sum of the lengths of `t` and `s`. -/
@[simp]
theorem length_append : {Z : AlgebraicSpaces B S hS} → (t : NormalizedBlowupTower B S hS X' Z) →
    (s : NormalizedBlowupTower B S hS X X') → (t.append s).length = t.length + s.length
  | _, .base e, s => by simp [append]
  | _, .step t hZ hZfin b z hz hb, s => by simp [append, length_append t s, Nat.succ_add]

/-- The centres of a concatenation of towers lie over `T` exactly when those of the lower tower
do and those of the upper tower lie over the preimage of `T`. -/
theorem centersOver_append :
    {Z : AlgebraicSpaces B S hS} → (t : NormalizedBlowupTower B S hS X' Z) →
    (s : NormalizedBlowupTower B S hS X X') → (T : Set (points B S hS X.obj)) →
    ((t.append s).CentersOver T ↔
      t.CentersOver (pointsMap B S hS X'.obj s.proj.hom ⁻¹' T) ∧ s.CentersOver T)
  | _, .base e, s, T => by simp [append]
  | _, .step t hZ hZfin b z hz hb, s, T => by
      rw [append, centersOver_step, centersOver_step, centersOver_append t s T, proj_append,
        ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp]
      simp only [Set.mem_preimage, Function.comp_apply]
      tauto

end NormalizedBlowupTower

/-! ### Factoring a morphism as a sequence of normalized blowups at closed points -/

/-- **A factorization of `f : Y ⟶ X` as a sequence of normalized blowings up at closed points
lying over the set of points `T ⊆ |X|`**: a tower

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

of normalized blowings up at closed points, all of whose centres lie over `T`, together with an
identification of `Y` with its top `Zₘ` under which `f` is the composite `Zₘ ⟶ X`.

This is the condition on both sides of Stacks 0BHL, taken there with `T = {x₁, …, xₙ}` for the
morphism to `X` and with `T = {uᵢ}` for the morphism to the `i`th étale neighborhood. -/
@[stacks 0BHL "the condition asserted on both sides of the equivalence: a factorization of the
given morphism as a finite sequence of normalized blowings up at closed points lying over the
given set of points. The equivalence itself is not proved: its proof is the argument of
Tag 0BHF, which this library does carry, together with a comparison of a normalization with an
étale base change of it, which it does not."]
structure NormalizedBlowupFactorization (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (T : Set (points B S hS X.obj))
    (f : Y ⟶ X) where
  /-- The top `Zₘ` of the tower. -/
  top : AlgebraicSpaces B S hS
  /-- The tower `Zₘ ⟶ … ⟶ Z₀ = X` of normalized blowings up at closed points. -/
  tower : NormalizedBlowupTower B S hS X top
  /-- Every centre of the tower lies over `T`. -/
  centersOver : tower.CentersOver T
  /-- The identification `Y = Zₘ`. -/
  iso : Y ≅ top
  /-- Under that identification, `f` is the composite `Zₘ ⟶ X`. -/
  iso_proj : iso.hom ≫ tower.proj = f

namespace NormalizedBlowupFactorization

variable {X Y : AlgebraicSpaces B S hS}

/-- The number `m` of normalized blowings up in a factorization. -/
def length {T : Set (points B S hS X.obj)} {f : Y ⟶ X}
    (F : NormalizedBlowupFactorization B S hS T f) : ℕ :=
  F.tower.length

/-- An isomorphism is factored by the empty sequence of normalized blowings up. -/
def ofIso (T : Set (points B S hS X.obj)) (e : Y ≅ X) :
    NormalizedBlowupFactorization B S hS T e.hom where
  top := Y
  tower := .base e
  centersOver := trivial
  iso := Iso.refl Y
  iso_proj := by simp

/-- The normalized blowing up at a closed point lying over `T` is factored by a sequence of
length one. -/
def ofBlowup (T : Set (points B S hS X.obj)) {hX : IsDecentSpace B S hS X.obj}
    {hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (hb : IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz f) (hzT : z ∈ T) :
    NormalizedBlowupFactorization B S hS T f where
  top := Y
  tower := .step (.base (Iso.refl X)) hX hXfin f z hz hb
  centersOver := by
    refine ⟨trivial, ?_⟩
    simpa using hzT
  iso := Iso.refl Y
  iso_proj := by simp

/-- The factorization condition grows with the set of points. -/
def mono {T T' : Set (points B S hS X.obj)} {f : Y ⟶ X}
    (F : NormalizedBlowupFactorization B S hS T f) (hTT' : T ⊆ T') :
    NormalizedBlowupFactorization B S hS T' f where
  top := F.top
  tower := F.tower
  centersOver := F.centersOver.mono hTT'
  iso := F.iso
  iso_proj := F.iso_proj

/-- **A composite of two factored morphisms is factored.**  If `p : Z ⟶ X` is a sequence of
normalized blowings up at closed points lying over `T` and `q : Y ⟶ Z` is one at closed points
lying over the preimage of `T`, then so is `q ≫ p`; the two sequences are concatenated. -/
def comp {Z : AlgebraicSpaces B S hS} {T : Set (points B S hS X.obj)} {p : Z ⟶ X} {q : Y ⟶ Z}
    (F : NormalizedBlowupFactorization B S hS T p)
    (G : NormalizedBlowupFactorization B S hS (pointsMap B S hS Z.obj p.hom ⁻¹' T) q) :
    NormalizedBlowupFactorization B S hS T (q ≫ p) where
  top := G.top
  tower := (G.tower.append (.base F.iso)).append F.tower
  centersOver := by
    rw [NormalizedBlowupTower.centersOver_append, NormalizedBlowupTower.centersOver_append]
    refine ⟨⟨?_, trivial⟩, F.centersOver⟩
    refine NormalizedBlowupTower.CentersOver.mono ?_ G.centersOver
    intro w hw
    have hp : F.iso.hom.hom ≫ F.tower.proj.hom = p.hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, F.iso_proj]
    simp only [Set.mem_preimage, NormalizedBlowupTower.proj_base] at hw ⊢
    rw [← Function.comp_apply (f := pointsMap B S hS F.top.obj F.tower.proj.hom),
      ← pointsMap_comp, hp]
    exact hw
  iso := G.iso
  iso_proj := by
    rw [NormalizedBlowupTower.proj_append, NormalizedBlowupTower.proj_append,
      NormalizedBlowupTower.proj_base, ← Category.assoc, ← Category.assoc, G.iso_proj,
      Category.assoc, F.iso_proj]

end NormalizedBlowupFactorization

/-! ### The two sides of Stacks 0BHL -/

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **Stacks 0BHL**, the condition on the morphism to `X`: `f : Y ⟶ X` factors as

`Y = Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

where each `Z_{j+1} ⟶ Z_j` is the normalized blowing up of `Z_j` at a closed point `z_j` lying
over `{x₁, …, xₙ}`. -/
@[stacks 0BHL "the left-hand side of the equivalence: the factorization of the morphism to X by \
normalized blowings up at closed points lying over {x₁, …, xₙ}"]
abbrev GlobalNormalizedBlowupFactorization {Y : AlgebraicSpaces B S hS} (f : Y ⟶ D.space) :=
  NormalizedBlowupFactorization B S hS (Set.range D.point) f

/-- **Stacks 0BHL**, the condition on the morphism to the `i`th étale neighborhood:
`gᵢ : Yᵢ ⟶ Uᵢ` factors as

`Yᵢ = Z_{i, mᵢ} ⟶ … ⟶ Z_{i, 1} ⟶ Z_{i, 0} = Uᵢ`

where each `Z_{i, j+1} ⟶ Z_{i, j}` is the normalized blowing up of `Z_{i, j}` at a closed point
lying over `uᵢ`. -/
@[stacks 0BHL "the right-hand side of the equivalence: the factorization of the morphism to the \
i-th elementary étale neighborhood by normalized blowings up at closed points lying over uᵢ"]
abbrev LocalNormalizedBlowupFactorization (i : Fin n) {Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ D.neighborhoodSpace i) :=
  NormalizedBlowupFactorization B S hS ({D.neighborhoodPoint i} : Set (points B S hS _)) g

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
