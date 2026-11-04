module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Blowing up an algebraic space at a closed point, and towers of such blowups

Let `S` be a scheme and let `X` be an algebraic space over `S` with a closed point
`z ∈ |X|`.  The *blowing up of `X` at `z`* is the blowing up of `X` in the reduced closed
subspace supported on `{z}`, which is **Stacks 0BHE**.

A *tower of blowups at closed points over `X`* is a finite chain

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

in which each `Z_{j+1} ⟶ Z_j` is the blowing up of `Z_j` at a closed point `z_j ∈ |Z_j|`.  A
morphism `f : Y ⟶ X` *factors as a sequence of blowings up at closed points lying over a set
`T ⊆ |X|`* when there is such a tower whose centres `z_j` all map into `T` and whose top `Zₘ`
is identified with `Y` compatibly with `f`.  This is the condition appearing on both sides of
**Stacks 0BHF**, with `T = {x₁, …, xₙ}` on the one side and `T = {uᵢ}` on the other; see
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.GlobalBlowupFactorization` and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.LocalBlowupFactorization`.

## Main definitions

* `AlgebraicGeometry.Space.closedPointSubspace` is the centre of the blowing up at a closed
  point: the reduced closed subspace of Stacks 03IQ supported on that point.
* `AlgebraicGeometry.Space.IsBlowupAtClosedPoint` is **Stacks 0BHE**.
* `AlgebraicGeometry.Space.BlowupTower` is the chain `Zₘ ⟶ … ⟶ Z₀ = X` as data, with
  `AlgebraicGeometry.Space.BlowupTower.proj` the composite `Z_j ⟶ X`,
  `AlgebraicGeometry.Space.BlowupTower.length` the number `m` of steps and
  `AlgebraicGeometry.Space.BlowupTower.CentersOver` the condition that every centre lies over
  a given set of points.
* `AlgebraicGeometry.Space.BlowupFactorization` is the factorization of a given morphism by
  such a tower, again as data.

## Main results

* `AlgebraicGeometry.Space.eq_closedPointSubspace` identifies the centre with the image of any
  closed immersion representing the point, which is how Stacks 0BHE names it.
* `AlgebraicGeometry.Space.BlowupTower.comap` and `AlgebraicGeometry.Space.BlowupTower.append`
  transport a tower along an isomorphism of its top and concatenate two towers; the latter is
  the step by which the induction in Stacks 0BHF lengthens a sequence of blowings up.
* `AlgebraicGeometry.Space.BlowupFactorization.ofIso`,
  `AlgebraicGeometry.Space.BlowupFactorization.ofBlowup`,
  `AlgebraicGeometry.Space.BlowupFactorization.comp` and
  `AlgebraicGeometry.Space.BlowupFactorization.mono` are the closure properties of the
  factorization condition: an isomorphism is factored by the empty sequence, a single blowing
  up at a closed point over `T` by a sequence of length one, a composite of two factored
  morphisms is factored, and the condition grows with `T`.

## Implementation notes

### The centre of the blowing up at a point

Stacks 0BHE takes `X` decent, represents the closed point `z` by a closed immersion
`i : Spec(k) ⟶ X` and blows up the closed subspace `i(Spec(k))`.  That closed subspace is
closed with point set `{z}` and is reduced, so by the uniqueness half of Stacks 03IQ it is the
reduced closed subspace supported on `{z}`, which is the datum
`AlgebraicGeometry.Space.reducedClosedSubspace`.  The centre is therefore taken to be that
subspace: `AlgebraicGeometry.Space.eq_closedPointSubspace` is the identification, and taking
it as the definition drops the decency hypothesis, which is used in the source only to produce
the closed immersion `i`.

### Being the blowing up at a point

`AlgebraicGeometry.Space.IsBlowupAlong` of Stacks 085U says that a morphism is *the* blowing up
in a closed subspace, by the universal property; the blowing up of an algebraic space is not
constructed in the library, as
`StacksFrontier/AlgebraicGeometry/Spaces/AdmissibleBlowup.lean` explains at length.  Being the
blowing up *at a closed point* is said here as the source says it — there is a blowing up of
`X` in `closedPointSubspace z hz` to which the given morphism is isomorphic over `X` — rather
than as `IsBlowupAlong` applied to the given morphism itself.  The two readings pick out the
same morphisms, `IsBlowupAlong` being a terminality condition and hence invariant under
isomorphism over `X`; carrying the isomorphism explicitly is what makes
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint.comp_iso` available, and that in turn is what
lets a tower be transported along an isomorphism of its top without transporting the
sheaf-theoretic effective-Cartier condition of Stacks 083Y across it.

### Towers as data

The chain `Zₘ ⟶ … ⟶ Z₀ = X` is an inductive type, with the bottom step `Z₀ = X` carried as an
isomorphism `Z₀ ≅ X`, since equality of objects of a category is not the available notion.  The
composite `Z_j ⟶ X` and the number of steps are then definitions by recursion rather than
fields, and the condition that the centres lie over a given set of points is a predicate on the
tower, stated through the composite.  The factorization of a morphism `f : Y ⟶ X` records the
tower, an isomorphism `Y ≅ Zₘ` and the equation saying that `f` is that isomorphism followed by
the composite — the factorization is data, exactly as the source's "`f` factors as" asserts the
existence of the chain itself and not merely of a proposition about it.

### Where the equivalence of Stacks 0BHF is

The "only if" direction — a factorization of `f` gives one of every `gᵢ` — is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerEtaleRestriction.lean`, as
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_localBlowupFactorization` and its
specialization at the functor `F` of Stacks 0BHA; the local sequence is the base change of the
global one, by Stacks 085S.  The converse is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerGlobalConverse.lean`, as
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_of_isPullback`
and its specialization at `F`, by the induction of the source; it consumes the full faithfulness
of `F`, the half of Stacks 0BHB the source omits, which is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModificationsAtClosedPointsFullyFaithful.lean`, and the
existence of the blowing up of an algebraic space at a closed point, which is
`AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint_unconditional` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupAtClosedPointExistenceUnconditional.lean`.  The
latter takes `[HasSheafify (BigFppfOver.topology B S hS) (Type u)]` as an instance argument,
which `AlgebraicGeometry.BigFppfOver.hasSheafify_type` supplies outright from essential
smallness of the big fppf site, so neither the converse nor the equivalence
`…nonempty_globalBlowupFactorization_iff` takes it.  The equivalence carries the
`@[stacks 0BHF]` attribute.

The base case of the converse — every `gᵢ` factored by the empty sequence, so that `f` is too —
is proved separately, in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerEtaleDescent.lean`; the morphism is then an
isomorphism by fppf locality of isomorphisms on the covering family `X ∖ {x₁, …, xₙ}`, `U₁`,
…, `Uₙ` of `X`, and `AlgebraicGeometry.Space.BlowupFactorization.ofIso` applies.

The identification of fibres of Stacks 0BHD, which the source's proof also cites, *is*
available, as `AlgebraicGeometry.Space.ClosedPointNeighborhoods.fibreAtPointIso` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModificationsAtClosedPointsProperties.lean`; the proof of
the "only if" direction given here does not use it, computing the inverse image of a centre
directly instead.

## References

* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The blowing up of an algebraic space at a closed point -/

/-- The centre of the blowing up of an algebraic space at a closed point: the reduced closed
subspace of Stacks 03IQ supported on that point.

Stacks 0BHE writes this subspace as the image `i(Spec(k))` of a closed immersion representing
the point; `AlgebraicGeometry.Space.eq_closedPointSubspace` identifies the two. -/
def closedPointSubspace {X : AlgebraicSpaces B S hS} (z : points B S hS X.obj)
    (hz : IsClosed ({z} : Set (points B S hS X.obj))) : ClosedSubspaces B S hS X.obj :=
  ⟨reducedClosedSubspace B S hS X.obj X.property {z} hz,
    isClosedSubspace_reducedClosedSubspace B S hS X.obj X.property {z} hz⟩

/-- **The centre of the blowing up at a closed point is the image of any closed immersion
representing the point.**  A closed subspace of `X` whose point set is `{z}` and which is
étale-locally reduced is `AlgebraicGeometry.Space.closedPointSubspace`.

This is the uniqueness half of Stacks 03IQ, and it is what makes the centre used here the
`Z = i(Spec(k))` of Stacks 0BHE: the image of a closed immersion `i : Spec(k) ⟶ X`
representing the closed point `z` is a closed subspace with point set `{z}`, and `Spec(k)` is
reduced. -/
theorem eq_closedPointSubspace {X : AlgebraicSpaces B S hS} (z : points B S hS X.obj)
    (hz : IsClosed ({z} : Set (points B S hS X.obj))) (W : Subfunctor X.obj)
    (hWc : IsClosedSubspace B S hS W)
    (hWz : Set.range (pointsMap B S hS W.toFunctor W.ι) = {z})
    (hWr : HasEtaleLocalProperty B S hS W.toFunctor (fun Y : Scheme.{u} => IsReduced Y)) :
    W = (closedPointSubspace B S hS z hz).1 :=
  eq_reducedClosedSubspace B S hS X.obj X.property {z} hz W hWc hWz hWr

/-- **Stacks 0BHE.** A morphism `f : Y ⟶ X` of algebraic spaces **is the blowing up of `X` at
the closed point `z`** when there is a blowing up of `X` in the reduced closed subspace
supported on `{z}` to which `f` is isomorphic over `X`.

Being the blowing up in a closed subspace is the universal property of Stacks 085U, which is
`AlgebraicGeometry.Space.IsBlowupAlong`; it already determines the morphism up to isomorphism
over `X`, so asking for the isomorphism here changes nothing and makes
`AlgebraicGeometry.Space.IsBlowupAtClosedPoint.comp_iso` available.  The centre is
`AlgebraicGeometry.Space.closedPointSubspace`, which is the `i(Spec(k))` of the source by
`AlgebraicGeometry.Space.eq_closedPointSubspace`. -/
@[stacks 0BHE]
def IsBlowupAtClosedPoint {X Y : AlgebraicSpaces B S hS} (z : points B S hS X.obj)
    (hz : IsClosed ({z} : Set (points B S hS X.obj))) (f : Y ⟶ X) : Prop :=
  ∃ (W : AlgebraicSpaces B S hS) (b : W ⟶ X),
    IsBlowupAlong B S hS (closedPointSubspace B S hS z hz) b ∧ ∃ e : Y ≅ W, e.hom ≫ b = f

variable {B S hS}

/-- A blowing up of `X` in the reduced closed subspace on a closed point is the blowing up of
`X` at that point. -/
theorem isBlowupAtClosedPoint_of_isBlowupAlong {X Y : AlgebraicSpaces B S hS}
    {z : points B S hS X.obj} {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsBlowupAlong B S hS (closedPointSubspace B S hS z hz) f) :
    IsBlowupAtClosedPoint B S hS z hz f :=
  ⟨Y, f, h, Iso.refl Y, Category.id_comp f⟩

namespace IsBlowupAtClosedPoint

/-- Precomposing the blowing up at a closed point with an isomorphism gives again the blowing
up at that point. -/
theorem comp_iso {X Y Y' : AlgebraicSpaces B S hS} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsBlowupAtClosedPoint B S hS z hz f) (e : Y' ≅ Y) :
    IsBlowupAtClosedPoint B S hS z hz (e.hom ≫ f) := by
  obtain ⟨W, b, hb, d, hd⟩ := h
  exact ⟨W, b, hb, e ≪≫ d, by rw [Iso.trans_hom, Category.assoc, hd]⟩

/-- If `f : Y ⟶ X` is the blowing up of `X` at the closed point `z`, then `Y` is isomorphic over
`X` to *any* blowing up of `X` in the reduced closed subspace supported on `{z}`. -/
theorem exists_iso_blowup {X Y : AlgebraicSpaces B S hS} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsBlowupAtClosedPoint B S hS z hz f) (W : AlgebraicSpaces B S hS) (b : W ⟶ X)
    (hb : IsBlowupAlong B S hS (closedPointSubspace B S hS z hz) b) :
    ∃ e : Y ≅ W, e.hom ≫ b = f := by
  obtain ⟨W', b', hb', d, hd⟩ := h
  obtain ⟨e, he⟩ := hb'.exists_iso hb
  exact ⟨d ≪≫ e, by rw [Iso.trans_hom, Category.assoc, he, hd]⟩

end IsBlowupAtClosedPoint

/-! ### Towers of blowups at closed points -/

/-- A **tower of blowings up at closed points over `X`**: the chain

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

in which each `Z_{j+1} ⟶ Z_j` is the blowing up of `Z_j` at a closed point of `Z_j`, indexed by
its top `Zₘ`.  The bottom identification `Z₀ = X` is carried as an isomorphism `Z₀ ≅ X`. -/
inductive BlowupTower (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) : AlgebraicSpaces B S hS → Type (u + 1)
  /-- The empty tower: `Z₀` together with its identification with `X`. -/
  | base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X) : BlowupTower B S hS X Z
  /-- Extend a tower with top `Z` by the blowing up of `Z` at a closed point of `Z`. -/
  | step {Z Z' : AlgebraicSpaces B S hS} (t : BlowupTower B S hS X Z) (b : Z' ⟶ Z)
      (z : points B S hS Z.obj) (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
      (hb : IsBlowupAtClosedPoint B S hS z hz b) : BlowupTower B S hS X Z'

namespace BlowupTower

variable {X X' : AlgebraicSpaces B S hS}

/-- The composite `Z_j ⟶ X` of a tower of blowings up. -/
def proj : {Z : AlgebraicSpaces B S hS} → BlowupTower B S hS X Z → (Z ⟶ X)
  | _, .base e => e.hom
  | _, .step t b _ _ _ => b ≫ proj t

/-- The number `m` of blowings up in a tower. -/
def length : {Z : AlgebraicSpaces B S hS} → BlowupTower B S hS X Z → ℕ
  | _, .base _ => 0
  | _, .step t _ _ _ _ => length t + 1

/-- Every centre of a tower of blowings up lies over the set of points `T`. -/
def CentersOver : {Z : AlgebraicSpaces B S hS} → BlowupTower B S hS X Z →
    Set (points B S hS X.obj) → Prop
  | _, .base _, _ => True
  | _, .step t _ z _ _, T => CentersOver t T ∧ pointsMap B S hS _ (proj t).hom z ∈ T

/-- The composite of the empty tower is its identification with `X`. -/
@[simp]
theorem proj_base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X) :
    (BlowupTower.base e : BlowupTower B S hS X Z).proj = e.hom := rfl

/-- The composite of an extended tower is the new blowing up followed by the composite of the
tower it extends. -/
@[simp]
theorem proj_step {Z Z' : AlgebraicSpaces B S hS} (t : BlowupTower B S hS X Z) (b : Z' ⟶ Z)
    (z : points B S hS Z.obj) (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
    (hb : IsBlowupAtClosedPoint B S hS z hz b) :
    (BlowupTower.step t b z hz hb).proj = b ≫ t.proj := rfl

/-- The empty tower has length `0`. -/
@[simp]
theorem length_base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X) :
    (BlowupTower.base e : BlowupTower B S hS X Z).length = 0 := rfl

/-- Extending a tower by one blowing up increases its length by one. -/
@[simp]
theorem length_step {Z Z' : AlgebraicSpaces B S hS} (t : BlowupTower B S hS X Z) (b : Z' ⟶ Z)
    (z : points B S hS Z.obj) (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
    (hb : IsBlowupAtClosedPoint B S hS z hz b) :
    (BlowupTower.step t b z hz hb).length = t.length + 1 := rfl

/-- Every centre of the empty tower lies over any set of points. -/
@[simp]
theorem centersOver_base {Z : AlgebraicSpaces B S hS} (e : Z ≅ X)
    (T : Set (points B S hS X.obj)) :
    (BlowupTower.base e : BlowupTower B S hS X Z).CentersOver T ↔ True := Iff.rfl

/-- The centres of an extended tower lie over `T` exactly when those of the tower it extends do
and the image in `X` of the new centre lies in `T`. -/
@[simp]
theorem centersOver_step {Z Z' : AlgebraicSpaces B S hS} (t : BlowupTower B S hS X Z)
    (b : Z' ⟶ Z) (z : points B S hS Z.obj)
    (hz : IsClosed ({z} : Set (points B S hS Z.obj)))
    (hb : IsBlowupAtClosedPoint B S hS z hz b) (T : Set (points B S hS X.obj)) :
    (BlowupTower.step t b z hz hb).CentersOver T ↔
      t.CentersOver T ∧ pointsMap B S hS Z.obj t.proj.hom z ∈ T := Iff.rfl

/-- The condition that every centre lies over `T` grows with `T`. -/
theorem CentersOver.mono {Z : AlgebraicSpaces B S hS} {t : BlowupTower B S hS X Z}
    {T T' : Set (points B S hS X.obj)} (hTT' : T ⊆ T') (h : t.CentersOver T) :
    t.CentersOver T' := by
  induction t with
  | base e => exact trivial
  | step t b z hz hb ih => exact ⟨ih h.1, hTT' h.2⟩

/-- Transport a tower along an isomorphism of its top: a tower with top `Z` and an isomorphism
`Z' ≅ Z` give a tower with top `Z'`, with the same centres. -/
def comap : {Z Z' : AlgebraicSpaces B S hS} → (Z' ≅ Z) → BlowupTower B S hS X Z →
    BlowupTower B S hS X Z'
  | _, _, e, .base f => .base (e ≪≫ f)
  | _, _, e, .step t b z hz hb => .step t (e.hom ≫ b) z hz (hb.comp_iso e)

/-- The composite of a transported tower is the isomorphism followed by the original composite. -/
@[simp]
theorem proj_comap {Z Z' : AlgebraicSpaces B S hS} (e : Z' ≅ Z) (t : BlowupTower B S hS X Z) :
    (comap e t).proj = e.hom ≫ t.proj := by
  cases t with
  | base f => simp [comap]
  | step t b z hz hb => simp [comap]

/-- Transporting a tower along an isomorphism of its top preserves its length. -/
@[simp]
theorem length_comap {Z Z' : AlgebraicSpaces B S hS} (e : Z' ≅ Z)
    (t : BlowupTower B S hS X Z) : (comap e t).length = t.length := by
  cases t with
  | base f => rfl
  | step t b z hz hb => rfl

/-- Transporting a tower along an isomorphism of its top does not change whether its centres lie
over `T`. -/
@[simp]
theorem centersOver_comap {Z Z' : AlgebraicSpaces B S hS} (e : Z' ≅ Z)
    (t : BlowupTower B S hS X Z) (T : Set (points B S hS X.obj)) :
    (comap e t).CentersOver T ↔ t.CentersOver T := by
  cases t with
  | base f => simp [comap]
  | step t b z hz hb => simp [comap]

/-- Concatenate a tower over the base `X'` with a tower over `X` whose top is `X'`. -/
def append : {Z : AlgebraicSpaces B S hS} → BlowupTower B S hS X' Z →
    BlowupTower B S hS X X' → BlowupTower B S hS X Z
  | _, .base e, s => comap e s
  | _, .step t b z hz hb, s => .step (append t s) b z hz hb

/-- The composite of a concatenation of towers is the composite of the upper tower followed by
that of the lower tower. -/
@[simp]
theorem proj_append : {Z : AlgebraicSpaces B S hS} → (t : BlowupTower B S hS X' Z) →
    (s : BlowupTower B S hS X X') → (t.append s).proj = t.proj ≫ s.proj
  | _, .base e, s => by simp [append]
  | _, .step t b z hz hb, s => by simp [append, proj_append t s]

/-- The length of a concatenation of towers is the sum of their lengths. -/
@[simp]
theorem length_append : {Z : AlgebraicSpaces B S hS} → (t : BlowupTower B S hS X' Z) →
    (s : BlowupTower B S hS X X') → (t.append s).length = t.length + s.length
  | _, .base e, s => by simp [append]
  | _, .step t b z hz hb, s => by simp [append, length_append t s, Nat.succ_add]

/-- The centres of a concatenation of towers lie over `T` exactly when those of the lower tower
do and those of the upper tower lie over the preimage of `T`. -/
theorem centersOver_append : {Z : AlgebraicSpaces B S hS} → (t : BlowupTower B S hS X' Z) →
    (s : BlowupTower B S hS X X') → (T : Set (points B S hS X.obj)) →
    ((t.append s).CentersOver T ↔
      t.CentersOver (pointsMap B S hS X'.obj s.proj.hom ⁻¹' T) ∧ s.CentersOver T)
  | _, .base e, s, T => by simp [append]
  | _, .step t b z hz hb, s, T => by
      rw [append, centersOver_step, centersOver_step, centersOver_append t s T, proj_append,
        ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp]
      simp only [Set.mem_preimage, Function.comp_apply]
      tauto

end BlowupTower

/-! ### Factoring a morphism as a sequence of blowups at closed points -/

/-- **A factorization of `f : Y ⟶ X` as a sequence of blowings up at closed points lying over
the set of points `T ⊆ |X|`**: a tower

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

of blowings up at closed points, all of whose centres lie over `T`, together with an
identification of `Y` with its top `Zₘ` under which `f` is the composite `Zₘ ⟶ X`.

This is the condition on both sides of **Stacks 0BHF**, taken there with `T = {x₁, …, xₙ}` for
the morphism to `X` and with `T = {uᵢ}` for the morphism to the `i`th étale neighborhood. -/
@[stacks 0BHF "the condition asserted on both sides of the equivalence: a factorization of the
given morphism as a finite sequence of blowings up at closed points lying over the given set of
points. The equivalence itself is
AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_globalBlowupFactorization_iff."]
structure BlowupFactorization (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (T : Set (points B S hS X.obj)) (f : Y ⟶ X) where
  /-- The top `Zₘ` of the tower. -/
  top : AlgebraicSpaces B S hS
  /-- The tower `Zₘ ⟶ … ⟶ Z₀ = X` of blowings up at closed points. -/
  tower : BlowupTower B S hS X top
  /-- Every centre of the tower lies over `T`. -/
  centersOver : tower.CentersOver T
  /-- The identification `Y = Zₘ`. -/
  iso : Y ≅ top
  /-- Under that identification, `f` is the composite `Zₘ ⟶ X`. -/
  iso_proj : iso.hom ≫ tower.proj = f

namespace BlowupFactorization

variable {X Y : AlgebraicSpaces B S hS}

/-- The number `m` of blowings up in a factorization. -/
def length {T : Set (points B S hS X.obj)} {f : Y ⟶ X} (F : BlowupFactorization B S hS T f) :
    ℕ :=
  F.tower.length

/-- An isomorphism is factored by the empty sequence of blowings up. -/
def ofIso (T : Set (points B S hS X.obj)) (e : Y ≅ X) :
    BlowupFactorization B S hS T e.hom where
  top := Y
  tower := .base e
  centersOver := trivial
  iso := Iso.refl Y
  iso_proj := by simp

/-- The blowing up at a closed point lying over `T` is factored by a sequence of length one. -/
def ofBlowup (T : Set (points B S hS X.obj)) {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (hb : IsBlowupAtClosedPoint B S hS z hz f) (hzT : z ∈ T) :
    BlowupFactorization B S hS T f where
  top := Y
  tower := .step (.base (Iso.refl X)) f z hz hb
  centersOver := by
    refine ⟨trivial, ?_⟩
    simpa using hzT
  iso := Iso.refl Y
  iso_proj := by simp

/-- The factorization condition grows with the set of points. -/
def mono {T T' : Set (points B S hS X.obj)} {f : Y ⟶ X} (F : BlowupFactorization B S hS T f)
    (hTT' : T ⊆ T') : BlowupFactorization B S hS T' f where
  top := F.top
  tower := F.tower
  centersOver := F.centersOver.mono hTT'
  iso := F.iso
  iso_proj := F.iso_proj

/-- **A composite of two factored morphisms is factored.**  If `p : Z ⟶ X` is a sequence of
blowings up at closed points lying over `T` and `q : Y ⟶ Z` is one at closed points lying over
the preimage of `T`, then so is `q ≫ p`; the two sequences are concatenated. -/
def comp {Z : AlgebraicSpaces B S hS} {T : Set (points B S hS X.obj)} {p : Z ⟶ X} {q : Y ⟶ Z}
    (F : BlowupFactorization B S hS T p)
    (G : BlowupFactorization B S hS (pointsMap B S hS Z.obj p.hom ⁻¹' T) q) :
    BlowupFactorization B S hS T (q ≫ p) where
  top := G.top
  tower := (G.tower.append (.base F.iso)).append F.tower
  centersOver := by
    rw [BlowupTower.centersOver_append, BlowupTower.centersOver_append]
    refine ⟨⟨?_, trivial⟩, F.centersOver⟩
    refine BlowupTower.CentersOver.mono ?_ G.centersOver
    intro w hw
    have hp : F.iso.hom.hom ≫ F.tower.proj.hom = p.hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, F.iso_proj]
    simp only [Set.mem_preimage, BlowupTower.proj_base] at hw ⊢
    rw [← Function.comp_apply (f := pointsMap B S hS F.top.obj F.tower.proj.hom),
      ← pointsMap_comp, hp]
    exact hw
  iso := G.iso
  iso_proj := by
    rw [BlowupTower.proj_append, BlowupTower.proj_append, BlowupTower.proj_base,
      ← Category.assoc, ← Category.assoc, G.iso_proj, Category.assoc, F.iso_proj]

end BlowupFactorization

/-! ### The two sides of Stacks 0BHF -/

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- **Stacks 0BHF**, the condition on the morphism to `X`: `f : Y ⟶ X` factors as

`Y = Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

where each `Z_{j+1} ⟶ Z_j` is the blowing up of `Z_j` at a closed point `z_j` lying over
`{x₁, …, xₙ}`. -/
@[stacks 0BHF "the condition on the morphism to X: it factors as a finite sequence of blowings
up at closed points lying over x₁, …, xₙ"]
abbrev GlobalBlowupFactorization {Y : AlgebraicSpaces B S hS} (f : Y ⟶ D.space) :=
  BlowupFactorization B S hS (Set.range D.point) f

/-- **Stacks 0BHF**, the condition on the morphism to the `i`th étale neighborhood:
`gᵢ : Yᵢ ⟶ Uᵢ` factors as

`Yᵢ = Z_{i, mᵢ} ⟶ … ⟶ Z_{i, 1} ⟶ Z_{i, 0} = Uᵢ`

where each `Z_{i, j+1} ⟶ Z_{i, j}` is the blowing up of `Z_{i, j}` at a closed point lying over
`uᵢ`. -/
@[stacks 0BHF "the condition on the morphism to the i-th étale neighborhood: it factors as a
finite sequence of blowings up at closed points lying over uᵢ"]
abbrev LocalBlowupFactorization (i : Fin n) {Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ D.neighborhoodSpace i) :=
  BlowupFactorization B S hS ({D.neighborhoodPoint i} : Set (points B S hS _)) g

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
