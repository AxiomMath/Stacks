module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerGlobalStep
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerModification

/-!
# The global blowing up at a closed point realizing the blowing up of one neighborhood at its
distinguished point

Let `S` be a scheme, let `X` be a decent algebraic space over `S`, let `x₁, …, xₙ ∈ |X|` be the
chosen pairwise distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the chosen elementary
étale neighborhoods, that is a term `D : ClosedPointNeighborhoods B S hS n`.

The inductive step of the "if" direction of Stacks 0BHF peels the *bottom* blowing up off one of
the local sequences and asks for a global blowing up of `X` restricting to it.  The bottom
blowing up of a sequence over `uᵢ` is a blowing up of `Uᵢ` at `uᵢ` itself — the lower end of the
tower is identified with `Uᵢ`, so the first centre lies over `uᵢ` along an isomorphism and is
therefore `uᵢ` — and any two blowings up of `Uᵢ` at `uᵢ` are isomorphic over `Uᵢ`
(`AlgebraicGeometry.Space.IsBlowupAtClosedPoint.exists_iso_blowup`).  So the global step needed
at every stage of the induction is one and the same, and it exists unconditionally: this file
builds it.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_globalBlowup_restricting_at_point`:
  for each `i` there is a morphism `b : X₁ ⟶ X` which is a blowing up of `X` at a closed point
  lying over `xᵢ` — carried as a `AlgebraicGeometry.Space.BlowupFactorization` of length one
  over `{x₁, …, xₙ}`, so `X₁` is an object of the category `C_{X, {x₁, …, xₙ}}` of Stacks
  0BHA — whose base change to `Uᵢ` is the blowing up of `Uᵢ` at `uᵢ` and whose base change to
  every other `U_j` is an isomorphism.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isPullback_comp_of_isPullback`: the
  identification `Z' ×_X Uᵢ = (Z ×_X Uᵢ) ×_Z Z'`, which carries the cartesian-square hypothesis
  of the step theorem from one stage of the induction to the next.

## Implementation notes

The blowing up is produced by
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_isBlowupAtClosedPoint_restricting`
applied to the trivial cartesian square

```
Uᵢ --Uᵢ ⟶ X--> X
|𝟙             |𝟙
Uᵢ --Uᵢ ⟶ X--> X
```

exhibiting `Uᵢ` as `X ×_X Uᵢ`, at the closed point `uᵢ`.  That theorem carries
`[HasSheafify (BigFppfOver.topology B S hS) (Type u)]`, from the existence of the blowing up of
an algebraic space at a closed point in
`AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint_unconditional`; the binder is carried here
too.  It is unconditional on the ideal sheaf, not hypothesis-free.

The factorization of `b` as a sequence of length one is
`AlgebraicGeometry.Space.BlowupFactorization.ofBlowup`, which needs the centre to lie in
`{x₁, …, xₙ}`; the centre is the point `w` with `w = xᵢ` returned by the step theorem, the
structure morphism of the square being the identity.  That `X₁` is then an object of
`C_{X, {x₁, …, xₙ}}` is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isModification_of_blowupFactorization`.

Being an isomorphism over the other neighborhoods is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_of_ne_of_isBlowupAtClosedPoint` at the
same trivial square, which is where the shrinking condition of Stacks 0BH9 — no point of `U_j`
lies over `xᵢ` for `j ≠ i` — enters.

No `@[stacks]` attribute is attached: this is a component of the inductive step of Stacks 0BHF,
not the tag.

## References

* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The `i`th neighborhood is `X ×_X Uᵢ`: the square with the two identities on one diagonal is
cartesian. -/
theorem isPullback_toSpaceHom_id (i : Fin n) :
    IsPullback (D.toSpaceHom i) (𝟙 (D.neighborhoodSpace i)) (𝟙 D.space) (D.toSpaceHom i) :=
  IsPullback.of_vert_isIso ⟨by simp⟩

/-- **The fibre product over `X` with `Uᵢ` follows a step of the tower.**  If `P` is `Z ×_X Uᵢ`
and `P'` is `P ×_Z Z'` for a morphism `Z' ⟶ Z`, then `P'` is `Z' ×_X Uᵢ`: the two cartesian
squares paste.

This is what carries the hypothesis of
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupTower_step` from one stage of the
induction of Stacks 0BHF to the next. -/
theorem isPullback_comp_of_isPullback {Z Z' P P' : AlgebraicSpaces B S hS} {i : Fin n}
    {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {b : Z' ⟶ Z} {r : P' ⟶ P} {s : P' ⟶ Z'}
    (sqr : IsPullback r s p b) : IsPullback s (r ≫ q) (b ≫ g) (D.toSpaceHom i) :=
  (IsPullback.paste_horiz sqr sq.flip).flip

/-- **The global blowing up at a closed point over `xᵢ` restricting to the blowing up of `Uᵢ` at
`uᵢ`.**

For each `i` there is a morphism `b : X₁ ⟶ X` together with a factorization of it as a sequence
of blowings up at closed points lying over `{x₁, …, xₙ}` of length one — that is, `b` is a
blowing up of `X` at a closed point lying over `xᵢ` — such that `X₁` is an object of the
category `C_{X, {x₁, …, xₙ}}` of Stacks 0BHA, every base change of `b` along `Uᵢ ⟶ X` is the
blowing up of `Uᵢ` at `uᵢ`, and every base change of `b` along `U_j ⟶ X` with `j ≠ i` is an
isomorphism.

This is the global step of the induction in the "if" direction of Stacks 0BHF: the bottom
blowing up of a sequence of blowings up of `Uᵢ` at closed points over `uᵢ` is a blowing up of
`Uᵢ` at `uᵢ`, and any two of those are isomorphic over `Uᵢ`, so this one step serves at every
stage. -/
theorem exists_globalBlowup_restricting_at_point
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (i : Fin n) :
    ∃ (X₁ : AlgebraicSpaces B S hS) (b : X₁ ⟶ D.space) (G : D.GlobalBlowupFactorization b),
      G.length = 1 ∧ IsModification B S hS D.openAwayFromPoints (Over.mk b.hom) ∧
        (∀ {P : AlgebraicSpaces B S hS} {r : P ⟶ D.neighborhoodSpace i} {s : P ⟶ X₁},
          IsPullback r s (D.toSpaceHom i) b →
            IsBlowupAtClosedPoint B S hS (D.neighborhoodPoint i)
              (D.isClosed_neighborhoodPoint i) r) ∧
        ∀ j : Fin n, j ≠ i → ∀ {P : AlgebraicSpaces B S hS} {r : P ⟶ D.neighborhoodSpace j}
          {s : P ⟶ X₁}, IsPullback r s (D.toSpaceHom j) b → IsIso r := by
  obtain ⟨w, hw, X₁, b, hgw, hb, hrest⟩ :=
    D.exists_isBlowupAtClosedPoint_restricting (D.isPullback_toSpaceHom_id i)
      (D.isClosed_neighborhoodPoint i) (by simp)
  have hwT : w ∈ Set.range D.point := ⟨i, by simpa using hgw.symm⟩
  refine ⟨X₁, b, BlowupFactorization.ofBlowup _ hb hwT, rfl,
    D.isModification_of_blowupFactorization (BlowupFactorization.ofBlowup _ hb hwT), hrest, ?_⟩
  intro j hji P r s sqr
  exact D.isIso_of_ne_of_isBlowupAtClosedPoint hji (D.isPullback_toSpaceHom_id j) hgw hb sqr

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
