module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMapBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of a family of cycles on fibres, and flat descent of relative cycles

Let `f : X ⟶ S` be locally of finite type, let `r, e ≥ 0` and let `j : U ⟶ X` be flat, locally of
finite type and of relative dimension `e`, viewed as a morphism of schemes over `S` through an
identity `j ≫ f = f_U`. On each fibre `j` induces a morphism `U_s ⟶ X_s` which is again flat,
locally of finite type and of relative dimension `e`, so flat pullback of cycles along it is a
homomorphism `Z_r(X_s) ⟶ Z_{r+e}(U_s)`, and a family `α` of `r`-cycles on the fibres of `X/S`
pulls back to a family `j^*α` of `(r+e)`-cycles on the fibres of `U/S`. That construction is the
flat pullback of Section 0H4N, and it is built here.

The file also builds `Stacks.Chow.baseChangedFiberCycleFlatPullback`, the flat pullback along the
base change of `j` to a scheme over `S`, which is the shape in which the valuative condition of
Definition 0H50 compares the two members of a flat pullback of a family of cycles on fibres.
Lemma 0H53, the flat descent statement built from it, is in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackDescent`.

## Main definitions

* `Stacks.Chow.fiberCycleFlatPullback` — flat pullback of fibrewise cycles along a flat morphism
  of the source over a fixed base, `Z_r(X_s) ⟶ Z_{r+e}(U_s)`.
* `Stacks.Chow.flatPullbackFamily` — **Section 0H4N**: the flat pullback `j^*α` of a family of
  `r`-cycles on fibres along a flat morphism of relative dimension `e`.
* `Stacks.Chow.baseChangedFiberCycleFlatPullback` — flat pullback of fibrewise cycles along the
  base change of `j` to a scheme over `S`.

## Main results

* `Stacks.Chow.isPullback_pullbackRestrict` — the base change along `g : T ⟶ S` of a morphism
  `j : U ⟶ X` of schemes over `S` is the base change of `j` along `X ×_S T ⟶ X`, as a cartesian
  square; hence flatness, local finite type and relative dimension are inherited by it and by
  the induced morphism of scheme-theoretic fibres.
* `Stacks.Chow.fiberCycleFlatPullback_apply` — the coefficient formula.

## Implementation notes

The structure morphism of the source of a flat morphism `j : U ⟶ X` over `S` is given as a
morphism `f_U : U ⟶ S` together with the identity `j ≫ f = f_U`, rather than as the composite
itself, so that the construction applies to the base changes of `j`, whose structure morphism is
the chosen projection `U ×_S T ⟶ T` and not literally a composite.

## References

* [Stacks Project, Lemma 0H53](https://stacks.math.columbia.edu/tag/0H53)
* [Stacks Project, Lemma 0H5F](https://stacks.math.columbia.edu/tag/0H5F)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Lemma 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
* [Stacks Project, Lemma 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The base change of a morphism of schemes over a fixed base -/

/-- **Stacks Project, Tag 02NK.** The base change along `g : T ⟶ S` of a morphism `j : U ⟶ X` of
schemes over `S` is the base change of `j` along the projection `X ×_S T ⟶ X`, exhibited as a
cartesian square. Pasting the cartesian square for `U ×_S T` onto the one for `X ×_S T` gives
the claim. -/
theorem isPullback_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    (h : j ≫ f = fU) (g : T ⟶ S) :
    IsPullback (pullback.fst fU g) (pullbackRestrict f fU j h g) j (pullback.fst f g) := by
  refine (IsPullback.of_right ?_ (pullbackRestrict_fst f fU j h g)
    (IsPullback.of_hasPullback f g).flip).flip
  rw [pullbackRestrict_snd, h]
  exact (IsPullback.of_hasPullback fU g).flip

/-- The base change of a morphism locally of finite type of schemes over a fixed base is locally
of finite type. -/
instance locallyOfFiniteType_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) [LocallyOfFiniteType j] (h : j ≫ f = fU) (g : T ⟶ S) :
    LocallyOfFiniteType (pullbackRestrict f fU j h g) :=
  MorphismProperty.of_isPullback (isPullback_pullbackRestrict f fU j h g) inferInstance

/-- The base change of a flat morphism of schemes over a fixed base is flat. -/
instance flat_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    [Flat j] (h : j ≫ f = fU) (g : T ⟶ S) : Flat (pullbackRestrict f fU j h g) :=
  MorphismProperty.of_isPullback (isPullback_pullbackRestrict f fU j h g) inferInstance

/-- **Stacks Project, Tag 02NK.** The base change of a morphism of relative dimension `e` of
schemes over a fixed base has relative dimension `e`. -/
theorem relativeDimension_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) [LocallyOfFiniteType j] (h : j ≫ f = fU) (g : T ⟶ S) {e : ℕ}
    (he : AlgebraicGeometry.RelativeDimension j e) :
    AlgebraicGeometry.RelativeDimension (pullbackRestrict f fU j h g) e :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_pullbackRestrict f fU j h g) he

/-- The morphism of scheme-theoretic fibres induced by a morphism locally of finite type of
schemes over the base is locally of finite type. -/
instance locallyOfFiniteType_fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) [LocallyOfFiniteType j] (h : j ≫ f = fU) (s : S) :
    LocallyOfFiniteType (fiberRestrict f fU j h s) :=
  locallyOfFiniteType_pullbackRestrict f fU j h (S.fromSpecResidueField s)

/-- The morphism of scheme-theoretic fibres induced by a flat morphism of schemes over the base
is flat. -/
instance flat_fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X) [Flat j]
    (h : j ≫ f = fU) (s : S) : Flat (fiberRestrict f fU j h s) :=
  flat_pullbackRestrict f fU j h (S.fromSpecResidueField s)

/-- **Stacks Project, Tag 02NK.** The morphism of scheme-theoretic fibres induced by a morphism
of relative dimension `e` of schemes over the base has relative dimension `e`. -/
theorem relativeDimension_fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) [LocallyOfFiniteType j] (h : j ≫ f = fU) (s : S) {e : ℕ}
    (he : AlgebraicGeometry.RelativeDimension j e) :
    AlgebraicGeometry.RelativeDimension (fiberRestrict f fU j h s) e :=
  relativeDimension_pullbackRestrict f fU j h (S.fromSpecResidueField s) he

/-! ### Flat pullback of a fibrewise cycle -/

/-- **Stacks Project, Tag 02RB on a fibre.** Flat pullback of fibrewise `r`-cycles along a flat
morphism `j : U ⟶ X` of schemes over `S`, locally of finite type and of relative dimension `e`:
the homomorphism `Z_r(X_s) ⟶ Z_{r+e}(U_s)` given by flat pullback along the induced morphism of
scheme-theoretic fibres `U_s ⟶ X_s`. -/
def fiberCycleFlatPullback {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j]
    (h : j ≫ f = fU) (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (s : S) (r : ℕ) :
    FiberCycleGroup f s r →+ FiberCycleGroup fU s (r + e) :=
  flatPullback (fieldChowSituation (S.residueField s)) (fU.fiberToSpecResidueField s)
    (f.fiberToSpecResidueField s) (fiberRestrict f fU j h s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) e
    (relativeDimension_fiberRestrict f fU j h s he) (r : ℤ)

/-- **Stacks Project, Tag 02RB on a fibre.** The coefficient of a flat pullback of a fibrewise
cycle at a point of `U_s`: the coefficient at the image point in `X_s`, times the multiplicity
with which the point enters the scheme-theoretic inverse image of the reduced closure of that
image. -/
@[simp]
theorem fiberCycleFlatPullback_apply {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j]
    (h : j ≫ f = fU) (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (s : S) (r : ℕ)
    (c : FiberCycleGroup f s r) (y : fU.fiber s) :
    (fiberCycleFlatPullback f fU j h e he s r c : AlgebraicCycle (fU.fiber s) ℤ) y =
      (c : AlgebraicCycle (f.fiber s) ℤ) (fiberRestrict f fU j h s y) *
        flatPullbackWeight (fieldChowSituation (S.residueField s))
          (fU.fiberToSpecResidueField s) (fiberRestrict f fU j h s) ((r : ℤ) + (e : ℤ)) y :=
  rfl

/-! ### Flat pullback of a family of cycles on fibres -/

/-- **Stacks Project, Section 0H4N.** The flat pullback `j^*α` of a family `α` of `r`-cycles on
the fibres of `X/S` along a flat morphism `j : U ⟶ X` of schemes over `S`, locally of finite type
and of relative dimension `e`: the family of `(r+e)`-cycles on the fibres of `U/S` whose member
over `s` is the flat pullback of `α_s` along `U_s ⟶ X_s`. -/
@[stacks 0H4N "flat pullback of a family of cycles on fibres"]
def flatPullbackFamily {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ S)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU)
    (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (r : ℕ) (α : FamilyOfCycles f r) :
    FamilyOfCycles fU (r + e) :=
  fun s => fiberCycleFlatPullback f fU j h e he s r (α s)

/-- The members of a flat pullback of a family of cycles on fibres. -/
@[simp]
theorem flatPullbackFamily_apply {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [LocallyOfFiniteType j] [Flat j]
    (h : j ≫ f = fU) (e : ℕ) (he : AlgebraicGeometry.RelativeDimension j e) (r : ℕ)
    (α : FamilyOfCycles f r) (s : S) :
    flatPullbackFamily f fU j h e he r α s = fiberCycleFlatPullback f fU j h e he s r (α s) :=
  rfl

/-! ### Flat pullback along the base change of the flat morphism -/

/-- The flat pullback, along the base change of `j : U ⟶ X` to `T`, of fibrewise cycles on the
fibres of `X ×_S T ⟶ T`. This is the homomorphism called `f_{i,t}^*` in the proof of
Lemma 0H53. -/
def baseChangedFiberCycleFlatPullback {X S U T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) (g : T ⟶ S) (t : T) (r : ℕ) :
    FiberCycleGroup (pullback.snd f g) t r →+ FiberCycleGroup (pullback.snd fU g) t (r + e) :=
  fiberCycleFlatPullback (pullback.snd f g) (pullback.snd fU g)
    (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) e
    (relativeDimension_pullbackRestrict f fU j h g he) t r

end Stacks.Chow

end
