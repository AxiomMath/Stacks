module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLengthBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Trace maps for a flat quasi-finite morphism

Let `f : X ⟶ Y` be a morphism of schemes which is flat, locally quasi-finite and locally of
finite presentation. Stacks Example `0GKI` asserts three things about this situation, and this
file states all three.

First, `f` carries a canonical positive weighting `w : X → ℤ`, namely

`w(x) = length_{𝒪_{X, x}} (𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}) * [κ(x) : κ(f(x))]_i`,

the second factor being the inseparable degree of the residue field extension. This is Stacks
tag `0F3D`: the function is `AlgebraicGeometry.flatQuasiFiniteWeight`, its positivity is
`AlgebraicGeometry.flatQuasiFiniteWeight_pos` and the weighting property is
`AlgebraicGeometry.flatQuasiFiniteWeight_isWeighting`, and the example adopts those three rather
than restating them.

Second, applying Stacks `0GKG` and `0GKH` to `f` and that weighting yields trace maps

`Tr_{f, K} : f_! f^{-1} K ⟶ K`

for `K` an object of `D(Y_étale, Λ)`, functorial in `K` and compatible with arbitrary base
change. The family of them is `AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace`, a natural
transformation of functors on the derived category, so functoriality in `K` is its naturality;
`AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace_naturality` states it.

Third, any base change `f' : X' ⟶ Y'` of `f` satisfies the same three hypotheses and `w`
restricts to the canonical weighting of `f'`. The three stability statements are recorded on
the tag in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.WeightingBaseChange`, and the restriction claim
is `AlgebraicGeometry.flatQuasiFiniteWeight_of_isPullback`. It is what makes the base-change
square of this file an assertion about the trace maps of the example on both sides:
`AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace_baseChange` compares the trace of `f` with
the trace attached to the *canonical weighting of `f'`*, not merely with the trace attached to
the restricted weight that Stacks `0GKH` part (2) delivers.

## Main definitions

* `AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace` — the family `Tr_{f, K}` of trace maps for
  the canonical weighting, as a natural transformation
  `f^{-1} ⋙ f_! ⟶ 𝟭` of endofunctors of `D(Y_étale, Λ)`.

## Main results

* `AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace_naturality` — functoriality in `K`.
* `AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace_baseChange` — compatibility with an
  arbitrary base change, stated with the canonical weighting of the base change on the other
  side.
* `AlgebraicGeometry.SmallEtale.weightedTraceModTrans_congr_weight` — the trace depends on the
  weighting only through the underlying function, which is what lets the previous statement be
  phrased with the canonical weighting of `f'`.

## Implementation notes

Nothing is redefined. The weighting is the one of tag `0F3D`, the trace is
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` of tag `0GKH` part (3) at that weighting,
and the base-change square is the corresponding clause of
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_spec` with the weighting of `f'`
rewritten.

`AlgebraicGeometry.SmallEtale.IsWeighting` is a `Prop`, so two proofs that one function is a
weighting of `f` are definitionally equal and the trace built from either is the same; the only
real content of `weightedTraceModTrans_congr_weight` is the substitution of one weighting
*function* for another, which is why it is stated with an equation between functions rather than
proved by `congr`.

The coefficient universes are the ones fixed upstream: the base-change comparison of tag `0F5J`
is carried at `AddCommGrpCat.{u + 1}`, so the `Λ`-module statements of tag `0GKH` parts (2) and
(3) live at `ModuleSheaf.{u, u + 1, u}` with `Λ : Type u`, and this file inherits that. The
hypothesis `LocallyOfFiniteType` is never written: Mathlib derives it from
`LocallyOfFinitePresentation`, so the hypothesis set here is exactly the example's.

## References

* [Stacks Project, Tag 0GKI](https://stacks.math.columbia.edu/tag/0GKI)
* [Stacks Project, Tag 0F3D](https://stacks.math.columbia.edu/tag/0F3D)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallEtale

universe u v t r

attribute [local instance] additive_abPullback

/-! ### The canonical weighting of the example

The example's first assertion is tag `0F3D` verbatim: the function given by the displayed
formula, its positivity, and the fact that it is a weighting. Those three declarations are
adopted rather than copied. -/

add_to_stacks 0GKI "the canonical positive weighting `w` of the example, given by the displayed \
formula -- the function itself" AlgebraicGeometry.flatQuasiFiniteWeight

add_to_stacks 0GKI "the canonical positive weighting `w` of the example -- positivity"
  AlgebraicGeometry.flatQuasiFiniteWeight_pos

add_to_stacks 0GKI "the canonical positive weighting `w` of the example -- that it is a \
weighting of `f`, which the example cites More on Morphisms, Lemma 0F3D for"
  AlgebraicGeometry.flatQuasiFiniteWeight_isWeighting

/-! ### The trace depends on the weighting only through its underlying function -/

section Congr

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The family of trace maps attached to a weighting depends on the weighting only through the
underlying function `X → ℤ`: equal functions give equal families, for any proofs that each is a
weighting. -/
theorem weightedTraceModTrans_congr_weight {w w' : X.obj → ℤ} (hww : w = w')
    (hw : IsWeighting (B.inclusion.map f) w) (hw' : IsWeighting (B.inclusion.map f) w') :
    weightedTraceModTrans.{u, v, r} B Λ f hw = weightedTraceModTrans.{u, v, r} B Λ f hw' := by
  subst hww
  rfl

end Congr

/-! ### The trace maps of the example -/

section Trace

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
  [Flat (B.inclusion.map f)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y Λ)]

/-- **Stacks Project, Example 0GKI: the trace maps of a flat quasi-finite morphism.** For
`f : X ⟶ Y` flat, locally quasi-finite and locally of finite presentation, and a ring `Λ`, the
family of trace maps

`Tr_{f, K} : f_! f^{-1} K ⟶ K`,  `K ∈ D(Y_étale, Λ)`,

obtained by applying Stacks `0GKG` and `0GKH` to `f` and the canonical weighting of Stacks
`0F3D`. It is a natural transformation of endofunctors of `D(Y_étale, Λ)`, so the example's
"functorial for `K`" is built into the datum; it is stated separately as
`AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace_naturality`. -/
@[stacks 0GKI "the trace maps `Tr_{f, K} : f_! f^{-1} K ⟶ K` for `K` in `D(Y_étale, Λ)`, \
obtained -- as the example says -- by applying Lemmas 0GKG and 0GKH to `f` and the canonical \
weighting of 0F3D, which is `AlgebraicGeometry.flatQuasiFiniteWeight`. The example asserts no \
property of these maps beyond the two in the next two declarations, functoriality in `K` and \
compatibility with arbitrary base change.", sga "4½ Cycle 2.3.1" "special case"]
def flatQuasiFiniteTrace :
    (pullbackMod.{u, u + 1, u} B Λ f).mapDerivedCategory ⋙
        (fShriekMod.{u, u + 1, u} B Λ f).mapDerivedCategory ⟶
      𝟭 (DerivedCategory (ModuleSheaf.{u, u + 1, u} B Y Λ)) :=
  derivedWeightedTraceMod.{u, u + 1, t, u} B Λ f
    (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f))

/-- **Stacks Project, Example 0GKI: the trace maps are functorial in `K`.** -/
@[stacks 0GKI "the example's `functorial for K in D(Y_étale, Λ)`, for the trace maps attached to \
the canonical weighting"]
theorem flatQuasiFiniteTrace_naturality
    {K K' : DerivedCategory (ModuleSheaf.{u, u + 1, u} B Y Λ)} (ψ : K ⟶ K') :
    ((pullbackMod.{u, u + 1, u} B Λ f).mapDerivedCategory ⋙
          (fShriekMod.{u, u + 1, u} B Λ f).mapDerivedCategory).map ψ ≫
        (flatQuasiFiniteTrace.{u, t} B Λ f).app K' =
      (flatQuasiFiniteTrace.{u, t} B Λ f).app K ≫ ψ :=
  (flatQuasiFiniteTrace.{u, t} B Λ f).naturality ψ

end Trace

/-! ### Compatibility of the trace maps with an arbitrary base change -/

section BaseChange

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
  [Flat (B.inclusion.map f)]
  (sq : IsPullback p f' f g)
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y Λ)]
  [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y' Λ)]

include sq in
/-- **Stacks Project, Example 0GKI: the trace maps are compatible with arbitrary base change.**
Let

```
X' --p--> X
|f'       |f
Y' --g--> Y
```

be cartesian. Then `f'` is again flat, locally quasi-finite and locally of finite presentation,
so it has its own canonical weighting, and the square formed by the base-change comparison
`g^{-1} f_! ≅ f'_! p^{-1}` of Stacks `0F5J`, the comparison of the two iterated inverse images,
and the two trace maps of the example commutes.

The statement is the base-change clause of
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_spec` with the weighting on the `f'` side
replaced by the canonical weighting of `f'`. That replacement is exactly the example's closing
remark that `w` restricts to the canonical weighting of `f'`, which is
`AlgebraicGeometry.flatQuasiFiniteWeight_of_isPullback`. -/
@[stacks 0GKI "the example's `compatible with arbitrary base change`, for the trace maps \
attached to the canonical weighting. Both sides are traces of the example: the `f'` side is the \
trace attached to the canonical weighting of `f'` itself, not to the restricted weight that \
0GKH part (2) delivers, the two being identified by \
`AlgebraicGeometry.flatQuasiFiniteWeight_of_isPullback` -- the example's closing claim that `w` \
restricts to the canonical weighting of `f'`",
  sga "4 XVII 6.2.3" "more general",
  sga "4 XVII 6.2.5" "special case"]
theorem flatQuasiFiniteTrace_baseChange :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    letI : Flat (B.inclusion.map f') :=
      MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
    letI : LocallyOfFinitePresentation (B.inclusion.map f') :=
      MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
    NatTrans.mapDerivedCategory
          (traceBaseChangeComparison.{u, u + 1, u} B Λ f' f (pullbackMod.{u, u + 1, u} B Λ f)
            (pullbackMod.{u, u + 1, u} B Λ f') (pullbackMod.{u, u + 1, u} B Λ g)
            (pullbackMod.{u, u + 1, u} B Λ p) (fShriekBaseChangeMod.{u} B Λ p f' f g sq)
            (inverseImageSquareMod.{u} B Λ p f' f g sq)).hom ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (pullbackMod.{u, u + 1, u} B Λ g)
          (pullbackMod.{u, u + 1, u} B Λ f' ⋙ fShriekMod.{u, u + 1, u} B Λ f')).hom ≫
        Functor.whiskerLeft (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory
          (NatTrans.mapDerivedCategory
            (weightedTraceModTrans.{u, u + 1, u} B Λ f'
              (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f')))) ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (pullbackMod.{u, u + 1, u} B Λ g)
          (𝟭 (ModuleSheaf.{u, u + 1, u} B Y' Λ))).inv =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (pullbackMod.{u, u + 1, u} B Λ f ⋙ fShriekMod.{u, u + 1, u} B Λ f)
          (pullbackMod.{u, u + 1, u} B Λ g)).hom ≫
        Functor.whiskerRight
          (NatTrans.mapDerivedCategory (weightedTraceModTrans.{u, u + 1, u} B Λ f
            (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f))))
          (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (𝟭 (ModuleSheaf.{u, u + 1, u} B Y Λ))
          (pullbackMod.{u, u + 1, u} B Λ g)).inv := by
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  let : Flat (B.inclusion.map f') :=
    MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
  let : LocallyOfFinitePresentation (B.inclusion.map f') :=
    MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
  rw [weightedTraceModTrans_congr_weight.{u, u + 1, u} B Λ f'
    (flatQuasiFiniteWeight_of_isPullback (B.inclusion.map f) (sq.map B.inclusion))
    (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f'))
    (IsWeighting.comp_of_isPullback (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f))
      (sq.map B.inclusion))]
  exact (derivedWeightedTraceMod_spec.{u, t} B Λ p f' f g sq
    (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f))).2.2.2.2.2.1

/-! ### The example in full, as one conjunction -/

/-- **Stacks Project, Example 0GKI, in full.** For `f : X ⟶ Y` flat, locally quasi-finite and
locally of finite presentation, a ring `Λ`, and an arbitrary cartesian square

```
X' --p--> X
|f'       |f
Y' --g--> Y
```

the six conjuncts are, in the example's own order:

1. the function `w = flatQuasiFiniteWeight f` of the displayed formula is strictly positive, and
2. is a weighting of `f` — together, the example's "canonical positive weighting";
3. the family `flatQuasiFiniteTrace` of trace maps `Tr_{f, K} : f_! f^{-1} K ⟶ K` is functorial
   for `K` in `D(Y_étale, Λ)`, and
4. compatible with the base change, which being arbitrary gives "compatible with arbitrary base
   change";
5. `f'` is again flat, locally quasi-finite and locally of finite presentation; and
6. `w` restricts along `p` to the canonical weighting of `f'`.

The trace maps themselves are data, so they enter the conjunction by name rather than as an
existential: every property the example asserts of them is asserted here of
`AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace`.

Neither side of conjunct 4 can be written down without the four instances of `f'`, so the
statement binds them in a `letI` block; each is the proof conjunct 5 asserts, so nothing beyond
the example's hypotheses is assumed, and the elaborated statement carries no binder for them. -/
@[stacks 0GKI "the example in full, as one conjunction in its own order: (1) positivity and (2) \
the weighting property of the function `w` of the displayed formula, which is the example's \
`canonical positive weighting`; (3) functoriality in `K` and (4) compatibility with the \
arbitrary base change, for the family `Tr_{f, K} : f_! f^{-1} K ⟶ K` of \
`AlgebraicGeometry.SmallEtale.flatQuasiFiniteTrace`; (5) that the base change `f'` is again \
flat, locally quasi-finite and locally of finite presentation; and (6) that `w` restricts along \
`p` to the canonical weighting of `f'`. The trace maps themselves are data, so they enter by \
name: the conjunction asserts every property the example asserts of them.",
  sga "4 XVII 6.2.3" "more general",
  sga "4 XVII 6.2.5" "special case"]
theorem flatQuasiFiniteWeight_and_flatQuasiFiniteTrace_allClauses :
    -- the canonical positive weighting `w` of the example
    (∀ x, 0 < flatQuasiFiniteWeight (B.inclusion.map f) x) ∧
    IsWeighting (B.inclusion.map f) (flatQuasiFiniteWeight (B.inclusion.map f)) ∧
    -- the trace maps are functorial for `K` in `D(Y_étale, Λ)`
    (∀ (K K' : DerivedCategory (ModuleSheaf.{u, u + 1, u} B Y Λ)) (ψ : K ⟶ K'),
        ((pullbackMod.{u, u + 1, u} B Λ f).mapDerivedCategory ⋙
              (fShriekMod.{u, u + 1, u} B Λ f).mapDerivedCategory).map ψ ≫
            (flatQuasiFiniteTrace.{u, t} B Λ f).app K' =
          (flatQuasiFiniteTrace.{u, t} B Λ f).app K ≫ ψ) ∧
    -- and compatible with the arbitrary base change
    (letI := locallyOfFiniteType_of_isPullback B p f' f g sq
     letI := locallyQuasiFinite_of_isPullback B p f' f g sq
     letI : Flat (B.inclusion.map f') :=
       MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
     letI : LocallyOfFinitePresentation (B.inclusion.map f') :=
       MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
     NatTrans.mapDerivedCategory
           (traceBaseChangeComparison.{u, u + 1, u} B Λ f' f (pullbackMod.{u, u + 1, u} B Λ f)
             (pullbackMod.{u, u + 1, u} B Λ f') (pullbackMod.{u, u + 1, u} B Λ g)
             (pullbackMod.{u, u + 1, u} B Λ p) (fShriekBaseChangeMod.{u} B Λ p f' f g sq)
             (inverseImageSquareMod.{u} B Λ p f' f g sq)).hom ≫
         (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
           (pullbackMod.{u, u + 1, u} B Λ g)
           (pullbackMod.{u, u + 1, u} B Λ f' ⋙ fShriekMod.{u, u + 1, u} B Λ f')).hom ≫
         Functor.whiskerLeft (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory
           (NatTrans.mapDerivedCategory
             (weightedTraceModTrans.{u, u + 1, u} B Λ f'
               (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f')))) ≫
         (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
           (pullbackMod.{u, u + 1, u} B Λ g)
           (𝟭 (ModuleSheaf.{u, u + 1, u} B Y' Λ))).inv =
       (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
           (pullbackMod.{u, u + 1, u} B Λ f ⋙ fShriekMod.{u, u + 1, u} B Λ f)
           (pullbackMod.{u, u + 1, u} B Λ g)).hom ≫
         Functor.whiskerRight
           (NatTrans.mapDerivedCategory (weightedTraceModTrans.{u, u + 1, u} B Λ f
             (flatQuasiFiniteWeight_isWeighting (B.inclusion.map f))))
           (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory ≫
         (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
           (𝟭 (ModuleSheaf.{u, u + 1, u} B Y Λ))
           (pullbackMod.{u, u + 1, u} B Λ g)).inv) ∧
    -- any base change of `f` satisfies the same three properties
    (Flat (B.inclusion.map f') ∧ LocallyQuasiFinite (B.inclusion.map f') ∧
      LocallyOfFinitePresentation (B.inclusion.map f')) ∧
    -- and `w` restricts to the canonical weighting of `f'`
    flatQuasiFiniteWeight (B.inclusion.map f') =
      flatQuasiFiniteWeight (B.inclusion.map f) ∘ (B.inclusion.map p) :=
  ⟨flatQuasiFiniteWeight_pos (B.inclusion.map f),
    flatQuasiFiniteWeight_isWeighting (B.inclusion.map f),
    fun _ _ ψ => flatQuasiFiniteTrace_naturality.{u, t} B Λ f ψ,
    flatQuasiFiniteTrace_baseChange.{u, t} B Λ p f' f g sq,
    ⟨MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance,
      locallyQuasiFinite_of_isPullback B p f' f g sq,
      MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance⟩,
    flatQuasiFiniteWeight_of_isPullback (B.inclusion.map f) (sq.map B.inclusion)⟩

end BaseChange

end AlgebraicGeometry.SmallEtale

end
