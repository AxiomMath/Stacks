module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The open-and-closed part cut out by an étale morphism which is closed over the base

Stacks 082H constructs its two pieces `W ⨿ V` of a base change `U ×_Y X` in two steps. First,
`V` is produced as the *image* of a scheme `Z₁` which is étale onto it and finite over `U`;
separatedness of `X ⟶ Y` makes that image both open and closed, and `W` is then defined as the
set-theoretic complement. This file carries out those two steps.

The openness is Tag 03IR, that an étale morphism of algebraic spaces is open on points, and the
closedness is part (1) of Tag 04NX, that a morphism whose composite to a further target is
universally closed has closed image as soon as the second morphism is separated. Both are
already available, so the content here is the combination and its consequence through
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenPointSetDecomposition.lean`: the image is a clopen
set of points, hence cuts out complementary open-and-closed subspaces.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_universallyClosed`: the image
  on points of an étale morphism whose composite to a separated target is universally closed is
  open and closed. These are steps 6 and 7 of the proof of Stacks 082H.
* `AlgebraicGeometry.Space.exists_clopen_subspace_decomposition_of_isEtale_of_universallyClosed`:
  that image therefore cuts the target into complementary open-and-closed subspaces.
* `AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_isFinite` and
  `AlgebraicGeometry.Space.exists_clopen_subspace_decomposition_of_isEtale_of_isFinite`: the
  same two statements with the universal closedness of the composite replaced by its
  *finiteness*, which is the form in which Stacks 082H has it.
* `AlgebraicGeometry.Space.exists_clopen_part_of_isClopen_pointSet`: the conclusion of
  Stacks 082H *except for its finiteness clause*, deduced from a clopen set of points together
  with the two conditions on the fibre stated for that set.

## Implementation notes

In the application to Stacks 082H the morphism `k` is the projection `U ×_Y X ⟶ U`, which is
separated because `X ⟶ Y` is and separatedness is stable under base change
(`AlgebraicGeometry.Space.isSeparated_pullbackSnd`), and `z ≫ k` is the morphism `Z₁ ⟶ U`,
which Stacks 082H has as *finite*. Both forms of the hypothesis are stated: universal
closedness is what part (1) of Tag 04NX consumes, and finiteness is what the source supplies;
they are related by `AlgebraicGeometry.Space.universallyClosed_of_isFinite` of
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyClosed.lean`, which carries out the
affine-local-to-global passage from the affine test objects of Stacks 03ZP to the arbitrary
base changes of Stacks 03HI.

The finiteness hypothesis of
`AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_isFinite` is **not** the
finiteness clause of the conclusion of Stacks 082H. It is finiteness of `z ≫ k`, which in the
application is `Z₁ ⟶ U`, the morphism produced by Tag 02LN in step 5; the clause of the
conclusion is finiteness of `V ⟶ U`, where `V` is the open-and-closed piece this file produces
as the image of `Z₁`. They are conditions on different morphisms, out of different objects, and
nothing here assumes any part of its own conclusion.

What is *not* here is the finiteness clause of Stacks 082H, that `V ⟶ U` is finite. The source
proves it by presenting `V` as the quotient of `Z₁` by the étale equivalence relation
`R = Z₁ ×_V Z₁` (Tag 0262, available as
`AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`), observing that `R` is closed in
`Z₁ ×_U Z₁` with finite projections, and then invoking Tag 03BM to see that `V` is an affine
*scheme*, Tag 03GN to see that `V ⟶ U` is proper and Tag 01WN to conclude that it is finite.
Tags 03BM, 03GN and 01WN are not in this development, which is why
`AlgebraicGeometry.Space.exists_clopen_part_of_isClopen_pointSet` stops short of that clause.

## References

* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The clopen image -/

/-- **The image of an étale morphism which is universally closed over a separated base is open
and closed.** Let `z : Z ⟶ P` be an étale morphism of algebraic spaces over `S` and let
`k : P ⟶ W` be separated with `z ≫ k` universally closed. Then the image of `|Z|` in `|P|` is
both open and closed.

Openness is Tag 03IR and closedness is part (1) of Tag 04NX. This is the pair of steps by which
Stacks 082H produces its open-and-closed piece `V` as the image of a scheme étale onto it and
finite over the base. -/
@[sga "3 X 9.7.3" "more general"]
theorem isClopen_range_pointsMap_of_isEtale_of_universallyClosed
    {Z P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W) (z : Z ⟶ P) (k : P ⟶ W)
    (hze : IsEtale B S hS z) (hzc : UniversallyClosed B S hS (z ≫ k))
    (hk : IsSeparated B S hS k) :
    _root_.IsClopen (Set.range (pointsMap B S hS Z z)) :=
  ⟨isClosed_range_of_comp_of_isSeparated B S hS hZ hP hW z k hzc hk,
    isOpen_range_pointsMap_of_isEtale B S hS z hZ hP hze⟩

/-- **An étale morphism which is universally closed over a separated base cuts its target into
complementary open-and-closed subspaces.** The two pieces are the ones cut out by the image of
the points and by its complement; their point sets are that image and its complement. -/
theorem exists_clopen_subspace_decomposition_of_isEtale_of_universallyClosed
    {Z P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W) (z : Z ⟶ P) (k : P ⟶ W)
    (hze : IsEtale B S hS z) (hzc : UniversallyClosed B S hS (z ≫ k))
    (hk : IsSeparated B S hS k) :
    ∃ W' V : Subfunctor P,
      IsOpenSubspace B S hS W' ∧ IsClosedSubspace B S hS W' ∧
      IsOpenSubspace B S hS V ∧ IsClosedSubspace B S hS V ∧
      (W' ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W' ⊓ V = (⊥ : Subfunctor P).sheafify (BigFppfOver.topology B S hS) ∧
      Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.range (pointsMap B S hS Z z) ∧
      Set.range (pointsMap B S hS W'.toFunctor W'.ι)
        = (Set.range (pointsMap B S hS Z z))ᶜ :=
  have h := isClopen_range_pointsMap_of_isEtale_of_universallyClosed B S hS hZ hP hW z k hze
    hzc hk
  exists_clopen_subspace_decomposition_of_isClopen B S hS hP _ h.2 h.1

/-! ### The clopen image from finiteness over the base -/

/-- **The image of an étale morphism which is finite over a separated base is open and
closed.** This is
`AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_universallyClosed` with the
hypothesis in the form Stacks 082H supplies it: there `z ≫ k` is the morphism `Z₁ ⟶ U` of
step 5, which Tag 02LN produces as a finite morphism.

The finiteness hypothesis is on `z ≫ k`, not on the open-and-closed piece cut out by the
conclusion; see the implementation notes of this file. -/
@[sga "3 X 9.7.3" "more general"]
theorem isClopen_range_pointsMap_of_isEtale_of_isFinite
    {Z P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W) (z : Z ⟶ P) (k : P ⟶ W)
    (hze : IsEtale B S hS z) (hzf : IsFinite B S hS (z ≫ k))
    (hk : IsSeparated B S hS k) :
    _root_.IsClopen (Set.range (pointsMap B S hS Z z)) :=
  isClopen_range_pointsMap_of_isEtale_of_universallyClosed B S hS hZ hP hW z k hze
    (universallyClosed_of_isFinite B S hS hZ hW hzf) hk

/-- **An étale morphism which is finite over a separated base cuts its target into
complementary open-and-closed subspaces.** This is
`AlgebraicGeometry.Space.exists_clopen_subspace_decomposition_of_isEtale_of_universallyClosed`
with the hypothesis in the form Stacks 082H supplies it. -/
theorem exists_clopen_subspace_decomposition_of_isEtale_of_isFinite
    {Z P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W) (z : Z ⟶ P) (k : P ⟶ W)
    (hze : IsEtale B S hS z) (hzf : IsFinite B S hS (z ≫ k))
    (hk : IsSeparated B S hS k) :
    ∃ W' V : Subfunctor P,
      IsOpenSubspace B S hS W' ∧ IsClosedSubspace B S hS W' ∧
      IsOpenSubspace B S hS V ∧ IsClosedSubspace B S hS V ∧
      (W' ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W' ⊓ V = (⊥ : Subfunctor P).sheafify (BigFppfOver.topology B S hS) ∧
      Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.range (pointsMap B S hS Z z) ∧
      Set.range (pointsMap B S hS W'.toFunctor W'.ι)
        = (Set.range (pointsMap B S hS Z z))ᶜ :=
  exists_clopen_subspace_decomposition_of_isEtale_of_universallyClosed B S hS hZ hP hW z k hze
    (universallyClosed_of_isFinite B S hS hZ hW hzf) hk

/-! ### The conclusion of Stacks 082H apart from its finiteness clause -/

/-- **The conclusion of Stacks 082H, apart from its finiteness clause, from a clopen set of
points.** Let `P` be an algebraic space over `S` equipped with two morphisms `k₁` and `k₂` — in
the application to Stacks 082H the two projections of `U ×_Y X` — let `u` be a point of the
target of `k₁` and let `x` be finitely many points of the target of `k₂`. A set `T` of points
of `P` which is open and closed, and over `u` accounts for exactly the points lying over the
`x i`, cuts `P` into two subfunctors which are open and closed subspaces, locally cover `P`,
are locally disjoint, and satisfy the two conditions on the fibre in the exact shape Stacks
082H states them.

The remaining clause of Stacks 082H is that `V ⟶ U` be finite; see the module documentation for
the three Stacks tags that clause needs and which this development does not have. The
hypotheses here are not that clause nor any part of this conclusion: `T` is a set of points,
and the conditions on it are conditions on points. -/
theorem exists_clopen_part_of_isClopen_pointSet
    {P Zu Zx : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (k₁ : P ⟶ Zu) (k₂ : P ⟶ Zx)
    (u : points B S hS Zu) {n : ℕ} (x : Fin n → points B S hS Zx)
    (T : Set (points B S hS P)) (hTo : _root_.IsOpen T) (hTc : _root_.IsClosed T)
    (hTV : ∀ t ∈ T, pointsMap B S hS P k₁ t = u → ∃ i, pointsMap B S hS P k₂ t = x i)
    (hTW : ∀ t ∉ T, pointsMap B S hS P k₁ t = u → ∀ i, pointsMap B S hS P k₂ t ≠ x i) :
    ∃ W V : Subfunctor P,
      IsOpenSubspace B S hS W ∧ IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧ IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor P).sheafify (BigFppfOver.topology B S hS) ∧
      Set.range (pointsMap B S hS V.toFunctor V.ι) = T ∧
      (∀ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ k₁) v = u →
          ∃ i, pointsMap B S hS V.toFunctor (V.ι ≫ k₂) v = x i) ∧
      (∀ w : points B S hS W.toFunctor,
        pointsMap B S hS W.toFunctor (W.ι ≫ k₁) w = u →
          ∀ i, pointsMap B S hS W.toFunctor (W.ι ≫ k₂) w ≠ x i) := by
  obtain ⟨W, V, h1, h2, h3, h4, h5, h6, hVpts, hWpts⟩ :=
    exists_clopen_subspace_decomposition_of_isClopen B S hS hP T hTo hTc
  refine ⟨W, V, h1, h2, h3, h4, h5, h6, hVpts, ?_, ?_⟩
  · intro v hv
    rw [pointsMap_comp_apply] at hv ⊢
    exact hTV _ (hVpts ▸ Set.mem_range_self v) hv
  · intro w hw i
    rw [pointsMap_comp_apply] at hw ⊢
    have hmem : pointsMap B S hS W.toFunctor W.ι w ∈ Tᶜ := hWpts ▸ Set.mem_range_self w
    exact hTW _ hmem hw i

end AlgebraicGeometry.Space

end
