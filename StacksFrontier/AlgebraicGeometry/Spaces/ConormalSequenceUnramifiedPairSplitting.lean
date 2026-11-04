module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalThickeningLocalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings

/-!
# An étale-local retraction of the first arrow of the conormal sequence

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be formally unramified morphisms of algebraic spaces over a
scheme `S` sitting in a commutative triangle `i ≫ g = j` with `g : X ⟶ Y` formally smooth, let
`Z ⊂ Z'` be a universal first-order thickening of `Z` over `X` and `Z ⊂ Z''` one of `Z` over
`Y`, and let `k : Z' ⟶ Z''` be the canonical morphism between them.  The first arrow of the
conormal sequence of Stacks 06BE is the map `𝒞_{Z/Z''} ⟶ 𝒞_{Z/Z'}` of Stacks 060A attached to
`k`, which is the conormal map of Stacks 04CP for the square of closed subspaces `k` is, and is
named that way throughout this file.  This file proves that the first arrow becomes split
injective after inverse image along the chart of `Z` cut out by an affine étale chart
`V ⟶ Z''`, and on a covering family of such charts of an arbitrary étale chart of `Z''`.

## Main definitions

* `AlgebraicGeometry.Space.thickeningChartSubspace`: the chart `Z ×_{Z''} V` of `Z` cut out by
  an étale chart `V ⟶ Z''`, a closed subspace of `V`.
* `AlgebraicGeometry.Space.thickeningChartProjection`: its projection to the smaller space of
  `Z ⊂ Z'`, read through the two identifications of the smaller spaces with `Z`.

## Main results

* `AlgebraicGeometry.Space.universalThickeningComparison_square`: the canonical morphism
  `Z' ⟶ Z''` and the identification of the two smaller spaces form a commutative square of
  closed subspaces.
* `AlgebraicGeometry.Space.universalThickeningConormalMap_eq_conormalMap`: the map of
  Stacks 060A is that conormal map, for a consumer that wants the other spelling.
* `AlgebraicGeometry.Space.exists_retraction_modulePullback_conormalMap_universalThickening`: on
  the chart `Z ×_{Z''} V` of an affine étale chart `V ⟶ Z''` the first arrow of the conormal
  sequence admits a retraction.
* `AlgebraicGeometry.Space.exists_retraction_cover_modulePullback_conormalMap_universalThickening`:
  every étale chart of `Z''` is covered by affine étale charts over which that happens.
* `AlgebraicGeometry.Space.mono_conormalMap_universalThickening`: the first arrow of the
  conormal sequence is a monomorphism, so the sequence is exact on the left.

## Implementation notes

The argument is the last paragraph of Stacks 06BK.  Over an affine étale chart `V ⟶ Z''` the
canonical morphism `k` has a section `s : V ⟶ Z'` restricting to the inclusion `Z ⟶ Z'` on
`P = Z ×_{Z''} V`, by
`AlgebraicGeometry.Space.exists_local_section_of_formallySmooth`.  Two conormal maps of
Stacks 04CP are attached to it: the map `α` of the canonical square `(P ⊂ V) ⟶ (Z ⊂ Z'')` of
the inverse image of a closed subspace, and the map `β` of the square `(P ⊂ V) ⟶ (Z ⊂ Z')`
over `s`, whose commutativity is the first clause satisfied by the section.  The first is an
isomorphism by the flat clause of Stacks 04CQ,
`AlgebraicGeometry.Space.isIso_conormalMap_of_isFlat`, an étale morphism being flat.  Since
`s ≫ k` is the chart itself, the canonical square is the square of `β` stacked under the square
of the first arrow, so the composition law of Stacks 04G2 in the form
`AlgebraicGeometry.Space.isIso_conormalMap_comp_iff` makes the inverse image
along the projection `P ⟶ Z` of the first arrow followed by `β` an isomorphism.  Hence that
inverse image of the first arrow is a factor of an isomorphism and so admits a retraction.

**Why the first arrow is named through its definition.**  The map of Stacks 060A,
`AlgebraicGeometry.Space.universalThickeningConormalMap`, is *by definition* the conormal map of
Stacks 04CP for the square of Stacks 060A, and the two spellings are interchangeable to the
elaborator.  They are not interchangeable to the kernel.  The type of the Stacks 060A map is
anchored at the subfunctor spelling `⟨Z.toFunctor, _⟩` of the smaller space, while the type of
every `AlgebraicGeometry.Space.conormalMap` is anchored at `⟨Z.1.toFunctor, Z.2.1⟩` for a closed
subspace `Z`, and no choice of argument makes those syntactically equal — it would need
`Z.1` to *be* the subfunctor.  Under an inverse image of modules the two anchorings give two
spellings of the category of modules on the smaller space, and the kernel, for which
`irreducible` is not binding, decides that by unfolding the inverse image to its construction by
sheafification and does not terminate.  So the statements here are written on the
`conormalMap` side throughout, which is the side the composition law of Stacks 04G2 and the flat
clause of Stacks 04CQ are stated on; no identification is then needed anywhere.
`AlgebraicGeometry.Space.universalThickeningConormalMap_eq_conormalMap` records the
identification for a consumer that wants the other spelling, and is cheap because it compares
the two morphisms alone rather than their images under a functor.

**Why the ambient spaces are explicit arguments below.**  The private lemmas take the ambient
algebraic spaces explicitly rather than inferring them from the closed subspaces.  Inferring
them means solving `?X.1 =?= F` for a metavariable `?X`, a projection applied to a
metavariable, which the unifier cannot do; it falls back on unfolding `ClosedSubspaces` to
`Subfunctor` and comparing the underlying `Set`s pointwise, which does not terminate.

## References

* [Stacks Project, Tag 06BK](https://stacks.math.columbia.edu/tag/06BK)
* [Stacks Project, Tag 06BE](https://stacks.math.columbia.edu/tag/06BE)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Retractions of a factor of an isomorphism -/

/-- **A composite which is an isomorphism retracts its first factor.**  If `a ≫ b = c` with `c`
invertible, then `b ≫ c⁻¹` is a left inverse of `a`. -/
private theorem exists_retraction_of_isIso_comp {C : Type*} [Category* C] {A Bb T : C}
    (a : A ⟶ Bb) (b : Bb ⟶ T) (c : A ⟶ T) [IsIso c] (hk : a ≫ b = c) :
    ∃ r : Bb ⟶ A, a ≫ r = 𝟙 A :=
  ⟨b ≫ inv c, by rw [← Category.assoc, hk, IsIso.hom_inv_id]⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A retraction from an invertible outer rectangle -/

/-- **An invertible outer rectangle retracts the inverse image of the upper square.**  For two
vertically composable commutative squares of closed subspaces whose composite rectangle has
invertible conormal map, the inverse image along the upper edge of the lower square of the
conormal map of the upper square admits a retraction.

The composition law of [Stacks Project, Tag 04G2] carries invertibility from the rectangle to
that composite. -/
private theorem exists_retraction_conormalMap_of_isIso
    (X X' X'' : AlgebraicSpaces B S hS) (g : X ⟶ X') (g' : X' ⟶ X'')
    (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (Z'' : ClosedSubspaces B S hS X''.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')
    (hsq'' : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      (f ≫ f') ≫ subspaceInclusion B S hS X'' Z'')
    (hiso : IsIso (conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'')) :
    ∃ r, (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫ r = 𝟙 _ := by
  have hab := (isIso_conormalMap_comp_iff B S hS g g' Z Z' Z'' f f' hsq hsq' hsq'').mp hiso
  exact exists_retraction_of_isIso_comp
    ((modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq'))
    (conormalMap B S hS Z Z' g f hsq)
    ((modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
      conormalMap B S hS Z Z' g f hsq) rfl

/-- **A morphism with a retraction is a monomorphism**, in the form the descent step below
consumes: if `u ≫ r = 𝟙` then `u` cancels on the right. -/
private theorem eq_of_comp_eq_of_retraction {C : Type*} [Category* C] {T A Bb : C}
    {u : A ⟶ Bb} {r : Bb ⟶ A} (hr : u ≫ r = 𝟙 A) {φ ψ : T ⟶ A} (h : φ ≫ u = ψ ≫ u) :
    φ = ψ := by
  rw [← Category.comp_id φ, ← hr, ← Category.assoc, h, Category.assoc, hr, Category.comp_id]

/-! ### Invariance of the conormal map under rewriting its two edges -/

/-- The conormal map of a square depends on its two vertical edges only through their values, so
invertibility transports along equalities of those edges. -/
private theorem isIso_conormalMap_congr (X X' : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) {g g' : X ⟶ X'}
    {f f' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS)}
    (hg : g = g') (hf : f = f')
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X Z ≫ g' = f' ≫ subspaceInclusion B S hS X' Z')
    (h : IsIso (conormalMap B S hS Z Z' g' f' hsq')) :
    IsIso (conormalMap B S hS Z Z' g f hsq) := by
  subst hg
  subst hf
  exact h

variable {X Y Z : AlgebraicSpaces B S hS}

/-! ### The chart of the smaller space cut out by an étale chart -/

/-- The chart of `Z` cut out by an étale chart `V ⟶ Z''` of the ambient space of a universal
first-order thickening `Z ⊂ Z''`: the inverse image `Z ×_{Z''} V`, a closed subspace of `V` by
[Stacks Project, Tag 083Q]. -/
noncomputable abbrev thickeningChartSubspace {j : Z ⟶ Y}
    (tj : UniversalFirstOrderThickening B S hS j) (V : BigFppfOver B S hS)
    (v : yoneda.obj V ⟶ tj.ambient.obj) :
    ClosedSubspaces B S hS (yoneda.obj V) :=
  preimageSubspace B S hS
    (ObjectProperty.homMk v :
      (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ tj.ambient)
    tj.closedSub

/-- The projection of the chart `Z ×_{Z''} V` of `Z` to the smaller space of a universal
first-order thickening `Z ⊂ Z'` of `Z`: the projection to the smaller space of `Z ⊂ Z''`,
followed by the two identifications of the smaller spaces with `Z`. -/
noncomputable abbrev thickeningChartProjection {i : Z ⟶ X} {j : Z ⟶ Y}
    (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) (V : BigFppfOver B S hS)
    (v : yoneda.obj V ⟶ tj.ambient.obj) :
    (⟨(thickeningChartSubspace B S hS tj V v).1.toFunctor,
        (thickeningChartSubspace B S hS tj V v).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨ti.closedSub.1.toFunctor, ti.closedSub.2.1⟩ :=
  ObjectProperty.homMk (tj.sub.fromPreimage v ≫ tj.sourceIso.inv ≫ ti.sourceIso.hom)

/-! ### The square of the canonical morphism -/

/-- **The canonical morphism `Z' ⟶ Z''` is a morphism of thickenings.**  The canonical morphism
of ambient spaces of [Stacks Project, Tag 06BK] and the identification of the two smaller spaces
form a commutative square of closed subspaces: this is the square of [Stacks Project, Tag 060A]
attached to the triangle `i ≫ g = j`. -/
theorem universalThickeningComparison_square (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    subspaceInclusion B S hS ti.ambient ti.closedSub ≫
        universalThickeningComparison B S hS g hij ti tj =
      (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj) :
          (⟨ti.closedSub.1.toFunctor, ti.closedSub.2.1⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨tj.closedSub.1.toFunctor, tj.closedSub.2.1⟩) ≫
        subspaceInclusion B S hS tj.ambient tj.closedSub :=
  ObjectProperty.hom_ext _ (universalThickeningComparison_restrict B S hS g hij ti tj)

/-- **The map of conormal modules of Stacks 060A is the conormal map of Stacks 04CP of the
square of closed subspaces it is built from.**  The two are the same morphism by definition.
The identification is stated here on the two morphisms alone, rather than under the inverse
image of modules that the results below apply to them, because that is what makes it cheap; see
the implementation notes of this file. -/
theorem universalThickeningConormalMap_eq_conormalMap (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    universalThickeningConormalMap B S hS g (universalThickeningSourceMap B S hS ti tj)
        ti.isUniversal tj.isUniversal
        (universalThickeningSourceMap_comm B S hS g hij ti tj) =
      @conormalMap B S hS ti.ambient tj.ambient ti.closedSub tj.closedSub
        (universalThickeningComparison B S hS g hij ti tj)
        (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj))
        (universalThickeningComparison_square B S hS g hij ti tj) :=
  rfl

/-! ### The étale covering by the charts of `Z` -/

/-- **The charts of the smaller space cut out by an étale covering of the ambient space cover
it.**  For an étale covering of the ambient space `Z''` of a universal first-order thickening
`Z ⊂ Z''` by representables, the inverse images of `Z` form an étale covering of `Z`: each
projection is a base change of a member of the covering, so is étale by Stacks 03FU, and joint
surjectivity is the fibre-product criterion of Stacks 03H4. -/
private theorem isEtaleCovering_fromPreimage {j : Z ⟶ Y}
    (tj : UniversalFirstOrderThickening B S hS j) {K : Type u}
    (V' : K → BigFppfOver B S hS) (c : ∀ k, yoneda.obj (V' k) ⟶ tj.ambient.obj)
    (hcov : IsEtaleCovering B S hS (fun k => yoneda.obj (V' k)) c) :
    IsEtaleCovering B S hS (fun k => (tj.sub.preimage (c k)).toFunctor)
      (fun k => tj.sub.fromPreimage (c k)) := by
  have hprealg : ∀ k, IsAlgebraicSpace B S hS (tj.sub.preimage (c k)).toFunctor := fun k =>
    (isClosedSubspace_preimage B S hS (c k) tj.sub tj.ambient.2
      (isAlgebraicSpace_yoneda B S hS (V' k)) tj.closedSub.2).1
  refine ⟨tj.closedSub.2.1, hprealg, fun k => ?_, ?_⟩
  · exact isEtale_of_isPullback B S hS
      (ObjectProperty.homMk (tj.sub.preimage (c k)).ι :
        (⟨(tj.sub.preimage (c k)).toFunctor, hprealg k⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (V' k), isAlgebraicSpace_yoneda B S hS (V' k)⟩)
      (ObjectProperty.homMk (tj.sub.fromPreimage (c k)) :
        (⟨(tj.sub.preimage (c k)).toFunctor, hprealg k⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨tj.sub.toFunctor, tj.closedSub.2.1⟩)
      (ObjectProperty.homMk (c k) :
        (⟨yoneda.obj (V' k), isAlgebraicSpace_yoneda B S hS (V' k)⟩ : AlgebraicSpaces B S hS) ⟶
          tj.ambient)
      (ObjectProperty.homMk tj.sub.ι :
        (⟨tj.sub.toFunctor, tj.closedSub.2.1⟩ : AlgebraicSpaces B S hS) ⟶ tj.ambient)
      (isPullback_homMk B S hS tj.closedSub.2.1
        (isAlgebraicSpace_yoneda B S hS (V' k)) tj.ambient.2 (hprealg k)
        (Subfunctor.isPullback_preimage (c k) tj.sub)).flip (hcov.etale k)
  · refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨k, b, hb⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov.jointly_surjective
      (pointsMap B S hS tj.sub.toFunctor tj.sub.ι q))
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
      (Subfunctor.isPullback_preimage (c k) tj.sub) q b hb.symm
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_range.mpr ⟨w, hw⟩⟩

/-- A covering by one étale morphism, precomposed with an étale covering of its source, is an
étale covering indexed by that covering alone. -/
private theorem isEtaleCovering_comp_unit {K : Type u} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : G ⟶ F) (g : ∀ k, X k ⟶ G)
    (hf : IsEtaleCovering B S hS (fun _ : Unit => G) (fun _ => f))
    (hg : IsEtaleCovering B S hS X g) : IsEtaleCovering B S hS X (fun k => g k ≫ f) :=
  IsEtaleCovering.reindex B S hS
    (isEtaleCovering_comp B S hS (fun _ : Unit => K) (fun _ => G) (fun _ => f) (fun _ => X)
      (fun _ => g) hf fun _ => hg)
    (σ := fun k : K => (⟨(), k⟩ : (_ : Unit) × K)) (by rintro ⟨⟨⟩, k⟩; exact ⟨k, rfl⟩)

/-! ### The étale-local retraction -/

section Splitting

-- Unfolding the inverse image of modules to its construction by sheafification does not
-- terminate, and nothing below needs it unfolded.  Without this the two statements below do
-- not elaborate: the inverse images they compare are formed at two spellings of the smaller
-- space, and the unifier unfolds them rather than comparing their arguments.
attribute [local irreducible] modulePullback

/-- **Stacks 06BK: the first arrow of the conormal sequence is étale-locally split.**  Let
`i : Z ⟶ X` and `j : Z ⟶ Y` sit in a commutative triangle `i ≫ g = j` with `g` formally
smooth, let `Z ⊂ Z'` be a universal first-order thickening of `Z` over `X` and `Z ⊂ Z''` one of
`Z` over `Y`, and let `V ⟶ Z''` be an étale chart with `V` affine.  Then the inverse image
along the projection `Z ×_{Z''} V ⟶ Z` of the first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of the conormal
sequence of [Stacks Project, Tag 06BE] admits a retraction.

The first arrow is named here through its definition: it is the conormal map of
[Stacks Project, Tag 04CP] for the square of [Stacks Project, Tag 060A] built from the canonical
morphism `Z' ⟶ Z''` and the identification of the two smaller spaces, which is what
`AlgebraicGeometry.Space.universalThickeningConormalMap` abbreviates. -/
@[stacks 06BK "the first arrow of the conormal sequence is split over an affine étale chart"]
theorem exists_retraction_modulePullback_conormalMap_universalThickening (g : X ⟶ Y)
    {i : Z ⟶ X} {j : Z ⟶ Y} (hij : i ≫ g = j)
    (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) (hg : FormallySmooth g.hom)
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ tj.ambient.obj) (hv : IsEtale B S hS v)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    ∃ r, (modulePullback B S hS (thickeningChartProjection B S hS ti tj V v)).map
        (@conormalMap B S hS ti.ambient tj.ambient ti.closedSub tj.closedSub
          (universalThickeningComparison B S hS g hij ti tj)
          (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj))
          (universalThickeningComparison_square B S hS g hij ti tj)) ≫ r = 𝟙 _ := by
  obtain ⟨s, hs₁, hs₂⟩ :=
    exists_local_section_of_formallySmooth B S hS g hij ti tj hg V v hv hV
  -- The chart of `Z` in `V` maps to the smaller space of `Z ⊂ Z'` over the section `s`.
  have hβhom : (tj.sub.preimage v).ι ≫ s =
      (tj.sub.fromPreimage v ≫ tj.sourceIso.inv ≫ ti.sourceIso.hom) ≫ ti.sub.ι := by
    rw [hs₁]
    simp only [Category.assoc]
  have hsqβ : subspaceInclusion B S hS
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS)
        (thickeningChartSubspace B S hS tj V v) ≫
      (ObjectProperty.homMk s :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          ti.ambient) =
      thickeningChartProjection B S hS ti tj V v ≫
        subspaceInclusion B S hS ti.ambient ti.closedSub :=
    ObjectProperty.hom_ext _ hβhom
  -- The square of the first arrow of the conormal sequence.
  have hsq' := universalThickeningComparison_square B S hS g hij ti tj
  -- The two squares stacked.
  have hsq'' : subspaceInclusion B S hS
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS)
        (thickeningChartSubspace B S hS tj V v) ≫
      (ObjectProperty.homMk s :
          (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
            ti.ambient) ≫ universalThickeningComparison B S hS g hij ti tj =
      (thickeningChartProjection B S hS ti tj V v ≫
          (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj) :
            (⟨ti.closedSub.1.toFunctor, ti.closedSub.2.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨tj.closedSub.1.toFunctor, tj.closedSub.2.1⟩)) ≫
        subspaceInclusion B S hS tj.ambient tj.closedSub := by
    rw [Category.assoc (thickeningChartProjection B S hS ti tj V v), ← Category.assoc, hsqβ,
      Category.assoc, hsq']
  -- The section composed with the canonical morphism is the chart itself.
  have hlow : (ObjectProperty.homMk s :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          ti.ambient) ≫ universalThickeningComparison B S hS g hij ti tj =
      (ObjectProperty.homMk v :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          tj.ambient) :=
    ObjectProperty.hom_ext _ hs₂
  -- On the chart of `Z` the two identifications with `Z` cancel.
  have huphom : (tj.sub.fromPreimage v ≫ tj.sourceIso.inv ≫ ti.sourceIso.hom) ≫
      universalThickeningSourceMap B S hS ti tj = tj.sub.fromPreimage v := by
    rw [universalThickeningSourceMap_eq, Category.assoc, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hup : thickeningChartProjection B S hS ti tj V v ≫
        (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj) :
          (⟨ti.closedSub.1.toFunctor, ti.closedSub.2.1⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨tj.closedSub.1.toFunctor, tj.closedSub.2.1⟩) =
      preimageProjection B S hS
        (ObjectProperty.homMk v :
          (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
            tj.ambient) tj.closedSub :=
    ObjectProperty.hom_ext _ huphom
  -- An étale chart is flat, so the conormal map of the canonical square is an isomorphism.
  have hflat : (smallEtaleRingedToposHom B S hS
      (ObjectProperty.homMk v :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          tj.ambient)).IsFlat :=
    (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS _).1
      (isFlat_of_isEtale B S hS hv)
  have hiso := isIso_conormalMap_congr B S hS
    (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) tj.ambient
    (thickeningChartSubspace B S hS tj V v) tj.closedSub hlow hup hsq''
    (conormalEtaleRestrictionSquare B S hS
      (ObjectProperty.homMk v :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          tj.ambient) tj.closedSub)
    (isIso_conormalMap_of_isFlat B S hS
      (ObjectProperty.homMk v :
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
          tj.ambient) tj.closedSub hflat)
  -- The first arrow is a factor of an isomorphism, so it admits a retraction.
  exact exists_retraction_conormalMap_of_isIso B S hS
    (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ti.ambient
    tj.ambient (ObjectProperty.homMk s) (universalThickeningComparison B S hS g hij ti tj)
    (thickeningChartSubspace B S hS tj V v) ti.closedSub tj.closedSub
    (thickeningChartProjection B S hS ti tj V v)
    (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj))
    hsqβ (universalThickeningComparison_square B S hS g hij ti tj) hsq'' hiso

/-- **Stacks 06BK, in a covering form.**  Under the hypotheses of
`AlgebraicGeometry.Space.exists_retraction_modulePullback_conormalMap_universalThickening`, an
arbitrary étale chart `V ⟶ Z''` is covered by affine étale charts over whose chart of `Z` the
first arrow of the conormal sequence admits a retraction. -/
@[stacks 06BK "the first arrow of the conormal sequence is split over a covering by affine \
étale charts"]
theorem exists_retraction_cover_modulePullback_conormalMap_universalThickening (g : X ⟶ Y)
    {i : Z ⟶ X} {j : Z ⟶ Y} (hij : i ≫ g = j)
    (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) (hg : FormallySmooth g.hom)
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ tj.ambient.obj) (hv : IsEtale B S hS v) :
    ∃ (I : Type u) (V' : I → BigFppfOver B S hS) (π : ∀ k, V' k ⟶ V),
      Sieve.generate (Presieve.ofArrows V' π) ∈ BigFppfOver.topology B S hS V ∧
        ∀ k, ∃ r, (modulePullback B S hS
              (thickeningChartProjection B S hS ti tj (V' k) (yoneda.map (π k) ≫ v))).map
            (@conormalMap B S hS ti.ambient tj.ambient ti.closedSub tj.closedSub
              (universalThickeningComparison B S hS g hij ti tj)
              (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj))
              (universalThickeningComparison_square B S hS g hij ti tj)) ≫ r = 𝟙 _ := by
  obtain ⟨I, V', π, -, -, -, hcov, hV'aff, -, hchart, -, -, -⟩ :=
    exists_squareZeroChart_cover_of_isFirstOrderThickening B S hS tj.isUniversal.firstOrder V v hv
  exact ⟨I, V', π, hcov, fun k =>
    exists_retraction_modulePullback_conormalMap_universalThickening B S hS g hij ti tj hg
      (V' k) (yoneda.map (π k) ≫ v) (hchart k) (hV'aff k)⟩

/-- **Stacks 06BK: the conormal sequence is exact on the left.**  Let `i : Z ⟶ X` and
`j : Z ⟶ Y` sit in a commutative triangle `i ≫ g = j` with `g` formally smooth, and let
`Z ⊂ Z'` be a universal first-order thickening of `Z` over `X` and `Z ⊂ Z''` one of `Z` over
`Y`.  Then the first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of the conormal sequence of
[Stacks Project, Tag 06BE] is a monomorphism.

The first arrow is named through its definition, as the conormal map of
[Stacks Project, Tag 04CP] for the square of [Stacks Project, Tag 060A]; see the implementation
notes of this file.  It is split injective over each affine étale chart of `Z''` by
`AlgebraicGeometry.Space.exists_retraction_modulePullback_conormalMap_universalThickening`, and
the charts of `Z` cut out by the affine étale charts of an atlas of `Z''` form an étale covering
of `Z`, so the two inverse images of a pair of morphisms it equalises agree on that covering and
the pair is equal. -/
@[stacks 06BK "the conormal sequence is exact on the left"]
theorem mono_conormalMap_universalThickening (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) (hg : FormallySmooth g.hom) :
    Mono (@conormalMap B S hS ti.ambient tj.ambient ti.closedSub tj.closedSub
      (universalThickeningComparison B S hS g hij ti tj)
      (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj))
      (universalThickeningComparison_square B S hS g hij ti tj)) := by
  obtain ⟨W, aw, hawSurj, hawEtale⟩ := tj.ambient.2.exists_atlas
  obtain ⟨K, V', π, hV'aff, hcovV⟩ := exists_affine_isEtaleCovering_yoneda B S hS W
  -- The affine étale charts of an atlas of `Z''` cover `Z''`.
  have hchart : IsEtaleCovering B S hS (fun k => yoneda.obj (V' k))
      (fun k => yoneda.map (π k) ≫ aw) := by
    exact isEtaleCovering_comp_unit B S hS aw (fun k => yoneda.map (π k))
      (isEtaleCovering_atlas B S hS tj.ambient.2 hawSurj hawEtale) hcovV
  -- Their charts of `Z` cover `Z`, through the two identifications of the smaller spaces.
  have hpre := isEtaleCovering_fromPreimage B S hS tj V' (fun k => yoneda.map (π k) ≫ aw) hchart
  have hcov : IsEtaleCovering B S hS
      (fun k => (thickeningChartSubspace B S hS tj (V' k) (yoneda.map (π k) ≫ aw)).1.toFunctor)
      (fun k => (thickeningChartProjection B S hS ti tj (V' k)
        (yoneda.map (π k) ≫ aw)).hom) := by
    exact isEtaleCovering_comp_unit B S hS (tj.sourceIso.inv ≫ ti.sourceIso.hom)
      (fun k => tj.sub.fromPreimage (yoneda.map (π k) ≫ aw))
      (isEtaleCovering_of_isIso B S hS (tj.sourceIso.inv ≫ ti.sourceIso.hom) ti.closedSub.2.1) hpre
  -- A morphism of modules is determined by its inverse images along that covering.
  refine ⟨fun φ ψ hφψ => ?_⟩
  refine QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun k => (⟨(thickeningChartSubspace B S hS tj (V' k) (yoneda.map (π k) ≫ aw)).1.toFunctor,
        (thickeningChartSubspace B S hS tj (V' k) (yoneda.map (π k) ≫ aw)).2.1⟩ :
      AlgebraicSpaces B S hS))
    (fun k => thickeningChartProjection B S hS ti tj (V' k) (yoneda.map (π k) ≫ aw))
    hcov φ ψ fun k => ?_
  obtain ⟨r, hr⟩ := exists_retraction_modulePullback_conormalMap_universalThickening B S hS g hij
    ti tj hg (V' k) (yoneda.map (π k) ≫ aw) (hchart.etale k) (hV'aff k)
  exact eq_of_comp_eq_of_retraction hr
    (by rw [← Functor.map_comp, ← Functor.map_comp, hφψ])

end Splitting

end AlgebraicGeometry.Space

end
