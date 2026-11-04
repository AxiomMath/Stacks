module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# Universal homeomorphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a *universal homeomorphism* when its base
change along every morphism to its target from an algebraic space over `S` induces a
homeomorphism on the spaces of points (Stacks 05Z5). This file gives the definition and the two
formal permanence properties of it: stability under base change (Stacks 0CFT) and under
composition (Stacks 0CFU). It also records that a universal homeomorphism is universally closed,
which is how the notion is used, and that the inclusion of the reduction of an algebraic space
is a universal homeomorphism, which is the content of Stacks 08AK. It then gives the criterion
that a universally closed, universally injective morphism whose base changes are all surjective
is a universal homeomorphism, and closes with the example of Stacks 05Z6: the squaring
composite out of the involution quotient of the affine line is universally closed, and the
descended morphism `X ⟶ 𝐀¹_k` itself is a universal homeomorphism. The latter is also the
assertion of the last sentence of Stacks 05ZI, that a universal homeomorphism from `X` to the
affine line can be exhibited directly by `t ↦ t ^ 2`.

## Main definitions

* `AlgebraicGeometry.Space.UniversalHomeomorphism`: **Stacks 05Z5**.

## Main results

* `AlgebraicGeometry.Space.universalHomeomorphism_pullback`: **Stacks 0CFT**, a base change of a
  universal homeomorphism is a universal homeomorphism; and
  `AlgebraicGeometry.Space.universalHomeomorphism_of_isPullback`, the same conclusion for an
  arbitrary cartesian square.
* `AlgebraicGeometry.Space.universalHomeomorphism_comp`: **Stacks 0CFU**, a composition of
  universal homeomorphisms is a universal homeomorphism.
* `AlgebraicGeometry.Space.universallyClosed_of_universalHomeomorphism`: a universal
  homeomorphism is universally closed.
* `AlgebraicGeometry.Space.universallyClosed_of_isLocallySurjective_comp`: **Stacks 08AJ** for
  a locally surjective first factor, with no algebraicity hypothesis.
* `AlgebraicGeometry.Space.universalHomeomorphism_of_universallyClosed_of_universallyInjective`:
  a universally closed, universally injective morphism all of whose base changes are surjective
  is a universal homeomorphism.
* `AlgebraicGeometry.Space.isAlgebraicSpace_points_affineLine`: the restricted functor of
  points of the affine line over a field is an algebraic space over that field.
* `AlgebraicGeometry.Space.universallyClosed_toQuotientSheaf_comp_squaringMap`: the universal
  closedness assertion of **Stacks 05Z6**, for the composite of the projection onto the
  involution quotient of the affine line with the squaring map of Stacks 05VS.
* `AlgebraicGeometry.Space.universalHomeomorphism_squaringMap`: the morphism `X ⟶ 𝐀¹_k`
  descended from squaring the coordinate is a universal homeomorphism. This is the last
  assertion of **Stacks 05Z6** and the last sentence of **Stacks 05ZI**.

## Implementation notes

The definition is the exact analogue of `AlgebraicGeometry.Space.UniversallyClosed` with
`IsClosedMap` replaced by `IsHomeomorph`, and the two permanence proofs are the analogues of
`AlgebraicGeometry.Space.universallyClosed_pullback` and
`AlgebraicGeometry.Space.universallyClosed_comp`. As there, the predicate is stated for an
arbitrary morphism of presheaves on the big fppf site of `S`, algebraicity of the source and
target being imposed by clients; only algebraicity of the test object enters, as a hypothesis of
the quantifier, exactly as in the source. The topology on the point set of Stacks 03BU is
`AlgebraicGeometry.Space.pointTopology`, installed as a local instance.

Everything turns on two statements about the map on points: it is a homeomorphism for an
isomorphism of presheaves, which is
`AlgebraicGeometry.Space.pointsHomeomorphOfIso`, and the map on points of a composite is the
composite of the maps on points, which is `AlgebraicGeometry.Space.pointsMap_comp`. Together
they give `AlgebraicGeometry.Space.isHomeomorph_pointsMap_of_comp_isIso`, the transport of the
property along a precomposed isomorphism; base change is then its instance at the pasting
isomorphism `W ×_Z (Z ×_Y X) ≅ W ×_Y X` and composition its instance at
`W ×_Z X ≅ (W ×_Z Y) ×_Y X`.

Stability under base change is stated both for the canonical fibre product, which is the form
Stacks 0CFT takes, and for an arbitrary cartesian square over the same cospan, which is what a
client with its own fibre product needs; the latter is deduced from the former exactly as
`AlgebraicGeometry.Space.universallyClosed_of_isPullback` is, through composition with the
comparison isomorphism.

For the reduction, the two halves of `isHomeomorph_iff_isEmbedding_surjective` are supplied
separately: the embedding half by Stacks 0ABJ applied to the base change of the inclusion,
which is again an immersion, and the surjectivity half by Stacks 03H4 applied to the point of
the reduction over a given point of the test space, which exists because the point set of the
reduction is the whole point set of the ambient space.

For the squaring composite, the target is the restricted functor of points of the affine line,
in which shape Stacks 05VS states the descended morphism. That presheaf is represented by the
chart `AlgebraicGeometry.AffineLineInvolution.affineLineChart`, by
`AlgebraicGeometry.Space.pointsYonedaIso`, which makes it an algebraic space and identifies the
composite with the morphism of represented presheaves induced by squaring of the coordinate —
the identification uses only the defining property
`AlgebraicGeometry.AffineLineInvolution.toQuotientSheaf_comp_squaringMap` of the descended
morphism. Squaring is the ring map `X ↦ X ^ 2` on the polynomial algebra in one variable,
which is integral because the variable satisfies `T ^ 2 - X` and generates; an integral
morphism of schemes is universally closed, and Stacks 03XD turns universal closedness of every
represented base change into universal closedness in the sense of Stacks 03HI. The integrality
argument is carried out with `Algebra.id` and `ULift.algebra` locally disabled, so that the
algebra structure induced by the ring map itself is the one instance resolution sees.

That same ring map is `MvPolynomial.expand 2`, hence injective, so the morphism of spectra it
induces has dense image; being integral it is also closed, and a closed dense image is
everything. This gives surjectivity of squaring on the chart, and
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange` propagates it to every base
change of the squaring composite, which Stacks 03MD reads as surjectivity on points. Since the
base change of the composite factors through the base change of the squaring map, the latter is
surjective as well. Universal closedness of the squaring map itself is obtained from universal
closedness of the composite by
`AlgebraicGeometry.Space.universallyClosed_of_isLocallySurjective_comp`, the quotient
projection being locally surjective by
`Stacks.Groupoids.isLocallySurjective_toQuotientSheaf`. The three together give the universal
homeomorphism; no step needs the quotient to be an algebraic space, which is what makes the
assertion available here at all.

The nonseparatedness assertion of Stacks 05Z6 is
`AlgebraicGeometry.AffineLineInvolution.not_isSeparated_squaringMap`, which is also part (5) of
Stacks 05VS and needs no hypothesis on the quotient at all — in particular neither the
algebraic-space property nor the effective descent of Stacks 0265 — because being separated is a
property of *every* represented base change of the relative diagonal, so one cartesian square
refutes it. What is still missing is the étale presentation: `AlgebraicGeometry.Space.IsEtale`
of the quotient chart contains representability of that chart, which this library has only from
the representable diagonal of the quotient sheaf
(`AlgebraicGeometry.Space.etale_toQuotientSheaf_of_relativelyRepresentable_diag`), hence only
conditionally on the effective descent of Stacks 0265 at the monomorphisms locally of finite
type.

## References

* [Stacks Project, Tag 05Z5](https://stacks.math.columbia.edu/tag/05Z5)
* [Stacks Project, Tag 0CFT](https://stacks.math.columbia.edu/tag/0CFT)
* [Stacks Project, Tag 0CFU](https://stacks.math.columbia.edu/tag/0CFU)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 08AK](https://stacks.math.columbia.edu/tag/08AK)
* [Stacks Project, Tag 05Z6](https://stacks.math.columbia.edu/tag/05Z6)
* [Stacks Project, Tag 05ZI](https://stacks.math.columbia.edu/tag/05ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The definition -/

section Defs

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05Z5.** A morphism of algebraic spaces over `S` is a *universal homeomorphism*
when its base change along every morphism to its target from an algebraic space over `S`
induces a homeomorphism on the spaces of points. -/
@[stacks 05Z5]
abbrev UniversalHomeomorphism (f : F ⟶ G) : Prop :=
  ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
    ∀ g : Z ⟶ G, IsHomeomorph (pointsMap B S hS (pullback g f) (pullback.fst g f))

end Defs

/-! ### Transport along an isomorphism -/

section Transport

variable {F F' G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If a morphism of presheaves on the big fppf site of `S` becomes, after precomposition with
an isomorphism, a morphism whose map on points is a homeomorphism, then its own map on points
is a homeomorphism. -/
theorem isHomeomorph_pointsMap_of_comp_isIso (e : F ⟶ F') [IsIso e] {g : F' ⟶ G} {f : F ⟶ G}
    (hfg : e ≫ g = f) (hg : IsHomeomorph (pointsMap B S hS F' g)) :
    IsHomeomorph (pointsMap B S hS F f) := by
  subst hfg
  rw [pointsMap_comp]
  exact hg.comp (pointsHomeomorphOfIso B S hS (asIso e)).isHomeomorph

/-- The map on points of a composite is a homeomorphism as soon as the maps on points of the
two factors are. -/
theorem isHomeomorph_pointsMap_comp {f : F ⟶ G} {g : G ⟶ H}
    (hg : IsHomeomorph (pointsMap B S hS G g)) (hf : IsHomeomorph (pointsMap B S hS F f)) :
    IsHomeomorph (pointsMap B S hS F (f ≫ g)) := by
  rw [pointsMap_comp]
  exact hg.comp hf

end Transport

/-! ### Universal closedness -/

section Closed

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A universal homeomorphism of algebraic spaces over `S` is universally closed: a
homeomorphism is in particular a closed map. -/
theorem universallyClosed_of_universalHomeomorphism {f : X ⟶ Y}
    (hf : UniversalHomeomorphism B S hS f) : UniversallyClosed B S hS f := fun Z hZ g ↦
  ((hf Z hZ g).homeomorph _).isClosedMap

end Closed

/-! ### Base change -/

section BaseChange

variable {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CFT.** A base change of a universal homeomorphism of algebraic spaces over `S` is
a universal homeomorphism.

Nothing is needed beyond unwinding the definition: a base change of `Z ×_Y X ⟶ Z` along
`k : W ⟶ Z` is a base change of `X ⟶ Y` along `k ≫ g`. -/
@[stacks 0CFT]
theorem universalHomeomorphism_pullback (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : UniversalHomeomorphism B S hS f) :
    UniversalHomeomorphism B S hS (pullback.fst g f) := fun V hV k ↦
  isHomeomorph_pointsMap_of_comp_isIso B S hS (pullbackRightPullbackFstIso g f k).hom
    (pullbackRightPullbackFstIso_hom_fst g f k) (hf V hV (k ≫ g))

/-- An isomorphism of presheaves on the big fppf site of `S` is a universal homeomorphism: each
of its base changes is again an isomorphism, and the map on points of an isomorphism is a
homeomorphism. -/
theorem universalHomeomorphism_of_isIso (e : X ⟶ Y) [IsIso e] :
    UniversalHomeomorphism B S hS e := fun V _ g ↦
  have : IsIso (pullback.fst g e) :=
    (IsPullback.of_isLimit (pullback.isLimit g e)).isIso_fst_of_isIso
  (pointsHomeomorphOfIso B S hS (asIso (pullback.fst g e))).isHomeomorph

end BaseChange

/-! ### Composition -/

section Comp

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CFU.** A composition of universal homeomorphisms of algebraic spaces over `S` is
a universal homeomorphism.

The base change `W ×_Z X ⟶ W` of the composite along `k : W ⟶ Z` is identified by the pasting
isomorphism `W ×_Z X ≅ (W ×_Z Y) ×_Y X` with the composition of a base change of `X ⟶ Y` and a
base change of `Y ⟶ Z`. -/
@[stacks 0CFU]
theorem universalHomeomorphism_comp (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : UniversalHomeomorphism B S hS f) (hg : UniversalHomeomorphism B S hS g) :
    UniversalHomeomorphism B S hS (f ≫ g) := by
  intro W hW k
  have hP : IsAlgebraicSpace B S hS (pullback k g) :=
    isAlgebraicSpace_pullback B S hS k g hW hY hZ
  exact isHomeomorph_pointsMap_of_comp_isIso B S hS (pullbackLeftPullbackSndIso k g f).inv
    (pullbackLeftPullbackSndIso_inv_fst k g f)
    (isHomeomorph_pointsMap_comp B S hS (hg W hW k)
      (hf (pullback k g) hP (pullback.snd k g)))

end Comp

/-! ### Base change along an arbitrary cartesian square -/

section Square

variable {A C Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CFT** for an arbitrary cartesian square: if `IsPullback a b g f` and `f` is a
universal homeomorphism, then so is `a`.

This is `AlgebraicGeometry.Space.universalHomeomorphism_pullback` composed with the
identification of the given square with the canonical fibre product. -/
@[stacks 0CFT]
theorem universalHomeomorphism_of_isPullback (hC : IsAlgebraicSpace B S hS C)
    (hZ : IsAlgebraicSpace B S hS Z) (hT : IsAlgebraicSpace B S hS T) (f : C ⟶ T) (g : Z ⟶ T)
    (hf : UniversalHomeomorphism B S hS f) {a : A ⟶ Z} {b : A ⟶ C}
    (hpb : IsPullback a b g f) : UniversalHomeomorphism B S hS a := by
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hC hT
  have hc := universalHomeomorphism_comp B S hS hP hZ hpb.isoPullback.hom (pullback.fst g f)
    (universalHomeomorphism_of_isIso B S hS hpb.isoPullback.hom)
    (universalHomeomorphism_pullback B S hS f g hf)
  rwa [hpb.isoPullback_hom_fst] at hc

end Square

/-! ### A criterion for a universal homeomorphism -/

section Criterion

variable {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A base change of a locally surjective morphism of presheaves of types is locally
surjective: a section of the base lifts, on the covering produced by local surjectivity of the
given morphism, to a section of the fibre product. -/
private theorem isLocallySurjective_of_isPullback
    (J : GrothendieckTopology (BigFppfOver B S hS))
    {F H K L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ H} {b : F ⟶ K} {c : H ⟶ L}
    {d : K ⟶ L} (h : IsPullback a b c d) (hc : Presheaf.IsLocallySurjective J c) :
    Presheaf.IsLocallySurjective J b := by
  have := hc
  refine ⟨fun {U} s => ?_⟩
  apply J.superset_covering _ (Presheaf.imageSieve_mem J c (d.app _ s))
  rintro V i ⟨t, ht⟩
  have hV := h.map ((evaluation _ _).obj (Opposite.op V))
  obtain ⟨x, -, hx⟩ := Types.exists_of_isPullback hV t (K.map i.op s)
    (ht.trans (d.naturality_apply i.op s).symm)
  exact ⟨x, hx⟩

/-- The comparison from the base change along `f ≫ q` to the base change along `q` commutes with
the first projections and fits in a cartesian square over `f`. -/
private theorem exists_lift_pullback_comp {X Y T W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : W ⟶ T) (f : X ⟶ Y) (q : Y ⟶ T) :
    ∃ r : pullback k (f ≫ q) ⟶ pullback k q, r ≫ pullback.fst k q = pullback.fst k (f ≫ q) ∧
      IsPullback r (pullback.snd k (f ≫ q)) (pullback.snd k q) f := by
  have hcomm : pullback.fst k (f ≫ q) ≫ k = (pullback.snd k (f ≫ q) ≫ f) ≫ q := by
    rw [Category.assoc]
    exact pullback.condition
  have hrfst := pullback.lift_fst _ _ hcomm
  have hrsnd := pullback.lift_snd _ _ hcomm
  refine ⟨_, hrfst, ?_⟩
  exact IsPullback.of_right (hrfst.symm ▸ IsPullback.of_hasPullback k (f ≫ q)) hrsnd
    (IsPullback.of_hasPullback k q)

/-- **Stacks 08AJ for a locally surjective first factor.** If `f ≫ q` is universally closed
and `f` is locally surjective for the fppf topology, then `q` is universally closed.

This is `AlgebraicGeometry.Space.universallyClosed_of_isSurjective_comp` with the surjectivity
of the base changes of `f` supplied by local surjectivity instead of by Stacks 03MH, which is
why no algebraicity hypothesis is needed: Stacks 03MH passes through the reductions of the four
corners of a cartesian square of algebraic spaces, whereas a base change of a locally
surjective morphism of presheaves is locally surjective for formal reasons, and a locally
surjective morphism is surjective on the point sets of Stacks 03BU by
`AlgebraicGeometry.Space.isSurjective_of_isLocallySurjective`. -/
theorem universallyClosed_of_isLocallySurjective_comp (f : X ⟶ Y) (q : Y ⟶ T)
    (hfq : UniversallyClosed B S hS (f ≫ q))
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    UniversallyClosed B S hS q := by
  intro W hW k
  obtain ⟨r, hrfst, hsquare⟩ := exists_lift_pullback_comp B S hS k f q
  have hsurj : IsSurjective B S hS r :=
    isSurjective_of_isLocallySurjective B S hS r
      (isLocallySurjective_of_isPullback B S hS _ hsquare.flip hf)
  refine IsClosedMap.of_comp_surjective hsurj (continuous_pointsMap B S hS r) ?_
  have hgoal : IsClosedMap
      (pointsMap B S hS (pullback k (f ≫ q)) (r ≫ pullback.fst k q)) := by
    rw [hrfst]
    exact hfq W hW k
  rwa [pointsMap_comp] at hgoal

/-- **A universally closed, universally injective morphism all of whose base changes are
surjective is a universal homeomorphism.** The map on points of each base change is
continuous, closed, injective and surjective, which is a homeomorphism by
`isHomeomorph_iff_continuous_isClosedMap_bijective`.

Surjectivity is asked of every base change rather than of `f` alone, because passing from the
one to the other is Stacks 03MH, which needs both source and target to be algebraic spaces. -/
theorem universalHomeomorphism_of_universallyClosed_of_universallyInjective (f : X ⟶ Y)
    (hcl : UniversallyClosed B S hS f) (hinj : UniversallyInjective B S hS f)
    (hsurj : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : Z ⟶ Y),
      IsSurjective B S hS (pullback.fst g f)) :
    UniversalHomeomorphism B S hS f := fun Z hZ g ↦
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨continuous_pointsMap B S hS _, hcl Z hZ g, hinj Z hZ g, hsurj Z g⟩

end Criterion

/-! ### The squaring map out of the involution quotient of the affine line -/

section Squaring

open AffineLineInvolution

variable (k : Type u) [Field k]

/-- The endomorphism `X ↦ X ^ 2` of the polynomial algebra in one variable. -/
private noncomputable def squarePolynomialMap :
    MvPolynomial PUnit.{u + 1} k →+* MvPolynomial PUnit.{u + 1} k :=
  (MvPolynomial.aeval (fun _ : PUnit.{u + 1} =>
    (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{u + 1} k) ^ 2)).toRingHom

private theorem squarePolynomialMap_X :
    squarePolynomialMap k (MvPolynomial.X PUnit.unit) =
      (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{u + 1} k) ^ 2 :=
  MvPolynomial.aeval_X _ PUnit.unit

private theorem squarePolynomialMap_C (r : k) :
    squarePolynomialMap k (MvPolynomial.C r) =
      (MvPolynomial.C r : MvPolynomial PUnit.{u + 1} k) := by
  show MvPolynomial.aeval _ (MvPolynomial.C r) = _
  rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

section

attribute [-instance] Algebra.id ULift.algebra

/-- `X ↦ X ^ 2` makes the polynomial algebra in one variable integral over itself: the
variable satisfies `T ^ 2 - X`, and it generates. -/
private theorem squarePolynomialMap_isIntegral :
    (squarePolynomialMap k).IsIntegral := by
  let R := MvPolynomial PUnit.{u + 1} k
  let φ := squarePolynomialMap k
  let ψ : R →+* ULift.{u + 1} R :=
    (ULift.ringEquiv (R := R)).symm.toRingHom.comp φ
  let : Algebra R (ULift.{u + 1} R) := RingHom.toAlgebra ψ
  have hAlgMap : algebraMap R (ULift.{u + 1} R) = ψ := rfl
  have hAI : Algebra.IsIntegral R (ULift.{u + 1} R) := by
    let A : Subalgebra R (ULift.{u + 1} R) :=
      Algebra.adjoin R (Set.range (fun i : PUnit.{u + 1} => ULift.up (MvPolynomial.X i : R)))
    have hX : ∀ i : PUnit.{u + 1}, _root_.IsIntegral R (ULift.up (MvPolynomial.X i : R)) := by
      intro i
      have hi : i = PUnit.unit := Subsingleton.elim _ _
      subst hi
      have hX2 : ψ (MvPolynomial.X PUnit.unit : R) =
          ULift.up ((MvPolynomial.X PUnit.unit : R) ^ 2) := by
        show (ULift.ringEquiv (R := R)).symm
            (squarePolynomialMap k (MvPolynomial.X PUnit.unit)) =
          ULift.up ((MvPolynomial.X PUnit.unit : R) ^ 2)
        rw [squarePolynomialMap_X]
        rfl
      have hroot : Polynomial.aeval (ULift.up (MvPolynomial.X PUnit.unit : R))
          (Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X PUnit.unit : R)) = 0 := by
        rw [Polynomial.aeval_def, hAlgMap, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_C, hX2, sub_eq_zero]
        rfl
      apply _root_.IsIntegral.of_aeval_monic
        (p := Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X PUnit.unit : R))
        (Polynomial.monic_X_pow_sub_C (MvPolynomial.X PUnit.unit : R) (by norm_num))
        (by norm_num)
      rw [hroot]
      exact isIntegral_zero (R := R) (B := ULift.{u + 1} R)
    have htop : A = ⊤ := by
      apply top_unique
      intro x hx
      clear hx
      show ULift.up x.down ∈ A
      induction x.down using MvPolynomial.induction_on with
      | C r =>
          have hC : ψ (MvPolynomial.C r : R) = ULift.up (MvPolynomial.C r : R) := by
            show (ULift.ringEquiv (R := R)).symm
                (squarePolynomialMap k (MvPolynomial.C r)) =
              ULift.up (MvPolynomial.C r : R)
            rw [squarePolynomialMap_C]
            rfl
          rw [← hC]
          simpa [hAlgMap] using A.algebraMap_mem (MvPolynomial.C r : R)
      | add p q hp hq =>
          show (ULift.up p + ULift.up q) ∈ A
          exact A.add_mem hp hq
      | mul_X p i hp =>
          show (ULift.up p * ULift.up (MvPolynomial.X i : R)) ∈ A
          exact A.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))
    have hA : Algebra.IsIntegral R A :=
      Algebra.IsIntegral.adjoin (fun x hx => by
        obtain ⟨i, rfl⟩ := hx
        exact hX i)
    have htopIntegral : Algebra.IsIntegral R (⊤ : Subalgebra R (ULift.{u + 1} R)) :=
      htop ▸ hA
    exact (Subalgebra.topEquiv (R := R) (A := ULift.{u + 1} R)).isIntegral_iff.mp
      htopIntegral
  have hψ : ψ.IsIntegral := algebraMap_isIntegral_iff.mpr hAI
  have hcomp : (ULift.ringEquiv (R := R)).toRingHom.comp ψ = φ := by
    apply RingHom.ext
    intro x
    simp [ψ]
  show φ.IsIntegral
  intro x
  rw [← hcomp]
  have hx := (RingHom.IsIntegralElem.map_iff
    (g := (ULift.ringEquiv (R := R)).toRingHom) (f := ψ)
    (ULift.ringEquiv (R := R)).injective (x := ULift.up x)).mpr (hψ (ULift.up x))
  simpa [ULift.ringEquiv] using hx

end

/-- Squaring of the coordinate of the affine line is, through the identification of affine
space with the spectrum of its coordinate ring, the morphism of spectra induced by the ring
map `X ↦ X ^ 2`. -/
private theorem affineLineSquare_left_eq_specMap :
    (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom (squarePolynomialMap k)) ≫
          (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv =
      (affineLineSquare k).left := by
  let R : CommRingCat.{u} := .of (MvPolynomial PUnit.{u + 1} k)
  let e := AffineSpace.SpecIso PUnit.{u + 1} (.of k)
  let φ : R ⟶ R := CommRingCat.ofHom (squarePolynomialMap k)
  show e.hom ≫ Spec.map φ ≫ e.inv = (affineLineSquare k).left
  refine AffineSpace.hom_ext ?_ ?_
  · dsimp only [e]
    simp only [Category.assoc, AffineSpace.SpecIso_inv_over]
    have hC : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k) =
        CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k) ≫ φ := by
      ext r
      simp [φ, squarePolynomialMap]
    calc
      e.hom ≫ Spec.map φ ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
          e.hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C ≫ φ) := by
            rw [← Spec.map_comp]
      _ = e.hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) := by rw [← hC]
      _ = AffineSpace PUnit.{u + 1} (Spec (.of k)) ↘ Spec (.of k) := by
            rw [← AffineSpace.SpecIso_inv_over, ← Category.assoc]
            simp
      _ = (affineLineSquare k).left ≫
          (AffineSpace PUnit.{u + 1} (Spec (.of k)) ↘ Spec (.of k)) := by
            simp [affineLineSquare]
  · intro i
    obtain rfl : i = PUnit.unit := Subsingleton.elim _ _
    show e.hom.appTop ((Spec.map φ).appTop
      (e.inv.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))) =
      (affineLineSquare k).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)
    dsimp only [e]
    rw [AffineSpace.SpecIso_inv_appTop_coord]
    have hnat := congrArg (fun g => g.hom (.X PUnit.unit))
      (Scheme.ΓSpecIso_inv_naturality φ)
    have hnat' : (Spec.map φ).appTop.hom
        ((Scheme.ΓSpecIso R).inv (.X PUnit.unit)) =
          (Scheme.ΓSpecIso R).inv (φ.hom (.X PUnit.unit)) := by
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using hnat.symm
    rw [hnat', AffineSpace.SpecIso_hom_appTop]
    simp [R, φ, squarePolynomialMap]

/-- The morphism of spectra induced by `X ↦ X ^ 2` is an integral morphism of schemes. -/
private instance isIntegralHom_specMap_squarePolynomialMap :
    _root_.AlgebraicGeometry.IsIntegralHom
      (Spec.map (CommRingCat.ofHom (squarePolynomialMap k))) :=
  IsIntegralHom.SpecMap_iff.mpr (squarePolynomialMap_isIntegral k)

/-- Squaring of the coordinate is an integral morphism of schemes: on the affine model it is
the ring map `X ↦ X ^ 2`, which is integral. -/
private instance isIntegralHom_affineLineSquare :
    _root_.AlgebraicGeometry.IsIntegralHom (affineLineSquare k).left := by
  rw [← affineLineSquare_left_eq_specMap k]
  infer_instance

/-- `X ↦ X ^ 2` is injective on the polynomial algebra in one variable: it is the expansion
of the variable by the factor two, `MvPolynomial.expand`. -/
private theorem squarePolynomialMap_injective :
    Function.Injective (squarePolynomialMap k) := by
  have h : squarePolynomialMap k = (MvPolynomial.expand 2).toRingHom := rfl
  rw [h]
  exact MvPolynomial.expand_injective (n := 2) (by norm_num)

/-- The morphism of spectra induced by `X ↦ X ^ 2` on the polynomial algebra in one variable
is surjective: being integral it is a closed map, and being induced by an injective ring map
it has dense image, so its image is closed and dense. -/
private theorem surjective_specMap_squarePolynomialMap :
    _root_.AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (squarePolynomialMap k))) := by
  have hcl : IsClosedMap (Spec.map (CommRingCat.ofHom (squarePolynomialMap k))) :=
    Scheme.Hom.isClosedMap _
  have hdense : DenseRange (Spec.map (CommRingCat.ofHom (squarePolynomialMap k))) := by
    show DenseRange (PrimeSpectrum.comap (squarePolynomialMap k))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot (squarePolynomialMap k)).mp
        (squarePolynomialMap_injective k)]
    exact bot_le
  have hclosed : IsClosed
      (Set.range (Spec.map (CommRingCat.ofHom (squarePolynomialMap k)))) := by
    simpa [Set.image_univ] using hcl _ isClosed_univ
  exact ⟨by rw [← Set.range_eq_univ, ← hclosed.closure_eq]; exact hdense.closure_range⟩

/-- Squaring of the coordinate is a surjective morphism of schemes. -/
private instance surjective_affineLineSquare :
    _root_.AlgebraicGeometry.Surjective (affineLineSquare k).left := by
  have := surjective_specMap_squarePolynomialMap k
  rw [← affineLineSquare_left_eq_specMap k]
  infer_instance

/-- The restricted functor of points of the affine line over `k` is the presheaf represented by
its chart in the site: the functor presenting the site is fully faithful, and the chart has the
affine line as its underlying scheme over `k`. -/
private noncomputable def affineLinePointsIso (hk : B.Contains (Spec (.of k))) :
    Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k) ≅
      yoneda.obj (affineLineChart k B hk) :=
  pointsYonedaIso (Over.post (X := B.obj hk) B.inclusion) (affineLineChart k B hk)

/-- The restricted functor of points of the affine line over `k` is an algebraic space over
`k`, being the presheaf represented by the chart
`AlgebraicGeometry.AffineLineInvolution.affineLineChart`. -/
theorem isAlgebraicSpace_points_affineLine (hk : B.Contains (Spec (.of k))) :
    IsAlgebraicSpace B (Spec (.of k)) hk
      (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)) :=
  AlgebraicGeometry.isAlgebraicSpace_of_iso B (Spec (.of k)) hk (affineLinePointsIso B k hk)
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (affineLineChart k B hk))

/-- Squaring of the coordinate, as an endomorphism of the chart of the affine line in the
site. -/
private noncomputable def affineLineChartSquare (hk : B.Contains (Spec (.of k))) :
    affineLineChart k B hk ⟶ affineLineChart k B hk :=
  Over.homMk (ObjectProperty.homMk (affineLineSquare k).left)
    (by apply ObjectProperty.hom_ext; exact (affineLineSquare k).w)

private theorem post_map_affineLineChartSquare (hk : B.Contains (Spec (.of k))) :
    (Over.post (X := B.obj hk) B.inclusion).map (affineLineChartSquare B k hk) =
      affineLineSquare k := by
  apply Over.OverMorphism.ext
  rfl

/-- Through the identification `AlgebraicGeometry.Space.pointsYonedaIso` of the restricted
functor of points of the affine line with the presheaf represented by its chart, the composite
of the projection onto the involution quotient with the descended squaring map of Stacks 05VS
is the morphism of represented presheaves induced by squaring of the coordinate.

Only the defining property
`AlgebraicGeometry.AffineLineInvolution.toQuotientSheaf_comp_squaringMap` of the descended
morphism is used. -/
private theorem toQuotientSheaf_comp_squaringMap_eq_conj (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
        squaringMap k B hk =
      (affineLinePointsIso B k hk).hom ≫
        yoneda.map (affineLineChartSquare B k hk) ≫ (affineLinePointsIso B k hk).inv := by
  rw [← cancel_epi (affineLinePointsIso B k hk).inv, Iso.inv_hom_id_assoc,
    toQuotientSheaf_comp_squaringMap k B hk]
  ext X y
  show (Over.post (X := B.obj hk) B.inclusion).map y ≫ affineLineSquare k =
    (Over.post (X := B.obj hk) B.inclusion).map (y ≫ affineLineChartSquare B k hk)
  rw [Functor.map_comp, post_map_affineLineChartSquare]
  rfl

/-- A property `P` of morphisms of schemes, stable under base change, holds for the composite of
the projection onto the involution quotient with the descended squaring map, after every
represented base change, as soon as it holds for squaring of the coordinate on the chart. -/
private theorem presheaf_toQuotientSheaf_comp_squaringMap {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]
    (hsq : P ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (affineLineChartSquare B k hk))) :
    (P.inverseImage (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
        squaringMap k B hk) := by
  have := hP.respectsIso
  rw [toQuotientSheaf_comp_squaringMap_eq_conj B k hk]
  exact MorphismProperty.RespectsIso.precomp _ (affineLinePointsIso B k hk).hom _
    (MorphismProperty.RespectsIso.postcomp _ (affineLinePointsIso B k hk).inv _
      ((presheaf_yoneda_map_iff B (Spec (.of k)) hk hP (affineLineChartSquare B k hk)).mpr hsq))

/-- **Stacks 05Z6.** The composite of the projection onto the quotient of the affine line by
the punctured involution relation with the descended squaring map of Stacks 05VS is
universally closed.

The composite is, through
`AlgebraicGeometry.Space.toQuotientSheaf_comp_squaringMap_eq_conj`, the morphism of
represented presheaves induced by squaring of the coordinate. Squaring is an integral morphism
of schemes, hence a universally closed one, so the induced morphism of presheaves is
universally closed after every represented base change, and Stacks 03XD turns that into
universal closedness in the sense of Stacks 03HI. No assumption on the characteristic is
needed. -/
@[stacks 05Z6 "closed_squaring"]
theorem universallyClosed_toQuotientSheaf_comp_squaringMap (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    UniversallyClosed B (Spec (.of k)) hk
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
        squaringMap k B hk) := by
  have hA := isAlgebraicSpace_points_affineLine B k hk
  have hsq : AlgebraicGeometry.UniversallyClosed
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (affineLineChartSquare B k hk)) := by
    show AlgebraicGeometry.UniversallyClosed (affineLineSquare k).left
    infer_instance
  have hprop := presheaf_toQuotientSheaf_comp_squaringMap B k
    AlgebraicGeometry.universallyClosed_isStableUnderBaseChange hk hsq
  exact (presheaf_universallyClosed_iff B (Spec (.of k)) hk hA hA hprop.rep).mp hprop

/-- The composite of the projection onto the involution quotient with the descended squaring
map is surjective after every represented base change: it is the morphism of represented
presheaves induced by squaring of the coordinate, which is a surjective morphism of
schemes. -/
private theorem presheafSurjective_toQuotientSheaf_comp_squaringMap
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
        squaringMap k B hk) := by
  refine presheaf_toQuotientSheaf_comp_squaringMap B k inferInstance hk ?_
  show _root_.AlgebraicGeometry.Surjective (affineLineSquare k).left
  infer_instance

/-- Every base change of the descended squaring map `X ⟶ 𝐀¹_k` is surjective on points.

The composite of the quotient projection with the squaring map is surjective after every
represented base change, and that property is stable under base change, so the base change of
the composite along any morphism of presheaves is surjective on points by Stacks 03MD. The
base change of the composite factors through the base change of the squaring map, so the
latter is surjective too. -/
theorem isSurjective_pullback_fst_squaringMap (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]
    (Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (g : Z ⟶ Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)) :
    IsSurjective B (Spec (.of k)) hk (pullback.fst g (squaringMap k B hk)) := by
  set P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (Spec (.of k)) hk) with hP
  set q := Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
    (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) with hq
  let := MorphismProperty.relative_isStableUnderBaseChange P (F := yoneda)
  have hbc : P.presheaf (pullback.fst g (q ≫ squaringMap k B hk)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g (q ≫ squaringMap k B hk)).flip
      (presheafSurjective_toQuotientSheaf_comp_squaringMap B k hk)
  have hs : IsSurjective B (Spec (.of k)) hk
      (pullback.fst g (q ≫ squaringMap k B hk)) :=
    isSurjective_of_presheafSurjective B (Spec (.of k)) hk _ hbc
  obtain ⟨r, hrfst, -⟩ := exists_lift_pullback_comp B (Spec (.of k)) hk g q (squaringMap k B hk)
  have key : Function.Surjective
      (pointsMap B (Spec (.of k)) hk _ (pullback.fst g (squaringMap k B hk)) ∘
        pointsMap B (Spec (.of k)) hk _ r) := by
    rw [← pointsMap_comp, hrfst]
    exact hs
  exact Function.Surjective.of_comp key

/-- **The descended squaring map `X ⟶ 𝐀¹_k` is universally closed.**

The composite of the quotient projection with it is universally closed, and the quotient
projection is locally surjective for the fppf topology by
`Stacks.Groupoids.isLocallySurjective_toQuotientSheaf`, so
`AlgebraicGeometry.Space.universallyClosed_of_isLocallySurjective_comp` applies. No assumption
on the characteristic is needed, and neither is the algebraic-space property of the
quotient. -/
theorem universallyClosed_squaringMap (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    UniversallyClosed B (Spec (.of k)) hk (squaringMap k B hk) :=
  universallyClosed_of_isLocallySurjective_comp B (Spec (.of k)) hk _ _
    (universallyClosed_toQuotientSheaf_comp_squaringMap B k hk)
    (Stacks.Groupoids.isLocallySurjective_toQuotientSheaf
      (BigFppfOver.topology B (Spec (.of k)) hk)
      (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k))

/-- **Stacks 05ZI, the last sentence: there is a universal homeomorphism `X ⟶ 𝐀¹_k`, exhibited
directly by `t ↦ t ^ 2` on affine space.**

Here `X` is the quotient of the affine line by the relation identifying `t` with `-t` away from
the origin, the algebraic space of Stacks 05Z6, and the morphism is the one Stacks 05VS
descends from squaring the coordinate. It is universally closed by
`AlgebraicGeometry.Space.universallyClosed_squaringMap`, universally injective by Stacks 05VS
part (4), and surjective after every base change by
`AlgebraicGeometry.Space.isSurjective_pullback_fst_squaringMap`; the criterion is
`AlgebraicGeometry.Space.universalHomeomorphism_of_universallyClosed_of_universallyInjective`.

Stacks 05Z6 and Stacks 05ZI state this over an algebraically closed field of characteristic
zero. Only `2 ≠ 0` in `k` is used, and only for universal injectivity. -/
@[stacks 05Z6 "universal_homeomorphism: the map X ⟶ 𝐀¹_k is a universal homeomorphism",
  stacks 05ZI "the remark's own last sentence: there exists a universal homeomorphism \
X ⟶ 𝐀¹_k, exhibited directly by t ↦ t² on affine spaces. NOT asserted: that this X is the \
same as the quotient Y/G of the remark's alternative construction, that Y ⟶ X is a nontrivial \
connected finite étale covering, and that 𝐀¹_k has no nontrivial connected finite étale \
coverings"]
theorem universalHomeomorphism_squaringMap (hchar : (2 : k) ≠ 0)
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    UniversalHomeomorphism B (Spec (.of k)) hk (squaringMap k B hk) :=
  universalHomeomorphism_of_universallyClosed_of_universallyInjective B (Spec (.of k)) hk _
    (universallyClosed_squaringMap B k hk)
    (universallyInjective_squaringMap k hchar B hk)
    (isSurjective_pullback_fst_squaringMap B k hk)

end Squaring

end AlgebraicGeometry.Space

end
