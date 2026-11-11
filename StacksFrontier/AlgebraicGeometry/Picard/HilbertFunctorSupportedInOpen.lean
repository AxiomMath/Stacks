module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf

/-!
# The subfunctors of the Hilbert functor of points given by an open of the ambient scheme

Let `X` be a scheme over `S` and let `d` be a natural number. For an open `U ⊆ X` say that a
degree-`d` Hilbert family in `X` over `T` is *supported in* `U` when the closed subscheme it
cuts out of `X ×_S T` maps into `U`. This condition is stable under base change, so the families
supported in `U` form a subfunctor `Stacks.Hilbert.supportedIn X d U` of the degree-`d` Hilbert
functor.

Two properties of these subfunctors are proved. First, the locus in the base over which a given
family is supported in `U` is open, and a base change lands in the subfunctor exactly when its
image is contained in that locus. Second, if every `d`-tuple of points of a single fibre of
`X ⟶ S` lies in an affine open of `X`, then every Hilbert family over the spectrum of a field is
supported in an affine open. These are the two conditions (2)(b) and (2)(c) of the gluing
criterion used in the proof of Stacks Tag 0B9A; the second is the one in which the hypothesis of
that proposition is consumed.

## Main definitions

* `Stacks.Hilbert.familyProjection` — the projection `X ×_S T ⟶ X`.
* `Stacks.Hilbert.HilbertFamily.toAmbient` — the morphism from the closed subscheme cut out by a
  Hilbert family to the ambient scheme `X`.
* `Stacks.Hilbert.HilbertFamily.structural` — the morphism from that subscheme to the base `T`,
  over which it is finite locally free of rank `d`.
* `Stacks.Hilbert.HilbertFamily.SupportedIn` — a Hilbert family is supported in an open of `X`.
* `Stacks.Hilbert.HilbertFamily.baseChangeMap` — the morphism from the subscheme cut out by a
  base-changed family to the subscheme cut out by the original one.
* `Stacks.Hilbert.HilbertFamily.notSupportedLocus` — the locus in the base over which a family
  fails to be supported in a given open of `X`.
* `Stacks.Hilbert.supportedIn` — the subfunctor of the degree-`d` Hilbert functor consisting of
  the families supported in a given open of `X`.
* `Stacks.Hilbert.HilbertFamily.supportOpens` — the complementary open of the base, over which a
  family is supported in a given open of `X`, and `Stacks.Hilbert.HilbertFamily.supportScheme`,
  the corresponding open subscheme of the base, viewed as a scheme over `S`.
* `Stacks.Hilbert.HilbertFamily.supportLift` — the factorization of a morphism of the base
  through that open subscheme, available when the base change of the family along it is
  supported in the given open of `X`.
* `Stacks.Hilbert.supportedInPullback` — the pullback of the subfunctor along a Hilbert family:
  the functor of morphisms to the base along which the family restricts into the subfunctor.

## Main results

* `Stacks.Hilbert.HilbertFamily.SupportedIn.baseChange` — being supported in an open of `X` is
  stable under base change.
* `Stacks.Hilbert.HilbertFamily.isClosed_notSupportedLocus` — the locus over which a family is
  supported in an open of `X` is open.
* `Stacks.Hilbert.HilbertFamily.baseChange_supportedIn_iff` — **condition (2)(b) of the gluing
  criterion of Stacks Tag 0B9A, in set-theoretic form**: a base change lies in the subfunctor
  exactly when the image of the base-change morphism avoids that closed locus.
* `Stacks.Hilbert.representableBy_supportedInPullback` — **condition (2)(b) in the form the
  gluing criterion consumes**: the inclusion of the subfunctor into the degree-`d` Hilbert
  functor is representable by open immersions, the representing object of its pullback along a
  family being `Stacks.Hilbert.HilbertFamily.supportScheme`.
* `Stacks.Hilbert.exists_isAffineOpen_supportedIn_of_specField` — **condition (2)(c), the clause
  of Stacks Tag 0B9A that consumes its hypothesis**: under the affine-containment hypothesis of
  that proposition, every degree-`d` Hilbert family over the spectrum of a field is supported in
  an affine open of `X`.
* `Stacks.Hilbert.exists_isAffineOpen_mem_supportOpens` — **the covering condition in the form
  the gluing criterion consumes**: for a degree-`d` Hilbert family over any base, every point of
  the base lies in the open over which the family is supported in some affine open of `X`.

## Implementation notes

*What this file is.* The source proves Tag 0B9A by applying the
representability criterion of Stacks 01JJ to the subfunctors formed here, for `U` running over
the affine opens of `X` after a reduction to an affine base. That criterion has four conditions:
(1) the Hilbert functor is a Zariski sheaf; (2)(a) each subfunctor is representable; (2)(b) each
inclusion is representable by open immersions; and (2)(c) the subfunctors cover the field-valued
points of the Hilbert functor.

Conditions (2)(b) and (2)(c) are what is proved here, and (2)(c) is the one that uses the
hypothesis of Tag 0B9A. Condition (2)(b) is proved twice: in set-theoretic form, as the open
locus in the base together with the criterion for a base change to lie in the subfunctor stated
as a containment of images (`Stacks.Hilbert.HilbertFamily.baseChange_supportedIn_iff`), and then
in the form the criterion consumes, as relative representability of the inclusion by open
immersions (`Stacks.Hilbert.representableBy_supportedInPullback`).

Condition (1) is Stacks 0B95, which this development has in full as
`Stacks.Hilbert.isSheaf_fpqcTopology_hilbertFunctorOfRank`; the Zariski form the criterion asks
for is `Stacks.Hilbert.isSheaf_zariskiTopology_hilbertFunctorOfRank`, in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorZariskiSheaf.lean`.

*Why no representability is asserted here.* Condition (2)(a) for Tag 0B9A is representability of the
subfunctor of families supported in an affine open `U ⊆ X`. Stacks 0B99, which is
representability of the Hilbert functor of an affine scheme over an affine base, is available
unconditionally as `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine`;
what Tag 0B9A needs on top of it is the identification of the subfunctor of families supported
in `U` with the Hilbert functor of `U` itself, which consumes the source's footnote that a family
of `U_T` is closed in `X_T`. That identification is `Stacks.Hilbert.supportedInIsoOpenAmbient` in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorOpenAmbient.lean`, and it is available only
under the **set form** `AlgebraicGeometry.HasAffineFinitePointsInFibres` of the fibrewise
affineness hypothesis — an affine open around every finite set of points of a fibre — which is
strictly stronger than the `d`-tuple form Tag 0B9A assumes: the footnote needs `d + 1` points of
one fibre, and with the `d`-tuple form alone the identification is false (the doubled-origin
counterexample is recorded in the module docstring of that file). So condition (2)(a) under the
literal `d`-tuple form is **not** the composite of 0B99 with that identification, and in the
doubled-origin example the subfunctor `Stacks.Hilbert.supportedIn X d U` is a proper subfunctor
of the Hilbert functor of `U` which no scheme represents. Nothing in this file asserts that
`Stacks.Hilbert.hilbertFunctorOfRank` is representable.

Under the set form, by contrast, (2)(a) is exactly Stacks 0B99 for `U` affine composed with that
identification, and what separates the four conditions from the conclusion is only the assembly
through Stacks 01JJ. That assembly is
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_familiesClosedInAmbient` in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentable.lean`. Tag 0B9A itself, in
the corrected form recorded in `errata.md` (separatedness of `X ⟶ S` at `d = 1`, the source's
`d`-tuple hypothesis otherwise), is, in the namespace `Stacks.Hilbert`,
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_isSeparated` in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`, where the
identification is fed from separatedness of `X ⟶ S` instead of from the set form; that theorem
carries the `@[stacks 0B9A]` attribute, and no declaration in this file does, each being a step
of its proof.

The criterion itself is available: Mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` carries Tag 01JJ, for a
Zariski sheaf on the category of all schemes, and a presheaf on the schemes over `S` is carried
to that category by `Stacks.Sites.totalPresheaf` with
`Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf`. That is how the criterion is applied to
a functor of exactly this shape in the proof of Tag 0BL4,
`Stacks.Morphisms.homFromFiniteLocallyFree_isRepresentable`, whose hypothesis on `X ⟶ S` is the
one of Tag 0B9A with `d` points replaced by a finite set of points. That route also makes the
reduction to an affine base of Stacks 01LG, which no declaration in this development carries,
unnecessary: the charts can be indexed by pairs of an affine open of `S` and an affine open of
`X` above it, as they are for Tag 0BL4.

*Why the non-support locus is closed.* The subscheme cut out by a degree-`d` Hilbert family is
finite over the base, because finite locally free implies finite by
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation` (Stacks
02KB), and a finite morphism of schemes is a closed map. The part of the subscheme lying outside
`U` is closed, so its image in the base is closed. The criterion for a base change to be
supported in `U` is then read off the cartesian square
`Stacks.Hilbert.HilbertFamily.isPullback_baseChangeMap`, which is
`Stacks.Hilbert.isPullback_familyBaseChangeMap_subschemeι` restated for the named structure
morphisms.

*Why the bound on the number of points holds.* The subscheme cut out by a degree-`d` family over
the spectrum of a field is finite locally free of rank `d` over that field, hence has at most `d`
points, by `AlgebraicGeometry.cardinalMk_pullback_le_of_degree_le` applied to the identity base
change. Its images in `X` therefore form a set admitting a surjection from `Fin d`, obtained by
inverting an embedding into `Fin d`; and all those images lie in one fibre of `X ⟶ S` because
the spectrum of a field has exactly one point. When the subscheme is empty the empty affine open
`AlgebraicGeometry.isAffineOpen_bot` supports the family and the hypothesis is not needed; this
is why no positivity assumption on `d` appears.

*How "supported in" is recorded.* A Hilbert family is recorded by its ideal sheaf, so the
condition is stated on the points of the closed subscheme cut out by that ideal sheaf, as a
pointwise membership rather than as a factorization of a morphism through the open subscheme.
This makes stability under base change a consequence of one identity of morphisms,
`Stacks.Hilbert.HilbertFamily.baseChange_toAmbient`.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B95](https://stacks.math.columbia.edu/tag/0B95)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01LG](https://stacks.math.columbia.edu/tag/01LG)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-! ### Families supported in an open of the ambient scheme -/

/-- The projection `X ×_S T ⟶ X`. -/
def familyProjection {S : Scheme.{u}} (X T : Over S) :
    ((Over.pullback T.hom).obj X).left ⟶ X.left :=
  pullback.fst X.hom T.hom

/-- The projection `X ×_S T ⟶ X` followed by `X ⟶ S` is the structure morphism of `X ×_S T`
followed by `T ⟶ S`. -/
theorem familyProjection_comp {S : Scheme.{u}} (X T : Over S) :
    familyProjection X T ≫ X.hom = ((Over.pullback T.hom).obj X).hom ≫ T.hom :=
  pullback.condition

/-- The comparison map `X ×_S T' ⟶ X ×_S T` is compatible with the projections to `X`. -/
theorem familyBaseChangeMap_comp_familyProjection {S : Scheme.{u}} (X : Over S) {T' T : Over S}
    (g : T' ⟶ T) :
    familyBaseChangeMap X g ≫ familyProjection X T = familyProjection X T' := by
  simp only [familyBaseChangeMap, familyProjection, pullback.map, pullback.lift_fst,
    Category.comp_id]

/-- The morphism to the ambient scheme `X` from the closed subscheme of `X ×_S T` cut out by a
degree-`d` Hilbert family. -/
def HilbertFamily.toAmbient {S : Scheme.{u}} {X T : Over S} {d : ℕ} (Z : HilbertFamily X T d) :
    Z.ideal.subscheme ⟶ X.left :=
  Z.ideal.subschemeι ≫ familyProjection X T

/-- A degree-`d` Hilbert family in `X` over `T` is *supported in* an open `U ⊆ X` when every
point of the closed subscheme it cuts out of `X ×_S T` maps into `U`. -/
def HilbertFamily.SupportedIn {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) : Prop :=
  ∀ z : Z.ideal.subscheme, Z.toAmbient z ∈ U

/-! ### Stability under base change -/

/-- The morphism from the closed subscheme cut out by a base-changed degree-`d` Hilbert family to
the one cut out by the original family: the two are related by a cartesian square over
`T' ⟶ T`, and this is its horizontal top edge. -/
def HilbertFamily.baseChangeMap {S : Scheme.{u}} {X : Over S} {T' T : Over S} {d : ℕ}
    (g : T' ⟶ T) (Z : HilbertFamily X T d) :
    (baseChange X g Z).ideal.subscheme ⟶ Z.ideal.subscheme :=
  (Z.ideal.comapIso (familyBaseChangeMap X g)).hom ≫
    pullback.snd (familyBaseChangeMap X g) Z.ideal.subschemeι

/-- The comparison square: the subscheme cut out by a base-changed degree-`d` Hilbert family
sits over the subscheme cut out by the original family. -/
theorem HilbertFamily.baseChangeMap_comp_subschemeι {S : Scheme.{u}} {X : Over S}
    {T' T : Over S} {d : ℕ} (g : T' ⟶ T) (Z : HilbertFamily X T d) :
    (baseChange X g Z).ideal.subschemeι ≫ familyBaseChangeMap X g =
      Z.baseChangeMap g ≫ Z.ideal.subschemeι := by
  change (Z.ideal.comap (familyBaseChangeMap X g)).subschemeι ≫ familyBaseChangeMap X g =
    ((Z.ideal.comapIso (familyBaseChangeMap X g)).hom ≫
      pullback.snd (familyBaseChangeMap X g) Z.ideal.subschemeι) ≫ Z.ideal.subschemeι
  rw [← Scheme.IdealSheafData.comapIso_hom_fst Z.ideal (familyBaseChangeMap X g),
    Category.assoc, Category.assoc, pullback.condition]

/-- The ambient projection of a base-changed degree-`d` Hilbert family factors through the
ambient projection of the original family. -/
theorem HilbertFamily.baseChange_toAmbient {S : Scheme.{u}} {X : Over S} {T' T : Over S} {d : ℕ}
    (g : T' ⟶ T) (Z : HilbertFamily X T d) :
    (baseChange X g Z).toAmbient = Z.baseChangeMap g ≫ Z.toAmbient := by
  rw [HilbertFamily.toAmbient, HilbertFamily.toAmbient,
    ← familyBaseChangeMap_comp_familyProjection X g,
    ← Category.assoc ((baseChange X g Z).ideal.subschemeι),
    HilbertFamily.baseChangeMap_comp_subschemeι, Category.assoc]

/-- Being supported in an open of `X` is stable under base change. -/
theorem HilbertFamily.SupportedIn.baseChange {S : Scheme.{u}} {X : Over S} {T' T : Over S}
    {d : ℕ} {Z : HilbertFamily X T d} {U : X.left.Opens} (h : Z.SupportedIn U) (g : T' ⟶ T) :
    (Stacks.Hilbert.baseChange X g Z).SupportedIn U := by
  intro z
  simpa [HilbertFamily.baseChange_toAmbient] using h _

/-- The subfunctor of the degree-`d` Hilbert functor of points of `X` over `S` consisting of the
families supported in an open `U ⊆ X`. -/
def supportedIn {S : Scheme.{u}} (X : Over S) (d : ℕ) (U : X.left.Opens) :
    Subfunctor (hilbertFunctorOfRank X d) where
  obj _ := {Z | Z.SupportedIn U}
  map _ _ hZ := hZ.baseChange _

/-- A degree-`d` Hilbert family lies in `Stacks.Hilbert.supportedIn X d U` exactly when it is
supported in `U`. -/
@[simp]
theorem mem_supportedIn_obj {S : Scheme.{u}} {X : Over S} {d : ℕ} {U : X.left.Opens}
    {T : (Over S)ᵒᵖ} {Z : HilbertFamily X T.unop d} :
    Z ∈ (supportedIn X d U).obj T ↔ Z.SupportedIn U :=
  Iff.rfl

/-! ### The locus in the base over which a family is supported in an open -/

/-- The structure morphism of the closed subscheme cut out by a degree-`d` Hilbert family: the
morphism to `T` over which that subscheme is finite locally free of rank `d`. -/
def HilbertFamily.structural {S : Scheme.{u}} {X T : Over S} {d : ℕ} (Z : HilbertFamily X T d) :
    Z.ideal.subscheme ⟶ T.left :=
  Z.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom

/-- The structure morphism of the subscheme cut out by a degree-`d` Hilbert family is finite
locally free of rank `d`. This is the defining property of a Hilbert family, repackaged for the
named structure morphism. -/
instance HilbertFamily.isFiniteLocallyFreeOfRank_structural {S : Scheme.{u}} {X T : Over S}
    {d : ℕ} (Z : HilbertFamily X T d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank Z.structural d :=
  Z.isFiniteLocallyFreeOfRank

/-- The structure morphism of the subscheme cut out by a degree-`d` Hilbert family is finite. -/
instance HilbertFamily.isFinite_structural {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) : IsFinite Z.structural :=
  ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    Z.structural).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Z.structural d)).1

/-- The locus in `T` over which a degree-`d` Hilbert family fails to be supported in an open
`U ⊆ X`: the image in `T` of the points of the subscheme cut out by the family whose image in
`X` lies outside `U`. -/
def HilbertFamily.notSupportedLocus {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) : Set T.left :=
  Z.structural.base '' {z | Z.toAmbient z ∉ U}

/-- **The locus over which a Hilbert family is supported in an open is open**, stated as the
closedness of its complement `Stacks.Hilbert.HilbertFamily.notSupportedLocus`. The subscheme cut
out by a degree-`d` Hilbert family is finite over `T`, hence maps closed sets to closed sets, and
the part of it lying outside `U` is closed. -/
theorem HilbertFamily.isClosed_notSupportedLocus {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) : IsClosed (Z.notSupportedLocus U) :=
  Z.structural.isClosedMap _ (U.2.preimage Z.toAmbient.continuous).isClosed_compl

/-- A degree-`d` Hilbert family is supported in `U` exactly when its non-support locus in the
base is empty. -/
theorem HilbertFamily.supportedIn_iff_notSupportedLocus_eq_empty {S : Scheme.{u}}
    {X T : Over S} {d : ℕ} (Z : HilbertFamily X T d) (U : X.left.Opens) :
    Z.SupportedIn U ↔ Z.notSupportedLocus U = ∅ := by
  rw [HilbertFamily.notSupportedLocus, Set.image_eq_empty, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h z hz => hz (h z), fun h z => not_not.mp (h z)⟩

/-- The comparison square between the subschemes cut out by a degree-`d` Hilbert family and by
its base change is cartesian over `T' ⟶ T`. -/
theorem HilbertFamily.isPullback_baseChangeMap {S : Scheme.{u}} {X : Over S} {T' T : Over S}
    {d : ℕ} (g : T' ⟶ T) (Z : HilbertFamily X T d) :
    IsPullback (Z.baseChangeMap g) (baseChange X g Z).structural Z.structural g.left :=
  isPullback_familyBaseChangeMap_subschemeι X g Z.ideal

/-- **Condition (2)(b) of the gluing criterion in the proof of Stacks Tag 0B9A.** A base change of a
degree-`d` Hilbert family is supported in an open `U ⊆ X` exactly when the base change misses
the non-support locus of the original family — a closed subset of `T` by
`Stacks.Hilbert.HilbertFamily.isClosed_notSupportedLocus`. -/
theorem HilbertFamily.baseChange_supportedIn_iff {S : Scheme.{u}} {X : Over S} {T' T : Over S}
    {d : ℕ} (g : T' ⟶ T) (Z : HilbertFamily X T d) (U : X.left.Opens) :
    (baseChange X g Z).SupportedIn U ↔ ∀ t : T'.left, g.left t ∉ Z.notSupportedLocus U := by
  constructor
  · intro h t ⟨z, hz, hzt⟩
    obtain ⟨w, hw, -⟩ :=
      Scheme.exists_preimage_of_isPullback (Z.isPullback_baseChangeMap g) z t hzt
    subst hw
    exact hz (by simpa [HilbertFamily.baseChange_toAmbient] using h w)
  · intro h w
    by_contra hw
    refine h ((baseChange X g Z).structural w) ⟨Z.baseChangeMap g w, ?_, ?_⟩
    · simpa [HilbertFamily.baseChange_toAmbient] using hw
    · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        (Z.isPullback_baseChangeMap g).w]

/-! ### The inclusion of the subfunctor is representable by open immersions -/

/-- The open of the base over which a degree-`d` Hilbert family is supported in an open
`U ⊆ X`: the complement of `Stacks.Hilbert.HilbertFamily.notSupportedLocus`, which is closed by
`Stacks.Hilbert.HilbertFamily.isClosed_notSupportedLocus`. -/
def HilbertFamily.supportOpens {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) : T.left.Opens :=
  ⟨(Z.notSupportedLocus U)ᶜ, (Z.isClosed_notSupportedLocus U).isOpen_compl⟩

/-- A point of the base lies in `Stacks.Hilbert.HilbertFamily.supportOpens` exactly when it is
not in the non-support locus. -/
@[simp]
theorem HilbertFamily.mem_supportOpens {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    {Z : HilbertFamily X T d} {U : X.left.Opens} {t : T.left} :
    t ∈ Z.supportOpens U ↔ t ∉ Z.notSupportedLocus U :=
  Iff.rfl

/-- The open subscheme of the base cut out by `Stacks.Hilbert.HilbertFamily.supportOpens`,
viewed as a scheme over `S`. -/
def HilbertFamily.supportScheme {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) : Over S :=
  Over.mk ((Z.supportOpens U).ι ≫ T.hom)

/-- The underlying scheme of `Stacks.Hilbert.HilbertFamily.supportScheme` is the open subscheme
`Stacks.Hilbert.HilbertFamily.supportOpens` of the base. -/
@[simp]
theorem HilbertFamily.supportScheme_left {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) :
    (Z.supportScheme U).left = (Z.supportOpens U).toScheme :=
  rfl

/-- The open immersion of `Stacks.Hilbert.HilbertFamily.supportScheme` into the base. -/
def HilbertFamily.supportSchemeι {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) : Z.supportScheme U ⟶ T :=
  Over.homMk (Z.supportOpens U).ι rfl

/-- The underlying morphism of `Stacks.Hilbert.HilbertFamily.supportSchemeι` is the inclusion of
the open subscheme `Stacks.Hilbert.HilbertFamily.supportOpens`. -/
@[simp]
theorem HilbertFamily.supportSchemeι_left {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) :
    (Z.supportSchemeι U).left = (Z.supportOpens U).ι :=
  rfl

/-- The inclusion of `Stacks.Hilbert.HilbertFamily.supportScheme` into the base is an open
immersion. -/
instance HilbertFamily.isOpenImmersion_supportSchemeι {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) :
    IsOpenImmersion (Z.supportSchemeι U).left :=
  inferInstanceAs (IsOpenImmersion (Z.supportOpens U).ι)

/-- The inclusion of `Stacks.Hilbert.HilbertFamily.supportScheme` into the base is a
monomorphism of schemes over `S`. -/
instance HilbertFamily.mono_supportSchemeι {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) : Mono (Z.supportSchemeι U) :=
  (Over.forget S).mono_of_mono_map
    (inferInstanceAs (Mono (Z.supportSchemeι U).left))

/-- A base change of a degree-`d` Hilbert family is supported in an open `U ⊆ X` exactly when
the base-change morphism lands in `Stacks.Hilbert.HilbertFamily.supportOpens`. -/
theorem HilbertFamily.baseChange_supportedIn_iff_range_subset {S : Scheme.{u}} {X : Over S}
    {T' T : Over S} {d : ℕ} (g : T' ⟶ T) (Z : HilbertFamily X T d) (U : X.left.Opens) :
    (baseChange X g Z).SupportedIn U ↔
      Set.range g.left.base ⊆ (Z.supportOpens U : Set T.left) := by
  rw [Z.baseChange_supportedIn_iff g U]
  exact ⟨fun h _ ⟨t, ht⟩ => ht ▸ h t, fun h t => h ⟨t, rfl⟩⟩

/-- The universal family over `Stacks.Hilbert.HilbertFamily.supportScheme` is supported in
`U`. -/
theorem HilbertFamily.supportedIn_baseChange_supportSchemeι {S : Scheme.{u}} {X T : Over S}
    {d : ℕ} (Z : HilbertFamily X T d) (U : X.left.Opens) :
    (baseChange X (Z.supportSchemeι U) Z).SupportedIn U := by
  rw [HilbertFamily.baseChange_supportedIn_iff_range_subset]
  exact (Z.supportOpens U).range_ι.le

/-- The underlying morphism of schemes of `Stacks.Hilbert.HilbertFamily.supportLift`. -/
def HilbertFamily.supportLiftLeft {S : Scheme.{u}} {X : Over S} {T' T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) {U : X.left.Opens} {g : T' ⟶ T}
    (hg : (baseChange X g Z).SupportedIn U) : T'.left ⟶ (Z.supportOpens U).toScheme :=
  IsOpenImmersion.lift (Z.supportOpens U).ι g.left (by
    rw [Scheme.Opens.range_ι]
    exact (HilbertFamily.baseChange_supportedIn_iff_range_subset g Z U).1 hg)

/-- `Stacks.Hilbert.HilbertFamily.supportLiftLeft` followed by the inclusion of the open
subscheme is the given morphism of the base. -/
@[simp]
theorem HilbertFamily.supportLiftLeft_comp {S : Scheme.{u}} {X : Over S} {T' T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) {U : X.left.Opens} {g : T' ⟶ T}
    (hg : (baseChange X g Z).SupportedIn U) :
    Z.supportLiftLeft hg ≫ (Z.supportOpens U).ι = g.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization of a morphism of the base through
`Stacks.Hilbert.HilbertFamily.supportScheme` available when the base change of the family along
it is supported in `U`. -/
def HilbertFamily.supportLift {S : Scheme.{u}} {X : Over S} {T' T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) {U : X.left.Opens} {g : T' ⟶ T}
    (hg : (baseChange X g Z).SupportedIn U) : T' ⟶ Z.supportScheme U :=
  Over.homMk (Z.supportLiftLeft hg) (by
    change _ ≫ (Z.supportOpens U).ι ≫ T.hom = T'.hom
    rw [← Category.assoc, HilbertFamily.supportLiftLeft_comp]
    exact Over.w g)

/-- `Stacks.Hilbert.HilbertFamily.supportLift` is a factorization of the given morphism. -/
@[simp]
theorem HilbertFamily.supportLift_comp {S : Scheme.{u}} {X : Over S} {T' T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) {U : X.left.Opens} {g : T' ⟶ T}
    (hg : (baseChange X g Z).SupportedIn U) :
    Z.supportLift hg ≫ Z.supportSchemeι U = g :=
  Over.OverMorphism.ext (Z.supportLiftLeft_comp hg)

/-- The factorization through `Stacks.Hilbert.HilbertFamily.supportScheme` is unique, its
inclusion into the base being an open immersion and hence a monomorphism. -/
theorem HilbertFamily.eq_supportLift {S : Scheme.{u}} {X : Over S} {T' T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) {U : X.left.Opens} {g : T' ⟶ T}
    (hg : (baseChange X g Z).SupportedIn U) {h : T' ⟶ Z.supportScheme U}
    (hh : h ≫ Z.supportSchemeι U = g) : h = Z.supportLift hg :=
  (cancel_mono (Z.supportSchemeι U)).1 (hh.trans (Z.supportLift_comp hg).symm)

/-- **The subfunctor of the degree-`d` Hilbert functor pulled back along a family.** For a
degree-`d` Hilbert family `Z` in `X` over `T`, this sends an `S`-scheme `W` to the morphisms
`W ⟶ T` along which `Z` pulls back to a family supported in `U` — that is, to the fibre product
of the subfunctor `Stacks.Hilbert.supportedIn X d U` with the functor of points of `T` over the
degree-`d` Hilbert functor, taken along `Z`. -/
def supportedInPullback {S : Scheme.{u}} {X T : Over S} {d : ℕ} (Z : HilbertFamily X T d)
    (U : X.left.Opens) : (Over S)ᵒᵖ ⥤ Type u where
  obj W := {g : W.unop ⟶ T // (baseChange X g Z).SupportedIn U}
  map h := ↾fun g => ⟨h.unop ≫ g.1, by
    rw [baseChange_comp]
    exact g.2.baseChange _⟩
  map_id _ := ConcreteCategory.hom_ext _ _ fun g => Subtype.ext (Category.id_comp g.1)
  map_comp _ _ := ConcreteCategory.hom_ext _ _ fun g => Subtype.ext (Category.assoc _ _ _)

/-- An element of `Stacks.Hilbert.supportedInPullback` is exactly a morphism to the base whose
restriction of the given family lies in the subfunctor `Stacks.Hilbert.supportedIn`. -/
theorem mem_supportedInPullback_iff {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    {Z : HilbertFamily X T d} {U : X.left.Opens} {W : (Over S)ᵒᵖ} (g : W.unop ⟶ T) :
    (∃ h : (supportedInPullback Z U).obj W, h.1 = g) ↔
      (hilbertFunctorOfRank X d).map g.op Z ∈ (supportedIn X d U).obj W :=
  ⟨fun ⟨h, hh⟩ => hh ▸ h.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

/-- **The inclusion of the subfunctor of families supported in an open `U ⊆ X` into the
degree-`d` Hilbert functor is representable by open immersions.** Pulled back along a degree-`d`
Hilbert family `Z` over an `S`-scheme `T`, it is represented by the open subscheme
`Stacks.Hilbert.HilbertFamily.supportScheme` of `T`, whose inclusion into `T` is an open
immersion by `Stacks.Hilbert.HilbertFamily.isOpenImmersion_supportSchemeι`.

Concretely, a morphism `g : W ⟶ T` of `S`-schemes pulls `Z` back into the subfunctor exactly
when it factors through that open subscheme, and the factorization is unique.

This is condition (2)(b) of the representability criterion of Stacks 01JJ, in the form that
criterion consumes, for the subfunctors that the source's proof of Stacks Tag 0B9A glues. -/
def representableBy_supportedInPullback {S : Scheme.{u}} {X T : Over S} {d : ℕ}
    (Z : HilbertFamily X T d) (U : X.left.Opens) :
    (supportedInPullback Z U).RepresentableBy (Z.supportScheme U) where
  homEquiv {W} :=
    show (W ⟶ Z.supportScheme U) ≃ {g : W ⟶ T // (baseChange X g Z).SupportedIn U} from
    { toFun := fun h => ⟨h ≫ Z.supportSchemeι U, by
        rw [baseChange_comp]
        exact (Z.supportedIn_baseChange_supportSchemeι U).baseChange h⟩
      invFun := fun g => Z.supportLift g.2
      left_inv := fun h => (Z.eq_supportLift _ rfl).symm
      right_inv := fun g => Subtype.ext (Z.supportLift_comp g.2) }
  homEquiv_comp f h := Subtype.ext (Category.assoc f h (Z.supportSchemeι U))

/-! ### The affine opens support the field-valued points -/

/-- A scheme finite locally free of rank `d` over the spectrum of a field has at most `d`
points. -/
private theorem cardinalMk_le_of_isFiniteLocallyFreeOfRank (k : Type u) [Field k]
    {Z : Scheme.{u}} (d : ℕ) (p : Z ⟶ Spec (CommRingCat.of k))
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank p d] : Cardinal.mk Z ≤ d := by
  have key := cardinalMk_pullback_le_of_degree_le p d
    (fun k' _ g => ⟨d, le_rfl, Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback g p).flip⟩) k (𝟙 _)
  have hsq : IsPullback p (𝟙 Z) (𝟙 (Spec (CommRingCat.of k))) p := IsPullback.of_id_snd
  exact (Cardinal.mk_congr (Equiv.ofBijective _
    (ConcreteCategory.bijective_of_isIso hsq.isoPullback.hom.base))).trans_le key

/-- **Condition (2)(c) of the gluing criterion in the proof of Stacks Tag 0B9A.** Let `X ⟶ S` be a
morphism of schemes and let `d` be a natural number such that any `d` points of `X` lying in a
single fibre of `X ⟶ S` are contained in an affine open of `X`. Then every degree-`d` Hilbert
family in `X` over the spectrum of a field is supported in an affine open of `X`.

The closed subscheme cut out by the family is finite locally free of rank `d` over the field, so
it has at most `d` points; all of their images in `X` lie in one fibre, because the spectrum of a
field has one point; so the hypothesis produces an affine open containing them all. -/
theorem exists_isAffineOpen_supportedIn_of_specField {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ S)
    (Z : HilbertFamily X (Over.mk g) d) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ Z.SupportedIn U := by
  have : Subsingleton ((Over.mk g).left : Type u) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k) : Type u))
  have hcomm : ∀ z, X.hom (Z.toAmbient z) = g (Z.structural z) := by
    intro z
    simp only [HilbertFamily.toAmbient, HilbertFamily.structural, ← Scheme.Hom.comp_apply,
      Category.assoc, familyProjection_comp]
    rfl
  rcases isEmpty_or_nonempty Z.ideal.subscheme with he | hne
  · exact ⟨⊥, isAffineOpen_bot _, he.elim⟩
  obtain ⟨e⟩ := (Cardinal.lift_mk_le'.{u, 0} (α := Z.ideal.subscheme) (β := Fin d)).mp
    (by simpa using cardinalMk_le_of_isFiniteLocallyFreeOfRank k d Z.structural)
  obtain ⟨U, hU, hmem⟩ := hX (g (Z.structural hne.some))
    (fun i => Z.toAmbient (Function.invFun e i)) fun i => by
      rw [hcomm]
      exact congrArg _ (Subsingleton.elim _ _)
  exact ⟨U, hU, fun z => by simpa only [Function.leftInverse_invFun e.injective z] using hmem (e z)⟩

/-- **Condition (2)(c) of the gluing criterion in the proof of Stacks Tag 0B9A,** in the language of
subfunctors: under the affine-containment hypothesis of that proposition, every field-valued
point of the degree-`d` Hilbert functor of `X` lies in the subfunctor of families supported in
some affine open of `X`. -/
theorem exists_isAffineOpen_mem_supportedIn_of_specField {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ S)
    (Z : (hilbertFunctorOfRank X d).obj (Opposite.op (Over.mk g))) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      Z ∈ (supportedIn X d U).obj (Opposite.op (Over.mk g)) :=
  exists_isAffineOpen_supportedIn_of_specField X d hX k g Z

/-- **The opens of the base over which a given degree-`d` Hilbert family is supported in an
affine open of `X` cover the base,** under the affine-containment hypothesis on the fibres of
`X ⟶ S`.

The source proves the covering condition by reducing it to the case of the spectrum of a field,
which is `Stacks.Hilbert.exists_isAffineOpen_supportedIn_of_specField`; this is that reduction,
run backwards. The family is base changed to the residue field of the point, which produces an
affine open supporting it there, and the point then lies in the corresponding open of the base
because the base change misses the non-support locus.

This is condition (2)(c) of the representability criterion of Stacks 01JJ in the form that
criterion consumes, for the subfunctors that the source's proof of Stacks Tag 0B9A glues. -/
theorem exists_isAffineOpen_mem_supportOpens {S : Scheme.{u}} (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    {T : Over S} (Z : HilbertFamily X T d) (t : T.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ t ∈ Z.supportOpens U := by
  let κ : Type u := T.left.residueField t
  let ι : Spec (CommRingCat.of κ) ⟶ T.left := T.left.fromSpecResidueField t
  let m : Over.mk (ι ≫ T.hom) ⟶ T := Over.homMk ι rfl
  obtain ⟨U, hU, hsupp⟩ :=
    exists_isAffineOpen_supportedIn_of_specField X d hX κ (ι ≫ T.hom) (baseChange X m Z)
  refine ⟨U, hU, ?_⟩
  have h := (Z.baseChange_supportedIn_iff m U).1 hsupp (default : Spec (CommRingCat.of κ))
  rwa [show m.left (default : Spec (CommRingCat.of κ)) = t from
    T.left.fromSpecResidueField_apply t _] at h

end Stacks.Hilbert

end
