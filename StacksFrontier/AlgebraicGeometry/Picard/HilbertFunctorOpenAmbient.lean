module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeDoubledLine
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGroupSchemeQuotient

/-!
# The subfunctor of families supported in an open is the Hilbert functor of that open

Let `X` be a scheme over `S`, let `U ⊆ X` be an open and let `d` be a natural number. A
degree-`d` Hilbert family in `X` over `T` supported in `U` is "the same thing as" a degree-`d`
Hilbert family in `U` over `T`. This file proves exactly that, as a bijection natural in `T`,
and hence as an isomorphism of functors on `(Over S)ᵒᵖ`.

This is the identification `F_U = Hilb^d_{U/S}` to which condition (2)(a) of the gluing
criterion in the proof of Stacks Tag 0B9A is reduced.

## Main definitions

* `Stacks.Hilbert.openAmbient` — an open of `X` viewed as a scheme over `S`, and
  `Stacks.Hilbert.openAmbientι` its inclusion into `X` over `S`.
* `Stacks.Hilbert.openAmbientMap` — the induced open immersion `U ×_S T ⟶ X ×_S T`.
* `Stacks.Hilbert.HilbertFamily.restrictToOpenAmbient` — the degree-`d` Hilbert family in `U`
  obtained from a degree-`d` Hilbert family in `X` supported in `U`, by restricting its ideal
  sheaf to `U ×_S T`.
* `Stacks.Hilbert.HilbertFamily.extendToAmbient` — the degree-`d` Hilbert family in `X` obtained
  from a degree-`d` Hilbert family in `U`, by pushing its ideal sheaf forward along
  `U ×_S T ⟶ X ×_S T`.
* `Stacks.Hilbert.supportedInEquivOpenAmbient` — the resulting bijection.
* `Stacks.Hilbert.supportedInIsoOpenAmbient` — the resulting isomorphism of functors.

## Main results

* `Stacks.Hilbert.isPullback_familyAmbientMap` — the square relating `Y ×_S T ⟶ X ×_S T` to
  `Y ⟶ X` through the projections to `X` and `Y` is cartesian; and
  `Stacks.Hilbert.opensRange_familyAmbientMap`, the open image of `Y ×_S T ⟶ X ×_S T` for an
  open immersion `Y ⟶ X`, the opens form of `Stacks.Hilbert.range_familyAmbientMap`.
* `Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism` — **the footnote to the
  proof of Stacks Tag 0B9A**: a morphism to `X ×_S T` whose composite with the projection to `T`
  is finite has closed image, provided every point of `X ×_S T` has an affine open of `X`
  containing its image and the images of the points of the source lying over the same point of
  `T`. Its two sufficient conditions are `…_of_hasAffineFinitePointsInFibres` — every finite set
  of points of a fibre of `X ⟶ S` lies in an affine open of `X` — and
  `Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism_of_isSeparated`, which asks
  nothing of the fibres.
* `Stacks.Hilbert.isClosedImmersion_subschemeι_comp_openAmbientMap` — consequently the closed
  subscheme cut out by a degree-`d` Hilbert family in `U` over `T` is a *closed* subscheme of
  `X ×_S T`, which is what the footnote is for. That statement, for every open and every base,
  is `Stacks.Hilbert.FamiliesClosedInAmbient`, the hypothesis under which the identification
  below is proved; it holds under the set form of the fibrewise affineness hypothesis
  (`Stacks.Hilbert.familiesClosedInAmbient_of_hasAffineFinitePointsInFibres`) and for a separated
  `X ⟶ S` (`Stacks.Hilbert.familiesClosedInAmbient_of_isSeparated`).
* `Stacks.Hilbert.supportedInEquivOpenAmbient_naturality` — the bijection commutes with base
  change of `T`, so `Stacks.Hilbert.supportedInIsoOpenAmbient` is an isomorphism of functors.

## Implementation notes

*What this is for, and what it is not.* The source proves Tag 0B9A by applying the
representability criterion of Stacks 01JJ to the subfunctors `F_U` of families supported in an
affine open `U ⊆ X`. Condition (2)(a) of that criterion asks each `F_U` to be representable, and
the source discharges it by identifying `F_U` with `Hilb^d_{U/S}` and invoking the affine case,
Stacks 0B99. This file is the identification. The affine case is available unconditionally, as
`Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine`, but **no
declaration here carries the `@[stacks 0B9A]` attribute**: an identification of two functors is
an input to condition (2)(a), not the condition itself, and still less the proposition. The tag
is registered on
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`
in `StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`. See
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorAffineRepresentableUnconditional.lean` for
Stacks 0B99, and the module docstring of
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorSupportedInOpen.lean` for the conditions of
the criterion that are available.

*Which direction is formal, and which is the footnote.* Restricting a family supported in `U` to
`U ×_S T` is formal: the open immersion `j : U ×_S T ⟶ X ×_S T` has image the preimage of `U`
under the projection `X ×_S T ⟶ X`, so a family supported in `U` has its subscheme inside the
image of `j`, the base change of `j` along that subscheme's inclusion is a surjective open
immersion hence an isomorphism, and the pulled-back ideal sheaf therefore cuts out the same
subscheme.

The other direction is the content of the source's footnote: given a family `Z ⊆ U ×_S T`, the
composite `Z ⟶ U ×_S T ⟶ X ×_S T` is an immersion, and it has to be a *closed* immersion for
its kernel to cut out `Z` again. That is `Stacks.Hilbert.FamiliesClosedInAmbient`, the hypothesis
carried by everything in the second half of this file. It is where an assumption on `X ⟶ S` is
consumed a second time — the first being condition (2)(c) — and, as explained below, the
fibrewise affineness assumption discharges it only in a form **strictly stronger** than the one
Tag 0B9A assumes, while separatedness of `X ⟶ S` discharges it outright. The source's argument,
reproduced in
`Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism`, is: given `x` in the closure
of the image and `t` its image in `T`, the hypothesis yields an affine open `U' ⊆ X` containing
the image of `x` and the images of the finitely many points of `Z` over `t`; the preimage `W` of
`U'` in `X ×_S T` is then an open containing `x` whose structure morphism to `T` is separated,
being a base change of the morphism `U' ⟶ S` out of an *affine*, hence separated, scheme;
shrinking the base to the open `T'` over which all of `Z` lands in `W` — open because `Z ⟶ T` is
a closed map — the restriction of `Z` is universally closed over `T'` and maps into an open of
`X ×_S T` separated over `T'`, so its image there is closed by Stacks 01W6
(`AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated`). Closedness of a set is local on
an open cover and `x` was arbitrary, so the image is closed.

*Why the fibrewise affineness hypothesis is taken in its set form, and why that is a real
strengthening.* The footnote needs an affine open containing the points of the fibre of `Z` over
`t` — at most `d` of them — **and** the extra point `x`, i.e. up to `d + 1` points of one fibre
of `X ⟶ S`. So the form of the hypothesis that discharges
`Stacks.Hilbert.FamiliesClosedInAmbient` here is
`AlgebraicGeometry.HasAffineFinitePointsInFibres X.hom`, which asks for an affine open around
every *finite* set of points of a fibre, rather than the `d`-tuple form in which Tag 0B9A states
its hypothesis.

The set form does **not** follow from the `d`-tuple form, and the gap is not a technicality: the
statements proved in this file are *false* under the `d`-tuple form alone. Take `d = 1`, let `X`
be the affine line with the origin doubled over `S = Spec k` and let `U` be one of its two
standard affine-line charts. The `1`-tuple form of the hypothesis is vacuous — every single
point of a scheme lies in an affine open — while the set form fails for `X`, the two origins
lying in no common affine open. Let `T` be the affine line and let `W` be the diagonal of
`U ×_S T`, a closed subscheme isomorphic to `T`, hence a degree-`1` Hilbert family in `U`. Its
image in `X ×_S T` is not closed: in the other chart it reads `{(y, u) : y = u ≠ 0}`, whose
closure adds the point `(0', 0)` lying over the second origin. So
`Stacks.Hilbert.isClosedImmersion_subschemeι_comp_openAmbientMap`, and with it
`Stacks.Hilbert.supportedInEquivOpenAmbient` and
`Stacks.Hilbert.supportedInIsoOpenAmbient`, fail with the hypothesis weakened to the `d`-tuple
form; and no derivation of the set form from the `d`-tuple form can exist.

Consequently the identification proved here is **not** available under the hypothesis of Tag
0B9A as that tag states it, and nothing here may be registered as condition (2)(a) of its proof.
What the same example shows is that the source's route to (2)(a) is itself unavailable in that
generality: for the doubled line and `d = 1` the subfunctor `F_U` of families supported in `U` is
a *proper* subfunctor of `Hilb¹_{U/S} = 𝔸¹` — over an affine `T = Spec B` it consists of the
`f ∈ B` whose vanishing locus is clopen, so it omits the identity of `𝔸¹` — and (2)(a) there
would have to be proved for `F_U` directly. It cannot be: `F_U` is `𝔸¹ ∖ {0}` glued to the
functor of nilpotents, which no scheme represents, and for the same reason `Hilb¹` of the doubled
line is **not** a scheme either, so the conclusion of Tag 0B9A fails at `d = 1`. The argument is
written out in the module docstring of
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`, which is also
where the tag is registered: under the source's own `d`-tuple hypothesis, on the range `2 ≤ d`
where the tag holds. Alongside it that file proves the generalisation to every `d`, which asks
for the affine open at `max d 2` points of a fibre — the source's hypothesis again for `2 ≤ d`,
and for `d ≤ 1` the two-point case, equivalently, as
`AlgebraicGeometry.isSeparated_of_exists_isAffineOpen_pair` shows, separatedness of `X ⟶ S`.

The set form is what Stacks Tag 0B9B establishes in all seven of its cases
(`StacksFrontier/AlgebraicGeometry/HilbertFibreAffineOpen/Basic.lean`), and the `d`-tuple form is
derived from it by
`Stacks.HilbertFibreAffineOpen.exists_isAffineOpen_forall_mem_of_hasAffineFinitePointsInFibres`
— that implication runs set form `⟹` `d`-tuple form, which is the direction needed to *apply*
0B9B. So nothing is lost for any of the seven cases of 0B9B.

*How the round trips are proved.* Both composites are computed through
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`: an ideal sheaf is the kernel of the
inclusion of the subscheme it cuts out, and a kernel is unchanged by precomposition with an
isomorphism. So it suffices, in each direction, to exhibit the inclusion of the subscheme cut
out by the transported ideal sheaf as an isomorphism followed by the original inclusion. No
general `map`-`comap` round-trip lemma for an open immersion is needed.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 0B9B](https://stacks.math.columbia.edu/tag/0B9B)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-! ### The comparison map of ambient schemes as a base change -/

/-- The defining cartesian square of `X ×_S T`, in the names this development uses for its two
projections. -/
theorem isPullback_structureMorphism (X T : Over S) :
    IsPullback (familyProjection X T) ((Over.pullback T.hom).obj X).hom X.hom T.hom :=
  IsPullback.of_hasPullback X.hom T.hom

/-- **The square comparing `Y ×_S T` with `X ×_S T` over `Y ⟶ X` is cartesian.** The projections
to the ambient schemes are its vertical edges, so `Y ×_S T ⟶ X ×_S T` is the base change of
`Y ⟶ X` along `X ×_S T ⟶ X`.

The square is obtained from the defining cartesian square of `Y ×_S T` by cancelling the
defining cartesian square of `X ×_S T` off its bottom. -/
theorem isPullback_familyAmbientMap {X Y : Over S} (i : Y ⟶ X) (T : Over S) :
    IsPullback (familyProjection Y T) (familyAmbientMap i T) i.left (familyProjection X T) := by
  refine IsPullback.of_bot ?_ (familyAmbientMap_comp_fst i T).symm
    (isPullback_structureMorphism X T)
  rw [familyAmbientMap_comp_hom, Over.w i]
  exact isPullback_structureMorphism Y T

/-- Precomposing with an isomorphism does not change the image of a morphism of schemes. -/
private theorem range_isIso_comp {A B C : Scheme.{u}} (e : A ⟶ B) [IsIso e] (h : B ⟶ C) :
    Set.range (e ≫ h) = Set.range h := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨e a, (Scheme.Hom.comp_apply e h a).symm⟩
  · rintro _ ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := e.surjective b
    exact ⟨a, Scheme.Hom.comp_apply e h a⟩

/-- **The image of `Y ×_S T ⟶ X ×_S T` is the preimage of the image of `Y ⟶ X`** under the
projection `X ×_S T ⟶ X`, as opens. -/
theorem opensRange_familyAmbientMap {X Y : Over S} (i : Y ⟶ X) [IsOpenImmersion i.left]
    (T : Over S) :
    (familyAmbientMap i T).opensRange = familyProjection X T ⁻¹ᵁ i.left.opensRange :=
  Opens.ext (range_familyAmbientMap i T)

/-- `Y ×_S T ⟶ X ×_S T` is compatible with base change of `T`. -/
theorem familyAmbientMap_comp_familyBaseChangeMap {X Y : Over S} (i : Y ⟶ X) {T' T : Over S}
    (g : T' ⟶ T) :
    familyAmbientMap i T' ≫ familyBaseChangeMap X g =
      familyBaseChangeMap Y g ≫ familyAmbientMap i T := by
  dsimp [familyAmbientMap, familyBaseChangeMap]
  rw [pullback.map_comp, pullback.map_comp]
  simp

/-! ### An open of the ambient scheme as a scheme over the base -/

/-- An open `U ⊆ X` of a scheme over `S`, viewed as a scheme over `S`. -/
def openAmbient (X : Over S) (U : X.left.Opens) : Over S :=
  Over.mk (U.ι ≫ X.hom)

/-- The underlying scheme of `U` viewed over `S` is the open subscheme `U`. -/
@[simp]
theorem openAmbient_left (X : Over S) (U : X.left.Opens) :
    (openAmbient X U).left = U.toScheme :=
  rfl

/-- The structure morphism of `U` viewed over `S` is the inclusion followed by `X ⟶ S`. -/
@[simp]
theorem openAmbient_hom (X : Over S) (U : X.left.Opens) :
    (openAmbient X U).hom = U.ι ≫ X.hom :=
  rfl

/-- The inclusion of an open `U ⊆ X` into `X`, as a morphism of schemes over `S`. -/
def openAmbientι (X : Over S) (U : X.left.Opens) : openAmbient X U ⟶ X :=
  Over.homMk U.ι rfl

/-- The morphism of schemes underlying the inclusion `U ⟶ X` over `S`. -/
@[simp]
theorem openAmbientι_left (X : Over S) (U : X.left.Opens) :
    (openAmbientι X U).left = U.ι :=
  rfl

/-- The inclusion of an open of `X` into `X` is an open immersion. -/
instance isOpenImmersion_openAmbientι_left (X : Over S) (U : X.left.Opens) :
    IsOpenImmersion (openAmbientι X U).left :=
  show IsOpenImmersion U.ι from inferInstance

/-- The morphism `U ×_S T ⟶ X ×_S T` induced by the inclusion of an open `U ⊆ X`. -/
def openAmbientMap (X : Over S) (U : X.left.Opens) (T : Over S) :
    ((Over.pullback T.hom).obj (openAmbient X U)).left ⟶
      ((Over.pullback T.hom).obj X).left :=
  familyAmbientMap (openAmbientι X U) T

/-- `U ×_S T ⟶ X ×_S T` is an open immersion. -/
instance isOpenImmersion_openAmbientMap (X : Over S) (U : X.left.Opens) (T : Over S) :
    IsOpenImmersion (openAmbientMap X U T) :=
  inferInstanceAs (IsOpenImmersion (familyAmbientMap (openAmbientι X U) T))

/-- `U ×_S T ⟶ X ×_S T` is compatible with the structure morphisms to `T`. -/
@[reassoc (attr := simp)]
theorem openAmbientMap_comp_structureMorphism (X : Over S) (U : X.left.Opens) (T : Over S) :
    openAmbientMap X U T ≫ ((Over.pullback T.hom).obj X).hom =
      ((Over.pullback T.hom).obj (openAmbient X U)).hom :=
  familyAmbientMap_comp_hom (openAmbientι X U) T

/-- `U ×_S T ⟶ X ×_S T` is compatible with the projections to `X`, through `U ⊆ X`. -/
@[reassoc]
theorem openAmbientMap_comp_familyProjection (X : Over S) (U : X.left.Opens) (T : Over S) :
    openAmbientMap X U T ≫ familyProjection X T =
      familyProjection (openAmbient X U) T ≫ U.ι :=
  familyAmbientMap_comp_fst (openAmbientι X U) T

/-- **The image of `U ×_S T ⟶ X ×_S T` is the preimage of `U` under `X ×_S T ⟶ X`.** -/
theorem range_openAmbientMap (X : Over S) (U : X.left.Opens) (T : Over S) :
    Set.range (openAmbientMap X U T) = familyProjection X T ⁻¹' (U : Set X.left) :=
  (range_familyAmbientMap (openAmbientι X U) T).trans
    (congrArg (fun s : Set X.left => familyProjection X T ⁻¹' s) (Scheme.Opens.range_ι U))

/-- **The image of `U ×_S T ⟶ X ×_S T` is the preimage of `U` under `X ×_S T ⟶ X`**, as
opens. -/
theorem opensRange_openAmbientMap (X : Over S) (U : X.left.Opens) (T : Over S) :
    (openAmbientMap X U T).opensRange = familyProjection X T ⁻¹ᵁ U :=
  Opens.ext (range_openAmbientMap X U T)

/-- The structure morphism of `U ×_S T` is separated when `U` is affine: it is a base change of
the morphism `U ⟶ S`, which is separated because `U` is an affine, hence separated, scheme. -/
theorem isSeparated_structureMorphism_openAmbient (X : Over S) {U : X.left.Opens}
    (hU : IsAffineOpen U) (T : Over S) :
    IsSeparated ((Over.pullback T.hom).obj (openAmbient X U)).hom := by
  have : IsAffine U.toScheme := hU
  show IsSeparated (pullback.snd (U.ι ≫ X.hom) T.hom)
  infer_instance

/-- `U ×_S T ⟶ X ×_S T` is compatible with base change of `T`. -/
theorem openAmbientMap_comp_familyBaseChangeMap (X : Over S) (U : X.left.Opens)
    {T' T : Over S} (g : T' ⟶ T) :
    openAmbientMap X U T' ≫ familyBaseChangeMap X g =
      familyBaseChangeMap (openAmbient X U) g ≫ openAmbientMap X U T :=
  familyAmbientMap_comp_familyBaseChangeMap (openAmbientι X U) g

/-! ### The footnote: a family of an open of `X` is closed in `X ×_S T` -/

/-- **The footnote to the proof of Stacks Tag 0B9A.** Let `T` be a scheme over `S` and let
`g : Z ⟶ X ×_S T` be a morphism whose composite with the projection `X ×_S T ⟶ T` is finite.
Assume that for every point `x` of `X ×_S T` some affine open `U ⊆ X` contains the image of `x`
in `X` together with the images in `X` of all the points of `Z` lying over the same point of `T`
as `x`. Then the image of `g` is closed.

That assumption is exactly what the source's argument consumes, and it is stated here rather
than any hypothesis on `X ⟶ S` so that the two ways of meeting it share this proof: the
fibrewise affineness hypothesis of Tag 0B9A meets it in
`Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism_of_hasAffineFinitePointsInFibres`,
and separatedness of `X ⟶ S` makes the conclusion available with no affine open at all, in
`Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism_of_isSeparated`.

The source's argument. Let `x` lie in the closure of the image and let `t` be its image in `T`.
The assumption provides an affine open `U ⊆ X` containing the image of `x` and the images of the
points of `Z` over `t`. Let `W ⊆ X ×_S T` be the preimage of `U`: its structure morphism
to `T` is separated, being a base change of the morphism out of the affine `U`. Since `Z ⟶ T` is
a closed map, the set of points of `T` over which `Z` fails to land in `W` is closed, and `t` is
not in it; let `T'` be its complement. Over `T'` the morphism `g` factors through the open
`O = W ∩ (X ×_S T)|_{T'}`, which is separated over `T'`, while the restriction of `Z` over `T'`
is universally closed; so Stacks 01W6 makes the factored morphism universally closed and its
image closed in `O`. As `x` lies in `O` and in the closure of the image of `g`, it lies in the
image of `g`. -/
theorem isClosed_range_of_isFinite_comp_structureMorphism (X : Over S) (T : Over S)
    {Z : Scheme.{u}} (g : Z ⟶ ((Over.pullback T.hom).obj X).left)
    [IsFinite (g ≫ ((Over.pullback T.hom).obj X).hom)]
    (hX : ∀ x : ((Over.pullback T.hom).obj X).left, ∃ U : X.left.Opens, IsAffineOpen U ∧
      familyProjection X T x ∈ U ∧ ∀ z : Z,
        ((Over.pullback T.hom).obj X).hom (g z) = ((Over.pullback T.hom).obj X).hom x →
          familyProjection X T (g z) ∈ U) :
    IsClosed (Set.range g) := by
  set p := ((Over.pullback T.hom).obj X).hom with hp
  set q := g ≫ p with hq
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨U, hU, hxU, hfibU⟩ := hX x
  -- `W` is the preimage of `U`: an open of `X ×_S T` containing `x` and the fibre of `Z`.
  set W : ((Over.pullback T.hom).obj X).left.Opens := familyProjection X T ⁻¹ᵁ U with hW
  have hxW : x ∈ W := hxU
  have hfibW : (q ⁻¹' {p x} : Set Z) ⊆ g ⁻¹' (W : Set _) := by
    intro z hz
    have hzq : q z = p x := hz
    rw [hq, Scheme.Hom.comp_apply] at hzq
    exact hfibU z hzq
  -- The locus in the base over which `Z` fails to land in `W` is closed and misses `p x`.
  have hCclosed : IsClosed (q '' ((g ⁻¹' (W : Set _))ᶜ)) :=
    q.isClosedMap _ (isClosed_compl_iff.mpr (W.2.preimage g.continuous))
  have hxC : p x ∉ q '' ((g ⁻¹' (W : Set _))ᶜ) := by
    rintro ⟨z, hz, hzx⟩
    exact hz (hfibW hzx)
  set T' : T.left.Opens := ⟨(q '' ((g ⁻¹' (W : Set _))ᶜ))ᶜ, hCclosed.isOpen_compl⟩ with hT'
  set O : ((Over.pullback T.hom).obj X).left.Opens := W ⊓ p ⁻¹ᵁ T' with hO
  have hxO : x ∈ O := ⟨hxW, hxC⟩
  -- Over `T'` the source of `g` lands in `W`, so `g ⁻¹ O` is the restriction of `Z` over `T'`.
  have hpreim : g ⁻¹' (O : Set _) = q ⁻¹' (T' : Set T.left) := by
    refine Set.Subset.antisymm (fun z hz => hz.2) (fun z hz => ⟨?_, hz⟩)
    by_contra hzW
    exact hz ⟨z, hzW, rfl⟩
  -- `g` restricted over `T'` factors through the open `O`.
  have hrange : Set.range ((q ⁻¹ᵁ T').ι ≫ g) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hpreim.ge z.2
  set gO := IsOpenImmersion.lift O.ι ((q ⁻¹ᵁ T').ι ≫ g) hrange with hgO
  have hgOfac : gO ≫ O.ι = (q ⁻¹ᵁ T').ι ≫ g := IsOpenImmersion.lift_fac _ _ hrange
  -- `O` is separated over `T'`: it sits inside `W`, which is `U ×_S T` with `U` affine.
  have hrange' : Set.range (O.ι ≫ p) ⊆ Set.range T'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact z.2.2
  set rO := IsOpenImmersion.lift T'.ι (O.ι ≫ p) hrange' with hrO
  have hrOfac : rO ≫ T'.ι = O.ι ≫ p := IsOpenImmersion.lift_fac _ _ hrange'
  have hrangeW : Set.range O.ι ⊆ Set.range (openAmbientMap X U T) := by
    rw [Scheme.Opens.range_ι, range_openAmbientMap]
    exact fun _ hz => hz.1
  have hlW : IsOpenImmersion.lift (openAmbientMap X U T) O.ι hrangeW ≫
      openAmbientMap X U T = O.ι := IsOpenImmersion.lift_fac _ _ hrangeW
  haveI : IsSeparated rO := by
    haveI : IsSeparated (rO ≫ T'.ι) := by
      rw [hrOfac, ← hlW, Category.assoc, openAmbientMap_comp_structureMorphism]
      haveI := isSeparated_structureMorphism_openAmbient X hU T
      infer_instance
    exact IsSeparated.of_comp rO T'.ι
  -- The restriction of `Z` over `T'` is universally closed, hence so is the factored morphism.
  haveI : UniversallyClosed (q ∣_ T') :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q T').flip inferInstance
  have hgOrO : gO ≫ rO = q ∣_ T' := by
    rw [← cancel_mono T'.ι, Category.assoc, hrOfac, ← Category.assoc, hgOfac,
      morphismRestrict_ι, Category.assoc, hq]
  haveI : UniversallyClosed (gO ≫ rO) := hgOrO ▸ inferInstance
  haveI : UniversallyClosed gO := UniversallyClosed.of_comp_of_isSeparated gO rO
  -- Hence the image of `g` meets `O` in a closed subset of `O`.
  have hgOapply : ∀ w : (q ⁻¹ᵁ T').toScheme, O.ι (gO w) = g ((q ⁻¹ᵁ T').ι w) := by
    intro w
    rw [← Scheme.Hom.comp_apply, hgOfac, Scheme.Hom.comp_apply]
  have himg : O.ι ⁻¹' Set.range g = Set.range gO := by
    refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨z, hz⟩ := hy
      have hzO : z ∈ (q ⁻¹ᵁ T' : Z.Opens) := by
        refine hpreim.le ?_
        rw [Set.mem_preimage, hz]
        exact y.2
      refine ⟨⟨z, hzO⟩, O.ι.isOpenEmbedding.injective ?_⟩
      rw [hgOapply ⟨z, hzO⟩]
      exact hz
    · obtain ⟨w, rfl⟩ := hy
      exact ⟨(q ⁻¹ᵁ T').ι w, (hgOapply w).symm⟩
  have hclosed : IsClosed (O.ι ⁻¹' Set.range g) := by
    rw [himg]
    exact gO.isClosedMap.isClosed_range
  -- `x` lies in `O` and in the closure of the image, hence in the image.
  have hx' : (⟨x, hxO⟩ : O.toScheme) ∈ closure (O.ι ⁻¹' Set.range g) :=
    O.ι.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage
      (show (⟨x, hxO⟩ : O.toScheme) ∈ O.ι ⁻¹' closure (Set.range g) from hx)
  rw [hclosed.closure_eq] at hx'
  exact hx'

/-- **The footnote, under the set form of the fibrewise affineness hypothesis.** If every finite
set of points lying in a single fibre of `X ⟶ S` is contained in an affine open of `X`, then the
image of a morphism `g : Z ⟶ X ×_S T` whose composite with the projection to `T` is finite is
closed: the fibre of `Z ⟶ T` over the image `t` of a point `x` is finite, so its image in `X`
together with the image of `x` is a finite set of points of the fibre of `X ⟶ S` over the image
of `t`. -/
theorem isClosed_range_of_isFinite_comp_structureMorphism_of_hasAffineFinitePointsInFibres
    (X : Over S) (hX : HasAffineFinitePointsInFibres X.hom) (T : Over S) {Z : Scheme.{u}}
    (g : Z ⟶ ((Over.pullback T.hom).obj X).left)
    [IsFinite (g ≫ ((Over.pullback T.hom).obj X).hom)] :
    IsClosed (Set.range g) := by
  refine isClosed_range_of_isFinite_comp_structureMorphism X T g fun x => ?_
  -- Projecting `X ×_S T ⟶ X` is compatible with the structure morphisms to `S`.
  have key : ∀ w : ((Over.pullback T.hom).obj X).left,
      X.hom (familyProjection X T w) = T.hom (((Over.pullback T.hom).obj X).hom w) := by
    intro w
    rw [← Scheme.Hom.comp_apply, familyProjection_comp, Scheme.Hom.comp_apply]
  have hfib : ((g ≫ ((Over.pullback T.hom).obj X).hom) ⁻¹'
      {((Over.pullback T.hom).obj X).hom x} : Set Z).Finite :=
    (g ≫ ((Over.pullback T.hom).obj X).hom).finite_preimage_singleton _
  have hEfib : ∀ y ∈ insert (familyProjection X T x)
      (familyProjection X T '' (g '' ((g ≫ ((Over.pullback T.hom).obj X).hom) ⁻¹'
        {((Over.pullback T.hom).obj X).hom x}))),
      X.hom y = T.hom (((Over.pullback T.hom).obj X).hom x) := by
    rintro y (rfl | ⟨w, ⟨z, hz, rfl⟩, rfl⟩)
    · exact key x
    · rw [key]
      refine congrArg _ ?_
      rw [← Scheme.Hom.comp_apply]
      exact hz
  obtain ⟨U, hU, hEU⟩ := hX (T.hom (((Over.pullback T.hom).obj X).hom x)) _
    (((hfib.image _).image _).insert _) hEfib
  refine ⟨U, hU, hEU (Set.mem_insert _ _), fun z hz => ?_⟩
  refine hEU (Set.mem_insert_of_mem _ ⟨g z, ⟨z, ?_, rfl⟩, rfl⟩)
  show (g ≫ ((Over.pullback T.hom).obj X).hom) z = _
  rw [Scheme.Hom.comp_apply]
  exact hz

/-- **The footnote, for a separated `X ⟶ S`, where it needs no affine open at all.** The
projection `X ×_S T ⟶ T` is a base change of `X ⟶ S`, hence separated, and `Z ⟶ T` is finite
and so universally closed; so `g` itself is universally closed by Stacks 01W6, and its image is
closed. -/
theorem isClosed_range_of_isFinite_comp_structureMorphism_of_isSeparated (X : Over S)
    [IsSeparated X.hom] (T : Over S) {Z : Scheme.{u}}
    (g : Z ⟶ ((Over.pullback T.hom).obj X).left)
    [IsFinite (g ≫ ((Over.pullback T.hom).obj X).hom)] :
    IsClosed (Set.range g) := by
  haveI : IsSeparated ((Over.pullback T.hom).obj X).hom :=
    show IsSeparated (pullback.snd X.hom T.hom) from inferInstance
  haveI : UniversallyClosed (g ≫ ((Over.pullback T.hom).obj X).hom) := inferInstance
  haveI : UniversallyClosed g :=
    UniversallyClosed.of_comp_of_isSeparated g ((Over.pullback T.hom).obj X).hom
  exact g.isClosedMap.isClosed_range

/-- **The closed subscheme of `U ×_S T` cut out by a degree-`d` Hilbert family in an open
`U ⊆ X` is a closed subscheme of `X ×_S T`, for every open `U` and every base `T`.** This is
what the footnote to the proof of Stacks Tag 0B9A delivers, and it is the only thing the
identification of the subfunctor of families supported in `U` with the Hilbert functor of `U`
needs of `X ⟶ S`; it is therefore carried as a hypothesis by that identification and by
everything built from it.

It holds under the set form of the fibrewise affineness hypothesis
(`Stacks.Hilbert.familiesClosedInAmbient_of_hasAffineFinitePointsInFibres`) and also, with no
hypothesis on the fibres, when `X ⟶ S` is separated
(`Stacks.Hilbert.familiesClosedInAmbient_of_isSeparated`). It fails for the `d`-tuple form in
which Tag 0B9A states its hypothesis, by the doubled-origin example in the module
docstring. -/
def FamiliesClosedInAmbient (X : Over S) : Prop :=
  ∀ (d : ℕ) (U : X.left.Opens) (T : Over S) (W : HilbertFamily (openAmbient X U) T d),
    IsClosedImmersion (W.ideal.subschemeι ≫ openAmbientMap X U T)

/-- The composite of the inclusion of the subscheme cut out by a degree-`d` Hilbert family in an
open `U ⊆ X` with `U ×_S T ⟶ X ×_S T` is finite over `T`. -/
instance isFinite_subschemeι_comp_openAmbientMap_comp_structureMorphism {X : Over S}
    {U : X.left.Opens} {T : Over S} {d : ℕ} (W : HilbertFamily (openAmbient X U) T d) :
    IsFinite ((W.ideal.subschemeι ≫ openAmbientMap X U T) ≫
      ((Over.pullback T.hom).obj X).hom) := by
  rw [Category.assoc, openAmbientMap_comp_structureMorphism]
  exact W.isFinite_structural

/-- **The closed subscheme of `U ×_S T` cut out by a degree-`d` Hilbert family in an open
`U ⊆ X` is a closed subscheme of `X ×_S T`.** This is what the footnote to the proof of Stacks
Tag 0B9A is for: the composite is an immersion for free, and the fibrewise affineness hypothesis
is what makes its image closed.

The hypothesis is genuinely needed in its set form: with it weakened to the `d`-tuple form in
which Tag 0B9A states its hypothesis the statement is false, by the doubled-origin example in
the module docstring. -/
theorem isClosedImmersion_subschemeι_comp_openAmbientMap {X : Over S}
    (hX : HasAffineFinitePointsInFibres X.hom) {U : X.left.Opens} {T : Over S} {d : ℕ}
    (W : HilbertFamily (openAmbient X U) T d) :
    IsClosedImmersion (W.ideal.subschemeι ≫ openAmbientMap X U T) :=
  IsClosedImmersion.of_isPreimmersion _
    (isClosed_range_of_isFinite_comp_structureMorphism_of_hasAffineFinitePointsInFibres X hX T _)

/-- **The set form of the fibrewise affineness hypothesis makes every family of an open closed
in the ambient scheme.** -/
theorem familiesClosedInAmbient_of_hasAffineFinitePointsInFibres {X : Over S}
    (hX : HasAffineFinitePointsInFibres X.hom) : FamiliesClosedInAmbient X :=
  fun _ _ _ W => isClosedImmersion_subschemeι_comp_openAmbientMap hX W

/-- **A separated `X ⟶ S` makes every family of an open closed in the ambient scheme**, with no
hypothesis on the fibres: a subscheme finite over `T` inside `X ×_S T` is closed as soon as
`X ×_S T ⟶ T` is separated. -/
theorem familiesClosedInAmbient_of_isSeparated (X : Over S) [IsSeparated X.hom] :
    FamiliesClosedInAmbient X :=
  fun _ _ T _ => IsClosedImmersion.of_isPreimmersion _
    (isClosed_range_of_isFinite_comp_structureMorphism_of_isSeparated X T _)

/-! ### Restricting a family supported in an open -/

/-- The base change of `U ×_S T ⟶ X ×_S T` along a morphism landing in its image is an
isomorphism onto the source. -/
private theorem isIso_pullback_snd_openAmbientMap {X T : Over S} {U : X.left.Opens}
    {A : Scheme.{u}} (f : A ⟶ ((Over.pullback T.hom).obj X).left)
    (h : ∀ a, f a ∈ Set.range (openAmbientMap X U T)) :
    IsIso (pullback.snd (openAmbientMap X U T) f) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  rw [Scheme.Hom.opensRange_pullbackSnd]
  exact Opens.ext (Set.eq_univ_of_forall h)

section Restrict

variable {X : Over S} {T : Over S} {d : ℕ}

/-- The base change along the inclusion of the subscheme cut out by a degree-`d` Hilbert family
of the open immersion `U ×_S T ⟶ X ×_S T`: a morphism from the subscheme cut out by the
restricted ideal sheaf to the subscheme cut out by the original one. -/
def HilbertFamily.toRestrict (Z : HilbertFamily X T d) (U : X.left.Opens) :
    (Z.ideal.comap (openAmbientMap X U T)).subscheme ⟶ Z.ideal.subscheme :=
  (Z.ideal.comapIso (openAmbientMap X U T)).hom ≫
    pullback.snd (openAmbientMap X U T) Z.ideal.subschemeι

/-- For a family supported in `U`, the comparison morphism of
`Stacks.Hilbert.HilbertFamily.toRestrict` is an isomorphism: an open immersion whose image is
everything, because the subscheme lands inside `U`. -/
theorem HilbertFamily.isIso_toRestrict {Z : HilbertFamily X T d} {U : X.left.Opens}
    (hZ : Z.SupportedIn U) : IsIso (Z.toRestrict U) := by
  haveI : IsIso (pullback.snd (openAmbientMap X U T) Z.ideal.subschemeι) :=
    isIso_pullback_snd_openAmbientMap _ fun z => by
      rw [range_openAmbientMap]
      simpa [HilbertFamily.toAmbient, Scheme.Hom.comp_apply] using hZ z
  rw [HilbertFamily.toRestrict]
  infer_instance

/-- The inclusion of the subscheme cut out by the restricted ideal sheaf, read through
`Stacks.Hilbert.HilbertFamily.toRestrict`. -/
theorem HilbertFamily.toRestrict_comp_subschemeι (Z : HilbertFamily X T d)
    (U : X.left.Opens) :
    (Z.ideal.comap (openAmbientMap X U T)).subschemeι ≫ openAmbientMap X U T =
      Z.toRestrict U ≫ Z.ideal.subschemeι := by
  rw [HilbertFamily.toRestrict, ← Scheme.IdealSheafData.comapIso_hom_fst Z.ideal
    (openAmbientMap X U T), Category.assoc, Category.assoc, pullback.condition]

/-- The structure morphism of the subscheme cut out by the restricted ideal sheaf, read through
`Stacks.Hilbert.HilbertFamily.toRestrict`. -/
theorem HilbertFamily.toRestrict_comp_structural (Z : HilbertFamily X T d)
    (U : X.left.Opens) :
    (Z.ideal.comap (openAmbientMap X U T)).subschemeι ≫
        ((Over.pullback T.hom).obj (openAmbient X U)).hom =
      Z.toRestrict U ≫ Z.structural := by
  rw [← openAmbientMap_comp_structureMorphism X U T, ← Category.assoc,
    Z.toRestrict_comp_subschemeι U, HilbertFamily.structural, Category.assoc]

/-- **The degree-`d` Hilbert family in `U` obtained from one in `X` supported in `U`**: its
ideal sheaf is the restriction of the original one to `U ×_S T`. -/
def HilbertFamily.restrictToOpenAmbient {U : X.left.Opens} (Z : HilbertFamily X T d)
    (hZ : Z.SupportedIn U) : HilbertFamily (openAmbient X U) T d where
  ideal := Z.ideal.comap (openAmbientMap X U T)
  isFiniteLocallyFreeOfRank := by
    haveI := HilbertFamily.isIso_toRestrict hZ
    haveI := Z.isFiniteLocallyFreeOfRank_structural
    exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (f := Z.structural) (IsPullback.of_horiz_isIso
        ⟨by rw [Z.toRestrict_comp_structural U, Category.comp_id]⟩)

/-- The ideal sheaf of the restricted family is the restricted ideal sheaf. -/
@[simp]
theorem HilbertFamily.restrictToOpenAmbient_ideal {U : X.left.Opens} (Z : HilbertFamily X T d)
    (hZ : Z.SupportedIn U) :
    (Z.restrictToOpenAmbient hZ).ideal = Z.ideal.comap (openAmbientMap X U T) :=
  rfl

end Restrict

/-! ### Extending a family of an open to the ambient scheme -/

section Extend

variable {X : Over S} {U : X.left.Opens} {T : Over S} {d : ℕ}

/-- The comparison isomorphism from the subscheme cut out by a degree-`d` Hilbert family in `U`
over `T` to the subscheme of `X ×_S T` cut out by the kernel of its inclusion. -/
def HilbertFamily.toExtend (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) :
    W.ideal.subscheme ⟶ (W.ideal.map (openAmbientMap X U T)).subscheme :=
  haveI := hX d U T W
  IsClosedImmersion.lift (W.ideal.map (openAmbientMap X U T)).subschemeι
    (W.ideal.subschemeι ≫ openAmbientMap X U T)
    (Scheme.IdealSheafData.ker_subschemeι _).le

/-- The comparison morphism of `Stacks.Hilbert.HilbertFamily.toExtend` is compatible with the
two inclusions into `X ×_S T`. -/
theorem HilbertFamily.toExtend_comp_subschemeι (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) :
    HilbertFamily.toExtend hX W ≫ (W.ideal.map (openAmbientMap X U T)).subschemeι =
      W.ideal.subschemeι ≫ openAmbientMap X U T :=
  haveI := hX d U T W
  IsClosedImmersion.lift_fac _ _ _

/-- The comparison morphism of `Stacks.Hilbert.HilbertFamily.toExtend` is an isomorphism: two
closed immersions into `X ×_S T` with the same kernel have the same source. -/
theorem HilbertFamily.isIso_toExtend (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) : IsIso (HilbertFamily.toExtend hX W) :=
  haveI := hX d U T W
  IsClosedImmersion.isIso_lift _ _ (Scheme.IdealSheafData.ker_subschemeι _)

/-- The subscheme of `X ×_S T` cut out by the pushed-forward ideal sheaf has the same image as
the subscheme cut out by the original one. -/
theorem HilbertFamily.range_subschemeι_map (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) :
    Set.range (W.ideal.map (openAmbientMap X U T)).subschemeι =
      Set.range (W.ideal.subschemeι ≫ openAmbientMap X U T) := by
  haveI := HilbertFamily.isIso_toExtend hX W
  rw [← HilbertFamily.toExtend_comp_subschemeι hX W, range_isIso_comp]

/-- The subscheme of `X ×_S T` cut out by the pushed-forward ideal sheaf lies in the image of
`U ×_S T ⟶ X ×_S T`. -/
theorem HilbertFamily.range_subschemeι_map_subset (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) :
    Set.range (W.ideal.map (openAmbientMap X U T)).subschemeι ⊆
      Set.range (openAmbientMap X U T) := by
  rw [HilbertFamily.range_subschemeι_map hX W, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact Set.range_comp_subset_range _ _

/-- **The degree-`d` Hilbert family in `X` obtained from one in an open `U ⊆ X`**: its ideal
sheaf is the pushforward of the original one along `U ×_S T ⟶ X ×_S T`, which cuts out a closed
subscheme of `X ×_S T` by the footnote to the proof of Stacks Tag 0B9A. -/
def HilbertFamily.extendToAmbient (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) : HilbertFamily X T d where
  ideal := W.ideal.map (openAmbientMap X U T)
  isFiniteLocallyFreeOfRank := by
    haveI := HilbertFamily.isIso_toExtend hX W
    haveI := W.isFiniteLocallyFreeOfRank_structural
    refine Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (f := W.structural) (g' := inv (HilbertFamily.toExtend hX W)) (g := 𝟙 T.left)
      (IsPullback.of_horiz_isIso ⟨?_⟩)
    rw [Category.comp_id, HilbertFamily.structural, IsIso.inv_comp_eq,
      ← Category.assoc, HilbertFamily.toExtend_comp_subschemeι, Category.assoc,
      openAmbientMap_comp_structureMorphism]

/-- The ideal sheaf of the extended family is the pushed-forward ideal sheaf. -/
@[simp]
theorem HilbertFamily.extendToAmbient_ideal (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) :
    (HilbertFamily.extendToAmbient hX W).ideal = W.ideal.map (openAmbientMap X U T) :=
  rfl

/-- The family extended from an open `U ⊆ X` is supported in `U`. -/
theorem HilbertFamily.extendToAmbient_supportedIn (hX : FamiliesClosedInAmbient X)
    (W : HilbertFamily (openAmbient X U) T d) :
    (HilbertFamily.extendToAmbient hX W).SupportedIn U := by
  intro z
  have hz : (W.ideal.map (openAmbientMap X U T)).subschemeι z ∈
      familyProjection X T ⁻¹' (U : Set X.left) := by
    rw [← range_openAmbientMap]
    exact HilbertFamily.range_subschemeι_map_subset hX W ⟨z, rfl⟩
  show ((HilbertFamily.extendToAmbient hX W).ideal.subschemeι ≫ familyProjection X T) z ∈ U
  rw [Scheme.Hom.comp_apply]
  exact hz

end Extend

/-! ### The identification of the subfunctor with the Hilbert functor of the open -/

section Equiv

variable {X : Over S} {U : X.left.Opens} {d : ℕ}

/-- Restricting and then extending recovers the family of `X`. -/
theorem HilbertFamily.extendToAmbient_restrictToOpenAmbient
    (hX : FamiliesClosedInAmbient X) {T : Over S} (Z : HilbertFamily X T d)
    (hZ : Z.SupportedIn U) :
    HilbertFamily.extendToAmbient hX (Z.restrictToOpenAmbient hZ) = Z := by
  haveI := HilbertFamily.isIso_toRestrict hZ
  refine HilbertFamily.ext ?_
  rw [HilbertFamily.extendToAmbient_ideal, HilbertFamily.restrictToOpenAmbient_ideal,
    Scheme.IdealSheafData.map, Z.toRestrict_comp_subschemeι U,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- Extending and then restricting recovers the family of the open. -/
theorem HilbertFamily.restrictToOpenAmbient_extendToAmbient
    (hX : FamiliesClosedInAmbient X) {T : Over S}
    (W : HilbertFamily (openAmbient X U) T d) :
    (HilbertFamily.extendToAmbient hX W).restrictToOpenAmbient
        (HilbertFamily.extendToAmbient_supportedIn hX W) = W := by
  haveI := HilbertFamily.isIso_toExtend hX W
  refine HilbertFamily.ext ?_
  rw [HilbertFamily.restrictToOpenAmbient_ideal, HilbertFamily.extendToAmbient_ideal]
  -- The base change of `U ×_S T ⟶ X ×_S T` along the inclusion of the pushed-forward
  -- subscheme is an isomorphism, because that subscheme lies in `U ×_S T`.
  haveI : IsIso (pullback.snd (openAmbientMap X U T)
      (W.ideal.map (openAmbientMap X U T)).subschemeι) :=
    isIso_pullback_snd_openAmbientMap _ fun z =>
      HilbertFamily.range_subschemeι_map_subset hX W ⟨z, rfl⟩
  -- The subscheme cut out by `W` lifts isomorphically into the fibre product.
  have hcomm : W.ideal.subschemeι ≫ openAmbientMap X U T =
      HilbertFamily.toExtend hX W ≫ (W.ideal.map (openAmbientMap X U T)).subschemeι :=
    (HilbertFamily.toExtend_comp_subschemeι hX W).symm
  have hsnd : pullback.lift W.ideal.subschemeι (HilbertFamily.toExtend hX W) hcomm ≫
      pullback.snd (openAmbientMap X U T) (W.ideal.map (openAmbientMap X U T)).subschemeι =
      HilbertFamily.toExtend hX W := pullback.lift_snd _ _ _
  have hfst : pullback.lift W.ideal.subschemeι (HilbertFamily.toExtend hX W) hcomm ≫
      pullback.fst (openAmbientMap X U T) (W.ideal.map (openAmbientMap X U T)).subschemeι =
      W.ideal.subschemeι := pullback.lift_fst _ _ _
  haveI : IsIso (pullback.lift W.ideal.subschemeι (HilbertFamily.toExtend hX W) hcomm) :=
    IsIso.of_isIso_fac_right hsnd
  have hinv : inv (pullback.lift W.ideal.subschemeι (HilbertFamily.toExtend hX W) hcomm) ≫
      W.ideal.subschemeι =
      pullback.fst (openAmbientMap X U T)
        (W.ideal.map (openAmbientMap X U T)).subschemeι :=
    (IsIso.inv_comp_eq _).mpr hfst.symm
  have hsub : (((W.ideal.map (openAmbientMap X U T)).comapIso (openAmbientMap X U T)).hom ≫
        inv (pullback.lift W.ideal.subschemeι (HilbertFamily.toExtend hX W) hcomm)) ≫
      W.ideal.subschemeι =
      ((W.ideal.map (openAmbientMap X U T)).comap (openAmbientMap X U T)).subschemeι := by
    rw [Category.assoc, hinv, Scheme.IdealSheafData.comapIso_hom_fst]
  calc (W.ideal.map (openAmbientMap X U T)).comap (openAmbientMap X U T)
      = ((W.ideal.map (openAmbientMap X U T)).comap
          (openAmbientMap X U T)).subschemeι.ker :=
        (Scheme.IdealSheafData.ker_subschemeι _).symm
    _ = ((((W.ideal.map (openAmbientMap X U T)).comapIso (openAmbientMap X U T)).hom ≫
          inv (pullback.lift W.ideal.subschemeι (HilbertFamily.toExtend hX W) hcomm)) ≫
          W.ideal.subschemeι).ker := by rw [hsub]
    _ = W.ideal.subschemeι.ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = W.ideal := Scheme.IdealSheafData.ker_subschemeι _

/-- **The subfunctor of degree-`d` Hilbert families supported in an open `U ⊆ X` is the
degree-`d` Hilbert functor of `U`.** This is the identification `F_U = Hilb^d_{U/S}` of the
proof of Stacks Tag 0B9A; naturality in `T` is
`Stacks.Hilbert.supportedInEquivOpenAmbient_naturality`. -/
def supportedInEquivOpenAmbient (hX : FamiliesClosedInAmbient X)
    (U : X.left.Opens) (d : ℕ) (T : Over S) :
    {Z : HilbertFamily X T d // Z.SupportedIn U} ≃ HilbertFamily (openAmbient X U) T d where
  toFun Z := Z.1.restrictToOpenAmbient Z.2
  invFun W := ⟨HilbertFamily.extendToAmbient hX W,
    HilbertFamily.extendToAmbient_supportedIn hX W⟩
  left_inv Z := Subtype.ext
    (HilbertFamily.extendToAmbient_restrictToOpenAmbient hX Z.1 Z.2)
  right_inv W := HilbertFamily.restrictToOpenAmbient_extendToAmbient hX W

/-- The identification `F_U = Hilb^d_{U/S}` sends a family supported in `U` to its
restriction. -/
@[simp]
theorem supportedInEquivOpenAmbient_apply (hX : FamiliesClosedInAmbient X)
    (U : X.left.Opens) (d : ℕ) (T : Over S)
    (Z : {Z : HilbertFamily X T d // Z.SupportedIn U}) :
    supportedInEquivOpenAmbient hX U d T Z = Z.1.restrictToOpenAmbient Z.2 :=
  rfl

/-- **The identification `F_U = Hilb^d_{U/S}` is natural in the base.** Restricting to `U ×_S T`
commutes with base change of `T`. -/
theorem supportedInEquivOpenAmbient_naturality (hX : FamiliesClosedInAmbient X)
    (U : X.left.Opens) (d : ℕ) {T' T : Over S} (g : T' ⟶ T)
    (Z : {Z : HilbertFamily X T d // Z.SupportedIn U}) :
    supportedInEquivOpenAmbient hX U d T' ⟨baseChange X g Z.1, Z.2.baseChange g⟩ =
      baseChange (openAmbient X U) g (supportedInEquivOpenAmbient hX U d T Z) := by
  refine HilbertFamily.ext ?_
  rw [supportedInEquivOpenAmbient_apply, supportedInEquivOpenAmbient_apply,
    HilbertFamily.restrictToOpenAmbient_ideal, baseChange_ideal, baseChange_ideal,
    HilbertFamily.restrictToOpenAmbient_ideal, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, openAmbientMap_comp_familyBaseChangeMap]

/-- **The subfunctor of degree-`d` Hilbert families supported in an open `U ⊆ X` is isomorphic,
as a functor on the schemes over `S`, to the degree-`d` Hilbert functor of `U`.** -/
def supportedInIsoOpenAmbient (hX : FamiliesClosedInAmbient X)
    (U : X.left.Opens) (d : ℕ) :
    (supportedIn X d U).toFunctor ≅ hilbertFunctorOfRank (openAmbient X U) d :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (supportedInEquivOpenAmbient hX U d T.unop)) (by
      intro T T' g
      apply ConcreteCategory.hom_ext
      intro Z
      exact supportedInEquivOpenAmbient_naturality hX U d g.unop Z)

end Equiv

end Stacks.Hilbert

end
