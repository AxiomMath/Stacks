module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.GraphOfRelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.EulerCharacteristicOnPoints

/-!
# Relative morphisms with prescribed numerical invariants (Stacks 0DPQ)

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site, with `z` flat, proper and of finite presentation and `x` separated and of finite
presentation, so that the relative morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 is an algebraic
space locally of finite presentation over `Q` by Stacks 0D1C.  Stacks 0DPQ fixes a set `I`, a
perfect object `E i ∈ D(𝒪_{Z ×_Q X})` for each `i ∈ I` and prescribed invariants `P : I → ℤ`,
and, recalling that `Mor_Q(Z, X)` is an open subspace of `Hilb_{Z ×_Q X / Q}` by Stacks 0D1B,
*defines*

`Mor^P_Q(Z, X) = Mor_Q(Z, X) ∩ Hilb^P_{Z ×_Q X / Q}`

with `Hilb^P` as in Stacks 0DPG.  It then asserts that `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat
closed immersion, and an open and closed immersion when `I` is finite, or `Q` is locally
Noetherian, or `I = ℤ` and `E i = L^{⊗ i}` for an invertible `𝒪_{Z ×_Q X}`-module `L` — in which
case the notation is `Mor^{P, L}_Q(Z, X)`.

The inclusion `Mor_Q(Z, X) ⊆ Hilb_{Z ×_Q X / Q}` is the graph transformation of Stacks 0D1A: a
relative morphism `(a, b)` at a test scheme `T` goes to the graph of `b`, a point of the Hilbert
functor over `T`.  So the intersection above is formed here as the inverse image along that
transformation: a relative morphism lies in `Mor^P_Q(Z, X)` exactly when its graph has the
prescribed invariants.

## Main definitions

* `AlgebraicGeometry.Space.HilbertOverEulerData`: the fibrewise numerical invariants of the
  families classified by the Hilbert functor over the schemes of the site, as data, together with
  their étale-local description as derived-fibre Euler characteristics and their compatibility
  with base change.
* `AlgebraicGeometry.Space.HilbertOverEulerData.IsPrescribed` and
  `AlgebraicGeometry.Space.HilbertOverEulerData.prescribedLocus`: the membership condition of
  Stacks 0DPG and the locus in the point space of the test scheme it is read off from.
* `AlgebraicGeometry.Space.HilbertOverEulerData.numericalHilbertPresheaf`: the subfunctor
  `Hilb^P_{Z ×_Q X / Q} ⊆ Hilb_{Z ×_Q X / Q}` of families with the prescribed invariants.
* `AlgebraicGeometry.Space.graphFamilyOfSection`: the graph of a section of `Mor_Q(Z, X)`, as a
  point of `Hilb_{Z ×_Q X / Q}`.
* `AlgebraicGeometry.Space.numericalRelativeHom`: **Stacks 0DPQ**, the subfunctor
  `Mor^P_Q(Z, X) ⊆ Mor_Q(Z, X)`, and
  `AlgebraicGeometry.Space.numericalRelativeHomInclusion` its inclusion into `Mor_Q(Z, X)`.
* `AlgebraicGeometry.Space.prescribedLocusSubspace`: the open subspace of a test scheme over
  which a relative morphism has the prescribed invariants.

## Main results

* `AlgebraicGeometry.Space.HilbertOverEulerData.isClopen_setOf_χ_eq`: the locus in the point space
  of the test scheme on which one invariant takes its prescribed value is open and closed.
* `AlgebraicGeometry.Space.HilbertOverEulerData.isClosed_prescribedLocus` and
  `AlgebraicGeometry.Space.HilbertOverEulerData.isClopen_prescribedLocus`: the locus on which all
  of them do is closed, and open and closed when `I` is finite.
* `AlgebraicGeometry.Space.graphFamilyOfSection_map`: the graph of a restricted section is the
  base change of the graph.
* `AlgebraicGeometry.Space.mem_numericalRelativeHom_iff` and
  `AlgebraicGeometry.Space.mem_numericalRelativeHom_iff_mem_numericalHilbertPresheaf`: the
  sections of `Mor^P_Q(Z, X)` over a scheme are the relative morphisms whose graph has the
  prescribed invariants, which is the intersection of the source.
* `AlgebraicGeometry.Space.mono_numericalRelativeHomInclusion`: the morphism
  `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a monomorphism.
* `AlgebraicGeometry.Space.mem_prescribedLocusSubspace_iff`: a morphism of test schemes restricts
  a relative morphism into `Mor^P_Q(Z, X)` exactly when it factors through that open subspace.
* `AlgebraicGeometry.Space.not_mem_numericalRelativeHom_of_ne`: distinct prescribed invariants cut
  out subfunctors with no relative morphism in common over a test scheme that has a point.

## Implementation notes

**Where the invariants live.**  The source's `Hilb^P` of Stacks 0DPG is a subfunctor of the
Hilbert functor on the schemes over the base, while `Mor_Q(Z, X)` and the graph transformation
are presheaves on the schemes of the site.  The invariants are therefore given here for the
families of `AlgebraicGeometry.Space.HilbertFamilyOver`, that is for
`AlgebraicGeometry.Space.hilbertPresheaf`, which is the Hilbert functor read on the schemes of
the site, and the intersection of the source is the inverse image along the graph
transformation.

**Why the invariants are data.**  The source's condition on a family `W ⊆ (Z ×_Q X)_T` is
`χ((Z ×_Q X)_t, E_{i,t} ⊗^𝐋 (i_*𝒪_W)_t) = P i` for every `i ∈ I` and every `t ∈ |T|`.  The Euler
characteristic of a perfect object on an algebraic space is not constructible in this
development, so the family of fibrewise invariants is given, as it is by
`AlgebraicGeometry.Space.HilbertEulerData` and by
`AlgebraicGeometry.Space.NumericalSituation.ChiData`; the perfect objects `E i` appear only
through the invariants they define.  Two properties of those invariants are recorded, both of
which the source's construction has: that an invariant of a base change at a point is the
invariant of the original family at the image point, which is what makes the condition stable
under base change, and the étale-local description of each invariant as a derived-fibre Euler
characteristic, which is the hypothesis of Stacks 0D1Z and is what makes the loci below open and
closed.

**What is proved of the source's assertion.**  The definition, the membership
characterisations, the monomorphism, and the open and closed loci.  A finite intersection of the
open and closed loci of one invariant is open and closed, and that is why the source's `I` finite
case is the reachable one; the locus of an arbitrary `I` is still closed.  Through the
correspondence of Stacks 03BZ the locus of a relative morphism over a test scheme `T` is the
point set of an open subspace of `T`, and a morphism into `T` restricts the relative morphism
into `Mor^P_Q(Z, X)` exactly when it factors through that subspace, which is how the source's
open immersion is tested on a test scheme.

That `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a **flat closed immersion**, and an **open and closed
immersion** of algebraic spaces, is not proved.  The source attributes both to the corresponding
assertion of Stacks 0DPG, which rests on Lemmas 0DND and 0DNE, assertions about a morphism of
algebraic stacks.

## References

* [Stacks Project, Tag 0DPQ](https://stacks.math.columbia.edu/tag/0DPQ)
* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0D1A](https://stacks.math.columbia.edu/tag/0D1A)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe v u

attribute [local instance] pointTopology

/-! ### The numerical invariants of the families over the schemes of the site -/

section Invariants

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- The fibrewise numerical invariants of the families classified by the Hilbert functor of
`f : X ⟶ Y` over the schemes of the site, indexed by a set `I`.

For a scheme `T` of the site, a family `y` classified by `Hilb_{X/Y}` over `T`, an index `i ∈ I`
and a point `t` of `T`, the integer `χ T y i t` stands for the Euler characteristic
`χ(X_t, E_{i,t} ⊗^𝐋 (i_*𝒪_W)_t)` of the source, for the perfect object `E i ∈ D(𝒪_X)` the source
fixes and the closed subspace `W` of the family.  The two fields are properties of the source's
invariants: the étale-local description of each of them as a derived-fibre Euler characteristic,
and the fibrewise compatibility that the invariant at a point of a base change is the invariant of
the original family at the image point. -/
structure HilbertOverEulerData (f : X ⟶ Y) (I : Type v) where
  /-- The invariant of index `i` of the family `y` at the point `t` of the test scheme. -/
  χ : ∀ T : BigFppfOver B S hS, HilbertFamilyOver f T → I → points B S hS (yoneda.obj T) → ℤ
  /-- Each invariant is étale locally a derived-fibre Euler characteristic, the hypothesis of
  Stacks 0D1Z. -/
  isEtaleLocally : ∀ (T : BigFppfOver B S hS) (y : HilbertFamilyOver f T) (i : I),
    IsEtaleLocallyDerivedFibreChi B S hS (yoneda.obj T) (χ T y i)
  /-- The invariants are fibrewise: the invariant of a base change at a point is the invariant of
  the original family at the image point. -/
  χ_baseChange : ∀ {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (y : HilbertFamilyOver f T) (i : I)
    (t : points B S hS (yoneda.obj T')),
    χ T' (y.baseChange g) i t = χ T y i (pointsMap B S hS (yoneda.obj T') (yoneda.map g) t)

namespace HilbertOverEulerData

variable {f : X ⟶ Y} {I : Type v} (χd : HilbertOverEulerData f I) (P : I → ℤ)

/-- **The membership condition of Stacks 0DPG.**  A family `y` classified by `Hilb_{X/Y}` over a
test scheme `T` has the prescribed invariants exactly when each of its invariants is the
prescribed one at every point of `T`. -/
def IsPrescribed {T : BigFppfOver B S hS} (y : HilbertFamilyOver f T) : Prop :=
  ∀ (i : I) (t : points B S hS (yoneda.obj T)), χd.χ T y i t = P i

/-- The locus in the point space of the test scheme on which all the invariants of a family take
their prescribed values. -/
def prescribedLocus {T : BigFppfOver B S hS} (y : HilbertFamilyOver f T) :
    Set (points B S hS (yoneda.obj T)) :=
  ⋂ i : I, {t | χd.χ T y i t = P i}

/-- A family has the prescribed invariants exactly when its prescribed locus is the whole point
space of the test scheme. -/
theorem isPrescribed_iff_prescribedLocus_eq_univ {T : BigFppfOver B S hS}
    (y : HilbertFamilyOver f T) :
    χd.IsPrescribed P y ↔ χd.prescribedLocus P y = Set.univ := by
  refine ⟨fun h => Set.eq_univ_of_forall fun t => Set.mem_iInter.2 fun i => h i t, fun h i t => ?_⟩
  exact Set.mem_iInter.1 (Set.eq_univ_iff_forall.1 h t) i

/-- **The locus on which one invariant takes its prescribed value is open and closed.**  The
invariant is étale locally a derived-fibre Euler characteristic, hence locally constant by
Stacks 0D1Z, and the fibres of a locally constant function are open and closed. -/
theorem isClopen_setOf_χ_eq {T : BigFppfOver B S hS} (y : HilbertFamilyOver f T) (i : I) :
    IsClopen {t : points B S hS (yoneda.obj T) | χd.χ T y i t = P i} :=
  (isLocallyConstant_of_isEtaleLocallyDerivedFibreChi B S hS (yoneda.obj T) (χd.χ T y i)
    (isAlgebraicSpace_yoneda B S hS T) (χd.isEtaleLocally T y i)).isClopen_fiber _

/-- The prescribed locus of a family is closed, being an intersection of closed loci. -/
theorem isClosed_prescribedLocus {T : BigFppfOver B S hS} (y : HilbertFamilyOver f T) :
    IsClosed (χd.prescribedLocus P y) :=
  isClosed_iInter fun i => (χd.isClopen_setOf_χ_eq P y i).isClosed

/-- **For a finite index set the prescribed locus of a family is open and closed**, being a
finite intersection of open and closed loci.  This finiteness is the first of the three cases in
which Stacks 0DPQ asserts an open and closed immersion. -/
theorem isClopen_prescribedLocus [Finite I] {T : BigFppfOver B S hS}
    (y : HilbertFamilyOver f T) : IsClopen (χd.prescribedLocus P y) :=
  isClopen_iInter_of_finite fun i => χd.isClopen_setOf_χ_eq P y i

/-- A base change of a family has the prescribed invariants exactly when the family's invariants
are the prescribed ones at the image points. -/
private theorem isPrescribed_baseChange_iff_forall {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (y : HilbertFamilyOver f T) :
    χd.IsPrescribed P (y.baseChange g) ↔
      ∀ (i : I) (t : points B S hS (yoneda.obj T')),
        χd.χ T y i (pointsMap B S hS (yoneda.obj T') (yoneda.map g) t) = P i :=
  forall₂_congr fun i t => by rw [χd.χ_baseChange]

/-- The membership condition is stable under base change: the invariants of the base change of a
family are the invariants of the family at the image points, so prescribing them is a condition
on the family that its base changes inherit. -/
theorem isPrescribed_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (y : HilbertFamilyOver f T) (h : χd.IsPrescribed P y) :
    χd.IsPrescribed P (y.baseChange g) :=
  (χd.isPrescribed_baseChange_iff_forall P g y).2 fun i _ => h i _

/-- **A base change of a family has the prescribed invariants exactly when the image of the point
space of the new test scheme lies in the prescribed locus.** -/
theorem isPrescribed_baseChange_iff_range_subset {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (y : HilbertFamilyOver f T) :
    χd.IsPrescribed P (y.baseChange g) ↔
      Set.range (pointsMap B S hS (yoneda.obj T') (yoneda.map g)) ⊆ χd.prescribedLocus P y :=
  (χd.isPrescribed_baseChange_iff_forall P g y).trans <| by
    rw [Set.range_subset_iff, forall_comm]
    simp [prescribedLocus]

/-- The subfunctor `Hilb^P_{X/Y} ⊆ Hilb_{X/Y}` of the families with the prescribed invariants,
on the Hilbert functor read on the schemes of the site.  It is a subfunctor because the
restriction maps are base change of families and the condition is stable under base change. -/
def numericalHilbertPresheaf : Subfunctor (hilbertPresheaf f) where
  obj _T := {y | χd.IsPrescribed P y}
  map i _y hy := χd.isPrescribed_baseChange P i.unop _ hy

/-- The sections of `Hilb^P_{X/Y}` over a scheme of the site are the families with the prescribed
invariants. -/
theorem mem_numericalHilbertPresheaf_iff (T : BigFppfOver B S hS)
    (y : (hilbertPresheaf f).obj (op T)) :
    y ∈ (χd.numericalHilbertPresheaf P).obj (op T) ↔ χd.IsPrescribed P y :=
  Iff.rfl

/-- **Distinct prescribed invariants cut out subfunctors with no family in common**, over a test
scheme that has a point: the invariants of a family at a point determine the prescription they
satisfy. -/
theorem not_isPrescribed_of_ne {P P' : I → ℤ} (hP : P ≠ P') {T : BigFppfOver B S hS}
    (t : points B S hS (yoneda.obj T)) (y : HilbertFamilyOver f T) (h : χd.IsPrescribed P y)
    (h' : χd.IsPrescribed P' y) : False :=
  hP (funext fun i => (h i t).symm.trans (h' i t))

end HilbertOverEulerData

end Invariants

/-! ### The subfunctor `Mor^P_Q(Z, X)` of relative morphisms, Stacks 0DPQ -/

section Numerical

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) {I : Type v}
    (χd : HilbertOverEulerData (graphAmbientMap B S hS z x hZ hX hQ) I) (P : I → ℤ)
    (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)

/-- **The graph of a section of the relative morphism functor**, as a point of the Hilbert functor
of `Z ×_Q X` over `Q`: the graph of Stacks 0D1A of the pair `(a, b)` the section corresponds to
under the bijection of Stacks 05Y2. -/
def graphFamilyOfSection (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T where
  toBase := (relativeHomSections B S hS Z X Q z x hZ hX hQ T s).base
  family := graphHilbertFamily hZ hX hQ (relativeHomSections B S hS Z X Q z x hZ hX hQ T s)
    hsep hfp hflat hproper

/-- The graph transformation of Stacks 0D1A takes a section of the relative morphism functor to
the graph of the pair it corresponds to. -/
theorem graphTransformation_app_eq_graphFamilyOfSection (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (graphTransformation hZ hX hQ hsep hfp hflat hproper).app (op T) (ULift.up s) =
      graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s :=
  rfl

/-- **The graph of a restricted section is the base change of the graph.**  This is the
naturality of the graph transformation of Stacks 0D1A. -/
theorem graphFamilyOfSection_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T'
        ((relativeHom B S hS Z X Q z x hZ hX hQ).map g.op s) =
      (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s).baseChange g := by
  have hsec : relativeHomSections B S hS Z X Q z x hZ hX hQ T'
        ((relativeHom B S hS Z X Q z x hZ hX hQ).map g.op s) =
      RelativeMorphism.restrict (yoneda.map g)
        (relativeHomSections B S hS Z X Q z x hZ hX hQ T s) :=
    relativeHomSections_map B S hS Z X Q z x hZ hX hQ g s
  refine Eq.trans (congrArg
    (fun q : RelativeMorphism B S hS Z X Q z x (yoneda.obj T') =>
      (⟨q.base, graphHilbertFamily hZ hX hQ q hsep hfp hflat hproper⟩ :
        HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T')) hsec) ?_
  exact HilbertFamilyOver.ext rfl (heq_of_eq (range_graphMap_restrict hZ hX hQ g _))

/-- **Stacks 0DPQ,** the subfunctor `Mor^P_Q(Z, X) ⊆ Mor_Q(Z, X)`: its sections over a scheme `T`
are the pairs `(a, b)` of Stacks 05Y1 at `T` whose graph, a point of `Hilb_{Z ×_Q X / Q}` over
`T` by Stacks 0D1A, has the prescribed invariants.  Since the graph transformation is the
inclusion `Mor_Q(Z, X) ⊆ Hilb_{Z ×_Q X / Q}` of Stacks 0D1B, this is the intersection
`Mor_Q(Z, X) ∩ Hilb^P_{Z ×_Q X / Q}` of the source, formed as an inverse image.

This is a subfunctor because the restriction maps of `Mor_Q(Z, X)` go to base change of graphs
and the condition on the invariants is stable under base change. -/
@[stacks 0DPQ "the definition of `Mor^P_B(Y, X)` as the subfunctor of `Mor_B(Y, X)` of relative \
morphisms whose graph has the prescribed invariants, with the open subspace of a test scheme \
that tests the source's open immersion for a finite index set; that \
`Mor^P_B(Y, X) ⟶ Mor_B(Y, X)` is a flat closed immersion rests on Lemmas 0DND and 0DNE, which \
are assertions about a morphism of algebraic stacks and are unavailable in this development, and \
is not stated"]
def numericalRelativeHom : Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) where
  obj T := {s | χd.IsPrescribed P
    (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T.unop s)}
  map {T T'} i s hs := by
    have h := χd.isPrescribed_baseChange P i.unop
      (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T.unop s) hs
    rwa [← graphFamilyOfSection_map B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper i.unop s]
      at h

/-- The sections of `Mor^P_Q(Z, X)` over a scheme are the pairs of Stacks 05Y1 whose graph has
the prescribed invariants. -/
theorem mem_numericalRelativeHom_iff (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    s ∈ (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper).obj (op T) ↔
      χd.IsPrescribed P
        (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s) :=
  Iff.rfl

/-- **The intersection of Stacks 0DPQ.**  A relative morphism lies in `Mor^P_Q(Z, X)` exactly
when its image under the inclusion `Mor_Q(Z, X) ⊆ Hilb_{Z ×_Q X / Q}` of Stacks 0D1B lies in
`Hilb^P_{Z ×_Q X / Q}`. -/
theorem mem_numericalRelativeHom_iff_mem_numericalHilbertPresheaf (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    s ∈ (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper).obj (op T) ↔
      (graphTransformation hZ hX hQ hsep hfp hflat hproper).app (op T) (ULift.up s) ∈
        (χd.numericalHilbertPresheaf P).obj (op T) :=
  Iff.rfl

/-- The inclusion `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)`: a relative morphism whose graph has the
prescribed invariants is in particular a relative morphism. -/
def numericalRelativeHomInclusion :
    (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper).toFunctor ⟶
      relativeHom B S hS Z X Q z x hZ hX hQ :=
  (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper).ι

/-- Each component of `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is injective: a relative morphism determines
the subtype element carrying it, the condition on the invariants being a proposition. -/
theorem injective_numericalRelativeHomInclusion_app (T : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective ((numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp
      hflat hproper).app T) :=
  fun _ _ h => Subtype.ext h

/-- **The morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a monomorphism.**  This is the part of the
source's "flat closed immersion" that a subfunctor inclusion carries unconditionally. -/
theorem mono_numericalRelativeHomInclusion :
    Mono (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) :=
  inferInstanceAs (Mono (Subfunctor.ι _))

/-- **Distinct prescribed invariants cut out subfunctors of `Mor_Q(Z, X)` with no relative
morphism in common**, over a test scheme that has a point. -/
theorem not_mem_numericalRelativeHom_of_ne {P P' : I → ℤ} (hP : P ≠ P')
    (T : BigFppfOver B S hS) (t : points B S hS (yoneda.obj T))
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T))
    (h : s ∈ (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper).obj
      (op T))
    (h' : s ∈ (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P' hsep hfp hflat hproper).obj
      (op T)) : False :=
  χd.not_isPrescribed_of_ne hP t _ h h'

/-! ### The locus in a test scheme on which the invariants are prescribed -/

/-- The morphism of presheaves attached to a morphism of the site is the one the Yoneda bijection
reads off from it. -/
private theorem yonedaEquiv_symm_eq_yoneda_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    (yonedaEquiv.symm g : yoneda.obj T' ⟶ yoneda.obj T) = yoneda.map g :=
  yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map g).symm

/-- **The open subspace of a test scheme on which a relative morphism has the prescribed
invariants**: the subspace of Stacks 03BZ cut out by the prescribed locus of its graph. -/
def prescribedLocusSubspace (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) : Subfunctor (yoneda.obj T) :=
  openSubspaceOfPoints B S hS (yoneda.obj T) (χd.prescribedLocus P
    (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s))

/-- **A morphism of test schemes restricts a relative morphism into `Mor^P_Q(Z, X)` exactly when
it factors through the open subspace cut out by the prescribed locus.** -/
theorem mem_prescribedLocusSubspace_iff (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) {T' : BigFppfOver B S hS}
    (g : T' ⟶ T) :
    g ∈ (prescribedLocusSubspace B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper T s).obj
        (op T') ↔
      (relativeHom B S hS Z X Q z x hZ hX hQ).map g.op s ∈
        (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper).obj
          (op T') := by
  rw [prescribedLocusSubspace, mem_openSubspaceOfPoints_iff,
    yonedaEquiv_symm_eq_yoneda_map B S hS g,
    mem_numericalRelativeHom_iff B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper,
    graphFamilyOfSection_map B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper g s]
  exact (χd.isPrescribed_baseChange_iff_range_subset P g _).symm

/-- The point set of the open subspace cut out by the prescribed locus is that locus. -/
theorem range_pointsMap_ι_prescribedLocusSubspace (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    Set.range (pointsMap B S hS
      (prescribedLocusSubspace B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper T s).toFunctor
      (prescribedLocusSubspace B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper T s).ι) =
      χd.prescribedLocus P
        (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s) :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- **For a finite index set the locus in a test scheme on which a relative morphism has the
prescribed invariants is an open subspace.**  Its point set is a finite intersection of open and
closed loci, hence open, and an open set of points of an algebraic space cuts out an open
subspace by Stacks 03BZ. -/
theorem isOpenSubspace_prescribedLocusSubspace [Finite I] (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    IsOpenSubspace B S hS
      (prescribedLocusSubspace B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper T s) :=
  isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS T) _
    (χd.isClopen_prescribedLocus P _).isOpen

end Numerical

end AlgebraicGeometry.Space

end
