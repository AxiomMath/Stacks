module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalRelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatClosedLocus
public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.CategoryTheory.MorphismProperty.RelativeNatIso

/-!
# `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion (Stacks 0DPQ)

Let `z : Z ⟶ Q` be flat, proper and of finite presentation and `x : X ⟶ Q` separated and of
finite presentation, and let `Mor^P_Q(Z, X) ⊆ Mor_Q(Z, X)` be the subfunctor of relative
morphisms whose graph has prescribed numerical invariants
(`AlgebraicGeometry.Space.numericalRelativeHom`).  Stacks 0DPQ asserts that the inclusion
`Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion, and an open and closed immersion when
the index set `I` is finite.

The proof is the one of Stacks 0DND, read on the test schemes.  Over a test scheme `T` and a
relative morphism `s` over `T`, a morphism `T' ⟶ T` restricts `s` into `Mor^P_Q(Z, X)` exactly
when it maps `|T'|` into the locus of `|T|` on which every invariant of the graph of `s` takes its
prescribed value.  Each invariant is locally constant by Stacks 0D1Z, so the locus is an
intersection of open and closed subsets of `|T|`, which is the support of a flat closed subscheme
of `T` representing the base change of the inclusion
(`AlgebraicGeometry.Space.relative_closedImmersion_flat_ι`); for finite `I` the intersection is
finite, hence open, and the closed subscheme is an open subscheme.

## Main definitions

* `AlgebraicGeometry.Space.relativeHomGraphPreimage`: the subfunctor of `Mor_Q(Z, X)` of
  relative morphisms whose graph lies in a given subfunctor of `Hilb_{Z ×_Q X / Q}`.

## Main results

* `AlgebraicGeometry.Space.numericalRelativeHom_eq_relativeHomGraphPreimage`: `Mor^P_Q(Z, X)`
  is the pull-back of `Hilb^P_{Z ×_Q X / Q}` along the graph transformation.
* `AlgebraicGeometry.Space.IsCutOutByPoints.relativeHomGraphPreimage`,
  `AlgebraicGeometry.Space.isFlat_and_isClosedImmersion_relativeHomGraphPreimage_ι` and
  `AlgebraicGeometry.Space.isOpenImmersion_and_isClosedImmersion_relativeHomGraphPreimage_ι`:
  the pull-back of a subfunctor of `Hilb_{Z ×_Q X / Q}` cut out by sets of points is cut out by
  the same sets, so the corresponding assertions about `Hilb^P` give those about `Mor^P`.
* `AlgebraicGeometry.Space.isFlat_and_isClosedImmersion_graphPreimage_hilbertCondition_ι` and
  `AlgebraicGeometry.Space.isOpenImmersion_and_isClosedImmersion_graphPreimage_hilbertCondition_ι`:
  for a condition on `Coh_{Z ×_Q X / Q}` cut out on its test schemes by closed
  generalization-stable, respectively open and closed, sets, the corresponding subfunctor
  `Mor_Q(Z, X) ∩ Hilb^C_{Z ×_Q X / Q}` is a flat closed, respectively open and closed,
  subfunctor of `Mor_Q(Z, X)`; this is the route of the source through Stacks 0DPG, 0DP6 and
  0DND.
* `AlgebraicGeometry.Space.isCutOutByPoints_numericalRelativeHom`: the subfunctor
  `Mor^P_Q(Z, X)` is cut out, over every test scheme, by an intersection of open and closed sets
  of points.
* `AlgebraicGeometry.Space.isFlat_and_isClosedImmersion_numericalRelativeHomInclusion`:
  **Stacks 0DPQ**, the morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion.
* `AlgebraicGeometry.Space.isOpenImmersion_and_isClosedImmersion_numericalRelativeHomInclusion`:
  **Stacks 0DPQ**, for a finite index set it is an open and closed immersion.

## Implementation notes

The invariants are those of `AlgebraicGeometry.Space.HilbertOverEulerData`, through which
`Mor^P_Q(Z, X)` is defined; the two properties used are the ones recorded there, local constancy
through the étale-local description of Stacks 0D1Z and compatibility with base change.

Of the source's three sufficient conditions for an open and closed immersion, the finiteness of
`I` is the one treated here.  The other two are not: for `Q` locally Noetherian the source uses
that `Mor_Q(Z, X)` is an algebraic space locally of finite presentation over `Q` (Stacks 0D1C),
so that it is locally Noetherian and the intersection of the open and closed loci on an atlas
is open, and for `I = ℤ` with `E i = L^{⊗ i}` it uses the Noetherian approximation of
Stacks 0DNE, which is a statement about the twisted Euler characteristics themselves and not
about arbitrary locally constant invariants compatible with base change.

## References

* [Stacks Project, Tag 0DPQ](https://stacks.math.columbia.edu/tag/0DPQ)
* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe v u

attribute [local instance] pointTopology

section Numerical

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) {I : Type v}
    (χd : HilbertOverEulerData (graphAmbientMap B S hS z x hZ hX hQ) I) (P : I → ℤ)
    (hsep : IsSeparated B S hS x) (hfp : IsFinitePresentation B S hS z)
    (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)

/-- The invariants of the graph of a relative morphism over a test scheme, read on the scheme
points of the test scheme through the homeomorphism of Stacks 03BX. -/
def graphInvariantOnScheme (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) (i : I)
    (t : (BigFppfOver.toScheme B S hS).obj T) : ℤ :=
  χd.χ T (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s) i
    ((schemePointsHomeomorph B S hS T).symm t)

/-- The invariants of the graph of a relative morphism are locally constant on the test scheme,
by Stacks 0D1Z. -/
theorem isLocallyConstant_graphInvariantOnScheme (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) (i : I) :
    IsLocallyConstant
      (graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper T s i) :=
  (isLocallyConstant_of_isEtaleLocallyDerivedFibreChi B S hS (yoneda.obj T) _
    (isAlgebraicSpace_yoneda B S hS T) (χd.isEtaleLocally T _ i)).comp_continuous
    (schemePointsHomeomorph B S hS T).symm.continuous

/-- The invariants of the graph of a restricted relative morphism are those of the graph at the
image points. -/
theorem graphInvariantOnScheme_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) (i : I)
    (t : (BigFppfOver.toScheme B S hS).obj T') :
    graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper T'
        ((relativeHom B S hS Z X Q z x hZ hX hQ).map g.op s) i t =
      graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper T s i
        ((BigFppfOver.toScheme B S hS).map g t) := by
  simp only [graphInvariantOnScheme]
  rw [graphFamilyOfSection_map B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper g s,
    χd.χ_baseChange g _ i]
  congr 1
  apply (schemePointsHomeomorph B S hS T).injective
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply,
    pointsToScheme_pointsMap_yoneda, ← schemePointsHomeomorph_apply,
    Homeomorph.apply_symm_apply]

/-- A relative morphism lies in `Mor^P_Q(Z, X)` exactly when the invariants of its graph take the
prescribed values at every scheme point of the test scheme. -/
theorem mem_numericalRelativeHom_iff_graphInvariantOnScheme (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    s ∈ (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper).obj (op T) ↔
      ∀ i t, graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper T s i t =
        P i := by
  rw [mem_numericalRelativeHom_iff]
  exact forall_congr' fun i => (schemePointsHomeomorph B S hS T).symm.surjective.forall

/-- **The subfunctor `Mor^P_Q(Z, X)` is cut out by intersections of open and closed sets of
points**: over a test scheme and a relative morphism there, it is cut out by the locus on which
every invariant of the graph takes its prescribed value. -/
theorem isCutOutByPoints_numericalRelativeHom :
    IsCutOutByPoints.{0}
      (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper)
      fun _ W => IsClosed W ∧ StableUnderGeneralization W :=
  isCutOutByPoints_of_isLocallyConstant _ P
    (graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper)
    (isLocallyConstant_graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper)
    (fun _ _ g s i t =>
      graphInvariantOnScheme_map B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper g s i t)
    (mem_numericalRelativeHom_iff_graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd P hsep hfp
      hflat hproper)

/-- For a finite index set the subfunctor `Mor^P_Q(Z, X)` is cut out by open and closed sets of
points. -/
theorem isCutOutByPoints_isClopen_numericalRelativeHom [Finite I] :
    IsCutOutByPoints.{0}
      (numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper)
      fun _ W => IsClopen W :=
  isCutOutByPoints_isClopen_of_isLocallyConstant _ P
    (graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper)
    (isLocallyConstant_graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper)
    (fun _ _ g s i t =>
      graphInvariantOnScheme_map B S hS Z X Q z x hZ hX hQ χd hsep hfp hflat hproper g s i t)
    (mem_numericalRelativeHom_iff_graphInvariantOnScheme B S hS Z X Q z x hZ hX hQ χd P hsep hfp
      hflat hproper)

/-- A morphism of presheaves whose represented base changes are flat closed immersions is a flat
closed immersion. -/
private theorem isFlat_and_isClosedImmersion_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (h : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f) :
    IsFlat B S hS f ∧ IsClosedImmersion B S hS f :=
  ⟨presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS _
    (fun i p hi hp => by
      have : Etale i := hi
      have : Flat p := hp
      exact MorphismProperty.comp_mem _ _ _ inferInstance this) _
    (MorphismProperty.relative_monotone (fun _ _ _ h => h.2) _ h),
    MorphismProperty.relative_monotone (fun _ _ _ h => h.1) _ h⟩

/-- A morphism of presheaves whose represented base changes are open and closed immersions is an
open and closed immersion. -/
private theorem isOpenImmersion_and_isClosedImmersion_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (h : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f) :
    IsOpenImmersion B S hS f ∧ IsClosedImmersion B S hS f :=
  ⟨MorphismProperty.relative_monotone (fun _ _ _ h => h.1) _ h,
    MorphismProperty.relative_monotone (fun _ _ _ h => h.2) _ h⟩

/-- Every represented base change of `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion of
schemes. -/
theorem presheaf_closedImmersion_flat_numericalRelativeHomInclusion :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
      (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) :=
  (MorphismProperty.presheaf_iff_relative_uliftYoneda _ _).2
    (relative_closedImmersion_flat_ι _
      (isCutOutByPoints_numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat
        hproper))

/-- The morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a closed immersion. -/
theorem isClosedImmersion_numericalRelativeHomInclusion :
    IsClosedImmersion B S hS
      (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) :=
  (isFlat_and_isClosedImmersion_of_presheaf B S hS
    (presheaf_closedImmersion_flat_numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P
      hsep hfp hflat hproper)).2

/-- The morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is flat: its represented base changes are flat,
and flatness passes from them to the étale charts. -/
theorem isFlat_numericalRelativeHomInclusion :
    IsFlat B S hS
      (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) :=
  (isFlat_and_isClosedImmersion_of_presheaf B S hS
    (presheaf_closedImmersion_flat_numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd
      P hsep hfp hflat hproper)).1

/-- For a finite index set the morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open immersion. -/
theorem isOpenImmersion_numericalRelativeHomInclusion [Finite I] :
    IsOpenImmersion B S hS
      (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) :=
  (isOpenImmersion_and_isClosedImmersion_of_presheaf B S hS
    ((MorphismProperty.presheaf_iff_relative_uliftYoneda _ _).2
      (relative_openImmersion_closedImmersion_ι _
        (isCutOutByPoints_isClopen_numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp
          hflat hproper)))).1

/-- **Stacks 0DPQ.**  The morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion. -/
@[stacks 0DPQ "`Mor^P_B(Y, X) ⟶ Mor_B(Y, X)` is a flat closed immersion"]
theorem isFlat_and_isClosedImmersion_numericalRelativeHomInclusion :
    IsFlat B S hS
        (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) ∧
      IsClosedImmersion B S hS
        (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) :=
  ⟨isFlat_numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper,
    isClosedImmersion_numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat
      hproper⟩

/-- **Stacks 0DPQ, the case of a finite index set.**  For `I` finite the morphism
`Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion. -/
@[stacks 0DPQ "for `I` finite, `Mor^P_B(Y, X) ⟶ Mor_B(Y, X)` is an open and closed immersion"]
theorem isOpenImmersion_and_isClosedImmersion_numericalRelativeHomInclusion [Finite I] :
    IsOpenImmersion B S hS
        (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) ∧
      IsClosedImmersion B S hS
        (numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper) :=
  ⟨isOpenImmersion_numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat
      hproper,
    isClosedImmersion_numericalRelativeHomInclusion B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat
      hproper⟩

/-! ### Subfunctors of `Mor_Q(Z, X)` pulled back from `Hilb_{Z ×_Q X / Q}` -/

/-- The subfunctor of `Mor_Q(Z, X)` pulled back along the graph transformation of Stacks 0D1A
from a subfunctor `G` of `Hilb_{Z ×_Q X / Q}`: the relative morphisms whose graph lies in `G`.
For `G = Hilb^P_{Z ×_Q X / Q}` this is the intersection `Mor_Q(Z, X) ∩ Hilb^P_{Z ×_Q X / Q}` of
Stacks 0DPQ. -/
def relativeHomGraphPreimage
    (G : Subfunctor (hilbertPresheaf (graphAmbientMap B S hS z x hZ hX hQ))) :
    Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) where
  obj T := {s | (graphTransformation hZ hX hQ hsep hfp hflat hproper).app T (ULift.up s) ∈ G.obj T}
  map {T T'} g s hs := by
    have h := G.map g hs
    let s' : (relativeHom B S hS Z X Q z x hZ hX hQ ⋙ uliftFunctor.{u + 1, u}).obj T := ULift.up s
    have e := NatTrans.naturality_apply (graphTransformation hZ hX hQ hsep hfp hflat hproper) g s'
    change (graphTransformation hZ hX hQ hsep hfp hflat hproper).app T'
      ((relativeHom B S hS Z X Q z x hZ hX hQ ⋙ uliftFunctor.{u + 1, u}).map g s') ∈ G.obj T'
    rw [e]
    exact h

/-- A relative morphism lies in the pulled-back subfunctor exactly when its graph lies in `G`. -/
theorem mem_relativeHomGraphPreimage_iff
    (G : Subfunctor (hilbertPresheaf (graphAmbientMap B S hS z x hZ hX hQ)))
    {T : (BigFppfOver B S hS)ᵒᵖ} (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj T) :
    s ∈ (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper G).obj T ↔
      (graphTransformation hZ hX hQ hsep hfp hflat hproper).app T (ULift.up s) ∈ G.obj T :=
  Iff.rfl

/-- **`Mor^P_Q(Z, X)` is the pull-back of `Hilb^P_{Z ×_Q X / Q}` along the graph
transformation.** -/
theorem numericalRelativeHom_eq_relativeHomGraphPreimage :
    numericalRelativeHom B S hS Z X Q z x hZ hX hQ χd P hsep hfp hflat hproper =
      relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper
        (χd.numericalHilbertPresheaf P) :=
  rfl

/-- **Being cut out by sets of points passes from a subfunctor of `Hilb_{Z ×_Q X / Q}` to its
pull-back to `Mor_Q(Z, X)`**, by the same sets: the graph transformation commutes with
restriction. -/
theorem IsCutOutByPoints.relativeHomGraphPreimage
    {G : Subfunctor (hilbertPresheaf (graphAmbientMap B S hS z x hZ hX hQ))}
    {p : ∀ U : BigFppfOver B S hS, Set ((BigFppfOver.toScheme B S hS).obj U) → Prop}
    (hG : IsCutOutByPoints.{u + 1} G p) :
    IsCutOutByPoints.{0}
      (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper G) p := by
  intro U s
  obtain ⟨W, hW, hGW⟩ := hG U ((graphTransformation hZ hX hQ hsep hfp hflat hproper).app _
    (ULift.up s))
  refine ⟨W, hW, fun V h => ?_⟩
  rw [← hGW h, mem_relativeHomGraphPreimage_iff]
  have e := NatTrans.naturality_apply (graphTransformation hZ hX hQ hsep hfp hflat hproper) h.op
    (show (relativeHom B S hS Z X Q z x hZ hX hQ ⋙ uliftFunctor.{u + 1, u}).obj (op U) from
      ULift.up s)
  exact ⟨fun hm => e ▸ hm, fun hm => e.symm ▸ hm⟩

/-- **The pull-back to `Mor_Q(Z, X)` of a subfunctor of `Hilb_{Z ×_Q X / Q}` cut out by closed,
generalization-stable sets of points is a flat closed subfunctor.**  Applied to
`Hilb^P_{Z ×_Q X / Q}` this is the deduction of the first assertion of Stacks 0DPQ from the
corresponding assertion of Stacks 0DPG. -/
theorem isFlat_and_isClosedImmersion_relativeHomGraphPreimage_ι
    {G : Subfunctor (hilbertPresheaf (graphAmbientMap B S hS z x hZ hX hQ))}
    (hG : IsCutOutByPoints.{u + 1} G fun _ W => IsClosed W ∧ StableUnderGeneralization W) :
    IsFlat B S hS (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper G).ι ∧
      IsClosedImmersion B S hS
        (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper G).ι := by
  exact isFlat_and_isClosedImmersion_of_presheaf B S hS
    ((MorphismProperty.presheaf_iff_relative_uliftYoneda _ _).2
      (relative_closedImmersion_flat_ι _
        (hG.relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper)))

/-- **The pull-back to `Mor_Q(Z, X)` of a subfunctor of `Hilb_{Z ×_Q X / Q}` cut out by open and
closed sets of points is an open and closed subfunctor.**  Applied to `Hilb^P_{Z ×_Q X / Q}` this
deduces each case of the second assertion of Stacks 0DPQ from the same case of Stacks 0DPG. -/
theorem isOpenImmersion_and_isClosedImmersion_relativeHomGraphPreimage_ι
    {G : Subfunctor (hilbertPresheaf (graphAmbientMap B S hS z x hZ hX hQ))}
    (hG : IsCutOutByPoints.{u + 1} G fun _ W => IsClopen W) :
    IsOpenImmersion B S hS
        (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper G).ι ∧
      IsClosedImmersion B S hS
        (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper G).ι := by
  exact isOpenImmersion_and_isClosedImmersion_of_presheaf B S hS
    ((MorphismProperty.presheaf_iff_relative_uliftYoneda _ _).2
      (relative_openImmersion_closedImmersion_ι _
        (hG.relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper)))

/-- **`Mor_Q(Z, X) ∩ Hilb^C_{Z ×_Q X / Q}` for a flat closed condition `C` on
`Coh_{Z ×_Q X / Q}`.**  When `C` is cut out on the test schemes of `Coh_{Z ×_Q X / Q}` by closed
sets stable under generalization, the relative morphisms whose graph, read in `Coh` through
Stacks 0D00 and Stacks 0DP6, satisfies `C` form a flat closed subfunctor of `Mor_Q(Z, X)`.  For
`C` the numerical condition of Stacks 0DNC this is the first assertion of Stacks 0DPQ, deduced
from the corresponding assertion about `Hilb^P` as in the source. -/
theorem isFlat_and_isClosedImmersion_graphPreimage_hilbertCondition_ι
    (hx_fp : IsFinitePresentation B S hS x)
    {C : CoherentObject (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
      (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation → Prop}
    (hC : ∀ {A' A}, CoherentHom A' A → C A → C A')
    (hcut : CoherentSituation.IsCutOutOnTestSchemes _ C
      fun _ W => IsClosed W ∧ StableUnderGeneralization W) :
    IsFlat B S hS (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper
        (hilbertCondition _ _ C hC)).ι ∧
      IsClosedImmersion B S hS (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp
        hflat hproper (hilbertCondition _ _ C hC)).ι :=
  isFlat_and_isClosedImmersion_relativeHomGraphPreimage_ι B S hS Z X Q z x hZ hX hQ hsep hfp
    hflat hproper ((QuotSituation.isCutOutByPoints_quotCondition _ hC hcut).preimage _)

/-- **`Mor_Q(Z, X) ∩ Hilb^C_{Z ×_Q X / Q}` for an open and closed condition `C` on
`Coh_{Z ×_Q X / Q}`** is an open and closed subfunctor of `Mor_Q(Z, X)`.  This deduces each case
of the second assertion of Stacks 0DPQ from the same case for `Coh^P` (Stacks 0DND, 0DNE). -/
theorem isOpenImmersion_and_isClosedImmersion_graphPreimage_hilbertCondition_ι
    (hx_fp : IsFinitePresentation B S hS x)
    {C : CoherentObject (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
      (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation → Prop}
    (hC : ∀ {A' A}, CoherentHom A' A → C A → C A')
    (hcut : CoherentSituation.IsCutOutOnTestSchemes _ C fun _ W => IsClopen W) :
    IsOpenImmersion B S hS (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat
        hproper (hilbertCondition _ _ C hC)).ι ∧
      IsClosedImmersion B S hS (relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp
        hflat hproper (hilbertCondition _ _ C hC)).ι :=
  isOpenImmersion_and_isClosedImmersion_relativeHomGraphPreimage_ι B S hS Z X Q z x hZ hX hQ
    hsep hfp hflat hproper ((QuotSituation.isCutOutByPoints_quotCondition _ hC hcut).preimage _)

end Numerical

end AlgebraicGeometry.Space

end
