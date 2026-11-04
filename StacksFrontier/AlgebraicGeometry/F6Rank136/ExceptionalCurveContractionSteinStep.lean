module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionExistence
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FiniteFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Permanence

/-!
# The Stein reduction in the existence of a contraction of an exceptional curve

[Stacks, Tag 0C2L] asserts that a contraction of an exceptional curve of the first kind `E ⊆ X`
exists as soon as there is a proper morphism `f : X ⟶ Y` to a Noetherian scheme which carries `E`
to a single point `y` and is quasi-finite at every point off `E`. Its proof opens by replacing
`f` by the first factor of its Stein factorization ([Stacks, Tag 03H0]), so that one may
additionally assume `f_* 𝒪_X = 𝒪_Y` and that the fibres of `f` are geometrically connected.

This file carries out that first step, unconditionally. Writing `Y' = f.normalization`,
`f' = f.toNormalization` and `π = f.fromNormalization` for the witnesses of the Stein
factorization, every hypothesis of the tag is inherited by `f'`:

* `Y'` is Noetherian, because `π` is finite and `Y` is Noetherian;
* `f'` is proper, which is [Stacks, Tag 03H2];
* `f'` still carries `E` to a *single* point `y'`, and that point lies over `y`. This is where
  the geometry enters: `E` is connected, being a presentation of `𝐏¹_k`, so its image under `f'`
  is a connected subset of the fibre `π⁻¹(y)`, and that fibre is finite
  (`Stacks.SteinFactorization.finite_preimage_singleton_fromNormalization`) and T1
  (`Stacks.SteinFactorization.t1Space_fiber_of_isIntegralHom`, `π` being integral), hence
  totally disconnected;
* `f'` is quasi-finite at every point off `E`, by [Stacks, Tag 03WR]
  (`AlgebraicGeometry.quasiFiniteAt_of_comp`) applied to `f = f' ≫ π`;
* and `{y'}` is closed, because `f'` is proper and `E` is closed and nonempty.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isConnected_support_of_iso_projectiveLineProj` — the
  support of an ideal sheaf whose subscheme is a copy of `𝐏¹_k` is connected and nonempty.
* `AlgebraicGeometry.isClosed_singleton_of_isProper_of_forall_base_eq` and
  `AlgebraicGeometry.isClosed_singleton_of_isProper_of_forall_subschemeι_base_eq` — a proper
  morphism carries a nonempty closed set, in particular an exceptional curve, to a closed point.
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying`
  — the existence statement of
  `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying` with its
  binder `hy` discharged from the properness of `f`.
* `AlgebraicGeometry.exists_forall_toNormalization_base_eq` — the first factor of the Stein
  factorization of a proper morphism carries a connected set lying over a point `y` to a single
  point over `y`.
* `AlgebraicGeometry.quasiFiniteAt_toNormalization` — quasi-finiteness at a point passes to the
  first factor of the Stein factorization.
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinCase` — the reduction: to
  prove [Stacks, Tag 0C2L] it is enough to prove it for a morphism whose fibres are
  geometrically connected and which satisfies `f_* 𝒪_X = 𝒪_Y`.

## What 0C2L still asks for

The tag is not registered here. What remains after this reduction is the body of the source's
proof: that `𝒪_{Y', y'}` is regular of dimension two, and that the scheme-theoretic fibre of
`f'` over `y'` is exactly `E`. Those are the binders `hreg`, `hdim` and `hfibre` of
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying`, together
with its `hclassify`; the implementation notes of
`StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionExistence.lean` say what each
of them needs.

On `hclassify` in particular: the iso criterion the source closes with is *not* [Stacks, Tag
0AB1] but Varieties, Lemma 33.17.3, [Stacks, Tag 0BFP] item (4) — the maximal open over which a
proper birational morphism with reduced source is an isomorphism contains every point whose
*local ring* is normal and which has a preimage at which the morphism is quasi-finite. That
asks for normality only at a point, which is what the source has (`Bl_y Y` is regular, hence
normal, at the points of its exceptional curve, and nothing is assumed about `Y` away from
`y`), and it is already available here as
`AlgebraicGeometry.mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal`. [Stacks, Tag
0AB1] (`AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal`) states its own
tag faithfully — integral schemes, an integral morphism, a globally normal target — and is
simply a different lemma from the one this step uses; making it more general is not the route to
`hclassify`.

What `hclassify` does still want, beyond that criterion: that the classifying morphism `g` to
`Bl_y Y` is proper and birational and that `X` is reduced; that `g` is an isomorphism away from
the exceptional curve of `Bl_y Y`, which the source obtains from `f_* 𝒪_X = 𝒪_Y` together with
quasi-finiteness off `E` — data carried by the hypothesis `H` of
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinCase` below and *not* by the
binders of
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying`,
so the two have to be used together; regularity of `Bl_y Y` along that curve; and the conormal
sheaf comparison of [Stacks, Tag 01R4], which is what makes the induced map of exceptional
curves non-constant and hence quasi-finite.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 03WR](https://stacks.math.columbia.edu/tag/03WR)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The support of a presented copy of `𝐏¹_k` is connected and nonempty.** If the closed
subscheme cut out by `D` is isomorphic to the projective line over a field, then the closed set
`D.support` carrying it is connected: it is the range of a continuous map out of the projective
line, which is integral, hence irreducible, hence connected and nonempty. -/
public theorem Scheme.IdealSheafData.isConnected_support_of_iso_projectiveLineProj
    {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme) :
    _root_.IsConnected (D.support : Set X) := by
  have hsurj : Function.Surjective e.hom.base := e.hom.homeomorph.surjective
  have hrange : Set.range (D.subschemeι.base ∘ e.hom.base) = (D.support : Set X) := by
    rw [hsurj.range_comp, D.range_subschemeι]
  rw [← hrange]
  exact isConnected_range (by fun_prop)

/-- The two ways of saying that a morphism carries the subscheme cut out by `D` to the point
`y`: pointwise on the subscheme, as [Stacks, Tag 0C5J] asks for it, and as a condition on the
support of `D`. -/
public theorem Scheme.IdealSheafData.forall_subschemeι_base_eq_iff_forall_mem_support
    {X Y : Scheme.{u}} (D : X.IdealSheafData) (f : X ⟶ Y) (y : Y) :
    (∀ z : D.subscheme, f.base (D.subschemeι.base z) = y) ↔
      ∀ x ∈ (D.support : Set X), f.base x = y := by
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := (D.range_subschemeι ▸ hx : x ∈ Set.range D.subschemeι.base)
    exact h z
  · intro h z
    exact h _ (D.range_subschemeι ▸ Set.mem_range_self z)

/-- **A proper morphism carries a nonempty closed set to a closed point.** If every point of a
nonempty closed set `Z ⊆ X` is sent to `y` by a proper morphism `f : X ⟶ Y`, then `{y}` is
closed in `Y`, because `f` is a closed map and `f '' Z = {y}`. -/
public theorem isClosed_singleton_of_isProper_of_forall_base_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (Z : Closeds X) (hne : (Z : Set X).Nonempty)
    (y : Y) (hmaps : ∀ x ∈ (Z : Set X), f.base x = y) :
    IsClosed ({y} : Set Y) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have himage : f.base '' (Z : Set X) = {y} := by
    refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 ⟨x₀, hx₀, hmaps x₀ hx₀⟩)
    rintro - ⟨x, hx, rfl⟩
    exact hmaps x hx
  exact himage ▸ f.isClosedMap _ Z.isClosed

/-- **The point an exceptional curve is carried to by a proper morphism is closed.** If the
subscheme cut out by `D` is isomorphic to `𝐏¹_k` and the proper morphism `f` maps every point of
it to `y`, then `{y}` is closed in `Y`.

This discharges the binder `hy` of
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying` from the
hypotheses [Stacks, Tag 0C2L] actually grants: the subscheme cut out by `D` is a copy of `𝐏¹_k`,
hence nonempty, and its support is closed, so its image under a proper morphism is a closed
point. -/
public theorem isClosed_singleton_of_isProper_of_forall_subschemeι_base_eq
    {X Y : Scheme.{u}} {D : X.IdealSheafData} {k : Type u} [Field k]
    (e : projectiveLineProj k ≅ D.subscheme) (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y) :
    IsClosed ({y} : Set Y) :=
  isClosed_singleton_of_isProper_of_forall_base_eq f D.support
    (D.isConnected_support_of_iso_projectiveLineProj k e).1 y
    ((D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hmaps)

/-- **A contraction of an exceptional curve of the first kind exists**, under the hypotheses of
[Stacks, Tag 0C2L] on `f` together with the three steps of that proof which this development
cannot yet perform. Against
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying` the binder
`hy` has been removed: that `{y}` is closed now follows from the properness of `f`, so `hfibre`
and `hclassify` are stated for the derived closedness. What remains carried is `hreg` and `hdim`,
that `𝒪_{Y, y}` is regular of dimension two, `hfibre`, that the scheme-theoretic fibre over `y`
is `E`, and `hclassify`, that the classifying morphism to the blowup at `y` is an
isomorphism. -/
public theorem exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying
    {X Y : Scheme.{u}} [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hfibre : ∀ hy : IsClosed ({y} : Set Y),
      D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f)
    (hclassify : ∀ (hy : IsClosed ({y} : Set Y)) (g : X ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))),
      g ≫ AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f → IsIso g) :
    ∃ (Z : Scheme.{u}) (b : X ⟶ Z), IsContractionOfExceptionalCurve D b :=
  have hy : IsClosed ({y} : Set Y) :=
    isClosed_singleton_of_isProper_of_forall_subschemeι_base_eq e f y hmaps
  exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying hE y hy hreg hdim f
    (hfibre hy) (hclassify hy)

/-- **The fibres of the second factor of a Stein factorization are totally disconnected.** The
fibre of `π = f.fromNormalization` over a point is finite ([Stacks, Tag 0E0M]) and T1, `π` being
integral, so it carries no connected subset with more than one point. -/
public theorem isTotallyDisconnected_preimage_fromNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) :
    IsTotallyDisconnected (f.fromNormalization.base ⁻¹' {y}) := by
  have : T1Space (f.fromNormalization.fiber y) :=
    Stacks.SteinFactorization.t1Space_fiber_of_isIntegralHom f.fromNormalization y
  have : T1Space ↥(f.fromNormalization.base ⁻¹' {y}) :=
    (f.fromNormalization.fiberHomeo y).t1Space
  have : Finite ↥(f.fromNormalization.base ⁻¹' {y}) :=
    Set.finite_coe_iff.mpr
      (Stacks.SteinFactorization.finite_preimage_singleton_fromNormalization f y)
  exact totallyDisconnectedSpace_subtype_iff.mp inferInstance

/-- **The normalization of a Noetherian scheme in a proper scheme over it is Noetherian.** The
second factor `π = f.fromNormalization` of the Stein factorization is finite, so it is locally of
finite type and quasi-compact, and both halves of Noetherianness descend along it. -/
public theorem isNoetherian_normalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsProper f] :
    IsNoetherian f.normalization := by
  have := Stacks.SteinFactorization.isFinite_fromNormalization f
  have := LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  have := QuasiCompact.compactSpace_of_compactSpace f.fromNormalization
  exact ⟨⟩

/-- **The first factor of a Stein factorization still contracts a connected set to a point.**
Let `f : X ⟶ Y` be proper and let `Z ⊆ X` be a connected set every point of which `f` sends to
`y`. Then the first factor `f' = f.toNormalization` of the Stein factorization of `f` sends every
point of `Z` to one and the same point `y'`, and `y'` lies over `y`.

The image `f' '' Z` is connected and nonempty and lies inside the fibre of
`π = f.fromNormalization` over `y`, which is totally disconnected
(`AlgebraicGeometry.isTotallyDisconnected_preimage_fromNormalization`). -/
public theorem exists_forall_toNormalization_base_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (Z : Set X) (hZ : _root_.IsConnected Z)
    (y : Y) (hmaps : ∀ x ∈ Z, f.base x = y) :
    ∃ y' : f.normalization, (∀ x ∈ Z, f.toNormalization.base x = y') ∧
      f.fromNormalization.base y' = y := by
  have hcomp : f.toNormalization ≫ f.fromNormalization = f :=
    Stacks.SteinFactorization.toNormalization_fromNormalization f
  have hbase : ∀ x : X, f.fromNormalization.base (f.toNormalization.base x) = f.base x := fun x ↦
    congrFun (congrArg (fun g : X ⟶ Y ↦ (g.base : X → Y)) hcomp) x
  have hsub : f.toNormalization.base '' Z ⊆ f.fromNormalization.base ⁻¹' {y} := by
    rintro - ⟨x, hx, rfl⟩
    exact Set.mem_preimage.2 (Set.mem_singleton_iff.2 ((hbase x).trans (hmaps x hx)))
  have hconn : _root_.IsPreconnected (f.toNormalization.base '' Z) :=
    hZ.2.image _ f.toNormalization.continuous.continuousOn
  have hsingle : (f.toNormalization.base '' Z).Subsingleton :=
    isTotallyDisconnected_preimage_fromNormalization f y _ hsub hconn
  obtain ⟨x₀, hx₀⟩ := hZ.1
  refine ⟨f.toNormalization.base x₀, fun x hx ↦ ?_, (hbase x₀).trans (hmaps x₀ hx₀)⟩
  exact hsingle ⟨x, hx, rfl⟩ ⟨x₀, hx₀, rfl⟩

/-- **Quasi-finiteness at a point passes to the first factor of a Stein factorization.** This is
[Stacks, Tag 03WR] applied to the factorization `f = f.toNormalization ≫ f.fromNormalization`. -/
public theorem quasiFiniteAt_toNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (x : X) (h : quasiFiniteAt f x) :
    quasiFiniteAt f.toNormalization x := by
  refine quasiFiniteAt_of_comp f.toNormalization f.fromNormalization x ?_
  rwa [Stacks.SteinFactorization.toNormalization_fromNormalization f]

/-- **The Stein reduction for [Stacks, Tag 0C2L].** To produce a contraction of an exceptional
curve of the first kind `E ⊆ X` from a proper morphism `f : X ⟶ Y` to a Noetherian scheme which
carries `E` to a point and is quasi-finite at every point off `E`, it is enough to do so for such
a morphism that is moreover geometrically connected and satisfies `f_* 𝒪_X = 𝒪_Y`: replace `f` by
the first factor of its Stein factorization, which inherits every hypothesis.

The hypothesis `H` is the tag's statement for that special case, with the extra data the Stein
factorization provides: the fibres of `f'` are geometrically connected, the canonical map
`𝒪_{Y'} ⟶ f'_* 𝒪_X` is an isomorphism, and the point `y'` that `E` is carried to is closed. -/
public theorem exists_isContractionOfExceptionalCurve_of_steinCase
    {X Y : Scheme.{u}} [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u} [Field k]
    (e : projectiveLineProj k ≅ D.subscheme) (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x)
    (H : ∀ (Y' : Scheme.{u}) (_ : IsNoetherian Y') (f' : X ⟶ Y') (_ : IsProper f')
      (_ : GeometricallyConnected f') (_ : IsIso f'.c) (y' : Y') (_ : IsClosed ({y'} : Set Y'))
      (_ : ∀ z : D.subscheme, f'.base (D.subschemeι.base z) = y')
      (_ : ∀ x ∉ (D.support : Set X), quasiFiniteAt f' x),
      ∃ (Z : Scheme.{u}) (b : X ⟶ Z), IsContractionOfExceptionalCurve D b) :
    ∃ (Z : Scheme.{u}) (b : X ⟶ Z), IsContractionOfExceptionalCurve D b := by
  have hconn : _root_.IsConnected (D.support : Set X) :=
    D.isConnected_support_of_iso_projectiveLineProj k e
  have hmaps' : ∀ x ∈ (D.support : Set X), f.base x = y :=
    (D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hmaps
  obtain ⟨y', hy'maps, -⟩ :=
    exists_forall_toNormalization_base_eq f (D.support : Set X) hconn y hmaps'
  have := Stacks.SteinFactorization.isProper_toNormalization f
  exact H f.normalization (isNoetherian_normalization f) f.toNormalization inferInstance
    (Stacks.SteinFactorization.geometricallyConnected_toNormalization f)
    (Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper f) y'
    (isClosed_singleton_of_isProper_of_forall_base_eq f.toNormalization D.support hconn.1 y'
      hy'maps)
    ((D.forall_subschemeι_base_eq_iff_forall_mem_support f.toNormalization y').2 hy'maps)
    fun x hx ↦ quasiFiniteAt_toNormalization f x (hqf x hx)

end AlgebraicGeometry

end
