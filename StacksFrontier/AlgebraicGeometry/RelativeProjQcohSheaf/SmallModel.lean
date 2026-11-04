module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Representable
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiSeparated

/-!
# The canonical small model of `F_d`, and where its smallness comes from

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), and fix an
integer `d`. Section 01NS attaches to `d` the functor `F_d` whose value on a test scheme `T` is
the set `F_d(T)` of strict equivalence classes of quadruples `(d, f : T → S, L, ψ)`, and **Tag
01NV** says that `F_d` is representable by a scheme.

`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Representable` states that tag with three
things carried: a `Type u`-valued Zariski sheaf `G` with bijections `G(T) ≃ F_d(T)`, the
compatibility of `G`'s restriction maps with those bijections, and the affine-local charts, which
are Tag 01NU. This file replaces the first two by the **canonical** small model and so removes
the compatibility hypothesis altogether, and it locates the smallness that the first one carries.

## The canonical small model

`F_d(T)` lives in `Type (u + 1)`, a quadruple recording an invertible module, while Mathlib's
form of Tag 01JJ (`AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`) is stated for
`Type u`-valued sheaves. Once the sets `F_d(T)` are known to be essentially small there is
nothing left to choose: `Fd.smallPresheaf` is `T ↦ Shrink (F_d(T))` with the restriction maps of
`F_d` conjugated by `equivShrink`, `Fd.smallEquiv` is the bijection, and the compatibility of the
two is `Fd.smallPresheaf_naturality`, a *theorem*. Whether this presheaf is a Zariski sheaf is
equivalent to whether `F_d` is one (`Fd.isSheaf_smallPresheaf_iff`), across the universe gap, by
`CategoryTheory.Presieve.isSheaf_iff_of_nat_equiv`.

## Smallness is not an artefact of the route

It is a consequence of the tag: a representation of `F_d` by a scheme `Y` is in particular a
bijection `F_d(T) ≃ (T ⟶ Y)` with a `Type u` set, so `Fd.small_of_representableBy`. No spelling
of Tag 01NV in terms of `CategoryTheory.Functor.RepresentableBy` can avoid it, cross-universe
though that structure is.

What smallness is *not* is independent of the affine-local charts. It is **local on the test
scheme** (`Fd.small_of_cover`, `Fd.small_of_openImmersion_cover`) by the separatedness of `F_d`,
which is proved unconditionally in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiSeparated`; and `F_d` restricted over
an open of `S` is covered by the opens over an affine cover of `S`, which gives
`Fd.small_of_baseCover`: smallness of all the sets `F_d(T)` follows from smallness of the sets of
classes whose morphism to `S` factors through a member of a cover of `S`. Those are the values of
the subfunctors `F_{d,i}` of the source's step (2), and their representability is step (3), that
is Tag 01NU. So the smallness half of what `G` carries is a consequence of Tag 01NU together with
an already-proved separatedness, and not a further assumption.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.smallPresheaf`: the canonical `Type
  u`-valued presheaf `T ↦ Shrink (F_d(T))`, for `F_d` with essentially small values.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.smallSheaf`: the same as a Zariski sheaf,
  given that `F_d` is one.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.small_of_representableBy`: **the smallness
  of the sets `F_d(T)` is a consequence of Tag 01NV**, so no statement of the tag can avoid it.
* `...Fd.small_of_cover`, `...Fd.small_of_openImmersion_cover`: the smallness of `F_d(T)` is
  local on `T`.
* `...Fd.small_of_baseCover`: and it follows from the smallness of the subfunctors of the
  source's step (2), hence from Tag 01NU.
* `...Fd.smallPresheaf_naturality`: the bijections of the canonical model are compatible with the
  restriction maps of `F_d` — this is the hypothesis `naturality` of
  `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_over_base`, discharged.
* `...Fd.isSheaf_smallPresheaf_iff`: the canonical model is a Zariski sheaf if and only if `F_d`
  is, across the universe gap.
* `...Fd.isSheaf_functor_of_exists_amalgamation`: `F_d` is a Zariski sheaf as soon as compatible
  families on covering sieves have amalgamations — the separatedness is already proved. That
  amalgamation half is in turn *equivalent* to a statement about quadruples with no sieve, no
  base morphism and no quotient in it, namely
  `...RelativeProjQcohSheaf.ZariskiAmalgamation.QuadrupleGlues`; see
  `...ZariskiAmalgamation.Fd.quadrupleGlues_iff_isSheaf`.
* `...Fd.exists_representableBy_functor_of_isSheaf` and `...Fd.isRepresentable_functor_of_isSheaf`:
  **Tag 01NV with the compatibility hypothesis discharged.** What is carried is the smallness of
  the sets `F_d(T)`, the Zariski sheaf property of `F_d`, and the charts of Tag 01NU.

## Not done here

Neither half of what `G` carried is proved **in this file**, and both are proved downstream.

The Zariski sheaf property of `F_d` is reduced here to its amalgamation half, and in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiAmalgamation` further to the
glueing of quadruples along a covering by opens; that glueing is **proved** in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleGluesProof.lean`
(`...RelativeProjQcohSheaf.quadrupleGlues_proof`), which yields `F_d` as a Zariski sheaf with no
hypothesis (`...RelativeProjQcohSheaf.Fd.isSheaf_functor`). The smallness of the sets `F_d(T)`
is reduced here to Tag 01NU (`Fd.small_of_baseCover`), and is **proved** outright, with no
reference to Tag 01NU, as the instance `...RelativeProjQcohSheaf.Fd.small` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleSmall.lean`.

Both of those files are downstream of this one, so the statements of Tag 01NV below bind the
sheaf property and the smallness regardless; the form of the tag that binds neither is
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts'` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean`. What remains
unproved anywhere is Tag 01NU in the form the charts want.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)

/-! ### The smallness of the values of `F_d` is a consequence of Tag 01NV -/

/-- **The smallness of the sets `F_d(T)` is a consequence of the representability of `F_d`.** A
representation of `F_d` by a scheme `Y` is a bijection `F_d(T) ≃ (T ⟶ Y)`, and the set of
morphisms of schemes `T ⟶ Y` lives in `Type u` while `F_d(T)` lives in `Type (u + 1)`.

`CategoryTheory.Functor.RepresentableBy` compares the two across the universe gap, so Tag 01NV
can be *stated* without any smallness assumption; what this says is that it cannot be *proved*
without one, because the smallness is part of its conclusion. -/
theorem Fd.small_of_representableBy {Y : Scheme.{u}}
    (e : (Fd.functor A d).RepresentableBy Y) (T : Scheme.{u}) : Small.{u} (Fd A d T) := by
  have h : Fd A d T ≃ (T ⟶ Y) := (e.homEquiv (X := T)).symm
  exact small_of_injective h.injective

/-- **The smallness of the sets `F_d(T)` is a consequence of the representability of `F_d`**, in
the form of the predicate; see `Fd.small_of_representableBy`. -/
theorem Fd.small_of_isRepresentable (h : (Fd.functor A d).IsRepresentable) (T : Scheme.{u}) :
    Small.{u} (Fd A d T) := by
  obtain ⟨Y, ⟨e⟩⟩ := h.has_representation
  exact Fd.small_of_representableBy A d e T

/-! ### The smallness of the values of `F_d` is local on the test scheme -/

/-- The sets `F_d(T)` are essentially small if the pullbacks along a family of morphisms into `T`,
read in essentially small sets, jointly detect equality. -/
private theorem Fd.small_of_pullback_eq {T : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ T) (hsmall : ∀ i, Small.{u} (Fd A d (Z i)))
    (h : ∀ ξ η : Fd A d T, (∀ i, Fd.pullback (g i) ξ = Fd.pullback (g i) η) → ξ = η) :
    Small.{u} (Fd A d T) := by
  have := hsmall
  refine small_of_injective (f := fun ξ : Fd A d T =>
    fun i => equivShrink (Fd A d (Z i)) (Fd.pullback (g i) ξ)) fun ξ η hξη => h ξ η fun i =>
    (equivShrink (Fd A d (Z i))).injective (congrFun hξη i)

/-- **The smallness of `F_d(T)` is local on `T`**: if the sets of classes on the members of an
open covering of `T` are essentially small, then so is `F_d(T)`.

A class is sent to the family of its restrictions to the members, read in the small models, and
that map is injective because `F_d` is a separated presheaf
(`Fd.eq_of_pullback_eq_of_cover`). -/
theorem Fd.small_of_cover {T : Scheme.{u}} {ι : Type u} (W : ι → T.Opens)
    (hW : ∀ x : T, ∃ a, x ∈ W a) (hsmall : ∀ a, Small.{u} (Fd A d (W a).toScheme)) :
    Small.{u} (Fd A d T) :=
  Fd.small_of_pullback_eq A d (fun a => (W a).ι) hsmall
    fun ξ η h => Fd.eq_of_pullback_eq_of_cover W hW ξ η h

/-- **The smallness of `F_d(T)` is local on `T`, for a covering by open immersions**, which is
the shape in which the Zariski topology on `Sch` presents its coverings. This is
`Fd.small_of_cover` with `Fd.eq_of_pullback_eq_of_openImmersion_cover` in place of
`Fd.eq_of_pullback_eq_of_cover`. -/
theorem Fd.small_of_openImmersion_cover {T : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ T) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ x : T, ∃ i, x ∈ (g i).opensRange) (hsmall : ∀ i, Small.{u} (Fd A d (Z i))) :
    Small.{u} (Fd A d T) :=
  Fd.small_of_pullback_eq A d g hsmall
    fun ξ η h => Fd.eq_of_pullback_eq_of_openImmersion_cover g hg ξ η h

/-- **The smallness of the values of `F_d` follows from the smallness of the subfunctors of the
source's step (2), hence from Tag 01NU.** Let `U` be a family of opens covering `S`, and suppose
that for every test scheme the set of classes whose morphism to `S` factors through a member of
the family is essentially small. Then every set `F_d(T)` is essentially small.

This is the reduction of the smallness that `Representable`'s hypothesis `G` carries to Tag 01NU:
the sets appearing in the hypothesis are the values of the subfunctors `F_{d,i} ⊆ F_d` of the
source's step (2), whose representability by a scheme — step (3), that is **Tag 01NU** — gives
bijections with `Type u` sets of morphisms and so gives the hypothesis.

The argument is the source's: a class `ξ` over `T` with morphism `f : T ⟶ S` restricts, on the
open `f ⁻¹ᵁ U i`, to a class whose morphism to `S` factors through `U i` by
`AlgebraicGeometry.morphismRestrict_ι`, those opens cover `T`, and `ξ` is determined by those
restrictions because `F_d` is separated. -/
theorem Fd.small_of_baseCover {ι : Type u} (U : ι → S.Opens) (hU : ∀ y : S, ∃ i, y ∈ U i)
    (hsmall : ∀ (i : ι) (W : Scheme.{u}),
      Small.{u} {ξ : Fd A d W // ∃ g : W ⟶ (U i).toScheme, g ≫ (U i).ι = ξ.1})
    (T : Scheme.{u}) : Small.{u} (Fd A d T) := by
  have := hsmall
  have key : ∀ f : T ⟶ S, Small.{u} {ξ : Fd A d T // ξ.1 = f} := by
    intro f
    refine small_of_injective (f := fun ξ : {ξ : Fd A d T // ξ.1 = f} => fun i : ι =>
      equivShrink _ (⟨Fd.pullback (f ⁻¹ᵁ U i).ι ξ.1,
        ⟨f ∣_ U i, by rw [Fd.pullback_fst, ξ.2]; exact morphismRestrict_ι f (U i)⟩⟩ :
        {ζ : Fd A d (f ⁻¹ᵁ U i).toScheme //
          ∃ g : (f ⁻¹ᵁ U i).toScheme ⟶ (U i).toScheme, g ≫ (U i).ι = ζ.1})) ?_
    intro ξ η h
    refine Subtype.ext (Fd.eq_of_pullback_eq_of_cover (fun i => f ⁻¹ᵁ U i) (fun x => ?_)
      ξ.1 η.1 fun i => ?_)
    · obtain ⟨i, hi⟩ := hU (f.base x)
      exact ⟨i, hi⟩
    · exact congrArg Subtype.val ((equivShrink _).injective (congrFun h i))
  have := key
  exact small_of_surjective (Equiv.sigmaFiberEquiv (fun ξ : Fd A d T => ξ.1)).surjective

/-! ### The canonical small model of `F_d` -/

section SmallModel

variable [∀ T : Scheme.{u}, Small.{u} (Fd A d T)]

/-- **The canonical `Type u`-valued model of the functor `F_d`**, for `F_d` with essentially
small values: its value on a test scheme is a `Type u` copy `Shrink (F_d(T))` of the set of
strict equivalence classes of quadruples, and its restriction maps are the pullback of a
quadruple conjugated by `equivShrink`.

Mathlib's form of Tag 01JJ, `AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`, is
stated for a `Type u`-valued sheaf, while `F_d(T)` lives in `Type (u + 1)`; this is the
replacement that the hypotheses `G` and `model` of
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_over_base` carry, made canonical.
Once the smallness is known there is nothing left to assume: the bijections are
`Fd.smallEquiv`, and their compatibility with the restriction maps of `F_d`, which is that
statement's hypothesis `naturality`, is the theorem `Fd.smallPresheaf_naturality`. -/
def Fd.smallPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (Fd A d T.unop)
  map φ := TypeCat.ofHom fun x =>
    equivShrink _ (Fd.pullback φ.unop ((equivShrink (Fd A d _)).symm x))
  map_id T := TypeCat.homEquiv.injective (funext fun x => by
    change equivShrink _ (Fd.pullback (𝟙 T.unop) ((equivShrink (Fd A d T.unop)).symm x)) = x
    rw [Fd.pullback_id, Equiv.apply_symm_apply])
  map_comp φ χ := TypeCat.homEquiv.injective (funext fun x => by
    change equivShrink _ (Fd.pullback (χ.unop ≫ φ.unop) ((equivShrink _).symm x))
      = equivShrink _ (Fd.pullback χ.unop ((equivShrink _).symm
          (equivShrink _ (Fd.pullback φ.unop ((equivShrink _).symm x)))))
    rw [Equiv.symm_apply_apply, Fd.pullback_comp])

/-- The value of `Fd.smallPresheaf` at `T` is `Shrink (Fd A d T.unop)`. -/
@[simp] theorem Fd.smallPresheaf_obj (T : Scheme.{u}ᵒᵖ) :
    (Fd.smallPresheaf A d).obj T = Shrink.{u} (Fd A d T.unop) := rfl

/-- The map of `Fd.smallPresheaf` along `φ` transports `Fd.pullback φ.unop` through
`equivShrink`. -/
@[simp] theorem Fd.smallPresheaf_map {T T' : Scheme.{u}ᵒᵖ} (φ : T ⟶ T')
    (x : (Fd.smallPresheaf A d).obj T) :
    (Fd.smallPresheaf A d).map φ x
      = equivShrink _ (Fd.pullback φ.unop ((equivShrink (Fd A d T.unop)).symm x)) := rfl

/-- **The bijection between the canonical small model of `F_d` and the sets `F_d(T)`.** -/
def Fd.smallEquiv (T : Scheme.{u}) : (Fd.smallPresheaf A d).obj (op T) ≃ Fd A d T :=
  (equivShrink (Fd A d T)).symm

/-- **The bijections of the canonical small model are compatible with the restriction maps of
`F_d`**: the class read off a restricted section is the pullback of the class read off the
section.

This is the hypothesis `naturality` of
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_over_base`, discharged for the
canonical model; `base_naturality` of
`...RelativeProjQcohSheaf.Fd.exists_representableBy_over_base` follows from it and
`Fd.pullback_fst`. -/
theorem Fd.smallPresheaf_naturality {T' T : Scheme.{u}} (k : T' ⟶ T)
    (x : (Fd.smallPresheaf A d).obj (op T)) :
    Fd.smallEquiv A d T' ((Fd.smallPresheaf A d).map k.op x)
      = Fd.pullback k (Fd.smallEquiv A d T x) := by
  simp only [Fd.smallEquiv, Fd.smallPresheaf_map]
  exact (equivShrink (Fd A d T')).symm_apply_apply _

/-- **The canonical small model is a Zariski sheaf exactly when `F_d` is**, across the universe
gap: the two are compared by the natural family of bijections `Fd.smallEquiv`, and being a sheaf
transports along such a family by `CategoryTheory.Presieve.isSheaf_iff_of_nat_equiv`, whose two
presheaves may be valued in different universes. -/
theorem Fd.isSheaf_smallPresheaf_iff :
    Presieve.IsSheaf Scheme.zariskiTopology.{u} (Fd.smallPresheaf A d) ↔
      Presieve.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d) :=
  Presieve.isSheaf_iff_of_nat_equiv (fun {T} => Fd.smallEquiv A d T)
    (fun {_ _} k x => Fd.smallPresheaf_naturality A d k x)

/-- **The canonical small model of `F_d` as a `Type u`-valued Zariski sheaf**, given that `F_d`
is a Zariski sheaf. This is the datum `G` of
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_over_base`, made canonical. -/
def Fd.smallSheaf (hsheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d)) :
    Sheaf Scheme.zariskiTopology.{u} (Type u) where
  obj := Fd.smallPresheaf A d
  property := (isSheaf_iff_isSheaf_of_type _ _).2
    ((Fd.isSheaf_smallPresheaf_iff A d).2 ((isSheaf_iff_isSheaf_of_type _ _).1 hsheaf))

/-- The underlying presheaf of `Fd.smallSheaf` is `Fd.smallPresheaf`. -/
@[simp] theorem Fd.smallSheaf_obj
    (hsheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d)) :
    (Fd.smallSheaf A d hsheaf).obj = Fd.smallPresheaf A d := rfl

end SmallModel

/-! ### What is left of step (1) -/

/-- **`F_d` is a Zariski sheaf as soon as compatible families have amalgamations.** The
separatedness half of the source's step (1) is proved unconditionally in
`...RelativeProjQcohSheaf.ZariskiSeparated.Fd.isSeparated_functor`, so only the existence of an
amalgamation is left, and this is `CategoryTheory.Presieve.IsSeparated.isSheaf` applied to it. -/
theorem Fd.isSheaf_functor_of_exists_amalgamation
    (hamalg : ∀ T : Scheme.{u}, ∀ Sv ∈ Scheme.zariskiTopology.{u} T,
      ∀ x : Presieve.FamilyOfElements (Fd.functor A d) (Sv : Sieve T).arrows, x.Compatible →
        ∃ t, x.IsAmalgamation t) :
    Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d) :=
  (isSheaf_iff_isSheaf_of_type _ _).2 ((Fd.isSeparated_functor A d).isSheaf hamalg)

/-! ### Tag 01NV with the compatibility hypothesis discharged -/

/-- **Stacks Project, Tag 01NV, conditionally, with the compatibility of the model discharged.**
The functor `F_d` of Section 01NS is representable by a scheme over `S`: there are a scheme `Y`, a
morphism `p : Y ⟶ S` and a representation of `F_d` by `Y` under which the morphism `T ⟶ Y`
representing a class `ξ ∈ F_d(T)`, composed with `p`, is the morphism `T ⟶ S` recorded by `ξ`.

This is `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_over_base` with the carried
`Type u`-valued sheaf `G`, the carried bijections `model` and the carried compatibility
`naturality` replaced by the canonical small model `Fd.smallPresheaf`, for which the
compatibility is the theorem `Fd.smallPresheaf_naturality`. What remains carried is therefore:

* the **smallness** of the sets `F_d(T)`, which by `Fd.small_of_representableBy` is a consequence
  of the conclusion and so cannot be dropped, and which by `Fd.small_of_baseCover` follows from
  Tag 01NU;
* the **Zariski sheaf property** of `F_d`, the source's step (1). It is a theorem — it is
  `...RelativeProjQcohSheaf.Fd.isSheaf_functor` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleGluesProof.lean` — but that file
  is **downstream** of this one, so the binder cannot be dropped here without making the import
  graph circular; the form of Tag 01NV that does not bind it is
  `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts'` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean`. Its
  separatedness half is `...ZariskiSeparated.Fd.isSeparated_functor`;
  `Fd.isSheaf_functor_of_exists_amalgamation` reduces it to the amalgamation half, and
  `...ZariskiAmalgamation.Fd.quadrupleGlues_iff_isSheaf` identifies that half with the glueing
  of quadruples along a covering by opens, which is what is proved downstream;
* the charts `c`, `hc`, `hcover`, that is the source's steps (2) and (3), namely **Tag 01NU**.
  Tag 01NU is proved over an affine base, and for Situation 01NN with `d ≥ 1` the charts are
  assembled from it in
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineOpenCharts.lean`
  (`...RelativeProjQcohSheaf.Fd.affineOpenChart` and its two properties), where the form of the
  tag that binds nothing, `...Fd.isRepresentable_functor_of_pos`, is stated; the binders stay
  here because this statement is more general than the tag, for an arbitrary graded algebra and
  an arbitrary integer `d`. -/
theorem Fd.exists_representableBy_functor_of_isSheaf
    [∀ T : Scheme.{u}, Small.{u} (Fd A d T)]
    (hsheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d))
    {ι : Type u} {X : ι → Scheme.{u}}
    (c : (i : ι) → yoneda.obj (X i) ⟶ Fd.smallPresheaf A d)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (e : (Fd.functor A d).RepresentableBy Y),
      ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1 :=
  Fd.exists_representableBy_functor_over_base A d (Fd.smallSheaf A d hsheaf)
    (Fd.smallEquiv A d) (fun {_ _} k x => Fd.smallPresheaf_naturality A d k x) c hc hcover

/-- **Stacks Project, Tag 01NV, conditionally, in the bare form, with the compatibility of the
model discharged.** This is `Fd.exists_representableBy_functor_of_isSheaf` forgetting the
structure morphism to `S`; see there for what is carried and what is proved. -/
theorem Fd.isRepresentable_functor_of_isSheaf
    [∀ T : Scheme.{u}, Small.{u} (Fd A d T)]
    (hsheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d))
    {ι : Type u} {X : ι → Scheme.{u}}
    (c : (i : ι) → yoneda.obj (X i) ⟶ Fd.smallPresheaf A d)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    (Fd.functor A d).IsRepresentable := by
  obtain ⟨Y, _, e, _⟩ := Fd.exists_representableBy_functor_of_isSheaf A d hsheaf c hc hcover
  exact ⟨Y, ⟨e⟩⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
