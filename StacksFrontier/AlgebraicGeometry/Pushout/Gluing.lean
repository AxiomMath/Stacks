module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.PushoutSituation
public import StacksFrontier.AlgebraicGeometry.Pushout.Chart

/-!
# Pushouts along a closed immersion and an integral morphism

In the standing situation of [Stacks Project, Tag 0ECI] — a closed immersion `i : Z ⟶ X` and an
integral morphism `j : Z ⟶ Y`, subject to the condition that every fibre of `j` maps under `i`
into a single affine open of `X` — the pushout `Y ⨿_Z X` exists as a scheme.  Its defining
square is also cartesian, its map from `X` is integral, its map from `Y` is a closed immersion,
and its structure sheaf is the fibre product of the two direct images over the direct image
from `Z`.

This is [Stacks Project, Tag 0E25].

## Main definitions

* `AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegral` packages the pushout scheme, its
  two canonical maps, and their universal property.
* `AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral` is the canonical chosen package.
* `AlgebraicGeometry.pushoutScheme`, `AlgebraicGeometry.pushoutInl` and
  `AlgebraicGeometry.pushoutInr` are its underlying scheme and canonical maps.
* `AlgebraicGeometry.pushoutToBase` is the induced structure morphism to the base.

## Main results

* `AlgebraicGeometry.pushoutSquare_isPullback`: the pushout square is also cartesian.
* `AlgebraicGeometry.pushoutInl_isIntegralHom` and
  `AlgebraicGeometry.pushoutInr_isClosedImmersion` give the two asserted morphism properties.
* `AlgebraicGeometry.pushoutStructureSheaf_isPullback` identifies the structure sheaf as a fibre
  product, read on each open of the pushout.

## Implementation notes

The pushout is constructed *as a locally ringed space* and then shown to be a scheme by
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme`: the open immersions from affine
schemes are the charts of `StacksFrontier.AlgebraicGeometry.Pushout.Chart`, one around every point.
It cannot be constructed as a pushout of schemes directly, because that is the statement being
proved; and the locally ringed space pushout is needed anyway, since
`AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace` does not preserve colimits and so a pushout
square of schemes says nothing about the underlying spaces or structure sheaves.  That is why the
assertions about the structure sheaf and about the two morphism properties are proved from
`Stacks.Pushout.isPushout_map_pushoutObj`, the pushout property one layer down, and not from the
scheme-level `AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral`'s own field.

The two morphism properties are Zariski-local at the target, so they follow from the charts: over
a chart the two maps are the two legs of the affine model, up to the isomorphism of the chart with
the corresponding open subscheme.  Note that `IsZariskiLocalAtTarget @IsIntegralHom` is not found
by `inferInstance` on this Mathlib revision and is fed as a term.

Being a cartesian square is *not* a Zariski-local property that can be invoked off the shelf, so
the fibre square is proved from the universal property directly: a test square is lifted over
each chart by the affine model's own cartesian square, and the local lifts are glued with
`AlgebraicGeometry.Scheme.Cover.glueMorphisms`.  Their compatibility, and the uniqueness of the
lift, are both free because the closed immersion `i` is a monomorphism.

The structure-sheaf identity is `Stacks.Pushout.isPullback_app_of_isPushout_right` applied to the
pushout square of presheafed spaces underlying the construction; it holds on every open with no
further hypothesis.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ECJ](https://stacks.math.columbia.edu/tag/0ECJ)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
* [Ferrand-Conducteur, Theorem 7.1(iii)]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Pushout

variable (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})

/-- The span of locally ringed spaces underlying the situation. -/
noncomputable abbrev pushoutSpan : WalkingSpan ⥤ LocallyRingedSpace.{u} :=
  span (Scheme.forgetToLocallyRingedSpace.map s.i) (Scheme.forgetToLocallyRingedSpace.map s.j)

/-- The canonical map from `X` into the pushout of locally ringed spaces. -/
noncomputable abbrev pushoutLRSInl :
    Scheme.forgetToLocallyRingedSpace.obj s.X ⟶ colimit (pushoutSpan s) :=
  colimit.ι (pushoutSpan s) WalkingSpan.left

/-- The canonical map from `Y` into the pushout of locally ringed spaces. -/
noncomputable abbrev pushoutLRSInr :
    Scheme.forgetToLocallyRingedSpace.obj s.Y ⟶ colimit (pushoutSpan s) :=
  colimit.ι (pushoutSpan s) WalkingSpan.right

/-- The colimit of the span is a pushout square of locally ringed spaces. -/
theorem isPushout_pushoutLRS :
    IsPushout (Scheme.forgetToLocallyRingedSpace.map s.i)
      (Scheme.forgetToLocallyRingedSpace.map s.j) (pushoutLRSInl s) (pushoutLRSInr s) :=
  IsPushout.of_isColimit_cocone (colimit.isColimit (pushoutSpan s))

/-- The two preimages in `Z` of an open of the pushout of locally ringed spaces agree. -/
theorem pushoutLRS_preimage_eq (W : Opens (colimit (pushoutSpan s)).toTopCat) :
    s.i ⁻¹ᵁ ((Opens.map (pushoutLRSInl s).base).obj W) =
      s.j ⁻¹ᵁ ((Opens.map (pushoutLRSInr s).base).obj W) :=
  congrArg (fun f : Scheme.forgetToLocallyRingedSpace.obj s.Z ⟶ colimit (pushoutSpan s) ↦
    (Opens.map f.base).obj W) (isPushout_pushoutLRS s).w

/-- **The pushout is a scheme.**  Its underlying locally ringed space is the pushout of the span
of locally ringed spaces; the affine charts around each point are
`Stacks.Pushout.exists_affineChart_of_isPushout` applied to the opens produced by
`Stacks.Pushout.exists_opens_isAffineOpen_preimage`. -/
noncomputable def pushoutObj : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (colimit (pushoutSpan s)) (by
    intro p
    obtain ⟨W, hpW, hU, hV⟩ := exists_opens_isAffineOpen_preimage s.i s.j
      s.fiber_preimage_subset_affine
      (isPushout_base_of_isPushout (isPushout_pushoutLRS s)) p
    obtain ⟨R, α, β, g, -, -, -, -, -, hgoi, hgr⟩ :=
      exists_affineChart_of_isPushout s.i s.j (isPushout_pushoutLRS s) W _ _ rfl rfl hU hV
        (pushoutLRS_preimage_eq s W)
    exact ⟨R, g, hgr.ge hpW, hgoi⟩)

/-- The underlying locally ringed space of the pushout scheme is the pushout of the span. -/
theorem pushoutObj_toLocallyRingedSpace :
    Scheme.forgetToLocallyRingedSpace.obj (pushoutObj s) = colimit (pushoutSpan s) := rfl


variable (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})

/-- The canonical map from `X` to the pushout, as a morphism of schemes. -/
noncomputable def pushoutObjInl : s.X ⟶ pushoutObj s :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage (pushoutLRSInl s)

/-- The canonical map from `Y` to the pushout, as a morphism of schemes. -/
noncomputable def pushoutObjInr : s.Y ⟶ pushoutObj s :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage (pushoutLRSInr s)

/-- The morphism of locally ringed spaces underlying `Stacks.Pushout.pushoutObjInl`. -/
lemma map_pushoutObjInl :
    Scheme.forgetToLocallyRingedSpace.map (pushoutObjInl s) = pushoutLRSInl s :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _

/-- The morphism of locally ringed spaces underlying `Stacks.Pushout.pushoutObjInr`. -/
lemma map_pushoutObjInr :
    Scheme.forgetToLocallyRingedSpace.map (pushoutObjInr s) = pushoutLRSInr s :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _

/-- The pushout square of locally ringed spaces, written with the two scheme morphisms.  This,
and not the scheme-level pushout square, is what the structure-sheaf identity is read off. -/
theorem isPushout_map_pushoutObj :
    IsPushout (Scheme.forgetToLocallyRingedSpace.map s.i)
      (Scheme.forgetToLocallyRingedSpace.map s.j)
      (Scheme.forgetToLocallyRingedSpace.map (pushoutObjInl s))
      (Scheme.forgetToLocallyRingedSpace.map (pushoutObjInr s)) := by
  rw [map_pushoutObjInl, map_pushoutObjInr]
  exact isPushout_pushoutLRS s

/-- **The square of schemes is a pushout square**, by full faithfulness of
`AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace`. -/
theorem isPushout_pushoutObj :
    IsPushout s.i s.j (pushoutObjInl s) (pushoutObjInr s) :=
  IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace (isPushout_map_pushoutObj s)

/-- Every point of the pushout lies in an open whose two preimages are affine, written with the
scheme morphisms. -/
theorem exists_opens_isAffineOpen_preimage_scheme (p : pushoutObj s) :
    ∃ W : (pushoutObj s).Opens, p ∈ W ∧ IsAffineOpen (pushoutObjInl s ⁻¹ᵁ W) ∧
      IsAffineOpen (pushoutObjInr s ⁻¹ᵁ W) :=
  exists_opens_isAffineOpen_preimage s.i s.j s.fiber_preimage_subset_affine
    (isPushout_base_of_isPushout (isPushout_map_pushoutObj s)) p

/-- The preimage in `Z` of an open of the pushout, along either leg. -/
theorem pushout_preimage_eq (W : (pushoutObj s).Opens) :
    s.i ⁻¹ᵁ (pushoutObjInl s ⁻¹ᵁ W) = s.j ⁻¹ᵁ (pushoutObjInr s ⁻¹ᵁ W) :=
  congrArg (fun f : s.Z ⟶ pushoutObj s ↦ f ⁻¹ᵁ W) (isPushout_pushoutObj s).w

/-- **The affine chart of the pushout, at the scheme level.**  Around every point there is an open
`W` of the pushout, an affine scheme `Spec R` isomorphic to `W`, and a cartesian square
identifying the restricted span with the affine model of [Stacks Project, Tag 0ET0]. -/
theorem exists_chart (p : pushoutObj s) :
    ∃ (W : (pushoutObj s).Opens) (R : CommRingCat.{u})
      (α : (pushoutObjInl s ⁻¹ᵁ W).toScheme ⟶ Spec R)
      (β : (pushoutObjInr s ⁻¹ᵁ W).toScheme ⟶ Spec R) (e : Spec R ≅ W.toScheme),
      p ∈ W ∧ IsIntegralHom α ∧ IsClosedImmersion β ∧
      α ≫ e.hom = pushoutObjInl s ∣_ W ∧ β ≫ e.hom = pushoutObjInr s ∣_ W ∧
      IsPullback (s.i ∣_ (pushoutObjInl s ⁻¹ᵁ W))
        (s.j.resLE (pushoutObjInr s ⁻¹ᵁ W) (s.i ⁻¹ᵁ (pushoutObjInl s ⁻¹ᵁ W))
          (pushout_preimage_eq s W).le) α β := by
  obtain ⟨W, hpW, hU, hV⟩ := exists_opens_isAffineOpen_preimage_scheme s p
  obtain ⟨R, α, β, g, hα, hβ, hpb, hga, hgb, hgoi, hgr⟩ :=
    exists_affineChart_of_isPushout s.i s.j (isPushout_map_pushoutObj s) W
      (pushoutObjInl s ⁻¹ᵁ W) (pushoutObjInr s ⁻¹ᵁ W) rfl rfl hU hV
      (pushout_preimage_eq s W)
  obtain ⟨gS, hgS⟩ : ∃ gS : Spec R ⟶ pushoutObj s,
      Scheme.forgetToLocallyRingedSpace.map gS = g :=
    ⟨Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage g,
      Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _⟩
  have hoi : IsOpenImmersion gS := by rw [← hgS] at hgoi; exact hgoi
  have hrange : Set.range gS.base = Set.range (W.ι).base :=
    (congrArg (fun k : Scheme.forgetToLocallyRingedSpace.obj (Spec R) ⟶
      Scheme.forgetToLocallyRingedSpace.obj (pushoutObj s) ↦ Set.range k.base) hgS).trans
      (hgr.trans (Scheme.Opens.range_ι W).symm)
  obtain ⟨e, he⟩ : ∃ e : Spec R ≅ W.toScheme, e.hom ≫ W.ι = gS :=
    ⟨IsOpenImmersion.isoOfRangeEq gS W.ι hrange,
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  have key : ∀ {T : Scheme.{u}} (a : T ⟶ Spec R) (b : T ⟶ W.toScheme),
      Scheme.forgetToLocallyRingedSpace.map a ≫ g =
        Scheme.forgetToLocallyRingedSpace.map (b ≫ W.ι) → a ≫ e.hom = b := fun a b h ↦ by
    rw [← cancel_mono W.ι, Category.assoc, he]
    exact Scheme.forgetToLocallyRingedSpace.map_injective (by rwa [Functor.map_comp, hgS])
  refine ⟨W, R, α, β, e, hpW, hα, hβ, key _ _ ?_, key _ _ ?_, hpb⟩
  · rw [morphismRestrict_ι, Functor.map_comp, map_pushoutObjInl]; exact hga
  · rw [morphismRestrict_ι, Functor.map_comp, map_pushoutObjInr]; exact hgb

/-- Over a chart the map from `X` is integral and the map from `Y` is a closed immersion. -/
theorem exists_chart_morphismProperty (p : pushoutObj s) :
    ∃ W : (pushoutObj s).Opens, p ∈ W ∧ IsIntegralHom (pushoutObjInl s ∣_ W) ∧
      IsClosedImmersion (pushoutObjInr s ∣_ W) := by
  obtain ⟨W, R, α, β, e, hpW, hα, hβ, hαe, hβe, -⟩ := exists_chart s p
  refine ⟨W, hpW, ?_, ?_⟩
  · rw [← hαe]; infer_instance
  · rw [← hβe]; infer_instance

/-- **The universal property of the fibre square.**  A commutative square over the pushout square
factors uniquely through `Z`; here only the existence is stated, the uniqueness being free from
`i` being a monomorphism.

The factorisation is built over each chart from the affine model's own cartesian square and glued
with `AlgebraicGeometry.Scheme.Cover.glueMorphisms`. -/
theorem exists_lift {S : Scheme.{u}} (f : S ⟶ s.X) (g : S ⟶ s.Y)
    (hfg : f ≫ pushoutObjInl s = g ≫ pushoutObjInr s) :
    ∃ u : S ⟶ s.Z, u ≫ s.i = f ∧ u ≫ s.j = g := by
  have hloc : ∀ x : S, ∃ (O : S.Opens) (v : O.toScheme ⟶ s.Z), x ∈ O ∧
      v ≫ s.i = O.ι ≫ f ∧ v ≫ s.j = O.ι ≫ g := by
    intro x
    obtain ⟨W, R, α, β, e, hpW, -, -, hαe, hβe, hpb⟩ :=
      exists_chart s ((f ≫ pushoutObjInl s) x)
    have hlf : (f ≫ pushoutObjInl s) ⁻¹ᵁ W ≤ f ⁻¹ᵁ (pushoutObjInl s ⁻¹ᵁ W) := le_of_eq rfl
    have hlg : (f ≫ pushoutObjInl s) ⁻¹ᵁ W ≤ g ⁻¹ᵁ (pushoutObjInr s ⁻¹ᵁ W) :=
      le_of_eq (congrArg (fun k : S ⟶ pushoutObj s ↦ k ⁻¹ᵁ W) hfg)
    have hcompat : f.resLE (pushoutObjInl s ⁻¹ᵁ W) ((f ≫ pushoutObjInl s) ⁻¹ᵁ W) hlf ≫ α =
        g.resLE (pushoutObjInr s ⁻¹ᵁ W) ((f ≫ pushoutObjInl s) ⁻¹ᵁ W) hlg ≫ β := by
      rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hαe, hβe, ← cancel_mono W.ι,
        Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι, ← Category.assoc,
        ← Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι, Category.assoc,
        Category.assoc, hfg]
    refine ⟨(f ≫ pushoutObjInl s) ⁻¹ᵁ W,
      hpb.lift _ _ hcompat ≫ (s.i ⁻¹ᵁ (pushoutObjInl s ⁻¹ᵁ W)).ι, hpW, ?_, ?_⟩
    · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hpb.lift_fst,
        Scheme.Hom.resLE_comp_ι]
    · rw [Category.assoc,
        ← Scheme.Hom.resLE_comp_ι s.j (pushout_preimage_eq s W).le,
        ← Category.assoc, hpb.lift_snd, Scheme.Hom.resLE_comp_ι]
  choose O v hxO hvi hvj using hloc
  let 𝒰 : S.OpenCover :=
    { I₀ := S, X x := (O x), f x := (O x).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ ⟨x, by simpa using hxO x⟩, inferInstance⟩ }
  refine ⟨𝒰.glueMorphisms v ?_, ?_, ?_⟩
  · intro x y
    rw [← cancel_mono s.i, Category.assoc, Category.assoc, hvi, hvi, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  all_goals refine 𝒰.hom_ext _ _ fun x ↦ ?_
  all_goals rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exacts [hvi x, hvj x]

/-- **The pushout square of schemes is also a fibre square.** -/
theorem isPullback_pushoutObj : IsPullback s.i s.j (pushoutObjInl s) (pushoutObjInr s) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (isPushout_pushoutObj s).w
    (fun c ↦ (exists_lift s c.fst c.snd c.condition).choose)
    (fun c ↦ (exists_lift s c.fst c.snd c.condition).choose_spec.1)
    (fun c ↦ (exists_lift s c.fst c.snd c.condition).choose_spec.2) ?_)
  intro c m h1 h2
  exact (inferInstance : Mono s.i).right_cancellation _ _
    (h1.trans (exists_lift s c.fst c.snd c.condition).choose_spec.1.symm)

end Stacks.Pushout

namespace AlgebraicGeometry

open Stacks.Pushout

/-- The scheme-theoretic pushout of a closed immersion and an integral morphism, together with
its two canonical maps and their universal property. -/
structure PushoutAlongClosedImmersionAndIntegral
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) where
  /-- The pushout scheme `Y ⨿_Z X`. -/
  P : Scheme.{u}
  /-- The canonical map from `X` to the pushout. -/
  a : s.X ⟶ P
  /-- The canonical map from `Y` to the pushout. -/
  b : s.Y ⟶ P
  /-- The displayed square is a pushout square of schemes. -/
  isPushout : IsPushout s.i s.j a b

/-- **Stacks Project, Tag 0E25.** The pushout along a closed immersion and an integral morphism
exists as a scheme. -/
@[stacks 0E25 "the pushout"]
noncomputable def pushoutAlongClosedImmersionAndIntegral
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    PushoutAlongClosedImmersionAndIntegral s where
  P := pushoutObj s
  a := pushoutObjInl s
  b := pushoutObjInr s
  isPushout := isPushout_pushoutObj s

/-- The underlying scheme of the pushout along a closed immersion and an integral morphism. -/
noncomputable abbrev pushoutScheme
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) : Scheme.{u} :=
  (pushoutAlongClosedImmersionAndIntegral s).P

/-- The canonical map from `X` to the pushout. -/
noncomputable abbrev pushoutInl
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) : s.X ⟶ pushoutScheme s :=
  (pushoutAlongClosedImmersionAndIntegral s).a

/-- The canonical map from `Y` to the pushout. -/
noncomputable abbrev pushoutInr
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) : s.Y ⟶ pushoutScheme s :=
  (pushoutAlongClosedImmersionAndIntegral s).b

/-- The canonical morphism from the pushout to the base scheme. -/
noncomputable def pushoutToBase
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) : pushoutScheme s ⟶ s.S :=
  (pushoutAlongClosedImmersionAndIntegral s).isPushout.desc s.pX s.pY
    (s.i_over.trans s.j_over.symm)

/-- **Stacks Project, Tag 0E25.** The pushout square is also a pullback square. -/
@[stacks 0E25 "the diagram is a fibre square"]
theorem pushoutSquare_isPullback
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    IsPullback s.i s.j (pushoutInl s) (pushoutInr s) :=
  isPullback_pushoutObj s

/-- **Stacks Project, Tag 0E25.** The canonical map from `X` to the pushout is integral. -/
@[stacks 0E25 "the morphism a is integral"]
instance pushoutInl_isIntegralHom
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    IsIntegralHom (pushoutInl s) := by
  have hzl : IsZariskiLocalAtTarget @IsIntegralHom :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x ↦
    (exists_chart_morphismProperty s x).imp fun _ h ↦ ⟨h.1, h.2.1⟩

/-- **Stacks Project, Tag 0E25.** The canonical map from `Y` to the pushout is a closed
immersion. -/
@[stacks 0E25 "the morphism b is a closed immersion"]
instance pushoutInr_isClosedImmersion
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u}) :
    IsClosedImmersion (pushoutInr s) :=
  IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x ↦
    (exists_chart_morphismProperty s x).imp fun _ h ↦ ⟨h.1, h.2.2⟩

/-- **Stacks Project, Tag 0E25.** On every open of the pushout, its ring of sections is the fibre
product of the rings of sections on `Y` and `X` over the corresponding ring on `Z`.

These are the component squares, after applying `CategoryTheory.sheafToPresheaf`, of the source's
square of sheaves of rings: its natural transformations have components `b.app U`, `a.app U`,
`j.app (b ⁻¹ᵁ U)`, and the transported map `i.app (a ⁻¹ᵁ U)` occurring below.  The equivalence
with the sheaf-level pullback is `CategoryTheory.IsPullback.iff_app` together with reflection of
limits along the fully faithful `CategoryTheory.sheafToPresheaf`. -/
@[stacks 0E25 "the structure sheaf"]
theorem pushoutStructureSheaf_isPullback
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (U : (pushoutScheme s).Opens) :
    let e : s.i ⁻¹ᵁ (pushoutInl s ⁻¹ᵁ U) =
        s.j ⁻¹ᵁ (pushoutInr s ⁻¹ᵁ U) :=
      congrArg (fun f : s.Z ⟶ pushoutScheme s ↦ f ⁻¹ᵁ U)
        (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
    IsPullback (pushoutInr s |>.app U) (pushoutInl s |>.app U)
      (s.j.app (pushoutInr s ⁻¹ᵁ U))
      (s.i.app (pushoutInl s ⁻¹ᵁ U) ≫
        eqToHom (congrArg (fun V ↦ Γ(s.Z, V)) e)) := by
  intro e
  have H2 := isPullback_app_of_isPushout_right
    ((isPushout_map_pushoutObj s).map lrsToPresheafedSpace) U (congrArg op e)
  rwa [eqToHom_map] at H2

end AlgebraicGeometry

end
