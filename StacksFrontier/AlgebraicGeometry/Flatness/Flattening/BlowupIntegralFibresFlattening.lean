module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic

/-!
# Finite local freeness on an open surjecting onto the base

Let `g : B ⟶ T` be a morphism of finite presentation with geometrically integral fibres and let
`G` be a finitely presented `𝒪_B`-module which is flat over `T` at the generic point of every
fibre. Then there is an open `V ⊆ B` on which `G` is free of finite rank near every point and
which surjects onto `T`.

This is [Stacks, Tag 080Q] read at the generic points of the fibres of a family with
geometrically integral fibres, where the fibre-wise hypothesis of that tag costs nothing: the
local ring of an integral scheme at its generic point is a field. The generic points of fibres
are handled this way throughout the proof of [Stacks, Tag 0811], which is
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective` of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/BlowupIntegralFibres0811.lean`.

## Main definitions

* `AlgebraicGeometry.GenericFibreFlatteningBlowup` is a flattening input *stronger* than
  [Stacks, Tag 0811] concludes. It is not a hypothesis of that tag, which is proved outright in
  `StacksFrontier/AlgebraicGeometry/Flatness/Flattening/BlowupIntegralFibres0811.lean`, and it is
  not what the Raynaud-Gruson induction of [Stacks, Tag 0815] consumes: that induction reads
  `AlgebraicGeometry.FinitePresentationHasGenericFibreFreeBlowup`, which
  `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` derives from the tag with
  nothing granted. So this predicate has no producer and none is possible from the tag; it is
  kept as the record of the sharper reduction.

## Main results

* `AlgebraicGeometry.exists_fibre_dense_preimage`: a morphism with geometrically integral fibres
  has, over every point of the target, a point of the source whose closure contains the whole
  fibre — the generic point of that fibre.
* `AlgebraicGeometry.asFiber_eq_genericPoint_of_fibre_subset_closure`: such a point *is* the
  generic point of the scheme-theoretic fibre.
* `AlgebraicGeometry.flat_fibre_stalk_of_fibre_subset_closure`: at such a point the fibre-wise
  hypothesis of [Stacks, Tag 080Q] holds for any module.
* `AlgebraicGeometry.exists_opens_forall_free_surjective_of_isFlatOverAt_fibre_dense`: the
  statement of the first paragraph.
* `AlgebraicGeometry.genericFibreFlatteningBlowup_of_strictTransform`: two of the six conditions
  of that input are free, being base changes of hypothesis (1) of [Stacks, Tag 0811].
* `AlgebraicGeometry.exists_isAdmissibleBlowup_opens_free_surjective`: the conclusion of
  [Stacks, Tag 0811] from that input. It carries no `@[stacks 0811]` attribute: the tag is proved
  outright elsewhere, under exactly the source's hypotheses, so this is a record of the sharper
  reduction and not the registration of the tag.

## Implementation notes

"Generic point of the fibre" is expressed twice. The hypothesis and the first two results use
the form `g⁻¹(g b) ⊆ closure {b}`, which mentions only the topology of `B` and needs no
irreducibility instance; `AlgebraicGeometry.asFiber_eq_genericPoint_of_fibre_subset_closure`
converts it into the form the fibre-wise criterion [Stacks, Tag 080Q] consumes, namely that the
corresponding point of `g.fiber (g b)` is `genericPoint` of that scheme. The conversion is
`Topology.IsInducing.closure_eq_preimage_closure_image` for the embedding `g.fiberι`, whose range
is `g⁻¹(g b)` (`AlgebraicGeometry.Scheme.Hom.range_fiberι`), together with uniqueness of generic
points in a sober space.

At the generic point of a fibre the fibre is integral, so the local ring there is the function
field of the fibre — a field, by Mathlib's `AlgebraicGeometry.Scheme.functionField` instance — and
every module over it is flat. That discharges the second hypothesis of [Stacks, Tag 080Q] with no
work, which is exactly why [Stacks, Tag 0811] assumes geometrically integral fibres.

"Free of finite rank near every point of `V`" is spelled out: every point of `V` has an open
neighbourhood inside `V` over which the module is isomorphic to a finite free module. That is the
form [Stacks, Tag 080Q] delivers, and it is what finite local freeness on `V` means; the
`LocalGeneratorsData` bookkeeping needed to phrase it as
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of the restriction to `V` is not carried
out here.

**Why this is not how [Stacks, Tag 0811] is proved.** The hypothesis below asks the module to be
of finite presentation on all of `B`, which for the strict transform in [Stacks, Tag 0811] is
exactly what the blowup has to achieve; the module there is of finite presentation only over the
distinguished open. The freeness in that tag therefore comes from the affine engine
[Stacks, Tag 0810], not from this statement, and
`AlgebraicGeometry.exists_freeAtPointOfRank_of_isFlatOverAt_over_open` is the place where
[Stacks, Tag 080Q] is used there — over the distinguished open, where finite presentation is a
hypothesis of the source.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)

-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Generic points of fibres -/

/-- A point of a fibre is generic in the fibre iff its image in the source has closure containing
the whole fibre. -/
private theorem fibre_subset_closure_fiberι_iff {B T : Scheme.{u}} (g : B ⟶ T) (t : T)
    (ξ : g.fiber t) : g.base ⁻¹' {t} ⊆ closure {g.fiberι t ξ} ↔ closure {ξ} = Set.univ := by
  rw [(g.fiberι t).isEmbedding.isInducing.closure_eq_preimage_closure_image,
    Set.image_singleton, Set.eq_univ_iff_forall, ← g.range_fiberι t, Set.range_subset_iff]
  rfl

/-- A morphism with geometrically integral fibres has, over every point `t` of the target, a
point `b` of the source whose closure contains the whole fibre over `t`: the generic point of
that fibre, which exists because the fibre is an integral scheme and schemes are sober. -/
theorem exists_fibre_dense_preimage {B T : Scheme.{u}} (g : B ⟶ T) [GeometricallyIntegral g]
    (t : T) : ∃ b : B, g.base b = t ∧ g.base ⁻¹' {t} ⊆ closure {b} := by
  have hint : IsIntegral (g.fiber t) := inferInstance
  refine ⟨g.fiberι t (genericPoint (g.fiber t)), ?_,
    (fibre_subset_closure_fiberι_iff g t _).2 (genericPoint_spec (g.fiber t))⟩
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← g.range_fiberι t]
  exact ⟨_, rfl⟩

/-- A point whose closure contains its whole fibre is the generic point of the scheme-theoretic
fibre through it. -/
theorem asFiber_eq_genericPoint_of_fibre_subset_closure {B T : Scheme.{u}} (g : B ⟶ T)
    [GeometricallyIntegral g] (b : B) (hb : g.base ⁻¹' {g.base b} ⊆ closure {b}) :
    g.asFiber b = genericPoint (g.fiber (g.base b)) := by
  have hint : IsIntegral (g.fiber (g.base b)) := inferInstance
  exact IsGenericPoint.eq ((fibre_subset_closure_fiberι_iff g _ _).1
    (by rwa [g.fiberι_asFiber b])) (genericPoint_spec (g.fiber (g.base b)))

/-- At a point whose closure contains its whole fibre, the fibre-wise flatness hypothesis of
[Stacks, Tag 080Q] is automatic: the fibre is integral and the point is its generic point, so
the local ring there is the function field of the fibre, a field, over which every module is
flat. -/
theorem flat_fibre_stalk_of_fibre_subset_closure {B T : Scheme.{u}} (g : B ⟶ T)
    [GeometricallyIntegral g] (G : B.Modules) (b : B)
    (hb : g.base ⁻¹' {g.base b} ⊆ closure {b}) :
    letI := Stacks.Flatness.stalkModule
      ((Scheme.Modules.pullback (g.fiberι (g.base b))).obj G) (g.asFiber b)
    Module.Flat (ToType ((g.fiber (g.base b)).presheaf.stalk (g.asFiber b)))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback (g.fiberι (g.base b))).obj G).val.presheaf
          (g.asFiber b))) := by
  have hint : IsIntegral (g.fiber (g.base b)) := inferInstance
  rw [asFiber_eq_genericPoint_of_fibre_subset_closure g b hb]
  have : Module.Free (ToType ((g.fiber (g.base b)).presheaf.stalk
      (genericPoint (g.fiber (g.base b)))))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback (g.fiberι (g.base b))).obj G).val.presheaf
          (genericPoint (g.fiber (g.base b))))) := Module.Free.of_divisionRing _ _
  exact Module.Flat.of_free

/-! ### The open subscheme of the conclusion -/

/-- **Finite local freeness on an open surjecting onto the base.** Let `g : B ⟶ T` be of finite
presentation with geometrically integral fibres and let `G` be a finitely presented
`𝒪_B`-module which is flat over `T` at the generic point of every fibre. There is an open
`V ⊆ B` which surjects onto `T` and over which `G` is free of finite rank near every point.

The fibre over a point of `T` is integral, so it has a generic point; `G` is free of finite rank
on a neighbourhood of that point by [Stacks, Tag 080Q], whose fibre-wise hypothesis holds because
the local ring of an integral scheme at its generic point is a field. Taking `V` to be the union
of those neighbourhoods gives both assertions. -/
theorem exists_opens_forall_free_surjective_of_isFlatOverAt_fibre_dense {B T : Scheme.{u}}
    (g : B ⟶ T) (hg : AlgebraicGeometry.FinitePresentation g) [GeometricallyIntegral g]
    (G : B.Modules) [G.IsFinitePresentation]
    (hflat : ∀ b : B, g.base ⁻¹' {g.base b} ⊆ closure {b} →
      IsFlatOverAt g.toLRSHom.toShHom G b) :
    ∃ V : B.Opens,
      (∀ b : B, b ∈ V → ∃ (W : B.Opens) (n : ℕ), b ∈ W ∧ W ≤ V ∧
        Nonempty (G.over W ≅ SheafOfModules.free (ULift.{u} (Fin n)))) ∧
      Function.Surjective (V.ι ≫ g).base := by
  classical
  have hstep : ∀ t : T, ∃ (b : B) (W : B.Opens) (n : ℕ), g.base b = t ∧ b ∈ W ∧
      Nonempty (G.over W ≅ SheafOfModules.free (ULift.{u} (Fin n))) := by
    intro t
    obtain ⟨b, hbt, hbcl⟩ := exists_fibre_dense_preimage g t
    subst hbt
    obtain ⟨W, hbW, n, hfree⟩ :=
      Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk g hg G b
        (hflat b hbcl) (flat_fibre_stalk_of_fibre_subset_closure g G b hbcl)
    exact ⟨b, W, n, rfl, hbW, hfree⟩
  choose b W n hbt hbW hfree using hstep
  refine ⟨⨆ t : T, W t, fun x hx ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨t, hxt⟩ := Opens.mem_iSup.mp hx
    exact ⟨W t, n t, hxt, le_iSup W t, hfree t⟩
  · refine ⟨⟨b t, Opens.mem_iSup.mpr ⟨t, hbW t⟩⟩, ?_⟩
    show g.base ((⨆ t : T, W t).ι.base ⟨b t, _⟩) = t
    exact hbt t

/-! ### The input of the Raynaud-Gruson induction -/

/-- **The flattening input of the Raynaud-Gruson induction.** A `U`-admissible blowup of `S`,
given by a centre `I` of finite presentation supported away from `U`, such that the projection
`X ×_S Bl_I(S) ⟶ Bl_I(S)` is of finite presentation with geometrically integral fibres and the
strict transform of `F` is finitely presented and flat over `Bl_I(S)` at the generic point of
every fibre of that projection.

This is *not* what [Stacks, Tag 0811] needs:
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective` proves that tag
under exactly the hypotheses of the source. It is strictly more than that tag concludes — global
finite presentation of the strict transform, and flatness at *every* generic point of a fibre of
the blown-up projection rather than freeness on an open surjecting onto the blowup — so it is
*stronger* than the Raynaud-Gruson induction of [Stacks, Tag 0815] needs. That induction consumes
`AlgebraicGeometry.FinitePresentationHasGenericFibreFreeBlowup`, which
`AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` proves from the tag outright, so
this predicate has no producer and is not needed; it is kept as the record of the sharper
reduction. It lives here because that is where the generic points of fibres are handled. -/
def GenericFibreFlatteningBlowup {S X : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (U : S.Opens) : Prop :=
  ∃ I : S.IdealSheafData,
    FinitePresentation I.subschemeι ∧
    Disjoint (U : Set S) (I.support : Set S) ∧
    AlgebraicGeometry.FinitePresentation (pullback.snd f (blowUpToBase I)) ∧
    GeometricallyIntegral (pullback.snd f (blowUpToBase I)) ∧
    (Stacks.StrictTransform.sheaf f (blowUpToBase I)
      (exceptionalIdeal I) F).IsFinitePresentation ∧
    ∀ z : Stacks.StrictTransform.baseChange f (blowUpToBase I),
      (pullback.snd f (blowUpToBase I)).base ⁻¹'
          {(pullback.snd f (blowUpToBase I)).base z} ⊆ closure {z} →
        IsFlatOverAt (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
          (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) z

/-- **Two of the six conditions of `AlgebraicGeometry.GenericFibreFlatteningBlowup` are free.**
The two that concern the projection alone — that it is of finite presentation and has
geometrically integral fibres — are the hypotheses (1) of [Stacks, Tag 0811] on `f` itself,
carried along the base change: both properties are stable under base change, and
`pullback.snd f (blowUpToBase I)` is the base change of `f` along the blowup. So what has to be
produced is only the centre together with the two conditions on the strict transform. -/
theorem genericFibreFlatteningBlowup_of_strictTransform {S X : Scheme.{u}} (f : X ⟶ S)
    (hf : AlgebraicGeometry.FinitePresentation f) [GeometricallyIntegral f] (F : X.Modules)
    (U : S.Opens)
    (h : ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      (Stacks.StrictTransform.sheaf f (blowUpToBase I)
        (exceptionalIdeal I) F).IsFinitePresentation ∧
      ∀ z : Stacks.StrictTransform.baseChange f (blowUpToBase I),
        (pullback.snd f (blowUpToBase I)).base ⁻¹'
            {(pullback.snd f (blowUpToBase I)).base z} ⊆ closure {z} →
          IsFlatOverAt (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
            (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) z) :
    GenericFibreFlatteningBlowup f F U := by
  obtain ⟨I, hIfp, hIdisj, hFfp, hflat⟩ := h
  have hp := IsPullback.of_hasPullback f (blowUpToBase I)
  refine ⟨I, hIfp, hIdisj, ⟨?_, ?_, ?_⟩, ?_, hFfp, hflat⟩
  · exact locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback hp
      hf.locallyOfFinitePresentation
  · exact quasiCompact_isStableUnderBaseChange.of_isPullback hp hf.quasiCompact
  · exact quasiSeparated_isStableUnderBaseChange.of_isPullback hp hf.quasiSeparated
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp ‹GeometricallyIntegral f›

/-- **The conclusion of [Stacks, Tag 0811] from
`AlgebraicGeometry.GenericFibreFlatteningBlowup`.** Given that input, there are a `U`-admissible
blowup of `S` — given by a centre `I` of finite presentation supported away from `U` — and an
open subscheme `V` of `X ×_S Bl_I(S)` such that

* **(a)** the strict transform of `F` along the blowup is free of finite rank on a neighbourhood
  of every point of `V`, that is, finitely locally free on `V`, and
* **(b)** `V` surjects onto `Bl_I(S)`.

**No `@[stacks 0811]` attribute is attached.** The tag is
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective` of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/BlowupIntegralFibres0811.lean`, which proves
it under exactly hypotheses (1)-(4) of the source, and the Raynaud-Gruson induction of
[Stacks, Tag 0815] reads its input from that proof rather than through this statement
(`AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup`). What is kept here is the
record of what `AlgebraicGeometry.GenericFibreFlatteningBlowup` buys: the passage from that
stronger input to (a) and (b) is [Stacks, Tag 080Q] at the generic points of the fibres together
with integrality of those fibres. The hypothesis is strictly more than the tag concludes, so it
cannot be discharged from the tag. -/
theorem exists_isAdmissibleBlowup_opens_free_surjective {S X : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (U : S.Opens) (h : GenericFibreFlatteningBlowup f F U) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      ∃ V : (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens,
        (∀ z : Stacks.StrictTransform.baseChange f (blowUpToBase I), z ∈ V →
          ∃ (W : (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens) (n : ℕ),
            z ∈ W ∧ W ≤ V ∧
            Nonempty ((Stacks.StrictTransform.sheaf f (blowUpToBase I)
              (exceptionalIdeal I) F).over W ≅
                SheafOfModules.free (ULift.{u} (Fin n)))) ∧
        Function.Surjective (V.ι ≫ pullback.snd f (blowUpToBase I)).base := by
  obtain ⟨I, hIfp, hIdisj, hgfp, hgint, hFfp, hflat⟩ := h
  have _ : GeometricallyIntegral (pullback.snd f (blowUpToBase I)) := hgint
  have _ : (Stacks.StrictTransform.sheaf f (blowUpToBase I)
    (exceptionalIdeal I) F).IsFinitePresentation := hFfp
  refine ⟨I, hIfp, hIdisj, (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase I)).mpr
    ⟨I, hIfp, hIdisj, Iso.refl _, Category.id_comp _⟩, ?_⟩
  exact exists_opens_forall_free_surjective_of_isFlatOverAt_fibre_dense
    (pullback.snd f (blowUpToBase I)) hgfp
    (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) hflat


end AlgebraicGeometry

end
