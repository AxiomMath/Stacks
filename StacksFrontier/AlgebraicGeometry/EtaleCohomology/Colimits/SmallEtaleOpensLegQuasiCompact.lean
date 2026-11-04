module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleOpensLeg

/-!
# Surjectivity of the leg on sections over an open from surjectivity over quasi-compact opens

The hypothesis `hsurj` of
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective_opensLeg` — the last
thing the degree-zero gluing condition `hsub` of [Stacks, Tag 09YQ] owes — asks for the
surjectivity of `Stacks.EtaleCohomology.opensSectionsLeg` over the pullback of an open `W` of a
level `X_i` **whose preimage in the limit `X` is quasi-compact**, at some level above `i`. The open
`W` itself is not quasi-compact: it comes from `AlgebraicGeometry.exists_preimage_eq_pair`, which
produces a pair of opens of one level with prescribed preimages and claims nothing about them.

The existing forms of the degree-zero statement of [Stacks, Tag 09YQ] over an object all work with
*quasi-compact* data. `Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum` and
`Stacks.EtaleCohomology.QcSeparatedColimit.sectionOver_colimit_of_qcqs_etale_object` ask their
object to be quasi-compact and quasi-separated, and
`Stacks.EtaleCohomology.QcqsLimitCohomology.globalSections_colimit_of_qcqs_level` asks it of the
level; the reason is the same in each case, that the one-hypercover produced is a *finite* family
of affines because a filtered colimit only sees finitely many conditions at once.

**This file closes that mismatch.** It shows that the surjectivity over a quasi-compact open of a
level implies the surjectivity over an arbitrary open with quasi-compact preimage, so that
`hsurj` may be discharged by an engine that only ever speaks of quasi-compact opens.

## Main results

* `Stacks.Cohomology.FreeYoneda.surjective_sections_map_of_injective` — **restriction along a
  monomorphism of a site is surjective on the sections of an injective abelian sheaf.** A section
  over the source is a map out of the free abelian sheaf on it
  (`Stacks.Cohomology.FreeYoneda.sectionsEquiv`), that free abelian sheaf is a subobject of the
  one on the target, and an injective object receives an extension along any monomorphism.
* `Stacks.EtaleCohomology.OpensAcyclicity.surjective_opensSectionsRestrict_of_injective` — the
  same for an inclusion of open subschemes, the inclusion being a monomorphism of the small étale
  site by `Stacks.EtaleCohomology.MayerVietoris.mono_opensToSite_map`.
* `AlgebraicGeometry.exists_map_preimage_le_map_preimage_of_initiallySmall` — the `≤` companion of
  `AlgebraicGeometry.exists_map_preimage_eq_map_preimage_of_initiallySmall`, i.e.
  Mathlib's `AlgebraicGeometry.exists_map_preimage_le_map_preimage` with the index universes freed.
  Only the *smaller* of the two opens has to be quasi-compact, which is exactly why this and not
  the `=` form is what is used below.
* `Stacks.EtaleCohomology.exists_opensSectionsLeg_eq_of_le` — **a section hit by the leg over a
  smaller open is hit by the leg over a bigger one with the same preimage**, when the sheaf
  upstairs is injective.
* `Stacks.EtaleCohomology.exists_isCompact_le_map_preimage` — **an open of a level with
  quasi-compact preimage contains, at some later level, a quasi-compact open with the same
  preimage.**
* `Stacks.EtaleCohomology.surjective_opensSectionsLeg_of_isCompact` — **`hsurj` from the
  surjectivity over the quasi-compact opens of the levels.**
* `Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg` — **`hsub` for the
  colimit sheaf of [Stacks, Tag 09YQ] from that surjectivity**, obtained by feeding the previous
  theorem to `sectionsDifference_of_surjective_opensLeg`.

## How the reduction goes

Let `W` be an open of `X_i` with `f_i^{-1}W` quasi-compact.

[Stacks, Tag 01Z4] (1) produces a level `k` and a **quasi-compact** open `V₀` of `X_k` with
`f_k^{-1}V₀ = f_i^{-1}W`. Joining `i` and `k` at a level `m` turns this into two opens of one and
the same `X_m` with the same preimage in `X`, the first of them quasi-compact. [Stacks, Tag 01Z4]
(2) would now say that two opens of a level with the same preimage agree at a further level — but
it asks *both* of them to be quasi-compact, which `W` is not. Its one-sided form
`exists_map_preimage_le_map_preimage` asks only the smaller one to be quasi-compact, and that is
available here: at some level `n` the pullback of `V₀` is **contained in** the pullback of `W`,
with the same preimage in `X`. So the question is reduced to a quasi-compact open of a level,
contained in the pullback of `W`.

Going back up from the quasi-compact open to the pullback of `W` is where injectivity of the
sheaves at the levels is used, and it is not a formality: the restriction map
`F_j(W') ⟶ F_j(V')` is surjective for an **injective** `F_j` — a section over `V'` is a morphism
`ℤ[V'] ⟶ F_j` out of the free abelian sheaf, `ℤ[V'] ⟶ ℤ[W']` is a monomorphism because
`V' ⟶ W'` is one and the free abelian sheaf functor preserves monomorphisms, and an injective
object receives an extension along a monomorphism. Injectivity of the `F_i` is a hypothesis of
`sectionsDifference_of_surjective_opensLeg` already, coming from the pointwise injective system
the vanishing half of [Stacks, Tag 09YQ] is applied to, so nothing is added. With the two opens
having the same preimage in `X`, the restriction map downstairs is the identity, and a lift over
`V'` extends to a lift over the pullback of `W`.

## What the consumer of the reduced hypothesis still has to know

`exists_oneHypercoverOf_datum` asks its object to be quasi-separated as well as quasi-compact, and
the quasi-compact open handed back here is not claimed quasi-separated — the statement assumes
nothing about the levels, so there is nothing to deduce it from. There is also nothing to do:
[Stacks, Tag 09YQ] assumes all the `X_i` quasi-compact and quasi-separated, and an open subscheme
of a quasi-separated scheme is quasi-separated, so a consumer carrying that hypothesis has it for
free. Leaving it out keeps the reduction itself free of any hypothesis on the levels.

## What this does not do

It does not supply the surjectivity over a quasi-compact open. That is the degree-zero statement
of [Stacks, Tag 09YQ] over such an open, which on the levels of [Stacks, Tag 0EYL] is the case
`p = 0` of `Stacks.WeakSites.ColimitSiteCohomology.isColimitCohomologyCocone` over the affine
objects of a level, followed by the finite one-hypercover step
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`; the module
docstring of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleOpensLeg.lean` records what is
available for it and what the passage from Mathlib's small étale sites to those levels still owes.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.InitiallySmall

universe v u uI

namespace Stacks.Cohomology.FreeYoneda

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

/-- **Restriction along a monomorphism of the site is surjective on the sections of an injective
abelian sheaf.** Sections of `G` over an object are the morphisms into `G` out of the free abelian
sheaf on it (`Stacks.Cohomology.FreeYoneda.sectionsEquiv`); the free abelian sheaf functor
preserves monomorphisms, being the composite of the Yoneda embedding, the free abelian group
functor and sheafification; and an injective object receives an extension along a monomorphism. -/
public theorem surjective_sections_map_of_injective (G : Sheaf J AddCommGrpCat.{v}) [Injective G]
    {U V : C} (h : V ⟶ U) [Mono h] :
    Function.Surjective (ConcreteCategory.hom (G.obj.map h.op)) := by
  intro σ
  refine ⟨sectionsEquiv U G (Injective.factorThru ((sectionsEquiv V G).symm σ)
    ((freeYoneda J).map h)), ?_⟩
  rw [← sectionsEquiv_naturality_left h G, Injective.comp_factorThru, Equiv.apply_symm_apply]

end Stacks.Cohomology.FreeYoneda

namespace Stacks.EtaleCohomology.OpensAcyclicity

variable {X : Scheme.{u}}

/-- **Restriction of sections of an injective abelian sheaf along an inclusion of open subschemes
is surjective.** An inclusion of opens is a monomorphism of the small étale site
(`Stacks.EtaleCohomology.MayerVietoris.mono_opensToSite_map`), so this is
`Stacks.Cohomology.FreeYoneda.surjective_sections_map_of_injective`. -/
public theorem surjective_opensSectionsRestrict_of_injective
    (G : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}) [Injective G]
    {U V : X.Opens} (h : U ≤ V) :
    Function.Surjective (ConcreteCategory.hom (opensSectionsRestrict G h)) :=
  have := MayerVietoris.mono_opensToSite_map (X := X) (homOfLE h)
  Stacks.Cohomology.FreeYoneda.surjective_sections_map_of_injective G
    ((MayerVietoris.opensToSite X).map (homOfLE h))

end Stacks.EtaleCohomology.OpensAcyclicity

namespace AlgebraicGeometry

/-- **[Stacks, Tag 01Z4] (2) in its one-sided form, with the index universes freed**: for opens
`U ≤ V` of a level whose preimages in the limit are nested, the pullbacks are nested at some later
level, and only `U` has to be quasi-compact.

This is Mathlib's `AlgebraicGeometry.exists_map_preimage_le_map_preimage` transported along the
small cofiltered model exactly as
`AlgebraicGeometry.exists_map_preimage_eq_map_preimage_of_initiallySmall` transports the two-sided
form; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean`. The one-sided form is
what a consumer with only one quasi-compact open has, and the two-sided form does not cover it. -/
public theorem exists_map_preimage_le_map_preimage_of_initiallySmall {I : Type uI}
    [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    {i : I} {U V : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (H : c.π.app i ⁻¹ᵁ U ≤ c.π.app i ⁻¹ᵁ V) :
    ∃ (j : I) (g : j ⟶ i), D.map g ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ V := by
  have {a b : CofilteredInitialModel.{u} I} (g : a ⟶ b) :
      IsAffineHom ((fromCofilteredInitialModel.{u} I ⋙ D).map g) := by
    dsimp; infer_instance
  obtain ⟨b, h, hb⟩ := exists_map_preimage_le_map_preimage
    (fromCofilteredInitialModel.{u} I ⋙ D) _
    ((Functor.Initial.isLimitWhiskerEquiv (fromCofilteredInitialModel.{u} I) c).symm hc)
    (i := Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)
    (U := D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i) ⁻¹ᵁ U)
    (V := D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i) ⁻¹ᵁ V)
    (QuasiCompact.isCompact_preimage _ U.isOpen hU)
    (by simpa only [Cone.whisker_π, Functor.whiskerLeft_app, ← Scheme.Hom.comp_preimage,
      c.w] using H)
  refine ⟨_, (fromCofilteredInitialModel.{u} I).map h ≫
    Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i, ?_⟩
  rwa [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

section LegLe

variable {T S : Scheme.{u}} (k : T ⟶ S)
  [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
  {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {𝒢 : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **A section hit by the leg over a smaller open is hit by the leg over a bigger one with the
same preimage**, provided the sheaf upstairs is injective.

Let `s` be a section of `𝒢` over `k^{-1}W` and suppose its restriction to `k^{-1}V`, which is the
*same* open, is the image under the leg of a section `g` of `G` over `V`. Then `g` extends to a
section over `W` because restriction along `V ≤ W` is surjective for an injective sheaf
(`Stacks.EtaleCohomology.OpensAcyclicity.surjective_opensSectionsRestrict_of_injective`), the leg
commutes with restriction (`Stacks.EtaleCohomology.opensSectionsLeg_restrict`), so the image of
that extension restricts to the section we started from, and restriction along an equality of
opens is injective.

This is pointwise in `s` because what consumes it is: the level at which a section of the colimit
sheaf is hit depends on the section, and no level hits them all; see
`Stacks.EtaleCohomology.surjective_opensSectionsLeg_of_isCompact`. -/
public theorem exists_opensSectionsLeg_eq_of_le [Injective G]
    (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢)
    {V W : S.Opens} (hVW : V ≤ W) (heq : k ⁻¹ᵁ V = k ⁻¹ᵁ W)
    (s : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict T).obj 𝒢) (k ⁻¹ᵁ W)))
    (g : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict S).obj G) V))
    (hg : opensSectionsLeg k ι V g =
      OpensAcyclicity.opensSectionsRestrict
        ((MayerVietoris.mayerVietorisRestrict T).obj 𝒢) (k.preimage_mono hVW) s) :
    ∃ g' : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict S).obj G) W), opensSectionsLeg k ι W g' = s := by
  have := MayerVietoris.injective_mayerVietorisRestrict G
  obtain ⟨g', hg'⟩ := OpensAcyclicity.surjective_opensSectionsRestrict_of_injective
    ((MayerVietoris.mayerVietorisRestrict S).obj G) hVW g
  refine ⟨g', OpensAcyclicity.opensSectionsRestrict_injective_of_eq
    ((MayerVietoris.mayerVietorisRestrict T).obj 𝒢) (k.preimage_mono hVW) heq ?_⟩
  rw [opensSectionsLeg_restrict k ι hVW g', hg', hg]

end LegLe

section Descent

open Stacks.EtaleCohomology.SmallEtaleLimitCohomology (conePi)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **An open of a level whose preimage in the limit is quasi-compact contains, at some later
level, a quasi-compact open with the same preimage.**

The preimage descends to a quasi-compact open of *some* level by [Stacks, Tag 01Z4] (1); joining
the two levels and applying the one-sided [Stacks, Tag 01Z4] (2),
`AlgebraicGeometry.exists_map_preimage_le_map_preimage_of_initiallySmall`, nests the two pullbacks
at a further level. The two-sided form would need the pullback of `W` to be quasi-compact as well,
which is not available: the opens produced by `AlgebraicGeometry.exists_preimage_eq_pair` carry no
quasi-compactness. -/
public theorem exists_isCompact_le_map_preimage (hc : IsLimit c) (i : Iᵒᵖ)
    (W : (D.obj i).Opens)
    (hW : IsCompact ((conePi c i ⁻¹ᵁ W : (c.pt).Opens) : Set c.pt)) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i) (V : (D.obj j).Opens), IsCompact (V : Set (D.obj j)) ∧
      V ≤ D.map a ⁻¹ᵁ W ∧ conePi c j ⁻¹ᵁ V = conePi c j ⁻¹ᵁ (D.map a ⁻¹ᵁ W) := by
  have : InitiallySmall.{max u v} Iᵒᵖ := initiallySmall_of_small_of_locallySmall.{max u v} Iᵒᵖ
  obtain ⟨k, V₀, hV₀c, hV₀⟩ :=
    exists_preimage_eq_of_initiallySmall D c hc (conePi c i ⁻¹ᵁ W) hW
  replace hV₀ : conePi c k ⁻¹ᵁ V₀ = conePi c i ⁻¹ᵁ W := hV₀
  obtain ⟨m, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i k
  have hpre : conePi c m ⁻¹ᵁ (D.map b ⁻¹ᵁ V₀) = conePi c m ⁻¹ᵁ (D.map a ⁻¹ᵁ W) := by
    simp only [conePi_preimage_map_preimage, hV₀]
  have hV₁c : IsCompact ((D.map b ⁻¹ᵁ V₀ : (D.obj m).Opens) : Set (D.obj m)) :=
    QuasiCompact.isCompact_preimage _ V₀.isOpen hV₀c
  obtain ⟨n, d, hd⟩ :=
    exists_map_preimage_le_map_preimage_of_initiallySmall D c hc hV₁c hpre.le
  refine ⟨n, d ≫ a, D.map d ⁻¹ᵁ (D.map b ⁻¹ᵁ V₀),
    QuasiCompact.isCompact_preimage _ (D.map b ⁻¹ᵁ V₀).isOpen hV₁c,
    by rwa [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_preimage], ?_⟩
  simp only [conePi_preimage_map_preimage, hV₀]

section Main

variable [∀ i : Iᵒᵖ, HasSheafify (D.obj i).smallEtaleTopology AddCommGrpCat.{max u v + 1}]
  [HasSheafify (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1}]

/-- **The surjectivity hypothesis `hsurj` of
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective_opensLeg`, from the
surjectivity of the leg over the quasi-compact opens of the levels.**

The quantification in `hsurj` is over the opens `W` of a level whose preimage in the limit is
quasi-compact, and such a `W` need not be quasi-compact itself. The hypothesis here is the same
statement restricted to the opens that *are* quasi-compact at their level, which is the form a
finite one-hypercover argument produces.

Both are **pointwise** in the section: a section of `𝒢` over the preimage of `W` is hit by the leg
at some level above, the level depending on the section. The level-first form — a level at which
the leg is surjective — is false; the docstring of
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective_opensLeg` carries the
counterexample.

The quasi-compact hypothesis is strictly weaker than `hsurj`, not a reformulation of it. It is
*implied* by `hsurj` because the projections of the cone are affine, hence quasi-compact,
morphisms (`AlgebraicGeometry.isAffineHom_π_app_of_initiallySmall`), so a quasi-compact open of a
level has quasi-compact preimage in the limit and is one of the opens `hsurj` speaks about. This
theorem is the converse, and it is where the work is:
`Stacks.EtaleCohomology.exists_isCompact_le_map_preimage` descends the open to a quasi-compact one
contained in it with the same preimage, and
`Stacks.EtaleCohomology.exists_opensSectionsLeg_eq_of_le` carries the section back up using
injectivity of the sheaf at the level. So the two hypotheses are interchangeable, and a consumer
may discharge the weaker one. -/
public theorem surjective_opensSectionsLeg_of_isCompact (hc : IsLimit c)
    (𝒢 : Sheaf (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (F : ∀ i : Iᵒᵖ, Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (hF : ∀ i : Iᵒᵖ, Injective (F i))
    (ι : ∀ i : Iᵒᵖ,
      (etaleAbelianInverseImage.{max u v, max u v + 1} (conePi c i)).obj (F i) ⟶ 𝒢)
    (hqc : ∀ (i : Iᵒᵖ) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) →
      ∀ τ : ToType (OpensAcyclicity.opensSections
        ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) (conePi c i ⁻¹ᵁ V)),
      ∃ (j : Iᵒᵖ) (a : j ⟶ i) (σ : ToType (OpensAcyclicity.opensSections
        ((MayerVietoris.mayerVietorisRestrict (D.obj j)).obj (F j)) (D.map a ⁻¹ᵁ V))),
        opensSectionsLeg (conePi c j) (ι j) (D.map a ⁻¹ᵁ V) σ =
          OpensAcyclicity.opensSectionsRestrict
            ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢)
            (conePi_preimage_map_preimage c a V).le τ)
    (i : Iᵒᵖ) (W : (D.obj i).Opens)
    (hW : IsCompact ((conePi c i ⁻¹ᵁ W : (c.pt).Opens) : Set c.pt))
    (τ : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) (conePi c i ⁻¹ᵁ W))) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i) (σ : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict (D.obj j)).obj (F j)) (D.map a ⁻¹ᵁ W))),
      opensSectionsLeg (conePi c j) (ι j) (D.map a ⁻¹ᵁ W) σ =
        OpensAcyclicity.opensSectionsRestrict
          ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢)
          (conePi_preimage_map_preimage c a W).le τ := by
  obtain ⟨j₀, a₀, V, hVc, hVle, hVeq⟩ := exists_isCompact_le_map_preimage hc i W hW
  have hVW₀ : conePi c j₀ ⁻¹ᵁ V = conePi c i ⁻¹ᵁ W := by
    simp only [hVeq, conePi_preimage_map_preimage]
  obtain ⟨j, a₁, σ₁, hσ₁⟩ := hqc j₀ V hVc (OpensAcyclicity.opensSectionsRestrict
    ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) hVW₀.le τ)
  have := hF j
  have hcomp : (D.map (a₁ ≫ a₀) ⁻¹ᵁ W : (D.obj j).Opens) = D.map a₁ ⁻¹ᵁ (D.map a₀ ⁻¹ᵁ W) := by
    rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_preimage]
  have hWj : conePi c j ⁻¹ᵁ (D.map a₁ ⁻¹ᵁ (D.map a₀ ⁻¹ᵁ W)) = conePi c i ⁻¹ᵁ W := by
    simp only [conePi_preimage_map_preimage]
  have heq : conePi c j ⁻¹ᵁ (D.map a₁ ⁻¹ᵁ V) =
      conePi c j ⁻¹ᵁ (D.map a₁ ⁻¹ᵁ (D.map a₀ ⁻¹ᵁ W)) := by
    simp only [conePi_preimage_map_preimage, hVW₀]
  have hg : opensSectionsLeg (conePi c j) (ι j) (D.map a₁ ⁻¹ᵁ V) σ₁ =
      OpensAcyclicity.opensSectionsRestrict
        ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) heq.le
        (OpensAcyclicity.opensSectionsRestrict
          ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) hWj.le τ) := by
    rw [hσ₁, OpensAcyclicity.opensSectionsRestrict_restrict,
      OpensAcyclicity.opensSectionsRestrict_restrict]
  obtain ⟨g', hg'⟩ := exists_opensSectionsLeg_eq_of_le.{max u v} (conePi c j) (ι j)
    (Scheme.Hom.preimage_mono _ hVle) heq _ σ₁ hg
  refine ⟨j, a₁ ≫ a₀, OpensAcyclicity.opensSectionsRestrict _ hcomp.le g', ?_⟩
  rw [← opensSectionsLeg_restrict (conePi c j) (ι j) hcomp.le g', hg',
    OpensAcyclicity.opensSectionsRestrict_restrict]

/-- **`hsub` for the colimit sheaf of [Stacks, Tag 09YQ] from the surjectivity of the leg over the
quasi-compact opens of the levels.** This is
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_surjective_opensLeg` with its
hypothesis `hsurj` supplied by
`Stacks.EtaleCohomology.surjective_opensSectionsLeg_of_isCompact`, so the quantification is over
the quasi-compact opens of the levels only. Nothing else in that theorem changes: the pair of
opens of the limit still descends by [Stacks, Tag 01Z4] (1), the Mayer--Vietoris splitting at the
level is still free from the injectivity of the sheaf there, and the transport down the projection
is still `exists_sectionsDifference_preimage_of_leg`. -/
public theorem sectionsDifference_of_isCompact_surjective_opensLeg [QuasiSeparatedSpace c.pt]
    (hc : IsLimit c)
    (𝒢 : Sheaf (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (F : ∀ i : Iᵒᵖ, Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{max u v + 1})
    (hF : ∀ i : Iᵒᵖ, Injective (F i))
    (ι : ∀ i : Iᵒᵖ,
      (etaleAbelianInverseImage.{max u v, max u v + 1} (conePi c i)).obj (F i) ⟶ 𝒢)
    (hqc : ∀ (i : Iᵒᵖ) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) →
      ∀ τ : ToType (OpensAcyclicity.opensSections
        ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) (conePi c i ⁻¹ᵁ V)),
      ∃ (j : Iᵒᵖ) (a : j ⟶ i) (σ : ToType (OpensAcyclicity.opensSections
        ((MayerVietoris.mayerVietorisRestrict (D.obj j)).obj (F j)) (D.map a ⁻¹ᵁ V))),
        opensSectionsLeg (conePi c j) (ι j) (D.map a ⁻¹ᵁ V) σ =
          OpensAcyclicity.opensSectionsRestrict
            ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢)
            (conePi_preimage_map_preimage c a V).le τ)
    (U V : (c.pt).Opens) (hU : IsCompact (U : Set c.pt)) (hV : IsAffineOpen V) :
    OpensAcyclicity.SectionsDifference
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝒢) U V :=
  OpensAcyclicity.sectionsDifference_of_surjective_opensLeg hc 𝒢 F hF ι
    (surjective_opensSectionsLeg_of_isCompact hc 𝒢 F hF ι hqc) U V hU hV

end Main

end Descent

end Stacks.EtaleCohomology

end
