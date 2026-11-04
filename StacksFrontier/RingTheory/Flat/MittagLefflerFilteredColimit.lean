module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.RingTheory.Flat.MittagLefflerEssFiniteType

/-!
# A filtered colimit of free modules with injective reductions is Mittag-Leffler

Stacks 05U7 presents a finite flat module over an essentially finite type local algebra on a
henselian base as a *filtered* colimit of free modules whose transition maps stay injective
modulo the maximal ideal, and concludes that the module is Mittag-Leffler. The module-level
deduction of the Mittag-Leffler conclusion in `StacksFrontier.RingTheory.Flat.MittagLefflerLocal`,
`Module.mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal`, is stated for a system indexed
by a nonempty *directed preorder*, because that is the index for which Stacks 0AS7 is formalized. A
filtered index category is strictly weaker: it need not be a preorder at all.

This file removes that mismatch. By Deligne's theorem (Stacks 0032, Mathlib's
`CategoryTheory.IsFiltered.exists_directed`) every small filtered category `I` receives a final
functor `G : α ⥤ I` from a nonempty directed partial order `α`; a final functor does not change
colimits, so the colimit of a filtered system is the colimit of its restriction along `G`, which
*is* indexed by a directed preorder. Every hypothesis of the directed statement — freeness of
the stages and injectivity of the reductions of the transition maps — is inherited by the
restricted system, since its stages and transition maps are stages and transition maps of the
original one.

## Main results

* `Module.mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal_of_isFiltered`: the colimit of
  a filtered system of free modules over a local ring with injective reductions modulo the
  maximal ideal is Mittag-Leffler, in the single-universe form of Stacks 059E (1).
* `Module.isMittagLeffler_of_isFilteredColimit_free_of_injective_mapQ_maximalIdeal`: the same,
  with the conclusion the predicate `IsMittagLeffler` of Stacks 059F in its universe-general
  form, for any module linearly equivalent to the colimit.

## Implementation notes

The index category is `SmallCategory I` with `I : Type (max u uM)`, matching both Mathlib's
`IsFiltered.exists_directed` — which needs the category small to apply Deligne's construction —
and the universe in which the modules of the system live.

`IsFiltered.exists_directed` produces a `PartialOrder`, which is in particular a `Preorder`, and
`IsDirected α (· ≤ ·)`, which is by definition `IsDirectedOrder α`; both, together with
`Nonempty α`, are introduced into the context as anonymous hypotheses of class type and so are
found by instance resolution, which is what lets the directed statement be applied verbatim.

The reduction of a transition map of the restricted system is the reduction of a transition map
of the original system, but not syntactically: `(G ⋙ F).map f` is `F.map (G.map f)` only up to
unfolding. The two injectivity hypotheses are therefore related by `Functor.comp_map`, which is
definitional, so the hypotheses transfer by `exact`.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 0AS7](https://stacks.math.columbia.edu/tag/0AS7)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
* [Stacks Project, Tag 059F](https://stacks.math.columbia.edu/tag/059F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe uP uQ uN uM u v w

namespace Module

/-- **The second half of the proof of Stacks 05U7, for a filtered index category.** Let
`(A, 𝔪)` be a local ring and let `(F i, u_{i i'})` be a system of free `A`-modules indexed by a
small filtered category, such that every transition map induces an injective map
`F i / 𝔪 F i → F i' / 𝔪 F i'`. Then the colimit of the system is a Mittag-Leffler `A`-module.

Being Mittag-Leffler is spelled out in the intrinsic form of Stacks 059E (1), as in the library's
Stacks 0AS7 and as in `Module.mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal`, of which
this is the filtered-index form. -/
theorem mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal_of_isFiltered
    {A : Type u} [CommRing A] [IsLocalRing A] [Small.{v} A]
    {I : Type w} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ ModuleCat.{v} A} {c : Cocone F}
    (hfree : ∀ i, Module.Free A (F.obj i))
    (hinj : ∀ {i j : I} (u : i ⟶ j), Function.Injective
      (Submodule.mapQ
        (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
        (F.map u).hom
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map u).hom)))
    (hc : IsColimit c) :
    ∀ (P : Type v) [AddCommGroup P] [Module A P] [Module.FinitePresentation A P]
        (f : P →ₗ[A] c.pt),
      ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module A Q) (_ : Module.FinitePresentation A Q)
        (g : P →ₗ[A] Q), ∀ (N : Type v) [AddCommGroup N] [Module A N],
          LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  obtain ⟨α, _, _, _, G, hG⟩ := IsFiltered.exists_directed I
  have hcw : IsColimit (c.whisker G) := (Functor.Final.isColimitWhiskerEquiv G c).symm hc
  exact mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal
    (F := G ⋙ F) (c := c.whisker G) (fun i => hfree (G.obj i))
    (fun {_ _} u => hinj (G.map u)) hcw

/-- **The second half of the proof of Stacks 05U7 for a filtered index category**, with the
conclusion the predicate `IsMittagLeffler` of Stacks 059F in its universe-general form. Any
`A`-module linearly equivalent to the colimit of a small filtered system of free `A`-modules
whose transition maps have injective reductions modulo `𝔪_A` is a Mittag-Leffler `A`-module.

This is the filtered-index form of
`Module.isMittagLeffler_of_colimit_free_of_injective_mapQ_maximalIdeal`. -/
theorem isMittagLeffler_of_isFilteredColimit_free_of_injective_mapQ_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A] {I : Type w} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ ModuleCat.{max u uM} A} {c : Cocone F}
    (hfree : ∀ i, Module.Free A (F.obj i))
    (hinj : ∀ {i j : I} (u : i ⟶ j), Function.Injective
      (Submodule.mapQ
        (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
        (F.map u).hom
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map u).hom)))
    (hc : IsColimit c) {N : Type uM} [AddCommGroup N] [Module A N]
    (e : (c.pt : Type (max u uM)) ≃ₗ[A] N) :
    IsMittagLeffler.{u, uP, uM, max u uQ, uN} A N :=
  IsMittagLeffler.of_small_univ
    (((isMittagLeffler_def_iff A (c.pt : Type (max u uM))).mpr
      (mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal_of_isFiltered
        hfree hinj hc)).of_linearEquiv e)

end Module

end
