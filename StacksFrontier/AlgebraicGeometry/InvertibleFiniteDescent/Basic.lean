module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Towards Stacks 0C0T: descent of invertible modules along a finite morphism

Stacks Tag 0C0T (Varieties, Lemma 33.38.7) asserts the following. Let `f : X ⟶ Y` be a finite
morphism of schemes, let `V ⊆ Y` be open with `f ∣_ V` an isomorphism, and assume the complement
`Vᶜ` carries the discrete topology. Then every invertible `𝒪_X`-module is the pullback of an
invertible `𝒪_Y`-module.

This file collects the cases of that assertion that are unconditional at this revision, each
stated in the shape the tag's statement uses — `∃ M, M` invertible `∧ Nonempty (f^* M ≅ L)`.
No `stacks` attribute is attached: the tag carries a single unlabelled assertion, so there is no
covering set short of the full statement. See the implementation notes for what is missing.

## Main results

* `Stacks.AlgebraicGeometry.InvertibleFiniteDescent.isIso_of_isIso_morphismRestrict_top`: a
  morphism whose restriction over `⊤` is an isomorphism is an isomorphism.
* `Stacks.AlgebraicGeometry.InvertibleFiniteDescent.exists_isInvertible_pullback_iso_of_isIso`:
  the conclusion of Tag 0C0T for an isomorphism `f`, with no finiteness or discreteness
  hypothesis. This is the base case of the tag, and the statement the two results below are built
  from.
* `Stacks.AlgebraicGeometry.InvertibleFiniteDescent.exists_isInvertible_pullback_iso_of_eq_top`:
  the conclusion of Tag 0C0T in the degenerate case `V = ⊤`, equivalently `Vᶜ = ∅`. The finiteness
  of `f` is not needed, and neither is the discreteness hypothesis, which is vacuous there.
* `InvertibleFiniteDescent.exists_isInvertible_pullback_iso_of_isoUnitModule`: the
  conclusion of Tag 0C0T for a *trivial* `L`, with `M = 𝒪_Y`, for an arbitrary morphism of
  schemes. Every invertible module is locally trivial, so this is the local model of the tag.
* `Stacks.AlgebraicGeometry.InvertibleFiniteDescent.exists_isInvertible_pullback_iso_restrict`:
  over `V` itself the module asked for exists and is invertible. This is the half of the
  construction that the hypothesis `IsIso (f ∣_ V)` supplies outright.

## The route, and what is missing

The source proof is cohomological: `Pic(X) = H¹(X, 𝒪_X^*)` (Cohomology, Lemma 20.6.1), the Leray
spectral sequence for `𝒪_X^*` along `f` (Cohomology, Lemma 20.13.4) with the vanishing of its
edge map (Divisors, Lemma 31.18.1), and then the two short exact sequences cut out of
`f^♯ : 𝒪_Y^* ⟶ f_* 𝒪_X^*`, whose kernel and cokernel are supported on the closed set `Vᶜ`;
discreteness of `Vᶜ` is what makes the higher cohomology of a sheaf supported there vanish
(Cohomology, Lemma 20.20.1). That route is not available, and the reason is the *multiplicative*
sheaf, not cohomology as such: nothing in this repository identifies `Pic` with `H¹` of the sheaf
of units, and the Leray machinery that is here — `Stacks.AlgebraicGeometry.RelativeLeray`,
`LeraySectionsCollapse` — is built for pushforwards of sheaves of *modules*, so it does not apply
to `𝒪_X^*` at all. The sheaf of units itself does exist
(`StacksFrontier/CategoryTheory/Sites/Modules/UnitsSheaf.lean`); the comparison with `Pic` and the
edge-map vanishing are what is absent.

The elementary route avoids the multiplicative sheaf. Writing `T = Vᶜ`, it runs: for each `t ∈ T`
the fibre `f⁻¹(t)` is finite, so `X ×_Y Spec 𝒪_{Y,t}` is the spectrum of a semilocal ring, whose
Picard group vanishes; spreading that out gives an open `U_t ∋ t` with `L` trivial on `f⁻¹(U_t)`;
discreteness of `T` shrinks `U_t` so that `U_t ∩ T = {t}`; and then `M` is glued over the cover
`{V} ∪ {U_t}` from `𝒪_{U_t}` and the module on `V` that
`exists_isInvertible_pullback_iso_restrict` already produces.

Two of those three steps are **not** missing, and it is worth being precise about which:

* the shrinking of `U_t` is Mathlib's `isOpen_inter_eq_singleton_of_mem_discrete`, see the
  implementation notes below;
* the gluing is `Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData` with
  `ChartGlueData.glued` and the chart identification `SchemeModuleGlue.chartIso`
  (`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean`), over
  `TopCat.Sheaf.OModuleGlueData` (`StacksFrontier/Topology/Sheaves/Glueing/OModule.lean`): a
  construction that *builds* an `X.Modules` from a sheaf of modules on each chart together with
  comparison isomorphisms over the overlaps, and identifies the restriction of the result along
  each chart with the module it was glued from. Invertibility of a glued `M` would then follow
  from that identification and the local criterion
  `Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over`.

What is genuinely missing is the local input: **the triviality of the Picard group of a semilocal
ring, and its spreading out to a neighbourhood** — that is, `L` trivial on `f⁻¹(U_t)` for some
open `U_t ∋ t`. "Semilocal" occurs in this repository only in
`StacksFrontier/AlgebraicGeometry/Variety/DimensionOne/GlueDVR.lean`, which is a different
statement about units, and no form of "an invertible module over a semilocal ring is free" is
present. Assembling the comparison isomorphisms of the `ChartGlueData` from such trivialisations,
and producing `f^* M ≅ L` from the chart identifications, is then work but not a missing theory.

## Implementation notes

**The invertibility predicate.** Tag 01CS is realised twice in this repository, as
`Stacks.SheafOfModules.IsInvertible` and as `AlgebraicGeometry.SheafOfModules.IsInvertible`
(hence as `Stacks.Ample.IsInvertibleModule`); the two are bridged by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. The statements
below use the first, which is the spelling in which Tag 0B8L is proved at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling of the pullback
(`Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj`). That instance is what makes the
existential witnesses below invertible, and it is the only place invertibility is produced here.

**The two pullback spellings.** `AlgebraicGeometry.Scheme.Modules.pullback g` and
`RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom` are identified by
`Stacks.ProjectiveBundleQuotients.pullbackIso`; instance search does not cross between them, so
the unit isomorphism `f^* 𝒪_Y ≅ 𝒪_X`, which is available at the second spelling as
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, is transported along that comparison here.

**The discreteness hypothesis is not an obstruction.** `DiscreteTopology (Vᶜ : Set Y)` is turned
into the usable form "every `t ∈ Vᶜ` has an open neighbourhood meeting `Vᶜ` only in `t`" by
Mathlib's `isOpen_inter_eq_singleton_of_mem_discrete`
(`Mathlib/Topology/Separation/Basic.lean`), whose hypothesis `IsDiscrete ↑Vᶜ` is
`isDiscrete_iff_discreteTopology` (`Mathlib/Topology/Constructions.lean`) applied to the
hypothesis as stated. Nothing needs to be built for that step, and nothing below needs it,
because the step it feeds is the gluing that is missing.

## References

* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.InvertibleFiniteDescent

/-! ### A morphism that is an isomorphism over `⊤` is an isomorphism -/

/-- **A morphism of schemes whose restriction over `⊤` is an isomorphism is an isomorphism.**
The restriction fits in `(f ∣_ ⊤) ≫ ι⊤ = ι(f ⁻¹ᵁ ⊤) ≫ f` and both inclusions of `⊤` are
isomorphisms, so the composite `ι(f ⁻¹ᵁ ⊤) ≫ f` is one and `f` is its right factor. -/
theorem isIso_of_isIso_morphismRestrict_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (f ∣_ (⊤ : Y.Opens))] : IsIso f := by
  have key : ∀ {Z : Scheme.{u}} (U : Z.Opens), U = ⊤ → IsIso U.ι := by
    rintro Z U rfl
    exact Z.topIso.isIso_hom
  have := key (⊤ : Y.Opens) rfl
  have := key (f ⁻¹ᵁ (⊤ : Y.Opens)) (by simp)
  have : IsIso ((f ⁻¹ᵁ (⊤ : Y.Opens)).ι ≫ f) := by
    rw [← morphismRestrict_ι f ⊤]; infer_instance
  exact IsIso.of_isIso_comp_left (f ⁻¹ᵁ (⊤ : Y.Opens)).ι f

/-! ### Tag 0C0T for an isomorphism -/

/-- **The conclusion of Stacks Tag 0C0T when `f` is an isomorphism**: every invertible
`𝒪_X`-module is the pullback of an invertible `𝒪_Y`-module, namely of its pullback along `f⁻¹`.

Invertibility of the witness is Tag 0B8L, and the isomorphism `f^* (f⁻¹)^* L ≅ L` is the
compatibility of the pullback with composition and with the identity. Neither finiteness of `f`
nor any hypothesis on a complement is used. -/
theorem exists_isInvertible_pullback_iso_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ M : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M ∧
        Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) :=
  ⟨(Scheme.Modules.pullback (inv f)).obj L, inferInstance,
    ⟨(Scheme.Modules.pullbackComp f (inv f)).app L ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id f)).app L ≪≫
      (Scheme.Modules.pullbackId X).app L⟩⟩

/-! ### Tag 0C0T in the degenerate case `V = ⊤` -/

/-- **Stacks Tag 0C0T in the case `V = ⊤`**, equivalently `Vᶜ = ∅`: the hypothesis
`IsIso (f ∣_ V)` then says that `f` itself is an isomorphism, and the conclusion follows from
`Stacks.AlgebraicGeometry.InvertibleFiniteDescent.exists_isInvertible_pullback_iso_of_isIso`. The
finiteness of `f` is not used, and the discreteness hypothesis on `Vᶜ` is vacuous. -/
theorem exists_isInvertible_pullback_iso_of_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : V = ⊤) [IsIso (f ∣_ V)] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ M : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M ∧
        Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  subst hV
  have := isIso_of_isIso_morphismRestrict_top f
  exact exists_isInvertible_pullback_iso_of_isIso f L

/-! ### Tag 0C0T for a trivial module -/

/-- **The conclusion of Stacks Tag 0C0T for a trivial `L`**, with `M = 𝒪_Y`: this holds for an
arbitrary morphism of schemes, with no finiteness, no open `V` and no discreteness. Every
invertible module is locally trivial, so this is the local model of the tag; what Tag 0C0T adds
is the globalisation, which is the gluing step named in the module docstring. -/
theorem exists_isInvertible_pullback_iso_of_isoUnitModule {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : X.Modules) (e : L ≅ Stacks.Ample.unitModule X) :
    ∃ M : Y.Modules,
      Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M ∧
        Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) :=
  ⟨Stacks.Ample.unitModule Y,
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Y.presheaf Y.ringCatSheaf.2 _).mpr inferInstance,
    ⟨(Stacks.ProjectiveBundleQuotients.pullbackIso f).app (Stacks.Ample.unitModule Y) ≪≫
      RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f.toLRSHom.toShHom ≪≫ e.symm⟩⟩

/-! ### The module over `V` exists -/

/-- **Over `V` itself the module that Stacks Tag 0C0T asks for exists and is invertible.** The
hypothesis `IsIso (f ∣_ V)` makes `f ∣_ V` an isomorphism of schemes, so
`Stacks.AlgebraicGeometry.InvertibleFiniteDescent.exists_isInvertible_pullback_iso_of_isIso`
applies to it and to the restriction `L|_{f⁻¹V}`, which is invertible by Tag 0B8L. This is the half
of the construction of `M` that the hypotheses supply outright; the other half, trivialising `L`
over a neighbourhood of each point of `Vᶜ` and gluing, is what is missing. -/
theorem exists_isInvertible_pullback_iso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    [IsIso (f ∣_ V)] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ M : V.toScheme.Modules,
      Stacks.SheafOfModules.IsInvertible V.toScheme.presheaf V.toScheme.ringCatSheaf.2 M ∧
        Nonempty ((Scheme.Modules.pullback (f ∣_ V)).obj M ≅
          (Scheme.Modules.pullback (Scheme.Opens.ι (f ⁻¹ᵁ V))).obj L) :=
  exists_isInvertible_pullback_iso_of_isIso (f ∣_ V)
    ((Scheme.Modules.pullback (Scheme.Opens.ι (f ⁻¹ᵁ V))).obj L)

end Stacks.AlgebraicGeometry.InvertibleFiniteDescent

end
