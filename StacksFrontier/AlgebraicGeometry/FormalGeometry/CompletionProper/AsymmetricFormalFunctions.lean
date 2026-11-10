module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceSeparated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksCore.Tactic.StacksAttribute

/-!
# The asymmetric comparison: only the target needs proper support

Let `X` be a locally Noetherian scheme, `f : X ⟶ S` locally of finite type, `ℐ` a quasi-coherent
ideal sheaf on `X` and `ℱ`, `𝒢` coherent `𝒪_X`-modules. This file proves that the completion
functor of Stacks 0880 is bijective on `Hom(ℱ, 𝒢)` with **no condition on `ℱ` at all** as soon as
the theorem on formal functions in degree zero is known for coherent sheaves whose support is
proper over `S`.

## Why an asymmetric statement is wanted

The full faithfulness this library carries for a non-proper base is
`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer`, and it is
**symmetric**: its two inputs are annihilation of the source *and* of the target by the ideal
sheaf of one closed subscheme proper over the base, produced from proper support of both by
`Stacks.Algebraization.exists_isProper_annihilatedByKer_pair`. That symmetry is what blocks the
algebra hypothesis of Stacks 09ZT, 0A42 and 0899: the residual
`AlgebraicGeometry.AdicAlgebraStructureTransport` has to move the *unit*
`AlgebraicGeometry.ModuleAlgebraData.unit`, a morphism out of `𝒪_X`, and `𝒪_X` has full support,
so `Stacks.Algebraization.HasProperSupport f (SheafOfModules.unit X.ringCatSheaf)` is properness
of `f` itself — which the consuming theorem does not have. The implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraAlgebraization.lean` record exactly
this.

## What is proved, and what the asymmetry costs

The whole of the asymmetry is the first result below: for coherent `ℱ` and `𝒢`, the support of
`SheafHom(ℱ, 𝒢)` is contained in the support of `𝒢`, so `SheafHom(ℱ, 𝒢)` has support proper over
the base as soon as `𝒢` does. Since a morphism `ℱ ⟶ 𝒢` is a global section of `SheafHom(ℱ, 𝒢)`
and the comparison Stacks 0883 consumes is the formal-functions comparison *for that one sheaf*
(`Stacks.Algebraization.completionFunctor_map_bijective`), the first variable then disappears
from the hypothesis list entirely: what is left is

  `hFF : ∀ ℋ coherent with support proper over S, IsIso (globalSectionsToLimit ℐ ℋ)`,

in which `ℱ` does not occur. That is the degree-zero theorem on formal functions (Stacks 087U,
i.e. [Stacks, Tag 02OC] in degree zero) for a coherent sheaf with **proper support** rather than
over a proper morphism, and it is the one residual: `Γ(X, 𝒩) ≅ limₙ Γ(X, 𝒩 / ℐⁿ𝒩)`.

So the answer to the question this file was written to settle is: **yes, the internal-hom support
containment is the whole asymmetry.** Nothing else about `ℱ` is used, and the residual is a
statement about a single sheaf.

## Why the residual is not discharged here

For a *proper* `f` the residual is `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper`,
unconditionally. For proper *support* it is not available at this pin, and the two routes to it
both need an input this library lacks:

* through `Stacks.Algebraization.isIso_cohomologyToLimit`, whose three hypotheses are the
  finiteness of `Hᵖ(X, ℋ)` over the base and the two uniform Artin-Rees bounds of
  [Stacks, Tag 02OB]. The latter are carried only by
  `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`,
  whose signature takes `AlgebraicGeometry.IsProper f` — properness of the morphism, not of the
  support.
* through the closed subscheme `Z ⊆ X` proper over `S` that
  `Stacks.Algebraization.exists_isProper_annihilatedByKer_of_hasProperSupport` produces, on which
  the residual *is* a theorem. Transporting it back to `X` along `Z ⟶ X` needs the comparison of
  `Stacks.Algebraization.globalSectionsToLimit` for `i_* ℋ_Z` on `X` with the one for `ℋ_Z` on
  `Z`. The isomorphism of inverse systems is available
  (`Stacks.Algebraization.pushforwardCompletionIso`), but the two comparisons are maps of
  `ModuleCat Γ(X, ⊤)` and of `ModuleCat Γ(Z, ⊤)` respectively, and the identification of the two
  limits across that change of base ring is not in this library.

A third route — reading
`Stacks.Algebraization.bijective_completionFunctor_map_iff_isIso_globalSectionsToLimit` backwards
on the pair `(𝒪_X / 𝒥, ℋ)`, both of whose members have proper support when `𝒥` is the annihilator
of `ℋ` — would discharge the residual from the symmetric theorem already proved, but it needs
`SheafHom(𝒪_X / 𝒥, ℋ) ≅ ℋ` for `𝒥 ℋ = 0`. The first-variable left exactness available for that,
`Stacks.SheafOfModules.InternalHom.ihomCokernelIsoKernel`, presents the left-hand side as the
kernel of the dual of `𝒥 𝒪_X ⟶ 𝒪_X`, and that dual has to be shown to vanish; it is stated for
`MonoidalClosed.internalHom`, which that file's own implementation notes say is identified with
the internal hom of [Stacks, Tag 03EM] at objects only. Nothing below assumes any of this.

## Main results

* `Stacks.Algebraization.supp_internalHomCoherent_subset` — `Supp SheafHom(ℱ, 𝒢) ⊆ Supp 𝒢`.
* `Stacks.Algebraization.hasProperSupport_internalHomCoherent` — hence `SheafHom(ℱ, 𝒢)` has
  support proper over the base when `𝒢` does. **This is the asymmetry.**
* `Stacks.Algebraization.bijective_completionFunctor_map_of_hasProperSupport` — **the asymmetric
  comparison**: `Hom(ℱ, 𝒢) ≅ Hom_{Coh(X, ℐ)}(ℱ^∧, 𝒢^∧) = limₙ Hom(ℱₙ, 𝒢ₙ)` for coherent `ℱ` and
  `𝒢` of proper support, granted the residual `hFF`.
* `Stacks.Algebraization.bijective_completionFunctor_map_of_hasProperSupport_adic` — the same in
  the adic vocabulary the consumers of Stacks 088E use, at `ℐ = I · 𝒪_X`.
* `Stacks.Algebraization.isIso_globalSectionsToLimit_of_hasProperSupport_of_isProper` — the
  residual is a theorem when `f` is proper, so the asymmetric comparison is unconditional there;
  this records that the binder is not vacuous.

## Implementation notes

The support containment is proved through annihilator ideal sheaves rather than through stalks.
`Stacks.Algebraization.idealPowerMultiple_sheafHom_eq_bot` says that an ideal sheaf annihilating
the target annihilates the internal hom, so the annihilator of `𝒢` is contained in the
annihilator of `SheafHom(ℱ, 𝒢)` by
`Stacks.Algebraization.le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot`; supports of ideal
sheaves are antitone, and the support of a coherent module is the support of its annihilator
(`AlgebraicGeometry.supp_eq_support_annihilatorIdeal`). No stalk of an internal hom is computed,
which is what makes the containment cheap: computing `SheafHom(ℱ, 𝒢)ₓ` as `Hom(ℱₓ, 𝒢ₓ)` would
need finite presentation of `ℱ` and a filtered-colimit argument.

`Stacks.Algebraization.internalHomCoherent X F G` is `rfl`-equal to
`(Stacks.Algebraization.sheafHomFunctor X (coherentObj F)).obj G.obj`, so the annihilation lemma,
stated for the functor, applies to it with no transport.

## References

* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 088D](https://stacks.math.columbia.edu/tag/088D)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-! ### The support of the internal hom -/

/-- **The support of the internal hom is contained in the support of its target.** For coherent
`ℱ` and `𝒢` on a locally Noetherian scheme, `Supp SheafHom(ℱ, 𝒢) ⊆ Supp 𝒢`.

The annihilator ideal sheaf of `𝒢` annihilates `SheafHom(ℱ, 𝒢)`, hence is contained in the
annihilator ideal sheaf of `SheafHom(ℱ, 𝒢)`; the support of an ideal sheaf is antitone, and the
support of a coherent module is the support of its annihilator. -/
public theorem supp_internalHomCoherent_subset {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    _root_.SheafOfModules.supp (internalHomCoherent X F G).obj ⊆
      _root_.SheafOfModules.supp G.obj := by
  have hG : G.obj.IsCoherent := G.property
  have hH : (internalHomCoherent X F G).obj.IsCoherent := (internalHomCoherent X F G).property
  have hGbot : idealPowerMultiple (annihilatorIdeal G.obj) 1 G.obj = ⊥ :=
    (le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot G.obj (annihilatorIdeal G.obj)).1
      le_rfl
  have hHbot : idealPowerMultiple (annihilatorIdeal G.obj) 1
      (internalHomCoherent X F G).obj = ⊥ :=
    idealPowerMultiple_sheafHom_eq_bot 1 (coherentObj F) G.obj hGbot
  have hle : annihilatorIdeal G.obj ≤ annihilatorIdeal (internalHomCoherent X F G).obj :=
    (le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot
      (internalHomCoherent X F G).obj (annihilatorIdeal G.obj)).2 hHbot
  rw [supp_eq_support_annihilatorIdeal (internalHomCoherent X F G).obj,
    supp_eq_support_annihilatorIdeal G.obj]
  exact fun x hx => Scheme.IdealSheafData.support_antitone hle hx

/-- **The internal hom has support proper over the base as soon as its target does.** This is the
asymmetry: no condition whatever is placed on the source `ℱ`.

Its support is contained in that of `𝒢` by
`Stacks.Algebraization.supp_internalHomCoherent_subset`, and a closed subset of a closed subset
proper over the base is proper over the base. -/
public theorem hasProperSupport_internalHomCoherent {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : HasProperSupport f G.obj) :
    HasProperSupport f (internalHomCoherent X F G).obj := by
  have hH : (internalHomCoherent X F G).obj.IsCoherent := (internalHomCoherent X F G).property
  have : (internalHomCoherent X F G).obj.IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := (internalHomCoherent X F G).obj)
  obtain ⟨Z, hZ, hZproper⟩ := hG
  refine ⟨⟨_root_.SheafOfModules.supp (internalHomCoherent X F G).obj,
    _root_.SheafOfModules.isClosed_supp (internalHomCoherent X F G).obj⟩, rfl, ?_⟩
  refine isProperOver_of_le f ?_ hZproper
  change _root_.SheafOfModules.supp (internalHomCoherent X F G).obj ≤ (Z : Set X)
  rw [hZ]
  exact supp_internalHomCoherent_subset F G

/-! ### The asymmetric comparison -/

/-- **The asymmetric formal-functions comparison.** Let `X` be locally Noetherian, `f : X ⟶ S`
locally of finite type and `ℐ` a quasi-coherent ideal sheaf on `X`. Granted the theorem on formal
functions in degree zero for coherent sheaves with support proper over `S` — the hypothesis `hFF`
— completion along `ℐ` is bijective on the morphisms from a coherent `ℱ` to a coherent `𝒢` whose
support is proper over `S`:

  `Hom(ℱ, 𝒢) ≅ Hom_{Coh(X, ℐ)}(ℱ^∧, 𝒢^∧) = limₙ Hom(ℱₙ, 𝒢ₙ)`.

**No condition is placed on `ℱ`.** This is what the symmetric
`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer` cannot give: it needs
the source annihilated by the ideal of a proper closed subscheme too, which for `ℱ = 𝒪_X` means
`f` is proper.

The proof is Stacks 0883 at a single hom-set
(`Stacks.Algebraization.completionFunctor_map_bijective`), whose input is the comparison for the
one sheaf `SheafHom(ℱ, 𝒢)`; that sheaf has support proper over `S` by
`Stacks.Algebraization.hasProperSupport_internalHomCoherent`, so `hFF` applies to it. -/
public theorem bijective_completionFunctor_map_of_hasProperSupport {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ S) [LocallyOfFiniteType f] (I : X.IdealSheafData)
    (hFF : ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      HasProperSupport f H.obj → IsIso (globalSectionsToLimit I H))
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : HasProperSupport f G.obj) :
    Function.Bijective
      ((completionFunctor X I).map :
        (F ⟶ G) → ((completionFunctor X I).obj F ⟶ (completionFunctor X I).obj G)) :=
  completionFunctor_map_bijective I F G
    (hFF (internalHomCoherent X F G) (hasProperSupport_internalHomCoherent f F G hG))

/-- **The asymmetric comparison in the adic vocabulary of Stacks 088D and 088E.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal and `f : X ⟶ Spec A` locally of finite type; put
`𝓘 = I · 𝒪_X`. Granted the theorem on formal functions in degree zero for coherent sheaves with
support proper over `A`, completion along `𝓘` is bijective on `Hom(ℱ, 𝒢)` for coherent `ℱ` and
coherent `𝒢` of proper support.

This is the form the algebra hypothesis of Stacks 09ZT, 0A42 and 0899 asks for: `ℱ` may be
`𝒪_X`, whose support is all of `X`. -/
public theorem bijective_completionFunctor_map_of_hasProperSupport_adic (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f]
    (hFF : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        HasProperSupport f H.obj → IsIso (globalSectionsToLimit (baseIdealSheaf A I f) H))
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : HasProperSupport f G.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Function.Bijective
      ((completionFunctor X (baseIdealSheaf A I f)).map :
        (F ⟶ G) → ((completionFunctor X (baseIdealSheaf A I f)).obj F ⟶
          (completionFunctor X (baseIdealSheaf A I f)).obj G)) :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  bijective_completionFunctor_map_of_hasProperSupport f (baseIdealSheaf A I f) hFF F G hG

/-! ### The specialisation at `ℱ = 𝒪_X` -/

/-- **The specialisation of the asymmetric comparison at `ℱ = 𝒪_X`.** The structure sheaf of a
locally Noetherian scheme is coherent ([Stacks, Tag 01XZ]), and it is an admissible source of the
asymmetric comparison precisely because no condition is placed on the source. So for a coherent
`𝒩` whose support is proper over `S`,

  `Hom(𝒪_X, 𝒩) ≅ Hom_{Coh(X, ℐ)}(𝒪_X^∧, 𝒩^∧)`,

which under `Stacks.Algebraization.globalSectionOfHom` on the left — morphisms out of the
structure sheaf are global sections — and the annihilation of `𝒩ₙ = 𝒩 / ℐⁿ⁺¹𝒩` by `ℐⁿ⁺¹` on the
right is `Γ(X, 𝒩) ≅ limₙ Γ(X, 𝒩ₙ)`, the theorem on formal functions in degree zero.

This is the statement the unit of `AlgebraicGeometry.ModuleAlgebraData` needs moved, and the one
the symmetric full faithfulness of
`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer` cannot supply, since
`Stacks.Algebraization.HasProperSupport f (SheafOfModules.unit X.ringCatSheaf)` is properness of
`f`. -/
public theorem bijective_completionFunctor_map_unit_of_hasProperSupport {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ S) [LocallyOfFiniteType f] (I : X.IdealSheafData)
    (hFF : ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      HasProperSupport f H.obj → IsIso (globalSectionsToLimit I H))
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : HasProperSupport f G.obj) :
    Function.Bijective
      ((completionFunctor X I).map :
        ((⟨SheafOfModules.unit X.ringCatSheaf,
              Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X⟩ :
            AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ⟶ G) →
          ((completionFunctor X I).obj
              ⟨SheafOfModules.unit X.ringCatSheaf,
                Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X⟩ ⟶
            (completionFunctor X I).obj G)) :=
  bijective_completionFunctor_map_of_hasProperSupport f I hFF _ G hG

/-- **The residual, for a proper morphism.** When `f` is proper every coherent sheaf satisfies the
degree-zero theorem on formal functions, with or without a condition on its support, so the
hypothesis `hFF` of `Stacks.Algebraization.bijective_completionFunctor_map_of_hasProperSupport`
holds. This records that the binder is satisfiable; it is not what the consumers of the
asymmetric form have, since they have only a separated morphism of finite type. -/
public theorem isIso_globalSectionsToLimit_of_hasProperSupport_of_isProper (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (_hH : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      HasProperSupport f H.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsIso (globalSectionsToLimit (baseIdealSheaf A I f) H) :=
  isIso_globalSectionsToLimit_of_isProper A I f H

end Stacks.Algebraization

end
