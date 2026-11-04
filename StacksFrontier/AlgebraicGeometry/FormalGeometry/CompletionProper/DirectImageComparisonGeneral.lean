module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GeneralBaseAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceSeparated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportAlgebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 088B over a base morphism that is not proper

Let `A` be a Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be locally of
finite type with `X` Noetherian, set `𝓘 = I · 𝒪_X`, let `π : Y ⟶ X` be proper with `Y` Noetherian
and let `𝒦 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. [Stacks, Tag 088B] produces, from a
coherent `𝒪_Y`-module `𝓕`, an object `(𝓖_n)` of `Coh(X, 𝓘)` and the source's isomorphism
`β : π^*(𝓖_n) ≅ 𝓕 ^∧`, a morphism

`α : (𝓖_n) ⟶ (π_*𝓕) ^∧`

whose levelwise kernels and cokernels are annihilated by a power of `𝒦`.

The library already has that statement with **`f` proper**,
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper`
(`CompletionProper/DevissageComparison.lean`), carrying one binder: `halg`, an algebraization of
`(𝓖_n)`. Properness of `f` enters there in exactly one place — it discharges the binder

`hff : Nonempty (completionFunctor Y (𝓘.comap π)).FullyFaithful`

of `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage`
through `Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper`, i.e. through
Stacks 0883 for `π ≫ f`. **This file deletes properness of `f`**, replacing `hff` by proper
support of the two modules the descent of `β` actually compares. The point of the deletion is
[Stacks, Tag 088E]: the scheme `X` there is separated, locally of finite type and quasi-compact
over `A` and never proper over `A`, so the `[IsProper f]` form of the comparison cannot be
instantiated at its point of use, while the proper-support hypotheses are exactly the data the
systems of 088E carry.

## How `hff` is discharged without properness

Full faithfulness of completion on `Y` is **false** for a non-proper `Y`: for `A = ℤ_p`,
`I = (p)` and `Y = 𝔸¹_{ℤ_p}` the hypothesis `hFF` of Stacks 0883 already fails at `H = 𝒪_Y`,
the map `H⁰(Y, 𝒪_Y) = ℤ_p[t] ⟶ lim ℤ_p[t]/pⁿ` missing `Σ pⁿtⁿ`, and so does the conclusion:
morphisms `𝒪_Y ^∧ ⟶ 𝒪_Y ^∧` in `Coh(Y, 𝓘 𝒪_Y)` are the elements of that limit, which is
strictly larger than `Hom(𝒪_Y, 𝒪_Y) = ℤ_p[t]`. No amount of bookkeeping will supply it. What the
proof of 088B uses it for, however, is a single descent: `β` presents an isomorphism between the
completions of the two coherent `𝒪_Y`-modules `π^*𝒜` and `𝓕` (`𝒜` an algebraization of `(𝓖_n)`),
and the descent only needs completion to be **bijective on the morphisms between those two
modules**. That is the move the first paragraph of the proof of 088E makes for its own full
faithfulness: restrict to a closed subscheme proper over `A`, where Stacks 0883 is unconditional.
Here it is available ready-made as
`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer`
(`CompletionProper/GrothendieckExistenceSeparated.lean`), which asks only that the two modules be
annihilated by the ideal sheaf of one closed subscheme proper over `A` — and two coherent modules
with support proper over `A` always are, by
`Stacks.Algebraization.exists_isProper_annihilatedByKer_pair`.

`Stacks.Algebraization.exists_iso_of_bijective_completionFunctor_map` is the elementary step that
turns those bijectivities into an isomorphism of modules; it replaces
`Stacks.Coherent.pullbackCompletionDescent`, whose input is the full faithfulness of the whole
functor.

## Why the support of the algebraization is a hypothesis and not a bookkeeping cost

The proper support of `𝓕` is free in the situation of 088E. The proper support of `𝒜` is a real
strengthening of `halg`, and it cannot be dropped: **the descent of `β` is false without it.**
Take `A = ℤ_p`, `I = (p)`, `X = 𝔸¹_{ℤ_p} = Spec ℤ_p[t]`, `f` the structure morphism, `π = 𝟙`,
`𝒜 = 𝒪_X / (pt - 1) = ℚ_p` and `𝓕 = 0`. Then `𝒜` is coherent, `𝒜 ^∧ = 0` because `p` acts
invertibly on `ℚ_p`, so `β : π^*(𝒜 ^∧) = 0 ≅ 0 = 𝓕 ^∧` exists, while `π^*𝒜 = ℚ_p` is not
isomorphic to `𝓕 = 0`. The support of `𝒜` is the closed point `V(pt - 1)`, whose image in
`Spec ℤ_p` is the generic point: a closed subset that is *not* proper over `A`, which is exactly
the hypothesis the counterexample violates. Once `𝒜` has support proper over `A` so does `π^*𝒜`,
by `Stacks.Algebraization.hasProperSupport_pullback_of_isProper`.

## Main results

* `Stacks.Algebraization.isProperOver_preimage_of_isProper` and
  `Stacks.Algebraization.hasProperSupport_pullback_of_isProper` — the inverse image along a proper
  morphism of a closed subset proper over the base is proper over the base, and the pullback of a
  module of finite type with support proper over the base has support proper over the base.
  Unconditional.
* `Stacks.Algebraization.exists_iso_of_bijective_completionFunctor_map` — completion reflects an
  isomorphism between two coherent modules from bijectivity on the morphisms between them, with no
  full faithfulness of the functor. Unconditional.
* `Stacks.Algebraization.exists_pullbackCompletionDescent_of_hasProperSupport` — **the descent of
  the source's `β` with `hff` deleted**, for an algebraization with support proper over the base.
* `exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_hasProperSupport` and
  `exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImageProperOver`
  — **Stacks 088B at a base ideal sheaf with the properness of the base morphism deleted and
  `hff` discharged.** One binder remains, the algebraization of `(𝓖_n)` with support proper over
  the base.
* `Stacks.Algebraization.IsDirectImageComparisonDefective` and
  `Stacks.Algebraization.essImage_of_isDirectImageComparison` — **the pre-repair form of
  `Stacks.Algebraization.IsDirectImageComparison`, restated locally, and its refutation**: that
  hypothesis implies that a coherent adic system whose pullback along *some* proper morphism is a
  completion is itself a completion, i.e. unrestricted Grothendieck existence. See the discussion
  below.

## What this is not: 088B at a general base, whose `hc` form is **false**

`Stacks.Algebraization.IsDirectImageComparison`
(`CompletionProper/ProperSupportAlgebraization.lean`) intends 088B at the source's own hypotheses
— an arbitrary Noetherian base `X`, an arbitrary quasi-coherent `𝓙 ⊆ 𝒪_X`, and **no**
algebraization binder. It is not proved here. It was at one point stated with one binder
weakened, and in that form it is **false**, by
`Stacks.Algebraization.essImage_of_isDirectImageComparison` below — which refutes
`Stacks.Algebraization.IsDirectImageComparisonDefective`, that pre-repair form restated in this
file so the refutation stays machine-checked, the live definition now carrying the repair.
The defect is in one binder.
The source assumes that `π` *is an isomorphism over* `X ∖ V(𝒦)`; the defective form replaces that
by the consequence

`hc : ∀ 𝒜, (𝓖 ≅ 𝒜 ^∧) → IsIso ((𝒜 ⟶ π_*π^*𝒜) |_{X ∖ V(𝒦)})`,

which is **vacuous as soon as `(𝓖_n)` has no algebraization at all** — and at a general base,
with no completeness anywhere, systems with no algebraization exist, which is exactly the
difficulty 088B is about. Read at `𝒦 = ⊤`, where `V(𝒦) = ∅` and annihilation by a power of `𝒦`
forces the levelwise kernels and cokernels to *vanish*, the defective form therefore asserts that
`π^*(𝓖_n)` being a completion forces `(𝓖_n)` to be one, for an arbitrary proper `π`. That is
unrestricted Grothendieck existence: taking for `π` the closed immersion of the subscheme cut out
by `𝓙` — along which `𝓙` pulls back to `⊥`, so that every pullback system is constant and hence
a completion — it makes *every* coherent adic system on *every* Noetherian scheme algebraizable,
which the counterexample of `CompletionCriteria/AffineExistenceDescent.lean` (a finite `B ^∧`-
module at the local ring of a node that is not the base change of a finite `B`-module) refutes.

The same substitution in `Stacks.Algebraization.IsProperDirectImageComparison`
(`CompletionProper/DevissageStep.lean`) is harmless, and that is why the defect appears only now:
there `X` is proper over a complete `A`, every object of `Coh(X, 𝓘)` is a completion by
Stacks 088C, and `hc` always has content. Deleting the properness of the base morphism destroys
precisely that, so a binder phrased this way cannot travel with the deletion. The repair is to
ask the source's hypothesis itself, `IsIso (π ∣_ 𝒦.support.compl)`, which implies `hc` by
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit` — the
implication the Chow step already uses — so no consumer loses anything; the live
`Stacks.Algebraization.IsDirectImageComparison` carries that repair, and only
`Stacks.Algebraization.IsDirectImageComparisonDefective` below keeps the `hc` form, to be refuted.

Even repaired, 088B at a general base is not reached here. Its remaining cost is the source's own
reduction, whose two steps are recorded in the module docstring of
`CompletionProper/GeneralBaseAlgebraization.lean`: the characterization of `α` makes the problem
local on the base (proved there, unconditionally,
`Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover`), and over an affine member
`U = Spec B` of the cover the algebraization comes from Stacks 087W only after `B` is replaced by
`B ^∧` by flat base change — the geometry of `(π ⁻¹ U) ×_{Spec B} Spec B ^∧` and the descent of
`α` along `B ⟶ B ^∧`, which this library does not carry. The restriction route of this file does
not help there either: a statement at an arbitrary Noetherian base mentions no ring `A` and no
morphism to an affine base, so neither "support proper over the base" nor Stacks 0883 is so much
as expressible in its binders.

No `stacks` attribute is attached here, following `CompletionProper/DevissageComparison.lean` and
`CompletionProper/ProperSupportAlgebraization.lean`: the statements below still carry a binder
beyond the source's hypotheses.

## References

* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
* [Stacks Project, Tag 0CYN](https://stacks.math.columbia.edu/tag/0CYN)
* [Stacks Project, Tag 0CYP](https://stacks.math.columbia.edu/tag/0CYP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### Proper support along a proper morphism -/

/-- **The inverse image of a closed subset proper over the base along a proper morphism is proper
over the base.** For `π : Y ⟶ X` proper, `f : X ⟶ S` locally of finite type and `Z ⊆ X` a closed
subset proper over `S`, the closed subset `π ⁻¹ Z` of `Y` is proper over `S`.

The closed subscheme structure witnessing it is the inverse image `π^{-1}𝒥 𝒪_Y` of the vanishing
ideal `𝒥` of `Z`, whose subscheme is the fibre product of `V(𝒥)` with `Y` over `X`
(`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`): the projection to `V(𝒥)` is a base change
of `π`, hence proper, and `V(𝒥) ⟶ S` is proper by hypothesis, so the composite is. That the
support of the inverse image ideal sheaf is `π ⁻¹ Z` is
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`, and the passage from one closed
subscheme structure on `π ⁻¹ Z` to the reduced one of [Stacks, Tag 0CYM] is
`AlgebraicGeometry.isProperOver_iff_exists_isProper`.

This is the companion of [Stacks, Tag 0CYP] for a proper morphism over a fixed base rather than
for a base change of that base. -/
@[ega "II 5.4.10" "more general", ega "III 5.3.5" "partial"]
public theorem isProperOver_preimage_of_isProper {Y X S : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (f : X ⟶ S) [LocallyOfFiniteType f] (Z : Closeds X) (hZ : IsProperOver f Z) :
    IsProperOver (π ≫ f) (Z.preimage π.continuous) := by
  let Iv := Scheme.IdealSheafData.vanishingIdeal Z
  let J := Iv.comap π
  let m : J.subscheme ⟶ Iv.subscheme := (Iv.comapIso π).hom ≫ pullback.snd π Iv.subschemeι
  have hcomap : IsPullback J.subschemeι m π Iv.subschemeι :=
    IsPullback.of_iso_pullback ⟨by simp [J, m]⟩ (Iv.comapIso π) (by simp [J]) rfl
  have : IsProper m := IsProper.isStableUnderBaseChange.of_isPullback hcomap inferInstance
  have : IsProper (Iv.subschemeι ≫ f) := hZ
  have hJproper : IsProper (J.subschemeι ≫ π ≫ f) := by
    rw [← Category.assoc, hcomap.w, Category.assoc]
    infer_instance
  refine (isProperOver_iff_exists_isProper (π ≫ f) (Z.preimage π.continuous)).2
    ⟨J, ?_, hJproper⟩
  rw [show J = Iv.comap π from rfl, Scheme.IdealSheafData.support_comap]
  exact Closeds.ext (by simpa using Scheme.IdealSheafData.coe_support_vanishingIdeal Z ▸ rfl)

/-- **The pullback along a proper morphism of a module with support proper over the base again has
support proper over the base.** The support of a pullback of a module of finite type is the
inverse image of the support ([Stacks, Tag 056J],
`Stacks.Modules.supp_pullback`), and the inverse image along a proper morphism of a closed subset
proper over the base is proper over the base. -/
public theorem hasProperSupport_pullback_of_isProper {Y X S : Scheme.{u}} (π : Y ⟶ X)
    [IsProper π] (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType]
    (hF : HasProperSupport f F) :
    HasProperSupport (π ≫ f) ((Scheme.Modules.pullback π).obj F) := by
  obtain ⟨Z, hZeq, hZproper⟩ := hF
  refine ⟨Z.preimage π.continuous, ?_, isProperOver_preimage_of_isProper π f Z hZproper⟩
  rw [Stacks.Modules.supp_pullback π F]
  show π ⁻¹' (Z : Set X) = _
  rw [hZeq]

/-! ### Reflecting an isomorphism from bijectivity at two objects -/

/-- **Completion reflects an isomorphism between two coherent modules as soon as it is bijective
on the morphisms between them.** No full faithfulness of the whole functor is used: the two
bijectivity statements at `(P, Q)` and `(Q, P)` produce the two morphisms, and injectivity at
`(P, P)` and `(Q, Q)` identifies their composites with the identities.

This is the hypothesis-minimal form of `Stacks.Coherent.pullbackCompletionDescent`, whose binder
`hff` is the full faithfulness of completion on the whole of `Coh(𝒪_X)`. For a scheme that is not
proper over the base that functor is not fully faithful, while the four bijectivities are
available at any pair of modules annihilated by the ideal sheaf of a closed subscheme proper over
the base, by `Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer`. -/
public theorem exists_iso_of_bijective_completionFunctor_map {X : Scheme.{u}}
    [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
    (P Q : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hPQ : Function.Bijective fun u : P ⟶ Q => ((completionFunctor X 𝓘).map u).hom)
    (hQP : Function.Bijective fun u : Q ⟶ P => ((completionFunctor X 𝓘).map u).hom)
    (hPP : Function.Injective fun u : P ⟶ P => ((completionFunctor X 𝓘).map u).hom)
    (hQQ : Function.Injective fun u : Q ⟶ Q => ((completionFunctor X 𝓘).map u).hom)
    (e : (completionFunctor X 𝓘).obj P ≅ (completionFunctor X 𝓘).obj Q) :
    Nonempty (P ≅ Q) := by
  obtain ⟨u, hu⟩ := hPQ.2 e.hom.hom
  obtain ⟨v, hv⟩ := hQP.2 e.inv.hom
  have hu' : (completionFunctor X 𝓘).map u = e.hom := ObjectProperty.hom_ext _ hu
  have hv' : (completionFunctor X 𝓘).map v = e.inv := ObjectProperty.hom_ext _ hv
  have hPP' : Function.Injective ((completionFunctor X 𝓘).map : (P ⟶ P) → _) :=
    fun _ _ hab => hPP (congrArg (fun k : (completionFunctor X 𝓘).obj P ⟶
      (completionFunctor X 𝓘).obj P => k.hom) hab)
  have hQQ' : Function.Injective ((completionFunctor X 𝓘).map : (Q ⟶ Q) → _) :=
    fun _ _ hab => hQQ (congrArg (fun k : (completionFunctor X 𝓘).obj Q ⟶
      (completionFunctor X 𝓘).obj Q => k.hom) hab)
  exact ⟨⟨u, v,
    hPP' (by rw [Functor.map_comp, hu', hv', e.hom_inv_id, CategoryTheory.Functor.map_id]),
    hQQ' (by rw [Functor.map_comp, hv', hu', e.inv_hom_id, CategoryTheory.Functor.map_id])⟩⟩

/-! ### Stacks 088B over a base morphism that is not proper -/

section Comparison

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Spec (.of A))
  [LocallyOfFiniteType f] (π : Y ⟶ X) [IsProper π]

/-- **The descent of the source's `β`, over a base morphism that is not proper.** Let `A` be a
Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be locally of finite type with
`X` Noetherian, set `𝓘 = I · 𝒪_X` and let `π : Y ⟶ X` be proper with `Y` Noetherian. Let `𝒜` be
a coherent `𝒪_X`-module and `𝓕` a coherent `𝒪_Y`-module, both with support proper over `A`.
Then the source's isomorphism

`β : π^*(𝒜 ^∧) ≅ 𝓕 ^∧`   in `Coh(Y, 𝓘 𝒪_Y)`

descends to an isomorphism `π^*𝒜 ≅ 𝓕` of coherent `𝒪_Y`-modules. **No properness of `f` and no
full faithfulness of completion on `Y`.**

`π^*𝒜` has support proper over `A` by
`Stacks.Algebraization.hasProperSupport_pullback_of_isProper`, so `π^*𝒜` and `𝓕` are annihilated
by the ideal sheaf of one closed subscheme of `Y` proper over `A`
(`Stacks.Algebraization.exists_isProper_annihilatedByKer_pair`), over which completion is
bijective on morphisms with no hypothesis
(`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer`, Stacks 0883 for a
proper morphism read through Stacks 087T). The isomorphism is then reflected by
`Stacks.Algebraization.exists_iso_of_bijective_completionFunctor_map`, applied to `β` composed
with the identification `(π^*𝒜) ^∧ ≅ π^*(𝒜 ^∧)` of
`Stacks.Coherent.completionPullbackIso`.

The proper support of `𝒜` is not removable: for `A = ℤ_p`, `I = (p)`, `X = 𝔸¹_{ℤ_p}`, `π = 𝟙`,
`𝒜 = 𝒪_X/(pt - 1) = ℚ_p` and `𝓕 = 0` one has `𝒜 ^∧ = 0`, so `β` exists, while `π^*𝒜 ≠ 0 = 𝓕`;
see the module docstring. -/
public theorem exists_pullbackCompletionDescent_of_hasProperSupport
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (h𝒜 : HasProperSupport f 𝒜.obj) (h𝓕 : HasProperSupport (π ≫ f) 𝓕.obj)
    (β : (coherentAdicPullback π (baseIdealSheaf A I f)).obj
        ((completionFunctor X (baseIdealSheaf A I f)).obj 𝒜) ≅
      (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj 𝓕) :
    Nonempty ((Scheme.Modules.pullback π).obj 𝒜.obj ≅ 𝓕.obj) := by
  have : 𝒜.obj.IsCoherent := 𝒜.property
  have : 𝓕.obj.IsCoherent := 𝓕.property
  have : 𝒜.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := 𝒜.obj)
  have : ((pullbackCoherentModules π).obj 𝒜).obj.IsCoherent :=
    ((pullbackCoherentModules π).obj 𝒜).property
  -- the pullback of the algebraization still has support proper over `A`
  -- one closed subscheme of `Y` proper over `A` carries both modules
  obtain ⟨J, hJ, hPa, hQa⟩ := exists_isProper_annihilatedByKer_pair (π ≫ f)
    ((pullbackCoherentModules π).obj 𝒜).obj 𝓕.obj
    (hasProperSupport_pullback_of_isProper π f 𝒜.obj h𝒜) h𝓕
  -- over it, completion is bijective on morphisms, with no hypothesis
  have hbij : ∀ R S : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
      Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι R.obj →
      Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι S.obj →
      Function.Bijective fun u : R ⟶ S =>
        ((completionFunctor Y ((baseIdealSheaf A I f).comap π)).map u).hom := by
    intro R S hR hS
    rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f π]
    exact bijective_completionFunctor_map_of_annihilatedByKer A I (π ≫ f) J hJ R S hR hS
  obtain ⟨b⟩ := exists_iso_of_bijective_completionFunctor_map
    ((baseIdealSheaf A I f).comap π) ((pullbackCoherentModules π).obj 𝒜) 𝓕
    (hbij _ _ hPa hQa) (hbij _ _ hQa hPa) (hbij _ _ hPa hPa).1 (hbij _ _ hQa hQa).1
    (completionPullbackIso π (baseIdealSheaf A I f) 𝒜 ≪≫ β)
  exact ⟨⟨b.hom.hom, b.inv.hom, ObjectProperty.isoHom_inv_id_hom b,
    ObjectProperty.isoInv_hom_id_hom b⟩⟩

/-- **Stacks 088B at a base ideal sheaf, with the properness of the base morphism deleted.** Let
`A` be a Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be locally of finite
type with `X` Noetherian, set `𝓘 = I · 𝒪_X`, let `π : Y ⟶ X` be proper with `Y` Noetherian and
let `𝒦 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. Let `𝓕` be a coherent `𝒪_Y`-module with
support proper over `A`, let `(𝓖_n)` be an object of `Coh(X, 𝓘)` algebraized by a coherent
`𝒪_X`-module `𝒜` with support proper over `A`, and let

`β : π^*(𝓖_n) ≅ 𝓕 ^∧`

be the source's isomorphism. If the adjunction map `𝒜 ⟶ π_*π^*𝒜` restricts to an isomorphism on
`X ∖ V(𝒦)` — the condition `hc` in which the source uses that `π` is an isomorphism there — then
there is a morphism

`α : (𝓖_n) ⟶ (π_*𝓕) ^∧`

whose levelwise kernels and cokernels are annihilated by a power of `𝒦`.

This is
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper`
with its hypothesis `[IsProper f]` **deleted**. Properness of `f` is used there only to discharge
the full-faithfulness binder `hff` of
`Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage`; here
that binder is discharged instead from the proper support of the two modules, by
`Stacks.Algebraization.exists_pullbackCompletionDescent_of_hasProperSupport`, and everything
after the descent is the library's existing unconditional route
`Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage`.

The deletion is what [Stacks, Tag 088E] needs: its `X` is separated, locally of finite type and
quasi-compact over `A` and not proper over `A`, so the `[IsProper f]` form cannot be instantiated
at the point where the dévissage of its `hSupp` applies 088B, whereas the systems there do carry
proper support. The one remaining binder is the algebraization `𝒜` of `(𝓖_n)` — the source's
reduction of 088B to an affine base, discussed in the module docstring. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_hasProperSupport
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (𝓖 : CoherentAdicSystems (baseIdealSheaf A I f))
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (e : 𝓖 ≅ (completionFunctor X (baseIdealSheaf A I f)).obj 𝒜)
    (h𝒜 : HasProperSupport f 𝒜.obj) (h𝓕 : HasProperSupport (π ≫ f) 𝓕.obj)
    (β : (coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓖 ≅
      (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj 𝓕)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) :
    ∃ α : 𝓖.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsKernelCokernelAnnihilatedByPower 𝒦 α := by
  obtain ⟨b⟩ := exists_pullbackCompletionDescent_of_hasProperSupport A I f π 𝒜 𝓕 h𝒜 h𝓕
    (((coherentAdicPullback π (baseIdealSheaf A I f)).mapIso e).symm ≪≫ β)
  exact exists_isKernelCokernelAnnihilatedByPower_properDirectImage π (baseIdealSheaf A I f) 𝒦
    𝒜 𝓕 b 𝓖 ((ObjectProperty.ι (IsCoherentAdicSystem (baseIdealSheaf A I f))).mapIso e) hc

/-- **Stacks 088B at a base ideal sheaf with the properness of the base morphism deleted, with the
algebraization as a single binder.** The same statement as
`exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_hasProperSupport` with the
algebraization `𝒜`, its iso `e` and its proper support packaged into one hypothesis `halg` and the
condition `hc` asked of every algebraization, which is the shape in which
`Stacks.Algebraization.IsProperDirectImageComparison` and
`Stacks.Algebraization.IsDirectImageComparison` state it.

`halg` is essential surjectivity of the completion functor of Stacks 088D — the functor
`Stacks.Algebraization.completionFunctorProperOver` between the categories of objects with
support proper over `A` — at the single system `(𝓖_n)`. It is the one binder left: no properness
of `f` and no full faithfulness anywhere. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImageProperOver
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (𝓖 : CoherentAdicSystems (baseIdealSheaf A I f))
    (halg : ∃ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      HasProperSupport f 𝒜.obj ∧
        Nonempty (𝓖 ≅ (completionFunctor X (baseIdealSheaf A I f)).obj 𝒜))
    (h𝓕 : HasProperSupport (π ≫ f) 𝓕.obj)
    (β : (coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓖 ≅
      (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj 𝓕)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      (𝓖 ≅ (completionFunctor X (baseIdealSheaf A I f)).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) :
    ∃ α : 𝓖.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsKernelCokernelAnnihilatedByPower 𝒦 α := by
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := halg
  exact exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_hasProperSupport A I f π
    𝒦 𝓕 𝓖 𝒜 e h𝒜 h𝓕 β (hc 𝒜 e)

end Comparison

/-! ### The pre-repair form of `IsDirectImageComparison` is false as stated -/

/-- **The pre-repair form of `Stacks.Algebraization.IsDirectImageComparison`.** This is that
definition verbatim except in its last binder, where the source's own hypothesis
`IsIso (π ∣_ 𝒦.support.compl)` is replaced by the consequence

`hc : ∀ 𝒜, (𝓖 ≅ 𝒜 ^∧) → IsIso ((𝒜 ⟶ π_*π^*𝒜) |_{X ∖ V(𝒦)})`,

which is vacuous whenever `(𝓖_n)` has no algebraization at all.

The live definition `Stacks.Algebraization.IsDirectImageComparison` has since been **repaired** and
asks the source's hypothesis; it is the one to use. The defective form is restated here solely so
that its refutation, `Stacks.Algebraization.essImage_of_isDirectImageComparison` below, stays
machine-checked — the defect is a fact about the `hc` phrasing, and the module docstring's account
of why that phrasing cannot travel with the deletion of properness of the base morphism is only
worth as much as a proof. Nothing in the library depends on it. -/
public def IsDirectImageComparisonDefective : Prop :=
  ∀ {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (π : Y ⟶ X) [IsProper π] (𝓙 𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (𝓖 : CoherentAdicSystems 𝓙),
    ((coherentAdicPullback π 𝓙).obj 𝓖 ≅ (completionFunctor Y (𝓙.comap π)).obj 𝓕) →
      (∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        (𝓖 ≅ (completionFunctor X 𝓙).obj 𝒜) →
          IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) →
        ∃ α : 𝓖.obj ⟶ ((completionFunctor X 𝓙).obj (properPushforwardCoherent π 𝓕)).obj,
          IsKernelCokernelAnnihilatedByPower 𝒦 α

/-- **The pre-repair form of `Stacks.Algebraization.IsDirectImageComparison` implies unrestricted
Grothendieck existence, and is therefore false.** Granted
`Stacks.Algebraization.IsDirectImageComparisonDefective`, let `X` be a Noetherian scheme,
`𝓙 ⊆ 𝒪_X` quasi-coherent, `(𝓖_n)` an object of `Coh(X, 𝓙)` and `π : Y ⟶ X` *any* proper morphism
with `Y` Noetherian along which `π^*(𝓖_n)` happens to be the completion of a coherent
`𝒪_Y`-module. Then `(𝓖_n)` is itself a completion — with no completeness of anything, and with
no hypothesis relating `π` to `(𝓖_n)` beyond `β`.

Nothing in the source licenses that. The lemma [Stacks, Tag 088B] assumes that `π` **is an
isomorphism** over `X ∖ V(𝒦)`; the defective form replaces that
hypothesis by its consequence `hc` at the algebraizations of `(𝓖_n)`, and `hc` is vacuously true
when `(𝓖_n)` has none — which at a general base is the normal state of affairs. The proof below
is then forced: take `𝒦 = ⊤`, so that `V(𝒦) = ∅` and `hc` asks for nothing; annihilation of the
levelwise kernels and cokernels by `⊤ ᵗ` makes them have empty support ([Stacks, Tag 01Y9],
`AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset`) hence vanish, so `α` is a
levelwise isomorphism and `(𝓖_n) ≅ (π_*𝓕) ^∧`.

The conclusion is absurd: applied to `π = 𝓙.subschemeι`, along which `𝓙` pulls back to `⊥`, so
that the pullback of any `𝓙`-adic system is a constant system and hence a completion, it
algebraizes every coherent adic system on every Noetherian scheme. That is refuted by
`CompletionCriteria/AffineExistenceDescent.lean`.

See the module docstring for where the defect comes from, why
`Stacks.Algebraization.IsProperDirectImageComparison` is unaffected, and the one-line repair —
which the live `Stacks.Algebraization.IsDirectImageComparison` now carries, so that what is
refuted below is the locally restated pre-repair form. -/
public theorem essImage_of_isDirectImageComparison (h : IsDirectImageComparisonDefective.{u})
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (π : Y ⟶ X) [IsProper π]
    (𝓙 : X.IdealSheafData) (𝓖 : CoherentAdicSystems 𝓙)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (β : (coherentAdicPullback π 𝓙).obj 𝓖 ≅ (completionFunctor Y (𝓙.comap π)).obj 𝓕) :
    (completionFunctor X 𝓙).essImage 𝓖 := by
  by_contra hE
  -- at `𝒦 = ⊤` the condition `hc` asks for nothing, there being no algebraization
  obtain ⟨α, t, ht, hkc⟩ := h π 𝓙 ⊤ 𝓕 𝓖 β (fun 𝒜 e => absurd ⟨𝒜, ⟨e.symm⟩⟩ hE)
  -- annihilation by a power of the unit ideal sheaf is vanishing
  have hzero : ∀ (M : X.Modules) [M.IsCoherent],
      idealPowerMultiple (⊤ : X.IdealSheafData) t M = ⊥ → IsZero M := by
    intro M _ hann
    have hsupp := (AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset
      M (⊤ : X.IdealSheafData)).1 ⟨t, hann⟩
    rw [Scheme.IdealSheafData.support_top] at hsupp
    exact Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty M
      (Set.subset_empty_iff.1 (by simpa using hsupp))
  have hiso : ∀ k : ℕ, IsIso (α.app (op k)) := by
    intro k
    have : _root_.SheafOfModules.IsCoherent.{u} (𝓖.obj.obj (op k)) := 𝓖.property.1 k
    have : _root_.SheafOfModules.IsCoherent.{u}
        (((completionFunctor X 𝓙).obj (properPushforwardCoherent π 𝓕)).obj.obj (op k)) :=
      ((completionFunctor X 𝓙).obj (properPushforwardCoherent π 𝓕)).property.1 k
    have := AlgebraicGeometry.isCoherent_kernel (α.app (op k))
    have := AlgebraicGeometry.isCoherent_cokernel (α.app (op k))
    have : Mono (α.app (op k)) := (Preadditive.mono_iff_isZero_kernel _).2 (hzero _ (hkc k).1)
    have : Epi (α.app (op k)) := Preadditive.epi_of_isZero_cokernel _ (hzero _ (hkc k).2)
    exact isIso_of_mono_of_epi _
  have : ∀ n : ℕᵒᵖ, IsIso (α.app n) := fun n => hiso n.unop
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact hE ⟨properPushforwardCoherent π 𝓕, ⟨(ObjectProperty.isoMk _ (asIso α)).symm⟩⟩

end Stacks.Algebraization

end
