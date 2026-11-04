module

public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic

/-!
# Stacks Tag 0C4K: relative ampleness of `L ⊗ f^* M ^⊗ a` along a composition

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, `L` an invertible `𝒪_X`-module and `M`
an invertible `𝒪_Y`-module. Stacks Tag 0C4K says that if `S` is quasi-compact, `L` is ample
relative to `f` and `M` is ample relative to `g`, then `L ⊗ f^* M ^⊗ a` is ample relative to
`g ∘ f` for all `a` beyond a single threshold.

Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple`, [Stacks, Tag 01VH], and the module
`L ⊗ f^* M ^⊗ a` is `Stacks.AmplePullbackPart1.tensorPullbackPowModule`.

## Main definitions

* `Stacks.RelativeAmpleCompositionThreshold.RelativeEventualAffineDatum`: **[Stacks, Tag 01PW] in
  the form this cluster consumes it**, over each affine open of the base. For every affine open
  `U ⊆ S` it asks for `Stacks.AmplePullbackPart1.EventualAffineDatum` for the restricted data
  `f|_{g⁻¹U}`, `L|_{(g ∘ f)⁻¹U}` and `M|_{g⁻¹U}` — the pointwise datum that part (1) of
  [Stacks, Tag 0892] is equivalent to, which is unproved in this repository. It is carried as a
  hypothesis rather than assumed silently.

## Main results

* `Stacks.RelativeAmpleCompositionThreshold.restrictTensorPullbackPowIso`: **the comparison
  `(L ⊗ f^* M ^⊗ a)|_{(g ∘ f)⁻¹U} ≅ L|_{(g ∘ f)⁻¹U} ⊗ (f|_{g⁻¹U})^* (M|_{g⁻¹U}) ^⊗ a`** for an
  open `U` of `S`. `../RelativeAmpleComposition/Basic.lean` records this as "the one piece of this
  cluster that is neither proved nor reduced here"; it is proved here, from pseudofunctoriality of
  the module pullback and [Stacks, Tag 01CD].
* `Stacks.RelativeAmpleCompositionThreshold.exists_threshold_isAmple_preimage`: over a single
  affine open `U` of `S`, a threshold beyond which the restriction of `L ⊗ f^* M ^⊗ a` to
  `(g ∘ f)⁻¹U` is ample.
* `Stacks.RelativeAmpleCompositionThreshold.exists_threshold_isRelativelyAmple_comp`:
  **Stacks Tag 0C4K over an arbitrary quasi-compact base**, on the single premise
  `RelativeEventualAffineDatum`.

## The route

`../RelativeAmpleComposition/Basic.lean` proves Tag 0C4K **over an affine base** on the premise
`Stacks.AmplePullbackPart1.EventualAffineDatum` and lists, under "What is not done", the two
things a general base needs on top of that:

> Over a general base Tag 0C4K needs, in addition, `RelativeAmpleLocalOnBase` **and** the
> compatibility of the tensor product and the pullback with restriction of the base to an open,
> which is not stated here: the restriction of `L ⊗ f^* M ^⊗ a` to `(g ∘ f)⁻¹V` has to be
> identified with `L| ⊗ (f|)^* (M|) ^⊗ a`, a Beck–Chevalley comparison for the open-immersion
> square. That is the one piece of this cluster that is neither proved nor reduced here.

Both are supplied. The first is now a theorem,
`Stacks.RelativeAmpleLocalOnBase.relativeAmpleLocalOnBase`
([Stacks, Tag 01VJ], clause (3) implies clause (1)). The second is
`Stacks.RelativeAmpleCompositionThreshold.restrictTensorPullbackPowIso`, and it needs no
Beck–Chevalley square: writing `V = g⁻¹U` and `W = f⁻¹V = (g ∘ f)⁻¹U`, the two composites
`W ⟶ X ⟶ Y` and `W ⟶ V ⟶ Y` are **equal** — that is
`AlgebraicGeometry.morphismRestrict_ι` for `f` and `V` — so pseudofunctoriality of the module
pullback (`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`, transported along the equality
by `Stacks.RelativeAmpleBaseChange.pullbackModuleCongr`) identifies `W.ι^* f^* (M ^⊗ a)` with
`(f|_V)^* V.ι^* (M ^⊗ a)`. [Stacks, Tag 01CD] in the two forms
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso` and
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` moves the restriction across the tensor
product and across the power of `M`.

With the comparison in hand, over an affine open `U ⊆ S` the restriction of `L ⊗ f^* M ^⊗ a` to
`(g ∘ f)⁻¹U` is ample for `a` large by `Stacks.AmplePullbackPart1.exists_threshold_isAmple`
applied to the restricted data, whose two hypotheses are quasi-compactness of `(g ∘ f)⁻¹U` — from
quasi-compactness of `f` and `g`, which relative ampleness supplies — and the datum.
Quasi-compactness of `S` then cuts the affine opens of `S` down to a finite subfamily, so the
maximum of their thresholds is a single threshold, and base-locality turns the resulting finite
affine covering into relative ampleness over every affine open of `S`.

## Implementation notes

**`(g ∘ f)⁻¹U = f⁻¹(g⁻¹U)` holds on the nose**, so the two descriptions of `W` are the same open
and no transport is needed between them. They are not interchangeable for *instance search*,
though: the domain of `f|_{g⁻¹U}` is `f⁻¹(g⁻¹U)` on the nose and
`Stacks.Ample.IsInvertibleModule` does not unify the two spellings of the scheme. So everything
about the restricted data — the comparison isomorphism, the datum and the single-open threshold —
is written with `f ⁻¹ᵁ (g ⁻¹ᵁ U)`, and only the final statement uses `(f ≫ g) ⁻¹ᵁ U`, which is the
spelling `Stacks.RelativeAmple.IsRelativelyAmple` for `f ≫ g` consumes.

**The hypotheses `hL` and `hM` of the source are kept, and enter through quasi-compactness.** The
ampleness content of the tag sits in `RelativeEventualAffineDatum`, exactly as it does over an
affine base in
`Stacks.RelativeAmpleComposition.exists_threshold_isRelativelyAmple_comp_of_isAffine`,
whose own module documentation records that this introduces "no new premise" because the datum is
the residue of part (1) of [Stacks, Tag 0892] already named in the tree. Neither `hL` nor `hM` is
dropped.

## What is not done

The premise `RelativeEventualAffineDatum` is not discharged: it is the module-valued form of
[Stacks, Tag 01PW] that `../AmplePullbackPart1/Basic.lean` isolates and
that is unproved, and no declaration in this repository carries
[Stacks, Tag 01PW] in that form. The attribute below is keyed to say so.

## References

* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [EGA II, Proposition 4.6.13 (i)]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AmplePullbackPart1 (tensorPullbackPowModule EventualAffineDatum)
open Stacks.RelativeAmpleBaseChange (pullbackModuleCompIso pullbackModuleCongr)
open Stacks.RelativeVeryAmple (pullbackTensorModulesIso tensorModulesMapIso
  pullbackTensorPowModuleIso)

universe u

namespace Stacks.RelativeAmpleCompositionThreshold

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (L : X.Modules) (M : Y.Modules)
  [IsInvertibleModule X L] [IsInvertibleModule Y M]

/-! ### Restriction of `L ⊗ f^* M ^⊗ a` to the preimage of an open of the base -/

/-- **The restriction of `L ⊗ f^* M ^⊗ a` to `(g ∘ f)⁻¹U` is `L| ⊗ (f|)^* (M|) ^⊗ a`.**

Write `V = g⁻¹U` and `W = f⁻¹V = (g ∘ f)⁻¹U`. The tensor product is moved across the restriction
`W.ι^*` by [Stacks, Tag 01CD] (`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`); on the second
factor, `W.ι ≫ f = (f|_V) ≫ V.ι` by `AlgebraicGeometry.morphismRestrict_ι`, so pullback
pseudofunctoriality turns `W.ι^* f^* (M ^⊗ a)` into `(f|_V)^* V.ι^* (M ^⊗ a)`, and Tag 01CD again
(`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`) rewrites `V.ι^* (M ^⊗ a)` as
`(V.ι^* M) ^⊗ a`.

`../RelativeAmpleComposition/Basic.lean` names this comparison as the one piece of the cluster it
neither proves nor reduces. No Beck–Chevalley square is involved: the two routes `W ⟶ Y` are
equal morphisms, not merely isomorphic. -/
def restrictTensorPullbackPowIso (U : S.Opens) (a : ℕ) :
    pullbackModule (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι (tensorPullbackPowModule f L M a) ≅
      tensorPullbackPowModule (f ∣_ (g ⁻¹ᵁ U))
        (pullbackModule (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι L) (pullbackModule (g ⁻¹ᵁ U).ι M) a :=
  pullbackTensorModulesIso (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι L
      (pullbackModule f (tensorPowModule Y M (a : ℤ))) ≪≫
    tensorModulesMapIso (f ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme (Iso.refl _)
      ((pullbackModuleCompIso (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι f _).symm ≪≫
        pullbackModuleCongr (morphismRestrict_ι f (g ⁻¹ᵁ U)).symm _ ≪≫
        pullbackModuleCompIso (f ∣_ (g ⁻¹ᵁ U)) (g ⁻¹ᵁ U).ι _ ≪≫
        (modulePullback (f ∣_ (g ⁻¹ᵁ U)).toLRSHom.toShHom).mapIso
          (pullbackTensorPowModuleIso (g ⁻¹ᵁ U).ι M a))

/-! ### Stacks Tag 01PW, in the form this cluster consumes it -/

/-- **[Stacks, Tag 01PW] over each affine open of the base**, as the pointwise datum that part (1)
of [Stacks, Tag 0892] is equivalent to.

For every affine open `U ⊆ S` this asks for `Stacks.AmplePullbackPart1.EventualAffineDatum` for the
restricted data `f|_{g⁻¹U} : (g ∘ f)⁻¹U ⟶ g⁻¹U`, `L|_{(g ∘ f)⁻¹U}` and `M|_{g⁻¹U}`: through every
point of `(g ∘ f)⁻¹U` there are a threshold `e` and an affine open `V`, independent of `a`, such
that for every `a ≥ e` some positive tensor power of the split module
`L| ^⊗ k ⊗ ((f|)^* M|) ^⊗ (a k)` carries a global section whose nonvanishing open is exactly `V`.

`Stacks.AmplePullbackPart1.EventualAffineDatum` is unproved in this repository —
`../AmplePullbackPart1/Basic.lean` isolates it as the single residue of part (1) of Tag 0892 and
the module-valued form of Tag 01PW — so it is carried here rather than assumed silently. Over an
affine base `U = ⊤` is the only affine open that matters and this is that file's premise
verbatim. -/
def RelativeEventualAffineDatum {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (L : X.Modules)
    (M : Y.Modules) [IsInvertibleModule X L] [IsInvertibleModule Y M] : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    EventualAffineDatum (f ∣_ (g ⁻¹ᵁ U)) (pullbackModule (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι L)
      (pullbackModule (g ⁻¹ᵁ U).ι M)

/-! ### The threshold over one affine open of the base -/

/-- **A threshold over a single affine open of the base.** For `U ⊆ S` affine whose preimage
`(g ∘ f)⁻¹U` is quasi-compact, and given the datum of [Stacks, Tag 01PW] there, the restriction of
`L ⊗ f^* M ^⊗ a` to `(g ∘ f)⁻¹U` is ample for every `a` beyond a threshold.

`Stacks.AmplePullbackPart1.exists_threshold_isAmple` is the statement for the restricted data, and
`Stacks.RelativeAmpleCompositionThreshold.restrictTensorPullbackPowIso` together with
`Stacks.RelativeVeryAmple.isAmple_congr` transports it onto the restriction of
`L ⊗ f^* M ^⊗ a` itself. -/
theorem exists_threshold_isAmple_preimage (U : S.Opens)
    (hdat : EventualAffineDatum (f ∣_ (g ⁻¹ᵁ U)) (pullbackModule (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι L)
      (pullbackModule (g ⁻¹ᵁ U).ι M))
    (hW : CompactSpace (f ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a → IsAmple (f ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme
      (pullbackModule (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι (tensorPullbackPowModule f L M a)) := by
  obtain ⟨n, hn⟩ := Stacks.AmplePullbackPart1.exists_threshold_isAmple (f ∣_ (g ⁻¹ᵁ U))
    (pullbackModule (f ⁻¹ᵁ (g ⁻¹ᵁ U)).ι L) (pullbackModule (g ⁻¹ᵁ U).ι M) hW hdat
  exact ⟨n, fun a ha => (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (restrictTensorPullbackPowIso f g L M U a)).mpr (hn a ha)⟩

/-! ### Stacks Tag 0C4K over a quasi-compact base -/

/-- **Stacks Tag 0C4K**, on the single premise
`Stacks.RelativeAmpleCompositionThreshold.RelativeEventualAffineDatum` — [Stacks, Tag 01PW] over
each affine open of the base.

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, `L` an invertible `𝒪_X`-module and `M` an
invertible `𝒪_Y`-module. If `S` is quasi-compact, `L` is ample relative to `f` and `M` is ample
relative to `g`, then there is a threshold `n` with `L ⊗ f^* M ^⊗ a` ample relative to `g ∘ f` for
every `a ≥ n`.

Relative ampleness of `L` and of `M` supplies quasi-compactness of `f` and of `g`, hence of the
composite, so the preimage of an affine open of `S` is quasi-compact and
`Stacks.RelativeAmpleCompositionThreshold.exists_threshold_isAmple_preimage` applies over each of
them. Quasi-compactness of `S` extracts a finite subfamily of the affine opens so chosen, and the
maximum of their thresholds serves for all of them at once; beyond it the finite family is an
affine open covering of `S` on whose preimages the restriction is ample, which
`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple` — [Stacks, Tag 01VJ],
clause (3) implies clause (1) — upgrades to relative ampleness over every affine open of `S`. -/
@[stacks 0C4K "on Tag 01PW as EventualAffineDatum over each affine open of the base"]
theorem exists_threshold_isRelativelyAmple_comp [CompactSpace S]
    (hdat : RelativeEventualAffineDatum f g L M)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a → Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g)
      (tensorPullbackPowModule f L M a) := by
  classical
  have hf : QuasiCompact f := hL.1
  have hg : QuasiCompact g := hM.1
  have hfg : QuasiCompact (f ≫ g) := inferInstance
  have key : ∀ x : S, ∃ (U : S.Opens) (n : ℕ), IsAffineOpen U ∧ x ∈ U ∧ ∀ a : ℕ, n ≤ a →
      IsAmple ((f ≫ g) ⁻¹ᵁ U).toScheme
        (pullbackModule ((f ≫ g) ⁻¹ᵁ U).ι (tensorPullbackPowModule f L M a)) := by
    intro x
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨n, hn⟩ := exists_threshold_isAmple_preimage f g L M U (hdat U hU)
      (Stacks.RelativeAmpleComposition.compactSpace_preimage_of_isCompact (f ≫ g) U hU.isCompact)
    exact ⟨U, n, hU, hxU, hn⟩
  choose U n hUaff hmem hample using key
  have hcover : (Set.univ : Set S) ⊆ ⋃ x : S, (U x : Set S) := fun y _ =>
    Set.mem_iUnion.mpr ⟨y, hmem y⟩
  obtain ⟨T, hT⟩ := (isCompact_univ (X := S)).elim_finite_subcover
    (fun x : S => (U x : Set S)) (fun x => (U x).isOpen) hcover
  refine ⟨T.sup n, fun a ha => ?_⟩
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple (f ≫ g)
    (tensorPullbackPowModule f L M a) hfg fun y => ?_
  obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ y))
  exact ⟨U x, hUaff x, hyx, hample x a ((Finset.le_sup hxT).trans ha)⟩

end Stacks.RelativeAmpleCompositionThreshold

end
