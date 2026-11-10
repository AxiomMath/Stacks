module

public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Meromorphic.IdealTimesModule
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Exactness
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.NowhereDenseDrop
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact

/-!
# The difference sequences of Tag 0BEM, from the ideal of denominators

`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences` reduces
[Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) to two hypotheses: Tag 02O6, and
the source's first paragraph of geometry — for a coherent `𝒢` of positive-dimensional support
and each twisting direction `i`, two short exact sequences of coherent sheaves with a common
first term, `𝒢` in the middle of one and `𝒢 ⊗ 𝓛ᵢ` in the middle of the other, both third terms
of strictly smaller support dimension.

This file supplies that second hypothesis **for a coherent sheaf of full support without
embedded associated points**, out of [Stacks, Tag 02P2] and a regular meromorphic section of
`𝓛ᵢ`. For such a `𝒢` the two sequences are the two denominator injections of Tag 02P2 followed
by their cokernels,

  `0 ⟶ ℐ𝒢 ⟶ 𝒢 ⟶ 𝒬 ⟶ 0`,  `0 ⟶ ℐ𝒢 ⟶ 𝒢 ⊗ 𝓛ᵢ ⟶ 𝒬' ⟶ 0`,

whose common first term is literally the same object, so all three isomorphisms the hypothesis
asks for are `Iso.refl` and its deliberate up-to-isomorphism weakening is not used.

## Main results

* `AlgebraicGeometry.exists_differenceSequences_of_supp_eq_univ`: the two sequences, for a
  coherent sheaf of full support with no embedded associated points, from Tag 02P2 — with the
  nowhere density of the two third terms' supports as well as the support-dimension drops it
  implies, because the inductive step of Tag 0BEM carries its drops in the nowhere-dense form.

## Implementation notes

**What this does not do, and why.** The hypothesis of
`exists_eulerPolynomial_twistedSheaf_of_differenceSequences` quantifies over *every* coherent
`𝒢` with `natDimSupp 𝒢 ≠ 0`, and Tag 02P2 is available only for a sheaf of full support with no
embedded associated points. Those two restrictions are not slack in the formalization: Tag 02P2
needs them to produce its *second* map at all —
`AlgebraicGeometry.denominatorIdealTimesModuleMul` takes both as explicit arguments, because the
two kernels are killed by checking stalks at the associated points of the sheaf, and that
argument identifies those points with generic points of irreducible components of the *scheme*.

Nor can the restriction be lifted by restating the nowhere density relatively. The exceptional
subset of Tag 02P2 is nowhere dense **in the scheme**
(`AlgebraicGeometry.denominatorBadLocus_isNowhereDense`), and for a sheaf of full support that is
exactly what the dimension drop consumes
(`AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense_of_supp_eq_univ`); for a sheaf of
smaller support the drop instead needs nowhere density in `Supp 𝒢`, equivalently that no
irreducible component of `Supp 𝒢` lies inside the exceptional subset
(`AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_forall_irreducibleComponents`), and nothing in
Tag 02P2 supplies that: `Supp 𝒢` is itself typically nowhere dense in the scheme, so the
absolute statement is consistent with the exceptional subset swallowing `Supp 𝒢` whole.

So the step from here to the full hypothesis is the source's own second and third paragraphs, and
the two of them behave quite differently. **Both are proved**, and both at the level of the
weaker hypothesis of `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep`: see
`AlgebraicGeometry.isTwistDifferenceStep_hasNoEmbeddedAssociatedPoints` of
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/StepAssembly.lean`, which consumes this theorem.

*The scheme change.* Tag 02OM's
`AlgebraicGeometry.exists_isCoherent_pushforward_iso_of_hasNoEmbeddedAssociatedPoints` takes a
coherent sheaf with no embedded associated points to a coherent sheaf of **full support** on its
scheme-theoretic support, and the common first term survives being pushed forward: the two
sequences built there have the same `ℐ𝒢'` in position one, so their direct images do too, and the
middle of the second becomes `𝒢 ⊗ 𝓛ᵢ` by the projection formula for a closed immersion. Both
transports that needs are available: the projection formula is
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`, at the `X.Modules` spelling
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`, and the cohomological half of
[Stacks, Tag 089W] is `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion`,
with the two combined in
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion`. Clause (b) of
Tag 02OM — that the descended sheaf again has no embedded associated points, which that file states
is absent and blocked on [Stacks, Tag 05EY] — is not needed either, because Tag 02OL applied *on
the subscheme* produces a quotient with the same (full) support and no embedded associated points.
The identification of the twist of a direct image with the direct image of the twist — the
projection formula folded over the exponent vector — is available too, as
`AlgebraicGeometry.pushforwardTwistedSheafIso`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/PushforwardTwist.lean`), with its Euler-
characteristic consequence `...eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion`
and the invariance of the support, of `AlgebraicGeometry.natDimSupp` and of relative nowhere
density along the closed immersion in the same file.

The *two explicit arguments* below, `s` and `hs`, are supplied on that subscheme by
`AlgebraicGeometry.exists_isRegularMeromorphicSection_pullback_subscheme_annihilatorIdeal`, which
is [Stacks, Tag 02OZ] case (3) applied there — Tag 02OM's first conjunct is exactly
`HasNoEmbeddedPoints` of the subscheme — with `i^*𝓛` invertible by
`AlgebraicGeometry.SheafOfModules.isInvertible_pullback`.

*The removal of embedded associated points cannot be done here, and is carried out next door.* Tag
02OL replaces `𝒢` by a quotient `𝒢/𝒦` with `𝒦` nowhere-dense-supported, and the two sequences it
then yields have `𝒢/𝒦` in the middle, not `𝒢`. Pulling them back along `𝒢 ⟶ 𝒢/𝒦` restores the
middles but makes the two first terms an extension of `ℐ(𝒢/𝒦)` by `𝒦` and an extension of
`ℐ(𝒢/𝒦) ⊗ 𝓛ᵢ` by `𝒦 ⊗ 𝓛ᵢ`, which are not isomorphic, so the common-first-term binder fails — and
the up-to-isomorphism weakening does not help, since it still asks for an isomorphism. The source
does not have this problem because it discharges `𝒦` by its induction hypothesis instead, which is
a statement about Euler characteristics and not about sequences. Accordingly the weaker hypothesis
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_hstep`, which asks for no common first
term at all, is the right target, and the reduction is carried out there:
`AlgebraicGeometry.isTwistDifferenceStep_of_hasNoEmbeddedAssociatedPoints`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/EmbeddedPointStep.lean`) supplies the inductive
step for an arbitrary coherent sheaf from the step for sheaves with no embedded associated points,
merging the four Euler characteristics into two with a biproduct.

**No attribute for Tag 0BEM or Tag 02P2 is attached.** Nothing here states a clause of either:
Tag 0BEM's statement is unconditional, and the statement below is a hypothesis of a reduction of
it, carrying hypotheses on `𝒢` that Tag 02P2's own clauses do not mention in this arrangement.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules.Invertible (tensorProduct)

universe u

namespace AlgebraicGeometry

/-- `Stacks.SheafOfModules.Invertible.tensorProduct` at the declared type `X.Modules`. The
unascribed term has declared type `SheafOfModules
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf _)`,
which is definitionally but not syntactically `X.Modules`, and instance search is syntactic;
compare `AlgebraicGeometry.tensorModules` and the `tensorMod` of
`StacksDraft.AlgebraicGeometry.F3b.Meromorphic.IdealTimesModule`. -/
private noncomputable abbrev tensorModulesDecl (X : Scheme.{u}) (F L : X.Modules) : X.Modules :=
  tensorProduct X.sheaf.obj X.ringCatSheaf.property F L

/-- **The two difference short exact sequences of [Stacks, Tag 0BEM], for a coherent sheaf of
full support with no embedded associated points.** This is the second hypothesis of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences`, supplied at such
a `𝒢` from the two denominator injections of [Stacks, Tag 02P2] and their cokernels.

Both sequences are a monomorphism followed by its cokernel, hence short exact; the six terms are
coherent by [Stacks, Tag 01Y1], the product `ℐ𝒢` as a quasi-coherent submodule of `𝒢` and the
two cokernels as quasi-coherent quotients; the two first terms are the *same* object, so the
three isomorphisms are `Iso.refl`; and the two support-dimension drops are Tag 02P2's nowhere
dense exceptional subset together with
`AlgebraicGeometry.natDimSupp_lt_natDimSupp_of_isNowhereDense_of_supp_eq_univ`.

**The nowhere density is returned as well as the drops it implies.** Tag 02P2 supplies the
*nowhere density* of the exceptional subset and the strict drop of
`AlgebraicGeometry.natDimSupp` is a consequence of it; the inductive step of [Stacks, Tag 0BEM]
(`AlgebraicGeometry.IsTwistDifferenceStep`) carries its drops in the nowhere-dense form, because
that is the form stable under the finite unions its biproduct merge takes, so a statement
returning only the strict drops cannot feed it. Nowhere density here is nowhere density **in the
scheme**, which for a sheaf of full support is the relative nowhere density the step asks for. -/
private theorem exists_differenceSequences_core (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : _root_.SheafOfModules.{u} X.ringCatSheaf)
    (hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L)
    (G : _root_.SheafOfModules.{u} X.ringCatSheaf) (hG : SheafOfModules.IsCoherent G)
    (hG0 : natDimSupp G ≠ 0)
    (hemb : HasNoEmbeddedAssociatedPoints G)
    (hsupp : SheafOfModules.supp G = Set.univ)
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s) :
    ∃ S T : ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf),
      S.ShortExact ∧ T.ShortExact ∧
      SheafOfModules.IsCoherent S.X₁ ∧ SheafOfModules.IsCoherent S.X₂ ∧
        SheafOfModules.IsCoherent S.X₃ ∧
      SheafOfModules.IsCoherent T.X₁ ∧ SheafOfModules.IsCoherent T.X₂ ∧
        SheafOfModules.IsCoherent T.X₃ ∧
      Nonempty (S.X₂ ≅ G) ∧
      Nonempty (T.X₂ ≅ tensorProduct X.sheaf.obj X.ringCatSheaf.property G L) ∧
      Nonempty (S.X₁ ≅ T.X₁) ∧
      IsNowhereDense (SheafOfModules.supp S.X₃) ∧
      IsNowhereDense (SheafOfModules.supp T.X₃) ∧
      natDimSupp S.X₃ < natDimSupp G ∧ natDimSupp T.X₃ < natDimSupp G := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hsupp' : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp = Set.univ := hsupp
  -- quasi-coherence of the three sheaves the product is built from
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hLinv
  have hLcoh : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  have hq : ∀ N : _root_.SheafOfModules.{u} X.ringCatSheaf, N.IsCoherent → N.IsQuasicoherent :=
    fun N hN => (((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X N).out 1 2 rfl
      rfl).mp hN).1
  have hGq : G.IsQuasicoherent := hq G hG
  have hIq : (denominatorIdeal X L s).IsQuasicoherent :=
    denominatorIdeal_isQuasicoherent X L s hLinv
  have htq : (tensorModulesDecl X (denominatorIdeal X L s) G).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ _ hIq hGq
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hLinv
  have hGLcoh : (tensorModulesDecl X G L).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X G L
  -- the product `ℐ𝒢`, as the image of the action, is a quasi-coherent submodule of `𝒢`
  have hPq : (denominatorIdealTimesModule X L G s).IsQuasicoherent := by
    have hcoker : (cokernel (denominatorIdealAction X L G s)).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
        (M := tensorModulesDecl X (denominatorIdeal X L s) G) (N := G)
        (denominatorIdealAction X L G s)
    change (kernel (cokernel.π (denominatorIdealAction X L G s))).IsQuasicoherent
    exact @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel X G _
      (cokernel.π (denominatorIdealAction X L G s)) inferInstance hcoker
  have hιmono : Mono (denominatorIdealTimesModuleι X L G s) :=
    denominatorIdealTimesModuleι_mono X L G s
  have hPcoh : (denominatorIdealTimesModule X L G s).IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _ G
      (denominatorIdealTimesModule X L G s) hG hPq
      (denominatorIdealTimesModuleι X L G s) hιmono
  have hμmono : Mono (denominatorIdealTimesModuleMul X L G s hLinv hs hemb hsupp').val :=
    denominatorIdealTimesModuleMul_mono X L G s hLinv hs hemb hsupp'
  -- the cokernel of a map from `ℐ𝒢` to a coherent sheaf is coherent
  have hcok : ∀ {N : _root_.SheafOfModules.{u} X.ringCatSheaf}
      (g : denominatorIdealTimesModule X L G s ⟶ N), N.IsCoherent → (cokernel g).IsCoherent := by
    intro N g hN
    have hNq := hq N hN
    exact @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi X _ N _ hN
      (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
        (M := denominatorIdealTimesModule X L G s) (N := N) g)
      (cokernel.π g) coequalizer.π_epi
  have hCιcoh := hcok (denominatorIdealTimesModuleι X L G s) hG
  have hCμcoh := hcok (denominatorIdealTimesModuleMul X L G s hLinv hs hemb hsupp').val hGLcoh
  -- the exceptional subset of Tag 02P2, nowhere dense in the scheme, contains both third terms
  have hndι : IsNowhereDense
      (SheafOfModules.supp (cokernel (denominatorIdealTimesModuleι X L G s))) :=
    IsNowhereDense.mono (denominatorIdealTimesModuleι_cokernel_support X L G s)
      (denominatorBadLocus_isNowhereDense X L s hLinv hs)
  have hndμ : IsNowhereDense (SheafOfModules.supp (cokernel
      (denominatorIdealTimesModuleMul X L G s hLinv hs hemb hsupp').val)) :=
    IsNowhereDense.mono
      (denominatorIdealTimesModuleMul_cokernel_supp X L G s hLinv hs hemb hsupp')
      (denominatorBadLocus_isNowhereDense X L s hLinv hs)
  exact ⟨ShortComplex.mk (denominatorIdealTimesModuleι X L G s)
      (cokernel.π (denominatorIdealTimesModuleι X L G s)) (cokernel.condition _),
    ShortComplex.mk (denominatorIdealTimesModuleMul X L G s hLinv hs hemb hsupp').val
      (cokernel.π (denominatorIdealTimesModuleMul X L G s hLinv hs hemb hsupp').val)
      (cokernel.condition _),
    ShortComplex.shortExact_mk_cokernel_π _, ShortComplex.shortExact_mk_cokernel_π _,
    hPcoh, hG, hCιcoh, hPcoh, hGLcoh, hCμcoh,
    ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, hndι, hndμ,
    natDimSupp_lt_natDimSupp_of_isNowhereDense_of_supp_eq_univ k f G _ hCιcoh hsupp hndι hG0,
    natDimSupp_lt_natDimSupp_of_isNowhereDense_of_supp_eq_univ k f G _ hCμcoh hsupp hndμ hG0⟩

/-- **The two difference short exact sequences of [Stacks, Tag 0BEM]**, in the exact shape the
`hseq` hypothesis of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_differenceSequences` asks for. See
`exists_differenceSequences_core` for the content; this is the same statement at the `X.Modules`
spelling of the category and the `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling
  of the tensor product, both of
which are definitionally but not syntactically the ones [Stacks, Tag 02P2] is stated at. -/
theorem exists_differenceSequences_of_supp_eq_univ (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (G : X.Modules) (hG : SheafOfModules.IsCoherent G) (hG0 : natDimSupp G ≠ 0)
    (hemb : HasNoEmbeddedAssociatedPoints G)
    (hsupp : SheafOfModules.supp G = Set.univ)
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s) :
    ∃ S T : ShortComplex X.Modules,
      S.ShortExact ∧ T.ShortExact ∧
      SheafOfModules.IsCoherent S.X₁ ∧ SheafOfModules.IsCoherent S.X₂ ∧
        SheafOfModules.IsCoherent S.X₃ ∧
      SheafOfModules.IsCoherent T.X₁ ∧ SheafOfModules.IsCoherent T.X₂ ∧
        SheafOfModules.IsCoherent T.X₃ ∧
      Nonempty (S.X₂ ≅ G) ∧
      Nonempty (T.X₂ ≅ ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.2)⟩).obj (G)).obj (L)) : X.Modules)) ∧
      Nonempty (S.X₁ ≅ T.X₁) ∧
      IsNowhereDense (SheafOfModules.supp S.X₃) ∧
      IsNowhereDense (SheafOfModules.supp T.X₃) ∧
      natDimSupp S.X₃ < natDimSupp G ∧ natDimSupp T.X₃ < natDimSupp G :=
  exists_differenceSequences_core k f L
    (inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 L)) G hG hG0 hemb hsupp s hs

end AlgebraicGeometry

end
