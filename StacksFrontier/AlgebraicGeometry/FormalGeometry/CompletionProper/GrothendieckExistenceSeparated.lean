module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedImmersionAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AnnihilatedCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticSupport.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Devissage

/-!
# Grothendieck's existence theorem with proper support

**Stacks 088E.** Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `X` be
a separated scheme of finite type over `A`. Then the functor of Stacks 088D

  `Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, 𝓘)`,  `𝓘 = I · 𝒪_X`,

is an equivalence.

This file proves the **first paragraph** of the source's proof: the reduction of 088E to Stacks
088C on the closed subschemes of `X` proper over `A`. The source puts it like this. For a closed
subscheme `Z ⊆ X` proper over `A` call a coherent module *supported on `Z`* when the ideal sheaf
of `Z` annihilates it, or equivalently when it is the direct image of a coherent module on `Z`
(Stacks 087T); by Stacks 088C the theorem is true for the functor between the modules and the
systems supported on `Z`; hence it suffices that every object of either category be supported on
*some* closed subscheme of `X` proper over `A`.

On the module side that is a theorem of this library, not a hypothesis: the scheme-theoretic
support of a coherent module is such a subscheme, by [Stacks, Tag 0CYS]. On the side of the
coherent adic systems it is the hypothesis `hSupp` below — the part of the source's proof that
runs Chow's lemma (Stacks 0200), the projective case (Stacks 0885) and Stacks 088B, none of which
this library carries in the form that argument needs.

**Full faithfulness is unconditional.** Two coherent modules with support proper over `A` are
both supported on one closed subscheme proper over `A` — the union of their scheme-theoretic
supports, a finite union of closed subsets proper over the base being proper over the base
([Stacks, Tag 0CYR]) — and over that subscheme completion is fully faithful with no hypothesis,
by Stacks 0883 for a proper morphism. So the only hypotheses the tagged statement carries are
`hSupp` and `hDev`, the inductive step of the Noetherian induction of Stacks 088C, the latter
asked on every closed subscheme of `X` proper over `A`.

## Main results

* `Stacks.Algebraization.exists_isProper_annihilatedByKer_of_hasProperSupport` and
  `Stacks.Algebraization.hasProperSupport_of_annihilatedByKer` — the two directions of
  "has support proper over the base" versus "is annihilated by the ideal sheaf of a closed
  subscheme proper over the base", for a coherent module. Unconditional.
* `Stacks.Algebraization.exists_isProper_annihilatedByKer_pair` — two such modules are
  annihilated by the ideal sheaf of *one* closed subscheme proper over the base. Unconditional.
* `Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer` — **full
  faithfulness**, between coherent modules annihilated by the ideal sheaf of a closed subscheme
  proper over the base. Unconditional.
* `Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_properSubschemes` — the
  reduction: Stacks 088E from Stacks 088C on the proper closed subschemes, together with
  `hSupp`.
* `Stacks.Algebraization.isEquivalence_completionFunctorProperOver` — **Stacks 088E** at the
  source's hypotheses, from `hDev` and `hSupp`.

## Implementation notes

The closed subscheme carrying a coherent module is `AlgebraicGeometry.annihilatorIdeal`, whose
support is the support of the module
(`AlgebraicGeometry.supp_eq_support_annihilatorIdeal`) and whose ideal annihilates it
(`AlgebraicGeometry.annihilatorIdeal_smul_eq_zero`); properness of the subscheme then follows
because properness of a closed subset does not depend on the closed subscheme structure put on
it, [Stacks, Tag 0CYL]. For a pair of modules the subscheme is cut out by the *product* of the
two ideal sheaves, whose support is the union of the two supports
(`AlgebraicGeometry.Scheme.IdealSheafData.support_mul`) and which is contained in each of them.

Full faithfulness is the square

```
Hom(F_Z, G_Z)               --completion on Z-->  Hom(F_Z ^∧, G_Z ^∧)
   |  i_*                                            |  i_* and the comparison
Hom(i_* F_Z, i_* G_Z)       --completion on X-->  Hom((i_* F_Z) ^∧, (i_* G_Z) ^∧)
```

three of whose edges are bijective — the top by Stacks 0883 for the proper morphism `Z ⟶ Spec A`,
the left by Stacks 08KS and the right because termwise direct image is bijective on morphisms of
inverse systems (`Stacks.Coherent.bijective_whiskerRight_pushforward`) and the comparison of the
two completions (`Stacks.Algebraization.pushforwardCompletionIso`) is an isomorphism; the square
commutes by `Stacks.Algebraization.pushforwardCompletionIso_naturality`. It is the square of
`Stacks.Coherent.bijective_completion_map_pushforward`, which assumes the completion functor on
`Z` to be an *equivalence*; here only its full faithfulness is used, and that is available with
no hypothesis, which is why the statement below carries none. The passage from the pair of
direct images to an arbitrary pair isomorphic to them is
`Stacks.Coherent.bijective_completion_map_of_iso`, and the square is closed by
`Stacks.Coherent.bijective_iff_of_commSquare`.

Essential surjectivity is `Stacks.Coherent.exists_coherent_completion_iso_of_annihilated` at
exponent one: annihilation by the ideal sheaf of the subscheme of `J` is annihilation by `J` in
the sense of `Stacks.Algebraization.idealPowerMultiple` at exponent one, which is
`Stacks.Algebraization.annihilatedByKer_subschemeι_iff_idealPowerMultiple_one`, and
`Stacks.Algebraization.IsSystemAnnihilatedBy` is that condition on every term of a system — the
family `Ξ` of the proof of Stacks 088C.

`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap` identifies `𝓘 𝒪_Z` with `I · 𝒪_Z`, which is
what lets Stacks 088C on `Z ⟶ Spec A` be read as a statement about the inverse image of `𝓘`.

Separatedness and quasi-compactness of `f` are in the binders, as in the source, but the
reduction itself does not use them: they are what the source needs in order to produce `hSupp`,
through Chow's lemma.

## References

* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088D](https://stacks.math.columbia.edu/tag/088D)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
* [Stacks Project, Tag 0CYR](https://stacks.math.columbia.edu/tag/0CYR)
* [Stacks Project, Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-! ### A proper closed subscheme carrying a module with proper support -/

/-- The closed subscheme of an ideal sheaf whose support is proper over the base is proper over
the base. -/
private theorem isProper_subschemeι_comp_of_isProperOver_support
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    {J : X.IdealSheafData} (hp : IsProperOver f J.support) : IsProper (J.subschemeι ≫ f) :=
  (exists_isProper_iff_forall_isProper f _).1
    ((isProperOver_iff_exists_isProper f _).1 hp) _ rfl

/-- **A coherent module with support proper over the base is annihilated by the ideal sheaf of a
closed subscheme proper over the base.** -/
public theorem exists_isProper_annihilatedByKer_of_hasProperSupport
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : HasProperSupport f F) :
    ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
      Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι F := by
  obtain ⟨Z, hZ, hZproper⟩ := hF
  refine ⟨annihilatorIdeal F, ?_, fun U a ha m => annihilatorIdeal_smul_eq_zero F U a ha m⟩
  have hsupp : (annihilatorIdeal F).support = Z :=
    Closeds.ext ((supp_eq_support_annihilatorIdeal F).symm.trans hZ.symm)
  exact isProper_subschemeι_comp_of_isProperOver_support f (hsupp ▸ hZproper)

/-- **Annihilation by the ideal sheaf of a closed subscheme passes to larger subschemes.** If
`J ≤ J'`, the subscheme of `J'` is contained in that of `J`, and a module annihilated by the
ideal of `J'` is annihilated by the smaller ideal `J`. -/
public theorem annihilatedByKer_subschemeι_of_le {X : Scheme.{u}} {J J' : X.IdealSheafData}
    (h : J ≤ J') (M : X.Modules)
    (hM : Stacks.ClosedImmersion.AnnihilatedByKer J'.subschemeι M) :
    Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι M := by
  intro U a ha m
  refine hM U a ?_ m
  have hcomp : ((Scheme.IdealSheafData.inclusion h ≫ J.subschemeι).app U).hom a =
      ((Scheme.IdealSheafData.inclusion h).app _).hom ((J.subschemeι.app U).hom a) := rfl
  rw [← Scheme.IdealSheafData.inclusion_subschemeι h, hcomp, ha, map_zero]
  rfl

/-- **Two coherent modules with support proper over the base are annihilated by the ideal sheaf
of one common closed subscheme proper over the base.** The subscheme is the union of the two
scheme-theoretic supports, whose ideal sheaf is the product of the two, and a finite union of
closed subsets proper over the base is proper over the base. -/
public theorem exists_isProper_annihilatedByKer_pair
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (hF : HasProperSupport f F) (hG : HasProperSupport f G) :
    ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
      Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι F ∧
      Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι G := by
  obtain ⟨J₁, hJ₁, hF₁⟩ := exists_isProper_annihilatedByKer_of_hasProperSupport f F hF
  obtain ⟨J₂, hJ₂, hG₂⟩ := exists_isProper_annihilatedByKer_of_hasProperSupport f G hG
  have hle₁ : J₁ * J₂ ≤ J₁ := Scheme.IdealSheafData.le_def.2 fun U => Ideal.mul_le_left
  have hle₂ : J₁ * J₂ ≤ J₂ := Scheme.IdealSheafData.le_def.2 fun U => Ideal.mul_le_right
  refine ⟨J₁ * J₂, ?_, annihilatedByKer_subschemeι_of_le hle₁ F hF₁,
    annihilatedByKer_subschemeι_of_le hle₂ G hG₂⟩
  refine isProper_subschemeι_comp_of_isProperOver_support f ?_
  rw [Scheme.IdealSheafData.support_mul]
  exact isProperOver_sup f _ _ ((isProperOver_iff_exists_isProper f _).2 ⟨J₁, rfl, hJ₁⟩)
    ((isProperOver_iff_exists_isProper f _).2 ⟨J₂, rfl, hJ₂⟩)

/-! ### Full faithfulness over a separated base, through a proper closed subscheme -/

/-- **Completion is bijective on morphisms between coherent modules annihilated by the ideal
sheaf of a closed subscheme proper over the base.** No hypothesis: the two modules are direct
images from the proper closed subscheme by Stacks 087T, completion commutes with that direct
image, and completion on the proper closed subscheme is fully faithful by Stacks 0883 — which is
unconditional for a proper morphism.

This is `Stacks.Coherent.bijective_completion_map_pushforward` with the hypothesis that the
completion functor on the subscheme be an *equivalence* replaced by what the square actually
uses, its full faithfulness, which over a proper closed subscheme is a theorem. -/
public theorem bijective_completionFunctor_map_of_annihilatedByKer
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (J : X.IdealSheafData) (hJ : IsProper (J.subschemeι ≫ f))
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι F.obj)
    (hG : Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι G.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Function.Bijective
      (fun u : F ⟶ G => ((completionFunctor X (baseIdealSheaf A I f)).map u).hom) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsProper (J.subschemeι ≫ f) := hJ
  let : IsLocallyNoetherian J.subscheme :=
    AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion J.subschemeι
  have : F.obj.IsCoherent := F.property
  have : G.obj.IsCoherent := G.property
  obtain ⟨FZ, hFZ, ⟨eF⟩⟩ :=
    exists_isCoherent_pushforward_iso_of_smul_eq_zero J.subschemeι F.obj hF
  obtain ⟨GZ, hGZ, ⟨eG⟩⟩ :=
    exists_isCoherent_pushforward_iso_of_smul_eq_zero J.subschemeι G.obj hG
  let FZ' : AlgebraicGeometry.SheafOfModules.CoherentModules J.subscheme.ringCatSheaf :=
    ⟨FZ, hFZ⟩
  let GZ' : AlgebraicGeometry.SheafOfModules.CoherentModules J.subscheme.ringCatSheaf :=
    ⟨GZ, hGZ⟩
  have eF' : pushforwardCoherentObj J.subschemeι FZ' ≅ F := ObjectProperty.isoMk _ eF
  have eG' : pushforwardCoherentObj J.subschemeι GZ' ≅ G := ObjectProperty.isoMk _ eG
  refine Stacks.Coherent.bijective_completion_map_of_iso _ eF'.symm eG'.symm ?_
  obtain ⟨ffZ⟩ : Nonempty (completionFunctor J.subscheme
      ((baseIdealSheaf A I f).comap J.subschemeι)).FullyFaithful := by
    rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f J.subschemeι]
    exact fullyFaithful_completionFunctor_of_isProper A I (J.subschemeι ≫ f)
  let ψF := pushforwardCompletionIso J.subschemeι (baseIdealSheaf A I f) FZ'
  let ψG := pushforwardCompletionIso J.subschemeι (baseIdealSheaf A I f) GZ'
  -- the three bijective edges of the square
  let β₁ : (FZ' ⟶ GZ') →
      (pushforwardCoherentObj J.subschemeι FZ' ⟶ pushforwardCoherentObj J.subschemeι GZ') :=
    pushforwardCoherentMap J.subschemeι
  let β₂ : (FZ' ⟶ GZ') →
      (((completionFunctor J.subscheme
            ((baseIdealSheaf A I f).comap J.subschemeι)).obj FZ').obj ⟶
        ((completionFunctor J.subscheme
            ((baseIdealSheaf A I f).comap J.subschemeι)).obj GZ').obj) :=
    fun u => ((completionFunctor J.subscheme
      ((baseIdealSheaf A I f).comap J.subschemeι)).map u).hom
  let β₃ : (((completionFunctor J.subscheme
            ((baseIdealSheaf A I f).comap J.subschemeι)).obj FZ').obj ⟶
        ((completionFunctor J.subscheme
            ((baseIdealSheaf A I f).comap J.subschemeι)).obj GZ').obj) →
      (((completionFunctor X (baseIdealSheaf A I f)).obj
            (pushforwardCoherentObj J.subschemeι FZ')).obj ⟶
        ((completionFunctor X (baseIdealSheaf A I f)).obj
            (pushforwardCoherentObj J.subschemeι GZ')).obj) :=
    fun α => ψF.hom ≫
      Functor.whiskerRight α (Scheme.Modules.pushforward J.subschemeι) ≫ ψG.inv
  let ffi := Stacks.ClosedImmersion.fullyFaithfulPushforward J.subschemeι
  have hβ₁ : Function.Bijective β₁ := by
    refine ⟨fun u v huv => ObjectProperty.hom_ext _ (ffi.map_injective ?_), fun w =>
      ⟨ObjectProperty.homMk (ffi.preimage w.hom),
        ObjectProperty.hom_ext _ (ffi.map_preimage w.hom)⟩⟩
    exact congrArg (fun k : pushforwardCoherentObj J.subschemeι FZ' ⟶
      pushforwardCoherentObj J.subschemeι GZ' => k.hom) huv
  have hβ₂ : Function.Bijective β₂ :=
    Function.Bijective.comp
      ⟨fun _ _ e => ObjectProperty.hom_ext _ e, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
      (ffZ.map_bijective FZ' GZ')
  have hβ₃ : Function.Bijective β₃ :=
    (ψF.symm.homCongr ψG.symm).bijective.comp
      (Stacks.Coherent.bijective_whiskerRight_pushforward J.subschemeι _ _)
  have key : ∀ u : FZ' ⟶ GZ',
      ((completionFunctor X (baseIdealSheaf A I f)).map (β₁ u)).hom = β₃ (β₂ u) := by
    intro u
    refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨m⟩ := n
    have h := pushforwardCompletionIso_naturality J.subschemeι (baseIdealSheaf A I f) u m
    show ((completionFunctor X (baseIdealSheaf A I f)).map
        (pushforwardCoherentMap J.subschemeι u)).hom.app (op m) =
      ψF.hom.app (op m) ≫ (Scheme.Modules.pushforward J.subschemeι).map
        (((completionFunctor J.subscheme
          ((baseIdealSheaf A I f).comap J.subschemeι)).map u).hom.app (op m)) ≫
        ψG.inv.app (op m)
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact (Stacks.Coherent.bijective_iff_of_commSquare _ _ β₁ β₃ hβ₁ hβ₃ fun u =>
    (key u).symm).1 hβ₂

/-! ### The two forms of annihilation by a closed subscheme -/

/-- Annihilation by the ideal sheaf cutting out the subscheme of `J` is annihilation by `J` in the
sense of `Stacks.Algebraization.idealPowerMultiple`, at exponent one. -/
public theorem annihilatedByKer_subschemeι_iff_idealPowerMultiple_one {X : Scheme.{u}}
    (J : X.IdealSheafData) (M : X.Modules) :
    Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι M ↔ idealPowerMultiple J 1 M = ⊥ := by
  have h2 := Stacks.Coherent.annihilatedByKer_subschemeι_pow_iff J 1 M
  rw [pow_one] at h2
  exact (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal J.subschemeι M).trans h2

/-- **A coherent module annihilated by the ideal sheaf of a closed subscheme proper over the base
has support proper over the base.** This is the converse direction of
`Stacks.Algebraization.exists_isProper_annihilatedByKer_of_hasProperSupport`, and it is the
minimality half of [Stacks, Tag 0CYS]: the module is the direct image of a coherent module on
that proper closed subscheme, so its scheme-theoretic support is contained in it. -/
public theorem hasProperSupport_of_annihilatedByKer
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (hJ : IsProper (J.subschemeι ≫ f))
    (F : X.Modules) [F.IsCoherent]
    (hF : Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι F) :
    HasProperSupport f F := by
  have : IsLocallyNoetherian J.subscheme :=
    AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion J.subschemeι
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isCoherent_pushforward_iso_of_smul_eq_zero J.subschemeι F hF
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := F)
  have : G.IsCoherent := hG
  have : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  have : G.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := G)
  refine ⟨⟨_root_.SheafOfModules.supp F, _root_.SheafOfModules.isClosed_supp F⟩, rfl, ?_⟩
  refine (Scheme.Modules.isProperOver_supp_iff_isProper_schemeTheoreticSupport f F).2 ?_
  exact (Scheme.Modules.isProper_schemeTheoreticSupport_iff_exists_pushforward f F).2
    ⟨J, G, inferInstance, inferInstance, hJ, ⟨e⟩⟩

/-! ### Grothendieck existence with proper support at the source's hypotheses -/

/-- **Stacks 088E from Stacks 088C on the proper closed subschemes of `X`.** Let `A` be a
Noetherian ring complete with respect to `I` and let `f : X ⟶ Spec A` be separated and of finite
type. Suppose

* `h088C`, that completion is an equivalence `Coh(𝒪_Z) ⥤ Coh(Z, 𝓘 𝒪_Z)` for every closed
  subscheme `Z ⊆ X` proper over `A`, and
* `hSupp`, that every coherent `𝓘`-adic system whose support is proper over `A` is annihilated by
  the ideal sheaf of some closed subscheme of `X` proper over `A`.

Then the functor of Stacks 088D is an equivalence.

This is the source's first paragraph. Full faithfulness does not use `h088C`: it is
`bijective_completionFunctor_map_of_annihilatedByKer`, which is unconditional. Essential
surjectivity is `hSupp` followed by `h088C` on the subscheme it produces, transported to `X` by
Stacks 087T; the algebraization produced there has support proper over `A` by
`hasProperSupport_of_annihilatedByKer`, so it is an object of the restricted source category. -/
public theorem isEquivalence_completionFunctorProperOver_of_properSubschemes
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088C : ∀ (K : X.IdealSheafData), IsProper (K.subschemeι ≫ f) →
      letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : IsLocallyNoetherian K.subscheme :=
        AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion K.subschemeι
      (completionFunctor K.subscheme
        ((baseIdealSheaf A I f).comap K.subschemeι)).IsEquivalence)
    (hSupp : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        HasProperSupport f (𝓖.obj.obj (op 0)) →
          ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
            IsSystemAnnihilatedBy J 𝓖.obj) :
    (completionFunctorProperOver A I f).IsEquivalence := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- full faithfulness, from the proper closed subscheme carrying the two modules
  have hbij : ∀ F G : CoherentModulesProperOver f,
      Function.Bijective ((completionFunctorProperOver A I f).map : (F ⟶ G) → _) := by
    intro F G
    have : F.obj.obj.IsCoherent := F.obj.property
    have : G.obj.obj.IsCoherent := G.obj.property
    obtain ⟨J, hJ, hFa, hGa⟩ :=
      exists_isProper_annihilatedByKer_pair f F.obj.obj G.obj.obj F.property G.property
    have h := bijective_completionFunctor_map_of_annihilatedByKer A I f J hJ F.obj G.obj hFa hGa
    refine (Stacks.Coherent.bijective_iff_of_commSquare _
      (fun u : F.obj ⟶ G.obj => ((completionFunctor X (baseIdealSheaf A I f)).map u).hom)
      (fun u : F ⟶ G => u.hom)
      (fun v : (completionFunctorProperOver A I f).obj F ⟶
        (completionFunctorProperOver A I f).obj G => v.hom.hom)
      ⟨fun _ _ e => ObjectProperty.hom_ext _ e, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
      ⟨fun _ _ e => ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ e),
        fun g => ⟨ObjectProperty.homMk (ObjectProperty.homMk g), rfl⟩⟩
      fun u => rfl).2 h
  obtain ⟨ff⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective _).2 hbij
  let := ff.full
  let := ff.faithful
  -- essential surjectivity, from the dévissage on the proper closed subscheme
  have hes : ∀ 𝓖 : CoherentAdicSystemsProperOver f (baseIdealSheaf A I f),
      (completionFunctorProperOver A I f).essImage 𝓖 := by
    intro 𝓖
    obtain ⟨J, hJ, hann⟩ := hSupp 𝓖.obj 𝓖.property
    have hKproper : IsProper ((J ^ 1).subschemeι ≫ f) := by rwa [pow_one]
    have : IsLocallyNoetherian (J ^ 1).subscheme :=
      AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion (J ^ 1).subschemeι
    obtain ⟨M, hM, ⟨eM⟩⟩ := Stacks.Coherent.exists_coherent_completion_iso_of_annihilated
      (baseIdealSheaf A I f) J 1 (h088C (J ^ 1) hKproper) 𝓖.obj.obj 𝓖.obj.property hann
    have : M.obj.IsCoherent := M.property
    have hMp : HasProperSupport f M.obj :=
      hasProperSupport_of_annihilatedByKer f J hJ M.obj
        ((annihilatedByKer_subschemeι_iff_idealPowerMultiple_one J M.obj).2 hM)
    exact ⟨⟨M, hMp⟩, ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ eM)⟩⟩
  let : (completionFunctorProperOver A I f).EssSurj := ⟨hes⟩
  exact { }

/-- **Stacks 088E, Grothendieck's existence theorem.** Let `A` be a Noetherian ring complete with
respect to an ideal `I` and let `f : X ⟶ Spec A` be separated and of finite type. Then the
functor of Stacks 088D

  `Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, 𝓘)`,  `𝓘 = I · 𝒪_X`,

is an equivalence, granted the two inputs below. Both are now carried, so 088E holds at the
hypotheses of the source and nothing else —
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds`. This declaration is the
reduction those two inputs feed:

* `hDev`, the inductive step of the Noetherian induction of Stacks 088C — a coherent adic system
  killed by a quasi-coherent ideal sheaf `L` is in the essential image of the completion functor
  as soon as every coherent adic system killed by an ideal sheaf strictly larger than `L` is —
  asked on every closed subscheme of `X` proper over `A`, which is where the source applies
  Stacks 088C; and
* `hSupp`, that every coherent `𝓘`-adic system with support proper over `A` is annihilated by the
  ideal sheaf of a closed subscheme of `X` proper over `A`. This is the second half of the
  source's proof, the half that applies Chow's lemma (Stacks 0200) to get a proper surjection
  from an H-quasi-projective `Y`, algebraizes the pullback on a projective compactification of
  `Y` by the projective case (Stacks 0885), and compares the result with the original system by
  Stacks 088B.

Everything between those two inputs and the conclusion is proved: the source's reduction through
Stacks 087T and [Stacks, Tag 0CYS], and full faithfulness, which carries no hypothesis at all.
`hDev` is turned into Stacks 088C on each proper closed subscheme by
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`.

No `stacks` attribute is attached: Stacks 088E is registered on
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds`. -/
public theorem isEquivalence_completionFunctorProperOver
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hDev : ∀ (K : X.IdealSheafData) (hK : IsProper (K.subschemeι ≫ f)),
      letI : IsProper (K.subschemeι ≫ f) := hK
      letI : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
      ∀ L : K.subscheme.IdealSheafData,
        (∀ L' : K.subscheme.IdealSheafData, L < L' →
            ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
                (baseIdealSheaf A I (K.subschemeι ≫ f)),
              IsSystemAnnihilatedBy L' 𝓖.obj →
                (completionFunctor K.subscheme
                  (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓖) →
          ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems
              (baseIdealSheaf A I (K.subschemeι ≫ f)),
            IsSystemAnnihilatedBy L 𝓕.obj →
              (completionFunctor K.subscheme
                (baseIdealSheaf A I (K.subschemeι ≫ f))).essImage 𝓕)
    (hSupp : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        HasProperSupport f (𝓖.obj.obj (op 0)) →
          ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
            IsSystemAnnihilatedBy J 𝓖.obj) :
    (completionFunctorProperOver A I f).IsEquivalence := by
  refine isEquivalence_completionFunctorProperOver_of_properSubschemes A I f ?_ hSupp
  intro K hK
  let : IsProper (K.subschemeι ≫ f) := hK
  rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f K.subschemeι]
  exact isEquivalence_completionFunctor_of_devissage A I (K.subschemeι ≫ f)
    (isIso_globalSectionsToLimit_of_isProper A I (K.subschemeι ≫ f)) (hDev K hK)

end Stacks.Algebraization

end
