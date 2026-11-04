module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness

/-!
# Raynaud–Gruson flattening by blowup

Stacks tag 0815 (More on Flatness, Theorem 38.30.7) is the Raynaud–Gruson flattening theorem.
Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be a morphism with `X`
quasi-compact and `f` locally of finite presentation, let `ℱ` be a quasi-coherent `𝒪_X`-module
of finite type, and let `U ⊆ S` be a quasi-compact open over which `ℱ` is of finite
presentation and flat. Then there is a `U`-admissible blowup `S' ⟶ S` whose strict transform
`ℱ'` is an `𝒪_{X'}`-module of finite presentation and flat over `S'`.

**The blowup is essential.** Without it the statement is false. If a flat refinement over `U`
itself always existed then, through
`AlgebraicGeometry.mem_fppfPrecoverage_of_isStandardVCovering`, every ph covering would be
refined by an fppf covering and the ph and fppf topologies would coincide; they are separated
classically by the normalization of a cuspidal curve, `Spec k[t] ⟶ Spec k[t², t³]`, which is
finite surjective with `k[t², t³] → k[t]` finite birational and not flat. What 0815 produces is
a refinement that is flat over `S'` *after* a proper base change `S' ⟶ S`, i.e. a ph covering,
and not a flat refinement over `S`.

**The strict transform is essential too.** The conclusion is *not* that the base change
`X ×_S S' ⟶ S'` becomes flat. Blowing up the base does not flatten the plain base change; one
must pass to the strict transform `X' ⊆ X ×_S S'`, the closed subscheme cut out by the sections
supported on the inverse image of the exceptional divisor. So the conclusion is phrased with
`Stacks.Blowup.strictTransformMap` and `Stacks.Blowup.strictTransformModule`, not with
`CategoryTheory.Limits.pullback.snd`.

## Main definitions

* `AlgebraicGeometry.HasModuleFlatteningBlowup` is the conclusion of tag 0815 for one triple
  `ℱ/X/S` and one open `U ⊆ S`.
* `AlgebraicGeometry.FinitePresentationHasModuleFlatteningBlowup` is the statement of tag 0815.
* `AlgebraicGeometry.HasModuleFlatteningBlowupFlat` is its flatness half, the sub-statement the
  Stacks proof isolates in its own first sentence.
* `AlgebraicGeometry.HasFlatteningBlowup` and
  `AlgebraicGeometry.FinitePresentationHasFlatteningBlowup` are the scheme-level forms, where
  the module is the structure sheaf and the conclusion is flatness of the morphism from the
  strict transform of `X` to the blowup.

Both statements are proved elsewhere in this development, from Stacks 0811 and nothing else;
see "The inputs" below. They are `Prop`s so that they can be carried as explicit hypotheses,
exactly as `AlgebraicGeometry.FinitePresentationHasFlatStratification` is for tag 0H3Z and
`AlgebraicGeometry.StandardVCoveringHasPHRefinement` is for tag 0ETR.

## Main results

* `Stacks.Blowup.exceptionalPullbackSet_top`, `Stacks.Blowup.exceptionalPullbackCompl_top`,
  `Stacks.Blowup.strictTransformIdeal_top` and
  `Stacks.Blowup.instIsIsoSchemeStrictTransformιTopIdealSheafData`: the blowup in the unit
  ideal sheaf — the blowup with empty centre, the only `⊤`-admissible one — has empty
  exceptional divisor, so the strict transform of `X` along it is the whole base change
  `X ×_S S'`.
* `AlgebraicGeometry.SheafOfModules.isZero_toSheafOfModules_supportedSectionsSubmodule` and
  `AlgebraicGeometry.SheafOfModules.cokernelSupportedSectionsSubmoduleIso`: on any scheme the
  submodule of sections supported on the empty set is zero, so dividing by it changes nothing.
  Together with the above these give `Stacks.Blowup.strictTransformSheafTopIso`: the strict
  transform of a module along the empty blowup is the plain pullback.
* `Stacks.Blowup.isFlatOver_strictTransformModule_top`,
  `AlgebraicGeometry.HasModuleFlatteningBlowupFlat.of_isFlatOver` and
  `AlgebraicGeometry.HasFlatteningBlowup.of_flat`: the region where the input is already flat
  over all of `S`, which is proved — at the module level for the flatness half of the
  conclusion, and at the structure sheaf in full.
* `Stacks.Blowup.eq_top_of_disjoint_univ_support`: an ideal sheaf whose support is disjoint from
  all of `S` is the unit ideal. So at `U = ⊤` the existential in the statements has exactly one
  candidate centre — no blowup is available — and the empty-centre region below is the only way
  the `U = ⊤` case can be witnessed. (Matching its hypothesis `IsFlatOver f ℱ` with the
  statement's `IsFlatOver (f.resLE ⊤ _ le_rfl) (ℱ.restrict ⊤.ι)` still needs flatness over the
  base to be transported along `Scheme.topIso`, which is not formalized here.) For `U < ⊤` the
  centre may be any finitely presented closed subscheme of the complement of `U`, which is
  where all the content of the theorem lies.

## The inputs

The proof in Stacks is an induction on `d = max_{s ∈ S} dim (Supp ℱ_s)` which reduces, étale
locally on source and target, to the case of a smooth morphism of affines with geometrically
irreducible fibres, then peels off a free direct summand. **That induction is proved**, in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.RaynaudGrusonInduction`, and so is each of
its four inputs:

* Stacks 0814, that the flattening question is étale local on source and target, is
  `AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf` in
  `StacksFrontier.AlgebraicGeometry.Flatness.Flattening.EtaleLocalFlatteningDescent`.
* Stacks 080G and 080W, the behaviour of the strict transform under affine pushforward and in a
  short exact sequence, are `AlgebraicGeometry.strictTransformSheafPushforwardIso` and
  `AlgebraicGeometry.strictTransformSheaf_shortExact`, read for flatness by
  `StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessShortExact`.
* Stacks 081N is `AlgebraicGeometry.FinitePresentationFromDenseOpen`'s
  `locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open`.
* Stacks 0811 is
  `AlgebraicGeometry.exists_isAdmissibleBlowup_opens_finitelyLocallyFree_surjective` in
  `StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibres0811`, proved under
  exactly the source's hypotheses. The induction consumes it in the shape
  `AlgebraicGeometry.FinitePresentationHasGenericFibreFreeBlowup`, and
  `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` in
  `StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811` derives that
  shape from the tag.

So the flatness assertion for a module, and hence
`AlgebraicGeometry.FinitePresentationHasFlatteningBlowup`, hold with nothing granted:
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup` in that same file. The sharper
hypothesis `AlgebraicGeometry.GenericFibreFlatteningBlowup`, which asks for global finite
presentation of the strict transform and for flatness at *every* generic point of a fibre of the
blown-up projection where Stacks 0811 gives freeness on an open surjecting onto the blowup, has
no producer and is no longer needed; the statements carrying it are kept as the record of that
sharper reduction.

One convenience is still absent, and it is what keeps the `U = ⊤` region below from being an
`iff` rather than an implication: the repository has no statement that the blowup in the unit
ideal sheaf is an isomorphism,

```lean
theorem isIso_blowUpToBase_top {S : Scheme} :
    IsIso (Stacks.Blowup.blowUpToBase (⊤ : S.IdealSheafData))
```

only that it is an isomorphism over the complement of the support of the centre
(`Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData`). So at `U = ⊤`
one can see that the only admissible centre is `⊤` without being able to descend flatness back
to `S` along the blowup.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- The submodule of sections supported on a subset that is empty is the zero submodule: a
section all of whose germs vanish is zero, by the separation axiom for the sheaf `F`.

The emptiness of the subset is a hypothesis rather than a literal `∅` so that the companion
`AlgebraicGeometry.SheafOfModules.cokernelSupportedSectionsSubmoduleIso` can be applied to a
subset that is only *provably* empty, without rewriting under the `HasCokernel` instance. -/
theorem isZero_toSheafOfModules_supportedSectionsSubmodule {X : Scheme.{u}} {Z : Set X}
    (hZ : Z = ∅) (F : SheafOfModules.{u} X.ringCatSheaf) :
    IsZero (supportedSectionsSubmodule Z F).toSheafOfModules := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  have hx : (x.1 : F.val.obj U) = 0 :=
    TopCat.Presheaf.section_ext ⟨F.val.presheaf, F.isSheaf⟩ (unop U) _ 0 fun y hy ↦
      (x.2 y hy (hZ ▸ Set.notMem_empty y)).trans (map_zero _).symm
  simp [show x = 0 from Subtype.ext hx]

/-- Dividing a module by its submodule of sections supported on an empty subset changes
nothing. -/
def cokernelSupportedSectionsSubmoduleIso {X : Scheme.{u}} {Z : Set X} (hZ : Z = ∅)
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    cokernel (supportedSectionsSubmodule Z F).ι ≅ F :=
  cokernelIsoOfEq ((isZero_toSheafOfModules_supportedSectionsSubmodule hZ F).eq_of_src _ 0) ≪≫
    cokernelZeroIsoTarget

end AlgebraicGeometry.SheafOfModules

namespace Stacks.Blowup

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- An ideal sheaf whose support is disjoint from the whole space is the unit ideal sheaf.

So the unit ideal sheaf is the only candidate centre for a `⊤`-admissible blowup, and the
`U = ⊤` case of Stacks 0815 asks for no blowup at all. -/
theorem eq_top_of_disjoint_univ_support {ℐ : S.IdealSheafData}
    (h : Disjoint ((⊤ : S.Opens) : Set S) (ℐ.support : Set S)) : ℐ = ⊤ := by
  have h0 : (ℐ.support : Set S) = ∅ := Set.univ_disjoint.mp (by simpa using h)
  exact ℐ.support_eq_bot_iff.mp (SetLike.coe_injective (by simpa using h0))

/-- The exceptional divisor of the blowup in the unit ideal sheaf is empty, so its inverse
image in `X ×_S S'` is empty too. -/
@[simp]
theorem exceptionalPullbackSet_top : exceptionalPullbackSet f (⊤ : S.IdealSheafData) = ∅ := by
  simp [exceptionalPullbackSet, exceptionalIdeal]

/-- The complement of the inverse image of the exceptional divisor of the blowup in the unit
ideal sheaf is all of `X ×_S S'`. -/
@[simp]
theorem exceptionalPullbackCompl_top :
    exceptionalPullbackCompl f (⊤ : S.IdealSheafData) = ⊤ := by
  ext x
  simp [exceptionalPullbackCompl]

/-- The strict transform of `X` along the blowup in the unit ideal sheaf is cut out by the zero
ideal sheaf: the sections supported on the empty set are the sections vanishing on all of
`X ×_S S'`. -/
theorem strictTransformIdeal_top : strictTransformIdeal f (⊤ : S.IdealSheafData) = ⊥ := by
  rw [strictTransformIdeal_eq_ker, exceptionalPullbackCompl_top]
  exact (blowUpPullback f (⊤ : S.IdealSheafData)).topIso.hom.ker_eq_bot_of_isIso

/-- The strict transform of `X` along the blowup in the unit ideal sheaf is the whole base
change `X ×_S S'`. -/
instance : IsIso (strictTransformι f (⊤ : S.IdealSheafData)) :=
  (Scheme.isIso_subschemeι_iff_eq_bot _).mpr (strictTransformIdeal_top f)

/-- The strict transform of a module along the blowup in the unit ideal sheaf is its plain
pullback to `X ×_S S'`: nothing is divided out, because the exceptional divisor is empty. -/
def strictTransformSheafTopIso (ℱ : X.Modules) :
    strictTransformSheaf f (⊤ : S.IdealSheafData) ℱ ≅
      (Scheme.Modules.pullback (blowUpPullbackToSource f (⊤ : S.IdealSheafData))).obj ℱ :=
  SheafOfModules.cokernelSupportedSectionsSubmoduleIso (exceptionalPullbackSet_top f) _

/-- **The empty-blowup region of Stacks 0815, flatness half.** A quasi-coherent module that is
already flat over `S` stays flat over the blowup in the unit ideal sheaf, i.e. no blowup is
needed.

The argument has three steps and uses no property of `f` whatsoever: the plain pullback of `ℱ`
to `X ×_S S'` is flat over `S'` because flatness of a module over the base is stable under base
change (Stacks 01U8); the strict transform agrees with that pullback because the exceptional
divisor is empty (`Stacks.Blowup.strictTransformSheafTopIso`); and the strict transform of `X`
is the whole of `X ×_S S'`, so pulling the module back along the closed immersion — which here
is an isomorphism — changes neither it nor its flatness. -/
theorem isFlatOver_strictTransformModule_top (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : IsFlatOver f.toLRSHom.toShHom ℱ) :
    IsFlatOver (strictTransformMap f (⊤ : S.IdealSheafData)).toLRSHom.toShHom
      (strictTransformModule f (⊤ : S.IdealSheafData) ℱ) := by
  let _ : SheafOfModules.IsQuasicoherent
      (R := structureSheafRing X.toRingedSpace) ℱ :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ)
  exact (isFlatOver_iff_modulePullback_isFlatOver (strictTransformι f (⊤ : S.IdealSheafData))
    (blowUpPullbackToBlowUp f (⊤ : S.IdealSheafData)) _).mp
    ((isFlatOver_iff_of_moduleIso
      (blowUpPullbackToBlowUp f (⊤ : S.IdealSheafData)).toLRSHom.toShHom
      (strictTransformSheafTopIso f ℱ)).mpr
      (modulePullback_isFlatOver
        (IsPullback.of_hasPullback f (blowUpToBase (⊤ : S.IdealSheafData))) ℱ hℱ))

end Stacks.Blowup

namespace AlgebraicGeometry

open Stacks.Blowup

/-- **The conclusion of Stacks 0815** for one quasi-coherent module `ℱ` on `X`, one morphism
`f : X ⟶ S` and one open `U ⊆ S`. There is a quasi-coherent sheaf of ideals `ℐ` on `S` whose
closed subscheme is of finite presentation over `S` and supported away from `U` — so that the
blowup of `S` in `ℐ` is a `U`-admissible blowup, by
`Stacks.Blowup.isAdmissibleBlowup_blowUpToBase` — such that the strict transform of `ℱ` is an
`𝒪_{X'}`-module of finite presentation and flat over the blowup.

The existential is over the centre `ℐ` rather than over an abstract morphism `b : S' ⟶ S` with
`Stacks.Blowup.IsAdmissibleBlowup U b`, because the strict transform is a construction attached
to a centre: `Stacks.Blowup.strictTransformMap` and `Stacks.Blowup.strictTransformModule` take
`ℐ`, and the predicate `Stacks.Blowup.IsAdmissibleBlowup` forgets which centre exhibits its
morphism. The two conjuncts recorded here are exactly the two conditions that predicate asks of
a centre. -/
def HasModuleFlatteningBlowup {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (ℱ : X.Modules) : Prop :=
  ∃ ℐ : S.IdealSheafData,
    FinitePresentation ℐ.subschemeι ∧
      Disjoint (U : Set S) (ℐ.support : Set S) ∧
        (strictTransformModule f ℐ ℱ).IsFinitePresentation ∧
          IsFlatOver (strictTransformMap f ℐ).toLRSHom.toShHom (strictTransformModule f ℐ ℱ)

/-- **The statement of Stacks 0815.** For a quasi-compact `X` over a quasi-compact and
quasi-separated `S` by a morphism locally of finite presentation, a quasi-coherent module of
finite type that is of finite presentation and flat over a quasi-compact open `U ⊆ S` can be
flattened by a `U`-admissible blowup of the base.

Its flatness half is proved for a module by
`AlgebraicGeometry.hasFlatteningCentre_of_genericFibreFreeBlowup` from the conclusion of
Stacks 0811, which `AlgebraicGeometry.finitePresentationHasGenericFibreFreeBlowup` supplies; see
the "The inputs" section of the module documentation.
`AlgebraicGeometry.HasModuleFlatteningBlowupFlat.of_isFlatOver` is the region proved with no
hypothesis at all. -/
def FinitePresentationHasModuleFlatteningBlowup : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (ℱ : X.Modules) [CompactSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType], IsCompact (U : Set S) →
    (ℱ.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation →
    IsFlatOver (f.resLE U (f ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom (ℱ.restrict (f ⁻¹ᵁ U).ι) →
    HasModuleFlatteningBlowup f U ℱ

/-- **The first half of the conclusion of Stacks 0815**: the same existential, asking only that
the strict transform be flat over the blowup and not that it be of finite presentation.

This is the statement the Stacks proof isolates in its own first sentence — "we first prove that
we can find a `U`-admissible blowup such that the strict transform is flat" — the finite
presentation being recovered at the very end from Stacks 081N. It is a weakening of
`AlgebraicGeometry.HasModuleFlatteningBlowup`, by
`AlgebraicGeometry.HasModuleFlatteningBlowup.flat`. -/
def HasModuleFlatteningBlowupFlat {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (ℱ : X.Modules) : Prop :=
  ∃ ℐ : S.IdealSheafData,
    FinitePresentation ℐ.subschemeι ∧
      Disjoint (U : Set S) (ℐ.support : Set S) ∧
        IsFlatOver (strictTransformMap f ℐ).toLRSHom.toShHom (strictTransformModule f ℐ ℱ)

/-- Tag 0815's conclusion implies its flatness half. -/
theorem HasModuleFlatteningBlowup.flat {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Opens}
    {ℱ : X.Modules} (h : HasModuleFlatteningBlowup f U ℱ) :
    HasModuleFlatteningBlowupFlat f U ℱ :=
  let ⟨ℐ, hfp, hdisj, _, hflat⟩ := h
  ⟨ℐ, hfp, hdisj, hflat⟩

/-- **The region of Stacks 0815 where no blowup is needed.** If the quasi-coherent module `ℱ` is
already flat over all of `S` then the blowup in the unit ideal sheaf works: its centre is empty,
so it is `U`-admissible for every `U`, and the strict transform along it is `ℱ` pulled back to
`X ×_S S'`, which is flat over `S'` by base change.

By `Stacks.Blowup.eq_top_of_disjoint_univ_support` the unit ideal sheaf is the only admissible
centre when `U = ⊤`, so at `U = ⊤` no blowup is available and this is the only way the
conclusion can be witnessed.

This is the flatness half only. Discharging the finite-presentation conjunct of
`AlgebraicGeometry.HasModuleFlatteningBlowup` even in this region needs the module pullback to
preserve finite presentation, which the repository now has as
`Stacks.Modules.isFinitePresentation_pullback`; it is not done here because the strict transform
has to be identified with that pullback first. -/
theorem HasModuleFlatteningBlowupFlat.of_isFlatOver {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : IsFlatOver f.toLRSHom.toShHom ℱ) : HasModuleFlatteningBlowupFlat f U ℱ :=
  ⟨⊤, finitePresentation_subschemeι_top, by simp, isFlatOver_strictTransformModule_top f ℱ hℱ⟩

/-- **The conclusion of Stacks 0815 at the structure sheaf**, read as a statement about
morphisms: there is a centre `ℐ` exhibiting a `U`-admissible blowup of `S` such that the strict
transform of `X` is flat over the blowup.

Note that the conclusion is flatness of `Stacks.Blowup.strictTransformMap f ℐ`, the structure
morphism of the strict transform `X' ⊆ X ×_S S'`, and *not* of
`CategoryTheory.Limits.pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)`: blowing up the base does
not flatten the plain base change. -/
def HasFlatteningBlowup {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) : Prop :=
  ∃ ℐ : S.IdealSheafData,
    FinitePresentation ℐ.subschemeι ∧
      Disjoint (U : Set S) (ℐ.support : Set S) ∧ Flat (strictTransformMap f ℐ)

/-- **The statement of Stacks 0815 at the structure sheaf.** A morphism of finite presentation
from a quasi-compact scheme to a quasi-compact and quasi-separated scheme, flat over a
quasi-compact open `U` of the base, becomes flat on the strict transform after a `U`-admissible
blowup of the base.

This is proved, with nothing granted, in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811`, as
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup`;
`AlgebraicGeometry.HasFlatteningBlowup.of_flat` is the region proved directly, with no appeal to
the induction at all. -/
def FinitePresentationHasFlatteningBlowup : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) [CompactSpace X] [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f], IsCompact (U : Set S) →
    Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) → HasFlatteningBlowup f U

/-- **The region of Stacks 0815 where no blowup is needed, at the structure sheaf.** If `f` is
already flat over all of `S` then the blowup in the unit ideal sheaf works: its centre is empty,
so it is `U`-admissible for every `U`, the strict transform of `X` along it is the whole base
change `X ×_S S'`, and the base change of a flat morphism is flat.

By `Stacks.Blowup.eq_top_of_disjoint_univ_support` the unit ideal sheaf is the only admissible
centre when `U = ⊤`, so at `U = ⊤` no blowup is available and this is the only way the
conclusion can be witnessed. Nothing about finite presentation or quasi-compactness is
needed. -/
theorem HasFlatteningBlowup.of_flat {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] (U : S.Opens) :
    HasFlatteningBlowup f U := by
  refine ⟨⊤, finitePresentation_subschemeι_top, by simp, ?_⟩
  rw [strictTransformMap]
  infer_instance

end AlgebraicGeometry

end
