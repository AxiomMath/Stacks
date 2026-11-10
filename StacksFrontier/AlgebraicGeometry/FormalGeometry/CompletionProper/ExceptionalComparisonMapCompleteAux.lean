module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Corner
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.MateComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AnnihilatedComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapFullyFaithfulAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapPullbackAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapPushforwardAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapQuotientAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapUnitAux
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.EquationsBaseChange
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk

/-!
# The kernel–cokernel bound of Stacks 088B over a complete affine base

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `f : X ⟶ Spec A` be
proper, write `𝒥 = I 𝒪_{Spec A}` and `ℐ = 𝒥 𝒪_X`, and let `𝒦 ⊆ 𝒪_{Spec A}` be a quasi-coherent
sheaf of ideals such that `f` is an isomorphism over the open complement of `V(𝒦)`. Let `(𝒢_n)`
be an object of `Coh(Spec A, 𝒥)`, let `𝓕` be a coherent `𝒪_X`-module and let
`β : (f^*𝒢_n) ≅ 𝓕^` be an isomorphism in `Coh(X, ℐ)`. [Stacks, Tag 088B] produces a map
`α : (𝒢_n) ⟶ (f_*𝓕)^` whose levelwise kernels and cokernels are annihilated by one power of
`𝒦`. This file proves that bound, with `α` presented by the equation that characterises it:
`α` composed with the comparison `(f_*𝓕)^ ⟶ f_*(𝓕^)` of the file
`ExceptionalComparisonMapPushforwardAux.lean` (in this directory,
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/`) is the map `γ` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/DirectImageComparison.lean`.

The proof is the source's. Over a complete base the completion functor is essentially
surjective ([Stacks, Tag 088C] in the affine case), so `(𝒢_n) ≅ 𝒢^` for a coherent
`𝒪_{Spec A}`-module `𝒢`; pullback commutes with completion, so `β` becomes an isomorphism
`(f^*𝒢)^ ≅ 𝓕^` in `Coh(X, ℐ)`, and completion is fully faithful over a complete base
([Stacks, Tag 0883]), so that isomorphism is the completion of a unique isomorphism
`b : f^*𝒢 ≅ 𝓕`. The adjunction map of `f^* ⊣ f_*` followed by `f_*b` is a morphism
`c : 𝒢 ⟶ f_*𝓕` of coherent `𝒪_{Spec A}`-modules — the direct image is coherent by
[Stacks, Tag 02O5] — which restricts to an isomorphism over `Spec A ∖ V(𝒦)`, because `f` does
there. So one positive power of `𝒦` annihilates `Ker(c)` and `Coker(c)`, hence `𝒦 ²ᵗ`
annihilates the levelwise kernels and cokernels of `c^`. Finally `α` *is* `c^` read through the
isomorphism `𝒢^ ≅ (𝒢_n)`, because the defining equation determines a morphism into `(f_*𝓕)^`:
over a complete base completion is full on `Spec A`, so any such morphism is a `c'^`, and the
equation forces `c'` and `c` to agree after composing with `f_*(𝓕 ⟶ 𝓕/ℐ ⁿ⁺¹𝓕)` for every `n`,
which by the adjunction `f^* ⊣ f_*` says that the adjoint transposes `f^*𝒢 ⟶ 𝓕` have equal
completions — and completion is faithful on `X`. **No form of the theorem on formal functions
is used**, only the full faithfulness of [Stacks, Tag 0883] on the two schemes.

## Main results

* `Stacks.Coherent.comap_baseIdealSheafOnSpec` — the inverse image of `I 𝒪_{Spec A}` along
  `f : X ⟶ Spec A` is `I 𝒪_X`.
* `Stacks.Coherent.essImage_completionFunctor_baseIdealSheafOnSpec` — Grothendieck existence on
  the spectrum of a complete Noetherian ring, at the ideal sheaf `I 𝒪_{Spec A}`.
* `Stacks.Coherent.isIso_restrict_unit_of_isIso_morphismRestrict` — the adjunction map
  `𝒢 ⟶ f_*f^*𝒢` restricts to an isomorphism over an open of the target on which `f` is an
  isomorphism.
* `Stacks.Coherent.exists_systemMap_isKernelCokernelAnnihilatedByPower_of_isAdicComplete` —
  the comparison map of Stacks 088B over a complete affine base exists, satisfies the defining
  equation, and has its levelwise kernels and cokernels annihilated by a power of `𝒦`.
* `Stacks.Coherent.systemMap_unique_pushforwardCompletionComparison_of_isAdicComplete` — a
  morphism into the completion of a proper direct image over a complete affine base is
  determined by its composite with the comparison map `(f_*𝓕)^ ⟶ f_*(𝓕^)`.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_isAdicComplete` — **the
  kernel–cokernel bound of Stacks 088B over a complete affine base**, for the map `α`
  characterised by the defining equation.

## Implementation notes

The ideal sheaf of `I` on `Spec A` is `Stacks.Coherent.baseIdealSheafOnSpec`, the spelling
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/AffineExistence.lean` uses;
`Stacks.Coherent.comap_baseIdealSheafOnSpec` identifies its inverse image with
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf`, which is the ideal sheaf the full
faithfulness statement of [Stacks, Tag 0883] is indexed by. Completeness is transported from
`A` to `Γ(Spec A, ⊤)` by `IsAdicComplete.congr_ringEquiv` along `Scheme.ΓSpecIso`. Full
faithfulness on the base itself is the same statement for the identity of `Spec A`, which is
proper because an isomorphism is finite; the ideal sheaves are identified by
`Stacks.Coherent.comap_baseIdealSheafOnSpec` together with
`AlgebraicGeometry.Scheme.IdealSheafData.comap_id`.

Uniqueness is proved against the *computation rule* of the comparison map rather than against
any invertibility statement about it: the only facts used are
`Stacks.Coherent.pushforwardCompletionComponent_π`,
`Stacks.Algebraization.completionFunctor_map_quotient`,
`CategoryTheory.Adjunction.homEquiv_naturality_right_symm` and the epimorphy of the completion
projections. This is why the theorem on formal functions ([Stacks, Tag 02OC]) does not appear;
the source needs it to *construct* `α`, and here `α` is given.

The restriction of the adjunction map is handled through the base-change comparison of the
restriction square rather than directly: the comparison carries the inverse image of the
adjunction map of `f` to the adjunction map of `f ∣_ V`
(`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_unit`), it is invertible for a
restriction square (`Stacks.AlgebraicGeometry.AffineBaseChange`), and the adjunction map of an
isomorphism is invertible because the inverse image along an isomorphism is fully faithful.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` carrying its
own `Category` instance, so a composite whose factors are presented at the two different
spellings is accepted while no rewrite by `CategoryTheory.Category.assoc` applies to it. Every
reassociation in the diagram chase is therefore performed in term mode out of
`CategoryTheory.Category.assoc` and `congrArg`, as in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/AffineExistence.lean`; the two
epimorphism cancellations name the category explicitly for the same reason.

The three instances `IsLocallyNoetherian X`, `IsNoetherian X` and the coherence of `f_*𝓕` are
consequences of properness rather than hypotheses, so they are supplied by `letI` inside the
statements instead of being assumed; this is why the remaining data of the two main statements
is quantified rather than bound by the theorem's binders.

No Stacks attribute for Tag 088B is placed. The source's lemma asserts the existence of `α` over
an arbitrary Noetherian base, obtained from the complete affine case by descent along `B ⟶ B^`;
only the complete affine case is proved here, so the tag's covering set is not complete.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

/-! ### The ideal sheaf attached to an ideal of the base ring -/

/-- The ideal sheaf `I 𝒪_{Spec A}` attached to an ideal `I` of `A` on the spectrum of `A`. -/
public def baseIdealSheafOnSpec (A : Type u) [CommRing A] (I : Ideal A) :
    (Spec (.of A)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I)

/-- The inverse image of `I 𝒪_{Spec A}` along `f : X ⟶ Spec A` is `I 𝒪_X`. -/
public theorem comap_baseIdealSheafOnSpec (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    (baseIdealSheafOnSpec A I).comap f =
      Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f := by
  rw [baseIdealSheafOnSpec, Stacks.IdealSheaf.comap_ofIdealTop, Ideal.map_map,
    Stacks.Cohomology.FormalFunctions.baseIdealSheaf,
    Stacks.Cohomology.FormalFunctions.baseIdeal, CommRingCat.hom_comp]

/-- Completeness of `A` for `I` is completeness of the global functions of `Spec A` for the
ideal generated by the image of `I`. -/
public theorem isAdicComplete_map_ΓSpecIso_inv (A : Type u) [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] :
    IsAdicComplete (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I) Γ(Spec (.of A), ⊤) :=
  (IsAdicComplete.congr_ringEquiv I
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv).2 inferInstance

/-- **Grothendieck existence on the spectrum of a complete Noetherian ring**, at the ideal sheaf
`I 𝒪_{Spec A}`: every coherent `I 𝒪_{Spec A}`-adic system is the completion of a coherent
module. -/
public theorem essImage_completionFunctor_baseIdealSheafOnSpec (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (G : CoherentAdicSystems (baseIdealSheafOnSpec A I)) :
    (Stacks.Algebraization.completionFunctor (Spec (.of A))
      (baseIdealSheafOnSpec A I)).essImage G := by
  let : IsNoetherianRing Γ(Spec (.of A), ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec (.of A))⟩
  let := isAdicComplete_map_ΓSpecIso_inv A I
  exact essImage_completionFunctor_of_isAdicComplete (Spec (.of A))
    (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I) G

/-! ### The adjunction map over an open on which the morphism is an isomorphism -/

/-- **The adjunction map `𝒢 ⟶ f_*f^*𝒢` restricts to an isomorphism over an open `V` of the
target on which `f` is an isomorphism.**

The base-change comparison of the restriction square of `f` over `V` carries the inverse image
along `V.ι` of the adjunction map of `f` to the adjunction map of `f ∣_ V`
(`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_unit`), and the comparison is an
isomorphism because the square is the restriction square
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`). The
adjunction map of `f ∣_ V` is an isomorphism because the inverse image along an isomorphism is
fully faithful. Restriction and inverse image are identified by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
public theorem isIso_restrict_unit_of_isIso_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) [IsIso (f ∣_ V)] (M : S.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι V)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) := by
  set u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M with hu
  set w := Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare f V
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit.app
      ((Scheme.Modules.pullback (Scheme.Opens.ι V)).obj M)) := by
    have := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isEquivalence_pullback (f ∣_ V)
    have : IsIso (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V)).unit :=
      Adjunction.unit_isIso_of_L_fully_faithful _
    exact NatIso.isIso_app_of_isIso _ _
  have hbc : IsIso (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
      ((Scheme.Modules.pullback f).obj M)) := by
    rw [← Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange]
    exact Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f V _
  have hsq : IsIso ((Scheme.Modules.pushforward (f ∣_ V)).map
      (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareIso w M).hom) :=
    Functor.map_isIso _ _
  have key := Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_unit w M
  have hcomp : IsIso ((Scheme.Modules.pullback (Scheme.Opens.ι V)).map u ≫
      (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
          ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pushforward (f ∣_ V)).map
          (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareIso w M).hom)) := by
    rw [hu, key]
    exact hunit
  have hpull : IsIso ((Scheme.Modules.pullback (Scheme.Opens.ι V)).map u) :=
    IsIso.of_isIso_comp_right _
      (Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange w
          ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pushforward (f ∣_ V)).map
          (Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareIso w M).hom)
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι V)).hom.naturality u
  have hr : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι V)).map u ≫
      (Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι V)).hom.app
        ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj M)) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι V)).hom.app
      ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj M))

/-- The completion functor on `X` at the inverse image of `I 𝒪_{Spec A}` is fully faithful. -/
private theorem nonempty_fullyFaithful_completionFunctor_comap (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Nonempty (Stacks.Algebraization.completionFunctor X
      ((baseIdealSheafOnSpec A I).comap f)).FullyFaithful := by
  rw [comap_baseIdealSheafOnSpec]
  exact Stacks.Algebraization.fullyFaithful_completionFunctor_of_isAdicComplete A I f

/-! ### The comparison map over a complete affine base -/

/-- **The comparison map of Stacks 088B over a complete affine base, with its kernel–cokernel
bound.** -/
public theorem exists_systemMap_isKernelCokernelAnnihilatedByPower_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (K : (Spec (.of A)).IdealSheafData)
    (hf : IsIso (f ∣_ K.support.compl))
    (G : CoherentAdicSystems (baseIdealSheafOnSpec A I))
    (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    ∀ β : (coherentAdicPullback f (baseIdealSheafOnSpec A I)).obj G ≅
      (Stacks.Algebraization.completionFunctor X
        ((baseIdealSheafOnSpec A I).comap f)).obj ⟨F, inferInstance⟩,
    ∃ a : G ⟶ (Stacks.Algebraization.completionFunctor (Spec (.of A))
        (baseIdealSheafOnSpec A I)).obj
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩,
      Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower K a.hom ∧
        a.hom ≫ pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F =
          directImageComparison f (baseIdealSheafOnSpec A I) G ⟨F, inferInstance⟩ β := by
  intro β
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  have := hf
  obtain ⟨Gc, ⟨e⟩⟩ := essImage_completionFunctor_baseIdealSheafOnSpec A I G
  have := Gc.property
  obtain ⟨hFF⟩ := nonempty_fullyFaithful_completionFunctor_comap A I f
  let w := (pullbackCompletionIso f (baseIdealSheafOnSpec A I) Gc).symm ≪≫
    (coherentAdicPullback f (baseIdealSheafOnSpec A I)).mapIso e ≪≫ β
  let b := hFF.preimage w.hom
  have hb : (Stacks.Algebraization.completionFunctor X
      ((baseIdealSheafOnSpec A I).comap f)).map b = w.hom := hFF.map_preimage w.hom
  have hbiso : IsIso b := by
    have : IsIso ((Stacks.Algebraization.completionFunctor X
        ((baseIdealSheafOnSpec A I).comap f)).map b) := by
      rw [hb]
      infer_instance
    exact hFF.isIso_of_isIso_map b
  have : IsIso (C := X.Modules) b.hom := Functor.map_isIso (ObjectProperty.ι _) b
  have : IsIso ((Scheme.Modules.pushforward f).map b.hom) :=
    Functor.map_isIso (Scheme.Modules.pushforward f) b.hom
  let c₁ : Gc ⟶ (⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ :
      AlgebraicGeometry.SheafOfModules.CoherentModules (Spec (.of A)).ringCatSheaf) :=
    ObjectProperty.homMk ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj ≫
      (Scheme.Modules.pushforward f).map b.hom)
  have hrestr : IsIso ((Scheme.Modules.restrictFunctor
      (Scheme.Opens.ι K.support.compl)).map c₁.hom) := by
    have := isIso_restrict_unit_of_isIso_morphismRestrict f K.support.compl Gc.obj
    have : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
        ((Scheme.Modules.pushforward f).map b.hom)) :=
      Functor.map_isIso (Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl))
        ((Scheme.Modules.pushforward f).map b.hom)
    change IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj ≫
        (Scheme.Modules.pushforward f).map b.hom))
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨t, ht, hker, hcok⟩ :=
    exists_pos_idealPowerMultiple_kernel_cokernel_eq_bot K c₁.hom hrestr
  have hq := isKernelCokernelAnnihilatedByPower_completionFunctor_map
    (baseIdealSheafOnSpec A I) K c₁ ht hker hcok
  refine ⟨e.inv ≫ (Stacks.Algebraization.completionFunctor (Spec (.of A))
    (baseIdealSheafOnSpec A I)).map c₁, ?_, ?_⟩
  · exact Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_iso_comp K
      ((ObjectProperty.ι (IsCoherentAdicSystem (baseIdealSheafOnSpec A I))).mapIso e).symm _ hq
  · refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨k⟩ := n
    have : IsIso (e.hom.hom.app (op k)) :=
      NatIso.isIso_app_of_isIso ((ObjectProperty.ι _).mapIso e).hom (op k)
    have hepi := epi_completionProjection (baseIdealSheafOnSpec A I) Gc k
    have hei : e.hom.hom.app (op k) ≫ e.inv.hom.app (op k) = 𝟙 _ :=
      congrArg (fun z : ((Stacks.Algebraization.completionFunctor (Spec (.of A))
        (baseIdealSheafOnSpec A I)).obj Gc).obj ⟶ ((Stacks.Algebraization.completionFunctor
          (Spec (.of A)) (baseIdealSheafOnSpec A I)).obj Gc).obj => z.app (op k))
        (ObjectProperty.isoHom_inv_id_hom e)
    have hmap := coherentAdicPullback_map_hom_app f (baseIdealSheafOnSpec A I) e.hom (op k)
    have hidk : (pullbackCompletionIso f (baseIdealSheafOnSpec A I) Gc).hom.hom.app (op k) ≫
        (pullbackCompletionIso f (baseIdealSheafOnSpec A I) Gc).inv.hom.app (op k) = 𝟙 _ :=
      congrArg (fun z : ((coherentAdicPullback f (baseIdealSheafOnSpec A I)).obj
          ((Stacks.Algebraization.completionFunctor (Spec (.of A))
            (baseIdealSheafOnSpec A I)).obj Gc)).obj ⟶ _ => z.app (op k))
        (ObjectProperty.isoHom_inv_id_hom (pullbackCompletionIso f
          (baseIdealSheafOnSpec A I) Gc))
    have step0 : ((Stacks.Algebraization.completionFunctor X
          ((baseIdealSheafOnSpec A I).comap f)).map b).hom.app (op k) =
        (pullbackCompletionIso f (baseIdealSheafOnSpec A I) Gc).inv.hom.app (op k) ≫
          (Scheme.Modules.pullback f).map (e.hom.hom.app (op k)) ≫ β.hom.hom.app (op k) := by
      rw [hb]
      exact congrArg (fun z => (pullbackCompletionIso f (baseIdealSheafOnSpec A I) Gc).inv.hom.app
        (op k) ≫ z ≫ β.hom.hom.app (op k)) hmap
    have hproj := pullbackCompletionIso_hom_app_projection f (baseIdealSheafOnSpec A I) Gc k
    have hstar : b.hom ≫ Stacks.Algebraization.completionProjection X
          ((baseIdealSheafOnSpec A I).comap f) ⟨F, inferInstance⟩ k =
        (Scheme.Modules.pullback f).map (Stacks.Algebraization.completionProjection
            (Spec (.of A)) (baseIdealSheafOnSpec A I) Gc k) ≫
          (Scheme.Modules.pullback f).map (e.hom.hom.app (op k)) ≫ β.hom.hom.app (op k) := by
      rw [← Stacks.Algebraization.completionFunctor_map_quotient X
        ((baseIdealSheafOnSpec A I).comap f) b k, step0, ← hproj]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z => (Scheme.Modules.pullback f).map
            (Stacks.Algebraization.completionProjection (Spec (.of A))
              (baseIdealSheafOnSpec A I) Gc k) ≫ z)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ ((Scheme.Modules.pullback f).map
                  (e.hom.hom.app (op k)) ≫ β.hom.hom.app (op k))) hidk).trans
              (Category.id_comp _))))
    have hunit₁ : e.hom.hom.app (op k) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj (op k)) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (((Stacks.Algebraization.completionFunctor (Spec (.of A))
              (baseIdealSheafOnSpec A I)).obj Gc).obj.obj (op k)) ≫
          (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
            (e.hom.hom.app (op k))) :=
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (e.hom.hom.app (op k))
    have hunit₂ : Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I) Gc k ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (((Stacks.Algebraization.completionFunctor (Spec (.of A))
            (baseIdealSheafOnSpec A I)).obj Gc).obj.obj (op k)) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj ≫
          (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
            (Stacks.Algebraization.completionProjection (Spec (.of A))
              (baseIdealSheafOnSpec A I) Gc k)) :=
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality
        (Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I) Gc k)
    have hquotk := Stacks.Algebraization.completionFunctor_map_quotient (Spec (.of A))
      (baseIdealSheafOnSpec A I) c₁ k
    have hcompk : Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I)
          (⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ :
            AlgebraicGeometry.SheafOfModules.CoherentModules (Spec (.of A)).ringCatSheaf) k ≫
        (pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F).app (op k) =
        (Scheme.Modules.pushforward f).map (Stacks.Algebraization.completionProjection X
          ((baseIdealSheafOnSpec A I).comap f) ⟨F, inferInstance⟩ k) :=
      pushforwardCompletionComponent_π f (baseIdealSheafOnSpec A I) F k
    have hA : e.hom.hom.app (op k) ≫ ((e.inv.hom.app (op k) ≫
          ((Stacks.Algebraization.completionFunctor (Spec (.of A))
            (baseIdealSheafOnSpec A I)).map c₁).hom.app (op k)) ≫
          (pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F).app (op k)) =
        ((Stacks.Algebraization.completionFunctor (Spec (.of A))
            (baseIdealSheafOnSpec A I)).map c₁).hom.app (op k) ≫
          (pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F).app (op k) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ (pushforwardCompletionComparison f
            (baseIdealSheafOnSpec A I) F).app (op k))
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ ((Stacks.Algebraization.completionFunctor (Spec (.of A))
                (baseIdealSheafOnSpec A I)).map c₁).hom.app (op k)) hei).trans
              (Category.id_comp _))))
    have hL : Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I) Gc k ≫ e.hom.hom.app (op k) ≫
        ((e.inv.hom.app (op k) ≫ ((Stacks.Algebraization.completionFunctor (Spec (.of A))
            (baseIdealSheafOnSpec A I)).map c₁).hom.app (op k)) ≫
          (pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F).app (op k)) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj ≫
          (Scheme.Modules.pushforward f).map (b.hom ≫
            Stacks.Algebraization.completionProjection X
              ((baseIdealSheafOnSpec A I).comap f) ⟨F, inferInstance⟩ k) :=
      (congrArg (fun z => Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I) Gc k ≫ z) hA).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (pushforwardCompletionComparison f
              (baseIdealSheafOnSpec A I) F).app (op k)) hquotk).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun z => c₁.hom ≫ z) hcompk).trans
                ((Category.assoc
                    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj)
                    ((Scheme.Modules.pushforward f).map b.hom) _).trans
                  (congrArg (fun z => (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                    Gc.obj ≫ z) (Functor.map_comp _ _ _).symm))))))
    have hB : e.hom.hom.app (op k) ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj (op k)) ≫
            (Scheme.Modules.pushforward f).map (β.hom.hom.app (op k))) =
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              (((Stacks.Algebraization.completionFunctor (Spec (.of A))
                (baseIdealSheafOnSpec A I)).obj Gc).obj.obj (op k)) ≫
            (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
              (e.hom.hom.app (op k)))) ≫
          (Scheme.Modules.pushforward f).map (β.hom.hom.app (op k)) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map (β.hom.hom.app (op k)))
          hunit₁)
    have hB₂ : Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I) Gc k ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              (((Stacks.Algebraization.completionFunctor (Spec (.of A))
                (baseIdealSheafOnSpec A I)).obj Gc).obj.obj (op k)) ≫
            (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
              (e.hom.hom.app (op k)))) =
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj ≫
            (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
              (Stacks.Algebraization.completionProjection (Spec (.of A))
                (baseIdealSheafOnSpec A I) Gc k))) ≫
          (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
            (e.hom.hom.app (op k))) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullback f).map (e.hom.hom.app (op k)))) hunit₂)
    have hC : ((Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
              (Stacks.Algebraization.completionProjection (Spec (.of A))
                (baseIdealSheafOnSpec A I) Gc k)) ≫
            (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
              (e.hom.hom.app (op k)))) ≫
          (Scheme.Modules.pushforward f).map (β.hom.hom.app (op k)) =
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
            (Stacks.Algebraization.completionProjection (Spec (.of A))
              (baseIdealSheafOnSpec A I) Gc k) ≫
          (Scheme.Modules.pullback f).map (e.hom.hom.app (op k)) ≫ β.hom.hom.app (op k)) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
              (Stacks.Algebraization.completionProjection (Spec (.of A))
                (baseIdealSheafOnSpec A I) Gc k)) ≫ z)
            (Functor.map_comp _ _ _).symm).trans (Functor.map_comp _ _ _).symm)
    have hR : Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I) Gc k ≫ e.hom.hom.app (op k) ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj (op k)) ≫
          (Scheme.Modules.pushforward f).map (β.hom.hom.app (op k))) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj ≫
          (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
              (Stacks.Algebraization.completionProjection (Spec (.of A))
                (baseIdealSheafOnSpec A I) Gc k) ≫
            (Scheme.Modules.pullback f).map (e.hom.hom.app (op k)) ≫
              β.hom.hom.app (op k)) :=
      (congrArg (fun z => Stacks.Algebraization.completionProjection (Spec (.of A))
          (baseIdealSheafOnSpec A I) Gc k ≫ z) hB).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map
              (β.hom.hom.app (op k))) hB₂).trans
            ((congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map
                (β.hom.hom.app (op k))) (Category.assoc _ _ _)).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun z => (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                  Gc.obj ≫ z) hC)))))
    apply (cancel_epi (e.hom.hom.app (op k))).mp
    apply (cancel_epi (C := (Spec (.of A)).Modules)
      (Stacks.Algebraization.completionProjection (Spec (.of A))
        (baseIdealSheafOnSpec A I) Gc k)).mp
    exact (hL.trans (congrArg (fun z =>
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Gc.obj ≫
        (Scheme.Modules.pushforward f).map z) hstar)).trans hR.symm

/-! ### Uniqueness of the comparison map, and the bound -/

/-- **A morphism into the completion of a proper direct image over a complete affine base is
determined by its composite with the comparison map `(f_*𝓕)^ ⟶ f_*(𝓕^)`.**

No form of the theorem on formal functions is used. Over a complete base the source is a
completion `𝒢^`, and completion is full on `Spec A`, so both morphisms are completions of
morphisms `𝒢 ⟶ f_*𝓕`; the hypothesis says that the two become equal after composing with the
direct images of the projections `𝓕 ⟶ 𝓕/ℐ ⁿ⁺¹𝓕`, hence — by the adjunction `f^* ⊣ f_*` — that
their adjoint transposes `f^*𝒢 ⟶ 𝓕` have equal completions, and completion is faithful on `X`
by [Stacks, Tag 0883]. -/
public theorem systemMap_unique_pushforwardCompletionComparison_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (G : CoherentAdicSystems (baseIdealSheafOnSpec A I))
    (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    ∀ a b : G ⟶ (Stacks.Algebraization.completionFunctor (Spec (.of A))
        (baseIdealSheafOnSpec A I)).obj
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩,
      a.hom ≫ pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F =
        b.hom ≫ pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F → a = b := by
  intro a b hab
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  let : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
  obtain ⟨Gc, ⟨e⟩⟩ := essImage_completionFunctor_baseIdealSheafOnSpec A I G
  have := Gc.property
  obtain ⟨hFFX⟩ := nonempty_fullyFaithful_completionFunctor_comap A I f
  obtain ⟨hFFY⟩ : Nonempty (Stacks.Algebraization.completionFunctor (Spec (.of A))
      (baseIdealSheafOnSpec A I)).FullyFaithful := by
    have := nonempty_fullyFaithful_completionFunctor_comap A I (𝟙 (Spec (.of A)))
    rwa [Scheme.IdealSheafData.comap_id] at this
  have := hFFX.faithful
  let ca := hFFY.preimage (e.hom ≫ a)
  let cb := hFFY.preimage (e.hom ≫ b)
  have hca : (Stacks.Algebraization.completionFunctor (Spec (.of A))
      (baseIdealSheafOnSpec A I)).map ca = e.hom ≫ a := hFFY.map_preimage _
  have hcb : (Stacks.Algebraization.completionFunctor (Spec (.of A))
      (baseIdealSheafOnSpec A I)).map cb = e.hom ≫ b := hFFY.map_preimage _
  have h1 : ((Stacks.Algebraization.completionFunctor (Spec (.of A))
        (baseIdealSheafOnSpec A I)).map ca).hom ≫
      pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F =
      ((Stacks.Algebraization.completionFunctor (Spec (.of A))
        (baseIdealSheafOnSpec A I)).map cb).hom ≫
      pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F := by
    rw [hca, hcb]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => e.hom.hom ≫ z) hab).trans (Category.assoc _ _ _).symm)
  have key : ∀ n : ℕ, ca.hom ≫ (Scheme.Modules.pushforward f).map
        (Stacks.Algebraization.completionProjection X
          ((baseIdealSheafOnSpec A I).comap f) ⟨F, inferInstance⟩ n) =
      cb.hom ≫ (Scheme.Modules.pushforward f).map
        (Stacks.Algebraization.completionProjection X
          ((baseIdealSheafOnSpec A I).comap f) ⟨F, inferInstance⟩ n) := by
    intro n
    have hcompk := pushforwardCompletionComponent_π f (baseIdealSheafOnSpec A I) F n
    have hn := congrArg (fun z : ((Stacks.Algebraization.completionFunctor (Spec (.of A))
      (baseIdealSheafOnSpec A I)).obj Gc).obj ⟶ _ => z.app (op n)) h1
    have hqa := Stacks.Algebraization.completionFunctor_map_quotient (Spec (.of A))
      (baseIdealSheafOnSpec A I) ca n
    have hqb := Stacks.Algebraization.completionFunctor_map_quotient (Spec (.of A))
      (baseIdealSheafOnSpec A I) cb n
    exact (congrArg (fun z => ca.hom ≫ z) hcompk.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (pushforwardCompletionComparison f
            (baseIdealSheafOnSpec A I) F).app (op n)) hqa.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => Stacks.Algebraization.completionProjection (Spec (.of A))
                (baseIdealSheafOnSpec A I) Gc n ≫ z) hn).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun z => z ≫ (pushforwardCompletionComparison f
                    (baseIdealSheafOnSpec A I) F).app (op n)) hqb).trans
                  ((Category.assoc _ _ _).trans
                    (congrArg (fun z => cb.hom ≫ z) hcompk))))))))
  have hadj : ∀ n : ℕ,
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv Gc.obj F).symm ca.hom ≫
        Stacks.Algebraization.completionProjection X ((baseIdealSheafOnSpec A I).comap f)
          ⟨F, inferInstance⟩ n =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv Gc.obj F).symm cb.hom ≫
        Stacks.Algebraization.completionProjection X ((baseIdealSheafOnSpec A I).comap f)
          ⟨F, inferInstance⟩ n := by
    intro n
    have ha' := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
      ca.hom (Stacks.Algebraization.completionProjection X
        ((baseIdealSheafOnSpec A I).comap f) ⟨F, inferInstance⟩ n)
    have hb' := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
      cb.hom (Stacks.Algebraization.completionProjection X
        ((baseIdealSheafOnSpec A I).comap f) ⟨F, inferInstance⟩ n)
    exact ha'.symm.trans ((congrArg (fun z =>
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv Gc.obj _).symm z)
      (key n)).trans hb')
  let ba : (⟨(Scheme.Modules.pullback f).obj Gc.obj,
        AlgebraicGeometry.isCoherent_pullback f Gc.obj⟩ :
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ⟶
      ⟨F, inferInstance⟩ :=
    ObjectProperty.homMk (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      Gc.obj F).symm ca.hom)
  let bb : (⟨(Scheme.Modules.pullback f).obj Gc.obj,
        AlgebraicGeometry.isCoherent_pullback f Gc.obj⟩ :
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ⟶
      ⟨F, inferInstance⟩ :=
    ObjectProperty.homMk (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      Gc.obj F).symm cb.hom)
  have hmapeq : (Stacks.Algebraization.completionFunctor X
        ((baseIdealSheafOnSpec A I).comap f)).map ba =
      (Stacks.Algebraization.completionFunctor X
        ((baseIdealSheafOnSpec A I).comap f)).map bb := by
    apply ObjectProperty.hom_ext
    refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨k⟩ := n
    have := epi_completionProjection ((baseIdealSheafOnSpec A I).comap f)
      (⟨(Scheme.Modules.pullback f).obj Gc.obj,
          AlgebraicGeometry.isCoherent_pullback f Gc.obj⟩ :
        AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) k
    refine (cancel_epi (C := X.Modules) (Stacks.Algebraization.completionProjection X
      ((baseIdealSheafOnSpec A I).comap f)
      (⟨(Scheme.Modules.pullback f).obj Gc.obj,
          AlgebraicGeometry.isCoherent_pullback f Gc.obj⟩ :
        AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) k)).mp ?_
    exact (Stacks.Algebraization.completionFunctor_map_quotient X
        ((baseIdealSheafOnSpec A I).comap f) ba k).trans
      ((hadj k).trans (Stacks.Algebraization.completionFunctor_map_quotient X
        ((baseIdealSheafOnSpec A I).comap f) bb k).symm)
  have hbaeq : ba = bb := (Stacks.Algebraization.completionFunctor X
    ((baseIdealSheafOnSpec A I).comap f)).map_injective hmapeq
  have hxeq : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv Gc.obj F).symm
        ca.hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv Gc.obj F).symm cb.hom :=
    congrArg (fun z : (⟨(Scheme.Modules.pullback f).obj Gc.obj,
        AlgebraicGeometry.isCoherent_pullback f Gc.obj⟩ :
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ⟶
      ⟨F, inferInstance⟩ => z.hom) hbaeq
  have hcaeq : ca = cb := by
    apply ObjectProperty.hom_ext
    exact ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv Gc.obj F).symm.injective
      hxeq
  refine (Iso.cancel_iso_hom_left e a b).mp ?_
  rw [← hca, ← hcb, hcaeq]

/-- **The kernel–cokernel bound of Stacks 088B over a complete affine base.** Let `A` be a
Noetherian ring complete for an ideal `I`, let `f : X ⟶ Spec A` be proper, let
`𝒦 ⊆ 𝒪_{Spec A}` be a quasi-coherent sheaf of ideals such that `f` is an isomorphism over
`Spec A ∖ V(𝒦)`, let `(𝒢_n)` be a coherent `I 𝒪_{Spec A}`-adic system, let `𝓕` be a coherent
`𝒪_X`-module and let `β : (f^*𝒢_n) ≅ 𝓕^` be an isomorphism in `Coh(X, I 𝒪_X)`. Then the
levelwise kernels and cokernels of the comparison map `α : (𝒢_n) ⟶ (f_*𝓕)^` are annihilated by
one power of `𝒦`.

The map `α` is given by the equation that characterises it: its composite with the comparison
`(f_*𝓕)^ ⟶ f_*(𝓕^)` is the morphism `γ` of
`Stacks.Coherent.directImageComparison`. That equation determines `α`
(`Stacks.Coherent.systemMap_unique_pushforwardCompletionComparison_of_isAdicComplete`), so the
bound follows from the one for the map constructed in
`Stacks.Coherent.exists_systemMap_isKernelCokernelAnnihilatedByPower_of_isAdicComplete`. -/
public theorem isKernelCokernelAnnihilatedByPower_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (K : (Spec (.of A)).IdealSheafData)
    (hf : IsIso (f ∣_ K.support.compl))
    (G : CoherentAdicSystems (baseIdealSheafOnSpec A I))
    (F : X.Modules) [F.IsCoherent] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    letI : ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
      AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F
    ∀ (β : (coherentAdicPullback f (baseIdealSheafOnSpec A I)).obj G ≅
        (Stacks.Algebraization.completionFunctor X
          ((baseIdealSheafOnSpec A I).comap f)).obj ⟨F, inferInstance⟩)
      (α : G ⟶ (Stacks.Algebraization.completionFunctor (Spec (.of A))
        (baseIdealSheafOnSpec A I)).obj
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩),
      α.hom ≫ pushforwardCompletionComparison f (baseIdealSheafOnSpec A I) F =
          directImageComparison f (baseIdealSheafOnSpec A I) G ⟨F, inferInstance⟩ β →
        Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower K α.hom := by
  intro β α hα
  obtain ⟨a, ha, hac⟩ :=
    exists_systemMap_isKernelCokernelAnnihilatedByPower_of_isAdicComplete A I f K hf G F β
  obtain rfl : α = a :=
    systemMap_unique_pushforwardCompletionComparison_of_isAdicComplete A I f G F α a
      (hα.trans hac.symm)
  exact ha

end Stacks.Coherent

end
