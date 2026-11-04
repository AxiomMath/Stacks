module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ClosedPushforward

/-!
# Completion is fully faithful on modules annihilated by the ideal of a closed subscheme

Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes with ideal sheaf `𝒥 = ker(i^♯)`, and
let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. If completion along `ℐ_Z = ℐ 𝒪_Z` is an
equivalence `Coh(𝒪_Z) ⥤ Coh(Z, ℐ_Z)` — hypothesis (1) of [Stacks, Tag 088A] read through the
closed-immersion equivalence of Tag 087T — then completion along `ℐ` is fully faithful on the
coherent `𝒪_X`-modules annihilated by `𝒥`, and reflects isomorphisms between them.

This is the step of the proof of Tag 088A at which the successive algebraizations
`G_e` of `(F_n / 𝒦 ᵉ⁺¹ F_n)` are compared: the identification
`G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ≅ G_e` cannot be read off the completions directly, because the
completion functor on all of `Coh(𝒪_X)` is not known to be full; it is full on the
`𝒦`-power-annihilated part, which is all the proof needs.

Everything rests on one square. For a coherent `M` annihilated by `𝒥` the adjunction unit
`M ⟶ i_* i^* M` is invertible ([Stacks, Tag 08KS]), and direct image commutes with completion
(`Stacks.Coherent.completionPushforwardIso`), so

`(M) ^∧_ℐ ≅ i_* ((i^* M) ^∧_{ℐ_Z})`

naturally in `M`. On the right-hand side `i^*` is fully faithful on the annihilated part (again
08KS), completion along `ℐ_Z` is fully faithful by hypothesis, and termwise direct image is
fully faithful because `i_*` is; so the left-hand side is fully faithful too.

## Main definitions

* `Stacks.Coherent.coherentPullback` — inverse image as a functor `Coh(𝒪_X) ⥤ Coh(𝒪_Z)`.
* `Stacks.Coherent.completionAnnihilatedPushforwardIso` — the square above.

## Main results

* `Stacks.Coherent.exists_unique_completion_preimage_of_annihilated` — **completion along `ℐ` is
  fully faithful on the coherent modules annihilated by the ideal of `Z`.**
* `Stacks.Coherent.completion_map_injective_of_annihilated` — the faithfulness half on its own.
* `Stacks.Coherent.isIso_of_isIso_completion_map_of_annihilated` — **completion reflects
  isomorphisms between coherent modules annihilated by the ideal of `Z`.**

## Implementation notes

The square is proved by composing with the completion projections, which are epimorphisms
(`Stacks.Algebraization.epi_completionProjection`); the normalizations used are
`Stacks.Algebraization.completionFunctor_map_quotient` for the completion functor and
`Stacks.Coherent.completionPushforwardIso_completionProjection` for the direct-image comparison.

`Coh(X, ℐ)` and `Coh(𝒪_X)` are full subcategories, so a morphism of either is a morphism of the
underlying object together with no data; `CategoryTheory.ObjectProperty.homMk`,
`CategoryTheory.ObjectProperty.hom_ext` and `CategoryTheory.ObjectProperty.isoMk` move between
the two spellings.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### Inverse image on coherent modules -/

/-- **Inverse image as a functor `Coh(𝒪_X) ⥤ Coh(𝒪_Z)`.** The pullback of a coherent module
along a morphism with locally Noetherian source is coherent, which is [Stacks, Tag 0EBF]. -/
public def coherentPullback [IsLocallyNoetherian Z] :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback i)
    fun M => AlgebraicGeometry.isCoherent_pullback i M.obj

omit [IsClosedImmersion i] in
/-- The underlying module of the inverse image is the inverse image of the underlying module. -/
public theorem coherentPullback_obj_obj [IsLocallyNoetherian Z]
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((coherentPullback i).obj M).obj = (Scheme.Modules.pullback i).obj M.obj := rfl

omit [IsClosedImmersion i] in
/-- The inverse image functor acts on morphisms by inverse image. -/
public theorem coherentPullback_map_hom [IsLocallyNoetherian Z]
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : M ⟶ N) :
    ((coherentPullback i).map f).hom = (Scheme.Modules.pullback i).map f.hom := rfl

/-! ### The unit at an annihilated module -/

/-- **[Stacks, Tag 08KS] in the form the proof of Tag 088A uses it.** If `𝒥 M = 0` for the ideal
sheaf `𝒥` cutting out `Z`, then the adjunction unit `M ⟶ i_* i^* M` is an isomorphism. -/
public theorem isIso_unit_app_of_idealPowerMultiple_ker_eq_bot (M : X.Modules)
    (hM : idealPowerMultiple i.ker 1 M = ⊥) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) := by
  refine Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i M ?_
  refine (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal i _).mpr fun U a ha m => ?_
  exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot hM U
    (by rw [pow_one]; exact ha) m

/-- **Inverse image is fully faithful on the annihilated part**, faithfulness half: a morphism
of coherent `𝒪_X`-modules annihilated by the ideal of `Z` is determined by its inverse image. -/
public theorem pullback_map_injective_of_annihilated {M N : X.Modules}
    (hM : idealPowerMultiple i.ker 1 M = ⊥) (hN : idealPowerMultiple i.ker 1 N = ⊥)
    {f g : M ⟶ N}
    (h : (Scheme.Modules.pullback i).map f = (Scheme.Modules.pullback i).map g) : f = g := by
  have := isIso_unit_app_of_idealPowerMultiple_ker_eq_bot i M hM
  have := isIso_unit_app_of_idealPowerMultiple_ker_eq_bot i N hN
  have hf := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality f
  have hg := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality g
  refine (cancel_mono ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N)).1 ?_
  dsimp only [Functor.id_map, Functor.comp_map] at hf hg
  rw [hf, hg, h]

/-- **Inverse image is fully faithful on the annihilated part**, fullness half: every morphism
`i^* M ⟶ i^* N` is the inverse image of a morphism `M ⟶ N`, when both `M` and `N` are
annihilated by the ideal of `Z`.

The preimage is the conjugate `η_M ≫ i_* g ≫ η_N ⁻¹` of `g` by the adjunction units, which are
invertible by [Stacks, Tag 08KS]; that it has the right inverse image is naturality of the unit
together with faithfulness of `i_*`. -/
public theorem exists_pullback_map_eq_of_annihilated {M N : X.Modules}
    (hM : idealPowerMultiple i.ker 1 M = ⊥) (hN : idealPowerMultiple i.ker 1 N = ⊥)
    (g : (Scheme.Modules.pullback i).obj M ⟶ (Scheme.Modules.pullback i).obj N) :
    ∃ f : M ⟶ N, (Scheme.Modules.pullback i).map f = g := by
  have := isIso_unit_app_of_idealPowerMultiple_ker_eq_bot i M hM
  have := isIso_unit_app_of_idealPowerMultiple_ker_eq_bot i N hN
  have := Stacks.ClosedImmersion.faithful_pushforward i
  refine ⟨(Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M ≫
    (Scheme.Modules.pushforward i).map g ≫
      inv ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N), ?_⟩
  refine (Scheme.Modules.pushforward i).map_injective ?_
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M ≫
      (Scheme.Modules.pushforward i).map g ≫
        inv ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj] at hnat
  refine (cancel_epi ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)).1 ?_
  rw [← hnat, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-! ### The square -/

/-- The direct image of the inverse image of a coherent module, as a coherent module. -/
public abbrev pushforwardCoherentPullback [IsLocallyNoetherian X]
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  ⟨(Scheme.Modules.pushforward i).obj ((coherentPullback i).obj M).obj,
    isCoherent_pushforward_of_isClosedImmersion i ((coherentPullback i).obj M).obj⟩

/-- The adjunction unit as an isomorphism of coherent modules, at a module annihilated by the
ideal sheaf cutting out `Z`. -/
public def coherentUnitIso [IsLocallyNoetherian X]
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : idealPowerMultiple i.ker 1 M.obj = ⊥) :
    M ≅ pushforwardCoherentPullback i M :=
  ObjectProperty.isoMk _
    (@asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj)
      (isIso_unit_app_of_idealPowerMultiple_ker_eq_bot i M.obj hM))

/-- **Completion of an annihilated coherent module is the direct image of the completion of its
inverse image.** For a coherent `𝒪_X`-module `M` annihilated by the ideal sheaf cutting out `Z`,

`(M) ^∧_ℐ ≅ i_* ((i^* M) ^∧_{ℐ 𝒪_Z})`.

The unit `M ⟶ i_* i^* M` is invertible by [Stacks, Tag 08KS], and direct image commutes with
completion by `Stacks.Coherent.completionPushforwardIso`. -/
public def completionAnnihilatedPushforwardIso [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : idealPowerMultiple i.ker 1 M.obj = ⊥) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    ((completionFunctor X I).obj M).obj ≅
      ((completionFunctor Z (I.comap i)).obj ((coherentPullback i).obj M)).obj ⋙
        Scheme.Modules.pushforward i :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  (ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso
      ((completionFunctor X I).mapIso (coherentUnitIso i M hM)) ≪≫
    completionPushforwardIso i I ((coherentPullback i).obj M)
      (isCoherent_pushforward_of_isClosedImmersion i ((coherentPullback i).obj M).obj)

/-- **The square is normalized by the completion projections.** -/
public theorem completionAnnihilatedPushforwardIso_completionProjection [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : idealPowerMultiple i.ker 1 M.obj = ⊥) (n : ℕ) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    completionProjection X I M n ≫
        (completionAnnihilatedPushforwardIso i I M hM).hom.app (op n) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫
        (Scheme.Modules.pushforward i).map
          (completionProjection Z (I.comap i) ((coherentPullback i).obj M) n) := by
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  show completionProjection X I M n ≫
      ((completionFunctor X I).map (coherentUnitIso i M hM).hom).hom.app (op n) ≫
        (completionPushforwardIso i I ((coherentPullback i).obj M)
          (isCoherent_pushforward_of_isClosedImmersion i
            ((coherentPullback i).obj M).obj)).hom.app (op n) = _
  have h1 := completionFunctor_map_quotient X I (coherentUnitIso i M hM).hom n
  have h2 := completionPushforwardIso_completionProjection i I ((coherentPullback i).obj M)
    (isCoherent_pushforward_of_isClosedImmersion i ((coherentPullback i).obj M).obj) n
  refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
    (completionPushforwardIso i I ((coherentPullback i).obj M)
      (isCoherent_pushforward_of_isClosedImmersion i
        ((coherentPullback i).obj M).obj)).hom.app (op n)) h1) ?_
  refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
  exact congrArg (fun z => (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫ z) h2

/-- **The square is natural in the module.** -/
public theorem completionAnnihilatedPushforwardIso_naturality [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (hM : idealPowerMultiple i.ker 1 M.obj = ⊥) (hN : idealPowerMultiple i.ker 1 N.obj = ⊥)
    (f : M ⟶ N) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    ((completionFunctor X I).map f).hom ≫
        (completionAnnihilatedPushforwardIso i I N hN).hom =
      (completionAnnihilatedPushforwardIso i I M hM).hom ≫
        Functor.whiskerRight
          ((completionFunctor Z (I.comap i)).map ((coherentPullback i).map f)).hom
          (Scheme.Modules.pushforward i) := by
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  refine NatTrans.ext (funext fun n => ?_)
  refine (Stacks.Algebraization.epi_completionProjection X I M n.unop).left_cancellation
    _ _ ?_
  have hnat : f.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N.obj =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map f.hom) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality f.hom
  have hM' := completionAnnihilatedPushforwardIso_completionProjection i I M hM n.unop
  have hN' := completionAnnihilatedPushforwardIso_completionProjection i I N hN n.unop
  have hq := completionFunctor_map_quotient X I f n.unop
  have hq' := completionFunctor_map_quotient Z (I.comap i) ((coherentPullback i).map f) n.unop
  show completionProjection X I M n.unop ≫
      ((completionFunctor X I).map f).hom.app (op n.unop) ≫
        (completionAnnihilatedPushforwardIso i I N hN).hom.app (op n.unop) =
    completionProjection X I M n.unop ≫
      (completionAnnihilatedPushforwardIso i I M hM).hom.app (op n.unop) ≫
        (Scheme.Modules.pushforward i).map
          (((completionFunctor Z (I.comap i)).map ((coherentPullback i).map f)).hom.app (op n.unop))
  have left : completionProjection X I M n.unop ≫
      ((completionFunctor X I).map f).hom.app (op n.unop) ≫
        (completionAnnihilatedPushforwardIso i I N hN).hom.app (op n.unop) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map f.hom) ≫
          (Scheme.Modules.pushforward i).map
            (completionProjection Z (I.comap i) ((coherentPullback i).obj N) n.unop) := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫
      (completionAnnihilatedPushforwardIso i I N hN).hom.app (op n.unop)) hq) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => f.hom ≫ z) hN') ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ (Scheme.Modules.pushforward i).map
      (completionProjection Z (I.comap i) ((coherentPullback i).obj N) n.unop)) hnat) ?_
    exact Category.assoc (obj := X.Modules) _ _ _
  have right : completionProjection X I M n.unop ≫
      (completionAnnihilatedPushforwardIso i I M hM).hom.app (op n.unop) ≫
        (Scheme.Modules.pushforward i).map
          (((completionFunctor Z (I.comap i)).map
            ((coherentPullback i).map f)).hom.app (op n.unop)) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map f.hom) ≫
          (Scheme.Modules.pushforward i).map
            (completionProjection Z (I.comap i) ((coherentPullback i).obj N) n.unop) := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ (Scheme.Modules.pushforward i).map
      (((completionFunctor Z (I.comap i)).map
        ((coherentPullback i).map f)).hom.app (op n.unop))) hM') ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg
      (fun z => (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫ z)
      ((Scheme.Modules.pushforward i).map_comp _ _).symm) ?_
    refine Eq.trans (congrArg
      (fun z => (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫
        (Scheme.Modules.pushforward i).map z) hq') ?_
    exact congrArg
      (fun z => (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M.obj ≫ z)
      ((Scheme.Modules.pushforward i).map_comp _ _)
  exact left.trans right.symm

/-! ### Full faithfulness -/

/-- **Completion along `ℐ` is fully faithful on the coherent modules annihilated by the ideal
sheaf cutting out `Z`**, as soon as completion along `ℐ 𝒪_Z` is an equivalence on `Coh(𝒪_Z)`.

This is the form in which hypothesis (1) of [Stacks, Tag 088A] is consumed: it is what lets the
successive algebraizations of the reductions `(F_n / 𝒦 ᵉ⁺¹ F_n)` be compared with one another,
the completion functor on all of `Coh(𝒪_X)` not being known to be full.

The three fully faithful functors the proof composes are inverse image on the annihilated part
(`Stacks.Coherent.pullback_map_injective_of_annihilated` and
`Stacks.Coherent.exists_pullback_map_eq_of_annihilated`, both forms of [Stacks, Tag 08KS]),
completion along `ℐ 𝒪_Z`, which is an equivalence by hypothesis, and termwise direct image,
fully faithful because `i_*` is. -/
public theorem exists_unique_completion_preimage_of_annihilated [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (h : letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
      (completionFunctor Z (I.comap i)).IsEquivalence)
    (M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : idealPowerMultiple i.ker 1 M.obj = ⊥) (hN : idealPowerMultiple i.ker 1 N.obj = ⊥)
    (φ : (completionFunctor X I).obj M ⟶ (completionFunctor X I).obj N) :
    ∃! ψ : M ⟶ N, (completionFunctor X I).map ψ = φ := by
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have := h
  have := Stacks.ClosedImmersion.faithful_pushforward i
  have := Stacks.ClosedImmersion.full_pushforward i
  let W := (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj
    (Scheme.Modules.pushforward i)
  have hinj : ∀ ψ ψ' : M ⟶ N, (completionFunctor X I).map ψ =
      (completionFunctor X I).map ψ' → ψ = ψ' := by
    intro ψ ψ' hψ
    have hw : Functor.whiskerRight
          ((completionFunctor Z (I.comap i)).map ((coherentPullback i).map ψ)).hom
          (Scheme.Modules.pushforward i) =
        Functor.whiskerRight
          ((completionFunctor Z (I.comap i)).map ((coherentPullback i).map ψ')).hom
          (Scheme.Modules.pushforward i) := by
      refine (cancel_epi (completionAnnihilatedPushforwardIso i I M hM).hom).1 ?_
      rw [← completionAnnihilatedPushforwardIso_naturality i I hM hN ψ,
        ← completionAnnihilatedPushforwardIso_naturality i I hM hN ψ', hψ]
    have hp : (coherentPullback i).map ψ = (coherentPullback i).map ψ' :=
      (completionFunctor Z (I.comap i)).map_injective
        (ObjectProperty.hom_ext _ (W.map_injective hw))
    exact ObjectProperty.hom_ext _ (pullback_map_injective_of_annihilated i hM hN
      (congrArg (fun g : (coherentPullback i).obj M ⟶ (coherentPullback i).obj N => g.hom) hp))
  obtain ⟨γ, hγ⟩ : ∃ γ : ((completionFunctor Z (I.comap i)).obj
        ((coherentPullback i).obj M)).obj ⟶
      ((completionFunctor Z (I.comap i)).obj ((coherentPullback i).obj N)).obj,
      Functor.whiskerRight γ (Scheme.Modules.pushforward i) =
        (completionAnnihilatedPushforwardIso i I M hM).inv ≫ φ.hom ≫
          (completionAnnihilatedPushforwardIso i I N hN).hom :=
    ⟨W.preimage _, W.map_preimage _⟩
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : (coherentPullback i).obj M ⟶ (coherentPullback i).obj N,
      (completionFunctor Z (I.comap i)).map ψ₀ = ObjectProperty.homMk γ :=
    ⟨(completionFunctor Z (I.comap i)).preimage _, Functor.map_preimage _ _⟩
  obtain ⟨f, hf⟩ := exists_pullback_map_eq_of_annihilated i hM hN ψ₀.hom
  have hpf : (coherentPullback i).map (ObjectProperty.homMk f : M ⟶ N) = ψ₀ :=
    ObjectProperty.hom_ext _ hf
  have key : (completionFunctor X I).map (ObjectProperty.homMk f : M ⟶ N) = φ := by
    refine ObjectProperty.hom_ext _ ?_
    refine (cancel_mono (completionAnnihilatedPushforwardIso i I N hN).hom).1 ?_
    rw [completionAnnihilatedPushforwardIso_naturality i I hM hN, hpf, hψ₀]
    show (completionAnnihilatedPushforwardIso i I M hM).hom ≫
      Functor.whiskerRight γ (Scheme.Modules.pushforward i) = _
    rw [hγ, Iso.hom_inv_id_assoc]
  exact ⟨ObjectProperty.homMk f, key, fun ψ' hψ' => hinj ψ' _ (hψ'.trans key.symm)⟩

/-- **Faithfulness on the annihilated part**, on its own: two morphisms of coherent modules
annihilated by the ideal sheaf cutting out `Z` with the same completion are equal. -/
public theorem completion_map_injective_of_annihilated [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (h : letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
      (completionFunctor Z (I.comap i)).IsEquivalence)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (hM : idealPowerMultiple i.ker 1 M.obj = ⊥) (hN : idealPowerMultiple i.ker 1 N.obj = ⊥)
    {ψ ψ' : M ⟶ N}
    (hψ : (completionFunctor X I).map ψ = (completionFunctor X I).map ψ') : ψ = ψ' := by
  obtain ⟨w, -, huniq⟩ := exists_unique_completion_preimage_of_annihilated i I h M N hM hN
    ((completionFunctor X I).map ψ')
  exact (huniq ψ hψ).trans (huniq ψ' rfl).symm

/-- **Completion reflects isomorphisms between coherent modules annihilated by the ideal sheaf
cutting out `Z`.** This is the clause the assembly of [Stacks, Tag 088A] consumes: the
identification `G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ≅ G_e` is produced by exhibiting a morphism whose
completion is invertible. -/
public theorem isIso_of_isIso_completion_map_of_annihilated [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (h : letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
      (completionFunctor Z (I.comap i)).IsEquivalence)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (hM : idealPowerMultiple i.ker 1 M.obj = ⊥) (hN : idealPowerMultiple i.ker 1 N.obj = ⊥)
    (ψ : M ⟶ N) [IsIso ((completionFunctor X I).map ψ)] : IsIso ψ := by
  obtain ⟨χ, hχ, -⟩ := exists_unique_completion_preimage_of_annihilated i I h N M hN hM
    (inv ((completionFunctor X I).map ψ))
  refine ⟨χ, ?_, ?_⟩
  · refine completion_map_injective_of_annihilated i I h hM hM ?_
    rw [(completionFunctor X I).map_comp, hχ, IsIso.hom_inv_id]
    exact ((completionFunctor X I).map_id M).symm
  · refine completion_map_injective_of_annihilated i I h hN hN ?_
    rw [(completionFunctor X I).map_comp, hχ, IsIso.inv_hom_id]
    exact ((completionFunctor X I).map_id N).symm

/-! ### The form used at a power of a second ideal -/

/-- Dividing by the first power of `𝒦 ʳ` is dividing by the `r`-th power of `𝒦`. -/
public theorem idealPowerMultiple_pow_one (K : X.IdealSheafData) (r : ℕ)
    (M : X.Modules) : idealPowerMultiple (K ^ r) 1 M = idealPowerMultiple K r M :=
  le_antisymm (idealPowerMultiple_le_of_pow_le (pow_one (K ^ r)).le M)
    (idealPowerMultiple_le_of_pow_le (pow_one (K ^ r)).ge M)

/-- A module annihilated by `𝒦 ᵉ⁺¹` is annihilated by the ideal sheaf of `V(𝒦 ᵉ⁺¹) ⟶ X`. -/
private theorem idealPowerMultiple_ker_subschemeι_eq_bot (K : X.IdealSheafData) (e : ℕ)
    (M : X.Modules) (hM : idealPowerMultiple K (e + 1) M = ⊥) :
    idealPowerMultiple (K ^ (e + 1)).subschemeι.ker 1 M = ⊥ := by
  rw [Scheme.IdealSheafData.ker_subschemeι, idealPowerMultiple_pow_one, hM]

/-- **Completion along `ℐ` is fully faithful on the coherent modules annihilated by `𝒦 ᵉ⁺¹`**,
granted hypothesis (1) of [Stacks, Tag 088A] at the level `e`.

This is `Stacks.Coherent.exists_unique_completion_preimage_of_annihilated` for the closed
immersion `V(𝒦 ᵉ⁺¹) ⟶ X`, whose ideal sheaf is `𝒦 ᵉ⁺¹`. -/
public theorem exists_unique_completion_preimage_of_power_annihilated [IsLocallyNoetherian X]
    (I K : X.IdealSheafData) (e : ℕ)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    (M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : idealPowerMultiple K (e + 1) M.obj = ⊥)
    (hN : idealPowerMultiple K (e + 1) N.obj = ⊥)
    (phi : (completionFunctor X I).obj M ⟶ (completionFunctor X I).obj N) :
    ∃! psi : M ⟶ N, (completionFunctor X I).map psi = phi := by
  refine exists_unique_completion_preimage_of_annihilated (K ^ (e + 1)).subschemeι I h M N
    ?_ ?_ phi
  · exact idealPowerMultiple_ker_subschemeι_eq_bot K e _ hM
  · exact idealPowerMultiple_ker_subschemeι_eq_bot K e _ hN

/-- **Faithfulness on the `𝒦 ᵉ⁺¹`-annihilated part**, on its own. -/
public theorem completion_map_injective_of_power_annihilated [IsLocallyNoetherian X]
    (I K : X.IdealSheafData) (e : ℕ)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (hM : idealPowerMultiple K (e + 1) M.obj = ⊥)
    (hN : idealPowerMultiple K (e + 1) N.obj = ⊥) {psi psi' : M ⟶ N}
    (hpsi : (completionFunctor X I).map psi = (completionFunctor X I).map psi') : psi = psi' := by
  obtain ⟨w, -, huniq⟩ := exists_unique_completion_preimage_of_power_annihilated I K e h M N
    hM hN ((completionFunctor X I).map psi')
  exact (huniq psi hpsi).trans (huniq psi' rfl).symm

/-- **Completion reflects isomorphisms between coherent modules annihilated by `𝒦 ᵉ⁺¹`.**

This is what produces the successor identifications `G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ≅ G_e` of the proof
of [Stacks, Tag 088A] out of isomorphisms of their completions. -/
public theorem isIso_of_isIso_completion_map_of_power_annihilated [IsLocallyNoetherian X]
    (I K : X.IdealSheafData) (e : ℕ)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    {M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (hM : idealPowerMultiple K (e + 1) M.obj = ⊥)
    (hN : idealPowerMultiple K (e + 1) N.obj = ⊥)
    (psi : M ⟶ N) [IsIso ((completionFunctor X I).map psi)] : IsIso psi := by
  refine isIso_of_isIso_completion_map_of_annihilated (K ^ (e + 1)).subschemeι I h ?_ ?_ psi
  · exact idealPowerMultiple_ker_subschemeι_eq_bot K e _ hM
  · exact idealPowerMultiple_ker_subschemeι_eq_bot K e _ hN

end Stacks.Coherent

end
