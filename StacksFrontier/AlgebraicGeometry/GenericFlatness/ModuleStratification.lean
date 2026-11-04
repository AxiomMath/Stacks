module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic

/-!
# The generic flatness stratification over a Noetherian base

Let `f : X ⟶ S` be a morphism of finite presentation with `S` Noetherian, and let `ℱ` be an
`𝒪_X`-module of finite presentation. Then there is a finite descending chain of closed
subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of the base, each cut out by an ideal sheaf of finite type,
with `S₀ ⊆ S` a thickening, such that the pullback of `ℱ` to `X ×_S (S_i ∖ S_{i+1})` is flat over
the locally closed stratum `S_i ∖ S_{i+1}`.

This is the Noetherian case of [Stacks, Tag 0ASY], which is the case to which the general
statement reduces by absolute Noetherian approximation; the structure-sheaf case of the
conclusion is `AlgebraicGeometry.HasFlatStratification`.

## Main results

* `AlgebraicGeometry.exists_flat_stratification_of_isNoetherian`: the stratification.

## Implementation notes

A closed subscheme of `S` is recorded by its quasi-coherent ideal sheaf, an
`AlgebraicGeometry.Scheme.IdealSheafData`, so the descending chain of closed subschemes is an
*ascending* chain `I : Fin (t + 1) → S.IdealSheafData`, and `S_t = ∅` is `I (Fin.last t) = ⊤`.
Over a Noetherian base every quasi-coherent ideal sheaf is automatically of finite type, so that
clause of the conclusion costs nothing here.

The stratum `S_i ∖ S_{i+1}` is the open subscheme of `S_i` obtained by removing the support of
`I (i+1)`, and its structure morphism to `S` is the composite of that open immersion with the
closed immersion. The conclusion is stated for that composite, while the induction is run with
the stratum presented instead as an open subscheme of the fibre product over the closed
subscheme; the two presentations are identified by
`AlgebraicGeometry.pullbackLeftPullbackSndIso` together with
`AlgebraicGeometry.pullbackRestrictIsoRestrict`.

The induction removes from a closed subset a dense open on which the pullback of `ℱ` becomes
flat, by generic flatness over the reduced induced closed subscheme, and recurses on the strictly
smaller closed complement. It terminates because the closed subsets of a Noetherian space are
well-founded for the strict order.

## References

* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

private theorem exists_strict_closed_remainder
    {T S : Type*} [TopologicalSpace T] [TopologicalSpace S] {i : T → S}
    (hinj : Function.Injective i) (hclosed : IsClosedMap i)
    (C : TopologicalSpace.Closeds S) (hrange : Set.range i = C)
    (U : TopologicalSpace.Opens T) (hU : Dense (U : Set T))
    (hC : C ≠ ⊥) :
    ∃ D : TopologicalSpace.Closeds S,
      D < C ∧ ∀ x : T, x ∈ U ↔ i x ∉ (D : Set S) := by
  let D : TopologicalSpace.Closeds S :=
    ⟨i '' (U : Set T)ᶜ, hclosed _ U.2.isClosed_compl⟩
  have hD : ∀ x : T, x ∈ U ↔ i x ∉ (D : Set S) := fun x => by
    refine ⟨?_, fun hxD => ?_⟩
    · rintro hxU ⟨y, hy, hxy⟩
      exact hy (hinj hxy ▸ hxU)
    · by_contra hxU
      exact hxD ⟨x, hxU, rfl⟩
  refine ⟨D, lt_of_le_of_ne ?_ fun hEq => ?_, hD⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (hrange ▸ Set.mem_range_self x : i x ∈ (C : Set S))
  · obtain ⟨y, hy⟩ : (C : Set S).Nonempty :=
      Set.nonempty_iff_ne_empty.2 fun h => hC (SetLike.ext' h)
    obtain ⟨x, rfl⟩ : y ∈ Set.range i := by rwa [hrange]
    obtain ⟨xU, hxU⟩ := hU.nonempty_iff.mpr ⟨x⟩
    have hixU : i xU ∈ (C : Set S) := hrange ▸ Set.mem_range_self xU
    exact (hD xU).1 hxU (hEq.ge hixU)

private theorem exists_dense_open_flat_over_reduced_closed
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
    (F : X.Modules) [F.IsFinitePresentation] (C : TopologicalSpace.Closeds S) :
    let I := Scheme.IdealSheafData.vanishingIdeal C
    let i := I.subschemeι
    let X' := pullback f i
    let g : X' ⟶ I.subscheme := pullback.snd f i
    let F' : X'.Modules := (Scheme.Modules.pullback (pullback.fst f i)).obj F
    ∃ U : I.subscheme.Opens,
      Dense (U : Set I.subscheme) ∧
        IsFlatOver (g.resLE U (g ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom
          (F'.restrict (g ⁻¹ᵁ U).ι) := by
  classical
  intro I i X' g F'
  have : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  let _ : F'.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback (pullback.fst f i) F
  have : F'.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F'
  have : F'.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F'
  obtain ⟨U, hUdense, _, _, hflat, _⟩ :=
    exists_dense_open_flat_finitePresentation g F'
  exact ⟨U, hUdense, by simpa [g, F', X', I] using hflat⟩

private lemma ideal_isFiniteType_of_isLocallyNoetherian
    (S : Scheme.{u}) [IsLocallyNoetherian S] (I : S.IdealSheafData) :
    Scheme.IdealSheafData.IsFiniteType I := by
  intro U
  have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian U
  exact Ideal.fg_of_isNoetherianRing _

private lemma flatOver_of_schemeIsoPullback {X X' S : Scheme.{u}}
    (e : X ≅ X') (f : X ⟶ S) (g : X' ⟶ S)
    (he : e.hom ≫ g = f) (M : X'.Modules) [M.IsQuasicoherent]
    (hM : IsFlatOver g.toLRSHom.toShHom M) :
    IsFlatOver f.toLRSHom.toShHom
      ((Scheme.Modules.pullback e.hom).obj M) := by
  have hsq : IsPullback e.hom f g (𝟙 S) := .of_horiz_isIso ⟨by simpa using he⟩
  exact @modulePullback_isFlatOver _ _ _ _ _ _ _ _ hsq M ‹_› hM

private noncomputable def flatStratum {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (I J : S.IdealSheafData) : Prop :=
  let Z := I.subscheme
  let V : S.Opens := J.support.compl
  let U : Z.Opens := I.subschemeι ⁻¹ᵁ V
  let P := pullback f I.subschemeι
  let p := pullback.snd f I.subschemeι
  let W : P.Opens := p ⁻¹ᵁ U
  let q := p.resLE U W le_rfl
  let F' := (Scheme.Modules.pullback (pullback.fst f I.subschemeι)).obj F
  IsFlatOver q.toLRSHom.toShHom (F'.restrict W.ι)

private noncomputable abbrev directFlatStratum {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (I J : S.IdealSheafData) : Prop :=
  let U : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ J.support.compl
  let g : U.toScheme ⟶ S := U.ι ≫ I.subschemeι
  IsFlatOver (pullback.snd f g).toLRSHom.toShHom
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F)

private lemma flatStratum_to_directFlatStratum
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsFinitePresentation]
    (I J : S.IdealSheafData) (h : flatStratum f F I J) :
    directFlatStratum f F I J := by
  classical
  let Z := I.subscheme
  let j := I.subschemeι
  let U : Z.Opens := j ⁻¹ᵁ J.support.compl
  let P := pullback f j
  let p := pullback.snd f j
  let W : P.Opens := p ⁻¹ᵁ U
  let qW := p.resLE U W le_rfl
  let T := pullback f (U.ι ≫ j)
  let qT := pullback.snd f (U.ι ≫ j)
  let α := pullbackLeftPullbackSndIso f j U.ι
  let β := pullbackRestrictIsoRestrict p U
  let e : T ≅ W := α.symm ≪≫ β
  have he : e.hom ≫ qW = qT := by
    apply (cancel_mono U.ι).1
    show α.inv ≫ β.hom ≫ (p.resLE U W le_rfl) ≫ U.ι = qT ≫ U.ι
    rw [Scheme.Hom.resLE_comp_ι, pullbackRestrictIsoRestrict_hom_ι_assoc]
    exact pullbackLeftPullbackSndIso_inv_fst_snd f j U.ι
  let p₁ := pullback.fst f j
  let r₁ := pullback.fst f (U.ι ≫ j)
  have heX : e.hom ≫ W.ι ≫ p₁ = r₁ := by
    show α.inv ≫ β.hom ≫ W.ι ≫ p₁ = r₁
    rw [pullbackRestrictIsoRestrict_hom_ι_assoc]
    exact pullbackLeftPullbackSndIso_inv_fst f j U.ι
  let M := (Scheme.Modules.pullback p₁).obj F
  let MW := M.restrict W.ι
  let MT := (Scheme.Modules.pullback r₁).obj F
  let _ : M.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback p₁ F
  let _ : MW.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation W.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback W.ι M)
  have : MW.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation MW
  let eM : (Scheme.Modules.pullback e.hom).obj MW ≅ MT :=
    (Scheme.Modules.pullback e.hom).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M) ≪≫
      (Scheme.Modules.pullbackComp e.hom W.ι).app M ≪≫
      (Scheme.Modules.pullbackComp (e.hom ≫ W.ι) p₁).app F ≪≫
      (Scheme.Modules.pullbackCongr heX).app F
  exact isFlatOver_of_moduleIso qT.toLRSHom.toShHom eM
    (flatOver_of_schemeIsoPullback e qT qW he MW (by simpa [MW, qW, flatStratum] using h))

private theorem exists_noetherian_flat_strata
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (C : TopologicalSpace.Closeds S) :
    ∃ (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData),
      I 0 = Scheme.IdealSheafData.vanishingIdeal C ∧
      (∀ i, Scheme.IdealSheafData.IsFiniteType (I i)) ∧
      (∀ i : Fin t, I (Fin.castSucc i) ≤ I (Fin.succ i)) ∧
      I (Fin.last t) = ⊤ ∧
      ∀ i : Fin t, flatStratum f F (I (Fin.castSucc i)) (I (Fin.succ i)) := by
  classical
  induction C using WellFoundedLT.induction with
  | ind C ih =>
    by_cases hC : C = ⊥
    · subst C
      exact ⟨0, fun _ => ⊤, by simp, fun _ => ideal_isFiniteType_of_isLocallyNoetherian S _,
        Fin.elim0, rfl, Fin.elim0⟩
    let J := Scheme.IdealSheafData.vanishingIdeal C
    let i := J.subschemeι
    have hrange : Set.range i.base = (C : Set S) := by
      rw [J.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    obtain ⟨U, hUdense, hflat⟩ := exists_dense_open_flat_over_reduced_closed f hf F C
    obtain ⟨D, hDC, hDU⟩ := exists_strict_closed_remainder i.isClosedEmbedding.injective
      i.isClosedEmbedding.isClosedMap C hrange U hUdense hC
    obtain ⟨t, I, hI0, -, hIle, hItop, hIflat⟩ := ih D hDC
    have hopen : U = i ⁻¹ᵁ (Scheme.IdealSheafData.vanishingIdeal D).support.compl := by
      ext x
      exact hDU x
    subst hopen
    let I' : Fin (t + 2) → S.IdealSheafData :=
      Fin.cases (Scheme.IdealSheafData.vanishingIdeal C) I
    refine ⟨t + 1, I', by simp [I'], fun _ => ideal_isFiniteType_of_isLocallyNoetherian S _,
      fun k => ?_, hItop, fun k => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) k
      · exact (Scheme.IdealSheafData.vanishingIdeal_antimono hDC.le).trans hI0.ge
      · simpa [I'] using hIle j
    · refine Fin.cases ?_ (fun j => ?_) k
      · show flatStratum f F (Scheme.IdealSheafData.vanishingIdeal C) (I 0)
        rw [hI0]
        exact hflat
      · simpa [I'] using hIflat j

/-- **Stacks Project, Tag 0ASY**, Noetherian case. For a morphism of finite presentation
`f : X ⟶ S` with `S` Noetherian and a finitely presented `𝒪_X`-module `ℱ`, the base carries a
finite ascending chain of quasi-coherent ideal sheaves of finite type, starting at the nilradical
— so that the first closed subscheme is a thickening of `S` — and ending at the unit ideal — so
that the last closed subscheme is empty — such that the pullback of `ℱ` to the fibre product of
`X` with each locally closed stratum is flat over that stratum. -/
public theorem exists_flat_stratification_of_isNoetherian {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData),
      Stacks.Thickenings.IsThickening (I 0).subschemeι ∧
      (∀ i, Scheme.IdealSheafData.IsFiniteType (I i)) ∧
      (∀ i : Fin t, I (Fin.castSucc i) ≤ I (Fin.succ i)) ∧
      I (Fin.last t) = ⊤ ∧
      ∀ i : Fin t,
        let Z := I (Fin.castSucc i)
        let V : S.Opens := (I (Fin.succ i)).support.compl
        let U : Z.subscheme.Opens := Z.subschemeι ⁻¹ᵁ V
        let g : U.toScheme ⟶ S := U.ι ≫ Z.subschemeι
        IsFlatOver (pullback.snd f g).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) := by
  obtain ⟨t, I, hI0, hIFT, hIle, hItop, hIflat⟩ := exists_noetherian_flat_strata f hf F ⊤
  refine ⟨t, I, ⟨inferInstance, ?_⟩, hIFT, hIle, hItop,
    fun i => flatStratum_to_directFlatStratum f F _ _ (hIflat i)⟩
  rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, hI0]
  simp

end AlgebraicGeometry
