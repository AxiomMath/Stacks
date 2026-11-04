module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence
public import StacksFrontier.AlgebraicGeometry.Limits.AdjoinFinsetSystem
public import StacksFrontier.RingTheory.ApproximationProperty.Basic
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianGRing
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing

/-!
# Tag 0A48 over a henselian local Noetherian G-ring, from the complete case

This file carries out the third paragraph of the Stacks proof of Tag 0A48, "Essential
surjectivity when `A` is a henselian local Noetherian G-ring". Let `A` be a henselian local
Noetherian G-ring and `X` proper over `A`, with closed fibre `X₀`. Granted the complete case (the
first two paragraphs of the source's proof, named here
`AlgebraicGeometry.ProperCompleteLocalFiniteEtaleEquivalence`), base change
`FÉt_X ⥤ FÉt_{X₀}` is essentially surjective, hence an equivalence.

## The argument

Let `U₀ ⟶ X₀` be finite étale, let `A^∧` be the completion of `A` and
`X^∧ = Spec A^∧ ×_{Spec A} X`.
* `A^∧ ⧸ 𝔪 A^∧ = A ⧸ 𝔪` (`AlgebraicGeometry.completionResidueEquiv`), so the closed fibre of
  `X^∧` retracts onto `X₀`, and `U₀` is a cover of the closed fibre of `X^∧`; by the complete case
  there is a finite étale `V ⟶ X^∧` whose special fibre is `U₀`.
* `A^∧` is the filtered colimit of its finitely generated `A`-subalgebras `A_i`, so `X^∧` is the
  limit of the `X_{A_i}` (`AlgebraicGeometry.AdjoinFinset.isLimitBcCone`), and `V` comes from a
  finite étale `U_i ⟶ X_{A_i}` (Tags 01ZM, 01ZO, 07RP, as
  `AlgebraicGeometry.exists_finiteEtale_model`).
* Artin approximation (Tag 07QY) gives an `A`-algebra map `A_i → A` agreeing with the inclusion
  `A_i ⊆ A^∧` modulo the maximal ideal (`AlgebraicGeometry.exists_algHom_mk_comp_eq_of_isGRing`),
  so the two maps `X₀ ⟶ X_{A_i}` agree, and the base change `U ⟶ X` of `U_i` along the induced
  `X ⟶ X_{A_i}` is finite étale with special fibre `U₀`.

The bookkeeping of the last step is isolated in
`AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_retraction`. Full faithfulness is deduced from
essential surjectivity, as in the source, by
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`.

## Main results

* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_adicCompletion` —
  essential surjectivity for `X`, from essential surjectivity for `X^∧` over `A^∧`.
* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing` and
  `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_isGRing` — Tag 0A48 for a
  henselian local Noetherian G-ring, granted the complete case.

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public section

open CategoryTheory Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### The residue field of the completion -/

section Completion

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The residue field of the completion `A^∧` of a Noetherian local ring is that of `A`:
`A^∧ ⧸ 𝔪 A^∧ ≃ A ⧸ 𝔪`, inverse to the map induced by `A → A^∧`. -/
noncomputable def completionResidueEquiv :
    AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ≃+*
      A ⧸ maximalIdeal A :=
  (RingEquiv.ofBijective (ResidueField.map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
    (AdicCompletion.residueField_map_bijective A)).symm

/-- The inverse of `AlgebraicGeometry.completionResidueEquiv` is induced by `A → A^∧`. -/
theorem completionResidueEquiv_symm_mk (a : A) :
    (completionResidueEquiv A).symm (Ideal.Quotient.mk (maximalIdeal A) a) =
      Ideal.Quotient.mk _ (algebraMap A (AdicCompletion (maximalIdeal A) A) a) :=
  ResidueField.map_residue (algebraMap A (AdicCompletion (maximalIdeal A) A)) a

/-- The residue map `A^∧ → A ⧸ 𝔪` of the completion of a Noetherian local ring. -/
noncomputable def completionResidue : AdicCompletion (maximalIdeal A) A →+* A ⧸ maximalIdeal A :=
  (completionResidueEquiv A).toRingHom.comp (Ideal.Quotient.mk _)

/-- The residue map of the completion restricts to the residue map of `A`. -/
theorem completionResidue_comp_algebraMap :
    (completionResidue A).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      Ideal.Quotient.mk (maximalIdeal A) := by
  ext a
  show completionResidueEquiv A (Ideal.Quotient.mk _ _) = _
  rw [← completionResidueEquiv_symm_mk, RingEquiv.apply_symm_apply]

/-- `AlgebraicGeometry.completionResidueEquiv_symm_mk`, as an equality of ring maps. -/
theorem completionResidueEquiv_symm_comp_mk :
    (completionResidueEquiv A).symm.toRingHom.comp (Ideal.Quotient.mk (maximalIdeal A)) =
      (Ideal.Quotient.mk _).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
  RingHom.ext (completionResidueEquiv_symm_mk A)

end Completion

/-! ### Artin approximation in the form used -/

/-- **A henselian local G-ring has the approximation property** (Stacks 07QY, without the
congruence). -/
theorem _root_.IsLocalRing.hasApproximationProperty_of_isGRing {R : Type u} [CommRing R]
    [HenselianLocalRing R] (hG : IsGRing R) : IsLocalRing.HasApproximationProperty R :=
  fun _ _ f x hx =>
    let ⟨b, _, hb⟩ := Stacks.Smoothing.exists_approximate_solution_of_henselian_isGRing hG f x hx 0
    ⟨b, hb⟩

/-- **Approximating a map to the completion, to first order.** Let `A` be a henselian local
G-ring and `E` a finite type `A`-algebra. Every `A`-algebra map `φ : E → A^∧` is congruent
modulo the maximal ideal of `A^∧` to the composite of an `A`-algebra map `E → A` with `A → A^∧`:
this is Stacks 07QY applied to a presentation of `E`, the source's "approximate this solution (to
order `11` for example) by a solution in `A`". -/
theorem exists_algHom_mk_comp_eq_of_isGRing {A : Type u} [CommRing A] [HenselianLocalRing A]
    [IsNoetherianRing A] (hG : IsGRing A) {E : Type u} [CommRing E] [Algebra A E]
    [Algebra.FiniteType A E] (φ : E →ₐ[A] AdicCompletion (maximalIdeal A) A) :
    ∃ σ : E →ₐ[A] A,
      (Ideal.Quotient.mk (maximalIdeal (AdicCompletion (maximalIdeal A) A))).comp
          ((algebraMap A (AdicCompletion (maximalIdeal A) A)).comp σ.toRingHom) =
        (Ideal.Quotient.mk (maximalIdeal (AdicCompletion (maximalIdeal A) A))).comp
          φ.toRingHom := by
  classical
  set Â := AdicCompletion (maximalIdeal A) A
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A E).FG)
  let x : Fin t.card → E := fun i => (t.equivFin.symm i : E)
  obtain ⟨σ, hσ⟩ := (IsLocalRing.hasApproximationProperty_of_isGRing hG).exists_algHom_sub_mem
    φ x 1
  refine ⟨σ, ?_⟩
  have hle : Ideal.map (algebraMap A Â) (maximalIdeal A ^ 1) ≤ maximalIdeal Â := by
    rw [pow_one, Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have key : ((Ideal.Quotient.mkₐ A (maximalIdeal Â)).comp ((Algebra.ofId A Â).comp σ)) =
      (Ideal.Quotient.mkₐ A (maximalIdeal Â)).comp φ := by
    refine AlgHom.ext_of_adjoin_eq_top ht fun y hy => ?_
    obtain ⟨i, hi⟩ : ∃ i, x i = y := ⟨t.equivFin ⟨y, hy⟩, by simp [x]⟩
    rw [← hi]
    show Ideal.Quotient.mk _ (algebraMap A Â (σ (x i))) = Ideal.Quotient.mk _ (φ (x i))
    rw [Ideal.Quotient.eq]
    exact hle (hσ i)
  exact congrArg AlgHom.toRingHom key

/-! ### Essential surjectivity through a retract and a spreading out -/

/-- **Essential surjectivity of base change, transported through a retract.** Let
`g : X₀ ⟶ X` and `g' : X₀' ⟶ X'` be morphisms of schemes, and let `κ : X₀ ⟶ X₀'` have a
retraction `ι`. Suppose base change along `g'` is essentially surjective on finite étale covers,
and every finite étale cover `V` of `X'` is the base change along some `q : X' ⟶ Y` of a cover of
`Y`, where `q` is linked to `g` by some `s : X ⟶ Y` with `g ≫ s = κ ≫ g' ≫ q`. Then base change
along `g` is essentially surjective.

A cover `U₀` of `X₀` is transported to `X₀'` along `ι`, lifted to a cover `V` of `X'`, spread out
to a cover `W` of `Y`, and pulled back to `X` along `s`; its base change to `X₀` is the base change
of `W` along `κ ≫ g' ≫ q`, which is that of `U₀` along `κ ≫ ι = 𝟙`. -/
theorem essSurj_finiteEtaleBaseChange_of_retraction {X X₀ X' X₀' : Scheme.{u}} (g : X₀ ⟶ X)
    (g' : X₀' ⟶ X') (ι : X₀' ⟶ X₀) (κ : X₀ ⟶ X₀') (hκι : κ ≫ ι = 𝟙 X₀)
    [(finiteEtaleBaseChange g').EssSurj]
    (hspread : ∀ V : FiniteEtaleOver X', ∃ (Y : Scheme.{u}) (q : X' ⟶ Y) (s : X ⟶ Y)
      (W : FiniteEtaleOver Y), g ≫ s = κ ≫ g' ≫ q ∧
        Nonempty ((finiteEtaleBaseChange q).obj W ≅ V)) :
    (finiteEtaleBaseChange g).EssSurj := by
  refine ⟨fun U₀ => ?_⟩
  let V := (finiteEtaleBaseChange g').objPreimage ((finiteEtaleBaseChange ι).obj U₀)
  let eV : (finiteEtaleBaseChange g').obj V ≅ (finiteEtaleBaseChange ι).obj U₀ :=
    (finiteEtaleBaseChange g').objObjPreimageIso _
  obtain ⟨Y, q, s, W, hfac, ⟨eW⟩⟩ := hspread V
  exact ⟨(finiteEtaleBaseChange s).obj W, ⟨
    ((finiteEtaleBaseChangeComp g s (κ ≫ g' ≫ q) hfac.symm).app W).symm ≪≫
    (finiteEtaleBaseChangeComp κ (g' ≫ q)).app W ≪≫
    (finiteEtaleBaseChange κ).mapIso ((finiteEtaleBaseChangeComp g' q).app W ≪≫
      (finiteEtaleBaseChange g').mapIso eW ≪≫ eV) ≪≫
    ((finiteEtaleBaseChangeComp κ ι (𝟙 _) hκι.symm).app U₀).symm ≪≫
    finiteEtaleBaseChangeId.app U₀⟩⟩

/-! ### The henselian G-ring case -/

/-- Composing `Spec` of two ring maps given by `CommRingCat.ofHom`. -/
private theorem specMap_ofHom_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [← Spec.map_comp]
  rfl

/-- `Spec` of a ring map and of a left inverse of it compose to the identity. -/
private theorem specMap_ofHom_comp_self {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (ψ : S →+* R) (h : ∀ x, ψ (φ x) = x) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = 𝟙 _ := by
  rw [specMap_ofHom_comp, ← Spec.map_id]
  exact congrArg _ (CommRingCat.hom_ext (RingHom.ext h))

/-- **Stacks Tag 0A48, essential surjectivity over a henselian local Noetherian G-ring, from the
complete case at the completion.** Let `A` be a henselian local Noetherian G-ring with
completion `A^∧`, and `X` proper over `A`. If base change to the closed fibre is essentially
surjective on finite étale covers of `X^∧ = Spec A^∧ ×_{Spec A} X`, then it is essentially
surjective on finite étale covers of `X`.

This is the source's argument. A cover `U₀` of `X₀` is a cover of the closed fibre of `X^∧`,
because `A^∧` and `A` have the same residue field, and so lifts to a finite étale `V ⟶ X^∧`.
Writing `A^∧` as the filtered colimit of its finitely generated `A`-subalgebras `A_i`, `X^∧` is
the limit of the `X_{A_i}`, and `V` comes from a finite étale cover of some `X_{A_i}`
(Tags 01ZM, 01ZO, 07RP, as `AlgebraicGeometry.exists_finiteEtale_model`). Artin approximation
(Tag 07QY) gives an `A`-algebra map `A_i → A` agreeing with the inclusion `A_i ⊆ A^∧` modulo the
maximal ideal, and the base change of the descended cover along the induced `X ⟶ X_{A_i}` is a
finite étale cover of `X` with closed fibre `U₀`. -/
theorem essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_adicCompletion
    (A : Type u) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] (hG : IsGRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hc : (finiteEtaleBaseChange (pullback.fst
      (pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A)))) f)
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (maximalIdeal (AdicCompletion (maximalIdeal A) A))))))).EssSurj) :
    (finiteEtaleBaseChange (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal A)))))).EssSurj := by
  set Â := AdicCompletion (maximalIdeal A) A
  let a : Spec (.of Â) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Â))
  let p : pullback a f ⟶ Spec (.of Â) := pullback.fst a f
  let c' : Spec (.of (Â ⧸ maximalIdeal Â)) ⟶ Spec (.of Â) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal Â)))
  let c : Spec (.of (A ⧸ maximalIdeal A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))
  let e := completionResidueEquiv A
  let ε := completionResidue A
  let g := pullback.fst f c
  let g' := pullback.fst p c'
  -- `X₀' ⟶ X₀`
  let ι : pullback p c' ⟶ pullback f c :=
    pullback.lift (g' ≫ pullback.snd a f)
      (pullback.snd p c' ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)) (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, Category.assoc]
        congr 1
        simp only [a, c, c', specMap_ofHom_comp]
        rw [completionResidueEquiv_symm_comp_mk])
  -- `X₀ ⟶ X^∧`
  let κ₁ : pullback f c ⟶ pullback a f :=
    pullback.lift (pullback.snd f c ≫ Spec.map (CommRingCat.ofHom ε)) g (by
      rw [Category.assoc, specMap_ofHom_comp, completionResidue_comp_algebraMap]
      exact pullback.condition.symm)
  -- `X₀ ⟶ X₀'`
  let κ : pullback f c ⟶ pullback p c' :=
    pullback.lift κ₁ (pullback.snd f c ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) (by
      rw [pullback.lift_fst, Category.assoc, specMap_ofHom_comp]
      rfl)
  have hκ₁ : κ ≫ g' = κ₁ := pullback.lift_fst _ _ _
  have hκι : κ ≫ ι = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hκ₁, Category.id_comp]
      exact pullback.lift_snd _ _ _
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, specMap_ofHom_comp_self _ _ e.apply_symm_apply, Category.id_comp,
        Category.comp_id]
  refine essSurj_finiteEtaleBaseChange_of_retraction g g' ι κ hκι fun V => ?_
  let : ∀ i, CompactSpace ((AdjoinFinset.bcDiagram A Â f).obj i) := fun i =>
    (AdjoinFinset.bcDiagram_compactSpace_and_quasiSeparatedSpace A Â f i).1
  let : ∀ i, QuasiSeparatedSpace ((AdjoinFinset.bcDiagram A Â f).obj i) := fun i =>
    (AdjoinFinset.bcDiagram_compactSpace_and_quasiSeparatedSpace A Â f i).2
  let : ∀ {i j : (Finset Â)ᵒᵖ} (e : i ⟶ j), IsAffineHom ((AdjoinFinset.bcDiagram A Â f).map e) :=
    fun e => AdjoinFinset.bcDiagram_isAffineHom A Â f e
  obtain ⟨i, W, ⟨eW⟩⟩ := exists_finiteEtale_model (AdjoinFinset.bcDiagram A Â f)
    (AdjoinFinset.bcCone A Â f) (AdjoinFinset.isLimitBcCone A Â f) V
  let Ai := Algebra.adjoin A (i.unop : Set Â)
  have : Algebra.FiniteType A Ai :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  obtain ⟨σ, hσ⟩ := exists_algHom_mk_comp_eq_of_isGRing hG Ai.val
  have hσε : (Ideal.Quotient.mk (maximalIdeal A)).comp σ.toRingHom = ε.comp Ai.val.toRingHom := by
    have h := congrArg e.toRingHom.comp hσ
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc] at h
    change (ε.comp (algebraMap A Â)).comp σ.toRingHom = ε.comp Ai.val.toRingHom at h
    rwa [completionResidue_comp_algebraMap] at h
  let s : X ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ai))) f :=
    pullback.lift (f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (𝟙 X) (by
      rw [Category.assoc, specMap_ofHom_comp_self _ _ σ.commutes, Category.id_comp,
        Category.comp_id])
  have key : g ≫ s = κ ≫ g' ≫ AdjoinFinset.bcProj A Â f i := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      have h1 : κ ≫ g' ≫ p = pullback.snd f c ≫ Spec.map (CommRingCat.ofHom ε) := by
        rw [← Category.assoc, hκ₁]
        exact pullback.lift_fst _ _ _
      calc g ≫ f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
          = pullback.snd f c ≫ c ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
            rw [← Category.assoc, pullback.condition, Category.assoc]
        _ = pullback.snd f c ≫ Spec.map (CommRingCat.ofHom ε) ≫
              Spec.map (CommRingCat.ofHom Ai.val.toRingHom) := by
            simp only [c, specMap_ofHom_comp]
            rw [hσε]
        _ = (κ ≫ g' ≫ p) ≫ Spec.map (CommRingCat.ofHom Ai.val.toRingHom) := by
            rw [h1, Category.assoc]
        _ = _ := by
            simp only [Category.assoc]
            rw [AdjoinFinset.bcProj_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.assoc, Category.assoc,
        AdjoinFinset.bcProj_snd, ← Category.assoc, hκ₁]
      exact (pullback.lift_snd _ _ _).symm
  refine ⟨_, AdjoinFinset.bcProj A Â f i, s, W, key, ⟨eW.symm⟩⟩

/-- **Stacks Tag 0A48, essential surjectivity over a henselian local Noetherian G-ring**, granted
the complete case `ProperCompleteLocalFiniteEtaleEquivalence`. -/
theorem essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing
    (hcomplete : ProperCompleteLocalFiniteEtaleEquivalence.{u})
    (A : Type u) [CommRing A] [HenselianLocalRing A] (hG : IsGRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal A)))))).EssSurj := by
  have : IsNoetherianRing A := hG.1
  refine essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_adicCompletion A hG f ?_
  have := hcomplete (AdicCompletion (maximalIdeal A) A) (pullback.fst (Spec.map
    (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))) f) inferInstance
  infer_instance

/-- **Stacks Tag 0A48 over a henselian local Noetherian G-ring**, granted the complete case
`ProperCompleteLocalFiniteEtaleEquivalence`: for `A` a henselian local Noetherian G-ring and `X`
proper over `A`, base change to the closed fibre is an equivalence on finite étale covers.

Essential surjectivity is
`AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing`, applied to every scheme
finite étale over `X` (again proper over `A`), and
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`
deduces full faithfulness from it, as in the source. -/
theorem isEquivalence_finiteEtaleBaseChange_of_isProper_of_isGRing
    (hcomplete : ProperCompleteLocalFiniteEtaleEquivalence.{u})
    (A : Type u) [CommRing A] [HenselianLocalRing A] (hG : IsGRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal A)))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj A (maximalIdeal A)
    (henselianPair_maximalIdeal A) f fun P =>
      have : IsProper (P.hom ≫ f) := isProper_comp_of_finiteEtaleOver f P
      essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing hcomplete A hG (P.hom ≫ f)

end AlgebraicGeometry

end
