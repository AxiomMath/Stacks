module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization.Existence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperGRing
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0GS2 over a complete Noetherian ring and over a henselian pair with a G-ring

Let `(A, I)` be a pair and `X` proper over `Spec A`, with closed fibre
`X₀ = X ×_{Spec A} Spec (A ⧸ I)`. This file carries out the first four paragraphs of the Stacks
proof of Tag 0GS2: base change `FÉt_X ⥤ FÉt_{X₀}` is an equivalence

* when `A` is Noetherian and `I`-adically complete
  (`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_isAdicComplete`), and
* when `(A, I)` is a henselian pair and `A` is a Noetherian G-ring, as
  `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair`.

## The argument

The complete case is the library's
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization`
(essential surjectivity by Grothendieck's algebraization theorem, full faithfulness by the graph
argument), fed with Grothendieck existence for finite sheaves of algebras over a proper scheme,
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_isProper`.

In the G-ring case, let `U₀ ⟶ X₀` be finite étale and let `A^∧` be the `I`-adic completion,
which is Noetherian and `I A^∧`-adically complete with `A^∧ ⧸ I A^∧ = A ⧸ I`
(`AlgebraicGeometry.adicCompletionQuotientEquiv`). So `U₀` is a cover of the closed fibre of
`X^∧ = Spec A^∧ ×_{Spec A} X`, and the complete case lifts it to a finite étale `V ⟶ X^∧`. As
`A^∧` is the filtered colimit of its finitely generated `A`-subalgebras `A_i`, `V` comes from a
finite étale cover of some `X_{A_i}` (Tags 01ZM, 01ZO, 07RP, as
`AlgebraicGeometry.exists_finiteEtale_model`). Artin approximation for the henselian pair `(A, I)`
over the G-ring `A` (Tag 0AH5, `Stacks.Smoothing.exists_solution_of_henselianPair_of_isGRing`)
gives an `A`-algebra map `A_i → A` agreeing with `A_i ⊆ A^∧` modulo `I A^∧`
(`AlgebraicGeometry.exists_algHom_mk_comp_eq_of_isGRing_of_henselianPair`), and the base change of
the descended cover along the induced `X ⟶ X_{A_i}` is a finite étale cover of `X` with closed
fibre `U₀`. Full faithfulness follows from essential surjectivity, as in the source, by
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`.

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 0AH5](https://stacks.math.columbia.edu/tag/0AH5)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-! ### The complete case -/

/-- **Stacks Tag 0GS2 over a complete Noetherian ring.** Let `A` be a Noetherian ring complete
with respect to an ideal `I` and let `X` be proper over `Spec A`. Then base change to the closed
fibre `X ×_{Spec A} Spec (A ⧸ I)` is an equivalence of categories of finite étale covers.

This is the library's reduction to Grothendieck existence for finite sheaves of algebras,
`isEquivalence_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization`, with Grothendieck
existence supplied by `adicFiniteAlgebraAlgebraization_of_isProper` for every scheme finite étale
over `X`, each of which is again proper over `Spec A`. -/
@[ega "IV 18.3.2" "Noetherian case",
  ega "IV 18.3.4",
  sga "1 X 2.1" "more general",
  sga "2 X 3.9" "partial",
  sga "4 XII 5.10" "more general",
  sga "4 XII 6.13" "more general"]
theorem isEquivalence_finiteEtaleBaseChange_of_isProper_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization A I f fun P =>
    have := isProper_comp_of_finiteEtaleOver f P
    adicFiniteAlgebraAlgebraization_of_isProper A I (P.hom ≫ f)

/-! ### The closed fibre of the completion -/

section Completion

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- The closed fibre of the `I`-adic completion of a Noetherian ring is that of `A`:
`A^∧ ⧸ I A^∧ ≃ A ⧸ I`, induced by evaluation `A^∧ → A ⧸ I` in degree one, whose kernel is
`I A^∧`. -/
noncomputable def adicCompletionQuotientEquiv :
    AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)) ≃+* A ⧸ I :=
  (Ideal.quotEquivOfEq
      (AdicCompletion.ker_evalOneₐ_eq_map I (IsNoetherian.noetherian I))).symm.trans
    (RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ I).toRingHom)
      (AdicCompletion.evalOneₐ_surjective I))

/-- `AlgebraicGeometry.adicCompletionQuotientEquiv` is induced by evaluation in degree one. -/
theorem adicCompletionQuotientEquiv_mk (x : AdicCompletion I A) :
    adicCompletionQuotientEquiv A I (Ideal.Quotient.mk _ x) = AdicCompletion.evalOneₐ I x :=
  rfl

/-- `AlgebraicGeometry.adicCompletionQuotientEquiv` composed with the quotient map is evaluation
in degree one. -/
theorem adicCompletionQuotientEquiv_comp_mk :
    (adicCompletionQuotientEquiv A I).toRingHom.comp
        (Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A)))) =
      (AdicCompletion.evalOneₐ I).toRingHom :=
  RingHom.ext (adicCompletionQuotientEquiv_mk A I)

/-- The inverse of `AlgebraicGeometry.adicCompletionQuotientEquiv` is induced by `A → A^∧`. -/
theorem adicCompletionQuotientEquiv_symm_comp_mk :
    (adicCompletionQuotientEquiv A I).symm.toRingHom.comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk _).comp (algebraMap A (AdicCompletion I A)) := by
  ext a
  show (adicCompletionQuotientEquiv A I).symm (Ideal.Quotient.mk I a) = _
  rw [RingEquiv.symm_apply_eq]
  rfl

end Completion

/-! ### Artin approximation in the form used -/

/-- **Approximating a map to the completion modulo `I`.** Let `(A, I)` be a henselian pair with `A`
a Noetherian G-ring, and let `E` be a finite type `A`-algebra. Every `A`-algebra map
`φ : E → A^∧` to the `I`-adic completion is congruent modulo `I A^∧` to the composite of an
`A`-algebra map `E → A` with `A → A^∧`. This is Tag 0AH5 for the G-ring `A`
(`Stacks.Smoothing.exists_solution_of_henselianPair_of_isGRing`) applied to a presentation of `E`,
the source's "approximate this solution (to order `11` for example) by a solution in `A`". -/
theorem exists_algHom_mk_comp_eq_of_isGRing_of_henselianPair {A : Type u} [CommRing A]
    {I : Ideal A} (hG : IsGRing A) (hI : HenselianPair A I) {E : Type u} [CommRing E]
    [Algebra A E] [Algebra.FiniteType A E] (φ : E →ₐ[A] AdicCompletion I A) :
    ∃ σ : E →ₐ[A] A,
      (Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A)))).comp
          ((algebraMap A (AdicCompletion I A)).comp σ.toRingHom) =
        (Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A)))).comp φ.toRingHom := by
  classical
  have : IsNoetherianRing A := hG.1
  set Â := AdicCompletion I A
  set J := I.map (algebraMap A Â)
  -- a presentation `E = A[X₁, …, Xₙ] / (p₁, …, pₘ)`
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  obtain ⟨m, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (RingHom.ker π.toRingHom))
  have hpker (j) : π (p j) = 0 := (hp ▸ Submodule.subset_span ⟨j, rfl⟩ : p j ∈ RingHom.ker _)
  let xh : Fin n → Â := fun l => φ (π (MvPolynomial.X l))
  have hcomp : φ.comp π = MvPolynomial.aeval xh :=
    MvPolynomial.algHom_ext fun l => by simp [xh]
  -- approximate the solution `xh` of the relations modulo `I`
  obtain ⟨a, ha, hsol⟩ := Stacks.Smoothing.exists_solution_of_henselianPair_of_isGRing hG hI p xh
    (fun j => by rw [← hcomp, AlgHom.comp_apply, hpker, map_zero]) (N := 1) one_ne_zero
  have hker : RingHom.ker π.toRingHom ≤
      RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) A →ₐ[A] A).toRingHom := by
    rw [← hp, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hsol j
  let σ : E →ₐ[A] A := AlgHom.liftOfSurjective π hπ (MvPolynomial.aeval a) hker
  refine ⟨σ, ?_⟩
  have key : (Ideal.Quotient.mkₐ A J).comp ((Algebra.ofId A Â).comp σ) =
      (Ideal.Quotient.mkₐ A J).comp φ := by
    refine (AlgHom.cancel_right hπ).mp (MvPolynomial.algHom_ext fun l => ?_)
    show Ideal.Quotient.mk J (algebraMap A Â (σ (π (MvPolynomial.X l)))) =
      Ideal.Quotient.mk J (φ (π (MvPolynomial.X l)))
    rw [AlgHom.liftOfSurjective_apply, MvPolynomial.aeval_X, Ideal.Quotient.eq, ← neg_mem_iff,
      neg_sub]
    simpa only [pow_one] using ha l
  exact congrArg AlgHom.toRingHom key

/-! ### The henselian G-ring case -/

/-- The closed fibre of `X` is a retract of the closed fibre of `X^∧ = Spec A^∧ ×_{Spec A} X`,
by a section compatible with evaluation `A^∧ → A ⧸ I` and with the projections to `X`. -/
private theorem exists_retraction_closedFibre_adicCompletion (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    ∃ (ι : pullback (pullback.fst (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion I A)))) f) (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A)))))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
      (κ : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
        pullback (pullback.fst (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion I A)))) f) (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A))))))),
      κ ≫ ι = 𝟙 _ ∧
      κ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
        pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ I).toRingHom) ∧
      κ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ := by
  set Â := AdicCompletion I A
  set J := I.map (algebraMap A Â)
  let a : Spec (.of Â) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Â))
  let p : pullback a f ⟶ Spec (.of Â) := pullback.fst a f
  let c' : Spec (.of (Â ⧸ J)) ⟶ Spec (.of Â) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let c : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let e := adicCompletionQuotientEquiv A I
  let ε : Â →+* A ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  let g' := pullback.fst p c'
  let ι : pullback p c' ⟶ pullback f c :=
    pullback.lift (g' ≫ pullback.snd a f)
      (pullback.snd p c' ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)) (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, Category.assoc]
        congr 1
        simp only [a, c, c', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rw [adicCompletionQuotientEquiv_symm_comp_mk])
  let κ₁ : pullback f c ⟶ pullback a f :=
    pullback.lift (pullback.snd f c ≫ Spec.map (CommRingCat.ofHom ε)) (pullback.fst f c) (by
      rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
      exact pullback.condition.symm)
  let κ : pullback f c ⟶ pullback p c' :=
    pullback.lift κ₁ (pullback.snd f c ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) (by
      rw [pullback.lift_fst, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        adicCompletionQuotientEquiv_comp_mk])
  have hκ₁ : κ ≫ g' = κ₁ := pullback.lift_fst _ _ _
  refine ⟨ι, κ, ?_, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hκ₁, Category.id_comp]
      exact pullback.lift_snd _ _ _
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.id_comp]
      rw [show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from
        RingHom.ext e.apply_symm_apply, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  all_goals rw [← Category.assoc, hκ₁]
  exacts [pullback.lift_fst _ _ _, pullback.lift_snd _ _ _]

/-- Over a henselian pair `(A, I)` with `A` a Noetherian G-ring, every finite étale cover of
`X^∧ = Spec A^∧ ×_{Spec A} X` is the base change of a finite étale cover of some `X_{A_i}`, for a
finitely generated `A`-subalgebra `A_i ⊆ A^∧`, along a projection `X^∧ ⟶ X_{A_i}` linked to the
closed fibre of `X` by a section `X ⟶ X_{A_i}` from Artin approximation. -/
private theorem exists_spread_finiteEtale_adicCompletion (A : Type u) [CommRing A] (I : Ideal A)
    (hI : HenselianPair A I) (hG : IsGRing A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] (κ : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
      pullback (pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion I A)))) f) (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A)))))))
    (hκp : κ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ I).toRingHom))
    (hκf : κ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _)
    (V : FiniteEtaleOver (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion I A)))) f)) :
    ∃ (Y : Scheme.{u}) (q : pullback (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion I A)))) f ⟶ Y) (s : X ⟶ Y) (W : FiniteEtaleOver Y),
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ s =
        κ ≫ pullback.fst _ _ ≫ q ∧ Nonempty ((finiteEtaleBaseChange q).obj W ≅ V) := by
  have : IsNoetherianRing A := hG.1
  set Â := AdicCompletion I A
  let c : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let e := adicCompletionQuotientEquiv A I
  let ε : Â →+* A ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  have : ∀ i, CompactSpace ((AdjoinFinset.bcDiagram A Â f).obj i) := fun i =>
    (AdjoinFinset.bcDiagram_compactSpace_and_quasiSeparatedSpace A Â f i).1
  have : ∀ i, QuasiSeparatedSpace ((AdjoinFinset.bcDiagram A Â f).obj i) := fun i =>
    (AdjoinFinset.bcDiagram_compactSpace_and_quasiSeparatedSpace A Â f i).2
  have : ∀ {i j : (Finset Â)ᵒᵖ} (e : i ⟶ j), IsAffineHom ((AdjoinFinset.bcDiagram A Â f).map e) :=
    fun e => AdjoinFinset.bcDiagram_isAffineHom A Â f e
  obtain ⟨i, W, ⟨eW⟩⟩ := exists_finiteEtale_model (AdjoinFinset.bcDiagram A Â f)
    (AdjoinFinset.bcCone A Â f) (AdjoinFinset.isLimitBcCone A Â f) V
  let Ai := Algebra.adjoin A (i.unop : Set Â)
  have : Algebra.FiniteType A Ai :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  obtain ⟨σ, hσ⟩ := exists_algHom_mk_comp_eq_of_isGRing_of_henselianPair hG hI Ai.val
  have hσε : (Ideal.Quotient.mk I).comp σ.toRingHom = ε.comp Ai.val.toRingHom := by
    have h := congrArg e.toRingHom.comp hσ
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, adicCompletionQuotientEquiv_comp_mk] at h
    change (ε.comp (algebraMap A Â)).comp σ.toRingHom = ε.comp Ai.val.toRingHom at h
    rwa [AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk] at h
  let s : X ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ai))) f :=
    pullback.lift (f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (𝟙 X) (by
      rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.id_comp,
        show σ.toRingHom.comp (algebraMap A Ai) = RingHom.id A from RingHom.ext σ.commutes,
        CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
  refine ⟨_, AdjoinFinset.bcProj A Â f i, s, W, ?_, ⟨eW.symm⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    calc pullback.fst f c ≫ f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
        = pullback.snd f c ≫ c ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
          rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = pullback.snd f c ≫ Spec.map (CommRingCat.ofHom ε) ≫
            Spec.map (CommRingCat.ofHom Ai.val.toRingHom) := by
          simp only [c, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rw [hσε]
      _ = (κ ≫ pullback.fst _ _ ≫ pullback.fst _ _) ≫
            Spec.map (CommRingCat.ofHom Ai.val.toRingHom) := by
          rw [hκp, Category.assoc]
      _ = _ := by
          simp only [Category.assoc]
          rw [AdjoinFinset.bcProj_fst]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.assoc, Category.assoc,
      AdjoinFinset.bcProj_snd]
    exact hκf.symm

/-- **Stacks Tag 0GS2, essential surjectivity over a henselian pair with a Noetherian G-ring,
from the complete case at the completion.** Let `(A, I)` be a henselian pair with `A` a Noetherian
G-ring, let `A^∧` be the `I`-adic completion and let `X` be proper over `Spec A`. If base change to
the closed fibre is essentially surjective on finite étale covers of
`X^∧ = Spec A^∧ ×_{Spec A} X`, then it is essentially surjective on finite étale covers of `X`.

This is the source's argument; see the module docstring. -/
theorem essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair_of_adicCompletion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) (hG : IsGRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hc : (finiteEtaleBaseChange (pullback.fst
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))) f)
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (algebraMap A (AdicCompletion I A)))))))).EssSurj) :
    (finiteEtaleBaseChange (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk I))))).EssSurj := by
  have : IsNoetherianRing A := hG.1
  obtain ⟨ι, κ, hκι, hκp, hκf⟩ := exists_retraction_closedFibre_adicCompletion A I f
  exact essSurj_finiteEtaleBaseChange_of_retraction _ _ ι κ hκι
    (exists_spread_finiteEtale_adicCompletion A I hI hG f κ hκp hκf)

/-- **Stacks Tag 0GS2, essential surjectivity over a henselian pair with a Noetherian G-ring.**
The complete case at the `I`-adic completion is
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_isAdicComplete`, the completion being
Noetherian and complete for the extension of `I`. -/
theorem essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) (hG : IsGRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk I))))).EssSurj := by
  have : IsNoetherianRing A := hG.1
  have : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    AdicCompletion.isAdicComplete_self I (IsNoetherian.noetherian I)
  refine essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair_of_adicCompletion
    A I hI hG f ?_
  have := isEquivalence_finiteEtaleBaseChange_of_isProper_of_isAdicComplete (AdicCompletion I A)
    (I.map (algebraMap A (AdicCompletion I A)))
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))) f)
  infer_instance

/-- **Stacks Tag 0GS2 over a henselian pair with a Noetherian G-ring.** Let `(A, I)` be a
henselian pair with `A` a Noetherian G-ring and let `X` be proper over `Spec A`. Then base change
to the closed fibre `X ×_{Spec A} Spec (A ⧸ I)` is an equivalence of categories of finite étale
covers.

Essential surjectivity is
`essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair`, applied to every scheme
finite étale over `X` (again proper over `A`), and
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj` deduces full
faithfulness from it, as in the source. -/
@[sga "1 X 2.1" "more general",
  sga "4 XII 5.10" "more general",
  sga "4 XII 5.9bis" "special case",
  sga "4 XII 6.13" "Clause 6.5(ii)",
  sga "4 XIII 1.1" "partial"]
theorem isEquivalence_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) (hG : IsGRing A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk I))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj A I hI f fun P =>
    have : IsProper (P.hom ≫ f) := isProper_comp_of_finiteEtaleOver f P
    essSurj_finiteEtaleBaseChange_of_isProper_of_isGRing_of_henselianPair A I hI hG (P.hom ≫ f)

end AlgebraicGeometry

end
