module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineOfCartesianChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceChartRings

/-!
# An affine intersection of closed subspaces has an affine member

Stacks 07SQ says that if the limit of a directed system of quasi-compact, quasi-separated
algebraic spaces with affine transition morphisms is affine, then some member of the system is
affine. In the big fppf sites of this library the statement fails without a bound on the index:
see `AlgebraicGeometry.Space.Refute07SQ.not_forall_exists_isAffineSpace_system_obj`. This file
proves it, with no bound on the index, for a directed system of closed subspaces `Zᵢ` of one
quasi-compact separated algebraic space `Y`, whose limit is the intersection `⋂ Zᵢ`. That is the
case the thickening route to Stacks 049D needs. The proof works over the terminal base, where
every affine scheme of the site is an object over the base.

The proof is the source's. Take an affine étale surjective chart `V = Spec C` of `Y` with affine
relation `R = Spec E`. The `Zᵢ` cut out ideals `Kᵢ ⊆ C`, and the intersection cuts out
`K∞ = ⋃ Kᵢ`. Affineness of the intersection makes `C ⧸ K∞` an étale, faithfully flat effective
quotient. The ring core `Stacks.AffineStageCore.exists_stage_data` then puts the square of
Stacks 084U, cartesian on rings, at some stage `k`, and
`AlgebraicGeometry.Space.isAffineSpace_of_isIso_lift` makes `Z_k` affine. The closed-immersion
structure is what makes the chart rings of all stages quotients of the one ring `C`, so no
bound on the index is needed.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_closedChartData`: a closed subspace whose chart
  rings carry the data of a cartesian square of Stacks 084U is affine.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

section Stage

variable (Y : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
  {V : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal}
  [IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj V)]
  {φ : yoneda.obj V ⟶ Y.1}
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal))) φ)
  {R : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal}
  [IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj R)] {t s : R ⟶ V}
  (hts : yoneda.map t ≫ φ = yoneda.map s ≫ φ)

/-- **A closed subspace carrying the data of a cartesian square of Stacks 084U is affine.** Let
`Z` be a closed subspace with chart data `D`, let `A'` be a ring of cardinality at most that of
`Γ(V)`, and let `P` be an étale `A'`-algebra with surjective spectrum map. Suppose
`α : A' → C ⧸ K_Z` and `ψ : P → C ⧸ K_Z` agree on `A'`, and that
`(C ⧸ K_Z) ⊗_{A'} P → E ⧸ K_Z E`, `c ⊗ p ↦ s̄ c · t̄ (ψ p)`, is bijective. Then `Z` is affine. -/
theorem isAffineSpace_of_closedChartData {Z : ClosedSubspaces B _ B.contains_terminal Y.1}
    (D : ClosedChartData Y he hts Z) {A' P : Type u} [CommRing A'] [CommRing P] [Algebra A' P]
    [Algebra.Etale A' P] (hsurjP : Function.Surjective (PrimeSpectrum.comap (algebraMap A' P)))
    (hA' : #A' ≤ #Γ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj V, ⊤))
    (α : A' →+* Γ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj V, ⊤) ⧸
      chartIdealAt B _ _ Y he Z)
    (ψ : P →+* Γ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj V, ⊤) ⧸
      chartIdealAt B _ _ Y he Z) (hψ : ψ.comp (algebraMap A' P) = α)
    (hbij : letI := α.toAlgebra
      ∃ h, Function.Bijective (Stacks.AffineStageCore.tensorLift (A := A')
        (Stacks.AffineStageCore.sBar
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).map s).appTop.hom
          (chartIdealAt B _ _ Y he Z))
        ((Stacks.AffineStageCore.tBar
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).map s).appTop.hom
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).map t).appTop.hom
          (chartIdealAt B _ _ Y he Z) (map_chartIdealAt_eq Y he hts Z)).comp ψ) h)) :
    IsAffineSpace B _ B.contains_terminal Z.1.toFunctor := by
  let Gm := BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal
  have hV' := D.isAffine_V'
  have hR' := D.isAffine_R'
  let X := Gm.obj D.V'
  let αV : A' →+* Γ(X, ⊤) := D.eV.symm.toRingHom.comp α
  let ψV : P →+* Γ(X, ⊤) := D.eV.symm.toRingHom.comp ψ
  -- the spectra of `A'` and `P` are objects of the site
  have hA'c : B.Contains (Spec (CommRingCat.of A')) := by
    refine lt_of_le_of_lt ?_ (show (Gm.obj V).size < B.cutoff from V.left.2)
    rw [Scheme.size_Spec, Scheme.size_of_isAffine (Gm.obj V)]
    exact max_le_max le_rfl hA'
  have hPc : B.Contains (Spec (CommRingCat.of P)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A' P hA'c
  let SA := terminalObj B B.contains_terminal hA'c
  let SP := terminalObj B B.contains_terminal hPc
  let π : SP ⟶ SA :=
    terminalHomMk B B.contains_terminal (Spec.map (CommRingCat.ofHom (algebraMap A' P)))
  let a : D.V' ⟶ SA :=
    terminalHomMk B B.contains_terminal (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom αV))
  let b : D.V' ⟶ SP :=
    terminalHomMk B B.contains_terminal (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψV))
  have h2 : ∀ x, ψV (algebraMap A' P x) = αV x := fun x => by simp [αV, ψV, ← hψ]
  have hψV : CommRingCat.ofHom (algebraMap A' P) ≫ CommRingCat.ofHom ψV = CommRingCat.ofHom αV :=
    CommRingCat.hom_ext (RingHom.ext h2)
  have hab : b ≫ π = a := by
    apply BigFppfOver.map_toScheme_injective
    change (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψV)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A' P)) = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom αV)
    rw [Category.assoc, ← Spec.map_comp, hψV]
  -- the two projections agree on `A'`
  let : Algebra A'
      (Γ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj V, ⊤) ⧸
        chartIdealAt B _ _ Y he Z) :=
    α.toAlgebra
  obtain ⟨h, hb⟩ := hbij
  have hst' :
      CommRingCat.ofHom αV ≫
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).map D.s'').appTop =
        CommRingCat.ofHom αV ≫
          ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).map D.t'').appTop := by
    ext x
    apply D.eR.injective
    change D.eR
        (((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).map D.s'').appTop.hom
          (D.eV.symm (α x))) =
      D.eR
        (((BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).map D.t'').appTop.hom
          (D.eV.symm (α x)))
    rw [D.eR_s, D.eR_t, RingEquiv.apply_symm_apply]
    have h1 := congrArg (fun f => f x) h
    simp only [RingHom.comp_apply] at h1
    change _ = _ at h1
    refine h1.trans ?_
    rw [← RingHom.comp_apply ψ, hψ]
  have hsa : D.s'' ≫ a = D.t'' ≫ a := by
    apply BigFppfOver.map_toScheme_injective
    change Gm.map D.s'' ≫ X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom αV) =
      Gm.map D.t'' ≫ X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom αV)
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hst']
  -- `Spec P ⟶ Spec A'` is flat and surjective
  have : Module.FaithfullyFlat A' P := Module.FaithfullyFlat.of_comap_surjective hsurjP
  have hff : (CommRingCat.ofHom (algebraMap A' P)).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  obtain ⟨hflat, hsurjπ⟩ := (flat_and_surjective_SpecMap_iff _).2 hff
  have : Flat (Gm.map π) := hflat
  have : Surjective (Gm.map π) := hsurjπ
  -- the square is cartesian on the chart
  have hτ : ∀ p, D.eR ((Gm.map D.t'').appTop.hom (ψV p)) =
      ((Stacks.AffineStageCore.tBar (Gm.map s).appTop.hom (Gm.map t).appTop.hom
        (chartIdealAt B _ _ Y he Z) (map_chartIdealAt_eq Y he hts Z)).comp ψ) p := by
    intro p
    change D.eR ((Gm.map D.t'').appTop.hom (D.eV.symm (ψ p))) = _
    rw [D.eR_t, RingEquiv.apply_symm_apply]
    rfl
  let iA : Algebra A' Γ(X, ⊤) := αV.toAlgebra
  have h' : (Gm.map D.s'').appTop.hom.comp (algebraMap A' Γ(X, ⊤)) =
      ((Gm.map D.t'').appTop.hom.comp ψV).comp (algebraMap A' P) := by
    ext x
    have h1 := congrArg (fun f => f x) hst'
    simp only [RingHom.comp_apply]
    rw [h2]
    exact h1
  have hbV : Function.Bijective (Stacks.AffineStageCore.tensorLift (A := A')
      (Gm.map D.s'').appTop.hom ((Gm.map D.t'').appTop.hom.comp ψV) h') :=
    Stacks.AffineStageCore.bijective_tensorLift_of_ringEquiv D.eV
      (fun a => RingEquiv.apply_symm_apply _ _) D.eR _ _ _ _ (fun x => D.eR_s x) hτ h h' hb
  have hiso := isIso_lift_of_bijective (Gm.map D.s'') (Gm.map D.t'')
    (CommRingCat.ofHom αV) (CommRingCat.ofHom ψV) hψV hst' ⟨h', hbV⟩
  exact isAffineSpace_of_isIso_lift Z.2.1 D.f D.t'' D.s'' D.isPullback D.surj D.etale π a b hab
    hsa hV' (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) hiso

/-- **Stacks 07SQ for a directed system of closed subspaces, over the terminal base.** Let `Y` be
a quasi-compact separated algebraic space and `(Zᵢ)` a directed antitone family of closed
subspaces of `Y`. If the intersection `⋂ Zᵢ`, which is the limit of the family, is affine, then
some `Zᵢ` beyond any given index is affine. No bound on the index is needed. -/
theorem exists_isAffineSpace_of_closedSubspaces_terminal
    (Y : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
    (hYqc : IsQuasiCompactSpace B _ B.contains_terminal Y.1)
    (hYsep : IsAbsolutelySeparated B _ B.contains_terminal B.contains_terminal Y.1)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] (i₀ : ι)
    (Z : ι → ClosedSubspaces B _ B.contains_terminal Y.1) (hZ : ∀ ⦃i j⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
    (haff : IsAffineSpace B _ B.contains_terminal (⨅ i, (Z i).1).toFunctor) :
    ∃ i, i₀ ≤ i ∧ IsAffineSpace B _ B.contains_terminal (Z i).1.toFunctor := by
  have : Nonempty ι := ⟨i₀⟩
  let Gm := BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal
  obtain ⟨V, R, φ, t, s, _, _, hsurj, het, hR⟩ :=
    exists_affine_chart_affine_relation Y B.contains_terminal hYqc hYsep
  let K : ι → Ideal Γ(Gm.obj V, ⊤) := fun i => chartIdealAt B _ _ Y het (Z i)
  have hK : Monotone K := fun i j hij =>
    definingIdealAt_antitone B _ _ Y (Z j) (Z i) (hZ hij) _
  have hinv : ∀ i, (K i).map (Gm.map t).appTop.hom = (K i).map (Gm.map s).appTop.hom :=
    fun i => map_chartIdealAt_eq Y het hR.w (Z i)
  have hcl : IsClosedSubspace B _ B.contains_terminal (⨅ i, (Z i).1) :=
    isClosedSubspace_sInf B _ _ Y.2 (Set.range fun i => (Z i).1)
      (Set.forall_mem_range.2 fun i => (Z i).2)
  let Zinf : ClosedSubspaces B _ B.contains_terminal Y.1 := ⟨⨅ i, (Z i).1, hcl⟩
  have hKinf : chartIdealAt B _ _ Y het Zinf = ⨆ i, K i :=
    le_antisymm (chartIdealAt_iInf_le Y het Z hcl)
      (iSup_le fun i => definingIdealAt_antitone B _ _ Y Zinf (Z i) (iInf_le _ i) _)
  obtain ⟨A, _, _, hEt, hFF, hst, hb⟩ :=
    exists_effective_of_isAffineSpace hR.w (nonempty_closedChartData hsurj hR Zinf).some haff
  -- `E` is étale, hence of finite presentation, over `C` through `s`
  have hfp : @Algebra.FinitePresentation Γ(Gm.obj V, ⊤) Γ(Gm.obj R, ⊤) _ _
      (Gm.map s).appTop.hom.toAlgebra := by
    let := (Gm.map s).appTop.hom.toAlgebra
    have : Algebra.Etale Γ(Gm.obj V, ⊤) Γ(Gm.obj R, ⊤) :=
      HasRingHomProperty.appTop (P := @Etale) (Gm.map s) (het.2 φ (yoneda.map t) s hR)
    infer_instance
  obtain ⟨m, k, hi₀m, hmk, P, _, _, α, ψ, hEtP, hsurjP, -, hψ, h, hbk⟩ :=
    Stacks.AffineStageCore.exists_stage_data_of_eq (Gm.map s).appTop.hom (Gm.map t).appTop.hom
      K hK hinv (chartIdealAt B _ _ Y het Zinf) hKinf (map_chartIdealAt_eq Y het hR.w Zinf) A hst hb
      hfp i₀
  have hA' : #(Stacks.AffineStageCore.eqStage (Gm.map s).appTop.hom (Gm.map t).appTop.hom (K m)
      (hinv m)) ≤ #Γ(Gm.obj V, ⊤) :=
    (Cardinal.mk_subtype_le _).trans (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective)
  exact ⟨k, hi₀m.trans hmk, isAffineSpace_of_closedChartData Y het hR.w
    (nonempty_closedChartData hsurj hR (Z k)).some hsurjP hA' α ψ hψ ⟨h, hbk⟩⟩

end Stage

end AlgebraicGeometry.Space

end
