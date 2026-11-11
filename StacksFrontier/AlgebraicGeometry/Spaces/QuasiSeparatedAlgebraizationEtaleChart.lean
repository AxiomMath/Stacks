module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedChartCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAlgebraizationChartClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAlgebraizationOpenChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAlgebraizationClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFibreFlatAtClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseObjectNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints

/-!
# An étale chart of the source carrying the algebraized morphisms

This is steps 2 and 3 of the design of the quasi-separated case of Stacks 0GHK
(`StacksFrontier/AlgebraicGeometry/Spaces/MorphismAlgebraizationQuasiSeparated.lean`).

Let `A` be a Noetherian ring complete with respect to an ideal `I`, `S = Spec A`, `X` proper over
`S`, `Y` quasi-separated and of finite type over `S`, and `g_n : X_n ⟶ Y_n` a compatible system of
morphisms between the adic fibres. There is an étale, surjective, quasi-compact and separated
`π : E ⟶ X` together with a morphism `ψ : E ⟶ Y` over `S` whose adic fibres are
`E_n ⟶ X_n ⟶ Y_n`.

The proof: `Y` has an étale chart `V ⟶ Y` from an affine scheme, with a proper compactification
`V ⊆ Ṽ ⊆ V̄ ×_S P` (`AlgebraicGeometry.Space.exists_chartCompactification`); the fibre products
`X_n ×_Y Ṽ` algebraize to a closed subspace `W` of `F ×_S P` proper over `S`
(`AlgebraicGeometry.Space.exists_algebraization_chartClosure`); an open subspace of `W` has
adic fibres `X_n ×_Y V` and maps to `V`
(`AlgebraicGeometry.Space.exists_isOpenSubspace_chart_adicFibre`); on the étale locus of its
projection to `X` near the closed fibre
(`AlgebraicGeometry.Space.exists_isOpenSubspace_isEtale_of_forall_isEtale_adicFibreMap`) the
projection is étale, its image is open and contains the closed fibre, hence is everything because
`X` is proper over `S` (`AlgebraicGeometry.Space.eq_univ_of_isOpen_of_range_adicFibre_subset`).

## Main results

* `AlgebraicGeometry.Space.exists_isEtale_adicFibreMap_eq_comp`: the étale chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}

/-- **An étale chart of the source carrying the algebraized morphisms.** Let `A` be a Noetherian
ring complete with respect to an ideal `I`, `X` proper and `Y` quasi-separated and of finite type
over `S = Spec A`, and `g_n : X_n ⟶ Y_n` a compatible system of morphisms over the thickenings
`S_n = Spec (A / I^{n+1})`. There are an algebraic space `E`, a morphism `π : E ⟶ X` which is
étale, surjective, quasi-compact and separated, and a morphism `ψ : E ⟶ Y` over `S` whose adic
fibres are `π_n` followed by `g_n`. -/
theorem exists_isEtale_adicFibreMap_eq_comp [IsNoetherianRing A] [IsAdicComplete I A]
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX) (hqY : IsQuasiSeparated B _ hS fY) (hfY : IsFiniteType B _ hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃ (E : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B _ hS E)
      (π : E ⟶ X) (ψ : E ⟶ Y) (hψ : ψ ≫ fY = π ≫ fX),
      IsEtale B _ hS π ∧ IsSurjective B _ hS π ∧ IsQuasiCompact B _ hS π ∧
        IsSeparated B _ hS π ∧
      ∀ n, adicFibreMap A I B hS hSn ψ hψ n = adicFibreMap A I B hS hSn π rfl n ≫ g n := by
  obtain rfl : hSn = contains_adicThickening A I B hS := rfl
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  -- step 2: the chart of `Y` and its compactification
  obtain ⟨V, v, P, p, o, Vb, πb, Vt, k, c, hv, hvs, hp, ho, hVb, hπb, hVt, hk, hc, hkv, hko⟩ :=
    exists_chartCompactification hY hqY hfY
  have hPyo := isAlgebraicSpace_yoneda B _ hS P
  -- step 3: algebraize the closure over `X`
  obtain ⟨F, hF, π, u, hπfin, hπprop, hsqu, hu, W, hW, i, hi, hWp, e, he1, he2⟩ :=
    exists_algebraization_chartClosure hX hY hpX g hgc p hp hVb hVt πb hπb c hc
  obtain ⟨E, ℓ, hE, hℓ, het, hsurj0, hid⟩ :=
    exists_isOpenSubspace_chart_adicFibre hX hY g hg v hv hvs p o ho hVb πb k hk c hkv hko
      hF π u hsqu hu hW i e he1 he2
  -- the projection `E ⟶ X`
  let f₁ : E.toFunctor ⟶ X := E.ι ≫ i ≫ pullback.fst _ _ ≫ π
  have hM : IsAlgebraicSpace B _ hS (pullback (π ≫ fX) (yoneda.map p)) :=
    isAlgebraicSpace_pullback B _ hS _ _ hF hPyo hbase
  have hfstM : IsProper B _ hS (pullback.fst (π ≫ fX) (yoneda.map p)) :=
    isProper_pullback_fst B _ hS hPyo hbase hF (yoneda.map p) (π ≫ fX) hp
  have hπp : IsProper B _ hS π :=
    ((isFinite_iff_isAffineHom_and_isProper B _ hS hF hX π).mp hπfin).2
  have hπW : IsProper B _ hS (i ≫ pullback.fst _ _ ≫ π) :=
    isProper_comp' B _ hS _ _ hM hX (isProper_of_isClosedImmersion B _ hS hW hM _ hi)
      (isProper_comp' B _ hS _ _ hF hX hfstM hπp)
  have hEimm : IsImmersion B _ hS E.ι := isImmersion_of_isOpenImmersion B _ hS hE.2
  have hlf : IsLocallyOfFiniteType B _ hS f₁ :=
    isLocallyOfFiniteType_comp' B _ hS _ _ hW hX
      (isLocallyOfFiniteType_of_isImmersion B _ hS _ hEimm) hπW.2.1.1
  -- the étale locus near the closed fibre
  obtain ⟨W', hW'o, hW'th, hW'et⟩ :=
    exists_isOpenSubspace_isEtale_of_forall_isEtale_adicFibreMap (A := A) (I := I) (B := B)
      (hS := hS) (hSn := contains_adicThickening A I B hS) hE.1 hX
      (fT := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) hpX.2.1.1 f₁
      (by simp only [f₁, Category.assoc]) hlf het
  refine ⟨W'.toFunctor, hW'o.1, W'.ι ≫ f₁, W'.ι ≫ ℓ ≫ v, eq_of_hom_yoneda_baseObject _ _,
    hW'et, ?_, ?_, ?_, fun n => ?_⟩
  · -- surjective: the image is open and contains the closed fibre
    have hopen : IsOpen (Set.range (pointsMap B _ hS _ (W'.ι ≫ f₁))) := by
      rw [← Set.image_univ]
      exact isOpenMap_pointsMap_of_isEtale B _ hS _ hW'o.1 hX hW'et _ isOpen_univ
    have hsub : Set.range (pointsMap B _ hS _ (pullback.fst fX
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) 0)))) ⊆
        Set.range (pointsMap B _ hS _ (W'.ι ≫ f₁)) := by
      rintro _ ⟨x0, rfl⟩
      obtain ⟨y, hy⟩ := hsurj0 x0
      refine ⟨pointsMap B _ hS _ (Subfunctor.lift _ (hW'th 0)) y, ?_⟩
      have hl := Subfunctor.lift_ι _ (hW'th 0)
      rw [← pointsMap_comp_apply, reassoc_of% hl, ← hy, ← pointsMap_comp_apply, adicFibreMap_fst]
    have huniv := eq_univ_of_isOpen_of_range_adicFibre_subset (IsAdicComplete.le_jacobson_bot I)
      fX hpX.2.2 hopen hsub
    exact Set.range_eq_univ.1 huniv
  · -- quasi-compact: an immersion into the Noetherian space `W`, followed by a proper morphism
    have hN := isNoetherian_of_isProper_baseObject A B hS W hW _ hWp
    have hqc := isQuasiCompact_of_isImmersion_of_isNoetherian B _ hS B.contains_terminal hW
      hW'o.1 hN (W'.ι ≫ E.ι)
      (isImmersion_comp B _ hS _ _ (isImmersion_of_isOpenImmersion B _ hS hW'o.2) hEimm)
    have h := isQuasiCompact_comp B _ hS hW hX _ _ hqc hπW.2.1.2
    simpa only [f₁, Category.assoc] using h
  · -- separated
    have h := isSeparated_comp B _ hS _ _
      (isSeparated_of_isImmersion B _ hS
        (isImmersion_comp B _ hS _ _ (isImmersion_of_isOpenImmersion B _ hS hW'o.2) hEimm))
      hπW.1
    simpa only [f₁, Category.assoc] using h
  · -- the adic fibres of `ψ`
    have h1 : adicFibreMap A I B hS (contains_adicThickening A I B hS)
        (fF := (W'.ι ≫ f₁) ≫ fX) (fG := fY) (W'.ι ≫ ℓ ≫ v)
        (eq_of_hom_yoneda_baseObject _ _) n =
        adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (fF := (W'.ι ≫ f₁) ≫ fX) (fG := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) W'.ι
          (by simp only [f₁, Category.assoc]) n ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fY)
          (ℓ ≫ v) (eq_of_hom_yoneda_baseObject _ _) n := by
      apply pullback.hom_ext <;> simp
    have h2 : adicFibreMap A I B hS (contains_adicThickening A I B hS)
        (fF := (W'.ι ≫ f₁) ≫ fX) (fG := fX) (W'.ι ≫ f₁) rfl n =
        adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (fF := (W'.ι ≫ f₁) ≫ fX) (fG := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) W'.ι
          (by simp only [f₁, Category.assoc]) n ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fX)
          (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) n := by
      apply pullback.hom_ext <;> simp [f₁]
    rw [h1, h2, hid n]
    exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Space

end
