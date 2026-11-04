module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelativeFunctorial
public import StacksFrontier.CategoryTheory.Triangulated.NaturalTriangleCoproducts

/-!
# Direct sums and derived direct images, by induction on elementary distinguished squares

Let `x : X ⟶ Z` be a morphism of algebraic spaces over a scheme `S`, with `X` quasi-compact and
quasi-separated, and let `G : D(𝒪_Z) ⥤ 𝒯` be an exact functor. This file reduces the statement

  *`G ∘ Rx_*` commutes with the direct sum of every admissible family of objects of `D(𝒪_X)`*

to the same statement for the affine objects `Y` étale over `X`, the admissibility of a family
being any condition stable under étale restriction (for instance: all members have
quasi-coherent cohomology). This is the route to [Stacks, Tag 08FB] through the induction
principle [Stacks, Tag 08GP]: across an elementary distinguished square `(U ⊆ W, V ⟶ W)` the
relative Mayer–Vietoris triangles of [Stacks, Tag 08JK] are natural in the object, so the
direct-sum comparison morphisms at `W` are controlled by those at `U`, `V` and `U ×_W V`
(`CategoryTheory.Pretriangulated.isIso_sigmaComparison_of_natTrans_distTriang`).

## Main results

* `AlgebraicGeometry.Space.isIso_sigmaComparison_derivedPushforward_of_square`: the step across
  one elementary distinguished square.
* `AlgebraicGeometry.Space.isIso_sigmaComparison_derivedPushforward_of_affine`: the induction.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08JK](https://stacks.math.columbia.edu/tag/08JK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T : Type*} [Category T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] (I : Type w)
  [HasCoproductsOfShape I T]
  [∀ Y : AlgebraicSpaces B S hS,
    HasCoproductsOfShape I (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))]

omit [Preadditive T] [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] in
/-- The direct-sum comparison morphism of `G ∘ Rc ∘ e^*` at a family is invertible when those of
the restriction `e^*` at the family and of `G ∘ Rc` at the restricted family are. -/
lemma isIso_sigmaComparison_etaleModulePullback_comp {Y W Z : AlgebraicSpaces B S hS}
    (e : Y ⟶ W) (he : IsEtale B S hS e.hom)
    (Rc : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (G : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ T)
    (K : I → DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hp : IsIso (sigmaComparison (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory K))
    (hc : IsIso (sigmaComparison (Rc ⋙ G)
      fun i ↦ (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory.obj (K i))) :
    IsIso (sigmaComparison (((etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory ⋙ Rc) ⋙ G)
      K) := by
  have h : IsIso (sigmaComparison
      ((etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory ⋙ (Rc ⋙ G)) K) := by
    rw [sigmaComparison_comp]
    infer_instance
  exact h

variable {I} in
/-- **The step across an elementary distinguished square.** Let `(U ⊆ W, V ⟶ W)` be an
elementary distinguished square with intersection `P`, let `w : W ⟶ Z`, and let `Rw`, `Ra`,
`Rb`, `Rc` be right derived functors of the direct images along `w` and along its restrictions
to `U`, `V`, `P`. If the restrictions to `U`, `V`, `P` commute with the direct sum of a family
`K` of objects of `D(𝒪_W)`, and `G ∘ Ra`, `G ∘ Rb`, `G ∘ Rc` commute with the direct sums of the
restricted families, then `G ∘ Rw` commutes with the direct sum of `K`. -/
theorem isIso_sigmaComparison_derivedPushforward_of_square {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) {Z : AlgebraicSpaces B S hS}
    (w : W ⟶ Z) (G : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ T) [G.Additive]
    [G.CommShift ℤ] [G.IsTriangulated]
    (Rw : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αw : (modulePushforward B S hS w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor αw
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (Ra : DerivedCategory (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αa : (modulePushforward B S hS (edsOpenHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ra)
    [Ra.IsRightDerivedFunctor αa (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (Rb : DerivedCategory
        (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αb : (modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rb)
    [Rb.IsRightDerivedFunctor αb (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (Rc : DerivedCategory
        (Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αc : (modulePushforward B S hS (edsInterHom B S hS hsq ≫ w)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rc)
    [Rc.IsRightDerivedFunctor αc (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (K : I → DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hpU : IsIso (sigmaComparison (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory K))
    (hpV : IsIso (sigmaComparison (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory K))
    (hpP : IsIso (sigmaComparison (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory K))
    (hA : IsIso (sigmaComparison (Ra ⋙ G) fun i ↦ (etaleModulePullback.{u, u} B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj (K i)))
    (hB : IsIso (sigmaComparison (Rb ⋙ G) fun i ↦ (etaleModulePullback.{u, u} B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj (K i)))
    (hC : IsIso (sigmaComparison (Rc ⋙ G) fun i ↦ (etaleModulePullback.{u, u} B S hS
      (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj (K i))) :
    IsIso (sigmaComparison (Rw ⋙ G) K) := by
  have hU := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) (edsOpenHom B S hS hsq ≫ w) Ra αa
  have hV := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) (edsEtaleHom B S hS hsq ≫ w) Rb αb
  have hP := isRightDerivedFunctor_restrictPushDerivedUnit B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) (edsInterHom B S hS hsq ≫ w) Rc αc
  obtain ⟨fU, fV', gU, gV, δ, hT⟩ :=
    exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_unconditional B S hS hsq w Rw _ _ _ αw
      _ _ _ inferInstance hU hV hP
  exact isIso_sigmaComparison_of_natTrans_distTriang _ _ _ _ _ _ _ _
    (natMVδWhisker Rw _ δ G) K (natMVTriangle_whiskerRight_mem_distTriang _ _ _ _ _ _ _ _ _ G hT)
    (isIso_sigmaComparison_etaleModulePullback_comp B S hS I _ _ Ra G K hpU hA)
    (isIso_sigmaComparison_etaleModulePullback_comp B S hS I _ _ Rb G K hpV hB)
    (isIso_sigmaComparison_etaleModulePullback_comp B S hS I _ _ Rc G K hpP hC)

/-- **Direct sums and derived direct images, by induction on quasi-compact quasi-separated étale
objects.** Let `x : X ⟶ Z` with `X` quasi-compact and quasi-separated, `G : D(𝒪_Z) ⥤ 𝒯` exact,
and for each algebraic space `Y` let `𝓕_Y` be a class of `I`-indexed families of objects of
`D(𝒪_Y)`, stable under étale restriction, on which étale restriction commutes with direct sums.
If for every affine `Y` étale over `X` along `y`, every right derived functor `R` of `(y ≫ x)_*`
makes `G ∘ R` commute with the direct sums of the families in `𝓕_Y`, then every right derived
functor `R` of `x_*` makes `G ∘ R` commute with the direct sums of the families in `𝓕_X`. This
is the induction principle of Stacks 08GP run with the natural relative Mayer–Vietoris triangles
of Stacks 08JK (`AlgebraicGeometry.Space.isIso_sigmaComparison_derivedPushforward_of_square`). -/
theorem isIso_sigmaComparison_derivedPushforward_of_affine (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Z : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (x : X ⟶ Z)
    (G : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ T) [G.Additive]
    [G.CommShift ℤ] [G.IsTriangulated]
    (𝓕 : ∀ Y : AlgebraicSpaces B S hS,
      (I → DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) → Prop)
    (h𝓕 : ∀ {Y Y' : AlgebraicSpaces B S hS} (e : Y' ⟶ Y) (he : IsEtale B S hS e.hom) K,
      𝓕 Y K → 𝓕 Y' fun i ↦ (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory.obj (K i))
    (hpull : ∀ {Y Y' : AlgebraicSpaces B S hS} (e : Y' ⟶ Y) (he : IsEtale B S hS e.hom) K,
      𝓕 Y K → IsIso (sigmaComparison (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory K))
    (haff : ∀ (Y : AlgebraicSpaces B S hS) (y : Y ⟶ X), IsEtale B S hS y.hom →
      IsAffineSpace B S hS Y.1 → ∀ K, 𝓕 Y K →
      ∀ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS (y ≫ x)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
        IsIso (sigmaComparison (R ⋙ G) K))
    (K : I → DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hK : 𝓕 X K)
    (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (α : (modulePushforward B S hS x).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    IsIso (sigmaComparison (R ⋙ G) K) := by
  let Φ : (Y : AlgebraicSpaces B S hS) → (Y ⟶ Z) → Prop := fun Y m =>
    ∀ K, 𝓕 Y K → ∀ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS m).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
        IsIso (sigmaComparison (R ⋙ G) K)
  have hcongr : ∀ {Y : AlgebraicSpaces B S hS} {m m' : Y ⟶ Z}, m = m' → Φ Y m → Φ Y m' := by
    rintro _ _ _ rfl h; exact h
  have hstep : ∀ {Y : AlgebraicSpaces B S hS} (m : Y ⟶ Z), Φ Y m → ∀ K, 𝓕 Y K →
      ∃ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS m).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) ∧
        IsIso (sigmaComparison (R ⋙ G) K) := by
    intro Y m hm K hK
    have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS
      (X := Y) (Z := Z) (modulePushforward B S hS m)
    let F := (modulePushforward B S hS m).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
    let α := F.totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    exact ⟨_, α, inferInstance, hm K hK _ α inferInstance⟩
  have key := qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Yp φ => ∀ hY : IsAlgebraicSpace B S hS Yp, IsEtale B S hS φ →
      Φ ⟨Yp, hY⟩ (ObjectProperty.homMk φ ≫ x))
    (fun V hV hY hφ K hK R α hR =>
      haff ⟨V.1.left.1, hY⟩ (ObjectProperty.homMk V.1.hom.hom) hφ hV K hK R α hR)
    (by
      intro W V U f hcomm hsq _ _ _ _ hU hV hInter hY hφ K hK R α hR
      let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hY⟩
      have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 U f := hsq
      let w : W' ⟶ Z := ObjectProperty.homMk W.1.hom.hom ≫ x
      have hUΦ : Φ (edsOpen B S hS hsq') (edsOpenHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ rfl)).trans (Category.assoc _ _ _))
          (hU hsq'.isOpenSubspace.1 (isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq') W.2))
      have hVΦ : Φ (edsEtale B S hS hsq') (edsEtaleHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ hcomm.symm)).trans
            (Category.assoc _ _ _))
          (hV hsq'.isAlgebraicSpace V.2)
      have hPΦ : Φ (edsInter B S hS hsq') (edsInterHom B S hS hsq' ≫ w) :=
        hcongr ((congrArg (· ≫ x) (ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm)).trans
            (Category.assoc _ _ _))
          (hInter (edsInter B S hS hsq').2 (by
            simpa only [Category.assoc] using
              isEtale_comp B S hS (f := pullback.fst U.ι f ≫ U.ι)
                (isEtale_edsInterHom B S hS hsq') W.2))
      obtain ⟨Ra, αa, _, hA⟩ := hstep _ hUΦ _ (h𝓕 _ _ K hK)
      obtain ⟨Rb, αb, _, hB⟩ := hstep _ hVΦ _ (h𝓕 _ _ K hK)
      obtain ⟨Rc, αc, _, hC⟩ := hstep _ hPΦ _ (h𝓕 _ _ K hK)
      exact isIso_sigmaComparison_derivedPushforward_of_square B S hS hsq' w G R α Ra αa Rb αb
        Rc αc K (hpull _ _ K hK) (hpull _ _ K hK) (hpull _ _ K hK) hA hB hC)
  exact hcongr (ObjectProperty.hom_ext _ (Category.id_comp _))
    (key X.2 (isEtale_id B S hS X.1)) K hK R α inferInstance

end AlgebraicGeometry.Space

end
