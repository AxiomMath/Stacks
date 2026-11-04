module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPullbackTensorTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.Tactic.HEqCongr

/-!
# Condition (2) of Stacks 0DKG for derived tensor products

For a commutative square `g' ≫ f = f' ≫ g` of algebraic spaces, quasi-coherent `E`, `K` on `X`,
`K'` on `X'` and `φ : L(g')^*K ⟶ K'`: if condition (2) of Stacks 0DKG holds for `(K, K', φ)`, it
holds for `(E ⊗ᴸ K, L(g')^*E ⊗ᴸ K')` and Stacks 07A4 followed by `L(g')^*E ⊗ᴸ φ`. This is the
chartwise form of the tensor step of Stacks 0DKI (1).

## Main results

* `AlgebraicGeometry.Space.affineChartwiseBaseChange_tensor`: condition (2) of Stacks 0DKG for
  `(K, K', φ)` implies it for `(E ⊗ᴸ K, L(g')^*E ⊗ᴸ K')` and Stacks 07A4 followed by
  `L(g')^*E ⊗ᴸ φ`, for quasi-coherent `E`, `K`, `K'`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_pullback_tensor_iff`: the same
  transfer on one affine chart, for the base change maps.
* `Stacks.Generic.chartTensor_eq_of_compatible`: the underlying identity, for abstract functors
  and bifunctors with compatible comparisons around a square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.Generic

/-- The inverse of the comparison of the two composites around a square, for a composite
identification `e₁ ≪≫ e₂`, as the explicit composite. -/
theorem squareCompositeIso_inv_app_trans {S T S' T' : Type*} [Category S] [Category T]
    [Category S'] [Category T'] {Lg : S ⥤ S'} {Lf' : S' ⥤ T'} {Lf : S ⥤ T} {Lg' : T ⥤ T'}
    {Lc Lc₀ : S ⥤ T'} (eg : Lg ⋙ Lf' ≅ Lc) (e₁ : Lf ⋙ Lg' ≅ Lc₀) (e₂ : Lc₀ ≅ Lc) (X : S) :
    e₁.hom.app X ≫ e₂.hom.app X ≫ eg.inv.app X =
      (Stacks.AffineProjectionFormula.squareCompositeIso eg (e₁ ≪≫ e₂)).inv.app X := by
  rw [Stacks.AffineProjectionFormula.squareCompositeIso_inv_app, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc]

/-- A natural transformation between uncurried bifunctors, read on a morphism in the second
variable. -/
theorem natTrans_uncurry_naturality_right {C₁ C₂ D₁ D₂ : Type*} {_ : Category C₁}
    {_ : Category C₂} {_ : Category D₁} {_ : Category D₂} {F : C₁ ⥤ C₁ ⥤ C₂}
    {G : D₁ ⥤ D₁ ⥤ D₂} {L : C₁ ⥤ D₁} {L' : C₂ ⥤ D₂}
    (α : Functor.uncurry.obj F ⋙ L' ⟶ L.prod L ⋙ Functor.uncurry.obj G) (X : C₁) {Y Y' : C₁}
    (f : Y ⟶ Y') :
    L'.map ((F.obj X).map f) ≫ α.app (X, Y') = α.app (X, Y) ≫ (G.obj (L.obj X)).map (L.map f) := by
  have h := α.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, f)
  simpa using h

/-- The bookkeeping of the chartwise tensor step, for arbitrary morphisms: the compatibility
`compat` of the four comparisons around a square, moved past `φk`. -/
theorem chartTensor_chain_eq {C : Type*} {_ : Category C} (Fy : C ⥤ C)
    {o₀ o₁ p₀ p₁ p₂ p₃ p₄ n₁ n₂ n₃ n₄ n₅ q₁ q₂ : C}
    (A : o₀ ⟶ o₁) (Bm : o₁ ⟶ Fy.obj n₁) (k₁ : n₁ ⟶ n₂) (k₂ : n₂ ⟶ n₃) (k₃ : n₃ ⟶ n₄)
    (sK : n₁ ⟶ n₄) (σK : n₄ ⟶ n₁) (φk : n₄ ⟶ n₅) (t₁ : o₀ ⟶ q₁) (t₂ : q₁ ⟶ q₂) (t₃ : q₂ ⟶ p₀)
    (s : o₀ ⟶ p₀) (σh : p₀ ⟶ o₀) (L₁ : p₀ ⟶ p₁) (L₂ : p₁ ⟶ p₂) (Ll : p₀ ⟶ p₂) (R₁ : p₁ ⟶ p₃)
    (R₁' : p₂ ⟶ p₄) (Nφ : p₃ ⟶ p₄) (X₁ : p₃ ⟶ Fy.obj n₄) (XX : p₃ ⟶ Fy.obj n₁)
    (Xf : p₄ ⟶ Fy.obj n₅)
    (hk : k₁ ≫ k₂ ≫ k₃ = sK) (hs : t₁ ≫ t₂ ≫ t₃ = s) (hLl : Ll = L₁ ≫ L₂)
    (hsσ : s ≫ σh = 𝟙 _) (hXX : XX = X₁ ≫ Fy.map σK) (compat : L₁ ≫ R₁ ≫ XX = σh ≫ A ≫ Bm)
    (hX : Fy.map σK ≫ Fy.map sK = 𝟙 _) (nat₂ : X₁ ≫ Fy.map φk = Nφ ≫ Xf)
    (nat₀ : L₂ ≫ R₁' = R₁ ≫ Nφ) :
    A ≫ Bm ≫ Fy.map (k₁ ≫ k₂ ≫ k₃ ≫ φk) = (t₁ ≫ t₂ ≫ t₃ ≫ Ll) ≫ R₁' ≫ Xf := by
  subst hk hs hLl hXX
  simp only [Functor.map_comp, Category.assoc] at compat hX nat₂ nat₀ ⊢
  calc _ = ((t₁ ≫ t₂ ≫ t₃) ≫ σh) ≫ A ≫ Bm ≫ Fy.map k₁ ≫ Fy.map k₂ ≫ Fy.map k₃ ≫ Fy.map φk := by
          rw [hsσ, Category.id_comp]
    _ = _ := by
          simp only [Category.assoc]
          rw [← reassoc_of% compat]
          simp only [reassoc_of% hX, reassoc_of% nat₀, nat₂]

/-- **The chartwise tensor step, abstractly.** For a square of categories whose two composites
are identified through `eg` and `ef = e₁ ≪≫ e₂`, and bifunctors with comparisons along the four
functors that are compatible at `(M, N)`, the comparison along `Lf` then `Lg'`, followed by the map
attached to `φ : Lg N ⟶ N'`, is the map attached to the comparison along `Lg` followed by
`Lg M ⊗ φ`, through the comparison along `Lf'`. -/
theorem chartTensor_eq_of_compatible {S T S' T' : Type*} [Category S] [Category T]
    [Category S'] [Category T'] {Lf : S ⥤ T} {Lf' : S' ⥤ T'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'}
    {Lc Lc₀ : S ⥤ T'} (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (e₁ : Lf ⋙ Lg' ≅ Lc₀)
    (e₂ : Lc₀ ≅ Lc) (hef : ef = e₁ ≪≫ e₂) (TS : S ⥤ S ⥤ S) (TS' : S' ⥤ S' ⥤ S')
    (TT : T ⥤ T ⥤ T) (TT' : T' ⥤ T' ⥤ T')
    (αf : Functor.uncurry.obj TS ⋙ Lf ⟶ Lf.prod Lf ⋙ Functor.uncurry.obj TT)
    (αf' : Functor.uncurry.obj TS' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ Functor.uncurry.obj TT')
    (αg : Functor.uncurry.obj TS ⋙ Lg ⟶ Lg.prod Lg ⋙ Functor.uncurry.obj TS')
    (αg' : Functor.uncurry.obj TT ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ Functor.uncurry.obj TT')
    (M N : S) (N' : S') (φ : Lg.obj N ⟶ N')
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef
      (Functor.uncurry.obj TS) (Functor.uncurry.obj TS') (Functor.uncurry.obj TT)
      (Functor.uncurry.obj TT') αf αf' αg αg' M N) :
    Lg'.map (αf.app (M, N) : Lf.obj ((TS.obj M).obj N) ⟶ (TT.obj (Lf.obj M)).obj (Lf.obj N)) ≫
        (αg'.app (Lf.obj M, Lf.obj N) :
          Lg'.obj ((TT.obj (Lf.obj M)).obj (Lf.obj N)) ⟶ (TT'.obj (Lg'.obj (Lf.obj M))).obj
            (Lg'.obj (Lf.obj N))) ≫
        (TT'.obj (Lg'.obj (Lf.obj M))).map
          (e₁.hom.app N ≫ e₂.hom.app N ≫ eg.inv.app N ≫ Lf'.map φ : Lg'.obj (Lf.obj N) ⟶ Lf'.obj
            N') =
      (e₁.hom.app ((TS.obj M).obj N) ≫ e₂.hom.app ((TS.obj M).obj N) ≫ eg.inv.app
        ((TS.obj M).obj N) ≫
          Lf'.map ((αg.app (M, N) : Lg.obj ((TS.obj M).obj N) ⟶ (TS'.obj (Lg.obj M)).obj
            (Lg.obj N)) ≫
            (TS'.obj (Lg.obj M)).map φ)) ≫
        (αf'.app (Lg.obj M, N') : Lf'.obj ((TS'.obj (Lg.obj M)).obj N') ⟶
          (TT'.obj (Lf'.obj (Lg.obj M))).obj (Lf'.obj N')) ≫
          (TT'.map ((Stacks.AffineProjectionFormula.squareCompositeIso eg ef).hom.app M)).app
            (Lf'.obj N') := by
  subst hef
  exact chartTensor_chain_eq (TT'.obj (Lg'.obj (Lf.obj M))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _
    (squareCompositeIso_inv_app_trans eg e₁ e₂ N) (squareCompositeIso_inv_app_trans eg e₁ e₂ _)
    (Functor.map_comp _ _ _) ((Stacks.AffineProjectionFormula.squareCompositeIso eg
      (e₁ ≪≫ e₂)).inv_hom_id_app _)
    (Functor.uncurry_obj_map _ _) hsq
    ((TT'.obj (Lg'.obj (Lf.obj M))).mapIso
      ((Stacks.AffineProjectionFormula.squareCompositeIso eg (e₁ ≪≫ e₂)).app N)).hom_inv_id
    ((TT'.map
      ((Stacks.AffineProjectionFormula.squareCompositeIso eg (e₁ ≪≫ e₂)).hom.app M)).naturality
      (Lf'.map φ)).symm
    (natTrans_uncurry_naturality_right αf' _ φ)

end Stacks.Generic


namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- `qcohDerived_smallEtaleDerivedTensor`, for objects of the derived category of
`𝒪`-modules in the ringed-topos spelling. -/
theorem qcohDerived_smallEtaleDerivedTensor_obj (Z : AlgebraicSpaces B S hS)
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (hE : QcohDerived B S hS Z E) (hK : QcohDerived B S hS Z K) :
    QcohDerived B S hS Z (((smallEtaleDerivedTensor B S hS Z).obj E).obj K) :=
  qcohDerived_smallEtaleDerivedTensor Z E K hE hK

/-- **The chartwise tensor step, on one chart.** For a commutative square
`g₀' ≫ a = a' ≫ g'`, the composite of Stacks 0DKH for a square `g₀' ≫ f₀ = f₀' ≫ g₀` attached to
the pullback along `a`, `a'` of Stacks 07A4 for `g'` followed by `L(g')^*E ⊗ᴸ φ` is invertible
exactly when the one attached to Stacks 07A4 for `g₀'` followed by `L(g₀')^*a^*E ⊗ᴸ` the pullback
of `φ` is. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_pullback_tensor_iff {U V V' U' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g')
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
      ((smallEtaleDerivedModulePullback B S hS a).obj
      (((smallEtaleDerivedTensor B S hS X).obj E).obj K))
        ((smallEtaleDerivedModulePullback B S hS a').obj
          (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K'))
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀') a).hom.app
          (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app
          (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app
          (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
          (smallEtaleDerivedModulePullback B S hS a').map
            ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
            ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).map φ))) ↔
      IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
        ((smallEtaleDerivedModulePullback B S hS a).obj E)).obj
        ((smallEtaleDerivedModulePullback B S hS a).obj K))
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
          ((smallEtaleDerivedModulePullback B S hS a).obj E))).obj
          ((smallEtaleDerivedModulePullback B S hS a').obj K'))
        ((smallEtaleDerivedPullbackTensorIso (representedSpaceMap B S hS g₀')).hom.app
          ((smallEtaleDerivedModulePullback B S hS a).obj E,
          (smallEtaleDerivedModulePullback B S hS a).obj K) ≫
          ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
            ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
            ((smallEtaleDerivedModulePullback B S hS a).obj E))).map
            ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
            a).hom.app K ≫ (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS a').map φ :
            (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
              ((smallEtaleDerivedModulePullback B S hS a).obj K) ⟶
              (smallEtaleDerivedModulePullback B S hS a').obj K'))) := by
  refine isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS (representedSpaceMap B S hS f₀)
    (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
    (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) _ _ _ _ _
    _
    ((smallEtaleDerivedPullbackTensorIso a).app (E, K) :
      (smallEtaleDerivedModulePullback B S hS a).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≅
        ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
          ((smallEtaleDerivedModulePullback B S hS a).obj E)).obj
          ((smallEtaleDerivedModulePullback B S hS a).obj K))
    ((smallEtaleDerivedPullbackTensorIso a').app
      ((smallEtaleDerivedModulePullback B S hS g').obj E, K') ≪≫
      ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).mapIso
        ((Stacks.AffineProjectionFormula.squareCompositeIso
        (smallEtaleDerivedModulePullbackCompIso B S hS a' g')
        (smallEtaleDerivedModulePullbackSquareIso B S hS a g' a' (representedSpaceMap B S hS g₀')
        ha')).app E)).app ((smallEtaleDerivedModulePullback B S hS a').obj K') :
      (smallEtaleDerivedModulePullback B S hS a').obj
        (((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K') ≅
        ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj
          ((smallEtaleDerivedModulePullback B S hS a).obj E))).obj
          ((smallEtaleDerivedModulePullback B S hS a').obj K')) ?_
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
    (Stacks.Generic.chartTensor_eq_of_compatible _ _ _ _
      (smallEtaleDerivedModulePullbackSquareIso.eq_1 B S hS a g' a' (representedSpaceMap B S hS g₀')
        ha')
      _ _ _ _ _ _ _ _ E K K' φ
      (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso a g' a'
        (representedSpaceMap B S hS g₀') ha' E K))) (by heq_congr)))

/-- **The chartwise tensor step on an affine chart, for the base change maps.** -/
theorem isIso_smallEtaleDerivedBaseChangeComp_chart_tensor {U V V' U' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g')
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K') (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (H : IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
      ((smallEtaleDerivedModulePullback B S hS a).obj K)
      ((smallEtaleDerivedModulePullback B S hS a').obj K')
      ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀') a).hom.app
        K ≫ (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS a').map φ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
      ((smallEtaleDerivedModulePullback B S hS a).obj
      (((smallEtaleDerivedTensor B S hS X).obj E).obj K))
        ((smallEtaleDerivedModulePullback B S hS a').obj
          (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K'))
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀') a).hom.app
          (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app
          (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app
          (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
          (smallEtaleDerivedModulePullback B S hS a').map
            ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
            ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).map φ))) :=
  (isIso_smallEtaleDerivedBaseChangeComp_pullback_tensor_iff B S hS g' a a' f₀ g₀ f₀' g₀' w₀ ha'
    E K K' φ).mpr
    (isIso_representedAffineBaseChangeComp_tensor B S hS f₀ g₀ f₀' g₀' w₀ _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a E hE)
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK) _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK') _ H)

/-- **Condition (2) of Stacks 0DKG passes to derived tensor products.** For quasi-coherent `E`,
`K` on `X`, `K'` on `X'` and `φ : L(g')^*K ⟶ K'`: if condition (2) of Stacks 0DKG holds for
`(K, K', φ)`, it holds for `(E ⊗ᴸ K, L(g')^*E ⊗ᴸ K')` and Stacks 07A4 followed by
`L(g')^*E ⊗ᴸ φ`. -/
theorem affineChartwiseBaseChange_tensor (w : g' ≫ f = f' ≫ g)
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ) :
    AffineChartwiseBaseChange B S hS f g f' g' w (((smallEtaleDerivedTensor B S hS X).obj E).obj K)
      (((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K')
      ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).map φ) := by
  refine ⟨fun U V V' U' _ _ _ _ a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb h₁ h₂ h₃ ha' => ?_⟩
  exact (isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff B S hS f₀ g₀ f₀' g₀' w₀ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a _
      (qcohDerived_smallEtaleDerivedTensor_obj B S hS X E K hE hK)) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' _
      (qcohDerived_smallEtaleDerivedTensor_obj B S hS X' _ K'
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g' E hE) hK')) _).mp
    (isIso_smallEtaleDerivedBaseChangeComp_chart_tensor B S hS g' a a' f₀ g₀ f₀' g₀' w₀ ha' E K hE
      hK K' hK' φ
      ((isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff B S hS f₀ g₀ f₀' g₀' w₀ _
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK) _
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK') _).mpr
        (h.isIso U V V' U' a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb h₁ h₂ h₃ ha')))

end AlgebraicGeometry.Space
