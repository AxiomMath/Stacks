module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InversePointReadingSquares

/-!
# The tensor square of the inverse-line factor of the conormal source

Let `q : ℰ ⟶ ℒ` be an invertible quotient on an algebraic space `X`, `x : T ⟶ X` a scheme point
and `h : T' ⟶ T` a morphism of test objects.  The base change of the inverse-line factor
`i_x : R_T(x^*(ℒ^{⊗ -1})) ≅ R_T(x^*ℒ)^{⊗ -1}` of the conormal source
(`AlgebraicGeometry.Space.inversePointReadingIso_baseChange_of_squares`) needs a tensor square at
`(ℒ^{⊗ -1}, ℒ)` and a unit square.  This file derives the tensor square from the monoidality of the
identification of the point readings (`AlgebraicGeometry.Space.pointReadingBaseChange_tensor_of`)
by inverting the identifications and passing from the monoidal tensor product to the tensor
product sheaf, and combines it with the unit square
(`AlgebraicGeometry.Space.inversePointReadingUnitSquare`).  The only remaining input is the
monoidality of the base change of the Zariski reading, the hypothesis `hc`.

## Main results

* `CategoryTheory.Functor.baseChangeTensorSquare_of_tensorPaste`: the generic paste.
* `AlgebraicGeometry.Space.inversePointReadingTensorSquare_of`: the tensor square, given `hc`.
* `AlgebraicGeometry.Space.inversePointReadingIso_baseChange`: the base change of the
  inverse-line factor, given `hc`.
* `AlgebraicGeometry.Space.conormalSourcePointReading_baseChange`: the base change of the
  conormal source read at scheme points, given `hc`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

/-- **A base-change tensor square from a tensor paste**: the monoidality square
`CategoryTheory.Functor.TensorPasteConclusion` of the identifications `a ≫ a'`, `b ≫ b'` and
`θ ≫ R'(c)`, inverted through `cΛ`, `cL` and `cΛL₀`, and transported along `n₀`, `n'`, is the
square `CategoryTheory.Functor.BaseChangeTensorSquare` of `μ = n₀ ≫ R(m) ≫ Z` and
`μ' = n' ≫ R'(m') ≫ Z''`. -/
theorem CategoryTheory.Functor.baseChangeTensorSquare_of_tensorPaste {𝒜 ℬ 𝒞 𝒟 : Type*}
    [Category 𝒜] [iℬ : Category ℬ] [i𝒞 : Category 𝒞] [Category 𝒟] {P : 𝒞 ⥤ ℬ} {R : 𝒟 ⥤ 𝒞}
    {R' : 𝒜 ⥤ ℬ} {F₀ : 𝒞 ⥤ 𝒞 ⥤ 𝒞} {F₁ : ℬ ⥤ ℬ ⥤ ℬ} {AΛ AL AΛL : 𝒞} {A'Λ A'L A'ΛL : ℬ}
    {cΛ : A'Λ ⟶ P.obj AΛ} {cL : A'L ≅ P.obj AL} {cΛL : A'ΛL ⟶ P.obj AΛL}
    {μ : AΛL ≅ (F₀.obj AΛ).obj AL} {μ' : A'ΛL ≅ (F₁.obj A'Λ).obj A'L}
    {κ : ∀ X Y : 𝒞, P.obj ((F₀.obj X).obj Y) ⟶ (F₁.obj (P.obj X)).obj (P.obj Y)}
    {D D' : 𝒟} {W₁ W₂ : ℬ} {GD Ex E'' : 𝒜} {m : D ⟶ D'} {Z : R.obj D' ⟶ (F₀.obj AΛ).obj AL}
    {a : P.obj AΛ ⟶ W₁} {a' : W₁ ⟶ A'Λ} {b : P.obj AL ⟶ W₂} {b' : W₂ ⟶ A'L}
    {θ : P.obj (R.obj D) ⟶ R'.obj GD} {c : GD ⟶ Ex} {m' : Ex ⟶ E''}
    {Z'' : R'.obj E'' ⟶ (F₁.obj A'Λ).obj A'L} {cΛL₀ : R'.obj Ex ⟶ P.obj (R.obj D)}
    {n₀ : AΛL ⟶ R.obj D} {n' : A'ΛL ⟶ R'.obj Ex}
    (t : CategoryTheory.Functor.TensorPasteConclusion P R R' F₁ m Z (κ AΛ AL) a a' b b' θ c m' Z'')
    (hu : cΛL₀ ≫ θ ≫ R'.map c = 𝟙 _) (hv₁ : (a ≫ a') ≫ cΛ = 𝟙 _) (hv₂ : (b ≫ b') ≫ cL.hom = 𝟙 _)
    (hnat : n' ≫ cΛL₀ = cΛL ≫ P.map n₀) (hμ : μ.hom = n₀ ≫ R.map m ≫ Z)
    (hμ' : μ'.hom = n' ≫ R'.map m' ≫ Z'') :
    CategoryTheory.Functor.BaseChangeTensorSquare F₀ F₁ P cΛ cL cΛL μ μ' κ := by
  have e₁ : ((F₁.map (a ≫ a')).app (P.obj AL) ≫ (F₁.obj A'Λ).map (b ≫ b')) ≫
      ((F₁.map cΛ).app A'L ≫ (F₁.obj (P.obj AΛ)).map cL.hom) = 𝟙 _ := by
    calc _ = (F₁.map (a ≫ a')).app (P.obj AL) ≫ ((F₁.obj A'Λ).map (b ≫ b') ≫
          (F₁.map cΛ).app A'L) ≫ (F₁.obj (P.obj AΛ)).map cL.hom := by
          simp only [Category.assoc]
      _ = (F₁.map (a ≫ a')).app (P.obj AL) ≫ ((F₁.map cΛ).app (P.obj AL) ≫
          (F₁.obj (P.obj AΛ)).map (b ≫ b')) ≫ (F₁.obj (P.obj AΛ)).map cL.hom := by
          rw [(F₁.map cΛ).naturality]
      _ = (F₁.map ((a ≫ a') ≫ cΛ)).app (P.obj AL) ≫
          (F₁.obj (P.obj AΛ)).map ((b ≫ b') ≫ cL.hom) := by
          simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
      _ = 𝟙 _ := by
          rw [hv₁, hv₂]
          simp
  have t' : P.map (R.map m ≫ Z) ≫ κ AΛ AL ≫ ((F₁.map (a ≫ a')).app (P.obj AL) ≫
      (F₁.obj A'Λ).map (b ≫ b')) = θ ≫ R'.map c ≫ R'.map m' ≫ Z'' := t
  have k : P.map (R.map m ≫ Z) ≫ κ AΛ AL = θ ≫ R'.map c ≫ R'.map m' ≫ Z'' ≫
      ((F₁.map cΛ).app A'L ≫ (F₁.obj (P.obj AΛ)).map cL.hom) := by
    calc P.map (R.map m ≫ Z) ≫ κ AΛ AL = (P.map (R.map m ≫ Z) ≫ κ AΛ AL ≫
          ((F₁.map (a ≫ a')).app (P.obj AL) ≫ (F₁.obj A'Λ).map (b ≫ b'))) ≫
          ((F₁.map cΛ).app A'L ≫ (F₁.obj (P.obj AΛ)).map cL.hom) := by
          rw [Category.assoc, Category.assoc, e₁, Category.comp_id]
      _ = _ := by
          rw [t']
          simp only [Category.assoc]
  change cΛL ≫ P.map μ.hom ≫ κ AΛ AL =
    μ'.hom ≫ ((F₁.map cΛ).app A'L ≫ (F₁.obj (P.obj AΛ)).map cL.hom)
  rw [hμ, hμ', P.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat, k, reassoc_of% hu]

/-- If `R(p) ≪≫ z = R(M(t) ≪≫ p') ≪≫ z'`, then `R(p') ≪≫ z'` is `M(t)⁻¹`, then `R(p)`, then `z`
followed by an identity `d`. -/
theorem CategoryTheory.Functor.mapIso_trans_hom_eq_of_trans_eq {𝒞 𝒞' 𝒟 : Type*} [Category 𝒞]
    [Category 𝒞'] [i𝒟 : Category 𝒟] (M : 𝒞 ⥤ 𝒞') (R : 𝒞' ⥤ 𝒟) {A A' : 𝒞} {P₁ P₂ : 𝒞'} {W : 𝒟}
    (t : A ≅ A') (p : M.obj A ≅ P₁) (z : R.obj P₁ ≅ W) (p' : M.obj A' ≅ P₂) (z' : R.obj P₂ ≅ W)
    (d : W ≅ W) (hd : d = Iso.refl W) (k : R.mapIso p ≪≫ z = R.mapIso (M.mapIso t ≪≫ p') ≪≫ z') :
    (R.mapIso p' ≪≫ z').hom = ((M ⋙ R).mapIso t.symm).hom ≫ R.map p.hom ≫ (z.hom ≫ d.hom) := by
  subst hd
  have k' := congrArg Iso.hom k
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at k'
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, Category.comp_id, k',
    Functor.mapIso_hom, Iso.symm_hom, ← Functor.comp_map, Iso.inv_hom_id_map_assoc]

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `AlgebraicGeometry.Space.zariskiReading_mapIso_modulePullbackTensorIso_trans` read on the
tensor comparison `Stacks.SheafOfModules.pullbackTensorIso`. -/
theorem zariskiReading_mapIso_modulePullbackTensorComparison_trans_hom {T : BigFppfOver B S hS}
    {Y : AlgebraicSpaces B S hS} (f : yonedaSpace B S hS T ⟶ Y)
    (F G : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite) :
    ((zariskiReadingFunctor T).mapIso (modulePullbackTensorComparison f G F) ≪≫
        zariskiReadingTensorIso T _ _ hF hG).hom =
      ((modulePullback B S hS f ⋙ zariskiReadingFunctor T).mapIso
          (modulesTensorObjIso B S hS Y.1 Y.2 F G).symm).hom ≫
        (zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS f F G).hom ≫
          ((zariskiReadingTensorObjIso T _ _ hF hG).hom ≫
            (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T) _ _).hom) :=
  CategoryTheory.Functor.mapIso_trans_hom_eq_of_trans_eq (modulePullback B S hS f)
    (zariskiReadingFunctor T) (modulesTensorObjIso B S hS Y.1 Y.2 F G)
    (modulePullbackTensorIso B S hS f F G) (zariskiReadingTensorObjIso T _ _ hF hG)
    (modulePullbackTensorComparison f G F) (zariskiReadingTensorIso T _ _ hF hG)
    (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T) _ _) rfl
    (zariskiReading_mapIso_modulePullbackTensorIso_trans f F G hF hG)

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

/-- `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso_inv_comp_hom` at `ℒ`, with the
identification of the invertible modules of `q_{x ∘ h}` and `τ^*q_x`. -/
theorem sectionPointQuotientBaseChangeL_inv_comp_hom
    [hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    (@CategoryTheory.CategoryStruct.comp _ (@CategoryTheory.Category.toCategoryStruct _
          Scheme.Modules.instCategory) _ _ _ (@CategoryTheory.CategoryStruct.comp _
          (@CategoryTheory.Category.toCategoryStruct _ Scheme.Modules.instCategory) _ _ _
          ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj Q.L))
          (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
            Scheme.Modules.instCategory (zariskiReadingFunctor T')
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
            ((modulePullback B S hS (pointHom x)).obj Q.L))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj Q.L)
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app Q.L)))
          (sectionPointQuotientBaseChangeL X E hE Q x h).hom) = 𝟙 _ :=
  pointZariskiModuleBaseChangeIso_inv_comp_hom X x h Q.L
    (isQuasicoherentOnSite_of_isInvertible B S hS X Q.L hQ)

/-- **The tensor square of the inverse-line factor** at `(ℒ^{⊗ -1}, ℒ)`, the hypothesis `hTh` of
`AlgebraicGeometry.Space.inversePointReadingIso_baseChange_of_squares`, from the monoidality of
the base change of the Zariski reading. -/
theorem inversePointReadingTensorSquare_of
    [hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T)
    (hc : ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
      (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
      CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
            ((zariskiReadingFunctor T).obj (N))).obj ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
              (isAlgebraicSpace_yoneda B S hS T'))
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
            ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
        ((Stacks.RingedSpace.comparisonBifunctorIso
            ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
          ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
        ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
        ((zariskiReadingPullbackHom h).app ((MonoidalCategory.tensorObj
              (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N)
              (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
              (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (representedSpaceMap B S hS h) (N) hN)
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (representedSpaceMap B S hS h) (M) hM)).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (N)))
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (M)))).hom)) :
    CategoryTheory.Functor.BaseChangeTensorSquare
      (𝒞₀ := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (𝒞₁ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (i₀ := Scheme.Modules.instCategory)
      (i₁ := Scheme.Modules.instCategory) (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          ((BigFppfOver.toScheme B S hS).obj T).presheaf (forget₂ CommRingCat RingCat)
          ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          ((BigFppfOver.toScheme B S hS).obj T').presheaf (forget₂ CommRingCat RingCat)
          ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
      (pointZariskiModuleBaseChangeIso X (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)) x h).hom
      (sectionPointQuotientBaseChangeL X E hE Q x h)
      (pointZariskiModuleBaseChangeIso X _ (SheafOfModules.IsQuasicoherentOnSite.of_iso
          (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)).symm
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L _)) x h).hom
      ((zariskiReadingFunctor T).mapIso (modulePullbackTensorComparison (pointHom x) Q.L
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))) ≪≫ zariskiReadingTensorIso T _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) _
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) _
          (isInvertible_modulePullback_obj B S hS (pointHom x) Q.L hQ)))
      ((zariskiReadingFunctor T').mapIso (modulePullbackTensorComparison
          (pointHom (yoneda.map h ≫ x)) Q.L (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))) ≪≫
        zariskiReadingTensorIso T' _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom (yoneda.map h ≫ x)) _ (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))
        (isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T') _
          (isInvertible_modulePullback_obj B S hS (pointHom (yoneda.map h ≫ x)) Q.L hQ)))
      (fun X Y => (Stacks.RingedSpace.comparisonBifunctorIso
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app (X, Y)) := by
  have hq₁ := SheafOfModules.IsQuasicoherentOnSite.of_iso
    (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property Q.L (-1)).symm
    (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1 + 1))
  have hq₂ := SheafOfModules.IsQuasicoherentOnSite.of_iso
    (modulesTensorObjIso B S hS X.1 X.2 (Stacks.SheafOfModules.Invertible.tensorPower
      (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)) Q.L).symm hq₁
  refine CategoryTheory.Functor.baseChangeTensorSquare_of_tensorPaste
    (cΛL₀ := (pointZariskiModuleBaseChangeIso X
          (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)) Q.L)
          hq₂ x h).hom)
    (n₀ := ((modulePullback B S hS (pointHom x) ⋙ zariskiReadingFunctor T).mapIso
          (X := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
            (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
            ((structureRingSheaf B S hS X).property)⟩).obj
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))).obj Q.L))
          (modulesTensorObjIso B S hS X.1 X.2 (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
            Q.L).symm).hom)
    (n' := ((modulePullback B S hS (pointHom (yoneda.map h ≫ x)) ⋙ zariskiReadingFunctor T').mapIso
          (X := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
            (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
            ((structureRingSheaf B S hS X).property)⟩).obj
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))).obj Q.L))
          (modulesTensorObjIso B S hS X.1 X.2 (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
            Q.L).symm).hom)
    (pointReadingBaseChange_tensor_of X x h hc
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)) Q.L
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1))
        (isQuasicoherentOnSite_of_isInvertible B S hS X Q.L hQ)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact pointZariskiModuleBaseChangeIso_hom_comp_inv X x h
      (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X.1 X.2)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)) Q.L)
      hq₂
  · exact pointZariskiModuleBaseChangeIso_inv_comp_hom X x h
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))
      (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1))
  · exact sectionPointQuotientBaseChangeL_inv_comp_hom X E hE Q x h
  · exact pointZariskiModuleBaseChangeIso_hom_naturality
      (M := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
            (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
            ((structureRingSheaf B S hS X).property)⟩).obj
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))).obj Q.L)) X x h
      (modulesTensorObjIso B S hS X.1 X.2 (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)) Q.L).symm
      hq₁
      hq₂
  · exact zariskiReading_mapIso_modulePullbackTensorComparison_trans_hom (pointHom x)
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)) Q.L _ _
  · exact (zariskiReading_mapIso_modulePullbackTensorComparison_trans_hom
        (pointHom (yoneda.map h ≫ x)) (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)) Q.L _
        _).trans
      (congrArg (CategoryStruct.comp _) (zariskiReadingTensorComparison_comp_eq X x h
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1)) Q.L
            (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1))
            (isQuasicoherentOnSite_of_isInvertible B S hS X Q.L hQ)).symm)

/-- **The inverse-line factors of the conormal source at `x` and `x ∘ h` are intertwined** by the
identification of the point readings and the inverse-line base change of Stacks 0B3V, given the
monoidality of the base change of the Zariski reading. -/
theorem inversePointReadingIso_baseChange {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T)
    (hc : ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
      (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
      CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
            ((zariskiReadingFunctor T).obj (N))).obj ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
              (isAlgebraicSpace_yoneda B S hS T'))
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
            ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
        ((Stacks.RingedSpace.comparisonBifunctorIso
            ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
          ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
        ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
        ((zariskiReadingPullbackHom h).app ((MonoidalCategory.tensorObj
              (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N)
              (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
              (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (representedSpaceMap B S hS h) (N) hN)
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (representedSpaceMap B S hS h) (M) hM)).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (N)))
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (M)))).hom)) :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
      Q.invertible.toAlgebraicGeometry
    (pointZariskiModuleBaseChangeIso X (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)) x h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (inversePointReadingIso X T x Q.L).hom ≫
      (Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)).hom =
      (inversePointReadingIso X T' (yoneda.map h ≫ x) Q.L).hom :=
  inversePointReadingIso_baseChange_of_squares (hQ := Q.invertible.toAlgebraicGeometry) X E hE Q x h
    (inversePointReadingTensorSquare_of (hQ := Q.invertible.toAlgebraicGeometry) X E hE Q x h hc)
    (inversePointReadingUnitSquare (hQ := Q.invertible.toAlgebraicGeometry) X E Q x h)

/-- **The source of the conormal isomorphism of Stacks 0B4I read at scheme points is compatible
with base change**, given the monoidality of the base change of the Zariski reading. -/
theorem conormalSourcePointReading_baseChange {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
    (h : T' ⟶ T)
    (hc : ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
      (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
      CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
            ((zariskiReadingFunctor T).obj (N))).obj ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
              (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
              (isAlgebraicSpace_yoneda B S hS T'))
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
            ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
        ((Stacks.RingedSpace.comparisonBifunctorIso
            ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
          ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
        ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
        ((zariskiReadingPullbackHom h).app ((MonoidalCategory.tensorObj
              (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N)
              (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
              (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (representedSpaceMap B S hS h) (N) hN)
            (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (representedSpaceMap B S hS h) (M) hM)).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (N)))
            ((zariskiReadingFunctor T').obj ((modulePullback B S hS
              (representedSpaceMap B S hS h)).obj (M)))).hom)) :
    haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L :=
      Q.invertible.toAlgebraicGeometry
    (pointZariskiModuleBaseChangeIso X (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q) x h).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        (CategoryTheory.Functor.compBifunctorMap
            (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules) (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T ((modulePullback B S hS (pointHom x)).obj (kernel Q.q))
              ((modulePullback B S hS (pointHom x)).obj
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1)))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
              (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))
              (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
            (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
              ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
              (kernel Q.q))) ((zariskiReadingFunctor T).obj
              ((modulePullback B S hS (pointHom x)).obj
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom) ≫
      (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T x) (pointZariskiModule X E T' (yoneda.map h ≫ x))
        (pointZariskiModuleBaseChangeIso X E hE x h) (sectionPointQuotient X E hE Q T x)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ x))
        (sectionPointQuotientBaseChangeL X E hE Q x h)
        (sectionPointQuotient_baseChange_q X E hE Q x h)).hom =
    (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T').Modules)
        (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      (@CategoryTheory.CategoryStruct.comp _
          (@CategoryTheory.Category.toCategoryStruct _ Scheme.Modules.instCategory) _ _ _
        (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
            Scheme.Modules.instCategory (zariskiReadingFunctor T')
          ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
              ((kernel Q.q ⊗ Stacks.SheafOfModules.Invertible.tensorPower
                  (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))))
            ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
                  (isAlgebraicSpace_yoneda B S hS T'))
                ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj (kernel Q.q))
                ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
                  (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                  (structureRingSheaf B S hS X).property Q.L (-1)))))
          (modulePullbackTensorIso B S hS (pointHom (yoneda.map h ≫ x)) (kernel Q.q)
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1))).hom)
        ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
                (kernel Q.q)) ((modulePullback B S hS (pointHom (yoneda.map h ≫ x))).obj
                (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1)))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
                (pointHom (yoneda.map h ≫ x)) (kernel Q.q)
                (isQuasicoherentOnSite_kernel_q X E hE Q))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
                (pointHom (yoneda.map h ≫ x)) (Stacks.SheafOfModules.Invertible.tensorPower
                (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
                (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
            (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
              ((zariskiReadingFunctor T').obj ((modulePullback B S hS
                (pointHom (yoneda.map h ≫ x))).obj (kernel Q.q)))
              ((zariskiReadingFunctor T').obj ((modulePullback B S hS
                (pointHom (yoneda.map h ≫ x))).obj
                (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T' (yoneda.map h ≫ x))
        (inversePointReadingIso X T' (yoneda.map h ≫ x) Q.L).hom) :=
  conormalSourcePointReading_baseChange_of (hQ := Q.invertible.toAlgebraicGeometry) X E hE Q x h hc
    (inversePointReadingIso_baseChange X E hE Q x h hc)

end AlgebraicGeometry.Space

end
