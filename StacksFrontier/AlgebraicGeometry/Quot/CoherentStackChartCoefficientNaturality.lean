module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangent

/-!
# Naturality of the coefficient identifications over a chart

For an object `x = (Spec A, ℱ)` of `Coh_{X/B}` over a chart and a morphism `f : A₁' → A₂'` of
square-zero thickenings of `A`, the identifications `p^*t_k^*𝒥_k ≅ p^*Ĩ_k` of the pulled-back
ideals of `Spec A ⊂ Spec A_k'` (`AlgebraicGeometry.Space.CoherentSituation.testSchemeIdealIso`)
carry the map of ideals `λ_g` of `g : Spec A₂' ⟶ Spec A₁'`
(`AlgebraicGeometry.Space.thickeningIdealMap`) to the map `I₁ ⟶ I₂` induced by `f`. With
`AlgebraicGeometry.Space.CoherentSituation.coefficientIsoOfIdealAt_hom_naturality` this gives the
naturality of the coefficients of the obstruction classes and of the tangent identification, the
coefficient part of the functoriality used in the second proof of Stacks 08WA.

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe w u

namespace CategoryTheory.Functor

/-- **A square of isomorphisms followed by a square of isomorphisms.** -/
theorem _root_.CategoryTheory.Iso.comp_trans_hom_eq {C : Type*} [Category* C]
    {a₁ a₂ b₁ b₂ c₁ c₂ : C} (l : a₁ ⟶ a₂) (t₁ : a₁ ≅ b₁) (t₂ : a₂ ≅ b₂) (κ : b₁ ⟶ b₂)
    (k₁ : b₁ ≅ c₁) (k₂ : b₂ ≅ c₂) (m : c₁ ⟶ c₂) (h₁ : l ≫ t₂.hom = t₁.hom ≫ κ)
    (h₂ : κ ≫ k₂.hom = k₁.hom ≫ m) :
    l ≫ (t₂ ≪≫ k₂).hom = (t₁ ≪≫ k₁).hom ≫ m := by
  rw [Iso.trans_hom, Iso.trans_hom, reassoc_of% h₁, h₂, Category.assoc]

/-- **A square of isomorphisms, conjugated by isomorphisms of the sources.** -/
theorem _root_.CategoryTheory.Iso.conj_comp_trans_hom_eq {C : Type*} [Category* C]
    {z₁ z₂ a₁ a₂ b₁ b₂ : C} (r₁ : z₁ ≅ a₁) (r₂ : z₂ ≅ a₂) (l : a₁ ⟶ a₂) (t₁ : a₁ ≅ b₁)
    (t₂ : a₂ ≅ b₂) (m : b₁ ⟶ b₂) (h : l ≫ t₂.hom = t₁.hom ≫ m) :
    (r₁.hom ≫ l ≫ r₂.inv) ≫ (r₂ ≪≫ t₂).hom = (r₁ ≪≫ t₁).hom ≫ m := by
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h,
    Category.assoc]

/-- **Composition of an `Ext` class with a square of coefficient maps.** -/
theorem _root_.CategoryTheory.Abelian.Ext.comp_mk₀_comp_mk₀_of_comp_eq {C : Type*} [Category* C]
    [Abelian C] [HasExt.{w} C] {X Y₁ Y₂ Z₁ Z₂ : C} {n : ℕ} (y : Abelian.Ext.{w} X Y₁ n)
    (a : Y₁ ⟶ Y₂) (ι₁ : Y₁ ⟶ Z₁) (ι₂ : Y₂ ⟶ Z₂) (b : Z₁ ⟶ Z₂) (h : a ≫ ι₂ = ι₁ ≫ b) :
    (y.comp (Abelian.Ext.mk₀ a) (add_zero n)).comp (Abelian.Ext.mk₀ ι₂) (add_zero n) =
      (y.comp (Abelian.Ext.mk₀ ι₁) (add_zero n)).comp (Abelian.Ext.mk₀ b) (add_zero n) := by
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀, h]

/-- **Two commuting squares give a commuting square through a functor.** If `l` is carried by
`t₁, t₂` to `κ` and `κ` by `k₁, k₂` to `m`, then `P l` is carried by `P(t₁ ≪≫ k₁)`,
`P(t₂ ≪≫ k₂)` to `P m`. -/
theorem map_comp_mapIso_trans_hom_of_comp_eq {C C' : Type*} [Category* C] [Category* C']
    (P : C ⥤ C')
    {a₁ a₂ b₁ b₂ c₁ c₂ : C} (l : a₁ ⟶ a₂) (t₁ : a₁ ≅ b₁) (t₂ : a₂ ≅ b₂) (κ : b₁ ⟶ b₂)
    (k₁ : b₁ ≅ c₁) (k₂ : b₂ ≅ c₂) (m : c₁ ⟶ c₂) (h₁ : l ≫ t₂.hom = t₁.hom ≫ κ)
    (h₂ : κ ≫ k₂.hom = k₁.hom ≫ m) :
    P.map l ≫ (P.mapIso (t₂ ≪≫ k₂)).hom = (P.mapIso (t₁ ≪≫ k₁)).hom ≫ P.map m := by
  simp only [Functor.mapIso_hom, Iso.trans_hom, ← Functor.map_comp]
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- A commuting square is unchanged when its two non-source morphisms are rewritten. -/
private theorem _root_.CategoryTheory.comp_eq_comp_of_eq_of_eq {C : Type*} [Category* C]
    {a b c d : C} {l : a ⟶ b} {m : c ⟶ d} {u u' : b ⟶ d} {v v' : a ⟶ c} (hu : u = u')
    (hv : v' = v) (h : l ≫ u' = v' ≫ m) : l ≫ u = v ≫ m := by
  rw [hu, ← hv, h]

/-- A commuting square of morphisms stays commuting after applying a functor. -/
private theorem map_comp_eq_map_comp_of_comp_eq {C C' : Type*} [Category* C] [Category* C']
    (P : C ⥤ C') {a b c d : C} {f : a ⟶ b} {g : b ⟶ c} {f' : a ⟶ d} {g' : d ⟶ c}
    (h : f ≫ g = f' ≫ g') : P.map f ≫ P.map g = P.map f' ≫ P.map g' := by
  simp only [← Functor.map_comp, h]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (hY : IsTerminal D.Y)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)
  {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
  {T₁ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₁}
  {T₂ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₂}
  (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] in
/-- **The kernel identification is natural in the thickening**: the restriction of `g^♯` to the
kernels of `Γ(Spec A_k') ⟶ Γ(Spec A)` corresponds to the map `I₁ ⟶ I₂` induced by `f`. -/
theorem thickeningKerMapOf_comp_kernelModuleIso_hom :
    thickeningKerMapOf (D.thickeningTestMap hY x hx T₁).left (D.thickeningTestMap hY x hx T₂).left
        (D.thickeningTestSchemeMap hY f).left
        (left_comp_left_eq_of_comp_eq (D.thickeningTestSchemeMap hY f)
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂) ≫
      (chartKernelIso hY hx T₂).hom =
    (chartKernelIso hY hx T₁).hom ≫
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (D.chartRingEquiv x hx).symm).functor.map
        f.kernelMap := by
  refine ConcreteCategory.hom_ext _ _ fun z => Subtype.ext ?_
  exact (kernelModuleIso_hom_apply hx f (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
    (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂) z).trans (f.kernelMap_spec _).symm

/-- `p^*t^*𝒥 ≅ p^*Ĩ` is the pullback of `t^*𝒥 ≅ J^~ ≅ Ĩ`. -/
theorem testSchemeIdealIso_hom_eq {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A') :
    (testSchemeIdealIso hY hx T).hom =
      (((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.projection
          x.T)).toRingedToposModulesHom.pullbackModules).mapIso
        (thickeningIdealTildeIso (D.thickeningTestMap hY x hx T).left
          (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T))
              (isFirstOrderThickening_range_yoneda_map B S hS _
              (D.isFirstOrderThickening_thickeningTestMap hY x hx T))
              (D.isFirstOrderThickening_thickeningTestMap hY x hx T) ≪≫
          (representedAffineAssociated B S hS x.T.left).mapIso (chartKernelIso hY hx T))).hom :=
  rfl

/-- **The map of coefficients `𝒢 ⊗ f_T^*𝒥₁ ⟶ 𝒢 ⊗ f_T^*𝒥₂` of a morphism of thickenings of test
schemes is `𝒢 ⊗ p^*λ_g`.** -/
theorem thickeningCoefficientMap_thickeningTestSchemeMap_eq :
    thickeningCoefficientMap (D.thickeningTestSchemeMap hY f)
        (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
        (objectToposModule x)).map
        ((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules.map
        (thickeningIdealMap (D.thickeningTestMap hY x hx T₁).left
            (D.thickeningTestMap hY x hx T₂).left
          (D.thickeningTestSchemeMap hY f).left
          (left_comp_left_eq_of_comp_eq (D.thickeningTestSchemeMap hY f)
            (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f))
          (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₁)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
          (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₂)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))) := by
  delta thickeningCoefficientMap
  refine congrArg _ ?_
  refine congrArg _ ?_
  congr

/-- **The identification `p^*t^*𝒥 ≅ p^*Ĩ` is natural in the thickening**: it carries the map of
ideals `λ_g` of `g : Spec A₂' ⟶ Spec A₁'` to the map `I₁ ⟶ I₂` induced by `f`. -/
theorem pullbackModules_map_thickeningIdealMap_comp_testSchemeIdealIso_hom :
        ((smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).map
        (thickeningIdealMap (D.thickeningTestMap hY x hx T₁).left
            (D.thickeningTestMap hY x hx T₂).left
          (D.thickeningTestSchemeMap hY f).left
          (left_comp_left_eq_of_comp_eq (D.thickeningTestSchemeMap hY f)
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f))
          (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₁)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
          (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₂)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂)) ≫
      (testSchemeIdealIso hY hx T₂).hom =
    (testSchemeIdealIso hY hx T₁).hom ≫
      ((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).map
        ((representedAffineAssociated B S hS x.T.left).map
          ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
              (D.chartRingEquiv x hx).symm).functor.map
            f.kernelMap)) := by
  exact comp_eq_comp_of_eq_of_eq (testSchemeIdealIso_hom_eq hY hx T₂)
    (testSchemeIdealIso_hom_eq hY hx T₁).symm
    (Functor.map_comp_mapIso_trans_hom_of_comp_eq _ _ _ _ _ _ _ _
      (thickeningIdealMap_comp_tildeIso_hom _ _ _ _ _ _ _ _ _ _)
      (Functor.map_comp_eq_map_comp_of_comp_eq _
        (thickeningKerMapOf_comp_kernelModuleIso_hom hY hx f)))


/-- `f̃^*t̃^*𝒥̃ ⊗ ℱ ≅ ℱ ⊗ p^*Ĩ` is the identification of coefficients of
`p^*t^*𝒥 ≅ p^*Ĩ` read through `f̃^*t̃^*𝒥̃ ≅ p^*t^*𝒥`. -/
theorem chartObstructionCoefficientIso_hom_eq {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A') :
    (chartObstructionCoefficientIso hY hx T).hom =
      (D.coefficientIsoOfIdealAt x (D.chartRingEquiv x hx) _ _
        (toRingedToposModulesHom_eq_baseProjection x)
        ((relativeSquareTestIdealIso hY hx T) ≪≫ testSchemeIdealIso hY hx T)).hom :=
  rfl

/-- **The coefficient of the obstruction classes is natural in the thickening**: under
`f̃^*t̃^*𝒥̃_k ⊗ ℱ ≅ ℱ ⊗ p^*Ĩ_k`, the map of coefficients induced by `λ_g` for
`g : Spec A₂' ⟶ Spec A₁'` is the map `ℱ ⊗ p^*Ĩ₁ ⟶ ℱ ⊗ p^*Ĩ₂` induced by `f`. -/
theorem chartObstructionCoefficientIso_hom_naturality :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
        (objectToposModule x)).map ((relativeSquareTestIdealIso hY hx T₁).hom ≫
          ((smallEtaleRingedToposHom B S hS
              (D.relativeSquareSituation.projection
              x.T)).toRingedToposModulesHom.pullbackModules).map
        (thickeningIdealMap (D.thickeningTestMap hY x hx T₁).left
            (D.thickeningTestMap hY x hx T₂).left
          (D.thickeningTestSchemeMap hY f).left
          (left_comp_left_eq_of_comp_eq (D.thickeningTestSchemeMap hY f)
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f))
          (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₁)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
          (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₂)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂)) ≫
              (relativeSquareTestIdealIso hY hx T₂).inv) ≫
      (chartObstructionCoefficientIso hY hx T₂).hom =
    (chartObstructionCoefficientIso hY hx T₁).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
        (objectToposModule x)).map
            ((@id (Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)))
          (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom).pullbackModules.map
          ((representedAffineAssociated B S hS x.T.left).map
              ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
              (D.chartRingEquiv x hx).symm).functor.map
            f.kernelMap))) := by
  have hl := Iso.conj_comp_trans_hom_eq (relativeSquareTestIdealIso hY hx T₁)
      (relativeSquareTestIdealIso hY hx T₂) _
    (testSchemeIdealIso hY hx T₁) (testSchemeIdealIso hY hx T₂) _
    (pullbackModules_map_thickeningIdealMap_comp_testSchemeIdealIso_hom hY hx f)
  exact comp_eq_comp_of_eq_of_eq (chartObstructionCoefficientIso_hom_eq hY hx T₂)
    (chartObstructionCoefficientIso_hom_eq hY hx T₁).symm
    (D.coefficientIsoOfIdealAt_hom_naturality x (D.chartRingEquiv x hx) _ _
      (toRingedToposModulesHom_eq_baseProjection x) f.kernelMap _ _ _ hl)


/-- The map of coefficients on the relative square is the map of coefficients of `extGroup`. -/
theorem pullbackModules_map_eq_baseProjection {K₁ K₂ : ModuleCat.{u} A} (g : K₁ ⟶ K₂) :
    (@id (Stacks.Sheaves.RingedToposModules.RingedToposHom
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)))
        (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom).pullbackModules.map
        ((representedAffineAssociated B S hS x.T.left).map
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
            (D.chartRingEquiv x hx).symm).functor.map g)) =
      (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom.pullbackModules.map
        ((representedAffineAssociated B S hS x.T.left).map
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
            (D.chartRingEquiv x hx).symm).functor.map g)) :=
  rfl

/-- The map of coefficients `ℱ ⊗ p^*K̃₁ ⟶ ℱ ⊗ p^*K̃₂` on the relative square is
`D.extCoefficientModuleMap`. -/
theorem sheafTensor_map_eq_extCoefficientModuleMap {K₁ K₂ : ModuleCat.{u} A} (g : K₁ ⟶ K₂) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
        (objectToposModule x)).map
      ((@id (Stacks.Sheaves.RingedToposModules.RingedToposHom
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)))
        (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom).pullbackModules.map
        ((representedAffineAssociated B S hS x.T.left).map
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
            (D.chartRingEquiv x hx).symm).functor.map g))) =
      D.extCoefficientModuleMap x (D.chartRingEquiv x hx) g :=
  (congrArg ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
    (objectToposModule x)).map (pullbackModules_map_eq_baseProjection hx g)).trans rfl

section Tangent

variable {M N : Deformation.Artin.SiteModule A B} (fMN : M ⟶ N)

/-- The kernel identifications `ker(A[M] → A) ≅ M` carry the map of kernels of `A[M] → A[N]` to
`f`. -/
theorem squareZeroModuleKernelIso_naturality :
    (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
        (hA := hA) fMN).kernelMap ≫ (Deformation.Artin.squareZeroModuleKernelIso N).hom =
      (Deformation.Artin.squareZeroModuleKernelIso M).hom ≫ fMN.hom := by
  change ((Deformation.Artin.squareZeroModuleKernelIso M).hom ≫ fMN.hom ≫
    (Deformation.Artin.squareZeroModuleKernelIso N).inv) ≫
      (Deformation.Artin.squareZeroModuleKernelIso N).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `ℱ ⊗ p^*M̃` as the coefficient of the tangent identification is the identification of
coefficients of `p^*t^*𝒥 ≅ p^*M̃`. -/
theorem tangentCoefficientIso_hom_eq (M : Deformation.Artin.SiteModule A B) :
    (tangentCoefficientIso hY hx M).hom =
      (D.coefficientIsoOfIdealAt x (D.chartRingEquiv x hx) _ _
        (toRingedToposModulesHom_eq_baseProjection x)
        (((smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.projection
            x.T)).toRingedToposModulesHom.pullbackModules).mapIso
            ((thickeningIdealTildeIso
            (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)).left
        (isIso_toRange_testSchemeMap
            (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
        (isFirstOrderThickening_range_yoneda_map B S hS _
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))) ≪≫
        (representedAffineAssociated B S hS x.T.left).mapIso
            (chartKernelIso hY hx (Deformation.Artin.squareZeroModuleThickening (toS := toS)
            (hA := hA) M) ≪≫ (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
            (D.chartRingEquiv x hx).symm).functor.mapIso
            (Deformation.Artin.squareZeroModuleKernelIso M))))).hom :=
  rfl

/-- **The coefficient of the tangent identification is natural in the module**: under
`p^*t^*𝒥_M ⊗ ℱ ≅ ℱ ⊗ p^*M̃`, the map of coefficients induced by `λ_g` for
`g : Spec A[N] ⟶ Spec A[M]` is the map `ℱ ⊗ p^*M̃ ⟶ ℱ ⊗ p^*Ñ` induced by `f`. -/
theorem tangentCoefficientIso_hom_naturality_of_comp
    (l : _) (e1 : l ≫ (thickeningIdealTildeIso
        (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)).left
        (isIso_toRange_testSchemeMap
            (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))
        (isFirstOrderThickening_range_yoneda_map B S hS _
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))).hom =
      (thickeningIdealTildeIso
          (D.thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)).left
        (isIso_toRange_testSchemeMap
            (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
        (isFirstOrderThickening_range_yoneda_map B S hS _
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))).hom ≫
            (representedAffineAssociated B S hS x.T.left).map
            (thickeningKerMapOf (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)).left
            (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)).left
      (D.thickeningTestSchemeMap hY
          (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
          (hA := hA) fMN)).left
      (left_comp_left_eq_of_comp_eq
          (D.thickeningTestSchemeMap hY
          (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
          (hA := hA) fMN))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) fMN)))
      (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
      (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
        (objectToposModule x)).map
            (((smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).map
        l) ≫
      (tangentCoefficientIso hY hx N).hom =
    (tangentCoefficientIso hY hx M).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
        (objectToposModule x)).map
            ((@id (Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)))
          (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom).pullbackModules.map
          ((representedAffineAssociated B S hS x.T.left).map
              ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
              (D.chartRingEquiv x hx).symm).functor.map fMN.hom))) := by
  exact comp_eq_comp_of_eq_of_eq (tangentCoefficientIso_hom_eq hY hx N)
    (tangentCoefficientIso_hom_eq hY hx M).symm
    (D.coefficientIsoOfIdealAt_hom_naturality x (D.chartRingEquiv x hx) _ _
      (toRingedToposModulesHom_eq_baseProjection x) fMN.hom _ _ _
      (Functor.map_comp_mapIso_trans_hom_of_comp_eq _ _ _ _ _ _ _ _ e1
        (Functor.map_comp_eq_map_comp_of_comp_eq _
          (Iso.comp_trans_hom_eq _ _ _ _ _ _ _
            (thickeningKerMapOf_comp_kernelModuleIso_hom hY hx
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                (hA := hA) fMN))
            (Functor.map_comp_eq_map_comp_of_comp_eq _
              (squareZeroModuleKernelIso_naturality fMN))))))

/-- **The coefficient of the tangent identification is natural in the module**: for a module map
`f : M ⟶ N` and the induced `g : Spec A[N] ⟶ Spec A[M]`, the map `ℱ ⊗ p^*λ_g` of coefficients
corresponds, under `tangentCoefficientIso`, to the map `ℱ ⊗ p^*M̃ ⟶ ℱ ⊗ p^*Ñ` induced by `f`. -/
theorem tangentCoefficientIso_hom_naturality :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).flip.obj
        (objectToposModule x)).map
            (((smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).map
        (thickeningIdealMap (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)).left
            (D.thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)).left
          (D.thickeningTestSchemeMap hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) fMN)).left
          (left_comp_left_eq_of_comp_eq
              (D.thickeningTestSchemeMap hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) fMN))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) fMN)))
          (isIso_toRange_testSchemeMap
              (D.thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
                (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
          (isIso_toRange_testSchemeMap
              (D.thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))
          (isFirstOrderThickening_range_yoneda_map B S hS _
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
                (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))) ≫
      (tangentCoefficientIso hY hx N).hom =
    (tangentCoefficientIso hY hx M).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O).obj
        (objectToposModule x)).map
            ((@id (Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T))
      (smallEtaleRingedTopos B S hS ((schemeSpaceFunctor B S hS).obj x.T.left)))
          (smallEtaleRingedToposHom B S hS (D.baseProjection x)).toModulesHom).pullbackModules.map
          ((representedAffineAssociated B S hS x.T.left).map
              ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
              (D.chartRingEquiv x hx).symm).functor.map fMN.hom))) :=
  tangentCoefficientIso_hom_naturality_of_comp hY hx fMN _
    (thickeningIdealMap_comp_tildeIso_hom _ _ _ _ _ _ _ _ _ _)

end Tangent

end AlgebraicGeometry.Space.CoherentSituation

end
