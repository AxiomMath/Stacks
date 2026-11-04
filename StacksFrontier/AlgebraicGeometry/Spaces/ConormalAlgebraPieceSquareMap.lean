module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapChartHom
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafPowersEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionConormalChartNaturality

/-!
# The degreewise map of conormal algebras of a commutative square

Let
```
Z_U --p--> Z
 |i_U      |i
 U  --φ--> X
```
be a commutative square of algebraic spaces, `i_U ≫ φ = p ≫ i`.  Pullback of regular functions
along `φ` carries `Ker(i^♯)ⁿ` into `Ker(i_U^♯)ⁿ` (the square carries `Ker(i^♯)` into
`Ker((i_U ≫ φ)^♯)`, and pullback along `φ` carries that into `Ker(i_U^♯)`), which gives a map
`φ^*(𝓘ⁿ) ⟶ 𝓘_Uⁿ` of `𝒪_U`-modules; its inverse image along `i_U`, read through the comparison
`p^*i^* ≅ i_U^*φ^*`, is the canonical map

`p^*(𝒞_{Z/X,*})_n ⟶ (𝒞_{Z_U/U,*})_n`

of degree-`n` pieces of conormal algebras (the degreewise map of Stacks 09RS).  When the square is
cartesian and `φ` is étale it is the isomorphism of Stacks 09RR.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap`: `φ^*(𝓘ⁿ) ⟶ 𝓘_Uⁿ`.
* `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap`: `p^*(𝒞_{Z/X,*})_n ⟶ (𝒞_{Z_U/U,*})_n`.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap_unitSection_coe`: the map carries the
  unit section of a regular function to its pullback.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap_comp_ι`: it is the restriction of the
  comparison `φ^*𝒪_X ⟶ 𝒪_U`.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap_comp`: the maps of two composable
  squares compose (the pasting law, on the ambient spaces).
* `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap_eq_etaleRestrictionPieceIso`: at a
  cartesian square with étale `φ` the map is the isomorphism of Stacks 09RR.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}

/-- The transport of sections along an equality of sheaves of ideals does not change the
underlying section of the structure sheaf. -/
theorem eqToHom_congrArg_toSheafOfModules_val_app_coe {I K : (unit R).Submodule} (h : I = K)
    (W : Cᵒᵖ) (x : I.toSheafOfModules.val.obj W) :
    ((eqToHom (congrArg (fun N : (unit R).Submodule ↦ N.toSheafOfModules) h)).val.app W x).1 =
      x.1 := by
  subst h
  rfl

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Z ZU : AlgebraicSpaces B S hS}
    (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)

/-- A commutative square carries the powers of the kernel ideal sheaf of `i` into those of the
diagonal `i_U ≫ φ`. -/
theorem kernelIdealSheafZPow_le_comp (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    kernelIdealSheafZPow B S hS i n ≤ kernelIdealSheafZPow B S hS (iU ≫ φ) n :=
  SheafOfModules.idealSheafZPow_mono (kernelIdealSheaf_le_comp B S hS iU i p φ hsq) n

/-- The chartwise linear map of sections `𝓘ⁿ ⟶ 𝓘_Uⁿ` along `φ` of a commutative square: pullback
of regular functions along the vertical morphism of a chart diagram. -/
def kernelIdealSheafZPowSquareFMap (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    ModuleFMap B S hS φ (kernelIdealSheafZPow B S hS iU n).toSheafOfModules
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules where
  app d s := ⟨(chartDiagramPullback B S hS φ d).hom s.1,
    mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback B S hS iU φ d n
      (kernelIdealSheafZPow_le_comp B S hS p iU i φ hsq n (op d.V) s.2)⟩
  naturality d d' k j hkj s := by
    have hcc : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X.1).map j)).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d'.g).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS U.1).map k)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← Functor.map_comp,
        ← Functor.map_comp, hkj]
    exact Subtype.ext (ConcreteCategory.congr_hom hcc s.1)
  map_add d s t := Subtype.ext (map_add (chartDiagramPullback B S hS φ d).hom s.1 t.1)
  map_smul d r s := Subtype.ext (map_mul (chartDiagramPullback B S hS φ d).hom r s.1)

/-- **The map `φ^*(𝓘ⁿ) ⟶ 𝓘_Uⁿ` of a commutative square**: the transpose of
`AlgebraicGeometry.Space.kernelIdealSheafZPowSquareFMap` along the chartwise universal property of
the direct image and the adjunction of Stacks 03D7. -/
def kernelIdealSheafZPowSquareMap (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    (modulePullback B S hS φ).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules ⟶
      (kernelIdealSheafZPow B S hS iU n).toSheafOfModules :=
  ((modulePullbackAdjunction B S hS φ).homEquiv _ _).symm
    ((modulePushforwardHomEquiv B S hS φ (kernelIdealSheafZPow B S hS iU n).toSheafOfModules
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules).symm
        (kernelIdealSheafZPowSquareFMap B S hS p iU i φ hsq n))

/-- The chartwise transpose of `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap` is the
chartwise map it is built from. -/
theorem modulePullbackHomFMap_kernelIdealSheafZPowSquareMap (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    modulePullbackHomFMap B S hS φ (kernelIdealSheafZPow B S hS i n).toSheafOfModules
        (kernelIdealSheafZPow B S hS iU n).toSheafOfModules
        (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n) =
      kernelIdealSheafZPowSquareFMap B S hS p iU i φ hsq n := by
  unfold modulePullbackHomFMap kernelIdealSheafZPowSquareMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The map of a commutative square carries a unit section to a pullback of regular
functions.** -/
theorem kernelIdealSheafZPowSquareMap_unitSection_coe (hsq : iU ≫ φ = p ≫ i) (n : ℤ)
    (d : ChartDiagram B S hS U.1 X.1 φ.hom)
    (s : (kernelIdealSheafZPow B S hS i n).toSheafOfModules.val.obj (op d.V)) :
    ((kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n).val.app (op d.U)
        (modulePullbackUnitSection B S hS φ
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules d s)).1 =
      chartDiagramPullback B S hS φ d s.1 := by
  rw [← modulePullbackHomFMap_app B S hS φ (kernelIdealSheafZPow B S hS i n).toSheafOfModules
      (kernelIdealSheafZPow B S hS iU n).toSheafOfModules
      (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n) d s,
    modulePullbackHomFMap_kernelIdealSheafZPowSquareMap]
  rfl

/-- **The degree-`n` map of conormal algebras of a commutative square** `i_U ≫ φ = p ≫ i`:
`p^*(𝒞_{Z/X,*})_n = p^*i^*(𝓘ⁿ) ≅ i_U^*φ^*(𝓘ⁿ) ⟶ i_U^*(𝓘_Uⁿ) = (𝒞_{Z_U/U,*})_n`. -/
def conormalAlgebraPieceSquareMap (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    (modulePullback B S hS p).obj ((conormalAlgebra B S hS i).piece n) ⟶
      (conormalAlgebra B S hS iU).piece n :=
  (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
    (modulePullback B S hS iU).map (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n)

/-- The characterising property of `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap`: its
two transposes give back the chartwise map. -/
theorem kernelIdealSheafZPowSquareMap_transpose (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    modulePushforwardHomEquiv B S hS φ (kernelIdealSheafZPow B S hS iU n).toSheafOfModules
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules
        ((modulePullbackAdjunction B S hS φ).homEquiv _ _
          (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n)) =
      kernelIdealSheafZPowSquareFMap B S hS p iU i φ hsq n :=
  modulePullbackHomFMap_kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n

/-- **The map of a commutative square is the restriction of the map of structure sheaves**:
`φ^*(𝓘ⁿ) ⟶ 𝓘_Uⁿ ⊆ 𝒪_U` is `φ^*(𝓘ⁿ ⊆ 𝒪_X)` followed by `φ^*𝒪_X ⟶ 𝒪_U`. -/
theorem kernelIdealSheafZPowSquareMap_comp_ι (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n ≫ (kernelIdealSheafZPow B S hS iU n).ι =
      (modulePullback B S hS φ).map (kernelIdealSheafZPow B S hS i n).ι ≫
        structureModulePullbackMap B S hS φ := by
  refine ((modulePullbackAdjunction B S hS φ).homEquiv _ _).injective ?_
  refine Eq.trans ((modulePullbackAdjunction B S hS φ).homEquiv_naturality_right
      (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n) (kernelIdealSheafZPow B S hS iU n).ι)
    (Eq.trans ?_ ((modulePullbackAdjunction B S hS φ).homEquiv_naturality_left
      (kernelIdealSheafZPow B S hS i n).ι (structureModulePullbackMap B S hS φ)).symm)
  refine Eq.trans ?_ (congrArg (fun t ↦ (kernelIdealSheafZPow B S hS i n).ι ≫ t)
    (structureModulePullbackMap_transpose B S hS φ).symm)
  refine (modulePushforwardHomEquiv B S hS φ _ _).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  refine Eq.trans (modulePushforwardHomEquiv_app_comp_right B S hS φ
    ((modulePullbackAdjunction B S hS φ).homEquiv _ _
      (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n))
    (kernelIdealSheafZPow B S hS iU n).ι d s) ?_
  refine Eq.trans (congrArg ((kernelIdealSheafZPow B S hS iU n).ι.val.app (op d.U))
    (congrFun (congrFun (congrArg ModuleFMap.app
      (kernelIdealSheafZPowSquareMap_transpose B S hS p iU i φ hsq n)) d) s)) ?_
  refine Eq.trans ?_ (modulePushforwardHomEquiv_app_comp_left B S hS φ
    (kernelIdealSheafZPow B S hS i n).ι
    ((modulePushforwardHomEquiv B S hS φ _ _).symm (structureModuleFMap B S hS φ)) d s).symm
  refine Eq.trans ?_ (congrFun (congrFun (congrArg ModuleFMap.app
      (Equiv.apply_symm_apply (modulePushforwardHomEquiv B S hS φ
        (SheafOfModules.unit (structureRingSheaf B S hS U))
        (SheafOfModules.unit (structureRingSheaf B S hS X)))
        (structureModuleFMap B S hS φ)).symm) d)
      ((kernelIdealSheafZPow B S hS i n).ι.val.app (op d.V) s))
  rfl

section Paste

variable {U₁ U₂ Z₁ Z₂ : AlgebraicSpaces B S hS}

/-- **The maps `φ^*(𝓘ⁿ) ⟶ 𝓘_Uⁿ` of two composable commutative squares compose**: the map of the
outer square is the composition comparison of Stacks 03LU, the inverse image along `φ₂` of the map
of the first square, and the map of the second square. -/
theorem kernelIdealSheafZPowSquareMap_comp (p₁ : Z₁ ⟶ Z) (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X)
    (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ φ₂ ≫ φ₁ = (p₂ ≫ p₁) ≫ i) (n : ℤ) :
    kernelIdealSheafZPowSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n =
      (modulePullbackCompIso B S hS φ₂ φ₁).inv.app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
        (modulePullback B S hS φ₂).map (kernelIdealSheafZPowSquareMap B S hS p₁ iU₁ i φ₁ h₁ n) ≫
          kernelIdealSheafZPowSquareMap B S hS p₂ iU₂ iU₁ φ₂ h₂ n := by
  refine (cancel_mono (kernelIdealSheafZPow B S hS iU₂ n).ι).mp ?_
  have hnat := (modulePullbackCompIso B S hS φ₂ φ₁).inv.naturality
    (kernelIdealSheafZPow B S hS i n).ι
  have hinner : ((modulePullback B S hS φ₂).map
        (kernelIdealSheafZPowSquareMap B S hS p₁ iU₁ i φ₁ h₁ n) ≫
        kernelIdealSheafZPowSquareMap B S hS p₂ iU₂ iU₁ φ₂ h₂ n) ≫
        (kernelIdealSheafZPow B S hS iU₂ n).ι =
      ((modulePullback B S hS φ₂).map ((modulePullback B S hS φ₁).map
          (kernelIdealSheafZPow B S hS i n).ι) ≫
        (modulePullback B S hS φ₂).map (structureModulePullbackMap B S hS φ₁)) ≫
        structureModulePullbackMap B S hS φ₂ :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (kernelIdealSheafZPowSquareMap_comp_ι B S hS p₂ iU₂ iU₁ φ₂ h₂ n)).trans
        ((Category.assoc _ _ _).symm.trans
          (eq_whisker ((((modulePullback B S hS φ₂).map_comp
              (kernelIdealSheafZPowSquareMap B S hS p₁ iU₁ i φ₁ h₁ n)
              (kernelIdealSheafZPow B S hS iU₁ n).ι).symm.trans
            (congrArg (modulePullback B S hS φ₂).map
              (kernelIdealSheafZPowSquareMap_comp_ι B S hS p₁ iU₁ i φ₁ h₁ n))).trans
            ((modulePullback B S hS φ₂).map_comp _ _)) _)))
  refine Eq.trans (kernelIdealSheafZPowSquareMap_comp_ι B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁)
    h₁₂ n) ?_
  refine Eq.trans (whisker_eq _ (structureModulePullbackMap_comp B S hS φ₂ φ₁)) ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (whisker_eq _ hinner)).symm
  refine Eq.trans ?_ (whisker_eq
    ((modulePullbackCompIso B S hS φ₂ φ₁).inv.app
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
    (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (eq_whisker hnat.symm _).symm
  exact (Category.assoc _ _ _).symm

end Paste

/-! ### At a cartesian square with étale base: Stacks 09RR -/

/-- The backward comparison of Stacks 03LW carries a section over the composite chart to the
unit section of the identity-vertical chart diagram. -/
private theorem inv_app_etaleUnit (hφ : IsEtale B S hS φ.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS U.1)
    (t : M.val.obj (op ((smallEtalePostcomp B S hS φ hφ).obj W))) :
    ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).inv.app M).val.app (op W) t =
      modulePullbackUnitSection B S hS φ M (ChartDiagram.etaleUnit B S hS φ hφ W) t :=
  have h465 := modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit
    B S hS φ hφ M W t
  have hid := (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom_inv_id_app M
  ((congrArg
      (fun x ↦ ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).inv.app M).val.app (op W) x)
      h465.symm).trans
    (congrArg (fun m ↦ m.val.app (op W)
      (modulePullbackChartSection B S hS φ M (ChartDiagram.etaleUnit B S hS φ hφ W) t)) hid)).trans
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS φ M
      (ChartDiagram.etaleUnit B S hS φ hφ W) t).symm

private theorem inv_comp_kernelIdealSheafZPowSquareMap_app (sq : IsPullback p iU i φ)
    (hφ : IsEtale B S hS φ.hom) (n : ℤ) (W : SmallEtale B S hS U.1)
    (x : ((etaleModulePullback.{u, u} B S hS φ hφ).obj
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules).val.obj (op W)) :
    ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).inv.app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
        kernelIdealSheafZPowSquareMap B S hS p iU i φ sq.w.symm n).val.app (op W) x =
      (eqToHom (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n)).val.app
        (op W) x := by
  refine (comp_val_app_apply B S hS _ _ (op W) x).trans (Subtype.ext ?_)
  refine (congrArg (fun y ↦ ((kernelIdealSheafZPowSquareMap B S hS p iU i φ sq.w.symm n).val.app
      (op W) y).1) (inv_app_etaleUnit B S hS φ hφ _ W x)).trans ?_
  refine (kernelIdealSheafZPowSquareMap_unitSection_coe B S hS p iU i φ sq.w.symm n
    (ChartDiagram.etaleUnit B S hS φ hφ W) x).trans ?_
  refine (chartDiagramPullback_etaleUnit_apply B S hS φ hφ W x.1).trans ?_
  exact (SheafOfModules.eqToHom_congrArg_toSheafOfModules_val_app_coe
    (etaleRestrictionIdealSheafZPowSheaf_eq B S hS φ hφ (kernelIdealSheaf B S hS i)
      (kernelIdealSheaf B S hS iU)
      (fun W ↦ kernelIdealSheaf_baseChange_obj B S hS p iU i φ sq hφ W) n) (op W) x).symm

/-- **At a cartesian square with étale `φ`, the map `φ^*(𝓘ⁿ) ⟶ 𝓘_Uⁿ` is the identification of
Stacks 03LW followed by the equality `𝓘ⁿ|_U = 𝓘_Uⁿ`.** -/
theorem kernelIdealSheafZPowSquareMap_eq_of_isEtale (sq : IsPullback p iU i φ)
    (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    kernelIdealSheafZPowSquareMap B S hS p iU i φ sq.w.symm n =
      (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
        eqToHom (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n) := by
  have key : (modulePullbackIsoEtaleModulePullback B S hS φ hφ).inv.app
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≫
      kernelIdealSheafZPowSquareMap B S hS p iU i φ sq.w.symm n =
      eqToHom (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n) := by
    refine Function.LeftInverse.injective
      (etaleRestrictHom_moduleFMapOfEtaleRestrictHom B S hS φ hφ
        (kernelIdealSheafZPow B S hS iU n).toSheafOfModules
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ?_
    refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun t ↦ ?_)
    exact inv_comp_kernelIdealSheafZPowSquareMap_app B S hS p iU i φ sq hφ n d.U _
  exact ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
    (kernelIdealSheafZPow B S hS i n).toSheafOfModules).inv_comp_eq.mp key

/-- **At a cartesian square with étale `φ`, the degree-`n` map of conormal algebras is the
isomorphism of Stacks 09RR.** -/
theorem conormalAlgebraPieceSquareMap_eq_etaleRestrictionPieceIso (sq : IsPullback p iU i φ)
    (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    conormalAlgebraPieceSquareMap B S hS p iU i φ sq.w.symm n =
      (conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ n).hom :=
  have h₁ : kernelIdealSheafZPowSquareMap B S hS p iU i φ sq.w.symm n =
      (kernelIdealSheafZPowEtaleRestrictionIso B S hS p iU i φ sq hφ n).hom :=
    (kernelIdealSheafZPowSquareMap_eq_of_isEtale B S hS p iU i φ sq hφ n).trans
      (Iso.trans_hom ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
        (eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n))).symm
  (congrArg (fun k ↦ ((modulePullbackSquareCompIso B S hS p iU i φ sq.w.symm).app
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU).map k) h₁).trans
    (conormalAlgebraEtaleRestrictionPieceIso_hom_eq_squareCompIso_comp B S hS p iU i φ sq hφ n).symm

/-- The degree-`n` map of conormal algebras of a commutative square, precomposed with the inverse
image along `p` of an isomorphism `ℳ ≅ (𝒞_{Z/X,*})_n`. -/
def conormalAlgebraPieceSquareMapOfIso (hsq : iU ≫ φ = p ≫ i) (n : ℤ)
    {M : Modules.{u, u} B S hS Z.1 Z.2} (e : M ≅ (conormalAlgebra B S hS i).piece n) :
    (modulePullback B S hS p).obj M ⟶ (conormalAlgebra B S hS iU).piece n :=
  (modulePullback B S hS p).map e.hom ≫ conormalAlgebraPieceSquareMap B S hS p iU i φ hsq n

/-- At a cartesian square with étale `φ`,
`AlgebraicGeometry.Space.conormalAlgebraPieceSquareMapOfIso` is the inverse image of the
isomorphism followed by the isomorphism of Stacks 09RR. -/
theorem conormalAlgebraPieceSquareMapOfIso_eq (sq : IsPullback p iU i φ)
    (hφ : IsEtale B S hS φ.hom) (n : ℤ) {M : Modules.{u, u} B S hS Z.1 Z.2}
    (e : M ≅ (conormalAlgebra B S hS i).piece n) :
    conormalAlgebraPieceSquareMapOfIso B S hS p iU i φ sq.w.symm n e =
      ((modulePullback B S hS p).mapIso e ≪≫
        conormalAlgebraEtaleRestrictionPieceIso B S hS p iU i φ sq hφ n).hom :=
  congrArg (fun k ↦ (modulePullback B S hS p).map e.hom ≫ k)
    (conormalAlgebraPieceSquareMap_eq_etaleRestrictionPieceIso B S hS p iU i φ sq hφ n)

/-- At a cartesian square with étale `φ` the degree-`n` map of conormal algebras is an
isomorphism. -/
theorem isIso_conormalAlgebraPieceSquareMap (sq : IsPullback p iU i φ)
    (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    IsIso (conormalAlgebraPieceSquareMap B S hS p iU i φ sq.w.symm n) := by
  rw [conormalAlgebraPieceSquareMap_eq_etaleRestrictionPieceIso B S hS p iU i φ sq hφ n]
  exact Iso.isIso_hom _

end AlgebraicGeometry.Space

end
