module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLiftAutPullback
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftAutomorphismsBaseChange

/-!
# The naturality of `g ↦ 1 + g` on the lifts of `w₀`

Let `f : V ⟶ W` be a linear map, `a` a lift of `w₀` over `k[V]`, `b` a lift over `k[W]` and
`φ : b ⟶ a` a morphism of lifts lying over `Spec k[W] ⟶ Spec k[V]`. Given the comparison of
Stacks 0DLL between the lifts of `E₀` of `a` and `b`
(`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftAutPullback`), the infinitesimal
automorphisms `1 + g` of `a` and `1 + (𝒪 ⊗ f)_* g` of `b`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftUnipotentAut`) are intertwined by `φ`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftUnipotentAut_hom_comp_eq`). The base
change of `1 + g` along `𝒪_{X₀}[V] ⟶ 𝒪_{X₀}[W]` is `1 + (𝒪 ⊗ f)_* g`
(`Deformation.ComplexLift.sqZeroExtReductionBaseChange_comparisonHom_conj`), and the comparison
carries the automorphisms of `a` to those of `b`. At the canonical arrow between the trivial
deformations this is the naturality of `g ↦ 1 + g` on the trivial deformations of `w₀`
(`AlgebraicGeometry.Space.ComplexesSituation.fibreTrivialAutNatural_of_fibreLiftAutPullback`).

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d u

/-- **Endomorphisms over identities commute with a compatible morphism, on comparisons.** Let
`τ₁ : L₁ ≅ F ⋙ G₀` and `τ₂ : L₂ ≅ G₁ ⋙ F` be composition comparisons whose unit laws through
`ι₀ : G₀ ≅ 𝟭` and `ι₁ : G₁ ≅ 𝟭` are the identifications `L₁ = F` and `L₂ = F`. For
`cf : F E' ⟶ E` and automorphisms `ε` of `E` and `ε'` of `E'` with `cf ≫ ε = F ε' ≫ cf`, the
composite comparisons of `(ι₀ ≫ ε⁻¹, cf)` and of `(cf, ι₁ ≫ ε'⁻¹)` agree. It is checked once, for
abstract functors. -/
theorem CategoryTheory.Functor.fibreComp_vert_comm {C₀ C₁ : Type*} [Category* C₀]
    [Category* C₁] {F : C₁ ⥤ C₀} {G₀ : C₀ ⥤ C₀} {G₁ : C₁ ⥤ C₁} {L₁ L₂ : C₁ ⥤ C₀}
    (τ₁ : L₁ ≅ F ⋙ G₀) (ι₀ : G₀ ≅ 𝟭 C₀) {e₁ : L₁ = F}
    (h1 : τ₁ ≪≫ Functor.isoWhiskerLeft F ι₀ ≪≫ F.rightUnitor = eqToIso e₁)
    (τ₂ : L₂ ≅ G₁ ⋙ F) (ι₁ : G₁ ≅ 𝟭 C₁) {e₂ : L₂ = F}
    (h2 : τ₂ ≪≫ Functor.isoWhiskerRight ι₁ F ≪≫ F.leftUnitor = eqToIso e₂)
    {E : C₀} {E' : C₁} (cf : F.obj E' ⟶ E) (ε : E ≅ E) (ε' : E' ≅ E')
    (h : cf ≫ ε.hom = F.map ε'.hom ≫ cf) (p : L₂.obj E' = L₁.obj E') :
    eqToHom p ≫ Functor.fibreComp τ₁ (ι₀.hom.app E ≫ ε.inv) cf =
      Functor.fibreComp τ₂ cf (ι₁.hom.app E' ≫ ε'.inv) := by
  have h' : cf ≫ ε.inv = F.map ε'.inv ≫ cf := by
    rw [Iso.comp_inv_eq, Category.assoc, h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      Functor.map_id, Category.id_comp]
  subst e₁ e₂
  have k1 := NatTrans.congr_app (congrArg Iso.hom h1) E'
  have k2 := NatTrans.congr_app (congrArg Iso.hom h2) E'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app] at k1 k2
  have hn := ι₀.hom.naturality cf
  simp only [Functor.id_map] at hn
  simp only [eqToHom_refl, Category.id_comp, Functor.fibreComp, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% hn, reassoc_of% k1, h', reassoc_of% k2]

/-- The canonical arrow between the trivial deformations along a module map lies, on the
right-hand components, over the morphism of trivial square-zero extensions. -/
theorem AlgebraicGeometry.Space.isHomLift_right_of_liftBaseOverMap.{v, w} (A : Type u) [CommRing A]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
    {M N : SiteModule A B} (f : M ⟶ N) {a b : Under x} (φ : a ⟶ b)
    (h : (Under.post p).IsHomLift (liftBaseOverMap A B S hS toS hA p x hx f).left φ) :
    p.IsHomLift (squareZeroOverMap A B S hS toS f) φ.right :=
  underPost_isHomLift_right p _ φ h

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

attribute [local instance] complexesCategory

/-- **Morphisms over identities given by automorphisms of the complexes commute with a morphism
compatible with them.** For a morphism `c : A ⟶ A'` of `Complexes_{X/Y}` and automorphisms `ε`
of `E_A` and `ε'` of `E_{A'}` with `c.fibre ∘ ε = L(X_c)^* ε' ∘ c.fibre`, the endomorphisms of
`A` and `A'` over the identities of their test schemes attached to `ε` and `ε'` satisfy
`n_ε ≫ c = c ≫ n_{ε'}`. -/
theorem complexesHom_vert_comp_eq_comp_vert {A A' : ComplexesObject D} (c : ComplexesHom A A')
    (ε : A.E ≅ A.E) (ε' : A'.E ≅ A'.E)
    (h : c.fibre ≫ ε.hom =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap c.base)).map ε'.hom ≫ c.fibre) :
    (⟨𝟙 A.T, (D.idComparison A.T).hom.app A.E ≫ ε.inv, inferInstance⟩ :
        ComplexesHom A A).comp c =
      c.comp (⟨𝟙 A'.T, (D.idComparison A'.T).hom.app A'.E ≫ ε'.inv, inferInstance⟩ :
        ComplexesHom A' A') := by
  have key := Functor.fibreComp_vert_comm (D.compComparison (𝟙 A.T) c.base) (D.idComparison A.T)
    (D.idComparison_comp_fac c.base) (D.compComparison c.base (𝟙 A'.T)) (D.idComparison A'.T)
    (D.comp_idComparison_fac c.base) c.fibre ε ε' h
  fapply ComplexesHom.ext
  · exact (Category.id_comp c.base).trans (Category.comp_id c.base).symm
  rw [ComplexesHom.comp_fibre, ComplexesHom.comp_fibre]
  dsimp only
  exact key _

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : ComplexesObject D}
  {hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {hk : B.Contains (Spec (.of k))}
  [hDer : ∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (coefficientRing (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)))]

/-- **A morphism of lifts of `w₀` intertwines the infinitesimal automorphisms attached to
compatible automorphisms of the lifts of `E₀`.** -/
theorem fibreLiftEndOfAut_hom_comp_eq {V W : FGModuleCat.{u} k}
    (a : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (b : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj W)) (φ : b.1.right ⟶ a.1.right)
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (α : Aut (fibreLiftDerivedLift (hDer := hDer V) a hK).K.obj)
    (hα : (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj V))).baseChange.map
          α.asIso.hom = 𝟙 _)
    (β : Aut (fibreLiftDerivedLift (hDer := hDer W) b hK).K.obj)
    (hβ : (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj
        ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).obj W))).baseChange.map
          β.asIso.hom = 𝟙 _)
    (hφ : φ.a.fibre ≫ (fibreDataComplexAut (hDer := hDer W) b.1.right.x b.1.hom.a
          (fibreLiftRetraction b) (fibreLiftSection_comp_retraction b)
          (isSquareZeroClosedImmersion_fibreLiftSection b) (fibreLiftScheme_left_eq b)
          (fibreLiftSection_conj b) hK β).hom =
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap φ.a.base)).map
          (fibreDataComplexAut (hDer := hDer V) a.1.right.x a.1.hom.a
            (fibreLiftRetraction a) (fibreLiftSection_comp_retraction a)
            (isSquareZeroClosedImmersion_fibreLiftSection a) (fibreLiftScheme_left_eq a)
            (fibreLiftSection_conj a) hK α).hom ≫ φ.a.fibre) :
    (fibreLiftEndOfAut (hDer := hDer W) b hK β hβ).1.right ≫ φ =
      φ ≫ (fibreLiftEndOfAut (hDer := hDer V) a hK α hα).1.right :=
  TwoFibreProductOver.Hom.ext'
    (complexesHom_vert_comp_eq_comp_vert φ.a _ _ hφ)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **The naturality of `g ↦ 1 + g` along morphisms of lifts of `w₀`**: for a linear map
`f : V ⟶ W` and a morphism `φ : b ⟶ a` from a lift of `w₀` over `k[W]` to one over `k[V]` lying
over `Spec k[W] ⟶ Spec k[V]`, the comparison of Stacks 0DLL
(`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftAutPullback`) makes `φ` intertwine
`1 + (𝒪 ⊗ f)_* g` on `b` with `1 + g` on `a`. -/
theorem fibreLiftUnipotentAut_hom_comp_eq (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (h : FibreLiftAutPullback (hDer := hDer) hK) {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (b : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj W)) (φ : b.1 ⟶ a.1)
    (hφ : (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
        (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom)).IsHomLift
      (squareZeroOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        ((fgSiteModule B hk).map f)) φ.right)
    (g : (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      x₀.E).obj V) :
    Functor.Fiber.fiberInclusion.map (fibreLiftUnipotentAut (hDer' := hDer) b hK
        ((coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
          x₀.E).map f g)) ≫ φ =
      φ ≫ Functor.Fiber.fiberInclusion.map (fibreLiftUnipotentAut (hDer' := hDer) a hK g) := by
  obtain ⟨e, he, hnat⟩ := h f a b φ.right hφ (Under.w φ)
  have hαβ := sqZeroExtReductionBaseChange_comparisonHom_conj.{d, d, u + 1}
    ((coefficientModule (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)).map f)
    (fibreLiftDerivedLift (hDer := hDer V) a hK) (fibreLiftDerivedLift (hDer := hDer W) b hK)
    e he (Multiplicative.ofAdd g)
  have hαβ' := Aut.ext (x := Aut.of (e.symm ≪≫ (coefficientReductionBaseChange.{d, u + 1}
      (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) f).functor.mapIso
        (comparisonHom (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) V)
          (fibreLiftDerivedLift (hDer := hDer V) a hK) (Multiplicative.ofAdd g)).asIso ≪≫ e)) hαβ
  have hmem : ∀ {U : FGModuleCat.{u} k}
      (y : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj U))
      (g' : (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        x₀.E).obj U),
      comparisonHom (coefficientReduction.{d, u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk) U)
        (fibreLiftDerivedLift (hDer := hDer U) y hK) (Multiplicative.ofAdd g') ∈
          automorphismsOfLift _ (fibreLiftDerivedLift (hDer := hDer U) y hK) :=
    fun _ _ => mem_of_range_eq _ (comparisonHom_range _ _) _
  have hα := (mem_automorphismsOfLift_iff _).1 (hmem a g)
  have hβ := (mem_automorphismsOfLift_iff _).1 (hαβ' ▸ hmem b _)
  have hU : fibreLiftUnipotentAut (hDer' := hDer) b hK
      ((coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
        x₀.E).map f g) = fibreLiftEndOfAut (hDer := hDer W) b hK _ hβ :=
    fibreLiftEndOfAut_congr (hDer := hDer W) b hK hαβ'.symm _ hβ
  have key := fibreLiftEndOfAut_hom_comp_eq a b φ.right hK _ hα _ hβ (hnat _)
  rw [hU]
  exact Under.UnderMorphism.ext key

/-- **`g ↦ 1 + g` commutes with restriction along morphisms of lifts of `w₀`**: for a morphism
`φ : b ⟶ a` of lifts of `w₀` lying over the map of base thickenings induced by `f : V ⟶ W`, the
infinitesimal automorphism `1 + (𝒪 ⊗ f)_* g` of `b` is the restriction along `φ`
(`Deformation.Artin.fiberEndRestrict`) of `1 + g` on `a`. -/
theorem fibreLiftUnipotentAut_eq_fiberEndRestrict
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (h : FibreLiftAutPullback (hDer := hDer) hK) {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj V))
    (b : FibreLift D iΛ x₀ hx₀ hk ((fgSiteModule B hk).obj W)) (φ : b.1 ⟶ a.1)
    (hφ : (Under.post (TwoFibreProductOver.structureFunctor (complexesFunctor D)
        (Over.map x₀.T.left.hom) (baseProj D.Y) (complexesToBaseObjects D)
        (schemePointToBase D.Y x₀.T.left x₀.T.hom))).IsHomLift
      (liftBaseOverMap k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
          (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
        (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
        ((fgSiteModule B hk).map f)).left φ)
    (g : (coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
      x₀.E).obj V) :
    fibreLiftUnipotentAut (hDer' := hDer) b hK
        ((coefficientHomLinearFunctor.{u + 1} (fieldPointCoefficientMap D iΛ x₀ hx₀ hk)
          x₀.E).map f g) =
      fiberEndRestrict _ (underPost_isFiberedInGroupoids _
        (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
          (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
          (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
          (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom)) (fibreBasePoint D x₀)) φ hφ
        (fibreLiftUnipotentAut (hDer' := hDer) a hK g) :=
  fiberEndRestrict_eq _ _ φ hφ _ _ (fibreLiftUnipotentAut_hom_comp_eq hK h f a b φ
    (isHomLift_right_of_liftBaseOverMap k B S hS _ hk _ (fibreBasePoint D x₀)
      (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) ((fgSiteModule B hk).map f) φ hφ) g)

/-- **Stacks 0DLL: the naturality of `g ↦ 1 + g` on the trivial deformations of `w₀`**
(`AlgebraicGeometry.Space.ComplexesSituation.FibreTrivialAutNatural`), from the comparison of the
lifts of `E₀` of a lift of `w₀` and of a pullback of it
(`AlgebraicGeometry.Space.ComplexesSituation.FibreLiftAutPullback`): the transition map of
`Inf_{w₀}` is restriction along the canonical arrow between the trivial deformations
(`Deformation.Artin.infinitesimalAutomorphismSetFunctor_map`), which carries `1 + g` to
`1 + (𝒪 ⊗ f)_* g` by
`AlgebraicGeometry.Space.ComplexesSituation.fibreLiftUnipotentAut_eq_fiberEndRestrict`. -/
theorem fibreTrivialAutNatural_of_fibreLiftAutPullback
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (hK : DerivedCategory.TStructure.t.minus x₀.E)
    (h : FibreLiftAutPullback (hDer := hDer) hK) :
    FibreTrivialAutNatural (hDer' := hDer) hfib hK := by
  intro V W f g
  let := underPost_isFibered _ (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
    (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
    (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
    (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom)) (fibreBasePoint D x₀)
  exact ((infinitesimalAutomorphismSetFunctor_map k B S hS _ hk _ _ _ _
    ((fgSiteModule B hk).map f) _).trans
    (fibreLiftUnipotentAut_eq_fiberEndRestrict hfib hK h f
      (Functor.pullbackFiber _ (liftId k B S hS _ hk _ (fibreBasePoint D x₀)
        (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk))
        (liftBaseOver k B S hS _ hk _ (fibreBasePoint D x₀)
          (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) ((fgSiteModule B hk).obj V)).hom)
      (Functor.pullbackFiber _ (liftId k B S hS _ hk _ (fibreBasePoint D x₀)
        (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk))
        (liftBaseOver k B S hS _ hk _ (fibreBasePoint D x₀)
          (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) ((fgSiteModule B hk).obj W)).hom)
      _ (Functor.pullbackFiberMap_isHomLift _ _ _) g).symm).symm

end ComplexesSituation

end AlgebraicGeometry.Space

end
