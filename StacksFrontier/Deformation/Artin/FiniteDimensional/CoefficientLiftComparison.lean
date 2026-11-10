module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.TwoFibreTangentBound
public import StacksFrontier.Deformation.ToposThickening.CoefficientSquareZeroReduction

/-!
# The tangent space of a 2-fibre product from a comparison with derived lifts

Let `𝒲 = 𝒳 ×_𝒴 𝒵` be a 2-fibre product of categories fibred in groupoids satisfying (RS*) and
`w₀` an object of `𝒲` over a field `k`. Let `O₀` be a sheaf of commutative `k`-algebras on a site
(through `θ : k ⟶ O₀`), `K₀` a bounded above object of `D(O₀)`, and for a finite-dimensional
`V` let `O₀[V] = O₀ ⊕ (O₀ ⊗_k V)` be the trivial square-zero extension
(`Deformation.ComplexLift.coefficientRing`).

A *coefficient lift comparison* (`Deformation.Artin.CoefficientLiftComparison`) sends each lift
of `w₀` over `k[V]` to an isomorphism class of lifts of `K₀` to `O₀[V]` in the sense of Stacks
0DIZ, compatibly with pullback of lifts along linear maps `V ⟶ W` and derived base change along
`O₀[V] ⟶ O₀[W]`, together with a reference lift in `D^{≤ 0}` for each `V`, compatible with
base change, such that two lifts of `w₀` over `k[ε]` with the same image in `𝒵` and the same
class are equal. In the proof of Stacks 0DLL, `𝒵 = Spec k`, `O₀` is the structure sheaf of the
fibre `X₀` on its small étale site, `K₀ = E₀` and the reference lift is the trivial deformation
`z^*E₀`.

From such a comparison the difference class of Stacks 0DIZ against the reference lift is a
fibre invariant in the `k`-linear functor `V ↦ Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k V))⟦1⟧)`, so the
tangent space of `𝒲` at `w₀` is finite dimensional as soon as that of `𝒵` and
`Hom(K₀, K₀⟦1⟧)` (the value at `V = k`) are
(`finiteDimensional_tangentModuleAt_twoFibreProduct_of_coefficientLiftComparison`).

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 07WY](https://stacks.math.columbia.edu/tag/07WY)
-/

/- This instance makes the universe unifier get stuck on sheaves of modules over a site in
`Type (u + 1)`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Deformation.ComplexLift

universe d d₀ u u₁ v₁ u₂ v₂ u₃ v₃

@[expose] public noncomputable section

namespace Deformation.Artin

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (hk : B.Contains (Spec (.of k)))
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (p𝒵 : 𝒵 ⥤ BigFppfOver B S hS)
  (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴)
  (w₀ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 F G)
  (hw : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G).obj w₀ =
    algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk)
  {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O₀ : Sheaf J CommRingCat.{u}}
  (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)
  [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (coefficientRing θ V)))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  (K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))

/-- The isomorphism classes of lifts of `K₀` to `O₀[V]` (Stacks 0DIZ). -/
abbrev coefficientLiftClasses (V : FGModuleCat.{u} k) :=
  Quotient (DerivedLift.setoid
    (T := derivedExtensionOfScalarsData.{d, d₀}
      (sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj V))) (K₀ := K₀))

/-- **A comparison of the lifts of `w₀` with lifts of `K₀` to the square-zero extensions
`O₀[V]`**, natural in `V` and separating lifts over `k[ε]` with the same image in `𝒵`, with a
reference lift in `D^{≤ 0}` for every `V`, compatible with base change. In the proof of Stacks
0DLL the comparison sends a lift `(z, E)` to `E` on the small étale site of `X₀` and the
reference lift is `z^*E₀`. -/
structure CoefficientLiftComparison where
  /-- The class of lifts of `K₀` attached to a lift of `w₀` over `k[V]`. -/
  toLift (V : FGModuleCat.{u} k) :
    squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).obj V) →
      coefficientLiftClasses.{d, d₀} θ K₀ V
  /-- Pullback of lifts along a linear map is derived base change along `O₀[V] ⟶ O₀[W]`. -/
  toLift_pullback {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
      ((fgSiteModule B hk).obj V))
    (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
      ((fgSiteModule B hk).obj W)) :
    IsPullbackOfSquareZeroLift k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).map f) a b →
      toLift W b = (coefficientReductionBaseChange.{d, d₀} θ f).liftClassMap (toLift V a)
  /-- The reference lift over `O₀[V]`. -/
  base (V : FGModuleCat.{u} k) :
    DerivedLift (derivedExtensionOfScalarsData.{d, d₀}
      (sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj V))) K₀
  /-- The reference lifts lie in `D^{≤ 0}`. -/
  base_isLE (V : FGModuleCat.{u} k) : (base V).K.obj.IsLE 0
  /-- The reference lifts are compatible with base change. -/
  base_baseChange {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    DerivedLift.Isomorphic ((base V).baseChange (coefficientReductionBaseChange.{d, d₀} θ f))
      (base W)
  /-- Lifts over `k[ε]` with the same image in `𝒵` and the same class are equal. -/
  separates (a b : squareZeroLiftClasses k B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
      ((fgSiteModule B hk).obj (FGModuleCat.of k k))) :
    sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ a =
        sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ b →
      toLift (FGModuleCat.of k k) a = toLift (FGModuleCat.of k k) b → a = b

variable {B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw θ K₀}

/-- The connecting classes of two lifts to `O₀[V]` differ by a restricted class: the input of the
classification of Stacks 0DIZ (2) for the trivial square-zero extension. -/
theorem coefficientReduction_connectingClass_sub (V : FGModuleCat.{u} k)
    (L L' : DerivedLift (derivedExtensionOfScalarsData.{d, d₀}
      (sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj V))) K₀) :
    ∃ ξ, connectingClass (coefficientReduction.{d, d₀} θ V) L -
        connectingClass (coefficientReduction.{d, d₀} θ V) L' =
      shiftedRestriction (coefficientReduction.{d, d₀} θ V) ξ :=
  connectingClass_sub_flatReduction.{d, d₀}
    (sqZeroExtIdealInclusion ((coefficientModule θ).obj V))
    (sqZeroExtIdealInclusion_comp ((coefficientModule θ).obj V))
    (isLocallySurjective_ringSheafMapOf _
      (isLocallySurjective_sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj V)))
    (shortExact_sqZeroExtIdealSequence ((coefficientModule θ).obj V)) L L'

namespace CoefficientLiftComparison

variable (Φ : CoefficientLiftComparison.{d, d₀} B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw θ K₀)

/-- **The fibre invariant of a lift of `w₀` over `k[V]`**: the difference class of Stacks 0DIZ
of its lift of `K₀` against the reference lift, in `Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k V))⟦1⟧)`. -/
def invariant (V : FGModuleCat.{u} k)
    (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw ((fgSiteModule B hk).obj V)) :
    (coefficientExtLinearFunctor.{d₀} θ K₀.obj).obj V :=
  liftClassMap (coefficientReduction.{d, d₀} θ V) (Φ.base V) (Φ.toLift V a)

/-- The fibre invariant is natural: if `b` over `k[W]` is a pullback of `a` over `k[V]` along
`f : V ⟶ W`, then the invariant of `b` is the image of the invariant of `a` under the map induced
by `f`. -/
theorem invariant_natural {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
      ((fgSiteModule B hk).obj V))
    (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
      hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
      ((fgSiteModule B hk).obj W))
    (hab : IsPullbackOfSquareZeroLift k B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
      ((fgSiteModule B hk).map f) a b) :
    Φ.invariant W b = (coefficientExtLinearFunctor.{d₀} θ K₀.obj).map f (Φ.invariant V a) := by
  have := Φ.base_isLE V
  have hbase : ∀ q : coefficientLiftClasses.{d, d₀} θ K₀ W,
      liftClassMap (coefficientReduction.{d, d₀} θ W) (Φ.base W) q =
        liftClassMap (coefficientReduction.{d, d₀} θ W)
          ((Φ.base V).baseChange (coefficientReductionBaseChange.{d, d₀} θ f)) q := by
    intro q
    induction q using Quotient.inductionOn with
    | h L' =>
      exact (liftDifference_congr_right (coefficientReduction.{d, d₀} θ W)
        (coefficientReduction_connectingClass_sub W) (Φ.base_baseChange f)).symm
  change liftClassMap (coefficientReduction.{d, d₀} θ W) (Φ.base W) (Φ.toLift W b) =
    liftClassMap (coefficientReduction.{d, d₀} θ V) (Φ.base V) (Φ.toLift V a) ≫
      ((derivedTensorRightMap.{d₀} ((coefficientModule θ).map f)).app K₀.obj)⟦(1 : ℤ)⟧'
  rw [Φ.toLift_pullback f a b hab, hbase]
  exact liftClassMap_baseChange (coefficientReductionBaseChange.{d, d₀} θ f) (Φ.base V)
    (Φ.toLift V a)

/-- Two lifts of `w₀` over `k[ε]` with the same image in `𝒵` and the same fibre invariant are
equal. -/
theorem invariant_separates (a b : squareZeroLiftClasses k B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
      ((fgSiteModule B hk).obj (FGModuleCat.of k k)))
    (h𝒵 : sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ a =
      sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ b)
    (hθ : Φ.invariant (FGModuleCat.of k k) a = Φ.invariant (FGModuleCat.of k k) b) : a = b :=
  Φ.separates a b h𝒵 (liftClassMap_injective (coefficientReduction.{d, d₀} θ _)
    (coefficientReduction_connectingClass_sub _) (Φ.base _) hθ)

end CoefficientLiftComparison

/-- **Stacks 07WY for a 2-fibre product, from a comparison with derived lifts.** In the setting
of `Deformation.Artin.finiteDimensional_tangentModuleAt_twoFibreProduct_of_fibre`, a coefficient
lift comparison `Φ` (lifts of `w₀` over `k[V]` ↦ lifts of `K₀` to `O₀[V]`, Stacks 0DIZ) makes the
tangent space of `𝓕_{𝒲,k,w₀}` finite dimensional as soon as that of `𝓕_{𝒵,k,z₀}` and the
group `Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k k))⟦1⟧) = Ext¹(K₀, K₀)` are. -/
theorem finiteDimensional_tangentModuleAt_twoFibreProduct_of_coefficientLiftComparison
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (rs𝒳 : SatisfiesRSStar B S hS p𝒳 h𝒳) (rs𝒴 : SatisfiesRSStar B S hS p𝒴 h𝒴)
    (rs𝒵 : SatisfiesRSStar B S hS p𝒵 h𝒵)
    (hw₀ : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT𝒵 : ∀ (hz₀ : (p𝒵 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒵 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀)
        hz₀).projection),
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
          ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀) hz₀).projection) hD
        (FGModuleCat.of k k)))
    (Φ : CoefficientLiftComparison.{d, d₀} B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw θ K₀)
    [FiniteDimensional k ((coefficientExtLinearFunctor.{d₀} θ K₀.obj).obj (FGModuleCat.of k k))]
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
      hw₀).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
        hw₀).projection) hD (FGModuleCat.of k k)) :=
  finiteDimensional_tangentModuleAt_twoFibreProduct_of_fibre B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G h𝒳 h𝒴
    h𝒵 w₀ hw hF hG rs𝒳 rs𝒴 rs𝒵 hw₀ hfinite hqc hT𝒵 (coefficientExtLinearFunctor.{d₀} θ K₀.obj)
    Φ.invariant (fun f a b hab => Φ.invariant_natural f a b hab)
    (fun a b h𝒵 hθ => Φ.invariant_separates a b h𝒵 hθ) hD

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (coefficientRing θ V)))] in
/-- **The infinitesimal automorphisms of a 2-fibre product, from the groups
`Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))`.** In the setting of
`finiteDimensional_tangentModuleAt_twoFibreProduct_of_coefficientLiftComparison`, if the groups
`Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))` (Stacks 0DIZ (1): the infinitesimal automorphisms of a lift of `K₀`
to `O₀[V]`) map, naturally in `V` and surjectively at `V = k`, onto the infinitesimal
automorphisms of the trivial deformation of `w₀` over `k[V]`, then `Inf(𝓕_{𝒲,k,w₀})` of Stacks
07WY is finite dimensional as soon as `Hom(K₀, K₀ ⊗^L O₀) = Ext⁰(K₀, K₀)` is. In the proof of
Stacks 0DLL, `θ_V(φ)` is the automorphism `1 + φ` of the trivial deformation `z^*E₀`. -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_twoFibreProduct_of_coefficientHom
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (rs𝒳 : SatisfiesRSStar B S hS p𝒳 h𝒳) (rs𝒴 : SatisfiesRSStar B S hS p𝒴 h𝒴)
    (rs𝒵 : SatisfiesRSStar B S hS p𝒵 h𝒵)
    (hw₀ : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    [FiniteDimensional k ((coefficientHomLinearFunctor.{d₀} θ K₀.obj).obj (FGModuleCat.of k k))]
    (aut : ∀ V : FGModuleCat.{u} k, (coefficientHomLinearFunctor.{d₀} θ K₀.obj).obj V →
      (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 F G h𝒳 h𝒵 h𝒴 hF hG)
          ((fgSiteModule B hk).obj V) ⟶
        trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 F G h𝒳 h𝒵 h𝒴 hF hG)
          ((fgSiteModule B hk).obj V)))
    (haut : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (g : (coefficientHomLinearFunctor.{d₀} θ K₀.obj).obj V),
      aut W ((coefficientHomLinearFunctor.{d₀} θ K₀.obj).map f g) =
        (infinitesimalAutomorphismSetFunctor k B S hS
          (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 F G h𝒳 h𝒵 h𝒴 hF hG)).map
          ((fgSiteModule B hk).map f) (aut V g))
    (hsurj : Function.Surjective (aut (FGModuleCat.of k k)))
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
      hw₀).projection)
    (y : (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
      hw₀).carrier)
    (hy : (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
      hw₀).projection.obj y = Deformation.residueFieldObject Λ k)
    (P : ChosenPushforwardsAt (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
      hw₀).projection y) :
    letI := naturalLocalizedTangentAddCommGroup P hD.satisfiesRS
    letI := naturalLocalizedTangentModule P hD.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) :=
  finiteDimensional_localizedAutomorphismFunctorTangent_of_natural_surjective (B := B) (S := S)
    (hS := hS) (hk := hk) (p := TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) (x := w₀)
    (hp := TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 F G h𝒳 h𝒵 h𝒴 hF hG) (iΛ := iΛ)
    (hRS := twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 F G h𝒳 h𝒴 h𝒵 hF hG rs𝒳 rs𝒴
      rs𝒵)
    (hx₀ := hw₀) (hx' := hw) (G := coefficientHomLinearFunctor.{d₀} θ K₀.obj) (θ := aut)
    (hθ := haut) (hsurj := hsurj) (hD := hD) (y := y) (hy := hy) (P := P)

end Deformation.Artin

end
