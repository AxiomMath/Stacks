module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeIso
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 073K, part (2): `H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')` as `B`-modules

For the cartesian square of **Stacks 073J**

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `𝓕` a quasi-coherent `𝒪_X`-module and `𝓕' = (g')^*𝓕`, **Stacks 073K, part (2)** says that if
`g` is flat, `f` is quasi-compact and quasi-separated and the two bases are affine, `Y = Spec(A)`
and `Y' = Spec(B)`, then

`H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')`

in every degree `i ≥ 0`, as `B`-modules: the left by its tensor factor `B`, the right because
`X'` lives over `Y' = Spec(B)`.

## Main definitions

* `AlgebraicGeometry.Space.BaseChangeDiagram.pulledBackMul`: the geometric action of `b ∈ B` on
  `𝓕'`, multiplication by the global regular function on `X'` that `b` pulls back to along `f'`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.baseModuleMul`: multiplication by `b` on the
  coordinate ring `B` of `Y'` read as an `A`-module.
* `Stacks.FlatDevissage.baseLinearEquivOfEquivariant`: an `A`-linear isomorphism `P ⊗_A R ≅ T`
  equivariant for the second tensor factor, as an `R`-linear isomorphism `R ⊗_A P ≅ T`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.naturalCohomologyPushforwardIso`: the isomorphism
  `H^i(X', 𝓕') ≅ H^i(X, g'_*𝓕')`, natural in the coefficient.
* `AlgebraicGeometry.Space.BaseChangeDiagram.cohomologyTensorTargetIso`: the isomorphism
  `H^i(X, 𝓕 ⊗_A B) ≅ H^i(X', 𝓕')`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeCoreIso`: the `A`-linear
  isomorphism `H^i(X, 𝓕) ⊗_A B ≅ H^i(X', 𝓕')`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase`: the isomorphism
  `H^i(X, 𝓕) ⊗_A B ≅ H^i(X', 𝓕')` of `B`-modules.

## Main results

* `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear_globalSmul`: over an affine
  chart, the comparison of sections intertwines multiplication of the second tensor factor by `b`
  with the geometric action of `b`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorIso_globalSmul`: the same for the
  glued isomorphism of sheaves.
* `AlgebraicGeometry.Space.rightDerived_globalSections_map_globalSmul`: derived global sections
  carry multiplication by a global regular function to multiplication by it.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeCoreIso_globalSmul`: the
  `A`-linear isomorphism `H^i(X, 𝓕) ⊗_A B ≅ H^i(X', 𝓕')` is equivariant for the two actions of `B`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules
open Stacks.FlatDevissage
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.TensorByBaseModule hiding ringSheaf

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe v w u

namespace Stacks.RightDerivedComp

/-- **The collapse isomorphism of `Stacks.RightDerivedComp.objIso`, read through a natural
isomorphism, is natural at an endomorphism of a `G`-acyclic object.** For a natural isomorphism
`e : R ⁿ (G ⋙ T) ≅ K`, the composite of `e.inv` with the collapse commutes with the actions of
`K` and of `R ⁿ T ∘ G` on an endomorphism `g`. -/
theorem objIso_comp_naturality {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C] [HasInjectiveResolutions D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [G.PreservesInjectiveObjects]
    (T : D ⥤ E) [T.Additive] (n : ℕ) {A : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A)) {K : C ⥤ E}
    (e : (G ⋙ T).rightDerived n ≅ K) (g : A ⟶ A) :
    K.map g ≫ (e.inv.app A ≫ (objIso G (injectiveResolution A) hA T n).hom) =
      (e.inv.app A ≫ (objIso G (injectiveResolution A) hA T n).hom) ≫
        (T.rightDerived n).map (G.map g) := by
  rw [← Category.assoc, e.inv.naturality, Category.assoc,
    objIso_hom_naturality G T n hA hA g, Category.assoc]

end Stacks.RightDerivedComp

namespace CategoryTheory

/-- **The comparison of the values of two equal functors at an object**, the `eqToIso` of the
equality of those values. -/
def Functor.eqToIsoObj {C D : Type*} [Category* C] [Category* D] {F F' : C ⥤ D} (hF : F = F')
    (M : C) : F.obj M ≅ F'.obj M :=
  eqToIso (congrArg (fun G => G.obj M) hF)

/-- **The comparison of the values of two equal functors intertwines their actions on an
endomorphism.** -/
theorem Functor.eqToIsoObj_comm {C D : Type*} [Category* C] [Category* D] {F F' : C ⥤ D}
    (hF : F = F') {M : C} (u : M ⟶ M) :
    F.map u ≫ (Functor.eqToIsoObj hF M).hom =
      (Functor.eqToIsoObj hF M).hom ≫ F'.map u := by
  subst hF
  simp [Functor.eqToIsoObj]

/-- **A commuting square between endomorphisms is carried to one by any functor.** -/
theorem Functor.map_comm {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y : C}
    {a : X ⟶ X} {b : Y ⟶ Y} {f : X ⟶ Y} (h : a ≫ f = f ≫ b) :
    F.map a ≫ F.map f = F.map f ≫ F.map b := by
  rw [← F.map_comp, h, F.map_comp]

/-- **Two commuting squares between endomorphisms compose**, along the composite of their
horizontal edges. -/
theorem endComm_comp {C : Type*} [Category* C] {X Y Z : C} {a : X ⟶ X} {b : Y ⟶ Y} {c : Z ⟶ Z}
    {f : X ⟶ Y} {g : Y ⟶ Z} (h₁ : a ≫ f = f ≫ b) (h₂ : b ≫ g = g ≫ c) :
    a ≫ f ≫ g = (f ≫ g) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **A commuting square against an isomorphism gives the square against its inverse**, with the
two endomorphisms exchanged. -/
theorem Iso.comm_inv {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y) {a : X ⟶ X} {b : Y ⟶ Y}
    (h : a ≫ e.hom = e.hom ≫ b) : b ≫ e.inv = e.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

end CategoryTheory

namespace Stacks.FlatDevissage

/-- **Multiplication by `b`, as an `A`-linear endomorphism of a commutative `A`-algebra `R`.** -/
def mulBaseMap {A : Type u} [CommRing A] {R : Type u} [CommRing R] [Algebra A R] (b : R) :
    ModuleCat.of A R ⟶ ModuleCat.of A R :=
  ModuleCat.ofHom (LinearMap.mulLeft A b)

/-- `Stacks.FlatDevissage.mulBaseMap b` sends `c` to `b * c`. -/
@[simp]
theorem mulBaseMap_apply {A : Type u} [CommRing A] {R : Type u} [CommRing R] [Algebra A R]
    (b c : R) : (mulBaseMap (A := A) b).hom c = b * c :=
  rfl

/-- **The map `a ↦ a • (b * c)` is `a ↦ a • c` followed by multiplication by `b`.** -/
theorem spanHom_mul {A : Type u} [CommRing A] {R : Type u} [CommRing R] [Algebra A R]
    (b c : R) :
    spanHom (M := ModuleCat.of A R) (b * c) = spanHom (M := ModuleCat.of A R) c ≫ mulBaseMap b :=
  (spanHom_comp c (mulBaseMap (A := A) b)).symm

/-- **Tensoring on the left is natural in the second factor**: an isomorphism of the first factor
commutes with an endomorphism of the second. -/
theorem tensorLeftObjIso_comm {A : Type u} [CommRing A] {P P' : ModuleCat.{w} A} (e : P ≅ P')
    {M : ModuleCat.{v} A} (u : M ⟶ M) :
    (tensorLeftFunctor.{u, w, v} P).map u ≫ (tensorLeftObjIso e M).hom =
      (tensorLeftObjIso e M).hom ≫ (tensorLeftFunctor.{u, w, v} P').map u :=
  ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

/-- **An `A`-linear isomorphism `P ⊗_A R ≅ T` which is equivariant for the second tensor factor is
an `R`-linear isomorphism `R ⊗_A P ≅ T`.** Here `T` carries an `A`-module and an `R`-module
structure, with no compatibility between them assumed; the hypothesis `hφ` says that `φ` carries
`x ⊗ (b * c)` to `b • φ (x ⊗ c)`. The underlying map is `φ` composed with the symmetry of the
tensor product. -/
def baseLinearEquivOfEquivariant {A : Type u} [CommRing A] {R : Type u} [CommRing R]
    [Algebra A R] {P : Type v} [AddCommGroup P] [Module A P]
    {T : Type v} [AddCommGroup T] [Module A T] [Module R T]
    (φ : (P ⊗[A] R) ≃ₗ[A] T)
    (hφ : ∀ (b c : R) (x : P), φ (x ⊗ₜ[A] (b * c)) = b • φ (x ⊗ₜ[A] c)) :
    (R ⊗[A] P) ≃ₗ[R] T := by
  classical
  set ψ : (R ⊗[A] P) →ₗ[A] T :=
    φ.toLinearMap ∘ₗ (TensorProduct.comm A R P).toLinearMap with hψ
  have hsmul : ∀ (b : R) (z : R ⊗[A] P), ψ (b • z) = b • ψ z := by
    intro b z
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      rw [TensorProduct.smul_tmul']
      change φ ((TensorProduct.comm A R P) ((b * c) ⊗ₜ[A] x)) =
        b • φ ((TensorProduct.comm A R P) (c ⊗ₜ[A] x))
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul]
      exact hφ b c x
    | add z w hz hw => rw [smul_add, map_add, map_add, hz, hw, smul_add]
  refine LinearEquiv.ofBijective
    ({ toFun := ψ, map_add' := ψ.map_add, map_smul' := hsmul } : (R ⊗[A] P) →ₗ[R] T) ?_
  exact φ.bijective.comp (TensorProduct.comm A R P).bijective

end Stacks.FlatDevissage

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived global sections of a multiplication by a global regular function are
multiplication by that function.** -/
theorem rightDerived_globalSections_map_globalSmul (X : AlgebraicSpaces B S hS)
    [HasInjectiveResolutions (Modules.{u, u} B S hS X.1 X.2)]
    (σ : GlobalSectionRing (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (M : Modules.{u, u} B S hS X.1 X.2) (i : ℕ) :
    ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).map
        (globalSmul _ σ M) =
      σ • 𝟙 (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj M) := by
  rw [globalSmul_eq_smul_id]
  exact (Functor.linear_iff _ _).1 inferInstance M σ

/-- **The two spellings of the tensor functor of an affine base agree**: tensoring by a module over
the coordinate ring, built from `AlgebraicGeometry.Space.baseChartCoefficientMap`, is the one built
from `AlgebraicGeometry.Space.geometricCoefficientMap`. -/
theorem tensorByBaseChartModule_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀) [IsIso V₀.obj.hom]
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    tensorByBaseChartModule B S hS f hV₀ 𝓕 =
      tensorByBaseModuleOfHom (baseChartRing B S hS Y V₀) (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) 𝓕 (geometricCoefficientMap B S hS f V₀) :=
  congrArg (fun θ => tensorByBaseModuleOfHom (baseChartRing B S hS Y V₀)
      (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) 𝓕 θ)
    (baseChartCoefficientMap_eq B S hS f hV₀)

variable {B S hS}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-- **The pulled back coefficient is acyclic for the direct image along `g'`**: the higher direct
images `R^n(g')_*𝓕'` vanish for `n > 0`, as in **Stacks 073H** for the affine morphism `g'` and the
quasi-coherent `𝓕'`. -/
theorem isZero_rightDerived_pushforward_pulledBack
    (hg' : yoneda.relativelyRepresentable D.g'.hom) (haff : IsAffineHom B S hS D.g'.hom)
    (n : ℕ) (hn : 0 < n) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    IsZero (((modulePushforward B S hS D.g').rightDerived n).obj D.pulledBack) :=
  isZero_rightDerived_modulePushforward_of_chartwise B S hS D.g' hg' D.pulledBack n
    (chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS D.g' haff hg' D.pulledBack
      D.isQuasicoherentOnSite_pulledBack n hn)

/-- **The collapse step of Stacks 073K, part (2), in a form that is natural in the coefficient**:
`H^i(X', 𝓕') ≅ H^i(X, g'_*𝓕')`, as `Γ(X, 𝒪_X)`-modules, through the Leray collapse
`Stacks.RightDerivedComp.objIso`. -/
def naturalCohomologyPushforwardIso (hg : IsFlat B S hS D.g.hom) (hY : IsAffineSpace B S hS D.Y.1)
    (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    ((globalSectionsRestrictScalars B S hS D.g').obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
          i).obj D.pulledBack) ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).rightDerived i).obj
        ((modulePushforward B S hS D.g').obj D.pulledBack)) :=
  have _h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have _h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  haveI := preservesInjectiveObjects_modulePushforward_of_isFlat B S hS D.g' (D.isFlat_g' hg)
  ((derivedGlobalSectionsPushforwardIso B S hS D.g' i).app D.pulledBack).symm ≪≫
    Stacks.RightDerivedComp.objIso (modulePushforward B S hS D.g')
      (injectiveResolution D.pulledBack)
      (D.isZero_rightDerived_pushforward_pulledBack (D.relativelyRepresentable_g' hY hY')
        (D.isAffineHom_g' hY hY'))
      (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)) i

/-- **The collapse is natural at an endomorphism of the coefficient.** -/
theorem naturalCohomologyPushforwardIso_naturality (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1)
    (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) (ν : D.pulledBack ⟶ D.pulledBack) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    ((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i ⋙
            globalSectionsRestrictScalars B S hS D.g').map ν ≫
        (D.naturalCohomologyPushforwardIso hg hY hY' i).hom =
      (D.naturalCohomologyPushforwardIso hg hY hY' i).hom ≫
        ((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).rightDerived
          i).map ((modulePushforward B S hS D.g').map ν) :=
  have _h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have _h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  have := preservesInjectiveObjects_modulePushforward_of_isFlat B S hS D.g' (D.isFlat_g' hg)
  Stacks.RightDerivedComp.objIso_comp_naturality (modulePushforward B S hS D.g')
    (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)) i
    (D.isZero_rightDerived_pushforward_pulledBack (D.relativelyRepresentable_g' hY hY')
      (D.isAffineHom_g' hY hY'))
    (derivedGlobalSectionsPushforwardIso B S hS D.g' i) ν


variable (hg' : yoneda.relativelyRepresentable D.g'.hom)
  (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]

/-- **The comparison of sections is equivariant for the second tensor factor, over a chart.**
Multiplying the second factor of `s ⊗ (c ⊗ b')` by `b` multiplies the image under
`AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear` by the pullback of `b` to
the base-changed chart. -/
theorem pushforwardTensorAppLinear_tmul_mul (U : SmallEtale B S hS D.X.1)
    (s : D.F.val.obj (op U)) (c : chartRing B S hS D.X.1 D.X.2 U)
    (b b' : baseChartRing B S hS D.Y' V₀') :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.pushforwardSectionsModule hg' U
    D.pushforwardTensorAppLinear hg' V₀ V₀' U
        (s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U]
          (c ⊗ₜ[baseChartRing B S hS D.Y V₀] (b * b'))) =
      D.baseChangeChartBaseHom hg' V₀' U b •
        D.pushforwardTensorAppLinear hg' V₀ V₀' U
          (s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U] (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b')) := by
  let := D.chartBaseAlgebra V₀ U
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.chartBaseChangeChartAlgebra hg' U
  let := D.pushforwardSectionsModule hg' U
  have hring : D.chartRingTensorHom hg' V₀ V₀' U
        (c ⊗ₜ[baseChartRing B S hS D.Y V₀] (b * b')) =
      D.baseChangeChartBaseHom hg' V₀' U b •
        D.chartRingTensorHom hg' V₀ V₀' U (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b') := by
    rw [D.chartRingTensorHom_tmul hg' V₀ V₀' U c (b * b'),
      D.chartRingTensorHom_tmul hg' V₀ V₀' U c b', map_mul, smul_eq_mul,
      Algebra.smul_def, Algebra.smul_def]
    ring
  have key : ∀ y : baseChartRing B S hS D.Y' V₀',
      D.pushforwardTensorAppLinear hg' V₀ V₀' U
          (s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U] (c ⊗ₜ[baseChartRing B S hS D.Y V₀] y)) =
        D.chartRingTensorHom hg' V₀ V₀' U (c ⊗ₜ[baseChartRing B S hS D.Y V₀] y) •
          D.unitSection hg' U s := fun _ => rfl
  rw [key (b * b'), key b', hring, smul_eq_mul, mul_smul]

/-- **Over a chart, the comparison of sections intertwines multiplication of the second tensor
factor by `b` with the geometric action of `b` on `𝓕'`.** -/
theorem pushforwardTensorAppLinear_globalSmul (hV₀' : IsTerminal V₀')
    (b : baseChartRing B S hS D.Y' V₀') (U : SmallEtale B S hS D.X.1)
    (s : D.F.val.obj (op U)) (c : chartRing B S hS D.X.1 D.X.2 U)
    (b' : baseChartRing B S hS D.Y' V₀') :
    letI := D.chartBaseAlgebra V₀ U
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    letI := D.pushforwardSectionsModule hg' U
    D.pushforwardTensorAppLinear hg' V₀ V₀' U
        (s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U]
          (c ⊗ₜ[baseChartRing B S hS D.Y V₀] (b * b'))) =
      (globalSmul _ (baseChartGlobalSectionRingHom B S hS D.f' hV₀' b)
          D.pulledBack).val.app (op (D.baseChangeChart hg' U))
        (D.pushforwardTensorAppLinear hg' V₀ V₀' U
          (s ⊗ₜ[chartRing B S hS D.X.1 D.X.2 U]
            (c ⊗ₜ[baseChartRing B S hS D.Y V₀] b'))) := by
  let := D.chartBaseAlgebra V₀ U
  let := baseChartAlgebra B S hS D.g V₀ V₀'
  let := D.pushforwardSectionsModule hg' U
  have hb : (baseChartGlobalSectionRingHom B S hS D.f' hV₀' b).val
        (op (D.baseChangeChart hg' U)) = D.baseChangeChartBaseHom hg' V₀' U b :=
    baseChartRingHom_apply B S hS D.f' hV₀' (D.baseChangeChart hg' U) b
  rw [globalSmul_app, hb]
  exact D.pushforwardTensorAppLinear_tmul_mul hg' V₀ V₀' U s c b b'

/-- **Multiplication by `b` on the coordinate ring `B` of `Y'`, read as an `A`-linear endomorphism
of the base module.** -/
def baseModuleMul (b : baseChartRing B S hS D.Y' V₀') :
    D.baseModule V₀ V₀' ⟶ D.baseModule V₀ V₀' :=
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  mulBaseMap b

/-- **The geometric action of `b ∈ B` on `𝓕'`**: multiplication by the global regular function on
`X'` that `b` pulls back to along `f'`. -/
def pulledBackMul (hV₀' : IsTerminal V₀') (b : baseChartRing B S hS D.Y' V₀') :
    D.pulledBack ⟶ D.pulledBack :=
  globalSmul _ (baseChartGlobalSectionRingHom B S hS D.f' hV₀' b) D.pulledBack

/-- **The presheaf-level comparison is equivariant, on a tensor `s ⊗ n`.** -/
theorem pushforwardTensorApp_globalSmul_tmul (hV₀' : IsTerminal V₀')
    (b : baseChartRing B S hS D.Y' V₀') {W : (SmallEtale B S hS D.X.1)ᵒᵖ}
    (s : D.F.val.obj W)
    (n : ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (geometricCoefficientMap B S hS D.f V₀)).obj
      ((Stacks.TensorByBaseModule.constantModulePresheaf
        (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀'))).obj W) :
    (((tensorByBaseModulePresheafOfHom (baseChartRing B S hS D.Y V₀)
              (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
              (geometricCoefficientMap B S hS D.f V₀)).map (D.baseModuleMul V₀ V₀' b) ≫
          D.pushforwardTensorComparison hg' V₀ V₀').app W).hom (s ⊗ₜ n) =
      ((D.pushforwardTensorComparison hg' V₀ V₀' ≫
          (PresheafOfModules.restrictScalars
              (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
                (structureSheaf B S hS D.X.1 D.X.2)).obj)).map
            ((SheafOfModules.forget _).map
              ((smallBaseChangeModulePushforward B S hS D.g' hg').map
                (D.pulledBackMul V₀' hV₀' b)))).app W).hom (s ⊗ₜ n) := by
  let := ((geometricCoefficientMap B S hS D.f V₀).app W).hom.toAlgebra
  let : Module (((structureSheaf B S hS D.X.1 D.X.2).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj W) (D.F.val.obj W) :=
    (D.F.val.obj W).isModule
  let : Module ((Stacks.TensorByBaseModule.constantRingPresheaf
        (C := SmallEtale B S hS D.X.1) (baseChartRing B S hS D.Y V₀)).obj W)
      (((Stacks.TensorByBaseModule.constantModulePresheaf
        (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀')).obj W) :=
    (((Stacks.TensorByBaseModule.constantModulePresheaf
      (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀')).obj W).isModule
  let : Module (((structureSheaf B S hS D.X.1 D.X.2).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj W)
      ((structureSheaf B S hS D.X.1 D.X.2).obj.obj W ⊗[
          (Stacks.TensorByBaseModule.constantRingPresheaf
            (C := SmallEtale B S hS D.X.1) (baseChartRing B S hS D.Y V₀)).obj W]
        (((Stacks.TensorByBaseModule.constantModulePresheaf
          (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀')).obj W)) :=
    (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
        (geometricCoefficientMap B S hS D.f V₀)).obj
      ((Stacks.TensorByBaseModule.constantModulePresheaf
        (baseChartRing B S hS D.Y V₀)).obj (D.baseModule V₀ V₀'))).obj W).isModule
  let : Module ((structureSheaf B S hS D.X.1 D.X.2).obj.obj W) (D.F.val.obj W) :=
    (D.F.val.obj W).isModule
  induction n using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((congrArg _ (TensorProduct.tmul_add s x y)).trans (map_add _ _ _)).trans
      ((congrArg₂ (· + ·) hx hy).trans
        (((congrArg _ (TensorProduct.tmul_add s x y)).trans (map_add _ _ _)).symm))
  | tmul c b' =>
    exact D.pushforwardTensorAppLinear_globalSmul hg' V₀ V₀' hV₀' b W.unop s c b'

/-- **The presheaf-level comparison `𝓕 ⊗_{\underline A} \underline B ⟶ g'_*𝓕'` is equivariant** for
multiplication of the second tensor factor by `b` and the geometric action of `b` on `𝓕'`. -/
theorem pushforwardTensorComparison_globalSmul (hV₀' : IsTerminal V₀')
    (b : baseChartRing B S hS D.Y' V₀') :
    (tensorByBaseModulePresheafOfHom (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).map (D.baseModuleMul V₀ V₀' b) ≫
        D.pushforwardTensorComparison hg' V₀ V₀' =
      D.pushforwardTensorComparison hg' V₀ V₀' ≫
        (PresheafOfModules.restrictScalars
            (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
              (structureSheaf B S hS D.X.1 D.X.2)).obj)).map
          ((SheafOfModules.forget _).map
            ((smallBaseChangeModulePushforward B S hS D.g' hg').map
              (D.pulledBackMul V₀' hV₀' b))) := by
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul s n => exact D.pushforwardTensorApp_globalSmul_tmul hg' V₀ V₀' hV₀' b s n

/-- **The gluing isomorphism is the transpose of the comparison** across the sheafification
adjunction. -/
theorem pushforwardTensorIso_hom (_hV₀' : IsTerminal V₀')
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] :
    (D.pushforwardTensorIso hg' V₀ V₀').hom =
      (PresheafOfModules.sheafificationHomEquiv.{u}
        (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
          (structureSheaf B S hS D.X.1 D.X.2)).obj)).symm
        (D.pushforwardTensorComparison hg' V₀ V₀') :=
  rfl

/-- **The gluing isomorphism `𝓕 ⊗_{\underline A} \underline B ≅ g'_*𝓕'` is equivariant** for
multiplication of the second tensor factor by `b` and the geometric action of `b` on `𝓕'`. -/
theorem pushforwardTensorIso_globalSmul (hV₀' : IsTerminal V₀')
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    (b : baseChartRing B S hS D.Y' V₀') :
    (tensorByBaseModuleOfHom (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).map (D.baseModuleMul V₀ V₀' b) ≫
        (D.pushforwardTensorIso hg' V₀ V₀').hom =
      (D.pushforwardTensorIso hg' V₀ V₀').hom ≫
        (smallBaseChangeModulePushforward B S hS D.g' hg').map (D.pulledBackMul V₀' hV₀' b) := by
  have hHE : (PresheafOfModules.sheafificationHomEquiv.{u}
        (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
          (structureSheaf B S hS D.X.1 D.X.2)).obj)
        (P := (tensorByBaseModulePresheafOfHom (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).obj (D.baseModule V₀ V₀'))
        (F := D.pushforwardPulledBack hg')) =
      (PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
          (structureSheaf B S hS D.X.1 D.X.2)).obj)).homEquiv _ _ :=
    Equiv.ext fun _ => rfl
  have hhom : (D.pushforwardTensorIso hg' V₀ V₀').hom =
      (PresheafOfModules.sheafification.{u}
          (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
            (structureSheaf B S hS D.X.1 D.X.2)).obj)).map
          (D.pushforwardTensorComparison hg' V₀ V₀') ≫
        (PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
            (structureSheaf B S hS D.X.1 D.X.2)).obj)).counit.app
          (D.pushforwardPulledBack hg') := by
    rw [D.pushforwardTensorIso_hom hg' V₀ V₀' hV₀', hHE]
    rfl
  have hmap : (tensorByBaseModuleOfHom (baseChartRing B S hS D.Y V₀)
        (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
        (geometricCoefficientMap B S hS D.f V₀)).map (D.baseModuleMul V₀ V₀' b) =
      (PresheafOfModules.sheafification.{u}
        (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
          (structureSheaf B S hS D.X.1 D.X.2)).obj)).map
        ((tensorByBaseModulePresheafOfHom (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).map (D.baseModuleMul V₀ V₀' b)) := rfl
  have hnat := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
      (structureSheaf B S hS D.X.1 D.X.2)).obj)).counit.naturality
      ((smallBaseChangeModulePushforward B S hS D.g' hg').map (D.pulledBackMul V₀' hV₀' b))
  have h1 := Functor.map_comm (PresheafOfModules.sheafification.{u}
    (𝟙 (Stacks.TensorByBaseModule.ringSheaf (SmallEtale.topology B S hS D.X.1)
      (structureSheaf B S hS D.X.1 D.X.2)).obj))
    (D.pushforwardTensorComparison_globalSmul hg' V₀ V₀' hV₀' b)
  rw [hmap, hhom]
  exact endComm_comp h1 hnat


omit [IsIso V₀'.obj.hom] in
/-- **The comparison of the two spellings of the coefficient map is equivariant**, after any
functor out of the `𝒪_X`-modules. -/
theorem spellingSquare {E : Type (u + 2)} [Category.{u + 1} E] (hV₀ : IsTerminal V₀)
    (G : Modules.{u, u} B S hS D.X.1 D.X.2 ⥤ E) (b : baseChartRing B S hS D.Y' V₀') :
    G.map ((tensorByBaseChartModule B S hS D.f hV₀ D.F).map (D.baseModuleMul V₀ V₀' b)) ≫
        G.map (Functor.eqToIsoObj (tensorByBaseChartModule_eq B S hS D.f hV₀ D.F)
          (D.baseModule V₀ V₀')).hom =
      G.map (Functor.eqToIsoObj (tensorByBaseChartModule_eq B S hS D.f hV₀ D.F)
          (D.baseModule V₀ V₀')).hom ≫
        G.map ((tensorByBaseModuleOfHom (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).map (D.baseModuleMul V₀ V₀' b)) :=
  Functor.map_comm G
    (Functor.eqToIsoObj_comm (tensorByBaseChartModule_eq B S hS D.f hV₀ D.F)
      (D.baseModuleMul V₀ V₀' b))

/-- **The gluing isomorphism is equivariant**, after any functor out of the `𝒪_X`-modules. -/
theorem gluingSquare {E : Type (u + 2)} [Category.{u + 1} E] (hV₀' : IsTerminal V₀')
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    (G : Modules.{u, u} B S hS D.X.1 D.X.2 ⥤ E) (b : baseChartRing B S hS D.Y' V₀') :
    G.map ((tensorByBaseModuleOfHom (baseChartRing B S hS D.Y V₀)
          (SmallEtale.topology B S hS D.X.1) (structureSheaf B S hS D.X.1 D.X.2) D.F
          (geometricCoefficientMap B S hS D.f V₀)).map (D.baseModuleMul V₀ V₀' b)) ≫
        G.map (D.pushforwardTensorIso hg' V₀ V₀').hom =
      G.map (D.pushforwardTensorIso hg' V₀ V₀').hom ≫
        G.map ((smallBaseChangeModulePushforward B S hS D.g' hg').map
          (D.pulledBackMul V₀' hV₀' b)) :=
  Functor.map_comm G (D.pushforwardTensorIso_globalSmul hg' V₀ V₀' hV₀' b)

omit [IsIso V₀'.obj.hom] in
/-- **The comparison of the two direct images is equivariant**, after any functor out of the
`𝒪_X`-modules. -/
theorem chartComparisonSquare {E : Type (u + 2)} [Category.{u + 1} E] (hV₀' : IsTerminal V₀')
    (G : Modules.{u, u} B S hS D.X.1 D.X.2 ⥤ E) (b : baseChartRing B S hS D.Y' V₀') :
    G.map ((smallBaseChangeModulePushforward B S hS D.g' hg').map
          (D.pulledBackMul V₀' hV₀' b)) ≫
        G.map ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).inv =
      G.map ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).inv ≫
        G.map ((modulePushforward B S hS D.g').map (D.pulledBackMul V₀' hV₀' b)) :=
  Functor.map_comm G
    (Iso.comm_inv ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack)
      ((modulePushforwardChartIso B S hS D.g' hg').hom.naturality
        (D.pulledBackMul V₀' hV₀' b)))

omit [IsIso V₀'.obj.hom] in
/-- **The collapse is equivariant**, after any functor out of the `Γ(X, 𝒪_X)`-modules. -/
theorem collapseSquare {E : Type (u + 2)} [Category.{u + 1} E] (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1)
    (hV₀' : IsTerminal V₀') (i : ℕ)
    (G : ModuleCat.{u + 1} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O).obj) ⥤ E)
    (b : baseChartRing B S hS D.Y' V₀') :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    G.map (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).rightDerived i).map
          ((modulePushforward B S hS D.g').map (D.pulledBackMul V₀' hV₀' b))) ≫
        G.map (D.naturalCohomologyPushforwardIso hg hY hY' i).inv =
      G.map (D.naturalCohomologyPushforwardIso hg hY hY' i).inv ≫
        G.map ((((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i ⋙
            globalSectionsRestrictScalars B S hS D.g').map (D.pulledBackMul V₀' hV₀' b))) :=
  have _h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have _h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have _h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  Functor.map_comm G
    (Iso.comm_inv (D.naturalCohomologyPushforwardIso hg hY hY' i)
      (D.naturalCohomologyPushforwardIso_naturality hg hY hY' i (D.pulledBackMul V₀' hV₀' b)))

/-- **`H^i(X, 𝓕 ⊗_A B) ≅ H^i(X', 𝓕')`**: the composite of the identification of the two spellings
of the coefficient map, the gluing isomorphism `𝓕 ⊗_{\underline A} \underline B ≅ g'_*𝓕'`, the
identification of the two direct images, and the collapse `H^i(X, g'_*𝓕') ≅ H^i(X', 𝓕')` of the
Leray spectral sequence along the affine morphism `g'`. -/
def cohomologyTensorTargetIso (hg : IsFlat B S hS D.g.hom) (hY : IsAffineSpace B S hS D.Y.1)
    (hY' : IsAffineSpace B S hS D.Y'.1) (hV₀ : IsTerminal V₀)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (cohomologyTensorFunctor B S hS D.f hV₀ D.F i).obj (D.baseModule V₀ V₀') ≅
      (globalSectionsRestrictScalars B S hS D.f ⋙
          baseChartRestrictScalars B S hS D.Y hV₀).obj
        ((globalSectionsRestrictScalars B S hS D.g').obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack)) :=
  have _h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have _h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have _h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).mapIso
      (Functor.eqToIsoObj (tensorByBaseChartModule_eq B S hS D.f hV₀ D.F)
        (D.baseModule V₀ V₀')) ≪≫
    (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).mapIso
      (D.pushforwardTensorIso hg' V₀ V₀') ≪≫
    (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).mapIso
      ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).symm ≪≫
    (globalSectionsRestrictScalars B S hS D.f ⋙
      baseChartRestrictScalars B S hS D.Y hV₀).mapIso
      (D.naturalCohomologyPushforwardIso hg hY hY' i).symm

/-- **That composite is equivariant**: it intertwines the endomorphism induced by multiplying the
second tensor factor by `b` with the endomorphism induced by the geometric action of `b` on
`𝓕'`. -/
theorem cohomologyTensorTargetIso_globalSmul (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1)
    (hV₀ : IsTerminal V₀) (hV₀' : IsTerminal V₀')
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ)
    (b : baseChartRing B S hS D.Y' V₀') :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (cohomologyTensorFunctor B S hS D.f hV₀ D.F i).map (D.baseModuleMul V₀ V₀' b) ≫
        (D.cohomologyTensorTargetIso hg' V₀ V₀' hg hY hY' hV₀ i).hom =
      (D.cohomologyTensorTargetIso hg' V₀ V₀' hg hY hY' hV₀ i).hom ≫
        (globalSectionsRestrictScalars B S hS D.f ⋙
            baseChartRestrictScalars B S hS D.Y hV₀).map
          ((((globalSectionsFunctor.{u + 1, u, u, u}
                (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i ⋙ globalSectionsRestrictScalars B S hS D.g').map
            (D.pulledBackMul V₀' hV₀' b))) :=
  have _h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have _h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have _h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  endComm_comp (D.spellingSquare V₀ V₀' hV₀ (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i) b)
    (endComm_comp
      (D.gluingSquare hg' V₀ V₀' hV₀'
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i) b)
      (endComm_comp
        (D.chartComparisonSquare hg' V₀' hV₀'
          (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i) b)
        (D.collapseSquare V₀' hg hY hY' hV₀' i (globalSectionsRestrictScalars B S hS D.f ⋙
          baseChartRestrictScalars B S hS D.Y hV₀) b)))

/-- **The `A`-linear isomorphism `H^i(X, 𝓕) ⊗_A B ≅ H^i(X', 𝓕')`**: the dévissage along Lazard's
theorem (**Stacks 058G**) followed by
`AlgebraicGeometry.Space.BaseChangeDiagram.cohomologyTensorTargetIso`. -/
def affineCohomologyBaseChangeCoreIso (hZ : B.Contains (⊤_ Scheme.{u})) (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1)
    (hV₀ : IsTerminal V₀) [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    (hXqc : IsQuasiCompactSpace B S hS D.X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ D.X.1) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (tensorLeftFunctor.{u, u + 1, u} (D.affineCohomologyOverBaseChart V₀ i)).obj
        (D.baseModule V₀ V₀') ≅
      (globalSectionsRestrictScalars B S hS D.f ⋙
          baseChartRestrictScalars B S hS D.Y hV₀).obj
        ((globalSectionsRestrictScalars B S hS D.g').obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack)) :=
  have _h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have _h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have _h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  haveI := D.flat_baseModule hg V₀ V₀'
  haveI : IsIso ((cohomologyTensorComparison B S hS hZ D.f hV₀ hXqc hXqs D.F i).app
      (D.baseModule V₀ V₀')) :=
    isIso_cohomologyTensorComparison_app_of_flat B S hS hZ D.f hV₀ hXqc hXqs D.F i
      (D.baseModule V₀ V₀')
  tensorLeftObjIso (cohomologyTensorFunctorUnitIso B S hS D.f hV₀ D.F i).symm
      (D.baseModule V₀ V₀') ≪≫
    asIso ((cohomologyTensorComparison B S hS hZ D.f hV₀ hXqc hXqs D.F i).app
      (D.baseModule V₀ V₀')) ≪≫
    D.cohomologyTensorTargetIso hg' V₀ V₀' hg hY hY' hV₀ i

/-- **The core isomorphism is equivariant** for multiplication of the second tensor factor by
`b` and the geometric action of `b` on `𝓕'`. -/
theorem affineCohomologyBaseChangeCoreIso_globalSmul (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1)
    (hV₀ : IsTerminal V₀) (hV₀' : IsTerminal V₀')
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    (hXqc : IsQuasiCompactSpace B S hS D.X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ D.X.1) (i : ℕ)
    (b : baseChartRing B S hS D.Y' V₀') :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (tensorLeftFunctor.{u, u + 1, u} (D.affineCohomologyOverBaseChart V₀ i)).map
          (D.baseModuleMul V₀ V₀' b) ≫
        (D.affineCohomologyBaseChangeCoreIso hg' V₀ V₀' hZ hg hY hY' hV₀ hXqc hXqs i).hom =
      (D.affineCohomologyBaseChangeCoreIso hg' V₀ V₀' hZ hg hY hY' hV₀ hXqc hXqs i).hom ≫
        (globalSectionsRestrictScalars B S hS D.f ⋙
            baseChartRestrictScalars B S hS D.Y hV₀).map
          ((((globalSectionsFunctor.{u + 1, u, u, u}
                (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i ⋙ globalSectionsRestrictScalars B S hS D.g').map
            (D.pulledBackMul V₀' hV₀' b))) :=
  have _h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have _h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have _h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  endComm_comp (tensorLeftObjIso_comm (cohomologyTensorFunctorUnitIso B S hS D.f hV₀ D.F i).symm
      (D.baseModuleMul V₀ V₀' b))
    (endComm_comp ((cohomologyTensorComparison B S hS hZ D.f hV₀ hXqc hXqs D.F i).naturality
        (D.baseModuleMul V₀ V₀' b))
      (D.cohomologyTensorTargetIso_globalSmul hg' V₀ V₀' hg hY hY' hV₀ hV₀' i b))

omit [IsIso V₀.obj.hom] [IsIso V₀'.obj.hom] in
/-- **The endomorphism of `H^i(X', 𝓕')` that the equivariance produces is multiplication by
`b`** for the `B`-module structure the right hand side of Stacks 073K, part (2) carries through
`f'`. -/
theorem pulledBackMul_rightDerived_apply
    [HasInjectiveResolutions (Modules.{u, u} B S hS D.X'.1 D.X'.2)]
    (hV₀ : IsTerminal V₀) (hV₀' : IsTerminal V₀') (i : ℕ)
    (b : baseChartRing B S hS D.Y' V₀')
    (y : (cohomologyFunctorOverBaseChart B S hS D.f' hV₀' i).obj D.pulledBack) :
    ((globalSectionsRestrictScalars B S hS D.f ⋙
          baseChartRestrictScalars B S hS D.Y hV₀).map
        ((((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
            i ⋙ globalSectionsRestrictScalars B S hS D.g').map
          (D.pulledBackMul V₀' hV₀' b)))).hom y = b • y := by
  have key : (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).map
          (D.pulledBackMul V₀' hV₀' b)) =
      (baseChartGlobalSectionRingHom B S hS D.f' hV₀' b) • 𝟙 _ :=
    rightDerived_globalSections_map_globalSmul B S hS D.X'
      (baseChartGlobalSectionRingHom B S hS D.f' hV₀' b) D.pulledBack i
  exact ConcreteCategory.congr_hom key y

/-- **Flat base change of cohomology over affine bases: `H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')` as
`B`-modules.** For the cartesian square of **Stacks 073J** with `𝓕` quasi-coherent, `g` flat, `f`
quasi-compact and quasi-separated and the two bases affine — `Y = Spec(A)` and `Y' = Spec(B)`,
presented by the charts `V₀` and `V₀'` with `A` and `B` their coordinate rings — the extension of
scalars of `H^i(X, 𝓕)` along `A ⟶ B` is the cohomology of the pulled back coefficient on `X'`, in
every degree `i`, as modules over `B`: the left hand side by its tensor factor `B` and the right
hand side because `X'` lives over `Y' = Spec(B)`. The left hand side is written `B ⊗_A H^i(X, 𝓕)`,
the extension of scalars. -/
@[stacks 073K "part (2), the affine case: H^i(X,F) ⊗_A B = H^i(X',F') as B-modules"]
def affineCohomologyBaseChangeIsoBase (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    ModuleCat.of (baseChartRing B S hS D.Y' V₀')
        (baseChartRing B S hS D.Y' V₀' ⊗[baseChartRing B S hS D.Y V₀]
          ↥(D.affineCohomologyOverBaseChart V₀ i)) ≅
      (baseChartRestrictScalars B S hS D.Y' (isTerminal_of_isIso_chart B S hS D.Y' V₀')).obj
        (D.affineCohomologyTarget i) := by
  have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  letI := baseChartAlgebra B S hS D.g V₀ V₀'
  have hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
  have hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
  have hg' : yoneda.relativelyRepresentable D.g'.hom := D.relativelyRepresentable_g' hY hY'
  have hXqc : IsQuasiCompactSpace B S hS D.X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS D.f.hom hY hqc
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ D.X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ D.f.hom
      D.X.property hY hqs
  letI : Module (baseChartRing B S hS D.Y' V₀') ↥(D.affineCohomologyTarget i) :=
    ((baseChartRestrictScalars B S hS D.Y'
      (isTerminal_of_isIso_chart B S hS D.Y' V₀')).obj (D.affineCohomologyTarget i)).isModule
  letI : Module (baseChartRing B S hS D.Y V₀) ↥(D.affineCohomologyTarget i) :=
    ((globalSectionsRestrictScalars B S hS D.f ⋙
      baseChartRestrictScalars B S hS D.Y (isTerminal_of_isIso_chart B S hS D.Y V₀)).obj
        ((globalSectionsRestrictScalars B S hS D.g').obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack))).isModule
  refine LinearEquiv.toModuleIso (baseLinearEquivOfEquivariant
    ((D.affineCohomologyBaseChangeCoreIso hg' V₀ V₀' hZ hg hY hY'
      (isTerminal_of_isIso_chart B S hS D.Y V₀) hXqc hXqs i).toLinearEquiv :
      (↥(D.affineCohomologyOverBaseChart V₀ i) ⊗[baseChartRing B S hS D.Y V₀]
        (baseChartRing B S hS D.Y' V₀')) ≃ₗ[baseChartRing B S hS D.Y V₀]
        ↥(D.affineCohomologyTarget i))
    (fun b c x => ?_))
  exact (congrArg (fun m : (tensorLeftFunctor.{u, u + 1, u}
        (D.affineCohomologyOverBaseChart V₀ i)).obj (D.baseModule V₀ V₀') ⟶
      (globalSectionsRestrictScalars B S hS D.f ⋙
          baseChartRestrictScalars B S hS D.Y
            (isTerminal_of_isIso_chart B S hS D.Y V₀)).obj
        ((globalSectionsRestrictScalars B S hS D.g').obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack)) =>
      ModuleCat.Hom.hom m (x ⊗ₜ[baseChartRing B S hS D.Y V₀] c))
    (D.affineCohomologyBaseChangeCoreIso_globalSmul hg' V₀ V₀' hZ hg hY hY'
      (isTerminal_of_isIso_chart B S hS D.Y V₀)
      (isTerminal_of_isIso_chart B S hS D.Y' V₀') hXqc hXqs i b)).trans
    (D.pulledBackMul_rightDerived_apply V₀ V₀' (isTerminal_of_isIso_chart B S hS D.Y V₀)
      (isTerminal_of_isIso_chart B S hS D.Y' V₀') i b _)

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end
