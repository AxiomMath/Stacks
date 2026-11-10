module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPushforwardDirectSums
public import StacksFrontier.Algebra.Homology.DerivedCategory.IsIsoAppOfTermwiseColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize

/-!
# The canonical map of Tags 0F1J and 0F1N on unbounded objects

Let `K` be a field, `n ≥ 1` an integer invertible in `K`, and consider a commutative diagram
```
X <-p-- X' <-h-- Y
|       |f'      |e
v       v        v
Spec K <- S' <-g- T
```
of schemes of finite type over `K` with `X' = X ×_K S'` and `Y = X' ×_{S'} T`. [Stacks, Tag 0F1N]
asserts that the canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is an isomorphism for all `E ∈ D(X_étale, ℤ/nℤ)` and `F ∈ D(T_étale, ℤ/nℤ)`. [Stacks, Tag 0F1J]
asserts the same for `E ∈ D⁺` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺`. This file proves the
first from the second and from `cd(h) < ∞` and `cd(g) < ∞` ([Stacks, Tag 0F10] (1)), which is
the source's proof.

## The proof

The source's, with one change of variable noted below. Both sides of the map are exact functors
of each variable which commute with direct sums: `⊗^L` and the inverse images do in general
(`Stacks.EtaleCohomology.EtaleCoefficients.preservesColimitsOfShape_tensor_obj`,
`preservesColimitsOfShape_tensor_flip_obj`, `preservesColimitsOfShape_pullback`), and `Rh_*`,
`Rg_*` do by [Stacks, Tag 0F11] (1)
(`Stacks.EtaleCohomology.EtaleCoefficients.preservesColimitsOfShape_pushforward`), because
`cd(h), cd(g) < ∞` and `ℤ/nℤ` is torsion. A morphism of such functors which is invertible at the
stupid truncations `σ^{≥-N}` of a complex is invertible at the complex: the complex is their
colimit, hence their homotopy colimit
(`Stacks.DerivedCategoryColimit.isIso_app_Q_obj_of_stupidTrunc`).

* In the variable `F`, the stupid truncations of any representative of `F` are bounded below, so
  the map is invertible at every `F` once it is at every bounded below `F`.
* In the variable `E`, `E` is represented by a K-flat complex `𝓔` of flat sheaves of
  `ℤ/nℤ`-modules ([Stacks, Tag 06YS]); its stupid truncations `σ^{≥-N}𝓔` are again K-flat
  (the truncation sequence is degreewise split and `σ^{≤-N-1}𝓔` is a bounded above complex of
  flat modules, [Stacks, Tag 06YQ]), vanish below `-N`, and so lie in `D⁺` with Tor amplitude
  in `[-N, ∞]`. There [Stacks, Tag 0F1J] applies.

The source reduces `E` to bounded complexes of arbitrary sheaves and `F` to bounded complexes of
flat sheaves. As written that does not meet the hypothesis of [Stacks, Tag 0F1J], which asks for
the Tor amplitude bound on `E`, not on `F`; and `F` need only be bounded below there. Resolving
`E`, not `F`, by flat modules is what makes the hypotheses of Tag 0F1J hold, and it needs no
bound above on either variable.

## Main results

* `Stacks.Cohomology.AbstractKunnethMap.tensorBaseChangeMap_naturality` — the canonical map is
  natural in both variables.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_obj_of_isGE` — the
  reduction to bounded below objects of Tor amplitude bounded below, for an arbitrary diagram with
  `g` and `h` quasi-compact and quasi-separated of finite cohomological dimension, torsion
  coefficients, and the first variable put through a triangulated functor commuting with direct
  sums.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_isGE` — the same at
  `p⁻¹`, as in [Stacks, Tag 0F1N].
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_isGE_of_hasTorAmplitudeGE`
  — the same at the identity, for an arbitrary object of `D(X'_étale, Λ)`.

The application to schemes of finite type over a field, where `cd(g)` and `cd(h)` are finite by
[Stacks, Tag 0F10] (1), is
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeFiniteType`.

## References

* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

/-! ### Naturality of the canonical map -/

namespace Stacks.Cohomology.AbstractKunnethMap

variable {DX' DS' DT DY : Type*} [Category* DX'] [Category* DS'] [Category* DT] [Category* DY]
  {gPull : DS' ⥤ DT} {gPush : DT ⥤ DS'} (adjg : gPull ⊣ gPush)
  {hPull : DX' ⥤ DY} {hPush : DY ⥤ DX'} (adjh : hPull ⊣ hPush)
  (f'Pull : DS' ⥤ DX') (ePull : DT ⥤ DY)
  (β : f'Pull ⋙ hPull ≅ gPull ⋙ ePull)
  (TX' : DX' × DX' ⥤ DX') (TY : DY × DY ⥤ DY)
  (μ : TX' ⋙ hPull ⟶ hPull.prod hPull ⋙ TY)

/-- **The canonical map of Tags 0F1J and 0F1N is natural in both variables.** -/
theorem tensorBaseChangeMap_naturality {A A' : DX'} {F F' : DT} (a : A ⟶ A') (b : F ⟶ F') :
    TX'.map (a ×ₘ f'Pull.map (gPush.map b)) ≫
        tensorBaseChangeMap adjg adjh f'Pull ePull β TX' TY μ A' F' =
      tensorBaseChangeMap adjg adjh f'Pull ePull β TX' TY μ A F ≫
        hPush.map (TY.map (hPull.map a ×ₘ ePull.map b)) := by
  have hbc := (baseChangeMap adjg adjh f'Pull ePull β).naturality b
  simp only [Functor.comp_map] at hbc
  have key : TX'.map (a ×ₘ f'Pull.map (gPush.map b)) ≫
      TX'.map (𝟙 A' ×ₘ (baseChangeMap adjg adjh f'Pull ePull β).app F') =
      TX'.map (𝟙 A ×ₘ (baseChangeMap adjg adjh f'Pull ePull β).app F) ≫
        TX'.map (a ×ₘ hPush.map (ePull.map b)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, prod_comp, prod_comp, hbc]
    simp
  simp only [tensorBaseChangeMap]
  rw [← Category.assoc, key, Category.assoc, projectionMap_naturality, Category.assoc]

end Stacks.Cohomology.AbstractKunnethMap

open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` is stated for the
-- standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The canonical map as a natural transformation in each variable -/

section NatTrans

variable {X' S' T Y : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The canonical map of Tags 0F1J and 0F1N on `D(-_étale, Λ)` is natural in both variables. -/
theorem tensorBaseChangeMap_naturality {A A' : DerivedModules Λ X'} {F F' : DerivedModules Λ T}
    (a : A ⟶ A') (b : F ⟶ F') :
    ((tensor Λ X').map a).app _ ≫
        ((tensor Λ X').obj A').map ((pullback Λ f').map ((pushforward Λ g).map b)) ≫
        tensorBaseChangeMap Λ f' g h e w A' F' =
      tensorBaseChangeMap Λ f' g h e w A F ≫
        (pushforward Λ h).map (((tensor Λ Y).map ((pullback Λ h).map a)).app _ ≫
          ((tensor Λ Y).obj _).map ((pullback Λ e).map b)) := by
  have := Stacks.Cohomology.AbstractKunnethMap.tensorBaseChangeMap_naturality (adjunction Λ g)
    (adjunction Λ h) (pullback Λ f') (pullback Λ e)
    (pullbackCompIso Λ h f' ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ e g).symm)
    (Functor.uncurry.obj (tensor Λ X')) (Functor.uncurry.obj (tensor Λ Y))
    (pullbackTensorIso Λ h).hom a b
  simp only [Functor.uncurry_obj_map, Category.assoc] at this
  exact this

/-- **The canonical map as a natural transformation of the first variable**, for fixed
`F ∈ D(T_étale, Λ)`: `A ⊗^L (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L e⁻¹F)`. -/
def tensorBaseChangeNatTransLeft (F : DerivedModules Λ T) :
    (tensor Λ X').flip.obj ((pullback Λ f').obj ((pushforward Λ g).obj F)) ⟶
      pullback Λ h ⋙ (tensor Λ Y).flip.obj ((pullback Λ e).obj F) ⋙ pushforward Λ h where
  app A := tensorBaseChangeMap Λ f' g h e w A F
  naturality A A' a := by
    simpa using tensorBaseChangeMap_naturality Λ f' g h e w a (𝟙 F)

/-- **The canonical map as a natural transformation of the second variable**, for fixed
`A ∈ D(X'_étale, Λ)`: `A ⊗^L (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L e⁻¹F)`. -/
def tensorBaseChangeNatTransRight (A : DerivedModules Λ X') :
    pushforward Λ g ⋙ pullback Λ f' ⋙ (tensor Λ X').obj A ⟶
      pullback Λ e ⋙ (tensor Λ Y).obj ((pullback Λ h).obj A) ⋙ pushforward Λ h where
  app F := tensorBaseChangeMap Λ f' g h e w A F
  naturality F F' b := by
    simpa using tensorBaseChangeMap_naturality Λ f' g h e w (𝟙 A) b

end NatTrans

/-! ### The reduction to bounded below objects -/

section Reduction

/-- A functor commuting with direct sums indexed by `Type (u + 1)` commutes with countable
direct sums. -/
theorem preservesColimitsOfShape_discrete_nat {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [PreservesColimitsOfShape (Discrete (ULift.{u + 1} ℕ)) F] :
    PreservesColimitsOfShape (Discrete ℕ) F :=
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F

variable {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X')
  (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)

/-- **The reduction to bounded below objects, along an exact functor commuting with direct
sums.** Let `h ≫ f' = e ≫ g` be a commutative square with `g` and `h` quasi-compact and
quasi-separated of finite cohomological dimension, let `Λ` be torsion, and let
`P : D(X_étale, Λ) ⥤ D(X'_étale, Λ)` be a triangulated functor commuting with countable direct
sums. Suppose the canonical map

`P(E) ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹P(E) ⊗^L_Λ e⁻¹F)`

is invertible for `E ∈ D⁺(X_étale, Λ)` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, Λ)`.
Then it is invertible for all `E ∈ D(X_étale, Λ)` and `F ∈ D(T_étale, Λ)`.

`cd(g), cd(h) < ∞` and the torsion of `Λ` are what make `Rg_*` and `Rh_*` commute with direct sums
([Stacks, Tag 0F11] (1)). `P` is `p⁻¹` in [Stacks, Tag 0F1N] (`isIso_tensorBaseChangeMap_of_isGE`)
and the identity in `isIso_tensorBaseChangeMap_of_isGE_of_hasTorAmplitudeGE`. -/
theorem isIso_tensorBaseChangeMap_obj_of_isGE [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact h] [QuasiSeparated h] (hcd_g : g.etaleCohomologicalDimension < ⊤)
    (hcd_h : h.etaleCohomologicalDimension < ⊤) (hΛ : IsAddTorsion Λ)
    (P : DerivedModules Λ X ⥤ DerivedModules Λ X') [P.CommShift ℤ] [P.IsTriangulated]
    [PreservesColimitsOfShape (Discrete ℕ) P]
    (isIso_of_isGE : ∀ (E : DerivedModules Λ X) (F : DerivedModules Λ T) (a b c : ℤ),
      E.IsGE b → HasTorAmplitudeGE Λ E a → F.IsGE c →
      IsIso (tensorBaseChangeMap Λ f' g h e w (P.obj E) F))
    (E : DerivedModules Λ X) (F : DerivedModules Λ T) :
    IsIso (tensorBaseChangeMap Λ f' g h e w (P.obj E) F) := by
  have := @preservesColimitsOfShape_discrete_nat _ _ _ _ _
    (preservesColimitsOfShape_pushforward Λ g hcd_g hΛ _)
  have := @preservesColimitsOfShape_discrete_nat _ _ _ _ _
    (preservesColimitsOfShape_pushforward Λ h hcd_h hΛ _)
  have hT : ∀ (Z : Scheme.{u}) (B : DerivedModules Λ Z),
      PreservesColimitsOfShape (Discrete ℕ) ((tensor Λ Z).obj B) := fun Z B =>
    @preservesColimitsOfShape_discrete_nat _ _ _ _ _
      (preservesColimitsOfShape_tensor_obj Λ Z _ B)
  have hT' : ∀ (Z : Scheme.{u}) (B : DerivedModules Λ Z),
      PreservesColimitsOfShape (Discrete ℕ) ((tensor Λ Z).flip.obj B) := fun Z B =>
    @preservesColimitsOfShape_discrete_nat _ _ _ _ _
      (preservesColimitsOfShape_tensor_flip_obj Λ Z _ B)
  -- The variable `F`: the map is invertible at every `F` once it is at every bounded below `F`.
  have step : ∀ (E : DerivedModules Λ X) (a b : ℤ), E.IsGE b → HasTorAmplitudeGE Λ E a →
      ∀ F : DerivedModules Λ T, IsIso (tensorBaseChangeMap Λ f' g h e w (P.obj E) F) := by
    intro E a b hE hamp F
    have := hT X' (P.obj E)
    have := hT Y ((pullback Λ h).obj (P.obj E))
    exact Stacks.DerivedCategoryColimit.isIso_app_of_forall_isGE
      (tensorBaseChangeNatTransRight Λ f' g h e w (P.obj E))
      (fun F c hF => isIso_of_isGE E F a b c hE hamp hF) F
  -- The variable `E`: resolve by a K-flat complex of flat modules and truncate stupidly.
  obtain ⟨K, q, hK, hflat, hq, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize (ringedTopos Λ X).O
      (DerivedCategory.Q.objPreimage E)
  let eE : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := hT' X' ((pullback Λ f').obj ((pushforward Λ g).obj F))
  have := hT' Y ((pullback Λ e).obj F)
  let φ := Functor.whiskerLeft P (tensorBaseChangeNatTransLeft Λ f' g h e w F)
  change IsIso (φ.app E)
  refine (NatTrans.isIso_app_iff_of_iso φ eE).1 ?_
  refine Stacks.DerivedCategoryColimit.isIso_app_Q_obj_of_stupidTrunc φ K fun N => ?_
  refine step _ (-(N : ℤ)) (-(N : ℤ)) ?_ ?_ F
  · rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  · exact hasTorAmplitudeGE_Q_obj Λ _ _
      (Stacks.SheafOfModules.DerivedTensorProduct.isKFlat_stupidTruncGE
        (X := (ringedTopos Λ X).toRingedSite) K hK hflat _)
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE _ _ i hi)

/-- **[Stacks, Tag 0F1N] from [Stacks, Tag 0F1J], for an arbitrary commutative square with `g`
and `h` quasi-compact and quasi-separated of finite cohomological dimension and torsion
coefficients.** Let `h ≫ f' = e ≫ g` be a commutative square and `p : X' ⟶ X`. Suppose the
canonical map

`p⁻¹E ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_Λ e⁻¹F)`

is invertible for `E ∈ D⁺(X_étale, Λ)` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, Λ)`,
which is the conclusion of [Stacks, Tag 0F1J] (`boundedBelowCase`). Then it is invertible for all
`E ∈ D(X_étale, Λ)` and `F ∈ D(T_étale, Λ)`.

`cd(g), cd(h) < ∞` and the torsion of `Λ` are what make `Rg_*` and `Rh_*` commute with direct sums
([Stacks, Tag 0F11] (1)). -/
theorem isIso_tensorBaseChangeMap_of_isGE [QuasiCompact g] [QuasiSeparated g] [QuasiCompact h]
    [QuasiSeparated h] (hcd_g : g.etaleCohomologicalDimension < ⊤)
    (hcd_h : h.etaleCohomologicalDimension < ⊤) (hΛ : IsAddTorsion Λ)
    (boundedBelowCase : ∀ (E : DerivedModules Λ X) (F : DerivedModules Λ T) (a b c : ℤ),
      E.IsGE b → HasTorAmplitudeGE Λ E a → F.IsGE c →
      IsIso (tensorBaseChangeMap Λ f' g h e w ((pullback Λ p).obj E) F))
    (E : DerivedModules Λ X) (F : DerivedModules Λ T) :
    IsIso (tensorBaseChangeMap Λ f' g h e w ((pullback Λ p).obj E) F) :=
  isIso_tensorBaseChangeMap_obj_of_isGE Λ f' g h e w hcd_g hcd_h hΛ (pullback Λ p)
    boundedBelowCase E F

/-- **The reduction to bounded below objects, at an arbitrary object of `D(X'_étale, Λ)`.** Let
`h ≫ f' = e ≫ g` be a commutative square with `g` and `h` quasi-compact and quasi-separated of
finite cohomological dimension, and `Λ` torsion. If the canonical map

`A ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L_Λ e⁻¹F)`

is invertible for `A ∈ D⁺(X'_étale, Λ)` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, Λ)`,
then it is invertible for all `A ∈ D(X'_étale, Λ)` and `F ∈ D(T_étale, Λ)`. This is
`isIso_tensorBaseChangeMap_obj_of_isGE` at the identity functor of `D(X'_étale, Λ)`. -/
theorem isIso_tensorBaseChangeMap_of_isGE_of_hasTorAmplitudeGE [QuasiCompact g]
    [QuasiSeparated g] [QuasiCompact h] [QuasiSeparated h]
    (hcd_g : g.etaleCohomologicalDimension < ⊤) (hcd_h : h.etaleCohomologicalDimension < ⊤)
    (hΛ : IsAddTorsion Λ)
    (isIso_of_isGE : ∀ (A : DerivedModules Λ X') (F : DerivedModules Λ T) (a b c : ℤ),
      A.IsGE b → HasTorAmplitudeGE Λ A a → F.IsGE c →
      IsIso (tensorBaseChangeMap Λ f' g h e w A F))
    (A : DerivedModules Λ X') (F : DerivedModules Λ T) :
    IsIso (tensorBaseChangeMap Λ f' g h e w A F) :=
  isIso_tensorBaseChangeMap_obj_of_isGE (X := X') Λ f' g h e w hcd_g hcd_h hΛ (𝟭 _)
    isIso_of_isGE A F

end Reduction

/-- `ℤ/nℤ`, `n ≥ 1`, is a torsion ring. -/
theorem isTorsion_ulift_zmod (n : ℕ) [NeZero n] : IsAddTorsion (ULift.{u + 1} (ZMod n)) :=
  fun x => isOfFinAddOrder_of_finite x

end Stacks.EtaleCohomology.EtaleCoefficients
