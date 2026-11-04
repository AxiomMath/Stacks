module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.Deformation.Applications.TangentClassCoordinateMap
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTerm
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionUntwist

/-!
# The twisted sixth term of Stacks 0E3V as a functor of the coefficient module

The obstruction map of [Stacks Project, Tag 0E3V] over the square-zero base `k[M]` takes values in
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`. Its `k`-linearity is naturality in `M`: the addition and
scalar action of the tangent modules are produced by the maps of coordinate modules
(Tag 06IH), so a class map that commutes with them is linear
(`Deformation.isLinearMap_of_natural_at`). This file builds the target side of that naturality.

## Main definitions

* `AlgebraicGeometry.coefficientSheafFunctor`: `M ↦ p^* M^~` for a scheme `p : X ⟶ Spec k`, an
  additive and `k`-linear functor (`AlgebraicGeometry.coefficientSheafFunctor_linear`).
* `Deformation.Examples.schemeMorphismObstructionExtFunctor`: the twisted sixth term
  `M ↦ Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)` as an additive, `k`-linear functor
  `FGModuleCat k ⥤ ModuleCat k`, acting by postcomposition with `(𝒪_X ⊗_k g)[1]`.
* `Deformation.tangentModuleDescendLinearMap`: a class map on objects of the fibres over the
  `k[M]`, invariant under isomorphism and natural in `M` for a linear target functor, descends
  to a `k`-linear map on the tangent modules.

## Main results

* `AlgebraicGeometry.moduleSpecΓFunctor_linear`, `AlgebraicGeometry.tilde_functor_linear`,
  `AlgebraicGeometry.pullback_toSpec_linear`: global sections on `Spec k`, `M ↦ M^~` and pullback
  to a scheme over `k` are `k`-linear for the structures of `AlgebraicGeometry.modulesLinear`.
* `Deformation.isLinearMap_tangentModuleDescend`: the linearity of the descended map.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Global sections on `Spec k` are `k`-linear**, for the `k`-linear structure of
`AlgebraicGeometry.modulesLinear` at the identity of `Spec k`: a scalar acts on global sections
through `Γ(Spec k, ⊤) ≅ k`, which is the `k`-module structure of `moduleSpecΓFunctor`. -/
theorem moduleSpecΓFunctor_linear :
    letI : Linear k (Spec (CommRingCat.of k)).Modules :=
      modulesLinear k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (moduleSpecΓFunctor (R := CommRingCat.of k)).Linear k := by
  let : Linear k (Spec (CommRingCat.of k)).Modules :=
    modulesLinear k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  rw [Functor.linear_iff]
  intro M c
  ext x
  rfl

/-- **`M ↦ M^~` is `k`-linear**, for the `k`-linear structure of `AlgebraicGeometry.modulesLinear`
at the identity of `Spec k`: it is left adjoint to the global sections, which are `k`-linear. -/
theorem tilde_functor_linear :
    letI : Linear k (Spec (CommRingCat.of k)).Modules :=
      modulesLinear k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (tilde.functor (CommRingCat.of k)).Linear k := by
  let : Linear k (Spec (CommRingCat.of k)).Modules :=
    modulesLinear k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  have := moduleSpecΓFunctor_linear (k := k)
  exact leftAdjoint_linear_of_rightAdjoint_linear k tilde.adjunction

/-- **Pullback along a morphism to `Spec k` is `k`-linear**, for the `k`-linear structures of
`AlgebraicGeometry.modulesLinear`: it is left adjoint to the pushforward, which is `k`-linear by
`AlgebraicGeometry.over_pushforward_linear`. -/
theorem pullback_toSpec_linear {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) :
    letI : Linear k (Spec (CommRingCat.of k)).Modules :=
      modulesLinear k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    letI : Linear k X.Modules := modulesLinear k (Over.mk p)
    (Scheme.Modules.pullback p).Linear k := by
  let : Linear k (Spec (CommRingCat.of k)).Modules :=
    modulesLinear k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  let : Linear k X.Modules := modulesLinear k (Over.mk p)
  have : (Scheme.Modules.pushforward p).Linear k :=
    over_pushforward_linear k (Over.homMk p (Category.comp_id p) :
      Over.mk p ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))))
  exact leftAdjoint_linear_of_rightAdjoint_linear k (Scheme.Modules.pullbackPushforwardAdjunction p)

/-- `M ↦ M^~` is additive, being a left adjoint. -/
theorem tilde_functor_additive : (tilde.functor (CommRingCat.of k)).Additive := by
  have : (tilde.functor (CommRingCat.of k)).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tilde.functor (CommRingCat.of k))
  exact Functor.additive_of_preservesBinaryBiproducts _

attribute [local instance] tilde_functor_additive

/-- **The quasi-coherent sheaf `𝒪_X ⊗_k M` as a functor of the `k`-vector space `M`**, for a
scheme `X` over `k`: `M ↦ p^* M^~`, valued in the sheaves of modules over the structure sheaf of
the underlying ringed space. -/
def coefficientSheafFunctor {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) :
    FGModuleCat.{u} k ⥤ SheafOfModules.{u} (structureSheafRing X.toRingedSpace) where
  obj M := (Scheme.Modules.pullback p).obj ((tilde.functor (CommRingCat.of k)).obj M.obj)
  map g := (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map g.hom)
  map_id M := by
    have h : (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map (𝟙 M.obj)) =
        𝟙 _ := by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact h
  map_comp g h := by
    have e : (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map
        (g.hom ≫ h.hom)) =
        (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map g.hom) ≫
          (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map h.hom) := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    exact e

/-- The functor `M ↦ p^* M^~` is additive. -/
instance {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) :
    (coefficientSheafFunctor p).Additive where
  map_add {M N g h} := by
    have e : (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map
        (g.hom + h.hom)) =
        (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map g.hom) +
          (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map h.hom) := by
      rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]
    exact e

/-- The functor `M ↦ p^* M^~` is `k`-linear, for the `k`-linear structure of
`AlgebraicGeometry.modulesLinear` at `p`. -/
theorem coefficientSheafFunctor_linear {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) :
    letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      modulesLinear k (Over.mk p)
    (coefficientSheafFunctor p).Linear k := by
  let : Linear k (Spec (CommRingCat.of k)).Modules :=
    modulesLinear k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  let : Linear k X.Modules := modulesLinear k (Over.mk p)
  have := tilde_functor_linear (k := k)
  have := pullback_toSpec_linear (k := k) p
  let : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    modulesLinear k (Over.mk p)
  refine ⟨fun {M N} g c => ?_⟩
  change (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map (c • g.hom)) =
    c • (Scheme.Modules.pullback p).map ((tilde.functor (CommRingCat.of k)).map g.hom)
  rw [Functor.map_smul, Functor.map_smul]

end AlgebraicGeometry

namespace Deformation

section NaturalClass

open CategoryTheory

universe w v₁ u₁ z

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
  (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p)
  (G : FGModuleCat.{w} k ⥤ ModuleCat.{z} k)
  (t : ∀ M : FGModuleCat.{w} k,
    𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj M) → G.obj M)
  (hinv : ∀ (M : FGModuleCat.{w} k) (x x' : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ
      k).obj M)),
    IsIsomorphic x x' → t M x = t M x')

/-- **A class map on objects of the fibres descends to the tangent module.** If `t` takes
isomorphic objects of the fibre over `k[M]` to the same value, it factors through the class
`Deformation.tangentClassAt`. -/
noncomputable def tangentModuleDescend (M : FGModuleCat.{w} k) :
    ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 M) → G.obj M :=
  fun τ => t M (tangentClassAt_surjective.{u, w, w} 𝓕 h𝓕 M τ).choose

include hinv in
/-- The descended map sends the tangent class of an object `x` of the fibre over `k[M]` to
`t M x`. -/
theorem tangentModuleDescend_tangentClassAt (M : FGModuleCat.{w} k)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj M)) :
    tangentModuleDescend 𝓕 h𝓕 G t M (tangentClassAt.{u, w, w} 𝓕 h𝓕 M x) = t M x :=
  hinv M _ x ((tangentClassAt_eq_iff.{u, w, w} 𝓕 h𝓕 M _ x).mp
    (tangentClassAt_surjective.{u, w, w} 𝓕 h𝓕 M (tangentClassAt.{u, w, w} 𝓕 h𝓕 M x)).choose_spec)

variable [G.Additive] [G.Linear k]
  (hnat : ∀ {M N : FGModuleCat.{w} k} (g : M ⟶ N)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj M))
    (y : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj N)) (a : x.1 ⟶ y.1),
    𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, w} Λ k).map g) a → t N y = G.map g (t M x))

include hinv hnat in
/-- **A class map natural in the coordinate module is `k`-linear on tangent modules.** -/
theorem isLinearMap_tangentModuleDescend (M : FGModuleCat.{w} k) :
    IsLinearMap k (tangentModuleDescend 𝓕 h𝓕 G t M) := by
  refine isLinearMap_of_natural_at k (associatedTangentSpaceModuleStructure.{u, w, w} 𝓕
    h𝓕.predeformation (tangentConditionS2.{u, w, w} h𝓕)).functor G
    (fun M => tangentModuleDescend 𝓕 h𝓕 G t M) (fun {M N} g τ => ?_) M
  obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, w, w} 𝓕 h𝓕 M τ
  obtain ⟨y, a, ha⟩ := exists_pushforward h𝓕.predeformation.cofibered
    ((squareZeroExtensionArtinian.{u, w, w} Λ k).map g) x.1 x.2
  have hy : 𝓕.p.obj y = (squareZeroExtensionArtinian.{u, w, w} Λ k).obj N :=
    IsHomLift.codomain_eq 𝓕.p ((squareZeroExtensionArtinian.{u, w, w} Λ k).map g) a
  let y' : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj N) := ⟨y, hy⟩
  have h := tangentModuleMapAt_tangentClassAt.{u, w, w} 𝓕 h𝓕 g x y' a ha
  rw [tangentModuleMapAt_eq] at h
  show tangentModuleDescend 𝓕 h𝓕 G t N ((((associatedTangentSpaceModuleStructure.{u, w, w} 𝓕
    h𝓕.predeformation (tangentConditionS2.{u, w, w} h𝓕)).functor.map g).hom)
      (tangentClassAt.{u, w, w} 𝓕 h𝓕 M x)) = _
  rw [h, tangentModuleDescend_tangentClassAt 𝓕 h𝓕 G t hinv N y',
    tangentModuleDescend_tangentClassAt 𝓕 h𝓕 G t hinv M x]
  exact hnat g x y' a ha

/-- The descended class map as a `k`-linear map. -/
noncomputable def tangentModuleDescendLinearMap (M : FGModuleCat.{w} k) :
    ↥(tangentModuleAt.{u, w, w} 𝓕 h𝓕 M) →ₗ[k] G.obj M :=
  (isLinearMap_tangentModuleDescend 𝓕 h𝓕 G t hinv hnat M).mk' _

/-- The descended `k`-linear map sends the tangent class of an object `x` of the fibre over `k[M]`
to `t M x`. -/
theorem tangentModuleDescendLinearMap_tangentClassAt (M : FGModuleCat.{w} k)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj M)) :
    tangentModuleDescendLinearMap 𝓕 h𝓕 G t hinv hnat M (tangentClassAt.{u, w, w} 𝓕 h𝓕 M x) =
      t M x :=
  tangentModuleDescend_tangentClassAt 𝓕 h𝓕 G t hinv M x

end NaturalClass

end Deformation

namespace Deformation.Examples

attribute [local instance] HasDerivedCategory.standard

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-- **The coefficient sheaf `𝒪_X ⊗_k M` as a functor of `M`**: `M ↦ (f ≫ pY)^* M^~`. -/
abbrev schemeMorphismCoefficientSheafFunctor :
    FGModuleCat.{u} k ⥤ SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  coefficientSheafFunctor (f ≫ pY : X ⟶ Spec (CommRingCat.of k))

/-- The shifted single complex `(𝒪_X ⊗_k M)[1]` as a functor of `M`. -/
abbrev schemeMorphismCoefficientShiftFunctor :
    FGModuleCat.{u} k ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  schemeMorphismCoefficientSheafFunctor f pY ⋙
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ⋙
      shiftFunctor _ (1 : ℤ)

/-- The functor `M ↦ (𝒪_X ⊗_k M)[1]` is `k`-linear, for the `k`-linear structure of
`AlgebraicGeometry.modulesLinear` at `f ≫ pY`. -/
theorem schemeMorphismCoefficientShiftFunctor_linear :
    letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      modulesLinear k (Over.mk (f ≫ pY))
    (schemeMorphismCoefficientShiftFunctor f pY).Linear k := by
  let : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    modulesLinear k (Over.mk (f ≫ pY))
  have := coefficientSheafFunctor_linear (k := k) (f ≫ pY : X ⟶ Spec (CommRingCat.of k))
  infer_instance

/-- The map of twisted sixth terms induced by a map of coefficient modules: postcomposition with
the shifted single complex of the map of coefficient sheaves. -/
def schemeMorphismObstructionExtTwistedMap {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    letI := schemeMorphismObstructionExtTwistedModule f pY M
    letI := schemeMorphismObstructionExtTwistedModule f pY N
    schemeMorphismObstructionExtTwisted f pY M →ₗ[k] schemeMorphismObstructionExtTwisted f pY N :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    modulesLinear k (Over.mk (f ≫ pY))
  Linear.rightComp k _ ((schemeMorphismCoefficientShiftFunctor f pY).map g)

/-- **The twisted sixth term `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)` as a functor of the coefficient
module `M`**: postcomposition with `(𝒪_X ⊗_k g)[1]`. -/
def schemeMorphismObstructionExtFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{u + 1} k where
  obj M := @ModuleCat.of k _ (schemeMorphismObstructionExtTwisted f pY M) _
    (schemeMorphismObstructionExtTwistedModule f pY M)
  map {M N} g :=
    letI := schemeMorphismObstructionExtTwistedModule f pY M
    letI := schemeMorphismObstructionExtTwistedModule f pY N
    ModuleCat.ofHom (schemeMorphismObstructionExtTwistedMap f pY g)
  map_id M := by
    let := schemeMorphismObstructionExtTwistedModule f pY M
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map (𝟙 M) = e
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  map_comp {M N O} g h := by
    let := schemeMorphismObstructionExtTwistedModule f pY M
    let := schemeMorphismObstructionExtTwistedModule f pY O
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map (g ≫ h) =
      ((e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map g) ≫
        (schemeMorphismCoefficientShiftFunctor f pY).map h
    rw [CategoryTheory.Functor.map_comp]
    exact (Category.assoc _ _ _).symm

/-- The functor of twisted sixth terms acts by postcomposition. -/
theorem schemeMorphismObstructionExtFunctor_map_apply {M N : FGModuleCat.{u} k} (g : M ⟶ N)
    (e : schemeMorphismObstructionExtTwisted f pY M) :
    (schemeMorphismObstructionExtFunctor f pY).map g e =
      (e : _ ⟶ _) ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((coefficientSheafFunctor (f ≫ pY : X ⟶ Spec (CommRingCat.of k))).map g))⟦(1 : ℤ)⟧' :=
  rfl

/-- The functor of twisted sixth terms is additive. -/
instance : (schemeMorphismObstructionExtFunctor f pY).Additive where
  map_add {M N g h} := by
    let := schemeMorphismObstructionExtTwistedModule f pY M
    let := schemeMorphismObstructionExtTwistedModule f pY N
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map (g + h) =
      (e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map g +
        (e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map h
    rw [CategoryTheory.Functor.map_add]
    exact Preadditive.comp_add _ _ _ _ _ _

/-- The functor of twisted sixth terms is `k`-linear. -/
instance : (schemeMorphismObstructionExtFunctor f pY).Linear k where
  map_smul {M N} g c := by
    let := schemeMorphismObstructionExtTwistedModule f pY M
    let := schemeMorphismObstructionExtTwistedModule f pY N
    let : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      modulesLinear k (Over.mk (f ≫ pY))
    have := schemeMorphismCoefficientShiftFunctor_linear f pY
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map (c • g) =
      c • ((e : _ ⟶ _) ≫ (schemeMorphismCoefficientShiftFunctor f pY).map g)
    rw [CategoryTheory.Functor.map_smul]
    exact Linear.comp_smul _ _ _ _ _ _

end Deformation.Examples
