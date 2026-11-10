module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.GlobalSectionLinear
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomCounitTransport

/-!
# An invertible homothety makes every endomorphism a scalar

Let `X` be a scheme and `K` an object of `D(𝒪_X)`. The global sections `Γ(X, 𝒪_X)` act on every
object of `D(𝒪_X)` by multiplication. If the homothety `𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)` is an
isomorphism, then every endomorphism of `K` in `D(𝒪_X)` is multiplication by a global section.

By the tensor–internal-hom bijection of Stacks 08DI an endomorphism `γ` of `K` is matched with a
morphism `𝒪_X[0] ⟶ R𝓗om(K, K)`; the homothety being invertible, that morphism is `c` followed by
the homothety for an endomorphism `c` of `𝒪_X[0]`, so `γ = λ_K⁻¹ ∘ (c ⊗ K) ∘ λ_K`. The
endomorphisms of `𝒪_X[0]` are those of `𝒪_X`, which are multiplications by global sections, and
the derived tensor product is linear in its first variable: on the K-flat complex `𝒪_X[0]` it is
the total tensor complex, where tensoring multiplication by `a` with the identity is
multiplication by `a`.

## Main results

* `AlgebraicGeometry.Scheme.unit_hom_eq_smul_id`: an endomorphism of `𝒪_X` is multiplication by
  its value on `1`.
* `AlgebraicGeometry.Scheme.canonicalDerivedTensor_map_smul_unit_app`: the derived tensor product
  is linear in its first variable at the structure sheaf.
* `AlgebraicGeometry.Scheme.derived_tensorUnit_hom_eq_smul_id`: an endomorphism of `𝒪_X[0]` in
  `D(𝒪_X)` is a scalar.
* `AlgebraicGeometry.Scheme.exists_eq_smul_id_of_isIso_derivedSheafHomothety`: if the homothety
  of `K` is invertible, every endomorphism of `K` is a scalar; the variants `_modules` and
  `_oxMod` state it for the spellings `X.Modules` and `OXMod X.toRingedSpace` of `𝒪_X`-modules.

## Implementation notes

The scalars act through `AlgebraicGeometry.Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id _)`, named
once for each spelling of the category of `𝒪_X`-modules (`linearStructureSheafModules`,
`linearRingedSiteModules`, `linearModules`, and `AlgebraicGeometry.Scheme.linearOXMod`), and
through Mathlib's induced linear structures on complexes and on `D(𝒪_X)`. The spellings are
definitionally equal but their instances are not syntactically so, which is why the auxiliary
lemmas in the `CategoryTheory` namespace take the instances of a category as implicit arguments.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

universe u

namespace CategoryTheory

/-- In a linear category, an endomorphism `f` with `f ≫ c = c ≫ (r · 1)` for an isomorphism `c`
is `r · 1`. The instances are implicit arguments so that the statement can be matched against
an equation whose instances are not the ones synthesis produces. -/
theorem eq_smul_id_of_comp_eq_comp_smul_id {R : Type*} [Ring R] {C : Type*} {_ : Category C}
    {_ : Preadditive C} {_ : Linear R C} {A B : C} {f : A ⟶ A} {c : A ⟶ B} (hc : IsIso c)
    {r : R} (h : f ≫ c = c ≫ (r • 𝟙 B)) : f = r • 𝟙 A := by
  rw [← cancel_mono c, h, Linear.comp_smul, Linear.smul_comp, Category.id_comp, Category.comp_id]

/-- A linear functor carries `r · 1` to `r · 1`, with the instances of the two categories
implicit. -/
theorem Functor.map_smul_id' {R : Type*} [Ring R] {C D : Type*} {_ : Category C} {_ : Category D}
    {_ : Preadditive C} {_ : Preadditive D} {_ : CategoryTheory.Linear R C}
    {_ : CategoryTheory.Linear R D} {F : C ⥤ D} [F.Additive] [F.Linear R] (r : R) (A : C) :
    F.map (r • 𝟙 A) = r • 𝟙 (F.obj A) := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- A natural endomorphism which is `r · 1` at an object is `r · 1` at every isomorphic object,
the instances of the target category being implicit. -/
theorem NatTrans.app_eq_smul_id_of_iso {R : Type*} [Ring R] {C D : Type*} [Category C]
    {_ : Category D} {_ : Preadditive D} {_ : CategoryTheory.Linear R D} {F : C ⥤ D}
    (τ : F ⟶ F) {x y : C} (e : x ≅ y) {r : R} (h : τ.app x = r • 𝟙 (F.obj x)) :
    τ.app y = r • 𝟙 (F.obj y) := by
  have hn := τ.naturality e.hom
  rw [h, Linear.smul_comp, Category.id_comp] at hn
  rw [← cancel_epi (F.map e.hom), hn, Linear.comp_smul, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- The `Γ(X, ⊤)`-linear structure on sheaves of `𝒪_X`-modules, in the spelling
`StructureSheafModules X.sheaf` of the derived internal hom and of the homothety. -/
@[instance_reducible]
def linearStructureSheafModules :
    Linear Γ(X, ⊤) (Stacks.SheafOfModules.StructureSheafModules X.sheaf) :=
  linearOfRingHom X Γ(X, ⊤) (RingHom.id _)

/-- The `Γ(X, ⊤)`-linear structure on sheaves of `𝒪_X`-modules, in the spelling of the ringed
site of the opens of `X` that the derived tensor product of Stacks 06YU is stated for. -/
@[instance_reducible]
def linearRingedSiteModules :
    Linear Γ(X, ⊤) (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O)) :=
  linearOfRingHom X Γ(X, ⊤) (RingHom.id _)

/-- **An endomorphism of the structure sheaf is multiplication by a global section**, namely by
its value on the section `1`. -/
theorem unit_hom_eq_smul_id (φ : SheafOfModules.unit X.ringCatSheaf ⟶
    SheafOfModules.unit X.ringCatSheaf) :
    letI := linearOfRingHom.{u, u} X Γ(X, ⊤) (RingHom.id _)
    ∃ a : Γ(X, ⊤), φ = a • 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  let := linearOfRingHom.{u, u} X Γ(X, ⊤) (RingHom.id _)
  refine ⟨(φ.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤)), ?_⟩
  refine (SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext fun U => ?_))
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  change _ = X.ringCatSheaf.obj.map (isTerminalTop.from U.unop).op
    ((φ.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))) • (1 : X.ringCatSheaf.obj.obj U)
  have hn := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (φ.val.naturality (isTerminalTop.from U.unop).op)) (1 : X.ringCatSheaf.obj.obj (op ⊤))
  have h1 : ((SheafOfModules.unit X.ringCatSheaf).val.map (isTerminalTop.from U.unop).op).hom
      (1 : X.ringCatSheaf.obj.obj (op ⊤)) = (1 : X.ringCatSheaf.obj.obj U) :=
    PresheafOfModules.unit_map_one _ _
  rw [smul_eq_mul, mul_one]
  exact (congrArg (φ.val.app U).hom h1).symm.trans hn

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

section RingedSite

attribute [local instance] linearRingedSiteModules

open Stacks.SheafOfModules in
/-- **Tensoring commutes with multiplication by a global section**, in the first variable:
`(a · 1_M) ⊗ N = a · 1_{M ⊗ N}`. -/
theorem sheafTensor_map_smul_id_app (a : Γ(X, ⊤))
    (M N : SheafOfModules.{u} (Tensor.ringSheaf (ringedSite X.sheaf).O)) :
    ((Tensor.sheafTensor (ringedSite X.sheaf).O).map (a • 𝟙 M)).app N =
      a • 𝟙 (((Tensor.sheafTensor (ringedSite X.sheaf).O).obj M).obj N) := by
  change ((Tensor.sheafTensor (ringedSite X.sheaf).O).map
      ((Stacks.SheafOfModules.globalSectionToEnd X.ringCatSheaf
        (Stacks.SheafOfModules.terminalSection X.ringCatSheaf ⊤ isTerminalTop a)).asHom.app
          M)).app N =
    (Stacks.SheafOfModules.globalSectionToEnd X.ringCatSheaf
        (Stacks.SheafOfModules.terminalSection X.ringCatSheaf ⊤ isTerminalTop a)).asHom.app _
  exact AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd
    (ringedSite X.sheaf).O N
    (Stacks.SheafOfModules.terminalSection X.ringCatSheaf ⊤ isTerminalTop a) M

open Stacks.SheafOfModules in
/-- **The total tensor complex is linear in its first variable**: tensoring multiplication by
`a` on a complex with the identity of another is multiplication by `a`. -/
theorem mapBifunctorMap_smul_id (a : Γ(X, ⊤))
    (K L : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf (ringedSite X.sheaf).O)) ℤ)
    {_ : (Tensor.sheafTensor (ringedSite X.sheaf).O).PreservesZeroMorphisms}
    {_ : ∀ M, ((Tensor.sheafTensor (ringedSite X.sheaf).O).obj M).PreservesZeroMorphisms}
    {_ : HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor (ringedSite X.sheaf).O)
      (ComplexShape.up ℤ)} :
    HomologicalComplex.mapBifunctorMap (a • 𝟙 K) (𝟙 L) (Tensor.sheafTensor (ringedSite X.sheaf).O)
      (ComplexShape.up ℤ) = a • 𝟙 (HomologicalComplex.mapBifunctor K L
        (Tensor.sheafTensor (ringedSite X.sheaf).O) (ComplexShape.up ℤ)) := by
  ext n : 1
  refine HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.smul_f_apply,
    HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, HomologicalComplex.id_f,
    HomologicalComplex.id_f, sheafTensor_map_smul_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id, Linear.smul_comp, Linear.comp_smul]

open Stacks.SheafOfModules in
/-- **The derived tensor product is linear in its first variable at the structure sheaf**:
`(a · 1_{𝒪_X[0]}) ⊗^L L = a · 1`. On the K-flat complex `𝒪_X[0]` the derived tensor product
is the total tensor complex, naturally in both variables, and there tensoring multiplication by
`a` with the identity is multiplication by `a` (`mapBifunctorMap_smul_id`). -/
theorem canonicalDerivedTensor_map_smul_unit_app (a : Γ(X, ⊤))
    (L : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf (ringedSite X.sheaf).O))) :
    ((canonicalDerivedTensorProduct (ringedSite X.sheaf)).tensor.map
        (a • 𝟙 (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf))))).app
      L = a • 𝟙 _ := by
  let T := canonicalDerivedTensorProduct (ringedSite X.sheaf)
  let S0 := RingedSite.structureSheafComplex (ringedSite X.sheaf)
  have hS : IsKFlat (ringedSite X.sheaf).O S0 := isKFlat_single_unit (ringedSite X.sheaf).O
  let L0 : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf (ringedSite X.sheaf).O)) ℤ :=
    DerivedCategory.Q.objPreimage L
  have key : (T.tensor.map (a • 𝟙 (DerivedCategory.Q.obj S0))).app (DerivedCategory.Q.obj L0) =
      a • 𝟙 _ := by
    have h3 : _ = (T.comparisonLeft S0 L0 hS).hom ≫ (a • 𝟙 _) :=
      ((T.comparisonLeft_naturality (a • 𝟙 S0) (𝟙 L0) hS hS).trans
        (congrArg (fun g => (T.comparisonLeft S0 L0 hS).hom ≫ DerivedCategory.Q.map g)
          (mapBifunctorMap_smul_id X a S0 L0))).trans
        (congrArg (fun g => (T.comparisonLeft S0 L0 hS).hom ≫ g)
          (Functor.map_smul_id' (F := DerivedCategory.Q) a _))
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Category.id_comp] at h3
    exact eq_smul_id_of_comp_eq_comp_smul_id inferInstance h3
  exact NatTrans.app_eq_smul_id_of_iso _ (DerivedCategory.Q.objObjPreimageIso L) key

end RingedSite

section StructureSheafModules

attribute [local instance] linearStructureSheafModules

open Stacks.SheafOfModules in
/-- **An endomorphism of `𝒪_X[0]` in `D(𝒪_X)` is multiplication by a global section**: the
single functor is fully faithful and linear, and an endomorphism of `𝒪_X` is a scalar
(`unit_hom_eq_smul_id`). -/
theorem derived_tensorUnit_hom_eq_smul_id
    (c : letI := derivedMonoidalStructure X.sheaf
      𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)) ⟶
        𝟙_ (DerivedCategory (StructureSheafModules X.sheaf))) :
    ∃ a : Γ(X, ⊤), c = a • 𝟙 _ := by
  obtain ⟨φ, hφ⟩ := (DerivedCategory.singleFunctor (StructureSheafModules X.sheaf) 0).map_surjective
    (show (DerivedCategory.singleFunctor (StructureSheafModules X.sheaf) 0).obj
        (SheafOfModules.unit (structureSheaf X.sheaf)) ⟶
      (DerivedCategory.singleFunctor (StructureSheafModules X.sheaf) 0).obj
        (SheafOfModules.unit (structureSheaf X.sheaf)) from c)
  obtain ⟨a, ha⟩ := unit_hom_eq_smul_id X φ
  refine ⟨a, hφ.symm.trans ?_⟩
  rw [ha]
  exact Functor.map_smul_id' a _

open Stacks.SheafOfModules in
/-- **An invertible homothety makes every endomorphism a scalar.** Let `K` be an object of
`D(𝒪_X)` whose homothety `𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)` is an isomorphism. Then every endomorphism
of `K` is multiplication by a global section of `𝒪_X`.

The endomorphism `γ` is matched by the bijection of Stacks 08DI with `c ≫ h` for the homothety
`h` and an endomorphism `c` of `𝒪_X[0]`, so `γ = λ_K⁻¹ ∘ (c ⊗ K) ∘ λ_K`; `c` is a scalar
(`derived_tensorUnit_hom_eq_smul_id`), and the derived tensor product is linear in its first
variable (`canonicalDerivedTensor_map_smul_unit_app`). The scalars act through
`linearStructureSheafModules X`. -/
theorem exists_eq_smul_id_of_isIso_derivedSheafHomothety
    (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : IsIso (derivedSheafHomothety X.sheaf K)) (γ : K ⟶ K) :
    ∃ a : Γ(X, ⊤), γ = a • 𝟙 K := by
  let := derivedMonoidalStructure X.sheaf
  obtain ⟨t, ht⟩ := (tensorHomBijective_derivedSheafHomCounit X.sheaf K K
    (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)))).2 ((λ_ K).hom ≫ γ)
  obtain ⟨a, ha⟩ := derived_tensorUnit_hom_eq_smul_id X (t ≫ inv (derivedSheafHomothety X.sheaf K))
  have ht' : t = (a • 𝟙 _) ≫ derivedSheafHomothety X.sheaf K := by
    rw [← ha, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨a, (cancel_epi (λ_ K).hom).1 ?_⟩
  dsimp only at ht
  have hw : (a • 𝟙 (𝟙_ (DerivedCategory (StructureSheafModules X.sheaf)))) ▷ K = a • 𝟙 _ :=
    canonicalDerivedTensor_map_smul_unit_app X a K
  rw [← ht, ht', comp_whiskerRight, Category.assoc, whiskerRight_derivedSheafHomothety_comp,
    hw, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

end StructureSheafModules

/-- The `Γ(X, ⊤)`-linear structure on `X.Modules`. -/
@[instance_reducible]
def linearModules : Linear Γ(X, ⊤) X.Modules :=
  linearOfRingHom X Γ(X, ⊤) (RingHom.id _)

/-- **An invertible homothety makes every endomorphism a scalar**, for an object of `D(𝒪_X)`
spelled through `X.Modules`, the scalars acting through `linearModules X`. -/
theorem exists_eq_smul_id_of_isIso_derivedSheafHomothety_modules (K : DerivedCategory X.Modules)
    (hK : IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf K)) (γ : K ⟶ K) :
    letI := linearModules X
    ∃ a : Γ(X, ⊤), γ = a • 𝟙 K :=
  let := linearStructureSheafModules X
  exists_eq_smul_id_of_isIso_derivedSheafHomothety X K hK γ

/-- **An invertible homothety makes every endomorphism a scalar**, for an object of `D(𝒪_X)`
spelled through `OXMod X.toRingedSpace`, the spelling of a relative dualizing complex, the
scalars acting through `linearOXMod X`. -/
theorem exists_eq_smul_id_of_isIso_derivedSheafHomothety_oxMod
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hK : IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf K)) (γ : K ⟶ K) :
    letI := linearOXMod X
    ∃ a : Γ(X, ⊤), γ = a • 𝟙 K :=
  let := linearStructureSheafModules X
  exists_eq_smul_id_of_isIso_derivedSheafHomothety X K hK γ

end AlgebraicGeometry.Scheme

end
