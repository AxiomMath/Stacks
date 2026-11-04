module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceDerivedLimit
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnconditionalBoundedness
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitTriangulatedTower
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitObjectIso
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel

/-!
# The object `K` of Grothendieck's existence theorem, and its boundedness

In Situation [Stacks, Tag 0CTC] the sheaves `Fₙ` on the closed subschemes `Xₙ ⊆ X` give an
inverse system `(iₙ,* Fₙ)` of quasi-coherent `𝒪_X`-modules
(`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.pushforwardSystem`).
[Stacks, Tag 0CTD] considers

`K = R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)`

and asserts that `K` lies in `D^b_QCoh(𝒪_X)` with nonzero cohomology sheaves only in degrees
`≥ 0`. This file proves that with nothing assumed beyond the situation, at any model of the
derived category of `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.derivedPushforwardSystemOfModel` —
  the system `(iₙ,* Fₙ)` in `D(𝒪_X)`, at any model, and
  `...quasiCoherentPushforwardSystem` — the same system read in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh` — a derived limit
  `L` of the system in `D(𝒪_X)` together with `K = DQ_X(L)`, recorded by its universal property:
  a map `ε : K ⟶ L` from an object with quasi-coherent cohomology sheaves, universal among such.
  This is the object `K` of [Stacks, Tag 0CTD] and of the later tags of the section.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.isLeftAdjoint_quasiCoherentι_ofModel` — the coherator
  of [Stacks, Tag 0CR0] at any model of `D(𝒪_X)`.
* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.nonempty_derivedLimitQCoh` — the
  data exist.
* `...DerivedLimitQCoh.isDerivedLimit_K` — `K` is a derived limit of the system in
  `D_QCoh(𝒪_X)`, the displayed equality.
* `...DerivedLimitQCoh.isGE_zero_and_exists_isLE` — `K` has cohomology sheaves only in degrees
  `≥ 0`, and only in finitely many degrees.
* `...nonempty_derivedLimitQCoh_and_isDerivedLimit_isGE_isLE` — [Stacks, Tag 0CTD].

## The proof

The source cites Example [Stacks, Tag 0CSB]. Every input is available without hypotheses:

* the coherator exists and is exact for every quasi-compact quasi-separated scheme
  ([Stacks, Tag 0CR0], `Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`), and the scheme
  of the situation is quasi-compact and quasi-separated, being of finite presentation over an
  affine scheme;
* `D(𝒪_X)` has countable products
  (`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`,
  [Stacks, Tag 0BK6]), so the derived limit exists ([Stacks, Tag 08TC]);
* the terms `iₙ,* Fₙ` are quasi-coherent, so they have affine hypercohomology in `[0, 0]`
  (`...ExistenceSituation.affineAmplitudeIn_derivedSystem_obj`),
  and the Milnor sequence of [Stacks, Tag 0D60] puts the hypercohomology of the derived limit over
  affine opens in `[0, 1]`
  (`AlgebraicGeometry.GrothendieckExistence.affineAmplitudeIn_of_isDerivedLimit`);
* the bounded cohomological dimension of the coherator, [Stacks, Tag 0CSA], is unconditional
  (`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs`).

## Implementation notes

The coherator and [Stacks, Tag 0CSA] are proved at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. The statements here are at a free
`HasDerivedCategory` binder: the boundedness is carried over from the locally small model along
the comparison equivalence `StacksDraft.DerivedModel.modelEquiv`, which is triangulated
(`StacksDraft.Perfect.derivedEquivalence_isTriangulated`), commutes with cohomology and identifies
the single-object functors. Under it, a derived limit goes to a derived limit, and a universal map
from `D_QCoh` to a universal map from `D_QCoh`.

`K` is recorded by its universal property rather than as `DQ_X(L)` for a chosen coherator, so
that it does not depend on a model or on a choice of right adjoint. This file discharges the
conditional statements of Tag 0CTD in
`StacksFrontier/AlgebraicGeometry/Flatness/BlowingUp/GrothendieckExistenceDerivedLimit.lean`.

## References

* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
* [Stacks Project, Tag 0CTC](https://stacks.math.columbia.edu/tag/0CTC)
* [Stacks Project, Tag 0CSB](https://stacks.math.columbia.edu/tag/0CSB)
* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Opposite
open Stacks.Duality Stacks.Duality.Coherator

universe w u

namespace AlgebraicGeometry.GrothendieckExistence

/-! ### Coreflections -/

section Coreflection

variable {D D₁ D₂ : Type*} [Category D] [Category D₁] [Category D₂]

/-- The counit of a coreflection onto a full subcategory is universal: for every object `M` of the
subcategory, composing with the counit at `L` is a bijection `Hom(M, R L) ≃ Hom(M, L)`. -/
theorem bijective_comp_counit (P : ObjectProperty D) {R : D ⥤ P.FullSubcategory}
    (adj : P.ι ⊣ R) (L : D) (M : D) (hM : P M) :
    Function.Bijective fun g : M ⟶ P.ι.obj (R.obj L) => g ≫ adj.counit.app L := by
  have key : (fun g : M ⟶ P.ι.obj (R.obj L) => g ≫ adj.counit.app L) =
      (adj.homEquiv ⟨M, hM⟩ L).symm ∘ (P.fullyFaithfulι.homEquiv (X := ⟨M, hM⟩)).symm := by
    funext g
    simp only [Function.comp_apply, Adjunction.homEquiv_counit]
    exact congrArg (· ≫ adj.counit.app L) (P.fullyFaithfulι.map_preimage (X := ⟨M, hM⟩) g).symm
  rw [key]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

/-- Universality of a map `ε : K ⟶ L` transports along an equivalence. -/
theorem bijective_comp_functor_map (e : D₁ ≌ D₂) {K L : D₁} (ε : K ⟶ L) (M : D₂)
    (h : Function.Bijective fun g : e.inverse.obj M ⟶ K => g ≫ ε) :
    Function.Bijective fun g : M ⟶ e.functor.obj K => g ≫ e.functor.map ε := by
  have key : (fun g : M ⟶ e.functor.obj K => g ≫ e.functor.map ε) =
      (e.symm.toAdjunction.homEquiv M L) ∘ (fun g => g ≫ ε) ∘
        (e.symm.toAdjunction.homEquiv M K).symm := by
    funext g
    simp only [Function.comp_apply]
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    rfl
  rw [key]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

/-- Universality of a map is unchanged by precomposing with an isomorphism. -/
theorem bijective_comp_iso_hom_comp {K' K L : D} (i : K' ≅ K) (ε : K ⟶ L) (M : D)
    (h : Function.Bijective fun g : M ⟶ K => g ≫ ε) :
    Function.Bijective fun g : M ⟶ K' => g ≫ i.hom ≫ ε := by
  have key : (fun g : M ⟶ K' => g ≫ i.hom ≫ ε) =
      (fun g : M ⟶ K => g ≫ ε) ∘ (Iso.refl M).homCongr i := by
    funext g
    simp
  rw [key]
  exact h.comp (Equiv.bijective _)

/-- Two universal maps into the same object from objects of the same class have isomorphic
sources. -/
def isoOfBijectiveComp (P : ObjectProperty D) {K₁ K₂ L : D} (ε₁ : K₁ ⟶ L) (ε₂ : K₂ ⟶ L)
    (hK₁ : P K₁) (hK₂ : P K₂)
    (h₁ : ∀ M, P M → Function.Bijective fun g : M ⟶ K₁ => g ≫ ε₁)
    (h₂ : ∀ M, P M → Function.Bijective fun g : M ⟶ K₂ => g ≫ ε₂) : K₁ ≅ K₂ where
  hom := ((h₂ K₁ hK₁).2 ε₁).choose
  inv := ((h₁ K₂ hK₂).2 ε₂).choose
  hom_inv_id := (h₁ K₁ hK₁).1 (by
    simp only [Category.assoc, ((h₁ K₂ hK₂).2 ε₂).choose_spec, ((h₂ K₁ hK₁).2 ε₁).choose_spec,
      Category.id_comp])
  inv_hom_id := (h₂ K₂ hK₂).1 (by
    simp only [Category.assoc, ((h₂ K₁ hK₁).2 ε₁).choose_spec, ((h₁ K₂ hK₂).2 ε₂).choose_spec,
      Category.id_comp])

end Coreflection

/-! ### The bound at the locally small model -/

/-- `AffineAmplitudeIn` is invariant under isomorphism. -/
theorem affineAmplitudeIn_of_iso {X : Scheme.{u}} {a b : ℤ} {K K' : DerivedCategory X.Modules}
    (e : K ≅ K') (hK : AffineAmplitudeIn X a b K) : AffineAmplitudeIn X a b K' :=
  fun U i hi => (hK U i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) i).mapIso
      ((derivedSectionsLocallySmall X U.1).mapIso e)).symm

/-- **The bound of [Stacks, Tag 0CTD] for any coherator, at the locally small model.** Let `X` be
a quasi-compact quasi-separated scheme, let `DQ_X` be any exact right adjoint of the inclusion
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)` and let `K` be a derived limit in `D(𝒪_X)` of an inverse system each of
whose terms has affine hypercohomology concentrated in degree `0`. Then the cohomology sheaves of
`DQ_X(K)` vanish in negative degrees and above some degree. -/
theorem isGE_zero_isLE_coherator_obj_of_isDerivedLimit (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
    (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]
    (L : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ => L.obj ⟨n⟩]
    (hL : ∀ n : ℕ, AffineAmplitudeIn X 0 0 (L.obj ⟨n⟩))
    (K : DerivedCategory X.Modules) (hK : IsDerivedLimit L K) :
    ∃ c : ℤ, ((quasiCoherentι X).obj (DQ.obj K)).IsGE 0 ∧
      ((quasiCoherentι X).obj (DQ.obj K)).IsLE c := by
  obtain ⟨N, hN⟩ := exists_isGE_isLE_coherator_obj_of_qcqs X DQ adj
  exact ⟨0 + 1 + N, hN 0 (0 + 1) K (affineAmplitudeIn_of_isDerivedLimit X L K hK 0 0 hL)⟩

/-! ### The coherator at any model of `D(𝒪_X)` -/

section AnyModelCoherator

variable (X : Scheme.{u}) [h : HasDerivedCategory.{w} X.Modules]

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`, at any model of the derived
category: quasi-coherent modules form a weak Serre subcategory. -/
instance derivedQuasicoherent_isTriangulated_ofModel :
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)

/-- **[Stacks, Tag 0CR0] at any model of `D(𝒪_X)`.** For a quasi-compact quasi-separated scheme
`X`, the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint, whatever model of the derived
category is chosen: it is conjugate, by the comparison equivalences, to the inclusion at the
locally small model, which has one by `Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`. -/
theorem isLeftAdjoint_quasiCoherentι_ofModel [CompactSpace X] [QuasiSeparatedSpace X] :
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.IsLeftAdjoint := by
  let E₁ := StacksDraft.DerivedModel.derivedCategoryBModelEquiv
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) h (Scheme.Modules.hasDerivedCategory X)
  let E₂ := StacksDraft.DerivedModel.modelEquiv h (Scheme.Modules.hasDerivedCategory X)
  exact @Stacks.Duality.StandardModel.isLeftAdjoint_of_comp_iso _ _ _ _ _ _ _ _ _
    (Stacks.Duality.Coherator.quasiCoherentι X) E₁.functor E₂.functor E₁.isEquivalence_functor
    E₂.isEquivalence_functor (Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι X) (Iso.refl _)

end AnyModelCoherator

namespace ExistenceSituation

variable (S : ExistenceSituation.{u})

/-! ### The standing instances -/

/-- The scheme of Situation [Stacks, Tag 0CTC] is quasi-compact. -/
instance compactSpace_X : CompactSpace S.X.left := S.compactSpace

/-- The scheme of Situation [Stacks, Tag 0CTC] is quasi-separated. -/
instance quasiSeparatedSpace_X : QuasiSeparatedSpace S.X.left := S.quasiSeparatedSpace

/-! ### The objects of the tag, at any model of `D(𝒪_X)` -/

/-- **The inverse system `(iₙ,* Fₙ)` read in `D(𝒪_X)`, at any model of the derived category**,
each term placed in degree zero. At the locally small model it is
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.derivedPushforwardSystem`, which is
elaborated at that model only; this one takes the model as a parameter. -/
def derivedPushforwardSystemOfModel [HasDerivedCategory.{w} S.X.left.Modules] :
    ℕᵒᵖ ⥤ DerivedCategory S.X.left.Modules :=
  S.pushforwardSystem ⋙ DerivedCategory.singleFunctor S.X.left.Modules 0

section AnyModel

variable [HasDerivedCategory.{w} S.X.left.Modules]

/-- The system `(iₙ,* Fₙ)` has a countable product in `D(𝒪_X)`: the derived category of sheaves
of modules has countable products, computed by K-injective resolutions ([Stacks, Tag 0BK6]). -/
instance hasProduct_derivedPushforwardSystemOfModel :
    HasProduct fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩ :=
  have := Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules
    S.X.left.ringCatSheaf
  inferInstance

/-- **The data of [Stacks, Tag 0CTD].** A derived limit `L = R lim_{D(𝒪_X)} Fₙ` of the system
`(iₙ,* Fₙ)` in `D(𝒪_X)`, together with an object `K` of `D(𝒪_X)` with quasi-coherent cohomology
sheaves and a map `ε : K ⟶ L` which is universal among maps into `L` from objects with
quasi-coherent cohomology sheaves. This universal property says exactly that `K = DQ_X(L)`, with
`DQ_X` the coherator of [Stacks, Tag 0CR0] and `ε` its counit; it characterizes `K` up to unique
isomorphism over `L`, and it does not depend on the model of the derived category. -/
structure DerivedLimitQCoh where
  /-- The derived limit `R lim_{D(𝒪_X)} Fₙ`. -/
  L : DerivedCategory S.X.left.Modules
  /-- `L` is a derived limit of the system `(iₙ,* Fₙ)`. -/
  isDerivedLimit : IsDerivedLimit S.derivedPushforwardSystemOfModel L
  /-- The object `K = DQ_X(L)`. -/
  K : DerivedCategory S.X.left.Modules
  /-- The cohomology sheaves of `K` are quasi-coherent. -/
  quasicoherent (i : ℤ) :
    ((DerivedCategory.homologyFunctor S.X.left.Modules i).obj K).IsQuasicoherent
  /-- The map `K ⟶ L`, the counit of the coherator. -/
  ε : K ⟶ L
  /-- `ε` is universal among maps into `L` from objects with quasi-coherent cohomology. -/
  universal (M : DerivedCategory S.X.left.Modules)
    (hM : ∀ i : ℤ, ((DerivedCategory.homologyFunctor S.X.left.Modules i).obj M).IsQuasicoherent) :
    Function.Bijective fun g : M ⟶ K => g ≫ ε

end AnyModel

/-! ### Transport from the locally small model -/

/-- **The bound of [Stacks, Tag 0CTD] at the locally small model, for a coreflection.** In
Situation [Stacks, Tag 0CTC], let `L` be a derived limit in `D(𝒪_X)` of an inverse system each of
whose terms has affine hypercohomology concentrated in degree `0`, and let `ε : K ⟶ L` be
universal among maps into `L` from objects with quasi-coherent cohomology sheaves, `K` itself
having quasi-coherent cohomology sheaves. Then the cohomology sheaves of `K` vanish in negative
degrees and above some degree. -/
theorem isGE_zero_and_exists_isLE_of_bijective_comp
    (Lsys : ℕᵒᵖ ⥤ DerivedCategory S.X.left.Modules) [HasProduct fun n : ℕ => Lsys.obj ⟨n⟩]
    (hamp : ∀ n : ℕ, AffineAmplitudeIn S.X.left 0 0 (Lsys.obj ⟨n⟩))
    (L : DerivedCategory S.X.left.Modules) (hL : IsDerivedLimit Lsys L)
    (K : DerivedCategory S.X.left.Modules) (hK : quasiCoherentProp S.X.left K) (ε : K ⟶ L)
    (hε : ∀ M, quasiCoherentProp S.X.left M → Function.Bijective fun g : M ⟶ K => g ≫ ε) :
    K.IsGE 0 ∧ ∃ c : ℤ, K.IsLE c := by
  have := isLeftAdjoint_quasiCoherentι S.X.left
  let adj := Adjunction.ofIsLeftAdjoint (quasiCoherentι S.X.left)
  let : (quasiCoherentι S.X.left).rightAdjoint.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  obtain ⟨c, hge, hle⟩ := isGE_zero_isLE_coherator_obj_of_isDerivedLimit S.X.left _ adj Lsys hamp
    L hL
  let iso := isoOfBijectiveComp (quasiCoherentProp S.X.left) ε (adj.counit.app L) hK
    ((quasiCoherentι S.X.left).rightAdjoint.obj L).2 hε
    (fun M hM => bijective_comp_counit _ adj _ M hM)
  have : DerivedCategory.TStructure.t.IsGE
      (((quasiCoherentι S.X.left).rightAdjoint ⋙ quasiCoherentι S.X.left).obj L) 0 := hge
  have : DerivedCategory.TStructure.t.IsLE
      (((quasiCoherentι S.X.left).rightAdjoint ⋙ quasiCoherentι S.X.left).obj L) c := hle
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso iso.symm 0,
    c, DerivedCategory.TStructure.t.isLE_of_iso iso.symm c⟩

section Transport

open AlgebraicGeometry.Scheme.Modules (hasDerivedCategory)

variable [h : HasDerivedCategory.{w} S.X.left.Modules]

/-- Quasi-coherence of all the cohomology sheaves transports along the comparison equivalence
with the locally small model. -/
theorem quasiCoherentProp_modelEquiv_functor_obj (M : DerivedCategory S.X.left.Modules)
    (hM : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj M).IsQuasicoherent) :
    quasiCoherentProp S.X.left
      ((StacksDraft.DerivedModel.modelEquiv h (hasDerivedCategory S.X.left)).functor.obj M) :=
  (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
    (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf) h
    (hasDerivedCategory S.X.left) M).2 hM

/-- An object of the locally small model with quasi-coherent cohomology sheaves pulls back along
the comparison equivalence to an object with quasi-coherent cohomology sheaves. -/
theorem isQuasicoherent_homology_modelEquiv_inverse_obj
    (M : @DerivedCategory S.X.left.Modules _ _ (hasDerivedCategory S.X.left))
    (hM : quasiCoherentProp S.X.left M) (i : ℤ) :
    ((DerivedCategory.homologyFunctor _ i).obj
      ((StacksDraft.DerivedModel.modelEquiv h
        (hasDerivedCategory S.X.left)).inverse.obj M)).IsQuasicoherent :=
  (StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
    (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf) h
    (hasDerivedCategory S.X.left) _).1
    (fun i => (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf).prop_of_iso
      ((@DerivedCategory.homologyFunctor S.X.left.Modules _ _
        (hasDerivedCategory S.X.left) i).mapIso
        ((StacksDraft.DerivedModel.modelEquiv h
          (hasDerivedCategory S.X.left)).counitIso.app M)).symm (hM i)) i

/-- The bound of [Stacks, Tag 0CTD], at an arbitrary model of `D(𝒪_X)`: transport to the locally
small model and apply
`...ExistenceSituation.isGE_zero_and_exists_isLE_of_bijective_comp`. -/
theorem DerivedLimitQCoh.isGE_zero_and_exists_isLE (d : S.DerivedLimitQCoh) :
    d.K.IsGE 0 ∧ ∃ c : ℤ, d.K.IsLE c := by
  let e := StacksDraft.DerivedModel.modelEquiv h (hasDerivedCategory S.X.left)
  have hsh : ∀ n : ℤ, (shiftFunctor (@DerivedCategory S.X.left.Modules _ _ h) n).Additive :=
    fun n => inferInstance
  have hsh' : ∀ n : ℤ,
      (shiftFunctor (@DerivedCategory S.X.left.Modules _ _ (hasDerivedCategory S.X.left))
        n).Additive := by
    let := Scheme.Modules.hasDerivedCategory S.X.left
    exact fun n => inferInstance
  let : e.functor.CommShift ℤ :=
    StacksDraft.Perfect.derivedEquivalenceCommShift h (hasDerivedCategory S.X.left)
  have : e.functor.IsTriangulated :=
    StacksDraft.Perfect.derivedEquivalence_isTriangulated h (hasDerivedCategory S.X.left)
  have : e.functor.IsRightAdjoint := e.symm.toAdjunction.isRightAdjoint
  obtain ⟨hp, hL⟩ := @Stacks.Injectives.isDerivedLimit_map_rightAdjoint _ _ _ _ _ _ _ _ _ _ hsh
    hsh' _ _ e.functor _ _ _ S.derivedPushforwardSystemOfModel _ d.L d.isDerivedLimit
  have hamp : ∀ n : ℕ, AffineAmplitudeIn S.X.left 0 0
      ((S.derivedPushforwardSystemOfModel ⋙ e.functor).obj ⟨n⟩) := fun n =>
    affineAmplitudeIn_of_iso
      ((StacksDraft.DerivedModel.modelSingleFunctorIso h
          (hasDerivedCategory S.X.left) 0).app
        (S.pushforwardSystem.obj ⟨n⟩)).symm
      (S.affineAmplitudeIn_derivedSystem_obj n)
  obtain ⟨hge, c, hle⟩ := @isGE_zero_and_exists_isLE_of_bijective_comp S _ hp hamp _ hL
    (e.functor.obj d.K) (S.quasiCoherentProp_modelEquiv_functor_obj d.K d.quasicoherent)
    (e.functor.map d.ε)
    (fun M hM => bijective_comp_functor_map e d.ε M
      (d.universal _ (S.isQuasicoherent_homology_modelEquiv_inverse_obj M hM)))
  exact ⟨(StacksDraft.DerivedModel.isGE_modelEquiv_iff h (hasDerivedCategory S.X.left) d.K 0).1 hge,
    c, (StacksDraft.DerivedModel.isLE_modelEquiv_iff h (hasDerivedCategory S.X.left) d.K c).1 hle⟩

/-- The system `(iₙ,* Fₙ)` read in `D_QCoh(𝒪_X)`, at any model of the derived category: its terms
are quasi-coherent modules placed in degree zero. -/
def quasiCoherentPushforwardSystem :
    ℕᵒᵖ ⥤ (DerivedCategoryB.derivedCategoryB (A := S.X.left.Modules)
      (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf)).FullSubcategory :=
  ObjectProperty.lift _ S.derivedPushforwardSystemOfModel fun n =>
    Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj _
      (S.isQuasicoherent_pushforwardSystem_obj n.unop)

/-- **[Stacks, Tag 0CR0] for the scheme of the situation, with the derived limit.** At any model
of `D(𝒪_X)` the data of
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh` exist: a derived
limit `L` of the system `(iₙ,* Fₙ)` exists because `D(𝒪_X)` has countable products, and
`K = DQ_X(L)` with the counit of the coherator is the required universal map. -/
theorem nonempty_derivedLimitQCoh : Nonempty S.DerivedLimitQCoh := by
  have := isLeftAdjoint_quasiCoherentι_ofModel S.X.left
  let P := DerivedCategoryB.derivedCategoryB (A := S.X.left.Modules)
    (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf)
  let adj := Adjunction.ofIsLeftAdjoint P.ι
  obtain ⟨L, hL⟩ := exists_isDerivedLimit S.derivedPushforwardSystemOfModel
  exact ⟨⟨L, hL, P.ι.obj (P.ι.rightAdjoint.obj L), (P.ι.rightAdjoint.obj L).2,
    adj.counit.app L, fun M hM => bijective_comp_counit P adj L M hM⟩⟩

/-- **The displayed equality of [Stacks, Tag 0CTD], at any model.** For the data `d`, the object
`K = DQ_X(R lim_{D(𝒪_X)} Fₙ)`, viewed in `D_QCoh(𝒪_X)`, is a derived limit
`R lim_{D_QCoh(𝒪_X)}(Fₙ)` of the system `(iₙ,* Fₙ)` read in `D_QCoh(𝒪_X)`; the existence of the
countable product in `D_QCoh(𝒪_X)` it is built from is part of the conclusion.

The coherator `DQ_X` is an exact right adjoint, so it carries the derived limit `L` to a derived
limit of the system `(DQ_X(iₙ,* Fₙ))`, which is the system `(iₙ,* Fₙ)` itself because `DQ_X` is the
identity on `D_QCoh(𝒪_X)`; and `DQ_X(L)` is `K` by the universal property of `d`. -/
theorem DerivedLimitQCoh.isDerivedLimit_K (d : S.DerivedLimitQCoh) :
    ∃ _hp : HasProduct fun n : ℕ => S.quasiCoherentPushforwardSystem.obj ⟨n⟩,
      IsDerivedLimit S.quasiCoherentPushforwardSystem ⟨d.K, d.quasicoherent⟩ := by
  have := isLeftAdjoint_quasiCoherentι_ofModel S.X.left
  let P := DerivedCategoryB.derivedCategoryB (A := S.X.left.Modules)
    (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf)
  let adj := Adjunction.ofIsLeftAdjoint P.ι
  let : P.ι.rightAdjoint.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  have : P.ι.rightAdjoint.IsRightAdjoint := adj.isRightAdjoint
  obtain ⟨hp, hDQ⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint P.ι.rightAdjoint
    S.derivedPushforwardSystemOfModel d.L d.isDerivedLimit
  let c : S.derivedPushforwardSystemOfModel ⋙ P.ι.rightAdjoint ≅ S.quasiCoherentPushforwardSystem :=
    Functor.isoWhiskerLeft S.quasiCoherentPushforwardSystem (asIso adj.unit).symm ≪≫
      S.quasiCoherentPushforwardSystem.rightUnitor
  have hq : HasProduct fun n : ℕ => S.quasiCoherentPushforwardSystem.obj ⟨n⟩ :=
    hasLimit_of_iso (F := Discrete.functor fun n : ℕ =>
      P.ι.rightAdjoint.obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))
      (Discrete.natIso fun n => c.app ⟨n.as⟩)
  have : HasProduct fun n : ℕ =>
    (S.derivedPushforwardSystemOfModel ⋙ P.ι.rightAdjoint).obj ⟨n⟩ := hp
  let i := isoOfBijectiveComp P (adj.counit.app d.L) d.ε (P.ι.rightAdjoint.obj d.L).2
    d.quasicoherent (fun M hM => bijective_comp_counit P adj d.L M hM) d.universal
  exact ⟨hq, IsDerivedLimit.of_objIso (P.fullyFaithfulι.preimageIso
    (X := P.ι.rightAdjoint.obj d.L) (Y := ⟨d.K, d.quasicoherent⟩) i).symm (hDQ.of_iso c)⟩

/-- **Stacks Project, Tag 0CTD.** In Situation [Stacks, Tag 0CTC] consider
`K = R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)`. Then `K` is in `D^b_QCoh(𝒪_X)` and in
fact `K` has nonzero cohomology sheaves only in degrees `≥ 0`.

Here, at any model of `D(𝒪_X)`, the data `d` of
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh` are a derived limit
`L = R lim_{D(𝒪_X)} Fₙ` and `K = DQ_X(L)`, characterized by its universal property; such data
exist (first conjunct). For any of them, `K` is also a derived limit
`R lim_{D_QCoh(𝒪_X)}(Fₙ)` of the system read in `D_QCoh(𝒪_X)`, which is the displayed equality,
and its cohomology sheaves vanish outside `[0, c]` for some `c`. -/
@[stacks 0CTD]
theorem nonempty_derivedLimitQCoh_and_isDerivedLimit_isGE_isLE :
    Nonempty S.DerivedLimitQCoh ∧ ∀ d : S.DerivedLimitQCoh,
      (∃ _hp : HasProduct fun n : ℕ => S.quasiCoherentPushforwardSystem.obj ⟨n⟩,
        IsDerivedLimit S.quasiCoherentPushforwardSystem ⟨d.K, d.quasicoherent⟩) ∧
      d.K.IsGE 0 ∧ ∃ c : ℤ, d.K.IsLE c :=
  ⟨S.nonempty_derivedLimitQCoh, fun d => ⟨d.isDerivedLimit_K, d.isGE_zero_and_exists_isLE⟩⟩

end Transport

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
