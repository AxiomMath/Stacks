module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels
public import StacksFrontier.Algebra.Homology.PseudoCoherentNoetherianModels
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConnectedConstantModels
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantComplexDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteTypeLocality

/-!
# The derived tensor product preserves locally constant finite type cohomology

Let `(C, J)` be a small site and `Λ` a Noetherian commutative ring. For `K, L` in `D^-` of the
sheaves of `Λ`-modules whose cohomology sheaves are locally constant of finite type, the cohomology
sheaves of `K ⊗^L_Λ L` are again locally constant of finite type. Here the derived tensor product
is `Stacks.ConstantRingModules.constantDerivedTensor`, the derived tensor product over the
constant sheaf of commutative rings on `Λ`, read through the identification of sheaves of modules
over it with sheaves of `Λ`-modules.

## Main results

* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_constantModel`: the
  conclusion when both factors are the constant complexes on bounded above complexes of
  `Λ`-modules of finite type.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_constantModelLeft`: the
  conclusion when one factor has such a model and the other is merely bounded with locally
  constant finite type cohomology.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_isBounded`: the bounded case,
  for an arbitrary sheaf of commutative rings with a locally bijective morphism out of the
  constant presheaf of rings on `Λ`.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor`: the general statement
  for objects of `D^-`.

All names are in the namespace `Stacks.ConstantRingModules`.

## Implementation notes

The reduction of the bounded above case to the bounded case is
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_of_bounded`, instantiated
at this derived tensor product by
`isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_of_bounded`.

1. **With models on both sides.** The derived tensor product of two constant complexes is the
   total tensor complex of the two complexes of constant sheaves of modules
   (`Stacks.ConstantRingModules.derivedTensorConstantComplexIso`), and its cohomology sheaves are
   locally constant of finite type
   (`isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_constantComplex`); both require
   the models to be finite free. A bounded above complex of finitely generated modules over a
   Noetherian ring is pseudo-coherent
   (`StacksDraft.PseudoCoherence.isPseudoCoherentIn_of_boundedAbove_finite_homology`), so it has a
   finite free representative with the same strict upper bound
   (`StacksDraft.PseudoCoherence.IsPseudoCoherentIn.exists_finiteFree_representative_le`), and the
   isomorphism in `D(Λ)` is carried to the associated constant complexes by the exactness of the
   constant-sheaf functor (`exists_finiteFree_constantSheafComplex_iso`).

2. **One cover at a time.** A cover trivializing one factor need not trivialize the other. Rather
   than refining two covers, which would require transporting a constant model along an arbitrary
   morphism of the site, the locality of the condition is used twice: first on a cover
   trivializing the first factor, then, on each member, on a cover trivializing the second. The
   second passage is to a slice of a slice, and the only transport needed there is along
   `Over.forget`, which is exact and carries constant sheaves to constant sheaves with no
   hypothesis on the site. Every sheafification hypothesis on the iterated slice sites is automatic
   at a small site with every universe equal.

3. **The slice compatibilities.** Restriction of the conclusion to a slice is
   `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for the cohomology and
   `Stacks.ConstantRingModules.derivedTensorOverObjIso` for the derived tensor product. The latter
   is stated for an arbitrary `(R, α)`, so it applies on `C` and on `C/U` alike; for the same
   reason the bounded case is proved for an arbitrary `(R, α)`.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules Stacks.ConstantSheaf Stacks.SheafOfModules
  Stacks.DerivedTensor.RingedSite StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] _root_.SheafOfModules.instAbelian
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

universe u

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- A complex vanishing strictly above `b` has no homology above `b`. -/
theorem isZero_homology_of_isStrictlyLE (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (i : ℤ) (hi : b < i) : IsZero (P.homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ (S := P.sc i) (P.isZero_of_isStrictlyLE b i hi)

/-- **A bounded above complex of finitely generated modules over a Noetherian ring has a bounded
above finite free representative with the same strict upper bound**, and the two constant
complexes attached to them are isomorphic in the derived category of sheaves of `Λ`-modules. -/
theorem exists_finiteFree_constantSheafComplex_iso
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hPfg : ∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) :
    ∃ P₁ : CochainComplex (ModuleCat.{u} Λ) ℤ, CochainComplex.IsStrictlyLE P₁ b ∧
      (∀ i : ℤ, Module.Finite Λ (P₁.X i)) ∧ (∀ i : ℤ, Module.Free Λ (P₁.X i)) ∧
      Nonempty (DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ P₁) ≅
        DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ P)) := by
  have hfin : ∀ i : ℤ, Module.Finite Λ (P.X i) := fun i => (ModuleCat.isFG_iff _).1 (hPfg i)
  have hvan : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) i).obj
        (DerivedCategory.Q.obj P)) := fun i hi =>
    (isZero_homology_of_isStrictlyLE Λ P b i hi).of_iso (homologyQObjIso P i)
  have hpc : IsPseudoCoherentIn (DerivedCategory.Q.obj P) :=
    isPseudoCoherentIn_of_boundedAbove_finite_homology _ ⟨b, hvan⟩ fun i =>
      (Module.Finite.equiv_iff (homologyQObjIso P i).toLinearEquiv).2
        (finite_homology_of_finite_X P i)
  obtain ⟨P₁, φ, hP₁, hP₁le, hφ⟩ := hpc.exists_finiteFree_representative_le b hvan
  refine ⟨P₁, hP₁le, fun i => (hP₁ i).1, fun i => (hP₁ i).2, ⟨?_⟩⟩
  exact ((constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.app P₁).symm ≪≫
    (constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategory.mapIso (asIso φ) ≪≫
      (constantSheaf J (ModuleCat.{u} Λ)).mapDerivedCategoryFactors.app P

section Model

variable (R : Sheaf J CommRingCat.{u})
  (α : constRing (C := C) Λ ⟶ (Tensor.ringSheaf.{u, u, u} R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

/-- **The cohomology sheaves of the derived tensor product of two objects which are the constant
complexes on bounded above complexes of `Λ`-modules of finite type are locally constant of finite
type.** -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_constantModel
    (A B : DerivedCategory (Sheaf J (ModuleCat.{u} Λ)))
    (P Q : CochainComplex (ModuleCat.{u} Λ) ℤ) (bP bQ : ℤ)
    [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ]
    (hP : ∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) (hQ : ∀ n : ℤ, ModuleCat.isFG Λ (Q.X n))
    (eA : A ≅ DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ P))
    (eB : B ≅ DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ Q)) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj (((derivedTensor Λ R α).obj A).obj B)) := by
  obtain ⟨P₁, hP₁le, hP₁fin, hP₁free, ⟨eP⟩⟩ :=
    exists_finiteFree_constantSheafComplex_iso (J := J) Λ P bP hP
  obtain ⟨Q₁, hQ₁le, hQ₁fin, hQ₁free, ⟨eQ⟩⟩ :=
    exists_finiteFree_constantSheafComplex_iso (J := J) Λ Q bQ hQ
  have := hP₁le
  have := hQ₁le
  let fA : DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ P₁) ≅ A := eP ≪≫ eA.symm
  let fB : DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ Q₁) ≅ B := eQ ≪≫ eB.symm
  refine ObjectProperty.prop_of_iso (IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ)
    ((DerivedCategory.homologyFunctor _ i).mapIso
      (((derivedTensor Λ R α).mapIso fA).app _ ≪≫
        ((derivedTensor Λ R α).obj A).mapIso fB)) ?_
  exact isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_constantComplex
    Λ R α P₁ Q₁ bP bQ hP₁fin hP₁free hQ₁fin hQ₁free i

/-! ### Restriction to a slice -/

/-- The restriction of sheaves of `Λ`-modules to the slice site over `U` is an additive functor. -/
local instance additive_overPullback (U : C) : (J.overPullback (ModuleCat.{u} Λ) U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restricting the constant complex on `P` to a slice site gives the constant complex on `P`
there. -/
def constantSheafComplexOverIso (U : C) (P : CochainComplex (ModuleCat.{u} Λ) ℤ) :
    (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ P)) ≅
      DerivedCategory.Q.obj (constantSheafComplex (J := J.over U) Λ P) :=
  ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategoryFactors.app
      (constantSheafComplex (J := J) Λ P)) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
        (Stacks.ConstantSheaf.overPullbackConstantSheafIso J (ModuleCat.{u} Λ) U).symm
        (ComplexShape.up ℤ)).app P)

/-- The cohomology of the derived tensor product, restricted to a slice site, is the cohomology
of the derived tensor product of the restrictions. -/
def homologyDerivedTensorOverIso (U : C)
    (A B : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) (i : ℤ) :
    (J.overPullback (ModuleCat.{u} Λ) U).obj
        ((DerivedCategory.homologyFunctor _ i).obj (((derivedTensor Λ R α).obj A).obj B)) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor Λ (R.over U) (tensorOverRingMap Λ R α U)).obj
            ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj A)).obj
          ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj B)) :=
  (((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategoryHomologyIso i).app
      (((derivedTensor Λ R α).obj A).obj B)).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso (derivedTensorOverObjIso Λ R α U A B)

/-! ### The conclusion over a cover -/

/-- A sheaf is of locally constant finite type once it is so over the members of a cover, each of
which carries a constant model of a given bounded complex `K` with such cohomology. -/
private theorem isFiniteTypeLocallyConstantModuleSheaf_of_constantModel_over
    (K : DerivedCategory.Bounded (Sheaf J (ModuleCat.{u} Λ)))
    (hK : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj K.obj)) (F : Sheaf J (ModuleCat.{u} Λ))
    (h : ∀ (U : C) (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (b : ℤ), P.IsStrictlyLE b →
      (∀ n : ℤ, ModuleCat.isFG Λ (P.X n)) →
      ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj K.obj ≅
        DerivedCategory.Q.obj (constantSheafComplex (J := J.over U) Λ P)) →
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} (J.over U) Λ (F.over U)) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ F := by
  refine isFiniteTypeLocallyConstantModuleSheaf_of_local J Λ _ fun X => ?_
  obtain ⟨T, ⟨e⟩, I, V, f, hcov, hmodel⟩ := exists_cover_constantComplex_representation J Λ X K hK
  refine ⟨I, V, f, hcov, fun j => ?_⟩
  obtain ⟨P, a, b, hz, hfg, ⟨eP⟩⟩ := hmodel j
  exact h (V j) P b ((CochainComplex.isStrictlyLE_iff P b).2 fun n hn =>
    hz n (by simp only [Set.mem_Icc]; omega)) hfg
    ((J.overPullback (ModuleCat.{u} Λ) (V j)).mapDerivedCategory.mapIso e ≪≫
      (J.overPullback (ModuleCat.{u} Λ) (V j)).mapDerivedCategoryFactors.app T ≪≫ eP)

/-- **One factor with a constant model is enough**: if `A` is the constant complex on a bounded
above complex of `Λ`-modules of finite type and `B` is bounded with locally constant finite type
cohomology, the cohomology sheaves of `A ⊗^L B` are locally constant of finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_constantModelLeft
    (A : DerivedCategory (Sheaf J (ModuleCat.{u} Λ)))
    (B : DerivedCategory.Bounded (Sheaf J (ModuleCat.{u} Λ)))
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (bP : ℤ) [P.IsStrictlyLE bP]
    (hP : ∀ n : ℤ, ModuleCat.isFG Λ (P.X n))
    (eA : A ≅ DerivedCategory.Q.obj (constantSheafComplex (J := J) Λ P))
    (hB : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj B.obj)) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor Λ R α).obj A).obj B.obj)) := by
  refine isFiniteTypeLocallyConstantModuleSheaf_of_constantModel_over Λ B hB _
    fun U Q₀ b₀ _ hfg eB => ?_
  refine ObjectProperty.prop_of_iso _ (homologyDerivedTensorOverIso Λ R α U A B.obj i).symm ?_
  exact isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_constantModel
    Λ (R.over U) (tensorOverRingMap Λ R α U) _ _ P Q₀ bP b₀ hP hfg
    ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.mapIso eA ≪≫
      constantSheafComplexOverIso Λ U P) eB i

/-- **The bounded case: both factors bounded with locally constant finite type cohomology.** -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_isBounded
    (K L : DerivedCategory.Bounded (Sheaf J (ModuleCat.{u} Λ)))
    (hK : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj K.obj))
    (hL : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj L.obj)) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor Λ R α).obj K.obj).obj L.obj)) := by
  obtain ⟨⟨aL, haL⟩, ⟨bL, hbL⟩⟩ := L.property
  let := haL
  let := hbL
  obtain ⟨TL, hTLa, hTLb, ⟨eL⟩⟩ := L.obj.exists_iso_Q_obj_of_isGE_of_isLE aL bL
  let := hTLa
  let := hTLb
  have hTL : ∀ q : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ (TL.homology q) :=
    fun q => ObjectProperty.prop_of_iso _
      ((DerivedCategory.homologyFunctor _ q).mapIso eL ≪≫
        (DerivedCategory.homologyFunctorFactors _ q).app TL) (hL q)
  refine isFiniteTypeLocallyConstantModuleSheaf_of_constantModel_over Λ K hK _
    fun U P₀ b₀ _ hfg eP₀ => ?_
  set G := J.overPullback (ModuleCat.{u} Λ) U with hG
  have : CochainComplex.IsStrictlyGE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj TL) aL :=
    (CochainComplex.isStrictlyGE_iff _ aL).2 fun n hn =>
      G.map_isZero (TL.isZero_of_isStrictlyGE aL n hn)
  have : CochainComplex.IsStrictlyLE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj TL) bL :=
    (CochainComplex.isStrictlyLE_iff _ bL).2 fun n hn =>
      G.map_isZero (TL.isZero_of_isStrictlyLE bL n hn)
  let eLV : G.mapDerivedCategory.obj L.obj ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj TL) :=
    G.mapDerivedCategory.mapIso eL ≪≫ G.mapDerivedCategoryFactors.app TL
  have : (G.mapDerivedCategory.obj L.obj).IsGE aL :=
    DerivedCategory.TStructure.t.isGE_of_iso eLV.symm aL
  have : (G.mapDerivedCategory.obj L.obj).IsLE bL :=
    DerivedCategory.TStructure.t.isLE_of_iso eLV.symm bL
  refine ObjectProperty.prop_of_iso _
    (homologyDerivedTensorOverIso Λ R α U K.obj L.obj i).symm ?_
  refine isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_constantModelLeft
    Λ (R.over U) (tensorOverRingMap Λ R α U) _
    ⟨G.mapDerivedCategory.obj L.obj, ⟨⟨aL, inferInstance⟩, ⟨bL, inferInstance⟩⟩⟩
    P₀ b₀ hfg
    eP₀
    (fun q => ?_) i
  exact ObjectProperty.prop_of_iso _
    (((DerivedCategory.homologyFunctor _ q).mapIso eLV ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj TL)).symm)
    (finiteTypeLocallyConstant_homology_over J TL q (hTL q) U)

/-! ### Stacks Tag 094H -/

/-- Let `(C, J)` be a small site, `Λ` a Noetherian commutative ring, and let `K` and `L` be
objects of `D^-` of the sheaves of `Λ`-modules whose cohomology sheaves are locally constant of
finite type. Then the cohomology sheaves of `K ⊗^L_Λ L` are locally constant of finite type, where
the derived tensor product is `Stacks.ConstantRingModules.constantDerivedTensor`, taken over the
constant sheaf of commutative rings on `Λ`. -/
@[stacks 094H "the full statement for the derived tensor product over the constant sheaf of \
  commutative rings on Λ: for K and L in D^- of the sheaves of Λ-modules whose cohomology \
  sheaves are locally constant of finite type, so are those of K ⊗^L_Λ L. The site is small and \
  every universe is one, which is the configuration in which the derived tensor product of \
  Stacks 06YU is available; apart from that nothing is assumed, and in particular the bounded \
  case of the tag is proved here and not supposed"]
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor
    (K L : DerivedCategory.Minus (Sheaf J (ModuleCat.{u} Λ)))
    (hK : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj K.obj))
    (hL : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj L.obj)) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (((constantDerivedTensor J Λ).obj K.obj).obj L.obj)) :=
  isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_of_bounded J Λ
    (fun K' L' hK' hL' i' =>
      isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensor_of_isBounded Λ
        (constantCommRingSheaf J Λ) (constantTensorRingMap J Λ) K' L' hK' hL' i')
    K L hK hL i

end Model

end Stacks.ConstantRingModules

end
