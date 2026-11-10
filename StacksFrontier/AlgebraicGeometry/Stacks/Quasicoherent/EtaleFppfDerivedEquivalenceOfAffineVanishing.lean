module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedCategoryBTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AlgebraicStackSiteSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineZariskiRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineVanishing
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedWeakSerreAcrossTopologies

/-!
# `ε^*` on the derived categories of an algebraic stack, for a class with affine vanishing

Let `𝒳` be an algebraic stack and `ε : 𝒳_fppf ⟶ 𝒳_étale` the comparison morphism. Let `L` be a
weak Serre subcategory of `Mod(𝒪_𝒳)` whose higher fppf cohomology vanishes over every object
lying over an affine scheme, and let `L' = ε_*L` be its image in `Mod(𝒳_étale, 𝒪_𝒳)`. This file
proves that

`ε^* : D_{L'}(𝒳_étale, 𝒪_𝒳) ⥤ D_L(𝒪_𝒳)`

is an equivalence. This is how the source proves that the middle vertical arrow of the diagram
of **Stacks 07B8** is an equivalence: by **Stacks 07A8** applied with `𝒞 = 𝒳`, `τ = fppf`,
`τ' = étale`, `𝒜 = L` and `ℬ` the objects lying over affine schemes. Condition (3) of 07A8 —
every object has an étale covering by objects of `ℬ` — holds because every scheme has a Zariski
covering by affines, and condition (4) is the vanishing assumed of `L`.

## The argument

The second conclusion of Stacks 07A8 in this library,
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE`, is stated for a ringed site
whose objects, morphisms and sections all lie in one universe. The site of `𝒳` has its objects
one universe up; so 07A8 is applied on the small model of `𝒳`
(`AlgebraicGeometry.Stack.fppfSmallModel`) to the class `L` transported there, and the resulting
equivalence is transported back along the equivalences of module categories, with which `ε^*`
commutes (`AlgebraicGeometry.Stack.smallModelPullbackSquareIso`), by
`DerivedCategoryB.isEquivalence_mapDerivedCategoryLift_of_transport`.

## Main results

* `AlgebraicGeometry.Stack.isZero_moduleCohomology_fppfSmallModel`: condition (4) of 07A8 on the
  small model.
* `AlgebraicGeometry.Stack.exists_etaleCovering_smallModelAffineObjects`: condition (3) of 07A8 on
  the small model.
* `AlgebraicGeometry.Stack.isEquivalence_epsilonPullbackDerivedLift_of_vanishing`: the
  equivalence `D_{L'}(𝒳_étale, 𝒪_𝒳) ≌ D_L(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.SmallModelSite Stacks.Cohomology.CompareTopologies

universe u w t₁ t₂

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] hasSheafify_associatedTopology_algebraicStack
  wEqualsLocallyBijective_associatedTopology_algebraicStack enoughInjectives_fppfModules
  Stacks.Cohomology.AcyclicCover.evaluation_additive

section SmallModel

/-- The objects of the small model of `𝒳` lying over affine schemes: the class `ℬ` of the proof
of **Stacks 07B8**, read on the small model. -/
abbrev smallModelAffineObjects : Set (fppfSmallModel B S hS 𝒳).C :=
  fun U ↦ IsAffineOver B S hS
    (𝒳.val.val.p.obj ((equivalence.{u} (C := 𝒳.val.val.obj)).functor.obj U))

/-- **Condition (3) of Stacks 07A8 on the small model of `𝒳`.** Every object of the small model
has a covering for the étale topology whose members lie over affine schemes.

An étale covering of the corresponding object of `𝒳` by objects over affine schemes
(`AlgebraicGeometry.FibredSite.exists_affine_ofArrows_etale`, from an affine open covering of the
scheme below) is carried to the small model by the quasi-inverse of the model equivalence; the
family of all arrows into the object from objects over affine schemes then covers, and it is
indexed by a type in the universe of the model. -/
theorem exists_etaleCovering_smallModelAffineObjects (U : (fppfSmallModel B S hS 𝒳).C) :
    ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ etaleSmallModelTopology B S hS 𝒳 U ∧
      ∀ i, smallModelAffineObjects B S hS 𝒳 (𝒰.X i) := by
  classical
  let e := equivalence.{u} (C := 𝒳.val.val.obj)
  let 𝒰 : PreZeroHypercover.{u} U :=
    { I₀ := {a : Σ V : (fppfSmallModel B S hS 𝒳).C, V ⟶ U // smallModelAffineObjects B S hS 𝒳 a.1}
      X a := a.1.1
      f a := a.1.2 }
  refine ⟨𝒰, ?_, fun a ↦ a.2⟩
  obtain ⟨I, y, φ, hy, hcov⟩ := FibredSite.exists_affine_ofArrows_etale B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (e.functor.obj U)
  change 𝒰.sieve₀ ∈ e.functor.inducedTopology
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) U
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
  refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale).superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨j⟩
  let g : e.inverse.obj (y j) ⟶ U := e.functor.preimage (e.counitIso.hom.app (y j) ≫ φ j)
  have hg : smallModelAffineObjects B S hS 𝒳 (e.inverse.obj (y j)) := by
    have : IsAffine (B.inclusion.obj ((Over.forget (B.obj hS)).obj
        (𝒳.val.val.p.obj ((𝟭 𝒳.val.val.obj).obj (y j))))) := hy j
    exact IsAffine.of_isIso (B.inclusion.map
      ((Over.forget (B.obj hS)).map (𝒳.val.val.p.map (e.counitIso.hom.app (y j)))))
  refine ⟨e.inverse.obj (y j), g, e.counitIso.inv.app (y j),
    ⟨_, 𝟙 _, g, Presieve.ofArrows.mk (⟨⟨_, g⟩, hg⟩ : 𝒰.I₀), Category.id_comp _⟩, ?_⟩
  simp [g]

variable (L : ObjectProperty (fppfModules B S hS 𝒳))

/-- A class of modules on `𝒳_fppf`, transported to the small model of `𝒳`. -/
abbrev fppfSmallModelClass : ObjectProperty (fppfSmallModelModules B S hS 𝒳) :=
  L.inverseImage (fppfModulesSmallModelEquivalence B S hS 𝒳).inverse

/-- **Condition (4) of Stacks 07A8 on the small model of `𝒳`.** If the higher cohomology of the
modules of `L` vanishes over the objects of `𝒳` lying over affine schemes, then the higher
cohomology of the modules of the transported class vanishes over the objects of the small model
lying over affine schemes.

The derived functors of the sections over an object of the model, precomposed with the model
equivalence of module categories, are the derived functors of the sections over the
corresponding object of `𝒳` (`CategoryTheory.Equivalence.compRightDerivedIso`, the two
evaluation functors agreeing definitionally). -/
theorem isZero_moduleCohomology_fppfSmallModel
    (hvan : ∀ F : fppfModules B S hS 𝒳, L F → ∀ x : 𝒳.val.val.obj,
      IsAffineOver B S hS (𝒳.val.val.p.obj x) → ∀ n : ℕ, 0 < n →
        IsZero (((SheafOfModules.evaluation
          (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) (op x)).rightDerived
            n).obj F))
    (U : (fppfSmallModel B S hS 𝒳).C) (hU : smallModelAffineObjects B S hS 𝒳 U) (n : ℕ)
    (hn : 0 < n) (F : fppfSmallModelModules B S hS 𝒳) (hF : fppfSmallModelClass B S hS 𝒳 L F) :
    IsZero (Stacks.Cohomology.moduleCohomology
      (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O) U n F) := by
  have h₁ : IsZero ((((fppfModulesSmallModelEquivalence B S hS 𝒳).functor ⋙
      SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
        (fppfSmallModel B S hS 𝒳).O) (op U)).rightDerived n).obj
      ((fppfModulesSmallModelEquivalence B S hS 𝒳).inverse.obj F)) := hvan _ hF _ hU n hn
  exact (h₁.of_iso (((fppfModulesSmallModelEquivalence B S hS 𝒳).compRightDerivedIso
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (fppfSmallModel B S hS 𝒳).O) (op U)) n).app _).symm).of_iso
    (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (fppfSmallModel B S hS 𝒳).O) (op U)).rightDerived n).mapIso
    ((fppfModulesSmallModelEquivalence B S hS 𝒳).counitIso.app F)).symm

end SmallModel

section SmallModelDerived

variable (L : ObjectProperty (fppfModules B S hS 𝒳)) [L.IsWeakSerreClass]
  (hvan : ∀ F : fppfModules B S hS 𝒳, L F → ∀ x : 𝒳.val.val.obj,
      IsAffineOver B S hS (𝒳.val.val.p.obj x) → ∀ n : ℕ, 0 < n →
        IsZero (((SheafOfModules.evaluation
          (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) (op x)).rightDerived
            n).obj F))

/-- The image of the transported class under `ε_*` of the small model: the class `A'` of
Stacks 07A8 there. -/
abbrev etaleSmallModelClass : ObjectProperty (etaleSmallModelModules B S hS 𝒳) :=
  imageOfLE (etaleSmallModelTopology_le B S hS 𝒳)
    (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O)
    (fppfSmallModelClass B S hS 𝒳 L)

include hvan in
/-- **Stacks 07A8 on the small model of `𝒳`.** For a weak Serre class `L` of `Mod(𝒪_𝒳)` whose
higher cohomology vanishes over the objects lying over affine schemes, `ε^*` of the small model
induces an equivalence `D_{ε_*A}(𝒪_{étale}) ≌ D_A(𝒪_{fppf})`, where `A` is `L` transported to the
small model.

The equivalence is the quasi-inverse of
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE`, whose hypotheses are
`AlgebraicGeometry.Stack.exists_etaleCovering_smallModelAffineObjects` and
`AlgebraicGeometry.Stack.isZero_moduleCohomology_fppfSmallModel`; that quasi-inverse is `ε^*`
applied termwise (`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLEInverseCompιIso`)
and `ε^*` is the sheafification of the finer topology
(`AlgebraicGeometry.RingedSite.pullbackToposCoarseningHomIso`).

Both derived categories are taken at `HasDerivedCategory.standard`, named in the statement: the
small model is a small site, where instance search finds the locally small model instead, and
`Stacks.Cohomology.CompareTopologies.derivedEquivalenceImageOfLE` is formed at the standard
model. The statement for arbitrary models on `𝒳` itself is
`AlgebraicGeometry.Stack.isEquivalence_epsilonPullbackDerivedLift_of_vanishing`. -/
theorem isEquivalence_smallModelPullbackDerivedLift :
    (@DerivedCategoryB.mapDerivedCategoryLift _ _ _ (HasDerivedCategory.standard _) _ _ _
      (HasDerivedCategory.standard _)
      (pullback (etaleSmallModelTopology_le B S hS 𝒳)
        (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O)) _ _ _
      (etaleSmallModelClass B S hS 𝒳 L) (fppfSmallModelClass B S hS 𝒳 L) _
      (fun _ hN ↦ prop_pullback_obj _ _ _ inferInstance hN)).IsEquivalence := by
  let : HasDerivedCategory (etaleSmallModelModules B S hS 𝒳) := HasDerivedCategory.standard _
  let : HasDerivedCategory (fppfSmallModelModules B S hS 𝒳) := HasDerivedCategory.standard _
  have hB := exists_etaleCovering_smallModelAffineObjects B S hS 𝒳
  have hv := isZero_moduleCohomology_fppfSmallModel B S hS 𝒳 L hvan
  let hl := ((fppfSmallModel B S hS 𝒳).coarseningHom
      (etaleSmallModelTopology_le B S hS 𝒳)).toRingedToposSiteHom
      |>.pullbackTopos_preservesFiniteLimits
    ((fppfSmallModel B S hS 𝒳).coarseningHom
      (etaleSmallModelTopology_le B S hS 𝒳)).isMorphismOfSites_toRingedToposSiteHom
    ((fppfSmallModel B S hS 𝒳).isFlatMapULift_fSharp_auxHomH_coarseningHom
      (etaleSmallModelTopology_le B S hS 𝒳))
  let hc := ((fppfSmallModel B S hS 𝒳).coarseningHom
    (etaleSmallModelTopology_le B S hS 𝒳)).toRingedToposSiteHom
    |>.pullbackTopos_preservesFiniteColimits
  let ha := Functor.additive_of_preserves_binary_products
    ((fppfSmallModel B S hS 𝒳).coarseningHom
      (etaleSmallModelTopology_le B S hS 𝒳)).toRingedToposSiteHom.pullbackTopos
  let e := derivedEquivalenceImageOfLE (fppfSmallModel B S hS 𝒳)
    (etaleSmallModelTopology_le B S hS 𝒳) (fppfSmallModelClass B S hS 𝒳 L)
    (smallModelAffineObjects B S hS 𝒳) hB hv
  let α : e.inverse ⋙ (DerivedCategoryB.derivedCategoryB (fppfSmallModelClass B S hS 𝒳 L)).ι ≅
      (DerivedCategoryB.derivedCategoryB (etaleSmallModelClass B S hS 𝒳 L)).ι ⋙
        (pullback (etaleSmallModelTopology_le B S hS 𝒳) (Stacks.SheafOfModules.Tensor.ringSheaf
          (fppfSmallModel B S hS 𝒳).O)).mapDerivedCategory :=
    derivedEquivalenceImageOfLEInverseCompιIso (fppfSmallModel B S hS 𝒳)
        (etaleSmallModelTopology_le B S hS 𝒳) (fppfSmallModelClass B S hS 𝒳 L)
        (smallModelAffineObjects B S hS 𝒳) hB hv ≪≫
      Functor.isoWhiskerLeft _
        (@Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ _
          (HasDerivedCategory.standard _) _ _ _ (HasDerivedCategory.standard _)
          (fppfSmallModel B S hS 𝒳 |>.coarseningHom
            (etaleSmallModelTopology_le B S hS 𝒳)).toRingedToposSiteHom.pullbackTopos
          (pullback (etaleSmallModelTopology_le B S hS 𝒳)
            (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O))
          ha hl hc
          (additive_pullback (etaleSmallModelTopology_le B S hS 𝒳)
            (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O))
          (preservesFiniteLimits_pullback (etaleSmallModelTopology_le B S hS 𝒳)
            (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O))
          (preservesFiniteColimits_pullback (etaleSmallModelTopology_le B S hS 𝒳)
            (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O))
          ((fppfSmallModel B S hS 𝒳).pullbackToposCoarseningHomIso
            (etaleSmallModelTopology_le B S hS 𝒳)))
  exact Functor.isEquivalence_of_iso (F := e.inverse)
    (((DerivedCategoryB.derivedCategoryB
      (fppfSmallModelClass B S hS 𝒳 L)).fullyFaithfulι.whiskeringRight _).preimageIso α)

end SmallModelDerived

section Transport

variable (L : ObjectProperty (fppfModules B S hS 𝒳)) [L.IsWeakSerreClass]
  (hvan : ∀ F : fppfModules B S hS 𝒳, L F → ∀ x : 𝒳.val.val.obj,
      IsAffineOver B S hS (𝒳.val.val.p.obj x) → ∀ n : ℕ, 0 < n →
        IsZero (((SheafOfModules.evaluation
          (fppfSiteRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) (op x)).rightDerived
            n).obj F))
  (L' : ObjectProperty (etaleModules B S hS 𝒳))
  (hL' : ∀ N, L' N ↔ imageOfLE (etaleTopologyLeFppf B S hS 𝒳)
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) L N)

include hL' in
/-- `ε^*` carries the image `L' = ε_*L` back into `L`: an object of `L'` is `ε_*` of an object of
`L`, and `ε^*ε_*` is the identity on sheaves for the finer topology. -/
theorem prop_epsilonPullback_obj_of_imageOfLE {N : etaleModules B S hS 𝒳} (hN : L' N) :
    L ((epsilonPullback B S hS 𝒳).obj N) :=
  prop_pullback_obj _ _ _ inferInstance ((hL' N).1 hN)

include hL' in
/-- The étale class `L'` corresponds, under the equivalence of `Mod(𝒳_étale, 𝒪_𝒳)` with the
modules of the étale site of the small model, to the image under `ε_*` of the transported
class: `ε_*` commutes with the two model equivalences
(`AlgebraicGeometry.Stack.smallModelPushforwardSquareIso`). -/
theorem prop_etaleSmallModelClass_iff (M : etaleModules B S hS 𝒳) :
    L' M ↔ etaleSmallModelClass B S hS 𝒳 L
      ((etaleModulesSmallModelEquivalence B S hS 𝒳).functor.obj M) := by
  rw [hL']
  constructor
  · rintro ⟨M₀, hM₀, ⟨e⟩⟩
    exact ⟨(fppfModulesSmallModelEquivalence B S hS 𝒳).functor.obj M₀,
      L.prop_of_iso ((fppfModulesSmallModelEquivalence B S hS 𝒳).unitIso.app M₀) hM₀,
      ⟨((smallModelPushforwardSquareIso B S hS 𝒳).app M₀).symm ≪≫
        (etaleModulesSmallModelEquivalence B S hS 𝒳).functor.mapIso e⟩⟩
  · rintro ⟨N, hN, ⟨e⟩⟩
    exact ⟨(fppfModulesSmallModelEquivalence B S hS 𝒳).inverse.obj N, hN,
      ⟨((smallModelPushforwardInverseSquareIso B S hS 𝒳).app N).symm ≪≫
        (etaleModulesSmallModelEquivalence B S hS 𝒳).inverse.mapIso e ≪≫
        ((etaleModulesSmallModelEquivalence B S hS 𝒳).unitIso.app M).symm⟩⟩

variable [HasDerivedCategory.{t₁} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t₂} (etaleModules B S hS 𝒳)]

include hvan hL' in
/-- **`ε^* : D_{L'}(𝒳_étale, 𝒪_𝒳) ⥤ D_L(𝒪_𝒳)` is an equivalence**, for a weak Serre class `L` of
`Mod(𝒪_𝒳)` whose higher fppf cohomology vanishes over the objects lying over affine schemes, and
its image `L' = ε_*L` in `Mod(𝒳_étale, 𝒪_𝒳)`. This is **Stacks 07A8** for `𝒳` with
`τ = fppf`, `τ' = étale`, `𝒜 = L` and `ℬ` the objects over affine schemes, as the proof of
**Stacks 07B8** applies it.

The derived categories carry arbitrary `HasDerivedCategory` instances. The equivalence is
`AlgebraicGeometry.Stack.isEquivalence_smallModelPullbackDerivedLift` transported along the
model equivalences of module categories, with which `ε^*` commutes
(`AlgebraicGeometry.Stack.smallModelPullbackSquareIso`), by
`DerivedCategoryB.isEquivalence_mapDerivedCategoryLift_of_transport`. -/
theorem isEquivalence_epsilonPullbackDerivedLift_of_vanishing :
    (DerivedCategoryB.mapDerivedCategoryLift (epsilonPullback B S hS 𝒳) L' L
      (fun _ hN ↦ prop_epsilonPullback_obj_of_imageOfLE B S hS 𝒳 L L' hL' hN)).IsEquivalence := by
  let : HasDerivedCategory (fppfSmallModelModules B S hS 𝒳) := HasDerivedCategory.standard _
  let : HasDerivedCategory (etaleSmallModelModules B S hS 𝒳) := HasDerivedCategory.standard _
  have := isEquivalence_smallModelPullbackDerivedLift B S hS 𝒳 L hvan
  exact DerivedCategoryB.isEquivalence_mapDerivedCategoryLift_of_transport
    (epsilonPullback B S hS 𝒳)
    (pullback (etaleSmallModelTopology_le B S hS 𝒳)
      (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O))
    (etaleModulesSmallModelEquivalence B S hS 𝒳) (fppfModulesSmallModelEquivalence B S hS 𝒳)
    (smallModelPullbackSquareIso B S hS 𝒳) L' L
    (etaleSmallModelClass B S hS 𝒳 L) (fppfSmallModelClass B S hS 𝒳 L)
    (prop_etaleSmallModelClass_iff B S hS 𝒳 L L' hL')
    (fun M ↦ L.prop_iff_of_iso ((fppfModulesSmallModelEquivalence B S hS 𝒳).unitIso.app M))
    (fun _ hN ↦ prop_epsilonPullback_obj_of_imageOfLE B S hS 𝒳 L L' hL' hN)
    (fun _ hN ↦ prop_pullback_obj _ _ _ inferInstance hN)

end Transport

end AlgebraicGeometry.Stack

end
