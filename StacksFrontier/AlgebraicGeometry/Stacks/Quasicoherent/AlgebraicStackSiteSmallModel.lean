module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleComparisonAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedEquivalence

/-!
# The fppf and étale sites of an algebraic stack on a small model

The fppf site `𝒳_fppf` of an algebraic stack has its objects in `Type (u + 1)`, its morphisms in
`Type u` and its structure sheaf in `CommRingCat.{u}`; it is essentially small at `u`
(`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`). The theory of ringed sites of
this library — the second conclusion of **Stacks 07A8** in particular — is stated for a ringed
site whose objects, morphisms and sections all lie in one universe. This file transports the
comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale` of **Stacks 07B8** to the small model of `𝒳` provided
by `Stacks.SheafOfModules.SmallModelSite.ringedSite`, and records that the transport commutes with
`ε^*` and `ε_*`.

## Main definitions

* `AlgebraicGeometry.Stack.fppfSmallModel`: the small model of `𝒳_fppf`, a ringed site with all
  its universes equal.
* `AlgebraicGeometry.Stack.etaleSmallModelTopology`: the étale topology on the small model, and
  `AlgebraicGeometry.Stack.etaleSmallModelTopology_le`: it is coarser than the fppf topology.
* `AlgebraicGeometry.Stack.fppfModulesSmallModelEquivalence`,
  `AlgebraicGeometry.Stack.etaleModulesSmallModelEquivalence`: `Mod(𝒪_𝒳)` and
  `Mod(𝒳_étale, 𝒪_𝒳)` are the module categories of the small model.

## Main results

* `AlgebraicGeometry.Stack.smallModelPushforwardSquareIso`: the transport commutes with `ε_*`.
* `AlgebraicGeometry.Stack.smallModelPullbackSquareIso`: the transport commutes with `ε^*`.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace CategoryTheory.Functor

/-- **The topology induced along an equivalence is monotone in the topology it is induced from.**
Along an equivalence, membership in the induced topology is membership of the pushed forward
sieve. -/
theorem inducedTopology_mono_of_isEquivalence {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) [G.IsEquivalence] {K₁ K₂ : GrothendieckTopology D} (h : K₁ ≤ K₂) :
    G.inducedTopology K₁ ≤ G.inducedTopology K₂ := by
  intro X R hR
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hR ⊢
  exact h _ hR

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

open Stacks.SheafOfModules.SmallModelSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The small model of the fppf site of an algebraic stack**: a ringed site whose objects,
morphisms and sections all lie in `Type u`, equivalent to `(𝒳_fppf, 𝒪_𝒳)`. -/
abbrev fppfSmallModel : RingedSite.{u, u, u} where
  C := SmallModel.{u} 𝒳.val.val.obj
  J := topology.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
  O := ((equivalence.{u} (C := 𝒳.val.val.obj)).functor.sheafPushforwardContinuous
    CommRingCat.{u} (topology.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf))
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)).obj
    (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)

/-- The étale topology on the small model of an algebraic stack, induced from `𝒳_étale`. -/
abbrev etaleSmallModelTopology : GrothendieckTopology (fppfSmallModel B S hS 𝒳).C :=
  topology.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)

/-- The étale topology of the small model is coarser than its fppf topology. -/
theorem etaleSmallModelTopology_le :
    etaleSmallModelTopology B S hS 𝒳 ≤ (fppfSmallModel B S hS 𝒳).J :=
  Functor.inducedTopology_mono_of_isEquivalence _ (etaleTopologyLeFppf B S hS 𝒳)

/-- The modules of the fppf site of the small model. -/
abbrev fppfSmallModelModules :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O)

/-- The modules of the étale site of the small model. -/
abbrev etaleSmallModelModules :=
  SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O).ofLE
    (etaleSmallModelTopology_le B S hS 𝒳))

/-- **`Mod(𝒪_𝒳)` is the module category of the fppf site of the small model.** -/
def fppfModulesSmallModelEquivalence :
    fppfModules B S hS 𝒳 ≌ fppfSmallModelModules B S hS 𝒳 :=
  modulesEquivalence.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
    (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)

/-- The functor of the model equivalence is continuous from the étale topology of the small model
to the étale topology of `𝒳`. -/
instance smallModel_functor_isContinuous_etale :
    (equivalence.{u} (C := 𝒳.val.val.obj)).functor.IsContinuous
      (etaleSmallModelTopology B S hS 𝒳)
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) :=
  functor_isContinuous.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)

/-- The inverse of the model equivalence is continuous from the étale topology of `𝒳` to the étale
topology of the small model. -/
instance smallModel_inverse_isContinuous_etale :
    (equivalence.{u} (C := 𝒳.val.val.obj)).inverse.IsContinuous
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      (etaleSmallModelTopology B S hS 𝒳) :=
  inverse_isContinuous.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)

/-- **`Mod(𝒳_étale, 𝒪_𝒳)` is the module category of the étale site of the small model.** -/
def etaleModulesSmallModelEquivalence :
    etaleModules B S hS 𝒳 ≌ etaleSmallModelModules B S hS 𝒳 :=
  haveI : (equivalence.{u} (C := 𝒳.val.val.obj)).functor.IsContinuous
      (topology.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale))
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale) :=
    functor_isContinuous.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
  haveI : (equivalence.{u} (C := 𝒳.val.val.obj)).inverse.IsContinuous
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      (topology.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)) :=
    inverse_isContinuous.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
  Stacks.SheafOfModules.reindexEquivalence
    (J' := topology.{u} (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale))
    (equivalence.{u} (C := 𝒳.val.val.obj))
    ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).ofLE
      (etaleTopologyLeFppf B S hS 𝒳))

/-- The functor of `fppfModulesSmallModelEquivalence` is additive. -/
instance : (fppfModulesSmallModelEquivalence B S hS 𝒳).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of `fppfModulesSmallModelEquivalence` is additive. -/
instance : (fppfModulesSmallModelEquivalence B S hS 𝒳).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor of `etaleModulesSmallModelEquivalence` is additive. -/
instance : (etaleModulesSmallModelEquivalence B S hS 𝒳).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of `etaleModulesSmallModelEquivalence` is additive. -/
instance : (etaleModulesSmallModelEquivalence B S hS 𝒳).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### `ε_*` commutes with the transport -/

/-- `ε_*` commutes with the transport to the small model, on the underlying presheaves of modules:
both sides are the pushforward of the underlying presheaf along the model equivalence. -/
def smallModelPushforwardSquareValIso (M : fppfModules B S hS 𝒳) :
    ((etaleModulesSmallModelEquivalence B S hS 𝒳).functor.obj
        ((fppfToEtaleModules B S hS 𝒳).obj M)).val ≅
      ((Stacks.Cohomology.CompareTopologies.pushforward (etaleSmallModelTopology_le B S hS 𝒳)
          (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O)).obj
          ((fppfModulesSmallModelEquivalence B S hS 𝒳).functor.obj M)).val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- `ε_*` commutes with the transport to the small model, at one module. -/
def smallModelPushforwardSquareObjIso (M : fppfModules B S hS 𝒳) :
    (etaleModulesSmallModelEquivalence B S hS 𝒳).functor.obj
        ((fppfToEtaleModules B S hS 𝒳).obj M) ≅
      (Stacks.Cohomology.CompareTopologies.pushforward (etaleSmallModelTopology_le B S hS 𝒳)
          (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O)).obj
          ((fppfModulesSmallModelEquivalence B S hS 𝒳).functor.obj M) :=
  (SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O).ofLE
      (etaleSmallModelTopology_le B S hS 𝒳))).preimageIso
    (smallModelPushforwardSquareValIso B S hS 𝒳 M)

/-- The isomorphisms `smallModelPushforwardSquareObjIso` are natural in the module. -/
theorem smallModelPushforwardSquareObjIso_naturality {M N : fppfModules B S hS 𝒳} (f : M ⟶ N) :
    (fppfToEtaleModules B S hS 𝒳 ⋙ (etaleModulesSmallModelEquivalence B S hS 𝒳).functor).map f ≫
        (smallModelPushforwardSquareObjIso B S hS 𝒳 N).hom =
      (smallModelPushforwardSquareObjIso B S hS 𝒳 M).hom ≫
        ((fppfModulesSmallModelEquivalence B S hS 𝒳).functor ⋙
          Stacks.Cohomology.CompareTopologies.pushforward (etaleSmallModelTopology_le B S hS 𝒳)
            (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O)).map f := by
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  ext U x
  rfl

/-- **`ε_*` commutes with the transport to the small model.** Both composites read a module on
`𝒳_fppf` on the étale site of the small model by pushing its underlying presheaf of modules
forward along the model equivalence. -/
def smallModelPushforwardSquareIso :
    fppfToEtaleModules B S hS 𝒳 ⋙ (etaleModulesSmallModelEquivalence B S hS 𝒳).functor ≅
      (fppfModulesSmallModelEquivalence B S hS 𝒳).functor ⋙
        Stacks.Cohomology.CompareTopologies.pushforward (etaleSmallModelTopology_le B S hS 𝒳)
          (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O) :=
  NatIso.ofComponents (smallModelPushforwardSquareObjIso B S hS 𝒳)
    (smallModelPushforwardSquareObjIso_naturality B S hS 𝒳)

/-! ### `ε^*` commutes with the transport -/

/-- Sheafification of abelian presheaves exists on each site of an algebraic stack: the site is
essentially small. -/
theorem hasSheafify_associatedTopology_algebraicStack (τ : SiteKind) :
    HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

/-- On each site of an algebraic stack the sheafification of abelian presheaves inverts exactly
the locally bijective morphisms: the site is essentially small. -/
theorem wEqualsLocallyBijective_associatedTopology_algebraicStack (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance] hasSheafify_associatedTopology_algebraicStack
  wEqualsLocallyBijective_associatedTopology_algebraicStack

/-- The square of right adjoints, read with the quasi-inverses of the transports: the étale
transport after `ε_*` of the small model is `ε_*` after the fppf transport. -/
def smallModelPushforwardInverseSquareIso :
    Stacks.Cohomology.CompareTopologies.pushforward (etaleSmallModelTopology_le B S hS 𝒳)
          (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O) ⋙
        (etaleModulesSmallModelEquivalence B S hS 𝒳).inverse ≅
      (fppfModulesSmallModelEquivalence B S hS 𝒳).inverse ⋙ fppfToEtaleModules B S hS 𝒳 :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (fppfModulesSmallModelEquivalence B S hS 𝒳).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (smallModelPushforwardSquareIso B S hS 𝒳).symm _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (etaleModulesSmallModelEquivalence B S hS 𝒳).unitIso.symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

/-- **`ε^*` commutes with the transport to the small model.** The two composites are left adjoint
to the two sides of `smallModelPushforwardInverseSquareIso`. -/
def smallModelPullbackSquareIso :
    epsilonPullback B S hS 𝒳 ⋙ (fppfModulesSmallModelEquivalence B S hS 𝒳).functor ≅
      (etaleModulesSmallModelEquivalence B S hS 𝒳).functor ⋙
        Stacks.Cohomology.CompareTopologies.pullback (etaleSmallModelTopology_le B S hS 𝒳)
          (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O) :=
  Adjunction.leftAdjointUniq
    ((epsilonAdjunction B S hS 𝒳).comp (fppfModulesSmallModelEquivalence B S hS 𝒳).toAdjunction)
    (((etaleModulesSmallModelEquivalence B S hS 𝒳).toAdjunction.comp
        (Stacks.Cohomology.CompareTopologies.adjunction (etaleSmallModelTopology_le B S hS 𝒳)
          (Stacks.SheafOfModules.Tensor.ringSheaf (fppfSmallModel B S hS 𝒳).O))).ofNatIsoRight
      (smallModelPushforwardInverseSquareIso B S hS 𝒳))

end AlgebraicGeometry.Stack

end
