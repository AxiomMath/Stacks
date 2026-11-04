module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedBiduality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw

/-!
# The biduality morphism over an affine open, read on `Spec Γ(X, V)`

Let `X` be a scheme, `V ⊆ X` an affine open and `K`, `L` objects of `D(𝒪_X)`. The biduality
morphism `L ⟶ R𝓗om(R𝓗om(L, K), K)` of [Stacks, Tag 0A89], restricted to the slice site
`Opens(X)/V`, is carried along the two equivalences `overEquiv V` (from the slice site to the open
subscheme `V`) and the pullback along `V ≅ Spec Γ(X, V)`, each of which carries the derived tensor
product to the derived tensor product naturally in both variables. So if `K|_V` and `L|_V` are the
complexes associated to objects `ω`, `M` of `D(Γ(X, V))`, the restricted biduality morphism is an
isomorphism exactly when the biduality morphism of `ω̃`, `M̃` on `Spec Γ(X, V)` is one.

## Main results

* `Stacks.Duality.isIso_derivedBiduality_restrictD_iff_of_models`: the comparison above.
* `Stacks.Duality.isIso_derivedBiduality_of_affineModels`: invertibility of the biduality morphism
  on `X` from its invertibility on `Spec Γ(X, V)` at models over every affine open `V`.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace Stacks.SheafOfModules

section RingedSpace

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The commutativity constraint `A ⊗^𝐋 B ≅ B ⊗^𝐋 A` of the derived tensor product of a ringed
space, the braiding of `Stacks.SheafOfModules.derivedSymmetricStructure`. -/
def derivedTensorBraiding (A B : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj A).obj B ≅ ((derivedTensor Rc).obj B).obj A :=
  letI := derivedMonoidalStructure Rc
  letI := derivedSymmetricStructure Rc
  β_ A B

/-- Naturality of the commutativity constraint `A ⊗^𝐋 B ≅ B ⊗^𝐋 A` in its second variable. -/
theorem derivedTensorBraiding_naturality_right (A : DerivedCategory (StructureSheafModules Rc))
    {B B' : DerivedCategory (StructureSheafModules Rc)} (g : B ⟶ B') :
    ((derivedTensor Rc).obj A).map g ≫ (derivedTensorBraiding Rc A B').hom =
      (derivedTensorBraiding Rc A B).hom ≫ ((derivedTensor Rc).map g).app A := by
  let := derivedMonoidalStructure Rc
  let := derivedSymmetricStructure Rc
  exact BraidedCategory.braiding_naturality_right A g

/-- Naturality of the commutativity constraint `A ⊗^𝐋 B ≅ B ⊗^𝐋 A` in its first variable. -/
theorem derivedTensorBraiding_naturality_left {A A' : DerivedCategory (StructureSheafModules Rc)}
    (f : A ⟶ A') (B : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).map f).app B ≫ (derivedTensorBraiding Rc A' B).hom =
      (derivedTensorBraiding Rc A B).hom ≫ ((derivedTensor Rc).obj B).map f := by
  let := derivedMonoidalStructure Rc
  let := derivedSymmetricStructure Rc
  exact BraidedCategory.braiding_naturality_left f B

/-- **The biduality morphism** `L ⟶ R𝓗om(R𝓗om(L, K), K)` of a ringed space, [Stacks, Tag 0A89]:
the transpose under [Stacks, Tag 08DI] of evaluation after the commutativity constraint. -/
def derivedBiduality (K L : DerivedCategory (StructureSheafModules Rc)) :
    L ⟶ ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op L)).obj K))).obj K :=
  (derivedSheafHomTensorEquiv Rc L (((derivedSheafHom Rc).obj (op L)).obj K) K).symm
    ((derivedTensorBraiding Rc L _).hom ≫ derivedSheafHomCounit Rc L K)

/-- The defining identity of the biduality morphism of a ringed space. -/
theorem derivedBiduality_spec (K L : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).map (derivedBiduality Rc K L)).app
          (((derivedSheafHom Rc).obj (op L)).obj K) ≫
        derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op L)).obj K) K =
      (derivedTensorBraiding Rc L _).hom ≫ derivedSheafHomCounit Rc L K := by
  rw [derivedTensor_map_app_comp_derivedSheafHomCounit, derivedBiduality,
    AddEquiv.apply_symm_apply]

end RingedSpace

end Stacks.SheafOfModules


namespace Stacks.Duality

open Stacks.Cohomology.SliceDerivedSheafHom (restrictD)

/-- **The biduality morphism along the pullback by an isomorphism of schemes.** For an isomorphism
`f : X ⟶ Y`, the biduality morphism of `A`, `B` on `Y` is an isomorphism exactly when that of any
objects isomorphic to `f^*A`, `f^*B` on `X` is one. -/
theorem isIso_derivedBiduality_pullback_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (A B : DerivedCategory (StructureSheafModules Y.sheaf))
    {A' B' : DerivedCategory (StructureSheafModules X.sheaf)}
    (a : (PullbackIsoTensor.pullbackEquivMod f).functor.mapDerivedCategory.obj A ≅ A')
    (b : (PullbackIsoTensor.pullbackEquivMod f).functor.mapDerivedCategory.obj B ≅ B') :
    IsIso (derivedBiduality Y.sheaf A B) ↔
      IsIso (derivedBiduality X.sheaf A' B') :=
  CategoryTheory.BidualityTransfer.isIso_iff_of_equivalence
    (derivedTensor Y.sheaf) (derivedTensor X.sheaf)
    (derivedTensorBraiding Y.sheaf) (derivedTensorBraiding X.sheaf)
    (PullbackIsoTensor.pullbackDerivedEquivalence f)
    (fun A B => ((PullbackIsoTensor.pullbackDerivedTensorNatIso f).app A).app B)
    (fun g B =>
      NatTrans.congr_app ((PullbackIsoTensor.pullbackDerivedTensorNatIso f).hom.naturality g) B)
    (fun A _ _ g => ((PullbackIsoTensor.pullbackDerivedTensorNatIso f).hom.app A).naturality g)
    (fun L _ _ g => derivedTensorBraiding_naturality_right _ L g)
    (fun L _ _ g => derivedTensorBraiding_naturality_right _ L g)
    (fun g L => derivedTensorBraiding_naturality_left _ g L)
    (derivedSheafHomCounit _ B A)
    (fun Z => tensorHomBijective_derivedSheafHomCounit' _ B A Z)
    (derivedSheafHomCounit _ _ A)
    (fun Z => tensorHomBijective_derivedSheafHomCounit' _ _ A Z)
    (derivedBiduality _ A B) (derivedBiduality_spec _ A B)
    b a
    (derivedSheafHomCounit _ B' A')
    (fun Z => tensorHomBijective_derivedSheafHomCounit' _ B' A' Z)
    (derivedSheafHomCounit _ _ A')
    (fun Z => tensorHomBijective_derivedSheafHomCounit' _ _ A' Z)
    (derivedBiduality _ A' B') (derivedBiduality_spec _ A' B')

/-- **The biduality morphism along `overEquiv V`.** The biduality morphism of `A`, `B` on the slice
site `Opens(X)/V` is an isomorphism exactly when that of any objects isomorphic to their images on
the open subscheme `V` is one. -/
theorem isIso_derivedBiduality_overEquiv_iff (X : Scheme.{u}) (V : X.Opens)
    (A B : DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over V).O)))
    {A' B' : DerivedCategory (StructureSheafModules V.toScheme.sheaf)}
    (a : (OverEquivTensor.overEquivMod X V).functor.mapDerivedCategory.obj A ≅ A')
    (b : (OverEquivTensor.overEquivMod X V).functor.mapDerivedCategory.obj B ≅ B') :
    IsIso (RingedSite.derivedBiduality ((Stacks.SheafOfModules.ringedSite X.sheaf).over V) A B) ↔
      IsIso (derivedBiduality V.toScheme.sheaf A' B') :=
  CategoryTheory.BidualityTransfer.isIso_iff_of_equivalence
    (Stacks.SheafOfModules.derivedTensorProductFunctor
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over V))
    (derivedTensor V.toScheme.sheaf)
    (RingedSite.derivedTensorBraiding ((Stacks.SheafOfModules.ringedSite X.sheaf).over V))
    (derivedTensorBraiding V.toScheme.sheaf)
    (OverEquivTensor.overEquivDerivedEquivalence X V)
    (fun A B => ((OverEquivTensor.overEquivDerivedTensorNatIso X V).app A).app B)
    (fun g B => NatTrans.congr_app
      ((OverEquivTensor.overEquivDerivedTensorNatIso X V).hom.naturality g) B)
    (fun A _ _ g => ((OverEquivTensor.overEquivDerivedTensorNatIso X V).hom.app A).naturality g)
    (fun L _ _ g => RingedSite.derivedTensorBraiding_naturality_right _ L g)
    (fun L _ _ g => derivedTensorBraiding_naturality_right _ L g)
    (fun g L => derivedTensorBraiding_naturality_left _ g L)
    (RingedSite.derivedSheafHomCounit _ B A)
    (fun Z => RingedSite.tensorHomBijective_derivedSheafHomCounit _ B A Z)
    (RingedSite.derivedSheafHomCounit _ _ A)
    (fun Z => RingedSite.tensorHomBijective_derivedSheafHomCounit _ _ A Z)
    (RingedSite.derivedBiduality _ A B) (RingedSite.derivedBiduality_spec _ A B)
    b a
    (derivedSheafHomCounit _ B' A')
    (fun Z => tensorHomBijective_derivedSheafHomCounit' _ B' A' Z)
    (derivedSheafHomCounit _ _ A')
    (fun Z => tensorHomBijective_derivedSheafHomCounit' _ _ A' Z)
    (derivedBiduality _ A' B') (derivedBiduality_spec _ A' B')

/-- **The restricted biduality morphism, read on `Spec Γ(X, V)`.** If the restrictions of `K` and
`L` to the affine open `V`, transported to the open subscheme, are the complexes associated to
`ω` and `M` (transported along `V ≅ Spec Γ(X, V)`), then the biduality morphism of `K|_V`, `L|_V`
on the slice site is an isomorphism exactly when the biduality morphism of `ω̃`, `M̃` on
`Spec Γ(X, V)` is one. -/
theorem isIso_derivedBiduality_restrictD_iff_of_models {X : Scheme.{u}} (V : X.Opens)
    (hV : IsAffineOpen V) (K L : DerivedCategory X.Modules)
    {ω M : DerivedCategory (ModuleCat.{u} Γ(X, V))}
    (iK : ((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf V).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(X, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω)
    (iL : ((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf V).mapDerivedCategory.obj L) ≅
      (tilde.functor Γ(X, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj M) :
    IsIso (RingedSite.derivedBiduality ((ringedSite X.sheaf).over V)
        ((restrictD (ringedSite X.sheaf) V).obj K) ((restrictD (ringedSite X.sheaf) V).obj L)) ↔
      IsIso (derivedBiduality (Spec Γ(X, V)).sheaf
        ((derivedTildeStructureSheafModules Γ(X, V)).obj ω)
        ((derivedTildeStructureSheafModules Γ(X, V)).obj M)) := by
  have e (N : DerivedCategory (ModuleCat.{u} Γ(X, V))) :=
    (Dualizing.mapDerivedCategoryComp (tilde.functor Γ(X, V))
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom)).app N ≪≫
    (PullbackIsoTensor.restrictFunctorDerivedIsoPullback hV.isoSpec.hom).app
      ((derivedTildeStructureSheafModules Γ(X, V)).obj N)
  exact (isIso_derivedBiduality_overEquiv_iff X V ((restrictD (ringedSite X.sheaf) V).obj K)
    ((restrictD (ringedSite X.sheaf) V).obj L) (iK ≪≫ e ω) (iL ≪≫ e M)).trans
    (isIso_derivedBiduality_pullback_iff hV.isoSpec.hom _ _ (Iso.refl _) (Iso.refl _)).symm

/-- **Invertibility of the biduality morphism from affine models.** If over every affine open `V`
the objects `K` and `L` have models `ω`, `M` over `Γ(X, V)` at which the biduality morphism on
`Spec Γ(X, V)` is an isomorphism, then the biduality morphism of `K`, `L` on `X` is an
isomorphism. -/
theorem isIso_derivedBiduality_of_affineModels {X : Scheme.{u}} (K L : DerivedCategory X.Modules)
    (h : ∀ (V : X.Opens) (hV : IsAffineOpen V), ∃ ω M : DerivedCategory (ModuleCat.{u} Γ(X, V)),
      Nonempty (((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf V).mapDerivedCategory.obj K) ≅
        (tilde.functor Γ(X, V) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω) ∧
      Nonempty (((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf V).mapDerivedCategory.obj L) ≅
        (tilde.functor Γ(X, V) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj M) ∧
      IsIso (derivedBiduality (Spec Γ(X, V)).sheaf
        ((derivedTildeStructureSheafModules Γ(X, V)).obj ω)
        ((derivedTildeStructureSheafModules Γ(X, V)).obj M))) :
    IsIso (RingedSite.derivedBiduality (ringedSite X.sheaf) K L) := by
  have hY : (Stacks.SheafOfModules.ringedSite X.sheaf).J.CoversTop
      (fun V : X.affineOpens => (V : X.Opens)) :=
    (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X))
  refine Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedBiduality_of_cover _ hY K L
    fun V => ?_
  obtain ⟨ω, M, ⟨iK⟩, ⟨iL⟩, hb⟩ := h V V.2
  exact (isIso_derivedBiduality_restrictD_iff_of_models (V : X.Opens) V.2 K L iK iL).2 hb

end Stacks.Duality
