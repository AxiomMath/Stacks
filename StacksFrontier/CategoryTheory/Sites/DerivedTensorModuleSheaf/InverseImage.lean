module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Transport
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensorNaturality

/-!
# The derived tensor product and inverse image along a morphism of sites

Let `G : C ⥤ D` be a continuous functor of sites whose comma categories are cofiltered (for
instance a functor preserving finite limits), and let `Λ` be a commutative ring. The inverse image
`G⁻¹` of sheaves of `Λ`-modules commutes with the derived tensor product of an arbitrary object
`K` with a bounded above object `L`, `G⁻¹(K ⊗_Λ^L L) ≅ G⁻¹K ⊗_Λ^L G⁻¹L`, and so with its
cohomology sheaves.

## Main results

* `Stacks.ModuleSheaf.sheafifiedFree_sheafPullback_obj`: inverse image carries a sheafified
  presheaf of free modules to a sheafified presheaf of free modules.
* `Stacks.ModuleSheaf.nonempty_homology_sheafPullback_tensor_iso`: the comparison of the cohomology
  sheaves of the derived tensor products.

## References

* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t t' w v u

namespace Stacks.ModuleSheaf

open Stacks.InverseImageTensor

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (G : C ⥤ D) (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]
  (J : GrothendieckTopology C) (J' : GrothendieckTopology D) [G.IsContinuous J J']
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) (ModuleCat.{w} Λ)]
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) (Type w)]
  [(G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J J').IsRightAdjoint]

/-- Inverse image of sheaves of `Λ`-modules is additive. -/
instance additive_sheafPullback : (G.sheafPullback (ModuleCat.{w} Λ) J J').Additive := by
  have hadj := G.sheafAdjunctionContinuous (ModuleCat.{w} Λ) J J'
  have : (G.sheafPullback (ModuleCat.{w} Λ) J J').IsLeftAdjoint := ⟨_, ⟨hadj⟩⟩
  have := hadj.leftAdjoint_preservesColimits
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (G.sheafPullback (ModuleCat.{w} Λ) J J')
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (G.sheafPullback (ModuleCat.{w} Λ) J J')
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Inverse image of sheaves of `Λ`-modules commutes with colimits. -/
instance preservesColimitsOfSize_sheafPullback :
    PreservesColimitsOfSize.{0, 0} (G.sheafPullback (ModuleCat.{w} Λ) J J') :=
  (G.sheafAdjunctionContinuous (ModuleCat.{w} Λ) J J').leftAdjoint_preservesColimits

/-- Inverse image of sheaves of `Λ`-modules is right exact. -/
instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits (G.sheafPullback (ModuleCat.{w} Λ) J J') :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Left Kan extension of presheaves commutes with the free module functor. -/
def lanFreeIso (S : Cᵒᵖ ⥤ Type w) :
    G.op.lan.obj (S ⋙ ModuleCat.free Λ) ≅ G.op.lan.obj S ⋙ ModuleCat.free Λ :=
  have := (ModuleCat.adj.{w} Λ).leftAdjoint_preservesColimits
  ((Functor.lanCompIsoOfPreserves (ModuleCat.free Λ) G.op).app S).symm

omit [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) (Type w)] in
variable {G Λ J J'} in
/-- **Inverse image carries a sheafified presheaf of free modules to a sheafified presheaf of free
modules**: the inverse image of the sheafification of `U ↦ Λ[S(U)]` is the sheafification of the
presheaf of free modules on the left Kan extension of `S`. -/
theorem sheafifiedFree_sheafPullback_obj {M : Sheaf J (ModuleCat.{w} Λ)}
    (hM : sheafifiedFree J Λ M) :
    sheafifiedFree J' Λ ((G.sheafPullback (ModuleCat.{w} Λ) J J').obj M) := by
  obtain ⟨S, ⟨e⟩⟩ := hM
  exact ⟨G.op.lan.obj S, ⟨(presheafToSheaf J' (ModuleCat.{w} Λ)).mapIso (lanFreeIso G Λ S).symm ≪≫
    ((sheafifyCompPullbackIso G Λ J J').app (S ⋙ ModuleCat.free Λ)).symm ≪≫
    (G.sheafPullback (ModuleCat.{w} Λ) J J').mapIso e⟩⟩

variable [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]

omit [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) (Type w)] in
/-- **Inverse image along a continuous functor of sites whose comma categories are cofiltered
commutes with the cohomology sheaves of the derived tensor product** of an arbitrary object with
a bounded above object:
`G⁻¹Hⁿ(K ⊗_Λ^L L) ≅ Hⁿ(G⁻¹K ⊗_Λ^L G⁻¹L)`. -/
theorem nonempty_homology_sheafPullback_tensor_iso
    [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
    [HasDerivedCategory.{t'} (Sheaf J' (ModuleCat.{w} Λ))]
    [PreservesFiniteLimits (G.sheafPullback (ModuleCat.{w} Λ) J J')]
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (b : ℤ) [L.IsLE b] (n : ℤ) :
    Nonempty ((G.sheafPullback (ModuleCat.{w} Λ) J J').obj
        ((DerivedCategory.homologyFunctor _ n).obj (K ⊗ L)) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        ((G.sheafPullback (ModuleCat.{w} Λ) J J').mapDerivedCategory.obj K ⊗
          (G.sheafPullback (ModuleCat.{w} Λ) J J').mapDerivedCategory.obj L)) :=
  nonempty_homology_mapDerivedCategory_tensor_iso.{t, t', w, v, u, v, u}
    (G.sheafPullback (ModuleCat.{w} Λ) J J') (sheafPullbackTensorIso G Λ J J')
    (sheafPullbackTensorIso_naturality_left G Λ J J')
    (fun M _ _ g => sheafPullbackTensorIso_naturality_right G Λ J J' M g)
    (fun _ hM => sheafifiedFree_sheafPullback_obj hM) K L b n

end Stacks.ModuleSheaf
