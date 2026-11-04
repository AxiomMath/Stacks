module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Transport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product and restriction to a slice site

Let `(C, J)` be a site, `Λ` a commutative ring and `V` an object of `C`. Restriction of sheaves of
`Λ`-modules to the slice site `C/V` commutes with the derived tensor product of an arbitrary
object `K` with a bounded above object `L`: `(K ⊗_Λ^L L)|_V ≅ K|_V ⊗_Λ^L L|_V`, and so with its
cohomology sheaves.

## Main results

* `Stacks.ModuleSheaf.sheafifiedFree_overPullback_obj`: restriction to `C/V` carries a sheafified
  presheaf of free modules to a sheafified presheaf of free modules.
* `Stacks.ModuleSheaf.nonempty_homology_overPullback_tensor_iso`: the comparison of cohomology
  sheaves, `Hⁿ(K ⊗_Λ^L L)|_V ≅ Hⁿ(K|_V ⊗_Λ^L L|_V)`.

## Implementation notes

Restriction to `C/V` is exact, commutes with colimits (it is the left adjoint of
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`, `Over.forget V` being cocontinuous), and is
monoidal (`Stacks.ConstantSheaf.overPullbackMonoidal`); it commutes with sheafification and
restricting the presheaf `U ↦ Λ[S(U)]` gives the presheaf of free modules on the restriction of
`S`, so `Stacks.ModuleSheaf.nonempty_homology_mapDerivedCategory_tensor_iso_of_monoidal` applies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t t' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}] (V : C)

/-- Restriction of sheaves of modules to a slice site commutes with colimits: it is the left
adjoint of the coinduction along the cocontinuous functor `Over.forget V`. -/
@[ega "0 4.3.2" "partial"]
instance preservesColimitsOfSize_overPullback :
    PreservesColimitsOfSize.{0, 0} (J.overPullback (ModuleCat.{w} Λ) V) :=
  ((Over.forget V).sheafAdjunctionCocontinuous (ModuleCat.{w} Λ)
    (J.over V) J).leftAdjoint_preservesColimits

/-- Restriction of sheaves of modules to a slice site is right exact. -/
instance preservesFiniteColimits_overPullback :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) V) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restriction of sheaves of modules to a slice site is left exact: on underlying presheaves it
is restriction of presheaves, which commutes with limits, and the forgetful functor from sheaves
to presheaves preserves and reflects finite limits. -/
@[sga "4 IV 11.2.2" "special case"]
instance preservesFiniteLimits_overPullback :
    PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) V) := by
  have : PreservesFiniteLimits
      (J.overPullback (ModuleCat.{w} Λ) V ⋙ sheafToPresheaf (J.over V) (ModuleCat.{w} Λ)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J (ModuleCat.{w} Λ) ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (J.over V) (ModuleCat.{w} Λ))

variable {J Λ V} in
/-- Restriction to a slice site carries a sheafified presheaf of free modules to a sheafified
presheaf of free modules: restriction commutes with sheafification. -/
theorem sheafifiedFree_overPullback_obj {M : Sheaf J (ModuleCat.{w} Λ)}
    (hM : sheafifiedFree J Λ M) :
    sheafifiedFree (J.over V) Λ ((J.overPullback (ModuleCat.{w} Λ) V).obj M) := by
  obtain ⟨S, ⟨e⟩⟩ := hM
  exact ⟨(Over.forget V).op ⋙ S, ⟨((Over.forget V).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{w} Λ) (J.over V) J).app (S ⋙ ModuleCat.free Λ) ≪≫
      (J.overPullback (ModuleCat.{w} Λ) V).mapIso e⟩⟩

/-- The monoidal structure of restriction to a slice site. -/
@[instance_reducible]
def overPullbackMonoidal : (J.overPullback (ModuleCat.{w} Λ) V).Monoidal :=
  haveI : ∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} Λ) := fun U =>
    Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE (J.over U) Λ
  Stacks.ConstantSheaf.overPullbackMonoidal J (ModuleCat.{w} Λ) V

variable {J Λ} in
/-- **Restriction to a slice site commutes with the cohomology sheaves of the derived tensor
product** of an arbitrary object with a bounded above object:
`Hⁿ(K ⊗_Λ^L L)|_V ≅ Hⁿ(K|_V ⊗_Λ^L L|_V)`. -/
theorem nonempty_homology_overPullback_tensor_iso
    [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
    [HasDerivedCategory.{t'} (Sheaf (J.over V) (ModuleCat.{w} Λ))]
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (b : ℤ) [L.IsLE b] (n : ℤ) :
    Nonempty ((J.overPullback (ModuleCat.{w} Λ) V).obj
        ((DerivedCategory.homologyFunctor _ n).obj (K ⊗ L)) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        ((J.overPullback (ModuleCat.{w} Λ) V).mapDerivedCategory.obj K ⊗
          (J.overPullback (ModuleCat.{w} Λ) V).mapDerivedCategory.obj L)) :=
  let := overPullbackMonoidal J Λ V
  nonempty_homology_mapDerivedCategory_tensor_iso_of_monoidal.{t, t', w, v, u, v, max u v}
    (J.overPullback (ModuleCat.{w} Λ) V) (fun _ hM => sheafifiedFree_overPullback_obj hM)
    K L b n

end Stacks.ModuleSheaf
