module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a homomorphism of stalks to an open neighbourhood

A homomorphism from the stalk of a finitely presented sheaf of modules on a ringed space to the
stalk of any sheaf of modules is induced by a homomorphism of the restrictions to some open
neighbourhood of the point.

## Main results

* `Stacks.SheafOfModules.SheafHomStalk.exists_localHom_of_stalkLinearMap` extends a map of
  stalks to a morphism between the restrictions on a neighbourhood.

## Implementation notes

The equality of stalk maps is stated on germs of sections over all smaller open neighbourhoods.
That identifies the induced map without choosing an isomorphism between the stalk of a
restricted module and the original stalk.

The locally Noetherian and coherence hypotheses of the source imply finite presentation of the
source module, which is the only property the argument uses. The proof reads the given stalk map
as a germ of the internal hom, which is legitimate because the canonical map from the stalk of
the internal hom to the module of maps of stalks is an isomorphism for a finitely presented
source. The internal hom is packaged as a `SheafHom`, whose section identifications are the
internal-hom presheaf of a ringed space together with its two naturality properties.

## References

* [Stacks Project, Tag 01Y4](https://stacks.math.columbia.edu/tag/01Y4)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.SheafHomStalk

/-- The internal hom of two sheaves of modules on a ringed space, packaged as a `SheafHom`:
its underlying object is the internal-hom presheaf of Tag 03EM, which is a sheaf because the
target is, and its section identifications and naturality properties hold by definition of that
presheaf. -/
public noncomputable def internalSheafHom
    (X : TopCat.{u}) (Rc : TopCat.Sheaf CommRingCat.{u} X)
    (F G : SheafOfModules.{u} (structureSheaf Rc)) : SheafHom Rc F G where
  obj :=
    { val := internalHom Rc.obj F.val G.val
      isSheaf := internalHom_isSheaf Rc.obj F.val G.val G.isSheaf }
  sectionsEquiv U := by
    change ((restrFun Rc.obj U).obj F.val ⟶
      (restrFun Rc.obj U).obj G.val) ≃+ (F.over U ⟶ G.over U)
    let e : (F.over U ⟶ G.over U) ≃
        ((restrFun Rc.obj U).obj F.val ⟶ (restrFun Rc.obj U).obj G.val) :=
      (SheafOfModules.fullyFaithfulForget ((structureSheaf Rc).over U)).homEquiv
        (X := F.over U) (Y := G.over U)
    exact
      { toFun := e.symm
        invFun := e
        left_inv := e.apply_symm_apply
        right_inv := e.symm_apply_apply
        map_add' := by
          intro f g
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          rfl }
  restrict_natural := by
    intro U V hVU s W hWV m
    change ((homRestr Rc.obj F.val G.val (homOfLE hVU) s).app
      (op (Over.mk (homOfLE hWV)))) m = _
    rfl
  smul_natural := by
    intro U r s W hWU m
    change ((smulHom Rc.obj F.val G.val U r s).app
      (op (Over.mk (homOfLE hWU)))) m = _
    rfl

/-- **Stacks Project, Tag 01Y4.** A linear map out of the stalk of a finitely presented sheaf of
modules on a ringed space is represented by a homomorphism on some open neighbourhood. -/
@[stacks 01Y4]
theorem exists_localHom_of_stalkLinearMap (X : TopCat.{u})
    (Rc : TopCat.Sheaf CommRingCat.{u} X)
    (G F : SheafOfModules.{u} (structureSheaf Rc))
    [G.IsFinitePresentation] (x : X)
    (ψ : TopCat.Presheaf.stalk (C := Ab.{u})
        (commVal G).presheaf x →ₗ[TopCat.Presheaf.stalk
          (C := CommRingCat.{u}) Rc.obj x]
      TopCat.Presheaf.stalk (C := Ab.{u}) (commVal F).presheaf x) :
    ∃ (U : Opens X) (_hxU : x ∈ U) (φ : G.over U ⟶ F.over U),
      ∀ (V : Opens X) (hVU : V ≤ U) (hxV : x ∈ V) (m : G.val.obj (op V)),
        TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf V x hxV
            ((φ.val.app (op (Over.mk (homOfLE hVU)))) m) =
          ψ (TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf V x hxV m) := by
  let H : SheafHom Rc G F := internalSheafHom X Rc G F
  let e := sheafHomStalkLinearEquivOfFinitePresentation H x
  let t := e.equiv.symm ψ
  obtain ⟨U, hxU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq H.obj.val.presheaf t
  refine ⟨U, hxU, H.sectionsEquiv U s, fun V hVU hxV m => ?_⟩
  let sV := H.obj.val.map (homOfLE hVU).op s
  have hH : germAt H.obj V x hxV sV = germAt H.obj U x hxU s :=
    TopCat.Presheaf.germ_res_apply (commVal H.obj).presheaf (homOfLE hVU) x hxV s
  have ht : e.equiv (germAt H.obj U x hxU s) = ψ :=
    (congrArg e.equiv hs).trans (e.equiv.apply_symm_apply ψ)
  rw [H.restrict_natural hVU s (le_refl V) m]
  simp only [homOfLE_refl]
  show germAt F V x hxV ((H.sectionsEquiv V sV).val.app (op (Over.mk (𝟙 V))) m) =
    ψ (germAt G V x hxV m)
  rw [← e.germ_apply V hxV sV m, hH, ht]

end Stacks.SheafOfModules.SheafHomStalk
