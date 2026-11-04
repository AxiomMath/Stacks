module

public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteLiftedCartesian

/-!
# Cartesian presheaves of modules on a site of affine schemes, over isomorphic rings

Let `L : C ⥤ Scheme` be a functor with affine values, preserving fibre products, on a category
with fibre products, and let `J` be a topology on `C` which is flatly cofinal for `L`
(`Stacks.AffineSiteBaseChange.IsFlatCofinal`). A cartesian presheaf of modules over the global
functions `Γ ∘ L` is a sheaf (`Stacks.AffineSiteBaseChange.isSheaf_of_isCartesianPresheaf`). This
file proves the same for a presheaf of modules over any presheaf of rings `R` isomorphic to
`Γ ∘ L`, the base change comparisons `R(Y) ⊗_{R(X)} M(X) ⟶ M(Y)` of its restriction maps being
isomorphisms (`Stacks.AffineSiteBaseChange.isSheaf_of_isIso_restrictionBaseChange_of_iso`): the
two conditions on the rings in the descent argument, faithful flatness of finite flat coverings
and the pushout property of fibre products, are carried along the isomorphism.

This is the form in which descent applies to a presheaf of modules on a site equivalent to a
site of affine schemes, over the rings of that site rather than over `Γ ∘ L` itself, as for the
small étale site of an algebraic space and its model in a smaller universe.

## Main results

* `Stacks.AffineSiteBaseChange.isSheaf_of_isIso_restrictionBaseChange_of_iso`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u v w

namespace Stacks.AffineSiteBaseChange

open _root_.AlgebraicGeometry

variable {C : Type v} [Category.{w} C] [HasPullbacks C] (L : C ⥤ Scheme.{u})
  [PreservesLimitsOfShape WalkingCospan L] [∀ X, IsAffine (L.obj X)]

/-- **A presheaf of modules over a presheaf of rings isomorphic to `Γ ∘ L`, whose restriction maps
have bijective base change comparisons, is a sheaf on a flatly cofinal site of affine schemes.**
-/
theorem isSheaf_of_isIso_restrictionBaseChange_of_iso {J : GrothendieckTopology C}
    (hJ : IsFlatCofinal L J) {R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : rings L ≅ R)
    (M : PresheafOfModules.{max t u} (R ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, t} M f)) :
    Presheaf.IsSheaf J M.presheaf := by
  have : ∀ Y : Cᵒᵖ, IsAffine (unop (L.op.obj Y)) := fun Y =>
    (inferInstance : IsAffine (L.obj Y.unop))
  have hmap : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      R.map f = φ.inv.app X ≫ (rings L).map f ≫ φ.hom.app Y := fun f => by
    rw [φ.hom.naturality f, Iso.inv_hom_id_app_assoc]
  refine Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'.{u, v, u, t, w, 0}
    L R ?_ ?_ M hM J ?_
  · intro U E hfin hE
    obtain ⟨hcover, hflat⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hE
    let _ (i : E.I₀) : Flat (L.map (E.f i)) := hflat i
    have hΓ := Scheme.faithfullyFlat_pi_appTop (fun i => L.obj (E.X i)) (fun i => L.map (E.f i))
      hcover
    convert RingHom.FaithfullyFlat.respectsIso.2 _ (φ.app (op U)).symm.commRingCatIsoToRingEquiv
      (RingHom.FaithfullyFlat.respectsIso.1 _
        (RingEquiv.piCongrRight fun i => (φ.app (op (E.X i))).commRingCatIsoToRingEquiv) hΓ)
      using 1
    ext r i
    exact ConcreteCategory.congr_hom (hmap (E.f i).op) r
  · intro X Y Z P fst snd a b h
    exact (isPushout_appTop_of_isPullback (Functor.map_isPullback L h)).of_iso (φ.app (op Z))
      (φ.app (op X)) (φ.app (op Y)) (φ.app (op P)) (φ.hom.naturality a.op)
      (φ.hom.naturality b.op) (φ.hom.naturality fst.op) (φ.hom.naturality snd.op)
  · intro V S hS
    obtain ⟨E, hfin, hE, hES, -⟩ := hJ V S hS
    exact ⟨E, hfin, hE, hES⟩

end Stacks.AffineSiteBaseChange

end
