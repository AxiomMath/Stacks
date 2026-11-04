module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative flat locus of a sheaf of modules

For a morphism of schemes `f : X ⟶ S` and an `𝒪_X`-module `F`, the *flat locus* of `F` over
`S` is the set of points of `X` at which the stalk of `F` is flat over the local ring of `S`
at the image point. Flatness at a point only depends on the stalk, so the locus is unchanged by
restriction along an open immersion; in particular the restriction of `F` to any open contained
in the flat locus is flat over `S`.

## Main definitions

* `AlgebraicGeometry.flatLocus` is the locus of relative flatness of `F`.

## Main results

* `AlgebraicGeometry.isFlatOverAt_restrict_iff`: relative flatness at a point is unchanged by
  restriction along an open immersion of the source.
* `AlgebraicGeometry.isFlatOver_restrict_of_subset_flatLocus`: the restriction to an open part
  of the flat locus is flat over the base.

## Implementation notes

Relative flatness at a point is `AlgebraicGeometry.IsFlatOverAt` for the underlying morphism of
sheafed spaces. The comparison of the stalk of a module with the stalk of its restriction along
an open immersion is `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`; the scalar
compatibility of that comparison is proved here, since the natural isomorphism is one of abelian
sheaves and carries no module structure on the nose.

## References

* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The comparison map from the stalk of the restriction of `F` along an open immersion to the
stalk of `F` at the image point. -/
noncomputable def restrictStalkMap {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) :
    (F.restrict j).presheaf.stalk w ⟶ F.presheaf.stalk (j w) :=
  (Scheme.Modules.restrictStalkNatIso j w).hom.app F

/-- `restrictStalkMap` sends the germ of a section of the restriction to the germ of the
corresponding section of `F` on the image open. -/
private theorem restrictStalkMap_germ {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {w : W} {T : W.Opens} (hT : w ∈ T) (t : Γ(F.restrict j, T)) :
    restrictStalkMap j F w ((F.restrict j).presheaf.germ T w hT t) =
      F.presheaf.germ (j ''ᵁ T) (j w) ⟨w, hT, rfl⟩ ((F.restrictAppIso j T).hom t) := by
  have h := congrArg (fun z : Γ(F.restrict j, T) ⟶ F.presheaf.stalk (j w) => z t)
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app j w F hT)
  exact h

/-- The comparison map `restrictStalkMap` is semilinear over the stalk map of `j`. -/
theorem restrictStalkMap_smul {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) (a : X.presheaf.stalk (j w))
    (m : (F.restrict j).presheaf.stalk w) :
    restrictStalkMap j F w ((j.stalkMap w).hom a • m) = a • restrictStalkMap j F w m := by
  let G := F.restrict j
  obtain ⟨V, hV, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨T, hT, t, rfl⟩ := G.presheaf.exists_germ_eq m
  let T' : W.Opens := T ⊓ j ⁻¹ᵁ V
  have hT' : w ∈ T' := ⟨hT, hV⟩
  let r' : Γ(W, T') := W.presheaf.map (homOfLE inf_le_right).op (j.app V r)
  let t' : Γ(G, T') := G.presheaf.map (homOfLE inf_le_left).op t
  let J : X.Opens := j ''ᵁ T'
  have hJ : j w ∈ J := ⟨w, hT', rfl⟩
  have hJV : J ≤ V := by
    rintro x ⟨z, hz, rfl⟩
    exact hz.2
  let rJ : Γ(X, J) := X.presheaf.map (homOfLE hJV).op r
  have hr : (j.stalkMap w).hom (X.presheaf.germ V (j w) hV r) =
      W.presheaf.germ T' w hT' r' := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (W.presheaf.germ_res_apply (homOfLE inf_le_right) w hT' (j.app V r)).symm
  have hm : G.presheaf.germ T w hT t = G.presheaf.germ T' w hT' t' :=
    (G.presheaf.germ_res_apply (homOfLE inf_le_left) w hT' t).symm
  have hrJ : X.presheaf.germ V (j w) hV r = X.presheaf.germ J (j w) hJ rJ :=
    (X.presheaf.germ_res_apply (homOfLE hJV) (j w) hJ r).symm
  have hscalar : (j.appIso T').inv r' = rJ := by
    have h := congrArg (fun z : Γ(X, V) ⟶ Γ(X, J) => z r)
      (Scheme.Hom.appLE_appIso_inv j (inf_le_right : T' ≤ j ⁻¹ᵁ V))
    exact h
  let eT : Γ(G, T') ≅ Γ(F, J) := F.restrictAppIso j T'
  let tF : Γ(F, J) := eT.hom t'
  have hsection : eT.hom (r' • t') = rJ • tF := by
    have h := Scheme.Modules.smul_restrictAppIso_hom_apply j F T' r' t'
    change eT.hom (r' • t') = (j.appIso T').inv r' • tF at h
    rw [hscalar] at h
    exact h
  rw [hr, hm, hrJ]
  calc
    _ = restrictStalkMap j F w (G.presheaf.germ T' w hT' (r' • t')) := by
      have hG : W.presheaf.germ T' w hT' r' • G.presheaf.germ T' w hT' t' =
          G.presheaf.germ T' w hT' (r' • t') :=
        (PresheafOfModules.germ_smul G.val w T' hT' r' t').symm
      exact congrArg (restrictStalkMap j F w) hG
    _ = F.presheaf.germ J (j w) hJ (eT.hom (r' • t')) :=
      restrictStalkMap_germ j F hT' (r' • t')
    _ = F.presheaf.germ J (j w) hJ (rJ • tF) := by rw [hsection]
    _ = X.presheaf.germ J (j w) hJ rJ • F.presheaf.germ J (j w) hJ tF :=
      PresheafOfModules.germ_smul F.val (j w) J hJ rJ tF
    _ = _ := by
      have h' : F.presheaf.germ J (j w) hJ tF =
          restrictStalkMap j F w (G.presheaf.germ T' w hT' t') :=
        (restrictStalkMap_germ j F hT' t').symm
      exact congrArg (fun z => X.presheaf.germ J (j w) hJ rJ • z) h'

/-- Relative flatness at a point is unchanged by restriction along an open immersion. -/
theorem isFlatOverAt_restrict_iff {W X S : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) (F : X.Modules) (w : W) :
    IsFlatOverAt (j ≫ f).toLRSHom.toShHom (F.restrict j) w ↔
      IsFlatOverAt f.toLRSHom.toShHom F (j w) := by
  let G := F.restrict j
  let _ : Module (S.presheaf.stalk (f (j w))) (G.presheaf.stalk w) :=
    Module.compHom _ ((j ≫ f).stalkMap w).hom
  let _ : Module (S.presheaf.stalk (f (j w))) (F.presheaf.stalk (j w)) :=
    Module.compHom _ (f.stalkMap (j w)).hom
  have hsmul (a : S.presheaf.stalk (f (j w))) (m : G.presheaf.stalk w) :
      restrictStalkMap j F w (a • m) = a • restrictStalkMap j F w m := by
    show restrictStalkMap j F w (((j ≫ f).stalkMap w).hom a • m) =
      (f.stalkMap (j w)).hom a • restrictStalkMap j F w m
    rw [Scheme.Hom.stalkMap_comp]
    exact restrictStalkMap_smul j F w ((f.stalkMap (j w)).hom a) m
  have _ : IsIso (restrictStalkMap j F w) :=
    ((Scheme.Modules.restrictStalkNatIso j w).app F).isIso_hom
  let e : G.presheaf.stalk w ≃ₗ[S.presheaf.stalk (f (j w))] F.presheaf.stalk (j w) :=
    LinearEquiv.ofBijective
      { toFun := restrictStalkMap j F w
        map_add' := (restrictStalkMap j F w).hom.map_add
        map_smul' := hsmul }
      (ConcreteCategory.bijective_of_isIso (restrictStalkMap j F w))
  show Module.Flat (S.presheaf.stalk (f (j w))) (G.presheaf.stalk w) ↔
    Module.Flat (S.presheaf.stalk (f (j w))) (F.presheaf.stalk (j w))
  exact Module.Flat.equiv_iff e

/-- The locus where `F` is flat over the target of `f`. -/
abbrev flatLocus {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Set X :=
  {x | IsFlatOverAt f.toLRSHom.toShHom F x}

/-- The restriction of a module to an open contained in its relative flat locus is flat over
the base. -/
theorem isFlatOver_restrict_of_subset_flatLocus {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (U : X.Opens) (hU : (U : Set X) ⊆ flatLocus f F) :
    IsFlatOver (U.ι ≫ f).toLRSHom.toShHom (F.restrict U.ι) :=
  fun x => (isFlatOverAt_restrict_iff U.ι f F x).mpr (hU x.2)

end AlgebraicGeometry
