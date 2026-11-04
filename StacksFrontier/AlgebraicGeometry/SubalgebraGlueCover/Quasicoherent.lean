module

public import StacksFrontier.AlgebraicGeometry.SubalgebraGlueCover.Sheaf
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealQcoh.Cover

/-!
# The glue of quasi-coherent subalgebras is quasi-coherent

Let `X` be a scheme, `A` a sheaf of commutative `𝒪_X`-algebras, `W : ι → X.Opens` a family of
opens and `C : ι → Subalg A` concrete subalgebras of `A` agreeing over the overlaps. This file
proves that `glue W C` is quasi-coherent as soon as each piece is and the family admits a
refinement by affine opens, each inside a member.

## Main definitions

* `valMap`: the comparison map of the sections of two concrete subalgebras over an open where they
  agree.
* `valMapOfLE`: the same comparison map at a smaller open, linear over the larger one.

## Main results

* `isLocalizedModule_of_obj_eq`: if two concrete subalgebras have the same sections over `U` and
  over `V ≤ U`, then the restriction map of the underlying module of one is a localization away
  from `a : Γ(X, U)` as soon as that of the other is.
* `isQuasicoherent_glue`: the glue of quasi-coherent pieces is quasi-coherent.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}} {A : AlgebraSheaf X}

/-! ### The comparison map at an open where two subalgebras agree -/

/-- The comparison map of the sections of two concrete subalgebras over an open `U` where they
agree, as a `Γ(X, U)`-linear map; it is the identity on underlying sections. -/
def valMap {C D : Subalg A} {U : X.Opens} (h : C.obj U = D.obj U) :
    Γ(AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C), U) →ₗ[Γ(X, U)]
      Γ(AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D), U) where
  toFun x := ⟨x.1, h ▸ x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The comparison map of the sections of two concrete subalgebras over a smaller open `V ≤ U`
where they agree, linear for the `Γ(X, U)`-module structures of
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE`. -/
def valMapOfLE {C D : Subalg A} {U V : X.Opens} (hVU : V ≤ U) (h : C.obj V = D.obj V) :
    letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU
    letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU
    Γ(AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C), V) →ₗ[Γ(X, U)]
      Γ(AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D), V) :=
  letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU
  letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU
  { toFun x := ⟨x.1, h ▸ x.2⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- The comparison map `valMap` is bijective. -/
theorem bijective_valMap {C D : Subalg A} {U : X.Opens} (h : C.obj U = D.obj U) :
    Function.Bijective (valMap (C := C) (D := D) h) :=
  ⟨fun x y e ↦ Subtype.ext (Subtype.ext_iff.mp e :), fun y ↦ ⟨⟨y.1, by rw [h]; exact y.2⟩, rfl⟩⟩

/-- The comparison map `valMapOfLE` is bijective. -/
theorem bijective_valMapOfLE {C D : Subalg A} {U V : X.Opens} (hVU : V ≤ U)
    (h : C.obj V = D.obj V) :
    Function.Bijective (valMapOfLE (C := C) (D := D) hVU h) :=
  bijective_valMap (U := V) h

/-- The comparison maps form a commuting square with the two restriction maps. -/
theorem valMap_comp_restrictₗ {C D : Subalg A} {U V : X.Opens} (hVU : V ≤ U)
    (hU : C.obj U = D.obj U) (hV : C.obj V = D.obj V) :
    letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU
    letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU
    (valMapOfLE (C := C) (D := D) hVU hV) ∘ₗ
        restrictₗ (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU =
      restrictₗ (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU ∘ₗ
        valMap (C := C) (D := D) hU := by
  let _ := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU
  let _ := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU
  ext x
  rfl

/-- If two concrete subalgebras have the same sections over `U` and over `V ≤ U`, then the
restriction map of the underlying module of one is a localization away from `a : Γ(X, U)` as
soon as that of the other is. -/
theorem isLocalizedModule_of_obj_eq {C D : Subalg A} {U V : X.Opens} (hVU : V ≤ U)
    (a : Γ(X, U)) (hU : C.obj U = D.obj U) (hV : C.obj V = D.obj V)
    (h : letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU
      IsLocalizedModule.Away a
        (restrictₗ (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU)) :
    letI := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU
    IsLocalizedModule.Away a
      (restrictₗ (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU) := by
  let _ := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf C)) hVU
  let _ := moduleOfLE (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU
  have h1 : IsLocalizedModule (Submonoid.powers a)
      (restrictₗ (AlgebraSheaf.underlyingModule (Subalg.toAlgebraSheaf D)) hVU ∘ₗ
        valMap (C := C) (D := D) hU) :=
    (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers a)
      (valMap (C := C) (D := D) hU) (bijective_valMap hU)).mpr h
  rw [← valMap_comp_restrictₗ hVU hU hV] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers a)
    (valMapOfLE (C := C) (D := D) hVU hV) (bijective_valMapOfLE hVU hV)).mp h1

/-! ### Quasi-coherence of the glue -/

section Glue

variable {ι : Type*} (W : ι → X.Opens) (C : ι → Subalg A)

/-- The glue of quasi-coherent pieces agreeing over the overlaps (`Agree`) is quasi-coherent,
provided the family admits a refinement by affine opens `V i` covering `X`, each inside some
member `W j`. The family `W` is not itself required to cover `X`. -/
theorem isQuasicoherent_glue (hagree : Agree W C) {I : Type u} (V : I → X.Opens)
    (hVcov : IsOpenCover V) (hVaff : ∀ i, IsAffineOpen (V i)) (hVW : ∀ i, ∃ j, V i ≤ W j)
    (hC : ∀ j, (Subalg.toAlgebraSheaf (C j)).IsQuasicoherent) :
    (Subalg.toAlgebraSheaf (glue W C)).IsQuasicoherent := by
  refine Stacks.DenominatorIdealQcoh.isQuasicoherent_of_isLocalizedModule_cover
    _ V hVcov hVaff fun i a ↦ ?_
  obtain ⟨j, hj⟩ := hVW i
  have := hC j
  exact isLocalizedModule_of_obj_eq (X.basicOpen_le a) a (glue_obj_of_le W C hagree hj)
    (glue_obj_of_le W C hagree ((X.basicOpen_le a).trans hj))
    (isLocalizedModule_restrictₗ _ (hVaff i) a rfl (X.basicOpen_le a))

/-- The case of two members: the glue of two quasi-coherent subalgebras agreeing over the overlap
of their opens is quasi-coherent, given an affine refinement of the pair. -/
theorem isQuasicoherent_glue_pair (W : Bool → X.Opens) (C : Bool → Subalg A)
    (h : ∀ V : X.Opens, V ≤ W false → V ≤ W true → (C false).obj V = (C true).obj V)
    {I : Type u} (V : I → X.Opens) (hVcov : IsOpenCover V) (hVaff : ∀ i, IsAffineOpen (V i))
    (hVW : ∀ i, ∃ j, V i ≤ W j)
    (hC : ∀ j, (Subalg.toAlgebraSheaf (C j)).IsQuasicoherent) :
    (Subalg.toAlgebraSheaf (glue W C)).IsQuasicoherent :=
  isQuasicoherent_glue W C (agree_pair W C h) V hVcov hVaff hVW hC

end Glue

end Stacks.RelativeSpec.AlgebraSheaf

end
