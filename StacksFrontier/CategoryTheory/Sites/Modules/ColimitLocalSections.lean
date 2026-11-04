module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Sections of a colimit of sheaves of modules are locally sections of a member

Let `M` be the colimit of a filtered diagram `D` of sheaves of modules on a site, with colimit
cocone `φ`.  Every section of `M` is *locally* the image of a section of some member `D k`: the
sieve of arrows along which it is in the image of one of the `φ k` covers. A section of `M`
which is locally in the image of a *monomorphism* `ι : N ⟶ M` is in its image.

## Main definitions

* `SheafOfModules.jointImageSieve`: the sieve of arrows along which a section of `M` is the image
  of a section of some member of `D`.
* `SheafOfModules.jointImageSubmodule`: the sections of `M` whose joint image sieve covers, as a
  submodule.

## Main results

* `SheafOfModules.mem_jointImageSieve_of_isColimit`: the joint image sieve of a section of a
  filtered colimit covers.
* `SheafOfModules.exists_eq_of_mono_of_imageSieve_mem`: a section locally in the image of a
  monomorphism is in its image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

section JointImage

variable {K : Type w} [Category.{v} K] {D : K ⥤ SheafOfModules.{u} R} {M : SheafOfModules.{u} R}
  (φ : D ⟶ (Functor.const K).obj M)

/-- The sieve of arrows `g : V ⟶ X` along which a section `x` of `M` over `X` is the image of a
section of some member of `D`. -/
def jointImageSieve {X : C} (x : M.val.obj (op X)) : Sieve X where
  arrows V g := ∃ (k : K) (y : (D.obj k).val.obj (op V)),
    (φ.app k).val.app (op V) y = M.val.map g.op x
  downward_closed := by
    rintro V W g ⟨k, y, hy⟩ h
    refine ⟨k, (D.obj k).val.map h.op y, ?_⟩
    rw [PresheafOfModules.naturality_apply, hy, op_comp, PresheafOfModules.map_comp_apply]
    rfl

variable [IsFiltered K]

/-- The sections of `M` which are locally images of sections of members of `D`, as a submodule. -/
def jointImageSubmodule : M.Submodule where
  obj X :=
    { carrier := {x | jointImageSieve φ x ∈ J X.unop}
      add_mem' := by
        intro x x' hx hx'
        refine J.superset_covering ?_ (J.intersection_covering hx hx')
        rintro V g ⟨⟨k, y, hy⟩, ⟨k', y', hy'⟩⟩
        let m := IsFiltered.max k k'
        refine ⟨m, (D.map (IsFiltered.leftToMax k k')).val.app _ y +
          (D.map (IsFiltered.rightToMax k k')).val.app _ y', ?_⟩
        rw [map_add, map_add]
        have e1 : (φ.app m).val.app (op V) ((D.map (IsFiltered.leftToMax k k')).val.app _ y) =
            (φ.app k).val.app (op V) y := by
          rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
            ← SheafOfModules.comp_val, φ.naturality]
          rfl
        have e2 : (φ.app m).val.app (op V) ((D.map (IsFiltered.rightToMax k k')).val.app _ y') =
            (φ.app k').val.app (op V) y' := by
          rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
            ← SheafOfModules.comp_val, φ.naturality]
          rfl
        rw [e1, e2, hy, hy']
        rfl
      zero_mem' := by
        refine J.superset_covering (fun V g _ => ?_) (J.top_mem _)
        obtain ⟨k⟩ : Nonempty K := IsFiltered.nonempty
        exact ⟨k, 0, by rw [map_zero, map_zero]; rfl⟩
      smul_mem' := by
        intro r x hx
        refine J.superset_covering ?_ hx
        rintro V g ⟨k, y, hy⟩
        refine ⟨k, R.obj.map g.op r • y, ?_⟩
        rw [map_smul, hy, PresheafOfModules.map_smul]
        rfl }
  map {X Y} f x hx := by
    change jointImageSieve φ (M.val.restrictₛₗ f x) ∈ J Y.unop
    have : jointImageSieve φ (M.val.restrictₛₗ f x) = (jointImageSieve φ x).pullback f.unop := by
      ext V g
      change (∃ k y, _ = M.val.map g.op (M.val.map f x)) ↔ (∃ k y, _ = M.val.map (g ≫ f.unop).op x)
      rw [op_comp, Quiver.Hom.op_unop, PresheafOfModules.map_comp_apply]
      exact Iff.rfl
    rw [this]
    exact J.pullback_stable f.unop hx
  isSheaf {X} x hx := by
    refine J.transitive hx _ fun V g hg => ?_
    change jointImageSieve φ (M.val.restrictₛₗ g.op x) ∈ J V at hg
    have : jointImageSieve φ (M.val.restrictₛₗ g.op x) = (jointImageSieve φ x).pullback g := by
      ext W h
      change (∃ k y, _ = M.val.map h.op (M.val.map g.op x)) ↔ (∃ k y, _ = M.val.map (h ≫ g).op x)
      rw [op_comp, PresheafOfModules.map_comp_apply]
      exact Iff.rfl
    rwa [← this]

/-- The factorization of `φ k` through the joint image submodule. -/
noncomputable def toJointImage (k : K) : D.obj k ⟶ (jointImageSubmodule φ).toSheafOfModules :=
  ⟨{ app := fun U => ModuleCat.ofHom (LinearMap.codRestrict _ ((φ.app k).val.app U).hom
        (fun z => J.superset_covering (fun V g _ =>
          ⟨k, (D.obj k).val.map g.op z, PresheafOfModules.naturality_apply _ _ _⟩)
          (J.top_mem _)))
     naturality := fun {U V} f => by
       ext z
       exact Subtype.ext (PresheafOfModules.naturality_apply (φ.app k).val f z) }⟩

/-- The joint image sieve of a section of a filtered colimit of sheaves of modules covers. -/
theorem mem_jointImageSieve_of_isColimit (hc : IsColimit (Cocone.mk M φ)) {X : C}
    (x : M.val.obj (op X)) : jointImageSieve φ x ∈ J X := by
  let N := jointImageSubmodule φ
  let c : Cocone D :=
    { pt := N.toSheafOfModules
      ι :=
        { app := fun k => toJointImage φ k
          naturality := fun k k' g => by
            apply SheafOfModules.hom_ext
            refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
            refine Subtype.ext ?_
            show (φ.app k').val.app U ((D.map g).val.app U z) = (φ.app k).val.app U z
            rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
              ← SheafOfModules.comp_val, φ.naturality]
            rfl } }
  have h : hc.desc c ≫ N.ι = 𝟙 M := by
    refine hc.hom_ext fun k => ?_
    rw [← Category.assoc, hc.fac, Category.comp_id]
    rfl
  have hx : x = (N.ι.val.app (op X)) ((hc.desc c).val.app (op X) x) :=
    (congrArg (fun ψ : M ⟶ M => ψ.val.app (op X) x) h).symm
  rw [hx]
  exact ((hc.desc c).val.app (op X) x).2

end JointImage

/-- A section locally in the image of a monomorphism is in its image. -/
theorem exists_eq_of_mono_of_imageSieve_mem {N M : SheafOfModules.{u} R} (ι : N ⟶ M) [Mono ι]
    {X : C} (x : M.val.obj (op X))
    (hx : Presheaf.imageSieve ((SheafOfModules.toSheaf R).map ι).hom x ∈ J X) :
    ∃ z : N.val.obj (op X), ι.val.app (op X) z = x := by
  classical
  have hinj := fun U => Stacks.SheafOfModules.injective_app_of_mono ι U
  have hsheaf (P : SheafOfModules.{u} R) :
      Presieve.IsSheaf J (P.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (GrothendieckTopology.HasSheafCompose.isSheaf _ P.isSheaf)
  let S := Presheaf.imageSieve ((SheafOfModules.toSheaf R).map ι).hom x
  let fam : Presieve.FamilyOfElements (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      S.arrows := fun V g hg => hg.choose
  have hfam : ∀ ⦃V⦄ (g : V ⟶ X) (hg : S g), ι.val.app (op V) (fam g hg) = M.val.map g.op x :=
    fun V g hg => hg.choose_spec
  have hcomp : fam.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ hw
    apply hinj
    refine (PresheafOfModules.naturality_apply ι.val g₁.op (fam f₁ h₁)).trans ?_
    refine Eq.trans ?_ (PresheafOfModules.naturality_apply ι.val g₂.op (fam f₂ h₂)).symm
    rw [hfam, hfam, ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
      ← op_comp, ← op_comp, hw]
  obtain ⟨z, hz⟩ := hsheaf N S hx fam hcomp
  refine ⟨z, (hsheaf M S hx).isSeparatedFor.ext fun V g hg => ?_⟩
  refine (PresheafOfModules.naturality_apply ι.val g.op z).symm.trans ?_
  exact (congrArg (ι.val.app (op V)) (hz.1 g hg)).trans (hfam g hg)

end SheafOfModules

end
