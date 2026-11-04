module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.Homology.ExtendScalars.FlatHomologyAdjoint

/-!
# The restriction maps of the cohomology of a complex of presheaves of modules

Let `B` be a sheaf of commutative rings on a site, `K` a complex of presheaves of modules over
`B` and `g : U ⟶ V` a morphism of the opposite of the site. The restriction map of the
cohomology presheaf `H^i(K)` along `g` is `B(U)`-linear, `H^i(K)(U) ⟶ H^i(K)(V)`, so it has a
`B(V)`-linear adjoint

`B(V) ⊗_{B(U)} H^i(K)(U) ⟶ H^i(K)(V)`,  `b ⊗ m ↦ b · m|_V`.

Evaluation of presheaves of modules is exact, so `H^i(K)(U) = H^i(K(U))`, and under these
identifications the restriction map of `H^i(K)` is the map on cohomology of the restriction map
of complexes `K(U) ⟶ K(V)` (`PresheafOfModules.homologyMap_restriction_comp`). So when
`B(U) → B(V)` is flat and the adjoint map of complexes `B(V) ⊗_{B(U)} K(U) ⟶ K(V)` is a
quasi-isomorphism, the adjoint of the restriction map of `H^i(K)` is an isomorphism
(`PresheafOfModules.isIso_homologyRestrictionAdjoint`). Everything here is stated for an arbitrary
complex `K`; the input is a property of the evaluations `K(U)`, `K(V)` alone.

## Main definitions

* `PresheafOfModules.restrictionAdjoint`: the adjoint `B(V) ⊗_{B(U)} P(U) ⟶ P(V)` of a
  restriction map of a presheaf of modules, and `PresheafOfModules.homologyRestrictionAdjoint` its
  case `P = H^i(K)`.

## Main results

* `PresheafOfModules.homologyMap_restriction_comp`: the restriction map of `H^i(K)` is the map on
  cohomology of the restriction map of complexes.
* `PresheafOfModules.isIso_homologyRestrictionAdjoint`: flat base change of the cohomology
  presheaf along a restriction map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe u v w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (B : Sheaf J CommRingCat.{w})
  (K : CochainComplex (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf B).obj) ℤ)
  (i : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V)

/-- The ring map `B(U) → B(V)` of the restriction along `g`. -/
abbrev sectionRestrictionHom : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj U →+*
    (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj V :=
  ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map g).hom

/-- The restriction map of complexes `K(U) ⟶ K(V)` along `g`, linear over `B(U) → B(V)`. -/
abbrev complexRestriction :
    ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      ((ModuleCat.restrictScalars (sectionRestrictionHom B g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((PresheafOfModules.evaluation _ V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (NatTrans.mapHomologicalComplex (PresheafOfModules.restriction
    (Stacks.SheafOfModules.Tensor.ringSheaf B).obj g) (ComplexShape.up ℤ)).app K

/-- The sections of `H^i(K)` over `U` are `H^i(K(U))`, evaluation being exact. -/
abbrev homologyEvaluationIso (U : Cᵒᵖ) :
    (((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology
        i ≅
      (K.homology i).obj U :=
  (Stacks.Homology.exactHomologyIso
    (PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf B).obj U) i).app K

/-- **The restriction map of `H^i(K)` is the map on cohomology of the restriction map of
complexes**, read through the identifications of the sections of `H^i(K)` with the cohomology of
the sections of `K`. -/
theorem homologyMap_restriction_comp :
    ModuleCat.homologyRestrictScalarsMap (sectionRestrictionHom B g) (complexRestriction B K g) i ≫
        (ModuleCat.restrictScalars (sectionRestrictionHom B g)).map
          (homologyEvaluationIso B K i V).hom =
      (homologyEvaluationIso B K i U).hom ≫ (K.homology i).map g := by
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf B).obj
  let ρ := PresheafOfModules.restriction O g
  have h : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ)).app K) i ≫
        ((K.sc i).mapHomologyIso (PresheafOfModules.evaluation O V ⋙
          ModuleCat.restrictScalars (O.map g).hom)).hom =
      ((K.sc i).mapHomologyIso (PresheafOfModules.evaluation O U)).hom ≫ ρ.app (K.homology i) :=
    congr_app (Stacks.Homology.exactHomologyIso_hom_naturality ρ i) K
  rw [ShortComplex.mapHomologyIso_comp_hom] at h
  rw [ModuleCat.homologyRestrictScalarsMap]
  exact (Category.assoc _ _ _).trans h

/-- **The adjoint of a restriction map** of a presheaf of modules `P` over `B`,
`B(V) ⊗_{B(U)} P(U) ⟶ P(V)`, `b ⊗ m ↦ b · m|_V`. -/
def restrictionAdjoint (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf B).obj) :
    (ModuleCat.extendScalars (sectionRestrictionHom B g)).obj (P.obj U) ⟶ P.obj V :=
  ((ModuleCat.extendRestrictScalarsAdj (sectionRestrictionHom B g)).homEquiv _ _).symm (P.map g)

/-- The adjoint of a restriction map sends `b ⊗ m` to `b · m|_V`. -/
theorem restrictionAdjoint_tmul
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf B).obj)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj V) (m : P.obj U) :
    restrictionAdjoint B g P (b ⊗ₜ[_, sectionRestrictionHom B g] m) =
      b • (P.map g m : ToType (P.obj V)) := by
  rw [restrictionAdjoint, Adjunction.homEquiv_counit]
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul _ _ b (P.map g m)

/-- **The adjoint of the restriction map of `H^i(K)`**, `B(V) ⊗_{B(U)} H^i(K)(U) ⟶ H^i(K)(V)`,
`b ⊗ m ↦ b · m|_V`. -/
abbrev homologyRestrictionAdjoint :
    (ModuleCat.extendScalars (sectionRestrictionHom B g)).obj ((K.homology i).obj U) ⟶
      (K.homology i).obj V :=
  restrictionAdjoint B g (K.homology i)

/-- The adjoint of the restriction map of `H^i(K)` is, through the identifications of sections
with cohomology of sections, the adjoint of the map on cohomology of the restriction map of
complexes. -/
theorem homologyRestrictionAdjoint_eq :
    homologyRestrictionAdjoint B K i g =
      (ModuleCat.extendScalars (sectionRestrictionHom B g)).map
          (homologyEvaluationIso B K i U).inv ≫
        ModuleCat.homologyExtendScalarsAdjoint (sectionRestrictionHom B g)
          (complexRestriction B K g) i ≫ (homologyEvaluationIso B K i V).hom := by
  let adj := ModuleCat.extendRestrictScalarsAdj (sectionRestrictionHom B g)
  have hmap : (K.homology i).map g = (homologyEvaluationIso B K i U).inv ≫
      ModuleCat.homologyRestrictScalarsMap (sectionRestrictionHom B g)
          (complexRestriction B K g) i ≫
        (ModuleCat.restrictScalars (sectionRestrictionHom B g)).map
          (homologyEvaluationIso B K i V).hom := by
    rw [homologyMap_restriction_comp, Iso.inv_hom_id_assoc]
  rw [homologyRestrictionAdjoint, restrictionAdjoint, hmap, adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm]
  rfl

/-- **Flat base change of the cohomology presheaf along a restriction map.** If `B(U) → B(V)` is
flat and the adjoint `B(V) ⊗_{B(U)} K(U) ⟶ K(V)` of the restriction map of complexes is a
quasi-isomorphism, then `B(V) ⊗_{B(U)} H^i(K)(U) ⟶ H^i(K)(V)`, `b ⊗ m ↦ b · m|_V`, is an
isomorphism. -/
theorem isIso_homologyRestrictionAdjoint (hflat : (sectionRestrictionHom B g).Flat)
    (hq : QuasiIso (((ModuleCat.extendScalars (sectionRestrictionHom B g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (complexRestriction B K g) ≫
      ModuleCat.extendRestrictScalarsAdjCounitComplex (sectionRestrictionHom B g)
        (ComplexShape.up ℤ)
        (((PresheafOfModules.evaluation _ V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :
    IsIso (homologyRestrictionAdjoint B K i g) := by
  have := ModuleCat.isIso_homologyExtendScalarsAdjoint (sectionRestrictionHom B g)
    (complexRestriction B K g) i hflat hq
  rw [homologyRestrictionAdjoint_eq]
  infer_instance

end PresheafOfModules

end
