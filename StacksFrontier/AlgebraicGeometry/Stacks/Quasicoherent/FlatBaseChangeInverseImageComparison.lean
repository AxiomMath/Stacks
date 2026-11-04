module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTransposeIsIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleStructureComparisonComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE

/-!
# The direct-image comparison of an inverse image of modules, on sections

* `PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq`: a transpose is invertible for one
  of the adjunctions of two equal maps of presheaves of rings exactly when it is for the other.
* `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_inverseImageIso`: on sections
  over a small étale object, the module comparison of Stacks 06W2 for an inverse image `f^{-1}G`
  is the one for `G`, through the identifications of Stacks 075D (3).
* `AlgebraicGeometry.Stack.isIso_homEquiv_symm_restrictModulePushforwardComparison_inverseImage`:
  the comparison for `f^{-1}G` at an arrow of `𝒳` is invertible when the one for `G` is.

The module `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImage` proves
the flat base change property of the inverse image by another route; these statements are what
the sheaf-level comparisons of this file consume.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' m

namespace PresheafOfModules

variable {C : Type*} [Category C] {D : Type*} [Category D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- **A transpose is invertible for one of the two adjunctions of two equal maps of presheaves
of rings exactly when it is for the other.** Two equal maps `φ = ψ : S ⟶ F.op ⋙ R` have equal
direct-image functors, so two adjunctions `L₁ ⊣ pushforward φ` and `L₂ ⊣ pushforward ψ` are two
adjunctions of one functor; a morphism into the direct image therefore has invertible transpose
for one exactly when it has for the other.

This is `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_rightAdjointEq` for the two
adjunctions, which is what carries a comparison map built over one spelling of a map of
structure sheaves to the other spelling.  The two morphisms being transposed are only required
to agree on sections, which is all a comparison map built by other means is known to satisfy. -/
theorem isIso_homEquiv_symm_iff_of_pushforward_eq {φ ψ : S ⟶ F.op ⋙ R} (hφψ : φ = ψ)
    {L₁ L₂ : PresheafOfModules.{m} S ⥤ PresheafOfModules.{m} R}
    (adj₁ : L₁ ⊣ pushforward.{m} φ) (adj₂ : L₂ ⊣ pushforward.{m} ψ)
    {M : PresheafOfModules.{m} S} {N : PresheafOfModules.{m} R}
    (w : M ⟶ (pushforward.{m} φ).obj N) (w' : M ⟶ (pushforward.{m} ψ).obj N)
    (hw : ∀ (X : Cᵒᵖ) (t : M.obj X), w.app X t = w'.app X t) :
    IsIso ((adj₁.homEquiv M N).symm w) ↔ IsIso ((adj₂.homEquiv M N).symm w') := by
  subst hφψ
  obtain rfl : w = w' := by
    refine PresheafOfModules.hom_ext fun X => ?_
    exact ModuleCat.hom_ext (LinearMap.ext (hw X))
  exact Adjunction.isIso_homEquiv_symm_iff_of_rightAdjointEq adj₁ adj₂ w

end PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴)
  (hp : (f ⋙ q).IsFiberedInGroupoids)
  (G : PresheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hG : Presheaf.IsSheaf (associatedTopology B S hS q (etaleTopology B)) G.presheaf)
  (hf : (f ⋙ q).IsFibredOneMorphism q f)

/-- **Stacks 075D, part (4), for the direct-image comparison of a presheaf of modules.** On
sections over a small étale object, the comparison of **Stacks 06W2** for the inverse image
`f^{-1}G` at an arrow `φ` of `𝒳`, followed by the identification of part (3) at the source of
`φ`, is the identification of part (3) at the target of `φ` followed by the comparison for `G`
itself at `f φ`.

This is
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_comp_inverseImageIso` at the presheaf
of sections of `G`: the module comparison of **Stacks 06WC** has the comparison for the
underlying presheaf of abelian groups as its map on sections, by
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app`, and the identification of
part (3) between modules is the identification between the underlying presheaves of sets, by
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleInverseImageMap_eq`. -/
theorem restrictModulePushforwardComparison_app_inverseImageIso {x' x : 𝒳} (φ : x' ⟶ x)
    (W : SmallEtale E (q.obj (f.obj x)).left.1 (contains_base B E h S hS q (f.obj x)))
    (n : (restrictModuleToSmallEtale B E h S hS (f ⋙ q) hp x (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).obj
        (Opposite.op W)) :
    (restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
          B E h S hS q hq f hp G hG hf x').hom.app
        (Opposite.op ((smallEtaleBaseChange E
          (smallEtaleBaseMorphism B E h S hS q (f.map φ))).obj W))
        ((restrictModulePushforwardComparison B E h S hS (f ⋙ q) hp φ (etaleTopology B)
          (etaleTopology_le_topology B)
          ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G)).app
            (Opposite.op W) n) =
      (restrictModulePushforwardComparison B E h S hS q hq (f.map φ) (etaleTopology B)
          (etaleTopology_le_topology B) G).app (Opposite.op W)
        ((restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
          B E h S hS q hq f hp G hG hf x).hom.app (Opposite.op W) n) := by
  have hpart4 := restrictionPushforwardComparison_comp_inverseImageIso B E h S hS q hq f hp hf φ
    (etaleSheafOfSections.{u, v', w', m} B S hS q hq G hG)
  have hset := CategoryTheory.congr_fun (NatTrans.congr_app hpart4 (Opposite.op W)) n
  simp only [NatTrans.comp_app] at hset
  exact hset.symm

include hG hf in
/-- **The comparison map of Stacks 06WC for the inverse image of a module is invertible as soon
as the one for the module is.**  Let `φ : x' ⟶ x` be an arrow of the source `𝒳` of a strictly
presented 1-morphism `f : 𝒳 ⥤ 𝒴`, and let `c` be the comparison map of **Stacks 06WC** for the
inverse image `f^{-1}G` at `φ`, read as the transpose of the direct-image comparison of
**Stacks 06W2** along a given adjunction.  If the comparison map for `G` itself at `f φ` is
invertible, so is `c`.

Three steps.  The square of **Stacks 075D** part (4) at the level of presheaves of modules,
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_inverseImageIso`, has the two
identifications of part (3) on its vertical sides, so
`CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_isoSquare` replaces the comparison for
`f^{-1}G` by the composite across that square.  The two maps of structure sheaves the two sides
are taken over are built from the localization equivalences of **Stacks 06W0** at `x` and at
`f x` and are not the same map on the nose, but they are equal, by
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_of_comp`; so
`PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq` identifies that composite's
transpose with the transpose of the comparison for `G`, the two transposes being taken along two
adjunctions of one direct-image functor. -/
theorem isIso_homEquiv_symm_restrictModulePushforwardComparison_inverseImage
    {x' x : 𝒳} (φ : x' ⟶ x)
    {LZ : PresheafOfModules.{m} (SmallEtale.structureSheaf E ((f ⋙ q).obj x).left.1
        (contains_base B E h S hS (f ⋙ q) x)).obj ⥤
      PresheafOfModules.{m} (SmallEtale.structureSheaf E ((f ⋙ q).obj x').left.1
        (contains_base B E h S hS (f ⋙ q) x')).obj}
    {LX : PresheafOfModules.{m} (SmallEtale.structureSheaf E (q.obj (f.obj x)).left.1
        (contains_base B E h S hS q (f.obj x))).obj ⥤
      PresheafOfModules.{m} (SmallEtale.structureSheaf E (q.obj (f.obj x')).left.1
        (contains_base B E h S hS q (f.obj x'))).obj}
    (adjZ : LZ ⊣ PresheafOfModules.pushforward.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS (f ⋙ q) φ))
      (smallEtaleStructureComparison B E h S hS (f ⋙ q) hp φ (etaleTopology B)
        (etaleTopology_le_topology B)))
    (adjX : LX ⊣ PresheafOfModules.pushforward.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS q (f.map φ)))
      (smallEtaleStructureComparison B E h S hS q hq (f.map φ) (etaleTopology B)
        (etaleTopology_le_topology B)))
    (hG' : IsIso ((adjX.homEquiv _ _).symm
      (restrictModulePushforwardComparison B E h S hS q hq (f.map φ) (etaleTopology B)
        (etaleTopology_le_topology B) G))) :
    IsIso ((adjZ.homEquiv _ _).symm
      (restrictModulePushforwardComparison B E h S hS (f ⋙ q) hp φ (etaleTopology B)
        (etaleTopology_le_topology B)
        ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G))) := by
  have hcmp := smallEtaleStructureComparison_eq_of_comp B E h S hS (etaleTopology B)
    (etaleTopology_le_topology B) q hq f hp φ
  set eX := restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
    B E h S hS q hq f hp G hG hf x with heX
  set eX' := restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
    B E h S hS q hq f hp G hG hf x' with heX'
  set u := restrictModulePushforwardComparison B E h S hS (f ⋙ q) hp φ (etaleTopology B)
    (etaleTopology_le_topology B)
    ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj G) with hu
  refine (Adjunction.isIso_homEquiv_symm_iff_of_isoSquare adjZ eX eX' u
    (eX.inv ≫ u ≫ (PresheafOfModules.pushforward.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS (f ⋙ q) φ))
      (smallEtaleStructureComparison B E h S hS (f ⋙ q) hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).map eX'.hom)
    (by rw [Iso.hom_inv_id_assoc])).mpr ?_
  refine (PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq hcmp adjZ adjX _
    (restrictModulePushforwardComparison B E h S hS q hq (f.map φ) (etaleTopology B)
      (etaleTopology_le_topology B) G) ?_).mpr hG'
  intro X t
  obtain ⟨W⟩ := X
  have hid : (eX.hom.app (Opposite.op W)) ((eX.inv.app (Opposite.op W)) t) = t := by
    have h0 := congrArg
      (fun k : _ ⟶ _ => PresheafOfModules.Hom.app k (Opposite.op W)) eX.inv_hom_id
    simpa only [PresheafOfModules.comp_app, PresheafOfModules.id_app, CategoryTheory.comp_apply,
      CategoryTheory.id_apply] using ConcreteCategory.congr_hom h0 t
  have hpart := restrictModulePushforwardComparison_app_inverseImageIso B E h S hS q hq f hp G hG
    hf φ W (eX.inv.app (Opposite.op W) t)
  rw [← heX, ← heX', ← hu, hid] at hpart
  simp only [PresheafOfModules.comp_app, CategoryTheory.comp_apply]
  exact hpart

end AlgebraicGeometry.Stack

end
