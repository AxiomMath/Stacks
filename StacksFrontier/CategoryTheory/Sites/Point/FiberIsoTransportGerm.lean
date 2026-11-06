module

public import StacksFrontier.CategoryTheory.Sites.Point.FiberIsoTransport

/-!
# Germs under the transport of a point along an isomorphism of its fibre

`Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj` identifies, for a continuous
`uf : C ⥤ D`, a point `Phi` of `(D, K)`, a point `Psi` of `(C, J)` with fibre isomorphic to
`uf ⋙ Phi.fiber` and a left adjoint `L` of the direct image, the fibre functor of `Psi` on
sheaves with `L` followed by the fibre functor of `Phi`. This file computes that identification
on germs.

## Main results

* `Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj_hom_app_counit_toPresheafFiber`: the
  identification, followed by the stalk of the counit `L(uf_*F) ⟶ F`, carries the germ at
  `(V, t)` of a section of `F` over `uf V` to its germ at `(uf V, e t)`.
* `Stacks.SitePointFiberIso.presheafFiberIsoOfFiberIso_hom_toPresheafFiber`: the comparison of
  the fibre functors of two points with isomorphic fibres carries a germ to the germ at the
  transported element.
* `CategoryTheory.conjugateIsoEquiv_symm_hom_app_comp_map_counit`: the transpose formula for a
  conjugate isomorphism followed by a counit, from which the germ formula is read off.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {SY : Type u₁} [Category.{v₁} SY] {SX : Type u₂} [Category.{v₂} SX]
  {T : Type u₃} [Category.{v₃} T]
  {L : SY ⥤ SX} {R : SX ⥤ SY} (adj : L ⊣ R) {P : SX ⥤ T} {Q : SY ⥤ T} {SP : T ⥤ SX}
  {SQ : T ⥤ SY} (aP : P ⊣ SP) (aQ : Q ⊣ SQ) (θ : SP ⋙ R ≅ SQ)

/-- The mate of a conjugate: if `Q ≅ L ⋙ P` is the conjugate of an isomorphism
`SP ⋙ R ≅ SQ` of right adjoints, the composite `Q R ⟶ P L R ⟶ P` with the counit of `L ⊣ R`
is the transpose of `R(η^P) ≫ θ`. -/
lemma conjugateIsoEquiv_symm_hom_app_comp_map_counit (M : SX) :
    ((conjugateIsoEquiv (adj.comp aP) aQ).symm θ).hom.app (R.obj M) ≫ P.map (adj.counit.app M) =
      (aQ.homEquiv _ _).symm (R.map (aP.unit.app M) ≫ θ.hom.app (P.obj M)) := by
  set γ := (conjugateIsoEquiv (adj.comp aP) aQ).symm θ with hγ
  have hθ : conjugateEquiv (adj.comp aP) aQ γ.hom = θ.hom := by
    rw [hγ, conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  have hc := conjugateEquiv_counit (adj.comp aP) aQ γ.hom (P.obj M)
  rw [hθ] at hc
  rw [Adjunction.homEquiv_counit, Q.map_comp, Category.assoc, hc, ← Category.assoc]
  have hn := γ.hom.naturality (R.map (aP.unit.app M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Functor.comp_obj]
  rw [hn, Category.assoc]
  congr 1
  simp only [Adjunction.comp_counit_app, Functor.id_obj]
  have hε := adj.counit.naturality (aP.unit.app M)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hε
  rw [← P.map_comp_assoc, hε, P.map_comp, Category.assoc, aP.left_triangle_components,
    Category.comp_id]

end CategoryTheory

namespace Stacks.SitePointFiberIso

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}

section Germ

/-- The comparison of the fibre functors of two points with isomorphic fibres carries a germ to
the germ at the transported element. -/
lemma presheafFiberIsoOfFiberIso_hom_toPresheafFiber (Psi : Point.{u} J) {G : C ⥤ Type u}
    (e : Psi.fiber ≅ G) (P : Cᵒᵖ ⥤ Type u) (V : C) (t : Psi.fiber.obj V) (s : P.obj (op V)) :
    (presheafFiberIsoOfFiberIso Psi e).hom.app P (Psi.toPresheafFiber V t P s) =
      (pointOfFiberIso Psi e).toPresheafFiber V (e.hom.app V t) P s := by
  let : HasColimitsOfShape (G.Elements)ᵒᵖ (Type u) :=
    inferInstanceAs (HasColimitsOfShape ((pointOfFiberIso Psi e).fiber.Elements)ᵒᵖ (Type u))
  show (Functor.Final.colimitIso (elementsEquivOfIso e).functor.op
      ((CategoryOfElements.π G).op ⋙ P)).hom
    (colimit.ι ((elementsEquivOfIso e).functor.op ⋙ (CategoryOfElements.π G).op ⋙ P)
      (op (Psi.fiber.elementsMk V t)) s) = _
  rw [Functor.Final.colimitIso_hom]
  exact congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    (colimit.ι_pre ((CategoryOfElements.π G).op ⋙ P) (elementsEquivOfIso e).functor.op
      (op (Psi.fiber.elementsMk V t)))) s

/-- **The stalk comparison of a base change, followed by the counit, on germs.** For the
identification `Ψ⁻¹ ≅ L ⋙ Φ⁻¹` of `Stacks.SitePointFiberIso.sheafFiberIsoOfFiberIsoOfAdj`, the
germ at `(V, t)` of a section `s` of `uf_*F`, that is of a section of `F` over `uf V`, is carried
by the identification followed by the stalk at `Φ` of the counit `L(uf_*F) ⟶ F` to the germ of
`s` at `(uf V, e t)`. -/
lemma sheafFiberIsoOfFiberIsoOfAdj_hom_app_counit_toPresheafFiber (Phi : Point.{u} K)
    (uf : C ⥤ D) [uf.IsContinuous J K] {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (adj : L ⊣ uf.sheafPushforwardContinuous (Type u) J K)
    (Psi : Point.{u} J) (e : Psi.fiber ≅ uf ⋙ Phi.fiber) (F : Sheaf K (Type u)) (V : C)
    (t : Psi.fiber.obj V) (s : F.obj.obj (op (uf.obj V))) :
    Phi.sheafFiber.map (adj.counit.app F)
        ((sheafFiberIsoOfFiberIsoOfAdj Phi uf adj Psi e).hom.app
          ((uf.sheafPushforwardContinuous (Type u) J K).obj F)
          (Psi.toPresheafFiber V t ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj s)) =
      Phi.toPresheafFiber (uf.obj V) (e.hom.app V t) F.obj s := by
  have h₁ := presheafFiberIsoOfFiberIso_hom_toPresheafFiber Psi e
    ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj V t s
  show Phi.sheafFiber.map (adj.counit.app F)
      ((sheafFiberIsoOfAdj Phi uf adj (pointOfFiberIso Psi e) rfl).hom.app
        ((uf.sheafPushforwardContinuous (Type u) J K).obj F)
        ((presheafFiberIsoOfFiberIso Psi e).hom.app
          ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj
          (Psi.toPresheafFiber V t ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj
            s))) = _
  rw [h₁]
  have hθ : (eqToIso (skyscraperSheafFunctor_eq_of_fiber_eq Phi uf (pointOfFiberIso Psi e)
      rfl)).hom.app (Phi.sheafFiber.obj F) = 𝟙 _ := by
    rw [eqToIso.hom, eqToHom_app]
    rfl
  have hη : ∀ x : Phi.fiber.obj (uf.obj V),
      (Phi.skyscraperSheafAdjunction.unit.app F).hom.app (op (uf.obj V)) ≫
        Pi.π (fun _ : Phi.fiber.obj (uf.obj V) => Phi.sheafFiber.obj F) x =
          Phi.toPresheafFiber (uf.obj V) x F.obj := fun x => by
    rw [← Adjunction.homEquiv_id]
    refine (congrArg (fun φ => φ.app (op (uf.obj V)) ≫ Pi.π (fun _ => Phi.sheafFiber.obj F) x)
      (GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_apply_hom Phi
        (𝟙 (Phi.sheafFiber.obj F)))).trans ?_
    exact (GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_π Phi _ (uf.obj V)
      x).trans (Category.comp_id _)
  have hg : (uf.sheafPushforwardContinuous (Type u) J K).map
        (Phi.skyscraperSheafAdjunction.unit.app F) ≫
      (eqToIso (skyscraperSheafFunctor_eq_of_fiber_eq Phi uf (pointOfFiberIso Psi e) rfl)).hom.app
        (Phi.sheafFiber.obj F) =
      (uf.sheafPushforwardContinuous (Type u) J K).map
        (Phi.skyscraperSheafAdjunction.unit.app F) :=
    (congrArg (fun φ => (uf.sheafPushforwardContinuous (Type u) J K).map
        (Phi.skyscraperSheafAdjunction.unit.app F) ≫ φ) hθ).trans (Category.comp_id _)
  have key : (pointOfFiberIso Psi e).toPresheafFiber V (e.hom.app V t)
      ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj ≫
      (((pointOfFiberIso Psi e).skyscraperSheafAdjunction.homEquiv _ _).symm
        ((uf.sheafPushforwardContinuous (Type u) J K).map
          (Phi.skyscraperSheafAdjunction.unit.app F) ≫
          (eqToIso (skyscraperSheafFunctor_eq_of_fiber_eq Phi uf (pointOfFiberIso Psi e)
            rfl)).hom.app (Phi.sheafFiber.obj F))) =
      Phi.toPresheafFiber (uf.obj V) (e.hom.app V t) F.obj := by
    refine (congrArg (fun g => (pointOfFiberIso Psi e).toPresheafFiber V (e.hom.app V t)
        ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj ≫
        (((pointOfFiberIso Psi e).skyscraperSheafAdjunction.homEquiv _ _).symm g)) hg).trans ?_
    refine (congrArg (fun φ => (pointOfFiberIso Psi e).toPresheafFiber V (e.hom.app V t)
        ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj ≫ φ)
      (GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_symm_apply
        (pointOfFiberIso Psi e) _)).trans ?_
    refine (GrothendieckTopology.Point.toPresheafFiber_skyscraperPresheafHomEquiv_symm
      (pointOfFiberIso Psi e) _ V (e.hom.app V t)).trans ?_
    exact hη (e.hom.app V t)
  have h₂ := ConcreteCategory.congr_hom
    (conjugateIsoEquiv_symm_hom_app_comp_map_counit adj Phi.skyscraperSheafAdjunction
      (pointOfFiberIso Psi e).skyscraperSheafAdjunction
      (eqToIso (skyscraperSheafFunctor_eq_of_fiber_eq Phi uf (pointOfFiberIso Psi e) rfl)) F)
    ((pointOfFiberIso Psi e).toPresheafFiber V (e.hom.app V t)
      ((uf.sheafPushforwardContinuous (Type u) J K).obj F).obj s)
  exact h₂.trans (ConcreteCategory.congr_hom key s)

end Germ

end Stacks.SitePointFiberIso

end
