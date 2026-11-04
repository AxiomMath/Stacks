module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitOfFiniteSites

/-!
# A colimit presentation whose legs are isomorphisms

Let `D` be an inverse system of sites with finite coverings whose index category is nonempty and
cofiltered, with a cocone of functors `u_j` to a site `C`, and let `F` be a system of abelian
sheaves on the levels. A compatible family `ι_j : F_j ⟶ u_{j,*} 𝒢` whose transposes
`u_j⁻¹ F_j ⟶ 𝒢` (`Stacks.WeakSites.ExtColimit.systemLeg`) are isomorphisms presents `𝒢` as
`colim_j u_j⁻¹ F_j` (`isColimitPresentation_of_isIso_systemLeg`): the factorisation of another
compatible family through `𝒢` is read off at one index, and agrees at every other index because
any two indices have a common lower bound.

This is the shape in which the inverse images of a single sheaf present the inverse image to the
limit: every leg is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w w' v' u'

namespace Stacks.WeakSites.ExtColimit

open CategoryTheory.Sites.InverseSystem InverseSystemOfFiniteSites
  Stacks.WeakSites.ColimitSiteCohomology Stacks.Homology

variable {D : InverseSystemOfFiniteSites.{v, u, max u v w}}
  {C : Type (max u v w)} [SmallCategory C]
  {uC : ∀ i, D.C i ⥤ C} {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
  {K : Precoverage C} [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]

/-- `systemLeg` followed by a morphism is the transpose of the leg followed by its direct image. -/
theorem systemLeg_comp {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    {𝒢 H : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (h : 𝒢 ⟶ H) (j : D.I) :
    systemLeg ι j ≫ h =
      systemLeg (fun j => ι j ≫ Functor.whiskerLeft (uC j).op h.hom) j := by
  simp only [systemLeg]
  rw [← Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- **A compatible family whose transposes are isomorphisms presents the colimit.** -/
theorem isColimitPresentation_of_isIso_systemLeg [Nonempty D.I]
    (hcofil : ∀ j j' : D.I, ∃ (m : D.I), Nonempty (m ⟶ j) ∧ Nonempty (m ⟶ j'))
    {F : AbelianSheafSystem.{v, u, max u v w, max u v w} D}
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι)
    (hiso : ∀ j, IsIso (systemLeg (K := K) ι j)) :
    IsColimitPresentation.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι := by
  refine ⟨hι, fun H g hg => ?_⟩
  obtain ⟨i₀⟩ := ‹Nonempty D.I›
  have key : ∀ (h : 𝒢 ⟶ H) (j : D.I),
      (ι j ≫ Functor.whiskerLeft (uC j).op h.hom = g j ↔
        systemLeg (K := K) ι j ≫ h = systemLeg (K := K) g j) := by
    intro h j
    rw [systemLeg_comp]
    refine ⟨fun e => by simp only [systemLeg, e], fun e => ?_⟩
    have e' := congrArg (fun z => (((colimitAdj.{v, u, w} D uC K j).homEquiv _ _) z).hom) e
    simp only [systemLeg, Equiv.apply_symm_apply] at e'
    exact e'
  have hred : ∀ (h : 𝒢 ⟶ H) {m j : D.I} (a : m ⟶ j),
      systemLeg (K := K) ι m ≫ h = systemLeg (K := K) g m →
        systemLeg (K := K) ι j ≫ h = systemLeg (K := K) g j := by
    intro h m j a e
    rw [← systemLeg_compat hu ι hι a, ← systemLeg_compat hu g hg a]
    simp only [Category.assoc, e]
  let h₀ : 𝒢 ⟶ H := inv (systemLeg (K := K) ι i₀) ≫ systemLeg (K := K) g i₀
  have hall : ∀ j, systemLeg (K := K) ι j ≫ h₀ = systemLeg (K := K) g j := by
    intro j
    obtain ⟨m, ⟨a⟩, ⟨b⟩⟩ := hcofil j i₀
    refine hred h₀ a ?_
    let φ := (colimitPullbackCompIso.{v, u, w} D uC hu K b).inv.app (F.obj i₀) ≫
      (colimitPullback.{v, u, w} D uC K m).map (F.map b)
    have hφ : ∀ (H : Sheaf K.toGrothendieck Ab.{max u v w})
        (κ : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ H.obj),
        IsCompatible.{v, u, max u v w, max u v w} D uC hu F H.obj κ →
          φ ≫ systemLeg (K := K) κ m = systemLeg (K := K) κ i₀ :=
      fun _ κ hκ => systemLeg_compat (K := K) hu κ hκ b
    have hι' := hφ 𝒢 ι hι
    have : IsIso (φ ≫ systemLeg (K := K) ι m) := by rw [hι']; infer_instance
    have := IsIso.of_isIso_comp_right φ (systemLeg (K := K) ι m)
    rw [← cancel_epi φ, ← Category.assoc, hι', hφ H g hg]
    simp [h₀]
  refine ⟨h₀, fun j => (key h₀ j).2 (hall j), fun h' hh' => ?_⟩
  have e := (key h' i₀).1 (hh' i₀)
  simp only [h₀, ← e, IsIso.inv_hom_id_assoc]

section Transfer

variable [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]

/-- `Ext` out of a fixed object into an isomorphic second variable, as an isomorphism of groups. -/
def extPostIso {𝒞 : Type u'} [Category.{v'} 𝒞] [Abelian 𝒞] [HasExt.{w'} 𝒞] (A : 𝒞) {X Y : 𝒞}
    (e : X ≅ Y) (n : ℕ) :
    AddCommGrpCat.of (Abelian.Ext.{w'} A X n) ≅ AddCommGrpCat.of (Abelian.Ext.{w'} A Y n) :=
  AddEquiv.toAddCommGrpIso
    { toFun := extConj (𝟙 A) e.hom
      invFun := extConj (𝟙 A) e.inv
      left_inv := fun x => by
        simp only [extConj_extConj, Category.id_comp, Iso.hom_inv_id,
          extConj_id]
      right_inv := fun x => by
        simp only [extConj_extConj, Category.id_comp, Iso.inv_hom_id,
          extConj_id]
      map_add' := extConj_add _ _ }

variable (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))

include hobj hhom hhom_inj hK in
/-- **The `Ext` colimit at any colimit presentation.** If the `Ext` cocone at the constructed
colimit sheaf of a system is a colimit, so is the `Ext` cocone at any other colimit
presentation. -/
theorem nonempty_isColimit_extCocone_of_presentation {i : D.I}
    (𝒜 : FirstVariable.{v, u, w} D uC hu K i) (n : ℕ)
    (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
    {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}}
    (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (hι : IsColimitPresentation.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι)
    (h : Nonempty (IsColimit (stdCocone hu hobj hhom hhom_inj hK 𝒜 n F))) :
    Nonempty (IsColimit (extCocone 𝒜 F ι n hι.1)) := by
  obtain ⟨hc⟩ := h
  obtain ⟨e, he⟩ := colimitPresentation_uniqueIso D uC hu K F
    (systemColimitSheaf D uC hu hobj hhom hhom_inj K hK F) 𝒢 _ ι
    (systemColimitSheaf_isColimitPresentation D uC hu hobj hhom hhom_inj K hK F) hι
  have hleg : ∀ j, systemLeg (K := K) (kanLegs hu hobj hhom hhom_inj hK F) j ≫ e.hom =
      systemLeg (K := K) ι j := by
    intro j
    rw [systemLeg_comp]
    congr 1
    exact funext he
  have key : ∀ (A : Over i) (x : Abelian.Ext.{max u v w} (𝒜.obj A) (F.obj A.left) n),
      extConj (𝟙 _) e.hom (extLeg 𝒜 F (kanLegs hu hobj hhom hhom_inj hK F) n A x) =
        extLeg 𝒜 F ι n A x := by
    intro A x
    rw [extLeg_apply, extLeg_apply, extConj_extConj, Category.id_comp, hleg]
  refine ⟨IsColimit.ofIsoColimit hc (Cocones.ext (extPostIso.{max u v w} 𝒜.top e n) (fun A => ?_))⟩
  ext x
  exact key A.unop x

end Transfer

end Stacks.WeakSites.ExtColimit

end
