module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification

/-!
# Factoring a point of a presented affine formal algebraic space through a given stage

Let `X` be presented as the colimit of the spectra `Spec (A ⧸ J)` of the quotients of a weakly
admissible topological ring `A` by its weak ideals of definition (Stacks 0AIC, condition (1)). A
morphism `h_V^# ⟶ X` out of the sheaf represented by an affine scheme `V = Spec C` factors through
some stage `Spec (A ⧸ J)` (the argument of Stacks 0AIA). If moreover every ring map `A ⧸ J → C`
kills a fixed weak ideal of definition `J₁`, then the factorization can be taken through the stage
`Spec (A ⧸ J₁)` itself, and it is unique there, the stages being subsheaves of `X`.

This is used for `C` with square-zero nilradical and `J₁ = I²` for an ideal of definition `I`:
the image of `I` in `C` consists of nilpotent elements.

## Main results

* `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.existsUnique_stage_factor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  {X : FppfSheaf B S hS} (P : WeakIdealColimitPresentation B S hS A X)

/-- The weak ideals of definition of a weakly admissible ring form a nonempty directed set. -/
theorem weakIdeals_nonempty_isDirected (hA : TopologicalRing.IsWeaklyAdmissible A) :
    Nonempty (WeakIdeals A) ∧ IsDirected (WeakIdeals A) (· ≤ ·) := by
  refine ⟨?_, ⟨fun J K => ?_⟩⟩
  · obtain ⟨J, hJ⟩ := hA.1
    exact ⟨OrderDual.toDual ⟨J, hJ⟩⟩
  · exact ⟨OrderDual.toDual ⟨J.1 ⊓ K.1, ⟨J.2.1.inter K.2.1, fun x hx => J.2.2 x hx.1⟩⟩,
      (inf_le_left : J.1 ⊓ K.1 ≤ J.1), (inf_le_right : J.1 ⊓ K.1 ≤ K.1)⟩

/-- The stages are subsheaves of `X`. -/
theorem mono_quotientMap (hA : TopologicalRing.IsWeaklyAdmissible A) (J : WeakIdeals A) :
    Mono (quotientMap B S hS A X P J) := by
  obtain ⟨_, _⟩ := weakIdeals_nonempty_isDirected (A := A) hA
  have : Mono (colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) J) := by
    apply Sheaf.mono_colimit_ι_of_mono_transition
    intro J K f
    have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f))) :=
      (weak_quotient_transition_isThickening B S hS A X P f).1
    exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying (BigFppfOver.topology B S hS)
      (BigFppfOver.toScheme B S hS) ((BigAffineFppf.inclusion B S hS).map (P.diagram.map f))
      inferInstance
  infer_instance

/-- A morphism of underlying schemes `W → Y` lifting `g : W ⟶ Z` along `f : Y ⟶ Z` comes from a
morphism `σ : W ⟶ Y` of the big fppf category over `S` with `σ ≫ f = g`. -/
theorem _root_.AlgebraicGeometry.BigFppfOver.exists_comp_eq_of_toScheme_comp_eq
    {W Y Z : BigFppfOver B S hS} (f : Y ⟶ Z) (g : W ⟶ Z)
    (h : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (hh : h ≫ (BigFppfOver.toScheme B S hS).map f = (BigFppfOver.toScheme B S hS).map g) :
    ∃ σ : W ⟶ Y, σ ≫ f = g := by
  refine ⟨Over.homMk (B.inclusion.preimage (X := W.left) (Y := Y.left) h) ?_, ?_⟩
  · apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage, ← Over.w f, Functor.map_comp, ← Category.assoc]
    change (h ≫ (BigFppfOver.toScheme B S hS).map f) ≫ _ = _
    rw [hh]
    change B.inclusion.map g.left ≫ _ = _
    rw [← Functor.map_comp, Over.w g]
  · apply (BigFppfOver.forget B S hS).map_injective
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage (X := W.left) (Y := Y.left) h ≫ f.left) = _
    rwa [Functor.map_comp, Functor.map_preimage]

/-- Let `W` be an object of the site whose underlying scheme is `Spec C`, and let `J₁` be a weak
ideal of definition of `A` killed by every ring map `A ⧸ J → C` out of a quotient by a weak ideal
of definition. Then every morphism `h_W^# ⟶ X` factors through the stage `Spec (A ⧸ J₁)`. -/
theorem exists_stage_factor (hA : TopologicalRing.IsWeaklyAdmissible A)
    (J₁ : WeakIdeals A) (C : CommRingCat.{u}) (W : BigFppfOver B S hS)
    (eW : (BigFppfOver.toScheme B S hS).obj W = Spec C)
    (hJ₁ : ∀ (M : WeakIdeals A) (ρ : A ⧸ M.1 →+* C) (x : A), x ∈ J₁.1 →
      ρ (Ideal.Quotient.mk M.1 x) = 0)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ X) :
    ∃ σ : W ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J₁),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map σ ≫
        quotientMap B S hS A X P J₁ = a := by
  obtain ⟨_, hdir⟩ := weakIdeals_nonempty_isDirected (A := A) hA
  let Jt := BigFppfOver.topology B S hS
  let V : BigAffineFppf B S hS := ⟨W, by
    change IsAffine ((BigFppfOver.toScheme B S hS).obj W)
    rw [eW]
    infer_instance⟩
  let D := P.diagram
  obtain ⟨j, g, hg⟩ := exists_factor_to_affine_stage B S hS X (WeakIdeals A) D
    (fun _ _ f => weak_quotient_transition_isThickening B S hS A X P f) P.colimitIso V a
  obtain ⟨m, hjm, h1m⟩ := hdir.directed j J₁
  let g' : V ⟶ D.obj m := g ≫ D.map (homOfLE hjm)
  let ψ : Spec C ⟶ Spec (.of (A ⧸ m.1)) :=
    eqToHom eW.symm ≫ (BigAffineFppf.toScheme B S hS).map g' ≫ (P.quotientIso m).hom
  let ρ : CommRingCat.of (A ⧸ m.1) ⟶ C := Spec.preimage ψ
  let ρ₁ : A ⧸ J₁.1 →+* C := Ideal.Quotient.lift J₁.1 (ρ.hom.comp (Ideal.Quotient.mk m.1))
    (fun x hx => hJ₁ m ρ.hom x hx)
  have hρ₁ : (CommRingCat.ofHom (Ideal.Quotient.factor (show m.1 ≤ J₁.1 from h1m)) ≫
      CommRingCat.ofHom ρ₁) = ρ := by
    ext x
    rfl
  let h : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigAffineFppf.toScheme B S hS).obj (D.obj J₁) :=
    eqToHom eW ≫ Spec.map (CommRingCat.ofHom ρ₁) ≫ (P.quotientIso J₁).inv
  have hkey : h ≫ (BigAffineFppf.toScheme B S hS).map (D.map (homOfLE h1m)) =
      (BigAffineFppf.toScheme B S hS).map g' := by
    rw [← cancel_mono (P.quotientIso m).hom, Category.assoc, P.quotientIso_natural]
    simp only [h, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp, hρ₁, Spec.map_preimage ψ]
    simp [ψ]
  obtain ⟨σ, hσ⟩ := BigFppfOver.exists_comp_eq_of_toScheme_comp_eq
    ((BigAffineFppf.inclusion B S hS).map (D.map (homOfLE h1m)))
    ((BigAffineFppf.inclusion B S hS).map g') h hkey
  let F := D ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda Jt
  have hcomp : (Sheaf.sheafifiedYoneda Jt).map σ ≫ colimit.ι F J₁ =
      (Sheaf.sheafifiedYoneda Jt).map ((BigAffineFppf.inclusion B S hS).map g) ≫
        colimit.ι F j := by
    rw [← colimit.w F (homOfLE h1m), ← colimit.w F (homOfLE hjm)]
    simp only [F, Functor.comp_map, ← Functor.map_comp_assoc, hσ]
    rfl
  have hfac : (Sheaf.sheafifiedYoneda Jt).map σ ≫ quotientMap B S hS A X P J₁ = a := by
    change (Sheaf.sheafifiedYoneda Jt).map σ ≫ colimit.ι F J₁ ≫ P.colimitIso.inv = a
    rwa [← Category.assoc, hcomp, Category.assoc]
  exact ⟨σ, hfac⟩

/-- **Factoring a point through a prescribed stage.** Let `W` be an object of the site whose
underlying scheme is `Spec C`, and let `J₁` be a weak ideal of definition of `A` killed by every
ring map `A ⧸ J → C` out of a quotient by a weak ideal of definition. Then every morphism
`h_W^# ⟶ X` factors uniquely through the stage `Spec (A ⧸ J₁)`. -/
theorem existsUnique_stage_factor (hA : TopologicalRing.IsWeaklyAdmissible A)
    (J₁ : WeakIdeals A) (C : CommRingCat.{u}) (W : BigFppfOver B S hS)
    (eW : (BigFppfOver.toScheme B S hS).obj W = Spec C)
    (hJ₁ : ∀ (M : WeakIdeals A) (ρ : A ⧸ M.1 →+* C) (x : A), x ∈ J₁.1 →
      ρ (Ideal.Quotient.mk M.1 x) = 0)
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ X) :
    ∃! σ : W ⟶ (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj J₁),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map σ ≫
        quotientMap B S hS A X P J₁ = a := by
  obtain ⟨σ, hσ⟩ := P.exists_stage_factor hA J₁ C W eW hJ₁ a
  have := P.mono_quotientMap hA J₁
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  exact ⟨σ, hσ, fun σ' hσ' =>
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
      ((cancel_mono _).mp (hσ'.trans hσ.symm))⟩

end AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation

end
