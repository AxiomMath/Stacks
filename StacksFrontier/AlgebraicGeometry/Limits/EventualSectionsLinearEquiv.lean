module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Limits.EventualModuleIsoSection
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic

/-!
# Descending a linear equivalence of global sections through a limit of affine schemes

Let `G` be a cofiltered diagram of affine schemes with affine transition morphisms and let `cG`
be a limit cone on it whose apex is affine. Let `F` and `F'` be sheaves of modules of finite
presentation on a stage `G.obj j₀`. A `Γ(cG.pt, ⊤)`-linear equivalence `v` of the global sections
of their pullbacks to the limit descends: at some stage over `j₀` there is a
`Γ(G.obj j, ⊤)`-linear equivalence `w` of the global sections of the pullbacks there whose base
change to the limit is `v`. Moreover, if `a : P ⟶ F` and `b : P ⟶ F'` are morphisms from a third
sheaf of finite presentation which `v` identifies on global sections, then `w` can be found
identifying them too.

## Main results

* `AlgebraicGeometry.exists_iso_app_top_eq`: on an affine scheme, a linear equivalence of the
  global sections of two quasi-coherent sheaves of modules is the action on global sections of an
  isomorphism of sheaves of modules.
* `AlgebraicGeometry.exists_stage_sections_linearEquiv_of_isLimit`: the descent of a linear
  equivalence of global sections, with the identification of two prescribed morphisms.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open Stacks.AlgebraicGeometry.ModuleLimits (canHom isFinitePresentation_pullback
  hom_ext_of_app_top exists_hom_app_top_eq)
open Stacks.AlgebraicGeometry.SectionsBaseChange (le_preimage_top)

universe u

namespace AlgebraicGeometry

/-! ### Morphisms of sheaves of modules read on global sections -/

/-- A composite of morphisms of sheaves of modules acts on a global section by the two actions in
turn. -/
private theorem comp_app_top_apply {X : Scheme.{u}} {M N Q : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ Q)
    (t : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app (φ ≫ ψ) ⊤ t
      = Scheme.Modules.Hom.app ψ ⊤ (Scheme.Modules.Hom.app φ ⊤ t) := by
  rw [Scheme.Modules.Hom.comp_app]
  rfl

/-- The identity morphism of a sheaf of modules fixes every global section. -/
private theorem id_app_top_apply {X : Scheme.{u}} {M : X.Modules} (t : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app (𝟙 M) ⊤ t = t := by
  rw [Scheme.Modules.Hom.id_app]
  rfl

/-- Two morphisms of sheaves of modules out of a composite are equal once they agree on global
sections. -/
private theorem comp_eq_of_app_top {X : Scheme.{u}} [IsAffine X] {M N Q : X.Modules}
    [M.IsQuasicoherent] [Q.IsQuasicoherent] (φ : M ⟶ N) (ψ : N ⟶ Q) (ρ : M ⟶ Q)
    (h : ∀ t : Γ(M, ⊤), Scheme.Modules.Hom.app ψ ⊤ (Scheme.Modules.Hom.app φ ⊤ t) =
      Scheme.Modules.Hom.app ρ ⊤ t) : φ ≫ ψ = ρ :=
  hom_ext_of_app_top fun t => (comp_app_top_apply φ ψ t).trans (h t)

/-! ### Reading a linear equivalence of global sections as an isomorphism of sheaves -/

/-- On an affine scheme, every `Γ(X, ⊤)`-linear equivalence between the global sections of two
quasi-coherent sheaves of modules is the action on global sections of an isomorphism of sheaves
of modules. -/
theorem exists_iso_app_top_eq {X : Scheme.{u}} [IsAffine X] {F F' : X.Modules}
    [F.IsQuasicoherent] [F'.IsQuasicoherent] (v : Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(F', ⊤)) :
    ∃ N : F ≅ F', ∀ s : Γ(F, ⊤), N.hom.app ⊤ s = v s := by
  obtain ⟨χ, hχ⟩ := exists_hom_app_top_eq (F := F) (G := F') v.toLinearMap
  obtain ⟨χ', hχ'⟩ := exists_hom_app_top_eq (F := F') (G := F) v.symm.toLinearMap
  refine ⟨⟨χ, χ', ?_, ?_⟩, hχ⟩
  · exact comp_eq_of_app_top _ _ _ fun s => by
      rw [id_app_top_apply, hχ, hχ']
      exact v.symm_apply_apply s
  · exact comp_eq_of_app_top _ _ _ fun s => by
      rw [id_app_top_apply, hχ', hχ]
      exact v.apply_symm_apply s

/-! ### The descent -/

/-- Let `cG` be a limit cone on a cofiltered diagram `G` of affine schemes with affine transition
morphisms and affine apex, let `P`, `F`, `F'` be sheaves of modules of finite presentation on a
stage `G.obj j₀`, and let `a : P ⟶ F`, `b : P ⟶ F'`. Let `v` be a `Γ(cG.pt, ⊤)`-linear equivalence
of the global sections of the pullbacks of `F` and `F'` to the limit which carries the action of
the pullback of `a` to the action of the pullback of `b`. Then some stage over `j₀` carries a
`Γ(G.obj j, ⊤)`-linear equivalence `w` of the global sections of the pullbacks of `F` and `F'`
there which carries the action of the pullback of `a` to the action of the pullback of `b` already
at that stage, and whose base change to the limit is `v`. -/
theorem exists_stage_sections_linearEquiv_of_isLimit {J : Type u} [Category.{u} J]
    [IsCofiltered J] (G : J ⥤ Scheme.{u})
    [∀ {a b : J} (g : a ⟶ b), IsAffineHom (G.map g)] [∀ a : J, IsAffine (G.obj a)]
    (cG : Cone G) (hcG : IsLimit cG) [IsAffine cG.pt] (j₀ : J)
    (P F F' : (G.obj j₀).Modules) (hP : P.IsFinitePresentation)
    (hF : F.IsFinitePresentation) (hF' : F'.IsFinitePresentation)
    (a : P ⟶ F) (b : P ⟶ F')
    (v : Γ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj F, ⊤) ≃ₗ[Γ(cG.pt, ⊤)]
      Γ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj F', ⊤))
    (hv : ∀ t : Γ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj P, ⊤),
      v (((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).map a).app ⊤ t) =
        ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).map b).app ⊤ t) :
    ∃ (j : J) (e : j ⟶ j₀)
      (w : Γ((Scheme.Modules.pullback (G.map e)).obj F, ⊤) ≃ₗ[Γ(G.obj j, ⊤)]
        Γ((Scheme.Modules.pullback (G.map e)).obj F', ⊤)),
      (∀ t : Γ((Scheme.Modules.pullback (G.map e)).obj P, ⊤),
          w (((Scheme.Modules.pullback (G.map e)).map a).app ⊤ t) =
            ((Scheme.Modules.pullback (G.map e)).map b).app ⊤ t) ∧
        ∀ x : Γ((Scheme.Modules.pullback (G.map e)).obj F, ⊤),
          (canHom (cG.π.app j) (G.map e) (cG.π.app j₀) (cG.w e) F').app ⊤
              (Scheme.Modules.pullbackSection (cG.π.app j)
                ((Scheme.Modules.pullback (G.map e)).obj F') ⊤ ⊤
                (le_preimage_top (cG.π.app j) ⊤) (w x)) =
            v ((canHom (cG.π.app j) (G.map e) (cG.π.app j₀) (cG.w e) F).app ⊤
              (Scheme.Modules.pullbackSection (cG.π.app j)
                ((Scheme.Modules.pullback (G.map e)).obj F) ⊤ ⊤
                (le_preimage_top (cG.π.app j) ⊤) x)) := by
  have hPl : ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj P).IsFinitePresentation :=
    isFinitePresentation_pullback _ P
  have hFl : ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback _ F
  have hF'l :
      ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj F').IsFinitePresentation :=
    isFinitePresentation_pullback _ F'
  have hPlq : ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj P).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation _
  have hFlq : ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation _
  have hF'lq : ((Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj F').IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation _
  obtain ⟨N, hN⟩ := exists_iso_app_top_eq (X := cG.pt) v
  have hab : (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).map a ≫ N.hom =
      (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).map b := by
    exact comp_eq_of_app_top _ _ _ fun t => by rw [hN]; exact hv t
  obtain ⟨j, e, mm, hcanon, hsec⟩ :=
    exists_stage_isIso_pullback_map_comp_eq G cG hcG j₀ P F F' hP hF hF' N a b hab
  refine ⟨j, e, sectionsLinearEquivOfIso mm ⊤, fun t => ?_, fun x => ?_⟩
  · refine Eq.trans (comp_app_top_apply ((Scheme.Modules.pullback (G.map e)).map a)
      mm.hom t).symm ?_
    rw [hsec]
  · have hpull :
        Scheme.Modules.Hom.app ((Scheme.Modules.pullback (cG.π.app j)).map mm.hom) ⊤
            (Scheme.Modules.pullbackSection (cG.π.app j)
              ((Scheme.Modules.pullback (G.map e)).obj F) ⊤ ⊤
              (le_preimage_top (cG.π.app j) ⊤) x)
          = Scheme.Modules.pullbackSection (cG.π.app j)
              ((Scheme.Modules.pullback (G.map e)).obj F') ⊤ ⊤
              (le_preimage_top (cG.π.app j) ⊤) (Scheme.Modules.Hom.app mm.hom ⊤ x) :=
      Scheme.Modules.pullbackSection_naturality (cG.π.app j) mm.hom ⊤ ⊤
        (le_preimage_top (cG.π.app j) ⊤) x
    have h := congrArg (fun k => Scheme.Modules.Hom.app k ⊤
      (Scheme.Modules.pullbackSection (cG.π.app j)
        ((Scheme.Modules.pullback (G.map e)).obj F) ⊤ ⊤
        (le_preimage_top (cG.π.app j) ⊤) x)) hcanon
    have hL := comp_app_top_apply ((Scheme.Modules.pullback (cG.π.app j)).map mm.hom)
      (canHom (cG.π.app j) (G.map e) (cG.π.app j₀) (cG.w e) F')
      (Scheme.Modules.pullbackSection (cG.π.app j)
        ((Scheme.Modules.pullback (G.map e)).obj F) ⊤ ⊤
        (le_preimage_top (cG.π.app j) ⊤) x)
    have hR := comp_app_top_apply (canHom (cG.π.app j) (G.map e) (cG.π.app j₀) (cG.w e) F)
      N.hom
      (Scheme.Modules.pullbackSection (cG.π.app j)
        ((Scheme.Modules.pullback (G.map e)).obj F) ⊤ ⊤
        (le_preimage_top (cG.π.app j) ⊤) x)
    rw [sectionsLinearEquivOfIso_apply, ← hpull, ← hN]
    exact hL.symm.trans (h.trans hR)

end AlgebraicGeometry

end
