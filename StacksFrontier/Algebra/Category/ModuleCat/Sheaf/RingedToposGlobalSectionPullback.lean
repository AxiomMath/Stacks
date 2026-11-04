module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTransferOfInverseImageIso
public import StacksFrontier.CategoryTheory.Limits.TerminalGlobalSectionMap

/-!
# Pulling back global sections of the structure sheaf along a morphism of ringed topoi

A morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` carries a global section
`t : ⊤ ⟶ O_D` of the structure sheaf of its target to the global section
`f^♯(f⁻¹t) : ⊤ ≅ f⁻¹⊤ ⟶ f⁻¹O_D ⟶ O_C` of the structure sheaf of its source, on underlying
sheaves of sets (`AlgebraicGeometry.RingedToposHom.globalSectionPullback`). It is the adjunct of
`t ≫ f♯ : ⊤ ⟶ f_*O_C`, so it only sees the morphism up to 2-isomorphism: any isomorphism of
direct images is invisible on global sections, the terminal object being preserved by both
adjoints. It is functorial for composition.

For the isomorphism `Φ = (g₂, id) ∘ (g₁, d)⁻¹` determined by an isomorphism
`d : g₁⁻¹O₁ ≅ g₂⁻¹O₂` (`AlgebraicGeometry.RingedToposHom.transferOfInverseImageIso`), this computes
`Φ` on global sections from `d`: a global section of `O₂` whose inverse image along `g₂` is the
image under `d` of the inverse image along `g₁` of a global section of `O₁` pulls back along `Φ`
to that section. This is how an isomorphism of the extensions of two deformations is read on the
functions of their total spaces in the proof of Stacks 0D1K.

## Main results

* `AlgebraicGeometry.RingedToposHom.globalSectionPullback_eq_of_twoIso`
* `AlgebraicGeometry.RingedToposHom.globalSectionPullback_comp`
* `AlgebraicGeometry.RingedToposHom.globalSectionPullback_transferOfInverseImageIso`

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

namespace AlgebraicGeometry.RingedToposHom

universe w v₁ u₁ v₂ u₂ v₃ u₃

section Generic

variable {A : RingedTopos.{v₁, u₁, w}} {B : RingedTopos.{v₂, u₂, w}}
  {C : RingedTopos.{v₃, u₃, w}}
  [A.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w})]
  [C.J.HasSheafCompose (forget RingCat.{w})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [A.J.HasSheafCompose (forget CommRingCat.{w})] [B.J.HasSheafCompose (forget CommRingCat.{w})]
  [C.J.HasSheafCompose (forget CommRingCat.{w})]

/-- **The pullback of a global section of the structure sheaf** along a morphism of ringed topoi
`f`: the inverse image `f⁻¹t` of `t : ⊤ ⟶ O_D` followed by `f^♯ : f⁻¹O_D ⟶ O_C`, on underlying
sheaves of sets. -/
def globalSectionPullback (f : RingedToposHom A B) (t : ⊤_ B.Topos ⟶ B.forgetRing.obj B.O) :
    ⊤_ A.Topos ⟶ A.forgetRing.obj A.O :=
  f.toToposHom.inverseImage.globalSectionMap t ≫ A.forgetRing.map f.fSharpInverseImage

/-- **The pullback of a global section is the adjunct of `t ≫ f♯`.** -/
theorem homEquiv_terminalComparison_comp_globalSectionPullback (f : RingedToposHom A B)
    (t : ⊤_ B.Topos ⟶ B.forgetRing.obj B.O) :
    f.toToposHom.adj.homEquiv _ _
        (terminalComparison f.toToposHom.inverseImage ≫ f.globalSectionPullback t) =
      t ≫ forgetFSharp f := by
  refine (Equiv.eq_symm_apply _).1 ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_left_symm _ _ _).symm
  refine Eq.trans ?_ (congrArg (f.toToposHom.inverseImage.map t ≫ ·)
    (forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget f))
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (IsIso.hom_inv_id_assoc _ _))

/-- A global section of `O_C` is determined by its adjunct. -/
theorem eq_globalSectionPullback_of_homEquiv_eq (f : RingedToposHom A B)
    (t : ⊤_ B.Topos ⟶ B.forgetRing.obj B.O) (w : ⊤_ A.Topos ⟶ A.forgetRing.obj A.O)
    (h : f.toToposHom.adj.homEquiv _ _ (terminalComparison f.toToposHom.inverseImage ≫ w) =
      t ≫ forgetFSharp f) :
    w = f.globalSectionPullback t :=
  (cancel_epi (terminalComparison f.toToposHom.inverseImage)).1
    ((f.toToposHom.adj.homEquiv _ _).injective
      (h.trans (homEquiv_terminalComparison_comp_globalSectionPullback f t).symm))

/-- **Global sections do not see 2-isomorphisms**: 2-isomorphic morphisms of ringed topoi pull
back global sections of the structure sheaf in the same way. -/
theorem globalSectionPullback_eq_of_twoIso {f g : RingedToposHom A B} (s : TwoIso f g)
    (t : ⊤_ B.Topos ⟶ B.forgetRing.obj B.O) :
    f.globalSectionPullback t = g.globalSectionPullback t := by
  refine eq_globalSectionPullback_of_homEquiv_eq g t _ ?_
  have := g.toToposHom.adj.rightAdjoint_preservesLimits
  have hterm : IsTerminal (g.toToposHom.pushforward.obj (⊤_ A.Topos)) :=
    terminalIsTerminal.isTerminalObj g.toToposHom.pushforward _
  have ht : f.toToposHom.adj.unit.app (⊤_ B.Topos) ≫
      f.toToposHom.pushforward.map (terminalComparison f.toToposHom.inverseImage) ≫
        s.e.hom.app (⊤_ A.Topos) =
      g.toToposHom.adj.unit.app (⊤_ B.Topos) ≫
        g.toToposHom.pushforward.map (terminalComparison g.toToposHom.inverseImage) :=
    hterm.hom_ext _ _
  rw [← s.commutes, ← Category.assoc, ← homEquiv_terminalComparison_comp_globalSectionPullback,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, s.e.hom.naturality]
  exact ((reassoc_of% ht) _).symm

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **Pulling back global sections is functorial**: along `g ∘ f` it is pulling back along `g`
and then along `f`. -/
theorem globalSectionPullback_comp (g : RingedToposHom B C) (f : RingedToposHom A B)
    (t : ⊤_ C.Topos ⟶ C.forgetRing.obj C.O) :
    (g.comp f).globalSectionPullback t = f.globalSectionPullback (g.globalSectionPullback t) := by
  symm
  refine eq_globalSectionPullback_of_homEquiv_eq (g.comp f) t _ ?_
  have htc : terminalComparison (g.comp f).toToposHom.inverseImage =
      f.toToposHom.inverseImage.map (terminalComparison g.toToposHom.inverseImage) ≫
        terminalComparison f.toToposHom.inverseImage :=
    terminal.hom_ext _ _
  rw [forgetFSharp_comp, htc, Category.assoc]
  show (g.toToposHom.adj.comp f.toToposHom.adj).homEquiv _ _ _ = _
  rw [Adjunction.comp_homEquiv_apply, Adjunction.homEquiv_naturality_left,
    homEquiv_terminalComparison_comp_globalSectionPullback, ← Category.assoc,
    Adjunction.homEquiv_naturality_right, homEquiv_terminalComparison_comp_globalSectionPullback,
    Category.assoc]

/-- The pullback of a global section along `AlgebraicGeometry.RingedToposHom.ofInverseImageMap`
is its inverse image followed by the prescribed map. -/
theorem globalSectionPullback_ofInverseImageMap {X : RingedTopos.{v₁, u₁, w}}
    {Y : RingedTopos.{v₂, u₂, w}} [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
    (f : MorphismOfTopoi X.Topos Y.Topos)
    (α : (inverseImageCommRingFunctor f).obj Y.O ⟶ X.O) (t : ⊤_ Y.Topos ⟶ Y.forgetRing.obj Y.O) :
    (ofInverseImageMap f α).globalSectionPullback t =
      f.inverseImage.globalSectionMap t ≫ X.forgetRing.map α :=
  congrArg (fun m => f.inverseImage.globalSectionMap t ≫ X.forgetRing.map m)
    (ofInverseImageMap_fSharpInverseImage f α)

/-- The pullback of a global section along `AlgebraicGeometry.RingedToposHom.ofInverseImageIso`
is its inverse image followed by the prescribed isomorphism. -/
theorem globalSectionPullback_ofInverseImageIso {X : RingedTopos.{v₁, u₁, w}}
    {Y : RingedTopos.{v₂, u₂, w}} [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
    (f : MorphismOfTopoi X.Topos Y.Topos)
    (e : (inverseImageCommRingFunctor f).obj Y.O ≅ X.O) (t : ⊤_ Y.Topos ⟶ Y.forgetRing.obj Y.O) :
    (ofInverseImageIso f e).globalSectionPullback t =
      f.inverseImage.globalSectionMap t ≫ X.forgetRing.map e.hom :=
  globalSectionPullback_ofInverseImageMap f e.hom t

end Generic

section Transfer

universe v u

variable {X Y₁ Y₂ T : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})] [T.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y₁.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y₂.J.HasSheafCompose (forget CommRingCat.{w})] [T.J.HasSheafCompose (forget CommRingCat.{w})]
  (g₁ : RingedToposHom X Y₁) (g₂ : RingedToposHom X Y₂)
  [g₁.toToposHom.pushforward.IsEquivalence] [g₂.toToposHom.pushforward.IsEquivalence]
  (d : (inverseImageCommRingFunctor g₁.toToposHom).obj Y₁.O ≅
    (inverseImageCommRingFunctor g₂.toToposHom).obj Y₂.O)

/-- **Pulling back along an isomorphism and then along its inverse** is pulling back along the
identity, on the global sections pulled back from a further ringed topos. -/
theorem globalSectionPullback_inverse_globalSectionPullback {Y : RingedTopos.{v, u, w}}
    [Y.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget CommRingCat.{w})]
    (σ : RingedToposHom Y T) (h : RingedToposHom X Y) [h.toToposHom.pushforward.IsEquivalence]
    [IsIso h.fSharp] (t : ⊤_ T.Topos ⟶ T.forgetRing.obj T.O) :
    h.inverse.globalSectionPullback (h.globalSectionPullback (σ.globalSectionPullback t)) =
      σ.globalSectionPullback t :=
  (congrArg h.inverse.globalSectionPullback (globalSectionPullback_comp σ h t).symm).trans
    ((globalSectionPullback_comp (σ.comp h) h.inverse t).symm.trans
      (globalSectionPullback_eq_of_twoIso (compCompInverseTwoIso σ h) t))

/-- **The transfer `Φ = (g₂, id) ∘ (g₁, d)⁻¹` on global sections.** Let `σ : (Sh(D₁), O₁) ⟶ T`,
let `t` be a global section of `O_T` and `y₁ = σ^♯t`. A global section `y` of `O₂` whose inverse
image along `g₂` is the image under `d` of the inverse image along `g₁` of `y₁` pulls back along
`Φ` to `y₁`. -/
theorem globalSectionPullback_transferOfInverseImageIso (σ : RingedToposHom Y₁ T)
    (t : ⊤_ T.Topos ⟶ T.forgetRing.obj T.O) (y₁ : ⊤_ Y₁.Topos ⟶ Y₁.forgetRing.obj Y₁.O)
    (h₁ : σ.globalSectionPullback t = y₁) (y : ⊤_ Y₂.Topos ⟶ Y₂.forgetRing.obj Y₂.O)
    (hy : g₂.toToposHom.inverseImage.globalSectionMap y =
      g₁.toToposHom.inverseImage.globalSectionMap y₁ ≫ X.forgetRing.map d.hom) :
    (transferOfInverseImageIso g₁ g₂ d).globalSectionPullback y = y₁ := by
  subst h₁
  have hT : (transferTarget g₂).globalSectionPullback y =
      (transferSource g₁ g₂ d).globalSectionPullback (σ.globalSectionPullback t) := by
    rw [globalSectionPullback_ofInverseImageIso, globalSectionPullback_ofInverseImageIso,
      ← hy, Iso.refl_hom]
    exact (congrArg (_ ≫ ·) ((pulledBackStructureRingedTopos g₂).forgetRing.map_id _)).trans
      (Category.comp_id _)
  exact (globalSectionPullback_comp (transferTarget g₂) (transferSource g₁ g₂ d).inverse y).trans
    ((congrArg (transferSource g₁ g₂ d).inverse.globalSectionPullback hT).trans
      (globalSectionPullback_inverse_globalSectionPullback σ (transferSource g₁ g₂ d) t))

end Transfer

end AlgebraicGeometry.RingedToposHom

end
