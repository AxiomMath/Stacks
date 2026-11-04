module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic

/-!
# The affine case of Tag 01ZR (2) over an affine open of a stage

Let `D` be a cofiltered diagram of schemes with affine transition morphisms, `c` a limit cone,
`i` a stage and `V` an **affine** open of `D i`. The preimages of `V` in the stages over `i` form
a cofiltered diagram of affine schemes with limit the preimage of `V` in `c.pt`
(`AlgebraicGeometry.EventualLimit.preimageDiagram`). This file proves the affine case of
[Stacks Project, Tag 01ZR] (2) for that diagram, and states its conclusion as a
`Stacks.AlgebraicGeometry.ModuleLimits.LocalDescent` datum, the localized canonical equation of
the tag.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_canonical_of_descend`: for a composite
  `q ≫ g = pi` of morphisms of affine schemes, a map of modules over the sections of the
  intermediate scheme which base-changes to the given morphism of sheaves is the action on
  sections of a morphism satisfying the canonical equation of the tag.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_localDescent_of_resLE_canonical_eq`: the canonical
  equation at the restricted morphisms gives a local descent datum.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_eq_resLE_of_isAffineOpen`: the affine
  case of the tag over an affine open `V` of the stage, stated for the **restricted** morphisms
  `AlgebraicGeometry.Scheme.Hom.resLE`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_localDescent_of_isAffineOpen`: the same, read as
  a local descent datum over `D.map k.hom ⁻¹ᵁ V`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Stacks.ModuleCat Stacks.AlgebraicGeometry.SectionsBaseChange

/-! ### The affine case, from a descended map of sections -/

/-- **The affine case of [Stacks Project, Tag 01ZR] (2) from a descended map of sections.**  Let
`q ≫ g = pi` be a composite of morphisms of affine schemes, `f : Γ(Z, ⊤) →ₐ[Γ(X, ⊤)] Γ(W, ⊤)` the
algebra map of `q`, `u` a map of the base changes to `Γ(W, ⊤)` of the global sections of `A` and
`B` which is `φ` on global sections, and `ul` a map of the base changes to `Γ(Z, ⊤)` which `f`
carries to `u`. Then there is a morphism `g^*A ⟶ g^*B` whose pullback along `q` becomes `φ` under
the canonical identification. -/
theorem exists_map_canonical_of_descend {W Z X : Scheme.{u}} [IsAffine W] [IsAffine Z]
    [IsAffine X] (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)
    (A B : X.Modules) [A.IsFinitePresentation] [B.IsFinitePresentation]
    [A.IsQuasicoherent] [B.IsQuasicoherent]
    (φ : (Scheme.Modules.pullback pi).obj A ⟶ (Scheme.Modules.pullback pi).obj B)
    (f : letI : Algebra Γ(X, ⊤) Γ(Z, ⊤) := (Scheme.Hom.appTop g).hom.toAlgebra
         letI : Algebra Γ(X, ⊤) Γ(W, ⊤) := (Scheme.Hom.appTop pi).hom.toAlgebra
         Γ(Z, ⊤) →ₐ[Γ(X, ⊤)] Γ(W, ⊤))
    (hf : ∀ β : Γ(Z, ⊤), f β = (Scheme.Hom.appTop q).hom β)
    (u : (ModuleCat.extendScalars (Scheme.Hom.appTop pi).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(A, ⊤)) ⟶
        (ModuleCat.extendScalars (Scheme.Hom.appTop pi).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(B, ⊤)))
    (hu : u ≫ (bcTop pi B).hom = (bcTop pi A).hom ≫ appTopHom φ)
    (ul : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(A, ⊤)) ⟶
        (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
          (ModuleCat.of Γ(X, ⊤) ↑Γ(B, ⊤)))
    (hul : letI : Algebra Γ(X, ⊤) Γ(Z, ⊤) := (Scheme.Hom.appTop g).hom.toAlgebra
           letI : Algebra Γ(X, ⊤) Γ(W, ⊤) := (Scheme.Hom.appTop pi).hom.toAlgebra
           ∀ y : (ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).obj
             (ModuleCat.of Γ(X, ⊤) ↑Γ(A, ⊤)),
             u (LinearMap.rTensor (↑Γ(A, ⊤)) f.toLinearMap y)
               = LinearMap.rTensor (↑Γ(B, ⊤)) f.toLinearMap (ul y)) :
    ∃ φj : (Scheme.Modules.pullback g).obj A ⟶ (Scheme.Modules.pullback g).obj B,
      (Scheme.Modules.pullback q).map φj ≫ canHom q g pi hpi B
        = canHom q g pi hpi A ≫ φ := by
  have hfpgA := isFinitePresentation_pullback g A
  have hfpgB := isFinitePresentation_pullback g B
  have hqcgA := _root_.isQuasicoherent_of_isFinitePresentation ((Scheme.Modules.pullback g).obj A)
  have hqcgB := _root_.isQuasicoherent_of_isFinitePresentation ((Scheme.Modules.pullback g).obj B)
  have hD := Stacks.ModuleCat.extendScalars_map_comp_cancelIsoApp
    (Scheme.Hom.appTop g).hom (Scheme.Hom.appTop q).hom (Scheme.Hom.appTop pi).hom
    (hp_triangle q g pi hpi)
    (ModuleCat.of Γ(X, ⊤) ↑Γ(A, ⊤)) (ModuleCat.of Γ(X, ⊤) ↑Γ(B, ⊤)) f hf u ul hul
  obtain ⟨φj, hφj0⟩ := exists_hom_app_top_eq (X := Z)
    (F := (Scheme.Modules.pullback g).obj A) (G := (Scheme.Modules.pullback g).obj B)
    ((bcTop g A).inv ≫ ul ≫ (bcTop g B).hom).hom
  refine ⟨φj, canonical_eq_of_descend q g pi hpi A B φ φj ul ?_ ?_⟩
  · have h1 : appTopHom φj = (bcTop g A).inv ≫ ul ≫ (bcTop g B).hom :=
      ModuleCat.hom_ext (LinearMap.ext hφj0)
    rw [h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · rw [reassoc_of% hD, hu]

/-- **A local descent datum from the canonical equation at the restricted morphisms.**  A morphism
`ψ` of the pullbacks along `Scheme.Hom.resLE g T Z₀ hZ` of the restrictions of `F` and `G` to `T`
which satisfies the canonical equation for the three restricted morphisms gives a morphism `Θ` of
the restrictions to `Z₀` of `g^*F` and `g^*G` with `LocalDescent q g pi hpi φ Z₀ Θ`. -/
theorem exists_localDescent_of_resLE_canonical_eq {P Z X : Scheme.{u}} (q : P ⟶ Z) (g : Z ⟶ X)
    (pi : P ⟶ X) (hpi : q ≫ g = pi) {F G : X.Modules}
    (φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G)
    {T : X.Opens} {Z₀ : Z.Opens} {W₀ : P.Opens} (hZ : Z₀ ≤ g ⁻¹ᵁ T) (hW : W₀ ≤ q ⁻¹ᵁ Z₀)
    (hW' : W₀ ≤ pi ⁻¹ᵁ T) (hW₂ : q ⁻¹ᵁ Z₀ ≤ W₀)
    (hres : Scheme.Hom.resLE q Z₀ W₀ hW ≫ Scheme.Hom.resLE g T Z₀ hZ
      = Scheme.Hom.resLE pi T W₀ hW')
    (ψ : (Scheme.Modules.pullback (Scheme.Hom.resLE g T Z₀ hZ)).obj
        (Scheme.Modules.restrict F T.ι) ⟶
      (Scheme.Modules.pullback (Scheme.Hom.resLE g T Z₀ hZ)).obj
        (Scheme.Modules.restrict G T.ι))
    (hψ : (Scheme.Modules.pullback (Scheme.Hom.resLE q Z₀ W₀ hW)).map ψ ≫
          canHom (Scheme.Hom.resLE q Z₀ W₀ hW) (Scheme.Hom.resLE g T Z₀ hZ)
            (Scheme.Hom.resLE pi T W₀ hW') hres (Scheme.Modules.restrict G T.ι)
        = canHom (Scheme.Hom.resLE q Z₀ W₀ hW) (Scheme.Hom.resLE g T Z₀ hZ)
              (Scheme.Hom.resLE pi T W₀ hW') hres (Scheme.Modules.restrict F T.ι) ≫
            ((Stacks.Modules.restrictPullbackObjIso pi hW' F).inv ≫
              (Scheme.Modules.restrictFunctor W₀.ι).map φ ≫
                (Stacks.Modules.restrictPullbackObjIso pi hW' G).hom)) :
    ∃ Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj F) Z₀.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback g).obj G) Z₀.ι,
      LocalDescent q g pi hpi φ Z₀ Θ :=
  ⟨_, localDescent_of_resLE_canonical_eq q g pi hpi φ hZ hW hW' hW₂ hres ψ hψ⟩

/-! ### The affine case over an affine open of a stage -/

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- The preimage of `V` under a composite is the preimage of its preimage. -/
private theorem preimage_preimage_eq_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (V : Z.Opens) : f ⁻¹ᵁ g ⁻¹ᵁ V = h ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, e]

/-- **The affine case of [Stacks Project, Tag 01ZR] (2) over an affine open of the stage, at the
restricted morphisms.**  A morphism between the pullbacks to the limit of two sheaves of modules
of finite presentation on the preimage of an affine open `V` of the stage `i` is, at a later
stage `k`, the base change of a morphism there, through the canonical identification of
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` for the three morphisms restricted to the
preimages of `V`. -/
theorem exists_canonical_eq_resLE_of_isAffineOpen (hc : IsLimit c) (i : I)
    {V : (D.obj i).Opens} (hV : IsAffineOpen V)
    (A B : V.toScheme.Modules) [A.IsFinitePresentation] [B.IsFinitePresentation]
    [A.IsQuasicoherent] [B.IsQuasicoherent]
    (hW' : (c.π.app i ⁻¹ᵁ V : c.pt.Opens) ≤ (c.π.app i ⁻¹ᵁ V : c.pt.Opens))
    (ξ : (Scheme.Modules.pullback
          (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW')).obj A ⟶
        (Scheme.Modules.pullback
          (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW')).obj B) :
    ∃ (k : Over i)
      (hZ : (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens)
          ≤ (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens))
      (hq : (c.π.app i ⁻¹ᵁ V : c.pt.Opens)
          ≤ (c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) : c.pt.Opens))
      (hres : Scheme.Hom.resLE (X := c.pt) (c.π.app k.left)
            (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hq ≫
          Scheme.Hom.resLE (D.map k.hom) V (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ
          = Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW')
      (ψ : (Scheme.Modules.pullback (Scheme.Hom.resLE (D.map k.hom) V
            (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ)).obj A ⟶
          (Scheme.Modules.pullback (Scheme.Hom.resLE (D.map k.hom) V
            (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ)).obj B),
      (Scheme.Modules.pullback (Scheme.Hom.resLE (X := c.pt) (c.π.app k.left)
              (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens)
              (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hq)).map ψ ≫
          canHom (Scheme.Hom.resLE (X := c.pt) (c.π.app k.left)
              (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens)
              (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hq)
            (Scheme.Hom.resLE (D.map k.hom) V
              (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ)
            (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW') hres B
        = canHom (Scheme.Hom.resLE (X := c.pt) (c.π.app k.left)
              (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens)
              (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hq)
            (Scheme.Hom.resLE (D.map k.hom) V
              (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ)
            (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V
              (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW') hres A ≫ ξ := by
  classical
  have haff : ∀ k : Over i,
      IsAffine (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens).toScheme :=
    fun k ↦ hV.preimage (D.map k.hom)
  have hXaff : IsAffine V.toScheme := hV
  have hPaff : IsAffine (c.π.app i ⁻¹ᵁ V : c.pt.Opens).toScheme :=
    EventualLimit.isAffineOpen_preimage_π_app D c hc i hV
  set E : (Over i)ᵒᵖ ⥤ CommRingCat.{u} :=
    (EventualLimit.preimageDiagram D i V).op ⋙ Scheme.Γ
  set d : Cocone E := Scheme.Γ.mapCocone (EventualLimit.preimageCone D c i V).op
  have hd : IsColimit d := by
    have : ∀ k : (Over i)ᵒᵖ,
        IsAffine ((EventualLimit.preimageDiagram D i V).op.obj k).unop :=
      fun k ↦ haff k.unop
    exact isColimitOfPreserves Scheme.Γ (EventualLimit.isLimitPreimageCone D c hc i V).op
  let σ : ∀ k : Over i,
      (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens).toScheme ⟶ V.toScheme :=
    fun k ↦ Scheme.Hom.resLE (D.map k.hom) V
      (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) le_rfl
  let _ : ∀ l : (Over i)ᵒᵖ, Algebra Γ(V.toScheme, ⊤) (E.obj l) :=
    fun l ↦ ((σ l.unop).appTop).hom.toAlgebra
  let _ : Algebra Γ(V.toScheme, ⊤) d.pt :=
    ((Scheme.Hom.resLE (X := c.pt) (c.π.app i) V
      (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW').appTop).hom.toAlgebra
  have halg : ∀ (k : (Over i)ᵒᵖ) (y : Γ(V.toScheme, ⊤)),
      algebraMap Γ(V.toScheme, ⊤) (E.obj k) y = (σ k.unop).appTop y := fun _ _ ↦ rfl
  have halgR : ∀ y : Γ(V.toScheme, ⊤),
      algebraMap Γ(V.toScheme, ⊤) d.pt y
        = (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V
            (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW').appTop y := fun _ ↦ rfl
  have ha : ∀ {l m : (Over i)ᵒᵖ} (ee : l ⟶ m) (x : Γ(V.toScheme, ⊤)),
      E.map ee (algebraMap Γ(V.toScheme, ⊤) (E.obj l) x)
        = algebraMap Γ(V.toScheme, ⊤) (E.obj m) x := by
    intro l m ee x
    have hp : (D.map m.unop.hom ⁻¹ᵁ V : (D.obj m.unop.left).Opens)
        ≤ (D.map ee.unop.left ⁻¹ᵁ (D.map l.unop.hom ⁻¹ᵁ V : (D.obj l.unop.left).Opens) :
          (D.obj m.unop.left).Opens) :=
      (preimage_preimage_eq_of_comp_eq _ _ _ (by rw [← D.map_comp, Over.w ee.unop]) V).ge
    rw [halg, halg]
    show (Scheme.Hom.resLE (D.map ee.unop.left)
        (D.map l.unop.hom ⁻¹ᵁ V : (D.obj l.unop.left).Opens)
        (D.map m.unop.hom ⁻¹ᵁ V : (D.obj m.unop.left).Opens) hp).appTop
          ((σ l.unop).appTop x) = (σ m.unop).appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      resLE_comp_resLE_of_comp_eq (D.map ee.unop.left) (D.map l.unop.hom) (D.map m.unop.hom)
        (by rw [← D.map_comp, Over.w ee.unop]) le_rfl hp le_rfl]
  have hq : ∀ k : Over i, (c.π.app i ⁻¹ᵁ V : c.pt.Opens)
      ≤ (c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) : c.pt.Opens) :=
    fun k ↦ (preimage_preimage_eq_of_comp_eq _ _ _ (c.w k.hom) V).ge
  have haR : ∀ (l : (Over i)ᵒᵖ) (x : Γ(V.toScheme, ⊤)),
      d.ι.app l (algebraMap Γ(V.toScheme, ⊤) (E.obj l) x)
        = algebraMap Γ(V.toScheme, ⊤) d.pt x := by
    intro l x
    rw [halg, halgR]
    show (Scheme.Hom.resLE (X := c.pt) (c.π.app l.unop.left)
        (D.map l.unop.hom ⁻¹ᵁ V : (D.obj l.unop.left).Opens)
        (c.π.app i ⁻¹ᵁ V : c.pt.Opens) (hq l.unop)).appTop ((σ l.unop).appTop x)
      = (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW').appTop x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      resLE_comp_resLE_of_comp_eq (c.π.app l.unop.left) (D.map l.unop.hom) (c.π.app i)
        (c.w l.unop.hom) le_rfl (hq l.unop) hW']
  have hMfp : Module.FinitePresentation Γ(V.toScheme, ⊤) ↑Γ(A, ⊤) :=
    finitePresentation_sectionsTop A
  let u : (ModuleCat.extendScalars (Scheme.Hom.appTop
        (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW')).hom).obj
        (ModuleCat.of Γ(V.toScheme, ⊤) ↑Γ(A, ⊤)) ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop
        (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW')).hom).obj
        (ModuleCat.of Γ(V.toScheme, ⊤) ↑Γ(B, ⊤)) :=
    (bcTop (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW') A).hom ≫
      appTopHom ξ ≫
        (bcTop (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V
          (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW') B).inv
  obtain ⟨l, ul, hul⟩ := Stacks.RingFilteredColimits.exists_descend_rTensor haR ha hd
    ↑Γ(A, ⊤) ↑Γ(B, ⊤) u.hom
  let k := l.unop
  have hZ : (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens)
      ≤ (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) := le_rfl
  have hres : Scheme.Hom.resLE (X := c.pt) (c.π.app k.left)
        (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) (c.π.app i ⁻¹ᵁ V : c.pt.Opens) (hq k) ≫
      Scheme.Hom.resLE (D.map k.hom) V (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ
      = Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW' :=
    resLE_comp_resLE_of_comp_eq (c.π.app k.left) (D.map k.hom) (c.π.app i)
      (c.w k.hom) hZ (hq k) hW'
  let ulM0 := ModuleCat.ofHom ul
  let ulM : (ModuleCat.extendScalars (Scheme.Hom.appTop
        (Scheme.Hom.resLE (D.map k.hom) V
          (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ)).hom).obj
        (ModuleCat.of Γ(V.toScheme, ⊤) ↑Γ(A, ⊤)) ⟶
      (ModuleCat.extendScalars (Scheme.Hom.appTop
        (Scheme.Hom.resLE (D.map k.hom) V
          (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ)).hom).obj
        (ModuleCat.of Γ(V.toScheme, ⊤) ↑Γ(B, ⊤)) := ulM0
  have hUX : u ≫ (bcTop (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V
        (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW') B).hom
      = (bcTop (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V
          (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW') A).hom ≫ appTopHom ξ := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨k, hZ, hq k, hres, exists_map_canonical_of_descend
    (Scheme.Hom.resLE (X := c.pt) (c.π.app k.left) (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens)
      (c.π.app i ⁻¹ᵁ V : c.pt.Opens) (hq k))
    (Scheme.Hom.resLE (D.map k.hom) V (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) hZ)
    (Scheme.Hom.resLE (X := c.pt) (c.π.app i) V (c.π.app i ⁻¹ᵁ V : c.pt.Opens) hW') hres A B ξ
    (Stacks.RingFilteredColimits.legAlgHom haR l) (fun _ ↦ rfl) u hUX ulM hul⟩

/-- **A local descent datum over an affine open of the stage.**  For an affine open `V` of the
stage `i` and two sheaves of modules of finite presentation there, a morphism between the
pullbacks of the two to the limit is, over the preimage of `V` at some later stage `k`, the
localized canonical equation of [Stacks Project, Tag 01ZR] (2) for a morphism of the restrictions
of the pullbacks to `k`. -/
theorem exists_localDescent_of_isAffineOpen (hc : IsLimit c) (i : I)
    {V : (D.obj i).Opens} (hV : IsAffineOpen V)
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (k : Over i)
      (Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
            (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens).ι ⟶
          Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
            (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens).ι),
      LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
        (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) Θ := by
  have hAfp := isFinitePresentation_restrict V.ι F
  have hBfp := isFinitePresentation_restrict V.ι G
  have hAqc := _root_.isQuasicoherent_of_isFinitePresentation (Scheme.Modules.restrict F V.ι)
  have hBqc := _root_.isQuasicoherent_of_isFinitePresentation (Scheme.Modules.restrict G V.ι)
  have hW' : (c.π.app i ⁻¹ᵁ V : c.pt.Opens) ≤ (c.π.app i ⁻¹ᵁ V : c.pt.Opens) := le_rfl
  obtain ⟨k, hZ, hq, hres, ψ, hψ⟩ := exists_canonical_eq_resLE_of_isAffineOpen D c hc i hV
    (Scheme.Modules.restrict F V.ι) (Scheme.Modules.restrict G V.ι) hW'
    ((Stacks.Modules.restrictPullbackObjIso (X := c.pt) (c.π.app i) hW' F).inv ≫
      (Scheme.Modules.restrictFunctor (c.π.app i ⁻¹ᵁ V : c.pt.Opens).ι).map φ ≫
        (Stacks.Modules.restrictPullbackObjIso (X := c.pt) (c.π.app i) hW' G).hom)
  have hq₂ : (c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens) : c.pt.Opens)
      ≤ (c.π.app i ⁻¹ᵁ V : c.pt.Opens) :=
    (preimage_preimage_eq_of_comp_eq _ _ _ (c.w k.hom) V).le
  exact ⟨k, exists_localDescent_of_resLE_canonical_eq (P := c.pt)
    (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ (T := V)
    (Z₀ := (D.map k.hom ⁻¹ᵁ V : (D.obj k.left).Opens))
    (W₀ := (c.π.app i ⁻¹ᵁ V : c.pt.Opens)) hZ hq hW' hq₂ hres ψ hψ⟩

end Stacks.AlgebraicGeometry.ModuleLimits

end
