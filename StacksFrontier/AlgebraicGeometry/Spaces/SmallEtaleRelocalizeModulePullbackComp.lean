module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparisonComp
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackTensorComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkInverseImage

/-!
# Relocalization of inverse images of modules is compatible with composition

Let `h : W ⟶ S` be a morphism of a big fppf site and `Λ` the lower-shriek extension of algebraic
spaces over `W` to algebraic spaces over `S`.  For a representable morphism `φ` of algebraic
spaces over `W`, `AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE` identifies
`φ^* ⋙ E ≅ E ⋙ (Λ φ)^*`, where `E` is the equivalence `Mod(𝒪_Y) ≌ Mod(𝒪_{Λ Y})` of
`AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE`.  This file proves that these
identifications are compatible with composition: they make `Λ` a morphism of the pseudofunctors
of inverse images of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.relocalizeBaseChangeIso_comp_hom_app`: the comparisons of base changes
  of étale charts across relocalization compose.
* `AlgebraicGeometry.Space.relocalizePushforwardIso_inv_comp`: the comparisons of direct images
  across relocalization compose.
* `AlgebraicGeometry.Space.relocalizeModulePullbackIso_comp`: **the comparisons of inverse images
  across relocalization compose.**

## Implementation notes

The inverse images have no formula, so the composition law is transposed to the right adjoints
with `CategoryTheory.conjugateEquiv`, as in
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp`.  There every comparison is a
direct image of sheaves of modules round a square of continuous functors
(`Stacks.SheafOfModules.pushforwardSquareIsoOfIso`), and the pentagon is the generic
`Stacks.SheafOfModules.pushforwardSquareIso_inv_comp`, applied at the compatibility of the
comparisons of charts, which is checked on the cartesian projections
(`AlgebraicGeometry.Space.iteratedBaseChange_hom_ext`).

The composite `Λ (φ ≫ ψ)` is definitionally `Λ φ ≫ Λ ψ`
(`AlgebraicGeometry.Space.relocalizeHomSE_comp`), but the elaborator should not be asked to see
it inside large terms: the comparisons over `S` are restated with the composite spelled
`Λ (φ ≫ ψ)` (`AlgebraicGeometry.Space.relocalizeChartCompIso`,
`AlgebraicGeometry.Space.relocalizeChartPushforwardCompIso`).

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange


namespace Stacks.SheafOfModules

section SquareComp

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}
  {K₁ : GrothendieckTopology D₁} {K₂ : GrothendieckTopology D₂} {K₃ : GrothendieckTopology D₃}
  {a : C₃ ⥤ C₂} {b : C₂ ⥤ C₁} {c : C₃ ⥤ C₁} {A : D₃ ⥤ D₂} {Bf : D₂ ⥤ D₁} {Cf : D₃ ⥤ D₁}
  {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}
  [a.IsContinuous J₃ J₂] [b.IsContinuous J₂ J₁] [c.IsContinuous J₃ J₁]
  [A.IsContinuous K₃ K₂] [Bf.IsContinuous K₂ K₁] [Cf.IsContinuous K₃ K₁]
  [E₁.IsContinuous J₁ K₁] [E₂.IsContinuous J₂ K₂] [E₃.IsContinuous J₃ K₃]
  [(a ⋙ b).IsContinuous J₃ J₁] [(A ⋙ Bf).IsContinuous K₃ K₁]
  [(E₂ ⋙ Bf).IsContinuous J₂ K₁] [(b ⋙ E₁).IsContinuous J₂ K₁]
  [(E₃ ⋙ A).IsContinuous J₃ K₂] [(a ⋙ E₂).IsContinuous J₃ K₂]
  [(E₃ ⋙ Cf).IsContinuous J₃ K₁] [(c ⋙ E₁).IsContinuous J₃ K₁]
  {O₁ : Sheaf J₁ RingCat.{u}} {O₂ : Sheaf J₂ RingCat.{u}} {O₃ : Sheaf J₃ RingCat.{u}}
  {P₁ : Sheaf K₁ RingCat.{u}} {P₂ : Sheaf K₂ RingCat.{u}} {P₃ : Sheaf K₃ RingCat.{u}}
  {fa : O₃ ⟶ (a.sheafPushforwardContinuous RingCat.{u} J₃ J₂).obj O₂}
  {fb : O₂ ⟶ (b.sheafPushforwardContinuous RingCat.{u} J₂ J₁).obj O₁}
  {fc : O₃ ⟶ (c.sheafPushforwardContinuous RingCat.{u} J₃ J₁).obj O₁}
  {gA : P₃ ⟶ (A.sheafPushforwardContinuous RingCat.{u} K₃ K₂).obj P₂}
  {gB : P₂ ⟶ (Bf.sheafPushforwardContinuous RingCat.{u} K₂ K₁).obj P₁}
  {gC : P₃ ⟶ (Cf.sheafPushforwardContinuous RingCat.{u} K₃ K₁).obj P₁}
  {ι₁ : O₁ ⟶ (E₁.sheafPushforwardContinuous RingCat.{u} J₁ K₁).obj P₁}
  {ι₂ : O₂ ⟶ (E₂.sheafPushforwardContinuous RingCat.{u} J₂ K₂).obj P₂}
  {ι₃ : O₃ ⟶ (E₃.sheafPushforwardContinuous RingCat.{u} J₃ K₃).obj P₃}

/-- **The direct images round squares of continuous functors compose.**  Given three squares
`E₂ ⋙ Bf ≅ b ⋙ E₁`, `E₃ ⋙ A ≅ a ⋙ E₂`, `E₃ ⋙ Cf ≅ c ⋙ E₁` and comparisons `c ≅ a ⋙ b`,
`Cf ≅ A ⋙ Bf` of continuous functors, compatible on objects, the isomorphisms of composite
direct images of `Stacks.SheafOfModules.pushforwardSquareIsoOfIso` satisfy the pentagon against the
composition comparisons of direct images.  On sections both sides are restriction along the
two sides of the compatibility of the squares. -/
theorem pushforwardSquareIso_inv_comp
    (rb : E₂ ⋙ Bf ≅ b ⋙ E₁) (ra : E₃ ⋙ A ≅ a ⋙ E₂) (rc : E₃ ⋙ Cf ≅ c ⋙ E₁)
    (κ : c ≅ a ⋙ b) (κ' : Cf ≅ A ⋙ Bf)
    (hb : (ι₂ ≫ (E₂.sheafPushforwardContinuous RingCat.{u} J₂ K₂).map gB) ≫
        (Functor.sheafPushforwardContinuousNatTrans rb.symm.hom RingCat.{u} J₂ K₁).app P₁ =
      fb ≫ (b.sheafPushforwardContinuous RingCat.{u} J₂ J₁).map ι₁)
    (ha : (ι₃ ≫ (E₃.sheafPushforwardContinuous RingCat.{u} J₃ K₃).map gA) ≫
        (Functor.sheafPushforwardContinuousNatTrans ra.symm.hom RingCat.{u} J₃ K₂).app P₂ =
      fa ≫ (a.sheafPushforwardContinuous RingCat.{u} J₃ J₂).map ι₂)
    (hc : (ι₃ ≫ (E₃.sheafPushforwardContinuous RingCat.{u} J₃ K₃).map gC) ≫
        (Functor.sheafPushforwardContinuousNatTrans rc.symm.hom RingCat.{u} J₃ K₁).app P₁ =
      fc ≫ (c.sheafPushforwardContinuous RingCat.{u} J₃ J₁).map ι₁)
    (hκ : (fa ≫ (a.sheafPushforwardContinuous RingCat.{u} J₃ J₂).map fb) ≫
        (Functor.sheafPushforwardContinuousNatTrans κ.hom RingCat.{u} J₃ J₁).app O₁ = fc)
    (hκ' : (gA ≫ (A.sheafPushforwardContinuous RingCat.{u} K₃ K₂).map gB) ≫
        (Functor.sheafPushforwardContinuousNatTrans κ'.hom RingCat.{u} K₃ K₁).app P₁ = gC)
    (hsite : ∀ V : C₃, κ'.hom.app (E₃.obj V) ≫ Bf.map (ra.hom.app V) ≫ rb.hom.app (a.obj V) =
      rc.hom.app V ≫ E₁.map (κ.hom.app V)) :
    Functor.whiskerRight (pushforwardSquareIsoOfIso fb gB ι₂ ι₁ rb hb).inv
          (SheafOfModules.pushforward.{u} fa) ≫
        Functor.whiskerLeft (SheafOfModules.pushforward.{u} gB)
          (pushforwardSquareIsoOfIso fa gA ι₃ ι₂ ra ha).inv ≫
        Functor.whiskerRight (SheafOfModules.pushforwardComp gA gB ≪≫
            SheafOfModules.pushforwardCongr₂ _ κ' hκ').hom
          (SheafOfModules.pushforward.{u} ι₃) =
      Functor.whiskerLeft (SheafOfModules.pushforward.{u} ι₁)
          (SheafOfModules.pushforwardComp fa fb ≪≫ SheafOfModules.pushforwardCongr₂ _ κ hκ).hom ≫
        (pushforwardSquareIsoOfIso fc gC ι₃ ι₁ rc hc).inv := by
  refine NatTrans.ext (funext fun M => SheafOfModules.hom_ext (PresheafOfModules.hom_ext
    fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)))
  have key : M.val.presheaf.map (rb.hom.app (a.obj V.unop)).op ≫
      M.val.presheaf.map (Bf.map (ra.hom.app V.unop)).op ≫
        M.val.presheaf.map (κ'.hom.app (E₃.obj V.unop)).op =
      M.val.presheaf.map (E₁.map (κ.hom.app V.unop)).op ≫
        M.val.presheaf.map (rc.hom.app V.unop).op := by
    simp only [← Functor.map_comp, ← op_comp, Category.assoc, hsite]
  exact congr($key x)

end SquareComp

end Stacks.SheafOfModules


namespace AlgebraicGeometry.Space

/-- Bookkeeping for a composite of five morphisms, two of which are rewritten as composites and
one square of which commutes. -/
private theorem comp_square_aux {C : Type*} [Category C] {P Q A₁ A₂ B₁ B₂ C₀ : C}
    (x : P ⟶ Q) (i : Q ⟶ A₁) (m : A₁ ⟶ A₂) (s₁ : A₂ ⟶ B₂) (s₂ : B₂ ⟶ C₀) (s₁' : A₁ ⟶ B₁)
    (d : B₁ ⟶ B₂) (o₁ : Q ⟶ B₁) (o₂ : B₁ ⟶ C₀) (h₁ : o₁ = i ≫ s₁') (h₂ : o₂ = d ≫ s₂)
    (h₃ : m ≫ s₁ = s₁' ≫ d) :
    x ≫ o₁ ≫ o₂ = (x ≫ i ≫ m) ≫ s₁ ≫ s₂ := by
  subst h₁ h₂
  simp only [Category.assoc, reassoc_of% h₃]

/-- Bookkeeping for cancelling two inverse pairs in a composite. -/
private theorem cancel_aux {C : Type*} [Category C] {P Q A₁ A₂ : C}
    (x : P ⟶ Q) (e : Q ⟶ A₁) (f : A₁ ⟶ A₂) (b : A₂ ⟶ A₁) (c : A₁ ⟶ Q)
    (hfb : f ≫ b = 𝟙 _) (hec : e ≫ c = 𝟙 _) :
    (x ≫ e ≫ f) ≫ b ≫ c = x := by
  simp only [Category.assoc, reassoc_of% hfb, hec, Category.comp_id]

/-- Cancelling a composite isomorphism against its two factors. -/
private theorem iso_trans_inv_cancel {C : Type*} [Category C] {P Q R T : C} (a : P ≅ Q) (b : Q ≅ R)
    (c : R ≅ T) : (a ≪≫ b).inv ≫ (a ≪≫ b ≪≫ c).hom = c.hom := by
  simp

/-- `CategoryTheory.conjugateEquiv_whiskerLeft`, for a conjugate of `τ` known to equal `σ`. -/
private theorem conjugateEquiv_whiskerLeft_eq {A' B' C' : Type*} [Category A'] [Category B']
    [Category C'] {L₁ L₂ : B' ⥤ C'} {R₁ R₂ : C' ⥤ B'} {L : A' ⥤ B'} {R : B' ⥤ A'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : L₂ ⟶ L₁) (σ : R₁ ⟶ R₂)
    (h : conjugateEquiv adj₁ adj₂ τ = σ) :
    conjugateEquiv (adj.comp adj₁) (adj.comp adj₂) (Functor.whiskerLeft L τ) =
      Functor.whiskerRight σ R :=
  (conjugateEquiv_whiskerLeft _ _ _ _).trans (congrArg (Functor.whiskerRight · R) h)

/-- `CategoryTheory.conjugateEquiv_whiskerRight`, for a conjugate of `τ` known to equal `σ`. -/
private theorem conjugateEquiv_whiskerRight_eq {A' B' C' : Type*} [Category A'] [Category B']
    [Category C'] {L₁ L₂ : A' ⥤ B'} {R₁ R₂ : B' ⥤ A'} {L : B' ⥤ C'} {R : C' ⥤ B'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : L₂ ⟶ L₁) (σ : R₁ ⟶ R₂)
    (h : conjugateEquiv adj₁ adj₂ τ = σ) :
    conjugateEquiv (adj₁.comp adj) (adj₂.comp adj) (Functor.whiskerRight τ L) =
      Functor.whiskerLeft R σ :=
  (conjugateEquiv_whiskerRight _ _ _ _).trans (congrArg (Functor.whiskerLeft R) h)

/-- Solving `a ≫ b ≫ c = x ≫ l` for `l`. -/
private theorem eq_inv_comp_of_comp_eq {C : Type*} [Category C] {P Q R T U : C} (x : P ≅ Q)
    (a : P ⟶ R) (b : R ⟶ T) (c : T ⟶ U) (l : Q ⟶ U) (hc : a ≫ b ≫ c = x.hom ≫ l) :
    l = x.inv ≫ a ≫ b ≫ c := by
  rw [hc, Iso.inv_hom_id_assoc]

section Iterated

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C D : AlgebraicSpaces B S hS} (f : D ⟶ A) (g : A ⟶ C)
  (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)

/-- **A morphism into an iterated base change of a chart is determined by its projection to the
chart.**  The iterated base change `(V ×_C A) ×_A D` of an étale chart `V` of `C` is a fibre
product of `D` and `V` over `C`; a morphism of charts of `D` into it already lies over `D`, so
it is determined by its composite with the two cartesian projections down to `V`. -/
theorem iteratedBaseChange_hom_ext {T : SmallEtale B S hS D.1} {V : SmallEtale B S hS C.1}
    {a b : T ⟶ (smallBaseChange B S hS f hf).obj ((smallBaseChange B S hS g hg).obj V)}
    (hab : a.hom.left ≫ hf.snd ((smallBaseChange B S hS g hg).obj V).1.hom ≫ hg.snd V.1.hom =
      b.hom.left ≫ hf.snd ((smallBaseChange B S hS g hg).obj V).1.hom ≫ hg.snd V.1.hom) :
    a = b := by
  have wa := CostructuredArrow.w a.hom
  have wb := CostructuredArrow.w b.hom
  have hfst : yoneda.map a.hom.left ≫ hf.fst ((smallBaseChange B S hS g hg).obj V).1.hom =
      yoneda.map b.hom.left ≫ hf.fst ((smallBaseChange B S hS g hg).obj V).1.hom :=
    wa.trans wb.symm
  have hcart : yoneda.map (hf.snd ((smallBaseChange B S hS g hg).obj V).1.hom) ≫
        hg.fst V.1.hom =
      hf.fst ((smallBaseChange B S hS g hg).obj V).1.hom ≫ f.hom :=
    (hf.w ((smallBaseChange B S hS g hg).obj V).1.hom).symm
  have key : ∀ c : T ⟶ (smallBaseChange B S hS f hf).obj ((smallBaseChange B S hS g hg).obj V),
      yoneda.map (c.hom.left ≫ hf.snd ((smallBaseChange B S hS g hg).obj V).1.hom) ≫
          hg.fst V.1.hom =
        (yoneda.map c.hom.left ≫ hf.fst ((smallBaseChange B S hS g hg).obj V).1.hom) ≫ f.hom :=
    fun c => (yoneda.map_comp_assoc _ _ _).trans
      ((congrArg (yoneda.map c.hom.left ≫ ·) hcart).trans (Category.assoc _ _ _).symm)
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hf.hom_ext hfst ?_))
  refine hg.hom_ext ((key a).trans ((congrArg (· ≫ f.hom) hfst).trans (key b).symm)) ?_
  exact (Category.assoc _ _ _).trans (hab.trans (Category.assoc _ _ _).symm)

end Iterated

section ChartConjugate

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C D : AlgebraicSpaces B S hS} (f : D ⟶ A) (g : A ⟶ C)
  (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
  (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)

/-- **The composition law of inverse images, transposed to base-change direct images.**  The
conjugate of the comparison `(f ≫ g)^* ≅ f^* g^*` of Stacks 03LU, with respect to the adjunctions
whose right adjoints are the base-change direct images along `f`, `g` and `f ≫ g`, is the
contraction `AlgebraicGeometry.Space.smallBaseChangeChartPushforwardCompIso`. -/
theorem conjugateEquiv_modulePullbackCompIso_inv_chart :
    conjugateEquiv
        (((modulePullbackAdjunction B S hS g).ofNatIsoRight
            (modulePushforwardChartIso B S hS g hg)).comp
          ((modulePullbackAdjunction B S hS f).ofNatIsoRight
            (modulePushforwardChartIso B S hS f hf)))
        ((modulePullbackAdjunction B S hS (f ≫ g)).ofNatIsoRight
          (modulePushforwardChartIso B S hS (f ≫ g) hfg))
        (modulePullbackCompIso B S hS f g).inv =
      (smallBaseChangeChartPushforwardCompIso B S hS f g hf hg hfg).hom := by
  have hc := Adjunction.comp_ofNatIsoRight (modulePullbackAdjunction B S hS g)
    (modulePullbackAdjunction B S hS f) (modulePushforwardChartIso B S hS g hg)
    (modulePushforwardChartIso B S hS f hf)
  rw [hc]
  have hd := Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight
    ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f))
    (modulePullbackAdjunction B S hS (f ≫ g))
    (Functor.isoWhiskerRight (modulePushforwardChartIso B S hS f hf) (modulePushforward B S hS g) ≪≫
      Functor.isoWhiskerLeft (smallBaseChangeModulePushforward B S hS f hf)
        (modulePushforwardChartIso B S hS g hg))
    (modulePushforwardChartIso B S hS (f ≫ g) hfg) (modulePullbackCompIso B S hS f g).inv
  refine hd.trans ?_
  rw [conjugateEquiv_modulePullbackCompIso_inv]
  exact (congrArg (_ ≫ ·) (congrArg Iso.hom
    (modulePushforwardChartIso_comp B S hS f g hf hg hfg)).symm).trans (iso_trans_inv_cancel _ _ _)

end ChartConjugate

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

variable {X Y Z : AlgebraicSpaces B W hW} (φ : X ⟶ Y) (ψ : Y ⟶ Z)

/-- The lower-shriek extension of a composite is the composite of the extensions, by definition. -/
theorem relocalizeHomSE_comp :
    relocalizeHomSE B W S hW hS h (φ ≫ ψ) =
      relocalizeHomSE B W S hW hS h φ ≫ relocalizeHomSE B W S hW hS h ψ := rfl

variable (hφ : yoneda.relativelyRepresentable φ.hom) (hψ : yoneda.relativelyRepresentable ψ.hom)
  (hφψ : yoneda.relativelyRepresentable (φ ≫ ψ).hom)

/-- The comparison of charts of `relocalizeBaseChangeIsoSE` followed by the cartesian projection
of `Λ φ` is the image of the cartesian projection of `φ`. -/
theorem relocalizeBaseChangeIso_inv_app_snd (V : SmallEtale B W hW Y.1) :
    ((relocalizeBaseChangeIsoSE B W S hW hS h φ hφ).inv.app V).hom.left ≫
        (relocalizeRepSE B W S hW hS h φ hφ).snd
          ((SmallEtale.relocalizeEquivalence B W S hW hS h Y.1).functor.obj V).obj.hom =
      (Over.map h).map (hφ.snd V.obj.hom) :=
  relocalizeBaseChangeOverIso_inv_sndSE B W S hW hS h φ hφ V

/-- The composition comparison of base changes of charts of `Λ X ⟶ Λ Y ⟶ Λ Z`, with the
composite spelled `Λ (φ ≫ ψ)`. -/
def relocalizeChartCompIso :
    smallBaseChange B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
        (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ) ≅
      smallBaseChange B S hS (relocalizeHomSE B W S hW hS h ψ)
          (relocalizeRepSE B W S hW hS h ψ hψ) ⋙
        smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeRepSE B W S hW hS h φ hφ) :=
  smallBaseChangeChartCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
    (relocalizeRepSE B W S hW hS h ψ hψ) (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)

/-- The structure maps of the sheaves of rings are compatible with
`AlgebraicGeometry.Space.relocalizeChartCompIso`. -/
theorem relocalizeChartCompIso_comparisonComp :
    haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
      (relocalizeRepSE B W S hW hS h φ hφ)
    haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h ψ)
      (relocalizeRepSE B W S hW hS h ψ hψ)
    haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
      (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)
    haveI := isContinuous_smallBaseChange_comp B S hS (relocalizeHomSE B W S hW hS h φ)
      (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
      (relocalizeRepSE B W S hW hS h ψ hψ)
    SheafOfModules.comparisonComp
        (smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h ψ)
          (relocalizeRepSE B W S hW hS h ψ hψ))
        (smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeRepSE B W S hW hS h φ hφ)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (relocalizeChartCompIso B W S hW hS h φ ψ hφ hψ hφψ).hom RingCat.{u}
        (SmallEtale.topology B S hS (relocalizeSpaceSE B W S hW hS h Z).1)
        (SmallEtale.topology B S hS (relocalizeSpaceSE B W S hW hS h X).1)).app
        (smallEtaleRingSheaf B S hS (relocalizeSpaceSE B W S hW hS h X).1
          (relocalizeSpaceSE B W S hW hS h X).2) =
      smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
        (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ) :=
  have := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeRepSE B W S hW hS h φ hφ)
  have := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h ψ)
    (relocalizeRepSE B W S hW hS h ψ hψ)
  smallBaseChangeSharp_comparisonComp B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
    (relocalizeRepSE B W S hW hS h ψ hψ) (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)

/-- The composition comparison of base-change direct images along `Λ φ` and `Λ ψ`, with the
composite spelled `Λ (φ ≫ ψ)`; it is
`AlgebraicGeometry.Space.smallBaseChangeChartPushforwardCompIso`
(`AlgebraicGeometry.Space.relocalizeChartPushforwardCompIso_eq`). -/
def relocalizeChartPushforwardCompIso :
    smallBaseChangeModulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ) ⋙
      smallBaseChangeModulePushforward B S hS (relocalizeHomSE B W S hW hS h ψ)
        (relocalizeRepSE B W S hW hS h ψ hψ) ≅
      smallBaseChangeModulePushforward B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
        (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ) :=
  haveI := isContinuous_smallBaseChange_comp B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
    (relocalizeRepSE B W S hW hS h ψ hψ)
  haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
    (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)
  haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeRepSE B W S hW hS h φ hφ)
  haveI := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h ψ)
    (relocalizeRepSE B W S hW hS h ψ hψ)
  SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr₂ _
    (relocalizeChartCompIso B W S hW hS h φ ψ hφ hψ hφψ)
    (relocalizeChartCompIso_comparisonComp B W S hW hS h φ ψ hφ hψ hφψ)

/-- The two spellings of the contraction of base-change direct images along `Λ φ` and `Λ ψ`
agree. -/
theorem relocalizeChartPushforwardCompIso_eq :
    relocalizeChartPushforwardCompIso B W S hW hS h φ ψ hφ hψ hφψ =
      smallBaseChangeChartPushforwardCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
        (relocalizeRepSE B W S hW hS h ψ hψ) (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ) :=
  rfl

/-- **The comparison of base changes of charts across relocalization is compatible with
composition**, on charts. -/
theorem relocalizeBaseChangeIso_comp_app (V : SmallEtale B W hW Z.1) :
    (relocalizeBaseChangeIsoSE B W S hW hS h (φ ≫ ψ) hφψ).inv.app V ≫
        (relocalizeChartCompIso B W S hW hS h φ ψ hφ hψ hφψ).hom.app
          ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V) =
      (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.map
          ((smallBaseChangeChartCompIso B W hW φ ψ hφ hψ hφψ).hom.app V) ≫
        (relocalizeBaseChangeIsoSE B W S hW hS h φ hφ).inv.app
          ((smallBaseChange B W hW ψ hψ).obj V) ≫
        (smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeRepSE B W S hW hS h φ hφ)).map
          ((relocalizeBaseChangeIsoSE B W S hW hS h ψ hψ).inv.app V) := by
  refine iteratedBaseChange_hom_ext B S hS _ _ _ _ ?_
  have e1 : ((smallBaseChangeChartCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
        (relocalizeRepSE B W S hW hS h ψ hψ) (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)).hom.app
        ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V)).hom.left ≫
        (relocalizeRepSE B W S hW hS h φ hφ).snd _ ≫ (relocalizeRepSE B W S hW hS h ψ hψ).snd _ =
      (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ).snd _ :=
    toOver_map_chartBaseChangeCompComparison_comp_snd B S hS
      (relocalizeHomSE B W S hW hS h φ) (relocalizeHomSE B W S hW hS h ψ)
      (relocalizeRepSE B W S hW hS h φ hφ) (relocalizeRepSE B W S hW hS h ψ hψ)
      (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)
      ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V)
  have e2 := relocalizeBaseChangeIso_inv_app_snd B W S hW hS h (φ ≫ ψ) hφψ V
  have e3 := smallBaseChange_map_snd B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeRepSE B W S hW hS h φ hφ) ((relocalizeBaseChangeIsoSE B W S hW hS h ψ hψ).inv.app V)
  have e4 := relocalizeBaseChangeIso_inv_app_snd B W S hW hS h φ hφ
    ((smallBaseChange B W hW ψ hψ).obj V)
  have e5 := relocalizeBaseChangeIso_inv_app_snd B W S hW hS h ψ hψ V
  have e6 : ((smallBaseChangeChartCompIso B W hW φ ψ hφ hψ hφψ).hom.app V).hom.left ≫
      hφ.snd _ ≫ hψ.snd _ = hφψ.snd _ :=
    toOver_map_chartBaseChangeCompComparison_comp_snd B W hW φ ψ hφ hψ hφψ V
  have hE : ((SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.map
      ((smallBaseChangeChartCompIso B W hW φ ψ hφ hψ hφψ).hom.app V)).hom.left =
      (Over.map h).map ((smallBaseChangeChartCompIso B W hW φ ψ hφ hψ hφψ).hom.app V).hom.left :=
    rfl
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e1)).trans (e2.trans ?_)
  rw [← e6]
  refine ((Over.map h).map_comp _ _).trans
    ((congrArg (_ ≫ ·) ((Over.map h).map_comp _ _)).trans ?_)
  exact comp_square_aux _ _ _ _ _ _ _ _ _ e4.symm e5.symm e3

/-- `AlgebraicGeometry.Space.relocalizeBaseChangeIso_comp_app`, for the forward comparisons. -/
theorem relocalizeBaseChangeIso_comp_hom_app (V : SmallEtale B W hW Z.1) :
    (relocalizeChartCompIso B W S hW hS h φ ψ hφ hψ hφψ).hom.app
          ((SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).functor.obj V) ≫
        (smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeRepSE B W S hW hS h φ hφ)).map
          ((relocalizeBaseChangeIsoSE B W S hW hS h ψ hψ).hom.app V) ≫
        (relocalizeBaseChangeIsoSE B W S hW hS h φ hφ).hom.app
          ((smallBaseChange B W hW ψ hψ).obj V) =
      (relocalizeBaseChangeIsoSE B W S hW hS h (φ ≫ ψ) hφψ).hom.app V ≫
        (SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.map
          ((smallBaseChangeChartCompIso B W hW φ ψ hφ hψ hφψ).hom.app V) := by
  refine (cancel_epi ((relocalizeBaseChangeIsoSE B W S hW hS h (φ ≫ ψ) hφψ).inv.app V)).1 ?_
  have hF : (smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ)).map
        ((relocalizeBaseChangeIsoSE B W S hW hS h ψ hψ).inv.app V) ≫
      (smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ)).map
        ((relocalizeBaseChangeIsoSE B W S hW hS h ψ hψ).hom.app V) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (relocalizeBaseChangeIso_comp_app B W S hW hS h φ ψ hφ hψ hφψ V)).trans
    ((cancel_aux _ _ _ _ _ hF
      (Iso.inv_hom_id_app (relocalizeBaseChangeIsoSE B W S hW hS h φ hφ)
        ((smallBaseChange B W hW ψ hψ).obj V))).trans
      (Iso.inv_hom_id_app_assoc (relocalizeBaseChangeIsoSE B W S hW hS h (φ ≫ ψ) hφψ) V _).symm))

/-- **The comparisons of direct images across relocalization compose**: the pentagon for
`AlgebraicGeometry.Space.relocalizePushforwardIsoSE` against the composition comparisons of the
base-change direct images over `W`
(`AlgebraicGeometry.Space.smallBaseChangeChartPushforwardCompIso`) and over `S` (in the spelling
`AlgebraicGeometry.Space.relocalizeChartPushforwardCompIso`). It is
`Stacks.SheafOfModules.pushforwardSquareIso_inv_comp` at the compatibility of charts
`AlgebraicGeometry.Space.relocalizeBaseChangeIso_comp_hom_app`. -/
theorem relocalizePushforwardIso_inv_comp :
    Functor.whiskerRight (relocalizePushforwardIsoSE B W S hW hS h φ hφ).inv
          (smallBaseChangeModulePushforward B W hW ψ hψ) ≫
        Functor.whiskerLeft
            (smallBaseChangeModulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)
              (relocalizeRepSE B W S hW hS h φ hφ))
          (relocalizePushforwardIsoSE B W S hW hS h ψ hψ).inv ≫
        Functor.whiskerRight (relocalizeChartPushforwardCompIso B W S hW hS h φ ψ hφ hψ hφψ).hom
          (relocalizeModulesRestriction B W S hW hS h Z) =
      Functor.whiskerLeft (relocalizeModulesRestriction B W S hW hS h X)
          (smallBaseChangeChartPushforwardCompIso B W hW φ ψ hφ hψ hφψ).hom ≫
        (relocalizePushforwardIsoSE B W S hW hS h (φ ≫ ψ) hφψ).inv := by
  have := isContinuous_smallBaseChange_comp B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
    (relocalizeRepSE B W S hW hS h ψ hψ)
  have := isContinuous_smallBaseChange_comp B W hW φ ψ hφ hψ
  have := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeRepSE B W S hW hS h φ hφ)
  have := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h ψ)
    (relocalizeRepSE B W S hW hS h ψ hψ)
  have := isContinuous_smallBaseChange B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
    (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)
  have := isContinuous_smallBaseChange B W hW φ hφ
  have := isContinuous_smallBaseChange B W hW ψ hψ
  have := isContinuous_smallBaseChange B W hW (φ ≫ ψ) hφψ
  have := isContinuous_smallBaseChange_comp_relocalizeEquivalence_functor B W S hW hS h φ hφ
  have := isContinuous_smallBaseChange_comp_relocalizeEquivalence_functor B W S hW hS h ψ hψ
  have := isContinuous_smallBaseChange_comp_relocalizeEquivalence_functor B W S hW hS h (φ ≫ ψ) hφψ
  have := isContinuous_relocalizeEquivalence_functor_comp_smallBaseChange B W S hW hS h φ hφ
  have := isContinuous_relocalizeEquivalence_functor_comp_smallBaseChange B W S hW hS h ψ hψ
  have := isContinuous_relocalizeEquivalence_functor_comp_smallBaseChange B W S hW hS h (φ ≫ ψ) hφψ
  exact Stacks.SheafOfModules.pushforwardSquareIso_inv_comp
    (fa := smallBaseChangeSharp B W hW ψ hψ) (fb := smallBaseChangeSharp B W hW φ hφ)
    (fc := smallBaseChangeSharp B W hW (φ ≫ ψ) hφψ)
    (gA := smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h ψ)
      (relocalizeRepSE B W S hW hS h ψ hψ))
    (gB := smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h φ)
      (relocalizeRepSE B W S hW hS h φ hφ))
    (gC := smallBaseChangeSharp B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
      (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ))
    (ι₁ := relocalizeRingMap B W S hW hS h X) (ι₂ := relocalizeRingMap B W S hW hS h Y)
    (ι₃ := relocalizeRingMap B W S hW hS h Z)
    (relocalizeBaseChangeIsoSE B W S hW hS h φ hφ) (relocalizeBaseChangeIsoSE B W S hW hS h ψ hψ)
    (relocalizeBaseChangeIsoSE B W S hW hS h (φ ≫ ψ) hφψ)
    (smallBaseChangeChartCompIso B W hW φ ψ hφ hψ hφψ)
    (relocalizeChartCompIso B W S hW hS h φ ψ hφ hψ hφψ)
    (relocalizeSharp_compat B W S hW hS h φ hφ) (relocalizeSharp_compat B W S hW hS h ψ hψ)
    (relocalizeSharp_compat B W S hW hS h (φ ≫ ψ) hφψ)
    (smallBaseChangeSharp_comparisonComp B W hW φ ψ hφ hψ hφψ)
    (relocalizeChartCompIso_comparisonComp B W S hW hS h φ ψ hφ hψ hφψ)
    (fun V => by
      convert relocalizeBaseChangeIso_comp_hom_app B W S hW hS h φ ψ hφ hψ hφψ V using 2)

/-! ### The composition law for inverse images -/

section PullbackComp

variable {Y' Z' : AlgebraicSpaces B W hW}

/-- The adjunction `φ^* ⋙ E_Y ⊣ E_Y⁻¹ ⋙ φ_*` through which
`AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE` is defined. -/
abbrev relocalizeModulePullbackSourceAdjunction (φ' : Y' ⟶ Z')
    (hφ' : yoneda.relativelyRepresentable φ'.hom) :=
  ((modulePullbackAdjunction B W hW φ').ofNatIsoRight
      (modulePushforwardChartIso B W hW φ' hφ')).comp
    (relocalizeModulesAdjunction B W S hW hS h Y')

/-- The adjunction `E_Z ⋙ (Λ φ)^* ⊣ (Λ φ)_* ⋙ E_Z⁻¹` through which
`AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE` is defined. -/
abbrev relocalizeModulePullbackTargetAdjunction (φ' : Y' ⟶ Z')
    (hφ' : yoneda.relativelyRepresentable φ'.hom) :=
  (relocalizeModulesAdjunction B W S hW hS h Z').comp
    ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ')).ofNatIsoRight
      (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ')
        (relocalizeRepSE B W S hW hS h φ' hφ')))

/-- **The unit characterisation of `AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE`**: its
conjugate is the comparison of direct images `AlgebraicGeometry.Space.relocalizePushforwardIsoSE`.
-/
theorem conjugateEquiv_relocalizeModulePullbackIso_inv (φ' : Y' ⟶ Z')
    (hφ' : yoneda.relativelyRepresentable φ'.hom) :
    conjugateEquiv (relocalizeModulePullbackSourceAdjunction B W S hW hS h φ' hφ')
        (relocalizeModulePullbackTargetAdjunction B W S hW hS h φ' hφ')
        (relocalizeModulePullbackIsoSE B W S hW hS h φ' hφ').inv =
      (relocalizePushforwardIsoSE B W S hW hS h φ' hφ').inv :=
  congrArg Iso.inv (Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight _ _ _)

section Factors

include hφ hψ hφψ

/-- The composition law of inverse images along `Λ φ` and `Λ ψ`, transposed: the contraction of
base-change direct images. -/
theorem conjugateEquiv_relocalize_modulePullbackCompIso_inv :
    conjugateEquiv
        (((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h ψ)).ofNatIsoRight
            (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h ψ)
              (relocalizeRepSE B W S hW hS h ψ hψ))).comp
          ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ)).ofNatIsoRight
            (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
              (relocalizeRepSE B W S hW hS h φ hφ))))
        ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))).ofNatIsoRight
          (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
            (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)))
        (modulePullbackCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
          (relocalizeHomSE B W S hW hS h ψ)).inv =
      (relocalizeChartPushforwardCompIso B W S hW hS h φ ψ hφ hψ hφψ).hom :=
  conjugateEquiv_modulePullbackCompIso_inv_chart B S hS (relocalizeHomSE B W S hW hS h φ)
    (relocalizeHomSE B W S hW hS h ψ) (relocalizeRepSE B W S hW hS h φ hφ)
    (relocalizeRepSE B W S hW hS h ψ hψ) (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ)

omit hφψ in
private theorem conj_factor_one :
    conjugateEquiv
        (((modulePullbackAdjunction B W hW ψ).ofNatIsoRight
            (modulePushforwardChartIso B W hW ψ hψ)).comp
          (relocalizeModulePullbackSourceAdjunction B W S hW hS h φ hφ))
        (((modulePullbackAdjunction B W hW ψ).ofNatIsoRight
            (modulePushforwardChartIso B W hW ψ hψ)).comp
          (relocalizeModulePullbackTargetAdjunction B W S hW hS h φ hφ))
        (Functor.whiskerLeft (modulePullback B W hW ψ)
          (relocalizeModulePullbackIsoSE B W S hW hS h φ hφ).inv) =
      Functor.whiskerRight (relocalizePushforwardIsoSE B W S hW hS h φ hφ).inv
        (smallBaseChangeModulePushforward B W hW ψ hψ) := by
  exact conjugateEquiv_whiskerLeft_eq _ _ _ _ _
    (conjugateEquiv_relocalizeModulePullbackIso_inv B W S hW hS h φ hφ)

omit hφψ in
private theorem conj_factor_two :
    conjugateEquiv
        (((modulePullbackAdjunction B W hW ψ).ofNatIsoRight
            (modulePushforwardChartIso B W hW ψ hψ)).comp
          (relocalizeModulePullbackTargetAdjunction B W S hW hS h φ hφ))
        ((relocalizeModulePullbackTargetAdjunction B W S hW hS h ψ hψ).comp
          ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ)).ofNatIsoRight
            (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
              (relocalizeRepSE B W S hW hS h φ hφ))))
        (Functor.whiskerRight (relocalizeModulePullbackIsoSE B W S hW hS h ψ hψ).inv
          (modulePullback B S hS (relocalizeHomSE B W S hW hS h φ))) =
      Functor.whiskerLeft
          (smallBaseChangeModulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)
            (relocalizeRepSE B W S hW hS h φ hφ))
        (relocalizePushforwardIsoSE B W S hW hS h ψ hψ).inv := by
  have ha := CategoryTheory.Adjunction.comp_assoc
    ((modulePullbackAdjunction B W hW ψ).ofNatIsoRight (modulePushforwardChartIso B W hW ψ hψ))
    (relocalizeModulesAdjunction B W S hW hS h Y)
    ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ)).ofNatIsoRight
      (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ)))
  rw [ha]
  exact conjugateEquiv_whiskerRight_eq _ _ _ _ _
    (conjugateEquiv_relocalizeModulePullbackIso_inv B W S hW hS h ψ hψ)

private theorem conj_factor_three :
    conjugateEquiv ((relocalizeModulePullbackTargetAdjunction B W S hW hS h ψ hψ).comp
          ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ)).ofNatIsoRight
            (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
              (relocalizeRepSE B W S hW hS h φ hφ))))
        ((relocalizeModulesAdjunction B W S hW hS h Z).comp
          ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))).ofNatIsoRight
            (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
              (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ))))
        (Functor.whiskerLeft
          (relocalizeModulesEquivalenceSE B W S hW hS h Z.2
            (relocalizeSpaceSE B W S hW hS h Z).2).functor
          (modulePullbackCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
            (relocalizeHomSE B W S hW hS h ψ)).inv) =
      Functor.whiskerRight (relocalizeChartPushforwardCompIso B W S hW hS h φ ψ hφ hψ hφψ).hom
        (relocalizeModulesRestriction B W S hW hS h Z) := by
  have ha := CategoryTheory.Adjunction.comp_assoc (relocalizeModulesAdjunction B W S hW hS h Z)
    ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h ψ)).ofNatIsoRight
      (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h ψ)
        (relocalizeRepSE B W S hW hS h ψ hψ)))
    ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ)).ofNatIsoRight
      (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ)))
  rw [← ha]
  exact conjugateEquiv_whiskerLeft_eq _ _ _ _ _
    (conjugateEquiv_relocalize_modulePullbackCompIso_inv B W S hW hS h φ ψ hφ hψ hφψ)

private theorem conj_factor_four :
    conjugateEquiv
        (((modulePullbackAdjunction B W hW ψ).ofNatIsoRight
            (modulePushforwardChartIso B W hW ψ hψ)).comp
          (relocalizeModulePullbackSourceAdjunction B W S hW hS h φ hφ))
        (relocalizeModulePullbackSourceAdjunction B W S hW hS h (φ ≫ ψ) hφψ)
        (Functor.whiskerRight (modulePullbackCompIso B W hW φ ψ).inv
          (relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor) =
      Functor.whiskerLeft (relocalizeModulesRestriction B W S hW hS h X)
        (smallBaseChangeChartPushforwardCompIso B W hW φ ψ hφ hψ hφψ).hom := by
  have ha := CategoryTheory.Adjunction.comp_assoc
    ((modulePullbackAdjunction B W hW ψ).ofNatIsoRight (modulePushforwardChartIso B W hW ψ hψ))
    ((modulePullbackAdjunction B W hW φ).ofNatIsoRight (modulePushforwardChartIso B W hW φ hφ))
    (relocalizeModulesAdjunction B W S hW hS h X)
  rw [ha]
  exact conjugateEquiv_whiskerRight_eq _ _ _ _ _
    (conjugateEquiv_modulePullbackCompIso_inv_chart B W hW φ ψ hφ hψ hφψ)
end Factors

/-- **Inverse images commute with relocalization, compatibly with composition.** For representable
morphisms `φ : X ⟶ Y` and `ψ : Y ⟶ Z` of algebraic spaces over `W`, the identification
`φ^* ⋙ E_X ≅ E_Y ⋙ (Λ φ)^*` of `AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE` followed by
the one for `ψ` is the one for `φ ≫ ψ`, read through the composition laws
`AlgebraicGeometry.Space.modulePullbackCompIso` of the inverse images over `W` and over `S`.

Both sides are comparisons of composites of left adjoints; the equality is checked on the
conjugates (`CategoryTheory.conjugateEquiv`), where it is the pentagon
`AlgebraicGeometry.Space.relocalizePushforwardIso_inv_comp` of the direct images. -/
theorem relocalizeModulePullbackIso_comp :
    Functor.isoWhiskerLeft (modulePullback B W hW ψ)
          (relocalizeModulePullbackIsoSE B W S hW hS h φ hφ) ≪≫
        Functor.isoWhiskerRight (relocalizeModulePullbackIsoSE B W S hW hS h ψ hψ)
          (modulePullback B S hS (relocalizeHomSE B W S hW hS h φ)) ≪≫
        Functor.isoWhiskerLeft
          (relocalizeModulesEquivalenceSE B W S hW hS h Z.2
            (relocalizeSpaceSE B W S hW hS h Z).2).functor
          (modulePullbackCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
            (relocalizeHomSE B W S hW hS h ψ)) =
      Functor.isoWhiskerRight (modulePullbackCompIso B W hW φ ψ)
          (relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor ≪≫
        relocalizeModulePullbackIsoSE B W S hW hS h (φ ≫ ψ) hφψ := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc]
  refine (conjugateEquiv
    (((modulePullbackAdjunction B W hW ψ).ofNatIsoRight
      (modulePushforwardChartIso B W hW ψ hψ)).comp
      (relocalizeModulePullbackSourceAdjunction B W S hW hS h φ hφ))
    ((relocalizeModulesAdjunction B W S hW hS h Z).comp
      ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))).ofNatIsoRight
        (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h (φ ≫ ψ))
          (relocalizeRepSE B W S hW hS h (φ ≫ ψ) hφψ))))).injective ?_
  have P := relocalizePushforwardIso_inv_comp B W S hW hS h φ ψ hφ hψ hφψ
  rw [← conj_factor_one B W S hW hS h φ ψ hφ hψ, ← conj_factor_two B W S hW hS h φ ψ hφ hψ,
    ← conj_factor_three B W S hW hS h φ ψ hφ hψ hφψ, ← conj_factor_four B W S hW hS h φ ψ hφ hψ hφψ,
    ← conjugateEquiv_relocalizeModulePullbackIso_inv B W S hW hS h (φ ≫ ψ) hφψ] at P
  have P' := P.trans (conjugateEquiv_comp _ _ _ _ _)
  refine (conjugateEquiv_comp
    (adj₂ := (relocalizeModulePullbackTargetAdjunction B W S hW hS h ψ hψ).comp
    ((modulePullbackAdjunction B S hS (relocalizeHomSE B W S hW hS h φ)).ofNatIsoRight
      (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeRepSE B W S hW hS h φ hφ)))) _ _ _ _).symm.trans ?_
  exact (congrArg (· ≫ _) (conjugateEquiv_comp _ _ _ _ _).symm).trans
    ((Category.assoc _ _ _).trans P')

omit hφ hψ hφψ in
/-- The comparison of `AlgebraicGeometry.Space.modulePullbackTriangle` at the composite
`Λ φ ≫ Λ ψ = Λ (φ ≫ ψ)` is the composition comparison of Stacks 03LU. -/
theorem modulePullbackTriangle_relocalizeHom_comp
    (hΛ : relocalizeHomSE B W S hW hS h φ ≫ relocalizeHomSE B W S hW hS h ψ =
      relocalizeHomSE B W S hW hS h (φ ≫ ψ)) :
    (modulePullbackTriangle B S hS hΛ).inv =
      (modulePullbackCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeHomSE B W S hW hS h ψ)).hom :=
  Category.comp_id _

omit hφψ in
/-- **The composition law for inverse images across relocalization, at a triangle.**  For
`φ ≫ ψ = k`, the identification for `k` is the identification for `φ` followed by the one for
`ψ`, read through the comparisons `AlgebraicGeometry.Space.modulePullbackTriangle` over `W` and
over `S`.  This is the form in which the relative Hom functors use it. -/
theorem relocalizeModulePullbackIso_triangle {k : X ⟶ Z} (hk : φ ≫ ψ = k)
    (hkrep : yoneda.relativelyRepresentable k.hom)
    (hΛ : relocalizeHomSE B W S hW hS h φ ≫ relocalizeHomSE B W S hW hS h ψ =
      relocalizeHomSE B W S hW hS h k) :
    relocalizeModulePullbackIsoSE B W S hW hS h k hkrep =
      Functor.isoWhiskerRight (modulePullbackTriangle B W hW hk)
          (relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor ≪≫
        Functor.isoWhiskerLeft (modulePullback B W hW ψ)
          (relocalizeModulePullbackIsoSE B W S hW hS h φ hφ) ≪≫
        Functor.isoWhiskerRight (relocalizeModulePullbackIsoSE B W S hW hS h ψ hψ)
          (modulePullback B S hS (relocalizeHomSE B W S hW hS h φ)) ≪≫
        Functor.isoWhiskerLeft
          (relocalizeModulesEquivalenceSE B W S hW hS h Z.2
            (relocalizeSpaceSE B W S hW hS h Z).2).functor
          (modulePullbackTriangle B S hS hΛ).symm := by
  subst hk
  rw [modulePullbackTriangle_rfl]
  have hc := congrArg Iso.hom (relocalizeModulePullbackIso_comp B W S hW hS h φ ψ hφ hψ hkrep)
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom] at hc ⊢
  rw [modulePullbackTriangle_relocalizeHom_comp B W S hW hS h φ ψ hΛ]
  exact eq_inv_comp_of_comp_eq (Functor.isoWhiskerRight (modulePullbackCompIso B W hW φ ψ)
    (relocalizeModulesEquivalenceSE B W S hW hS h X.2
      (relocalizeSpaceSE B W S hW hS h X).2).functor)
    _ _ _ _ hc

end PullbackComp

end AlgebraicGeometry.Space

end
