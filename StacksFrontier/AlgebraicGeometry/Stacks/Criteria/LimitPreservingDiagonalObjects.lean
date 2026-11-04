module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
import all StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation

/-!
# Limit preservation on objects passes to the relative diagonal

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S` which is representable by algebraic spaces and limit preserving on objects. Then the
relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is again limit preserving on objects.

This is the fullness content of Stacks 0CMV, phrased at the level of fibre categories: it is the
input the converse direction of that tag needs about the diagonal, and it carries no tag of its
own. It is a consequence of the representability criterion of Stacks 02ZY (through faithfulness
of the underlying functor of `f`), of Stacks 06CX, and of Stacks 04AK.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_twoFibreProductDiagonal`: the relative
  diagonal of a 1-morphism representable by algebraic spaces and limit preserving on objects is
  limit preserving on objects.
* `AlgebraicGeometry.Stack.exists_stage_eq_of_relativelyLimitPreserving`: two sections over a
  stage which agree over an affine inverse limit already agree at a later stage.

## Implementation notes

An object of the fibre of `𝒳 ×_{f, 𝒴, f} 𝒳` over `U_i` is a triple `(x₁, x₂, φ)` with
`φ : f x₁ ≅ f x₂`, and a strongly cartesian morphism out of `Δ_f x` into it is a pair of
strongly cartesian morphisms `x ⟶ x₁`, `x ⟶ x₂` compatible with `φ`. Descending it to a stage is
therefore descending an isomorphism `x₁ ≅ x₂` over `φ`, and that is read off the algebraic space
representing the base change of `f` along the scheme-valued point `f x₂` of `𝒴`: the two objects
`(x₁, φ⁻¹)` and `(x₂, 𝟙)` of its fibre give two sections which agree over the limit, hence at
some stage. Local finite presentation of that algebraic space comes from Stacks 06CX and turns
into relative limit preservation by Stacks 04AK, exactly as in the proof of Stacks 06CX itself;
`exists_stage_eq_of_relativelyLimitPreserving` is the injectivity half of the resulting filtered
colimit of section sets, the surjectivity half being the private
`exists_stage_of_relativelyLimitPreserving` of the 06CX file. Both are built on the single
`Nonempty (IsColimit _)` statement extracted there.

That the second component of the descended comparison is the right one is checked after applying
the underlying functor of `f`, which is faithful because `f` is representable by algebraic
spaces (Stacks 04Y5).

## References

* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 0CMV](https://stacks.math.columbia.edu/tag/0CMV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] Cat.category StrictBicategory.category
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  Pseudofunctor.CoGrothendieck.forget BasedCategory.ofFunctor
  PresheafOfCategories.objEquiv Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.ChoiceOfPullbacks.sliceFunctor TwoFibreProductOver.fst
  Over.post

namespace AlgebraicGeometry.Stack

universe u

/-- **The injectivity half of the descent of sections.** Two sections of `F` over a stage of a
cofiltered system of affines in the slice over `U` which agree after restriction to the limit
already agree after a single transition morphism, provided the structural morphism of the
algebraic space representing `F` is relatively limit preserving. -/
theorem exists_stage_eq_of_relativelyLimitPreserving
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (X : SpacesOverSmallerBase B U.left.1 S U.left.2 hS U.hom)
    (ι : X.1.left ≅ (OverShriek.relocalizePresheafFunctor U.hom).obj F)
    (hι : ∀ W t, X.1.hom.app W (ι.inv.app W t) = Over.homMk t.1.1 t.2)
    (hrel : RelativelyLimitPreserving.{u, u, u, u} B S hS X.1.hom)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over U.left) (c : Cone D)
    (hc : IsLimit ((Over.forget U.left ⋙ B.inclusion).mapCone c))
    (hD : ∀ i, IsAffine ((Over.forget U.left ⋙ B.inclusion).obj (D.obj i)))
    (hpt : IsAffine ((Over.forget U.left ⋙ B.inclusion).obj c.pt))
    (i : I) (t₁ t₂ : F.obj (op (D.obj i)))
    (h : F.map (c.π.app i).op t₁ = F.map (c.π.app i).op t₂) :
    ∃ (k : I) (a : k ⟶ i), F.map (D.map a).op t₁ = F.map (D.map a).op t₂ := by
  obtain ⟨hq⟩ := nonempty_isColimit_of_relativelyLimitPreserving.{u, u, u}
    B S hS U F X ι hι hrel D c hc hD hpt
  obtain ⟨k, a, hka⟩ := (Types.FilteredColimit.isColimit_eq_iff' hq t₁ t₂).mp h
  exact ⟨k.unop, a.unop, hka⟩

/-- Two strongly cartesian morphisms of `p` lying over one and the same morphism of the base and
with a common codomain have canonically isomorphic domains: there is a vertical isomorphism
between them through which the two morphisms factor. -/
private lemma exists_vertical_iso_of_isStronglyCartesian {C : Type*} [Category C]
    {Z : Type*} [Category Z] (p : Z ⥤ C) {R T : C} (g : R ⟶ T) {a a' b : Z}
    (φ : a ⟶ b) (φ' : a' ⟶ b) (hφ : p.IsStronglyCartesian g φ)
    (hφ' : p.IsStronglyCartesian g φ') :
    ∃ θ : a' ⟶ a, IsIso θ ∧ p.IsHomLift (𝟙 R) θ ∧ θ ≫ φ = φ' := by
  have hrefl : g = (Iso.refl R).hom ≫ g := by simp
  refine ⟨(Functor.IsStronglyCartesian.domainIsoOfBaseIso p hrefl φ φ').hom, inferInstance, ?_, ?_⟩
  · exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p hrefl φ φ'
  · rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
    exact Functor.IsStronglyCartesian.fac p g φ hrefl φ'

/-- **The relative diagonal of a 1-morphism representable by algebraic spaces which is limit
preserving on objects is limit preserving on objects.** This is the fullness content of
Stacks 0CMV at the level of fibre categories; it has no tag of its own and follows from
Stacks 02ZY, Stacks 06CX and Stacks 04AK. -/
theorem isLimitPreservingOnObjects_twoFibreProductDiagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)
    (hp : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳 𝒴 f) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B S hS 𝒳
      (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳 𝒴 𝒳 f f)
      (BigFppfOver.twoFibreProductDiagonal.{u, u, u} B S hS 𝒳 𝒴 f) := by
  classical
  intro I hI hcof D c hc i w x γ hγ
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let Fh := CatFiberedInGroupoids.homFunctor f
  have hFcp : Fh ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p f
  let T := BigAffineFppf.inclusion B S hS
  let Ds := D ⋙ T
  let cs := T.mapCone c
  let Ui := Ds.obj i
  let q := Over.map Ui.hom
  let cy := 𝒴.val.p.chosenPullbacks
  let E := nestedOverToOver Ui
  have hwbase : w.1.base = Ui := w.2
  have hy₀ : 𝒴.val.p.obj (Fh.obj w.1.y) = Ui :=
    (Functor.congr_obj hFcp w.1.y).trans (w.1.hy.trans hwbase)
  let y₀ : 𝒴.val.p.Fiber Ui := ⟨Fh.obj w.1.y, hy₀⟩
  let ypt := E ⋙ cy.sliceFunctor y₀
  have hyq : ypt ⋙ 𝒴.val.p = q := by
    show E ⋙ cy.sliceFunctor y₀ ⋙ 𝒴.val.p = q
    rw [Functor.ChoiceOfPullbacks.sliceFunctor_comp]
    rfl
  obtain ⟨Fsp, hFsp, ⟨e⟩⟩ := hp Ui ypt hyq
  let P := TwoFibreProductOver.fst q 𝒳.val.p 𝒴.val.p ypt Fh
  let X := (spacesOverSmallerBaseFunctor B Ui.left.1 S Ui.left.2 hS Ui.hom).obj ⟨Fsp, hFsp⟩
  have hfp := (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation
    B S hS 𝒳 𝒴 f hp).1 hlim Ui ypt hyq Fsp hFsp ⟨e⟩
  have hrel : RelativelyLimitPreserving.{u, u, u, u} B S hS X.1.hom :=
    relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS
      X.property (isAlgebraicSpace_yoneda B S hS (Over.mk Ui.hom)) hfp
  let D₀ : Over i ⥤ Over Ui.left :=
    Over.post Ds ⋙ Over.post (BigFppfOver.forget B S hS)
  let c₀ := stageCone Ds cs i
  have hcs : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cs) :=
    IsLimit.ofIsoLimit hc (Functor.mapConeMapCone c).symm
  have hc₀ := stageCone_isLimit B S hS Ds cs i hcs
  have hD₀ : ∀ j, IsAffine ((Over.forget Ui.left ⋙ B.inclusion).obj (D₀.obj j)) :=
    fun j => (D.obj j.left).property
  have hpt₀ : IsAffine ((Over.forget Ui.left ⋙ B.inclusion).obj c₀.pt) := c.pt.property
  have hbase₀ : q.obj c₀.pt = cs.pt := by
    show Over.mk ((cs.π.app i).left ≫ Ui.hom) = cs.pt
    rw [(cs.π.app i).w]
    rfl
  have hbase₁ : ∀ j : Over i, q.obj (D₀.obj j) = Ds.obj j.left := by
    intro j
    show Over.mk ((Ds.map j.hom).left ≫ Ui.hom) = Ds.obj j.left
    rw [(Ds.map j.hom).w]
    rfl
  have hstage : ∀ j : Over i,
      (E.obj (D₀.obj j)).hom = eqToHom (hbase₁ j) ≫ Ds.map j.hom := by
    intro j
    apply Over.OverMorphism.ext
    simp [E, nestedOverToOver, nestedOverObject, D₀]
    rfl
  have hγw : Fh.map γ.a ≫ w.1.iso.hom = Fh.map γ.b := by
    have h : Fh.map γ.a ≫ w.1.iso.hom = (Iso.refl (Fh.obj x.1)).hom ≫ Fh.map γ.b := γ.w
    rwa [Iso.refl_hom, Category.id_comp] at h
  have hγbase : γ.hbase = eqToHom x.2 ≫ T.map (c.π.app i) ≫ eqToHom hwbase.symm :=
    IsHomLift.fac' (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳 𝒴 𝒳 f f).val.p
      (T.map (c.π.app i)) γ
  have hlift : ∀ {a b : type_of% x.1} (φ : a ⟶ b), 𝒳.val.p.IsHomLift γ.hbase φ →
      𝒳.val.p.IsHomLift (T.map (c.π.app i)) φ := fun φ h => by
    rw [hγbase] at h
    exact (IsHomLift.lift_comp_eqToHom_iff 𝒳.val.p (T.map (c.π.app i)) φ hwbase.symm).1
      ((IsHomLift.lift_eqToHom_comp_iff 𝒳.val.p
        (T.map (c.π.app i) ≫ eqToHom hwbase.symm) φ x.2).1 h)
  have ha₁ : 𝒳.val.p.IsHomLift (T.map (c.π.app i)) γ.a := hlift _ γ.ha
  have ha₂ : 𝒳.val.p.IsHomLift (T.map (c.π.app i)) γ.b := hlift _ γ.hb
  let k₀ := (E.obj c₀.pt).hom
  have hk₀ : k₀ = eqToHom hbase₀ ≫ cs.π.app i := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left]
    simp [k₀, E, nestedOverToOver, nestedOverObject, c₀, stageCone]
  have hFb : 𝒴.val.p.IsHomLift k₀ (Fh.map γ.b : Fh.obj x.1 ⟶ y₀.1) := by
    rw [hk₀]
    have : 𝒴.val.p.IsHomLift (cs.π.app i) (Fh.map γ.b : Fh.obj x.1 ⟶ y₀.1) := by
      have : 𝒳.val.p.IsHomLift (cs.π.app i) γ.b := by simpa [cs, T] using ha₂
      exact Functor.isHomLift_map_of_comp_eq hFcp (cs.π.app i) γ.b
    infer_instance
  obtain ⟨κ₂, _, hκ₂, hκ₂fac⟩ : ∃ θ : ypt.obj c₀.pt ⟶ Fh.obj x.1, IsIso θ ∧
      𝒴.val.p.IsHomLift (𝟙 (q.obj c₀.pt)) θ ∧ θ ≫ Fh.map γ.b = cy.map k₀ y₀ :=
    exists_vertical_iso_of_isStronglyCartesian 𝒴.val.p k₀
      (Fh.map γ.b : Fh.obj x.1 ⟶ y₀.1) (cy.map k₀ y₀)
      (𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift k₀ _) (cy.isStronglyCartesian k₀ y₀)
  let C : TwoFibreProductOver q 𝒳.val.p 𝒴.val.p ypt Fh :=
    ⟨q.obj c₀.pt, c₀.pt, x.1, rfl, x.2.trans hbase₀.symm, asIso κ₂, hκ₂⟩
  let j₀ : Over i := Over.mk (𝟙 i)
  have hk₁ : (E.obj (D₀.obj j₀)).hom = eqToHom (hbase₁ j₀) := by
    have h := hstage j₀
    rw [show Ds.map j₀.hom = 𝟙 Ui from Ds.map_id i] at h
    exact h.trans (Category.comp_id _)
  have hidlift : 𝒴.val.p.IsHomLift (E.obj (D₀.obj j₀)).hom (𝟙 y₀.1) := by
    rw [hk₁]
    exact IsHomLift.id_lift_eqToHom_domain (hbase₁ j₀) (hy₀.trans (hbase₁ j₀).symm)
  have hwisolift : 𝒴.val.p.IsHomLift (E.obj (D₀.obj j₀)).hom w.1.iso.hom := by
    have hfe : eqToHom (hbase₁ j₀) =
        eqToHom (hwbase.trans (hbase₁ j₀).symm).symm ≫ 𝟙 w.1.base ≫ eqToHom hwbase := by
      simp
    rw [hk₁, hfe]
    have := w.1.vertical
    infer_instance
  obtain ⟨κ, _, hκ, hκfac⟩ : ∃ θ : ypt.obj (D₀.obj j₀) ⟶ Fh.obj w.1.y, IsIso θ ∧
      𝒴.val.p.IsHomLift (𝟙 (q.obj (D₀.obj j₀))) θ ∧
      θ ≫ 𝟙 (Fh.obj w.1.y) = cy.map (E.obj (D₀.obj j₀)).hom y₀ :=
    exists_vertical_iso_of_isStronglyCartesian 𝒴.val.p (E.obj (D₀.obj j₀)).hom
      (𝟙 y₀.1) (cy.map (E.obj (D₀.obj j₀)).hom y₀)
      (𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ _) (cy.isStronglyCartesian _ _)
  have hκeq : κ = cy.map (E.obj (D₀.obj j₀)).hom y₀ := by simpa using hκfac
  obtain ⟨ι₁, _, hι₁, hι₁fac⟩ : ∃ θ : ypt.obj (D₀.obj j₀) ⟶ Fh.obj w.1.x, IsIso θ ∧
      𝒴.val.p.IsHomLift (𝟙 (q.obj (D₀.obj j₀))) θ ∧
      θ ≫ w.1.iso.hom = cy.map (E.obj (D₀.obj j₀)).hom y₀ :=
    exists_vertical_iso_of_isStronglyCartesian 𝒴.val.p (E.obj (D₀.obj j₀)).hom
      w.1.iso.hom (cy.map (E.obj (D₀.obj j₀)).hom y₀)
      (𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ _) (cy.isStronglyCartesian _ _)
  have h₁obj : 𝒳.val.p.obj w.1.x = q.obj (D₀.obj j₀) :=
    w.1.hx.trans (hwbase.trans (hbase₁ j₀).symm)
  have h₂obj : 𝒳.val.p.obj w.1.y = q.obj (D₀.obj j₀) :=
    w.1.hy.trans (hwbase.trans (hbase₁ j₀).symm)
  let A₁ : TwoFibreProductOver q 𝒳.val.p 𝒴.val.p ypt Fh :=
    ⟨q.obj (D₀.obj j₀), D₀.obj j₀, w.1.x, rfl, h₁obj, asIso ι₁, hι₁⟩
  let A₂ : TwoFibreProductOver q 𝒳.val.p 𝒴.val.p ypt Fh :=
    ⟨q.obj (D₀.obj j₀), D₀.obj j₀, w.1.y, rfl, h₂obj, asIso κ, hκ⟩
  have hqleg : ∀ j : Over i, q.map (c₀.π.app j) =
      eqToHom hbase₀ ≫ cs.π.app j.left ≫ eqToHom (hbase₁ j).symm := by
    intro j
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left]
    simp [q, c₀, stageCone]
  have hqleg₀ : q.map (c₀.π.app j₀) =
      eqToHom hbase₀ ≫ T.map (c.π.app i) ≫ eqToHom (hbase₁ j₀).symm := hqleg j₀
  have hsliceFac : ypt.map (c₀.π.app j₀) ≫ cy.map (E.obj (D₀.obj j₀)).hom y₀ =
      cy.map k₀ y₀ :=
    Functor.ChoiceOfPullbacks.sliceFunctor_map_fac cy y₀ (E.map (c₀.π.app j₀))
  let Φ₂ : C ⟶ A₂ :=
    { hbase := q.map (c₀.π.app j₀)
      a := c₀.π.app j₀
      b := γ.b
      ha := inferInstance
      hb := by
        show 𝒳.val.p.IsHomLift (q.map (c₀.π.app j₀)) γ.b
        rw [hqleg₀]
        infer_instance
      w := by
        show ypt.map (c₀.π.app j₀) ≫ κ = κ₂ ≫ Fh.map γ.b
        rw [hκeq, hκ₂fac]
        exact hsliceFac }
  let Φ₁ : C ⟶ A₁ :=
    { hbase := q.map (c₀.π.app j₀)
      a := c₀.π.app j₀
      b := γ.a
      ha := inferInstance
      hb := by
        show 𝒳.val.p.IsHomLift (q.map (c₀.π.app j₀)) γ.a
        rw [hqleg₀]
        infer_instance
      w := by
        show ypt.map (c₀.π.app j₀) ≫ ι₁ = κ₂ ≫ Fh.map γ.a
        rw [← cancel_mono w.1.iso.hom, Category.assoc, Category.assoc, hι₁fac, hsliceFac,
          ← hκ₂fac]
        exact congrArg (κ₂ ≫ ·) hγw.symm }
  let Cf : P.Fiber c₀.pt := ⟨C, rfl⟩
  let A₁f : P.Fiber (D₀.obj j₀) := ⟨A₁, rfl⟩
  let A₂f : P.Fiber (D₀.obj j₀) := ⟨A₂, rfl⟩
  obtain ⟨kk, aa, hkk⟩ := exists_stage_eq_of_relativelyLimitPreserving B S hS Ui Fsp X
    ((spacesOverSmallerBaseFunctorForgetIso B Ui.left.1 S Ui.left.2 hS Ui.hom).app ⟨Fsp, hFsp⟩)
    (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B Ui.left.1 S Ui.left.2 hS Ui.hom ⟨Fsp, hFsp⟩)
    hrel D₀ c₀ hc₀ hD₀ hpt₀ j₀ (pointOfObj Fsp P e A₁f) (pointOfObj Fsp P e A₂f)
    ((pointOfObj_map_of_lift Fsp P e (x := Cf) (y := A₁f) (c₀.π.app j₀) Φ₁
      (Functor.IsHomLift.map (p := P) Φ₁)).symm.trans
      (pointOfObj_map_of_lift Fsp P e (x := Cf) (y := A₂f) (c₀.π.app j₀) Φ₂
        (Functor.IsHomLift.map (p := P) Φ₂)))
  have hPfib : P.IsFiberedInGroupoids :=
    fst_isFiberedInGroupoids_overMap Ui.hom 𝒳.val.p 𝒴.val.p ypt Fh
      𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hyq hFcp
  obtain ⟨z₁, ρ₁, hρ₁⟩ := hPfib.exists_lift (D₀.map aa) A₁ A₁f.2
  obtain ⟨z₂, ρ₂, hρ₂⟩ := hPfib.exists_lift (D₀.map aa) A₂ A₂f.2
  let R₁ : P.Fiber (D₀.obj kk) := ⟨z₁, IsHomLift.domain_eq P (D₀.map aa) ρ₁⟩
  let R₂ : P.Fiber (D₀.obj kk) := ⟨z₂, IsHomLift.domain_eq P (D₀.map aa) ρ₂⟩
  obtain ⟨ψ⟩ := fiberIso_of_point_eq Fsp P e R₁ R₂
    ((pointOfObj_map_of_lift Fsp P e (x := R₁) (y := A₁f) (D₀.map aa) ρ₁ hρ₁).trans
      (hkk.trans (pointOfObj_map_of_lift Fsp P e (x := R₂) (y := A₂f) (D₀.map aa) ρ₂ hρ₂).symm))
  have hzb : ∀ {j : Over i} (R : P.Fiber (D₀.obj j)), R.1.base = Ds.obj j.left := fun R =>
    R.1.hx.symm.trans ((congrArg q.obj R.2).trans (hbase₁ _))
  have hlb : ∀ {j j' : Over i} {R : P.Fiber (D₀.obj j)} {R' : P.Fiber (D₀.obj j')}
      (ρ : R.1 ⟶ R'.1) (g : j ⟶ j'), P.IsHomLift (D₀.map g) ρ →
      ρ.a = eqToHom R.2 ≫ D₀.map g ≫ eqToHom R'.2.symm ∧
        𝒳.val.p.IsHomLift (T.map (D.map g.left)) ρ.b := by
    intro j j' R R' ρ g hρ
    have hρa : ρ.a = eqToHom R.2 ≫ D₀.map g ≫ eqToHom R'.2.symm :=
      IsHomLift.fac' P (D₀.map g) ρ
    refine ⟨hρa, ?_⟩
    have hbase : ρ.hbase = eqToHom (hzb R) ≫ Ds.map g.left ≫ eqToHom (hzb R').symm := by
      rw [ρ.hbase_eq, hρa]
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.eqToHom_left, Functor.map_comp, eqToHom_map]
      simp [q, D₀]
    have := ρ.hb
    have hh : 𝒳.val.p.IsHomLift
        (eqToHom (hzb R).symm ≫ ρ.hbase ≫ eqToHom (hzb R')) ρ.b := inferInstance
    rw [hbase] at hh
    simpa [Ds] using hh
  obtain ⟨hρ₁a, hρ₁b⟩ := hlb (R := R₁) (R' := A₁f) ρ₁ aa hρ₁
  obtain ⟨hρ₂a, hρ₂b⟩ := hlb (R := R₂) (R' := A₂f) ρ₂ aa hρ₂
  obtain ⟨hψa, hψb⟩ := hlb (R := R₁) (R' := R₂) ψ.hom.1 (𝟙 kk) (by simpa using ψ.hom.2)
  have hacomp : ψ.hom.1.a ≫ ρ₂.a = ρ₁.a := by
    rw [hψa, hρ₂a, hρ₁a]
    simp
  have hwsq : Fh.map ρ₁.b ≫ w.1.iso.hom = Fh.map (ψ.hom.1.b ≫ ρ₂.b) := by
    have e1 : ypt.map ρ₁.a ≫ ι₁ = z₁.iso.hom ≫ Fh.map ρ₁.b := ρ₁.w
    have e2 : ypt.map ρ₂.a ≫ κ = z₂.iso.hom ≫ Fh.map ρ₂.b := ρ₂.w
    have e3 : ypt.map ψ.hom.1.a ≫ z₂.iso.hom = z₁.iso.hom ≫ Fh.map ψ.hom.1.b := ψ.hom.1.w
    rw [← cancel_epi z₁.iso.hom, ← reassoc_of% e1, hι₁fac, ← hacomp]
    simp only [Functor.map_comp, Category.assoc]
    rw [← hκeq, e2, reassoc_of% e3]
  let x' : 𝒳.val.p.Fiber (T.obj (D.obj kk.left)) := ⟨z₁.y, z₁.hy.trans (hzb R₁)⟩
  have hcompb : 𝒳.val.p.IsHomLift (T.map (D.map aa.left)) (ψ.hom.1.b ≫ ρ₂.b) := by
    have : 𝒳.val.p.IsHomLift (𝟙 (T.obj (D.obj kk.left))) ψ.hom.1.b := by simpa using hψb
    simpa using (inferInstance : 𝒳.val.p.IsHomLift
      (𝟙 (T.obj (D.obj kk.left)) ≫ T.map (D.map aa.left)) (ψ.hom.1.b ≫ ρ₂.b))
  have hFaith : Fh.Faithful :=
    faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hp
  let γ' : (TwoFibreProductOver.diagonal hFcp).obj x'.1 ⟶ w.1 :=
    { hbase := eqToHom x'.2 ≫ T.map (D.map aa.left) ≫ eqToHom hwbase.symm
      a := ρ₁.b
      b := ψ.hom.1.b ≫ ρ₂.b
      ha := by
        show 𝒳.val.p.IsHomLift
          (eqToHom x'.2 ≫ T.map (D.map aa.left) ≫ eqToHom hwbase.symm) ρ₁.b
        infer_instance
      hb := by
        show 𝒳.val.p.IsHomLift
          (eqToHom x'.2 ≫ T.map (D.map aa.left) ≫ eqToHom hwbase.symm) (ψ.hom.1.b ≫ ρ₂.b)
        infer_instance
      w := by
        show Fh.map ρ₁.b ≫ w.1.iso.hom =
          (Iso.refl (Fh.obj x'.1)).hom ≫ Fh.map (ψ.hom.1.b ≫ ρ₂.b)
        rw [Iso.refl_hom, Category.id_comp]
        exact hwsq }
  have hγ'hl : (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsHomLift
      (T.map (D.map aa.left)) γ' :=
    IsHomLift.of_fac' _ (T.map (D.map aa.left)) γ' x'.2 hwbase rfl
  obtain ⟨xu, δ, hδ⟩ := 𝒳.isFiberedInGroupoids.exists_lift (T.map (c.π.app kk.left)) x'.1 x'.2
  let xU : 𝒳.val.p.Fiber (T.obj c.pt) :=
    ⟨xu, IsHomLift.domain_eq 𝒳.val.p (T.map (c.π.app kk.left)) δ⟩
  have hcw : T.map (c.π.app kk.left) ≫ T.map (D.map aa.left) = T.map (c.π.app i) := by
    rw [← T.map_comp, c.w aa.left]
    rfl
  have hδρ : 𝒳.val.p.IsHomLift (T.map (c.π.app i)) (δ ≫ ρ₁.b : xu ⟶ w.1.x) := by
    rw [← hcw]
    infer_instance
  obtain ⟨β, hβiso, hβlift, hβfac⟩ := exists_vertical_iso_of_isStronglyCartesian 𝒳.val.p
    (T.map (c.π.app i)) γ.a (δ ≫ ρ₁.b : xu ⟶ w.1.x)
    (𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ _)
    (𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ _)
  refine ⟨kk.left, aa.left, x', xU, δ, β, γ',
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ δ, hβlift, hβiso, ?_, ?_⟩
  · exact (BigFppfOver.twoFibreProduct.{u, u, u} B S hS 𝒳 𝒴 𝒳 f f).2.isStronglyCartesian_homLift
      _ γ'
  · refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact hβfac.symm
    · show δ ≫ (ψ.hom.1.b ≫ ρ₂.b) = β ≫ γ.b
      apply Fh.map_injective
      rw [Fh.map_comp, ← hwsq, ← Category.assoc, ← Fh.map_comp, ← hβfac, Fh.map_comp,
        Category.assoc, hγw]
      exact (Fh.map_comp _ _).symm

end AlgebraicGeometry.Stack

end
