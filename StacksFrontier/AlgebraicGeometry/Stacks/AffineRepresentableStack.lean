module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SitePullbackStackSquare
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverMapCorners
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSlicePullback
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Algebraic stacks representable by an affine scheme

An algebraic stack over `S` is *representable by an affine scheme*
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineRepresentable`) when it is equivalent over the
big fppf category of `S` to the slice of that category at an object whose underlying scheme is
affine. This file records elementary properties of the notion: it holds for the stack of an
affine scheme, it is invariant under equivalence over the base, such a stack is quasi-compact and
quasi-separated over `S`, its structure functor is faithful, and a 2-fibre product of stacks
representable by affine schemes is again representable by an affine scheme.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineRepresentable_schemeStack`: the stack of an
  affine object of the site is representable by an affine scheme.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineRepresentable_of_equivalenceOver`:
  representability by an affine scheme is invariant under equivalence over the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactStack_of_isAffineRepresentable`: such a
  stack is quasi-compact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_of_isAffineRepresentable`: such a
  stack is quasi-separated over `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.faithful_p_of_isAffineRepresentable`: the structure
  functor of such a stack is faithful.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineRepresentable_twoFibreProductAlgebraicStack`:
  the 2-fibre product of a cospan of stacks representable by affine schemes is representable by
  the fibre product of the affine schemes (Stacks 01JM read through Stacks 004B and Stacks 0041).

## Implementation notes

The 2-fibre product statement is proved at the level of `CategoryTheory.TwoFibreProductOver`: the
three corners are replaced by the slices they are equivalent to
(`CategoryTheory.TwoFibreProductOver.isEquivalence_mapCorners`), the two legs then become functors
over the base between slices, which are 2-isomorphic to the functors `CategoryTheory.Over.map` of
the morphisms of the site underlying them (`AlgebraicGeometry.Stack.schemeStackMapIso`), and the
2-fibre product of two such functors is the slice at the fibre product of the site
(`CategoryTheory.TwoFibreProductOver.slicePullback`, over
`AlgebraicGeometry.Stack.isPullback_sitePullback`).

## References

* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 01JM](https://stacks.math.columbia.edu/tag/01JM)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The algebraic stack of an affine object of the site is representable by an affine scheme. -/
theorem isAffineRepresentable_schemeStack (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    IsAffineRepresentable B S hS (schemeStack.{u, w} B S hS U) :=
  ⟨U, hU, ⟨StacksRepresentableCFG.EquivalenceOver.refl _⟩⟩

/-- Representability by an affine scheme is invariant under equivalence over the base. -/
theorem isAffineRepresentable_of_equivalenceOver {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p 𝒴.val.val.p)
    (h : IsAffineRepresentable B S hS 𝒴) : IsAffineRepresentable B S hS 𝒳 := by
  obtain ⟨U, hU, ⟨e'⟩⟩ := h
  exact ⟨U, hU, ⟨e.trans e'⟩⟩

/-- The structure functor of an algebraic stack representable by an affine scheme is faithful:
it is an equivalence followed by the forgetful functor of a slice. -/
theorem faithful_p_of_isAffineRepresentable {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (h : IsAffineRepresentable B S hS 𝒳) : 𝒳.val.val.p.Faithful := by
  obtain ⟨U, -, ⟨e⟩⟩ := h
  have := e.isEquivalence_hom_functor
  rw [← e.hom.w]
  have : (schemeFibredCategory B S hS U).val.p.Faithful :=
    ⟨fun h => Over.OverMorphism.ext h⟩
  exact Functor.Faithful.comp e.hom.functor (schemeFibredCategory B S hS U).val.p

/-- The 1-morphism of algebraic stacks out of the stack of `U` underlying an equivalence over the
base `𝒳 ≃ Sch/U`. -/
def schemeStackHomOfEquivalenceOver {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (schemeFibredCategory B S hS U).val.p) :
    schemeStack.{u, w} B S hS U ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨e.inv.functor, e.inv.w⟩)

/-- An algebraic stack representable by an affine scheme is quasi-compact. -/
theorem isQuasiCompactStack_of_isAffineRepresentable {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (h : IsAffineRepresentable B S hS 𝒳) : IsQuasiCompactStack B S hS 𝒳.val 𝒳.property := by
  obtain ⟨U, hU, ⟨e⟩⟩ := h
  have := e.isEquivalence_inv_functor
  have : (schemeStackHomOfEquivalenceOver B S hS e).hom.hom.toFunctor.EssSurj :=
    inferInstanceAs e.inv.functor.EssSurj
  exact isQuasiCompactStack_of_essSurj B S hS (schemeStackHomOfEquivalenceOver B S hS e)
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS U hU)

/-- An algebraic stack representable by an affine scheme is quasi-separated over `S`. -/
theorem isQuasiSeparatedOver_of_isAffineRepresentable {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (h : IsAffineRepresentable B S hS 𝒳) : IsQuasiSeparatedOver.{u, w} B S hS 𝒳 := by
  obtain ⟨U, hU, ⟨e⟩⟩ := h
  let c : 𝒳.val.val ⥤ᵇ (schemeStack.{u, w} B S hS U).val.val := ⟨e.hom.functor, e.hom.w⟩
  have hcomp : BasedFunctor.comp c (structureMorphism B S hS (schemeStack.{u, w} B S hS U)).hom.hom
      = (structureMorphism B S hS 𝒳).hom.hom :=
    congrArg (fun k => k.hom.hom) (comp_structureMorphism B S hS
      (Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom c) :
        𝒳 ⟶ schemeStack.{u, w} B S hS U))
  exact isQuasiSeparated_of_equivalence B S hS
    (structureMorphism B S hS (schemeStack.{u, w} B S hS U)) (structureMorphism B S hS 𝒳) c
    (eqToIso hcomp) e.isEquivalence_hom_functor
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS U hU)

section TwoFibreProduct

variable {𝒜 𝒬 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism of algebraic stacks conjugated by equivalences over the base of its source and
target with slices of the site, as a 1-morphism between the represented algebraic stacks. -/
def conjugateSchemeStackHom {A₀ P₀ : BigFppfOver B S hS} (g : 𝒜 ⟶ 𝒬)
    (ea : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (Over.forget A₀))
    (ec : StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p (Over.forget P₀)) :
    schemeStack.{u, w} B S hS A₀ ⟶ schemeStack.{u, w} B S hS P₀ :=
  have hw : (ea.inv.functor ⋙ g.hom.hom.toFunctor ⋙ ec.hom.functor) ⋙ Over.forget P₀ =
      Over.forget A₀ := by
    rw [Functor.assoc, Functor.assoc, ec.hom.w, g.hom.hom.w, ea.inv.w]
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨ea.inv.functor ⋙ g.hom.hom.toFunctor ⋙ ec.hom.functor, hw⟩)

/-- The natural isomorphism `g ⋙ e_𝒬 ≅ e_𝒜 ⋙ Over.map a₀` attached to a 1-morphism `g` and
equivalences of its source and target with slices, `a₀` being the morphism of the site
underlying the conjugate of `g`. -/
def conjugateSchemeStackHomIso {A₀ P₀ : BigFppfOver B S hS} (g : 𝒜 ⟶ 𝒬)
    (ea : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (Over.forget A₀))
    (ec : StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p (Over.forget P₀)) :
    g.hom.hom.toFunctor ⋙ ec.hom.functor ≅
      ea.hom.functor ⋙ Over.map (siteMap B S hS (conjugateSchemeStackHom B S hS g ea ec)) :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight ea.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft ea.hom.functor
      ((BasedNatTrans.forgetful _ _).mapIso
        (algStackHomHomIso B S hS
          (schemeStackMapIso B S hS (conjugateSchemeStackHom B S hS g ea ec))))

/-- Each component of `conjugateSchemeStackHomIso` lies over an identity morphism of the site. -/
theorem conjugateSchemeStackHomIso_isHomLift {A₀ P₀ : BigFppfOver B S hS} (g : 𝒜 ⟶ 𝒬)
    (ea : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (Over.forget A₀))
    (ec : StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p (Over.forget P₀)) (x : 𝒜.val.val.obj) :
    (Over.forget P₀).IsHomLift
      (𝟙 ((Over.forget P₀).obj (ec.hom.functor.obj (g.hom.hom.toFunctor.obj x))))
      ((conjugateSchemeStackHomIso B S hS g ea ec).hom.app x) := by
  have hw : (g.hom.hom.toFunctor ⋙ ec.hom.functor) ⋙ Over.forget P₀ = 𝒜.val.val.p := by
    rw [Functor.assoc, ec.hom.w, g.hom.hom.w]
  have hx : (Over.forget P₀).obj (ec.hom.functor.obj (g.hom.hom.toFunctor.obj x)) =
      𝒜.val.val.p.obj x :=
    Functor.congr_obj hw x
  have h1 : (Over.forget P₀).IsHomLift (𝟙 (𝒜.val.val.p.obj x))
      ((g.hom.hom.toFunctor ⋙ ec.hom.functor).map (ea.unitIso.hom.app x)) :=
    have := ea.isHomLift_unitIso_hom_app x
    Functor.isHomLift_map_of_comp_eq hw _ _
  let ψ := algStackHomHomIso B S hS
    (schemeStackMapIso B S hS (conjugateSchemeStackHom B S hS g ea ec))
  let η := (BasedNatTrans.forgetful _ _).mapIso ψ
  have h2 : (Over.forget P₀).IsHomLift (𝟙 (𝒜.val.val.p.obj x))
      (η.hom.app (ea.hom.functor.obj x)) := by
    have : (Over.forget P₀).IsHomLift (𝟙 ((Over.forget A₀).obj (ea.hom.functor.obj x)))
        (η.hom.app (ea.hom.functor.obj x)) :=
      BasedNatTrans.app_isHomLift ψ.hom (ea.hom.functor.obj x)
    have hx' : (Over.forget A₀).obj (ea.hom.functor.obj x) = 𝒜.val.val.p.obj x :=
      Functor.congr_obj ea.hom.w x
    rwa [hx'] at this
  rw [hx]
  simp only [conjugateSchemeStackHomIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Functor.comp_map]
  exact @IsHomLift.comp_of_lift_id _ _ _ _ (Over.forget P₀) (𝒜.val.val.p.obj x) _ _ _
    (ec.hom.functor.map (g.hom.hom.map (ea.unitIso.hom.app x))) (η.hom.app (ea.hom.functor.obj x))
    h1 h2

/-- **A 2-fibre product of algebraic stacks representable by affine schemes is representable by
an affine scheme**: the fibre product of the affine schemes of the site underlying the two legs
(Stacks 01JM, read through Stacks 004B and Stacks 0041). -/
theorem isAffineRepresentable_twoFibreProductAlgebraicStack (g : 𝒜 ⟶ 𝒬) (t : 𝒯 ⟶ 𝒬)
    (hA : IsAffineRepresentable B S hS 𝒜) (hP : IsAffineRepresentable B S hS 𝒬)
    (hT : IsAffineRepresentable B S hS 𝒯) :
    IsAffineRepresentable B S hS (twoFibreProductAlgebraicStack B S hS g t) := by
  obtain ⟨A₀, hA₀, ⟨ea₀⟩⟩ := hA
  obtain ⟨P₀, hP₀, ⟨ec₀⟩⟩ := hP
  obtain ⟨T₀, hT₀, ⟨eb₀⟩⟩ := hT
  let ea : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p (Over.forget A₀) := ea₀
  let ec : StacksRepresentableCFG.EquivalenceOver 𝒬.val.val.p (Over.forget P₀) := ec₀
  let eb : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p (Over.forget T₀) := eb₀
  set a₀ := siteMap B S hS (conjugateSchemeStackHom B S hS g ea ec)
  set b₀ := siteMap B S hS (conjugateSchemeStackHom B S hS t eb ec)
  let M := TwoFibreProductOver.mapCorners ea.hom.w eb.hom.w ec.hom.w
    (F' := Over.map a₀) (G' := Over.map b₀)
    (conjugateSchemeStackHomIso B S hS g ea ec) (conjugateSchemeStackHomIso B S hS t eb ec)
    (conjugateSchemeStackHomIso_isHomLift B S hS g ea ec)
    (conjugateSchemeStackHomIso_isHomLift B S hS t eb ec)
  have hM : M.IsEquivalence := TwoFibreProductOver.isEquivalence_mapCorners ea eb ec rfl rfl _ _
    (conjugateSchemeStackHomIso_isHomLift B S hS g ea ec)
    (conjugateSchemeStackHomIso_isHomLift B S hS t eb ec)
  have hpb := isPullback_sitePullback B S hS a₀ b₀
  have hfib₂ : (TwoFibreProductOver.structureFunctor (Over.forget A₀) (Over.forget T₀)
      (Over.forget P₀) (Over.map a₀) (Over.map b₀)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (Functor.IsFiberedInGroupoids.over_forget A₀) (Functor.IsFiberedInGroupoids.over_forget T₀)
      (Functor.IsFiberedInGroupoids.over_forget P₀) rfl rfl
  obtain ⟨e₁⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (twoFibreProductAlgebraicStack B S hS g t).val.isFiberedInGroupoids hfib₂ M
    (TwoFibreProductOver.mapCorners_comp_structureFunctor _ _ _ _ _ _ _) hM
  obtain ⟨e₂⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (Functor.IsFiberedInGroupoids.over_forget (sitePullbackObj B S hS a₀ b₀)) hfib₂
    (TwoFibreProductOver.slicePullback hpb)
    (TwoFibreProductOver.slicePullback_comp_structureFunctor hpb) inferInstance
  refine ⟨sitePullbackObj B S hS a₀ b₀, ?_, ⟨e₁.trans e₂.symm⟩⟩
  rw [toScheme_obj_sitePullbackObj]
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A₀) := hA₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := hT₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj P₀) := hP₀
  infer_instance

end TwoFibreProduct

end AlgebraicGeometry.Stack.AlgebraicStacks

end
