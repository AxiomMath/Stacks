module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleDirectImageSections
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrowTerminalPullback

/-!
# The direct image along an affine 1-morphism is cartesian between affines

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
and `F` a sheaf of `𝒪_𝒳`-modules. For an arrow `φ : y ⟶ y'` of `𝒴` over a morphism of affine
schemes, suppose that the comma categories `CostructuredArrow f y` and `CostructuredArrow f y'`
have terminal objects `x₀ = y ×_𝒴 𝒳` and `x₀' = y' ×_𝒴 𝒳`, with `x₀'` over an affine scheme.
Then the arrow `k : x₀ ⟶ x₀'` induced by terminality lies over the base change of the scheme
morphism under `φ` (`CategoryTheory.isPullback_map_of_isTerminal_costructuredArrow`), so the
square of global functions is a pushout, and the sections of `f_*F` over `y`, `y'` are those of
`F` over `x₀`, `x₀'`. Hence
(`Stacks.SheafOfModules.bijective_restrictionBaseChange_ranObj_of_isTerminal`)

`Γ(y) ⊗_{Γ(y')} (f_*F)(y') ⟶ (f_*F)(y)` is bijective as soon as
`Γ(x₀) ⊗_{Γ(x₀')} F(x₀') ⟶ F(x₀)` is.

This is the cartesian half of clause (4) of **Stacks 076Z** for the rule `LQCoh^fbc` in the
proof of **Stacks 0765**: for `𝒳` and `𝒴` represented by affine schemes the fibre products
`y ×_𝒴 𝒳` exist and are affine over affine `y`, and the base change of a flat (or étale) morphism
is flat (or étale), so cartesianness of `F` along flat (étale) maps of affines passes to `f_*F`.

## Main results

* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_moduleDirectImage_of_isTerminal`: the
  statement for the canonical direct image `AlgebraicGeometry.Stack.moduleDirectImage`.
* `isIso_restrictionBaseChange_moduleDirectImage_of_isTerminal_of_isTerminal` (namespace
  `AlgebraicGeometry.Stack`): if `𝒳` and `𝒴` have terminal objects over affine schemes and `F`
  is cartesian between affines along a base-change-stable class `P` of morphisms, then so is
  `f_*F`.
* `exists_isTerminal_costructuredArrow_of_isAffineRepresentable` (namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`): the terminal arrows `y ×_𝒴 𝒳` for a 1-morphism of
  algebraic stacks represented by affine schemes, over an affine scheme when `y` is.
* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_stackModuleDirectImage`: the same
  cartesianness for the direct image `AlgebraicGeometry.Stack.stackModuleDirectImage` along a
  1-morphism of algebraic stacks represented by affine schemes.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w v' w'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section General

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  [f.IsCocontinuous (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)]
  [∀ F : 𝒳ᵒᵖ ⥤ RingCat.{u}, f.op.HasPointwiseRightKanExtension F]
  [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u}, f.op.HasPointwiseRightKanExtension F]

/-- If `𝒳` and `𝒴` have terminal objects over affine schemes, a terminal object of
`CostructuredArrow f z` with `z` over an affine scheme lies over an affine scheme. -/
private theorem isAffine_obj_left_of_isTerminal_costructuredArrow (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    {x₀ : 𝒳} (hx₀ : IsTerminal x₀) {y₀ : 𝒴} (hy₀ : IsTerminal y₀)
    (hax₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₀)))
    (hay₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y₀)))
    {z : 𝒴} {t : CostructuredArrow f z} (ht : IsTerminal t)
    (hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj z))) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj t.left)) := by
  subst hf
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hzero := isTerminalCostructuredArrowMkOfIsTerminal f hx₀ hy₀
  have := hz
  have := hay₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (q.obj (f.obj (CostructuredArrow.mk (hy₀.from (f.obj x₀))).left))) := hax₀
  exact .of_isPullback ((isPullback_map_of_isTerminal_costructuredArrow (f ⋙ q) q f hp hq
    rfl (hy₀.from z) ht hzero).map (BigFppfOver.toScheme B S hS))

/-- **The direct image is cartesian over an arrow of affines with terminal arrows.** Let
`φ : y ⟶ y'` be an arrow of `𝒴` between objects over affine schemes, `t`, `t'` terminal objects of
`CostructuredArrow f y`, `CostructuredArrow f y'` with `t'.left` over an affine scheme, and
`k : t.left ⟶ t'.left` the induced arrow. If `F` is cartesian over `k`, then `f_*F` is cartesian
over `φ`. -/
theorem isIso_restrictionBaseChange_moduleDirectImage_of_isTerminal
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ))
    {y y' : 𝒴} (φ : y ⟶ y') {t : CostructuredArrow f y} (ht : IsTerminal t)
    {t' : CostructuredArrow f y'} (ht' : IsTerminal t')
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y)))
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y')))
    (hx' : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj t'.left)))
    (hF : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS p hp τ hτ).obj) F.val
      (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left.op)) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS q hq τ hτ).obj)
      ((moduleDirectImage.{u, v, w, v', w', u} B S hS p q hp hq f hf τ hτ).obj F).val φ.op) := by
  subst hf
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let k : t.left ⟶ t'.left := (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left
  have hpb := (isPullback_map_of_isTerminal_costructuredArrow (f ⋙ q) q f hp hq rfl φ ht
    ht').map (BigFppfOver.toScheme B S hS)
  have := hy
  have := hy'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj (f.obj t'.left))) := hx'
  have hpo := isPushout_appTop_of_isPullback hpb
  rw [ConcreteCategory.isIso_iff_bijective]
  refine Stacks.SheafOfModules.bijective_restrictionBaseChange_ranObj_of_isTerminal f
    (S := (structureSheaf B S hS (f ⋙ q) hp τ hτ).obj) (T := (structureSheaf B S hS q hq τ hτ).obj)
    (Stacks.SheafOfModules.structureMapPresheaf f
      (moduleDirectImageStructureMap B S hS (f ⋙ q) q hp hq f rfl τ hτ))
    F.val φ ht ht' ((BigFppfOver.toScheme B S hS).map (q.map t.hom)).appTop
    ((BigFppfOver.toScheme B S hS).map (q.map t'.hom)).appTop (fun s => ?_) (fun s => ?_) hpo
    ((ConcreteCategory.isIso_iff_bijective _).1 hF)
  · exact (congrArg (fun g => RingCat.Hom.hom g s)
      (scalarπ_moduleDirectImageStructureMap B S hS (f ⋙ q) q hp hq f rfl τ hτ (op y)
        (StructuredArrow.mk (Y := op t.left) t.hom.op))).trans rfl
  · exact (congrArg (fun g => RingCat.Hom.hom g s)
      (scalarπ_moduleDirectImageStructureMap B S hS (f ⋙ q) q hp hq f rfl τ hτ (op y')
        (StructuredArrow.mk (Y := op t'.left) t'.hom.op))).trans rfl

/-- **The direct image is cartesian between affines along a base-change-stable class of maps.**
Let `𝒳` and `𝒴` have terminal objects `x₀`, `y₀` over affine schemes (as when they are represented
by affine schemes), and let `P` be a class of morphisms of schemes stable under base change, such
as the flat or the étale morphisms. If `F` is cartesian over every arrow of `𝒳` between objects
over affine schemes lying over a morphism in `P`, then so is `f_*F` on `𝒴`. -/
theorem isIso_restrictionBaseChange_moduleDirectImage_of_isTerminal_of_isTerminal
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ))
    {x₀ : 𝒳} (hx₀ : IsTerminal x₀) {y₀ : 𝒴} (hy₀ : IsTerminal y₀)
    (hax₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₀)))
    (hay₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y₀)))
    (hF : ∀ ⦃x x' : 𝒳⦄ (ψ : x ⟶ x'), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x')) →
      P ((BigFppfOver.toScheme B S hS).map (p.map ψ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp τ hτ).obj) F.val ψ.op))
    ⦃y y' : 𝒴⦄ (φ : y ⟶ y') (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y)))
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y')))
    (hφ : P ((BigFppfOver.toScheme B S hS).map (q.map φ))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS q hq τ hτ).obj)
      ((moduleDirectImage.{u, v, w, v', w', u} B S hS p q hp hq f hf τ hτ).obj F).val φ.op) := by
  subst hf
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have haff : ∀ (z : 𝒴) (t : CostructuredArrow f z), IsTerminal t →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj (f.obj t.left))) :=
    fun _ _ ht hz => isAffine_obj_left_of_isTerminal_costructuredArrow B S hS (f ⋙ q) q hp hq f
      rfl hx₀ hy₀ hax₀ hay₀ ht hz
  obtain ⟨t, ⟨ht⟩⟩ := exists_isTerminal_costructuredArrow (f ⋙ q) q f hp hq rfl hx₀ hy₀ y
  obtain ⟨t', ⟨ht'⟩⟩ := exists_isTerminal_costructuredArrow (f ⋙ q) q f hp hq rfl hx₀ hy₀ y'
  refine isIso_restrictionBaseChange_moduleDirectImage_of_isTerminal B S hS (f ⋙ q) q hp hq f rfl
    τ hτ F φ ht ht' hy hy' (haff y' t' ht' hy') (hF _ (haff y t ht hy) (haff y' t' ht' hy') ?_)
  exact P.of_isPullback ((isPullback_map_of_isTerminal_costructuredArrow (f ⋙ q) q f hp hq rfl
    φ ht ht').map (BigFppfOver.toScheme B S hS)).flip hφ

end General

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack represented by an affine scheme `U` has a terminal object, lying over `U`:
the object corresponding to `id_U`. -/
theorem AlgebraicStacks.exists_isTerminal_of_isAffineRepresentable
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳) :
    ∃ x₀ : 𝒳.val.val.obj, Nonempty (IsTerminal x₀) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀)) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := h𝒳
  refine ⟨e.inv.functor.obj (Over.mk (𝟙 U)),
    ⟨(Over.mkIdTerminal (X := U)).isTerminalObj e.toEquivalence.inverse⟩, ?_⟩
  have hx : 𝒳.val.val.p.obj (e.inv.functor.obj (Over.mk (𝟙 U))) = U :=
    Functor.congr_obj e.inv.w (Over.mk (𝟙 U))
  rwa [hx]

/-- **Terminal arrows for a 1-morphism of algebraic stacks represented by affine schemes.** For
`f : 𝒳 ⟶ 𝒴` with `𝒳` and `𝒴` representable by affine schemes, every object `y` of `𝒴` has a
terminal arrow `(x₀, f x₀ ⟶ y)` in `CostructuredArrow f y` — the fibre product `y ×_𝒴 𝒳` — and
`x₀` lies over an affine scheme when `y` does. This is the input of the sections formula
`AlgebraicGeometry.Stack.stackModuleDirectImageSectionsIsoOfIsTerminal` (Stacks 075P) in the
affine case. -/
theorem AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineRepresentable
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒴) (y : 𝒴.val.val.obj) :
    ∃ t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y, Nonempty (IsTerminal t) ∧
      (IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y)) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj t.left))) := by
  obtain ⟨x₀, ⟨hx₀⟩, hax₀⟩ := AlgebraicStacks.exists_isTerminal_of_isAffineRepresentable B S hS h𝒳
  obtain ⟨y₀, ⟨hy₀⟩, hay₀⟩ := AlgebraicStacks.exists_isTerminal_of_isAffineRepresentable B S hS h𝒴
  have hp := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  obtain ⟨t, ⟨ht⟩⟩ := exists_isTerminal_costructuredArrow 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    hp hx₀ hy₀ y
  exact ⟨t, ⟨ht⟩, fun hy => isAffine_obj_left_of_isTerminal_costructuredArrow B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) hp hx₀ hy₀
    hax₀ hay₀ ht hy⟩

/-- **The direct image along a 1-morphism of algebraic stacks represented by affine schemes is
cartesian between affines along a base-change-stable class of maps.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks representable by affine schemes, `τ` a topology, `P` a class of
morphisms of schemes stable under base change (for instance the flat, or the étale, morphisms)
and `F` a module on `𝒳_τ` which is cartesian over every arrow between objects over affine
schemes lying over a morphism in `P`. Then `f_*F` is cartesian over every such arrow of `𝒴`:
`Γ(y) ⊗_{Γ(y')} (f_*F)(y') ⟶ (f_*F)(y)` is bijective. -/
theorem isIso_restrictionBaseChange_stackModuleDirectImage
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (τ : SiteKind)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒴)
    (F : StackModules B S hS τ 𝒳)
    (hF : ∀ ⦃x x' : 𝒳.val.val.obj⦄ (ψ : x ⟶ x'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x')) →
      P ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (B.baseTopology τ)
          (B.baseTopology_le_topology τ)).obj) F.val ψ.op))
    ⦃y y' : 𝒴.val.val.obj⦄ (φ : y ⟶ y')
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y)))
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y')))
    (hφ : P ((BigFppfOver.toScheme B S hS).map (𝒴.val.val.p.map φ))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj)
      ((stackModuleDirectImage B S hS f τ).obj F).val φ.op) := by
  obtain ⟨x₀, ⟨hx₀⟩, hax₀⟩ := AlgebraicStacks.exists_isTerminal_of_isAffineRepresentable B S hS h𝒳
  obtain ⟨y₀, ⟨hy₀⟩, hay₀⟩ := AlgebraicStacks.exists_isTerminal_of_isAffineRepresentable B S hS h𝒴
  have := isIso_restrictionBaseChange_moduleDirectImage_of_isTerminal_of_isTerminal B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (B.baseTopology τ) (B.baseTopology_le_topology τ) P F hx₀ hy₀ hax₀ hay₀ hF φ hy hy' hφ
  exact @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _ _ _ _
    ((SheafOfModules.forget _).mapIso
      ((stackModuleDirectImageIsoModuleDirectImage B S hS f τ).app F).symm) _ _ φ.op this

end AlgebraicGeometry.Stack
