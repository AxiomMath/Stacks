module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePoint
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentedPresheaf

/-!
# Terminal arrows into an object lying over an affine scheme, along an affine 1-morphism

Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks over `S` (Stacks 0CHQ) and `y` an
object of `𝒴` lying over an affine scheme `V`.  The base change of `f` along the scheme-valued
point `(Sch/V) ⟶ 𝒴` of `y` is an algebraic space affine over `V`, hence represented by an affine
scheme `W`, and the object `x₀` of `𝒳` corresponding to `id_W` gives a terminal object
`(x₀, f x₀ ⟶ y)` of `CostructuredArrow f y`, with `x₀` lying over the affine scheme `W`
(`CategoryTheory.TwoFibreProductOver.TerminalArrow.isTerminalRepresentingArrow`).

This is the input the sections formula `Γ(y, f_* M) = Γ(x₀, M)` of
`AlgebraicGeometry.Stack.fppfModulesPushforwardSectionsIsoOfIsTerminal` needs in Stacks 0GQI.

As a consequence the direct image along an affine 1-morphism is cartesian between affines along
any base-change-stable class of morphisms along which its argument is
(`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_stackModuleDirectImage_of_isAffineHom`):
the arrow between the terminal arrows over `y ⟶ y'` lies over the base change of `y ⟶ y'`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineHom`.
* `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_moduleDirectImage_of_forall_isTerminal`
  and `AlgebraicGeometry.Stack.isIso_restrictionBaseChange_stackModuleDirectImage_of_isAffineHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w v' w'

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine 1-morphism has terminal arrows into objects lying over affine schemes, from
objects lying over affine schemes.**  For `f : 𝒳 ⟶ 𝒴` affine and `y` lying over an affine
scheme, `CostructuredArrow f y` has a terminal object `(x₀, f x₀ ⟶ y)` with `x₀` lying over an
affine scheme: the base change of `f` along `y` is represented by an affine scheme. -/
theorem exists_isTerminal_costructuredArrow_of_isAffineHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsAffineHom B S hS f) (y : 𝒴.val.val.obj)
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y))) :
    ∃ t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y,
      Nonempty (IsTerminal t) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj t.left)) := by
  set U := 𝒴.val.val.p.obj y
  obtain ⟨y', hy', ξ, -⟩ := StacksRepresentableCFG.exists_pointOverMap_of_obj 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids U y rfl
  obtain ⟨F, hF, ⟨e⟩⟩ := hf.1 U y' hy'
  have haff : Space.IsAffineHom B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.affineMorphismProperty B S hS) U F hF).1
      (hf.2 U y' hy' F hF ⟨e⟩)
  obtain ⟨W, pW, qW, hpb⟩ := haff ⟨U, hy⟩ (𝟙 (yoneda.obj U))
  have iW : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ≅
      (OverShriek.relocalizePresheafFunctor U.hom).obj F :=
    hpb.isoIsPullback _ _ IsPullback.of_id_fst
  obtain ⟨j⟩ := OverShriek.nonempty_iso_yoneda_of_relocalize U.hom F iW.symm
  let e' := e.trans (PresheafOfCategories.equivalenceOverOfIso j)
  let t₀ := TwoFibreProductOver.TerminalArrow.toCostructuredArrow (𝒞 := B.Schemes)
      (X := B.obj hS) (A := U.left) U.hom 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) y'
      (TwoFibreProductOver.TerminalArrow.representingObject U.hom 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) y' e')
  have ht₀ : IsTerminal t₀ := isTerminalRepresentingArrowStack B S hS f U y' hy' e'
  refine ⟨(CostructuredArrow.mapIso ξ).functor.obj t₀,
    ⟨ht₀.isTerminalObj (CostructuredArrow.mapIso ξ).functor⟩, ?_⟩
  change IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj
    (TwoFibreProductOver.TerminalArrow.representingObject U.hom 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) y' e').y))
  rw [TwoFibreProductOver.TerminalArrow.p𝒳_obj_representingObject_y U.hom 𝒳.val.val.p
    𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) y' e']
  exact W.property

end AlgebraicGeometry.Stack.AlgebraicStacks

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

/-- **The direct image is cartesian between affines along a base-change-stable class of maps,
given terminal arrows over affine objects.**  Suppose every object `y` of `𝒴` over an affine
scheme has a terminal arrow `(x₀, f x₀ ⟶ y)` with `x₀` over an affine scheme, and let `P` be a
class of morphisms of schemes stable under base change.  If `F` is cartesian over every arrow of
`𝒳` between objects over affine schemes lying over a morphism in `P`, so is `f_*F` on `𝒴`. -/
theorem isIso_restrictionBaseChange_moduleDirectImage_of_forall_isTerminal
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ))
    (hterm : ∀ y : 𝒴, IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y)) →
      ∃ t : CostructuredArrow f y, Nonempty (IsTerminal t) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj t.left)))
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
  obtain ⟨t, ⟨ht⟩, hat⟩ := hterm y hy
  obtain ⟨t', ⟨ht'⟩, hat'⟩ := hterm y' hy'
  exact isIso_restrictionBaseChange_moduleDirectImage_of_isTerminal B S hS (f ⋙ q) q hp hq f rfl
    τ hτ F φ ht ht' hy hy' hat' (hF _ hat hat' (P.of_isPullback
      ((isPullback_map_of_isTerminal_costructuredArrow (f ⋙ q) q f hp hq rfl φ ht ht').map
        (BigFppfOver.toScheme B S hS)).flip hφ))

end General

/-- **The direct image along an affine 1-morphism of algebraic stacks is cartesian between
affines along a base-change-stable class of maps.**  Let `f : 𝒳 ⟶ 𝒴` be affine, `P` a class of
morphisms of schemes stable under base change (the flat, or the étale, morphisms) and `F` a
module on `𝒳_τ` cartesian over every arrow between objects over affine schemes lying over a
morphism in `P`.  Then `f_*F` is cartesian over every such arrow of `𝒴`. -/
theorem isIso_restrictionBaseChange_stackModuleDirectImage_of_isAffineHom
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (τ : SiteKind)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsAffineHom B S hS f) (F : StackModules B S hS τ 𝒳)
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
  have := isIso_restrictionBaseChange_moduleDirectImage_of_forall_isTerminal B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (B.baseTopology τ) (B.baseTopology_le_topology τ) P F
    (AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineHom B S hS f hf) hF φ hy hy' hφ
  exact @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _ _ _ _
    ((SheafOfModules.forget _).mapIso
      ((stackModuleDirectImageIsoModuleDirectImage B S hS f τ).app F).symm) _ _ φ.op this

end AlgebraicGeometry.Stack
