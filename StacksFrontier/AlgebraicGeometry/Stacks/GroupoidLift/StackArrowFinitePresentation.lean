module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackArrowChart

/-!
# The space of arrows of the groupoid of a chart is locally of finite presentation

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks whose relative diagonal is locally of finite
presentation, the presheaf of vertical morphisms over the comparison isomorphism of a
scheme-valued point `(x, x', α)` of `𝒳 ×_𝒴 𝒳` over `U` is locally of finite presentation over `U`
(`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_relVertHomPresheaf`): it is the base change
of the diagonal along that point.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_relVertHomPresheaf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Stack

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section RelDiag

open CategoryTheory.TwoFibreProductOver.DiagonalFibre
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

/-- Precomposing with an isomorphism does not change local finite presentation of a morphism of
presheaves. -/
private theorem isLocallyOfFinitePresentation_iso_comp_iff
    {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F') (g : F' ⟶ G) :
    Space.IsLocallyOfFinitePresentation B S hS (e.hom ≫ g) ↔
      Space.IsLocallyOfFinitePresentation B S hS g :=
  have : MorphismProperty.RespectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS g) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _
  MorphismProperty.cancel_left_of_respectsIso _ e.hom g

/-- For an algebraic space `G` over `V`, the structure morphism of `G` is locally of finite
presentation over the base iff the corresponding morphism of algebraic spaces over `S` is. -/
private theorem spaceProperty_algebraicSpaceMap_iff_terminal
    (V : BigFppfOver B S hS) (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G) :
    spaceProperty B S hS (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g :
          MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
        (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)) ↔
      Space.IsLocallyOfFinitePresentation B V.left.1 V.left.2 (terminal.from G) := by
  have hri : (spaceProperty B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g :
        MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (prop_algebraicSpaceMap_iff B S hS _ V G hG).trans
    ((Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B V.left.1 S V.left.2 hS V.hom
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) G).trans ?_)
  exact ⟨Space.holdsOnEveryEtaleChart_of_isTerminal B V.left.1 V.left.2
      (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj V.left.2))))
      terminalIsTerminal _ _,
    Space.holdsOnEveryEtaleChart_of_isTerminal B V.left.1 V.left.2 terminalIsTerminal
      (Over.mkIdTerminal.isTerminalObj yoneda _) _ _⟩

/-- **The base change of a locally finitely presented relative diagonal to a scheme-valued point.**
If the relative diagonal of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks is locally of finite
presentation, then for a point `Y = (x, x', α)` of `𝒳 ×_{f, 𝒴, f} 𝒳` over `U` the presheaf of
vertical morphisms `x ⟶ x'` lying over `α` is locally of finite presentation over `U`. -/
theorem isLocallyOfFinitePresentation_relVertHomPresheaf
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hΔ : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.relativeDiagonal B S hS f))
    (U : BigFppfOver B S hS)
    (Y : BigFppfOver B U.left.1 U.left.2 ⥤
      TwoFibreProductOver 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
        f.hom.hom.toFunctor)
    (hY : Y ⋙ RelProdP 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor = Over.map U.hom) :
    Space.IsLocallyOfFinitePresentation B U.left.1 U.left.2
      (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
        hY f.hom.hom.w)) := by
  let Plfp : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g
  have hP := Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  have hrep := isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hsome := (hasPropertyOnEverySmoothDiagram_iff_some.{u, t} B S hS Plfp hP 𝒳.2
    (AlgebraicStacks.twoFibreProduct B S hS f f).2 _).1 hΔ
  have hrel := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, t, u + 1} B S hS Plfp hP 𝒳.2
    (AlgebraicStacks.twoFibreProduct B S hS f f).2 _ hrep).1 hsome
  obtain ⟨G, hG, ⟨eG⟩⟩ := isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack.{u, u, u + 1}
    B S hS 𝒳.val 𝒴.val f.hom 𝒳.2 𝒴.2 U Y hY
  have hE := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hY f.hom.hom.w G).mpr ⟨eG⟩
  have h := hrel U Y hY G hG hE
  have h3 := (spaceProperty_algebraicSpaceMap_iff_terminal B S hS U G hG).mp h
  have hiso : relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hY
      f.hom.hom.w ≅ G :=
    ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso eG
  rw [show terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids hY f.hom.hom.w) = hiso.hom ≫ terminal.from G from
    terminal.hom_ext _ _]
  exact (isLocallyOfFinitePresentation_iso_comp_iff B U.left.1 U.left.2 hiso _).mpr h3

/-- Isomorphic presheaves have locally finitely presented structural morphisms together. -/
theorem isLocallyOfFinitePresentation_terminal_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (h : Space.IsLocallyOfFinitePresentation B S hS (terminal.from F)) :
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from G) := by
  rw [show terminal.from F = e.hom ≫ terminal.from G from terminal.hom_ext _ _] at h
  exact (isLocallyOfFinitePresentation_iso_comp_iff B S hS e _).mp h

/-! ### Points of the relative self-product over a scheme -/

section RelPair

variable {B S hS} {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {Z : BigFppfOver B S hS} (F : 𝒳.val.obj ⥤ (schemeFibredCategory B S hS Z).val.obj)
  (hF : F ⋙ (schemeFibredCategory B S hS Z).val.p = 𝒳.val.p)

include hF in
/-- The underlying object of `F.obj x` is the image of `x` in the base. -/
theorem relPair_left_eq (x : 𝒳.val.obj) : (F.obj x).left = 𝒳.val.p.obj x :=
  Functor.congr_obj hF x

/-- **Two objects over `V` with the same image in `Z`.** -/
def SameImage {V : BigFppfOver B S hS} (x₀ x₁ : 𝒳.val.p.Fiber V) : Prop :=
  eqToHom ((relPair_left_eq F hF x₀.1).trans x₀.2).symm ≫ (F.obj x₀.1).hom =
    eqToHom ((relPair_left_eq F hF x₁.1).trans x₁.2).symm ≫ (F.obj x₁.1).hom

/-- For a morphism `c : y ⟶ x` lying over `g : W ⟶ V`, the structure morphism of `F.obj y` to `Z`
factors as `g` followed by the structure morphism of `F.obj x`. -/
theorem relPair_hom_eq {y x : 𝒳.val.obj} {W V : BigFppfOver B S hS} (g : W ⟶ V) (c : y ⟶ x)
    [𝒳.val.p.IsHomLift g c] (hy : 𝒳.val.p.obj y = W) (hx : 𝒳.val.p.obj x = V) :
    eqToHom ((relPair_left_eq F hF y).trans hy).symm ≫ (F.obj y).hom =
      g ≫ eqToHom ((relPair_left_eq F hF x).trans hx).symm ≫ (F.obj x).hom := by
  have hw := Over.w (F.map c)
  have e : (F.map c).left = eqToHom (relPair_left_eq F hF y) ≫ 𝒳.val.p.map c ≫
      eqToHom (relPair_left_eq F hF x).symm := Functor.congr_hom hF c
  have e' := IsHomLift.fac' 𝒳.val.p g c
  rw [← hw, e, e']
  simp

variable [𝒳.val.p.IsFibered] {V : BigFppfOver B S hS} (x₀ x₁ : 𝒳.val.p.Fiber V)

/-- The chosen-pullback functor of `x` on the big fppf site of `V`. -/
noncomputable abbrev relPairCmp (x : 𝒳.val.p.Fiber V) :
    BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj :=
  Over.iteratedSliceBackward V ⋙ Functor.pullbackSliceFunctor 𝒳.val.p x

/-- The chosen-pullback functor of `x` lies over the forgetful functor `Over.map V.hom`. -/
theorem relPairCmp_comp (x : 𝒳.val.p.Fiber V) :
    relPairCmp x ⋙ 𝒳.val.p = Over.map V.hom :=
  Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p V x

/-- The structure morphism to `Z` of the image of the chosen pullback of `x` along `a` is the
composite of `a` with the structure morphism of the image of `x`. -/
theorem relPair_hom_eq_obj (x : 𝒳.val.p.Fiber V) (a : BigFppfOver B V.left.1 V.left.2) :
    eqToHom ((relPair_left_eq F hF ((relPairCmp x).obj a)).trans
        (Functor.congr_obj (relPairCmp_comp x) a)).symm ≫ (F.obj ((relPairCmp x).obj a)).hom =
      ((Over.iteratedSliceBackward V).obj a).hom ≫
        eqToHom ((relPair_left_eq F hF x.1).trans x.2).symm ≫ (F.obj x.1).hom := by
  have : 𝒳.val.p.IsHomLift ((Over.iteratedSliceBackward V).obj a).hom
      (Functor.IsPreFibered.pullbackMap x.2 ((Over.iteratedSliceBackward V).obj a).hom) :=
    inferInstance
  exact relPair_hom_eq F hF ((Over.iteratedSliceBackward V).obj a).hom
    (Functor.IsPreFibered.pullbackMap x.2 ((Over.iteratedSliceBackward V).obj a).hom)
    (Functor.IsPreFibered.pullbackObj_proj x.2 _) x.2

variable {x₀ x₁}

/-- The comparison isomorphism at `a` of the images of the two chosen pullbacks. -/
noncomputable def relPairIso (hα : SameImage F hF x₀ x₁) (a : BigFppfOver B V.left.1 V.left.2) :
    F.obj ((relPairCmp x₀).obj a) ≅ F.obj ((relPairCmp x₁).obj a) :=
  Over.isoMk (eqToIso (((relPair_left_eq F hF _).trans
      (Functor.congr_obj (relPairCmp_comp x₀) a)).trans
    ((relPair_left_eq F hF _).trans (Functor.congr_obj (relPairCmp_comp x₁) a)).symm)) (by
    have h0 := relPair_hom_eq_obj F hF x₀ a
    have h1 := relPair_hom_eq_obj F hF x₁ a
    rw [hα, ← h1] at h0
    rw [← cancel_epi (eqToHom ((relPair_left_eq F hF ((relPairCmp x₀).obj a)).trans
      (Functor.congr_obj (relPairCmp_comp x₀) a)).symm), h0]
    simp)

/-- The underlying morphism of `relPairIso` is an `eqToHom`. -/
theorem relPairIso_hom_left (hα : SameImage F hF x₀ x₁) (a : BigFppfOver B V.left.1 V.left.2) :
    (relPairIso F hF hα a).hom.left = eqToHom (((relPair_left_eq F hF _).trans
      (Functor.congr_obj (relPairCmp_comp x₀) a)).trans
    ((relPair_left_eq F hF _).trans (Functor.congr_obj (relPairCmp_comp x₁) a)).symm) := rfl

/-- **The point `(x₀, x₁, α)` of the relative self-product over the big fppf site of `V`.** -/
noncomputable def relPair (hα : SameImage F hF x₀ x₁) :
    BigFppfOver B V.left.1 V.left.2 ⥤ RelProd 𝒳.val.p (schemeFibredCategory B S hS Z).val.p F where
  obj a :=
    { base := (Over.map V.hom).obj a
      x := (relPairCmp x₀).obj a
      y := (relPairCmp x₁).obj a
      hx := Functor.congr_obj (relPairCmp_comp x₀) a
      hy := Functor.congr_obj (relPairCmp_comp x₁) a
      iso := relPairIso F hF hα a
      vertical := by
        refine IsHomLift.of_fac' _ _ _
          ((relPair_left_eq F hF _).trans (Functor.congr_obj (relPairCmp_comp x₀) a))
          ((relPair_left_eq F hF _).trans (Functor.congr_obj (relPairCmp_comp x₁) a)) ?_
        change (relPairIso F hF hα a).hom.left = _
        rw [relPairIso_hom_left]
        simp only [Category.id_comp]
        exact (eqToHom_trans _ _).symm }
  map {a b} g :=
    { hbase := (Over.map V.hom).map g
      a := (relPairCmp x₀).map g
      b := (relPairCmp x₁).map g
      ha := VertHom.isHomLift_map (relPairCmp_comp x₀) g
      hb := VertHom.isHomLift_map (relPairCmp_comp x₁) g
      w := by
        refine Over.OverMorphism.ext ?_
        have e0 : (F.map ((relPairCmp x₀).map g)).left = eqToHom (relPair_left_eq F hF _) ≫
            𝒳.val.p.map ((relPairCmp x₀).map g) ≫ eqToHom (relPair_left_eq F hF _).symm :=
          Functor.congr_hom hF _
        have e1 : (F.map ((relPairCmp x₁).map g)).left = eqToHom (relPair_left_eq F hF _) ≫
            𝒳.val.p.map ((relPairCmp x₁).map g) ≫ eqToHom (relPair_left_eq F hF _).symm :=
          Functor.congr_hom hF _
        have g0 : 𝒳.val.p.map ((relPairCmp x₀).map g) = eqToHom _ ≫ (Over.map V.hom).map g ≫
            eqToHom _ := Functor.congr_hom (relPairCmp_comp x₀) g
        have g1 : 𝒳.val.p.map ((relPairCmp x₁).map g) = eqToHom _ ≫ (Over.map V.hom).map g ≫
            eqToHom _ := Functor.congr_hom (relPairCmp_comp x₁) g
        change (F.map ((relPairCmp x₀).map g)).left ≫ (relPairIso F hF hα b).hom.left =
          (relPairIso F hF hα a).hom.left ≫ (F.map ((relPairCmp x₁).map g)).left
        rw [e0, e1, g0, g1, relPairIso_hom_left, relPairIso_hom_left]
        simp }
  map_id a := TwoFibreProductOver.Hom.ext' ((relPairCmp x₀).map_id a) ((relPairCmp x₁).map_id a)
  map_comp f g := TwoFibreProductOver.Hom.ext' ((relPairCmp x₀).map_comp f g)
    ((relPairCmp x₁).map_comp f g)

/-- The point `relPair F hF hα` lies over `Over.map V.hom`. -/
theorem relPair_comp (hα : SameImage F hF x₀ x₁) :
    relPair F hF hα ⋙ RelProdP 𝒳.val.p (schemeFibredCategory B S hS Z).val.p F =
      Over.map V.hom :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by rfl)

/-- Over a scheme, every vertical morphism between the two components lies over the comparison
isomorphism, so the presheaf of vertical morphisms over `α` is the isomorphism presheaf of
`x₀` and `x₁`. -/
noncomputable def relPairRelVertHomIso (hα : SameImage F hF x₀ x₁) :
    relVertHomPresheaf (schemeFibredCategory B S hS Z).isFiberedInGroupoids
        𝒳.isFiberedInGroupoids (relPair_comp F hF hα) hF ≅
      (Over.iteratedSliceBackward V).op ⋙ 𝒳.val.p.isomPresheaf x₀ x₁ :=
  (NatIso.ofComponents (fun a => Equiv.toIso
      { toFun := fun (m : RelVertHom _ _ _) => m.1
        invFun := fun m => ⟨m, by
          have hm := m.2
          refine Over.OverMorphism.ext ?_
          have e : (F.map m.1).left = eqToHom (relPair_left_eq F hF _) ≫ 𝒳.val.p.map m.1 ≫
              eqToHom (relPair_left_eq F hF _).symm := Functor.congr_hom hF m.1
          have e2 := IsHomLift.fac' 𝒳.val.p (𝟙 ((Over.map V.hom).obj a.unop)) m.1
          refine e.trans ?_
          rw [show ((relPair F hF hα).obj a.unop).iso = relPairIso F hF hα a.unop from rfl,
            relPairIso_hom_left]
          simp [e2]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl) : relVertHomPresheaf (schemeFibredCategory B S hS Z).isFiberedInGroupoids
        𝒳.isFiberedInGroupoids (relPair_comp F hF hα) hF ≅
      VertHom.presheaf 𝒳.isFiberedInGroupoids
        (Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p V x₀)
        (Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p V x₁)) ≪≫
    Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.p V x₀ x₁ 𝒳.isFiberedInGroupoids

end RelPair

end RelDiag

/-! ### The space of arrows -/

namespace GroupoidLift

open AlgebraicGeometry.Space.ChartDescent

variable {B S hS} {T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- A category fibred in groupoids is fibred. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- **The space of arrows of the groupoid of a chart is locally of finite presentation over
`Spec (P ⊗ P)`, from the relative diagonal.** Let `f : 𝒳 ⟶ Z` be a 1-morphism of algebraic stacks
to a scheme whose relative diagonal is locally of finite presentation, and suppose the two objects
`ξ v₀`, `ξ vₗ` over `Spec (P ⊗ P)` have the same image in `Z`. The space of arrows is the base
change of that diagonal along the point `(ξ v₀, ξ vₗ)`, so it is locally of finite presentation
over `Spec (P ⊗ P)`. -/
theorem isLocallyOfFinitePresentation_arrSpace_of_diagonal
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val) {Z : BigFppfOver B S hS}
    (f : (show AlgebraicStacks.{u, t} B S hS from ⟨𝒳, h𝒳⟩) ⟶
      (show AlgebraicStacks.{u, t} B S hS from
        ⟨schemeFibredCategory B S hS Z, isAlgebraicStack_schemeFibredCategory B S hS Z⟩))
    (hΔ : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.relativeDiagonal B S hS f))
    (hα : SameImage f.hom.hom.toFunctor f.hom.hom.w (pairObj₀ a ι) (pairObj₁ a ι)) :
    Space.IsLocallyOfFinitePresentation B S hS (OverShriek.presheafToYoneda (pairIsom a ι)) := by
  set V := specOver (pairAlg P)
  have hL := isLocallyOfFinitePresentation_relVertHomPresheaf B S hS f hΔ V
    (relPair f.hom.hom.toFunctor f.hom.hom.w hα) (relPair_comp f.hom.hom.toFunctor f.hom.hom.w hα)
  let G' := (Over.iteratedSliceBackward V).op ⋙ pairIsom a ι
  let c : _ ≅ G' := relPairRelVertHomIso f.hom.hom.toFunctor f.hom.hom.w hα
  have hG' : Space.IsLocallyOfFinitePresentation B V.left.1 V.left.2 (terminal.from G') :=
    isLocallyOfFinitePresentation_terminal_of_iso B V.left.1 V.left.2 c hL
  have hI := (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp
    (SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳 h𝒳)
  obtain ⟨F, hF, ⟨e⟩⟩ := hI V (pairObj₀ a ι) (pairObj₁ a ι)
  let e' : F ≅ G' :=
    ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u, u}).whiskeringRight _).preimageIso e
  have hG'alg : IsAlgebraicSpace B V.left.1 V.left.2 G' :=
    isAlgebraicSpace_of_iso B V.left.1 V.left.2 e'.symm hF
  have h3 := (spaceProperty_algebraicSpaceMap_iff_terminal B S hS V G' hG'alg).mpr hG'
  let E := (Over.iteratedSliceEquiv V).op.congrLeft (E := Type u)
  let e'' : E.inverse.obj G' ≅ pairIsom a ι := (E.unitIso.app _).symm
  have hcomp : OverShriek.presheafToYoneda (E.inverse.obj G') =
      (OverShriek.presheafFunctor.map e''.hom) ≫ OverShriek.presheafToYoneda (pairIsom a ι) := by
    ext W x
    rfl
  have h4 : Space.IsLocallyOfFinitePresentation B S hS
      (OverShriek.presheafToYoneda (E.inverse.obj G')) := h3
  rw [hcomp] at h4
  exact (isLocallyOfFinitePresentation_iso_comp_iff B S hS
    (OverShriek.presheafFunctor.mapIso e'') _).mp h4

/-- **The space of arrows of the groupoid of a chart is locally of finite presentation over
`Spec (P ⊗ P)`**, when `𝒳` is locally of finite presentation over a scheme `Z` and the two objects
`ξ v₀`, `ξ vₗ` over `Spec (P ⊗ P)` have the same image in `Z`: the relative diagonal of `𝒳 ⟶ Z` is
then locally of finite presentation (Stacks 0CMG). -/
theorem isLocallyOfFinitePresentation_arrSpace (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    {Z : BigFppfOver B S hS} (f : 𝒳 ⟶ schemeFibredCategory B S hS Z)
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hα : SameImage f.hom.toFunctor f.hom.w (pairObj₀ a ι) (pairObj₁ a ι)) :
    Space.IsLocallyOfFinitePresentation B S hS (OverShriek.presheafToYoneda (pairIsom a ι)) := by
  let 𝒳' : AlgebraicStacks.{u, t} B S hS := ⟨𝒳, h𝒳⟩
  let 𝒵 : AlgebraicStacks.{u, t} B S hS :=
    ⟨schemeFibredCategory B S hS Z, isAlgebraicStack_schemeFibredCategory B S hS Z⟩
  let f' : 𝒳' ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom f
  have hlft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f' :=
    fun U V hU hV a b h η h1 h2 h3 =>
      Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (hf U V hU hV a b h η h1 h2 h3)
  exact isLocallyOfFinitePresentation_arrSpace_of_diagonal a ι h𝒳 f'
    (AlgebraicStacks.isLocallyOfFinitePresentation_relativeDiagonal B S hS f' hlft) hα

end StackChart

open StackChart

/-- The sections of an affine scheme étale over the space of arrows form a finitely presented
algebra over `A'`, as soon as the space of arrows is locally of finite presentation over
`Spec (P ⊗ P)`. -/
theorem finitePresentation_sectionsAlg_of_isLocallyOfFinitePresentation
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS
      (OverShriek.presheafToYoneda (pairIsom a ι)))
    [Algebra.FinitePresentation (ringOf B S hS T') P.obj]
    {U₁ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)]
    (ξ : (arrSpace a ι).obj (op U₁))
    (hξ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yonedaEquiv.symm ξ)) :
    Algebra.FinitePresentation (ringOf B S hS T')
      (sectionsAlg U₁ ((arrSpaceToBase a ι).app (op U₁) ξ)).obj := by
  set j₁ := (arrSpaceToBase a ι).app (op U₁) ξ
  set ψ : U₁ ⟶ specOver (pairAlg P) := ξ.1
  have hsq : yoneda.map ψ ≫ 𝟙 _ = yonedaEquiv.symm ξ ≫
      OverShriek.presheafToYoneda (pairIsom a ι) := by
    ext W g
    rfl
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj (specOver (pairAlg P)))) := by
    rw [← yoneda.map_id]
    exact (Space.presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mpr
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have hψ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map ψ) :=
    hlfp U₁ (specOver (pairAlg P)) (yonedaEquiv.symm ξ) (𝟙 _) ψ hξ hid hsq
  have hPP : Algebra.FinitePresentation (ringOf B S hS T') (pairAlg P).obj :=
    Algebra.FinitePresentation.trans (ringOf B S hS T') P.obj (P.obj ⊗[ringOf B S hS T'] P.obj)
  have hbase : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (specOverToBase (pairAlg P))) := by
    show LocallyOfFinitePresentation (specToBase (pairAlg P))
    rw [specToBase]
    have : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') (pairAlg P).obj))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr hPP)
    infer_instance
  have hj₁ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map j₁) := by
    rw [show j₁ = ψ ≫ specOverToBase (pairAlg P) from rfl, Functor.map_comp]
    infer_instance
  exact RingHom.finitePresentation_algebraMap.mp (HasRingHomProperty.iff_of_isAffine.mp hj₁)

/-- The sections of an affine scheme étale over the space of arrows form a finitely presented
algebra over `A'`. -/
theorem finitePresentation_sectionsAlg (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    {Z : BigFppfOver B S hS} (f : 𝒳 ⟶ schemeFibredCategory B S hS Z)
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hα : SameImage f.hom.toFunctor f.hom.w (pairObj₀ a ι) (pairObj₁ a ι))
    [Algebra.FinitePresentation (ringOf B S hS T') P.obj]
    {U₁ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)]
    (ξ : (arrSpace a ι).obj (op U₁))
    (hξ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yonedaEquiv.symm ξ)) :
    Algebra.FinitePresentation (ringOf B S hS T')
      (sectionsAlg U₁ ((arrSpaceToBase a ι).app (op U₁) ξ)).obj :=
  finitePresentation_sectionsAlg_of_isLocallyOfFinitePresentation a ι
    (isLocallyOfFinitePresentation_arrSpace a ι h𝒳 f hf hα) ξ hξ

private theorem exists_arrowChart_finitePresentation_aux (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS
      (OverShriek.presheafToYoneda (pairIsom a ι)))
    [Algebra.FinitePresentation (ringOf B S hS T') P.obj]
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    ∃ (C₁ : SmallAlg (ringOf B S hS T') B.cutoff) (f : C ⟶ C₁)
      (_ : Surjective ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (_ : Etale ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (Q : SmallAlg (ringOf B S hS T') B.cutoff)
      (_ : Algebra.FinitePresentation (ringOf B S hS T') Q.obj)
      (b : Chart (stackArr a ι) Q.obj)
      (_ : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q.obj)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).src = v.comp sV)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).tgt = v.comp tV)
      (ε : Q.obj →ₐ[ringOf B S hS T'] C₁.obj), b.app C₁ ε = Arr.idt (f.hom.hom.comp w) := by
  set X := arrSpace a ι
  set π := arrSpaceToBase a ι
  have hX := isAlgebraicSpace_arrSpace a ι h𝒳
  obtain ⟨r₀, hr₀⟩ := relToArr_surjective a ι (Arr.idt (a := a) (ι := ι) w)
  obtain ⟨U, aU, haS, haE⟩ := hX.exists_atlas
  set g : yoneda.obj (specOver C) ⟶ X := yonedaEquiv.symm r₀.1
  set hrep := haS.rep
  set q : hrep.pullback g ⟶ specOver C := hrep.snd g
  set k : hrep.pullback g ⟶ U := hrep.fst' g
  have hqs : Surjective ((BigFppfOver.toScheme B S hS).map q) := haS.property_snd g
  have hqe : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    haE.2 g (hrep.fst g) q (hrep.isPullback g)
  obtain ⟨c, U₁, r, s, m, hc, hU₁, hrs, hre, hse, hms⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement_factor inferInstance q hqs hqe k
  set ξ : X.obj (op U₁) := aU.app (op U₁) s
  have hξ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yonedaEquiv.symm ξ) := by
    rw [yonedaEquiv_symm_app_eq]
    exact MorphismProperty.comp_mem _ _ _
      ((Space.presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mpr hse) haE
  set j₁ : U₁ ⟶ T' := π.app (op U₁) ξ
  set Q := sectionsAlg U₁ j₁
  set qQ := sectionsPoint π ξ
  have hqQ := formallyEtale_sectionsPoint π ξ hξ
  set jc : c ⟶ T' := r ≫ q ≫ specOverToBase C
  have hk : aU.app _ k = X.map q.op r₀.1 := by
    have h := Space.app_tautological_section_representing B S hS (hrep.isPullback g)
    have hf : (hrep.fst g).app (op (hrep.pullback g)) (𝟙 _) = k := by
      rw [← hrep.map_fst']
      exact Category.id_comp (obj := BigFppfOver B S hS) k
    rwa [hf] at h
  have hm : X.map m.op ξ = X.map (r ≫ q).op r₀.1 := by
    have h1 : X.map m.op ξ = aU.app _ (m ≫ s) := (NatTrans.naturality_apply aU m.op s).symm
    rw [h1, hms]
    have h2 : aU.app _ (r ≫ k) = X.map r.op (aU.app _ k) := NatTrans.naturality_apply aU r.op k
    rw [h2, hk, ← Functor.map_comp_apply, ← op_comp]
  have hmj : m ≫ j₁ = jc := by
    have h := congrArg (π.app (op c)) hm
    rw [app_map_eq, app_map_eq, r₀.2] at h
    exact h.trans (Category.assoc _ _ _)
  have hfpQ : Algebra.FinitePresentation (ringOf B S hS T') Q.obj :=
    finitePresentation_sectionsAlg_of_isLocallyOfFinitePresentation a ι hlfp ξ hξ
  set C₁ := sectionsAlg c jc
  obtain ⟨f₁, hf₁⟩ := exists_specOverMap (T' := T') (C := C) (D := C₁)
    (sectionsHom c jc ≫ r ≫ q) (by
      rw [Category.assoc, Category.assoc]
      exact sectionsHom_comp c jc)
  refine ⟨C₁, f₁, ?_, ?_, Q, hfpQ, arrChart a ι Q qQ, arrChart_isFormallyEtale a ι Q qQ hqQ, _, _,
    arrChart_src a ι Q qQ, arrChart_tgt a ι Q qQ, (sectionsMap m hmj).hom.hom, ?_⟩
  · rw [hf₁, Functor.map_comp]
    infer_instance
  · rw [hf₁, Functor.map_comp]
    infer_instance
  · rw [arrChart_app, ← relToArr_map]
    have hpt : (relPoints T' π).map (SmallAlg.homMk (sectionsMap m hmj).hom.hom) qQ =
        (relPoints T' π).map f₁ r₀ := by
      apply Subtype.ext
      show X.map (specOverMap (sectionsMap m hmj)).op (X.map (sectionsHom U₁ j₁).op ξ) =
        X.map (specOverMap f₁).op r₀.1
      rw [← Functor.map_comp_apply, ← op_comp, specOverMap_sectionsMap, op_comp,
        Functor.map_comp_apply, hm, ← Functor.map_comp_apply, ← op_comp, hf₁]
    rw [hpt, relToArr_map, hr₀]
    exact Arr.map_idt f₁ w

/-- **A formally étale chart of the arrows near an identity, by a finitely presented algebra,
from the finiteness of the space of arrows.**
`AlgebraicGeometry.Stack.GroupoidLift.exists_arrowChart`, with the chart algebra `Q` of finite
presentation over `A'`, when the space of arrows is locally of finite presentation over
`Spec (P ⊗ P)` and `P` is of finite presentation over `A'`. -/
theorem exists_arrowChart_finitePresentation_of_isLocallyOfFinitePresentation
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS
      (OverShriek.presheafToYoneda (pairIsom a ι)))
    [Algebra.FinitePresentation (ringOf B S hS T') P.obj]
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    ∃ (C₁ : SmallAlg (ringOf B S hS T') B.cutoff) (f : C ⟶ C₁)
      (_ : Surjective ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (_ : Etale ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (Q : SmallAlg (ringOf B S hS T') B.cutoff)
      (_ : Algebra.FinitePresentation (ringOf B S hS T') Q.obj)
      (_ : Module.FinitePresentation Q.obj Ω[Q.obj⁄ringOf B S hS T'])
      (b : Chart (stackArr a ι) Q.obj)
      (_ : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q.obj)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).src = v.comp sV)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).tgt = v.comp tV)
      (ε : Q.obj →ₐ[ringOf B S hS T'] C₁.obj), b.app C₁ ε = Arr.idt (f.hom.hom.comp w) := by
  obtain ⟨C₁, f₁, h₁, h₂, Q, hQ, b, hb, sV, tV, hs, ht, ε, hε⟩ :=
    exists_arrowChart_finitePresentation_aux a ι h𝒳 hlfp w
  exact ⟨C₁, f₁, h₁, h₂, Q, hQ, inferInstance, b, hb, sV, tV, hs, ht, ε, hε⟩

/-- **A formally étale chart of the arrows near an identity, by a finitely presented algebra.**
`AlgebraicGeometry.Stack.GroupoidLift.exists_arrowChart`, with the chart algebra `Q` of finite
presentation over `A'`, when `𝒳` is locally of finite presentation over a scheme `Z`, `P` is of
finite presentation over `A'` and the two objects `ξ v₀`, `ξ vₗ` over `Spec (P ⊗ P)` have the same
image in `Z`. -/
theorem exists_arrowChart_finitePresentation (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    {Z : BigFppfOver B S hS} (f : 𝒳 ⟶ schemeFibredCategory B S hS Z)
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hα : SameImage f.hom.toFunctor f.hom.w (pairObj₀ a ι) (pairObj₁ a ι))
    [Algebra.FinitePresentation (ringOf B S hS T') P.obj]
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    ∃ (C₁ : SmallAlg (ringOf B S hS T') B.cutoff) (f : C ⟶ C₁)
      (_ : Surjective ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (_ : Etale ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (Q : SmallAlg (ringOf B S hS T') B.cutoff)
      (_ : Algebra.FinitePresentation (ringOf B S hS T') Q.obj)
      (_ : Module.FinitePresentation Q.obj Ω[Q.obj⁄ringOf B S hS T'])
      (b : Chart (stackArr a ι) Q.obj)
      (_ : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q.obj)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).src = v.comp sV)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).tgt = v.comp tV)
      (ε : Q.obj →ₐ[ringOf B S hS T'] C₁.obj), b.app C₁ ε = Arr.idt (f.hom.hom.comp w) :=
  exists_arrowChart_finitePresentation_of_isLocallyOfFinitePresentation a ι h𝒳
    (isLocallyOfFinitePresentation_arrSpace a ι h𝒳 f hf hα) w

end GroupoidLift

end AlgebraicGeometry.Stack

end
