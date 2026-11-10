module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartComparison

/-!
# The ring map attached to a section of an inverse image of a representable sheaf

Let `(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of the small étale
ringed topoi of two algebraic spaces.  Let `V` be an étale chart of `Y`, `U` an étale chart of
`X`, and `s` a section over `U` of `g⁻¹h_V`.  Then
`b ↦ g♯(g⁻¹(b)(s))` is a ring map `Γ(V, 𝒪_V) ⟶ Γ(U, 𝒪_U)`, and when `V` is affine it is the
map on global functions of a unique morphism of schemes `f_s : U ⟶ V`.  This is the
construction with which the proof of Stacks 04KL begins: in the source `f_s` is produced by
Stacks 04I7 from the localized morphism `(g_s, g_s♯)` of Stacks 04J8; for an affine `V` the
morphism Stacks 04I6 produces is `Spec` of the ring map on global sections of `(g_s, g_s♯)`,
which is the ring map constructed here.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageSectionTransport`: for `s` a section over `U` of
  `g⁻¹h_V`, the transformation `(g_*E)(V) ⟶ E(U)` natural in the sheaf `E`.
* `AlgebraicGeometry.Space.chartRingHom`: the ring map `Γ(V, 𝒪_V) ⟶ Γ(U, 𝒪_U)` attached to `s`.

## Main results

* `AlgebraicGeometry.Space.chartRingHom_apply`: the ring map is `b ↦ g♯(g⁻¹(b)(s))`.

## Implementation notes

The ring structure on the sections of a direct image is the one *transported* along the
direct image, so the ring map is first produced as a transformation of finite-product-preserving
functors to types, and only then read as a ring map, exactly as for
`AlgebraicGeometry.RingedToposHom.globalSectionsMap` (which is the case of the terminal
charts).

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] smallEtaleTopology_subcanonical

/-- The underlying scheme of an étale chart. -/
abbrev chartSch {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS F) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj U.obj.left

/-- The sheaf of rings underlying the structure sheaf of the small étale site of an algebraic
space. -/
abbrev ringO (X : AlgebraicSpaces B S hS) : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1)
    (smallEtaleRingedTopos B S hS X).O

variable {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

/-- The sheaf on the small étale site of `X` which is the inverse image along `g` of the sheaf
represented by an étale chart `V` of `Y`. -/
abbrev invRep (V : SmallEtale B S hS Y.1) : Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
  g.toToposHom.inverseImage.obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V)

/-- The transformation `(g_*E)(V) ⟶ E(U)` attached to a section `s` over `U` of `g⁻¹h_V`: a
section of `g_*E` over `V` is a map `h_V ⟶ g_*E`, its adjoint is a map `g⁻¹h_V ⟶ E`, and that
map is evaluated at `s`. -/
def inverseImageSectionTransport (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V) ⟶
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) (op U) where
  app E := ↾fun x ↦ ((g.toToposHom.adj.homEquiv _ _).symm
    ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x)).hom.app (op U) s
  naturality E E' m := by
    ext (x : (g.toToposHom.pushforward.obj E).obj.obj (op V))
    have h1 := GrothendieckTopology.yonedaEquiv_symm_naturality_right
      (SmallEtale.topology B S hS Y.1) V (g.toToposHom.pushforward.map m) x
    have h : (g.toToposHom.adj.homEquiv _ E').symm
        ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
          ((g.toToposHom.pushforward.map m).hom.app (op V) x)) =
        (g.toToposHom.adj.homEquiv _ E).symm
          ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x) ≫ m := by
      rw [← h1, Adjunction.homEquiv_naturality_right_symm]
    exact congrArg (fun φ ↦ φ.hom.app (op U) s) h

/-- The ring map underlying `AlgebraicGeometry.Space.inverseImageSectionRingHom`. -/
def inverseImageSectionRingHom' (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    ToType (((pushforwardCommRingFunctor g.toToposHom).obj
        (smallEtaleRingedTopos B S hS X).O).obj.obj (op V)) →+*
      ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U)) where
  toFun x := (inverseImageSectionTransport g V U s).app
    (Sheaf.ringSheaf (ringO X)) x
  map_one' :=
    (Sheaf.ringOneObj_naturality (ringO X) (inverseImageSectionTransport g V U s)).trans
      (Sheaf.sectionsFunctor_map_ringOneHom (ringO X) (op U) default)
  map_mul' x y :=
    (Sheaf.ringMulObj_naturality (ringO X) (inverseImageSectionTransport g V U s) x y).trans
      (Sheaf.sectionsFunctor_map_ringMulHom (ringO X) (op U) _ _)
  map_zero' :=
    (Sheaf.ringZeroObj_naturality (ringO X) (inverseImageSectionTransport g V U s)).trans
      (Sheaf.sectionsFunctor_map_ringZeroHom (ringO X) (op U) default)
  map_add' x y :=
    (Sheaf.ringAddObj_naturality (ringO X) (inverseImageSectionTransport g V U s) x y).trans
      (Sheaf.sectionsFunctor_map_ringAddHom (ringO X) (op U) _ _)

/-- The transformation of `AlgebraicGeometry.Space.inverseImageSectionTransport` on the structure
sheaf, as a ring map `Γ(V, g_*𝒪_X) ⟶ Γ(U, 𝒪_X)` for the transported ring structure on the
sections of the direct image. -/
def inverseImageSectionRingHom (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    ((pushforwardCommRingFunctor g.toToposHom).obj (smallEtaleRingedTopos B S hS X).O).obj.obj
        (op V) ⟶ (smallEtaleRingedTopos B S hS X).O.obj.obj (op U) :=
  ConcreteCategory.ofHom (C := CommRingCat) (inverseImageSectionRingHom' g V U s)

/-- **The ring map attached to a section of `g⁻¹h_V`.** For an étale chart `V` of `Y`, an étale
chart `U` of `X` and a section `s` over `U` of `g⁻¹h_V`, the ring map
`Γ(V, 𝒪_V) ⟶ Γ(U, 𝒪_U)` sending `b` to `g♯(g⁻¹(b)(s))`: the structure map `g♯` over `V`,
followed by evaluation at `s`. -/
def chartRingHom (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    Γ(chartSch V, ⊤) ⟶ Γ(chartSch U, ⊤) :=
  g.fSharp.hom.app (op V) ≫ inverseImageSectionRingHom g V U s

/-- The sheaf of sets underlying the structure sheaf of the small étale ringed topos. -/
abbrev setO (Z : AlgebraicSpaces B S hS) : Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  (smallEtaleRingedTopos B S hS Z).forgetRing.obj (smallEtaleRingedTopos B S hS Z).O

/-- The coordinate map `g⁻¹h_V ⟶ 𝒪_X` attached to a regular function `b` on `V`: the inverse
image of `b : h_V ⟶ 𝒪_Y` followed by the inverse-image form of the structure map. -/
def invCoord (V : SmallEtale B S hS Y.1) (b : (setO Y).obj.obj (op V)) : invRep g V ⟶ setO X :=
  g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm b) ≫
    g.fSharpSet

/-- The coordinate map is the adjoint of the section `g♯(b)` of `g_*𝒪_X` over `V`. -/
theorem homEquiv_symm_forgetFSharp (V : SmallEtale B S hS Y.1) (b : (setO Y).obj.obj (op V)) :
    (g.toToposHom.adj.homEquiv _ _).symm
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
        ((RingedToposHom.forgetFSharp g).hom.app (op V) b)) = invCoord g V b := by
  have h1 := GrothendieckTopology.yonedaEquiv_symm_naturality_right
    (SmallEtale.topology B S hS Y.1) V (RingedToposHom.forgetFSharp g) b
  rw [← h1, Adjunction.homEquiv_naturality_left_symm]
  rfl

/-- **The formula for the ring map attached to `s`.** For `b ∈ Γ(V, 𝒪_V)`, regarded as a map
`h_V ⟶ 𝒪_Y`, the image of `b` is the value at `s` of `g⁻¹h_V ⟶ g⁻¹𝒪_Y ⟶ 𝒪_X`, the second map
being the inverse-image form of the structure map. -/
theorem chartRingHom_apply (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) (b : (setO Y).obj.obj (op V)) :
    (chartRingHom g V U s).hom b = (invCoord g V b).hom.app (op U) s := by
  change ((g.toToposHom.adj.homEquiv _ _).symm
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
        ((RingedToposHom.forgetFSharp g).hom.app (op V) b))).hom.app (op U) s = _
  exact congrArg (fun φ ↦ φ.hom.app (op U) s) (homEquiv_symm_forgetFSharp g V b)

/-- **Naturality of the ring map in the chart of the source.** Restricting `s` along a morphism
`i : U' ⟶ U` of étale charts of `X` composes the ring map with the restriction of functions. -/
theorem chartRingHom_restrict (V : SmallEtale B S hS Y.1) {U U' : SmallEtale B S hS X.1}
    (i : U' ⟶ U) (s : (invRep g V).obj.obj (op U)) :
    chartRingHom g V U' ((invRep g V).obj.map i.op s) =
      chartRingHom g V U s ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map i.hom.left).op := by
  ext b
  exact (chartRingHom_apply g V U' _ b).trans
    ((ConcreteCategory.congr_hom ((invCoord g V b).hom.naturality i.op) s).trans
      (congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map i.hom.left).op).hom
        (chartRingHom_apply g V U s b).symm))

/-- **Naturality of the ring map in the chart of the target.** For a morphism `c : V' ⟶ V` of
étale charts of `Y` and a section `s'` over `U` of `g⁻¹h_{V'}`, the ring map attached to the
image of `s'` in `g⁻¹h_V` is restriction of functions along `c` followed by the ring map
attached to `s'`. -/
theorem chartRingHom_map (U : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1}
    (c : V' ⟶ V) (s' : (invRep g V').obj.obj (op U)) :
    chartRingHom g V U ((g.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U) s') =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map c.hom.left).op ≫
        chartRingHom g V' U s' := by
  ext b
  refine (chartRingHom_apply g V U _ b).trans (Eq.trans ?_ (chartRingHom_apply g V' U s' _).symm)
  change (g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map c) ≫
      g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm b) ≫
        g.fSharpSet).hom.app (op U) s' = _
  have h := GrothendieckTopology.yonedaEquiv_symm_naturality_left
    (SmallEtale.topology B S hS Y.1) c (setO Y) (show (setO Y).obj.obj (op V) from b)
  rw [← Category.assoc, ← Functor.map_comp, h]
  rfl

/-! ### The morphism of schemes attached to a section, for an affine chart of the target -/

/-- **The morphism of schemes `f_s : U ⟶ V`** attached to a section `s` over `U` of `g⁻¹h_V`,
for an affine étale chart `V` of `Y`: the morphism inducing `chartRingHom g V U s` on global
functions. -/
def chartSchemeHom (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) : chartSch U ⟶ chartSch V :=
  Stacks.EtaleCohomology.schemeHomOfAppTop _ _ (chartRingHom g V U s)

/-- `f_s` induces `chartRingHom g V U s` on global functions. -/
@[simp]
theorem chartSchemeHom_appTop (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (chartSchemeHom g V U s).appTop = chartRingHom g V U s :=
  Stacks.EtaleCohomology.appTop_schemeHomOfAppTop _ _ _

/-- `f_s` is natural in the chart of the source. -/
theorem chartSchemeHom_restrict (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    {U U' : SmallEtale B S hS X.1} (i : U' ⟶ U) (s : (invRep g V).obj.obj (op U)) :
    chartSchemeHom g V U' ((invRep g V).obj.map i.op s) =
      (BigFppfOver.toScheme B S hS).map i.hom.left ≫ chartSchemeHom g V U s := by
  apply ext_of_isAffine
  rw [chartSchemeHom_appTop, Scheme.Hom.comp_appTop, chartSchemeHom_appTop,
    chartRingHom_restrict]
  rfl

/-- `f_s` is natural in the chart of the target. -/
theorem chartSchemeHom_map (U : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V)] [IsAffine (chartSch V')]
    (c : V' ⟶ V) (s' : (invRep g V').obj.obj (op U)) :
    chartSchemeHom g V U ((g.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U) s') =
      chartSchemeHom g V' U s' ≫ (BigFppfOver.toScheme B S hS).map c.hom.left := by
  apply ext_of_isAffine
  rw [chartSchemeHom_appTop, Scheme.Hom.comp_appTop, chartSchemeHom_appTop,
    chartRingHom_map]
  rfl

end AlgebraicGeometry.Space
