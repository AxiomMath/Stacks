module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeSquare07MS
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiFlatteningSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RingedPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RingedStructureMorphism07MS

/-!
# The square of ringed topoi of [Stacks, Tag 07MS]

For a morphism `f : (S, I, γ) ⟶ (S', I', γ')` of divided power schemes and a compatible
`g : X ⟶ X'` (the situation of [Stacks, Tag 07MJ], `g` arbitrary), the square

```
  ((X/S)_cris, 𝒪_{X/S}) --f_cris--> ((X'/S')_cris, 𝒪_{X'/S'})
          | τ_{X/S}                         | τ_{X'/S'}
          v                                 v
     (S_Zar, 𝒪_S) ---------f_Zar------> (S'_Zar, 𝒪_{S'})
```

of morphisms of ringed topoi 2-commutes.  This is the square whose base change map, in the sense
of [Stacks, Tag 07A7], is the base change map of [Stacks, Tag 07MS].

The 2-isomorphism is `structureSquarePushforwardIso` on direct images, which comes from the square
of topoi of [Stacks, Tag 07Q9].  What has to be checked is that it carries the structure map of one
route to the structure map of the other.  Sections of `τ_{X'/S', *}f_{cris, *}𝒪_{X/S}` over an
open `V'` of `S'` are detected by the dominating pairs `(A', A, k)` over `X'_{V'}`
(`crisZariskiLeft_hom_extCoeff`), and at such a pair both structure maps send a function on `V'`
to its pullback to the ambient scheme `T_A` of `A`: along `T_A ⟶ S ⟶ S'`
(`squareLower_chain`) and along `T_A ⟶ T_{A'} ⟶ S'` (`squareUpper_chain`), which agree because `k`
is a morphism over `S'` (`square_pullback_eq`).

## Main definitions

* `squareLower`, `squareUpper` — the two routes `f_Zar ∘ τ_{X/S}` and `τ_{X'/S'} ∘ f_cris`.
* `structureSquareTwoIso` — the 2-isomorphism between them.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- The sheaf of sets underlying `𝒪_{X/S}` on the crystalline ringed topos. -/
abbrev crisStructureSet (S : GlobalCrystallineSituation.{u}) :
    Sheaf (smallTopology S) (Type (u + 1)) :=
  (crisRingedTopos S).forgetRing.obj (crisRingedTopos S).O

/-- The composite of restrictions and counits reading a section of `u_{X'/S', *}f_{cris, *}ℋ` over
`V` at a dominating pair over `V`. -/
abbrev dominationChain (G : Sheaf (smallTopology S) (Type (u + 1))) (V : S'.X.Opens)
    (e : StructuredArrow (op V) (dominationToOpens S S' f g h)) :=
  ((forgetToOpens S').op.ran.obj ((CrystallineThickening.ι S').op ⋙
        (changeBase S S' f g h).op.ran.obj
          ((CrystallineThickening.ι S).op.ran.obj G.obj))).map e.hom ≫
    (((forgetToOpens S').op.ranCounit.app
        ((CrystallineThickening.ι S').op ⋙
          (changeBase S S' f g h).op.ran.obj
            ((CrystallineThickening.ι S).op.ran.obj G.obj))).app e.right.left) ≫
      ((changeBase S S' f g h).op.ran.obj
          ((CrystallineThickening.ι S).op.ran.obj G.obj)).map e.right.hom ≫
        (((changeBase S S' f g h).op.ranCounit.app
          ((CrystallineThickening.ι S).op.ran.obj G.obj)).app
            ((CrystallineThickening.ι S).op.obj e.right.right)) ≫
          (((CrystallineThickening.ι S).op.ranCounit.app G.obj).app e.right.right)

/-- **The lower route `f_Zar ∘ τ_{X/S}` of the square of [Stacks, Tag 07MS]**, as a morphism of
ringed topoi `((X/S)_cris, 𝒪_{X/S}) ⟶ (S'_Zar, 𝒪_{S'})`. -/
abbrev squareLower : RingedToposHom (crisRingedTopos S) (zariskiRingedTopos S'.S.scheme) :=
  RingedToposHom.comp (X := crisRingedTopos S) (Y := zariskiRingedTopos S.S.scheme)
    (Z := zariskiRingedTopos S'.S.scheme) (zariskiRingedHom f.hom) (structureRingedHom S)

/-- **The upper route `τ_{X'/S'} ∘ f_cris` of the square of [Stacks, Tag 07MS]**, as a morphism of
ringed topoi `((X/S)_cris, 𝒪_{X/S}) ⟶ (S'_Zar, 𝒪_{S'})`. -/
abbrev squareUpper : RingedToposHom (crisRingedTopos S) (zariskiRingedTopos S'.S.scheme) :=
  RingedToposHom.comp (X := crisRingedTopos S) (Y := crisRingedTopos S')
    (Z := zariskiRingedTopos S'.S.scheme) (structureRingedHom S') (crisRingedHomComp f g h)

/-- **The object of `Cris(X/S)` of a dominating pair over `X'_{V'}` lies over `X_{f⁻¹V'}`.**  Its
open is inside `g⁻¹(X'_{V'})`, and `g⁻¹(X'_{V'}) = X_{f⁻¹V'}` because `X ⟶ X' ⟶ S'` is
`X ⟶ S ⟶ S'`. -/
theorem dominationPairs_le_base_preimage (V' : S'.S.scheme.Opens)
    (e : StructuredArrow (op ((Opens.map (sourceToBase S').base).obj V'))
      (dominationToOpens S S' f g h)) :
    (forgetToOpens S).obj e.right.right.unop ≤
      (Opens.map (sourceToBase S).base).obj (f.hom ⁻¹ᵁ V') := by
  refine (dominationPairs_le_preimage S S' f g h _ e).trans (le_of_eq ?_)
  change (Opens.map g.base).obj ((Opens.map (sourceToBase S').base).obj V') =
    (Opens.map (sourceToBase S).base).obj ((Opens.map f.hom.base).obj V')
  rw [← Opens.map_comp_obj, ← Opens.map_comp_obj]
  congr 2
  exact congrArg (fun φ : S.X ⟶ S'.S.scheme => φ.base)
    (comp_sourceToBase (f := f) (g := g) (h := h))

/-- The structure map of `f_Zar` on sections over `V'` is `f^♯`, its sections raised. -/
theorem zariskiRingedHom_forgetFSharp_app {Z Z' : Scheme.{u}} (φ : Z ⟶ Z') (V' : Z'.Opens) :
    (RingedToposHom.forgetFSharp (zariskiRingedHom φ)).hom.app (op V') =
      (CategoryTheory.forget CommRingCat.{u + 1}).map
        (SheafOfModules.commRingCatULift.{u, u + 1}.map (φ.app V')) :=
  rfl

/-- **The lower route of the square on sections.**  The structure map of
`f_Zar ∘ τ_{X/S}`, carried across `structureSquarePushforwardIso`, read at a dominating pair
`(A', A, k)` over `X'_{V'}`, is the pullback of functions along `T_A ⟶ S ⟶ S'`. -/
theorem squareLower_chain (V' : S'.S.scheme.Opens)
    (e : StructuredArrow (op ((Opens.map (sourceToBase S').base).obj V'))
      (dominationToOpens S S' f g h)) :
    (RingedToposHom.forgetFSharp (squareLower f)).hom.app (op V') ≫
      ((structureSquarePushforwardIso f g h).hom.app (crisStructureSet S)).hom.app (op V') ≫
        dominationChain f g h (crisStructureSet S) _ e =
    (CategoryTheory.forget CommRingCat.{u + 1}).map
      (SheafOfModules.commRingCatULift.{u, u + 1}.map (f.hom.app V' ≫
        e.right.right.unop.obj.toBase.hom.appLE (f.hom ⁻¹ᵁ V') ⊤
          (top_le_toBase_preimage (dominationPairs_le_base_preimage f g h V' e)))) := by
  have hcell := crisZariskiCell_app_hom_app_comp_ranCounitCoeff S S' f g h (Type (u + 1))
    (crisStructureSet S) ((Opens.map (sourceToBase S').base).obj V') e.right.left.unop
    e.right.right.unop e.right.hom.unop (leOfHom e.hom.unop)
    (dominationPairs_le_preimage S S' f g h _ e)
  have hτ := structureRingedHom_forgetFSharp_chain S (f.hom ⁻¹ᵁ V') e.right.right.unop
    (dominationPairs_le_base_preimage f g h V' e)
  have hchain : dominationChain f g h (crisStructureSet S) _ e =
      ((S'.forgetToOpens.op.ran.obj ((CrystallineThickening.ι S').op ⋙
          (S.changeBase S' f g h).op.ran.obj
            ((CrystallineThickening.ι S).op.ran.obj (crisStructureSet S).obj))).map
          (homOfLE (leOfHom e.hom.unop)).op ≫
        (S'.forgetToOpens.op.ranCounit.app ((CrystallineThickening.ι S').op ⋙
          (S.changeBase S' f g h).op.ran.obj
            ((CrystallineThickening.ι S).op.ran.obj (crisStructureSet S).obj))).app
          (op (unop e.right.left)) ≫
        ((S.changeBase S' f g h).op.ran.obj
            ((CrystallineThickening.ι S).op.ran.obj (crisStructureSet S).obj)).map
          e.right.hom.unop.op ≫
        ((S.changeBase S' f g h).op.ranCounit.app
            ((CrystallineThickening.ι S).op.ran.obj (crisStructureSet S).obj)).app
          ((CrystallineThickening.ι S).op.obj (op (unop e.right.right))) ≫
        ((CrystallineThickening.ι S).op.ranCounit.app (crisStructureSet S).obj).app
          (op (unop e.right.right))) := rfl
  have hiso : ((structureSquarePushforwardIso f g h).hom.app (crisStructureSet S)).hom.app
        (op V') =
      ((S.forgetToOpens.op.ran.obj (crisStructureSet S).obj).map
          ((structureSquareOpensIso f g h).inv.app V').op) ≫
        ((crisZariskiCellCoeff S S' f g h (Type (u + 1))).app (crisStructureSet S)).hom.app
          (op ((Opens.map (sourceToBase S').base).obj V')) := rfl
  have hcomp := congrArg (fun φ ↦ φ.hom.app (op V'))
    (RingedToposHom.forgetFSharp_comp (zariskiRingedHom f.hom) (structureRingedHom S))
  have hres : (S.forgetToOpens.op.ran.obj (crisStructureSet S).obj).map
        ((structureSquareOpensIso f g h).inv.app V').op ≫
      (S.forgetToOpens.op.ran.obj (crisStructureSet S).obj).map
        (homOfLE (dominationPairs_le_preimage S S' f g h _ e)).op =
      (S.forgetToOpens.op.ran.obj (crisStructureSet S).obj).map
        (homOfLE (dominationPairs_le_base_preimage f g h V' e)).op := by
    rw [← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  rw [hchain, hiso]
  ext x
  refine (ConcreteCategory.congr_hom hcell _).trans ?_
  have hres' := congrArg (· ≫ (S.forgetToOpens.op.ranCounit.app (crisStructureSet S).obj).app
    (op (unop e.right.right))) hres
  simp only [Category.assoc] at hres'
  refine (ConcreteCategory.congr_hom hres' _).trans ?_
  have final : (squareLower f).forgetFSharp.hom.app (op V') ≫
      (S.forgetToOpens.op.ran.obj (crisStructureSet S).obj).map
        (homOfLE (dominationPairs_le_base_preimage f g h V' e)).op ≫
      (S.forgetToOpens.op.ranCounit.app (crisStructureSet S).obj).app (op (unop e.right.right)) =
      (CategoryTheory.forget CommRingCat.{u + 1}).map
        (SheafOfModules.commRingCatULift.{u, u + 1}.map (f.hom.app V' ≫
          e.right.right.unop.obj.toBase.hom.appLE (f.hom ⁻¹ᵁ V') ⊤
            (top_le_toBase_preimage (dominationPairs_le_base_preimage f g h V' e)))) := by
    refine (congrArg (· ≫ _) hcomp).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) hτ).trans ?_
    rfl
  exact ConcreteCategory.congr_hom final x

/-- **The upper route of the square on sections.**  The structure map of
`τ_{X'/S'} ∘ f_cris`, read at a dominating pair `(A', A, k)` over `X'_{V'}`, is the pullback of
functions along `T_A ⟶ T_{A'} ⟶ S'`. -/
theorem squareUpper_chain (V' : S'.S.scheme.Opens)
    (e : StructuredArrow (op ((Opens.map (sourceToBase S').base).obj V'))
      (dominationToOpens S S' f g h)) :
    (RingedToposHom.forgetFSharp (squareUpper f g h)).hom.app (op V') ≫
        dominationChain f g h (crisStructureSet S) _ e =
    (CategoryTheory.forget CommRingCat.{u + 1}).map
      (SheafOfModules.commRingCatULift.{u, u + 1}.map (e.right.left.unop.obj.toBase.hom.appLE V' ⊤
          (top_le_toBase_preimage (leOfHom e.hom.unop)) ≫
        e.right.hom.unop.targetHom.hom.appTop)) := by
  -- `H` is the presheaf underlying `f_{cris, *}𝒪_{X/S}`, spelled as in `dominationChain`
  let H : (CrystallineThickening S')ᵒᵖ ⥤ Type (u + 1) := (CrystallineThickening.ι S').op ⋙
    (S.changeBase S' f g h).op.ran.obj ((CrystallineThickening.ι S).op.ran.obj
      (crisStructureSet S).obj)
  let ψ : (crisStructureSet S').obj ⟶ H :=
    (RingedToposHom.forgetFSharp (crisRingedHomComp f g h)).hom
  let τ' : (zariskiRingedTopos S'.S.scheme).forgetRing.obj (zariskiRingedTopos S'.S.scheme).O ⟶
      ((structureToposMorphism S').pushforward.obj (crisStructureSet S')) :=
    RingedToposHom.forgetFSharp (structureRingedHom S')
  have hcomp : (RingedToposHom.forgetFSharp (squareUpper f g h)).hom.app (op V') =
      τ'.hom.app (op V') ≫ ((forgetToOpens S').op.ran.map ψ).app
        (op ((Opens.map (sourceToBase S').base).obj V')) :=
    congrArg (fun φ ↦ φ.hom.app (op V'))
      (RingedToposHom.forgetFSharp_comp (structureRingedHom S') (crisRingedHomComp f g h))
  have hτ : τ'.hom.app (op V') ≫
      ((forgetToOpens S').op.ran.obj (crisStructureSet S').obj).map e.hom ≫
        ((forgetToOpens S').op.ranCounit.app (crisStructureSet S').obj).app e.right.left =
      (CategoryTheory.forget CommRingCat.{u + 1}).map
        (SheafOfModules.commRingCatULift.{u, u + 1}.map
          (e.right.left.unop.obj.toBase.hom.appLE V' ⊤
            (top_le_toBase_preimage (leOfHom e.hom.unop)))) := by
    have he : e.hom = (homOfLE (leOfHom e.hom.unop)).op := Subsingleton.elim _ _
    exact (congrArg (fun m ↦ τ'.hom.app (op V') ≫
      ((forgetToOpens S').op.ran.obj (crisStructureSet S').obj).map m ≫
        ((forgetToOpens S').op.ranCounit.app (crisStructureSet S').obj).app e.right.left) he).trans
      (structureRingedHom_forgetFSharp_chain S' V' e.right.left.unop (leOfHom e.hom.unop))
  let rest := ((S.changeBase S' f g h).op.ran.obj ((CrystallineThickening.ι S).op.ran.obj
        (crisStructureSet S).obj)).map e.right.hom ≫
      ((S.changeBase S' f g h).op.ranCounit.app ((CrystallineThickening.ι S).op.ran.obj
        (crisStructureSet S).obj)).app ((CrystallineThickening.ι S).op.obj e.right.right) ≫
      ((CrystallineThickening.ι S).op.ranCounit.app (crisStructureSet S).obj).app
        e.right.right
  have hd : ψ.app e.right.left ≫ rest =
      ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O).obj.map
        e.right.hom.unop.op :=
    crisRingedHomComp_forgetFSharp_chain f g h e.right.left.unop e.right.right.unop
      e.right.hom.unop
  have hnat : ((forgetToOpens S').op.ran.obj (crisStructureSet S').obj).map e.hom ≫
      ((forgetToOpens S').op.ran.map ψ).app _ =
      ((forgetToOpens S').op.ran.map ψ).app _ ≫ ((forgetToOpens S').op.ran.obj H).map e.hom :=
    ((forgetToOpens S').op.ran.map ψ).naturality e.hom
  have hcounit : ((forgetToOpens S').op.ran.map ψ).app _ ≫
      ((forgetToOpens S').op.ranCounit.app H).app e.right.left =
      ((forgetToOpens S').op.ranCounit.app (crisStructureSet S').obj).app e.right.left ≫
        ψ.app e.right.left :=
    congrArg (fun t ↦ NatTrans.app t e.right.left) ((forgetToOpens S').op.ranCounit.naturality ψ)
  have k1 : ((forgetToOpens S').op.ran.map ψ).app _ ≫
      ((forgetToOpens S').op.ran.obj H).map e.hom ≫
        ((forgetToOpens S').op.ranCounit.app H).app e.right.left ≫ rest =
      ((forgetToOpens S').op.ran.obj (crisStructureSet S').obj).map e.hom ≫
        ((forgetToOpens S').op.ran.map ψ).app _ ≫
          ((forgetToOpens S').op.ranCounit.app H).app e.right.left ≫ rest :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat.symm).trans (Category.assoc _ _ _))
  have k2 : ((forgetToOpens S').op.ran.map ψ).app _ ≫
      ((forgetToOpens S').op.ranCounit.app H).app e.right.left ≫ rest =
      ((forgetToOpens S').op.ranCounit.app (crisStructureSet S').obj).app e.right.left ≫
        ((bigCrisRingedTopos S').forgetRing.obj (bigCrisRingedTopos S').O).obj.map
          e.right.hom.unop.op :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ rest) hcounit).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hd)))
  refine (congrArg (· ≫ dominationChain f g h (crisStructureSet S) _ e) hcomp).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (τ'.hom.app (op V') ≫ ·) (k1.trans (congrArg (_ ≫ ·) k2))).trans ?_
  have k3 := congrArg (· ≫ ((bigCrisRingedTopos S').forgetRing.obj
    (bigCrisRingedTopos S').O).obj.map e.right.hom.unop.op) hτ
  simp only at k3
  exact k3

/-- The two pullbacks of functions agree: `T_A ⟶ S ⟶ S'` is `T_A ⟶ T_{A'} ⟶ S'`. -/
theorem square_pullback_eq (V' : S'.S.scheme.Opens)
    (e : StructuredArrow (op ((Opens.map (sourceToBase S').base).obj V'))
      (dominationToOpens S S' f g h)) :
    f.hom.app V' ≫ e.right.right.unop.obj.toBase.hom.appLE (f.hom ⁻¹ᵁ V') ⊤
        (top_le_toBase_preimage (dominationPairs_le_base_preimage f g h V' e)) =
      e.right.left.unop.obj.toBase.hom.appLE V' ⊤
          (top_le_toBase_preimage (leOfHom e.hom.unop)) ≫
        e.right.hom.unop.targetHom.hom.appTop := by
  have key : ∀ {φ₁ φ₂ : e.right.right.unop.obj.thickening.target.scheme ⟶ S'.S.scheme}
      (_ : φ₁ = φ₂) (e₁ : (⊤ : e.right.right.unop.obj.thickening.target.scheme.Opens) ≤ φ₁ ⁻¹ᵁ V')
      (e₂ : (⊤ : e.right.right.unop.obj.thickening.target.scheme.Opens) ≤ φ₂ ⁻¹ᵁ V'),
      φ₁.appLE V' ⊤ e₁ = φ₂.appLE V' ⊤ e₂ := by
    rintro _ _ rfl _ _
    rfl
  have hb : e.right.hom.unop.targetHom.hom ≫ e.right.left.unop.obj.toBase.hom =
      e.right.right.unop.obj.toBase.hom ≫ f.hom := by
    have : e.right.hom.unop.targetHom ≫ e.right.left.unop.obj.toBase =
        e.right.right.unop.obj.toBase ≫ f := e.right.hom.unop.base_naturality
    exact (DividedPowerScheme.Hom.comp_hom _ _).symm.trans
      ((congrArg DividedPowerScheme.Hom.hom this).trans (DividedPowerScheme.Hom.comp_hom _ _))
  have h1 := Scheme.Hom.comp_appLE e.right.right.unop.obj.toBase.hom f.hom V' ⊤
    (top_le_toBase_preimage (dominationPairs_le_base_preimage f g h V' e))
  have h2 := Scheme.Hom.appLE_comp_appLE e.right.hom.unop.targetHom.hom
    e.right.left.unop.obj.toBase.hom V' ⊤ ⊤ (top_le_toBase_preimage (leOfHom e.hom.unop)) le_top
  have h3 : e.right.hom.unop.targetHom.hom.appTop =
      e.right.hom.unop.targetHom.hom.appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  exact h1.symm.trans ((key hb.symm _ _).trans (h2.symm.trans (congrArg (_ ≫ ·) h3.symm)))

/-- **The square of ringed topoi of [Stacks, Tag 07MS] commutes**: the two routes
`f_Zar ∘ τ_{X/S}` and `τ_{X'/S'} ∘ f_cris` from `((X/S)_cris, 𝒪_{X/S})` to `(S'_Zar, 𝒪_{S'})` are
2-isomorphic, by `structureSquarePushforwardIso` on direct images, which carries the structure map
of one to that of the other: both send a function on an open of `S'` to its pullbacks along the
objects of `Cris(X/S)`. -/
def structureSquareTwoIso :
    RingedToposHom.TwoIso (A := crisRingedTopos S) (B := zariskiRingedTopos S'.S.scheme)
      (squareLower f) (squareUpper f g h) where
  e := structureSquarePushforwardIso f g h
  commutes := by
    refine Sheaf.hom_ext ?_
    ext V' : 2
    refine crisZariskiLeft_hom_extCoeff S S' f g h (Type (u + 1)) (crisStructureSet S)
      ((Opens.map (sourceToBase S').base).obj V'.unop) (fun e ↦ ?_)
    exact ((Category.assoc _ _ _).trans (squareLower_chain f g h V'.unop e)).trans
      ((congrArg _ (congrArg _ (square_pullback_eq f g h V'.unop e))).trans
        (squareUpper_chain f g h V'.unop e).symm)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
