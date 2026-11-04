module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
import all
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityCoefficients

/-!
# The base change map of sheaves of sets on sections

Let

```
Y --h--> X
|e       |f
v        v
T --g--> S
```

be a commutative square of schemes and `F` a sheaf of sets on the small étale site of `T`. The
base change map `Stacks.EtaleCohomology.smallEtaleSetBaseChange : f⁻¹ g_* F ⟶ h_* e⁻¹ F` is the
mate of the identification of the two composite direct images, and this file computes it on
sections: on the image under the unit of `f⁻¹ ⊣ f_*` of a section `σ` of `g_*F` over an étale
`S`-scheme `W` it is the image of `σ` under the unit of `e⁻¹ ⊣ e_*`, restricted along the
canonical morphism `(W ×_S X) ×_X Y ⟶ (W ×_S T) ×_T Y`.

Consequently, restricting a section of `g_*F` over `W` to global sections of `f⁻¹ g_* F` along a
morphism `r : X ⟶ W` over `S`, applying the base change map and reading the result on `Y` gives
the restriction of the underlying section of `F` along the induced morphism `Y ⟶ W ×_S T`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSetBaseChange_app_smallEtaleUnitApp` — the base change map on
  the image of a section under the unit.
* `Stacks.EtaleCohomology.smallEtaleSetBaseChange_app_smallEtaleInverseImageSections` — the base
  change map on the restriction of a section to global sections.

## Implementation notes

The base change map is a mate, and Mathlib's `CategoryTheory.unit_mateEquiv_symm` is the identity
that transposes it along the adjunction for `f`; what is left is the action of the
identification of the two composite direct images on sections, which is restriction along the
comparison of the two composite base change functors of sites. That comparison is pinned down
only through its projection to `W`, since a morphism into an iterated base change is determined
by it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- The bookkeeping behind the projection of the composite lift in
`smallEtaleSetBaseChange_app_smallEtaleInverseImageSections`, in an abstract category. -/
private theorem comp_chain_fst {C : Type*} [Category* C] {A B₁ B₂ B₃ D₁ E P Q : C}
    (a : A ⟶ B₁) (b : B₁ ⟶ B₂) (c : B₂ ⟶ B₃) (p₁ : B₃ ⟶ D₁) (p₂ : D₁ ⟶ E) (q₁ : B₂ ⟶ Q)
    (q₂ : Q ⟶ E) (r₁ : B₁ ⟶ P) (l : P ⟶ Q) (y : A ⟶ P) (x : P ⟶ E) (z : A ⟶ B₃)
    (r' : A ⟶ D₁) (hc : c ≫ p₁ ≫ p₂ = q₁ ≫ q₂) (hb : b ≫ q₁ = r₁ ≫ l) (ha : a ≫ r₁ = y)
    (hl : l ≫ q₂ = x) (hz : z ≫ p₁ = r') (hr : r' ≫ p₂ = y ≫ x) :
    (a ≫ b ≫ c) ≫ p₁ ≫ p₂ = z ≫ p₁ ≫ p₂ := by
  simp only [Category.assoc]
  rw [hc, ← Category.assoc b, hb, Category.assoc, hl, ← Category.assoc a, ha,
    ← Category.assoc z, hz, hr]

/-- Three consecutive restrictions of an element of a presheaf of types are the restriction along
the composite. -/
private theorem map_op_map_op_map_op_apply {C : Type*} [Category* C] (P : Cᵒᵖ ⥤ Type*)
    {U V W Z : C} (a : U ⟶ V) (b : V ⟶ W) (c : W ⟶ Z) (y : P.obj (op Z)) :
    P.map a.op (P.map b.op (P.map c.op y)) = P.map (a ≫ b ≫ c).op y := by
  simp only [op_comp, Functor.map_comp, types_comp_apply]

section Square

variable {Y T X S : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
  (w : e ≫ g = h ≫ f)

/-- The mate, along the inverse-image/direct-image adjunctions for `e` and `f`, of a
transformation `β : e_* g_* ⟶ h_* f_*`, evaluated on the image under the unit for `f` of a section
`σ` of `g_*F` over `W`, is `β` evaluated on the image of `σ` under the unit for `e`. The
transformation is a variable, so this is `CategoryTheory.unit_mateEquiv_symm` read at one
section and no two spellings of a section of a composite direct image are compared. -/
private theorem mate_app_unit_app
    (β : TwoSquare
      ((smallEtaleBaseChange e).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology T) (smallEtaleTopology Y))
      ((smallEtaleBaseChange h).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology X) (smallEtaleTopology Y))
      ((smallEtaleBaseChange g).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology S) (smallEtaleTopology T))
      ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology S) (smallEtaleTopology X)))
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) (W : S.Etale)
    (σ : F.obj.obj (op ((smallEtaleBaseChange g).obj W))) :
    (((mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
        (smallEtaleInverseImageAdjunction.{u, v} f)).symm β).app F).hom.app
        (op ((smallEtaleBaseChange f).obj W))
        (((smallEtaleInverseImageAdjunction.{u, v} f).unit.app
          (((smallEtaleBaseChange g).sheafPushforwardContinuous (Type (max (u + 1) v))
            (smallEtaleTopology S) (smallEtaleTopology T)).obj F)).hom.app (op W) σ) =
      (β.app ((smallEtaleInverseImage.{u, v} e).obj F)).hom.app (op W)
        (((smallEtaleInverseImageAdjunction.{u, v} e).unit.app F).hom.app
          (op ((smallEtaleBaseChange g).obj W)) σ) := by
  have key := unit_mateEquiv_symm (smallEtaleInverseImageAdjunction.{u, v} e)
    (smallEtaleInverseImageAdjunction.{u, v} f) β F
  have h0 := congrArg (fun q => q.hom.app (op W)) key
  have h1 := ConcreteCategory.congr_hom h0 σ
  exact h1.symm

/-- The base change map of sheaves of sets is the mate of the square comparison of direct
images. -/
private theorem smallEtaleSetBaseChange_eq_mate_squareIso :
    smallEtaleSetBaseChange.{u, v} e h g f w =
      (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
        (smallEtaleInverseImageAdjunction.{u, v} f)).symm
          (smallEtaleSquarePushforwardIsoAt e h g f w (Type (max (u + 1) v))).hom :=
  rfl

/-- **The base change map on the image of a section under the unit.** For a section `σ` of
`g_* F` over an étale `S`-scheme `W`, the base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` carries the
image of `σ` under the unit of `f⁻¹ ⊣ f_*` to the image of `σ` under the unit of `e⁻¹ ⊣ e_*`,
restricted along any morphism `ι : (W ×_S X) ×_X Y ⟶ (W ×_S T) ×_T Y` of the small étale site of
`Y` compatible with the projections to `W` (there is exactly one). -/
theorem smallEtaleSetBaseChange_app_smallEtaleUnitApp
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) (W : S.Etale)
    (ι : (smallEtaleBaseChange h).obj ((smallEtaleBaseChange f).obj W) ⟶
      (smallEtaleBaseChange e).obj ((smallEtaleBaseChange g).obj W))
    (hι : ι.left ≫ pullback.fst _ e ≫ pullback.fst W.hom g =
      pullback.fst _ h ≫ pullback.fst W.hom f)
    (σ : F.obj.obj (op ((smallEtaleBaseChange g).obj W))) :
    ((smallEtaleSetBaseChange.{u, v} e h g f w).app F).hom.app
        (op ((smallEtaleBaseChange f).obj W))
        (smallEtaleUnitApp f ((smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T) |>.obj F) W σ) =
      ((smallEtaleInverseImage.{u, v} e).obj F).obj.map ι.op
        (smallEtaleUnitApp e F ((smallEtaleBaseChange g).obj W) σ) := by
  have hsite : (siteSquare e h g f w).hom.app W = ι :=
    smallEtaleBaseChange_baseChange_hom_ext e g
      ((siteSquare_hom_fst e h g f w W).trans hι.symm)
  have hβ := smallEtaleSquarePushforwardIsoAt_app (Type (max (u + 1) v)) e h g f w
    ((smallEtaleInverseImage.{u, v} e).obj F) W
  rw [hsite] at hβ
  rw [smallEtaleSetBaseChange_eq_mate_squareIso]
  exact (mate_app_unit_app e h g f _ F W σ).trans (ConcreteCategory.congr_hom hβ _)

include w in
/-- There is a morphism `(W ×_S X) ×_X Y ⟶ (W ×_S T) ×_T Y` of the small étale site of `Y`
compatible with the projections to `W`. -/
theorem exists_smallEtaleBaseChange_square_hom (W : S.Etale) :
    ∃ ι : (smallEtaleBaseChange h).obj ((smallEtaleBaseChange f).obj W) ⟶
        (smallEtaleBaseChange e).obj ((smallEtaleBaseChange g).obj W),
      ι.left ≫ pullback.fst _ e ≫ pullback.fst W.hom g =
        pullback.fst _ h ≫ pullback.fst W.hom f :=
  ⟨(siteSquare e h g f w).hom.app W, siteSquare_hom_fst e h g f w W⟩

/-- **The base change map on the restriction of a section to global sections.** Let `σ` be a
section of `g_* F` over an étale `S`-scheme `W`, that is, a section of `F` over `W ×_S T`, and let
`r : X ⟶ W` be a morphism over `S`. Restrict `σ` to a global section of `f⁻¹ g_* F` along `r`,
apply the base change map, and read the resulting section of `h_* e⁻¹ F` over the final object on
`Y`: the result is the restriction of `σ` to a global section of `e⁻¹ F` along the morphism
`r' : Y ⟶ W ×_S T` with components `h ≫ r` and `e`. -/
theorem smallEtaleSetBaseChange_app_smallEtaleInverseImageSections
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) (W : S.Etale)
    (r : X ⟶ W.left) (hr : r ≫ W.hom = f) (r' : Y ⟶ ((smallEtaleBaseChange g).obj W).left)
    (hr' : r' ≫ ((smallEtaleBaseChange g).obj W).hom = e)
    (hrr' : r' ≫ pullback.fst W.hom g = h ≫ r)
    (σ : F.obj.obj (op ((smallEtaleBaseChange g).obj W))) :
    ((smallEtaleInverseImage.{u, v} e).obj F).obj.map
        (smallEtaleBaseChangeLift h (Scheme.Etale.mk (𝟙 X)) h (Category.comp_id h)).op
        (((smallEtaleSetBaseChange.{u, v} e h g f w).app F).hom.app
          (op (Scheme.Etale.mk (𝟙 X)))
          (smallEtaleInverseImageSections f ((smallEtaleBaseChange g).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T) |>.obj F)
            (smallEtaleBaseChangeLift f W r hr) σ)) =
      smallEtaleInverseImageSections e F
        (smallEtaleBaseChangeLift e ((smallEtaleBaseChange g).obj W) r' hr') σ := by
  obtain ⟨ι, hι⟩ := exists_smallEtaleBaseChange_square_hom e h g f w W
  let L := (smallEtaleInverseImage.{u, v} e).obj F
  let lf := smallEtaleBaseChangeLift f W r hr
  let lh := smallEtaleBaseChangeLift h (Scheme.Etale.mk (𝟙 X)) h (Category.comp_id h)
  have hnat := NatTrans.naturality_apply ((smallEtaleSetBaseChange.{u, v} e h g f w).app F).hom
    lf.op (smallEtaleUnitApp f ((smallEtaleBaseChange g).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T) |>.obj F) W σ)
  have hG := smallEtaleSetBaseChange_app_smallEtaleUnitApp e h g f w F W ι hι σ
  have hlift : lh ≫ (smallEtaleBaseChange h).map lf ≫ ι =
      smallEtaleBaseChangeLift e ((smallEtaleBaseChange g).obj W) r' hr' := by
    refine smallEtaleBaseChange_baseChange_hom_ext e g ?_
    have h2 : ((smallEtaleBaseChange h).map lf).left ≫ pullback.fst _ h =
        pullback.fst _ h ≫ lf.left := smallEtaleBaseChange_map_left_fst h lf
    have h3 : lh.left ≫ pullback.fst _ h = h := pullback.lift_fst _ _ _
    have h4 : lf.left ≫ pullback.fst W.hom f = r := pullback.lift_fst _ _ _
    have h5 : (smallEtaleBaseChangeLift e ((smallEtaleBaseChange g).obj W) r' hr').left ≫
        pullback.fst _ e = r' := pullback.lift_fst _ _ _
    exact comp_chain_fst lh.left ((smallEtaleBaseChange h).map lf).left ι.left _ _ _ _ _
      lf.left h r _ r' hι h2 h3 h4 h5 hrr'
  refine (congrArg (L.obj.map lh.op) hnat).trans ?_
  show L.obj.map lh.op (L.obj.map ((smallEtaleBaseChange h).map lf).op
      (((smallEtaleSetBaseChange.{u, v} e h g f w).app F).hom.app _
        (smallEtaleUnitApp f _ W σ))) = _
  refine (congrArg (fun z => L.obj.map lh.op (L.obj.map ((smallEtaleBaseChange h).map lf).op z))
    hG).trans ?_
  refine (map_op_map_op_map_op_apply L.obj lh ((smallEtaleBaseChange h).map lf) ι _).trans ?_
  exact congrArg
    (fun m => L.obj.map m.op (smallEtaleUnitApp e F ((smallEtaleBaseChange g).obj W) σ)) hlift

end Square

end Stacks.EtaleCohomology

end
