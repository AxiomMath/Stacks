module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparisonCommShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.DirectImageConnectingMap

/-!
# The connecting morphisms of the source of the base change map, along a composite base

Let

```
X₁ --v₁--> X₀
|g₁         |g₀
v           v
S₁ --u₁--> S₀
```

be a commutative square of schemes and let `u₂ : S₂ ⟶ S₁` be a further morphism. For a short
exact sequence `E` on `X₀`, a short exact sequence `E'` on `X₁` and a morphism
`σ : v₁⁻¹E ⟶ E'`, the inverse image along `u₂` of the base change map of the square, followed
by `R h_* σ`, commutes with the connecting morphisms of the sources of the base change maps along
`u₂ ≫ u₁` and along `u₂`, where each horizontal arrow is preceded by the comparison
`(u₂ ≫ u₁)⁻¹ ≅ u₂⁻¹u₁⁻¹`:

```
(u₂ ≫ u₁)⁻¹R^q g₀_* X₃ ─────u₂⁻¹(BC ≫ R^q g₁_* σ₃)─────→ u₂⁻¹R^q g₁_* X₃'
          │ δSource(u₂ ≫ u₁, g₀)                         │ δSource(u₂, g₁)
(u₂ ≫ u₁)⁻¹R^{q+1} g₀_* X₁ ─u₂⁻¹(BC ≫ R^{q+1} g₁_* σ₁)─→ u₂⁻¹R^{q+1} g₁_* X₁'
```

The connecting morphisms involved are both connecting morphisms of homology sequences of derived
triangles, and the square is the naturality of the connecting morphism along a morphism of
triangles: the derived comparison `R((u₂ ≫ u₁)⁻¹) ≅ R(u₁⁻¹) ⋙ R(u₂⁻¹)`, the image under `R(u₂⁻¹)`
of the derived base change map of the square, and the image of the morphism of triangles attached
to `σ`. What is proved by hand is that the two identifications of the sources with cohomology of
derived functors carry the one to the other, `pullbackBaseChange_comp_baseChangeSourceIso`.

## Main results

* `Stacks.EtaleCohomology.pullbackBaseChange_comp_baseChangeSourceIso` — the comparison of the
  identifications, in every degree.
* `Stacks.EtaleCohomology.higherBaseChangeδSource_paste` — **the square above commutes.**

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-! ### The naturality of the connecting morphism along `pullbackTriangleHom` -/

section General

variable {Y T : Scheme.{u}} (e : Y ⟶ T) (q : ℕ)
  {E : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hE : E.ShortExact)
  {E' : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1})} (hE' : E'.ShortExact)
  (σ : E.map (smallEtalePullbackAb e) ⟶ E')
  {𝒟 : Type*} [Category* 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
  (G : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ⥤ 𝒟) [G.CommShift ℤ]
  (H : 𝒟 ⥤ 𝒜) [H.ShiftSequence ℤ]

omit [Preadditive 𝒟] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  [Abelian 𝒜] in
/-- The naturality of the connecting morphism of the homology sequence of `H` along the image
under a functor `G` compatible with the shift of `pullbackTriangleHom σ`, with the triangle
`G(Re⁻¹(…))` read as the image under the composite `Re⁻¹ ⋙ G`. -/
theorem homologySequenceδ_map_pullbackTriangleHom :
    (H.shift (q : ℤ)).map (G.map (singlePullbackComp e σ.τ₃)) ≫
      H.homologySequenceδ (G.mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hE')) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl =
    H.homologySequenceδ (((smallEtalePullbackAb e).rightDerivedFunctorPlus ⋙ G).mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
      (H.shift ((q + 1 : ℕ) : ℤ)).map (G.map (singlePullbackComp e σ.τ₁)) := by
  have hnat := H.homologySequenceδ_naturality
    ((Functor.mapTriangleCompIso (smallEtalePullbackAb e).rightDerivedFunctorPlus G).hom.app
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ≫
      G.mapTriangle.map (pullbackTriangleHom e hE hE' σ)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl
  have h₁ : ((Functor.mapTriangleCompIso (smallEtalePullbackAb e).rightDerivedFunctorPlus
        G).hom.app (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ≫
      G.mapTriangle.map (pullbackTriangleHom e hE hE' σ)).hom₁ =
      G.map (singlePullbackComp e σ.τ₁) :=
    Category.id_comp _
  have h₃ : ((Functor.mapTriangleCompIso (smallEtalePullbackAb e).rightDerivedFunctorPlus
        G).hom.app (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ≫
      G.mapTriangle.map (pullbackTriangleHom e hE hE' σ)).hom₃ =
      G.map (singlePullbackComp e σ.τ₃) :=
    Category.id_comp _
  rwa [h₁, h₃] at hnat

end General

/-! ### The comparison of the identifications -/

section Paste

variable {X₀ X₁ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (u₁ : S₁ ⟶ S₀)
  (v₁ : X₁ ⟶ X₀) (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (u₂ : S₂ ⟶ S₁)

/-- The rearrangement behind `pullbackBaseChange_comp_baseChangeSourceIso`, in an abstract
category. -/
private theorem mid_algebra {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : C}
    (c : O₁ ⟶ O₂) (m : O₂ ⟶ O₃) (b₂ : O₃ ⟶ O₅) (bu : O₁ ⟶ O₆) (hc : O₆ ⟶ O₄)
    (hx : O₄ ⟶ O₅) (pb : O₂ ⟶ O₇) (ei : O₇ ⟶ O₄) (prd : O₃ ⟶ O₈) (px : O₇ ⟶ O₈)
    (ei' : O₈ ⟶ O₅) (h₁ : bu ≫ hc = c ≫ pb ≫ ei) (h₂ : m ≫ prd = pb ≫ px)
    (h₃ : b₂ = prd ≫ ei') (h₄ : px ≫ ei' = ei ≫ hx) :
    c ≫ m ≫ b₂ = bu ≫ hc ≫ hx := by
  rw [h₃, reassoc_of% h₂, h₄, reassoc_of% h₁]

/-- The sheaf-level rearrangement behind `pullbackBaseChange_comp_baseChangeSourceIso`, in an
abstract category. -/
private theorem mid_sheaf_algebra {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ : C}
    (bc : O₁ ⟶ O₂) (rs : O₂ ⟶ O₃) (rz : O₃ ⟶ O₄) (rv : O₂ ⟶ O₅) (hs : O₅ ⟶ O₄)
    (bs : O₁ ⟶ O₆) (hd : O₆ ⟶ O₇) (bt : O₂ ⟶ O₇) (hεh : O₅ ⟶ O₇) (hε' : O₇ ⟶ O₅)
    (hx : O₆ ⟶ O₄) (e₂ : bs ≫ hd = bc ≫ bt) (e₃ : bt = rv ≫ hεh) (e₃' : hεh ≫ hε' = 𝟙 _)
    (e₄ : rs ≫ rz = rv ≫ hs) (ex : hx = hd ≫ hε' ≫ hs) :
    bc ≫ rs ≫ rz = bs ≫ hx := by
  rw [e₄, ex, reassoc_of% e₂, e₃]
  simp only [Category.assoc]
  rw [reassoc_of% e₃']

variable (n : ℕ) {F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}}
  {Z : Sheaf (smallEtaleTopology X₁) Ab.{u + 1}} (s : (smallEtalePullbackAb v₁).obj F ⟶ Z)

/-- The sheaf-level half of `pullbackBaseChange_comp_baseChangeSourceIso`: the base change map
followed by `R^n g₁_* s`, read through the comparison of conventions for `R^n g₁_*`, is the
degree-`n` cohomology of the derived base change map followed by `Rg₁_*` of `s` in degree zero,
read through the identification of the source. -/
theorem higherBaseChangeMapAb_comp_rightDerivedIso :
    (higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ n).app F ≫
        ((smallEtalePushforwardAb g₁).rightDerived n).map s ≫
          (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₁) n).hom.app Z =
      (baseChangeSourceIso u₁ g₀ n).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₁) Ab.{u + 1})
          (n : ℤ)).map ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
            ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
              F) ≫
          (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map (singlePullbackComp v₁ s)) := by
  let Hn := DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₁) Ab.{u + 1})
    (n : ℤ)
  let Rg₁ := (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus
  let rD₁ := Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₁) n
  let ε := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso (smallEtalePullbackAb v₁) 0
  let sgl := DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₁) Ab.{u + 1}) 0
  let dBC := (smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
    ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F)
  have e₃' : Hn.map (Rg₁.map (ε.hom.app F)) ≫ Hn.map (Rg₁.map (ε.inv.app F)) = 𝟙 _ :=
    (Hn.map_comp _ _).symm.trans ((congrArg Hn.map ((Rg₁.map_comp _ _).symm.trans
      ((congrArg Rg₁.map (ε.hom_inv_id_app F)).trans (Rg₁.map_id _)))).trans (Hn.map_id _))
  have e₄ : ((smallEtalePushforwardAb g₁).rightDerived n).map s ≫ rD₁.hom.app Z =
      rD₁.hom.app ((smallEtalePullbackAb v₁).obj F) ≫ Hn.map (Rg₁.map (sgl.map s)) :=
    rD₁.hom.naturality s
  have ex : Hn.map (dBC ≫ Rg₁.map (singlePullbackComp v₁ s)) =
      Hn.map dBC ≫ Hn.map (Rg₁.map (ε.inv.app F)) ≫ Hn.map (Rg₁.map (sgl.map s)) :=
    (Hn.map_comp _ _).trans
      (Hn.map dBC ≫= (congrArg Hn.map (Rg₁.map_comp _ _)).trans (Hn.map_comp _ _))
  exact mid_sheaf_algebra _ _ _ _ _ _ _ _ _ _ _
    (baseChangeSourceIso_hom_app_comp u₁ g₀ g₁ v₁ w₁ n F)
    (baseChangeTargetIso_hom_app g₁ v₁ n F) e₃' e₄ ex

/-- **The comparison of the identifications.** The composition comparison of the inverse images
along `u₂ ≫ u₁`, followed by the inverse image along `u₂` of the base change map of the square
and of `R^n g₁_* s`, read through the identification of the source of the base change map along
`u₂`, is the identification of the source of the base change map along `u₂ ≫ u₁` followed by the
degree-`n` cohomology of the derived comparison `R((u₂ ≫ u₁)⁻¹) ≅ R(u₁⁻¹) ⋙ R(u₂⁻¹)` and of the
image under `R(u₂⁻¹)` of the derived base change map and of `Rg₁_* s`. -/
theorem pullbackBaseChange_comp_baseChangeSourceIso :
    (smallEtalePullbackAbCompIso u₂ u₁).inv.app
        (((smallEtalePushforwardAb g₀).rightDerived n).obj F) ≫
        (smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ n).app F ≫
          ((smallEtalePushforwardAb g₁).rightDerived n).map s) ≫
        (baseChangeSourceIso u₂ g₁ n).hom.app Z =
      (baseChangeSourceIso (u₂ ≫ u₁) g₀ n).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1})
          (n : ℤ)).map ((smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).inv.app
            ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
                F))) ≫
        (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1})
          (n : ℤ)).map ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
            ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
              ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
                F) ≫
            (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map
              (singlePullbackComp v₁ s))) := by
  let P := smallEtalePullbackAb u₂
  let Hn := DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₁) Ab.{u + 1})
    (n : ℤ)
  let eR := Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb u₂)
    (n : ℤ)
  let x := (smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
      ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F) ≫
    (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map (singlePullbackComp v₁ s)
  have Q := higherBaseChangeMapAb_comp_rightDerivedIso g₀ g₁ u₁ v₁ w₁ n s
  have h₂ : P.map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ n).app F ≫
        ((smallEtalePushforwardAb g₁).rightDerived n).map s) ≫
      P.map ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₁) n).hom.app Z) =
      P.map ((baseChangeSourceIso u₁ g₀ n).hom.app F) ≫ P.map (Hn.map x) :=
    (P.map_comp _ _).symm.trans ((congrArg P.map ((Category.assoc _ _ _).trans Q)).trans
      (P.map_comp _ _))
  have h₄ : P.map (Hn.map x) ≫ eR.inv.app _ = eR.inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1})
        (n : ℤ)).map ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map x) :=
    eR.inv.naturality x
  exact mid_algebra _ _ _ _ _ _ _ _ _ _ _ (source_paste g₀ u₁ u₂ n F) h₂
    (baseChangeSourceIso_hom_app u₂ g₁ n Z) h₄

/-- The transformation `Rg₀_* ⋙ R((u₂ ≫ u₁)⁻¹) ⟶ Rv₁⁻¹ ⋙ Rg₁_* ⋙ R(u₂⁻¹)`: the derived comparison
of the inverse images along `u₂ ≫ u₁`, followed by the image under `R(u₂⁻¹)` of the derived base
change map of the square. -/
def pasteDerivedTrans :
    derivedBaseChangeSource (u₂ ≫ u₁) g₀ ⟶
      (smallEtalePullbackAb v₁).rightDerivedFunctorPlus ⋙ derivedBaseChangeSource u₂ g₁ :=
  Functor.whiskerLeft (smallEtalePushforwardAb g₀).rightDerivedFunctorPlus
      (smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁)
      (smallEtalePullbackAb u₂).rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- The component of `pasteDerivedTrans` at `K` is the comparison of the derived inverse images
along `u₂ ≫ u₁` at `Rg₀_* K`, followed by the image under `R(u₂⁻¹)` of the derived base change
map at `K`. -/
theorem pasteDerivedTrans_app
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X₀) Ab.{u + 1})) :
    (pasteDerivedTrans g₀ g₁ u₁ v₁ w₁ u₂).app K =
      (smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).inv.app
          ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj K) ≫
        (smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
          ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app K) := by
  simp [pasteDerivedTrans]

/-- `pasteDerivedTrans` commutes with the shifts by `ℤ`. -/
instance natTransCommShift_pasteDerivedTrans :
    NatTrans.CommShift (pasteDerivedTrans g₀ g₁ u₁ v₁ w₁ u₂) ℤ := by
  have : NatTrans.CommShift (smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).hom ℤ :=
    Functor.natTransCommShift_rightDerivedFunctorPlusCompIsoOfExact _ _ _ _
  have : NatTrans.CommShift (smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁) ℤ :=
    commShift_smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁
  dsimp only [pasteDerivedTrans]
  infer_instance

section Connecting

variable (q : ℕ) {E : ShortComplex (Sheaf (smallEtaleTopology X₀) Ab.{u + 1})} (hE : E.ShortExact)
  {E' : ShortComplex (Sheaf (smallEtaleTopology X₁) Ab.{u + 1})} (hE' : E'.ShortExact)
  (σ : E.map (smallEtalePullbackAb v₁) ⟶ E')

/-- The naturality of the connecting morphism of the homology sequence along the derived
counterpart of the inverse image along `u₂` of the base change map followed by `R g₁_* σ`. -/
theorem homologySequenceδ_pasteDerived :
    ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) 0).shift
        (q : ℤ)).map ((pasteDerivedTrans g₀ g₁ u₁ v₁ w₁ u₂).app
          ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
            E.X₃) ≫ (derivedBaseChangeSource u₂ g₁).map (singlePullbackComp v₁ σ.τ₃)) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1})
          0).homologySequenceδ ((derivedBaseChangeSource u₂ g₁).mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hE')) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl =
    (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1})
          0).homologySequenceδ ((derivedBaseChangeSource (u₂ ≫ u₁) g₀).mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) 0).shift
        ((q + 1 : ℕ) : ℤ)).map ((pasteDerivedTrans g₀ g₁ u₁ v₁ w₁ u₂).app
          ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
            E.X₁) ≫ (derivedBaseChangeSource u₂ g₁).map (singlePullbackComp v₁ σ.τ₁)) := by
  have hA := Stacks.Triangulated.homologySequenceδ_natTrans
    (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) 0)
    (pasteDerivedTrans g₀ g₁ u₁ v₁ w₁ u₂)
    (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl
  have hB := homologySequenceδ_map_pullbackTriangleHom v₁ q hE hE' σ
    (derivedBaseChangeSource u₂ g₁)
    (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) 0)
  exact (Functor.map_comp _ _ _ =≫ _).trans
    ((Category.assoc _ _ _).trans ((_ ≫= hB).trans
      ((Category.assoc _ _ _).symm.trans ((hA =≫ _).trans
        ((Category.assoc _ _ _).trans (_ ≫= (Functor.map_comp _ _ _).symm))))))

/-- The degree-`n` cohomology of the derived counterpart, written through `pasteDerivedTrans`. -/
theorem homologyFunctor_map_pasteDerived (n : ℕ) {F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}}
    {Z : Sheaf (smallEtaleTopology X₁) Ab.{u + 1}} (s : (smallEtalePullbackAb v₁).obj F ⟶ Z) :
    (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1})
          (n : ℤ)).map ((smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).inv.app
            ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
                F))) ≫
        (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1})
          (n : ℤ)).map ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
            ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
              ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
                F) ≫
            (smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map (singlePullbackComp v₁ s))) =
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) 0).shift
        (n : ℤ)).map ((pasteDerivedTrans g₀ g₁ u₁ v₁ w₁ u₂).app
          ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj
            F) ≫ (derivedBaseChangeSource u₂ g₁).map (singlePullbackComp v₁ s)) := by
  rw [pasteDerivedTrans_app]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
  rfl

/-- The rearrangement behind `higherBaseChangeδSource_paste`, in an abstract category. -/
private theorem paste_δ_algebra {C : Type*} [Category* C]
    {A₃ B₃ K₃ L₃ M₃ A₁ B₁ K₁ L₁ M₁ : C}
    (c₃ : A₃ ⟶ B₃) (m₃ : B₃ ⟶ K₃) (b₃ : K₃ ⟶ L₃) (d' : L₃ ⟶ L₁) (b₁i : L₁ ⟶ K₁)
    (bu₃ : A₃ ⟶ M₃) (d : M₃ ⟶ M₁) (bu₁i : M₁ ⟶ A₁) (c₁ : A₁ ⟶ B₁) (m₁ : B₁ ⟶ K₁)
    (φ₃ : M₃ ⟶ L₃) (φ₁ : M₁ ⟶ L₁) (b₁ : K₁ ⟶ L₁) (bu₁ : A₁ ⟶ M₁)
    (h₁ : c₃ ≫ m₃ ≫ b₃ = bu₃ ≫ φ₃) (h₂ : c₁ ≫ m₁ ≫ b₁ = bu₁ ≫ φ₁) (h₃ : φ₃ ≫ d' = d ≫ φ₁)
    (i₁ : b₁ ≫ b₁i = 𝟙 _) (i₂ : bu₁i ≫ bu₁ = 𝟙 _) :
    c₃ ≫ m₃ ≫ b₃ ≫ d' ≫ b₁i = (bu₃ ≫ d ≫ bu₁i) ≫ c₁ ≫ m₁ := by
  have h₂' : c₁ ≫ m₁ = bu₁ ≫ φ₁ ≫ b₁i := by
    rw [← reassoc_of% h₂, i₁, Category.comp_id]
  rw [reassoc_of% h₁, reassoc_of% h₃, h₂']
  simp only [Category.assoc]
  rw [reassoc_of% i₂]

/-- **The connecting morphisms of the sources of the base change maps along `u₂ ≫ u₁` and along
`u₂` are compatible with the inverse image along `u₂` of the base change map of the square.**
For a short exact sequence `E` on `X₀`, a short exact sequence `E'` on `X₁` and a morphism
`σ : v₁⁻¹E ⟶ E'`, the inverse image along `u₂` of the base change map of the square followed
by `R g₁_* σ`, read through the composition comparison of the inverse images along `u₂ ≫ u₁`,
commutes with `higherBaseChangeδSource` along `u₂ ≫ u₁` and along `u₂`. -/
theorem higherBaseChangeδSource_paste :
    (smallEtalePullbackAbCompIso u₂ u₁).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived q).obj E.X₃) ≫
        (smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app E.X₃ ≫
          ((smallEtalePushforwardAb g₁).rightDerived q).map σ.τ₃) ≫
        higherBaseChangeδSource u₂ g₁ q hE' =
      higherBaseChangeδSource (u₂ ≫ u₁) g₀ q hE ≫
        (smallEtalePullbackAbCompIso u₂ u₁).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived (q + 1)).obj E.X₁) ≫
        (smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ (q + 1)).app E.X₁ ≫
          ((smallEtalePushforwardAb g₁).rightDerived (q + 1)).map σ.τ₁) := by
  have key := fun (n : ℕ) {F Z} (s : (smallEtalePullbackAb v₁).obj F ⟶ Z) =>
    (pullbackBaseChange_comp_baseChangeSourceIso g₀ g₁ u₁ v₁ w₁ u₂ n s).trans
      ((baseChangeSourceIso (u₂ ≫ u₁) g₀ n).hom.app F ≫=
        homologyFunctor_map_pasteDerived g₀ g₁ u₁ v₁ w₁ u₂ n s)
  exact paste_δ_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ (key q σ.τ₃) (key (q + 1) σ.τ₁)
    (homologySequenceδ_pasteDerived g₀ g₁ u₁ v₁ w₁ u₂ q hE hE' σ)
    ((baseChangeSourceIso u₂ g₁ (q + 1)).hom_inv_id_app E'.X₁)
    ((baseChangeSourceIso (u₂ ≫ u₁) g₀ (q + 1)).inv_hom_id_app E.X₁)

end Connecting

end Paste

end Stacks.EtaleCohomology

end
