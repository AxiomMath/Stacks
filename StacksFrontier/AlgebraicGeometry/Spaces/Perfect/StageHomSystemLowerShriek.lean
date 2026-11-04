module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationStageHomSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedStagesEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelDerivedPullbackSquarePaste
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfectPullback
public import StacksFrontier.CategoryTheory.Adjunction.InvertibleMateHomEquivStages

/-!
# Morphisms out of an extension by zero along the stages of a restricted limit

Let `D` be a situation of Stacks 09RH, `w : W₀ ⟶ X₀` a quasi-compact quasi-separated algebraic
space over the chosen stage and `y : Y₀ ⟶ W₀` an étale morphism from a quasi-compact
quasi-separated algebraic space. Restricting `D` to `W₀` and to `Y₀` gives the systems
`Wₖ = Xₖ ×_{X₀} W₀` and `Yₖ = Xₖ ×_{X₀} Y₀`. At a stage `i`, let `j : Yᵢ' ⟶ Wᵢ` be an étale
morphism which is a base change of `y` (a piece of the elementary distinguished square of the
stage `i`, say). For `A` perfect on `Yᵢ'` and `K` perfect on `Wᵢ`, the groups
`Hom(Lf_{ki}^*(j_! A), Lf_{ki}^* K)` are identified, compatibly with the transition maps and the
maps to the limit, with the groups `Hom(Lf_{Y,ki}^* A', Lf_{Y,ki}^* K')` of the restriction to
`Y₀` (`A'`, `K'` the pullbacks of `A`, `j^*K` to `Yᵢ`): by the base change of extension by zero
(the invertible mate of Stacks 03DT on the models) and the pasting of the squares of derived
pullbacks. So if morphisms of perfect objects descend in the restriction to `Y₀`, the filtered
colimit statement of Stacks 09RI holds for `j_! A` and `K` in the restriction to `W₀`
(`AlgebraicGeometry.Space.DescentSituation.stageHomSystem_isColimitAt_lowerShriek`).

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space

/-- If the isomorphisms `cA`, `cGA`, `cmA`, `dA` and `cB`, `cGB`, `cmB`, `dB` satisfy the cocycle
relations `hA` and `hB`, then conjugating `F.map y` by `cGA`, `cGB` and then by `cmA`, `cmB` equals
conjugating `F.map (cA.hom ≫ y ≫ cB.inv)` by `dA`, `dB`. This is the form in which the transition
maps of two systems of morphism groups related by composition isomorphisms agree. -/
theorem conj_conj_of_cocycle {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟)
    {GA HA GB HB : 𝒞} {G'A H'A G'B H'B : 𝒟} (cA : GA ≅ HA) (cB : GB ≅ HB)
    (cGA : F.obj HA ≅ H'A) (cGB : F.obj HB ≅ H'B) (cmA : G'A ≅ H'A) (cmB : G'B ≅ H'B)
    (dA : F.obj GA ≅ G'A) (dB : F.obj GB ≅ G'B)
    (hA : F.map cA.hom ≫ cGA.hom = dA.hom ≫ cmA.hom)
      (hB : F.map cB.hom ≫ cGB.hom = dB.hom ≫ cmB.hom)
    (y : HA ⟶ HB) :
    cmA.hom ≫ (cGA.inv ≫ F.map y ≫ cGB.hom) ≫ cmB.inv =
      dA.inv ≫ F.map (cA.hom ≫ y ≫ cB.inv) ≫ dB.hom := by
  have h₁ : cGB.hom ≫ cmB.inv = F.map cB.inv ≫ dB.hom := by
    rw [Iso.comp_inv_eq, Category.assoc, ← hB, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have h₂ : cmA.hom ≫ cGA.inv = dA.inv ≫ F.map cA.hom := by
    rw [Iso.eq_inv_comp, ← reassoc_of% hA, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% h₂, h₁]

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)
  {W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW₀ : IsAlgebraicSpace B S hS W₀)
  (hW₀qc : IsQuasiCompactSpace B S hS W₀) (hW₀qs : IsAbsolutelyQuasiSeparated B S hS hZ W₀)
  (w : W₀ ⟶ D.system.obj (op D.base))
  {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₀ : IsAlgebraicSpace B S hS Y₀)
  (hY₀qc : IsQuasiCompactSpace B S hS Y₀) (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
  (y : Y₀ ⟶ W₀)

/-- The morphism `Xₖ ×_{X₀} Y₀ ⟶ Xₖ ×_{X₀} W₀` from a stage of the restriction to `Y₀` to the
stage of the restriction to `W₀`. -/
def restrictStageHom (k : {i : I // D.base ≤ i}) :
    (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k),
        (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k),
        (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k⟩ :=
  ObjectProperty.homMk (baseChangeOverRestrict B S hS y w (D.system.map (homOfLE k.2).op))

/-- The morphism `X ×_{X₀} Y₀ ⟶ X ×_{X₀} W₀` between the limits of the restrictions. -/
def restrictLimitHom :
    (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
        (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.pt,
        (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace⟩ :=
  ObjectProperty.homMk (baseChangeOverRestrict B S hS y w (D.limitCone.π.app (op D.base)))

/-- The morphisms `restrictStageHom` commute with the transition maps `Yₘ ⟶ Yₖ` and
`Wₘ ⟶ Wₖ` of the restrictions to `Y₀` and `W₀`. -/
theorem restrictStageHom_comm {k m : {i : I // D.base ≤ i}} (h : k ≤ m) :
    (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m),
          (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k⟩) ≫
        D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k =
      D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y m ≫
        (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE h).op) :
          (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op m),
            (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace m⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k),
              (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k⟩) :=
  ObjectProperty.hom_ext _
    (baseChangeOverRestrict_comp_baseChangeOverMap B S hS y w _ _ _
      ((laterStagesToBaseStage D).naturality (homOfLE h).op |>.trans (Category.comp_id _))).symm

/-- The morphism `restrictLimitHom` of limits commutes with the projections to the stage `k` and
the morphism `restrictStageHom` at `k`. -/
theorem restrictLimitHom_comm (k : {i : I // D.base ≤ i}) :
    (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k)) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
          (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k⟩) ≫
        D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k =
      D.restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y ≫
        (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.π.app (op k)) :
          (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.pt,
            (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k),
              (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k⟩) :=
  ObjectProperty.hom_ext _
    (baseChangeOverRestrict_comp_baseChangeOverMap B S hS y w _ _ _
      (limitCone_π_comp_laterStagesToBaseStage D (op k))).symm

/-- The base change `X ×_{X₀} Y₀ ⟶ X ×_{X₀} W₀` of an étale `y` is étale. -/
private theorem isEtale_baseChangeOverRestrict (hW₀ : IsAlgebraicSpace B S hS W₀)
    (hY₀ : IsAlgebraicSpace B S hS Y₀) (hy : IsEtale B S hS y)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ D.system.obj (op D.base))
    (hP : IsAlgebraicSpace B S hS (pullback p (y ≫ w)))
    (hQ : IsAlgebraicSpace B S hS (pullback p w)) :
    IsEtale B S hS (baseChangeOverRestrict B S hS y w p) :=
  isEtale_of_isPullback B S hS
    (ObjectProperty.homMk (pullback.snd _ _) : (⟨_, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY₀⟩)
    _ (ObjectProperty.homMk y : (⟨Y₀, hY₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W₀, hW₀⟩)
    (ObjectProperty.homMk (pullback.snd _ _) : (⟨_, hQ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W₀, hW₀⟩)
    (IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (isPullback_baseChangeOverRestrict B S hS y w _).flip) hy

/-- If `y` is étale, then so is its base change `Yₖ ⟶ Wₖ`. -/
theorem isEtale_restrictStageHom (hy : IsEtale B S hS y) (k : {i : I // D.base ≤ i}) :
    IsEtale B S hS (D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k).hom :=
  D.isEtale_baseChangeOverRestrict w y hW₀ hY₀ hy _
    ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k)
    ((D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k)

/-- If `y` is étale, then so is its base change `X ×_{X₀} Y₀ ⟶ X ×_{X₀} W₀`. -/
theorem isEtale_restrictLimitHom (hy : IsEtale B S hS y) :
    IsEtale B S hS (D.restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y).hom :=
  D.isEtale_baseChangeOverRestrict w y hW₀ hY₀ hy _
    (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace
    (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace

variable (i : {i : I // D.base ≤ i}) {Yᵢ : AlgebraicSpaces B S hS}
    (j : Yᵢ ⟶
      (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
          (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS))
  (q : Yᵢ.1 ⟶ Y₀) (hY : IsPullback j.hom q (pullback.snd (D.system.map (homOfLE i.2).op) w) y)

/-- The comparison from the stage `i` of the restriction to `Y₀` to a base change `Yᵢ` of `y`
over the stage `i` of the restriction to `W₀`. -/
def restrictStageToPiece :
    (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
        (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ : AlgebraicSpaces B S hS) ⟶ Yᵢ :=
  ObjectProperty.homMk (hY.lift (baseChangeOverRestrict B S hS y w (D.system.map (homOfLE i.2).op))
    (pullback.snd _ _) (baseChangeOverRestrict_snd B S hS y w _))

/-- The morphism from a stage `k ≥ i` of the restriction to `Y₀` to `Yᵢ`. -/
def pieceStageHom (k : {k // i ≤ k}) :
    (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
        (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS) ⟶ Yᵢ :=
  (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE k.2).op) :
      (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
          (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
          (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ : AlgebraicSpaces B S hS)) ≫
    D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY

/-- The morphism from the limit of the restriction to `Y₀` to `Yᵢ`. -/
def pieceLimitHom :
    (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
        (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
    Yᵢ :=
  (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op i)) :
      (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
          (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
          (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ : AlgebraicSpaces B S hS)) ≫
    D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY

/-- The morphisms `pieceStageHom` are compatible with the transition maps `Yₘ ⟶ Yₖ` of the
restriction to `Y₀`. -/
theorem pieceStageHom_trans {k m : {k // i ≤ k}} (h : k ≤ m) :
    (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) ≫
        D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k =
          D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY m := by
  rw [pieceStageHom, pieceStageHom, ← Category.assoc]
  congr 1
  exact ObjectProperty.hom_ext _ ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map_comp _ _).symm

/-- The morphism `pieceLimitHom` is the composite of the projection of the limit to the stage `k`
with `pieceStageHom` at `k`. -/
theorem pieceLimitHom_trans (k : {k // i ≤ k}) :
    (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k.1)) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) ≫
        D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k =
          D.pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY := by
  rw [pieceStageHom, pieceLimitHom, ← Category.assoc]
  congr 1
  exact ObjectProperty.hom_ext _ ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.w _)

/-- For `k ≥ i`, the square formed by `restrictStageHom`, `pieceStageHom`, the transition map
`Wₖ ⟶ Wᵢ` and `j` is a pullback square. -/
theorem isPullback_pieceStageHom (k : {k // i ≤ k}) :
    IsPullback (D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k.1)
      (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
      (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE k.2).op) :
          (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
              (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
              (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS)) j :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    (isPullback_baseChangeOverMap_comp_lift B S hS y w _ _ _
      ((laterStagesToBaseStage D).naturality (homOfLE k.2).op |>.trans (Category.comp_id _)) j.hom q
        hY)

/-- The square formed by `restrictLimitHom`, `pieceLimitHom`, the projection of the limit of the
restriction to `W₀` to the stage `i`, and `j` is a pullback square. -/
theorem isPullback_pieceLimitHom :
    IsPullback (D.restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y)
      (D.pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY)
      (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.π.app (op i)) :
          (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.pt,
              (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
              (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS)) j :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    (isPullback_baseChangeOverMap_comp_lift B S hS y w _ _ _
      (limitCone_π_comp_laterStagesToBaseStage D (op i)) j.hom q hY)

/-- For `i ≤ k ≤ m`, the transition maps `Yₘ ⟶ Yₖ ⟶ Yᵢ` of the restriction to `Y₀` compose to
the transition map `Yₘ ⟶ Yᵢ`. -/
theorem restrictY_map_comp {k m : {k // i ≤ k}} (h : k ≤ m) :
    (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE k.2).op) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ :
              AlgebraicSpaces B S hS)) =
      ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE m.2).op) :=
  ObjectProperty.hom_ext _ ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map_comp _ _).symm

/-- For `i ≤ k`, the projection of the limit of the restriction to `Y₀` to the stage `k`, followed
by the transition map `Yₖ ⟶ Yᵢ`, is the projection to the stage `i`. -/
theorem restrictY_limit_comp (k : {k // i ≤ k}) :
    (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k.1)) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE k.2).op) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ :
              AlgebraicSpaces B S hS)) =
      ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op i)) :=
  ObjectProperty.hom_ext _ ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.w _)

/-- The square of derived pullbacks between the stage `k` and the stage `i`, around `j`. -/
abbrev pieceSquare (k : {k // i ≤ k}) :=
  spacesEtaleModelDerivedPullbackSquare B S hS
    (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE k.2).op) :
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
            (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
            (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS))
    (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k) j
      (D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k.1)
    (D.isPullback_pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k).w.symm

/-- The square of derived pullbacks between the limit and the stage `i`, around `j`. -/
abbrev pieceLimitSquare :=
  spacesEtaleModelDerivedPullbackSquare B S hS
    (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.π.app (op i)) :
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.pt,
            (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
            (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS))
    (D.pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) j
      (D.restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y)
    (D.isPullback_pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY).w.symm

/-- The components of the square of derived pullbacks `pieceSquare` are isomorphisms. -/
instance isIso_pieceSquare_app (k : {k // i ≤ k})
    (Z : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS)).O))) :
    IsIso ((D.pieceSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k).app Z) := by
  rw [pieceSquare, spacesEtaleModelDerivedPullbackSquare_app]
  infer_instance

/-- The components of the square of derived pullbacks `pieceLimitSquare` are isomorphisms. -/
instance isIso_pieceLimitSquare_app
    (Z : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS)).O))) :
    IsIso ((D.pieceLimitSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY).app Z) := by
  rw [pieceLimitSquare, spacesEtaleModelDerivedPullbackSquare_app]
  infer_instance

/-- The transition maps of the morphisms `Lh_k^* X ⟶ Lh_k^* Z` along the stages `k ≥ i`, for the
morphisms `h_k` from the stages of the restriction to `Y₀` to `Yᵢ`. -/
def pieceRaise
    (X Z : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Yᵢ).O)))
    (k m : {k // i ≤ k}) (h : k ≤ m)
    (z : (derivedPullback
          (spacesEtaleModelHom B S hS
            (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k))).obj X ⟶
      (derivedPullback
          (spacesEtaleModelHom B S hS
            (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k))).obj Z) :
    (derivedPullback
        (spacesEtaleModelHom B S hS
          (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY m))).obj X ⟶
      (derivedPullback
          (spacesEtaleModelHom B S hS
            (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY m))).obj Z :=
  (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS))
      (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
        (D.pieceStageHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY h) X).inv ≫
    (derivedPullback
        (spacesEtaleModelHom B S hS
          ((ObjectProperty.homMk
              ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
              (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m.1),
                  (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m.1⟩ :
                AlgebraicSpaces B S hS) ⟶
              (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                  (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
                AlgebraicSpaces B S hS))))).map z ≫
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
        (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
          (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m.1),
              (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
              (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS))
      (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
        (D.pieceStageHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY h) Z).hom

/-- The maps to the limit of the morphisms `Lh_k^* X ⟶ Lh_k^* Z`. -/
def pieceLim
    (X Z : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Yᵢ).O)))
    (k : {k // i ≤ k})
    (z : (derivedPullback
          (spacesEtaleModelHom B S hS
            (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k))).obj X ⟶
      (derivedPullback
          (spacesEtaleModelHom B S hS
            (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k))).obj Z) :
    (derivedPullback
        (spacesEtaleModelHom B S hS
          (D.pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY))).obj X ⟶
      (derivedPullback
        (spacesEtaleModelHom B S hS
          (D.pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY))).obj Z :=
  (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k.1)) :
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
            (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS))
      (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
        (D.pieceLimitHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k) X).inv ≫
    (derivedPullback
        (spacesEtaleModelHom B S hS
          ((ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k.1)) :
              (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
                  (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ :
                AlgebraicSpaces B S hS) ⟶
              (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                  (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
                AlgebraicSpaces B S hS))))).map z ≫
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
        (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k.1)) :
          (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
              (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
              (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS))
      (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
        (D.pieceLimitHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k) Z).hom

/-- **The stages of the restriction to `Y₀`, read on `Yᵢ`.** If morphisms of perfect objects
descend in the restriction to `Y₀`, the groups `Hom(Lh_k^* A, Lh_k^* Z)` for perfect `A`, `Z` on
`Yᵢ` have `Hom(Lh^* A, Lh^* Z)` at the limit as filtered colimit. -/
theorem isStagesColimit_pieceRaise
    (hFFY : (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).PerfectHomsDescend)
    (X Z : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Yᵢ).O)))
    (hX : (spacesEtaleModelRingedSite B S hS Yᵢ).IsPerfect X)
    (hZ' : (spacesEtaleModelRingedSite B S hS Yᵢ).IsPerfect Z) :
    Stacks.IsStagesColimit (I := {k // i ≤ k})
      (fun k m h z => D.pieceRaise hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY X Z k m h z)
      (fun k z => D.pieceLim hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY X Z k z) := by
  have key := PerfectHomsDescend.isStagesColimit _ hFFY i.2
    (isPerfect_derivedPullback_spacesEtaleModelHom
        (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) X hX)
    (isPerfect_derivedPullback_spacesEtaleModelHom
        (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) Z hZ')
  refine Stacks.IsStagesColimit.ofEquiv _ _
    (fun k =>
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (ObjectProperty.homMk
            ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE k.2).op) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ : AlgebraicSpaces B S hS))
        (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) rfl X).symm.homCongr
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (ObjectProperty.homMk
            ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE k.2).op) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ : AlgebraicSpaces B S hS))
        (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) rfl Z).symm)
    ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op i)) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ : AlgebraicSpaces B S hS))
        (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) rfl X).symm.homCongr
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op i)) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op i),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace i⟩ : AlgebraicSpaces B S hS))
        (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) rfl Z).symm)
    ?_ ?_ key
  · intro k m h z
    simp only [raiseStageHom]
    have c := fun W => spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS _ _
      (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY)
      (D.restrictY_map_comp (w := w) (hY₀ := hY₀) (hY₀qc := hY₀qc) (hY₀qs := hY₀qs) (y := y) i h)
      rfl rfl (D.pieceStageHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY h) W
    exact conj_conj_of_cocycle _ _ _ _ _ _ _ _ _ (c X) (c Z) z
  · intro k z
    simp only [limitStageHom]
    have c := fun W => spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS _ _
      (D.restrictStageToPiece hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY)
      (D.restrictY_limit_comp (w := w) (hY₀ := hY₀) (hY₀qc := hY₀qc) (hY₀qs := hY₀qs) (y := y) i k)
      rfl rfl (D.pieceLimitHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k) W
    exact conj_conj_of_cocycle _ _ _ _ _ _ _ _ _ (c X) (c Z) z

/-- For `i ≤ k ≤ m`, the transition maps `Wₘ ⟶ Wₖ ⟶ Wᵢ` of the restriction to `W₀` compose to
the transition map `Wₘ ⟶ Wᵢ`. -/
theorem restrictW_map_comp {k m : {k // i ≤ k}} (h : k ≤ m) :
    (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE h).op) :
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op m.1),
            (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace m.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
            (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE k.2).op) :
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS)) =
      ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE m.2).op) :=
  ObjectProperty.hom_ext _ ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map_comp _ _).symm

/-- For `i ≤ k`, the projection of the limit of the restriction to `W₀` to the stage `k`, followed
by the transition map `Wₖ ⟶ Wᵢ`, is the projection to the stage `i`. -/
theorem restrictW_limit_comp (k : {k // i ≤ k}) :
    (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.π.app (op k.1)) :
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.pt,
            (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
            (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE k.2).op) :
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS)) =
      ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.π.app (op i)) :=
  ObjectProperty.hom_ext _ ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.w _)

/-- The base change morphism of extension by zero along a cartesian square of étale morphisms is
invertible at `A`. -/
private theorem isIso_app_mateEquiv_symm_pieceSquare {Y W Y' W' : AlgebraicSpaces B S hS}
    {j : Y ⟶ W} {j' : Y' ⟶ W'} {g : W' ⟶ W} {h : Y' ⟶ Y} (hj : IsEtale B S hS j.hom)
    (hj' : IsEtale B S hS j'.hom) (sq : IsPullback j' h g j)
    (A : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS Y).O))) :
    IsIso (((mateEquiv (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j hj)
      (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j' hj')).symm
        (spacesEtaleModelDerivedPullbackSquare B S hS g h j j' sq.w.symm)).app A) :=
  haveI := isIso_mateEquiv_symm_spacesEtaleModelDerivedLowerShriekAdjunction B S hS _ _ j _
    sq.w.symm hj hj' sq
  NatIso.isIso_app_of_isIso _ A

include q hY in
/-- **Morphisms out of an extension by zero along the stages of a restricted limit.** If morphisms
of perfect objects descend in the restriction of `D` to an étale `y : Y₀ ⟶ W₀`, and `j : Yᵢ ⟶ Wᵢ`
is an étale base change of `y` over the stage `i` of the restriction to `W₀`, then for `A` perfect
on `Yᵢ` and `K` perfect on `Wᵢ` the group `Hom(Lfᵢ^*(j_! A), Lfᵢ^* K)` is the filtered colimit of
the groups `Hom(Lf_{ki}^*(j_! A), Lf_{ki}^* K)`, `k ≥ i`. -/
theorem stageHomSystem_isColimitAt_lowerShriek
    (hFFY : (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).PerfectHomsDescend)
    (hy : IsEtale B S hS y) (hj : IsEtale B S hS j.hom)
      (A : DerivedCategory
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Yᵢ).O)))
    (hA : (spacesEtaleModelRingedSite B S hS Yᵢ).IsPerfect A)
      (K : DerivedCategory
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleModelRingedTopos B S hS
              (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
                  (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS)).O)))
    (hK : (spacesEtaleModelRingedSite B S hS
          (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
              (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ :
            AlgebraicSpaces B S hS)).IsPerfect K) :
    ((D.restrictTo hW₀ hW₀qc hW₀qs w).stageHomSystem i).IsColimitAt
      ((spacesEtaleModelDerivedLowerShriek B S hS j hj).obj A) K := by
  have key := D.isStagesColimit_pieceRaise hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY hFFY A
    ((derivedPullback (spacesEtaleModelHom B S hS j)).obj K) hA
    (isPerfect_derivedPullback_spacesEtaleModelHom j K hK)
  refine Stacks.IsStagesColimit.ofEquiv
    (fun (k m : {k // i ≤ k}) (h : k ≤ m) x => (D.restrictTo hW₀ hW₀qc hW₀qs w).raiseStageHom k.2 h
      x)
    (fun (k : {k // i ≤ k}) x => (D.restrictTo hW₀ hW₀qc hW₀qs w).limitStageHom k.2 x)
    (fun k =>
      haveI := isIso_app_mateEquiv_symm_pieceSquare hj
        (D.isEtale_restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y hy k.1)
        (D.isPullback_pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k) A
      Equiv.ofBijective _ (Adjunction.stageMateHom_bijective
        (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j hj)
          (D.pieceSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
        (spacesEtaleModelDerivedLowerShriekAdjunction B S hS
            (D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k.1)
          (D.isEtale_restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y hy k.1)) A K))
    (haveI := isIso_app_mateEquiv_symm_pieceSquare hj
        (D.isEtale_restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y hy)
        (D.isPullback_pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY) A
     Equiv.ofBijective _ (Adjunction.stageMateHom_bijective
       (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j hj)
         (D.pieceLimitSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY)
       (spacesEtaleModelDerivedLowerShriekAdjunction B S hS
           (D.restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y)
         (D.isEtale_restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y hy)) A K)) ?_ ?_ key
  · intro k m h x
    exact Adjunction.stageMateHom_comp (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j hj)
      (D.pieceSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
      (spacesEtaleModelDerivedPullbackSquare B S hS
        (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).system.map (homOfLE h).op) :
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op m.1),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace m.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS))
        (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m.1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS))
        (D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k.1)
          (D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y m.1)
        (D.restrictStageHom_comm hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y (k := k.1) (m := m.1) h))
      (D.pieceSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY m)
      (fun X => spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.map (homOfLE h).op) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op m.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace m.1⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS))
        (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
          (D.pieceStageHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY h) X)
      (fun Z => (D.restrictTo hW₀ hW₀qc hW₀qs w).stageTransitionDerivedPullbackIso k.2 h Z) A K
      (fun X Y φ => spacesEtaleModelDerivedPullbackCompIsoOfEq_hom_naturality B S hS _ _ _ φ)
      (fun Z => spacesEtaleModelDerivedPullbackSquare_paste B S hS j _ _ _ _ _ _
        (D.restrictW_map_comp (hW₀ := hW₀) (hW₀qc := hW₀qc) (hW₀qs := hW₀qs) (w := w) i h)
        (D.pieceStageHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY h)
        (D.isPullback_pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k).w.symm
        (D.restrictStageHom_comm hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y (k := k.1) (m := m.1) h)
        (D.isPullback_pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY m).w.symm Z) x
  · intro k x
    exact Adjunction.stageMateHom_comp (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j hj)
      (D.pieceSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
      (spacesEtaleModelDerivedPullbackSquare B S hS
        (ObjectProperty.homMk ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.π.app (op k.1)) :
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).limitCone.pt,
                (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op k.1),
                (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k.1⟩ : AlgebraicSpaces B S hS))
        (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k.1)) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS))
        (D.restrictStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k.1)
          (D.restrictLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y)
        (D.restrictLimitHom_comm hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k.1))
      (D.pieceLimitSquare hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY)
      (fun X => spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (ObjectProperty.homMk ((D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.π.app (op k.1)) :
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitCone.pt,
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).limitAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).system.obj (op k.1),
                (D.restrictTo hY₀ hY₀qc hY₀qs (y ≫ w)).algebraicSpace k.1⟩ :
              AlgebraicSpaces B S hS))
        (D.pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
          (D.pieceLimitHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k) X)
      (fun Z => (D.restrictTo hW₀ hW₀qc hW₀qs w).stageProjectionDerivedPullbackIso k.2 Z) A K
      (fun X Y φ => spacesEtaleModelDerivedPullbackCompIsoOfEq_hom_naturality B S hS _ _ _ φ)
      (fun Z => spacesEtaleModelDerivedPullbackSquare_paste B S hS j _ _ _ _ _ _
        (D.restrictW_limit_comp (hW₀ := hW₀) (hW₀qc := hW₀qc) (hW₀qs := hW₀qs) (w := w) i k)
        (D.pieceLimitHom_trans hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k)
        (D.isPullback_pieceStageHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY k).w.symm
        (D.restrictLimitHom_comm hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y k.1)
        (D.isPullback_pieceLimitHom hW₀ hW₀qc hW₀qs w hY₀ hY₀qc hY₀qs y i j q hY).w.symm Z) x

end DescentSituation

end AlgebraicGeometry.Space
