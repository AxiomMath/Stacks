module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.StructureSharpDominance
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringAtlas

/-!
# Morphisms out of the target of a contraction descend along coverings of the base

Let `Q` be a scheme of the site, `f : X ⟶ Q`, `g₁ : Y₁ ⟶ Q`, `g₂ : Y₂ ⟶ Q` algebraic spaces over
`Q` with `Y₂` separated, and `cᵢ : X ⟶ Yᵢ` morphisms over `Q` such that every base change of `c₁`
along a scheme `T ⟶ Q` has `𝒪_{Y₁,T} = c₁,T,*𝒪_{X_T}`. Given an fpqc covering `{Wᵢ ⟶ Q}` and, over
each `Wᵢ`, a morphism `ψᵢ : Y₁ ×_Q Wᵢ ⟶ Y₂` over `Q` with `c₁,Wᵢ ≫ ψᵢ = c₂` on `X ×_Q Wᵢ`, the `ψᵢ`
glue to a morphism `Ψ : Y₁ ⟶ Y₂` over `Q` with `c₁ ≫ Ψ = c₂`.

The `ψᵢ` agree on the overlaps because on `Y₁ ×_Q (Wᵢ ×_Q Wⱼ)` the two restrictions agree after
the base change of `c₁`, whose structure map is an isomorphism, so that morphisms out of its
target into the separated `Y₂` are determined after it
(`AlgebraicGeometry.Space.eq_of_comp_eq_of_isIso_structureSharp`); then they descend along the
fpqc covering `{Y₁ ×_Q Wᵢ ⟶ Y₁}` (Stacks 04P2). This is how the local isomorphisms of Stacks 0E89
give the uniqueness in Stacks 0E8A, and how its étale-local contractions are compared.

## Main results

* `AlgebraicGeometry.Space.exists_desc_of_isFpqcCovering_of_isIso_structureSharp`

## References

* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ContractionDescentAlongCovering :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ContractionDescentAlongCovering
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base change of an fpqc covering, presented by given cartesian squares, is an fpqc
covering. -/
private theorem isFpqcCovering_of_isPullback_squares {I : Type v} {Y : AlgebraicSpaces B S hS}
    {Yi : I → AlgebraicSpaces B S hS} (g : ∀ i, Yi i ⟶ Y)
    (hg : IsFpqcCovering B S hS fun i => (g i).hom) {X : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {Xi : I → AlgebraicSpaces B S hS} (f' : ∀ i, Xi i ⟶ Yi i) (g' : ∀ i, Xi i ⟶ X)
    (hpb : ∀ i, IsPullback (g' i) (f' i) f (g i)) :
    IsFpqcCovering B S hS fun i => (g' i).hom := by
  have h₁ := isFpqcCovering_pullback_fst B S hS Yi g hg X f
  have h₂ := isFpqcCovering_isoComp B S hS (fun i => ((hpb i).isoPullback.hom).hom)
    (fun i => (pullback.fst f (g i)).hom) h₁
  convert h₂ using 2 with i
  exact congrArg (fun k : Xi i ⟶ X => k.hom) (hpb i).isoPullback_hom_fst.symm

/-- **Morphisms out of the target of a contraction descend along fpqc coverings of the base.**
Let `f : X ⟶ Q`, `g₁ : Y₁ ⟶ Q`, `g₂ : Y₂ ⟶ Q` be algebraic spaces over a scheme `Q` of the site,
with `g₂` separated, and `cᵢ : X ⟶ Yᵢ` morphisms over `Q` such that the base change of `c₁` along
every scheme `T ⟶ Q` has structure map an isomorphism. Let `{φᵢ : Wᵢ ⟶ Q}` be an fpqc covering,
`X'ᵢ`, `Y'ᵢ` the base changes of `X`, `Y₁` along `φᵢ`, with `c'ᵢ : X'ᵢ ⟶ Y'ᵢ` induced by `c₁`, and
`ψᵢ : Y'ᵢ ⟶ Y₂` morphisms over `Q` with `c'ᵢ ≫ ψᵢ = (X'ᵢ ⟶ X) ≫ c₂`. Then there is a morphism
`Ψ : Y₁ ⟶ Y₂` over `Q` with `c₁ ≫ Ψ = c₂` restricting to every `ψᵢ`. -/
theorem exists_desc_of_isFpqcCovering_of_isIso_structureSharp
    {I : Type v} {Q : BigFppfOver B S hS} {W : I → BigFppfOver B S hS} (φ : ∀ i, W i ⟶ Q)
    (hφ : IsFpqcCovering B S hS (fun i => (schemeSpaceMap (φ i)).hom))
    {X Y₁ Y₂ : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace Q) (g₁ : Y₁ ⟶ schemeSpace Q)
    (g₂ : Y₂ ⟶ schemeSpace Q) (hg₂ : IsSeparated B S hS g₂.hom)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = f) (_hc₂ : c₂ ≫ g₂ = f)
    (hdom : ∀ (T : BigFppfOver B S hS) (h : T ⟶ Q),
      IsIso (structureSharp B S hS
        (structureContractionBaseChange B S hS c₁ hc₁ (schemeSpaceMap h))))
    {X' Y' : I → AlgebraicSpaces B S hS} (pX : ∀ i, X' i ⟶ X)
    (fX : ∀ i, X' i ⟶ schemeSpace (W i))
    (hpX : ∀ i, IsPullback (pX i) (fX i) f (schemeSpaceMap (φ i)))
    (pY : ∀ i, Y' i ⟶ Y₁) (fY : ∀ i, Y' i ⟶ schemeSpace (W i))
    (hpY : ∀ i, IsPullback (pY i) (fY i) g₁ (schemeSpaceMap (φ i)))
    (c' : ∀ i, X' i ⟶ Y' i) (hc'p : ∀ i, c' i ≫ pY i = pX i ≫ c₁)
    (hc'f : ∀ i, c' i ≫ fY i = fX i)
    (ψ : ∀ i, Y' i ⟶ Y₂) (hψg : ∀ i, ψ i ≫ g₂ = fY i ≫ schemeSpaceMap (φ i))
    (hψc : ∀ i, c' i ≫ ψ i = pX i ≫ c₂) :
    ∃ Ψ : Y₁ ⟶ Y₂, Ψ ≫ g₂ = g₁ ∧ c₁ ≫ Ψ = c₂ ∧ ∀ i, pY i ≫ Ψ = ψ i := by
  have hcovY : IsFpqcCovering B S hS (fun i => (pY i).hom) :=
    isFpqcCovering_of_isPullback_squares (fun i => schemeSpaceMap (φ i)) hφ g₁ fY pY hpY
  have hcovX : IsFpqcCovering B S hS (fun i => (pX i).hom) :=
    isFpqcCovering_of_isPullback_squares (fun i => schemeSpaceMap (φ i)) hφ f fX pX hpX
  -- the restrictions agree on the overlaps
  have hagree : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (pY i).hom (pY j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (pY i) (pY j) ⟶ Y' i) ≫ ψ i =
      (ObjectProperty.homMk (pullback.snd (pY i).hom (pY j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (pY i) (pY j) ⟶ Y' j) ≫ ψ j := by
    intro i j
    set E := AlgebraicSpaces.fiberProduct B S hS (pY i) (pY j)
    set e₁ : E ⟶ Y' i := ObjectProperty.homMk (pullback.fst (pY i).hom (pY j).hom)
    set e₂ : E ⟶ Y' j := ObjectProperty.homMk (pullback.snd (pY i).hom (pY j).hom)
    have hE : e₁ ≫ pY i = e₂ ≫ pY j :=
      (AlgebraicSpaces.isPullback_fiberProduct B S hS (pY i) (pY j)).w
    -- the overlap of the two members
    let T := pullback (φ i) (φ j)
    let t₁ : T ⟶ W i := pullback.fst (φ i) (φ j)
    let t₂ : T ⟶ W j := pullback.snd (φ i) (φ j)
    let hT : T ⟶ Q := t₁ ≫ φ i
    have ht : t₂ ≫ φ j = hT := (pullback.condition).symm
    have hTsq : IsPullback (schemeSpaceMap t₁) (schemeSpaceMap t₂) (schemeSpaceMap (φ i))
        (schemeSpaceMap (φ j)) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _)
        ((IsPullback.of_hasPullback (φ i) (φ j)).map yoneda)
    -- the base changes of `X` and `Y₁` to the overlap
    let YT := AlgebraicSpaces.fiberProduct B S hS g₁ (schemeSpaceMap hT)
    let yT₁ : YT ⟶ Y₁ := ObjectProperty.homMk (pullback.fst g₁.hom (schemeSpaceMap hT).hom)
    let yT₂ : YT ⟶ schemeSpace T := ObjectProperty.homMk
      (pullback.snd g₁.hom (schemeSpaceMap hT).hom)
    have hYT := AlgebraicSpaces.isPullback_fiberProduct B S hS g₁ (schemeSpaceMap hT)
    let XT := AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap hT)
    let xT₁ : XT ⟶ X := ObjectProperty.homMk (pullback.fst f.hom (schemeSpaceMap hT).hom)
    let xT₂ : XT ⟶ schemeSpace T := ObjectProperty.homMk
      (pullback.snd f.hom (schemeSpaceMap hT).hom)
    have hXT := AlgebraicSpaces.isPullback_fiberProduct B S hS f (schemeSpaceMap hT)
    let cT := structureContractionBaseChange B S hS c₁ hc₁ (schemeSpaceMap hT)
    have hcT₁ : cT ≫ yT₁ = xT₁ ≫ c₁ := structureContractionBaseChange_fst B S hS c₁ hc₁ _
    have hcT₂ : cT ≫ yT₂ = xT₂ := structureContractionBaseChange_snd B S hS c₁ hc₁ _
    have hT₁ : schemeSpaceMap hT = schemeSpaceMap t₁ ≫ schemeSpaceMap (φ i) :=
      schemeSpaceMap_comp t₁ (φ i)
    have hT₂ : schemeSpaceMap hT = schemeSpaceMap t₂ ≫ schemeSpaceMap (φ j) := by
      rw [← ht]; exact schemeSpaceMap_comp t₂ (φ j)
    -- the maps from the overlap to the two members
    let rY₁ : YT ⟶ Y' i := (hpY i).lift yT₁ (yT₂ ≫ schemeSpaceMap t₁)
      (by rw [hYT.w, Category.assoc, ← hT₁])
    let rY₂ : YT ⟶ Y' j := (hpY j).lift yT₁ (yT₂ ≫ schemeSpaceMap t₂)
      (by rw [hYT.w, Category.assoc, ← hT₂])
    let rX₁ : XT ⟶ X' i := (hpX i).lift xT₁ (xT₂ ≫ schemeSpaceMap t₁)
      (by rw [hXT.w, Category.assoc, ← hT₁])
    let rX₂ : XT ⟶ X' j := (hpX j).lift xT₁ (xT₂ ≫ schemeSpaceMap t₂)
      (by rw [hXT.w, Category.assoc, ← hT₂])
    have hr₁ : cT ≫ rY₁ = rX₁ ≫ c' i := by
      apply (hpY i).hom_ext
      · rw [Category.assoc, (hpY i).lift_fst, hcT₁, Category.assoc, hc'p, ← Category.assoc,
          (hpX i).lift_fst]
      · rw [Category.assoc, (hpY i).lift_snd, ← Category.assoc, hcT₂, Category.assoc, hc'f,
          (hpX i).lift_snd]
    have hr₂ : cT ≫ rY₂ = rX₂ ≫ c' j := by
      apply (hpY j).hom_ext
      · rw [Category.assoc, (hpY j).lift_fst, hcT₁, Category.assoc, hc'p, ← Category.assoc,
          (hpX j).lift_fst]
      · rw [Category.assoc, (hpY j).lift_snd, ← Category.assoc, hcT₂, Category.assoc, hc'f,
          (hpX j).lift_snd]
    -- the two restrictions agree on the base change to the overlap
    have hab : rY₁ ≫ ψ i = rY₂ ≫ ψ j := by
      have := hdom T hT
      refine eq_of_comp_eq_of_isIso_structureSharp B S hS cT g₂ hg₂ ?_ ?_
      · simp only [Category.assoc, hψg]
        rw [← Category.assoc rY₁, (hpY i).lift_snd, ← Category.assoc rY₂, (hpY j).lift_snd,
          Category.assoc, Category.assoc, ← hT₁, ← hT₂]
      · rw [← Category.assoc, hr₁, Category.assoc, hψc, ← Category.assoc, (hpX i).lift_fst,
          ← Category.assoc, hr₂, Category.assoc, hψc, ← Category.assoc, (hpX j).lift_fst]
    -- the overlap of the members maps to the base change to the overlap
    let eT : E ⟶ schemeSpace T := hTsq.lift (e₁ ≫ fY i) (e₂ ≫ fY j) (by
      rw [Category.assoc, ← (hpY i).w, ← Category.assoc, hE, Category.assoc, (hpY j).w,
        Category.assoc])
    let eY : E ⟶ YT := hYT.lift (e₁ ≫ pY i) eT (by
      rw [Category.assoc, (hpY i).w, hT₁, ← Category.assoc, ← Category.assoc, hTsq.lift_fst])
    have he₁ : eY ≫ rY₁ = e₁ := by
      apply (hpY i).hom_ext
      · rw [Category.assoc, (hpY i).lift_fst, hYT.lift_fst]
      · rw [Category.assoc, (hpY i).lift_snd, ← Category.assoc, hYT.lift_snd, hTsq.lift_fst]
    have he₂ : eY ≫ rY₂ = e₂ := by
      apply (hpY j).hom_ext
      · rw [Category.assoc, (hpY j).lift_fst, hYT.lift_fst, hE]
      · rw [Category.assoc, (hpY j).lift_snd, ← Category.assoc, hYT.lift_snd, hTsq.lift_snd]
    rw [← he₁, ← he₂, Category.assoc, Category.assoc, hab]
  obtain ⟨Ψ, hΨ, -⟩ := existsUnique_desc_of_fpqcCovering B S hS pY hcovY Y₂ ψ hagree
  refine ⟨Ψ, ?_, ?_, hΨ⟩
  · -- `Ψ` lies over `Q`
    obtain ⟨k, -, hk⟩ := existsUnique_desc_of_fpqcCovering B S hS pY hcovY (schemeSpace Q)
      (fun i => pY i ≫ g₁) (fun i j => by
        rw [← Category.assoc, ← Category.assoc,
          (AlgebraicSpaces.isPullback_fiberProduct B S hS (pY i) (pY j)).w])
    refine (hk _ fun i => ?_).trans (hk _ fun i => rfl).symm
    rw [← Category.assoc, hΨ, hψg, (hpY i).w]
  · -- `c₁ ≫ Ψ = c₂`
    obtain ⟨k, -, hk⟩ := existsUnique_desc_of_fpqcCovering B S hS pX hcovX Y₂
      (fun i => pX i ≫ c₂) (fun i j => by
        rw [← Category.assoc, ← Category.assoc,
          (AlgebraicSpaces.isPullback_fiberProduct B S hS (pX i) (pX j)).w])
    refine (hk _ fun i => ?_).trans (hk _ fun i => rfl).symm
    rw [← Category.assoc, ← hc'p, Category.assoc, hΨ, hψc]

end AlgebraicGeometry.Space

end
