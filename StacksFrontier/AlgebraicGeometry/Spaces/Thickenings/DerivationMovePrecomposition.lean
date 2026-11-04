module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInclusionRestriction

/-!
# The action of [Stacks Project, Tag 0CK6] under precomposition with a morphism of thickenings

Let `(e₀, c) : (Z ⊂ X) ⟶ (W₀ ⊂ W)` be a morphism of first order thickenings over `T`, let
`θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` be `𝒪_Z`-linear, and let `(h, h') : (Z₂ ⊂ X₂) ⟶ (Z ⊂ X)` be a
morphism of first order thickenings.  Then `(h ≫ e₀, h' ≫ c)` is a morphism of first order
thickenings over `T`, and
`AlgebraicGeometry.Space.comp_derivationMove` proves
`h' ≫ (θ · c) = θ₂ · (h' ≫ c)`, where
`θ₂ : (h ≫ e₀)^*Ω_{W₀/T} ≅ h^*e₀^*Ω_{W₀/T} ⟶ h^*𝒞_{Z/X} ⟶ 𝒞_{Z₂/X₂}` is the pullback of `θ`
followed by the conormal map of the square ([Stacks Project, Tag 04CP]).  This is the
compatibility of the action of [Stacks Project, Tag 061C] with the restriction maps of the sheaves
involved.

The proof checks the three conditions characterizing `θ₂ · (h' ≫ c)`
(`AlgebraicGeometry.Space.eq_derivationMove`) on `h' ≫ (θ · c)`:
* the conormal maps agree, by the composition law of conormal maps ([Stacks Project, Tag 04G2]);
* the derivation clause, by Equation [Stacks Project, Tag 0619] under precomposition
  (`AlgebraicGeometry.Space.derivationFamilyOfHom_comp`), the restriction of the ideal inclusions
  (`AlgebraicGeometry.Space.restrictedSquareZeroValues_ι_conormalMap_restriction`) and the
  restriction of the transported comorphisms
  (`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_source`).

## Implementation notes

The composite `h ≫ e₀` is taken in `AlgebraicSpaces B S hS` throughout: that is the spelling of
the comparisons of [Stacks Project, Tag 03LU] and [Stacks Project, Tag 03G2] that the derivation
clause runs through.  The restriction of the transported comorphisms is restated in that spelling
at variables
(`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_source_algebraicSpaces`).

## References

* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X₂ X W T : AlgebraicSpaces B S hS} (Z₂ : ClosedSubspaces B S hS X₂.1)
  (Z : ClosedSubspaces B S hS X.1) (W₀ : ClosedSubspaces B S hS W.1) (h' : X₂ ⟶ X)
  (h : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X₂ Z₂ ≫ h' = h ≫ subspaceInclusion B S hS X Z)
  (q : W ⟶ T)
  (hZ₂ : IsFirstOrderThickening B S hS X₂ Z₂.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
  (hW : IsFirstOrderThickening B S hS W W₀.1)

include hsq in
/-- The square of a morphism of thickenings `(e₀, c)` precomposed with `(h, h')`, with the
composite `h ≫ e₀` taken in `AlgebraicSpaces B S hS`. -/
theorem comp_assoc_of_square_algebraicSpaces (c : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    subspaceInclusion B S hS X₂ Z₂ ≫ h' ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) ≫
        subspaceInclusion B S hS W W₀ :=
  comp_assoc_of_square_restricted B S hS Z₂ Z h' h hsq W₀ c e₀ hc

/-- `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_source` with the composite
`h ≫ e₀` taken in `AlgebraicSpaces B S hS`, the spelling of the comparison of iterated direct
images that follows it. -/
theorem restrictedSharpThroughThickening_comp_source_algebraicSpaces (c : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS Z₂ W₀ (h' ≫ c)
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
        (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c hc) =
      restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)) :=
  restrictedSharpThroughThickening_comp_source B S hS Z₂ Z h' h hsq W₀ c e₀ hc

section Core

variable (c b : X ⟶ W)
  (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (hb : subspaceInclusion B S hS X Z ≫ b = e₀ ≫ subspaceInclusion B S hS W W₀)

/-- **The conormal clause under precomposition.**  Two morphisms of thickenings `(e₀, c)` and
`(e₀, b)` with the same conormal map keep the same conormal map after precomposition with
`(h, h')`, by the composition law of conormal maps of [Stacks Project, Tag 04G2]. -/
theorem conormalMap_comp_source_eq
    (hcm : conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ b e₀ hb) :
    conormalMap B S hS Z₂ W₀ (h' ≫ c)
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
        (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c hc) =
      conormalMap B S hS Z₂ W₀ (h' ≫ b)
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
        (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq b hb) :=
  (conormalMap_comp_triangle B S hS (g := h') (g' := c) (Z := Z₂) (Z' := Z) (Z'' := W₀) (f := h)
      (f' := e₀) (hsq := hsq) (hsq' := hc)
      (fc := @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) (hfc := rfl)
      (hsqc := comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c hc)).trans
    ((congrArg (fun m ↦ (modulePullbackTriangle B S hS
        (rfl : h ≫ e₀ = @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)).hom.app
          (conormalModule B S hS W W₀) ≫
        (modulePullback B S hS h).map m ≫ conormalMap B S hS Z₂ Z h' h hsq) hcm).trans
      (conormalMap_comp_triangle B S hS (g := h') (g' := b) (Z := Z₂) (Z' := Z) (Z'' := W₀)
        (f := h) (f' := e₀) (hsq := hsq) (hsq' := hb)
        (fc := @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) (hfc := rfl)
        (hsqc := comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq b hb)).symm)

/-- Equation [Stacks Project, Tag 0619] under precomposition, followed by the inclusion of the
ideal of values: the derivation attached to `θ₂`, included in `(h ≫ e₀)_*(i₂^{-1}𝒪_{X₂})`, is
`ρ = (e₀)_*σ` (followed by the comparison of iterated direct images) of the derivation attached
to `θ`, included in `(e₀)_*(i^{-1}𝒪_X)`. -/
theorem ι_derivationFamilyOfHom_comp_source_eq
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (y : (structureRingSheaf B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)).obj.obj
      V) :
    (restrictedSquareZeroValues B S hS Z₂ W₀
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) hZ₂).ι
        (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q)
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
          (conormalModule B S hS X₂ Z₂)
          ((modulePullbackCompIso B S hS h e₀).inv.app
              (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ≫
            (modulePullback B S hS h).map θ ≫ conormalMap B S hS Z₂ Z h' h hsq) V y) =
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))).hom.app V
        ((restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
          (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
            (conormalModule B S hS X Z) θ V y)) :=
  (congrArg (restrictedSquareZeroValues B S hS Z₂ W₀
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) hZ₂).ι
      (derivationFamilyOfHom_comp B S hS (subspaceInclusion B S hS W W₀ ≫ q) h e₀
        (conormalModule B S hS X Z) (conormalModule B S hS X₂ Z₂) θ
        (conormalMap B S hS Z₂ Z h' h hsq) V y)).trans
    (restrictedSquareZeroValues_ι_conormalMap_restriction B S hS Z₂ Z W₀ h' h e₀ hsq hZ₂ hZ V
      (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
        (conormalModule B S hS X Z) θ V y))

/-- **The derivation clause under precomposition.**  If the transported comorphisms of `c` and
`b` differ by the derivation attached to `θ`, then those of `h' ≫ c` and `h' ≫ b` differ by the
derivation attached to `θ₂ = (θ pulled back along h) ≫ (conormal map of the square)`. -/
theorem ι_derivationFamilyOfHom_comp_source
    (θ : (modulePullback B S hS e₀).obj
        (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
      conormalModule B S hS X Z)
    (hD : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
            (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
              (conormalModule B S hS X Z) θ V
              ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb).hom.app V x)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V)) :
    (restrictedSquareZeroValues B S hS Z₂ W₀
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) hZ₂).ι
        (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q)
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
          (conormalModule B S hS X₂ Z₂)
          ((modulePullbackCompIso B S hS h e₀).inv.app
              (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ≫
            (modulePullback B S hS h).map θ ≫ conormalMap B S hS Z₂ Z h' h hsq) V
          ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
            x)) =
      (restrictedSharpThroughThickening B S hS Z₂ W₀ (h' ≫ c)
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
          (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c hc)).hom.app V x -
        (restrictedSharpThroughThickening B S hS Z₂ W₀ (h' ≫ b)
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
          (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq b hb)).hom.app V x :=
  by
  have key (c' : X ⟶ W)
      (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀) :
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))).hom.app V
        ((restrictedSharpThroughThickening B S hS Z W₀ c' e₀ hc').hom.app V x) =
      (restrictedSharpThroughThickening B S hS Z₂ W₀ (h' ≫ c')
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)
          (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c' hc')).hom.app V x :=
    (ringSheafHom_comp_app_apply _ _ V x).symm.trans
      (ringSheafHom_congr_app_apply
        (restrictedSharpThroughThickening_comp_source_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀
          hsq c' hc').symm V x)
  exact (ι_derivationFamilyOfHom_comp_source_eq B S hS Z₂ Z W₀ h' h e₀ hsq q hZ₂ hZ θ V _).trans
    ((congrArg _ (hD V x)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·) (key c hc) (key b hb))))

end Core

section Move

variable (c : X ⟶ W)
  (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (θ : (modulePullback B S hS e₀).obj
      (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ⟶
    conormalModule B S hS X Z)
  (p : X ⟶ T) (hcq : c ≫ q = p)

include hcq in
/-- The morphism of thickenings `(e₀, c)` over `T` precomposed with `(h, h')` lies over `T`. -/
theorem comp_comp_eq_comp_assoc : (h' ≫ c) ≫ q = h' ≫ p :=
  (Category.assoc _ _ _).trans (congrArg (h' ≫ ·) hcq)

include hW in
/-- **A morphism with the properties of `θ · c`, precomposed with `(h, h')`, is `θ₂ · (h' ≫ c)`.**
The three conditions of `AlgebraicGeometry.Space.eq_derivationMove` are checked on `h' ≫ b`. -/
theorem comp_eq_derivationMove (b : X ⟶ W)
    (hb : subspaceInclusion B S hS X Z ≫ b = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hbq : b ≫ q = p)
    (hcm : conormalMap B S hS Z W₀ c e₀ hc = conormalMap B S hS Z W₀ b e₀ hb)
    (hD : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : ToType ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V)),
        (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
            (derivationFamilyOfHom B S hS (subspaceInclusion B S hS W W₀ ≫ q) e₀
              (conormalModule B S hS X Z) θ V
              ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
                x)) =
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc).hom.app V x -
            (restrictedSharpThroughThickening B S hS Z W₀ b e₀ hb).hom.app V x) :
    h' ≫ b =
      derivationMove B S hS Z₂ W₀ (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) q
        hZ₂ (h' ≫ c) (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c hc)
        ((modulePullbackCompIso B S hS h e₀).inv.app
            (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ≫
          (modulePullback B S hS h).map θ ≫ conormalMap B S hS Z₂ Z h' h hsq)
        (h' ≫ p) (comp_comp_eq_comp_assoc B S hS h' q c p hcq) :=
  eq_derivationMove B S hS Z₂ W₀ (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) q
    hZ₂ hW (h' ≫ c) (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c hc) _
    (h' ≫ p) (comp_comp_eq_comp_assoc B S hS h' q c p hcq) (h' ≫ b)
    ⟨comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq b hb,
      comp_comp_eq_comp_assoc B S hS h' q b p hbq,
      conormalMap_comp_source_eq B S hS Z₂ Z W₀ h' h e₀ hsq c b hc hb hcm,
      ι_derivationFamilyOfHom_comp_source B S hS Z₂ Z W₀ h' h e₀ hsq q hZ₂ hZ c b hc hb θ hD⟩

include hW in
/-- **The action of [Stacks Project, Tag 0CK6] under precomposition with a morphism of
thickenings.**  For a morphism of first order thickenings `(e₀, c) : (Z ⊂ X) ⟶ (W₀ ⊂ W)` over `T`,
`θ : e₀^*Ω_{W₀/T} ⟶ 𝒞_{Z/X}` and a morphism of first order thickenings
`(h, h') : (Z₂ ⊂ X₂) ⟶ (Z ⊂ X)`: `h' ≫ (θ · c) = θ₂ · (h' ≫ c)`, where
`θ₂ : (h ≫ e₀)^*Ω_{W₀/T} ≅ h^*e₀^*Ω_{W₀/T} ⟶ h^*𝒞_{Z/X} ⟶ 𝒞_{Z₂/X₂}` is the pullback of `θ` along
`h` followed by the conormal map of the square `(h, h')` of [Stacks Project, Tag 04CP]. -/
theorem comp_derivationMove :
    h' ≫ derivationMove B S hS Z W₀ e₀ q hZ c hc θ p hcq =
      derivationMove B S hS Z₂ W₀ (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) q
        hZ₂ (h' ≫ c) (comp_assoc_of_square_algebraicSpaces B S hS Z₂ Z W₀ h' h e₀ hsq c hc)
        ((modulePullbackCompIso B S hS h e₀).inv.app
            (sheafOfDifferentials B S hS (subspaceInclusion B S hS W W₀ ≫ q)) ≫
          (modulePullback B S hS h).map θ ≫ conormalMap B S hS Z₂ Z h' h hsq)
        (h' ≫ p) (comp_comp_eq_comp_assoc B S hS h' q c p hcq) := by
  obtain ⟨hb, hbq, hcm, hD⟩ := derivationMove_spec B S hS Z W₀ e₀ q hZ hW c hc θ p hcq
  exact comp_eq_derivationMove B S hS Z₂ Z W₀ h' h e₀ hsq q hZ₂ hZ hW c hc θ p hcq _ hb hbq hcm
    hD

end Move

end AlgebraicGeometry.Space

end
