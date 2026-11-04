module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreement

/-!
# Two morphisms over an arbitrary base agree on the functions read from the base

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceBaseAgreement.lean` proves that
the comorphisms, read through a thickening `Z ⊂ X`, of two morphisms `c, c' : X ⟶ W` agreeing on
`Z` agree on the functions read along a morphism `p : W ⟶ X` with `c ≫ p = c' ≫ p`: the base is
the source `X` itself, which is the case of the sections of a groupoid.  The source states the
lemmas it is used for ([Stacks Project, Tag 0618] and [Stacks Project, Tag 04D0]) for two
morphisms of thickenings over an arbitrary base `B`.  This file proves the same statements for a
morphism `q : W ⟶ T` to an arbitrary algebraic space `T` with `c ≫ q = c' ≫ q`, by the same
argument; nothing in it uses that `T` is `X`.

## Main results

* `structureSharp_comp_map_structureSharpThroughThickeningAt_eq_over`:
  the two comorphisms agree after the direct-image form `q^♯ : 𝒪_T ⟶ q_*𝒪_W`.
* `structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq_over`:
  the same after the inverse-image form `q^♯ : q^{-1}𝒪_T ⟶ 𝒪_W`.
* `inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq_over`:
  the two transported comorphisms on the small étale site of `W₀` agree after `j^{-1}(q^♯)`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W T : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- Two members of a family of morphisms at equal indices agree after transport. -/
private theorem family_congr_over {Cc : Type*} [Category Cc] {io : Type*} {A : Cc}
    (R : io → Cc) (F : ∀ k, A ⟶ R k) {k k' : io} (e : k = k') {D : Cc} (p : R k = D)
    (p' : R k' = D) :
    F k ≫ eqToHom p = F k' ≫ eqToHom p' := by
  cases e; rfl

/-- **The comorphism of `c : X ⟶ W`, read through the thickening and then along `q : W ⟶ T`, is
the comorphism of the composite `c ≫ q`.** -/
theorem structureSharp_comp_map_structureSharpThroughThickeningAt_over (c : X ⟶ W) (q : W ⟶ T)
    (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) :
    (structureSharp B S hS q ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
          (structureSharpThroughThickeningAt B S hS Z c κ h)) ≫
        pushforwardRingSheafCompHom B S hS κ q
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpThroughThickeningAt B S hS Z (c ≫ q) (κ ≫ q)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ q) h)) := by
  cases h
  have e1 : structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl =
      structureSharpThroughThickening B S hS Z c := Category.comp_id _
  have e2 : structureSharpThroughThickeningAt B S hS Z (c ≫ q)
        ((subspaceInclusion B S hS X Z ≫ c) ≫ q)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ q) (rfl : subspaceInclusion B S hS X Z ≫ c =
            subspaceInclusion B S hS X Z ≫ c))) =
      structureSharpThroughThickening B S hS Z (c ≫ q) := Category.comp_id _
  rw [e1]
  exact (Category.assoc _ _ _).trans
    ((structureSharpThroughThickening_comp B S hS Z c q).trans e2.symm)

/-- **Two morphisms over `T` which agree on the thickening have the same comorphism read through
the thickening, after the comorphism `q^♯ : 𝒪_T ⟶ q_*𝒪_W` of the structure morphism.** -/
theorem structureSharp_comp_map_structureSharpThroughThickeningAt_eq_over (c c' : X ⟶ W)
    (q : W ⟶ T) (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ)
    (h' : subspaceInclusion B S hS X Z ≫ c' = κ) (hcc : c ≫ q = c' ≫ q) :
    structureSharp B S hS q ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
          (structureSharpThroughThickeningAt B S hS Z c κ h) =
      structureSharp B S hS q ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
          (structureSharpThroughThickeningAt B S hS Z c' κ h') := by
  have hK := pushforwardRingSheafCompHom_comp_inv B S hS κ q
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
  have hfam := family_congr_over
    (fun k : X ⟶ T => pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS T.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ≫ k)).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (fun k => structureSharpThroughThickening B S hS Z k) hcc
    (congrArg (fun n : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T =>
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS n).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ q) h)))
    (congrArg (fun n : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T =>
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS n).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ q) h')))
  have hstep : (structureSharp B S hS q ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
        (structureSharpThroughThickeningAt B S hS Z c κ h)) ≫
      pushforwardRingSheafCompHom B S hS κ q
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
    (structureSharp B S hS q ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
        (structureSharpThroughThickeningAt B S hS Z c' κ h')) ≫
      pushforwardRingSheafCompHom B S hS κ q
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) := by
    rw [structureSharp_comp_map_structureSharpThroughThickeningAt_over,
      structureSharp_comp_map_structureSharpThroughThickeningAt_over]
    exact hfam
  exact cancel_right_of_comp_id _ _ _ _ hK hstep

/-- **The same agreement after the inverse-image form `q^♯ : q^{-1}𝒪_T ⟶ 𝒪_W`**, by transposing
along `q^{-1} ⊣ q_*`. -/
theorem structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq_over
    (c c' : X ⟶ W) (q : W ⟶ T)
    (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ)
    (h' : subspaceInclusion B S hS X Z ≫ c' = κ) (hcc : c ≫ q = c' ≫ q) :
    structureSharpRingInverseImage B S hS q ≫
        structureSharpThroughThickeningAt B S hS Z c κ h =
      structureSharpRingInverseImage B S hS q ≫
        structureSharpThroughThickeningAt B S hS Z c' κ h' := by
  have key : ∀ (d : X ⟶ W) (hd : subspaceInclusion B S hS X Z ≫ d = κ),
      ringUnit (smallToposMorphismTypeU B S hS q) (structureRingSheaf B S hS T) ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
            (structureSharpRingInverseImage B S hS q ≫
              structureSharpThroughThickeningAt B S hS Z d κ hd) =
        structureSharp B S hS q ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
            (structureSharpThroughThickeningAt B S hS Z d κ hd) := by
    intro d hd
    rw [(pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map_comp
      (structureSharpRingInverseImage B S hS q)
      (structureSharpThroughThickeningAt B S hS Z d κ hd)]
    exact Eq.trans (Category.assoc _ _ _).symm
      (congrArg (fun m => m ≫ (pushforwardRingFunctor (smallToposMorphismTypeU B S hS q)).map
          (structureSharpThroughThickeningAt B S hS Z d κ hd))
        (ringUnit_comp_map_structureSharpRingInverseImage B S hS q))
  refine comp_eq_of_ringUnit_comp_map_eq (smallToposMorphismTypeU B S hS q)
    (structureRingSheaf B S hS T) ?_
  exact (key c h).trans
    ((structureSharp_comp_map_structureSharpThroughThickeningAt_eq_over B S hS Z c c' q κ h h'
      hcc).trans (key c' h').symm)

variable (W₀ : ClosedSubspaces B S hS W.1)

/-- **The two transported comorphisms on the small étale site of `W₀` agree after
`j^{-1}(q^♯)`**, for two morphisms over `T` restricting to the same `e₀ ≫ j`. -/
theorem inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq_over
    (c c' : X ⟶ W) (q : W ⟶ T)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hcc : c ≫ q = c' ≫ q) :
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS q) ≫
        restrictedSharpThroughThickening B S hS Z W₀ c e₀ h =
      (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS q) ≫
        restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h' := by
  have hnat : ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheafInverseImage B S hS q) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS q)) =
      structureSharpRingInverseImage B S hS q ≫
        ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheaf B S hS W) :=
    ((ringUnitNatTrans (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).naturality
      (structureSharpRingInverseImage B S hS q)).symm
  have key : ∀ (d : X ⟶ W)
      (hd : subspaceInclusion B S hS X Z ≫ d = e₀ ≫ subspaceInclusion B S hS W W₀),
      ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
            (structureRingSheafInverseImage B S hS q) ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
                (subspaceInclusion B S hS W W₀))).map
                (structureSharpRingInverseImage B S hS q) ≫
              restrictedSharpThroughThickening B S hS Z W₀ d e₀ hd) =
        (structureSharpRingInverseImage B S hS q ≫
            structureSharpThroughThickeningAt B S hS Z d
              (e₀ ≫ subspaceInclusion B S hS W W₀) hd) ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) := by
    intro d hd
    refine Eq.trans (congrArg (fun m => ringUnit (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))
          (structureRingSheafInverseImage B S hS q) ≫ m)
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map_comp _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun m => m ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map
        (restrictedSharpThroughThickening B S hS Z W₀ d e₀ hd)) hnat) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun m => structureSharpRingInverseImage B S hS q ≫ m)
      (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ d e₀ hd)) ?_
    exact (Category.assoc _ _ _).symm
  refine comp_eq_of_ringUnit_comp_map_eq (smallToposMorphismTypeU B S hS
    (subspaceInclusion B S hS W W₀)) (structureRingSheafInverseImage B S hS q) ?_
  refine (key c h).trans (Eq.trans ?_ (key c' h').symm)
  exact congrArg (fun m => m ≫ pushforwardRingSheafCompInv B S hS e₀
      (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq_over B S hS Z c c' q
      (e₀ ≫ subspaceInclusion B S hS W W₀) h h' hcc)

end AlgebraicGeometry.Space

end
