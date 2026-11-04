module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceCommonTarget

/-!
# The comorphisms of two morphisms agreeing on a thickening, read on a closed subspace of the
target

Let `Z ⊂ X` be a thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace of a second algebraic space, with inclusion
`j : W₀ ⟶ W`, and let `c : X ⟶ W` be a morphism whose restriction to the thickening factors
through `W₀`, say `i ≫ c = e₀ ≫ j` for a morphism `e₀ : Z ⟶ W₀`.

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceCommonTarget.lean` reads the
comorphism of `c` as a morphism of sheaves of rings

`𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)`

on the small étale site of `W`, in a target depending on `c` only through `i ≫ c`.  This file
transports that morphism to the small étale site of `W₀`: it becomes

`j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`,

the adjunct along `j^{-1} ⊣ j_*` of the comorphism read through the comparison
`j_*((e₀)_*(i^{-1}𝒪_X)) ≅ (e₀ ≫ j)_*(i^{-1}𝒪_X)` of iterated direct images.

The point of the transport is the source: `j^{-1}𝒪_W` carries the locally surjective reduction
`j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`, which is the quotient map the descent of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` is taken along.  On the site
of `W` there is no such map — `𝒪_W` is not a sheaf of rings over `W₀` — so the difference of
two comorphisms cannot be made into a derivation of `𝒪_{W₀}` there.  On the site of `W₀` it
can, and that is what [Stacks Project, Tag 0CKE] needs: there the thickening `Z ⊂ X` is
`U₀ ⊂ U`, the closed subspace `W₀ ⊆ W` is `R₀ = s^{-1}(U₀) ⊆ R`, `c` is a section of the source
lying in `Γ₀`, and `e₀` is the unit of the restricted groupoid.

No full faithfulness of the direct image is used: the transport is the adjunction bijection,
and the comparison of iterated direct images is the one already available for sheaves of rings.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardRingSheafCompInv`: the comparison
  `(f ≫ g)_*O ⟶ g_*(f_*O)` of iterated direct images of a sheaf of rings, which is
  [Stacks Project, Tag 03G2], part (3), read in the direction the transport consumes.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening`: **the comorphism of `c` read as a
  morphism `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`** on the small étale site of `W₀`.
* `AlgebraicGeometry.Space.restrictedStructureSharpReduction`: the comorphism of `e₀ ≫ j` read
  in the same way, which is what the previous morphism becomes after the reduction
  `i^{-1}𝒪_X ⟶ 𝒪_Z`.

## Main results

* `Stacks.Sheaves.ToposPullback.pullbackRingSheafComp_inv_naturality` and
  `Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans_comp_comp_inv_naturality`: the
  two naturalities the comparison is assembled from, at an abstract site.
* `AlgebraicGeometry.Space.pushforwardRingSheafCompInv_naturality`: the comparison of iterated
  direct images is natural in the sheaf of rings.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_reduction`: **the transported
  comorphism, followed by the direct image of the reduction `i^{-1}𝒪_X ⟶ 𝒪_Z`, is the
  transported comorphism of `e₀ ≫ j`.**  In particular it does not depend on `c`.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_reduction_eq`: **two morphisms
  whose restrictions to the thickening are one and the same morphism `e₀` have transported
  comorphisms which agree after the reduction**, so their sectionwise difference takes its
  values in the sectionwise kernel of the reduction.  This is hypothesis (1) of
  [Stacks Project, Tag 0618] on the site where the quotient map lives.

## Implementation notes

The comparison of iterated direct images is used only in the direction
`(f ≫ g)_*O ⟶ g_*(f_*O)`, so it is defined as a bare morphism rather than as the inverse of a
bundled isomorphism: `CategoryTheory.Iso.trans_hom` does not fire at terms of this size, and a
morphism whose definition is syntactically a composite can be rewritten with the naturality of
its two factors directly.  Both factors are the identity on underlying sheaves of sets, so the
naturality is proved, as everything in the file it builds on is, by
`CategoryTheory.Sheaf.hom_ext_sections` through the faithful
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv₁ uu₁ vv₂ uu₂

variable {C₁ : Type uu₁} [Category.{vv₁} C₁] {C₂ : Type uu₂} [Category.{vv₂} C₂]
  {D : Type uu} [Category.{vv} D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  {K : GrothendieckTopology D}
  [J₁.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J₂.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  (Φ₁ : Sheaf K (Type ww) ⥤ Sheaf J₁ (Type ww)) [PreservesFiniteProducts Φ₁]
  (Φ₂ : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Φ₂]

/-- **The inverse comparison of a ring structure transported in two steps with one transported
in one step is natural in the sheaf of rings.**  This is
`Stacks.Sheaves.ToposPullback.pullbackRingSheafComp_naturality` read on the inverse
isomorphism. -/
theorem pullbackRingSheafComp_inv_naturality {R₁ R₂ : Sheaf K RingCat.{ww}} (a : R₁ ⟶ R₂) :
    pullbackRingSheafMap J₂ (Φ₁ ⋙ Φ₂) a ≫ (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ R₂).inv =
      (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ R₁).inv ≫
        pullbackRingSheafMap J₂ Φ₂ (pullbackRingSheafMap J₁ Φ₁ a) :=
  ((Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 (pullbackRingSheafComp_naturality J₁ J₂ Φ₁ Φ₂ a)).trans
      (Category.assoc _ _ _))).symm

variable {Φ : Sheaf K (Type ww) ⥤ Sheaf J₂ (Type ww)} [PreservesFiniteProducts Φ]

/-- **The transport of a sheaf of rings along a natural transformation into a composite,
followed by the inverse comparison with the two-step transport, is natural in the sheaf of
rings.**  This is the composite through which the direct image along a composite is compared
with the iterated direct image; both factors are natural, by
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans_naturality` and
`Stacks.Sheaves.ToposPullback.pullbackRingSheafComp_inv_naturality`. -/
theorem pullbackRingSheafMapOfNatTrans_comp_comp_inv_naturality (θ : Φ ⟶ Φ₁ ⋙ Φ₂)
    {O O' : Sheaf K RingCat.{ww}} (a : O ⟶ O') :
    pullbackRingSheafMap J₂ Φ a ≫
        (pullbackRingSheafMapOfNatTrans J₂ O' θ ≫
          (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ O').inv) =
      (pullbackRingSheafMapOfNatTrans J₂ O θ ≫
          (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ O).inv) ≫
        pullbackRingSheafMap J₂ Φ₂ (pullbackRingSheafMap J₁ Φ₁ a) := by
  rw [← Category.assoc, ← pullbackRingSheafMapOfNatTrans_naturality, Category.assoc,
    pullbackRingSheafComp_inv_naturality, ← Category.assoc]

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of iterated direct images of a sheaf of rings -/

section PushforwardComp

variable {V₁ V₂ V₃ : AlgebraicSpaces B S hS}

/-- **The comparison of iterated direct images of a sheaf of rings**, in the direction
`(f ≫ g)_*O ⟶ g_*(f_*O)`: the transport along the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of
[Stacks Project, Tag 03G2], part (3), followed by the comparison
`Stacks.Sheaves.ToposPullback.pullbackRingSheafComp` of a ring structure transported in two
steps with one transported in one.  Both are the identity on underlying sheaves of sets. -/
noncomputable def pushforwardRingSheafCompInv (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS g).pushforward
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
          (smallToposMorphismTypeU B S hS f).pushforward O) :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS V₃.1) O
      (smallToposMorphismTypeU_comp B S hS f g).inv ≫
    (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1)
      (SmallEtale.topology B S hS V₃.1) (smallToposMorphismTypeU B S hS f).pushforward
      (smallToposMorphismTypeU B S hS g).pushforward O).inv

/-- **The comparison of iterated direct images is natural in the sheaf of rings.**  Both sides
have the comparison of the transporting functors composed with the iterated direct image of the
given morphism as their underlying morphism of sheaves of sets, in the two orders, and those
agree by naturality of that comparison. -/
theorem pushforwardRingSheafCompInv_naturality (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    {O O' : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}} (a : O ⟶ O') :
    pullbackRingSheafMap (SmallEtale.topology B S hS V₃.1)
          (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward a ≫
        pushforwardRingSheafCompInv B S hS f g O' =
      pushforwardRingSheafCompInv B S hS f g O ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS V₃.1)
          (smallToposMorphismTypeU B S hS g).pushforward
          (pullbackRingSheafMap (SmallEtale.topology B S hS V₂.1)
            (smallToposMorphismTypeU B S hS f).pushforward a) :=
  pullbackRingSheafMapOfNatTrans_comp_comp_inv_naturality
    (SmallEtale.topology B S hS V₂.1) (SmallEtale.topology B S hS V₃.1)
    (smallToposMorphismTypeU B S hS f).pushforward
    (smallToposMorphismTypeU B S hS g).pushforward
    (smallToposMorphismTypeU_comp B S hS f g).inv a

end PushforwardComp

/-! ### The comorphism read on a closed subspace of the target -/

section RestrictedTarget

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)

/-- **The sheaf of rings on the small étale site of `W₀` in which the comorphisms of the
morphisms agreeing on the thickening `Z ⊂ X` are compared:** the direct image along
`e₀ : Z ⟶ W₀` of the inverse image `i^{-1}𝒪_X` of the structure sheaf of the ambient space of
the thickening.

It is `AlgebraicGeometry.Space.thickeningLiftRingSheaf` read on the smaller site: the direct
image along `i ≫ c = e₀ ≫ j` has been replaced by the direct image along `e₀`, the remaining
factor `j` having been moved to the source of the morphism. -/
noncomputable abbrev restrictedThickeningLiftRingSheaf
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)) :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
    (smallToposMorphismTypeU B S hS e₀).pushforward
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- **The comorphism of `c : X ⟶ W` read on the small étale site of a closed subspace
`W₀ ⊆ W` through which its restriction to the thickening factors:** the adjunct along
`j^{-1} ⊣ j_*` of `AlgebraicGeometry.Space.structureSharpThroughThickeningAt`, read through the
comparison `AlgebraicGeometry.Space.pushforwardRingSheafCompInv` of iterated direct images.

Its source `j^{-1}𝒪_W` carries the locally surjective reduction `j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`,
which is what makes the difference of two such morphisms descend to a derivation of
`𝒪_{W₀}`. -/
noncomputable def restrictedSharpThroughThickening (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀ :=
  ((ringImageAdjunction
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).homEquiv
      (structureRingSheaf B S hS W)
      (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)).symm
    (structureSharpThroughThickeningAt B S hS Z c
        (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
      pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))

/-- **The comorphism of `e₀ ≫ j` read on the small étale site of `W₀` in the same way:** the
adjunct along `j^{-1} ⊣ j_*` of the comorphism of [Stacks Project, Tag 03G8] of `e₀ ≫ j`, read
through the comparison of iterated direct images.

This is what the transported comorphism of any `c` with `i ≫ c = e₀ ≫ j` becomes after the
reduction `i^{-1}𝒪_X ⟶ 𝒪_Z`. -/
noncomputable def restrictedStructureSharpReduction
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)) :
    structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (smallToposMorphismTypeU B S hS e₀).pushforward
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :=
  ((ringImageAdjunction
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).homEquiv
      (structureRingSheaf B S hS W) _).symm
    (structureSharp B S hS (e₀ ≫ subspaceInclusion B S hS W W₀) ≫
      pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)))

/-- **The transported comorphism of `c`, followed by the direct image of the reduction
`i^{-1}𝒪_X ⟶ 𝒪_Z`, is the transported comorphism of `e₀ ≫ j`.**

So it depends on `c` only through the restriction `e₀` of `c` to the thickening, which is what
makes the difference of two such morphisms take its values in the sectionwise kernel of the
reduction. -/
theorem restrictedSharpThroughThickening_comp_reduction (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS Z W₀ c e₀ h ≫
        pullbackRingSheafMap
          (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      restrictedStructureSharpReduction B S hS Z W₀ e₀ := by
  have hnat := pushforwardRingSheafCompInv_naturality B S hS e₀
    (subspaceInclusion B S hS W W₀)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
  have hred := structureSharpThroughThickeningAt_comp_reduction B S hS Z c
    (e₀ ≫ subspaceInclusion B S hS W W₀) h
  refine Eq.trans
    (Adjunction.homEquiv_naturality_right_symm
      (ringImageAdjunction
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))) _ _).symm
    (congrArg ((ringImageAdjunction
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).homEquiv
      (structureRingSheaf B S hS W) _).symm ?_)
  calc (structureSharpThroughThickeningAt B S hS Z c
            (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward
          (pullbackRingSheafMap
            (SmallEtale.topology B S hS
              (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
            (smallToposMorphismTypeU B S hS e₀).pushforward
            (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)))
      = structureSharpThroughThickeningAt B S hS Z c
            (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
          (pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
              (structureRingSheafInverseImage B S hS
                (subspaceInclusion B S hS X Z)) ≫
            pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
              (smallToposMorphismTypeU B S hS
                (subspaceInclusion B S hS W W₀)).pushforward
              (pullbackRingSheafMap
                (SmallEtale.topology B S hS
                  (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
                (smallToposMorphismTypeU B S hS e₀).pushforward
                (structureSharpRingInverseImage B S hS
                  (subspaceInclusion B S hS X Z)))) := Category.assoc _ _ _
    _ = structureSharpThroughThickeningAt B S hS Z c
            (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
          (pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
              (smallToposMorphismTypeU B S hS
                (e₀ ≫ subspaceInclusion B S hS W W₀)).pushforward
              (structureSharpRingInverseImage B S hS
                (subspaceInclusion B S hS X Z)) ≫
            pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
              (structureRingSheaf B S hS
                (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))) :=
        congrArg (fun m ↦ structureSharpThroughThickeningAt B S hS Z c
          (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫ m) hnat.symm
    _ = (structureSharpThroughThickeningAt B S hS Z c
            (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
          pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
            (smallToposMorphismTypeU B S hS
              (e₀ ≫ subspaceInclusion B S hS W W₀)).pushforward
            (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS X Z))) ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
            (structureRingSheaf B S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :=
        (Category.assoc _ _ _).symm
    _ = structureSharp B S hS (e₀ ≫ subspaceInclusion B S hS W W₀) ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
            (structureRingSheaf B S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :=
        congrArg (fun m ↦ m ≫ pushforwardRingSheafCompInv B S hS e₀
          (subspaceInclusion B S hS W W₀)
          (structureRingSheaf B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))) hred

/-- **The defining adjunction identity of
`AlgebraicGeometry.Space.restrictedSharpThroughThickening`**: the unit of `j^{-1} ⊣ j_*`
followed by the direct image of the transported comorphism is the comorphism read in the direct
image along `e₀ ≫ j`, through the comparison of iterated direct images.

This is what carries a statement about the comorphism on the small étale site of `W` back to one
about the transported comorphism on the small étale site of `W₀`. -/
theorem ringUnit_comp_map_restrictedSharpThroughThickening (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheaf B S hS W) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h) =
      structureSharpThroughThickeningAt B S hS Z c
          (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
        pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  (ringImageAdjunction_homEquiv_apply
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
      (structureRingSheaf B S hS W)
      (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **Two morphisms whose restrictions to the thickening are one and the same morphism `e₀`
have transported comorphisms which agree after the reduction.**  This is hypothesis (1) of
[Stacks Project, Tag 0618] on the small étale site of `W₀`: the sectionwise difference of the
two transported comorphisms, which is formed in the single sheaf of rings
`(e₀)_*(i^{-1}𝒪_X)`, takes its values in the sectionwise kernel of the reduction
`i^{-1}𝒪_X ⟶ 𝒪_Z`. -/
theorem restrictedSharpThroughThickening_comp_reduction_eq (c c' : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS Z W₀ c e₀ h ≫
        pullbackRingSheafMap
          (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h' ≫
        pullbackRingSheafMap
          (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  (restrictedSharpThroughThickening_comp_reduction B S hS Z W₀ c e₀ h).trans
    (restrictedSharpThroughThickening_comp_reduction B S hS Z W₀ c' e₀ h').symm

end RestrictedTarget

end AlgebraicGeometry.Space

end
