module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals

/-!
# The chart reading of a comorphism through a thickening, modulo the defining ideal

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W`, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)`.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartRing.lean` reads such an
`a` over an étale scheme chart `V` of `W` and an étale scheme chart of `X` above `X ×_W V` as a
map `Γ(V, ⊤) ⟶ Γ(V', ⊤)` of regular functions.

This file proves that **the structure map of `i` kills the difference of two such readings as
soon as the two morphisms have the same reduction** — the same composite with the direct image
of `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`.  Since the structure map of `i` on the sections over a chart *is*
the defining ideal of the thickening there,
`AlgebraicGeometry.Space.definingIdealAt`, and that ideal is the kernel of restriction of
regular functions to the chart `Z ×_X V'` of the thickening by
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`, this says that the chart reading of `a` is
pinned on the thickening by the reduction of `a`.

The reason is that the structure map of `i` factors as the unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` of
`i^{-1} ⊣ i_*` followed by the direct image of the reduction
(`AlgebraicGeometry.Space.thickeningRingUnit_comp_pullbackRingSheafMap`), and the chart reading
is exactly the value of `a` read on the chart and brought back along `η`.  So after the
structure map of `i` the `η` cancels and only the reduction of `a` is left, the chart projection
and the comparison of iterated direct images being natural in the sheaf of rings.

## Main results

* `Stacks.Sheaves.ToposPullback.app_pullbackRingSheafMap_natTrans`: **the chart reading of the
  sections of an inverse-image sheaf of rings is natural in the sheaf of rings.**
* `AlgebraicGeometry.Space.app_structureSharp_thickeningLiftChartAppTop_eq`: **the chart reading
  of a morphism, after the structure map of `i`, is the chart reading of its reduction**, and
* `AlgebraicGeometry.Space.app_structureSharp_thickeningLiftChartAppTop_congr`: **two morphisms
  with the same reduction have chart readings whose values are identified by the structure map
  of `i`**, hence differ by a section of the defining ideal of the thickening.
* `AlgebraicGeometry.Space.pushforwardRingSheafCompHom_naturality`: the comparison of iterated
  direct images is natural in the sheaf of rings in the direction `g_*(f_*O) ⟶ (f ≫ g)_*O`
  too, and `AlgebraicGeometry.Space.structureSharp_comp_pushforwardRingSheafCompHom` is the
  composition law of [Stacks Project, Tag 03G8] written with it.
* `AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_comp_reduction`: **a solution of
  the lifting problem carried back to the ambient site has the comorphism of `e₀ ≫ j` for its
  reduction**, as soon as the solution has that reduction on the site of `W₀`.  This is what
  makes the congruence above applicable to the solution
  [Stacks Project, Tag 0618] produces, and
  `AlgebraicGeometry.Space.thickeningLiftOfIndex_comp_reduction` carries the reduction across
  the index transport.
* `AlgebraicGeometry.Space.sub_thickeningLiftChartAppTop_mem_definingIdealAt`: the chart reading
  differs from the chartwise pullback of `c` by a section of the defining ideal of the
  thickening, and
* `AlgebraicGeometry.Space.comp_rep_snd_thickeningLiftChartHom_eq` and
  `AlgebraicGeometry.Space.comp_rep_snd_eq_of_toScheme_map_eq`: **hence the attached morphism of
  charts agrees with the one `c` induces on the chart `Z ×_X V'` of the thickening**, as a
  morphism of schemes and then as a morphism of the site.  That is the second clause of the
  lifting condition `AlgebraicGeometry.Space.IsChartLift` over an affine chart of `W`.

## Implementation notes

The hypothesis is an equation of the two composites with the reduction, rather than the equality
of the difference with a section of the conormal module: that is the form
`AlgebraicGeometry.Space.structureSharpThroughThickening_comp_reduction` produces, and it needs
no module theory.

The naturality of the chart reading is stated at an abstract site, as the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` require of
every such step: at the geometric terms the two `rfl`s it rests on are deterministic
`whnf` timeouts.

**No `@[stacks]` attribute is placed.**  As in the files this one extends, what is proved is a
comparison internal to this development of two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), iterated
  direct images.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the correspondence
  between lifts and linear maps.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this reading is
  an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]

/-- **The reading of the sections of an inverse-image sheaf of rings along a natural
transformation is natural in the sheaf of rings.**  Both sides are the transformation evaluated
at the underlying morphism of sheaves of sets, in the two orders, and those agree by naturality
of the transformation.

This is `CategoryTheory.NatTrans.naturality_apply` at the transformation, stated in the two
spellings a reading of an inverse-image sheaf of rings arrives in: the inverse image of a
morphism of sheaves of rings on the one side and the morphism itself on the other. -/
theorem app_pullbackRingSheafMap_natTrans {O O' : Sheaf K RingCat.{ww}} (ρ : O ⟶ O')
    (X : Cᵒᵖ) (Z : Dᵒᵖ) (θ : Φ ⋙ Sheaf.sectionsFunctor J X ⟶ Sheaf.sectionsFunctor K Z)
    (w : ToType ((pullbackRingSheaf J Φ O).obj.obj X)) :
    θ.app (Sheaf.ringSheaf O') ((pullbackRingSheafMap J Φ ρ).hom.app X w) =
      ρ.hom.app Z (θ.app (Sheaf.ringSheaf O) w) :=
  NatTrans.naturality_apply θ
    ((sheafCompose K (CategoryTheory.forget RingCat.{ww})).map ρ) w

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry

universe u

/-- **Two morphisms into an affine scheme agree after a morphism into their source as soon as
their maps of regular functions do.**  This is `AlgebraicGeometry.ext_of_isAffine` at the
affine target, read on the sections; it is the pre-composition companion of
`AlgebraicGeometry.comp_eq_of_appTop_comp_eq_of_isAffine`, which cancels on the other side. -/
theorem comp_eq_of_appTop_apply_eq {K₀ K V : Scheme.{u}} [IsAffine V]
    (m : K₀ ⟶ K) {ψ χ : K ⟶ V}
    (h : ∀ b, m.appTop.hom (ψ.appTop.hom b) = m.appTop.hom (χ.appTop.hom b)) :
    m ≫ ψ = m ≫ χ :=
  ext_of_isAffine (((Scheme.Hom.comp_appTop m ψ).trans
    (CommRingCat.hom_ext (RingHom.ext h))).trans (Scheme.Hom.comp_appTop m χ).symm)

namespace Space

/-! ### Rearrangements -/

/-- **Naturality transfers across a two-sided inverse.**  If two mutually inverse pairs are
natural in one direction then they are natural in the other.  Stated over an abstract category
with each morphism a variable, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` require of these
rearrangements. -/
private theorem comp_hom_eq_of_comp_inv_eq {Cc : Type*} [Category Cc] {P Q P' Q' : Cc}
    (hh : P ⟶ Q) (iv : Q ⟶ P) (hh' : P' ⟶ Q') (iv' : Q' ⟶ P') (r : Q ⟶ Q') (m : P ⟶ P')
    (h1 : hh ≫ iv = 𝟙 P) (h2 : iv' ≫ hh' = 𝟙 Q') (h : r ≫ iv' = iv ≫ m) :
    m ≫ hh' = hh ≫ r := by
  rw [← Category.id_comp (m ≫ hh'), ← h1, Category.assoc, ← reassoc_of% h, h2,
    Category.comp_id]

/-- Moving the last factor of a four-fold composite across a naturality square and then
rewriting the middle two factors. -/
private theorem comp_comp_comp_eq_of_comp_eq {Cc : Type*} [Category Cc]
    {A₁ A₂ A₃ A₄ A₅ A₆ : Cc} (u : A₁ ⟶ A₂) (v : A₂ ⟶ A₃) (w : A₃ ⟶ A₄) (r : A₄ ⟶ A₅)
    (m : A₃ ⟶ A₆) (w' : A₆ ⟶ A₅) (x : A₂ ⟶ A₆) (t : A₁ ⟶ A₅)
    (h1 : m ≫ w' = w ≫ r) (h2 : v ≫ m = x) (h3 : (u ≫ x) ≫ w' = t) :
    ((u ≫ v) ≫ w) ≫ r = t := by
  rw [← h3, ← h2]
  simp [h1]

/-- Reassociating a composite of four factors whose first two are rewritten together. -/
private theorem comp_assoc_eq_of_comp_eq {Cc : Type*} [Category Cc] {A₁ A₂ A₃ A₄ A₅ : Cc}
    (u : A₁ ⟶ A₂) (p : A₂ ⟶ A₃) (q : A₃ ⟶ A₄) (k : A₄ ⟶ A₅) (s : A₁ ⟶ A₃) (t : A₁ ⟶ A₅)
    (h1 : u ≫ p = s) (h2 : s ≫ q ≫ k = t) :
    (u ≫ p ≫ q) ≫ k = t := by
  rw [← h2, ← h1]
  simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The comparison of iterated direct images, in the other direction -/

/-- **The comparison of iterated direct images `g_*(f_*O) ⟶ (f ≫ g)_*O` is natural in the sheaf
of rings.**  It is the inverse of
`AlgebraicGeometry.Space.pushforwardRingSheafCompInv`, which is natural by
`AlgebraicGeometry.Space.pushforwardRingSheafCompInv_naturality`, and naturality transfers
across a two-sided inverse. -/
theorem pushforwardRingSheafCompHom_naturality {V₁ V₂ V₃ : AlgebraicSpaces B S hS}
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    {O O' : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}} (ρ : O ⟶ O') :
    pullbackRingSheafMap (SmallEtale.topology B S hS V₃.1)
          (smallToposMorphismTypeU B S hS g).pushforward
          (pullbackRingSheafMap (SmallEtale.topology B S hS V₂.1)
            (smallToposMorphismTypeU B S hS f).pushforward ρ) ≫
        pushforwardRingSheafCompHom B S hS f g O' =
      pushforwardRingSheafCompHom B S hS f g O ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS V₃.1)
          (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward ρ :=
  comp_hom_eq_of_comp_inv_eq _ (pushforwardRingSheafCompInv B S hS f g O) _
    (pushforwardRingSheafCompInv B S hS f g O') _ _
    (pushforwardRingSheafCompHom_comp_inv B S hS f g O)
    (pushforwardRingSheafCompInv_comp_hom B S hS f g O')
    (pushforwardRingSheafCompInv_naturality B S hS f g ρ)

/-- The defining equation of
`AlgebraicGeometry.Space.pushforwardRingSheafCompHom`, so that a consumer rewrites with it
rather than make the kernel unfold the definition inside a composite of this size:
unifying the two spellings in place is a deterministic `whnf` timeout. -/
theorem pushforwardRingSheafCompHom_eq {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂)
    (g : V₂ ⟶ V₃) (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pushforwardRingSheafCompHom B S hS f g O =
      (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1)
          (SmallEtale.topology B S hS V₃.1) (smallToposMorphismTypeU B S hS f).pushforward
          (smallToposMorphismTypeU B S hS g).pushforward O).hom ≫
        pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS V₃.1) O
          (smallToposMorphismTypeU_comp B S hS f g).hom := rfl

/-- **The composition law of [Stacks Project, Tag 03G8] in the comparison spelling.**  This is
`AlgebraicGeometry.Space.structureSharp_comp` with its last two factors written as
`AlgebraicGeometry.Space.pushforwardRingSheafCompHom`, which is the form the carried-back
solution of the lifting problem arrives in. -/
theorem structureSharp_comp_pushforwardRingSheafCompHom
    {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) :
    structureSharp B S hS g ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS g)).map
          (structureSharp B S hS f) ≫
        pushforwardRingSheafCompHom B S hS f g (structureRingSheaf B S hS V₁) =
      structureSharp B S hS (f ≫ g) := by
  rw [pushforwardRingSheafCompHom_eq]
  exact structureSharp_comp B S hS f g

/-! ### The reduction of a carried-back solution of the lifting problem -/

/-- **A solution of the lifting problem carried back to the ambient site has the comorphism of
`e₀ ≫ j` for its reduction**, as soon as the solution itself has that reduction on the site of
`W₀`. -/
theorem liftRestrictedSharpThroughThickening_comp_reduction
    (W₀ : ClosedSubspaces B S hS W.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)
    (hg : g ≫ pullbackRingSheafMap (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallToposMorphismTypeU B S hS e₀).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
        structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀) ≫
          structureSharp B S hS e₀) :
    liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS
            (e₀ ≫ subspaceInclusion B S hS W W₀)).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharp B S hS (e₀ ≫ subspaceInclusion B S hS W W₀) := by
  have h2 : (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map g ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (pullbackRingSheafMap (SmallEtale.topology B S hS
              (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
            (smallToposMorphismTypeU B S hS e₀).pushforward
            (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS X Z))) =
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map (structureSharp B S hS e₀) := by
    rw [← Functor.map_comp, hg]
    exact Functor.map_comp _ _ _
  have h3 : (ringUnit (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀)) (structureRingSheaf B S hS W) ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
                (subspaceInclusion B S hS W W₀))).map
              (structureSharpRingInverseImage B S hS
                (subspaceInclusion B S hS W W₀)) ≫
            (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
              (subspaceInclusion B S hS W W₀))).map (structureSharp B S hS e₀)) ≫
        pushforwardRingSheafCompHom B S hS e₀ (subspaceInclusion B S hS W W₀)
          (structureRingSheaf B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) =
      structureSharp B S hS (e₀ ≫ subspaceInclusion B S hS W W₀) :=
    comp_assoc_eq_of_comp_eq _ _ _ _
      (structureSharp B S hS (subspaceInclusion B S hS W W₀)) _
      (ringUnit_comp_map_structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀))
      (structureSharp_comp_pushforwardRingSheafCompHom B S hS e₀
        (subspaceInclusion B S hS W W₀))
  exact comp_comp_comp_eq_of_comp_eq _ _ _ _ _ _ _ _
    (pushforwardRingSheafCompHom_naturality B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)))
    h2 h3

/-- The reduction of a morphism into `(i ≫ c)_*(i^{-1}𝒪_X)`: its composite with the direct
image along `i ≫ c` of the structure map `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`. -/
noncomputable abbrev thickeningLiftReduction (c : X ⟶ W) :
    thickeningLiftRingSheaf B S hS Z c ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ≫ c)).pushforward
        (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :=
  pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ≫ c)).pushforward
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- **The chart reading of a morphism `𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)`, after the structure map of
`i`, depends on the morphism only through its reduction.**

The structure map of `i` is the unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` followed by the direct image of
the reduction, and the chart reading is the value of the morphism over `V` read on the chart and
brought back along `η`; so `η` cancels and what is left is the chart reading of the reduction,
the chart projection and the comparison of iterated direct images both being natural in the
sheaf of rings. -/
theorem app_structureSharp_thickeningLiftChartAppTop_eq (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app j.right
        (thickeningLiftChartAppTop B S hS Z hZ c a V j b) =
      (directImageChartProjection B S hS c V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
            (CategoryTheory.forget RingCat.{u})).obj
          ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).obj
            (structureRingSheaf B S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))))
        ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
              (structureRingSheaf B S hS
                (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).hom.app (op V)
          ((a ≫ thickeningLiftReduction B S hS Z c).hom.app (op V) b)) := by
  refine (ringSheafHom_congr_app_apply
    (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z) j.right
    (thickeningLiftChartAppTop B S hS Z hZ c a V j b)).symm.trans ?_
  refine (ringSheafHom_comp_app_apply (thickeningRingUnit B S hS Z)
    (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)))
    j.right (thickeningLiftChartAppTop B S hS Z hZ c a V j b)).trans ?_
  refine Eq.trans (congrArg
    (fun z ↦ (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).hom.app j.right z)
    (thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c a V j b)) ?_
  refine (app_pullbackRingSheafMap_natTrans (SmallEtale.topology B S hS W.1)
    (SmallEtale.topology B S hS X.1) (smallEtaleDirectImage B S hS c)
    (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (op V) j.right (directImageChartProjection B S hS c V j) _).symm.trans ?_
  refine congrArg
    (fun z ↦ (directImageChartProjection B S hS c V j).app
      ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj
        ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z))).obj
          (structureRingSheaf B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)))) z) ?_
  refine (ringSheafHom_comp_app_apply
    (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
      (smallEtaleDirectImage B S hS c)
      (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))))
    (op V) (a.hom.app (op V) b)).symm.trans ?_
  refine (ringSheafHom_congr_app_apply
    (pushforwardRingSheafCompInv_naturality B S hS (subspaceInclusion B S hS X Z) c
      (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS X Z))).symm (op V) (a.hom.app (op V) b)).trans ?_
  refine (ringSheafHom_comp_app_apply (thickeningLiftReduction B S hS Z c)
    (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheaf B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)))
    (op V) (a.hom.app (op V) b)).trans ?_
  exact congrArg
    (fun z ↦ (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheaf B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).hom.app (op V) z)
    (ringSheafHom_comp_app_apply a (thickeningLiftReduction B S hS Z c) (op V) b).symm

/-- **Two morphisms with the same reduction have chart readings which the structure map of `i`
identifies.**  Their difference is therefore a section of the defining ideal of the thickening
at the chart, by `AlgebraicGeometry.Space.definingIdealAt`. -/
theorem app_structureSharp_thickeningLiftChartAppTop_congr (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a a' : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      a' ≫ thickeningLiftReduction B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app j.right
        (thickeningLiftChartAppTop B S hS Z hZ c a V j b) =
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app j.right
        (thickeningLiftChartAppTop B S hS Z hZ c a' V j b) := by
  have h := app_structureSharp_thickeningLiftChartAppTop_eq B S hS Z hZ c a V j b
  rw [hred] at h
  exact h.trans (app_structureSharp_thickeningLiftChartAppTop_eq B S hS Z hZ c a' V j b).symm

/-! ### The reduction at an index given by an equation -/

/-- **The transport to the tautological index preserves the reduction.**  A solution of the
lifting problem indexed by a morphism `e` out of the thickening with `i ≫ c = e`, read at the
index `i ≫ c` by `AlgebraicGeometry.Space.thickeningLiftOfIndex`, still has the comorphism of
`i ≫ c` for its reduction. -/
theorem thickeningLiftOfIndex_comp_reduction (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e)
    (a : structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (hred : a ≫ pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS e).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
        structureSharp B S hS e) :
    thickeningLiftOfIndex B S hS Z c e h a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c) := by
  subst h
  simpa only [thickeningLiftOfIndex, eqToHom_refl, Category.comp_id] using hred

/-! ### The chart reading agrees with the chartwise pullback on the thickening -/

/-- **A morphism whose reduction is the comorphism of `i ≫ c` has, on the chart of the
thickening, the chartwise pullback of `c` for its chart reading.**

This is
`AlgebraicGeometry.Space.app_structureSharp_thickeningLiftChartAppTop_congr` compared against
the comorphism of `c` read through the thickening, whose reduction is the comorphism of `i ≫ c`
(`AlgebraicGeometry.Space.structureSharpThroughThickening_comp_reduction`) and whose chart
reading is the chartwise pullback
(`AlgebraicGeometry.Space.thickeningLiftChartAppTop_structureSharpThroughThickening`). -/
theorem app_structureSharp_thickeningLiftChartAppTop_eq_chartPullback
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app j.right
        (thickeningLiftChartAppTop B S hS Z hZ c a V j b) =
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app j.right
        (chartPullbackRingHom B S hS c V j b) :=
  (app_structureSharp_thickeningLiftChartAppTop_congr B S hS Z hZ c a
      (structureSharpThroughThickening B S hS Z c)
      (hred.trans (structureSharpThroughThickening_comp_reduction B S hS Z c).symm) V j b).trans
    (congrArg
      (fun z : ToType ((structureRingSheaf B S hS X).obj.obj j.right) ↦
        (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app j.right z)
      (DFunLike.congr_fun
        (thickeningLiftChartAppTop_structureSharpThroughThickening B S hS Z hZ c V j) b))

/-- **The chart reading of such a morphism differs from the chartwise pullback of `c` by a
section of the defining ideal of the thickening at the chart.**

`AlgebraicGeometry.Space.definingIdealAt` *is* the kernel of the structure map of `i` on the
sections over the chart, so this is the previous statement rephrased; and
`AlgebraicGeometry.Space.definingIdealAt_eq_ker` identifies that ideal with the kernel of
restriction of regular functions along the closed immersion of schemes `Z ×_X V' ⟶ V'`.  So the
two maps of regular functions `Γ(V, ⊤) ⟶ Γ(V', ⊤)` agree after restriction to the chart of the
thickening, which is the second clause of the lifting condition
`AlgebraicGeometry.Space.IsChartLift` over an affine chart `V`. -/
theorem sub_thickeningLiftChartAppTop_mem_definingIdealAt
    (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    thickeningLiftChartAppTop B S hS Z hZ c a V j b -
        chartPullbackRingHom B S hS c V j b ∈ definingIdealAt B S hS X Z j.right :=
  RingHom.mem_ker.2 (by
    rw [map_sub,
      app_structureSharp_thickeningLiftChartAppTop_eq_chartPullback B S hS Z hZ c a hred V j b,
      sub_self])

/-! ### Clause 2 of the lifting condition, over an affine chart -/

/-- **The morphism of charts attached to a morphism whose reduction is the comorphism of `i ≫ c`
agrees, on the chart of the thickening, with the morphism of charts `c` itself induces.**

Both are morphisms of schemes from the chart `Z ×_X V'` of the thickening into the affine chart
`V` of `W`, so `AlgebraicGeometry.ext_of_isAffine` applies, and what has to be checked is that
their maps of regular functions agree after restriction along `Z ×_X V' ⟶ V'` — which is
`AlgebraicGeometry.Space.sub_thickeningLiftChartAppTop_mem_definingIdealAt` read through
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`.

For `c` a section of a morphism and `a` a solution of the lifting problem this is the second
clause of the lifting condition `AlgebraicGeometry.Space.IsChartLift`: the attached morphism of
charts restricts on the thickening to the restriction of `c`. -/
theorem comp_rep_snd_thickeningLiftChartHom_eq (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))] :
    (BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd j.right.unop.1.hom) ≫
        thickeningLiftChartHom B S hS Z hZ c a V j =
      (BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd j.right.unop.1.hom) ≫
        (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c V j) := by
  refine comp_eq_of_appTop_apply_eq _ fun b ↦ ?_
  have hker : thickeningLiftChartAppTop B S hS Z hZ c a V j b -
        chartPullbackRingHom B S hS c V j b ∈
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd j.right.unop.1.hom)).op).hom :=
    definingIdealAt_eq_ker B S hS X Z j.right.unop ▸
      sub_thickeningLiftChartAppTop_mem_definingIdealAt B S hS Z hZ c a hred V j b
  have hmem : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (Z.2.2.rep.snd j.right.unop.1.hom)).op).hom
          (thickeningLiftChartAppTop B S hS Z hZ c a V j b) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (Z.2.2.rep.snd j.right.unop.1.hom)).op).hom
        (chartPullbackRingHom B S hS c V j b) :=
    sub_eq_zero.mp ((map_sub _ _ _).symm.trans (RingHom.mem_ker.mp hker))
  rw [Scheme.Γ_map_op] at hmem
  have hR : (((BigFppfOver.toScheme B S hS).map
        (chartBaseChangeMap B S hS c V j)).appTop).hom b =
      chartPullbackRingHom B S hS c V j b :=
    toScheme_map_chartBaseChangeMap_appTop B S hS c V j b
  rwa [thickeningLiftChartHom_appTop, hR]

/-- **The same for a morphism of the site lifting the attached morphism of charts.**  The
functor from the big fppf category over `S` to schemes is faithful, so the equation of schemes is
an equation of the site. -/
theorem comp_rep_snd_eq_of_toScheme_map_eq (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ c a V j) :
    Z.2.2.rep.snd j.right.unop.1.hom ≫ ψ =
      Z.2.2.rep.snd j.right.unop.1.hom ≫ chartBaseChangeMap B S hS c V j :=
  (BigFppfOver.toScheme B S hS).map_injective
    (((BigFppfOver.toScheme B S hS).map_comp _ ψ).trans
      (((congrArg (fun z ↦ (BigFppfOver.toScheme B S hS).map
              (Z.2.2.rep.snd j.right.unop.1.hom) ≫ z) hψ).trans
          (comp_rep_snd_thickeningLiftChartHom_eq B S hS Z hZ c a hred V j)).trans
        ((BigFppfOver.toScheme B S hS).map_comp _
          (chartBaseChangeMap B S hS c V j)).symm))

/-- **Clause 2 of the lifting condition `AlgebraicGeometry.Space.IsChartLift`.**  The section of
`W` over the chart `V'` of `X` given by the attached morphism of charts followed by the chart
`V ⟶ W` agrees with the restriction of `c` to the thickening on every point of `V'` lying in
`Z`.

A point of `V'` lying in `Z` factors through the chart `Z ×_X V'` of the thickening, the
thickening being representable over `X`, and there the attached morphism of charts is the one
`c` induces, by
`AlgebraicGeometry.Space.comp_rep_snd_eq_of_toScheme_map_eq`. -/
theorem yoneda_map_comp_chart_hom_eq_restriction (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ c a V j)
    (Ww : BigFppfOver B S hS) (k : Ww ⟶ (SmallEtale.toOver B S hS X.1).obj j.right.unop)
    (t : yoneda.obj Ww ⟶ Z.1.toFunctor)
    (hkt : yoneda.map k ≫ j.right.unop.1.hom = t ≫ Z.1.ι) :
    yoneda.map k ≫ yoneda.map ψ ≫ V.1.hom = t ≫ Z.1.ι ≫ c.hom := by
  have hk : k ≫ ψ = k ≫ chartBaseChangeMap B S hS c V j := by
    rw [← Z.2.2.rep.lift_snd t k hkt.symm, Category.assoc, Category.assoc,
      comp_rep_snd_eq_of_toScheme_map_eq B S hS Z hZ c a hred V j ψ hψ]
  have hj : yoneda.map (chartBaseChangeMap B S hS c V j) ≫ V.1.hom =
      j.right.unop.1.hom ≫ c.hom :=
    (chartBaseChangeMap_comm B S hS c j.right.unop V j.hom.unop).symm
  rw [← Functor.map_comp_assoc, hk, Functor.map_comp_assoc, hj, reassoc_of% hkt]

end Space

end AlgebraicGeometry

end
