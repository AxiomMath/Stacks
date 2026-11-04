module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafRingUnit

/-!
# The two comorphisms of two morphisms agreeing on a thickening, in one sheaf of rings

Let `Z ⊂ X` be a thickening of algebraic spaces over a scheme `S`, with inclusion `i : Z ⟶ X`,
and let `c : X ⟶ W` be a morphism.  The comorphism `c^♯ : 𝒪_W ⟶ c_*𝒪_X` of
[Stacks Project, Tag 03G8], composed with the direct image of the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` and
with the comparison of iterated direct images, is a morphism of sheaves of rings

`𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)`.

The point is that the target depends on `c` **only through the composite `i ≫ c`**.  So two
morphisms `a, b : X ⟶ W` which agree on the thickening — `i ≫ a = i ≫ b`, which is hypothesis
(1) of [Stacks Project, Tag 0618] — have their two comorphisms in one and the same sheaf of
rings, where their difference can be formed, and no comparison of the two direct images
`a_*𝒪_X` and `b_*𝒪_X` has to be chosen.  Carrying `𝒪_X` along the unit loses nothing: the unit
is an isomorphism, by
`AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`.

The agreement of the two maps after the reduction `i^{-1}𝒪_X ⟶ 𝒪_Z` is then immediate, and is
the other half of what the difference of two lifts needs: both composites are the comorphism of
the single morphism `i ≫ a = i ≫ b`, so the difference takes its values in the sectionwise
kernel of the reduction.  This is the step which in the direct-image presentation needs the
comparison isomorphism of [Stacks Project, Tag 05ZM] to be compatible with the restriction to
the thickening; here it is the composition law of [Stacks Project, Tag 03G8] together with the
adjunction, and nothing else.

## Main definitions

* `AlgebraicGeometry.Space.thickeningLiftRingSheaf`: the sheaf of rings
  `(i ≫ c)_*(i^{-1}𝒪_X)` in which the comorphisms are compared.
* `AlgebraicGeometry.Space.structureSharpThroughThickening`: the comorphism of `c` read in it,
  and `AlgebraicGeometry.Space.structureSharpThroughThickeningAt` the same read in the direct
  image along a morphism the composite `i ≫ c` is equal to, which is the form in which two
  morphisms agreeing on the thickening give two morphisms with one source and one target.

## Main results

* `Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans_naturality`: the morphism of
  inverse images induced by a natural transformation of the transporting functors is natural in
  the sheaf of rings.
* `Stacks.Sites.sub_mem_ker_of_comp_eq`: the sectionwise difference of two morphisms of sheaves
  of rings agreeing after a third takes its values in the sectionwise kernel of that third.
* `AlgebraicGeometry.Space.structureSharp_comp`: **[Stacks Project, Tag 03G8], compatibility
  with composition, at sheaves of rings.**  The set-level statement
  `AlgebraicGeometry.Space.structureSharpSet_comp` lifted through the faithful
  `CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`.
* `AlgebraicGeometry.Space.structureSharpThroughThickening_comp_reduction`: **the comorphism
  read in `(i ≫ c)_*(i^{-1}𝒪_X)`, followed by the reduction `i^{-1}𝒪_X ⟶ 𝒪_Z`, is the
  comorphism of `i ≫ c`.**  In particular it depends on `c` only through `i ≫ c`, which is the
  hypothesis the difference of two lifts consumes.
* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp_reduction_eq`: **the two
  comorphisms of two morphisms agreeing on the thickening agree after the reduction**, so their
  sectionwise difference takes its values in the sectionwise kernel of the reduction.  This is
  hypothesis (1) of [Stacks Project, Tag 0618] in usable form.

## Implementation notes

The comparison of iterated direct images is used in two pieces: the identification
`Stacks.Sheaves.ToposPullback.pullbackRingSheafComp` of the ring structure transported in two
steps with the ring structure transported in one — the identity on underlying sheaves of sets —
and `AlgebraicGeometry.Space.pullbackRingSheafMapOfNatTrans` at the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of the direct image along a composite
with the composite of the direct images.  Both are natural in the sheaf of rings, which is what
lets the reduction be moved across them.

Every proof here is a computation of underlying morphisms of sheaves of sets, lifted through the
faithfulness of `CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`.  That is the
only way the ring-level composition law is available: [Stacks Project, Tag 03G8]'s compatibility
with composition is carried in this development on underlying sheaves of sets, as
`AlgebraicGeometry.Space.structureSharpSet_comp`, and at sheaves of *commutative* rings, as
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp`, while the sheaves of modules of
this development are indexed over `RingCat`-valued sheaves of rings.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']

/-- **The morphism of inverse images induced by a natural transformation is natural in the sheaf
of rings.**  Both sides have the transformation composed with the inverse image of the given
morphism as their underlying morphism of sheaves of sets, in the two orders, and those agree by
naturality of the transformation. -/
theorem pullbackRingSheafMapOfNatTrans_naturality (θ : Φ ⟶ Φ')
    {O O' : Sheaf K RingCat.{ww'}} (a : O ⟶ O') :
    pullbackRingSheafMapOfNatTrans J O θ ≫ pullbackRingSheafMap J Φ' a =
      pullbackRingSheafMap J Φ a ≫ pullbackRingSheafMapOfNatTrans J O' θ := by
  refine (sheafCompose J (CategoryTheory.forget RingCat.{ww})).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, ringSheafMap_pullbackRingSheafMapOfNatTrans,
    ringSheafMap_pullbackRingSheafMapOfNatTrans, ringSheafMap_pullbackRingSheafMap,
    ringSheafMap_pullbackRingSheafMap]
  exact (θ.naturality _).symm

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sites

universe v₁ u₁ w₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- **The sectionwise difference of two morphisms of sheaves of rings which agree after a third
morphism takes its values in the sectionwise kernel of that morphism.**  For the two comorphisms
of two morphisms agreeing on a thickening, read in one sheaf of rings, and the reduction to the
thickening, this is the statement that the difference of the two lifts is a section of the ideal
of the thickening. -/
theorem sub_mem_ker_of_comp_eq {A E Q : Sheaf J RingCat.{w₁}} (f g : A ⟶ E) (ρ : E ⟶ Q)
    (hρ : f ≫ ρ = g ≫ ρ) (V : Cᵒᵖ) (x : A.obj.obj V) :
    f.hom.app V x - g.hom.app V x ∈ RingHom.ker (ρ.hom.app V).hom := by
  have h : (ρ.hom.app V).hom (f.hom.app V x) = (ρ.hom.app V).hom (g.hom.app V x) :=
    ConcreteCategory.congr_hom (congrArg (fun t : A ⟶ Q ↦ t.hom.app V) hρ) x
  rw [RingHom.mem_ker, map_sub, h, sub_self]

end Stacks.Sites

namespace AlgebraicGeometry.Space

universe u

/-- The associativity bookkeeping of a four-fold composite whose last three factors are moved
across three given equations.  It is stated separately because the terms it is applied to are
large and because `rw` is not reliable at them. -/
private theorem comp_eq_of_steps {C : Type*} [Category C] {P₀ P Q₁ Q₂ Q₃ Q₁' Q₂' R : C}
    (s : P₀ ⟶ P) (u : P ⟶ Q₁) (k : Q₁ ⟶ Q₂) (n : Q₂ ⟶ Q₃) (r : Q₃ ⟶ R)
    (σ : Q₂ ⟶ Q₂') (n' : Q₂' ⟶ R) (τ : Q₁ ⟶ Q₁') (k' : Q₁' ⟶ Q₂') (v : P ⟶ Q₁')
    (h1 : n ≫ r = σ ≫ n') (h2 : τ ≫ k' = k ≫ σ) (h3 : u ≫ τ = v) :
    (s ≫ u ≫ k ≫ n) ≫ r = s ≫ v ≫ k' ≫ n' :=
  calc (s ≫ u ≫ k ≫ n) ≫ r = s ≫ u ≫ k ≫ n ≫ r := by simp only [Category.assoc]
    _ = s ≫ u ≫ k ≫ σ ≫ n' := by rw [h1]
    _ = s ≫ u ≫ (τ ≫ k') ≫ n' := by rw [h2, Category.assoc]
    _ = s ≫ v ≫ k' ≫ n' := by simp only [← h3, Category.assoc]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The composition law of Stacks 03G8 at sheaves of rings -/

section Comp

variable {V₁ V₂ V₃ : AlgebraicSpaces B S hS}

/-- **[Stacks Project, Tag 03G8], compatibility with composition, at sheaves of rings.**  The
comorphism of `g` followed by the direct image of the comorphism of `f` and by the comparison of
iterated direct images is the comorphism of `f ≫ g`.

This is `AlgebraicGeometry.Space.structureSharpSet_comp` lifted through the faithful
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`; the comparison is the
identity on underlying sheaves of sets in its first factor and
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` in its second. -/
theorem structureSharp_comp (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) :
    structureSharp B S hS g ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS g)).map
          (structureSharp B S hS f) ≫
        (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1)
            (SmallEtale.topology B S hS V₃.1)
            (smallToposMorphismTypeU B S hS f).pushforward
            (smallToposMorphismTypeU B S hS g).pushforward
            (structureRingSheaf B S hS V₁)).hom ≫
        pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS V₃.1)
          (structureRingSheaf B S hS V₁)
          (smallToposMorphismTypeU_comp B S hS f g).hom =
      structureSharp B S hS (f ≫ g) := by
  refine (sheafCompose (SmallEtale.topology B S hS V₃.1)
    (CategoryTheory.forget RingCat.{u})).map_injective ?_
  simp only [Functor.map_comp, pullbackRingSheafFunctor_map]
  exact structureSharpSet_comp B S hS f g

end Comp

/-! ### The comorphism read in the direct image along the composite -/

section Thickening

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (c : X ⟶ W)

/-- **The sheaf of rings in which the comorphisms of the morphisms agreeing on a thickening are
compared:** the direct image along `i ≫ c` of the inverse image `i^{-1}𝒪_X` of the structure
sheaf of the ambient space of the thickening `Z ⊂ X`.

It depends on `c` only through the composite `i ≫ c`, which is what makes it a common target
for the comorphisms of two morphisms agreeing on the thickening. -/
noncomputable abbrev thickeningLiftRingSheaf :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ≫ c)).pushforward
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- **The comorphism of `c : X ⟶ W` read in `(i ≫ c)_*(i^{-1}𝒪_X)`:** the comorphism
`c^♯ : 𝒪_W ⟶ c_*𝒪_X` of [Stacks Project, Tag 03G8] followed by the direct image of the unit
`𝒪_X ⟶ i_*i^{-1}𝒪_X` of `i^{-1} ⊣ i_*` and by the comparison of iterated direct images. -/
noncomputable def structureSharpThroughThickening :
    structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c :=
  structureSharp B S hS c ≫
    (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
      (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
        (structureRingSheaf B S hS X)) ≫
    (pullbackRingSheafComp (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
        (smallToposMorphismTypeU B S hS c).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom ≫
    pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS W.1)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
      (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c).hom

/-- The defining equation of `AlgebraicGeometry.Space.structureSharpThroughThickening`, stated
so that consumers rewrite with it rather than unfold the definition. -/
theorem structureSharpThroughThickening_eq :
    structureSharpThroughThickening B S hS Z c =
      structureSharp B S hS c ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
          (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
            (structureRingSheaf B S hS X)) ≫
        (pullbackRingSheafComp (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS W.1)
            (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
            (smallToposMorphismTypeU B S hS c).pushforward
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom ≫
        pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS W.1)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
          (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c).hom :=
  rfl

/-- **The comorphism read in `(i ≫ c)_*(i^{-1}𝒪_X)`, followed by the reduction
`i^{-1}𝒪_X ⟶ 𝒪_Z`, is the comorphism of `i ≫ c`.**

So it depends on `c` only through the composite `i ≫ c`: two morphisms agreeing on the
thickening have comorphisms which agree after the reduction, which is what makes their
difference take its values in the sectionwise kernel of the reduction. -/
theorem structureSharpThroughThickening_comp_reduction :
    structureSharpThroughThickening B S hS Z c ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ≫ c)).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c) := by
  have hnat := pullbackRingSheafMapOfNatTrans_naturality (SmallEtale.topology B S hS W.1)
    (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c).hom
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
  have hcomp := pullbackRingSheafComp_naturality (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS W.1)
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
    (smallToposMorphismTypeU B S hS c).pushforward
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
  have hmap : (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
        (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
          (structureRingSheaf B S hS X)) ≫
      pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS c).pushforward
        (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))) =
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
        (structureSharp B S hS (subspaceInclusion B S hS X Z)) :=
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map_comp _ _).symm.trans
      (congrArg (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
        (ringUnit_comp_map_structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z)))
  refine Eq.trans ?_ (structureSharp_comp B S hS (subspaceInclusion B S hS X Z) c)
  rw [structureSharpThroughThickening_eq]
  exact comp_eq_of_steps _ _ _ _ _ _ _ _ _ _ hnat hcomp hmap

end Thickening

/-! ### Two morphisms agreeing on the thickening -/

section Pair

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The comorphism of `c : X ⟶ W`, read in the direct image along a morphism `e` that the
composite `i ≫ c` is equal to.**  For two morphisms `a, b : X ⟶ W` agreeing on the thickening
this is a pair of morphisms of sheaves of rings with one and the same source and target, at
`e := i ≫ a = i ≫ b`. -/
noncomputable def structureSharpThroughThickeningAt (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e) :
    structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  structureSharpThroughThickening B S hS Z c ≫
    eqToHom (congrArg (fun m : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W ↦
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS m).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) h)

/-- The comorphism of `c` read in the direct image along `e = i ≫ c`, followed by the reduction
`i^{-1}𝒪_X ⟶ 𝒪_Z`, is the comorphism of `e`. -/
theorem structureSharpThroughThickeningAt_comp_reduction (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = e) :
    structureSharpThroughThickeningAt B S hS Z c e h ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS e).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharp B S hS e := by
  subst h
  rw [structureSharpThroughThickeningAt, eqToHom_refl, Category.comp_id]
  exact structureSharpThroughThickening_comp_reduction B S hS Z c

/-- **The two comorphisms of two morphisms agreeing on a thickening agree after the
reduction.**  This is hypothesis (1) of [Stacks Project, Tag 0618] in the form the difference of
the two lifts consumes: the sectionwise difference of the two comorphisms, which is formed in
the single sheaf of rings `(i ≫ a)_*(i^{-1}𝒪_X)`, takes its values in the sectionwise kernel of
the reduction `i^{-1}𝒪_X ⟶ 𝒪_Z`. -/
theorem structureSharpThroughThickeningAt_comp_reduction_eq (a b : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (ha : subspaceInclusion B S hS X Z ≫ a = e)
    (hb : subspaceInclusion B S hS X Z ≫ b = e) :
    structureSharpThroughThickeningAt B S hS Z a e ha ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS e).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpThroughThickeningAt B S hS Z b e hb ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS e).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  (structureSharpThroughThickeningAt_comp_reduction B S hS Z a e ha).trans
    (structureSharpThroughThickeningAt_comp_reduction B S hS Z b e hb).symm

end Pair

end AlgebraicGeometry.Space

end
