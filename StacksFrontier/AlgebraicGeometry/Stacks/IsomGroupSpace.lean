module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PseudoTorsors
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria

/-!
# The Isom algebraic spaces of an algebraic stack (Stacks 04YP)

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, let `T` be a
scheme of that site and let `x` and `y` be objects of the fibre category of `𝒳` over `T`.
**Stacks 04YP** says that

1. `Isom_𝒳(y, y)` is a *group algebraic space* over `T`, and
2. `Isom_𝒳(x, y)` is a *pseudo-torsor* for `Isom_𝒳(y, y)` over `T`.

Here `Isom_𝒳(x, y)` is the presheaf on the big fppf site of `T` whose sections over `V ⟶ T` are
the isomorphisms between the restrictions of `x` and `y` to `V`; it is an algebraic space because
the diagonal of `𝒳` is representable by algebraic spaces, which is condition (2) of
**Stacks 045G**. The group law of `Isom_𝒳(y, y)` is composition of local automorphisms and the
action on `Isom_𝒳(x, y)` is postcomposition; the pseudo-torsor condition is then the statement
that for two local isomorphisms `p, q : x ⟶ y` there is a unique local automorphism `g` of `y`
with `p ≫ g = q`, namely `p⁻¹ ≫ q`.

## Main definitions

* `AlgebraicGeometry.Stack.isomSpace`: `Isom_𝒳(x, y)`, as a presheaf on the big fppf site of `T`.
* `AlgebraicGeometry.Stack.siteTerminalSpace`: the base algebraic space, `T` read on its own
  site.
* `AlgebraicGeometry.Stack.isomSpaceComp` and `AlgebraicGeometry.Stack.isomSpaceSmul`:
  composition of local automorphisms and postcomposition by one.
* `AlgebraicGeometry.Stack.isomSpaceGrpObj` and
  `AlgebraicGeometry.Stack.isomSpaceOverGrpObj`: the group object structure on `Isom_𝒳(y, y)`,
  on the site of `T` and over the base algebraic space.
* `AlgebraicGeometry.Stack.isomSpaceOverModObj`: the action of `Isom_𝒳(y, y)` on
  `Isom_𝒳(x, y)`.
* `AlgebraicGeometry.Stack.automorphismGroupSpace`: **Stacks 04YP**, part (1), the group
  algebraic space of automorphisms.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpace_isomSpace`: `Isom_𝒳(x, y)` is an algebraic space.
* `AlgebraicGeometry.Stack.isomSpaceOverGrpObj_mul` and
  `AlgebraicGeometry.Stack.isomSpaceOverModObj_smul`: the group law and the action are
  composition and postcomposition of local isomorphisms.
* `AlgebraicGeometry.Stack.isomSpaceOver_isPseudoTorsor`: **Stacks 04YP**, part (2).

## Implementation notes

The two parts of Stacks 04YP are formalized as structures on the *canonical* objects rather than as
existential statements identifying some group algebraic space with `Isom_𝒳(y, y)`: the group law,
the action and the pseudo-torsor condition are all asserted of
`AlgebraicGeometry.Stack.isomSpaceOver`, whose underlying presheaf is `Isom_𝒳(x, y)` by
definition. This is why no transport of structure along an equality of presheaves appears
anywhere below.

The group-object and module-object structures of Stacks 043H and 043Q are structures on an object
*over a base*, while `Isom_𝒳(x, y)` is a presheaf on the site of `T`; the passage is
`CategoryTheory.Over.equivalenceOfIsTerminal` at the base algebraic space, which is a final
object of presheaves on that site. That equivalence is monoidal because both categories are
cartesian monoidal, so `CategoryTheory.Functor.grpObjObj` transports the group object. Mathlib
has no module-object analogue of `CategoryTheory.Functor.grpObjObj`, so
`AlgebraicGeometry.Stack.modObjOfMonoidal` supplies it. That declaration is a statement about an
arbitrary monoidal functor and nothing about stacks: it belongs in `CategoryTheory.Monoidal`, and
is kept here only because this is its single consumer.

A section of `Isom_𝒳(y, y)` over `V` is a morphism of the fibre category together with a proof
that it belongs to `CategoryTheory.Functor.isomSubpresheaf`, i.e. that it is an isomorphism. The
group structure on sections is therefore the one of `CategoryTheory.Aut` of the restriction of
`y`, transported along that bijection; this is only used to get the inverse and the group
identities on sections, which is what the `CategoryTheory.GrpObj` fields reduce to after
`CategoryTheory.NatTrans.ext`.

## References

* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0498](https://stacks.math.columbia.edu/tag/0498)
* [Stacks Project, Tag 04TW](https://stacks.math.columbia.edu/tag/04TW)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u v w

namespace AlgebraicGeometry.Stack

/-- **A module object is carried along a monoidal functor.** If `K` is a monoidal functor, `M` a
monoid object of its source, `X` a module object over `M`, and `M'` a monoid structure on `K M`
whose unit and multiplication are the images of those of `M`, then `K X` is a module object over
`K M`, with the image action.

This is the module-object analogue of Mathlib's `CategoryTheory.Functor.grpObjObj`, which Mathlib
does not have; it is a statement about an arbitrary monoidal functor and belongs in
`CategoryTheory.Monoidal`. -/
@[instance_reducible]
def modObjOfMonoidal
    {C D : Type*} [Category.{v} C] [MonoidalCategory C]
    [Category.{w} D] [MonoidalCategory D]
    (K : C ⥤ D) [K.Monoidal]
    {M X : C} [MonObj M] [ModObj M X] (M' : MonObj (K.obj M))
    (hone : Functor.LaxMonoidal.ε K ≫ K.map η[M] = M'.one)
    (hmul : Functor.LaxMonoidal.μ K M M ≫ K.map μ[M] = M'.mul) :
    ModObj (K.obj M) (K.obj X) where
  smul := Functor.LaxMonoidal.μ K M X ≫ K.map γ[M, X]
  one_smul := by
    rw [← hone]
    change (Functor.LaxMonoidal.ε K ≫ K.map η[M]) ▷ K.obj X ≫
      Functor.LaxMonoidal.μ K M X ≫ K.map γ[M, X] = _
    calc
      _ = Functor.LaxMonoidal.ε K ▷ K.obj X ≫
          Functor.LaxMonoidal.μ K (𝟙_ C) X ≫ K.map ((η[M] ▷ X) ≫ γ[M, X]) := by
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
          Functor.LaxMonoidal.μ_natural_left_assoc, ← K.map_comp]
      _ = Functor.LaxMonoidal.ε K ▷ K.obj X ≫
          Functor.LaxMonoidal.μ K (𝟙_ C) X ≫ K.map (λ_ X).hom := by
        congr 4
        exact ModObj.one_smul (M := M) X
      _ = _ := by simp
  mul_smul := by
    rw [← hmul]
    change (Functor.LaxMonoidal.μ K M M ≫ K.map μ[M]) ▷ K.obj X ≫
      Functor.LaxMonoidal.μ K M X ≫ K.map γ[M, X] = _
    calc
      _ = Functor.LaxMonoidal.μ K M M ▷ K.obj X ≫
          Functor.LaxMonoidal.μ K (M ⊗ M) X ≫ K.map ((μ[M] ▷ X) ≫ γ[M, X]) := by
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
          Functor.LaxMonoidal.μ_natural_left_assoc, ← K.map_comp]
      _ = Functor.LaxMonoidal.μ K M M ▷ K.obj X ≫
          Functor.LaxMonoidal.μ K (M ⊗ M) X ≫
            K.map ((α_ M M X).hom ≫ M ◁ γ[M, X] ≫ γ[M, X]) := by
        rw [show (μ[M] ▷ X) ≫ γ[M, X] =
          (α_ M M X).hom ≫ M ◁ γ[M, X] ≫ γ[M, X] from by
            simp]
      _ = (α_ (K.obj M) (K.obj M) (K.obj X)).hom ≫
          K.obj M ◁ Functor.LaxMonoidal.μ K M X ≫
            Functor.LaxMonoidal.μ K M (M ⊗ X) ≫ K.map (M ◁ γ[M, X]) ≫
              K.map γ[M, X] := by
        simp only [Functor.map_comp, Functor.LaxMonoidal.associativity_assoc]
      _ = (α_ (K.obj M) (K.obj M) (K.obj X)).hom ≫
          K.obj M ◁ (Functor.LaxMonoidal.μ K M X ≫ K.map γ[M, X]) ≫
            Functor.LaxMonoidal.μ K M X ≫ K.map γ[M, X] := by
        simp only [Category.assoc, ← Functor.LaxMonoidal.μ_natural_right_assoc,
          MonoidalCategory.whiskerLeft_comp]

/-- `Isom_𝒳(x, y)`, the presheaf of isomorphisms between two objects `x` and `y` of the fibre
category of `𝒳` over a scheme `U` of the big fppf site of `S`, read as a presheaf on the big
fppf site of `U` itself: its sections over `V ⟶ U` are the isomorphisms between the restrictions
of `x` and `y` to `V`.

This is `CategoryTheory.Functor.isomPresheaf` reindexed along
`CategoryTheory.Over.iteratedSliceBackward`, which is the presheaf whose algebraicity is
condition (2) of Stacks 045G
(`AlgebraicGeometry.Stack.IsAlgebraicSpaceIsomPresheaf`). -/
abbrev isomSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) :
    (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  (Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.isomPresheaf x y

/-- The algebraic space over which the Isom spaces of objects over `U` live: the presheaf
represented by the terminal object of the big fppf site of `U`, i.e. `U` itself read on its own
site. It is the final object of that site, so an algebraic space over it is just an algebraic
space. -/
abbrev siteTerminalSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) :=
  yoneda.obj (⊤_ (BigFppfOver B U.left.1 U.left.2))

/-- `AlgebraicGeometry.Stack.siteTerminalSpace` is a final object of the category of presheaves
on the big fppf site of `U`: it is represented by the terminal object of that site, and the
Yoneda embedding preserves terminal objects. -/
noncomputable def isTerminal_siteTerminalSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) :
    Limits.IsTerminal (siteTerminalSpace B S hS U) := by
  change Limits.IsTerminal
    (yoneda.obj (⊤_ (BigFppfOver B U.left.1 U.left.2)))
  have hT : Limits.IsTerminal
      (⊤_ (BigFppfOver B U.left.1 U.left.2)) := Limits.terminalIsTerminal
  apply CategoryTheory.Functor.isTerminal
  intro V
  change Limits.IsTerminal (V.unop ⟶ ⊤_ (BigFppfOver B U.left.1 U.left.2))
  let hV : ∀ (Y : Type u), Y ⟶ (V.unop ⟶
      ⊤_ (BigFppfOver B U.left.1 U.left.2)) :=
    fun Y => TypeCat.ofHom (fun _ : Y => hT.from V.unop)
  refine Limits.IsTerminal.ofUniqueHom
    hV ?_
  intro X f
  ext x
  exact congrArg (fun g : V.unop ⟶
      ⊤_ (BigFppfOver B U.left.1 U.left.2) => g.left.hom)
    (hT.hom_ext ((ConcreteCategory.hom f).toFun x) (hT.from V.unop))

/-- The group law of `Isom_𝒳(y, y)`: reverse categorical composition of local automorphisms,
`(a, b) ↦ b ≫ a`. The order is reversed so that postcomposition
(`AlgebraicGeometry.Stack.isomSpaceSmul`) is a *left* action. -/
noncomputable def isomSpaceComp (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (a b : (isomSpace B S hS 𝒳 U y y).obj V) :
    (isomSpace B S hS 𝒳 U y y).obj V :=
  ⟨b.1 ≫ a.1, by
    change IsIso (b.1 ≫ a.1)
    exact IsIso.comp_isIso' b.2 a.2⟩

/-- The action of `Isom_𝒳(y, y)` on `Isom_𝒳(x, y)`: postcomposition of a local isomorphism
`x ⟶ y` by a local automorphism of `y`. -/
noncomputable def isomSpaceSmul (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (p : (isomSpace B S hS 𝒳 U x y).obj V)
    (g : (isomSpace B S hS 𝒳 U y y).obj V) :
    (isomSpace B S hS 𝒳 U x y).obj V :=
  ⟨p.1 ≫ g.1, by
    change IsIso (p.1 ≫ g.1)
    exact IsIso.comp_isIso' p.2 g.2⟩

private lemma isIso_isomSpace_coe (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    (a : (isomSpace B S hS 𝒳 U y y).obj V) → IsIso a.1 := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  intro a
  have hmem := a.2
  change a.1 ∈ (𝒳.val.p.isomSubpresheaf y y).obj _ at hmem
  exact (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U) y y a.1).mp hmem

private def isomSpaceSelfEquivAut (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    [𝒳.val.p.IsPreFibered]
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    (isomSpace B S hS 𝒳 U y y).obj V ≃
      Aut (𝒳.val.p.pullbackFiber y ((Over.iteratedSliceBackward U).obj V.unop).hom) := by
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  exact
    { toFun := fun a => by
        letI : IsIso a.1 := isIso_isomSpace_coe B S hS 𝒳 U y V a
        exact .of (asIso a.1)
      invFun := fun a => by
        letI : IsIso a.asIso.hom := Iso.isIso_hom a.asIso
        exact ⟨a.asIso.hom,
          (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U) y y a.asIso.hom).2
            (by infer_instance)⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun a => Aut.ext (Iso.ext rfl) }

private abbrev isomSpaceSelfGroup (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    [𝒳.val.p.IsPreFibered]
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    Group ((isomSpace B S hS 𝒳 U y y).obj V) :=
  (isomSpaceSelfEquivAut B S hS 𝒳 U y V).group

@[instance_reducible] private noncomputable def isomSpaceSelfGroupInstance (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    Group ((isomSpace B S hS 𝒳 U y y).obj V) := by
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  exact isomSpaceSelfGroup B S hS 𝒳 U y V

attribute [local instance] isomSpaceSelfGroupInstance

private noncomputable def isomSpaceOne (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    (isomSpace B S hS 𝒳 U y y).obj V := by
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  exact ⟨𝟙 _,
    (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U) y y (𝟙 _)).2
      (by infer_instance)⟩

private lemma isomSpaceSelfGroup_mul (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (a b : (isomSpace B S hS 𝒳 U y y).obj V) :
    a * b = isomSpaceComp B S hS 𝒳 U y V a b := by
  apply Subtype.ext
  rfl

private lemma isomSpaceComp_eq_mul (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (a b : (isomSpace B S hS 𝒳 U y y).obj V) :
    isomSpaceComp B S hS 𝒳 U y V a b = a * b :=
  (isomSpaceSelfGroup_mul B S hS 𝒳 U y V a b).symm

private lemma isomSpaceOne_eq_one (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    isomSpaceOne B S hS 𝒳 U y V = 1 := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  let : Group ((isomSpace B S hS 𝒳 U y y).obj V) :=
    isomSpaceSelfGroup B S hS 𝒳 U y V
  apply Subtype.ext
  rfl

private lemma isomSpace_map_comp (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    {V W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ}
    (f : V ⟶ W) (a b : (isomSpace B S hS 𝒳 U y y).obj V) :
    (isomSpace B S hS 𝒳 U y y).map f (isomSpaceComp B S hS 𝒳 U y V a b) =
      isomSpaceComp B S hS 𝒳 U y W
        ((isomSpace B S hS 𝒳 U y y).map f a)
        ((isomSpace B S hS 𝒳 U y y).map f b) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  apply Subtype.ext
  dsimp [isomSpace, isomSpaceComp]
  exact Functor.morRestrict_comp_hom (p := 𝒳.val.p) y y y
    ((Over.iteratedSliceBackward U).map f.unop) b.1 a.1

private lemma isomSpace_map_smul (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U)
    {V W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ}
    (f : V ⟶ W) (p : (isomSpace B S hS 𝒳 U x y).obj V)
    (g : (isomSpace B S hS 𝒳 U y y).obj V) :
    (isomSpace B S hS 𝒳 U x y).map f
      (isomSpaceSmul B S hS 𝒳 U x y V p g) =
      isomSpaceSmul B S hS 𝒳 U x y W
        ((isomSpace B S hS 𝒳 U x y).map f p)
        ((isomSpace B S hS 𝒳 U y y).map f g) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  apply Subtype.ext
  dsimp [isomSpace, isomSpaceSmul]
  exact Functor.morRestrict_comp_hom (p := 𝒳.val.p) x y y
    ((Over.iteratedSliceBackward U).map f.unop) p.1 g.1

private lemma isomSpace_map_one (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    {V W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ}
    (f : V ⟶ W) :
    (isomSpace B S hS 𝒳 U y y).map f (isomSpaceOne B S hS 𝒳 U y V) =
      isomSpaceOne B S hS 𝒳 U y W := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  apply Subtype.ext
  dsimp [isomSpace, isomSpaceOne]
  exact Functor.morRestrict_id_hom (p := 𝒳.val.p) y
    ((Over.iteratedSliceBackward U).map f.unop)

private lemma isomSpace_map_inv (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    {V W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ}
    (f : V ⟶ W) (a : (isomSpace B S hS 𝒳 U y y).obj V) :
    (isomSpace B S hS 𝒳 U y y).map f (a⁻¹) =
      ((isomSpace B S hS 𝒳 U y y).map f a)⁻¹ := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  apply (inv_eq_of_mul_eq_one_right ?_).symm
  calc
    (isomSpace B S hS 𝒳 U y y).map f a *
        (isomSpace B S hS 𝒳 U y y).map f (a⁻¹) =
      isomSpaceComp B S hS 𝒳 U y W
        ((isomSpace B S hS 𝒳 U y y).map f a)
        ((isomSpace B S hS 𝒳 U y y).map f (a⁻¹)) :=
      isomSpaceSelfGroup_mul B S hS 𝒳 U y W _ _
    _ = (isomSpace B S hS 𝒳 U y y).map f
        (isomSpaceComp B S hS 𝒳 U y V a (a⁻¹)) :=
      (isomSpace_map_comp B S hS 𝒳 U y f a (a⁻¹)).symm
    _ = (isomSpace B S hS 𝒳 U y y).map f
        (isomSpaceOne B S hS 𝒳 U y V) := by
      rw [isomSpaceComp_eq_mul, isomSpaceOne_eq_one, mul_inv_cancel]
    _ = 1 := by rw [isomSpace_map_one, isomSpaceOne_eq_one]

/-- `Isom_𝒳(x, y)` as an object over `AlgebraicGeometry.Stack.siteTerminalSpace`, which is where
the group-object and module-object structures of Stacks 043H and 043Q live. The structure
morphism is the unique one to a final object, so this carries no information beyond the presheaf
itself. -/
noncomputable def isomSpaceOver (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) : Over (siteTerminalSpace B S hS U) :=
  (Over.equivalenceOfIsTerminal (isTerminal_siteTerminalSpace B S hS U)).inverse.obj
    (isomSpace B S hS 𝒳 U x y)

/-- **`Isom_𝒳(x, y)` is an algebraic space.** For two objects `x` and `y` of the fibre category
of an algebraic stack `𝒳` over a scheme `U` of the big fppf site of `S`, the presheaf of
isomorphisms `x ⟶ y` on the big fppf site of `U` is an algebraic space over `U`.

Untagged: this is condition (2) of Stacks 045G for `𝒳`, obtained from representability of the
diagonal — the third clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` — through
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`. It is an
input to Stacks 04YP rather than part of its statement. -/
theorem isAlgebraicSpace_isomSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) :
    IsAlgebraicSpace B U.left.1 U.left.2
      (isomSpace B S hS 𝒳 U x y) := by
  rcases h𝒳 with ⟨hFib, _hStack, hDiag, _hAtlas⟩
  let 𝒳' := CatFiberedInGroupoids.mk 𝒳.val hFib
  have hRepDiag : HasRepresentableDiagonal B S hS 𝒳' := hDiag
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳').mp hRepDiag U x y
  let eF : F ⋙ uliftFunctor.{u, u} ≅ F :=
    Functor.isoWhiskerLeft F uliftFunctorTrivial ≪≫ Functor.rightUnitor F
  let eG : (isomSpace B S hS 𝒳 U x y) ⋙ uliftFunctor.{u, u} ≅
    isomSpace B S hS 𝒳 U x y :=
    Functor.isoWhiskerLeft (isomSpace B S hS 𝒳 U x y)
      uliftFunctorTrivial ≪≫ Functor.rightUnitor _
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (eF.symm ≪≫ e ≪≫ eG).symm hF

/-- **The group object structure on `Isom_𝒳(y, y)`.** The multiplication is reverse composition
of local automorphisms, the unit is the identity, and the inverse is the categorical inverse,
which exists because a section of `Isom_𝒳(y, y)` is by definition an isomorphism. -/
@[instance_reducible]
noncomputable def isomSpaceGrpObj (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    [𝒳.val.p.IsPreFibered]
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U) : GrpObj (isomSpace B S hS 𝒳 U y y) := by
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  refine
    { one := {
        app := fun V => TypeCat.ofHom (fun (_ :
          (MonoidalCategoryStruct.tensorUnit
            ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)).obj V) =>
            letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
            ⟨𝟙 _, by
              exact (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p)
                (U := U) y y (𝟙 _)).2 (by infer_instance)⟩
          )
        naturality := by
          intro V W f
          ext z
          apply Subtype.ext
          exact congrArg Subtype.val
            (isomSpace_map_one B S hS 𝒳 U y f).symm }
      mul := {
        app := fun V => TypeCat.ofHom (fun (z : (MonoidalCategoryStruct.tensorObj
            (isomSpace B S hS 𝒳 U y y) (isomSpace B S hS 𝒳 U y y)).obj V) =>
          isomSpaceComp B S hS 𝒳 U y V
            ((CartesianMonoidalCategory.fst (isomSpace B S hS 𝒳 U y y)
              (isomSpace B S hS 𝒳 U y y)).app V z)
            ((CartesianMonoidalCategory.snd (isomSpace B S hS 𝒳 U y y)
              (isomSpace B S hS 𝒳 U y y)).app V z))
        naturality := by
          intro V W f
          ext z
          apply Subtype.ext
          exact congrArg Subtype.val
            (isomSpace_map_comp B S hS 𝒳 U y f
              ((CartesianMonoidalCategory.fst (isomSpace B S hS 𝒳 U y y)
                (isomSpace B S hS 𝒳 U y y)).app V z)
              ((CartesianMonoidalCategory.snd (isomSpace B S hS 𝒳 U y y)
                (isomSpace B S hS 𝒳 U y y)).app V z)).symm }
      inv := {
        app := fun V => TypeCat.ofHom (fun (z : (isomSpace B S hS 𝒳 U y y).obj V) => by
          letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
          have hmem := z.2
          change z.1 ∈ (𝒳.val.p.isomSubpresheaf y y).obj _ at hmem
          letI : IsIso z.1 :=
            (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) (U := U)
              y y z.1).mp hmem
          exact ⟨inv z.1, by
            change IsIso (inv z.1)
            infer_instance⟩)
        naturality := by
          intro V W f
          ext z
          apply Subtype.ext
          exact congrArg Subtype.val
            (isomSpace_map_inv B S hS 𝒳 U y f z).symm }
      one_mul := by
        ext V z
        rcases z with ⟨⟨⟩, a⟩
        apply Subtype.ext
        change a.1 ≫ 𝟙 _ = a.1
        exact Category.comp_id _
      mul_one := by
        ext V z
        rcases z with ⟨a, ⟨⟩⟩
        apply Subtype.ext
        change 𝟙 _ ≫ a.1 = a.1
        exact Category.id_comp _
      mul_assoc := by
        ext V z
        rcases z with ⟨⟨a, b⟩, c⟩
        apply Subtype.ext
        change c.1 ≫ (b.1 ≫ a.1) = (c.1 ≫ b.1) ≫ a.1
        exact (Category.assoc _ _ _).symm
      left_inv := by
        ext V z
        let : IsIso z.1 := isIso_isomSpace_coe B S hS 𝒳 U y V z
        apply Subtype.ext
        change z.1 ≫ inv z.1 = 𝟙 _
        exact IsIso.hom_inv_id z.1
      right_inv := by
        ext V z
        let : IsIso z.1 := isIso_isomSpace_coe B S hS 𝒳 U y V z
        apply Subtype.ext
        change inv z.1 ≫ z.1 = 𝟙 _
        exact IsIso.inv_hom_id z.1 }

/-- **The action of `Isom_𝒳(y, y)` on `Isom_𝒳(x, y)` on the site of `T`.** A local automorphism
of `y` acts on a local isomorphism `x ⟶ y` by postcomposition. -/
@[instance_reducible]
noncomputable def isomSpaceModObj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    [𝒳.val.p.IsPreFibered]
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) :
    let F := isomSpace B S hS 𝒳 U y y
    let P := isomSpace B S hS 𝒳 U x y
    letI : GrpObj F := isomSpaceGrpObj B S hS 𝒳 U y
    ModObj F P := by
  let F := isomSpace B S hS 𝒳 U y y
  let P := isomSpace B S hS 𝒳 U x y
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  letI : GrpObj F := isomSpaceGrpObj B S hS 𝒳 U y
  refine {
    smul := {
      app := fun V => TypeCat.ofHom fun z =>
        isomSpaceSmul B S hS 𝒳 U x y V
          ((CartesianMonoidalCategory.snd F P).app V z)
          ((CartesianMonoidalCategory.fst F P).app V z)
      naturality := by
        intro V W f
        ext z
        apply Subtype.ext
        exact congrArg Subtype.val (isomSpace_map_smul B S hS 𝒳 U x y f
          ((CartesianMonoidalCategory.snd F P).app V z)
          ((CartesianMonoidalCategory.fst F P).app V z)).symm
    }
    one_smul := by
      ext V z
      rcases z with ⟨g, p⟩
      apply Subtype.ext
      change p.1 ≫ 𝟙 _ = p.1
      exact Category.comp_id _
    mul_smul := by
      ext V z
      rcases z with ⟨⟨g₁, g₂⟩, p⟩
      apply Subtype.ext
      change p.1 ≫ (g₂.1 ≫ g₁.1) = (p.1 ≫ g₂.1) ≫ g₁.1
      exact (Category.assoc _ _ _).symm
  }

/-- **The group object structure on `Isom_𝒳(y, y)` over
`AlgebraicGeometry.Stack.siteTerminalSpace`.** This is
`AlgebraicGeometry.Stack.isomSpaceGrpObj` transported along the equivalence between presheaves
on the site of `U` and presheaves over a final object, which is monoidal because both sides are
cartesian monoidal. -/
@[instance_reducible]
noncomputable def isomSpaceOverGrpObj (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U) :
    GrpObj (isomSpaceOver B S hS 𝒳 U y y) := by
  let E := Over.equivalenceOfIsTerminal (isTerminal_siteTerminalSpace B S hS U)
  let F := isomSpace B S hS 𝒳 U y y
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  letI : GrpObj F := isomSpaceGrpObj B S hS 𝒳 U y
  letI : E.inverse.Monoidal := Functor.Monoidal.ofChosenFiniteProducts E.inverse
  exact Functor.grpObjObj (F := E.inverse) (G := F)

private theorem isomSpaceOver_lift_map_section
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [(Over.equivalenceOfIsTerminal (isTerminal_siteTerminalSpace B S hS U)).inverse.Monoidal]
    (F G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (Q : Over (siteTerminalSpace B S hS U))
    (a : Q ⟶ (Over.equivalenceOfIsTerminal
      (isTerminal_siteTerminalSpace B S hS U)).inverse.obj F)
    (b : Q ⟶ (Over.equivalenceOfIsTerminal
      (isTerminal_siteTerminalSpace B S hS U)).inverse.obj G)
    {H : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u} (m : (F ⊗ G) ⟶ H)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (t : Q.left.obj V) :
    ((Over.equivalenceOfIsTerminal
        (isTerminal_siteTerminalSpace B S hS U)).inverse.map m).left.app V
      (((CartesianMonoidalCategory.lift a b).left ≫
        (Functor.LaxMonoidal.μ (Over.equivalenceOfIsTerminal
          (isTerminal_siteTerminalSpace B S hS U)).inverse F G).left).app V t) =
      m.app V ((a.left.app V) t, (b.left.app V) t) := by
  let E := Over.equivalenceOfIsTerminal (isTerminal_siteTerminalSpace B S hS U)
  have hpair :
      ((CartesianMonoidalCategory.lift a b).left ≫
        (Functor.LaxMonoidal.μ E.inverse F G).left).app V t =
        ((a.left.app V) t, (b.left.app V) t) := by
    apply Prod.ext
    · change ((CartesianMonoidalCategory.lift a b).left ≫
        (Functor.LaxMonoidal.μ E.inverse F G).left ≫
        (E.inverse.map (CartesianMonoidalCategory.fst F G)).left).app V t = _
      have hμ := congrArg Over.Hom.left (Functor.Monoidal.μ_fst E.inverse F G)
      have hμV := congrArg (fun f => f.app V) hμ
      have hμt := congrArg (fun f => f ((CartesianMonoidalCategory.lift a b).left.app V t)) hμV
      calc
        _ = ((CartesianMonoidalCategory.lift a b ≫
          CartesianMonoidalCategory.fst _ _).left.app V) t := hμt
        _ = _ := by simp
    · change ((CartesianMonoidalCategory.lift a b).left ≫
        (Functor.LaxMonoidal.μ E.inverse F G).left ≫
        (E.inverse.map (CartesianMonoidalCategory.snd F G)).left).app V t = _
      have hμ := congrArg Over.Hom.left (Functor.Monoidal.μ_snd E.inverse F G)
      have hμV := congrArg (fun f => f.app V) hμ
      have hμt := congrArg (fun f => f ((CartesianMonoidalCategory.lift a b).left.app V t)) hμV
      calc
        _ = ((CartesianMonoidalCategory.lift a b ≫
          CartesianMonoidalCategory.snd _ _).left.app V) t := hμt
        _ = _ := by simp
  rw [hpair]
  rfl

/-- **The group law of `Isom_𝒳(y, y)` is composition of local automorphisms.** On a pair of
sections of `Isom_𝒳(y, y)` over a test object `Q`, the multiplication of
`AlgebraicGeometry.Stack.isomSpaceOverGrpObj` is
`AlgebraicGeometry.Stack.isomSpaceComp`, i.e. reverse categorical composition. -/
@[stacks 04YP "part (1): the group law is composition of automorphisms"]
theorem isomSpaceOverGrpObj_mul (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (y : 𝒳.val.p.Fiber U)
    (Q : Over (siteTerminalSpace B S hS U))
    (a b : Q ⟶ isomSpaceOver B S hS 𝒳 U y y)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (t : Q.left.obj V) :
    (letI : GrpObj (isomSpaceOver B S hS 𝒳 U y y) :=
      isomSpaceOverGrpObj B S hS 𝒳 U y;
      ((CartesianMonoidalCategory.lift a b ≫
        MonObj.mul (X := isomSpaceOver B S hS 𝒳 U y y)).left.app V) t =
      isomSpaceComp B S hS 𝒳 U y V
        ((a.left.app V) t)
        ((b.left.app V) t)) := by
  let E := Over.equivalenceOfIsTerminal (isTerminal_siteTerminalSpace B S hS U)
  let F := isomSpace B S hS 𝒳 U y y
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  let : GrpObj F := isomSpaceGrpObj B S hS 𝒳 U y
  let : E.inverse.Monoidal := Functor.Monoidal.ofChosenFiniteProducts E.inverse
  exact isomSpaceOver_lift_map_section B S hS U F F Q a b (MonObj.mul (X := F)) V t

/-- **Stacks 04YP, part (2): the action.** `Isom_𝒳(y, y)` acts on `Isom_𝒳(x, y)` over
`AlgebraicGeometry.Stack.siteTerminalSpace`, by postcomposition. -/
@[stacks 04YP "part (2): the action by postcomposition", instance_reducible]
noncomputable def isomSpaceOverModObj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) :
    let G := isomSpaceOver B S hS 𝒳 U y y
    let P := isomSpaceOver B S hS 𝒳 U x y
    letI : GrpObj G := isomSpaceOverGrpObj B S hS 𝒳 U y
    ModObj G P := by
  let E := Over.equivalenceOfIsTerminal (isTerminal_siteTerminalSpace B S hS U)
  let F := isomSpace B S hS 𝒳 U y y
  let X := isomSpace B S hS 𝒳 U x y
  let G := isomSpaceOver B S hS 𝒳 U y y
  let P := isomSpaceOver B S hS 𝒳 U x y
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  letI : GrpObj F := isomSpaceGrpObj B S hS 𝒳 U y
  letI : ModObj F X := isomSpaceModObj B S hS 𝒳 U x y
  letI : E.inverse.Monoidal := Functor.Monoidal.ofChosenFiniteProducts E.inverse
  letI : GrpObj G := isomSpaceOverGrpObj B S hS 𝒳 U y
  let M' : MonObj (E.inverse.obj F) := Functor.monObjObj (F := E.inverse) F
  have hone : Functor.LaxMonoidal.ε E.inverse ≫ E.inverse.map η[F] = M'.one := rfl
  have hmul : Functor.LaxMonoidal.μ E.inverse F F ≫ E.inverse.map μ[F] = M'.mul := rfl
  letI : MonObj G := M'
  change ModObj (E.inverse.obj F) (E.inverse.obj X)
  exact modObjOfMonoidal E.inverse M' hone hmul

/-- **The action of `Isom_𝒳(y, y)` on `Isom_𝒳(x, y)` is postcomposition.** On a section of
`Isom_𝒳(y, y)` and a section of `Isom_𝒳(x, y)` over a test object `Q`, the action of
`AlgebraicGeometry.Stack.isomSpaceOverModObj` is
`AlgebraicGeometry.Stack.isomSpaceSmul`. -/
@[stacks 04YP "part (2): the action is postcomposition"]
theorem isomSpaceOverModObj_smul
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U)
    (Q : Over (siteTerminalSpace B S hS U))
    (g : Q ⟶ isomSpaceOver B S hS 𝒳 U y y)
    (p : Q ⟶ isomSpaceOver B S hS 𝒳 U x y)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) (t : Q.left.obj V) :
    (letI : GrpObj (isomSpaceOver B S hS 𝒳 U y y) :=
      isomSpaceOverGrpObj B S hS 𝒳 U y;
      letI : ModObj (isomSpaceOver B S hS 𝒳 U y y)
        (isomSpaceOver B S hS 𝒳 U x y) :=
        isomSpaceOverModObj B S hS 𝒳 U x y;
      ((CartesianMonoidalCategory.lift g p ≫
        ModObj.smul (M := isomSpaceOver B S hS 𝒳 U y y)
          (X := isomSpaceOver B S hS 𝒳 U x y)).left.app V) t) =
      isomSpaceSmul B S hS 𝒳 U x y V ((p.left.app V) t) ((g.left.app V) t) := by
  let E := Over.equivalenceOfIsTerminal (isTerminal_siteTerminalSpace B S hS U)
  let F := isomSpace B S hS 𝒳 U y y
  let X := isomSpace B S hS 𝒳 U x y
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒳.val.p.IsPreFibered := 𝒳.isFiberedInGroupoids.isFibered.toIsPreFibered
  let : GrpObj F := isomSpaceGrpObj B S hS 𝒳 U y
  let : ModObj F X := isomSpaceModObj B S hS 𝒳 U x y
  let : E.inverse.Monoidal := Functor.Monoidal.ofChosenFiniteProducts E.inverse
  exact isomSpaceOver_lift_map_section B S hS U F X Q g p (ModObj.smul (M := F) (X := X)) V t

private lemma isomSpaceSmul_existsUnique
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U)
    (V : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ)
    (p q : (isomSpace B S hS 𝒳 U x y).obj V) :
    ∃! g, isomSpaceSmul B S hS 𝒳 U x y V p g = q := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : IsIso p.1 := p.2
  let : IsIso q.1 := q.2
  refine ⟨⟨inv p.1 ≫ q.1, ?_⟩, ?_, ?_⟩
  · change IsIso (inv p.1 ≫ q.1)
    infer_instance
  · apply Subtype.ext
    change p.1 ≫ inv p.1 ≫ q.1 = q.1
    simp
  · intro g hg
    apply Subtype.ext
    have h := congrArg Subtype.val hg
    change p.1 ≫ g.1 = q.1 at h
    change g.1 = inv p.1 ≫ q.1
    rw [← h]
    simp

/-- **Stacks 04YP, part (2).** `Isom_𝒳(x, y)` is a pseudo-torsor under `Isom_𝒳(y, y)` over `U`:
the shear map `(g, p) ↦ (p ≫ g, p)` is an isomorphism, because for two local isomorphisms
`p, q : x ⟶ y` the unique local automorphism `g` of `y` with `p ≫ g = q` is `p⁻¹ ≫ q`. -/
@[stacks 04YP "part (2): isomorphism pseudo-torsor"]
theorem isomSpaceOver_isPseudoTorsor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U) :
    let G := isomSpaceOver B S hS 𝒳 U y y
    let P := isomSpaceOver B S hS 𝒳 U x y
    letI : GrpObj G := isomSpaceOverGrpObj B S hS 𝒳 U y
    letI : ModObj G P := isomSpaceOverModObj B S hS 𝒳 U x y
    IsPseudoTorsor G P := by
  let G := isomSpaceOver B S hS 𝒳 U y y
  let P := isomSpaceOver B S hS 𝒳 U x y
  let : GrpObj G := isomSpaceOverGrpObj B S hS 𝒳 U y
  let : ModObj G P := isomSpaceOverModObj B S hS 𝒳 U x y
  apply ModObj.isIso_leftSMul_iff.mpr
  intro Q p q
  have hex (V) (t : Q.left.obj V) :=
    isomSpaceSmul_existsUnique B S hS 𝒳 U x y V (p.left.app V t) (q.left.app V t)
  choose g hg huniq using hex
  let a : Q.left ⟶ G.left := {
    app := fun V => TypeCat.ofHom (g V)
    naturality := by
      intro V W f
      ext t
      change g W (Q.left.map f t) = (isomSpace B S hS 𝒳 U y y).map f (g V t)
      apply (huniq W (Q.left.map f t) _ ?_).symm
      have hnat (r : Q ⟶ P) : r.left.app W (Q.left.map f t) =
          (isomSpace B S hS 𝒳 U x y).map f (r.left.app V t) :=
        congrArg (fun k => k t) (r.left.naturality f)
      rw [hnat p, hnat q]
      exact (isomSpace_map_smul B S hS 𝒳 U x y f
        (p.left.app V t) (g V t)).symm.trans
          (congrArg (fun z => (isomSpace B S hS 𝒳 U x y).map f z) (hg V t))
  }
  let m : Q ⟶ G := Over.homMk a
    ((isTerminal_siteTerminalSpace B S hS U).hom_ext _ _)
  have heval (n : Q ⟶ G) (V) (t : Q.left.obj V) :
      (n • p).left.app V t =
        isomSpaceSmul B S hS 𝒳 U x y V (p.left.app V t) (n.left.app V t) :=
    isomSpaceOverModObj_smul B S hS 𝒳 U x y Q n p V t
  refine ⟨m, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    ext V t
    exact (heval m V t).trans (hg V t)
  · intro n hn
    apply Over.OverMorphism.ext
    ext V t
    apply huniq V t
    exact (heval n V t).symm.trans
      (congrArg (fun k : Q ⟶ P => k.left.app V t) hn)

/-- **Stacks 04YP, part (1).** For an object `y` of the fibre category of an algebraic stack `𝒳`
over a scheme `T` of the big fppf site of `S`, the automorphisms of `y` form a group algebraic
space over `T`: the presheaf `Isom_𝒳(y, y)` is an algebraic space
(`AlgebraicGeometry.Stack.isAlgebraicSpace_isomSpace`) and it carries the group object structure
`AlgebraicGeometry.Stack.isomSpaceOverGrpObj`, whose law is composition of local automorphisms by
`AlgebraicGeometry.Stack.isomSpaceOverGrpObj_mul`. -/
@[stacks 04YP "part (1): automorphism group algebraic space"]
def automorphismGroupSpace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber U) :
    Space.GroupAlgebraicSpace B U.left.1 U.left.2 (siteTerminalSpace B S hS U)
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2
        (⊤_ (BigFppfOver B U.left.1 U.left.2))) := by
  letI : GrpObj (isomSpaceOver B S hS 𝒳 U y y) := isomSpaceOverGrpObj B S hS 𝒳 U y
  refine ⟨Grp.mk (isomSpaceOver B S hS 𝒳 U y y), ?_⟩
  change IsAlgebraicSpace B U.left.1 U.left.2 (isomSpace B S hS 𝒳 U y y)
  exact isAlgebraicSpace_isomSpace B S hS 𝒳 h𝒳 U y y

/-- The underlying object over the base of
`AlgebraicGeometry.Stack.automorphismGroupSpace` is `Isom_𝒳(y, y)`, on the nose. -/
@[simp]
theorem automorphismGroupSpace_obj_X (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (U : BigFppfOver B S hS) (y : 𝒳.val.p.Fiber U) :
    (automorphismGroupSpace B S hS 𝒳 h𝒳 U y).obj.X = isomSpaceOver B S hS 𝒳 U y y :=
  rfl

end AlgebraicGeometry.Stack

end
