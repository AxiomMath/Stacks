module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Galois.Equivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Functoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale covers as finite continuous fundamental-group sets

Let `X` be a connected scheme and `x` a geometric point of `X`. Grothendieck's main theorem for
the étale fundamental group says that the fibre functor
`F_x : FÉt_X ⥤ Type`, `Y ↦ finiteEtaleFiber x Y`, induces an equivalence between `FÉt_X` and the
category of finite sets with a continuous action of `π₁(X, x) = Aut F_x`, under which the
underlying finite set of the action attached to `Y` is the geometric fibre `F_x(Y)` and the action
is evaluation of natural automorphisms.

The whole of that statement is proved here from one hypothesis: that `F_x` satisfies the Galois
category axioms of Stacks Tag 0BMY, i.e.
`Stacks.FundamentalGroup.IsGaloisCategory (finiteEtaleFiberFunctor x)`. Given that hypothesis the
argument is formal. Lifting `F_x` through the finiteness of its values gives a functor
`finiteEtaleFiberFintypeFunctor` into `FintypeCat` whose composite with the inclusion is `F_x`
*on the nose*; `CategoryTheory.IsGaloisCategory.toGaloisCategory` and
`CategoryTheory.IsGaloisCategory.fiberFunctor` turn the hypothesis into Mathlib's
`CategoryTheory.GaloisCategory` together with `CategoryTheory.PreGaloisCategory.FiberFunctor`, so
Mathlib's `CategoryTheory.PreGaloisCategory.functorToContAction` is an equivalence onto the finite
continuous `Aut (finiteEtaleFiberFintypeFunctor x)`-sets. Since `FintypeCat.incl` is fully
faithful, the two automorphism groups agree as groups; they also agree as topological groups,
because both topologies are induced by evaluation on the fibres, and the inverse is continuous
because `Aut` of a fibre functor is compact and `π₁(X, x)` is Hausdorff. Restricting the action
along that isomorphism gives the equivalence, and the identification of underlying sets with the
geometric fibres is the identity.

## The Galois-category hypothesis

The declarations below take `IsGaloisCategory (finiteEtaleFiberFunctor x)` as an instance
hypothesis, since that is all the argument uses. For a connected scheme the hypothesis holds:
`Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor` is Stacks Tag 0BNB. The
hypothesis-free statement of Tag 0BND (1) is
`AlgebraicGeometry.exists_finiteEtaleEquivalence`.

## Main definitions

* `AlgebraicGeometry.finiteEtaleFiberFintypeFunctor` — the geometric fibre functor with values in
  `FintypeCat`, satisfying `finiteEtaleFiberFintypeFunctor X x ⋙ FintypeCat.incl =
  finiteEtaleFiberFunctor x` by `rfl`.
* `AlgebraicGeometry.autContinuousMulEquivEtaleFundamentalGroup` — the identification of
  `Aut (finiteEtaleFiberFintypeFunctor X x)` with `π₁(X, x)` as topological groups.
* `AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategory` — the equivalence between `FÉt_X`
  and the finite continuous `π₁(X, x)`-sets.
* `AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso` — its underlying sets are
  the geometric fibres.

## Main results

* `AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategory_action` — under that identification
  `σ : π₁(X, x)` acts on the fibre of `Y` as the component `σ_Y`.
* `AlgebraicGeometry.exists_finiteEtaleEquivalence_of_isGaloisCategory` — the existential form:
  some equivalence carries a fibre identification compatible with the action.

## Implementation notes

The equivalence and the fibre identification are given as *data*, not merely existentially, and
the action equation is proved for that data; the existential statement is then immediate. The
fibre identification is a natural isomorphism each of whose components is the identity, which is
what makes the action equation an instance of `MulEquiv.apply_symm_apply`.

The topology on `π₁(X, x)` is `Stacks.FundamentalGroup.functorAutomorphismTopology`, which is a
definition rather than an instance for a general functor, so the continuity proof rewrites the
goal into its induced form before applying `continuous_induced_rng`. On the other side Mathlib
topologises `Aut F` for `F : C ⥤ FintypeCat` by `CategoryTheory.PreGaloisCategory.autEmbedding`;
the two agree componentwise, and the component map factors through the discrete space
`Aut ((finiteEtaleFiberFintypeFunctor X x).obj Y)`, which is why no computation with the
pointwise-convergence topology is needed.

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
* [Stacks Project, Tag 0BN4](https://stacks.math.columbia.edu/tag/0BN4)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.FundamentalGroup
open scoped FintypeCatDiscrete CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [ConnectedSpace X] (x : GeometricPoint X)
  [hG : IsGaloisCategory (finiteEtaleFiberFunctor x)]

/-- The geometric fibre functor of a connected scheme, with values in `FintypeCat`. It is defined
whenever the Galois category axioms are available, since those record the finiteness of the
fibres. -/
def finiteEtaleFiberFintypeFunctor : FiniteEtaleOver X ⥤ FintypeCat.{u} :=
  ObjectProperty.lift _ (finiteEtaleFiberFunctor x) (fun Y ↦ hG.finite_obj Y)

omit [ConnectedSpace X] in
/-- Composing the `FintypeCat`-valued geometric fibre functor with the inclusion of finite types
into types returns the geometric fibre functor itself, not merely an isomorphic functor. -/
theorem finiteEtaleFiberFintypeFunctor_comp_incl :
    finiteEtaleFiberFintypeFunctor X x ⋙ FintypeCat.incl = finiteEtaleFiberFunctor x :=
  rfl

/-- Natural automorphisms of the `FintypeCat`-valued geometric fibre functor are the same as
natural automorphisms of the geometric fibre functor, because the inclusion of finite types into
types is fully faithful. This is the étale fundamental group as a group. -/
def autMulEquivEtaleFundamentalGroup :
    Aut (finiteEtaleFiberFintypeFunctor X x) ≃* EtaleFundamentalGroup X x :=
  ((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight
    (FiniteEtaleOver X)).autMulEquivOfFullyFaithful (finiteEtaleFiberFintypeFunctor X x)

/-- The identification of automorphism groups is continuous: the topology on the étale
fundamental group is induced by evaluation on the fibres, and each evaluation factors through the
discrete group of automorphisms of a single fibre. -/
theorem continuous_autMulEquivEtaleFundamentalGroup :
    Continuous (autMulEquivEtaleFundamentalGroup X x) := by
  let F := finiteEtaleFiberFunctor x
  let finF := finiteEtaleFiberFintypeFunctor X x
  let _tF (Y : FiniteEtaleOver X) : TopologicalSpace (F.obj Y) := ⊥
  let _dF (Y : FiniteEtaleOver X) : DiscreteTopology (F.obj Y) := ⟨rfl⟩
  let _tP (Y : FiniteEtaleOver X) : TopologicalSpace (Equiv.Perm (F.obj Y)) := autTopology
  show @Continuous _ (EtaleFundamentalGroup X x) _
    (TopologicalSpace.induced (componentEmbedding F) inferInstance) _
  refine continuous_induced_rng.mpr (continuous_pi fun Y ↦ ?_)
  have key : (fun σ : Aut finF ↦ componentEmbedding F (autMulEquivEtaleFundamentalGroup X x σ) Y)
      = (fun τ : Aut (finF.obj Y) ↦ (FintypeCat.incl.mapIso τ).toEquiv) ∘
        (fun σ ↦ PreGaloisCategory.autEmbedding finF σ Y) :=
    rfl
  exact key ▸ continuous_of_discreteTopology.comp ((continuous_apply Y).comp continuous_induced_dom)

/-- The automorphism group of the `FintypeCat`-valued geometric fibre functor is the étale
fundamental group as a *topological* group. The inverse is continuous because the source is
compact and the target is Hausdorff, both of which hold because the fibres are finite. -/
def autContinuousMulEquivEtaleFundamentalGroup :
    Aut (finiteEtaleFiberFintypeFunctor X x) ≃ₜ* EtaleFundamentalGroup X x :=
  haveI _hfin : ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) := fun Y ↦ hG.finite_obj Y
  { __ := autMulEquivEtaleFundamentalGroup X x
    continuous_toFun := continuous_autMulEquivEtaleFundamentalGroup X x
    continuous_invFun :=
      (continuous_autMulEquivEtaleFundamentalGroup X x).continuous_symm_of_equiv_compact_to_t2
        (f := (autMulEquivEtaleFundamentalGroup X x).toEquiv) }

/-- **Stacks 0BND, the equivalence.** Finite étale covers of a connected scheme `X` are
equivalent to finite sets with a continuous action of the étale fundamental group. The equivalence
is Mathlib's fundamental theorem of Galois categories, with the acting group transported along
`AlgebraicGeometry.autContinuousMulEquivEtaleFundamentalGroup`. Its instance argument, the Galois
category axioms of the geometric fibre functor, is always found: it is the instance
`Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor`, which proves Tag 0BNB. -/
@[sga "3 X 7.0.2" "special case", sga "5 VI 1.2.3.1"]
def finiteEtaleEquivalenceOfIsGaloisCategory :
    FiniteEtaleOver X ≌ ContAction FintypeCat.{u} (EtaleFundamentalGroup X x) :=
  letI : CategoryTheory.GaloisCategory (FiniteEtaleOver X) :=
    IsGaloisCategory.toGaloisCategory (finiteEtaleFiberFunctor x)
  letI : IsGaloisCategory (finiteEtaleFiberFintypeFunctor X x ⋙ FintypeCat.incl) := hG
  letI : PreGaloisCategory.FiberFunctor (finiteEtaleFiberFintypeFunctor X x) :=
    IsGaloisCategory.fiberFunctor (finiteEtaleFiberFintypeFunctor X x)
  (PreGaloisCategory.functorToContAction
      (finiteEtaleFiberFintypeFunctor X x)).asEquivalence.trans
    (ContAction.resEquiv FintypeCat.{u} (autContinuousMulEquivEtaleFundamentalGroup X x).symm)

/-- The underlying finite set of the continuous action attached to a finite étale cover is its
geometric fibre. Each component of this natural isomorphism is the identity. -/
def finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso :
    (finiteEtaleEquivalenceOfIsGaloisCategory X x).functor ⋙
        forget₂ (ContAction FintypeCat.{u} (EtaleFundamentalGroup X x))
          FintypeCat.{u} ⋙ FintypeCat.incl ≅ finiteEtaleFiberFunctor x :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro Y Z f
    ext y
    rfl)

/-- On the equivalence of
`AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategory`, an element of the étale fundamental
group acts on the geometric fibre of a finite étale cover by evaluating the corresponding natural
automorphism on that cover. -/
theorem finiteEtaleEquivalenceOfIsGaloisCategory_action (Y : FiniteEtaleOver X)
    (σ : EtaleFundamentalGroup X x)
    (y : ((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.V.obj) :
    ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y)
        (ConcreteCategory.hom
          (((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.ρ σ) y) =
      (σ.app Y).hom (((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y) y) :=
  ConcreteCategory.congr_hom
    (congrArg (fun τ : Aut (finiteEtaleFiberFunctor x) ↦ τ.hom.app Y)
      ((autMulEquivEtaleFundamentalGroup X x).apply_symm_apply σ)) y

/-- **Stacks 0BND, the existential form, for a fibre functor with the Galois category axioms.**
If the geometric fibre functor of a connected scheme satisfies the Galois category axioms (which it
does, by `Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor`), then there is an
equivalence between finite étale covers of `X` and finite continuous actions of the étale
fundamental group, together with an identification of the underlying finite sets with the
geometric fibres under which the action is evaluation of natural automorphisms. -/
@[sga "5 VI 1.2.3.1"]
theorem exists_finiteEtaleEquivalence_of_isGaloisCategory :
    ∃ E : FiniteEtaleOver X ≌ ContAction FintypeCat.{u} (EtaleFundamentalGroup X x),
      ∃ α : E.functor ⋙
          forget₂ (ContAction FintypeCat.{u} (EtaleFundamentalGroup X x))
            FintypeCat.{u} ⋙ FintypeCat.incl ≅ finiteEtaleFiberFunctor x,
        ∀ (Y : FiniteEtaleOver X) (σ : EtaleFundamentalGroup X x)
          (y : (E.functor.obj Y).obj.V.obj),
          (α.hom.app Y) (ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ) y) =
            (σ.app Y).hom ((α.hom.app Y) y) :=
  ⟨finiteEtaleEquivalenceOfIsGaloisCategory X x,
    finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x,
    finiteEtaleEquivalenceOfIsGaloisCategory_action X x⟩

end AlgebraicGeometry

end
