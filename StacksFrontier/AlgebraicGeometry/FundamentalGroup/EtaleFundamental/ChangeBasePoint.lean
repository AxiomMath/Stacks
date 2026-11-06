module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap

/-!
# Change of geometric base point for the étale fundamental group

Let `X` be a connected scheme and let `x`, `x'` be two geometric points of `X`. An isomorphism
`t : F_x ≅ F_{x'}` of the two geometric fibre functors transports natural automorphisms by
conjugation, and so induces an isomorphism `π₁(X, x) ≃ π₁(X, x')` of étale fundamental groups.
That transport is a homeomorphism for the topologies of Stacks 0BMR, because on each fibre it is
the conjugate of an evaluation by a map between two discrete sets; so the two fundamental groups
of a connected scheme are isomorphic as topological groups, canonically up to the choice of `t`.

Changing `t` changes the induced isomorphism only by an inner automorphism, and *some* `t` always
exists — both of these are properties of the Galois category `FÉt_X` rather than of the
topology, and they are proved here from Stacks 0BN5 applied to the identity functor of `FÉt_X`,
viewed as an exact functor between the two Galois-category structures that `x` and `x'` give it.

## The Galois-category hypothesis

The transport itself — `AlgebraicGeometry.etaleFundamentalGroupMulEquiv` and its continuity — is
unconditional: it takes the fibre-functor isomorphism as an argument. The *existence* of such an
isomorphism, its *uniqueness up to inner conjugation*, and its compatibility with the actions
of Stacks 0BND need `FÉt_X` to be a Galois category at the relevant point, so those declarations
take `CategoryTheory.IsGaloisCategory (finiteEtaleFiberFunctor x)` as an instance
hypothesis. For a connected scheme it holds, by Stacks Tag 0BNB
(`Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor`); the hypothesis-free
statements of Tag 0BND (2) are
`AlgebraicGeometry.nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace`,
`AlgebraicGeometry.nonempty_etaleFundamentalGroupContinuousMulEquiv`,
`AlgebraicGeometry.isInnerConjugate_etaleFundamentalGroupContinuousMulEquiv` and
`AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquiv_action`.

## Main definitions

* `AlgebraicGeometry.etaleFundamentalGroupMulEquiv` — the isomorphism of étale fundamental
  groups induced by an isomorphism of geometric fibre functors, namely conjugation.
* `AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquiv` — the same, as an isomorphism of
  topological groups.
* `AlgebraicGeometry.finiteEtaleFiberFintypeFunctorIso` — the `FintypeCat`-valued form of a
  fibre-functor isomorphism, obtained as a preimage under a fully faithful whiskering.

## Main results

* `Stacks.FundamentalGroup.conjAut_app_apply` and
  `Stacks.FundamentalGroup.conjAut_app_apply_inv` — the component of a conjugated natural
  automorphism of a set-valued functor, in the two forms a computation needs.
* `AlgebraicGeometry.continuous_etaleFundamentalGroupMulEquiv` — transport along a
  fibre-functor isomorphism is continuous.
* `AlgebraicGeometry.nonempty_finiteEtaleFiberFunctorIso` — any two geometric fibre functors of
  a connected scheme are isomorphic, conditionally on Tag 0BNB.
* `AlgebraicGeometry.isInnerConjugate_etaleFundamentalGroupMulEquiv` — two choices of
  fibre-functor isomorphism induce inner-conjugate homomorphisms, conditionally on Tag 0BNB.
* `AlgebraicGeometry.etaleFundamentalGroupMulEquiv_action` — the comparison intertwines the two
  actions on the geometric fibres, conditionally on Tag 0BNB.

## Implementation notes

Continuity is proved through the universal property of the topology on `Aut F` recorded by
`Stacks.FundamentalGroup.continuous_of_continuous_component` and
`Stacks.FundamentalGroup.continuous_componentEmbedding_apply`, rather than by unfolding the
induced topology: the component of `t.conjAut σ` at `Y` is `t.hom.app Y` applied to the
component of `σ` at `Y` evaluated at `t.inv.app Y z`, and the outer map is a map between
discrete spaces. This is why `conjAut_app_apply_inv` is stated with the argument on the
*target* fibre.

The two conditional results go through the `FintypeCat`-valued fibre functor
`AlgebraicGeometry.finiteEtaleFiberFintypeFunctor`, since Stacks 0BN5 is stated for
finite-set-valued fibre functors. That functor composed with `FintypeCat.incl` is the geometric
fibre functor on the nose, so the Galois-category hypotheses transfer by
`inferInstanceAs`, and the automorphism groups are identified by
`AlgebraicGeometry.autMulEquivEtaleFundamentalGroup`.

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 0BN5](https://stacks.math.columbia.edu/tag/0BN5)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup

universe u v w

namespace Stacks.FundamentalGroup

variable {C : Type u} [Category.{v} C] {F G : C ⥤ Type w}

/-- The component at `Y` of a natural automorphism conjugated along `t : F ≅ G`, evaluated at a
point of `F.obj Y` carried across by `t`. -/
theorem conjAut_app_apply (t : F ≅ G) (σ : Aut F) (Y : C) (z : F.obj Y) :
    ((t.conjAut σ).asIso.app Y).hom (t.hom.app Y z) = t.hom.app Y ((σ.asIso.app Y).hom z) := by
  have h : (t.conjAut σ).asIso.hom.app Y = t.inv.app Y ≫ σ.asIso.hom.app Y ≫ t.hom.app Y := by
    rw [Iso.conjAut_hom]
    simp [Iso.conj_apply, NatTrans.comp_app]
  show ((t.conjAut σ).asIso.hom.app Y) (t.hom.app Y z) = _
  rw [h]
  simp only [comp_apply, Iso.hom_inv_id_app_apply]
  rfl

/-- The component at `Y` of a natural automorphism conjugated along `t : F ≅ G`, evaluated at an
arbitrary point of `G.obj Y`: pull the point back along `t.inv`, act, and push forward again. -/
theorem conjAut_app_apply_inv (t : F ≅ G) (σ : Aut F) (Y : C) (w : G.obj Y) :
    ((t.conjAut σ).asIso.app Y).hom w = t.hom.app Y ((σ.asIso.app Y).hom (t.inv.app Y w)) := by
  simpa using conjAut_app_apply t σ Y (t.inv.app Y w)

end Stacks.FundamentalGroup

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] {x x' : GeometricPoint X}

/-- The isomorphism of étale fundamental groups induced by an isomorphism of the geometric fibre
functors at two geometric points, namely conjugation of natural automorphisms. -/
def etaleFundamentalGroupMulEquiv
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    EtaleFundamentalGroup X x ≃* EtaleFundamentalGroup X x' :=
  t.conjAut

/-- Transport of étale fundamental groups along an isomorphism of geometric fibre functors is
continuous: on each fibre it is an evaluation followed by a map of discrete spaces. -/
theorem continuous_etaleFundamentalGroupMulEquiv
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    Continuous (etaleFundamentalGroupMulEquiv t) := by
  refine Stacks.FundamentalGroup.continuous_of_continuous_component
    (finiteEtaleFiberFunctor x) (finiteEtaleFiberFunctor x')
    (etaleFundamentalGroupMulEquiv t) fun Y z ↦ ?_
  let _tA : TopologicalSpace (Aut (finiteEtaleFiberFunctor x)) :=
    Stacks.FundamentalGroup.functorAutomorphismTopology (finiteEtaleFiberFunctor x)
  let _tX : TopologicalSpace ((finiteEtaleFiberFunctor x).obj Y) := ⊥
  let _dX : DiscreteTopology ((finiteEtaleFiberFunctor x).obj Y) := ⟨rfl⟩
  let _tX' : TopologicalSpace ((finiteEtaleFiberFunctor x').obj Y) := ⊥
  have hinner := Stacks.FundamentalGroup.continuous_componentEmbedding_apply
    (finiteEtaleFiberFunctor x) Y (t.inv.app Y z)
  have houter : @Continuous ((finiteEtaleFiberFunctor x).obj Y)
      ((finiteEtaleFiberFunctor x').obj Y) _tX _tX' (fun a ↦ t.hom.app Y a) :=
    continuous_of_discreteTopology
  have hkey : (fun σ ↦ ((etaleFundamentalGroupMulEquiv t σ).asIso.app Y).hom z)
      = (fun a ↦ t.hom.app Y a) ∘ (fun σ : Aut (finiteEtaleFiberFunctor x) ↦
        (σ.asIso.app Y).hom (t.inv.app Y z)) :=
    funext fun σ ↦ Stacks.FundamentalGroup.conjAut_app_apply_inv t σ Y z
  exact hkey ▸ houter.comp hinner

/-- The isomorphism of *topological* groups between the étale fundamental groups at two
geometric points determined by an isomorphism of their geometric fibre functors. -/
def etaleFundamentalGroupContinuousMulEquiv
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    EtaleFundamentalGroup X x ≃ₜ* EtaleFundamentalGroup X x' where
  toMulEquiv := etaleFundamentalGroupMulEquiv t
  continuous_toFun := continuous_etaleFundamentalGroupMulEquiv t
  continuous_invFun := continuous_etaleFundamentalGroupMulEquiv t.symm

section IsGaloisCategory

variable (X) (x x')

/-- Whiskering on the right with the inclusion of finite types into types is fully faithful,
because that inclusion is. -/
def fullyFaithfulWhiskeringRightFintypeIncl :
    ((Functor.whiskeringRight (FiniteEtaleOver X) FintypeCat.{u} (Type u)).obj
      FintypeCat.incl).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight (FiniteEtaleOver X)

variable [IsGaloisCategory (finiteEtaleFiberFunctor x)]
  [IsGaloisCategory (finiteEtaleFiberFunctor x')]

omit [ConnectedSpace X] in
/-- **Stacks 0BND, existence of the base-point comparison, conditionally on Tag 0BNB.** Any two
geometric fibre functors on the finite étale covers of a connected scheme are isomorphic. This is
Stacks 0BN5 for the identity functor of `FÉt_X`, which is exact, read against the two
Galois-category structures that the two points give it. -/
theorem nonempty_finiteEtaleFiberFunctorIso :
    Nonempty (finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') := by
  let _gx : IsGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor X x)) :=
    inferInstanceAs (IsGaloisCategory (finiteEtaleFiberFunctor x))
  let _gx' : IsGaloisCategory (setValuedFiberFunctor (finiteEtaleFiberFintypeFunctor X x')) :=
    inferInstanceAs (IsGaloisCategory (finiteEtaleFiberFunctor x'))
  have hId : exactFunctor (FiniteEtaleOver X) (FiniteEtaleOver X)
      (𝟭 (FiniteEtaleOver X)) := by
    rw [exactFunctor_iff]
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨t⟩ := CategoryTheory.nonempty_fiberIso_of_exact
    (finiteEtaleFiberFintypeFunctor X x') (finiteEtaleFiberFintypeFunctor X x)
    (𝟭 (FiniteEtaleOver X)) hId
  exact ⟨(Functor.leftUnitor (finiteEtaleFiberFintypeFunctor X x ⋙ FintypeCat.incl)).symm ≪≫
    (Functor.associator (𝟭 (FiniteEtaleOver X)) (finiteEtaleFiberFintypeFunctor X x)
      FintypeCat.incl).symm ≪≫
    ((Functor.whiskeringRight (FiniteEtaleOver X) FintypeCat.{u} (Type u)).obj
      FintypeCat.incl).mapIso t⟩

variable {X x x'}

/-- The `FintypeCat`-valued form of an isomorphism of geometric fibre functors, obtained as its
preimage under the fully faithful whiskering with `FintypeCat.incl`. -/
def finiteEtaleFiberFintypeFunctorIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    finiteEtaleFiberFintypeFunctor X x ≅ finiteEtaleFiberFintypeFunctor X x' :=
  (fullyFaithfulWhiskeringRightFintypeIncl X).preimageIso t

/-- The identification of `Aut` of the `FintypeCat`-valued fibre functor with the étale
fundamental group intertwines conjugation by a `FintypeCat`-valued fibre-functor isomorphism
with conjugation by its underlying set-valued one. -/
theorem autMulEquivEtaleFundamentalGroup_conjAut
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')
    (σ : Aut (finiteEtaleFiberFintypeFunctor X x)) :
    autMulEquivEtaleFundamentalGroup X x'
        ((finiteEtaleFiberFintypeFunctorIso t).conjAut σ) =
      t.conjAut (autMulEquivEtaleFundamentalGroup X x σ) := by
  let L := (Functor.whiskeringRight (FiniteEtaleOver X) FintypeCat.{u} (Type u)).obj
    FintypeCat.incl
  apply Aut.ext
  show L.mapIso ((finiteEtaleFiberFintypeFunctorIso t).conjAut σ).asIso
    = (t.conjAut (L.mapAut _ σ)).asIso
  rw [Functor.map_conjAut]
  let tL : L.obj (finiteEtaleFiberFintypeFunctor X x) ≅
      L.obj (finiteEtaleFiberFintypeFunctor X x') := t
  have ht : L.mapIso (finiteEtaleFiberFintypeFunctorIso t) = tL :=
    (fullyFaithfulWhiskeringRightFintypeIncl X).isoEquiv.right_inv tL
  rw [ht]
  rfl

/-- **Stacks 0BND, independence of the base-point comparison, conditionally on Tag 0BNB.** Two
choices of isomorphism of geometric fibre functors induce isomorphisms of étale fundamental
groups that differ by an inner automorphism of the target. This is Stacks 0BN5's
independence-up-to-inner-conjugacy statement, transported along
`AlgebraicGeometry.autMulEquivEtaleFundamentalGroup`. -/
theorem isInnerConjugate_etaleFundamentalGroupMulEquiv
    (t₁ t₂ : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    IsInnerConjugate (etaleFundamentalGroupMulEquiv t₁).toMonoidHom
      (etaleFundamentalGroupMulEquiv t₂).toMonoidHom := by
  let F := finiteEtaleFiberFintypeFunctor X x'
  let F' := finiteEtaleFiberFintypeFunctor X x
  let d (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :=
    galoisFunctorDataOfFiberIso F F' (𝟭 (FiniteEtaleOver X)) (finiteEtaleFiberFintypeFunctorIso t)
  have hcomp (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
      (etaleFundamentalGroupMulEquiv t).toMonoidHom =
        ((autMulEquivEtaleFundamentalGroup X x').toMonoidHom.comp (d t).hom.toMonoidHom).comp
          (autMulEquivEtaleFundamentalGroup X x).symm.toMonoidHom := by
    ext σ
    rw [(d t).hom_toMonoidHom]
    have h := autMulEquivEtaleFundamentalGroup_conjAut t
      ((autMulEquivEtaleFundamentalGroup X x).symm σ)
    rw [(autMulEquivEtaleFundamentalGroup X x).apply_symm_apply] at h
    exact h.symm
  obtain ⟨g, hg⟩ := galoisFunctorData_hom_innerConjugate (d t₁) (d t₂)
  refine ⟨autMulEquivEtaleFundamentalGroup X x' g, fun σ ↦ ?_⟩
  rw [hcomp t₁, hcomp t₂]
  simpa [map_mul, map_inv] using congrArg (autMulEquivEtaleFundamentalGroup X x')
    (hg ((autMulEquivEtaleFundamentalGroup X x).symm σ))

/-- **Stacks 0BND, compatibility of the base-point comparison with the actions, conditionally on
Tag 0BNB.** The change-of-base-point isomorphism intertwines the actions on the geometric fibres
underlying the two equivalences of
`AlgebraicGeometry.finiteEtaleEquivalenceOfIsGaloisCategory`. -/
theorem etaleFundamentalGroupMulEquiv_action
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')
    (Y : FiniteEtaleOver X) (σ : EtaleFundamentalGroup X x)
    (y : ((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.V.obj) :
    t.hom.app Y
        ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y
          (ConcreteCategory.hom
            (((finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.obj Y).obj.ρ σ).asHom y)) =
      (finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').hom.app Y
        (ConcreteCategory.hom
          (((finiteEtaleEquivalenceOfIsGaloisCategory X x').functor.obj Y).obj.ρ
            (etaleFundamentalGroupMulEquiv t σ)).asHom
          ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').inv.app Y
            (t.hom.app Y
              ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y y)))) := by
  rw [finiteEtaleEquivalenceOfIsGaloisCategory_action X x Y σ y,
    finiteEtaleEquivalenceOfIsGaloisCategory_action X x' Y (etaleFundamentalGroupMulEquiv t σ)
      ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x').inv.app Y
        (t.hom.app Y ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y y))),
    Iso.inv_hom_id_app_apply]
  exact (Stacks.FundamentalGroup.conjAut_app_apply t σ Y
    ((finiteEtaleEquivalenceOfIsGaloisCategoryFiberIso X x).hom.app Y y)).symm

end IsGaloisCategory

end AlgebraicGeometry

end
