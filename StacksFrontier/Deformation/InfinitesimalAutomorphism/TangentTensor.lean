module

public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentVectorSpace
public import StacksFrontier.Deformation.PredeformationTangent.LinearLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The acting group of Tag 06JY: Tag 06IA for the automorphism functor

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), let `x` be an object
of `𝓕`, and fix the bookkeeping `P` of chosen pushforwards of `x` with which Tag 06JT's
automorphism functor is defined. For a finite-dimensional `k`-vector space `M` write `x[M]`
for the chosen pushforward of `x` to the square-zero extension `k ⊕ M` of the residue field,
and `Inf(x[M]/x_0)` for the automorphisms of `x[M]` that become trivial after reduction to the
special fibre. This file proves that

`Inf(x[M]/x_0) = T_{id_{x_0}} Aut(x) ⊗_k M`,

which is Tag 06IA applied to the automorphism functor, and the identification of the acting
group that Tag 06JY asserts. Composition of infinitesimal automorphisms on the left is
addition on the right.

The argument is the source's. The assignment `M ↦ Inf(x[M]/x_0)` is a functor on
finite-dimensional vector spaces; it takes the zero module to a one-element set, because
reduction from the square-zero extension by the zero module is an isomorphism; and it turns
products into products, because `k ⊕ (M × N)` is the fibre product of `k ⊕ M` and `k ⊕ N` over
`k` and condition (RS) carries that fibre square to a fibre square of automorphism groups. A
set-valued functor with those two properties has a canonical `k`-linear lift, and that lift is
tensoring with its value at a rank-one module, which is the tangent space of Tag 06JV (1).

## Main definitions

* `Deformation.infinitesimalAutomorphismModuleFunctor`: the functor
  `M ↦ Inf(x[M]/x_0)`.
* `Deformation.infinitesimalAutomorphismLinearLift`: its canonical `k`-linear lift.
* `Deformation.tangentCarrierLinearEquiv`: the value of the lift at the rank-one module is the
  tangent space at the identity of the automorphism functor.

## Main results

* `Deformation.isPullback_squareZeroProd`: the square-zero extension by a product is the fibre
  product of the two square-zero extensions over the residue field.
* `Deformation.existsUnique_prodAut`: the product condition, as the unique gluing of two
  infinitesimal automorphisms over the two coordinates.
* `Deformation.transportAut_prodSumMap_eq_mul`: the Eckmann-Hilton step, that the glued
  automorphism transported along the sum of the two coordinates is the composition.
* `Deformation.exists_tensorEquiv_infinitesimalAutomorphismKernel`: **Tag 06IA for the
  automorphism functor**, the identification `T_{id_{x_0}} Aut(x) ⊗_k M = Inf(x[M]/x_0)`
  carrying addition to composition.
* `Deformation.exists_mulEquiv_tensor_infinitesimalAutomorphismKernel`: the same
  identification read in the other direction.

## Implementation notes

The vector-space structure on `T_{id_{x_0}} Aut(x)` is *not* redefined here: it is the one
Tag 06JV (1) selects, namely `Deformation.naturalLocalizedTangentModule`, whose addition is
composition of infinitesimal automorphisms of the dual-number pushforward and whose scalar
action is transport along the scaling of the infinitesimal coordinate. What has to be proved,
and is proved in `Deformation.tangentCarrierLinearEquiv`, is that this structure agrees with
the one the linear lift produces: addition agrees by the Eckmann-Hilton step above, and the
scalar actions agree because a `k`-linear functor carries `c • 𝟙` to `c • 𝟙`. Without that
comparison the tensor product on the left would be formed with a different, unrelated vector
space structure, and the statement would not be the source's.

The square-zero extension by `M` is read as an object *under* the base of `x`, because that is
the shape `Deformation.ChosenPushforwardsAt` and Tag 06JT's automorphism functor take. At the
rank-one module `ULift k` it is the canonical dual-number object of
`StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent`, and its reduction is
`Deformation.tangentReduction`; this is recorded in
`Deformation.squareZeroUnderRed_rankOne`.

The square-zero extensions under the base of `x`, their coordinate maps and their reduction
are `Deformation.squareZeroUnder`, `Deformation.squareZeroUnderMap` and
`Deformation.squareZeroUnderRed` of
`StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentVectorSpace`, where the
construction is used at the rank-one and rank-two modules; the development here is its
reading at an arbitrary coordinate module, which is what the tensor description needs.
`Deformation.isPullback_squareZeroProd` is the fibre-square fact at a product of coordinate
modules, and is deduced from the same carrier-level criterion
`Deformation.isPullback_of_carrier`.

What this contributes to Tag 06JY, and what it does not. Tag 06JY asserts a free and
transitive action of `T_{id_{x_0}} Aut(x') ⊗_k I` on `Inf(x'/x)`, where `I` is the kernel of
the base surjection. Condition (RS) already supplies such an action with acting group
`Inf(x_I/x_0)`, where `x_I` is a pushforward of an (RS) fibre square of `x'` with itself over
`x` along the difference coordinate `(a_1, a_2) ↦ (ā_1, a_2 - a_1)`. The theorems here
identify `Inf(x[I]/x_0) = T_{id_{x_0}} Aut(x') ⊗_k I` for the *chosen* pushforward `x[I]` of
`x'` to `k ⊕ I`, that is for the split extension; the trivial extension `k ⊕ I` appearing
there is literally the same object of `𝒞_Λ`. What is still needed to make Tag 06JY
unconditional is that `x_I` is isomorphic to `x[I]` over `k ⊕ I`, which holds because the
diagonal of the fibre square splits the difference coordinate: `(a, a) ↦ (ā, 0)`. That is a
statement about fibre squares, not about tangent spaces, and it is not proved here.

The universe hypotheses are the weakest the construction allows: the coordinate modules live
in the carrier universe `max v w` of the Artinian algebras, not in the universe `w` of the
residue field, which is what `Deformation.linearFunctorLiftOfProductConditions` and
`Deformation.rankOneTensorEquiv` were generalized for. The tangent space itself lives in a
universe strictly larger than the fibre-morphism universe `v₁`, so it cannot be fed to
`Deformation.rankOneTensorEquiv` as the rank-one value directly; the tensor equivalence is
therefore formed at the lift's own value, and only then transported along
`Deformation.tangentCarrierLinearEquiv`.

## References

* [Stacks Project, Tag 06I9](https://stacks.math.columbia.edu/tag/06I9)
* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
* [Stacks Project, Tag 06JT](https://stacks.math.columbia.edu/tag/06JT)
* [Stacks Project, Tag 06JU](https://stacks.math.columbia.edu/tag/06JU)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
-/

@[expose] public section

namespace Deformation

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w u₁ v₁ z

/-! ### Square-zero extensions as objects under the base -/

section Under

attribute [local instance] mopI csI

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The two coordinate projections exhibit the square-zero extension by a product as the
fibre product of the two square-zero extensions over the residue field. -/
public theorem isPullback_squareZeroProd (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M N : FGModuleCat.{max v w} k) :
    IsPullback
      ((squareZeroAlgFunctor.{u, v, w} A).map
        (FGModuleCat.ofHom (LinearMap.fst k M N))).right
      ((squareZeroAlgFunctor.{u, v, w} A).map
        (FGModuleCat.ofHom (LinearMap.snd k M N))).right
      (squareZeroAlgRed.{u, v, w} A M).right
      (squareZeroAlgRed.{u, v, w} A N).right := by
  refine isPullback_of_carrier _ _ _ _ ?_ (Or.inl ?_) ?_ ?_
  · exact (congrArg Under.Hom.right
      (squareZeroAlgFunctor_map_red.{u, v, w} A (FGModuleCat.ofHom (LinearMap.fst k M N)))).trans
      (congrArg Under.Hom.right
        (squareZeroAlgFunctor_map_red.{u, v, w} A
          (FGModuleCat.ofHom (LinearMap.snd k M N)))).symm
  · exact fun c => ⟨TrivSqZeroExt.inl c.down, rfl⟩
  · intro z z' h1 h2
    refine TrivSqZeroExt.ext ?_ (Prod.ext ?_ ?_)
    · exact ((squareZeroAlgFunctor_map_fst.{u, v, w} A
        (FGModuleCat.ofHom (LinearMap.fst k M N)) z).symm.trans
        (congrArg TrivSqZeroExt.fst h1)).trans
        (squareZeroAlgFunctor_map_fst.{u, v, w} A
          (FGModuleCat.ofHom (LinearMap.fst k M N)) z')
    · exact ((squareZeroAlgFunctor_map_snd.{u, v, w} A
        (FGModuleCat.ofHom (LinearMap.fst k M N)) z).symm.trans
        (congrArg TrivSqZeroExt.snd h1)).trans
        (squareZeroAlgFunctor_map_snd.{u, v, w} A
          (FGModuleCat.ofHom (LinearMap.fst k M N)) z')
    · exact ((squareZeroAlgFunctor_map_snd.{u, v, w} A
        (FGModuleCat.ofHom (LinearMap.snd k M N)) z).symm.trans
        (congrArg TrivSqZeroExt.snd h2)).trans
        (squareZeroAlgFunctor_map_snd.{u, v, w} A
          (FGModuleCat.ofHom (LinearMap.snd k M N)) z')
  · intro a b hab
    have hfst : TrivSqZeroExt.fst a = TrivSqZeroExt.fst b :=
      congrArg ULift.down (hab : ULift.up (TrivSqZeroExt.fst a) = ULift.up (TrivSqZeroExt.fst b))
    obtain ⟨z, hz1, hz2⟩ :
        ∃ z : ↥((squareZeroAlgFunctor.{u, v, w} A).obj (FGModuleCat.of k (↥M × ↥N))).right,
        TrivSqZeroExt.fst z = TrivSqZeroExt.fst a ∧
          TrivSqZeroExt.snd z = (TrivSqZeroExt.snd a, TrivSqZeroExt.snd b) :=
      ⟨((TrivSqZeroExt.fst a, (TrivSqZeroExt.snd a, TrivSqZeroExt.snd b)) :
        TrivSqZeroExt k (↥M × ↥N)), rfl, rfl⟩
    refine ⟨z, TrivSqZeroExt.ext ?_ ?_, TrivSqZeroExt.ext ?_ ?_⟩
    · exact (squareZeroAlgFunctor_map_fst.{u, v, w} A
        (FGModuleCat.ofHom (LinearMap.fst k M N)) z).trans hz1
    · exact (squareZeroAlgFunctor_map_snd.{u, v, w} A
        (FGModuleCat.ofHom (LinearMap.fst k M N)) z).trans
        (congrArg (fun m => (ModuleCat.Hom.hom
          (FGModuleCat.ofHom (LinearMap.fst k M N)).hom) m) hz2)
    · exact ((squareZeroAlgFunctor_map_fst.{u, v, w} A
        (FGModuleCat.ofHom (LinearMap.snd k M N)) z).trans hz1).trans hfst
    · exact (squareZeroAlgFunctor_map_snd.{u, v, w} A
        (FGModuleCat.ofHom (LinearMap.snd k M N)) z).trans
        (congrArg (fun m => (ModuleCat.Hom.hom
          (FGModuleCat.ofHom (LinearMap.snd k M N)).hom) m) hz2)

end Under

/-! ### The functor of infinitesimal automorphisms over square-zero extensions -/

section Modules

attribute [local instance] mopI csI

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]

variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}
  (P : ChosenPushforwardsAt p x)

/-- Transporting along a coordinate map and then reducing is reducing. -/
private theorem transportAut_red_transportAut_map {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (a : Aut (P.obj (squareZeroUnder p x M))) :
    P.transportAut (squareZeroUnderRed p x N) (P.transportAut (squareZeroUnderMap p x f) a) =
      P.transportAut (squareZeroUnderRed p x M) a := by
  rw [← P.transportAut_comp, squareZeroUnderMap_red]

/-- Transport along a linear map of coordinate modules preserves the kernel of reduction. -/
public theorem transportAut_mem_ker {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (a : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M)) :
    P.transportAutHom (squareZeroUnderMap p x f) a.1 ∈
      MonoidHom.ker (P.transportAutHom (squareZeroUnderRed p x N)) :=
  MonoidHom.mem_ker.mpr
    ((transportAut_red_transportAut_map P f a.1).trans (MonoidHom.mem_ker.mp a.2))

/-- Transport of an infinitesimal automorphism along a coordinate map. -/
public noncomputable def transportInfinitesimalAutomorphism
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (a : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M)) :
    infinitesimalAutomorphismKernel P (squareZeroUnderRed p x N) :=
  ⟨P.transportAutHom (squareZeroUnderMap p x f) a.1, transportAut_mem_ker P f a⟩

/-- **The automorphism functor of `x` in coordinate form.** The infinitesimal automorphisms,
relative to the special fibre, of the pushforwards of `x` to the square-zero extensions of the
residue field, as a functor of the coordinate module. -/
public noncomputable def infinitesimalAutomorphismModuleFunctor :
    FGModuleCat.{max v w} k ⥤ Type v₁ where
  obj M := infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M)
  map f := ↾transportInfinitesimalAutomorphism P f
  map_id M := by
    apply ConcreteCategory.hom_ext
    intro a
    refine Subtype.ext ?_
    change P.transportAut (squareZeroUnderMap p x (𝟙 M)) a.1 = a.1
    rw [squareZeroUnderMap_id]
    exact P.transportAut_id _ _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    refine Subtype.ext ?_
    change P.transportAut (squareZeroUnderMap p x (f ≫ g)) a.1 =
      P.transportAut (squareZeroUnderMap p x g)
        (P.transportAut (squareZeroUnderMap p x f) a.1)
    rw [squareZeroUnderMap_comp, P.transportAut_comp]

/-- The transported automorphism underlying a value of the coordinate functor. -/
public theorem infinitesimalAutomorphismModuleFunctor_map_coe
    {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (a : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M)) :
    ((infinitesimalAutomorphismModuleFunctor P).map f a).1 =
      P.transportAutHom (squareZeroUnderMap p x f) a.1 := rfl

/-! ### The zero condition -/

/-- An automorphism over the square-zero extension by the zero module that reduces to the
identity is the identity. -/
private theorem eq_one_of_transportAut_red_zero
    (a : Aut (P.obj (squareZeroUnder p x (FGModuleCat.of k PUnit.{max v w + 1}))))
    (h1 : P.transportAut
      (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1})) a = 1) : a = 1 := by
  let _ := isIso_squareZeroUnderRed_zero (p := p) (x := x)
  have h := congrArg (P.transportAut
    (inv (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1})))) h1
  rw [← P.transportAut_comp, IsIso.hom_inv_id, P.transportAut_id] at h
  exact h.trans (map_one (P.transportAutHom
    (inv (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1})))))

/-- There is no infinitesimal automorphism over the square-zero extension by the zero module
other than the identity. -/
public theorem subsingleton_infinitesimalAutomorphismKernel_zero :
    Subsingleton (infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1}))) :=
  ⟨fun a b => Subtype.ext
    ((eq_one_of_transportAut_red_zero P a.1 (MonoidHom.mem_ker.mp a.2)).trans
      (eq_one_of_transportAut_red_zero P b.1 (MonoidHom.mem_ker.mp b.2)).symm)⟩

/-- The identity is an infinitesimal automorphism over the square-zero extension by the zero
module. -/
public theorem nonempty_infinitesimalAutomorphismKernel_zero :
    Nonempty (infinitesimalAutomorphismKernel P
      (squareZeroUnderRed p x (FGModuleCat.of k PUnit.{max v w + 1}))) :=
  ⟨1⟩

end Modules

/-! ### The product condition -/

section Prod

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}
  (P : ChosenPushforwardsAt p x) (M N : FGModuleCat.{max v w} k)

attribute [local instance] mopI csI

/-- The two coordinate projections exhibit the product extension as a fibre square, read
under the base of `x`. -/
private theorem isPullback_prodUnder :
    IsPullback (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))).right
      (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))).right
      (squareZeroUnderRed p x M).right (squareZeroUnderRed p x N).right :=
  isPullback_squareZeroProd.{u, v, w} (p.obj x) M N

/-- The two coordinate projections of the product pushforward agree after reduction. -/
private theorem prodCone_condition :
    P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) ≫
        P.map (squareZeroUnderRed p x M) =
      P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) ≫
        P.map (squareZeroUnderRed p x N) := by
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg P.map
    ((squareZeroUnderMap_red (p := p) (x := x)
        (FGModuleCat.ofHom (LinearMap.fst k M N))).trans
      (squareZeroUnderMap_red (p := p) (x := x)
        (FGModuleCat.ofHom (LinearMap.snd k M N))).symm)

/-- The image under `p` of the square of pushforwards is a pullback square. -/
private theorem isPullback_prod_base :
    IsPullback
      (p.map (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N)))))
      (p.map (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N)))))
      (p.map (P.map (squareZeroUnderRed p x M)))
      (p.map (P.map (squareZeroUnderRed p x N))) := by
  refine (isPullback_prodUnder (p := p) (x := x) M N).of_iso
    (eqToIso (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).2.symm)
    (eqToIso (P.obj (squareZeroUnder p x M)).2.symm)
    (eqToIso (P.obj (squareZeroUnder p x N)).2.symm)
    (eqToIso (P.obj (specialFibreUnder (p := p) (x := x))).2.symm) ?_ ?_ ?_ ?_
  · rw [p_map_P_map P (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N)))]
    simp
  · rw [p_map_P_map P (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N)))]
    simp
  · rw [p_map_P_map P (squareZeroUnderRed p x M)]; simp
  · rw [p_map_P_map P (squareZeroUnderRed p x N)]; simp

/-- Under (RS), the square of chosen pushforwards over the two coordinates is a pullback
square. -/
private theorem isLimit_prodCone (hp : SatisfiesRS p) :
    Nonempty (IsLimit (PullbackCone.mk
      (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))))
      (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))))
      (prodCone_condition P M N))) := by
  refine isLimit_of_map_isLimit hp _ _ _ ?_ ⟨?_⟩
  · rw [p_map_P_map P (squareZeroUnderRed p x N)]
    exact surjective_hom_comp _ _ (surjective_hom_eqToHom _)
      (surjective_hom_comp _ _ (fun c => ⟨TrivSqZeroExt.inl c.down, rfl⟩)
        (surjective_hom_eqToHom _))
  · exact IsLimit.ofIsoLimit (isPullback_prod_base P M N).isLimit
      (PullbackCone.ext (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm)

/-- **The product condition for the automorphism functor.** Under (RS), there is a unique
automorphism of the pushforward to the square-zero extension by a product whose two
coordinate transports are prescribed, provided each is trivial after reduction. -/
@[sga "7 VI 2.6(c)" "more general"]
public theorem existsUnique_prodAut (hp : SatisfiesRS p)
    (α : Aut (P.obj (squareZeroUnder p x M))) (β : Aut (P.obj (squareZeroUnder p x N)))
    (hα : α.asIso.hom.val ≫ P.map (squareZeroUnderRed p x M) = P.map (squareZeroUnderRed p x M))
    (hβ : β.asIso.hom.val ≫ P.map (squareZeroUnderRed p x N) = P.map (squareZeroUnderRed p x N)) :
    ∃! γ : Aut (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))),
      P.transportAut (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) γ = α ∧
        P.transportAut (squareZeroUnderMap p x
          (FGModuleCat.ofHom (LinearMap.snd k M N))) γ = β := by
  classical
  obtain ⟨hlim⟩ := isLimit_prodCone P M N hp
  have huniq : ∀ h h' : (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1 ⟶
        (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1,
      h ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) =
        h' ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) →
      h ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) =
        h' ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) →
      h = h' :=
    fun h h' e1 e2 => PullbackCone.IsLimit.hom_ext hlim e1 e2
  have hbase : ∀ g : (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1 ⟶
        (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1,
      p.map g ≫
          p.map (P.map (squareZeroUnderMap p x
            (FGModuleCat.ofHom (LinearMap.fst k M N)))) =
        p.map (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N)))) →
      p.map g ≫
          p.map (P.map (squareZeroUnderMap p x
            (FGModuleCat.ofHom (LinearMap.snd k M N)))) =
        p.map (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N)))) →
      p.IsHomLift (𝟙 (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N))).right) g := by
    intro g h1 h2
    have hid : p.map g =
        𝟙 (p.obj (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1) := by
      refine PullbackCone.IsLimit.hom_ext (isPullback_prod_base P M N).isLimit ?_ ?_
      · exact h1.trans (Category.id_comp _).symm
      · exact h2.trans (Category.id_comp _).symm
    refine IsHomLift.of_fac' p
      (𝟙 (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N))).right) g
      (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).2
      (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).2 ?_
    rw [hid]
    simp
  have build : ∀ (a : Aut (P.obj (squareZeroUnder p x M)))
      (b : Aut (P.obj (squareZeroUnder p x N))),
      a.asIso.hom.val ≫ P.map (squareZeroUnderRed p x M) = P.map (squareZeroUnderRed p x M) →
      b.asIso.hom.val ≫ P.map (squareZeroUnderRed p x N) = P.map (squareZeroUnderRed p x N) →
      ∃ g : (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1 ⟶
          (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1,
        p.IsHomLift (𝟙 (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N))).right) g ∧
        g ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) =
          P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) ≫
            a.asIso.hom.val ∧
        g ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) =
          P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) ≫
            b.asIso.hom.val := by
    intro a b ha hb
    have hcond :
        (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) ≫
            a.asIso.hom.val) ≫ P.map (squareZeroUnderRed p x M) =
          (P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) ≫
            b.asIso.hom.val) ≫ P.map (squareZeroUnderRed p x N) := by
      rw [Category.assoc, ha, Category.assoc, hb]
      exact prodCone_condition P M N
    obtain ⟨g, hl1, hl2⟩ :
        ∃ g : (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1 ⟶
          (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1,
        g ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) =
            P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) ≫
              a.asIso.hom.val ∧
          g ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) =
            P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) ≫
              b.asIso.hom.val :=
      ⟨PullbackCone.IsLimit.lift hlim _ _ hcond,
        PullbackCone.IsLimit.lift_fst hlim _ _ hcond,
        PullbackCone.IsLimit.lift_snd hlim _ _ hcond⟩
    refine ⟨g, hbase g ?_ ?_, hl1, hl2⟩
    · rw [← p.map_comp, hl1, p.map_comp, p_map_aut P a, Category.comp_id]
    · rw [← p.map_comp, hl2, p.map_comp, p_map_aut P b, Category.comp_id]
  have hinv : ∀ (L : FGModuleCat.{max v w} k) (a : Aut (P.obj (squareZeroUnder p x L))),
      a.asIso.hom.val ≫ P.map (squareZeroUnderRed p x L) = P.map (squareZeroUnderRed p x L) →
      a.asIso.inv.val ≫ P.map (squareZeroUnderRed p x L) = P.map (squareZeroUnderRed p x L) := by
    intro L a ha
    have hii : a.asIso.inv.val ≫ a.asIso.hom.val = 𝟙 (P.obj (squareZeroUnder p x L)).1 :=
      congrArg Subtype.val a.asIso.inv_hom_id
    calc a.asIso.inv.val ≫ P.map (squareZeroUnderRed p x L)
        = a.asIso.inv.val ≫ a.asIso.hom.val ≫ P.map (squareZeroUnderRed p x L) := by rw [ha]
      _ = P.map (squareZeroUnderRed p x L) := by rw [← Category.assoc, hii, Category.id_comp]
  obtain ⟨g, hgl, hg1, hg2⟩ := build α β hα hβ
  obtain ⟨g', hgl', hg1', hg2'⟩ := build α⁻¹ β⁻¹ (hinv M α hα) (hinv N β hβ)
  have hcomp : ∀ (a : Aut (P.obj (squareZeroUnder p x M)))
      (b : Aut (P.obj (squareZeroUnder p x N)))
      (g g' : (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1 ⟶
        (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1),
      g ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) =
        P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) ≫ a.asIso.hom.val →
      g ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) =
        P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) ≫ b.asIso.hom.val →
      g' ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) =
        P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.fst k M N))) ≫ a.asIso.inv.val →
      g' ≫ P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) =
        P.map (squareZeroUnderMap p x (FGModuleCat.ofHom (LinearMap.snd k M N))) ≫ b.asIso.inv.val →
      g ≫ g' = 𝟙 (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥N)))).1 := by
    intro a b g g' h1 h2 h1' h2'
    have ea : a.asIso.hom.val ≫ a.asIso.inv.val = 𝟙 (P.obj (squareZeroUnder p x M)).1 :=
      congrArg Subtype.val a.asIso.hom_inv_id
    have eb : b.asIso.hom.val ≫ b.asIso.inv.val = 𝟙 (P.obj (squareZeroUnder p x N)).1 :=
      congrArg Subtype.val b.asIso.hom_inv_id
    refine huniq _ _ ?_ ?_
    · rw [Category.assoc, h1', ← Category.assoc, h1, Category.assoc, ea, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, h2', ← Category.assoc, h2, Category.assoc, eb, Category.comp_id,
        Category.id_comp]
  have hgg := hcomp α β g g' hg1 hg2 hg1' hg2'
  have hgg' := hcomp α⁻¹ β⁻¹ g' g hg1' hg2' hg1 hg2
  refine ⟨.of ⟨⟨g, hgl⟩, ⟨g', hgl'⟩, Functor.Fiber.hom_ext hgg, Functor.Fiber.hom_ext hgg'⟩,
    ⟨(transportAut_eq_iff P _ _ α).mpr hg1, (transportAut_eq_iff P _ _ β).mpr hg2⟩, ?_⟩
  intro γ' hγ'
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  show γ'.asIso.hom.val = g
  refine huniq _ _ ?_ ?_
  · exact ((transportAut_eq_iff P _ γ' α).mp hγ'.1).trans hg1.symm
  · exact ((transportAut_eq_iff P _ γ' β).mp hγ'.2).trans hg2.symm

/-- **The product condition.** Under (RS), the coordinate functor of infinitesimal
automorphisms turns the two product projections into a bijection onto the product. -/
public theorem bijective_infinitesimalAutomorphismModuleFunctor_prod (hp : SatisfiesRS p) :
    Function.Bijective
      (fun z : (infinitesimalAutomorphismModuleFunctor P).obj
          (FGModuleCat.of k (↥M × ↥N)) ↦
        ((infinitesimalAutomorphismModuleFunctor P).map
            (FGModuleCat.ofHom (LinearMap.fst k M N)) z,
          (infinitesimalAutomorphismModuleFunctor P).map
            (FGModuleCat.ofHom (LinearMap.snd k M N)) z)) := by
  classical
  constructor
  · intro z z' hzz
    refine Subtype.ext ?_
    have h1 : P.transportAut (squareZeroUnderMap p x
        (FGModuleCat.ofHom (LinearMap.fst k M N))) z.1 =
        P.transportAut (squareZeroUnderMap p x
          (FGModuleCat.ofHom (LinearMap.fst k M N))) z'.1 :=
      congrArg Subtype.val (congrArg Prod.fst hzz)
    have h2 : P.transportAut (squareZeroUnderMap p x
        (FGModuleCat.ofHom (LinearMap.snd k M N))) z.1 =
        P.transportAut (squareZeroUnderMap p x
          (FGModuleCat.ofHom (LinearMap.snd k M N))) z'.1 :=
      congrArg Subtype.val (congrArg Prod.snd hzz)
    obtain ⟨γ, -, huniq⟩ := existsUnique_prodAut P M N hp
      (P.transportAut (squareZeroUnderMap p x
        (FGModuleCat.ofHom (LinearMap.fst k M N))) z.1)
      (P.transportAut (squareZeroUnderMap p x
        (FGModuleCat.ofHom (LinearMap.snd k M N))) z.1)
      ((mem_ker_transportAutHom_iff P _ _).mp (transportAut_mem_ker P
        (FGModuleCat.ofHom (LinearMap.fst k M N)) z))
      ((mem_ker_transportAutHom_iff P _ _).mp (transportAut_mem_ker P
        (FGModuleCat.ofHom (LinearMap.snd k M N)) z))
    exact (huniq z.1 ⟨rfl, rfl⟩).trans (huniq z'.1 ⟨h1.symm, h2.symm⟩).symm
  · rintro ⟨a, b⟩
    obtain ⟨γ, ⟨hγ1, hγ2⟩, -⟩ := existsUnique_prodAut P M N hp a.1 b.1
      ((mem_ker_transportAutHom_iff P _ _).mp a.2)
      ((mem_ker_transportAutHom_iff P _ _).mp b.2)
    have hmem : γ ∈ MonoidHom.ker
        (P.transportAutHom (squareZeroUnderRed p x (FGModuleCat.of k (↥M × ↥N)))) := by
      refine MonoidHom.mem_ker.mpr ?_
      show P.transportAut (squareZeroUnderRed p x (FGModuleCat.of k (↥M × ↥N))) γ = 1
      rw [← transportAut_red_transportAut_map P (FGModuleCat.ofHom (LinearMap.fst k M N)) γ,
        hγ1]
      exact MonoidHom.mem_ker.mp a.2
    exact ⟨⟨γ, hmem⟩, Prod.ext (Subtype.ext hγ1) (Subtype.ext hγ2)⟩

end Prod

/-! ### The coordinate maps of a self-product -/

section Coord

variable {k : Type w} [Field k] (M : FGModuleCat.{z} k)

/-- The sum of the two coordinates of a self-product of coordinate modules. -/
public noncomputable def prodSumMap : FGModuleCat.of k (↥M × ↥M) ⟶ M :=
  FGModuleCat.ofHom (LinearMap.fst k M M + LinearMap.snd k M M)

/-- The sum of the two coordinates is the categorical sum of the two projections. -/
public theorem prodSumMap_eq :
    prodSumMap M =
      FGModuleCat.ofHom (LinearMap.fst k M M) + FGModuleCat.ofHom (LinearMap.snd k M M) :=
  rfl

/-- The first inclusion into a self-product of coordinate modules. -/
public noncomputable def prodInlMap : M ⟶ FGModuleCat.of k (↥M × ↥M) :=
  FGModuleCat.ofHom (LinearMap.inl k M M)

/-- The second inclusion into a self-product of coordinate modules. -/
public noncomputable def prodInrMap : M ⟶ FGModuleCat.of k (↥M × ↥M) :=
  FGModuleCat.ofHom (LinearMap.inr k M M)

/-- The first inclusion followed by the first projection is the identity. -/
public theorem prodInlMap_fst :
    prodInlMap M ≫ FGModuleCat.ofHom (LinearMap.fst k M M) = 𝟙 M := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

/-- The first inclusion followed by the second projection is zero. -/
public theorem prodInlMap_snd :
    prodInlMap M ≫ FGModuleCat.ofHom (LinearMap.snd k M M) = 0 := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

/-- The first inclusion followed by the sum of the two coordinates is the identity. -/
public theorem prodInlMap_sum : prodInlMap M ≫ prodSumMap M = 𝟙 M := by
  apply FGModuleCat.hom_ext
  exact LinearMap.ext fun t => by change t + 0 = t; simp

/-- The second inclusion followed by the first projection is zero. -/
public theorem prodInrMap_fst :
    prodInrMap M ≫ FGModuleCat.ofHom (LinearMap.fst k M M) = 0 := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

/-- The second inclusion followed by the second projection is the identity. -/
public theorem prodInrMap_snd :
    prodInrMap M ≫ FGModuleCat.ofHom (LinearMap.snd k M M) = 𝟙 M := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

/-- The second inclusion followed by the sum of the two coordinates is the identity. -/
public theorem prodInrMap_sum : prodInrMap M ≫ prodSumMap M = 𝟙 M := by
  apply FGModuleCat.hom_ext
  exact LinearMap.ext fun t => by change 0 + t = t; simp

/-- Scaling of a coordinate module is the categorical scalar multiple of the identity. -/
public theorem scaleMap_eq (c : k) :
    FGModuleCat.ofHom (c • LinearMap.id : ↥M →ₗ[k] ↥M) = c • 𝟙 M := by
  apply FGModuleCat.hom_ext; exact LinearMap.ext fun _ => rfl

end Coord

/-! ### Composition is the addition of the automorphism functor -/

section EckmannHilton

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}
  (P : ChosenPushforwardsAt p x)

attribute [local instance] mopI csI

/-- An infinitesimal automorphism is killed by a zero map of coordinate modules. -/
public theorem transportAut_zeroMap {M N : FGModuleCat.{max v w} k}
    (a : Aut (P.obj (squareZeroUnder p x M)))
    (ha : P.transportAut (squareZeroUnderRed p x M) a = 1) :
    P.transportAut (squareZeroUnderMap p x (0 : M ⟶ N)) a = 1 := by
  have h2 : P.transportAut (squareZeroUnderMap p x
      (0 : M ⟶ FGModuleCat.of k PUnit.{max v w + 1})) a = 1 :=
    eq_one_of_transportAut_red_zero P _ ((transportAut_red_transportAut_map P _ a).trans ha)
  have hz : (0 : M ⟶ N) = (0 : M ⟶ FGModuleCat.of k PUnit.{max v w + 1}) ≫
      (0 : FGModuleCat.of k PUnit.{max v w + 1} ⟶ N) := zero_comp.symm
  rw [hz, squareZeroUnderMap_comp, P.transportAut_comp, h2]
  exact map_one (P.transportAutHom (squareZeroUnderMap p x
    (0 : FGModuleCat.of k PUnit.{max v w + 1} ⟶ N)))

/-- **Composition is the addition of the automorphism functor.** Under (RS), the transport of
the glued automorphism along the sum of the two coordinates is the composition of the two
prescribed infinitesimal automorphisms. This is the Eckmann-Hilton step of Tag 06JV (1),
in coordinate form. -/
public theorem transportAut_prodSumMap_eq_mul (hp : SatisfiesRS p)
    (M : FGModuleCat.{max v w} k) (a b : Aut (P.obj (squareZeroUnder p x M)))
    (ha : P.transportAut (squareZeroUnderRed p x M) a = 1)
    (hb : P.transportAut (squareZeroUnderRed p x M) b = 1)
    (γ : Aut (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥M)))))
    (hγ1 : P.transportAut (squareZeroUnderMap p x
      (FGModuleCat.ofHom (LinearMap.fst k M M))) γ = a)
    (hγ2 : P.transportAut (squareZeroUnderMap p x
      (FGModuleCat.ofHom (LinearMap.snd k M M))) γ = b) :
    P.transportAut (squareZeroUnderMap p x (prodSumMap M)) γ = a * b := by
  classical
  have key : ∀ s t : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      ∃! δ : Aut (P.obj (squareZeroUnder p x (FGModuleCat.of k (↥M × ↥M)))),
        P.transportAut (squareZeroUnderMap p x
            (FGModuleCat.ofHom (LinearMap.fst k M M))) δ = s.1 ∧
          P.transportAut (squareZeroUnderMap p x
            (FGModuleCat.ofHom (LinearMap.snd k M M))) δ = t.1 :=
    fun s t => existsUnique_prodAut P M M hp s.1 t.1
      ((mem_ker_transportAutHom_iff P _ _).mp s.2)
      ((mem_ker_transportAutHom_iff P _ _).mp t.2)
  choose Γ hΓ hΓu using key
  have hΓmul : ∀ s t s' t' : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      Γ (s * s') (t * t') = Γ s t * Γ s' t' := by
    intro s t s' t'
    refine (hΓu (s * s') (t * t') _ ⟨?_, ?_⟩).symm
    · rw [show P.transportAut (squareZeroUnderMap p x
          (FGModuleCat.ofHom (LinearMap.fst k M M))) (Γ s t * Γ s' t') =
            P.transportAut (squareZeroUnderMap p x
              (FGModuleCat.ofHom (LinearMap.fst k M M))) (Γ s t) *
            P.transportAut (squareZeroUnderMap p x
              (FGModuleCat.ofHom (LinearMap.fst k M M))) (Γ s' t') from
          map_mul (P.transportAutHom (squareZeroUnderMap p x
            (FGModuleCat.ofHom (LinearMap.fst k M M)))) _ _,
        (hΓ s t).1, (hΓ s' t').1]
      rfl
    · rw [show P.transportAut (squareZeroUnderMap p x
          (FGModuleCat.ofHom (LinearMap.snd k M M))) (Γ s t * Γ s' t') =
            P.transportAut (squareZeroUnderMap p x
              (FGModuleCat.ofHom (LinearMap.snd k M M))) (Γ s t) *
            P.transportAut (squareZeroUnderMap p x
              (FGModuleCat.ofHom (LinearMap.snd k M M))) (Γ s' t') from
          map_mul (P.transportAutHom (squareZeroUnderMap p x
            (FGModuleCat.ofHom (LinearMap.snd k M M)))) _ _,
        (hΓ s t).2, (hΓ s' t').2]
      rfl
  have hΓone_right : ∀ s : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      Γ s 1 = P.transportAut (squareZeroUnderMap p x (prodInlMap M)) s.1 := by
    intro s
    refine (hΓu s 1 _ ⟨?_, ?_⟩).symm
    · rw [← P.transportAut_comp, ← squareZeroUnderMap_comp, prodInlMap_fst,
        squareZeroUnderMap_id, P.transportAut_id]
    · rw [← P.transportAut_comp, ← squareZeroUnderMap_comp, prodInlMap_snd]
      exact transportAut_zeroMap P s.1 (MonoidHom.mem_ker.mp s.2)
  have hΓone_left : ∀ t : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      Γ 1 t = P.transportAut (squareZeroUnderMap p x (prodInrMap M)) t.1 := by
    intro t
    refine (hΓu 1 t _ ⟨?_, ?_⟩).symm
    · rw [← P.transportAut_comp, ← squareZeroUnderMap_comp, prodInrMap_fst]
      exact transportAut_zeroMap P t.1 (MonoidHom.mem_ker.mp t.2)
    · rw [← P.transportAut_comp, ← squareZeroUnderMap_comp, prodInrMap_snd,
        squareZeroUnderMap_id, P.transportAut_id]
  have hsum_one_right : ∀ s : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      P.transportAut (squareZeroUnderMap p x (prodSumMap M)) (Γ s 1) = s.1 := by
    intro s
    rw [hΓone_right s, ← P.transportAut_comp, ← squareZeroUnderMap_comp, prodInlMap_sum,
      squareZeroUnderMap_id, P.transportAut_id]
  have hsum_one_left : ∀ t : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      P.transportAut (squareZeroUnderMap p x (prodSumMap M)) (Γ 1 t) = t.1 := by
    intro t
    rw [hΓone_left t, ← P.transportAut_comp, ← squareZeroUnderMap_comp, prodInrMap_sum,
      squareZeroUnderMap_id, P.transportAut_id]
  have hsum_mul : ∀ s t : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      P.transportAut (squareZeroUnderMap p x (prodSumMap M)) (Γ s t) = s.1 * t.1 := by
    intro s t
    have h : Γ s t = Γ s 1 * Γ 1 t := by
      have h' := hΓmul s 1 1 t
      rwa [mul_one, one_mul] at h'
    rw [h, show P.transportAut (squareZeroUnderMap p x (prodSumMap M)) (Γ s 1 * Γ 1 t) =
        P.transportAut (squareZeroUnderMap p x (prodSumMap M)) (Γ s 1) *
          P.transportAut (squareZeroUnderMap p x (prodSumMap M)) (Γ 1 t) from
        map_mul (P.transportAutHom (squareZeroUnderMap p x (prodSumMap M))) _ _,
      hsum_one_right s, hsum_one_left t]
  have hγ : γ = Γ ⟨a, MonoidHom.mem_ker.mpr ha⟩ ⟨b, MonoidHom.mem_ker.mpr hb⟩ :=
    hΓu ⟨a, MonoidHom.mem_ker.mpr ha⟩ ⟨b, MonoidHom.mem_ker.mpr hb⟩ γ ⟨hγ1, hγ2⟩
  rw [hγ]
  exact hsum_mul ⟨a, MonoidHom.mem_ker.mpr ha⟩ ⟨b, MonoidHom.mem_ker.mpr hb⟩

end EckmannHilton

/-! ### The linear lift and its tensor description -/

section Tensor

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}
  (P : ChosenPushforwardsAt p x)

attribute [local instance] mopI csI

/-- Transport of the value of a set-valued functor along an equality of functors commutes
with the functor's action on morphisms. -/
public theorem cast_functor_map {C : Type u₁} [Category.{v₁} C] {G H : C ⥤ Type z}
    (hGH : G = H) {M N : C} (h : M ⟶ N) (y : G.obj M) :
    cast (congrArg (fun K : C ⥤ Type z => K.obj N) hGH) (G.map h y) =
      H.map h (cast (congrArg (fun K : C ⥤ Type z => K.obj M) hGH) y) := by
  subst hGH
  rfl

/-- **Stacks Project, Tag 06IA for the automorphism functor.** The canonical `k`-linear lift
of the coordinate functor of infinitesimal automorphisms. -/
public noncomputable def infinitesimalAutomorphismLinearLift (hp : SatisfiesRS p) :
    LinearFunctorLift k (infinitesimalAutomorphismModuleFunctor P) :=
  linearFunctorLiftOfProductConditions k (infinitesimalAutomorphismModuleFunctor P)
    (nonempty_infinitesimalAutomorphismKernel_zero P)
    (subsingleton_infinitesimalAutomorphismKernel_zero P)
    (fun M N => bijective_infinitesimalAutomorphismModuleFunctor_prod P M N hp)

/-- The value of the linear lift has the infinitesimal automorphisms as underlying set. -/
public theorem infinitesimalAutomorphismLinearLift_carrier (hp : SatisfiesRS p)
    (M : FGModuleCat.{max v w} k) :
    (((infinitesimalAutomorphismLinearLift P hp).functor.obj M : ModuleCat.{v₁} k) :
        Type v₁) =
      infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M) :=
  congrArg (fun G : FGModuleCat.{max v w} k ⥤ Type v₁ => G.obj M)
    (infinitesimalAutomorphismLinearLift P hp).forget_comp

/-- The transport to the infinitesimal automorphisms commutes with the action on
morphisms. -/
public theorem cast_lift_map (hp : SatisfiesRS p) {M N : FGModuleCat.{max v w} k} (f : M ⟶ N)
    (y : (((infinitesimalAutomorphismLinearLift P hp).functor.obj M : ModuleCat.{v₁} k) :
      Type v₁)) :
    cast (infinitesimalAutomorphismLinearLift_carrier P hp N)
        (((infinitesimalAutomorphismLinearLift P hp).functor.map f).hom y) =
      (infinitesimalAutomorphismModuleFunctor P).map f
        (cast (infinitesimalAutomorphismLinearLift_carrier P hp M) y) :=
  cast_functor_map (infinitesimalAutomorphismLinearLift P hp).forget_comp f y

/-- Addition in the linear lift is composition of infinitesimal automorphisms. -/
public theorem cast_lift_add (hp : SatisfiesRS p) (M : FGModuleCat.{max v w} k)
    (a b : (((infinitesimalAutomorphismLinearLift P hp).functor.obj M : ModuleCat.{v₁} k) :
      Type v₁)) :
    cast (infinitesimalAutomorphismLinearLift_carrier P hp M) (a + b) =
      cast (infinitesimalAutomorphismLinearLift_carrier P hp M) a *
        cast (infinitesimalAutomorphismLinearLift_carrier P hp M) b := by
  classical
  let Q := (infinitesimalAutomorphismLinearLift P hp).functor
  let L := infinitesimalAutomorphismModuleFunctor P
  let cM : (((Q.obj M : ModuleCat.{v₁} k) : Type v₁)) ≃ L.obj M :=
    Equiv.cast (infinitesimalAutomorphismLinearLift_carrier P hp M)
  let cP : (((Q.obj (FGModuleCat.of k (↥M × ↥M)) : ModuleCat.{v₁} k) : Type v₁)) ≃
      L.obj (FGModuleCat.of k (↥M × ↥M)) :=
    Equiv.cast (infinitesimalAutomorphismLinearLift_carrier P hp
      (FGModuleCat.of k (↥M × ↥M)))
  obtain ⟨γ, hγ⟩ := (bijective_infinitesimalAutomorphismModuleFunctor_prod P M M hp).2
    (cM a, cM b)
  have hγ1 : L.map (FGModuleCat.ofHom (LinearMap.fst k M M)) γ = cM a :=
    congrArg Prod.fst hγ
  have hγ2 : L.map (FGModuleCat.ofHom (LinearMap.snd k M M)) γ = cM b :=
    congrArg Prod.snd hγ
  have hmap : ∀ f : FGModuleCat.of k (↥M × ↥M) ⟶ M,
      cM ((Q.map f).hom (cP.symm γ)) = L.map f γ := by
    intro f
    show cast (infinitesimalAutomorphismLinearLift_carrier P hp M) _ = _
    rw [cast_lift_map P hp f (cP.symm γ)]
    show L.map f (cP (cP.symm γ)) = _
    rw [cP.apply_symm_apply]
  have hqa : (Q.map (FGModuleCat.ofHom (LinearMap.fst k M M))).hom (cP.symm γ) = a :=
    cM.injective ((hmap _).trans hγ1)
  have hqb : (Q.map (FGModuleCat.ofHom (LinearMap.snd k M M))).hom (cP.symm γ) = b :=
    cM.injective ((hmap _).trans hγ2)
  have hsum : (Q.map (prodSumMap M)).hom (cP.symm γ) = a + b := by
    have hadd : Q.map (prodSumMap M) =
        Q.map (FGModuleCat.ofHom (LinearMap.fst k M M)) +
          Q.map (FGModuleCat.ofHom (LinearMap.snd k M M)) := by
      rw [prodSumMap_eq, Q.map_add]
    rw [hadd, show ((Q.map (FGModuleCat.ofHom (LinearMap.fst k M M)) +
        Q.map (FGModuleCat.ofHom (LinearMap.snd k M M))).hom) (cP.symm γ) =
          (Q.map (FGModuleCat.ofHom (LinearMap.fst k M M))).hom (cP.symm γ) +
          (Q.map (FGModuleCat.ofHom (LinearMap.snd k M M))).hom (cP.symm γ) from rfl,
      hqa, hqb]
  have hstep : cM (a + b) = L.map (prodSumMap M) γ := by
    rw [← hsum]
    exact hmap _
  rw [show cast (infinitesimalAutomorphismLinearLift_carrier P hp M) (a + b) = cM (a + b)
    from rfl, hstep]
  refine Subtype.ext ?_
  show P.transportAut (squareZeroUnderMap p x (prodSumMap M)) γ.1 = _
  exact transportAut_prodSumMap_eq_mul P hp M (cM a).1 (cM b).1
    (MonoidHom.mem_ker.mp (cM a).2) (MonoidHom.mem_ker.mp (cM b).2) γ.1
    (congrArg Subtype.val hγ1) (congrArg Subtype.val hγ2)

/-- The scalar action in the linear lift is transport along the scaling of the coordinate. -/
public theorem cast_lift_smul (hp : SatisfiesRS p) (M : FGModuleCat.{max v w} k) (c : k)
    (a : (((infinitesimalAutomorphismLinearLift P hp).functor.obj M : ModuleCat.{v₁} k) :
      Type v₁)) :
    (cast (infinitesimalAutomorphismLinearLift_carrier P hp M) (c • a)).1 =
      P.transportAutHom (squareZeroUnderMap p x
          (FGModuleCat.ofHom (c • LinearMap.id : ↥M →ₗ[k] ↥M)))
        (cast (infinitesimalAutomorphismLinearLift_carrier P hp M) a).1 := by
  let Q := (infinitesimalAutomorphismLinearLift P hp).functor
  have hsm : (Q.map (c • 𝟙 M)).hom a = c • a := by
    rw [Q.map_smul, Q.map_id]
    rfl
  have hstep : cast (infinitesimalAutomorphismLinearLift_carrier P hp M) (c • a) =
      (infinitesimalAutomorphismModuleFunctor P).map
        (FGModuleCat.ofHom (c • LinearMap.id : ↥M →ₗ[k] ↥M))
        (cast (infinitesimalAutomorphismLinearLift_carrier P hp M) a) := by
    rw [← hsm, scaleMap_eq M c]
    exact cast_lift_map P hp (c • 𝟙 M) a
  rw [hstep]
  rfl


/-- The reduction of the canonical dual numbers is the reduction of the square-zero extension
by the rank-one module. -/
public theorem squareZeroUnderRed_rankOne :
    squareZeroUnderRed p x (FGModuleCat.of k (ULift.{v} k)) =
      tangentReduction (p := p) (x := x) := rfl

/-- The linear identification of the value of the lift at the rank-one module with the
tangent space at the identity of the automorphism functor of `x`. -/
public noncomputable def tangentCarrierLinearEquiv (hp : SatisfiesRS p) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    (((infinitesimalAutomorphismLinearLift P hp).functor.obj
        (FGModuleCat.of k (ULift.{v} k)) : ModuleCat.{v₁} k) : Type v₁) ≃ₗ[k]
      localizedAutomorphismFunctorTangent P := by
  letI := naturalLocalizedTangentAddCommGroup P hp
  letI := naturalLocalizedTangentModule P hp
  obtain ⟨hadd, hsmul⟩ := naturalLocalizedTangentModule_spec P hp
  let E := localizedTangentEquivKernel P
  let cc : (((infinitesimalAutomorphismLinearLift P hp).functor.obj
      (FGModuleCat.of k (ULift.{v} k)) : ModuleCat.{v₁} k) : Type v₁) ≃
      infinitesimalAutomorphismKernel P (tangentReduction (p := p) (x := x)) :=
    Equiv.cast (infinitesimalAutomorphismLinearLift_carrier P hp
      (FGModuleCat.of k (ULift.{v} k)))
  let e0 := cc.trans E.symm
  refine { toFun := e0, invFun := e0.symm, left_inv := e0.left_inv,
           right_inv := e0.right_inv, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    refine E.injective ?_
    rw [show E (e0 (a + b)) = E (E.symm (cc (a + b))) from rfl, E.apply_symm_apply,
      show E (e0 a + e0 b) = E (E.symm (cc a)) * E (E.symm (cc b)) from
        hadd (E.symm (cc a)) (E.symm (cc b)), E.apply_symm_apply, E.apply_symm_apply]
    exact cast_lift_add P hp (FGModuleCat.of k (ULift.{v} k)) a b
  · intro r a
    refine E.injective (Subtype.ext ?_)
    have h1 : E (e0 (r • a)) = cc (r • a) := E.apply_symm_apply _
    have h2 : E (e0 a) = cc a := E.apply_symm_apply _
    have h3 : (E (r • e0 a)).1 =
        P.transportAutHom (tangentScaling (p := p) (x := x) r) (cc a).1 := by
      rw [hsmul r (e0 a), h2]
    change ((E (e0 (r • a))).1) = (E (r • e0 a)).1
    rw [h1, h3]
    exact cast_lift_smul P hp (FGModuleCat.of k (ULift.{v} k)) r a

/-- **Stacks Project, Tag 06IA for the automorphism functor.** The infinitesimal
automorphisms, relative to the special fibre, of the pushforward of `x` to the square-zero
extension of the residue field by a finite-dimensional vector space `M` are the tangent space
at the identity of the automorphism functor of `x`, tensored over the residue field with `M`.
The identification carries addition of tangent vectors to composition of automorphisms. -/
public theorem exists_tensorEquiv_infinitesimalAutomorphismKernel (hp : SatisfiesRS p)
    (M : FGModuleCat.{max v w} k) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    ∃ e : TensorProduct k (localizedAutomorphismFunctorTangent P) M ≃
        infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M),
      ∀ s t, e (s + t) = e s * e t := by
  let _ : AddCommGroup (localizedAutomorphismFunctorTangent P) :=
    naturalLocalizedTangentAddCommGroup P hp
  let _ : Module k (localizedAutomorphismFunctorTangent P) :=
    naturalLocalizedTangentModule P hp
  let Q := (infinitesimalAutomorphismLinearLift P hp).functor
  let _ : Q.Additive := (infinitesimalAutomorphismLinearLift P hp).additive
  let _ : Q.Linear k := (infinitesimalAutomorphismLinearLift P hp).linear
  let T₀ : Type v₁ :=
    ((Q.obj (FGModuleCat.of k (ULift.{v} k)) : ModuleCat.{v₁} k) : Type v₁)
  let R : TensorProduct k T₀ ↥M ≃ₗ[k] ((Q.obj M : ModuleCat.{v₁} k) : Type v₁) :=
    rankOneTensorEquiv k (uliftRankOneCoord.{w, v} k) Q T₀ (LinearEquiv.refl k T₀) M
  let C : TensorProduct k (localizedAutomorphismFunctorTangent P) ↥M ≃ₗ[k]
      TensorProduct k T₀ ↥M :=
    TensorProduct.congr (tangentCarrierLinearEquiv P hp).symm (LinearEquiv.refl k ↥M)
  let RR := C.trans R
  refine ⟨RR.toEquiv.trans (Equiv.cast
    (infinitesimalAutomorphismLinearLift_carrier P hp M)), fun s t => ?_⟩
  show cast (infinitesimalAutomorphismLinearLift_carrier P hp M) (RR (s + t)) =
    cast (infinitesimalAutomorphismLinearLift_carrier P hp M) (RR s) *
      cast (infinitesimalAutomorphismLinearLift_carrier P hp M) (RR t)
  rw [RR.map_add]
  exact cast_lift_add P hp M (RR s) (RR t)


/-- **Stacks Project, Tag 06IA for the automorphism functor.** The identification of Tag 06IA
read in the other direction: composition of infinitesimal automorphisms over the square-zero
extension by `M` is addition in the tangent space tensored with `M`. -/
public theorem exists_mulEquiv_tensor_infinitesimalAutomorphismKernel (hp : SatisfiesRS p)
    (M : FGModuleCat.{max v w} k) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    ∃ e : infinitesimalAutomorphismKernel P (squareZeroUnderRed p x M) ≃
        TensorProduct k (localizedAutomorphismFunctorTangent P) M,
      ∀ a b, e (a * b) = e a + e b := by
  let _ : AddCommGroup (localizedAutomorphismFunctorTangent P) :=
    naturalLocalizedTangentAddCommGroup P hp
  let _ : Module k (localizedAutomorphismFunctorTangent P) :=
    naturalLocalizedTangentModule P hp
  obtain ⟨e, he⟩ := exists_tensorEquiv_infinitesimalAutomorphismKernel P hp M
  refine ⟨e.symm, fun a b => ?_⟩
  refine e.injective ?_
  rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply]

end Tensor

end Deformation

end
