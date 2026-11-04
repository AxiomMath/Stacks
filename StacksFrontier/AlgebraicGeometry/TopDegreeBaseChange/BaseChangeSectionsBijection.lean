module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenCohomologyTopDegree
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineOpenTensorCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RestrictPullbackTopDegreeBridge
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TildePullbackCrossing
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing

/-!
# The map on sections that conclusion (c) of [Stacks, Tag 0EX3] needs, and its bijectivity

`BaseChangeSectionsGenerators.lean` reduces conclusion (c) of [Stacks, Tag 0EX3] over a
compatible pair of affine opens to three data: a `Γ(Y'', W)`-linear map `ψ` out of the base
change

> `Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V)`,

its bijectivity, and its agreement with `Γ(W, γ⁺)` on the pure tensors `1 ⊗ a`. This file
constructs `ψ`, computes it on the pure tensors, and reduces its bijectivity to one identity
about multiplication.

The construction is the source's. Conclusion (b) of the tag presents the endofunctor
`Φ : M ↦ H^d(f'⁻¹(V), F'| ⊗ (f' ∣_ V)^* M~)` of `Γ(V, ⊤)`-modules as tensoring with
`H^d(f'⁻¹(V), F'|)`, which over the affine open `V` is `Γ(R^d f'_* F', V)`; and the right-hand
end `Γ(R^d f''_* (h')^* F', W)` is the value of `Φ` at the functions on `W`
(`topDegreeFunctorObjIsoTargetSections`). The Eilenberg-Watts comparison then presents a map out
of the base change, and that map is bijective as soon as the identification of the right-hand end
carries the endomorphism `Φ(multiplication by a)` to multiplication by `a`. That one identity is
the hypothesis `hmul` of `bijective_baseChangeSectionsMap`; everything else below is proved, and
no hypothesis is placed on either base or on any morphism beyond what the situation provides.

## Main definitions

* `ModuleCat.ExtendScalars.congrBase`: **extension of scalars does not see which of two
  isomorphic base rings is used.** This crosses `Γ(Y', V)` and `Γ(V, ⊤)`.
* `ModuleCat.ExtendScalars.restrictScalarsSelfIso`: the ring of scalars transported along a ring
  isomorphism.
* `…TopDegreeBaseChange.mulLeftRestrictScalars`: multiplication by a ring element, read as an
  endomorphism of the ring viewed as a module over a base ring through a ring map.
* `…TopDegreeBaseChange.fromExtendScalarsComp`: the map out of a base change that the
  Eilenberg-Watts presentation produces.
* `…TopDegreeBaseChange.sectionsIsoPushforwardUnitSections`,
  `…TopDegreeBaseChange.pullbackTildeSectionsIso`: the functions on `W`, in the two spellings the
  geometric factor of conclusion (b) and the right-hand end of the computation use.
* `…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` and
  `…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections`: **the value of `Φ` at the
  functions on `W` is `Γ(R^d f''_* (h')^* F', W)`**, through the cohomology of `((h')^* F')|`
  over `f''⁻¹(W)`.
* `…TopDegreeBaseChange.topDegreeFunctorObjSelfIsoSourceSections`: **the Eilenberg-Watts module
  of `Φ` is `Γ(R^d f'_* F', V)`.**
* `…TopDegreeBaseChange.baseChangeSectionsMap`: **the map `ψ`**, a `Γ(Y'', W)`-linear map
  `Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`.

## Main results

* `…TopDegreeBaseChange.bijective_fromExtendScalars_of_mulLeft` and
  `…TopDegreeBaseChange.bijective_fromExtendScalarsComp`: **the module theory behind the
  construction.** For a right exact linear endofunctor `F` of `ModuleCat R` commuting with direct
  sums, a ring map `φ : R ⟶ A`, and a bijection `Ξ` out of `F(A)` carrying
  `F(multiplication by a)` to multiplication by `a`, the map `A ⊗_R F(R) ⟶ N` determined by
  `x ↦ Ξ (F(r ↦ r • 1)(x))` is bijective. This is Eilenberg-Watts read on the pure tensors.
* `…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul` together with
  `…TopDegreeBaseChange.baseChangeSectionsMap_eq`: **`ψ` on the pure tensors**, which is what the
  agreement with `Γ(W, γ⁺)` is matched against.
* `…TopDegreeBaseChange.appLE_eq_comp_topIso` and
  `…TopDegreeBaseChange.appTop_comp_eq_appTop_comp_algebraMap`: the two identities of ring maps
  the computation rests on — that `h.appLE V W` factors through the functions on `V`, and that
  the functions on `V` act on the cohomology over `f''⁻¹(W)` the same way along either side of
  the restricted square.
* `…TopDegreeBaseChange.bijective_baseChangeSectionsMap`: **`ψ` is bijective**, from the
  multiplication identity `hmul` alone.

## Implementation notes

*Why the multiplication identity is the one thing asked for.* The Eilenberg-Watts comparison of
`Stacks.EilenbergWatts.linearEquiv` sends `x ⊗ m` to `F(r ↦ r • m)(x)`, and `r ↦ r • a` is
`r ↦ r • 1` followed by multiplication by `a` (`toSpanSingleton_eq_mulLeftRestrictScalars`). So
the comparison is linear over the ring `A` for the action `a • y = F(multiplication by a)(y)` on
`F(A)`, which is `mulLeftRestrictScalars`; what `hmul` says is that this action is the one the
target carries. Geometrically that is the statement that the identification of
`Γ(R^d f''_* (h')^* F', W)` with `Φ(Γ(Y'', W))` is linear over the functions on `W` and not
merely over the functions on `V`, and it splits along the three factors of
`topDegreeFunctorObjIsoTargetSections`: multiplication on the module associated to the functions
on `W`, the projection formula, and the Leray comparison of [Stacks, Tag 089W], where `H^n` of
multiplication by a global function upstairs is multiplication by it.

*Why the ring `A` enters as `(ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)` and not
through an `Algebra` instance.* The `Module R A` instance carried by
`(ModuleCat.extendScalars φ).obj M` is `Module.compHom A φ`; for an abstract `Algebra R A` that
is only propositionally the `Algebra.toModule` instance, so the two tensor products `A ⊗_R M`
would be different types. Restricting scalars along `φ` produces `Module.compHom` on the nose, so
every tensor product below is formed with one and the same instance.

*One definitional reconciliation per `rfl` lemma, and no reconciliation at a component.* The
value of `Φ` is a composite of three functors and a restriction of scalars, and the tensor
product of module sheaves occurs in it under a different constant from the one the right-hand end
of the computation uses; `topDegreeFunctor_obj_eq` records that identification once, by `rfl`, so
that the chain `topDegreeFunctorObjIsoCohomologyUpstairs` is formed at a single spelling and
every factor of it is an isomorphism applied by `Functor.mapIso`. Reconciling the two spellings
inside that chain instead exhausts the elaborator's budget.

*The two readings of the scalars upstairs are crossed by `eqToIso` of a `congrArg`.* The
functions on `V` act on `H^d(f''⁻¹(W), -)` along `f'` and then `h'`, and along `h` and then
`f''`; the two ring maps are equal by `appTop_comp_eq_appTop_comp_algebraMap`, and the transport
is `congrArg` in the ring map, as in
`…TopDegreeBaseChange.affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology`.

*Why the bijectivity of `ψ` is read through `baseChangeSectionsMap_eq`.* The statement
`bijective_fromExtendScalarsComp_sections` is about the map `fromExtendScalarsComp` produces at
the geometric data, which is what `ψ` is defined to be; stating it at `ψ` and asking the
elaborator to identify the two by `exact` makes it unfold the whole composite inside
`Function.Bijective`, which exceeds its recursion budget. Rewriting with the propositional
equality `baseChangeSectionsMap_eq` — itself a one-step `rfl` — avoids that unfolding, and is why
that equation is recorded.

*`omit` on the four properties of the functor.* `fromExtendScalarsComp` and its value on the pure
tensors use the functor only as a functor. Leaving the four Eilenberg-Watts hypotheses in their
argument lists would make the instances part of the term, so the same map written in two places
would carry two different instance terms and the two would have to be identified.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TensorProduct
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped ChangeOfRings

universe u

namespace ModuleCat.ExtendScalars

variable {R₀ R A : Type u} [CommRing R₀] [CommRing R] [CommRing A]

/-- **The map out of an extension of scalars on a pure tensor.** The `A`-linear map determined by
an `R`-linear `g` sends `a ⊗ x` to `a • g x`; this is how `a ⊗ x ↦ a • g x` is read off the
construction. -/
lemma fromExtendScalars_tmul (ρ : R₀ →+* A) {X : ModuleCat.{u} R₀} {Y : ModuleCat.{u} A}
    (g : X ⟶ (ModuleCat.restrictScalars ρ).obj Y) (a : A) (x : X) :
    (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars ρ g) (a ⊗ₜ[R₀,ρ] x) =
      a • ((g x : Y)) := rfl

/-- **The map out of an extension of scalars on a pure tensor with `1`.** The `A`-linear map
determined by an `R`-linear `g` sends `1 ⊗ x` to `g x`, which is what determines it. -/
lemma fromExtendScalars_one_tmul (ρ : R₀ →+* A) {X : ModuleCat.{u} R₀} {Y : ModuleCat.{u} A}
    (g : X ⟶ (ModuleCat.restrictScalars ρ).obj Y) (x : X) :
    (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars ρ g)
      ((1 : A) ⊗ₜ[R₀,ρ] x) = g x := by
  rw [fromExtendScalars_tmul, one_smul]

/-- **Multiplication by a scalar respects equality of elements**, for the scalars of a module
read through a ring map. The statement exists so that the congruence can be applied where the
`A`-action on `(ModuleCat.restrictScalars ρ).obj Y` is the one `fromExtendScalars_tmul`
produces. -/
lemma smul_congr (ρ : R₀ →+* A) {Y : ModuleCat.{u} A} (a : A)
    {x y : (ModuleCat.restrictScalars ρ).obj Y} (h : x = y) : a • x = a • y :=
  congrArg (fun z : (ModuleCat.restrictScalars ρ).obj Y => a • z) h

section CongrBase

variable (σ : R₀ ≃+* R) (φ : R →+* A) {M : ModuleCat.{u} R} {M₀ : ModuleCat.{u} R₀}
  (j : (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj M ≅ M₀)

/-- The forward map of `ModuleCat.ExtendScalars.congrBase`, `a ⊗ x ↦ a ⊗ j⁻¹ x`: the map out of
an extension of scalars determined by the unit of the extension-restriction adjunction along
`φ`, read through `j⁻¹`. -/
def congrBaseHom :
    (ModuleCat.extendScalars ((φ : R →+* A).comp (σ : R₀ →+* R))).obj M₀ ⟶
      (ModuleCat.extendScalars φ).obj M :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars _
    (j.inv ≫ (ModuleCat.restrictScalars (σ : R₀ →+* R)).map
      ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M))

/-- The backward map of `ModuleCat.ExtendScalars.congrBase`, `a ⊗ y ↦ a ⊗ j y`. The `R`-linear
map it is determined by is the preimage, under the equivalence of categories that restriction of
scalars along a ring isomorphism is, of the unit of the extension-restriction adjunction along
`φ ∘ σ` read through `j`. -/
def congrBaseInv :
    (ModuleCat.extendScalars φ).obj M ⟶
      (ModuleCat.extendScalars ((φ : R →+* A).comp (σ : R₀ →+* R))).obj M₀ :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).fullyFaithfulFunctor.preimage
      (show (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj M ⟶
          (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj
            ((ModuleCat.restrictScalars φ).obj
              ((ModuleCat.extendScalars ((φ : R →+* A).comp (σ : R₀ →+* R))).obj M₀)) from
        j.hom ≫ (ModuleCat.extendRestrictScalarsAdj
          ((φ : R →+* A).comp (σ : R₀ →+* R))).unit.app M₀))

/-- The forward map of `ModuleCat.ExtendScalars.congrBase` on a pure tensor. -/
lemma congrBaseHom_tmul (a : A) (x : M₀) :
    (congrBaseHom σ φ j) (a ⊗ₜ[R₀,((φ : R →+* A).comp (σ : R₀ →+* R))] x) =
      a ⊗ₜ[R,φ] ((ModuleCat.Hom.hom j.inv) x) :=
  (fromExtendScalars_tmul _ _ a x).trans
    ((ModuleCat.ExtendScalars.smul_tmul φ a 1 _).trans
      (congrArg (fun t : A => t ⊗ₜ[R,φ] ((ModuleCat.Hom.hom j.inv) x)) (mul_one a)))

/-- The backward map of `ModuleCat.ExtendScalars.congrBase` on a pure tensor. -/
lemma congrBaseInv_tmul (a : A) (y : M) :
    (congrBaseInv σ φ j) (a ⊗ₜ[R,φ] y) =
      a ⊗ₜ[R₀,((φ : R →+* A).comp (σ : R₀ →+* R))] ((ModuleCat.Hom.hom j.hom) y) := by
  refine (fromExtendScalars_tmul _ _ a y).trans (Eq.trans ?_
    ((ModuleCat.ExtendScalars.smul_tmul ((φ : R →+* A).comp (σ : R₀ →+* R)) a 1 _).trans
      (congrArg (fun t : A => t ⊗ₜ[R₀,((φ : R →+* A).comp (σ : R₀ →+* R))]
        ((ModuleCat.Hom.hom j.hom) y)) (mul_one a))))
  refine congrArg (fun z => a • z) ?_
  exact congrArg (fun ι : (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj M ⟶
      (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj
        ((ModuleCat.restrictScalars φ).obj
          ((ModuleCat.extendScalars ((φ : R →+* A).comp (σ : R₀ →+* R))).obj M₀)) =>
    (ModuleCat.Hom.hom ι) y)
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).fullyFaithfulFunctor.map_preimage _)

/-- `j⁻¹` followed by `j` is the identity, read on elements. -/
lemma hom_inv_apply (x : M₀) : (ModuleCat.Hom.hom j.hom) ((ModuleCat.Hom.hom j.inv) x) = x :=
  congrArg (fun ι : M₀ ⟶ M₀ => (ModuleCat.Hom.hom ι) x) j.inv_hom_id

/-- `j` followed by `j⁻¹` is the identity, read on elements. -/
lemma inv_hom_apply (y : M) : (ModuleCat.Hom.hom j.inv) ((ModuleCat.Hom.hom j.hom) y) = y :=
  congrArg (fun ι : (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj M ⟶
      (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj M => (ModuleCat.Hom.hom ι) y) j.hom_inv_id

/-- **Extension of scalars does not see which of two isomorphic base rings is used.** For a ring
isomorphism `σ : R₀ ≃+* R`, a ring map `φ : R →+* A`, a module `M` over `R` and an isomorphism
`j` of `R₀`-modules from `M` with its scalars restricted along `σ` to `M₀`,

`A ⊗_{R₀} M₀ ≅ A ⊗_R M`

as `A`-modules, by `a ⊗ x ↦ a ⊗ j⁻¹ x`. Both directions are maps out of an extension of scalars,
so both are determined by their values on the pure tensors `1 ⊗ x`, and there the two composites
are `a ⊗ x ↦ a ⊗ j (j⁻¹ x)` and `a ⊗ y ↦ a ⊗ j⁻¹ (j y)`. -/
def congrBase :
    (ModuleCat.extendScalars ((φ : R →+* A).comp (σ : R₀ →+* R))).obj M₀ ≅
      (ModuleCat.extendScalars φ).obj M where
  hom := congrBaseHom σ φ j
  inv := congrBaseInv σ φ j
  hom_inv_id := ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun x =>
    (CategoryTheory.comp_apply (congrBaseHom σ φ j) (congrBaseInv σ φ j) _).trans
      ((congrArg (fun z => (congrBaseInv σ φ j) z) (congrBaseHom_tmul σ φ j 1 x)).trans
        ((congrBaseInv_tmul σ φ j 1 _).trans
          (congrArg (fun y => ((1 : A) ⊗ₜ[R₀,((φ : R →+* A).comp (σ : R₀ →+* R))] y))
            (hom_inv_apply σ j x))))
  inv_hom_id := ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun y =>
    (CategoryTheory.comp_apply (congrBaseInv σ φ j) (congrBaseHom σ φ j) _).trans
      ((congrArg (fun z => (congrBaseHom σ φ j) z) (congrBaseInv_tmul σ φ j 1 y)).trans
        ((congrBaseHom_tmul σ φ j 1 _).trans
          (congrArg (fun z => ((1 : A) ⊗ₜ[R,φ] z)) (inv_hom_apply σ j y))))

/-- The isomorphism `ModuleCat.ExtendScalars.congrBase` on a pure tensor. -/
lemma congrBase_hom_tmul (a : A) (x : M₀) :
    (congrBase σ φ j).hom (a ⊗ₜ[R₀,((φ : R →+* A).comp (σ : R₀ →+* R))] x) =
      a ⊗ₜ[R,φ] ((ModuleCat.Hom.hom j.inv) x) :=
  congrBaseHom_tmul σ φ j a x

/-- **The ring of scalars transported along a ring isomorphism.** For ring maps `φ : R →+* A`
and `ψ : R →+* B` and a ring isomorphism `e : A ≃+* B` with `ψ = e ∘ φ`, the rings `A` and `B`
are isomorphic as `R`-modules, through `e`. This is
`ModuleCat.restrictScalarsIsoOfEquiv` — which says that `B`, viewed as an `A`-module through `e`,
is `A` — with the scalars of both sides further restricted along `φ`. -/
def restrictScalarsSelfIso (φ : R →+* A) {B : Type u} [CommRing B] (ψ : R →+* B) (e : A ≃+* B)
    (he : ψ = (e : A →+* B).comp φ) :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of A A) ≅
      (ModuleCat.restrictScalars ψ).obj (ModuleCat.of B B) := by
  subst he
  exact ((ModuleCat.restrictScalars φ).mapIso (ModuleCat.restrictScalarsIsoOfEquiv e)).symm

/-- The isomorphism `restrictScalarsSelfIso` is `e` on elements. -/
lemma restrictScalarsSelfIso_hom_apply (φ : R →+* A) {B : Type u} [CommRing B] (ψ : R →+* B)
    (e : A ≃+* B) (he : ψ = (e : A →+* B).comp φ) (x : A) :
    (restrictScalarsSelfIso φ ψ e he).hom x = e x := by
  subst he
  rfl

end CongrBase

end ModuleCat.ExtendScalars

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **Multiplication by a ring element, as an endomorphism of a module of scalars.** For a ring
map `φ : R →+* A`, the ring `A` is an `R`-module through `φ`, and multiplication by `a : A` is
`R`-linear for that action. This is the endomorphism of the argument of a functor whose image
under the functor gives the action of `A` on the value, in the Eilenberg-Watts presentation. -/
def mulLeftRestrictScalars {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (a : A) :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of A A) ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of A A) :=
  (ModuleCat.restrictScalars φ).map (ModuleCat.ofHom (LinearMap.mulLeft A a))

/-- **`r ↦ r • a` is `r ↦ r • 1` followed by multiplication by `a`.** The two sides send `r` to
`φ r * a` and to `a * (φ r * 1)`, which agree because `A` is commutative. -/
lemma toSpanSingleton_eq_mulLeftRestrictScalars {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (a : A) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) a) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A)) ≫
        mulLeftRestrictScalars φ a := by
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  show φ r * a = a * (φ r * 1)
  rw [mul_one, mul_comm]

variable {R₀ R A : Type u} [CommRing R₀] [CommRing R] [CommRing A]
  (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [Functor.Linear R F]
  [PreservesFiniteColimits F] [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F]

/-- **The module theory behind the construction of `ψ`.** Let `F` be a right exact `R`-linear
endofunctor of `R`-modules commuting with arbitrary direct sums — so Eilenberg-Watts
(`Stacks.EilenbergWatts.linearEquiv`) presents it as tensoring with `F(R)` — let `φ : R →+* A`
and `ρ : R₀ →+* A` be ring maps with `ρ = φ ∘ σ` for a ring isomorphism `σ : R₀ ≃+* R`, and let
`M₀` be an `R₀`-module isomorphic to `F(R)` with its scalars restricted along `σ`.

If `Ξ` is an additive bijection from `F(A)` to an `A`-module `N` which carries
`F(multiplication by a)` to multiplication by `a`, then the `A`-linear map
`A ⊗_{R₀} M₀ ⟶ N` whose value at `1 ⊗ m` is `Ξ (F(r ↦ r • 1)(j m))` is **bijective**: on the
pure tensor `a ⊗ m` it is the Eilenberg-Watts comparison at `j m ⊗ a`, because
`r ↦ r • a` factors through multiplication by `a`. -/
theorem bijective_fromExtendScalars_of_mulLeft
    (σ : R₀ ≃+* R) (φ : R →+* A) (ρ : R₀ →+* A)
    (hρ : ρ = (φ : R →+* A).comp (σ : R₀ →+* R)) {M₀ : ModuleCat.{u} R₀}
    (j : (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj (F.obj (ModuleCat.of R R)) ≅ M₀)
    {N : ModuleCat.{u} A}
    (Xi : (F.obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) : Type u) → (N : Type u))
    (hadd : ∀ x y, Xi (x + y) = Xi x + Xi y) (hbij : Function.Bijective Xi)
    (hmul : ∀ (a : A) (y : F.obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))),
      Xi ((F.map (mulLeftRestrictScalars φ a)).hom y) = a • ((Xi y : N)))
    (al : M₀ ⟶ (ModuleCat.restrictScalars ρ).obj N)
    (hal : ∀ x : M₀, al x =
      Xi ((F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A)))).hom
        ((ModuleCat.Hom.hom j.inv) x))) :
    Function.Bijective (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars ρ al) := by
  subst hρ
  have hzero : Xi 0 = 0 := by
    have h := hadd 0 0
    simpa using h.symm
  have key : ∀ z : (ModuleCat.extendScalars ((φ : R →+* A).comp (σ : R₀ →+* R))).obj M₀,
      (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          ((φ : R →+* A).comp (σ : R₀ →+* R)) al) z =
      Xi (Stacks.EilenbergWatts.linearEquiv F
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
        (TensorProduct.comm R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
          (F.obj (ModuleCat.of R R))
          ((ModuleCat.ExtendScalars.congrBaseHom σ φ j) z))) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      refine (map_zero _).trans (Eq.symm ?_)
      refine Eq.trans (congrArg (fun w => Xi (Stacks.EilenbergWatts.linearEquiv F
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
        (TensorProduct.comm R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
          (F.obj (ModuleCat.of R R)) w))) (map_zero _)) ?_
      refine Eq.trans (congrArg (fun w => Xi (Stacks.EilenbergWatts.linearEquiv F
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) w)) (map_zero _)) ?_
      exact (congrArg Xi (map_zero _)).trans hzero
    | tmul a m =>
      refine (ModuleCat.ExtendScalars.fromExtendScalars_tmul _ al a m).trans ?_
      refine (ModuleCat.ExtendScalars.smul_congr (R₀ := R₀) (A := A) (Y := N)
        ((φ : R →+* A).comp (σ : R₀ →+* R)) a (hal m)).trans ?_
      refine (hmul a ((F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A)))).hom
        ((ModuleCat.Hom.hom j.inv) m))).symm.trans ?_
      refine Eq.trans (congrArg Xi ((CategoryTheory.comp_apply
        (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A))))
        (F.map (mulLeftRestrictScalars φ a)) _).symm)) ?_
      refine Eq.trans (congrArg (fun ι : F.obj (ModuleCat.of R R) ⟶
          F.obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) =>
        Xi ((ModuleCat.Hom.hom ι) ((ModuleCat.Hom.hom j.inv) m)))
        (((F.map_comp _ _).symm).trans (congrArg F.map
          (toSpanSingleton_eq_mulLeftRestrictScalars φ a).symm))) ?_
      refine Eq.trans (congrArg Xi (Stacks.EilenbergWatts.linearEquiv_tmul F
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
        ((ModuleCat.Hom.hom j.inv) m) a).symm) ?_
      exact congrArg (fun w => Xi (Stacks.EilenbergWatts.linearEquiv F
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) w))
        (((congrArg (TensorProduct.comm R
              ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
              (F.obj (ModuleCat.of R R)))
            (ModuleCat.ExtendScalars.congrBaseHom_tmul σ φ j a m)).trans
          (TensorProduct.comm_tmul _ _ _ _ _)).symm)
    | add z z' hz hz' =>
      refine (map_add _ z z').trans ?_
      refine (congrArg₂ (fun t t' : (N : Type u) => t + t') hz hz').trans ?_
      refine ((hadd _ _).symm).trans (congrArg Xi ?_)
      refine Eq.trans ((map_add _ _ _).symm) (congrArg (Stacks.EilenbergWatts.linearEquiv F
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))) ?_)
      exact Eq.trans ((map_add _ _ _).symm) (congrArg (TensorProduct.comm R
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (F.obj (ModuleCat.of R R)))
        (map_add _ _ _).symm)
  rw [show (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        ((φ : R →+* A).comp (σ : R₀ →+* R)) al :
      ((ModuleCat.extendScalars ((φ : R →+* A).comp (σ : R₀ →+* R))).obj M₀ : Type u) →
        (N : Type u)) =
      Xi ∘ (Stacks.EilenbergWatts.linearEquiv F
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))) ∘
        (TensorProduct.comm R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
          (F.obj (ModuleCat.of R R))) ∘
        (ModuleCat.ExtendScalars.congrBaseHom σ φ j) from funext key]
  refine hbij.comp ((Stacks.EilenbergWatts.linearEquiv F _).bijective.comp
    ((TensorProduct.comm R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A))
          (F.obj (ModuleCat.of R R))).bijective.comp ?_))
  exact ConcreteCategory.bijective_of_isIso (ModuleCat.ExtendScalars.congrBase σ φ j).hom

section Comp

variable (σ : R₀ ≃+* R) (φ : R →+* A) (ρ : R₀ →+* A)
  (hρ : ρ = (φ : R →+* A).comp (σ : R₀ →+* R)) {M₀ : ModuleCat.{u} R₀}
  (j : (ModuleCat.restrictScalars (σ : R₀ →+* R)).obj (F.obj (ModuleCat.of R R)) ≅ M₀)
  {N : ModuleCat.{u} A}
  (Xi : F.obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) ⟶
    (ModuleCat.restrictScalars φ).obj N)

omit [F.Additive] [Functor.Linear R F] [PreservesFiniteColimits F]
  [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F] in
/-- **The map out of a base change that the Eilenberg-Watts presentation produces.** For a ring
isomorphism `σ : R₀ ≃+* R`, ring maps `φ : R →+* A` and `ρ : R₀ →+* A` with `ρ = φ ∘ σ`, an
`R₀`-module `M₀` identified by `j` with the Eilenberg-Watts module `F(R)` of `F`, and a
comparison `Xi` of `F(A)` with an `A`-module `N`, the `A`-linear map

`A ⊗_{R₀} M₀ ⟶ N`

determined by `x ↦ Xi (F(r ↦ r • 1) (j⁻¹ x))`. The transport along `ρ = φ ∘ σ` of the restriction
of scalars is `ModuleCat.restrictScalarsCongr`, whose underlying map is the identity. -/
def fromExtendScalarsComp :
    (ModuleCat.extendScalars ρ).obj M₀ ⟶ N :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars ρ
    (j.inv ≫ (ModuleCat.restrictScalars (σ : R₀ →+* R)).map
        (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A))) ≫ Xi) ≫
      (ModuleCat.restrictScalarsCongr hρ.symm).hom.app N)

omit [F.Additive] [Functor.Linear R F] [PreservesFiniteColimits F]
  [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F] in
/-- **`fromExtendScalarsComp` on the pure tensors.** Its value at `1 ⊗ x` is the value at `x` of
the `R₀`-linear map the construction is determined by: `j` inverted, then `F` of the unit
`r ↦ r • 1` of the ring `A` followed by `Xi`, then the transport of the restriction of scalars
along `ρ = φ ∘ σ`.

*Why the right-hand side is kept as a single morphism applied to the element,* rather than the
nest of applications of `Xi`, of `F` of the unit and of `j⁻¹` that unfolding it would give. At
the concrete geometric spelling this is used at, a `CategoryTheory.comp_apply` or a
`ModuleCat.restrictScalars.map_apply` performed against that spelling costs a definitional
reconciliation of a restriction of scalars in the presence of a concrete element, and that
exhausts the elaborator; keeping the composite intact is what
`…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul_of_eq` needs in order to discharge each
ingredient separately and at morphism level. -/
lemma fromExtendScalarsComp_one_tmul (x : M₀) :
    fromExtendScalarsComp F σ φ ρ hρ j Xi ((1 : A) ⊗ₜ[R₀,ρ] x) =
      (j.inv ≫ (ModuleCat.restrictScalars (σ : R₀ →+* R)).map
          (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
            ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A))) ≫ Xi) ≫
        (ModuleCat.restrictScalarsCongr hρ.symm).hom.app N) x := by
  rw [fromExtendScalarsComp, ModuleCat.ExtendScalars.fromExtendScalars_one_tmul]

/-- **The module theory behind the construction of `ψ`.** This is
`bijective_fromExtendScalars_of_mulLeft` at the `R₀`-linear map `fromExtendScalarsComp` is
determined by. Its hypotheses are the two properties of `Xi`: bijectivity, and carrying
`F(multiplication by a)` to multiplication by `a`, the latter as an equality of morphisms. -/
theorem bijective_fromExtendScalarsComp
    (hbij : Function.Bijective (ModuleCat.Hom.hom Xi))
    (hmul : ∀ a : A, F.map (mulLeftRestrictScalars φ a) ≫ Xi =
      Xi ≫ (ModuleCat.restrictScalars φ).map (a • 𝟙 N)) :
    Function.Bijective (ModuleCat.Hom.hom (fromExtendScalarsComp F σ φ ρ hρ j Xi)) :=
  bijective_fromExtendScalars_of_mulLeft F σ φ ρ hρ j
    (fun y => (ModuleCat.Hom.hom Xi) y) (fun y y' => map_add _ y y') hbij
    (fun a y =>
      (CategoryTheory.comp_apply (F.map (mulLeftRestrictScalars φ a)) Xi y).symm.trans
        ((congrArg (fun ι : F.obj ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) ⟶
            (ModuleCat.restrictScalars φ).obj N => (ModuleCat.Hom.hom ι) y) (hmul a)).trans
          (CategoryTheory.comp_apply Xi
            ((ModuleCat.restrictScalars φ).map (a • 𝟙 N)) y)))
    (j.inv ≫ (ModuleCat.restrictScalars (σ : R₀ →+* R)).map
        (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)) (1 : A))) ≫ Xi) ≫
      (ModuleCat.restrictScalarsCongr hρ.symm).hom.app N)
    (fun _ => rfl)

end Comp

section Geometry

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

omit [IsAffine (V : Scheme)] [IsAffine (W : Scheme)] in
/-- **The map on sections of `h` over the pair of opens factors through the functions on `V`.**
`h.appLE V W` is the ring map `Γ(V, ⊤) ⟶ Γ(Y'', W)` of the pair of opens read through
`AlgebraicGeometry.Scheme.Opens.topIso` at `V`. -/
lemma appLE_eq_comp_topIso :
    (h.appLE V W hWV).hom =
      ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom).comp
        ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv : Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))
        := by
  rw [RingHom.comp_assoc]
  rw [show (Scheme.Opens.topIso V).hom.hom.comp
        ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
          Γ(S.Y', V) →+* Γ((V : Scheme), ⊤)) = RingHom.id _ from
    congrArg CommRingCat.Hom.hom (Scheme.Opens.topIso V).inv_hom_id]
  rfl

omit [IsAffine (W : Scheme)] in
/-- **The functions on `W` act on the cohomology over `f''⁻¹(W)` through either side of the
restricted square.** The two ring maps `Γ(V, ⊤) ⟶ Γ(f''⁻¹(W), ⊤)` — one along `h` and then
`f''`, the other along `f'` and then `h'` — are equal, because the square restricted to the pair
of opens commutes. The second is the one the Eilenberg-Watts functor restricts scalars along,
by `…TopDegreeBaseChangeSituation.restrictBase_appTop_eq_algebraMap`. -/
lemma appTop_comp_eq_appTop_comp_algebraMap :
    (f'' ∣_ W).appTop.hom.comp ((Scheme.Opens.topIso W).inv.hom.comp
        ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)) =
      (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
          (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom.comp
        (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤)) := by
  rw [S.restrictBase_appTop_eq_algebraMap V]
  have hw := (isPullback_resLE_of_isPullback hsq hWV (V := V) (W := W)).w
  have h1 : (Scheme.Opens.topIso W).inv.hom.comp
      ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom) =
      (h.resLE V W hWV).appTop.hom := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rfl
  rw [h1]
  have h2 := congrArg (fun ι : _ ⟶ _ => CommRingCat.Hom.hom (Scheme.Hom.appTop ι)) hw
  simp only [Scheme.Hom.comp_appTop] at h2
  exact h2.symm

/-- **The functions on `W` over the functions on `V`, in the spelling the geometric factor of
conclusion (b) consumes.** The ring `Γ(Y'', W)`, read as a module over `Γ(V, ⊤)` through
`h.appLE V W` and `AlgebraicGeometry.Scheme.Opens.topIso`, is the module of global sections of
`(h ∣_ V^W)_* 𝒪_W` — which is what the right-hand end of the computation,
`…TopDegreeBaseChange.cohomologyPullbackIsoTensorTildeAffineOpens`, tensors with. The two differ
by the ring isomorphism `Γ(Y'', W) ≅ Γ(W, ⊤)`, and the compatibility of the two ring maps is
`AlgebraicGeometry.Scheme.Hom.resLE_app_top`. -/
def sectionsIsoPushforwardUnitSections :
    (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
          (Scheme.Opens.topIso V).hom.hom)).obj (ModuleCat.of Γ(Y'', W) Γ(Y'', W)) ≅
      (ModuleCat.restrictScalars (h.resLE V W hWV).appTop.hom).obj
        (ModuleCat.of Γ((W : Scheme), ⊤) Γ((W : Scheme), ⊤)) :=
  ModuleCat.ExtendScalars.restrictScalarsSelfIso _ _
    ((Scheme.Opens.topIso W).symm.commRingCatIsoToRingEquiv)
    (by
      have h1 : (Scheme.Opens.topIso W).inv.hom.comp
          ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom) =
          (h.resLE V W hWV).appTop.hom := by
        rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
        rfl
      exact h1.symm)

/-- **The tensor factor of the geometric factor of (b) at the functions on `W`, in the spelling
the right-hand end of the computation uses.** The geometric factor pulls the tilde module back
along the structure morphism `(f' ∣_ V) ≫ V.isoSpec` of the restricted situation over
`Spec Γ(V, ⊤)`; the right-hand end pulls the associated module of
`Stacks.Coherent.affineTilde` back along `f' ∣_ V`. The two agree:
`AlgebraicGeometry.Scheme.Modules.pullbackComp` splits the composite and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` identifies the restriction along
`V.isoSpec` with the pullback along it, which is the one step of `affineTilde` beyond the tilde
functor. -/
def pullbackTildeSectionsIso :
    (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).obj
        ((AlgebraicGeometry.tilde.functor (CommRingCat.of Γ((V : Scheme), ⊤))).obj
          ((ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom)).obj (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))) ≅
      (Scheme.Modules.pullback (S.f' ∣_ V)).obj
        ((Stacks.Coherent.affineTilde (V : Scheme)).obj
          ((_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).obj
            ((Scheme.Modules.pushforward (h.resLE V W hWV)).obj
              (Scheme.unitModule (W : Scheme))))) :=
  pullbackTildeIsoPullbackAffineTilde S.f' V
      ((ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
        (Scheme.Opens.topIso V).hom.hom)).obj (ModuleCat.of Γ(Y'', W) Γ(Y'', W))) ≪≫
    (Scheme.Modules.pullback (S.f' ∣_ V)).mapIso
      ((Stacks.Coherent.affineTilde (V : Scheme)).mapIso
        (sectionsIsoPushforwardUnitSections S h hWV))

/-- **The value of the functor of [Stacks, Tag 0EX3] (b) over `V`, written out.** The functor is
a composite of three functors and a restriction of scalars, each of which is an `abbrev` or a
functor composition, so the equality holds by `rfl`; it is recorded as an equality of objects so
that the chain of isomorphisms below is formed at one spelling of the tensor product of module
sheaves and no isomorphism has to be reconciled at a component. -/
lemma topDegreeFunctor_obj_eq (N : ModuleCat.{u} Γ((V : Scheme), ⊤)) :
    ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩).obj N =
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).obj
        (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).obj
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).obj
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).obj
                ((AlgebraicGeometry.tilde.functor
                  (CommRingCat.of Γ((V : Scheme), ⊤))).obj N)))) := rfl

/-- **The value at the functions on `W` of the functor of [Stacks, Tag 0EX3] (b) over `V` is the
degree-`d` cohomology of `(h')^* F'` over `f''⁻¹(W)`.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`F'`, the endofunctor `M ↦ H^d(f'⁻¹(V), F'| ⊗ (f' ∣_ V)^* M~)` of `Γ(V, ⊤)`-modules takes the
functions on `W` to `H^d(f''⁻¹(W), ((h')^* F')|)`.

Three existing results are composed: the functions on `W` are the global sections of
`(h ∣_ V^W)_* 𝒪_W` (`sectionsIsoPushforwardUnitSections`, through `pullbackTildeSectionsIso`),
the geometric factor at that module is the right-hand end of the source's computation
(`…TopDegreeBaseChange.cohomologyPullbackIsoTensorTildeAffineOpens`), and the two spellings of
the cohomology upstairs agree
(`…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso`). -/
def topDegreeFunctorObjIsoCohomologyUpstairs :
    ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩).obj
        ((ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
          (Scheme.Opens.topIso V).hom.hom)).obj (ModuleCat.of Γ(Y'', W) Γ(Y'', W))) ≅
      (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
          Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).obj
        ((ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
            (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).obj
          (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
              ((Scheme.Modules.pullback h').obj F')))) :=
  eqToIso (topDegreeFunctor_obj_eq S F'
      ((ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
        (Scheme.Opens.topIso V).hom.hom)).obj (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))) ≪≫
    (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
      Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).mapIso
    (((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).mapIso
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).mapIso
          ((Iso.refl ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).prod
            (pullbackTildeSectionsIso S h hWV))) ≪≫
      (cohomologyPullbackIsoTensorTildeAffineOpens hsq hWV
          (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d).symm ≪≫
      (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
          (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).mapIso
        (restrictPullbackRightDerivedPlusIso (h := h) h'
          (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).symm)

include hsq in
/-- **The base-changed morphism is quasi-compact.** `f''` is a base change of `S.f'`, which is
one, and quasi-compactness is stable under base change. -/
theorem quasiCompact_of_isPullback : QuasiCompact f'' :=
  have := S.quasiCompact_f'
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) hsq inferInstance

include hsq in
/-- **The base-changed morphism is quasi-separated.** `f''` is a base change of `S.f'`, which is
one, and quasi-separatedness is stable under base change. -/
theorem quasiSeparated_of_isPullback : QuasiSeparated f'' :=
  have := S.quasiSeparated_f'
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) hsq inferInstance

/-- **The sections of the right-hand end of `γ⁺` over `W` are the value at the functions on `W`
of the functor of [Stacks, Tag 0EX3] (b) over `V`.** This is the computation the source performs:
over a compatible pair of affine opens, `Γ(R^d f''_* (h')^* F', W)` is `Φ(Γ(Y'', W))` for the
endofunctor `Φ` of `Γ(V, ⊤)`-modules of conclusion (b), both read as modules over the functions
on `V`.

`topDegreeFunctorObjIsoCohomologyUpstairs` computes the left-hand side as the cohomology of
`((h')^* F')|` over `f''⁻¹(W)`, and [Stacks, Tag 01XK] over the affine open `W` —
`…TopDegreeBaseChange.targetSectionsIsoCohomology` — computes the right-hand side as the same
cohomology. The two readings of the action of the functions on `V` on that cohomology, one along
each side of the restricted square, agree by
`appTop_comp_eq_appTop_comp_algebraMap`; the transport between them is `eqToIso` of a `congrArg`
in the ring map, as in
`…TopDegreeBaseChange.affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology`. -/
def topDegreeFunctorObjIsoTargetSections :
    ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩).obj
        ((ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
          (Scheme.Opens.topIso V).hom.hom)).obj (ModuleCat.of Γ(Y'', W) Γ(Y'', W))) ≅
      (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
          (Scheme.Opens.topIso V).hom.hom)).obj
        (ModuleCat.of Γ(Y'', W)
          Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'), W)) :=
  topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV ≪≫
    eqToIso (congrArg (fun ψ : (S.restrictBase V).affineBaseRing →+*
          Γ((f'' ⁻¹ᵁ W : Scheme), ⊤) =>
        (ModuleCat.restrictScalars ψ).obj
          (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
              ((Scheme.Modules.pullback h').obj F'))))
      (appTop_comp_eq_appTop_comp_algebraMap S h' f'' h hsq hWV).symm) ≪≫
    (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
        (Scheme.Opens.topIso V).hom.hom)).mapIso
      (targetSectionsIsoCohomology S F' h' f''
        (quasiCompact_of_isPullback S h' f'' h hsq)
        (quasiSeparated_of_isPullback S h' f'' h hsq) W)

/-- **The identification of the right-hand end with the value of the functor of conclusion (b) is
bijective**, being an isomorphism of modules. -/
lemma bijective_topDegreeFunctorObjIsoTargetSections :
    Function.Bijective (ModuleCat.Hom.hom
      (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) :=
  have := Iso.isIso_hom (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV)
  ConcreteCategory.bijective_of_isIso _

/-- **The sections of `R^d f'_* F'` over `V` are the Eilenberg-Watts module of the functor of
conclusion (b) over `V`.** The module `Φ(Γ(V, ⊤))` of
`…TopDegreeBaseChangeSituation.topDegreeFunctorObjSelfIso` is the top-degree cohomology of `F'`
over `f'⁻¹(V)`, which by [Stacks, Tag 01XK] over the affine open `V` is `Γ(R^d f'_* F', V)`; the
two readings of the scalars are crossed by `AlgebraicGeometry.Scheme.Opens.topIso`, which is the
restriction of scalars the statement is read through. -/
def topDegreeFunctorObjSelfIsoSourceSections :
    (ModuleCat.restrictScalars ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
        Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))).obj
      (((S.restrictBase V).topDegreeFunctor
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
            (inferInstance :
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩).obj
        (ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤))) ≅
      ModuleCat.of Γ(S.Y', V)
        Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V) :=
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  (ModuleCat.restrictScalars ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
      Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))).mapIso
      ((S.restrictBase V).topDegreeFunctorObjSelfIso
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩) ≪≫
    (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').symm ≪≫
    affineOpenCohomologyIsoSections S.f' V F' S.d

/-- **The map `ψ` that conclusion (c) of [Stacks, Tag 0EX3] needs over a compatible pair of
affine opens.** The `Γ(Y'', W)`-linear map

`Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`

of `fromExtendScalarsComp`, for the functor `Φ` of conclusion (b) over `V`, the identification
`topDegreeFunctorObjSelfIsoSourceSections` of the sections of `R^d f'_* F'` over `V` with the
Eilenberg-Watts module of `Φ`, and the identification
`topDegreeFunctorObjIsoTargetSections` of the sections of `R^d f''_* (h')^* F'` over `W` with the
value of `Φ` at the functions on `W`. Its value on `1 ⊗ x` is
`baseChangeSectionsMap_one_tmul`. -/
def baseChangeSectionsMap :
    (ModuleCat.extendScalars (h.appLE V W hWV).hom).obj
        (ModuleCat.of Γ(S.Y', V)
          Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V)) ⟶
      ModuleCat.of Γ(Y'', W)
        Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pullback h').obj F'), W) :=
  fromExtendScalarsComp
    ((S.restrictBase V).topDegreeFunctor
      ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
        (inferInstance :
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩)
    ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv)
    ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)
    (h.appLE V W hWV).hom (appLE_eq_comp_topIso S h hWV)
    (topDegreeFunctorObjSelfIsoSourceSections S F')
    (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom

/-- **`ψ` is the map `fromExtendScalarsComp` produces**, by definition. The equation is recorded
so that the statements about that map can be read as statements about `ψ`. -/
lemma baseChangeSectionsMap_eq :
    baseChangeSectionsMap S F' h' f'' h hsq hWV = fromExtendScalarsComp
      ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩)
      ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv)
      ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)
      (h.appLE V W hWV).hom (appLE_eq_comp_topIso S h hWV)
      (topDegreeFunctorObjSelfIsoSourceSections S F')
      (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom := rfl

/-- **`ψ` is bijective.** For a top-degree base-change situation `S`, a quasi-coherent `F'` on
`X'`, a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'` and an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, the
`Γ(Y'', W)`-linear map

`ψ : Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`

of `baseChangeSectionsMap` is bijective, as soon as the identification
`topDegreeFunctorObjIsoTargetSections` of the right-hand end with the value of the functor `Φ` of
conclusion (b) at the functions on `W` carries `Φ(multiplication by a)` to multiplication by `a`
— the hypothesis `hmul`.

Everything else is proved: `bijective_fromExtendScalarsComp` is Eilenberg-Watts read on the pure
tensors, the base rings `Γ(Y', V)` and `Γ(V, ⊤)` are crossed by `appLE_eq_comp_topIso`, and the
Eilenberg-Watts module is `Γ(R^d f'_* F', V)` by `topDegreeFunctorObjSelfIsoSourceSections`.
Neither base carries a hypothesis and neither morphism carries one beyond what the situation
provides: only the two opens are affine. -/
theorem bijective_fromExtendScalarsComp_sections
    (hmul : ∀ a : Γ(Y'', W),
      ((S.restrictBase V).topDegreeFunctor
            ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (inferInstance :
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                  F').IsQuasicoherent)⟩).map
            (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
              (Scheme.Opens.topIso V).hom.hom) a) ≫
          (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom =
        (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom ≫
          (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
              (Scheme.Opens.topIso V).hom.hom)).map
            (a • 𝟙 (ModuleCat.of Γ(Y'', W)
              Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                ((Scheme.Modules.pullback h').obj F'), W)))) :
    Function.Bijective (ModuleCat.Hom.hom (fromExtendScalarsComp
      ((S.restrictBase V).topDegreeFunctor
        ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
          (inferInstance :
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩)
      ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv)
      ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)
      (h.appLE V W hWV).hom (appLE_eq_comp_topIso S h hWV)
      (topDegreeFunctorObjSelfIsoSourceSections S F')
      (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom)) := by
  let G : (SheafOfModules.isQuasicoherent
      (S.restrictBase V).affineBaseOver.left.ringCatSheaf).FullSubcategory :=
    ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
      (inferInstance :
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F').IsQuasicoherent)⟩
  have := (S.restrictBase V).additive_topDegreeFunctor G
  have := (S.restrictBase V).linear_topDegreeFunctor G
  have := (S.restrictBase V).preservesFiniteColimits_topDegreeFunctor G
  have := fun J : Type u =>
    (S.restrictBase V).preservesColimitsOfShape_discrete_topDegreeFunctor G J
  exact bijective_fromExtendScalarsComp _ _ _ _ _ _ _
    (bijective_topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV) hmul

/-- **`ψ` is bijective.** This is `bijective_fromExtendScalarsComp_sections` read through
`baseChangeSectionsMap_eq`, which says that `ψ` is the map that statement is about. -/
theorem bijective_baseChangeSectionsMap
    (hmul : ∀ a : Γ(Y'', W),
      ((S.restrictBase V).topDegreeFunctor
            ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (inferInstance :
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                  F').IsQuasicoherent)⟩).map
            (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
              (Scheme.Opens.topIso V).hom.hom) a) ≫
          (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom =
        (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom ≫
          (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
              (Scheme.Opens.topIso V).hom.hom)).map
            (a • 𝟙 (ModuleCat.of Γ(Y'', W)
              Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                ((Scheme.Modules.pullback h').obj F'), W)))) :
    Function.Bijective (ModuleCat.Hom.hom
      (baseChangeSectionsMap S F' h' f'' h hsq hWV)) := by
  rw [baseChangeSectionsMap_eq]
  exact bijective_fromExtendScalarsComp_sections S F' h' f'' h hsq hWV hmul

end Geometry

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
