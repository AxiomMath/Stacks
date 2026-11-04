module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistCocycleSections

/-!
# The composition law for a pushed-forward comparison, at the level of variables

For an open immersion `a : P ⟶ Q` of schemes, a further morphism `c : Q ⟶ Z`, a module `M` on `Q`
and a module `K` on `P` together with an identification `ι : a^* M ≅ K`, there is a canonical
morphism of sheaves of modules on `Z`

`pushComparison a c hac M K ι : c_* M ⟶ cP_* K`,

where `hac : a ≫ c = cP`. This is the shape of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested`, Tag 01NO's twist comparison for a
nested pair of affine opens of the base of a relative homogeneous spectrum pushed forward to the
relative Proj, with every scheme, module and identification a **variable**.

**This file proves that these morphisms compose as soon as the identifications `ι` do**, which
reduces the composition law for `pushNested` — the one statement
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` is reduced to by
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.isNestedCocycle_of_pushNested_comp` — to the
cocycle condition on the *inverse-image* identifications alone. No open of `Z`, no section and no
containment occurs anywhere below.

## Main definitions

* `…PushforwardCocycle.transpose`: the adjoint transpose of a morphism out of an inverse image,
  `ψ : f^* M ⟶ N` ↦ `M ⟶ f_* N`.
* `…PushforwardCocycle.pushforwardCompCongr`: the identification
  `c_*(a_* K) ≅ cP_* K` attached to `hac : a ≫ c = cP`, the three tail factors of `pushNested`
  with the comparison of the identifications removed.
* `…PushforwardCocycle.pushComparison`: the pushed-forward comparison itself, in the four-factor
  shape `pushNested` has.

## Main results

* `…PushforwardCocycle.transpose_cocycle`: **the transposition step.** A cocycle condition on the
  inverse-image identifications becomes a cocycle condition on their transposes, which are
  morphisms between *pushforwards* and so have concrete sections.
* `…PushforwardCocycle.comp_of_transpose_cocycle`: **the structural step.** A cocycle condition on
  the transposes gives the composition law for the pushed-forward comparisons.
* `…PushforwardCocycle.pushComparison_eq_transpose`: the four-factor shape is the pushforward of
  the transpose followed by `pushforwardCompCongr`.
* `…PushforwardCocycle.pushComparison_comp`: **the two steps composed** — the composition law for
  `pushComparison` from the cocycle condition on the inverse-image identifications.

## Implementation notes

Every proof below is an explicit chain of `Eq.trans`, composed with
`Stacks.AlgebraicGeometry.ProjInclusionTwist.comp_congr` and never with `rw` or `simp`. The reason
is the one recorded throughout this directory: `AlgebraicGeometry.Scheme.Modules` is a `def`, and
a rewrite on a goal mentioning a pushforward of a twist leaves the term type-incorrect at the
transparency `rw` matches with. At the level of variables the terms are small, so a chain of named
lemmas elaborates in seconds while the same goals defeat `simp` outright.

Two spellings are definitionally equal and used as such, each isolated in its own `rfl` lemma so
that no consumer has to rely on the coincidence: `pushforward (α ≫ β) = pushforward α ⋙
pushforward β` (`pushforward_comp_map`) and `pullback α ⋙ pushforward α` applied to a morphism
(`pullback_pushforward_map`). The first is what makes `pushforwardCompCongr` typecheck without an
explicit `AlgebraicGeometry.Scheme.Modules.pushforwardComp`.

`comp_of_transpose_cocycle` is the one proof that descends to sections, because the coherence it
needs — that the pseudofunctoriality and congruence isomorphisms of the pushforward compose — is
not available as a named lemma. There every factor is the identity or a restriction along an
equality of opens, by `AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app` and
`pushforwardCongr_hom_app_app`, and `presheaf_map_eqToHom_self` collapses the latter.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)

## Not done here

No tag is claimed. The cocycle condition on the inverse-image identifications is a **hypothesis**
of every statement below; for Tag 01NO's twist comparisons it is the third assertion of Tag 01MZ
and is not proved in this file.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjInclusionTwist
open Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.AlgebraicGeometry.PushforwardCocycle

universe u

/-! ### Transport along an equality of opens -/

/-- Restriction of a sheaf of modules along a reflexive equality of opens is the identity.
Stated with the equality a free argument, which proof irrelevance reduces to `rfl`: it is applied
at equalities whose two sides are definitionally equal but not syntactically so, and the
elaborator unifies them because it works at default transparency, where `simp` does not. -/
public theorem presheaf_map_eqToHom_self {W : Scheme.{u}} (M : W.Modules) {V : W.Opens}
    (e : V = V) : M.presheaf.map (eqToHom e).op = 𝟙 _ := by
  obtain rfl : e = rfl := Subsingleton.elim _ _
  simp

/-! ### Congruence for a composite

`Stacks.AlgebraicGeometry.ProjInclusionTwist.comp_congr` leaves both factors implicit, so
supplying `rfl` for the untouched one makes the elaborator infer it from the equation rather than
from the goal; at the terms below that reaches the deterministic `whnf` timeout. The one-sided
forms — `CategoryTheory.whisker_eq` and `CategoryTheory.eq_whisker` — take the untouched factor
as an explicit argument, which is read off the goal, and elaborate in milliseconds. -/

section Congr

variable {C : Type*} [Category C]

/-- `hom` of a threefold composite of isomorphisms, at the level of variables. -/
public theorem trans₃_hom {X₀ X₁ X₂ X₃ : C} (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) :
    (a ≪≫ b ≪≫ c).hom = a.hom ≫ b.hom ≫ c.hom :=
  rfl

end Congr

variable {X X' Y Z : Scheme.{u}}

/-- The pseudofunctoriality isomorphism of the pushforward is the identity: the pushforward along
a composite **is** the composite of the pushforwards, and both sides of the component are the
same object. -/
public theorem pushforwardComp_hom_app_eq_id (f : X ⟶ X') (g : X' ⟶ Y) (N : X.Modules) :
    (Scheme.Modules.pushforwardComp f g).hom.app N =
      𝟙 ((Scheme.Modules.pushforward (f ≫ g)).obj N) :=
  Scheme.Modules.hom_ext _ _ fun _ => rfl

/-- The congruence isomorphism of the pushforward at a reflexive equality is the identity. -/
public theorem pushforwardCongr_refl_hom_app (f : X ⟶ X') (hf : f = f) (M : X.Modules) :
    (Scheme.Modules.pushforwardCongr hf).hom.app M = 𝟙 _ :=
  Scheme.Modules.hom_ext _ _ fun U =>
    (Scheme.Modules.pushforwardCongr_hom_app_app hf U).trans (presheaf_map_eqToHom_self M _)

/-- The pushforward along a composite, on a morphism, is the two pushforwards in turn. -/
public theorem pushforward_comp_map (α : X ⟶ X') (β : X' ⟶ Y) {A B : X.Modules} (ξ : A ⟶ B) :
    (Scheme.Modules.pushforward (α ≫ β)).map ξ
      = (Scheme.Modules.pushforward β).map ((Scheme.Modules.pushforward α).map ξ) := rfl

/-- The functor the unit of the pullback--pushforward adjunction is natural into, on a
morphism. -/
public theorem pullback_pushforward_map (α : X ⟶ X') {A B : X'.Modules} (ξ : A ⟶ B) :
    (Scheme.Modules.pullback α ⋙ Scheme.Modules.pushforward α).map ξ
      = (Scheme.Modules.pushforward α).map ((Scheme.Modules.pullback α).map ξ) := rfl

/-! ### The adjoint transpose -/

/-- **The adjoint transpose of a morphism out of an inverse image.** A morphism `f^* M ⟶ N` read
as a morphism `M ⟶ f_* N`, through the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.

The point of passing to the transpose is that the inverse image of a sheaf of modules is a
sheafification of a tensor product and has no usable description of its sections, while a
pushforward has exactly the sections of its argument over the inverse image of the open. -/
public def transpose (f : X ⟶ X') (M : X'.Modules) {N : X.Modules}
    (ψ : (Scheme.Modules.pullback f).obj M ⟶ N) :
    M ⟶ (Scheme.Modules.pushforward f).obj N :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
    (Scheme.Modules.pushforward f).map ψ

/-- **The transpose absorbs a precomposition**: composing with a morphism before transposing is
the same as pulling that morphism back inside the transpose. This is naturality of the unit. -/
public theorem comp_transpose (α : X ⟶ X') (M N' : X'.Modules) (N : X.Modules) (ψβ : M ⟶ N')
    (ψα : (Scheme.Modules.pullback α).obj N' ⟶ N) :
    ψβ ≫ transpose α N' ψα =
      (Scheme.Modules.pullbackPushforwardAdjunction α).unit.app M ≫
        (Scheme.Modules.pushforward α).map ((Scheme.Modules.pullback α).map ψβ ≫ ψα) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    ((Scheme.Modules.pullbackPushforwardAdjunction α).unit.naturality ψβ) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _
    ((eq_whisker (pullback_pushforward_map α ψβ) _).trans (Functor.map_comp _ _ _).symm)

/-- Two transposes in a row, with the second pushed forward along the first morphism, form the
transpose of the composite -- the unit of the composite adjunction followed by the pushforward of
the composite. -/
public theorem transpose_comp_map_transpose (α : X ⟶ X') (β : X' ⟶ Y) (M : Y.Modules)
    (N' : X'.Modules) (N : X.Modules) (ψβ : (Scheme.Modules.pullback β).obj M ⟶ N')
    (ψα : (Scheme.Modules.pullback α).obj N' ⟶ N) :
    transpose β M ψβ ≫ (Scheme.Modules.pushforward β).map (transpose α N' ψα) =
      ((Scheme.Modules.pullbackPushforwardAdjunction β).unit.app M ≫
          (Scheme.Modules.pushforward β).map
            ((Scheme.Modules.pullbackPushforwardAdjunction α).unit.app
              ((Scheme.Modules.pullback β).obj M))) ≫
        (Scheme.Modules.pushforward (α ≫ β)).map
          ((Scheme.Modules.pullback α).map ψβ ≫ ψα) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ ((Functor.map_comp _ _ _).symm.trans
    (congrArg (fun z => (Scheme.Modules.pushforward β).map z)
      (comp_transpose α _ N' N ψβ ψα)))) ?_
  refine Eq.trans (whisker_eq _ (Functor.map_comp _ _ _)) ?_
  exact (Category.assoc _ _ _).symm

/-- **The transposition step.** A cocycle condition on three identifications of inverse images --
the one Tag 01MZ's third assertion asserts for the twist comparisons -- becomes a cocycle
condition on their adjoint transposes.

The two conditions are equivalent, since `CategoryTheory.Adjunction.homEquiv` is a bijection; this
is the direction that is used, and the one worth having, because the transposes are morphisms
between pushforwards and so can be computed on sections. -/
public theorem transpose_cocycle (α : X ⟶ X') (β : X' ⟶ Y) (γ : X ⟶ Y) (hγ : α ≫ β = γ)
    (M : Y.Modules) (N' : X'.Modules) (N : X.Modules)
    (ψβ : (Scheme.Modules.pullback β).obj M ⟶ N')
    (ψα : (Scheme.Modules.pullback α).obj N' ⟶ N)
    (ψγ : (Scheme.Modules.pullback γ).obj M ⟶ N)
    (hcoc : (Scheme.Modules.pullbackCongr hγ).inv.app M ≫
        (Scheme.Modules.pullbackComp α β).inv.app M ≫
        (Scheme.Modules.pullback α).map ψβ ≫ ψα = ψγ) :
    transpose β M ψβ ≫ (Scheme.Modules.pushforward β).map (transpose α N' ψα) ≫
        (Scheme.Modules.pushforwardCongr hγ).hom.app N =
      transpose γ M ψγ := by
  have hA : (Scheme.Modules.pullbackPushforwardAdjunction β).unit.app M ≫
      (Scheme.Modules.pushforward β).map
        ((Scheme.Modules.pullbackPushforwardAdjunction α).unit.app
          ((Scheme.Modules.pullback β).obj M)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (α ≫ β)).unit.app M ≫
        (Scheme.Modules.pushforward (α ≫ β)).map
          ((Scheme.Modules.pullbackComp α β).inv.app M) :=
    (Adjunction.comp_unit_app _ _ _).symm.trans
      (unit_comp_map_pullbackComp_inv α β M).symm
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (transpose_comp_map_transpose α β M N' N ψβ ψα) _) ?_
  refine Eq.trans (eq_whisker (eq_whisker hA _) _) ?_
  refine Eq.trans (eq_whisker (Category.assoc _ _ _) _) ?_
  refine Eq.trans (eq_whisker (whisker_eq _
    (Functor.map_comp (Scheme.Modules.pushforward (α ≫ β))
      ((Scheme.Modules.pullbackComp α β).inv.app M)
      ((Scheme.Modules.pullback α).map ψβ ≫ ψα)).symm) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ ((Scheme.Modules.pushforwardCongr hγ).hom.naturality
    ((Scheme.Modules.pullbackComp α β).inv.app M ≫
      (Scheme.Modules.pullback α).map ψβ ≫ ψα))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (unit_comp_map_pullbackCongr_inv hγ M).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Functor.map_comp (Scheme.Modules.pushforward γ)
    ((Scheme.Modules.pullbackCongr hγ).inv.app M)
    ((Scheme.Modules.pullbackComp α β).inv.app M ≫
      (Scheme.Modules.pullback α).map ψβ ≫ ψα)).symm) ?_
  exact whisker_eq _ (congrArg (fun z => (Scheme.Modules.pushforward γ).map z) hcoc)

/-! ### The pushed-forward comparison -/

/-- The identification of the pushforward of a pushforward with the pushforward along the
composite, followed by the congruence isomorphism along `hac : a ≫ c = cP`. These are the second
and third factors of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail`. -/
public def pushforwardCompCongr {P Q : Scheme.{u}} (a : P ⟶ Q) (c : Q ⟶ Z) {cP : P ⟶ Z}
    (hac : a ≫ c = cP) (K : P.Modules) :
    (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pushforward a).obj K) ⟶
      (Scheme.Modules.pushforward cP).obj K :=
  (Scheme.Modules.pushforwardComp a c).hom.app K ≫
    (Scheme.Modules.pushforwardCongr hac).hom.app K

/-- **The structural step.** Granted the cocycle condition on the transposes, the pushforwards of
the transposes compose.

This is the only statement below that is proved on sections, and it has to be: the coherence it
needs is that the pseudofunctoriality and congruence isomorphisms of the pushforward compose, and
on sections every one of those factors is the identity or a restriction along an equality of
opens. -/
public theorem comp_of_transpose_cocycle (cY : Y ⟶ Z) (cX' : X' ⟶ Z) (cX : X ⟶ Z)
    (α : X ⟶ X') (β : X' ⟶ Y) (γ : X ⟶ Y) (hγ : α ≫ β = γ)
    (hβ : β ≫ cY = cX') (hα : α ≫ cX' = cX) (hc : γ ≫ cY = cX)
    (M : Y.Modules) (N' : X'.Modules) (N : X.Modules)
    (Θβ : M ⟶ (Scheme.Modules.pushforward β).obj N')
    (Θα : N' ⟶ (Scheme.Modules.pushforward α).obj N)
    (Θγ : M ⟶ (Scheme.Modules.pushforward γ).obj N)
    (hcoc : Θβ ≫ (Scheme.Modules.pushforward β).map Θα ≫
        (Scheme.Modules.pushforwardComp α β).hom.app N ≫
        (Scheme.Modules.pushforwardCongr hγ).hom.app N = Θγ) :
    ((Scheme.Modules.pushforward cY).map Θβ ≫ pushforwardCompCongr β cY hβ N') ≫
        ((Scheme.Modules.pushforward cX').map Θα ≫ pushforwardCompCongr α cX' hα N) =
      (Scheme.Modules.pushforward cY).map Θγ ≫ pushforwardCompCongr γ cY hc N := by
  subst hγ hβ hα hcoc
  have hid : ∀ U : Z.Opens, ((Scheme.Modules.pushforwardCongr hc).hom.app N).app U = 𝟙 _ :=
    fun U => congrArg (·.app U) (pushforwardCongr_refl_hom_app _ hc N)
  simp only [pushforwardCompCongr, Functor.map_comp, Category.assoc]
  ext V x
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    presheaf_map_eqToHom_self, hid]
  simp

/-- **The pushed-forward comparison attached to an identification of an inverse image.** The unit
of the restriction--pushforward adjunction pushed forward along `c`, the two identifications of
`pushforwardCompCongr`, and the pushforward of the identification `ι` read through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

These are, factor for factor, the four factors of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested`, with every scheme, module and
identification a variable. -/
public def pushComparisonUnit {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a] (c : Q ⟶ Z)
    (M : Q.Modules) :
    (Scheme.Modules.pushforward c).obj M ⟶
      (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pushforward a).obj
        ((Scheme.Modules.restrictFunctor a).obj M)) :=
  (Scheme.Modules.pushforward c).map ((Scheme.Modules.restrictAdjunction a).unit.app M)

/-- The three remaining factors of `pushComparison`, all isomorphisms. Written with
`CategoryTheory.Iso.app`, `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` and
`CategoryTheory.Functor.mapIso` in exactly the spelling of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail`: the instance is then reached by
delta reduction alone, while the `hom`-of-a-composite spelling forces a conversion the kernel
cannot afford at the relative Proj. -/
public def pushComparisonTail {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a] (c : Q ⟶ Z)
    {cP : P ⟶ Z} (hac : a ≫ c = cP) (M : Q.Modules) (K : P.Modules)
    (ι : (Scheme.Modules.pullback a).obj M ≅ K) :
    (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pushforward a).obj
        ((Scheme.Modules.restrictFunctor a).obj M)) ≅
      (Scheme.Modules.pushforward cP).obj K :=
  (Scheme.Modules.pushforwardComp a c).app ((Scheme.Modules.restrictFunctor a).obj M) ≪≫
    (Scheme.Modules.pushforwardCongr hac).app ((Scheme.Modules.restrictFunctor a).obj M) ≪≫
      (Scheme.Modules.pushforward cP).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ι)

/-- **The pushed-forward comparison**, the unit factor followed by the three isomorphisms. -/
public def pushComparison {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a] (c : Q ⟶ Z)
    {cP : P ⟶ Z} (hac : a ≫ c = cP) (M : Q.Modules) (K : P.Modules)
    (ι : (Scheme.Modules.pullback a).obj M ≅ K) :
    (Scheme.Modules.pushforward c).obj M ⟶ (Scheme.Modules.pushforward cP).obj K :=
  pushComparisonUnit a c M ≫ (pushComparisonTail a c hac M K ι).hom

/-- The unit factor written out, by definition. Stated so that a consumer at a concrete instance
reaches it by instantiating a variable-level lemma, which costs the kernel nothing, instead of
asking for the same `rfl` where the delta step is expensive. -/
public theorem pushComparisonUnit_eq {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a]
    (c : Q ⟶ Z) (M : Q.Modules) :
    pushComparisonUnit a c M =
      (Scheme.Modules.pushforward c).map ((Scheme.Modules.restrictAdjunction a).unit.app M) :=
  rfl

/-- The tail written out, by definition. -/
public theorem pushComparisonTail_eq {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a]
    (c : Q ⟶ Z) {cP : P ⟶ Z} (hac : a ≫ c = cP) (M : Q.Modules) (K : P.Modules)
    (ι : (Scheme.Modules.pullback a).obj M ≅ K) :
    pushComparisonTail a c hac M K ι =
      (Scheme.Modules.pushforwardComp a c).app ((Scheme.Modules.restrictFunctor a).obj M) ≪≫
        (Scheme.Modules.pushforwardCongr hac).app ((Scheme.Modules.restrictFunctor a).obj M) ≪≫
          (Scheme.Modules.pushforward cP).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ι) :=
  rfl

/-- **The unit factor on a section is a restriction map.** The component of the unit of the
restriction adjunction over an open is the restriction from that open to the image of its
preimage, by `AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`. -/
public theorem pushComparisonUnit_app_apply {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a]
    (c : Q ⟶ Z) (M : Q.Modules) (V : Z.Opens)
    (s : ((Scheme.Modules.pushforward c).obj M).val.obj (op V)) :
    (pushComparisonUnit a c M).val.app (op V) s =
      M.val.map (homOfLE (a.image_preimage_le (c ⁻¹ᵁ V))).op s :=
  rfl

/-- **A morphism that acts on sections as that restriction map is the unit factor.** This is the
only form in which the unit factor can be identified at a concrete instance: identifying it with
the pushforward of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`'s unit -- which is its
definition -- exceeds the **kernel's** deterministic timeout at the relative Proj, because
inferring the type of that unit unfolds an adjunction built by a tactic block, while the action
on sections is a plain restriction map and costs seconds. The same is recorded in
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedUnit_app_apply`.

The containment of the two opens is a free argument: morphisms between opens are unique. -/
public theorem eq_pushComparisonUnit {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a]
    (c : Q ⟶ Z) (M : Q.Modules)
    (u : (Scheme.Modules.pushforward c).obj M ⟶
      (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pushforward a).obj
        ((Scheme.Modules.restrictFunctor a).obj M)))
    (hu : ∀ (V : Z.Opens) (i₀ : (a ''ᵁ (a ⁻¹ᵁ (c ⁻¹ᵁ V)) : Q.Opens) ⟶ c ⁻¹ᵁ V)
      (s : ((Scheme.Modules.pushforward c).obj M).val.obj (op V)),
      u.val.app (op V) s = M.val.map i₀.op s) :
    u = pushComparisonUnit a c M := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  exact (hu V (homOfLE (a.image_preimage_le (c ⁻¹ᵁ V))) s).trans
    (pushComparisonUnit_app_apply a c M V s).symm

/-- The comparison is its unit factor followed by its tail, by definition. Stated so that a
consumer at a concrete instance can reach it by instantiating a variable-level lemma instead of
asking the kernel for the same `rfl` there. -/
public theorem pushComparison_eq_unit_comp {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a]
    (c : Q ⟶ Z) {cP : P ⟶ Z} (hac : a ≫ c = cP) (M : Q.Modules) (K : P.Modules)
    (ι : (Scheme.Modules.pullback a).obj M ≅ K) :
    pushComparison a c hac M K ι =
      pushComparisonUnit a c M ≫ (pushComparisonTail a c hac M K ι).hom :=
  rfl

/-- The comparison with its three isomorphism factors read as morphisms. Proved by *applying*
`CategoryTheory.Iso.app_hom`, `CategoryTheory.Functor.mapIso_hom` and `trans₃_hom`, each of which
is a `rfl` lemma at the level of variables; asking for the same identity by `rfl` at a concrete
instance exhausts the kernel's budget. -/
public theorem pushComparison_eq_comp {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a]
    (c : Q ⟶ Z) {cP : P ⟶ Z} (hac : a ≫ c = cP) (M : Q.Modules) (K : P.Modules)
    (ι : (Scheme.Modules.pullback a).obj M ≅ K) :
    pushComparison a c hac M K ι =
      (Scheme.Modules.pushforward c).map ((Scheme.Modules.restrictAdjunction a).unit.app M) ≫
        (Scheme.Modules.pushforwardComp a c).hom.app
            ((Scheme.Modules.restrictFunctor a).obj M) ≫
          (Scheme.Modules.pushforwardCongr hac).hom.app
              ((Scheme.Modules.restrictFunctor a).obj M) ≫
            (Scheme.Modules.pushforward cP).map
              (((Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ι).hom) := by
  refine whisker_eq _ ?_
  refine Eq.trans (trans₃_hom _ _ _) ?_
  refine Eq.trans (eq_whisker (Iso.app_hom _ _) _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (eq_whisker (Iso.app_hom _ _) _) ?_
  exact whisker_eq _ (Functor.mapIso_hom _ _)

/-- **The pushed-forward comparison is the pushforward of the transpose of its identification**,
followed by `pushforwardCompCongr`. The trade of the unit of the restriction adjunction for the
unit of the pullback adjunction is
`Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`; the
rest is naturality of the two identifications in the module. -/
public theorem pushComparison_eq_transpose {P Q : Scheme.{u}} (a : P ⟶ Q) [IsOpenImmersion a]
    (c : Q ⟶ Z) {cP : P ⟶ Z} (hac : a ≫ c = cP) (M : Q.Modules) (K : P.Modules)
    (ι : (Scheme.Modules.pullback a).obj M ≅ K) :
    pushComparison a c hac M K ι =
      (Scheme.Modules.pushforward c).map (transpose a M ι.hom) ≫
        pushforwardCompCongr a c hac K := by
  refine Eq.trans (pushComparison_eq_comp a c hac M K ι) ?_
  have hunit : (Scheme.Modules.restrictAdjunction a).unit.app M ≫
      (Scheme.Modules.pushforward a).map
        (((Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ι).hom) =
      transpose a M ι.hom := by
    refine Eq.trans (whisker_eq _ (Functor.map_comp (Scheme.Modules.pushforward a)
      ((Scheme.Modules.restrictFunctorIsoPullback a).app M).hom ι.hom)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker
      (ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback a M) _
  generalize ((Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ι).hom = φ at hunit ⊢
  refine Eq.trans (whisker_eq _ (whisker_eq _
    ((Scheme.Modules.pushforwardCongr hac).hom.naturality φ).symm)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    ((Scheme.Modules.pushforwardComp a c).hom.naturality φ).symm _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker ((Functor.map_comp _ _ _).symm.trans
    (congrArg (fun z => (Scheme.Modules.pushforward c).map z) hunit)) _) ?_
  exact whisker_eq _ (Category.assoc _ _ _).symm

/-- **The pushed-forward comparisons compose as soon as their identifications do.** For three
open immersions `α`, `β`, `γ = α ≫ β` into a common scheme, compatible with the three morphisms
to `Z`, and identifications `ιβ`, `ια`, `ιγ` of the corresponding inverse images satisfying the
cocycle condition, the comparison attached to `γ` is the one attached to `β` followed by the one
attached to `α`.

This is the shape in which `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` --
and hence the twist `𝒪_{𝐏(E)}(1)` of Tag 01VM -- is reduced to Tag 01MZ's third assertion. -/
public theorem pushComparison_comp (cY : Y ⟶ Z) (cX' : X' ⟶ Z) (cX : X ⟶ Z)
    (α : X ⟶ X') (β : X' ⟶ Y) (γ : X ⟶ Y) [IsOpenImmersion α] [IsOpenImmersion β]
    [IsOpenImmersion γ] (hγ : α ≫ β = γ) (hβ : β ≫ cY = cX') (hα : α ≫ cX' = cX)
    (hc : γ ≫ cY = cX) (M : Y.Modules) (N' : X'.Modules) (N : X.Modules)
    (ιβ : (Scheme.Modules.pullback β).obj M ≅ N')
    (ια : (Scheme.Modules.pullback α).obj N' ≅ N)
    (ιγ : (Scheme.Modules.pullback γ).obj M ≅ N)
    (hcoc : (Scheme.Modules.pullbackCongr hγ).inv.app M ≫
        (Scheme.Modules.pullbackComp α β).inv.app M ≫
        (Scheme.Modules.pullback α).map ιβ.hom ≫ ια.hom = ιγ.hom) :
    pushComparison β cY hβ M N' ιβ ≫ pushComparison α cX' hα N' N ια =
      pushComparison γ cY hc M N ιγ := by
  have hbridge : transpose β M ιβ.hom ≫
      (Scheme.Modules.pushforward β).map (transpose α N' ια.hom) ≫
        (Scheme.Modules.pushforwardComp α β).hom.app N ≫
        (Scheme.Modules.pushforwardCongr hγ).hom.app N = transpose γ M ιγ.hom :=
    Eq.trans (whisker_eq _ (whisker_eq _
      ((eq_whisker (pushforwardComp_hom_app_eq_id α β N) _).trans (Category.id_comp _))))
      (transpose_cocycle α β γ hγ M N' N ιβ.hom ια.hom ιγ.hom hcoc)
  refine Eq.trans (comp_congr (pushComparison_eq_transpose β cY hβ M N' ιβ)
    (pushComparison_eq_transpose α cX' hα N' N ια)) ?_
  refine Eq.trans (comp_of_transpose_cocycle cY cX' cX α β γ hγ hβ hα hc M N' N
    (transpose β M ιβ.hom) (transpose α N' ια.hom) (transpose γ M ιγ.hom) hbridge) ?_
  exact (pushComparison_eq_transpose γ cY hc M N ιγ).symm

/-- **The composition law in factored form**, with the unit factor and the tail of each
comparison supplied as variables.

This is the form a consumer at a concrete instance can use. Its three hypotheses on each
comparison are exactly the three identifications the kernel will check there: the unit factor
through its action on sections (`eq_pushComparisonUnit`), the tail as an equation of isomorphisms
(a single delta), and the comparison as the composite of the two (one more delta). Supplying the
comparison itself as a single identification does not work; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/ChartTransNonNested/TwistCocycle.lean`. -/
public theorem pushComparison_comp_of (cY : Y ⟶ Z) (cX' : X' ⟶ Z) (cX : X ⟶ Z)
    (α : X ⟶ X') (β : X' ⟶ Y) (γ : X ⟶ Y) [IsOpenImmersion α] [IsOpenImmersion β]
    [IsOpenImmersion γ] (hγ : α ≫ β = γ) (hβ : β ≫ cY = cX') (hα : α ≫ cX' = cX)
    (hc : γ ≫ cY = cX) (M : Y.Modules) (N' : X'.Modules) (N : X.Modules)
    (ιβ : (Scheme.Modules.pullback β).obj M ≅ N')
    (ια : (Scheme.Modules.pullback α).obj N' ≅ N)
    (ιγ : (Scheme.Modules.pullback γ).obj M ≅ N)
    (uβ : (Scheme.Modules.pushforward cY).obj M ⟶
      (Scheme.Modules.pushforward cY).obj ((Scheme.Modules.pushforward β).obj
        ((Scheme.Modules.restrictFunctor β).obj M)))
    (uα : (Scheme.Modules.pushforward cX').obj N' ⟶
      (Scheme.Modules.pushforward cX').obj ((Scheme.Modules.pushforward α).obj
        ((Scheme.Modules.restrictFunctor α).obj N')))
    (uγ : (Scheme.Modules.pushforward cY).obj M ⟶
      (Scheme.Modules.pushforward cY).obj ((Scheme.Modules.pushforward γ).obj
        ((Scheme.Modules.restrictFunctor γ).obj M)))
    (Tβ : (Scheme.Modules.pushforward cY).obj ((Scheme.Modules.pushforward β).obj
        ((Scheme.Modules.restrictFunctor β).obj M)) ≅
      (Scheme.Modules.pushforward cX').obj N')
    (Tα : (Scheme.Modules.pushforward cX').obj ((Scheme.Modules.pushforward α).obj
        ((Scheme.Modules.restrictFunctor α).obj N')) ≅
      (Scheme.Modules.pushforward cX).obj N)
    (Tγ : (Scheme.Modules.pushforward cY).obj ((Scheme.Modules.pushforward γ).obj
        ((Scheme.Modules.restrictFunctor γ).obj M)) ≅
      (Scheme.Modules.pushforward cX).obj N)
    (huβ : ∀ (V : Z.Opens) (i₀ : (β ''ᵁ (β ⁻¹ᵁ (cY ⁻¹ᵁ V)) : Y.Opens) ⟶ cY ⁻¹ᵁ V)
      (s : ((Scheme.Modules.pushforward cY).obj M).val.obj (op V)),
      uβ.val.app (op V) s = M.val.map i₀.op s)
    (huα : ∀ (V : Z.Opens) (i₀ : (α ''ᵁ (α ⁻¹ᵁ (cX' ⁻¹ᵁ V)) : X'.Opens) ⟶ cX' ⁻¹ᵁ V)
      (s : ((Scheme.Modules.pushforward cX').obj N').val.obj (op V)),
      uα.val.app (op V) s = N'.val.map i₀.op s)
    (huγ : ∀ (V : Z.Opens) (i₀ : (γ ''ᵁ (γ ⁻¹ᵁ (cY ⁻¹ᵁ V)) : Y.Opens) ⟶ cY ⁻¹ᵁ V)
      (s : ((Scheme.Modules.pushforward cY).obj M).val.obj (op V)),
      uγ.val.app (op V) s = M.val.map i₀.op s)
    (hTβ : Tβ = pushComparisonTail β cY hβ M N' ιβ)
    (hTα : Tα = pushComparisonTail α cX' hα N' N ια)
    (hTγ : Tγ = pushComparisonTail γ cY hc M N ιγ)
    (hcoc : (Scheme.Modules.pullbackCongr hγ).inv.app M ≫
        (Scheme.Modules.pullbackComp α β).inv.app M ≫
        (Scheme.Modules.pullback α).map ιβ.hom ≫ ια.hom = ιγ.hom) :
    (uβ ≫ Tβ.hom) ≫ (uα ≫ Tα.hom) = uγ ≫ Tγ.hom := by
  subst hTβ hTα hTγ
  obtain rfl := eq_pushComparisonUnit β cY M uβ huβ
  obtain rfl := eq_pushComparisonUnit α cX' N' uα huα
  obtain rfl := eq_pushComparisonUnit γ cY M uγ huγ
  exact pushComparison_comp cY cX' cX α β γ hγ hβ hα hc M N' N ιβ ια ιγ hcoc

end Stacks.AlgebraicGeometry.PushforwardCocycle

end
