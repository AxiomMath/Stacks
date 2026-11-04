module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMorphismHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering

/-!
# Full faithfulness of pullback along a refinement by one-member étale coverings

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `𝒱 = {V j ⟶ X}` be a
family of algebraic spaces over `X`, and refine it by replacing each member `V j` by a space
`W j` mapping to it by `u j : W j ⟶ V j`, where `{u j}` is a *one-member surjective étale
covering* of `V j` and `u j` is relatively representable.  This is the situation of Stacks 0419,
`AlgebraicGeometry.Space.exists_fpqc_scheme_refinement`: there `W j` is a scheme atlas of `V j`,
so `u j` is surjective étale, and its source is represented, which gives relative
representability.

Pullback of descent data along that refinement, Stacks 04W4, is then **fully faithful**.  This
file proves it, and so makes the refinement transport of effectivity of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/RefinementCanonical.lean`
unconditional in that situation: it is step (3) of the proof of Stacks 04W8, the reduction of
effectivity along an arbitrary fpqc covering of algebraic spaces to effectivity along a covering
by schemes.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.refineFamily` is the refined family `{W j ⟶ X}`
  and `…refineFamilyHom` the refinement, a morphism of families of Stacks 00VT over the identity
  of `X` whose index map is the identity.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.fullyFaithful_pullbackFunctor_refineFamilyHom`
  is **the full faithfulness of pullback along such a refinement**, and
  `…fullyFaithful_pullbackFunctor_refineFamilyHom_of_represented` is the form Stacks 0419
  delivers, in which relative representability is discharged by representability of the sources.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.faithful_pullbackFunctor`: **pullback along a
  refinement is faithful** as soon as the members of the refining family cover, in the étale
  topology, the members of the refined family they map to, and every member of the refined
  family is hit.  This is the sheaf condition on the small étale site,
  `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.full_pullbackFunctor_of_exists_app`: **pullback
  along such a refinement is full** once the *components* of a morphism of the pulled-back data
  descend.  The content is that the descended components then automatically commute with the
  pairwise isomorphisms of Stacks 04W3 of the refined family.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_app_refineFamilyHom`: the components do
  descend, by descent of morphisms of modules along a one-member étale covering,
  `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_pullbackDatum_iff_refineFamilyHom`
  and `…isEffective_of_forall_isEffective_refineFamilyHom`: **the refinement transport of
  effectivity, with no hypothesis at all.**  These are
  `…isEffective_pullbackDatum_iff` and `…isEffective_of_forall_isEffective` of
  `RefinementCanonical.lean` with their one input supplied.

## The dictionary this file builds

Descent of morphisms along the one-member covering `{u j}`
(`…exists_modulePullback_map_eq_of_dominated`) asks for a compatibility of the given morphism of
inverse images with the canonical comparison of Stacks 04W5 **at every pair of morphisms into
`W j` with equal composites to `V j`**, while a morphism of the pulled-back descent data carries
the pairwise condition of Stacks 04W3 **over the pairwise fibre products of the refining family
over `X`**.  The two are reconciled here:

* `…canonicalComparison_naturality_of_pullbackDatumHom` is one half: such a pair of morphisms
  has equal composites to `X` as well, hence factors through `W j ×_X W j`, and the pairwise
  isomorphism of the *given* datum read at two morphisms which agree is the identity — that is
  `…transitionOn_self`, a consequence of the cocycle condition — so the pulled-back pairwise
  isomorphism read there is exactly the canonical comparison
  (`…transitionOn_pullbackDatum_self`).
* `…naturality_of_transitionOn_of_isEtaleCovering` is the other half: the pairwise condition for
  the refined family may be checked after pullback along a one-member étale covering of
  `V i ×_X V j`, and `…exists_isEtaleCovering_familyPairMap` produces such a covering by a space
  mapping to `W i ×_X W j`, as the composite of the two base changes of `{u i}` and `{u j}`.

## Implementation notes

The component modules of the pulled-back datum are written out as inverse images, never as the
projection `(pullbackDatum Φ D).F`, in every statement that also mentions a comparison of
inverse images: the two differ by one delta-iota step, and underneath `≫` that step is a kernel
deterministic timeout at these types (the obstruction recorded in the implementation notes of
`RefinementCanonical.lean`).  That is the reason for
`…transitionOn_naturality_of_pairwise`, which is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_naturality` for *plain* pairwise data
— the component modules and the pairwise isomorphisms arbitrary, the compatibility a hypothesis
— and so can be instantiated at the written-out inverse images.  Neither quasi-coherence nor the
cocycle condition is used in it, so it is strictly more general than the descent-datum form, of
which it is not a copy: the descent-datum form is its instance at `F := D.F`, `φ := D.transition`
and `app := a.app`.

For the same reason the two legs and the two leg conditions of the pairwise isomorphism of the
refined family are left to be *inferred* where the translation is consumed, in
`…full_pullbackFunctor_of_exists_app`, rather than written out: a leg condition written out and
matched against the one the translation produces is a second kernel deterministic timeout, while
with the leg conditions inferred the same proof is checked at once.

The index map of the refinement is the identity by construction, which is what Stacks 0419
delivers and what lets the descended components be indexed by the index type of the refined
family with no transport.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W4](https://stacks.math.columbia.edu/tag/04W4)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
* [Stacks Project, Tag 00VT](https://stacks.math.columbia.edu/tag/00VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- An idempotent isomorphism is the identity.

It is stated at a variable isomorphism of a variable category on purpose: a consumer whose
isomorphism is a pairwise isomorphism of a descent datum instantiates it with no reduction. -/
theorem eq_refl_of_trans_self {A : C} {e : A ≅ A} (h : e ≪≫ e = e) : e = Iso.refl A := by
  have h' : e.hom ≫ e.hom = e.hom := congrArg Iso.hom h
  have h'' := congrArg (fun t : A ⟶ A => t ≫ e.inv) h'
  exact Iso.ext (by simpa using h'')

end CategoryTheory.Iso

universe u v v'

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Pairwise

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- **The pairwise isomorphism of a descent datum at one index, read along two morphisms which
agree, is the identity.**  This is the cocycle condition of Stacks 04W3 at the triple
`i, i, i`: it makes that isomorphism idempotent. -/
theorem transitionOn_self (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (D : DescentDatum B S hS Y f) {T : AlgebraicSpaces B S hS} (i : I)
    (v : T ⟶ pair B S hS Y f i i) (w : T ⟶ Y i)
    (hi : v ≫ pairFst B S hS Y f i i = w) (hj : v ≫ pairSnd B S hS Y f i i = w) :
    transitionOn B S hS Y f D.F D.transition i i v w w hi hj = Iso.refl _ :=
  Iso.eq_refl_of_trans_self (D.cocycle i i i T w w w v v v hi hj hi hj hi hj)

/-- The pairwise isomorphism of a descent datum at one index, read along two morphisms which are
*equal*, is the transport along that equality. -/
theorem transitionOn_eq_eqToIso (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (D : DescentDatum B S hS Y f) {T : AlgebraicSpaces B S hS} (i : I)
    (v : T ⟶ pair B S hS Y f i i) (a b : T ⟶ Y i)
    (hi : v ≫ pairFst B S hS Y f i i = a) (hj : v ≫ pairSnd B S hS Y f i i = b)
    (hab : a = b) :
    transitionOn B S hS Y f D.F D.transition i i v a b hi hj =
      eqToIso (congrArg (fun q : T ⟶ Y i =>
        (modulePullback B S hS q).obj (D.F i)) hab) := by
  subst hab
  exact transitionOn_self B S hS Y f D i v a hi hj

/-- **A family of morphisms of modules commuting with two families of pairwise isomorphisms
commutes with their readings on any test space.**

This is `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_naturality` for *plain*
pairwise data rather than for a morphism of descent data: the component modules and the pairwise
isomorphisms are arbitrary and the compatibility is a hypothesis.  Neither quasi-coherence nor
the cocycle condition is used, so the descent-datum form is the instance `F := D.F`,
`φ := D.transition`, `app := a.app`, `hnat := a.naturality` of this one.

The general form is what a consumer holding the pulled-back data of Stacks 04W4 needs: there the
component modules are inverse images, and they must be *written out* rather than named by the
projection `(pullbackDatum Φ D).F`, because a composite mentioning both that projection and a
comparison of inverse images asks the kernel for a delta-iota step underneath `≫`, which at
these types does not finish. -/
theorem transitionOn_naturality_of_pairwise (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F G : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    (χ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (G i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (G j))
    (app : ∀ i, F i ⟶ G i)
    (hnat : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).map (app i) ≫
        (χ i j).hom =
      (φ i j).hom ≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).map (app j))
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    (modulePullback B S hS vi).map (app i) ≫
        (transitionOn B S hS Y f G χ i j v vi vj hi hj).hom =
      (transitionOn B S hS Y f F φ i j v vi vj hi hj).hom ≫
        (modulePullback B S hS vj).map (app j) := by
  subst hi
  subst hj
  simp only [transitionOn, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, pullbackComparison_naturality, Category.assoc]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, hnat, Functor.map_comp, Category.assoc,
    pullbackComparison_inv_naturality]

/-- **The pairwise condition of a morphism of descent data, from its reading on a dominating
test space.**  A family of morphisms of the component modules commutes with the pairwise
isomorphisms of Stacks 04W3 at the pair `i, j` as soon as it does so after pullback along a
morphism `c` into `Y i ×_X Y j` whose one-member family is an étale covering of it.

This is where descent of *morphisms* enters the pairwise condition: the equation to be checked
lives on `Y i ×_X Y j`, and a morphism of modules there is determined by its inverse image along
an étale covering, by the sheaf condition on the small étale site. -/
theorem naturality_of_transitionOn_of_isEtaleCovering (Y : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Y i ⟶ X) {D E : DescentDatum B S hS Y f} (app : ∀ t, D.F t ⟶ E.F t) (i j : I)
    {Z : AlgebraicSpaces B S hS} (c : Z ⟶ pair B S hS Y f i j) (ci : Z ⟶ Y i) (cj : Z ⟶ Y j)
    (hi : c ≫ pairFst B S hS Y f i j = ci) (hj : c ≫ pairSnd B S hS Y f i j = cj)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => Z.1) (fun _ => c.hom))
    (hnat : (modulePullback B S hS ci).map (app i) ≫
          (transitionOn B S hS Y f E.F E.transition i j c ci cj hi hj).hom =
        (transitionOn B S hS Y f D.F D.transition i j c ci cj hi hj).hom ≫
          (modulePullback B S hS cj).map (app j)) :
    (modulePullback B S hS (pairFst B S hS Y f i j)).map (app i) ≫ (E.transition i j).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Y f i j)).map (app j) := by
  subst hi
  subst hj
  have : (modulePullback B S hS c).Faithful :=
    ⟨fun {_ _} φ φ' h => modulePullback_map_injective_of_isEtaleCovering B S hS
      (fun _ : Unit => Z) (fun _ => c) hcov φ φ' fun _ => h⟩
  refine (modulePullback B S hS c).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp]
  simp only [transitionOn, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc] at hnat
  rw [← Category.assoc, pullbackComparison_naturality, Category.assoc,
    ← pullbackComparison_inv_naturality] at hnat
  simpa only [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right_assoc] using hnat

end Pairwise

section Family

variable {U V : AlgebraicSpaces B S hS} {𝒰 : PreZeroHypercover.{v} U}
  {𝒱 : PreZeroHypercover.{v'} V} {g : U ⟶ V}

/-- **At one index, and at two morphisms with equal composites to the corresponding member of
the refined family, the pairwise isomorphism of the pulled-back datum read on a test space is
the canonical comparison of Stacks 04W5.**

The pairwise isomorphism of the given datum disappears: by
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_self` it is read there at two
morphisms into one member which agree, so it is a transport, and the comparisons on either side
are those of the canonical comparison. -/
theorem transitionOn_pullbackDatum_self (Φ : 𝒰.HomOver 𝒱 g)
    (D : DescentDatum B S hS 𝒱.X 𝒱.f) {T : AlgebraicSpaces B S hS} (i : 𝒰.I₀)
    (v : T ⟶ pair B S hS 𝒰.X 𝒰.f i i) (a b : T ⟶ 𝒰.X i)
    (hi : v ≫ pairFst B S hS 𝒰.X 𝒰.f i i = a)
    (hj : v ≫ pairSnd B S hS 𝒰.X 𝒰.f i i = b)
    (hab : a ≫ Φ.h₀ i = b ≫ Φ.h₀ i) :
    transitionOn B S hS 𝒰.X 𝒰.f (pullbackDatum B S hS Φ D).F
        (pullbackDatum B S hS Φ D).transition i i v a b hi hj =
      canonicalComparison a b (Φ.h₀ i) (Φ.h₀ i) hab (D.F (Φ.s₀ i)) := by
  have h := transitionOn_pullbackTransition B S hS Φ D i i v a b hi hj
  rw [transitionOn_eq_eqToIso B S hS 𝒱.X 𝒱.f D (Φ.s₀ i) _ _ _ _ _ hab] at h
  rw [canonicalComparison]
  exact h

end Family

section Refinement

variable {X : AlgebraicSpaces B S hS} {𝒰 : PreZeroHypercover.{v} X}
  {𝒱 : PreZeroHypercover.{v'} X}

/-- **A pairwise fibre product of the refined family is covered, in the étale topology, by a
space mapping to the corresponding pairwise fibre product of the refining family.**

Each member of the refining family covers the member it maps to, so the base change of
`{Φ.h₀ i}` along the first projection of `V (s₀ i) ×_X V (s₀ j)` covers that fibre product, and
the base change of `{Φ.h₀ j}` along the second leg of the result covers it in turn; the
composite is the covering asked for, and it factors through `U i ×_X U j` because its two legs
do. -/
theorem exists_isEtaleCovering_familyPairMap (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    (hcov : ∀ t, IsEtaleCovering B S hS (fun _ : Unit => (𝒰.X t).1) (fun _ => (Φ.h₀ t).hom))
    (i j : 𝒰.I₀) :
    ∃ (Z : AlgebraicSpaces B S hS) (w : Z ⟶ pair B S hS 𝒰.X 𝒰.f i j),
      IsEtaleCovering B S hS (fun _ : Unit => Z.1)
        (fun _ => (w ≫ familyPairMap B S hS Φ Φ i j).hom) := by
  have hleg₁ := refinementLeg B S hS Φ i
  have hleg₂ := refinementLeg B S hS Φ j
  let Z₁ := AlgebraicSpaces.fiberProduct B S hS
    (pairFst B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)) (Φ.h₀ i)
  let a₁ : Z₁ ⟶ pair B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j) := ObjectProperty.homMk
    (pullback.fst (pairFst B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).hom (Φ.h₀ i).hom)
  let b₁ : Z₁ ⟶ 𝒰.X i := ObjectProperty.homMk
    (pullback.snd (pairFst B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).hom (Φ.h₀ i).hom)
  have sq₁ : IsPullback a₁ b₁ (pairFst B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)) (Φ.h₀ i) :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS _ _
  let Z₂ := AlgebraicSpaces.fiberProduct B S hS
    (a₁ ≫ pairSnd B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)) (Φ.h₀ j)
  let a₂ : Z₂ ⟶ Z₁ := ObjectProperty.homMk
    (pullback.fst (a₁ ≫ pairSnd B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).hom (Φ.h₀ j).hom)
  let b₂ : Z₂ ⟶ 𝒰.X j := ObjectProperty.homMk
    (pullback.snd (a₁ ≫ pairSnd B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).hom (Φ.h₀ j).hom)
  have sq₂ : IsPullback a₂ b₂ (a₁ ≫ pairSnd B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)) (Φ.h₀ j) :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS _ _
  have hpair := AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒰.f i) (𝒰.f j)
  have hw : (a₂ ≫ b₁) ≫ 𝒰.f i = b₂ ≫ 𝒰.f j := by
    simp only [Category.assoc, ← hleg₁, ← hleg₂, ← reassoc_of% sq₁.w,
      pair_condition B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j), reassoc_of% sq₂.w]
  refine ⟨Z₂, hpair.lift (a₂ ≫ b₁) b₂ hw, ?_⟩
  have hc : hpair.lift (a₂ ≫ b₁) b₂ hw ≫ familyPairMap B S hS Φ Φ i j = a₂ ≫ a₁ := by
    refine (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒱.f (Φ.s₀ i))
      (𝒱.f (Φ.s₀ j))).hom_ext ?_ ?_ <;>
      simp only [Category.assoc, familyPairMap_fst, familyPairMap_snd,
        reassoc_of% hpair.lift_fst, reassoc_of% hpair.lift_snd, sq₁.w, sq₂.w]
  have cov₁ : IsEtaleCovering B S hS (fun _ : Unit => Z₁.1) (fun _ => a₁.hom) :=
    isEtaleCovering_pullback B S hS (pairFst B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).hom
      (pair B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).property
      (fun _ : Unit => (𝒰.X i).1) (fun _ => (Φ.h₀ i).hom) (hcov i)
  have cov₂ : IsEtaleCovering B S hS (fun _ : Unit => Z₂.1) (fun _ => a₂.hom) :=
    isEtaleCovering_pullback B S hS
      (a₁ ≫ pairSnd B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).hom Z₁.property
      (fun _ : Unit => (𝒰.X j).1) (fun _ => (Φ.h₀ j).hom) (hcov j)
  rw [hc]
  refine ⟨(pair B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Φ.s₀ j)).property, fun _ => Z₂.property,
    fun _ => isEtale_comp B S hS (cov₂.etale ()) (cov₁.etale ()), ?_⟩
  have h₁ : Set.range (pointsMap B S hS Z₁.1 a₁.hom) = Set.univ := by
    simpa only [Set.iUnion_const] using cov₁.jointly_surjective
  have h₂ : Set.range (pointsMap B S hS Z₂.1 a₂.hom) = Set.univ := by
    simpa only [Set.iUnion_const] using cov₂.jointly_surjective
  rw [Set.iUnion_const]
  show Set.range (pointsMap B S hS Z₂.1 (a₂.hom ≫ a₁.hom)) = Set.univ
  rw [pointsMap_comp, Set.range_comp, h₂, Set.image_univ, h₁]

/-- **The dictionary between the pairwise condition over `X` and the canonical comparison over a
member of the refined family.**  A morphism of the pulled-back descent data is, at the pair
`(i, i)`, compatible with the canonical comparison of Stacks 04W5 at *every* pair of morphisms
into `U i` with equal composites to `V (s₀ i)` — which is the compatibility that descent of
morphisms of modules along `Φ.h₀ i` consumes.

Two such morphisms have equal composites to `X` as well, so they factor through `U i ×_X U i`,
and `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_pullbackDatum_self` identifies
the pulled-back pairwise isomorphism read there with the canonical comparison. -/
theorem canonicalComparison_naturality_of_pullbackDatumHom (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    {D E : DescentDatum B S hS 𝒱.X 𝒱.f}
    (ψ : pullbackDatum B S hS Φ D ⟶ pullbackDatum B S hS Φ E) (i : 𝒰.I₀)
    (P : AlgebraicSpaces B S hS) (a b : P ⟶ 𝒰.X i) (hab : a ≫ Φ.h₀ i = b ≫ Φ.h₀ i) :
    (modulePullback B S hS a).map (ψ.app i) ≫
        (canonicalComparison a b (Φ.h₀ i) (Φ.h₀ i) hab (E.F (Φ.s₀ i))).hom =
      (canonicalComparison a b (Φ.h₀ i) (Φ.h₀ i) hab (D.F (Φ.s₀ i))).hom ≫
        (modulePullback B S hS b).map (ψ.app i) := by
  have hab' : a ≫ 𝒰.f i = b ≫ 𝒰.f i := by
    rw [← refinementLeg B S hS Φ i, ← Category.assoc, ← Category.assoc, hab]
  have hp := AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒰.f i) (𝒰.f i)
  have key := transitionOn_naturality B S hS 𝒰.X 𝒰.f ψ i i (hp.lift a b hab') a b
    (hp.lift_fst a b hab') (hp.lift_snd a b hab')
  rwa [transitionOn_pullbackDatum_self B S hS Φ E i _ a b _ _ hab,
    transitionOn_pullbackDatum_self B S hS Φ D i _ a b _ _ hab] at key

/-- **Pullback along a refinement is faithful.**  A morphism of descent data for the refined
family is determined by its components, and each component is determined by its inverse image
along the member of the refining family above it, by the sheaf condition on the small étale site
of that member. -/
theorem faithful_pullbackFunctor (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    (hcov : ∀ t, IsEtaleCovering B S hS (fun _ : Unit => (𝒰.X t).1) (fun _ => (Φ.h₀ t).hom))
    (hsurj : ∀ j, ∃ i, Φ.s₀ i = j) :
    (pullbackFunctor B S hS Φ).Faithful where
  map_injective {D E} a b h := by
    refine DescentDatum.Hom.ext fun j => ?_
    obtain ⟨i, rfl⟩ := hsurj j
    refine modulePullback_map_injective_of_isEtaleCovering B S hS (fun _ : Unit => 𝒰.X i)
      (fun _ => Φ.h₀ i) (hcov i) (a.app (Φ.s₀ i)) (b.app (Φ.s₀ i)) fun _ => ?_
    have h' : pullbackHom B S hS Φ a = pullbackHom B S hS Φ b := h
    have hi := congrArg
      (fun c : pullbackDatum B S hS Φ D ⟶ pullbackDatum B S hS Φ E => c.app i) h'
    rw [pullbackHom_app, pullbackHom_app] at hi
    exact hi

/-- **Pullback along a refinement is full**, granted that the *components* of a morphism of the
pulled-back data descend.

The content is the pairwise condition of the descended family: it is checked over a pairwise
fibre product `V i ×_X V j` of the refined family after pullback along the covering of
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isEtaleCovering_familyPairMap`, where it is
the pairwise condition of the given morphism read on a test space, through the coherence
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_pullbackTransition` of Stacks 04W4.

The two legs and the two leg conditions of the pairwise isomorphism are left to be inferred in
the closing step: written out and matched, they are a kernel deterministic timeout. -/
theorem full_pullbackFunctor_of_exists_app (Φ : 𝒰.HomOver 𝒱 (𝟙 X))
    (hcov : ∀ t, IsEtaleCovering B S hS (fun _ : Unit => (𝒰.X t).1) (fun _ => (Φ.h₀ t).hom))
    (hsurj : ∀ j, ∃ i, Φ.s₀ i = j)
    (happ : ∀ (D E : DescentDatum B S hS 𝒱.X 𝒱.f)
      (ψ : pullbackDatum B S hS Φ D ⟶ pullbackDatum B S hS Φ E),
      ∃ app : ∀ t, D.F t ⟶ E.F t,
        ∀ t, (modulePullback B S hS (Φ.h₀ t)).map (app (Φ.s₀ t)) = ψ.app t) :
    (pullbackFunctor B S hS Φ).Full where
  map_surjective {D E} ψ := by
    obtain ⟨app, hψ⟩ := happ D E ψ
    have hnatU : ∀ i j : 𝒰.I₀,
        (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).map
            ((modulePullback B S hS (Φ.h₀ i)).map (app (Φ.s₀ i))) ≫
          (pullbackTransition B S hS Φ E i j).hom =
        (pullbackTransition B S hS Φ D i j).hom ≫
          (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).map
            ((modulePullback B S hS (Φ.h₀ j)).map (app (Φ.s₀ j))) := by
      intro i j
      rw [hψ i, hψ j]
      exact ψ.naturality i j
    refine ⟨⟨app, ?_⟩, DescentDatum.Hom.ext fun t => hψ t⟩
    intro i j
    obtain ⟨i', rfl⟩ := hsurj i
    obtain ⟨j', rfl⟩ := hsurj j
    obtain ⟨Z, w, hcovZ⟩ := exists_isEtaleCovering_familyPairMap B S hS Φ hcov i' j'
    have key := transitionOn_naturality_of_pairwise B S hS 𝒰.X 𝒰.f
      (fun t => (modulePullback B S hS (Φ.h₀ t)).obj (D.F (Φ.s₀ t)))
      (fun t => (modulePullback B S hS (Φ.h₀ t)).obj (E.F (Φ.s₀ t)))
      (pullbackTransition B S hS Φ D) (pullbackTransition B S hS Φ E)
      (fun t => (modulePullback B S hS (Φ.h₀ t)).map (app (Φ.s₀ t))) hnatU i' j' w
      (w ≫ pairFst B S hS 𝒰.X 𝒰.f i' j') (w ≫ pairSnd B S hS 𝒰.X 𝒰.f i' j') rfl rfl
    rw [transitionOn_pullbackTransition B S hS Φ D i' j' w _ _ rfl rfl,
      transitionOn_pullbackTransition B S hS Φ E i' j' w _ _ rfl rfl] at key
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at key
    rw [← Category.assoc, pullbackComparison_inv_naturality, Category.assoc,
      ← pullbackComparison_naturality] at key
    exact naturality_of_transitionOn_of_isEtaleCovering B S hS 𝒱.X 𝒱.f app (Φ.s₀ i') (Φ.s₀ j')
      (w ≫ familyPairMap B S hS Φ Φ i' j') _ _ _ _ hcovZ
      ((Iso.cancel_iso_hom_right_assoc _ _ _ _ _).mp ((Iso.cancel_iso_inv_left _ _ _).mp key))

end Refinement

section SchemeRefinement

variable {X : AlgebraicSpaces B S hS} (𝒱 : PreZeroHypercover.{v} X)
  (W : 𝒱.I₀ → AlgebraicSpaces B S hS) (u : ∀ i, W i ⟶ 𝒱.X i)

/-- The refinement of a family of algebraic spaces over `X` by a family of morphisms into its
members: the family `{W i ⟶ V i ⟶ X}`, with the index type of the given family. -/
def refineFamily : PreZeroHypercover.{v} X where
  I₀ := 𝒱.I₀
  X := W
  f i := u i ≫ 𝒱.f i

/-- The members of the refined family are the given spaces. -/
@[simp]
theorem refineFamily_X : (refineFamily B S hS 𝒱 W u).X = W :=
  rfl

/-- The structure morphisms of the refined family are the composites. -/
@[simp]
theorem refineFamily_f (i : 𝒱.I₀) : (refineFamily B S hS 𝒱 W u).f i = u i ≫ 𝒱.f i :=
  rfl

/-- **The refinement, as a morphism of families of morphisms with fixed target of Stacks 00VT
over the identity of `X`.**  Its index map is the identity. -/
def refineFamilyHom : (refineFamily B S hS 𝒱 W u).HomOver 𝒱 (𝟙 X) where
  s₀ i := i
  h₀ i := u i
  w₀ _ := (Category.comp_id _).symm

/-- The index map of the refinement is the identity. -/
@[simp]
theorem refineFamilyHom_s₀ (i : 𝒱.I₀) : (refineFamilyHom B S hS 𝒱 W u).s₀ i = i :=
  rfl

/-- The morphisms of the refinement are the given ones. -/
@[simp]
theorem refineFamilyHom_h₀ (i : 𝒱.I₀) : (refineFamilyHom B S hS 𝒱 W u).h₀ i = u i :=
  rfl

/-- **The components of a morphism of the pulled-back descent data descend.**  Each component is
a morphism of the two inverse images along `u i`, compatible with the canonical comparison of
Stacks 04W5 at every pair of morphisms into `W i` with equal composites to `V i` by
`…canonicalComparison_naturality_of_pullbackDatumHom`, hence the inverse image of a morphism of
the component modules of the given data by descent of morphisms along a one-member surjective
étale covering,
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated`. -/
theorem exists_app_refineFamilyHom
    (hrep : ∀ i, yoneda.relativelyRepresentable (u i).hom)
    (hcov : ∀ i, IsEtaleCovering B S hS (fun _ : Unit => (W i).1) (fun _ => (u i).hom))
    (D E : DescentDatum B S hS 𝒱.X 𝒱.f)
    (ψ : pullbackDatum B S hS (refineFamilyHom B S hS 𝒱 W u) D ⟶
      pullbackDatum B S hS (refineFamilyHom B S hS 𝒱 W u) E) :
    ∃ app : ∀ t, D.F t ⟶ E.F t, ∀ t,
      (modulePullback B S hS ((refineFamilyHom B S hS 𝒱 W u).h₀ t)).map
        (app ((refineFamilyHom B S hS 𝒱 W u).s₀ t)) = ψ.app t := by
  choose app hψ using fun t => exists_modulePullback_map_eq_of_dominated B S hS
    ((refineFamilyHom B S hS 𝒱 W u).h₀ t) ((hcov t).etale ()) (hrep t) (hcov t) (ψ.app t)
    (canonicalComparison_naturality_of_pullbackDatumHom B S hS
      (refineFamilyHom B S hS 𝒱 W u) ψ t)
  exact ⟨app, hψ⟩

/-- **Pullback of quasi-coherent descent data along a refinement by one-member surjective étale
coverings is fully faithful.**

This is the input that the refinement transport of effectivity of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/RefinementCanonical.lean` asks for,
and the only hypotheses are on the refinement: each `u i` is a one-member surjective étale
covering of `V i` and is relatively representable.  Both hold for the refinement by schemes of
Stacks 0419; see `…fullyFaithful_pullbackFunctor_refineFamilyHom_of_represented`. -/
def fullyFaithful_pullbackFunctor_refineFamilyHom
    (hrep : ∀ i, yoneda.relativelyRepresentable (u i).hom)
    (hcov : ∀ i, IsEtaleCovering B S hS (fun _ : Unit => (W i).1) (fun _ => (u i).hom)) :
    (pullbackFunctor B S hS (refineFamilyHom B S hS 𝒱 W u)).FullyFaithful :=
  have := faithful_pullbackFunctor B S hS (refineFamilyHom B S hS 𝒱 W u) hcov
    fun j => ⟨j, rfl⟩
  have := full_pullbackFunctor_of_exists_app B S hS (refineFamilyHom B S hS 𝒱 W u) hcov
    (fun j => ⟨j, rfl⟩) (exists_app_refineFamilyHom B S hS 𝒱 W u hrep hcov)
  .ofFullyFaithful _

/-- **Pullback along a refinement whose members are represented is fully faithful.**  This is the
shape Stacks 0419 delivers: the refining spaces are the algebraic spaces represented by objects
of the site, so relative representability of the refining morphisms is the diagonal criterion,
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace`, and the only hypothesis
left is that each refining morphism is a surjective étale covering. -/
def fullyFaithful_pullbackFunctor_refineFamilyHom_of_represented
    (T : 𝒱.I₀ → BigFppfOver B S hS)
    (e : ∀ i, schemeSpace (T i) ⟶ 𝒱.X i)
    (hcov : ∀ i, IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj (T i))
      (fun _ => (e i).hom)) :
    (pullbackFunctor B S hS (refineFamilyHom B S hS 𝒱
      (fun i => schemeSpace (T i)) e)).FullyFaithful :=
  fullyFaithful_pullbackFunctor_refineFamilyHom B S hS 𝒱 _ e
    (fun i => relativelyRepresentable_of_isAlgebraicSpace B S hS (𝒱.X i).property (e i).hom) hcov

/-- **Effectivity descends from a refinement by one-member surjective étale coverings, with no
hypothesis.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_pullbackDatum_iff` with its one
input — full faithfulness of pullback along the refinement — supplied. -/
theorem isEffective_pullbackDatum_iff_refineFamilyHom
    (hrep : ∀ i, yoneda.relativelyRepresentable (u i).hom)
    (hcov : ∀ i, IsEtaleCovering B S hS (fun _ : Unit => (W i).1) (fun _ => (u i).hom))
    {D : DescentDatum B S hS 𝒱.X 𝒱.f} :
    IsEffective B S hS (refineFamily B S hS 𝒱 W u).X (refineFamily B S hS 𝒱 W u).f
        (pullbackDatum B S hS (refineFamilyHom B S hS 𝒱 W u) D) ↔
      IsEffective B S hS 𝒱.X 𝒱.f D :=
  isEffective_pullbackDatum_iff B S hS (refineFamilyHom B S hS 𝒱 W u)
    (fullyFaithful_pullbackFunctor_refineFamilyHom B S hS 𝒱 W u hrep hcov)

/-- **Effectivity for a family follows from effectivity for a refinement of it by one-member
surjective étale coverings, with no hypothesis.**  This is the form the reduction of Stacks 04W8
to a covering by schemes consumes: an arbitrary family is refined by one whose members are
schemes (Stacks 0419, `AlgebraicGeometry.Space.exists_fpqc_scheme_refinement`), effectivity is
proved for the refinement, and this carries it back. -/
theorem isEffective_of_forall_isEffective_refineFamilyHom
    (hrep : ∀ i, yoneda.relativelyRepresentable (u i).hom)
    (hcov : ∀ i, IsEtaleCovering B S hS (fun _ : Unit => (W i).1) (fun _ => (u i).hom))
    (h : ∀ E : DescentDatum B S hS (refineFamily B S hS 𝒱 W u).X (refineFamily B S hS 𝒱 W u).f,
      IsEffective B S hS (refineFamily B S hS 𝒱 W u).X (refineFamily B S hS 𝒱 W u).f E)
    (D : DescentDatum B S hS 𝒱.X 𝒱.f) : IsEffective B S hS 𝒱.X 𝒱.f D :=
  isEffective_of_forall_isEffective B S hS (refineFamilyHom B S hS 𝒱 W u)
    (fullyFaithful_pullbackFunctor_refineFamilyHom B S hS 𝒱 W u hrep hcov) h D

end SchemeRefinement

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
