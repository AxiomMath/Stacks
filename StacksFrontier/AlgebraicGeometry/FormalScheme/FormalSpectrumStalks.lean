module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings as the stalks of a formal spectrum

The stalks of the structure sheaf `𝒪_{Spf A} = lim 𝒪_λ` of the formal spectrum of a
pre-admissible topological ring are local rings, so the formal spectrum is an object of the
category `LTRS` of locally topologically ringed spaces. For each ideal of definition `I` the
closed immersion `Spec (A/I) → Spec A` identifies `Spec (A/I)` homeomorphically with the space of
open primes, so the stalks of each term `𝒪_λ` of the inverse system are the local rings of the
`Spec (A/I_λ)`; because the comparison maps of the system come from morphisms of schemes, they
are local homomorphisms on stalks, and a section of the limit is therefore invertible as soon as
one of its components is.

## Main definitions

* `AlgebraicGeometry.spfComponentSpaceOn` and `AlgebraicGeometry.spfComponentRingedSpaceOn`: the
  term `𝒪_λ` of the inverse system viewed as a presheafed, respectively ringed, space on `Spf A`.
* `AlgebraicGeometry.spfComponentHomOn` and `AlgebraicGeometry.spfTransitionHomOn`: the
  identification of `Spec (A/I)` with `(Spf A, 𝒪_I)` as presheafed spaces of rings, and its
  composite with the morphism of schemes inducing a transition map of the inverse system.
* `AlgebraicGeometry.spfProjectionOn`: the projection of `𝒪_{Spf A}` onto the term `𝒪_λ` of the
  inverse system defining it.
* `AlgebraicGeometry.spfLTRS`: the formal spectrum of a pre-admissible topological ring as an
  object of `LTRS`.

## Main results

* `AlgebraicGeometry.surjective_spfOfQuotientOn` and
  `AlgebraicGeometry.isInducing_spfOfQuotientOn`: for an ideal of definition `I` the map
  `Spec (A/I) → Spf A` is a homeomorphism.
* `AlgebraicGeometry.isLocalRing_stalk_spfComponentOn`: the stalks of each `𝒪_λ` are local rings.
* `AlgebraicGeometry.isLocalHom_stalkFunctor_map_spfTransitionOn`: the comparison map
  `𝒪_λ → 𝒪_μ` of the inverse system is a local homomorphism on stalks.
* `AlgebraicGeometry.isLocalHom_spfProjectionOn_stalk`: a germ of `𝒪_{Spf A}` is invertible as soon
  as its image in one `𝒪_λ` is.
* `AlgebraicGeometry.isLocalRing_stalk_spfPresheaf`: the stalks of `𝒪_{Spf A}` are local rings.

## Implementation notes

Invertibility of a section of the limit is componentwise, by
`TopCommRingCat.isUnit_of_isLimit`: the inverses of the components are automatically compatible,
since a ring homomorphism carries the inverse of a unit to the inverse of its image. The
components of a germ are therefore invertible on a common neighbourhood, namely the basic open
set of the component in which invertibility is assumed: at each of its points the germ of any
other component is invertible, because any two ideals of definition are both contained in a
third one and the comparison maps reflect units; invertibility of a section of a sheaf of rings
at every point of an open set gives invertibility over that open set.

Only pre-admissibility is used, as for the sheaf condition: completeness of `A` enters the
source's remaining deferred verification, that `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}}`.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace TopCommRingCat

variable {J : Type u} [SmallCategory J]

/-- A section of a diagram of topological rings is a unit as soon as each of its components is:
the inverses of the components are compatible, a ring homomorphism carrying the inverse of a
unit to the inverse of its image. -/
theorem isUnit_of_isLimit {F : J ⥤ TopCommRingCat.{u}} {c : Cone F} (hc : IsLimit c)
    (x : c.pt.α) (h : ∀ j, IsUnit ((c.π.app j).1 x)) : IsUnit x := by
  classical
  let e : c.pt ≅ TopCommRingCat.of (limitSubring F) :=
    hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have hcomp : ∀ j, ((limitCone F).π.app j).1 (e.hom.1 x) = (c.π.app j).1 x := fun j =>
    congrArg (fun g : c.pt ⟶ F.obj j => g.1 x)
      (hc.conePointUniqueUpToIso_hom_comp (limitConeIsLimit F) j)
  set y : limitSubring F := e.hom.1 x
  have hyj : ∀ j, IsUnit (y.1 j) := fun j => by
    have := h j
    rwa [← hcomp j] at this
  set z : (j : J) → (F.obj j).α := fun j => (((hyj j).unit⁻¹ : (F.obj j).αˣ) : (F.obj j).α)
  have hmul : ∀ j, y.1 j * z j = 1 := fun j => (hyj j).mul_val_inv
  have hzmem : z ∈ limitSubring F := by
    intro j k f
    have hyk : (F.map f).1 (y.1 j) = y.1 k := y.2 f
    have h1 : y.1 k * (F.map f).1 (z j) = 1 := by
      rw [← hyk, ← map_mul, hmul j, map_one]
    exact (left_inv_eq_right_inv ((mul_comm _ _).trans (hmul k)) h1).symm
  have hinv : e.inv.1 y = x :=
    congrArg (fun g : c.pt ⟶ c.pt => g.1 x) e.hom_inv_id
  exact hinv ▸ RingHom.isUnit_map e.inv.1
    (IsUnit.of_mul_eq_one (⟨z, hzmem⟩ : limitSubring F) (Subtype.ext (funext hmul)))

end TopCommRingCat

namespace AlgebraicGeometry

open TopologicalRing

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-! ### `Spec (A/I)` is the space of open primes -/

/-- Every open prime of `A` comes from a prime of `A ⧸ I`, for `I` an ideal of definition: it
contains `I`, so it lies in the image of `Spec (A/I) → Spec A`. -/
@[ega "I 10.1.1" "more general"]
theorem surjective_spfOfQuotientOn (I : SpfIndex A P) :
    Function.Surjective (spfOfQuotientOn A I) := by
  intro x
  have hrange : x.1 ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I.1)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
    exact SetLike.coe_subset_coe.2
      ((mem_openPrimes_iff_le_of_isWeakIdealOfDefinition A I.isWeakIdealOfDefinition x.1).1 x.2)
  obtain ⟨q, hq⟩ := hrange
  exact ⟨q, Subtype.ext hq⟩

/-- Every open prime of `A` comes from a prime of `A ⧸ I`, for `I` an ideal of definition: it
contains `I`, so it lies in the image of `Spec (A/I) → Spec A`.

The ideals-of-definition case of `surjective_spfOfQuotientOn`. -/
@[ega "I 10.1.1" "partial"]
theorem surjective_spfOfQuotient (I : IdealsOfDefinition A) :
    Function.Surjective (spfOfQuotient A I) :=
  surjective_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The identification of `Spec (A/I)` with the space of open primes is inducing, being the
corestriction of the closed immersion `Spec (A/I) → Spec A`. -/
theorem isInducing_spfOfQuotientOn (I : SpfIndex A P) :
    Topology.IsInducing (spfOfQuotientOn A I) :=
  ((PrimeSpectrum.isEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).isInducing).codRestrict _

/-- The identification of `Spec (A/I)` with the space of open primes is inducing, being the
corestriction of the closed immersion `Spec (A/I) → Spec A`.

The ideals-of-definition case of `isInducing_spfOfQuotientOn`. -/
theorem isInducing_spfOfQuotient (I : IdealsOfDefinition A) :
    Topology.IsInducing (spfOfQuotient A I) :=
  isInducing_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- Comparing the stalks of `𝒪_λ` with those of the structure sheaf of `Spec (A/I_λ)` is an
isomorphism, the identification of `Spec (A/I_λ)` with the space of open primes being
inducing. -/
instance isIso_stalkPushforward_spfOfQuotientOn (I : SpfIndex A P)
    (q : Spec (spfQuotientOn A I)) :
    IsIso ((Spec (spfQuotientOn A I)).presheaf.stalkPushforward CommRingCat.{u}
      (spfOfQuotientOn A I) q) :=
  TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
    (isInducing_spfOfQuotientOn A I) _ q

/-- Comparing the stalks of `𝒪_λ` with those of the structure sheaf of `Spec (A/I_λ)` is an
isomorphism, the identification of `Spec (A/I_λ)` with the space of open primes being
inducing.

The ideals-of-definition case of `isIso_stalkPushforward_spfOfQuotientOn`. -/
instance isIso_stalkPushforward_spfOfQuotient (I : IdealsOfDefinition A)
    (q : Spec (spfQuotient A I)) :
    IsIso ((Spec (spfQuotient A I)).presheaf.stalkPushforward CommRingCat.{u}
      (spfOfQuotient A I) q) :=
  isIso_stalkPushforward_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I) (q := q)

/-- The stalks of the structure sheaf of `Spec (A/I)`, viewed on `Spf A`, are local rings: they
are the local rings of `Spec (A/I)`. -/
theorem isLocalRing_stalk_spfComponentOn (I : SpfIndex A P) (x : spfSpace A) :
    IsLocalRing ((spfComponentOn A I).stalk x) := by
  obtain ⟨q, rfl⟩ := surjective_spfOfQuotientOn A I x
  exact (asIso ((Spec (spfQuotientOn A I)).presheaf.stalkPushforward CommRingCat.{u}
    (spfOfQuotientOn A I) q)).commRingCatIsoToRingEquiv.symm.isLocalRing

/-- The stalks of the structure sheaf of `Spec (A/I)`, viewed on `Spf A`, are local rings: they
are the local rings of `Spec (A/I)`.

The ideals-of-definition case of `isLocalRing_stalk_spfComponentOn`. -/
theorem isLocalRing_stalk_spfComponent (I : IdealsOfDefinition A) (x : spfSpace A) :
    IsLocalRing ((spfComponent A I).stalk x) :=
  isLocalRing_stalk_spfComponentOn (A := A) (P := IsIdealOfDefinition) (I := I) (x := x)

/-! ### The comparison maps of the inverse system are local on stalks -/

/-- The term `𝒪_λ` of the inverse system defining `𝒪_{Spf A}`, as a presheafed space of rings on
the space of open primes. -/
noncomputable def spfComponentSpaceOn (I : SpfIndex A P) :
    PresheafedSpace CommRingCat.{u} where
  carrier := spfSpace A
  presheaf := spfComponentOn A I

/-- The term `𝒪_λ` of the inverse system defining `𝒪_{Spf A}`, as a presheafed space of rings on
the space of open primes.

The ideals-of-definition case of `spfComponentSpaceOn`. -/
@[reducible] noncomputable def spfComponentSpace (I : IdealsOfDefinition A) :
    PresheafedSpace CommRingCat.{u} :=
  spfComponentSpaceOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The identification of `Spec (A/I)` with `(Spf A, 𝒪_λ)` as presheafed spaces of rings: the
sections agree on the nose, `𝒪_λ` being the pushforward of the structure sheaf of
`Spec (A/I)`. -/
noncomputable def spfComponentHomOn (I : SpfIndex A P) :
    (Spec (spfQuotientOn A I)).toPresheafedSpace ⟶ spfComponentSpaceOn A I where
  base := spfOfQuotientOn A I
  c := 𝟙 _

/-- The identification of `Spec (A/I)` with `(Spf A, 𝒪_λ)` as presheafed spaces of rings: the
sections agree on the nose, `𝒪_λ` being the pushforward of the structure sheaf of
`Spec (A/I)`.

The ideals-of-definition case of `spfComponentHomOn`. -/
@[reducible] noncomputable def spfComponentHom (I : IdealsOfDefinition A) :
    (Spec (spfQuotient A I)).toPresheafedSpace ⟶ spfComponentSpace A I :=
  spfComponentHomOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- For ideals of definition `I ⊆ J` the morphism `Spec (A/J) → (Spf A, 𝒪_I)` of presheafed
spaces of rings whose comparison map is the transition map of the inverse system. -/
noncomputable def spfTransitionHomOn {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    (Spec (spfQuotientOn A J)).toPresheafedSpace ⟶ spfComponentSpaceOn A I :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).toLRSHom.toHom ≫ spfComponentHomOn A I

/-- For ideals of definition `I ⊆ J` the morphism `Spec (A/J) → (Spf A, 𝒪_I)` of presheafed
spaces of rings whose comparison map is the transition map of the inverse system.

The ideals-of-definition case of `spfTransitionHomOn`. -/
@[reducible] noncomputable def spfTransitionHom {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    (Spec (spfQuotient A J)).toPresheafedSpace ⟶ spfComponentSpace A I :=
  spfTransitionHomOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

/-- The stalk map of `AlgebraicGeometry.spfTransitionHomOn` is the stalk map of the transition map
of the inverse system, followed by the comparison of the stalks of `𝒪_J` with those of
`Spec (A/J)`. -/
theorem stalkMap_spfTransitionHomOn {I J : SpfIndex A P} (h : I.1 ≤ J.1)
    (q : Spec (spfQuotientOn A J)) :
    (spfTransitionHomOn A h).stalkMap q =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (spfOfQuotientOn A J q)).map
          (spfTransitionOn A h) ≫
        (Spec (spfQuotientOn A J)).presheaf.stalkPushforward CommRingCat.{u}
          (spfOfQuotientOn A J) q := rfl

/-- The stalk map of `AlgebraicGeometry.spfTransitionHom` is the stalk map of the transition map
of the inverse system, followed by the comparison of the stalks of `𝒪_J` with those of
`Spec (A/J)`.

The ideals-of-definition case of `stalkMap_spfTransitionHomOn`. -/
theorem stalkMap_spfTransitionHom {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1)
    (q : Spec (spfQuotient A J)) :
    (spfTransitionHom A h).stalkMap q =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (spfOfQuotient A J q)).map
          (spfTransition A h) ≫
        (Spec (spfQuotient A J)).presheaf.stalkPushforward CommRingCat.{u}
          (spfOfQuotient A J) q :=
  stalkMap_spfTransitionHomOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)
    (q := q)

/-- The stalk map of the identification of `Spec (A/I)` with `(Spf A, 𝒪_I)` is a local
homomorphism, being an isomorphism. -/
instance isLocalHom_stalkMap_spfComponentHomOn (I : SpfIndex A P)
    (q : Spec (spfQuotientOn A I)) :
    IsLocalHom ((spfComponentHomOn A I).stalkMap q).hom := by
  have h1 : IsLocalHom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (spfOfQuotientOn A I q)).map
      (𝟙 (spfComponentOn A I))).hom := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have h2 : IsLocalHom ((Spec (spfQuotientOn A I)).presheaf.stalkPushforward CommRingCat.{u}
      (spfOfQuotientOn A I) q).hom := inferInstance
  have h3 : IsLocalHom
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (spfOfQuotientOn A I q)).map
          (𝟙 (spfComponentOn A I)) ≫
        (Spec (spfQuotientOn A I)).presheaf.stalkPushforward CommRingCat.{u}
          (spfOfQuotientOn A I) q).hom) :=
    @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h2 h1
  exact h3

/-- The stalk map of the identification of `Spec (A/I)` with `(Spf A, 𝒪_I)` is a local
homomorphism, being an isomorphism.

The ideals-of-definition case of `isLocalHom_stalkMap_spfComponentHomOn`. -/
instance isLocalHom_stalkMap_spfComponentHom (I : IdealsOfDefinition A)
    (q : Spec (spfQuotient A I)) :
    IsLocalHom ((spfComponentHom A I).stalkMap q).hom :=
  isLocalHom_stalkMap_spfComponentHomOn (A := A) (P := IsIdealOfDefinition) (I := I) (q := q)

/-- The transition map `𝒪_I → 𝒪_J` of the inverse system defining `𝒪_{Spf A}` is a local
homomorphism on stalks: it is induced by the morphism of schemes
`Spec (A/J) → Spec (A/I)`. -/
theorem isLocalHom_stalkFunctor_map_spfTransitionOn {I J : SpfIndex A P} (h : I.1 ≤ J.1)
    (x : spfSpace A) :
    IsLocalHom
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (spfTransitionOn A h)).hom := by
  obtain ⟨q, rfl⟩ := surjective_spfOfQuotientOn A J x
  have hcomp : IsLocalHom ((spfTransitionHomOn A h).stalkMap q).hom := by
    rw [spfTransitionHomOn, PresheafedSpace.stalkMap.comp]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _
      (LocallyRingedSpace.isLocalHomStalkMap
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).toLRSHom q)
      (isLocalHom_stalkMap_spfComponentHomOn A I _)
  rw [stalkMap_spfTransitionHomOn] at hcomp
  exact @isLocalHom_of_comp _ _ _ _ _ _
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (spfOfQuotientOn A J q)).map
      (spfTransitionOn A h)).hom
    ((Spec (spfQuotientOn A J)).presheaf.stalkPushforward CommRingCat.{u}
      (spfOfQuotientOn A J) q).hom hcomp

/-- The transition map `𝒪_I → 𝒪_J` of the inverse system defining `𝒪_{Spf A}` is a local
homomorphism on stalks: it is induced by the morphism of schemes
`Spec (A/J) → Spec (A/I)`.

The ideals-of-definition case of `isLocalHom_stalkFunctor_map_spfTransitionOn`. -/
theorem isLocalHom_stalkFunctor_map_spfTransition {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1)
    (x : spfSpace A) :
    IsLocalHom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (spfTransition A h)).hom :=
  isLocalHom_stalkFunctor_map_spfTransitionOn (A := A) (P := IsIdealOfDefinition) (I := I)
    (J := J) (h := h) (x := x)

/-! ### The stalks of the structure sheaf of a formal spectrum -/

/-- The term `𝒪_λ` of the inverse system defining `𝒪_{Spf A}`, as a ringed space on the space of
open primes. -/
noncomputable def spfComponentRingedSpaceOn (I : SpfIndex A P) : RingedSpace.{u} where
  carrier := spfSpace A
  presheaf := spfComponentOn A I
  IsSheaf := isSheaf_spfComponentOn A I

/-- The term `𝒪_λ` of the inverse system defining `𝒪_{Spf A}`, as a ringed space on the space of
open primes.

The ideals-of-definition case of `spfComponentRingedSpaceOn`. -/
@[reducible] noncomputable def spfComponentRingedSpace (I : IdealsOfDefinition A) :
    RingedSpace.{u} :=
  spfComponentRingedSpaceOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The projection of `𝒪_{Spf A} = lim 𝒪_λ` onto the term `𝒪_λ` of the inverse system defining
it. -/
noncomputable def spfProjectionOn (I : SpfIndex A P) :
    spfPresheafOn A P ⟶ pseudoDiscrete (spfComponentOn A I) :=
  limit.π (spfDiagramOn A P ⋙ pseudoDiscreteFunctor) I

/-- The projection of `𝒪_{Spf A} = lim 𝒪_λ` onto the term `𝒪_λ` of the inverse system defining
it.

The ideals-of-definition case of `spfProjectionOn`. -/
@[reducible] noncomputable def spfProjection (I : IdealsOfDefinition A) :
    spfPresheaf A ⟶ pseudoDiscrete (spfComponent A I) :=
  spfProjectionOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The projections of `𝒪_{Spf A}` are compatible with the transition maps of the inverse
system. -/
theorem spfProjectionOn_app_spfTransitionOn_app {I J : SpfIndex A P} (h : I.1 ≤ J.1)
    (U : (Opens (spfSpace A))ᵒᵖ) (s : ((spfPresheafOn A P).obj U).α) :
    (spfTransitionOn A h).app U (((spfProjectionOn A I).app U).1 s) =
      ((spfProjectionOn A J).app U).1 s :=
  congrArg (fun k : spfPresheafOn A P ⟶ pseudoDiscrete (spfComponentOn A J) => (k.app U).1 s)
    (limit.w (spfDiagramOn A P ⋙ pseudoDiscreteFunctor) (homOfLE h))

/-- The projections of `𝒪_{Spf A}` are compatible with the transition maps of the inverse
system.

The ideals-of-definition case of `spfProjectionOn_app_spfTransitionOn_app`. -/
theorem spfProjection_app_spfTransition_app {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1)
    (U : (Opens (spfSpace A))ᵒᵖ) (s : ((spfPresheaf A).obj U).α) :
    (spfTransition A h).app U (((spfProjection A I).app U).1 s) =
      ((spfProjection A J).app U).1 s :=
  spfProjectionOn_app_spfTransitionOn_app (A := A) (P := IsIdealOfDefinition) (I := I) (J := J)
    (h := h) (U := U) (s := s)

/-- The transition maps of the inverse system carry the germ of one component of a section of
`𝒪_{Spf A}` to the germ of the other. -/
theorem stalkFunctor_map_spfTransitionOn_germ {I J : SpfIndex A P} (h : I.1 ≤ J.1)
    {U : Opens (spfSpace A)} (s : ((spfPresheafOn A P).obj (op U)).α) {y : spfSpace A}
    (hy : y ∈ U) :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map (spfTransitionOn A h)
        ((spfComponentOn A I).germ U y hy (((spfProjectionOn A I).app (op U)).1 s)) =
      (spfComponentOn A J).germ U y hy (((spfProjectionOn A J).app (op U)).1 s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy (spfTransitionOn A h) _).trans
    (congrArg ((spfComponentOn A J).germ U y hy)
      (spfProjectionOn_app_spfTransitionOn_app A h (op U) s))

/-- If the germ of one component of a section of `𝒪_{Spf A}` is invertible, so is the germ of
every other component. -/
theorem isUnit_germ_spfProjectionOn_of_isUnit {μ : SpfIndex A P} (lam : SpfIndex A P)
    {U : Opens (spfSpace A)} (s : ((spfPresheafOn A P).obj (op U)).α) {y : spfSpace A}
    (hy : y ∈ U)
    (h : IsUnit ((spfComponentOn A μ).germ U y hy (((spfProjectionOn A μ).app (op U)).1 s))) :
    IsUnit ((spfComponentOn A lam).germ U y hy (((spfProjectionOn A lam).app (op U)).1 s)) := by
  have hnl : (spfIndexMeet A lam μ).1 ≤ lam.1 := inf_le_left
  have hnm : (spfIndexMeet A lam μ).1 ≤ μ.1 := inf_le_right
  rw [← stalkFunctor_map_spfTransitionOn_germ A hnm] at h
  rw [← stalkFunctor_map_spfTransitionOn_germ A hnl]
  exact RingHom.isUnit_map _
    ((isLocalHom_stalkFunctor_map_spfTransitionOn A hnm y).map_nonunit _ h)

/-- A germ of `𝒪_{Spf A}` is invertible as soon as its image in one term `𝒪_λ` of the inverse
system is: the component in which it is invertible is invertible on a whole neighbourhood, and
there every other component is invertible too, because any two ideals of definition contain a
third one and the transition maps reflect units. -/
theorem isLocalHom_spfProjectionOn_stalk (μ : SpfIndex A P) (x : spfSpace A) :
    IsLocalHom
      ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} x).map (spfProjectionOn A μ)).1 := by
  have : PreservesFilteredColimits (forget TopCommRingCat.{u}) :=
    (HasForget₂.forget_comp (C := TopCommRingCat.{u}) (D := CommRingCat.{u})) ▸
      (inferInstance : PreservesFilteredColimits
        (forget₂ TopCommRingCat.{u} CommRingCat.{u} ⋙ forget CommRingCat.{u}))
  refine ⟨fun a ha => ?_⟩
  obtain ⟨U, hxU, s, rfl⟩ := (spfPresheafOn A P).exists_germ_eq a
  set sμ : (spfComponentOn A μ).obj (op U) := ((spfProjectionOn A μ).app (op U)).1 s
  have haP : IsUnit ((pseudoDiscrete (spfComponentOn A μ)).germ U x hxU sμ) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply (C := TopCommRingCat.{u}) U x hxU
      (spfProjectionOn A μ) s ▸ ha
  have haC : IsUnit ((spfComponentOn A μ).germ U x hxU sμ) := by
    have h1 : IsUnit (((forget₂ TopCommRingCat.{u} CommRingCat.{u}).map
          ((pseudoDiscrete (spfComponentOn A μ)).germ U x hxU) ≫
        (pseudoDiscreteStalkIso (spfComponentOn A μ) x).hom).hom sμ) :=
      RingHom.isUnit_map (pseudoDiscreteStalkIso (spfComponentOn A μ) x).hom.hom haP
    rw [germ_pseudoDiscreteStalkIso_hom] at h1
    exact h1
  obtain ⟨V, hVU, hxV, hVmem⟩ : ∃ (V : Opens (spfSpace A)) (hVU : V ≤ U), x ∈ V ∧
      ∀ (y : spfSpace A) (hy : y ∈ V),
        IsUnit ((spfComponentOn A μ).germ U y (hVU hy) sμ) :=
    ⟨(spfComponentRingedSpaceOn A μ).basicOpen sμ,
      RingedSpace.basicOpen_le (spfComponentRingedSpaceOn A μ) sμ,
      (RingedSpace.mem_basicOpen (spfComponentRingedSpaceOn A μ) sμ x hxU).2 haC,
      fun y hy => (RingedSpace.mem_basicOpen (spfComponentRingedSpaceOn A μ) sμ y _).1 hy⟩
  set res : ((spfPresheafOn A P).obj (op V)).α :=
    ((spfPresheafOn A P).map (homOfLE hVU).op).1 s
  have hcomponent : ∀ lam : SpfIndex A P,
      IsUnit (((spfProjectionOn A lam).app (op V)).1 res) := by
    intro lam
    have hslres : ((spfProjectionOn A lam).app (op V)).1 res =
        (spfComponentOn A lam).map (homOfLE hVU).op (((spfProjectionOn A lam).app (op U)).1 s) :=
      congrArg (fun k : (spfPresheafOn A P).obj (op U) ⟶
          (pseudoDiscrete (spfComponentOn A lam)).obj (op V) => k.1 s)
        ((spfProjectionOn A lam).naturality (homOfLE hVU).op)
    rw [hslres]
    refine RingedSpace.isUnit_of_isUnit_germ (spfComponentRingedSpaceOn A lam) V _ fun y hy => ?_
    exact cast (congrArg IsUnit ((spfComponentOn A lam).germ_res_apply (homOfLE hVU) y hy
      (((spfProjectionOn A lam).app (op U)).1 s))).symm
      (isUnit_germ_spfProjectionOn_of_isUnit A lam s (hVU hy) (hVmem y hy))
  have hunitV : IsUnit res :=
    TopCommRingCat.isUnit_of_isLimit
      (isLimitOfPreserves ((evaluation (Opens (spfSpace A))ᵒᵖ TopCommRingCat.{u}).obj (op V))
        (limit.isLimit (spfDiagramOn A P ⋙ pseudoDiscreteFunctor))) res hcomponent
  have hgerm : (spfPresheafOn A P).germ U x hxU s = (spfPresheafOn A P).germ V x hxV res :=
    ((spfPresheafOn A P).germ_res_apply (homOfLE hVU) x hxV s).symm
  rw [hgerm]
  exact RingHom.isUnit_map ((spfPresheafOn A P).germ V x hxV).1 hunitV

/-- A germ of `𝒪_{Spf A}` is invertible as soon as its image in one term `𝒪_λ` of the inverse
system is: the component in which it is invertible is invertible on a whole neighbourhood, and
there every other component is invertible too, because any two ideals of definition contain a
third one and the transition maps reflect units.

The ideals-of-definition case of `isLocalHom_spfProjectionOn_stalk`. -/
theorem isLocalHom_spfProjection_stalk (μ : IdealsOfDefinition A) (x : spfSpace A) :
    IsLocalHom ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} x).map (spfProjection A μ)).1 :=
  isLocalHom_spfProjectionOn_stalk (A := A) (P := IsIdealOfDefinition) (μ := μ) (x := x)

/-- **Deferred by the source** ("At this point one should check several things"): the stalks of
the structure presheaf `lim 𝒪_λ` of the formal spectrum taken along a weak ideal system with at
least one member are local rings. -/
theorem isLocalRing_stalk_spfPresheafOn (μ : SpfIndex A P) (x : spfSpace A) :
    IsLocalRing ((spfPresheafOn A P).stalk x).α := by
  have : IsLocalRing ((spfComponentOn A μ).stalk x) := isLocalRing_stalk_spfComponentOn A μ x
  have : IsLocalRing ((pseudoDiscrete (spfComponentOn A μ)).stalk x).α :=
    isLocalRing_stalk_pseudoDiscrete (spfComponentOn A μ) x
  let θ : ((spfPresheafOn A P).stalk x).α →+* ((pseudoDiscrete (spfComponentOn A μ)).stalk x).α :=
    ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} x).map (spfProjectionOn A μ)).1
  have : IsLocalHom θ := isLocalHom_spfProjectionOn_stalk A μ x
  exact θ.domain_isLocalRing

/-- **Deferred by the source** ("At this point one should check several things"): the stalks of
the structure sheaf `𝒪_{Spf A} = lim 𝒪_λ` of the formal spectrum of a pre-admissible topological
ring are local rings. -/
theorem isLocalRing_stalk_spfPresheaf (hA : IsPreAdmissible A) (x : spfSpace A) :
    IsLocalRing ((spfPresheaf A).stalk x).α :=
  isLocalRing_stalk_spfPresheafOn A ⟨hA.choose, hA.choose_spec⟩ x

variable (P) in
/-- The formal spectrum taken along a weak ideal system, as an object of the category `LTRS` of
locally topologically ringed spaces. The chosen member `I₀` of the system is what makes the
space a locally topologically ringed one at all: it witnesses that the system is nonempty, which
is both the sheaf condition `AlgebraicGeometry.isSheaf_spfPresheafOn` and the locality of the
stalks `AlgebraicGeometry.isLocalRing_stalk_spfPresheafOn`. Any two choices give the same object,
the data of the formal spectrum depending on `I₀` only through proofs. -/
noncomputable def spfLTRSOn (I₀ : SpfIndex A P) : LTRS.{u} where
  toSheafedSpace := spfSheafedSpaceOn A P (isWeaklyPreAdmissible_of_spfIndex A I₀)
  isLocalRing := isLocalRing_stalk_spfPresheafOn A I₀

/-- The presheafed space of topological rings underlying the formal spectrum taken along a weak
ideal system, as an object of `LTRS`, is that formal spectrum. -/
@[simp]
theorem spfLTRSOn_toPresheafedSpace (I₀ : SpfIndex A P) :
    (spfLTRSOn A P I₀).toPresheafedSpace = SpfOn A P := rfl

/-- The formal spectrum of a pre-admissible topological ring as an object of the category `LTRS`
of locally topologically ringed spaces. -/
@[reducible, ega "I 10.1.2"] noncomputable def spfLTRS (hA : IsPreAdmissible A) : LTRS.{u} :=
  spfLTRSOn A IsIdealOfDefinition (preAdmissibleSpfIndex A hA)

/-- The presheafed space of topological rings underlying the formal spectrum as an object of
`LTRS` is `Spf A`. -/
@[simp]
theorem spfLTRS_toPresheafedSpace (hA : IsPreAdmissible A) :
    (spfLTRS A hA).toPresheafedSpace = Spf A := rfl

/-- **McQuillan's formal spectrum is a locally topologically ringed space.** For a weakly
admissible topological ring the formal spectrum taken along its *weak* ideals of definition
carries a sheaf of topological rings with local stalks. -/
@[reducible] noncomputable def spfwLTRS (hA : IsWeaklyPreAdmissible A) : LTRS.{u} :=
  spfLTRSOn A IsWeakIdealOfDefinition (weaklyPreAdmissibleSpfIndex A hA)

/-- The presheafed space of topological rings underlying McQuillan's formal spectrum as an object
of `LTRS` is `Spfw A`. -/
@[simp]
theorem spfwLTRS_toPresheafedSpace (hA : IsWeaklyPreAdmissible A) :
    (spfwLTRS A hA).toPresheafedSpace = SpfOn A IsWeakIdealOfDefinition := rfl

end AlgebraicGeometry
