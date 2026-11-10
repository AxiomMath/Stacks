module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumComponentIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms out of a formal spectrum

Let `A` be a pre-admissible topological ring, so that `Spf A` is the space of open primes of `A`
carrying the structure sheaf `𝒪_{Spf A} = lim 𝒪_λ`. This file proves the source's identification

`Mor_{LTRS}(Spf A, 𝔜) = lim_λ Mor_{LTRS}(Spec (A/I_λ), 𝔜)`,

a compatible family of morphisms out of the quotients `Spec (A/I_λ)` assembling into a unique
morphism out of `Spf A`.

Nothing deep happens. The underlying map is forced, each `Spec (A/I_λ) → Spf A` being a
homeomorphism; and the comparison map of sheaves is forced too, the sections of `𝒪_{Spf A}`
being a limit of the sections of the `𝒪_λ`. What there is to do is bookkeeping: the base maps
of the given family are only *propositionally* equal to the common map, so the cone condition,
the compatibility of the stalk maps and the final identities have to be pushed through
transports. The device used throughout is `AlgebraicGeometry.PresheafedSpace.ofBaseEq`, which
replaces the base map of a morphism of presheafed spaces by an equal one; after that
replacement every identity in sight holds with its two sides having *definitionally* equal base
maps, and no transport survives.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.ofBaseEq`: a morphism of presheafed spaces with its base
  map replaced by an equal one.
* `AlgebraicGeometry.spfQuotientTransitionOn`: the morphism `Spec (A/J) → Spec (A/I)` of locally
  topologically ringed spaces attached to an inclusion `I ⊆ J` of ideals of definition.

## Main results

* `AlgebraicGeometry.spfOn_hom_ext`: two morphisms out of `Spf A` agreeing after every
  `Spec (A/I) → Spf A` are equal.
* `AlgebraicGeometry.exists_hom_of_spfPointOn_comp_eq`: a compatible family of morphisms
  `Spec (A/I) → Z` of presheafed spaces of topological rings comes from a morphism
  `Spf A → Z`.
* `AlgebraicGeometry.existsUnique_hom_of_spfQuotientPointOn_comp_eq`: **the mapping-limit
  formula.** A compatible family of morphisms `Spec (A/I_λ) → 𝔜` of locally topologically
  ringed spaces comes from a *unique* morphism `Spf A → 𝔜`.

## Implementation notes

The formula is stated as an `ExistsUnique` rather than as an equivalence of types, because that
is the shape its consumers use: the surjectivity half of Stacks 0AI1 produces the morphisms
`Spec (A/I_λ) → 𝔜` from a transformation of functors of points and needs both the morphism
`Spf A → 𝔜` they induce and the identities `Spec (A/I_λ) → Spf A → 𝔜 = Spec (A/I_λ) → 𝔜`.

Only pre-admissibility is used: a single ideal of definition is enough to pin down the base map,
and the ideals of definition of any topological ring are stable under intersection, which is
what makes the base maps of the family agree.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

namespace PresheafedSpace

variable {C : Type*} [Category C]

/-- A morphism of presheafed spaces with its base map replaced by an equal one. The point of the
construction is that the result has the *given* map as its base map definitionally, so that
identities between morphisms whose base maps are only propositionally equal can be stated, and
proved, without transport. -/
def ofBaseEq {X Y : PresheafedSpace C} (α : X ⟶ Y) {φ : X.carrier ⟶ Y.carrier}
    (hφ : φ = α.base) : X ⟶ Y where
  base := φ
  c := α.c ≫ (TopCat.Presheaf.pushforwardEq hφ.symm X.presheaf).hom

/-- The base map of `ofBaseEq α hφ` is `φ`. -/
@[simp]
theorem ofBaseEq_base {X Y : PresheafedSpace C} (α : X ⟶ Y) {φ : X.carrier ⟶ Y.carrier}
    (hφ : φ = α.base) : (ofBaseEq α hφ).base = φ := rfl

/-- The sheaf map of `ofBaseEq α hφ` is that of `α` followed by the identification of the
pushforwards along the equal maps `α.base` and `φ`. -/
@[simp]
theorem ofBaseEq_c {X Y : PresheafedSpace C} (α : X ⟶ Y) {φ : X.carrier ⟶ Y.carrier}
    (hφ : φ = α.base) :
    (ofBaseEq α hφ).c = α.c ≫ (TopCat.Presheaf.pushforwardEq hφ.symm X.presheaf).hom := rfl

/-- Replacing the base map of a morphism of presheafed spaces by an equal one does not change
the morphism. -/
theorem ofBaseEq_eq {X Y : PresheafedSpace C} (α : X ⟶ Y) {φ : X.carrier ⟶ Y.carrier}
    (hφ : φ = α.base) : ofBaseEq α hφ = α := by
  subst hφ
  refine hext _ _ rfl (heq_of_eq (NatTrans.ext (funext fun V => ?_)))
  simp [ofBaseEq]

end PresheafedSpace

open TopologicalRing

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-! ### The system of quotients -/

/-- For ideals of definition `I ⊆ J` the morphism `Spec (A/J) → Spec (A/I)` of locally
topologically ringed spaces attached to the surjection `A/I → A/J`. -/
noncomputable def spfQuotientTransitionOn {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    schemeToLTRSObj (Spec (spfQuotientOn A J)) ⟶ schemeToLTRSObj (Spec (spfQuotientOn A I)) :=
  (schemeToFormalScheme.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))).hom

/-- For ideals of definition `I ⊆ J` the morphism `Spec (A/J) → Spec (A/I)` of locally
topologically ringed spaces attached to the surjection `A/I → A/J`.

The ideals-of-definition case of `spfQuotientTransitionOn`. -/
@[reducible,
  ega "I 10.10.4" "partial"]
noncomputable def spfQuotientTransition {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    schemeToLTRSObj (Spec (spfQuotient A J)) ⟶ schemeToLTRSObj (Spec (spfQuotient A I)) :=
  spfQuotientTransitionOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The morphism of presheafed spaces underlying `AlgebraicGeometry.spfQuotientTransitionOn`. -/
theorem spfQuotientTransitionOn_toHom {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    (spfQuotientTransitionOn A h).toHom =
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := rfl

omit [IsTopologicalRing A] in
/-- The morphism of presheafed spaces underlying `AlgebraicGeometry.spfQuotientTransition`.

The ideals-of-definition case of `spfQuotientTransitionOn_toHom`. -/
theorem spfQuotientTransition_toHom {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    (spfQuotientTransition A h).toHom =
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) :=
  spfQuotientTransitionOn_toHom (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

/-- The morphisms `Spec (A/I_λ) → SpfOn A P` are themselves a family compatible with the transition
maps: the system of quotients and the morphisms out of it form a cocone with vertex `SpfOn A P`. -/
theorem spfQuotientTransitionOn_comp_spfQuotientPointOn (I₀ : SpfIndex A P)
    {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    spfQuotientTransitionOn A h ≫ spfQuotientPointOn A I₀ I = spfQuotientPointOn A I₀ J :=
  LocallyTopologicallyRingedSpace.Hom.ext' (schemeToLTRSHom_comp_spfPointOn A h)

/-- The morphisms `Spec (A/I_λ) → Spf A` are themselves a family compatible with the transition
maps: the system of quotients and the morphisms out of it form a cocone with vertex `Spf A`.

The ideals-of-definition case of `spfQuotientTransitionOn_comp_spfQuotientPointOn`. -/
theorem spfQuotientTransition_comp_spfQuotientPoint (hA : IsPreAdmissible A)
    {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    spfQuotientTransition A h ≫ spfQuotientPoint A hA I = spfQuotientPoint A hA J :=
  spfQuotientTransitionOn_comp_spfQuotientPointOn (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA) (I := I) (J := J) (h := h)

/-- The identification of `Spec (A/J)` with the space of open primes factors through that of
`Spec (A/I)`, for `I ⊆ J`. No transport is needed: `A/I → A/J` composed with `A → A/I` is
`A → A/J` on the nose. -/
theorem base_comp_spfOfQuotientOn {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).base ≫ spfOfQuotientOn A I =
      spfOfQuotientOn A J := rfl

/-- The identification of `Spec (A/J)` with the space of open primes factors through that of
`Spec (A/I)`, for `I ⊆ J`. No transport is needed: `A/I → A/J` composed with `A → A/I` is
`A → A/J` on the nose.

The ideals-of-definition case of `base_comp_spfOfQuotientOn`. -/
theorem base_comp_spfOfQuotient {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).base ≫ spfOfQuotient A I =
      spfOfQuotient A J :=
  base_comp_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

/-! ### The identifications of the quotients with the terms of the inverse system -/

/-- The transition map of the inverse system, read on the pushforwards to `SpfOn A P` of the
pseudo-discrete structure sheaves of the quotients. It is the comparison map of
`Spec (A/J) → Spec (A/I)`, pushed forward along `Spec (A/I) → SpfOn A P`; no transport is needed,
the triangle of spectra over `SpfOn A P` commuting definitionally. -/
@[ega "I 10.1.1" "partial"]
noncomputable def spfPDTransitionOn {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    spfOfQuotientOn A I _* pseudoDiscrete (Spec (spfQuotientOn A I)).presheaf ⟶
      spfOfQuotientOn A J _* pseudoDiscrete (Spec (spfQuotientOn A J)).presheaf :=
  (TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfOfQuotientOn A I)).map
    (pseudoDiscreteC (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))))

/-- The transition map of the inverse system, read on the pushforwards to `Spf A` of the
pseudo-discrete structure sheaves of the quotients. It is the comparison map of
`Spec (A/J) → Spec (A/I)`, pushed forward along `Spec (A/I) → Spf A`; no transport is needed,
the triangle of spectra over `Spf A` commuting definitionally.

The ideals-of-definition case of `spfPDTransitionOn`. -/
@[reducible,
  ega "I 10.1.1" "partial"]
noncomputable def spfPDTransition {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    spfOfQuotient A I _* pseudoDiscrete (Spec (spfQuotient A I)).presheaf ⟶
      spfOfQuotient A J _* pseudoDiscrete (Spec (spfQuotient A J)).presheaf :=
  spfPDTransitionOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

/-- The transition map `𝒪_I → 𝒪_J` of the inverse system defining `𝒪_{SpfOn A P}`, between the
pseudo-discretised terms. -/
noncomputable def spfComponentPDTransitionOn {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    pseudoDiscrete (spfComponentOn A I) ⟶ pseudoDiscrete (spfComponentOn A J) :=
  pseudoDiscreteFunctor.map (spfTransitionOn A h)

/-- The transition map `𝒪_I → 𝒪_J` of the inverse system defining `𝒪_{Spf A}`, between the
pseudo-discretised terms.

The ideals-of-definition case of `spfComponentPDTransitionOn`. -/
@[reducible] noncomputable def spfComponentPDTransition {I J : IdealsOfDefinition A}
    (h : I.1 ≤ J.1) :
    pseudoDiscrete (spfComponent A I) ⟶ pseudoDiscrete (spfComponent A J) :=
  spfComponentPDTransitionOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

/-- The comparison map of the identification of `Spec (A/I)` with `(SpfOn A P, 𝒪_I)`, read as a map
of presheaves of topological rings on `SpfOn A P`. -/
noncomputable def spfComponentPDcOn (I : SpfIndex A P) :
    pseudoDiscrete (spfComponentOn A I) ⟶
      spfOfQuotientOn A I _* pseudoDiscrete (Spec (spfQuotientOn A I)).presheaf :=
  (spfComponentPDOn A I).c

/-- The comparison map of the identification of `Spec (A/I)` with `(Spf A, 𝒪_I)`, read as a map
of presheaves of topological rings on `Spf A`.

The ideals-of-definition case of `spfComponentPDcOn`. -/
@[reducible] noncomputable def spfComponentPDc (I : IdealsOfDefinition A) :
    pseudoDiscrete (spfComponent A I) ⟶
      spfOfQuotient A I _* pseudoDiscrete (Spec (spfQuotient A I)).presheaf :=
  spfComponentPDcOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The comparison map of `Spec (A/I) → SpfOn A P` is the projection of `𝒪_{SpfOn A P} = lim 𝒪_λ`
onto `𝒪_I`, followed by the identification of `(SpfOn A P, 𝒪_I)` with `Spec (A/I)`. -/
theorem spfPointOn_c (I : SpfIndex A P) :
    (spfPointOn A I).c = spfProjectionOn A I ≫ spfComponentPDcOn A I := rfl

/-- The comparison map of `Spec (A/I) → Spf A` is the projection of `𝒪_{Spf A} = lim 𝒪_λ` onto
`𝒪_I`, followed by the identification of `(Spf A, 𝒪_I)` with `Spec (A/I)`.

The ideals-of-definition case of `spfPointOn_c`. -/
theorem spfPoint_c (I : IdealsOfDefinition A) :
    (spfPoint A I).c = spfProjection A I ≫ spfComponentPDc A I :=
  spfPointOn_c (A := A) (P := IsIdealOfDefinition) (I := I)

/-- **The identifications of the `Spec (A/I_λ)` with the terms `𝒪_λ` of the inverse system are
compatible with the transition maps.** Both sides are, on sections, the comparison map of
`Spec (A/J) → Spec (A/I)`: the transition map of the inverse system is that comparison map
whiskered onto `SpfOn A P`, and the identifications are the identity on sections. -/
theorem spfComponentPDIsoOn_hom_comp {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    (spfComponentPDIsoOn A I).hom ≫ spfComponentPDTransitionOn A h =
      spfPDTransitionOn A h ≫ (spfComponentPDIsoOn A J).hom :=
  NatTrans.ext (funext fun _ => Subtype.ext (RingHom.ext fun _ => rfl))

/-- **The identifications of the `Spec (A/I_λ)` with the terms `𝒪_λ` of the inverse system are
compatible with the transition maps.** Both sides are, on sections, the comparison map of
`Spec (A/J) → Spec (A/I)`: the transition map of the inverse system is that comparison map
whiskered onto `Spf A`, and the identifications are the identity on sections.

The ideals-of-definition case of `spfComponentPDIsoOn_hom_comp`. -/
theorem spfComponentPDIso_hom_comp {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    (spfComponentPDIso A I).hom ≫ spfComponentPDTransition A h =
      spfPDTransition A h ≫ (spfComponentPDIso A J).hom :=
  spfComponentPDIsoOn_hom_comp (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

/-- The identification of `Spec (A/I)` with `(SpfOn A P, 𝒪_I)` and the comparison morphism of
pseudo-discretised presheafed spaces are inverse on sections: both are the identity there. -/
theorem spfComponentPDIsoOn_hom_comp_spfComponentPDcOn (I : SpfIndex A P) :
    (spfComponentPDIsoOn A I).hom ≫ spfComponentPDcOn A I = 𝟙 _ :=
  NatTrans.ext (funext fun _ => Subtype.ext (RingHom.ext fun _ => rfl))

/-- The identification of `Spec (A/I)` with `(Spf A, 𝒪_I)` and the comparison morphism of
pseudo-discretised presheafed spaces are inverse on sections: both are the identity there.

The ideals-of-definition case of `spfComponentPDIsoOn_hom_comp_spfComponentPDcOn`. -/
theorem spfComponentPDIso_hom_comp_spfComponentPDc (I : IdealsOfDefinition A) :
    (spfComponentPDIso A I).hom ≫ spfComponentPDc A I = 𝟙 _ :=
  spfComponentPDIsoOn_hom_comp_spfComponentPDcOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-! ### Separation -/

/-- **Two morphisms out of a formal spectrum agreeing on every `Spec (A/I)` are equal.** The
maps `Spec (A/I) → SpfOn A P` are jointly surjective — each is a homeomorphism — and they separate
the sections of `𝒪_{SpfOn A P} = lim 𝒪_λ`. -/
theorem spfOn_hom_ext (I₀ : SpfIndex A P) {Z : PresheafedSpace TopCommRingCat.{u}}
    {f₁ f₂ : SpfOn A P ⟶ Z}
    (h : ∀ I : SpfIndex A P, spfPointOn A I ≫ f₁ = spfPointOn A I ≫ f₂) : f₁ = f₂ := by
  refine presheafedSpace_hom_ext_of_cover (fun I : SpfIndex A P => spfPointOn A I)
    (fun x => ?_) (fun _ _ _ _ hab => spfPointOn_hom_ext A hab) f₁ f₂ h
  obtain ⟨q, hq⟩ := surjective_spfOfQuotientOn A I₀ x
  exact ⟨I₀, q, hq⟩

/-- **Two morphisms out of a formal spectrum agreeing on every `Spec (A/I)` are equal.** The
maps `Spec (A/I) → Spf A` are jointly surjective — each is a homeomorphism — and they separate
the sections of `𝒪_{Spf A} = lim 𝒪_λ`.

The ideals-of-definition case of `spfOn_hom_ext`. -/
theorem spf_hom_ext (hA : IsPreAdmissible A) {Z : PresheafedSpace TopCommRingCat.{u}}
    {f₁ f₂ : Spf A ⟶ Z}
    (h : ∀ I : IdealsOfDefinition A, spfPoint A I ≫ f₁ = spfPoint A I ≫ f₂) : f₁ = f₂ :=
  spfOn_hom_ext (A := A) (P := IsIdealOfDefinition) (I₀ := preAdmissibleSpfIndex A hA) (Z := Z)
    (f₁ := f₁) (f₂ := f₂) (h := h)

/-! ### The glued morphism -/

section Glue

variable {Z : PresheafedSpace TopCommRingCat.{u}}
  (g : ∀ I : SpfIndex A P,
    pseudoDiscreteSpace (Spec (spfQuotientOn A I)).toPresheafedSpace ⟶ Z)

/-- The base map of the morphism `SpfOn A P → Z` glued from a compatible family: the base map of
one member of the family, read on `SpfOn A P` through the homeomorphism
`Spec (A/I₀) → SpfOn A P`. -/
noncomputable def spfGlueBaseOn (I₀ : SpfIndex A P) : spfSpace A ⟶ Z.carrier :=
  inv (spfOfQuotientOn A I₀) ≫ (g I₀).base

/-- The base maps of a compatible family all give the same map `SpfOn A P → Z`: two ideals of
definition contain a third one, and the family is compatible with the transition map to it. -/
theorem inv_spfOfQuotientOn_comp_base_eq
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    (I J : SpfIndex A P) :
    inv (spfOfQuotientOn A I) ≫ (g I).base = inv (spfOfQuotientOn A J) ≫ (g J).base := by
  have key : ∀ (K L : SpfIndex A P) (h : K.1 ≤ L.1),
      inv (spfOfQuotientOn A L) ≫ (g L).base = inv (spfOfQuotientOn A K) ≫ (g K).base := by
    intro K L h
    have hbase : spfOfQuotientOn A L =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).base ≫ spfOfQuotientOn A K :=
      (base_comp_spfOfQuotientOn A h).symm
    have hgb : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))).base ≫ (g K).base =
        (g L).base := congrArg PresheafedSpace.Hom.base (hg K L h)
    rw [← cancel_epi (spfOfQuotientOn A L), IsIso.hom_inv_id_assoc]
    conv_rhs => rw [hbase]
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
    exact hgb.symm
  exact (key (spfIndexMeet A I J) I inf_le_left).trans
    (key (spfIndexMeet A I J) J inf_le_right).symm

/-- Each `Spec (A/I) → SpfOn A P`, followed by the glued base map, is the base map of the member of
the family at `I`. -/
theorem spfOfQuotientOn_comp_spfGlueBaseOn
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    (I₀ I : SpfIndex A P) :
    spfOfQuotientOn A I ≫ spfGlueBaseOn A g I₀ = (g I).base := by
  rw [spfGlueBaseOn, inv_spfOfQuotientOn_comp_base_eq A g hg I₀ I, IsIso.hom_inv_id_assoc]

section Base

variable (β : spfSpace A ⟶ Z.carrier)
  (hβ : ∀ I : SpfIndex A P, spfOfQuotientOn A I ≫ β = (g I).base)

/-- The member of the family at `I`, with its base map rewritten as the composite
`Spec (A/I) → SpfOn A P → Z`. The two are the same morphism, by
`AlgebraicGeometry.spfGluePointOn_eq`; what the rewriting buys is that the base map is now that
composite *definitionally*, so that the identities below need no transport. -/
noncomputable def spfGluePointOn (I : SpfIndex A P) :
    pseudoDiscreteSpace (Spec (spfQuotientOn A I)).toPresheafedSpace ⟶ Z :=
  PresheafedSpace.ofBaseEq (g I) (hβ I)

/-- Rewriting the base map changes nothing: the morphism of `AlgebraicGeometry.spfGluePointOn` is
the member of the family at `I`. -/
theorem spfGluePointOn_eq (I : SpfIndex A P) : spfGluePointOn A g β hβ I = g I :=
  PresheafedSpace.ofBaseEq_eq _ _

/-- The compatibility of the family, stated for the morphisms with rewritten base maps. Both
sides now have the same base map definitionally, so it is an identity of comparison maps of
sheaves on the nose. -/
theorem spfGluePointOn_comp
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫
        spfGluePointOn A g β hβ I = spfGluePointOn A g β hβ J := by
  rw [spfGluePointOn_eq, spfGluePointOn_eq]
  exact hg I J h

/-- The comparison map of sheaves of the member of the family at `I`, read as a map into the
pushforward along `SpfOn A P → Z` of the term `𝒪_I` of the inverse system. -/
noncomputable def spfGlueCOn (I : SpfIndex A P) :
    Z.presheaf ⟶
      β _* (spfOfQuotientOn A I _* pseudoDiscrete (Spec (spfQuotientOn A I)).presheaf) :=
  (spfGluePointOn A g β hβ I).c

/-- **The comparison maps of the family are compatible with the transition maps of the inverse
system.** This is the compatibility of the family itself, read off the equality of morphisms
`AlgebraicGeometry.spfGluePointOn_comp`, whose two sides have the same base map. -/
theorem spfGlueCOn_comp
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    spfGlueCOn A g β hβ I ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} β).map
        (spfPDTransitionOn A h) = spfGlueCOn A g β hβ J :=
  eq_of_heq (congr_arg_heq
    (fun α : pseudoDiscreteSpace (Spec (spfQuotientOn A J)).toPresheafedSpace ⟶ Z => α.c)
    (spfGluePointOn_comp A g β hβ hg h))

/-- The leg at `λ` of the glued comparison map: the comparison map of the member of the family
at `λ`, read through the identification of `Spec (A/I_λ)` with `(SpfOn A P, 𝒪_λ)`. -/
noncomputable def spfGlueLegOn (I : SpfIndex A P) :
    Z.presheaf ⟶ β _* pseudoDiscrete (spfComponentOn A I) :=
  spfGlueCOn A g β hβ I ≫
    (TopCat.Presheaf.pushforward TopCommRingCat.{u} β).map (spfComponentPDIsoOn A I).hom

/-- **The legs are compatible with the transition maps of the inverse system**, so they are a
cone on it. -/
theorem spfGlueLegOn_comp
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    spfGlueLegOn A g β hβ I ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} β).map
        (spfComponentPDTransitionOn A h) = spfGlueLegOn A g β hβ J := by
  simp only [spfGlueLegOn]
  rw [Category.assoc, ← Functor.map_comp, spfComponentPDIsoOn_hom_comp A h, Functor.map_comp,
    ← Category.assoc, spfGlueCOn_comp A g β hβ hg h]

/-- **The legs come from a map into `𝒪_{SpfOn A P} = lim 𝒪_λ`**, the pushforward of a limit of
presheaves being the limit of the pushforwards. -/
theorem exists_comp_spfProjectionOn_eq_spfGlueLegOn
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J) :
    ∃ c : Z.presheaf ⟶ β _* spfPresheafOn A P, ∀ I : SpfIndex A P,
      c ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} β).map (spfProjectionOn A I) =
        spfGlueLegOn A g β hβ I := by
  have : PreservesLimitsOfShape (SpfIndex A P)
      (TopCat.Presheaf.pushforward TopCommRingCat.{u} β) :=
    inferInstanceAs (PreservesLimitsOfShape (SpfIndex A P)
      ((Functor.whiskeringLeft _ _ _).obj (Opens.map β).op))
  have HL := isLimitOfPreserves (TopCat.Presheaf.pushforward TopCommRingCat.{u} β)
    (limit.isLimit (spfDiagramOn A P ⋙ pseudoDiscreteFunctor))
  exact ⟨HL.lift
    { pt := Z.presheaf
      π :=
        { app := fun I => spfGlueLegOn A g β hβ I
          naturality := fun _ _ k => (Category.id_comp _).trans
            (spfGlueLegOn_comp A g β hβ hg (leOfHom k)).symm } }, fun I => HL.fac _ I⟩

end Base

/-- **A compatible family of morphisms out of the quotients comes from a morphism out of the
formal spectrum.** The underlying map is forced, each `Spec (A/I_λ) → SpfOn A P` being a
homeomorphism, and the comparison map of sheaves is the one the limit `𝒪_{SpfOn A P} = lim 𝒪_λ`
provides. -/
theorem exists_hom_of_spfPointOn_comp_eq (I₀ : SpfIndex A P)
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J) :
    ∃ f : SpfOn A P ⟶ Z, ∀ I : SpfIndex A P, spfPointOn A I ≫ f = g I := by
  obtain ⟨c, hc⟩ := exists_comp_spfProjectionOn_eq_spfGlueLegOn A g (spfGlueBaseOn A g I₀)
    (spfOfQuotientOn_comp_spfGlueBaseOn A g hg I₀) hg
  refine ⟨⟨spfGlueBaseOn A g I₀, c⟩, fun I => ?_⟩
  rw [← spfGluePointOn_eq A g (spfGlueBaseOn A g I₀)
    (spfOfQuotientOn_comp_spfGlueBaseOn A g hg I₀) I]
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  change c ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} _).map
    (spfProjectionOn A I ≫ spfComponentPDcOn A I) = spfGlueCOn A g _ _ I
  rw [Functor.map_comp, ← Category.assoc, hc I, spfGlueLegOn, Category.assoc, ← Functor.map_comp,
    spfComponentPDIsoOn_hom_comp_spfComponentPDcOn, CategoryTheory.Functor.map_id,
    Category.comp_id]

end Glue

/-! ### The ideals-of-definition forms of the gluing -/

section Glue

variable {Z : PresheafedSpace TopCommRingCat.{u}}
  (g : ∀ I : IdealsOfDefinition A,
    pseudoDiscreteSpace (Spec (spfQuotient A I)).toPresheafedSpace ⟶ Z)

/-- The base map of the morphism `Spf A → Z` glued from a compatible family: the base map of one
member of the family, read on `Spf A` through the homeomorphism `Spec (A/I₀) → Spf A`.

The ideals-of-definition case of `spfGlueBaseOn`. -/
@[reducible] noncomputable def spfGlueBase (I₀ : IdealsOfDefinition A) : spfSpace A ⟶ Z.carrier :=
  spfGlueBaseOn A g I₀

/-- The base maps of a compatible family all give the same map `Spf A → Z`: two ideals of
definition contain a third one, and the family is compatible with the transition map to it.

The ideals-of-definition case of `inv_spfOfQuotientOn_comp_base_eq`. -/
theorem inv_spfOfQuotient_comp_base_eq
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    (I J : IdealsOfDefinition A) :
    inv (spfOfQuotient A I) ≫ (g I).base = inv (spfOfQuotient A J) ≫ (g J).base :=
  inv_spfOfQuotientOn_comp_base_eq (g := g) (A := A) (P := IsIdealOfDefinition) (hg := hg) (I := I)
    (J := J)

/-- Each `Spec (A/I) → Spf A`, followed by the glued base map, is the base map of the member of
the family at `I`.

The ideals-of-definition case of `spfOfQuotientOn_comp_spfGlueBaseOn`. -/
theorem spfOfQuotient_comp_spfGlueBase
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    (I₀ I : IdealsOfDefinition A) :
    spfOfQuotient A I ≫ spfGlueBase A g I₀ = (g I).base :=
  spfOfQuotientOn_comp_spfGlueBaseOn (g := g) (A := A) (P := IsIdealOfDefinition) (hg := hg)
    (I₀ := I₀) (I := I)

section Base

variable (β : spfSpace A ⟶ Z.carrier)
  (hβ : ∀ I : IdealsOfDefinition A, spfOfQuotient A I ≫ β = (g I).base)

/-- The member of the family at `I`, with its base map rewritten as the composite
`Spec (A/I) → Spf A → Z`. The two are the same morphism, by
`AlgebraicGeometry.spfGluePoint_eq`; what the rewriting buys is that the base map is now that
composite *definitionally*, so that the identities below need no transport.

The ideals-of-definition case of `spfGluePointOn`. -/
@[reducible] noncomputable def spfGluePoint (I : IdealsOfDefinition A) :
    pseudoDiscreteSpace (Spec (spfQuotient A I)).toPresheafedSpace ⟶ Z :=
  spfGluePointOn A g β hβ I

/-- Rewriting the base map changes nothing: the morphism of `AlgebraicGeometry.spfGluePoint` is
the member of the family at `I`.

The ideals-of-definition case of `spfGluePointOn_eq`. -/
theorem spfGluePoint_eq (I : IdealsOfDefinition A) : spfGluePoint A g β hβ I = g I :=
  spfGluePointOn_eq (hβ := hβ) (β := β) (g := g) (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The compatibility of the family, stated for the morphisms with rewritten base maps. Both
sides now have the same base map definitionally, so it is an identity of comparison maps of
sheaves on the nose.

The ideals-of-definition case of `spfGluePointOn_comp`. -/
theorem spfGluePoint_comp
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫
        spfGluePoint A g β hβ I = spfGluePoint A g β hβ J :=
  spfGluePointOn_comp (hβ := hβ) (β := β) (g := g) (A := A) (P := IsIdealOfDefinition) (hg := hg)
    (I := I) (J := J) (h := h)

/-- The comparison map of sheaves of the member of the family at `I`, read as a map into the
pushforward along `Spf A → Z` of the term `𝒪_I` of the inverse system.

The ideals-of-definition case of `spfGlueCOn`. -/
@[reducible] noncomputable def spfGlueC (I : IdealsOfDefinition A) :
    Z.presheaf ⟶
      β _* (spfOfQuotient A I _* pseudoDiscrete (Spec (spfQuotient A I)).presheaf) :=
  spfGlueCOn A g β hβ I

/-- **The comparison maps of the family are compatible with the transition maps of the inverse
system.** This is the compatibility of the family itself, read off the equality of morphisms
`AlgebraicGeometry.spfGluePoint_comp`, whose two sides have the same base map.

The ideals-of-definition case of `spfGlueCOn_comp`. -/
theorem spfGlueC_comp
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    spfGlueC A g β hβ I ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} β).map
        (spfPDTransition A h) = spfGlueC A g β hβ J :=
  spfGlueCOn_comp (hβ := hβ) (β := β) (g := g) (A := A) (P := IsIdealOfDefinition) (hg := hg)
    (I := I) (J := J) (h := h)

/-- The leg at `λ` of the glued comparison map: the comparison map of the member of the family
at `λ`, read through the identification of `Spec (A/I_λ)` with `(Spf A, 𝒪_λ)`.

The ideals-of-definition case of `spfGlueLegOn`. -/
@[reducible] noncomputable def spfGlueLeg (I : IdealsOfDefinition A) :
    Z.presheaf ⟶ β _* pseudoDiscrete (spfComponent A I) :=
  spfGlueLegOn A g β hβ I

/-- **The legs are compatible with the transition maps of the inverse system**, so they are a
cone on it.

The ideals-of-definition case of `spfGlueLegOn_comp`. -/
theorem spfGlueLeg_comp
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J)
    {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    spfGlueLeg A g β hβ I ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} β).map
        (spfComponentPDTransition A h) = spfGlueLeg A g β hβ J :=
  spfGlueLegOn_comp (hβ := hβ) (β := β) (g := g) (A := A) (P := IsIdealOfDefinition) (hg := hg)
    (I := I) (J := J) (h := h)

/-- **The legs come from a map into `𝒪_{Spf A} = lim 𝒪_λ`**, the pushforward of a limit of
presheaves being the limit of the pushforwards.

The ideals-of-definition case of `exists_comp_spfProjectionOn_eq_spfGlueLegOn`. -/
theorem exists_comp_spfProjection_eq_spfGlueLeg
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J) :
    ∃ c : Z.presheaf ⟶ β _* spfPresheaf A, ∀ I : IdealsOfDefinition A,
      c ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} β).map (spfProjection A I) =
        spfGlueLeg A g β hβ I :=
  exists_comp_spfProjectionOn_eq_spfGlueLegOn (hβ := hβ) (β := β) (g := g) (Z := Z) (A := A)
    (P := IsIdealOfDefinition) (hg := hg)

end Base

/-- **A compatible family of morphisms out of the quotients comes from a morphism out of the
formal spectrum.** The underlying map is forced, each `Spec (A/I_λ) → Spf A` being a
homeomorphism, and the comparison map of sheaves is the one the limit `𝒪_{Spf A} = lim 𝒪_λ`
provides.

The ideals-of-definition case of `exists_hom_of_spfPointOn_comp_eq`. -/
theorem exists_hom_of_spfPoint_comp_eq (hA : IsPreAdmissible A)
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ g I = g J) :
    ∃ f : Spf A ⟶ Z, ∀ I : IdealsOfDefinition A, spfPoint A I ≫ f = g I :=
  exists_hom_of_spfPointOn_comp_eq (g := g) (Z := Z) (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA) (hg := hg)

end Glue

/-! ### The mapping-limit formula -/

/-- **The mapping-limit formula for a formal spectrum**, `Mor(SpfOn A P, 𝔜) = lim_λ
Mor(Spec (A/I_λ), 𝔜)`. A family of morphisms `Spec (A/I_λ) → 𝔜` of locally topologically ringed
spaces compatible with the transition maps `Spec (A/I_μ) → Spec (A/I_λ)` of the system of
quotients comes from a unique morphism `SpfOn A P → 𝔜`.

Existence is `AlgebraicGeometry.exists_hom_of_spfPointOn_comp_eq`, the locality of the stalk maps
of the morphism it produces coming from that of the stalk maps of the family; uniqueness is
`AlgebraicGeometry.spfOn_hom_ext`. -/
theorem existsUnique_hom_of_spfQuotientPointOn_comp_eq (I₀ : SpfIndex A P) {Y : LTRS.{u}}
    (g : ∀ I : SpfIndex A P, schemeToLTRSObj (Spec (spfQuotientOn A I)) ⟶ Y)
    (hg : ∀ (I J : SpfIndex A P) (h : I.1 ≤ J.1),
      spfQuotientTransitionOn A h ≫ g I = g J) :
    ∃! f : spfLTRSOn A P I₀ ⟶ Y, ∀ I : SpfIndex A P,
      spfQuotientPointOn A I₀ I ≫ f = g I := by
  obtain ⟨f₀, hf₀⟩ := exists_hom_of_spfPointOn_comp_eq A (fun I => (g I).toHom) I₀
    fun I J h => congrArg LocallyTopologicallyRingedSpace.Hom.toHom (hg I J h)
  have hloc : ∀ x : SpfOn A P, IsLocalHom (f₀.stalkMap x).1 := by
    intro x
    obtain ⟨q, rfl⟩ := surjective_spfOfQuotientOn A I₀ x
    have key : IsLocalHom ((spfPointOn A I₀ ≫ f₀).stalkMap q).1 := by
      rw [hf₀ I₀]
      exact (g I₀).isLocalHom q
    rw [PresheafedSpace.stalkMap.comp] at key
    exact @isLocalHom_of_comp _ _ _ _ _ _ (f₀.stalkMap _).1
      ((spfPointOn A I₀).stalkMap q).1 key
  refine ⟨⟨f₀, hloc⟩, fun I => LocallyTopologicallyRingedSpace.Hom.ext' (hf₀ I), fun f' hf' => ?_⟩
  refine LocallyTopologicallyRingedSpace.Hom.ext' (spfOn_hom_ext A I₀ fun I => ?_)
  exact (congrArg LocallyTopologicallyRingedSpace.Hom.toHom (hf' I)).trans (hf₀ I).symm

/-- **The mapping-limit formula for a formal spectrum**, `Mor(Spf A, 𝔜) = lim_λ
Mor(Spec (A/I_λ), 𝔜)`. A family of morphisms `Spec (A/I_λ) → 𝔜` of locally topologically ringed
spaces compatible with the transition maps `Spec (A/I_μ) → Spec (A/I_λ)` of the system of
quotients comes from a unique morphism `Spf A → 𝔜`.

Existence is `AlgebraicGeometry.exists_hom_of_spfPoint_comp_eq`, the locality of the stalk maps
of the morphism it produces coming from that of the stalk maps of the family; uniqueness is
`AlgebraicGeometry.spf_hom_ext`.

The ideals-of-definition case of `existsUnique_hom_of_spfQuotientPointOn_comp_eq`. -/
theorem existsUnique_hom_of_spfQuotientPoint_comp_eq (hA : IsPreAdmissible A) {Y : LTRS.{u}}
    (g : ∀ I : IdealsOfDefinition A, schemeToLTRSObj (Spec (spfQuotient A I)) ⟶ Y)
    (hg : ∀ (I J : IdealsOfDefinition A) (h : I.1 ≤ J.1),
      spfQuotientTransition A h ≫ g I = g J) :
    ∃! f : spfLTRS A hA ⟶ Y, ∀ I : IdealsOfDefinition A,
      spfQuotientPoint A hA I ≫ f = g I :=
  existsUnique_hom_of_spfQuotientPointOn_comp_eq (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA) (Y := Y) (g := g) (hg := hg)

end AlgebraicGeometry

end
