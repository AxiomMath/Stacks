module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyIsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BafflingTheoremIdentity

/-!
# The identity law of a system of étale sheaves, transported to cohomology

`Stacks.EtaleCohomology.EtaleSheafSystem` ([Stacks, Tag 0EZL]) imposes only the cocycle
condition, following the source, which does not ask the map attached to an identity index to be
the identity; and that omission cannot be repaired by adding a field, since
`id_eq_zero_of_isIso_systemTransitionMap_zeroTransitionSystem` (in the namespace
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology`) exhibits a legitimate system whose identity
transition is invertible only on a zero sheaf. The identity law is therefore a *hypothesis on a
system*, and this file carries it from the sheaves to their cohomology.

The hypothesis is `Stacks.EtaleCohomology.HasSheafIdentityLaw`: the map the system attaches to
an identity index is the canonical identification
`Stacks.EtaleCohomology.systemPullbackId` of the inverse image along that transition with the
identity functor. Its consequence is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.HasCohomologyIdentityLaw`, the one extra input
of `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimit_levelCohomologyCocone` — the
statement of [Stacks, Tag 09YQ] in the tag's own spelling, with the cohomology of the levels
themselves as the objects of the diagram.

The hypothesis holds for the system of direct images of a sheaf along the projections of a cone,
by `Stacks.EtaleCohomology.directImageSystem_map_id`; so every presented system built on
`Stacks.EtaleCohomology.directImageSystem` satisfies the identity law on cohomology in every
degree.

## Main definitions

* `Stacks.EtaleCohomology.systemPullbackId` — the canonical identification of the inverse image
  along an identity transition with the identity functor on sheaves: the left-adjoint mate of
  `Stacks.EtaleCohomology.systemPushforwardId`.
* `Stacks.EtaleCohomology.HasSheafIdentityLaw` — **the sheaf-level identity law** for a system
  of sheaves on an inverse system of schemes: the map attached to an identity index is that
  identification. A hypothesis on a system, never a field of the structure.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comparison_eq_self` — for a morphism
  `g : X ⟶ X` whose base change on the small étale site is isomorphic to the identity functor,
  restriction along `g` followed by the canonical comparison `g^{-1}ℱ ≅ ℱ` is the identity on
  `H^n(X, ℱ)`, for *every* abelian sheaf `ℱ`. This is the generalisation to an arbitrary sheaf of
  the step of the baffling theorem
  `Stacks.EtaleCohomology.absoluteFrobenius_etaleCohomologyRestrictionMap_eq_id`, which states it
  for the constant sheaf, and like it is proved from
  `Stacks.Homology.ext_mapExactFunctor_of_isoId`.
* `Stacks.EtaleCohomology.hasSheafIdentityLaw_directImageSystem` — **the instance that matters**:
  the system of direct images satisfies the sheaf-level identity law.
* `hasCohomologyIdentityLaw_of_hasSheafIdentityLaw` (in the namespace
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology`) — **the transport**: a presented system
  whose underlying system satisfies the sheaf-level identity law satisfies the identity law on
  cohomology, in every degree.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.hasCohomologyIdentityLaw_directImageSystem`
  — the two combined, at the presented system
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.presentedSystemOfIsColimitPresentation`
  built on the direct-image system.

## Implementation notes

**Why this spelling of the sheaf-level law.** The three identifications of the inverse image
along an identity transition with the identity functor that this development has — the mate
`systemPullbackId` of `systemPushforwardId`, taken along
`Stacks.EtaleCohomology.systemAdjunction`, which is the adjunction the system carries its
transitions along; `Stacks.EtaleCohomology.etaleSheafPullbackComparison`, taken along the
*constructed* inverse image, which is the functor the restriction map on cohomology is built
from; and `Stacks.EtaleCohomology.systemPullbackIsoInverseImage`, the comparison of the two
inverse images — are all `CategoryTheory.Adjunction.leftAdjointUniq` isomorphisms of left
adjoints of one and the same functor `systemPushforward D A (𝟙 i)`. So
`systemPullbackIsoInverseImage_hom_comp_etaleSheafPullbackComparison_hom_app` is
`CategoryTheory.Adjunction.leftAdjointUniq_trans_app` and nothing more, and the law may be
stated at `systemPullbackId` — the form in which `directImageSystem_map_id` proves it, up to
the adjunction — while the transport reads it at `etaleSheafPullbackComparison`, the form in
which the generalised baffling step consumes it. No transport lemma beyond that triangle is
needed.

That the two pushforward identifications agree is not an extra step either:
`etaleSheafPushforwardComparison X g e A` is by definition the inverse of
`CategoryTheory.Functor.sheafPushforwardContinuousId' e.symm`, and `systemPushforwardId D A i` is
`sheafPushforwardContinuousId'` of `Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf`, so taking
`e` to be the inverse of the latter makes them definitionally inverse to one another.

**The sheaf-level law is at arbitrary coefficients.** `HasSheafIdentityLaw` and
`hasSheafIdentityLaw_directImageSystem` are stated for a coefficient category `A : Type w` with
`Category.{w'} A`, as `EtaleSheafSystem` itself is; only the transport to cohomology specialises
to `AddCommGrpCat.{u + 1}`, where `Stacks.EtaleCohomology.etaleCohomologyTransition` lives.

**Universe names.** In the first section `v` is the coefficient universe parameter and `w` the
universe in which `Ext`-groups are computed, as in
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`; in the later sections `v` is the universe
of the index type and `w`, `w'` are the universes of the coefficient category, as in
`Stacks.EtaleCohomology.EtaleSheafSystem`. The two groups are declared in separate sections.

No `@[stacks]` attribute is placed: what is proved here is one input of the colimit statement of
[Stacks, Tag 09YQ], and the registration of that tag is assembled where its inputs are all
discharged.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 03SP](https://stacks.math.columbia.edu/tag/03SP)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

/-! ### Restriction along a morphism whose base change is the identity -/

section Comparison

universe u v w

/-- **Restriction along `g : X ⟶ X` is the identity on cohomology, for every sheaf**, as soon as
base change by `g` on the small étale site is isomorphic to the identity functor: the canonical
map on étale cohomology attached to `g`, followed by the canonical comparison `g^{-1}ℱ ≅ ℱ` of
`Stacks.EtaleCohomology.etaleSheafPullbackComparison`, sends every class of `H^n(X, ℱ)` to
itself.

For `ℱ` a constant sheaf and `g` the absolute Frobenius this is the baffling theorem
`Stacks.EtaleCohomology.absoluteFrobenius_etaleCohomologyRestrictionMap_eq_id`
([Stacks, Tag 03SN]); the proof is the same, the exactness of the inverse image making
`Stacks.Homology.ext_mapExactFunctor_of_isoId` applicable, and only the identification of the
comparison on the constant sheaf `ℤ` — `etaleAbelianInverseImageConstantIso_hom_app` — is needed
to see the two comparisons in the restriction map and in the statement as the components of one
isomorphism. -/
theorem etaleCohomologyRestrictionMap_comparison_eq_self {X : Scheme.{u}} (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (n : ℕ)
    (x : Sheaf.H.{w} F n) :
    Sheaf.H.map ((etaleSheafPullbackComparison.{u, v} X g e).hom.app F) n
        (etaleCohomologyRestrictionMap.{u, v, w} g F n x) = x := by
  let : IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _
  let : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    CategoryTheory.IsGrothendieckAbelian.enoughInjectives
  have hhom : ((etaleAbelianInverseImageConstantIso.{u, v} g).app
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).hom =
      ((etaleSheafPullbackComparison.{u, v} X g e).app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)))).hom :=
    etaleAbelianInverseImageConstantIso_hom_app.{u, v} g e
      (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))
  have hinv : ((etaleAbelianInverseImageConstantIso.{u, v} g).app
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).inv =
      (etaleSheafPullbackComparison.{u, v} X g e).inv.app _ :=
    congrArg Iso.inv (Iso.ext hhom)
  rw [Sheaf.H.map_apply, etaleCohomologyRestrictionMap_apply,
    Ext.comp_assoc_of_third_deg_zero, hinv]
  exact Stacks.Homology.ext_mapExactFunctor_of_isoId
    (etaleAbelianInverseImage.{u, v} g) (etaleSheafPullbackComparison.{u, v} X g e) _ n _ x

end Comparison

/-! ### The sheaf-level identity law -/

section SheafLaw

universe w' w v u

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- **The inverse image along an identity transition is the identity functor**: the left-adjoint
mate, along `Stacks.EtaleCohomology.systemAdjunction`, of the identification
`Stacks.EtaleCohomology.systemPushforwardId` of the direct image along that transition with the
identity functor. It is the canonical identification and not merely an isomorphism: it is pinned
by `homEquiv_systemPullbackId_hom_app`. -/
def systemPullbackId (i : Iᵒᵖ) : systemPullback D A (𝟙 i) ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq (systemAdjunction D A (𝟙 i))
    (Adjunction.id.ofNatIsoRight (systemPushforwardId D A i).symm)

/-- `Stacks.EtaleCohomology.systemPullbackId` is the mate of
`Stacks.EtaleCohomology.systemPushforwardId`: its transpose across the adjunction between the
inverse and direct images along an identity transition is the inverse of that identification.
This determines it uniquely, and it is the form in which
`Stacks.EtaleCohomology.directImageSystem_map_id` proves the identity law. -/
theorem homEquiv_systemPullbackId_hom_app (i : Iᵒᵖ)
    (S : Sheaf (smallEtaleTopology (D.obj i)) A) :
    (systemAdjunction D A (𝟙 i)).homEquiv _ _ ((systemPullbackId D A i).hom.app S) =
      (systemPushforwardId D A i).inv.app S := by
  rw [systemPullbackId, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp

/-- **The identity law for a system of sheaves, at the level of sheaves.** The map which a system
attaches to an identity index of the inverse system is the canonical identification
`Stacks.EtaleCohomology.systemPullbackId` of the inverse image along that transition with the
identity functor.

[Stacks, Tag 0EZL] does not impose this, following the source, which asks only for the cocycle
condition; and it must not be imposed, since
`SmallEtaleLimitCohomology.id_eq_zero_of_isIso_systemTransitionMap_zeroTransitionSystem` refutes it
for a legitimate system. It is a hypothesis on a system, and
`Stacks.EtaleCohomology.hasSheafIdentityLaw_directImageSystem` discharges it for the system of
direct images. -/
def HasSheafIdentityLaw (F : EtaleSheafSystem D A) : Prop :=
  ∀ i : Iᵒᵖ, F.map (𝟙 i) = (systemPullbackId D A i).hom.app (F.obj i)

variable (c : Cone D) (F : Sheaf (smallEtaleTopology c.pt) A)

/-- **The system of direct images satisfies the sheaf-level identity law.** This is
`Stacks.EtaleCohomology.directImageSystem_map_id`, which states it for the transposes across the
adjunction, read through the characterisation `homEquiv_systemPullbackId_hom_app` of the
canonical identification. -/
theorem hasSheafIdentityLaw_directImageSystem :
    HasSheafIdentityLaw D A (directImageSystem D A c F) := fun i =>
  ((systemAdjunction D A (𝟙 i)).homEquiv _ _).injective
    ((directImageSystem_map_id D A c F i).trans
      (homEquiv_systemPullbackId_hom_app D A i
        ((directImageSystem D A c F).obj i)).symm)

end SheafLaw

/-! ### The transport to cohomology -/

section Transport

universe v u

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]

/-- **The three canonical identifications fit in a triangle.** The comparison of the two inverse
images along an identity transition
(`Stacks.EtaleCohomology.systemPullbackIsoInverseImage`), followed by the identification of the
constructed inverse image with the identity functor
(`Stacks.EtaleCohomology.etaleSheafPullbackComparison`, at the inverse of
`Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf`), is the identification
`Stacks.EtaleCohomology.systemPullbackId` taken along the adjunction the system carries its
transitions along.

All three are isomorphisms of left adjoints of the one functor
`Stacks.EtaleCohomology.systemPushforward` at the identity transition, so this is
`CategoryTheory.Adjunction.leftAdjointUniq_trans_app`. -/
theorem systemPullbackIsoInverseImage_hom_comp_etaleSheafPullbackComparison_hom_app (i : Iᵒᵖ)
    (S : Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) :
    (systemPullbackIsoInverseImage D (𝟙 i)).hom.app S ≫
        (etaleSheafPullbackComparison.{u, u + 1} (D.obj i) (D.map (𝟙 i))
          (smallEtaleBaseChangeIdOf (D.map (𝟙 i)) (D.map_id i)).symm).hom.app S =
      (systemPullbackId D AddCommGrpCat.{u + 1} i).hom.app S :=
  Adjunction.leftAdjointUniq_trans_app _ _ _ S

variable [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]

/-- **The transition of a system along an identity index acts as the identity on cohomology**, as
soon as the system satisfies the sheaf-level identity law. The transition on cohomology is
restriction along `D.map (𝟙 i)` followed by the map the transition of the system induces, so
under the hypothesis it is the map of
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comparison_eq_self` at
`g = D.map (𝟙 i)`. -/
theorem etaleCohomologyTransition_id_apply (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (h : HasSheafIdentityLaw D AddCommGrpCat.{u + 1} F) (i : Iᵒᵖ) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (F.obj i) p) :
    etaleCohomologyTransition F (𝟙 i) p x = x := by
  have hw : systemTransitionMap F (𝟙 i) =
      (etaleSheafPullbackComparison.{u, u + 1} (D.obj i) (D.map (𝟙 i))
        (smallEtaleBaseChangeIdOf (D.map (𝟙 i)) (D.map_id i)).symm).hom.app (F.obj i) := by
    change (systemPullbackIsoInverseImage D (𝟙 i)).inv.app (F.obj i) ≫ F.map (𝟙 i) = _
    rw [h i,
      ← systemPullbackIsoInverseImage_hom_comp_etaleSheafPullbackComparison_hom_app D i (F.obj i),
      ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hx : etaleCohomologyTransition F (𝟙 i) p x =
      Sheaf.H.map (systemTransitionMap F (𝟙 i)) p
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (D.map (𝟙 i)) (F.obj i) p x) := rfl
  rw [hx, hw]
  exact etaleCohomologyRestrictionMap_comparison_eq_self.{u, u + 1, u + 1} (D.map (𝟙 i))
    (smallEtaleBaseChangeIdOf (D.map (𝟙 i)) (D.map_id i)).symm (F.obj i) p x

namespace SmallEtaleLimitCohomology

variable {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]

section General

variable {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}

/-- **The transport.** A presented system whose underlying system of sheaves satisfies the
sheaf-level identity law `Stacks.EtaleCohomology.HasSheafIdentityLaw` satisfies
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.HasCohomologyIdentityLaw`, in every degree.

This is the one extra input of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimit_levelCohomologyCocone`, the colimit
statement of [Stacks, Tag 09YQ] with the cohomology groups of the levels themselves as the
objects of the diagram. -/
theorem hasCohomologyIdentityLaw_of_hasSheafIdentityLaw (E : PresentedSystem P)
    (h : HasSheafIdentityLaw D AddCommGrpCat.{u + 1} E.sys) (p : ℕ) :
    HasCohomologyIdentityLaw E p :=
  fun i x => etaleCohomologyTransition_id_apply D E.sys h i p x

end General

/-- **The identity law on cohomology for the direct-image system.** A presented system built by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.presentedSystemOfIsColimitPresentation` on the
system of direct images of a sheaf along the projections of a cone satisfies the identity law on
cohomology in every degree: the sheaf-level law holds by
`Stacks.EtaleCohomology.hasSheafIdentityLaw_directImageSystem`, which is
[Stacks, Tag 0EYN] read at an identity index. -/
theorem hasCohomologyIdentityLaw_directImageSystem
    (𝓕 𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj
        ((directImageSystem D AddCommGrpCat.{u + 1} c 𝓕).obj i) ⟶ 𝒢)
    (hpres : IsColimitPresentation (c := c)
      (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝒢 ι) (p : ℕ) :
    HasCohomologyIdentityLaw
      (presentedSystemOfIsColimitPresentation
        (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝒢 ι hpres) p :=
  hasCohomologyIdentityLaw_of_hasSheafIdentityLaw D _
    (hasSheafIdentityLaw_directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) p

end SmallEtaleLimitCohomology

end Transport

end Stacks.EtaleCohomology

end
