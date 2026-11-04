module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumMap
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumStalks

/-!
# The formal spectrum of a continuous ring map as a morphism of `LTRS`

For a continuous homomorphism `φ : A → B` of pre-admissible topological rings the morphism
`Spf φ : Spf B → Spf A` of presheafed spaces of topological rings is a local homomorphism on
stalks, so it is a morphism of the category `LTRS` of locally topologically ringed spaces.

## Main definitions

* `AlgebraicGeometry.spfComponentSpaceMap`: for ideals of definition `I` of `A` and `J` of `B`
  with `I ⊆ φ⁻¹(J)`, the morphism `(Spf B, 𝒪^B_J) → (Spf A, 𝒪^A_I)` of presheafed spaces of
  rings induced by `φ`, and `AlgebraicGeometry.spfComponentSpaceMapPseudoDiscrete` its
  pseudo-discretisation.
* `AlgebraicGeometry.spfMapLTRS`: the morphism `Spf φ : Spf B → Spf A` of locally topologically
  ringed spaces.

## Main results

* `AlgebraicGeometry.isLocalHom_stalkMap_spfComponentSpaceMap`: the induced morphism of the
  terms of the two inverse systems is a local homomorphism on stalks, being induced by the
  morphism of schemes `Spec (B/J) → Spec (A/I)`.
* `AlgebraicGeometry.spfMapC_comp_spfProjection`: the comparison map of `Spf φ` followed by the
  projection of `𝒪_{Spf B}` onto `𝒪^B_J` is the projection of `𝒪_{Spf A}` onto
  `𝒪^A_{I₀ ⊓ φ⁻¹(J)}` followed by the induced map of those terms.
* `AlgebraicGeometry.isLocalHom_stalkMap_spfMap`: the stalk maps of `Spf φ` are local
  homomorphisms.

## Implementation notes

Locality of the stalk maps of `Spf φ` is reduced to the terms of the inverse systems rather than
computed in the limit `𝒪_{Spf A} = lim 𝒪_λ`. A germ of `𝒪_{Spf A}` is invertible as soon as its
image in one term is, by `AlgebraicGeometry.isLocalHom_spfProjectionOn_stalk`; and the induced map
of terms is a local homomorphism on stalks for free, because it comes from a morphism of schemes
`Spec (B/J) → Spec (A/I)`, whose stalk maps are local by
`AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap`. So neither completeness, nor
nilpotence, nor a comparison of residue fields is needed, exactly as for the locality of the
stalks themselves.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

open TopologicalRing

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {φ : A →+* B} (hφ : Continuous φ)

/-! ### The induced morphism of the terms of the inverse systems -/

/-- For ideals of definition `I` of `A` and `J` of `B` with `I ⊆ φ⁻¹(J)`, the morphism
`(Spf B, 𝒪^B_J) → (Spf A, 𝒪^A_I)` of presheafed spaces of rings induced by `φ`: on points it is
`q ↦ φ⁻¹(q)` and on sections it is `AlgebraicGeometry.spfComponentMap`. -/
noncomputable def spfComponentSpaceMap (J : IdealsOfDefinition B) (I : IdealsOfDefinition A)
    (hI : I.1 ≤ Ideal.comap φ J.1) :
    spfComponentSpace B J ⟶ spfComponentSpace A I where
  base := spfMapBase A B hφ
  c := spfComponentMap A B hφ J I hI

/-- The identification of `Spec (B/J)` with `(Spf B, 𝒪^B_J)` followed by the induced morphism of
terms is the morphism of schemes `Spec (B/J) → Spec (A/I)` followed by the identification of
`Spec (A/I)` with `(Spf A, 𝒪^A_I)`: the square of spectra commutes definitionally, because
`A/I → B/J` precomposed with `A → A/I` is `A → B → B/J`. -/
theorem spfComponentHom_comp_spfComponentSpaceMap (J : IdealsOfDefinition B)
    (I : IdealsOfDefinition A) (hI : I.1 ≤ Ideal.comap φ J.1) :
    spfComponentHom B J ≫ spfComponentSpaceMap A B hφ J I hI
      = (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J.1 φ hI))).toLRSHom.toHom
          ≫ spfComponentHom A I :=
  PresheafedSpace.ext _ _ rfl (NatTrans.ext (funext fun _ => rfl))

/-- The induced morphism of the terms of the two inverse systems is a local homomorphism on
stalks: it comes from the morphism of schemes `Spec (B/J) → Spec (A/I)`, whose stalk maps are
local, and from the identifications of the `Spec (A/I)` with the space of open primes, which are
isomorphisms on stalks. -/
theorem isLocalHom_stalkMap_spfComponentSpaceMap (J : IdealsOfDefinition B)
    (I : IdealsOfDefinition A) (hI : I.1 ≤ Ideal.comap φ J.1) (y : spfSpace B) :
    IsLocalHom ((spfComponentSpaceMap A B hφ J I hI).stalkMap y).hom := by
  obtain ⟨q, rfl⟩ := surjective_spfOfQuotientOn B J y
  have hcomp : IsLocalHom
      ((spfComponentHomOn B J ≫ spfComponentSpaceMap A B hφ J I hI).stalkMap q).hom := by
    rw [spfComponentHom_comp_spfComponentSpaceMap, PresheafedSpace.stalkMap.comp]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _
      (LocallyRingedSpace.isLocalHomStalkMap
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J.1 φ hI))).toLRSHom q)
      (isLocalHom_stalkMap_spfComponentHomOn A I _)
  rw [PresheafedSpace.stalkMap.comp] at hcomp
  exact @isLocalHom_of_comp _ _ _ _ _ _
    ((spfComponentSpaceMap A B hφ J I hI).stalkMap (spfOfQuotientOn B J q)).hom
    ((spfComponentHomOn B J).stalkMap q).hom hcomp

variable (hA : IsPreAdmissible A)

/-- The pseudo-discretisation of `AlgebraicGeometry.spfComponentSpaceMap`: the same morphism of
presheafed spaces, read with the pseudo-discrete topologies on all rings of sections. -/
noncomputable def spfComponentSpaceMapPseudoDiscrete (J : IdealsOfDefinition B)
    (I : IdealsOfDefinition A) (hI : I.1 ≤ Ideal.comap φ J.1) :
    pseudoDiscreteSpace (spfComponentSpace B J) ⟶ pseudoDiscreteSpace (spfComponentSpace A I) :=
  letI := prespectralSpace_spfSpace_of_isWeaklyPreAdmissible A
    (isWeaklyPreAdmissible_of_isPreAdmissible hA)
  { base := spfMapBase A B hφ
    c := pseudoDiscretePushforward (spfMapBase A B hφ) (spfComponentMap A B hφ J I hI) }

/-- Forgetting the pseudo-discrete topologies returns
`AlgebraicGeometry.spfComponentSpaceMap`. -/
theorem forgetPseudoDiscreteHom_spfComponentSpaceMapPseudoDiscrete (J : IdealsOfDefinition B)
    (I : IdealsOfDefinition A) (hI : I.1 ≤ Ideal.comap φ J.1) :
    forgetPseudoDiscreteHom (spfComponentSpaceMapPseudoDiscrete A B hφ hA J I hI)
      = spfComponentSpaceMap A B hφ J I hI :=
  PresheafedSpace.ext _ _ rfl (NatTrans.ext (funext fun _ => rfl))

/-- The pseudo-discretised induced morphism of terms is a local homomorphism on stalks, the
pseudo-discrete topologies leaving the stalks of the underlying presheaves of rings
unchanged. -/
theorem isLocalHom_stalkMap_spfComponentSpaceMapPseudoDiscrete (J : IdealsOfDefinition B)
    (I : IdealsOfDefinition A) (hI : I.1 ≤ Ideal.comap φ J.1) (y : spfSpace B) :
    IsLocalHom ((spfComponentSpaceMapPseudoDiscrete A B hφ hA J I hI).stalkMap y).1 :=
  (isLocalHom_stalkMap_iff (spfComponentSpaceMapPseudoDiscrete A B hφ hA J I hI) y).2
    (by rw [forgetPseudoDiscreteHom_spfComponentSpaceMapPseudoDiscrete]
        exact isLocalHom_stalkMap_spfComponentSpaceMap A B hφ J I hI y)

/-! ### Locality of the stalk maps of `Spf φ` -/

variable (I₀ : IdealsOfDefinition A)

/-- The comparison map of `Spf φ`, followed by the projection of `𝒪_{Spf B}` onto the term
`𝒪^B_J`, is the projection of `𝒪_{Spf A}` onto `𝒪^A_{I₀ ⊓ φ⁻¹(J)}` followed by the induced map
of those terms. This is the defining property of `AlgebraicGeometry.spfMapC` as a map of
limits. -/
theorem spfMapC_comp_spfProjection (J : IdealsOfDefinition B) :
    spfMapC A B hφ I₀ hA
        ≫ Functor.whiskerLeft (Opens.map (spfMapBase A B hφ)).op (spfProjection B J)
      = spfProjection A (spfPullbackIdeal A B hφ I₀ J)
          ≫ (spfComponentSpaceMapPseudoDiscrete A B hφ hA J
              (spfPullbackIdeal A B hφ I₀ J) (spfPullbackIdeal_le A B hφ I₀ J)).c := by
  let _ := prespectralSpace_spfSpace_of_isWeaklyPreAdmissible A
    (isWeaklyPreAdmissible_of_isPreAdmissible hA)
  let _ : PreservesLimitsOfShape (IdealsOfDefinition B)
      (TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ)) :=
    whiskeringLeft_preservesLimitsOfShape (IdealsOfDefinition B)
      (Opens.map (spfMapBase A B hφ)).op
  show (spfLimitMap A B hφ I₀ hA
        ≫ (preservesLimitIso
            (TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ))
            (spfDiagram B ⋙ pseudoDiscreteFunctor)).inv)
      ≫ (TopCat.Presheaf.pushforward TopCommRingCat.{u} (spfMapBase A B hφ)).map
          (limit.π (spfDiagram B ⋙ pseudoDiscreteFunctor) J)
    = limit.π (spfDiagram A ⋙ pseudoDiscreteFunctor)
        ((spfPullbackFunctor A B hφ I₀).obj J)
      ≫ (spfDiagramMap A B hφ I₀ hA).app J
  rw [Category.assoc, preservesLimitIso_inv_π, spfLimitMap, Category.assoc, limMap_π,
    ← Category.assoc, limit.pre_π]

/-- Sectionwise form of `AlgebraicGeometry.spfMapC_comp_spfProjection`: on a section `s` of
`𝒪_{Spf A}` over `V`, projecting the image under `Spf φ` to `𝒪^B_J` agrees with projecting `s`
to `𝒪^A_{I₀ ⊓ φ⁻¹(J)}` and applying the induced map of terms. -/
theorem spfMapC_app_spfProjectionOn_apply (J : IdealsOfDefinition B) (V : Opens (spfSpace A))
    (s : (spfPresheaf A).obj (op V)) :
    ((spfProjectionOn B J).app (op ((Opens.map (spfMapBase A B hφ)).obj V))).1
        (((spfMapC A B hφ I₀ hA).app (op V)).1 s)
      = (((spfComponentSpaceMapPseudoDiscrete A B hφ hA J (spfPullbackIdeal A B hφ I₀ J)
            (spfPullbackIdeal_le A B hφ I₀ J)).c).app (op V)).1
          (((spfProjectionOn A (spfPullbackIdeal A B hφ I₀ J)).app (op V)).1 s) :=
  congrArg (fun k : (spfPresheaf A).obj (op V) ⟶ (pseudoDiscrete (spfComponentOn B J)).obj
      (op ((Opens.map (spfMapBase A B hφ)).obj V)) => k.1 s)
    (congrFun (congrArg NatTrans.app (spfMapC_comp_spfProjection A B hφ hA I₀ J)) (op V))

/-- Taking stalks, the comparison map of `Spf φ` followed by the projection onto the stalk of
`𝒪^B_J` is the projection onto the stalk of `𝒪^A_{I₀ ⊓ φ⁻¹(J)}` followed by the stalk map of the
induced morphism of terms. -/
theorem spfProjection_stalk_stalkMap_spfMap (J : IdealsOfDefinition B) (y : spfSpace B)
    (a : ((spfPresheaf A).stalk ((spfMapBase A B hφ) y)).α) :
    ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} y).map (spfProjection B J)).1
        (((spfMap A B hφ I₀ hA).stalkMap y).1 a)
      = ((spfComponentSpaceMapPseudoDiscrete A B hφ hA J (spfPullbackIdeal A B hφ I₀ J)
            (spfPullbackIdeal_le A B hφ I₀ J)).stalkMap y).1
          (((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} ((spfMapBase A B hφ) y)).map
              (spfProjection A (spfPullbackIdeal A B hφ I₀ J))).1 a) := by
  have : PreservesFilteredColimits (forget TopCommRingCat.{u}) :=
    (HasForget₂.forget_comp (C := TopCommRingCat.{u}) (D := CommRingCat.{u})) ▸
      (inferInstance : PreservesFilteredColimits
        (forget₂ TopCommRingCat.{u} CommRingCat.{u} ⋙ forget CommRingCat.{u}))
  obtain ⟨V, hxV, s, rfl⟩ := (spfPresheaf A).exists_germ_eq a
  have h1 : ((spfMap A B hφ I₀ hA).stalkMap y).1
        ((spfPresheaf A).germ V ((spfMapBase A B hφ) y) hxV s)
      = (spfPresheaf B).germ ((Opens.map (spfMapBase A B hφ)).obj V) y hxV
          (((spfMapC A B hφ I₀ hA).app (op V)).1 s) :=
    PresheafedSpace.stalkMap_germ_apply (spfMap A B hφ I₀ hA) V y hxV s
  have h2 : ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} y).map (spfProjectionOn B J)).1
        ((spfPresheaf B).germ ((Opens.map (spfMapBase A B hφ)).obj V) y hxV
          (((spfMapC A B hφ I₀ hA).app (op V)).1 s))
      = (pseudoDiscrete (spfComponentOn B J)).germ
          ((Opens.map (spfMapBase A B hφ)).obj V) y hxV
          (((spfProjectionOn B J).app (op ((Opens.map (spfMapBase A B hφ)).obj V))).1
            (((spfMapC A B hφ I₀ hA).app (op V)).1 s)) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply
      ((Opens.map (spfMapBase A B hφ)).obj V) y hxV (spfProjectionOn B J) _
  have h3 : ((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} ((spfMapBase A B hφ) y)).map
          (spfProjectionOn A (spfPullbackIdeal A B hφ I₀ J))).1
        ((spfPresheaf A).germ V ((spfMapBase A B hφ) y) hxV s)
      = (pseudoDiscrete (spfComponentOn A (spfPullbackIdeal A B hφ I₀ J))).germ V
          ((spfMapBase A B hφ) y) hxV
          (((spfProjectionOn A (spfPullbackIdeal A B hφ I₀ J)).app (op V)).1 s) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V ((spfMapBase A B hφ) y) hxV
      (spfProjectionOn A (spfPullbackIdeal A B hφ I₀ J)) s
  have h4 : ((spfComponentSpaceMapPseudoDiscrete A B hφ hA J (spfPullbackIdeal A B hφ I₀ J)
          (spfPullbackIdeal_le A B hφ I₀ J)).stalkMap y).1
        ((pseudoDiscrete (spfComponentOn A (spfPullbackIdeal A B hφ I₀ J))).germ V
          ((spfMapBase A B hφ) y) hxV
          (((spfProjectionOn A (spfPullbackIdeal A B hφ I₀ J)).app (op V)).1 s))
      = (pseudoDiscrete (spfComponentOn B J)).germ
          ((Opens.map (spfMapBase A B hφ)).obj V) y hxV
          ((((spfComponentSpaceMapPseudoDiscrete A B hφ hA J (spfPullbackIdeal A B hφ I₀ J)
              (spfPullbackIdeal_le A B hφ I₀ J)).c).app (op V)).1
            (((spfProjectionOn A (spfPullbackIdeal A B hφ I₀ J)).app (op V)).1 s)) :=
    PresheafedSpace.stalkMap_germ_apply (spfComponentSpaceMapPseudoDiscrete A B hφ hA J
      (spfPullbackIdeal A B hφ I₀ J) (spfPullbackIdeal_le A B hφ I₀ J)) V y hxV _
  rw [h3, h4, h1, h2, spfMapC_app_spfProjectionOn_apply A B hφ hA I₀ J V s]

variable (hB : IsPreAdmissible B)

include hB in
/-- The stalk maps of `Spf φ` are local homomorphisms: a germ of `𝒪_{Spf A}` is invertible as
soon as its image in one term `𝒪^A_λ` is, and the induced map from that term to `𝒪^B_J` is a
local homomorphism on stalks because it comes from a morphism of schemes. -/
theorem isLocalHom_stalkMap_spfMap (y : spfSpace B) :
    IsLocalHom ((spfMap A B hφ I₀ hA).stalkMap y).1 := by
  obtain ⟨J₀, hJ₀⟩ := hB
  refine ⟨fun a ha => ?_⟩
  have hunit : IsUnit (((TopCat.Presheaf.stalkFunctor TopCommRingCat.{u} y).map
      (spfProjectionOn B ⟨J₀, hJ₀⟩)).1 (((spfMap A B hφ I₀ hA).stalkMap y).1 a)) :=
    RingHom.isUnit_map _ ha
  rw [spfProjection_stalk_stalkMap_spfMap A B hφ hA I₀ ⟨J₀, hJ₀⟩ y a] at hunit
  exact (isLocalHom_spfProjectionOn_stalk A (spfPullbackIdeal A B hφ I₀ ⟨J₀, hJ₀⟩) _).map_nonunit _
    ((isLocalHom_stalkMap_spfComponentSpaceMapPseudoDiscrete A B hφ hA ⟨J₀, hJ₀⟩
      (spfPullbackIdeal A B hφ I₀ ⟨J₀, hJ₀⟩)
      (spfPullbackIdeal_le A B hφ I₀ ⟨J₀, hJ₀⟩) y).map_nonunit _ hunit)

/-- `Spf` on morphisms, as a morphism of locally topologically ringed spaces: the formal
spectrum of a continuous ring map `φ : A → B` between pre-admissible topological rings, viewed
as a morphism `Spf B → Spf A` of `LTRS`. -/
noncomputable def spfMapLTRS : spfLTRS B hB ⟶ spfLTRS A hA where
  toHom := spfMap A B hφ I₀ hA
  isLocalHom := isLocalHom_stalkMap_spfMap A B hφ hA I₀ hB

/-- The morphism of presheafed spaces underlying `Spf φ` as a morphism of `LTRS` is
`AlgebraicGeometry.spfMap`. -/
@[simp]
theorem spfMapLTRS_toHom :
    (spfMapLTRS A B hφ hA I₀ hB).toHom = spfMap A B hφ I₀ hA := rfl

/-- `Spf φ` as a morphism of `LTRS` does not depend on the chosen ideal of definition `I₀` of
`A`, so it is canonically attached to the continuous ring map `φ`. -/
theorem spfMapLTRS_eq (I₀' : IdealsOfDefinition A) :
    spfMapLTRS A B hφ hA I₀ hB = spfMapLTRS A B hφ hA I₀' hB :=
  LocallyTopologicallyRingedSpace.Hom.ext' (spfMap_eq A B hφ hA I₀ I₀')

end

end AlgebraicGeometry
