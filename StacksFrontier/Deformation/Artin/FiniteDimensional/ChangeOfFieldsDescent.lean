module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.ChangeOfFields
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Morphism

/-!
# Finite-dimensionality descends along a finite extension of the residue field

For a deformation category `𝓕` over `𝒞_{Λ,k}` and a finite extension `l/k`, the tangent space and
the infinitesimal automorphisms of the change of residue field `𝓕_{l/k}` are the scalar
extensions to `l` of those of `𝓕` (Stacks 07WB and 07WC). So if they are finite-dimensional over
`l`, those of `𝓕` are finite-dimensional over `k`. This is the first reduction in the proof of
Stacks 07X1. The file also records that infinitesimal automorphisms transport backwards along a
faithful `1`-morphism (the argument of Stacks 06L8) and between the points of the special fibre
(Stacks 06JV (2)).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation

universe u v w y z u₁ v₁ u₂ v₂

section Descent

variable (S : ChangeOfFieldsSituation.{u, v, v})

/-- **The tangent space descends along a finite extension of the residue field** (Stacks 07WB):
if the tangent space of the change of residue field `𝓕_{l/k}` is finite-dimensional over `l`, then
that of `𝓕` is finite-dimensional over `k`. -/
theorem finiteDimensional_tangentModuleAt_of_changeOfFields
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (h𝓕 : IsDeformationCategory.{u, v, v} 𝓕.p)
    (h𝓖 : IsDeformationCategory.{u, v, v} (changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p))
    (hfin : FiniteDimensional S.l ↥(tangentModuleAt.{u, v, v}
      (BasedCategory.ofFunctor (changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p)) h𝓖
      (FGModuleCat.of S.l S.l))) :
    FiniteDimensional S.k ↥(tangentModuleAt.{u, v, v} 𝓕 h𝓕 (FGModuleCat.of S.k S.k)) := by
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, changeOfFieldsProjection S 𝓕.p⟩
  have hG := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt (𝓕 := 𝓖) h𝓖).mpr hfin
  refine (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt h𝓕).mp ?_
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (SchlessingerConditionS2 (Elements.π
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨tangentConditionS2.{u, v, v} h𝓕⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
  let : Fact (SchlessingerConditionS2 (Elements.π
      (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) := ⟨tangentConditionS2.{u, v, v} h𝓖⟩
  let : AddCommGroup (artinianTangentSpace S.Λ S.l
      (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered)) :=
    associatedTangentSpaceAddCommGroupUnlifted 𝓖
  let : Module S.l (artinianTangentSpace S.Λ S.l
      (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered)) :=
    associatedTangentSpaceModuleUnlifted 𝓖
  let : AddCommGroup (artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)) :=
    associatedTangentSpaceAddCommGroupUnlifted 𝓕
  let : Module S.k (artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)) :=
    associatedTangentSpaceModuleUnlifted 𝓕
  have : FiniteDimensional S.l (artinianTangentSpace S.Λ S.l
      (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered)) := hG
  let E := tangentSpaceChangeOfFields S 𝓕 h𝓕.predeformation (tangentConditionS2.{u, v, v} h𝓕)
  exact finiteDimensional_of_finiteDimensional_tensorProduct (l := S.l)
    (Module.Finite.equiv E.symm)

/-- **The infinitesimal automorphisms descend along a finite extension of the residue field**
(Stacks 07WC): if they are finite-dimensional over `l` at a point of the special fibre of the
change of residue field `𝓕_{l/k}`, then they are finite-dimensional over `k` at every point of the
special fibre of `𝓕`. -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_changeOfFields
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, v} S.Λ S.k) (hp : IsDeformationCategory p)
    (x₀ : p.Fiber (residueFieldObject.{u, v, v} S.Λ S.k))
    (P : ChosenPushforwardsAt p x₀.1)
    (xₗ : (changeOfFieldsProjection S p).Fiber (residueFieldObject.{u, v, v} S.Λ S.l))
    (Q : ChosenPushforwardsAt (changeOfFieldsProjection S p) xₗ.1)
    (hfin :
      letI := naturalLocalizedTangentAddCommGroup Q
        (changeOfFieldsProjection_satisfiesRS S p hp.satisfiesRS)
      letI := naturalLocalizedTangentModule Q
        (changeOfFieldsProjection_satisfiesRS S p hp.satisfiesRS)
      FiniteDimensional S.l (localizedAutomorphismFunctorTangent Q)) :
    letI := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
    letI := naturalLocalizedTangentModule P hp.satisfiesRS
    FiniteDimensional S.k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup Q
    (changeOfFieldsProjection_satisfiesRS S p hp.satisfiesRS)
  let := naturalLocalizedTangentModule Q
    (changeOfFieldsProjection_satisfiesRS S p hp.satisfiesRS)
  let := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
  let := naturalLocalizedTangentModule P hp.satisfiesRS
  obtain ⟨E, -⟩ := existsUnique_infinitesimalAutomorphismsChangeOfFields S p hp x₀ P xₗ Q
  exact finiteDimensional_of_finiteDimensional_tensorProduct (l := S.l)
    (Module.Finite.of_surjective (hM := hfin) E.symm.toLinearMap E.symm.surjective)

end Descent

section Transport

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Infinitesimal automorphisms transport backwards along a faithful `1`-morphism** (the
argument of Stacks 06L8, through Stacks 07W6): the induced linear map on infinitesimal
automorphisms is injective, the comparison of dual-number pushforwards being an isomorphism. -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful
    {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G] (Φ : F ⥤ G) [Φ.Faithful]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hw : Φ ⋙ q = p) (hp : SatisfiesRS p) (hq : SatisfiesRS q) {x₀ : F}
    (P : ChosenPushforwardsAt p x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀))
    (hfin :
      letI := naturalLocalizedTangentAddCommGroup Q hq
      letI := naturalLocalizedTangentModule Q hq
      FiniteDimensional k (localizedAutomorphismFunctorTangent Q)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup Q hq
  let := naturalLocalizedTangentModule Q hq
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  obtain ⟨T, H, hHlift, -, hconj⟩ := exists_inducedInfinitesimalLinearMap Φ hw hp hq P Q
  have hHiso : IsIso H := isIso_of_isHomLift_id hq.1 H hHlift
  have hTinj : Function.Injective T := by
    intro a b hab
    apply (localizedTangentEquivKernel P).injective
    apply Subtype.ext
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    apply Φ.map_injective
    have h1 := hconj a
    rw [hab] at h1
    exact (cancel_epi H).mp (h1.symm.trans (hconj b))
  have := hfin
  exact Module.Finite.of_injective T hTinj

/-- **Finite-dimensionality of the infinitesimal automorphisms does not depend on the point of the
special fibre nor on the chosen pushforwards** (Stacks 06JV (2)). -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_hom
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : SatisfiesRS p) {x x₀ : F} (j : x ⟶ x₀)
    (hbase : p.obj x₀ = residueFieldObject.{u, v, w} Λ k)
    (P : ChosenPushforwardsAt p x) (Q : ChosenPushforwardsAt p x₀)
    (hfin :
      letI := naturalLocalizedTangentAddCommGroup Q hp
      letI := naturalLocalizedTangentModule Q hp
      FiniteDimensional k (localizedAutomorphismFunctorTangent Q)) :
    letI := naturalLocalizedTangentAddCommGroup P hp
    letI := naturalLocalizedTangentModule P hp
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup Q hp
  let := naturalLocalizedTangentModule Q hp
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  have := hfin
  exact Module.Finite.equiv
    (canonicalLocalizedTangentAutomorphismLinearEquiv hp j hbase P Q).symm

/-- The lifted model of the infinitesimal automorphisms, the one
`Deformation.IsFiniteDimensionalDeformationCategory` speaks about, is finite-dimensional as soon
as the tangent space at the identity of the automorphism functor is. -/
theorem finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : SatisfiesRS p) {x : F} (P : ChosenPushforwardsAt p x)
    (hfin :
      letI := naturalLocalizedTangentAddCommGroup P hp
      letI := naturalLocalizedTangentModule P hp
      FiniteDimensional k (localizedAutomorphismFunctorTangent P)) :
    FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, v, w} P hp).functor.obj
      (FGModuleCat.of k (ULift.{v} k))) := by
  let := naturalLocalizedTangentAddCommGroup P hp
  let := naturalLocalizedTangentModule P hp
  have := hfin
  exact Module.Finite.equiv (tangentCarrierLinearEquiv.{u, v, w} P hp).symm

end Transport

end Deformation
