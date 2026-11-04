module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.PerfectIffStalkTorDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge

/-!
# Perfect morphisms and the relative Tor dimension of the structure sheaf

Let `f : X ⟶ S` be a morphism of schemes. Consider the conditions

1. `f` is perfect;
2. the structure sheaf `𝒪_X`, viewed as a sheaf of `f^{-1}𝒪_S`-modules, locally has finite Tor
   dimension on the inverse-image ringed space `(X, f^{-1}𝒪_S)`
   (`AlgebraicGeometry.Scheme.Hom.LocallyHasFiniteRelativeTorDimension`);
3. for every point `x` of `X` the local ring `𝒪_{X, x}` has finite Tor dimension as an
   `𝒪_{S, f x}`-module.

Condition (2) holds exactly when `X` has an open covering on each member of which one interval
bounds the Tor amplitude of the local rings over the local rings of the base. For any `f`,
(1) implies (2) and (2) implies (3); for `f` pseudo-coherent the three are equivalent.

## Main results

* `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_iff_exists_cover`:
  condition (2) holds, for a family of certificates pinned to the genuine tensor product, exactly
  when `X` has an open covering on each member of which the Tor amplitude of the local rings over
  the local rings of the base is bounded by one interval.
* `forall_hasFiniteTorDimensionCanonical_stalk_of_locallyHasFiniteRelativeTorDimension`, in the
  namespace `AlgebraicGeometry.Scheme.Hom`: condition (2) implies condition (3).
* `locallyHasFiniteRelativeTorDimension_of_forall_exists_uniform_bound`, in the same namespace:
  if every point has a neighbourhood on which one interval bounds the Tor amplitude of the local
  rings, then condition (2) holds.
* `locallyHasFiniteRelativeTorDimension_of_forall_affineOpen`, in the same namespace: if on every
  compatible pair of affine opens one interval bounds the Tor amplitude of the local rings, then
  condition (2) holds.
* `locallyHasFiniteRelativeTorDimension_of_perfect`, in the same namespace: condition (1) implies
  condition (2).
* `locallyHasFiniteRelativeTorDimension_canonical_of_perfect`, in the same namespace: condition
  (1) implies condition (2) at the canonical family of certificates.
* `locallyHasFiniteRelativeTorDimension_canonical_iff`, in the same namespace: at the canonical
  family, condition (2) is `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`.
* `AlgebraicGeometry.perfect_tfae`: for a pseudo-coherent morphism the three conditions are
  equivalent, with condition (2) read at the derived tensor product.

## References

* [Stacks Project, Lemma 37.61.11 (Tag 069C)](https://stacks.math.columbia.edu/tag/069C)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Lemma 15.68.19 (Tag 0B67)](https://stacks.math.columbia.edu/tag/0B67)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a family of certificates pinned to the genuine tensor product of sheaves of modules,
`𝒪_X` locally has finite Tor dimension as a sheaf of `f^{-1}𝒪_S`-modules exactly when `X` has an
open covering on each member `U` of which there is a single interval `[a, b]` containing the Tor
amplitude of `𝒪_{X, y}` over `𝒪_{S, f y}` for every `y ∈ U`. -/
theorem locallyHasFiniteRelativeTorDimension_iff_exists_cover
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D) :
    LocallyHasFiniteRelativeTorDimension f D ↔
      ∃ (I : Type u) (U : I → TopologicalSpace.Opens
          (RingedSpace.inverseImage S.toRingedSpace f.base).carrier),
        iSup U = ⊤ ∧ ∀ i : I, ∃ a b : ℤ, ∀ y : X, y ∈ U i →
          letI : Algebra (ToType (S.presheaf.stalk (f.base y))) (ToType (X.presheaf.stalk y)) :=
            (f.stalkMap y).hom.toAlgebra
          HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base y)))
            ((DerivedCategory.singleFunctor
                (ModuleCat.{u} (ToType (S.presheaf.stalk (f.base y)))) 0).obj
              (ModuleCat.of (ToType (S.presheaf.stalk (f.base y)))
                (ToType (X.presheaf.stalk y)))) a b := by
  refine Iff.trans (RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq _ D hD _) ?_
  refine exists_congr fun I => exists_congr fun U => and_congr_right fun _ =>
    forall_congr' fun i => exists_congr fun a => exists_congr fun b => ?_
  refine (Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk
    _ (U i) _ a b).trans ?_
  exact forall₂_congr fun y _ => hasTorAmplitudeCanonical_stalk_relative_iff f y a b

/-- If `𝒪_X` locally has finite Tor dimension as a sheaf of `f^{-1}𝒪_S`-modules, read at a
family of certificates pinned to the genuine tensor product, then for every point `x` of `X` the
local ring `𝒪_{X, x}` has finite Tor dimension as an `𝒪_{S, f x}`-module through the stalk map
of `f`. -/
theorem forall_hasFiniteTorDimensionCanonical_stalk_of_locallyHasFiniteRelativeTorDimension
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (h : LocallyHasFiniteRelativeTorDimension f D) :
    ∀ x : X,
      let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      HasFiniteTorDimensionCanonical (S.presheaf.stalk (f.base x))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (S.presheaf.stalk (f.base x))) 0).obj
          (ModuleCat.of (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x))) := by
  obtain ⟨I, U, hUtop, hbound⟩ :=
    (locallyHasFiniteRelativeTorDimension_iff_exists_cover f D hD).mp h
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i :=
    TopologicalSpace.Opens.mem_iSup.mp (show x ∈ iSup U from by rw [hUtop]; trivial)
  obtain ⟨a, b, hamp⟩ := hbound i
  exact (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).mpr
    ⟨a, b, hamp x hi⟩

/-- If every point of `X` has an open neighbourhood on which one interval contains the Tor
amplitude of `𝒪_{X, y}` over `𝒪_{S, f y}` for every point `y` of that neighbourhood, then `𝒪_X`
locally has finite Tor dimension as a sheaf of `f^{-1}𝒪_S`-modules, for every family of
certificates pinned to the genuine tensor product. -/
theorem locallyHasFiniteRelativeTorDimension_of_forall_exists_uniform_bound
    (h : ∀ x : X, ∃ (U : TopologicalSpace.Opens
          (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) (_ : x ∈ U) (a b : ℤ),
        ∀ y : X, y ∈ U →
          letI : Algebra (ToType (S.presheaf.stalk (f.base y))) (ToType (X.presheaf.stalk y)) :=
            (f.stalkMap y).hom.toAlgebra
          HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base y)))
            ((DerivedCategory.singleFunctor
                (ModuleCat.{u} (ToType (S.presheaf.stalk (f.base y)))) 0).obj
              (ModuleCat.of (ToType (S.presheaf.stalk (f.base y)))
                (ToType (X.presheaf.stalk y)))) a b)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D) :
    LocallyHasFiniteRelativeTorDimension f D := by
  choose U hU a b hamp using h
  exact (locallyHasFiniteRelativeTorDimension_iff_exists_cover f D hD).mpr
    ⟨X, U, eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hU z⟩,
      fun z => ⟨a z, b z, hamp z⟩⟩

/-- If on every compatible pair of affine opens `U ≤ f ⁻¹ᵁ V` one interval contains the Tor
amplitude of `𝒪_{X, y}` over `𝒪_{S, f y}` for every point `y` of `U`, then `𝒪_X` locally has
finite Tor dimension as a sheaf of `f^{-1}𝒪_S`-modules, for every family of certificates pinned
to the genuine tensor product. -/
theorem locallyHasFiniteRelativeTorDimension_of_forall_affineOpen
    (hchart : ∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V → U ≤ f ⁻¹ᵁ V →
      ∃ a b : ℤ, ∀ y : X, y ∈ U →
        letI : Algebra (ToType (S.presheaf.stalk (f.base y))) (ToType (X.presheaf.stalk y)) :=
          (f.stalkMap y).hom.toAlgebra
        HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base y)))
          ((DerivedCategory.singleFunctor
              (ModuleCat.{u} (ToType (S.presheaf.stalk (f.base y)))) 0).obj
            (ModuleCat.of (ToType (S.presheaf.stalk (f.base y)))
              (ToType (X.presheaf.stalk y)))) a b)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D) :
    LocallyHasFiniteRelativeTorDimension f D := by
  refine locallyHasFiniteRelativeTorDimension_of_forall_exists_uniform_bound f (fun x => ?_) D hD
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxV (f ⁻¹ᵁ V).2
  obtain ⟨a, b, hamp⟩ := hchart U hU V hV hUV
  exact ⟨U, hxU, a, b, hamp⟩

/-- A perfect morphism of schemes `f : X ⟶ S` has `𝒪_X` locally of finite Tor dimension as a
sheaf of `f^{-1}𝒪_S`-modules, for every family of certificates pinned to the genuine tensor
product. -/
theorem locallyHasFiniteRelativeTorDimension_of_perfect [Perfect f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D) :
    LocallyHasFiniteRelativeTorDimension f D :=
  locallyHasFiniteRelativeTorDimension_of_forall_affineOpen f
    (fun U hU V hV hUV =>
      AlgebraicGeometry.Perfect.exists_hasTorAmplitudeCanonical_stalk_of_affineOpen
        f U hU V hV hUV)
    D hD

/-- A perfect morphism of schemes `f : X ⟶ S` has `𝒪_X` locally of finite Tor dimension as a
sheaf of `f^{-1}𝒪_S`-modules, read at the canonical family of certificates
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`. -/
theorem locallyHasFiniteRelativeTorDimension_canonical_of_perfect [Perfect f] :
    LocallyHasFiniteRelativeTorDimension f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) :=
  locallyHasFiniteRelativeTorDimension_of_perfect f _
    (isGenuineRelativeTensorFamily_canonical f)

/-- At the canonical family of certificates, `𝒪_X` locally has finite relative Tor dimension
exactly when the restriction of scalars of `𝒪_X[0]` along `f^{-1}𝒪_S ⟶ 𝒪_X` locally has finite
Tor dimension on the inverse-image ringed space `(X, f^{-1}𝒪_S)`, read at the derived tensor
product on each open subspace. -/
theorem locallyHasFiniteRelativeTorDimension_canonical_iff :
    LocallyHasFiniteRelativeTorDimension f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) ↔
      Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension
        (RingedSpace.inverseImage S.toRingedSpace f.base)
        ((derivedScalarRestriction f).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
            (structureModule X.toRingedSpace))) :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

open Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

/-- Let `f : X ⟶ S` be a pseudo-coherent morphism of schemes. The following are equivalent:
1. `f` is perfect;
2. `𝒪_X` locally has finite Tor dimension as a sheaf of `f^{-1}𝒪_S`-modules, that is, the
   restriction of scalars of `𝒪_X[0]` along `f^{-1}𝒪_S ⟶ 𝒪_X` locally has finite Tor dimension
   on the inverse-image ringed space `(X, f^{-1}𝒪_S)`, at the derived tensor product;
3. for every `x ∈ X` the local ring `𝒪_{X, x}` has finite Tor dimension as an
   `𝒪_{S, f x}`-module through the stalk map of `f`. -/
@[stacks 069C]
theorem perfect_tfae {X S : Scheme.{u}} (f : X ⟶ S) [PseudoCoherent f] :
    List.TFAE
      [Perfect f,
        Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension
          (RingedSpace.inverseImage S.toRingedSpace f.base)
          ((derivedScalarRestriction f).obj
            ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
              (structureModule X.toRingedSpace))),
        ∀ x : X,
          let _ : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
            (f.stalkMap x).hom.toAlgebra
          HasFiniteTorDimensionCanonical (S.presheaf.stalk (f.base x))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} (S.presheaf.stalk (f.base x))) 0).obj
              (ModuleCat.of (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)))] := by
  tfae_have 1 → 2 := fun _ =>
    (locallyHasFiniteRelativeTorDimension_canonical_iff f).mp
      (locallyHasFiniteRelativeTorDimension_canonical_of_perfect f)
  tfae_have 2 → 3 := fun h =>
    forall_hasFiniteTorDimensionCanonical_stalk_of_locallyHasFiniteRelativeTorDimension f _
      (isGenuineRelativeTensorFamily_canonical f)
      ((locallyHasFiniteRelativeTorDimension_canonical_iff f).mpr h)
  tfae_have 3 → 1 := perfect_of_forall_hasFiniteTorDimensionCanonical_stalk f
  tfae_finish

end AlgebraicGeometry

end
