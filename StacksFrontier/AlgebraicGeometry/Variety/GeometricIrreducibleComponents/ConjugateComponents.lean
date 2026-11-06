module

public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.GaloisOrbit
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Conjugacy of the irreducible components lying over a fixed component

Let `X` be a scheme over a field `k` and let `K/k` be an extension of fields. Two irreducible
components of the base change `X_K` with the same image in `X` are *conjugate*: there is an
automorphism of `X_K` over `X` carrying one onto the other. This file proves that, and exhibits
the hypothesis on `K/k` that it needs.

## Main results

* `AlgebraicGeometry.exists_algEquiv_image_eq_of_irreducibleComponentsBaseChangeMap_eq`: for a
  normal extension `K/k`, two irreducible components of `X_K` whose images in `X` agree are
  carried onto one another by the automorphism of `X_K` induced by some `σ : K ≃ₐ[k] K`.
* `AlgebraicGeometry.bijOn_image_baseChangeComparison`: for a tower `k ⊆ E ⊆ K` with `E`
  separably closed in `K`, the comparison map `X_K ⟶ X_E` is a bijection on irreducible
  components. Taking `E` to be the separable closure of `k` in `K` reduces an arbitrary
  extension to a separable algebraic one.
* `AlgebraicGeometry.exists_algEquiv_image_baseChangeComparison_eq`: for an arbitrary extension
  `K/k` whose separable part `E` is normal over `k`, two irreducible components of `X_K` with
  the same image in `X` have conjugate images in `X_E`.

## Which hypothesis on `K/k` is needed, and why

Write `E` for the separable closure of `k` in `K`, that is, `separableClosure k K`.

The components of `X_K` over a fixed component with generic point `η` are the minimal primes of
`κ(η) ⊗[k] K` (Tag 04KY and its affine input Tag 04KP), and conjugacy is transitivity of
`K ≃ₐ[k] K` on those primes. **Normality of `E/k` cannot be dropped.** For `k = ℚ` and
`K = ℚ(2 ^ (1 / 3))`, a non-normal cubic field, the group `K ≃ₐ[k] K` is trivial, while for
`X = Spec K` over `k` the base change `X_K = Spec (K ⊗[k] K)` has two irreducible components,
whose residue fields have degrees `1` and `2` over `K`. So the components over the single
component of `X` are not interchangeable in any sense: no group acting on `X_K` over `X` is
transitive on them, and numerical invariants of the two differ. The same example rules out a
statement about an arbitrary extension with no hypothesis.

**Separability of `K/k` is not needed.** A purely inseparable extension is a universal
homeomorphism on spectra, so it splits no component at all; the transitivity statement is proved
here for every normal extension, separable or not
(`gal_acts_transitively_on_primes_of_normal`).

**An arbitrary extension factors through `E`.** `E` is separably closed in `K`
(`separableClosure.separableClosure_eq_bot`), hence `Spec K` is geometrically irreducible over
`E` (Tag 0G33), and therefore `X_K ⟶ X_E` is a bijection on irreducible components — the
generalization of Tag 038H from a separably closed base to a base separably closed in the
extension. Nothing beyond `E` contributes, so the honest hypothesis for conjugacy over an
arbitrary `K` is normality of `E/k`, and the group that acts is `E ≃ₐ[k] E`. Asking instead for
an automorphism of `X_K` would need every `k`-automorphism of `E` to extend to `K`, which is
automatic for `K/k` normal but not in general.

## Implementation notes

The conjugating automorphism of `X_K` is the one of the canonical action
`AlgebraicGeometry.galoisActionOnBaseChange`, and the components over a fixed component are a
fibre of `AlgebraicGeometry.irreducibleComponentsBaseChangeMap`; the orbit description of that
fibre is Tag 04KY, generalized to a normal extension in
`AlgebraicGeometry.fiber_irreducibleComponentsBaseChangeMap_eq_orbit`. That the automorphisms of
the action are morphisms over `X` is `Stacks.Descent.baseChangeAction_comp_fst`.

Over a separable closure and for `X` locally of finite type, the conjugacy of the components
lying over one component of `X` is also a clause of
`AlgebraicGeometry.exists_finite_single_orbit_decomposition` (Tag 04KZ), which in addition
decomposes the inverse image of the component. The statement here needs neither the finiteness
hypothesis nor a separably closed extension, and is phrased at a fibre of the map on
components.

The comparison map for a tower is `AlgebraicGeometry.baseChangeComparison`. It is exhibited as a
base change of `Spec K ⟶ Spec E` along the structure morphism of `X_E`, which is what transfers
geometric irreducibility and universal openness to it; the bijection on components is then
Mathlib's `AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv` for an open geometrically
irreducible morphism.

## References

* [Stacks Project, Tag 04KY](https://stacks.math.columbia.edu/tag/04KY)
* [Stacks Project, Tag 04KX](https://stacks.math.columbia.edu/tag/04KX)
* [Stacks Project, Tag 04KW](https://stacks.math.columbia.edu/tag/04KW)
* [Stacks Project, Tag 04KP](https://stacks.math.columbia.edu/tag/04KP)
* [Stacks Project, Tag 038H](https://stacks.math.columbia.edu/tag/038H)
* [Stacks Project, Tag 0G33](https://stacks.math.columbia.edu/tag/0G33)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- Two irreducible components of a base change along a **normal** extension `K/k` that have the
same image in the original scheme are conjugate: the automorphism of `X_K` attached to some
`σ : K ≃ₐ[k] K` carries the first onto the second. That automorphism is a morphism over `X`
(`Stacks.Descent.baseChangeAction_comp_fst` of
`AlgebraicGeometry/Descent/QuasiCoherent/GaloisFieldExtension.lean`), so the two components are
interchangeable over `X`.

Normality is necessary, not a convenience of the proof: over the non-normal cubic extension
`ℚ(2 ^ (1 / 3))/ℚ` the group `K ≃ₐ[k] K` is trivial while components do split, with residue
degrees `1` and `2`. -/
public theorem exists_algEquiv_image_eq_of_irreducibleComponentsBaseChangeMap_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Normal k K]
    (X : Over (Spec (.of k)))
    (Z W : (galoisActionOnGeometricIrreducibleComponents k K X).V)
    (h : irreducibleComponentsBaseChangeMap k K X Z =
      irreducibleComponentsBaseChangeMap k K X W) :
    ∃ σ : K ≃ₐ[k] K,
      ((galoisActionOnBaseChange k K X).ρ (MulOpposite.op σ)).asHom.base '' Z.1 = W.1 := by
  have hmem : W ∈ (irreducibleComponentsBaseChangeMap k K X) ⁻¹'
      {irreducibleComponentsBaseChangeMap k K X Z} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact h.symm
  rw [fiber_irreducibleComponentsBaseChangeMap_eq_orbit k K X Z] at hmem
  obtain ⟨σ, hσ⟩ := hmem
  refine ⟨σ.unop, ?_⟩
  have h2 := congrArg Subtype.val hσ
  rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe] at h2
  rw [MulOpposite.op_unop]
  exact h2

/-- The comparison map of a tower `k → E → K` is a morphism over the original scheme. -/
public theorem baseChangeComparison_comp_fst
    (k E K : Type u) [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    baseChangeComparison k E K X f ≫ pullback.fst f (Spec.map (ofHom (algebraMap k E))) =
      pullback.fst f (Spec.map (ofHom (algebraMap k K))) :=
  pullback.lift_fst _ _ _

/-- The comparison map of a tower `k → E → K` exhibits the base change along `K` as the base
change of the base change along `E` by `Spec K ⟶ Spec E`. -/
public theorem isPullback_baseChangeComparison
    (k E K : Type u) [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    IsPullback (baseChangeComparison k E K X f)
      (pullback.snd f (Spec.map (ofHom (algebraMap k K))))
      (pullback.snd f (Spec.map (ofHom (algebraMap k E))))
      (Spec.map (ofHom (algebraMap E K))) := by
  have halg : Spec.map (ofHom (algebraMap E K)) ≫ Spec.map (ofHom (algebraMap k E)) =
      Spec.map (ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply k E K x).symm
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f (Spec.map (ofHom (algebraMap k E))))
  rw [halg, baseChangeComparison_comp_fst]
  exact IsPullback.of_hasPullback f (Spec.map (ofHom (algebraMap k K)))

/-- For a tower `k → E → K` of fields in which `E` is separably closed in `K`, taking images
along the comparison map `X_K ⟶ X_E` is a bijection from the irreducible components of `X_K` to
those of `X_E`.

This is Tag 038H with the base field separably closed *in the extension* rather than separably
closed: `Spec K` is then geometrically irreducible over `E` (Tag 0G33), which is all the
argument uses. For `E` the separable closure of `k` in `K` the hypothesis is automatic. -/
@[ega "IV 4.5.21" "more general"]
public theorem bijOn_image_baseChangeComparison
    (k E K : Type u) [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
    (hsc : separableClosure E K = ⊥)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    Set.BijOn (fun Z ↦ (baseChangeComparison k E K X f).base '' Z)
      (irreducibleComponents
        (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K)))))
      (irreducibleComponents
        (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E))))) := by
  have hgi : GeometricallyIrreducible (Spec.map (ofHom (algebraMap E K))) :=
    (separableClosure.eq_bot_iff_geometricallyIrreducible E K).mp hsc
  have hsq := (isPullback_baseChangeComparison k E K X f).flip
  have : GeometricallyIrreducible (baseChangeComparison k E K X f) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) hsq hgi
  have : UniversallyOpen (baseChangeComparison k E K X f) :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) hsq inferInstance
  let b := baseChangeComparison k E K X f
  let e := Scheme.Hom.irreducibleComponentsEquiv b b.isOpenMap
  exact Set.InvOn.bijOn (f' := (b.base ⁻¹' ·))
    ⟨fun _ hZ => congrArg Subtype.val (e.symm_apply_apply ⟨_, hZ⟩),
      fun _ _ => Set.image_preimage_eq _ b.surjective⟩
    (fun _ hZ => (e ⟨_, hZ⟩).2) fun _ hT => (e.symm ⟨_, hT⟩).2

/-- **Orbit comparison across an arbitrary extension.** Let `X` be a scheme over a field `k`, let
`K/k` be an arbitrary extension of fields, and let `E` be the separable closure of `k` in `K`,
assumed normal over `k`. Two irreducible components of `X_K` with the same image in `X` have
conjugate images in `X_E`: some `σ : E ≃ₐ[k] E` carries the first image onto the second.

Taking images along the comparison map `X_K ⟶ X_E` is a bijection on irreducible components
(`AlgebraicGeometry.bijOn_image_baseChangeComparison`), so this determines the two components of
`X_K` themselves, and the conjugating automorphism of `X_E` is a morphism over `X`
(`Stacks.Descent.baseChangeAction_comp_fst`).

Normality of `E/k` is necessary: for `k = ℚ` and `K = ℚ(2 ^ (1 / 3))` we have `E = K`, the group
`E ≃ₐ[k] E` is trivial, and `Spec (K ⊗[k] K)` has two components with residue degrees `1` and
`2` over `K`. -/
public theorem exists_algEquiv_image_baseChangeComparison_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Normal k ↥(separableClosure k K)]
    (X : Over (Spec (.of k)))
    (Z W : irreducibleComponents
      (pullback (C := Scheme.{u}) X.hom (Spec.map (ofHom (algebraMap k K)))))
    (h : (pullback.fst X.hom (Spec.map (ofHom (algebraMap k K)))).base '' Z.1 =
      (pullback.fst X.hom (Spec.map (ofHom (algebraMap k K)))).base '' W.1) :
    ∃ σ : ↥(separableClosure k K) ≃ₐ[k] ↥(separableClosure k K),
      ((galoisActionOnBaseChange k ↥(separableClosure k K) X).ρ (MulOpposite.op σ)).asHom.base ''
          ((baseChangeComparison k ↥(separableClosure k K) K X.left X.hom).base '' Z.1) =
        (baseChangeComparison k ↥(separableClosure k K) K X.left X.hom).base '' W.1 := by
  have hbij := bijOn_image_baseChangeComparison k ↥(separableClosure k K) K
    (separableClosure.separableClosure_eq_bot k K) X.left X.hom
  refine exists_algEquiv_image_eq_of_irreducibleComponentsBaseChangeMap_eq
    k ↥(separableClosure k K) X
    ⟨_, hbij.mapsTo Z.2⟩ ⟨_, hbij.mapsTo W.2⟩ (Subtype.ext ?_)
  show (pullback.fst X.hom (Spec.map (ofHom (algebraMap k ↥(separableClosure k K))))).base ''
      ((baseChangeComparison k ↥(separableClosure k K) K X.left X.hom).base '' Z.1) =
    (pullback.fst X.hom (Spec.map (ofHom (algebraMap k ↥(separableClosure k K))))).base ''
      ((baseChangeComparison k ↥(separableClosure k K) K X.left X.hom).base '' W.1)
  have hcomp : ∀ V : Set (pullback (C := Scheme.{u}) X.hom
        (Spec.map (ofHom (algebraMap k K)))),
      (pullback.fst X.hom (Spec.map (ofHom (algebraMap k ↥(separableClosure k K))))).base ''
          ((baseChangeComparison k ↥(separableClosure k K) K X.left X.hom).base '' V) =
        (pullback.fst X.hom (Spec.map (ofHom (algebraMap k K)))).base '' V := by
    intro V
    rw [← Set.image_comp]
    exact congrArg (· '' V) (congrArg (fun g : _ ⟶ X.left => (g.base : _ → X.left))
      (baseChangeComparison_comp_fst k ↥(separableClosure k K) K X.left X.hom))
  rw [hcomp, hcomp, h]

end AlgebraicGeometry
