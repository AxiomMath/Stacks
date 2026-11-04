module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusFibre
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.RingTheory.FormallySmooth.Field
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separable residue fields at the generic points make the generic fibre smooth on a dense open

Let `A` be a domain with fraction field `K` and let `f : X ⟶ Spec A` be locally of finite type.
**If the residue field at every generic point of an irreducible component of `X` is separable
over the residue field of `Spec A` below it, then the reduction of `X ×_{Spec A} Spec K` has a
dense open subscheme smooth over `K`.**  This is the first paragraph of the proof of Tag 0BRR,
where it replaces the purely inseparable extension of the first paragraph of Tag 09IL: the
source's route is through geometric reducedness of the generic fibre, Tags 04KS and 056V; here the
smooth locus is shown directly to contain every generic point.

The projection `X ×_{Spec A} Spec K ⟶ X` is the base change of `Spec K ⟶ Spec A`, a flat
preimmersion, so it carries generic points to generic points and induces isomorphisms on residue
fields; so do the reduction, a surjective closed immersion, and `Spec K ⟶ Spec A`.  At a generic
point of the reduced scheme the local ring is its residue field, so membership of the smooth locus
is formal smoothness of a map of residue fields, which is the separability of Tag 030O by
`Algebra.FormallySmooth.iff_isSeparableExtension`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_iff_residueFieldMap`: between local rings
  which are fields, a stalk map is formally smooth exactly when the residue field map is.
* `AlgebraicGeometry.exists_dense_open_smooth_reduction_pullback_of_isSeparableExtension`: the
  dense smooth open of the reduced generic fibre.

## References

* [Stacks Project, Tag 0BRR](https://stacks.math.columbia.edu/tag/0BRR)
* [Stacks Project, Tag 04KS](https://stacks.math.columbia.edu/tag/04KS)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 0320](https://stacks.math.columbia.edu/tag/0320)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Formal smoothness of a composite of ring maps whose second factor is an isomorphism. -/
theorem formallySmooth_comp_iff_of_isIso_right {R S T : CommRingCat.{u}} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : (f ≫ g).hom.FormallySmooth ↔ f.hom.FormallySmooth := by
  rw [CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_right_isIso f g

/-- Formal smoothness of a composite of ring maps whose first factor is an isomorphism. -/
theorem formallySmooth_comp_iff_of_isIso_left {R S T : CommRingCat.{u}} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : (f ≫ g).hom.FormallySmooth ↔ g.hom.FormallySmooth := by
  rw [CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso f g

/-- The local rings of the spectrum of a field are fields. -/
theorem isField_stalk_Spec_field (K : Type u) [Field K] (x : Spec (.of K)) :
    IsField ((Spec (.of K)).presheaf.stalk x) := by
  let K' := (Spec.structureSheaf K).presheaf.stalk x
  let : Algebra K K' := StructureSheaf.stalkAlgebra K x
  have : x.asIdeal.IsPrime := x.isPrime
  let : IsLocalization.AtPrime K' x.asIdeal := StructureSheaf.IsLocalization.to_stalk K x
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ x.asIdeal.primeCompl
    (fun a ha ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  exact MulEquiv.isField (Field.toIsField K) e.toRingEquiv.symm.toMulEquiv

/-- The residue map of a local ring of a scheme which is a field is an isomorphism. -/
theorem Scheme.isIso_residue_of_isField (X : Scheme.{u}) (x : X)
    (hx : IsField (X.presheaf.stalk x)) : IsIso (X.residue x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, X.residue_surjective x⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (IsLocalRing.residue_eq_zero_iff a).1 ha
  rwa [IsLocalRing.isField_iff_maximalIdeal_eq.1 hx] at hmem

/-- Between local rings which are fields, a stalk map is formally smooth exactly when the
residue field map is. -/
theorem Scheme.Hom.formallySmooth_stalkMap_iff_residueFieldMap {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (x : X) (hX : IsField (X.presheaf.stalk x)) (hY : IsField (Y.presheaf.stalk (φ x))) :
    (φ.stalkMap x).hom.FormallySmooth ↔ (φ.residueFieldMap x).hom.FormallySmooth := by
  have := X.isIso_residue_of_isField x hX
  have := Y.isIso_residue_of_isField (φ x) hY
  rw [← formallySmooth_comp_iff_of_isIso_right (φ.stalkMap x) (X.residue x),
    ← Scheme.residue_residueFieldMap, formallySmooth_comp_iff_of_isIso_left]

/-- Formal smoothness of the residue field map of a composite, the first residue field map being
an isomorphism. -/
theorem Scheme.Hom.formallySmooth_residueFieldMap_comp_iff_of_isIso_left {X Y Z : Scheme.{u}}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z) (x : X) [IsIso (φ.residueFieldMap x)] :
    ((φ ≫ ψ).residueFieldMap x).hom.FormallySmooth ↔
      (ψ.residueFieldMap (φ x)).hom.FormallySmooth :=
  by rw [Scheme.residueFieldMap_comp]; exact formallySmooth_comp_iff_of_isIso_right _ _

/-- Formal smoothness of the residue field map of a composite, the second residue field map
being an isomorphism. -/
theorem Scheme.Hom.formallySmooth_residueFieldMap_comp_iff_of_isIso_right {X Y Z : Scheme.{u}}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z) (x : X) [IsIso (ψ.residueFieldMap (φ x))] :
    ((φ ≫ ψ).residueFieldMap x).hom.FormallySmooth ↔
      (φ.residueFieldMap x).hom.FormallySmooth :=
  by
    rw [Scheme.residueFieldMap_comp]
    exact formallySmooth_comp_iff_of_isIso_left (ψ.residueFieldMap _) _

/-- Formal smoothness of a residue field map depends only on the morphism. -/
theorem Scheme.Hom.formallySmooth_residueFieldMap_congr {X Y : Scheme.{u}} {φ ψ : X ⟶ Y}
    (e : φ = ψ) (x : X) :
    (φ.residueFieldMap x).hom.FormallySmooth ↔ (ψ.residueFieldMap x).hom.FormallySmooth := by
  subst e
  rfl

/-- A preimmersion induces isomorphisms of residue fields. -/
theorem Scheme.Hom.isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [IsPreimmersion φ] (x : X) : IsIso (φ.residueFieldMap x) :=
  isIso_residueFieldMap_of_stalkMap_surjective φ x (φ.stalkMap_surjective x)

/-- A surjective closed immersion carries generic points of irreducible components to generic
points of irreducible components: it is a homeomorphism. -/
theorem mem_genericPoints_of_isClosedImmersion_of_surjective {Z W : Scheme.{u}} (ρ : Z ⟶ W)
    [IsClosedImmersion ρ] [Surjective ρ] {z : Z} (hz : z ∈ genericPoints Z) :
    ρ z ∈ genericPoints W := by
  refine mem_genericPoints_of_generalizingMap (f := ρ.base) (fun a w h => ?_) hz
  obtain ⟨a', rfl⟩ := ρ.surjective w
  exact ⟨a', ρ.isEmbedding.isInducing.specializes_iff.1 h, rfl⟩

/-- **The reduction of the generic fibre is smooth on a dense open when the residue fields at
the generic points are separable.** Let `A` be a domain with fraction field `K` and let
`f : X ⟶ Spec A` be locally of finite type, such that for every generic point `x` of an
irreducible component of `X` the residue field `κ(x)` is separable over the residue field of
`Spec A` at `f x`. Then the reduction of `X ×_{Spec A} Spec K` has a dense open subscheme smooth
over `Spec K`.

The projection `X ×_{Spec A} Spec K ⟶ X` is a flat preimmersion, so it carries generic points
to generic points and induces isomorphisms of residue fields; at a generic point of the
reduction the local ring is the residue field, which is therefore formally smooth over `K`.
The smooth locus of the reduction contains every generic point, hence is dense. -/
@[ega "IV 17.15.12" "Second assertion"]
theorem exists_dense_open_smooth_reduction_pullback_of_isSeparableExtension {A : Type u}
    [CommRing A] [IsDomain A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hsep : ∀ x : X, x ∈ genericPoints X →
      letI : Algebra ((Spec (.of A)).residueField (f x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension ((Spec (.of A)).residueField (f x)) (X.residueField x)) :
    let j : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A K))
    ∃ (Z : Scheme.{u}) (ρ : Z ⟶ (pullback f j : Scheme.{u})),
      IsClosedImmersion ρ ∧ Surjective ρ ∧ IsReduced Z ∧
        ρ.ker = (pullback f j : Scheme.{u}).nilradical ∧
        ∃ U : Z.Opens, Dense (U : Set Z) ∧ Smooth (U.ι ≫ ρ ≫ pullback.snd f j) := by
  intro j
  have : Flat j := flat_Spec_map_algebraMap_of_isFractionRing A K
  have : IsPreimmersion j := IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  set I := Scheme.IdealSheafData.vanishingIdeal (X := (pullback f j : Scheme.{u}))
    (⊤ : Closeds (pullback f j : Scheme.{u})) with hI
  have hIn : I = (pullback f j : Scheme.{u}).nilradical := by simp [hI]
  have hsurj : Surjective I.subschemeι := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, hIn]
    simp
  set p := I.subschemeι ≫ pullback.snd f j with hp
  have hgen : ∀ z ∈ genericPoints I.subscheme, z ∈ p.smoothLocus := by
    intro z hz
    set w := I.subschemeι z
    have hw : w ∈ genericPoints (pullback f j : Scheme.{u}) :=
      mem_genericPoints_of_isClosedImmersion_of_surjective I.subschemeι hz
    have hx : pullback.fst f j w ∈ genericPoints X :=
      mem_genericPoints_of_generalizingMap (Flat.generalizingMap _) hw
    have hfx : (f.residueFieldMap (pullback.fst f j w)).hom.FormallySmooth := by
      let : Algebra ((Spec (.of A)).residueField (f (pullback.fst f j w)))
          (X.residueField (pullback.fst f j w)) :=
        (f.residueFieldMap (pullback.fst f j w)).hom.toAlgebra
      exact RingHom.formallySmooth_algebraMap.2
        ((Algebra.FormallySmooth.iff_isSeparableExtension _ _).2 (hsep _ hx))
    have hZ : IsField (I.subscheme.presheaf.stalk z) :=
      isField_stalk_of_closure_mem_irreducibleComponents _ z hz
    have hK : IsField ((Spec (.of K)).presheaf.stalk (p z)) := isField_stalk_Spec_field K _
    have := I.subschemeι.isIso_residueFieldMap_of_isPreimmersion z
    have := j.isIso_residueFieldMap_of_isPreimmersion (pullback.snd f j w)
    have := (pullback.fst f j).isIso_residueFieldMap_of_isPreimmersion w
    have h1 : ((pullback.fst f j ≫ f).residueFieldMap w).hom.FormallySmooth :=
      (Scheme.Hom.formallySmooth_residueFieldMap_comp_iff_of_isIso_left _ _ w).2 hfx
    have h2 : ((pullback.snd f j ≫ j).residueFieldMap w).hom.FormallySmooth :=
      (Scheme.Hom.formallySmooth_residueFieldMap_congr pullback.condition w).1 h1
    have h3 : ((pullback.snd f j).residueFieldMap w).hom.FormallySmooth :=
      (Scheme.Hom.formallySmooth_residueFieldMap_comp_iff_of_isIso_right _ _ w).1 h2
    have h4 : ((I.subschemeι ≫ pullback.snd f j).residueFieldMap z).hom.FormallySmooth :=
      (Scheme.Hom.formallySmooth_residueFieldMap_comp_iff_of_isIso_left _ _ z).2 h3
    rw [Scheme.Hom.mem_smoothLocus, p.formallySmooth_stalkMap_iff_residueFieldMap z hZ hK]
    exact h4
  refine ⟨I.subscheme, I.subschemeι, inferInstance, hsurj, inferInstance,
    ker_eq_nilradical_of_surjective _, p.smoothLocus,
    (dense_iff_closure_eq.mpr genericPoints.closure).mono hgen, ?_⟩
  apply (Scheme.Hom.smoothLocus_eq_top_iff).mp
  show Scheme.Hom.smoothLocus (p.smoothLocus.ι ≫ p) = ⊤
  rw [← Scheme.Hom.preimage_smoothLocus_eq p.smoothLocus.ι p]
  simp

end AlgebraicGeometry

end
