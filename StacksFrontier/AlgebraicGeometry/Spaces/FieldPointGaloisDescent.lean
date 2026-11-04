module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField

/-!
# Galois descent for field-valued points of a scheme

A morphism `Spec L ⟶ X` which is invariant under every element of the Galois group of a
finite Galois extension `L/K` factors through `Spec K`, and the graphs of the automorphisms
of `L/K` cover the self-product `Spec L ×_{Spec K} Spec L`. Together these two facts are the
descent data for field-valued points of a scheme along a finite Galois extension.

The input for producing such an extension is also collected here: a scheme étale over
`Spec K` with a point has a point valued in a finite separable extension of `K`, and every
finite separable extension of `K` embeds into a finite Galois one.

## Main results

* `AlgebraicGeometry.exists_specMap_comp_eq_of_isGaloisInvariant`: a Galois-invariant
  morphism from the spectrum of a finite Galois extension factors through the spectrum of the
  base field.
* `AlgebraicGeometry.exists_algEquiv_specMap_eq`: two morphisms to the spectrum of a normal
  extension agreeing over the base field differ by an automorphism of the extension.
* `AlgebraicGeometry.exists_graph_eq_of_isGalois`: the graphs of the automorphisms of a finite
  Galois extension `L/K` jointly cover `Spec L ×_{Spec K} Spec L`.
* `AlgebraicGeometry.Etale.exists_finiteSeparable_point`: a nonempty scheme étale over
  `Spec K` has a point valued in a finite separable extension of `K`.
* `exists_isGalois_of_finiteDimensional_of_isSeparable`: a finite separable extension embeds
  into a finite Galois extension.
* `AlgebraicGeometry.etale_specMap_algebraMap`: a finite separable extension of fields gives
  an étale morphism of spectra.

## Implementation notes

`Spec` is contravariant on rings, so an automorphism `σ` of `L` over `K` acts on `Spec L` by
`Spec.map σ`, and invariance of a morphism `f : Spec L ⟶ X` is `Spec.map σ ≫ f = f` for every
`σ`. The factorization is read off the description of a field-valued point of a scheme as a
point together with an embedding of its residue field
(`AlgebraicGeometry.Scheme.SpecToEquivOfField`): invariance says that the embedding lands in
the fixed field of the Galois group, which is the image of `K`.

The covering statement is phrased with the graph morphisms given by
`CategoryTheory.Limits.pullback.lift (Spec.map σ) (𝟙 _)`; each is a section of the second
projection and therefore an open immersion, so the family is an étale covering.

## References

* [Stacks Project, Tag 02Z5](https://stacks.math.columbia.edu/tag/02Z5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Two facts about finite separable extensions -/

/-- Two embeddings of a normal extension `L/K` into a field `M` over `K` differ by an
automorphism of `L/K`. -/
theorem AlgHom.exists_algEquiv_comp_eq_of_normal (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Normal K L] (p q : L →ₐ[K] M) :
    ∃ σ : L ≃ₐ[K] L, q.comp σ.toAlgHom = p := by
  let : Algebra L M := q.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' q.comp_algebraMap.symm
  exact ⟨Normal.algHomEquivAut K M L p, (Normal.algHomEquivAut K M L).symm_apply_apply p⟩

/-- Every finite separable extension of `K` embeds into a finite Galois extension of `K`,
namely into the normal closure of the extension inside an algebraic closure of `K`. -/
theorem exists_isGalois_of_finiteDimensional_of_isSeparable (K E : Type u) [Field K] [Field E]
    [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra K M) (_ : FiniteDimensional K M)
      (_ : IsGalois K M), Nonempty (E →ₐ[K] M) := by
  classical
  let A := AlgebraicClosure K
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_of_splits (F := K) (E := E) (K := A)
    fun x => ⟨Algebra.IsIntegral.isIntegral (R := K) x, IsAlgClosed.splits _⟩
  let : Algebra E A := φ.toRingHom.toAlgebra
  have : IsScalarTower K E A := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let M := IntermediateField.normalClosure K E A
  have : FiniteDimensional K M := normalClosure.is_finiteDimensional K E A
  have (f : E →ₐ[K] A) : Algebra.IsSeparable K f.fieldRange :=
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  have : Algebra.IsSeparable K M := by
    change Algebra.IsSeparable K (↑(⨆ f : E →ₐ[K] A, f.fieldRange : IntermediateField K A))
    infer_instance
  have : IsGalois K M := isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(normalClosure.algHomEquiv K E A).symm φ⟩⟩

namespace AlgebraicGeometry

/-! ### Spectra of field extensions -/

/-- Post-composing with the structure map of a field extension `L/K` is unchanged by the
action of an automorphism of `L/K` on `Spec L`. -/
theorem specMap_algEquiv_comp_specMap_algebraMap (K L : Type u) [Field K] [Field L]
    [Algebra K L] (σ : L ≃ₐ[K] L) :
    Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext σ.commutes))

/-- The morphism of spectra induced by a finite separable extension of fields is étale. -/
theorem etale_specMap_algebraMap (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  change (algebraMap K L).Etale
  rw [RingHom.etale_algebraMap]
  exact ⟨Algebra.FormallyEtale.of_isSeparable K L,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- Two morphisms into the spectrum of a normal extension `L/K` which agree after projection
to `Spec K` differ by an automorphism of `L/K`. -/
theorem exists_algEquiv_specMap_eq (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Normal K L] (p q : Spec (.of M) ⟶ Spec (.of L))
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ σ : L ≃ₐ[K] L, p = q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  obtain ⟨p, rfl⟩ := Spec.map_surjective p
  obtain ⟨q, rfl⟩ := Spec.map_surjective q
  let : Algebra K M := (q.hom.comp (algebraMap K L)).toAlgebra
  have hp : p.hom.comp (algebraMap K L) = q.hom.comp (algebraMap K L) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective
      (show Spec.map (CommRingCat.ofHom (algebraMap K L) ≫ p) =
          Spec.map (CommRingCat.ofHom (algebraMap K L) ≫ q) by
        simpa only [Spec.map_comp] using h))
  obtain ⟨σ, hσ⟩ := AlgHom.exists_algEquiv_comp_eq_of_normal K L M
    ⟨p.hom, fun x => congrArg (fun f : K →+* M => f x) hp⟩ ⟨q.hom, fun _ => rfl⟩
  refine ⟨σ, ?_⟩
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom hσ).symm)

/-- A morphism from the spectrum of a finite Galois extension `L/K` to a scheme which is
invariant under the Galois group factors through `Spec K`. -/
theorem exists_specMap_comp_eq_of_isGaloisInvariant (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (X : Scheme.{u})
    (f : Spec (.of L) ⟶ X)
    (hf : ∀ σ : L ≃ₐ[K] L, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f = f) :
    ∃ g : Spec (.of K) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ g = f := by
  let z := Scheme.SpecToEquivOfField L X f
  have hz : Spec.map z.2 ≫ X.fromSpecResidueField z.1 = f :=
    (Scheme.SpecToEquivOfField L X).symm_apply_apply f
  have hfix (σ : L ≃ₐ[K] L) : σ.toRingHom.comp z.2.hom = z.2.hom := by
    have h := hf σ
    rw [← hz, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  let e := RingEquiv.ofBijective (algebraMap K L).rangeRestrict
    ⟨fun _ _ h => (algebraMap K L).injective (congrArg Subtype.val h),
      (algebraMap K L).rangeRestrict_surjective⟩
  let p : X.residueField z.1 →+* K := e.symm.toRingHom.comp
    (z.2.hom.codRestrict (algebraMap K L).range fun x =>
      (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) _).mpr fun σ =>
        congrArg (fun φ : X.residueField z.1 →+* L => φ x) (hfix σ))
  refine ⟨Spec.map (CommRingCat.ofHom p) ≫ X.fromSpecResidueField z.1, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, ← hz]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext fun x =>
    congrArg Subtype.val (e.apply_symm_apply ⟨z.2.hom x, _⟩))

/-- The graphs of the automorphisms of a finite Galois extension `L/K` jointly cover the
self-product of `Spec L` over `Spec K`: every point of `Spec L ×_{Spec K} Spec L` lies in the
image of the graph of some `σ : L ≃ₐ[K] L`. -/
theorem exists_graph_eq_of_isGalois (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (r : Spec (.of L) ⟶ Spec (.of K))
    (hr : r = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (aut : (L ≃ₐ[K] L) → (Spec (.of L) ⟶ Spec (.of L)))
    (haut : ∀ σ, aut σ = Spec.map (CommRingCat.ofHom σ.toRingHom))
    (har : ∀ σ, aut σ ≫ r = r) (x : (pullback r r : Scheme)) :
    ∃ (σ : L ≃ₐ[K] L) (y : Spec (.of L)),
      (pullback.lift (f := r) (g := r) (aut σ) (𝟙 _) (by simp [har])) y = x := by
  let t := (pullback r r).fromSpecResidueField x
  have ht : (t ≫ pullback.fst r r) ≫ r = (t ≫ pullback.snd r r) ≫ r := by
    simp [pullback.condition]
  obtain ⟨σ, hσ⟩ := exists_algEquiv_specMap_eq K L ((pullback r r).residueField x)
    (t ≫ pullback.fst r r) (t ≫ pullback.snd r r) (by simpa [hr] using ht)
  let g : Spec (.of L) ⟶ pullback r r :=
    pullback.lift (aut σ) (𝟙 _) (by simp [har])
  have htg : (t ≫ pullback.snd r r) ≫ g = t := by
    apply pullback.hom_ext
    · simpa only [g, Category.assoc, pullback.lift_fst, haut] using hσ.symm
    · simp only [g, Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨σ, (t ≫ pullback.snd r r) default, ?_⟩
  change ((t ≫ pullback.snd r r) ≫ g) default = x
  rw [htg]
  exact Scheme.fromSpecResidueField_apply x default

/-- The canonical identification of a field with the residue field of its spectrum at the
unique point. -/
private def specResidueFieldRingEquiv (K : Type u) [Field K] :
    K ≃+* (Spec (.of K)).residueField (default : Spec (.of K)) := by
  let R₀ := (⊥ : Ideal K).ResidueField
  let Q := K ⧸ (⊥ : Ideal K)
  letI : Algebra K R₀ := ((algebraMap Q R₀).comp (algebraMap K Q)).toAlgebra
  letI : IsScalarTower K Q R₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing K R₀ :=
    IsFractionRing.of_ringEquiv_left (RingEquiv.quotientBot K).symm fun x => rfl
  exact (IsFractionRing.algEquiv K K R₀).toRingEquiv.trans
    (Scheme.Spec.residueFieldIso (.of K)
      (default : Spec (.of K))).commRingCatIsoToRingEquiv.symm

private theorem specResidueFieldIso_inv_comp_algebraMap (K : Type u) [Field K] :
    (Scheme.Spec.residueFieldIso (CommRingCat.of K) default).inv.hom.comp
      (algebraMap K (⊥ : Ideal K).ResidueField) = (specResidueFieldRingEquiv K).toRingHom := by
  ext t
  rfl

/-- **Stacks 02GL at a point.** A nonempty scheme étale over the spectrum of a field `K` has
a point valued in a finite separable extension of `K`, compatibly with the structure
morphisms.

The fibre of an étale morphism over the unique point of `Spec K` is a coproduct of spectra of
finite separable extensions of the residue field there, which is `K` itself; a point of the
scheme singles out one summand. -/
theorem Etale.exists_finiteSeparable_point (K : Type u) [Field K] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of K)) [Etale q] (hne : Nonempty X) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L) (f : Spec (.of L) ⟶ X),
      f ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  classical
  let y : Spec (.of K) := default
  obtain ⟨I, L, hField, hAlg, hFinite, hSeparable, e, he⟩ :=
    Etale.exists_iso_fiber_coproduct_spectra_finite_separable q y
  obtain ⟨x⟩ := hne
  have hqx : q x = y := Subsingleton.elim _ _
  let z : q.fiber y := hqx ▸ (q.asFiberHom x) (default : Spec (X.residueField x))
  let i := ((AlgebraicGeometry.sigmaMk fun i : I => Spec (.of (L i))).symm (e.hom z)).1
  let f₀ : Spec (.of (L i)) ⟶ q.fiber y := Sigma.ι (fun i : I => Spec (.of (L i))) i ≫ e.inv
  let f := f₀ ≫ q.fiberι y
  let eK := specResidueFieldRingEquiv K
  let K₀ := (Spec (.of K)).residueField y
  let : Algebra K K₀ := eK.toRingHom.toAlgebra
  let : Algebra K (L i) := ((algebraMap K₀ (L i)).comp eK.toRingHom).toAlgebra
  have : IsScalarTower K K₀ (L i) := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite K K₀ :=
    Module.Finite.equiv ({ toRingEquiv := eK, commutes' := fun _ => rfl } :
      K ≃ₐ[K] K₀).toLinearEquiv
  have : Module.Finite K₀ (L i) := hFinite i
  have : Module.Finite K (L i) := Module.Finite.trans K₀ (L i)
  have : Algebra.IsSeparable K (L i) :=
    Algebra.IsSeparable.of_equiv_equiv eK.symm (RingEquiv.refl (L i)) (by
      ext x
      change algebraMap K₀ (L i) ((algebraMap K K₀) (eK.symm x)) = algebraMap K₀ (L i) x
      exact congrArg (algebraMap K₀ (L i)) (eK.apply_symm_apply x))
  refine ⟨L i, hField i, inferInstance, inferInstance, inferInstance, f, ?_⟩
  have hcomponent : f₀ ≫ q.fiberToSpecResidueField y =
      Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of K)).residueField y) (L i))) := by
    rw [← he]
    simp [f₀]
  change f₀ ≫ q.fiberι y ≫ q = _
  rw [q.fiber_fac, ← Category.assoc, hcomponent,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp,
    ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x =>
    congrArg (algebraMap K₀ (L i))
      (congrArg (fun φ : K →+* K₀ => φ x) (specResidueFieldIso_inv_comp_algebraMap K))))

end AlgebraicGeometry

end
