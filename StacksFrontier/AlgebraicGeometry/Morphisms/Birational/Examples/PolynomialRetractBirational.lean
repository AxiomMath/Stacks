module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Examples.PolynomialRetract

/-!
# The polynomial retract is birational in both directions

For the square-zero extension `B` of `A = k[x]` over a field `k`, both the projection
`Spec B ⟶ Spec A` induced by the inclusion and the section `Spec A ⟶ Spec B` induced by the
retraction are birational.

Both spectra are irreducible, the inclusion inducing a homeomorphism, so each has a single
generic point, and the two correspond. At those generic points the local rings are both the
rational function field `k(x)`: the kernel of the retraction is square-zero, so it dies in the
localization.

## Main results

* `AlgebraicGeometry.PolynomialRetract.inclusionMap_isBirational`: the projection is birational.
* `AlgebraicGeometry.PolynomialRetract.retraction_isBirational`: the section is birational.

## Implementation notes

Birationality is the predicate of Tag 01RO, covering both the bijection on generic points and
the isomorphism on local rings there. The stalk maps of these spectrum morphisms are
transported to localization homomorphisms through the canonical stalk isomorphisms of an affine
scheme.

## References

* [Stacks Project, Tag 01RQ](https://stacks.math.columbia.edu/tag/01RQ), Example 29.50.4
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PolynomialRetract

/-- The retraction undoes the canonical inclusion on each element. -/
private lemma retraction_inclusion (k : Type u) [Field k] (a : baseRing k) :
    retractionMap k (inclusionMap k a) = a :=
  RingHom.congr_fun (retractionMap_comp_inclusionMap k) a

/-- The kernel of the retraction lies over the generic point of `Spec k[x]`. -/
private theorem comap_inclusionMap_projectionKernel (k : Type u) [Field k] :
    PrimeSpectrum.comap (inclusionMap k)
      (⟨projectionKernel k, projectionKernel_isPrime k⟩ : PrimeSpectrum (extensionRing k)) =
        ⊥ := by
  ext a
  simp [projectionKernel, retraction_inclusion]

/-- The homeomorphism induced by the inclusion maps the generic point to the generic point. -/
private theorem homeomorph_genericPoint (k : Type u) [Field k]
    [IrreducibleSpace (Spec (CommRingCat.of (extensionRing k)))] :
    PrimeSpectrum.comap (inclusionMap k)
        (genericPoint (Spec (CommRingCat.of (extensionRing k)))) =
      genericPoint (Spec (CommRingCat.of (baseRing k))) := by
  let H := (isHomeomorph_comap_inclusionMap (k := k)).homeomorph
  change H _ = _
  have h : IsGenericPoint (H (genericPoint (Spec (.of (extensionRing k))))) Set.univ := by
    have h' := (genericPoint_spec (Spec (.of (extensionRing k)))).image H.continuous
    change closure ({H (genericPoint (Spec (.of (extensionRing k))))} :
      Set (PrimeSpectrum (baseRing k))) =
        closure (H '' (Set.univ : Set (PrimeSpectrum (extensionRing k)))) at h'
    rwa [Set.image_univ_of_surjective H.surjective, closure_univ] at h'
  exact ((genericPoint_spec (Spec (.of (baseRing k)))).eq h).symm

/-- The generic point of the spectrum of the quotient ring is the kernel of the retraction. -/
private theorem genericPoint_eq_projectionKernel (k : Type u) [Field k]
    [IrreducibleSpace (Spec (CommRingCat.of (extensionRing k)))] :
    genericPoint (Spec (CommRingCat.of (extensionRing k))) =
      (⟨projectionKernel k,
        projectionKernel_isPrime k⟩ : PrimeSpectrum (extensionRing k)) :=
  (isHomeomorph_comap_inclusionMap k).injective <|
    (homeomorph_genericPoint k).trans <|
      (genericPoint_eq_bot_of_affine (CommRingCat.of (baseRing k))).trans
        (comap_inclusionMap_projectionKernel k).symm

/-- At the generic point the localization map induced by the inclusion is bijective: both
localizations are the rational function field of `k[x]`. -/
private theorem localRingHom_projection_isIso (k : Type u) [Field k]
    (I : Ideal (baseRing k)) [I.IsPrime]
    (hM : I.primeCompl = nonZeroDivisors (baseRing k))
    (hIJ : I = Ideal.comap (inclusionMap k) (projectionKernel k)) :
    Function.Bijective (Localization.localRingHom I
      (projectionKernel k) (inclusionMap k) hIJ) := by
  let A := baseRing k
  let J := projectionKernel k
  let : IsLocalization I.primeCompl (FractionRing A) :=
    hM.symm ▸ (inferInstance : IsFractionRing A (FractionRing A))
  let eA : Localization.AtPrime I ≃ₐ[A] FractionRing A :=
    IsLocalization.algEquiv I.primeCompl (Localization.AtPrime I) (FractionRing A)
  let ℓ := Localization.localRingHom I J (inclusionMap k) hIJ
  have hcomp : (genericLocalizationEquiv k).toRingHom.comp ℓ =
      eA.toRingHom := by
    refine IsLocalization.ringHom_ext I.primeCompl (RingHom.ext fun a ↦ ?_)
    change (genericLocalizationEquiv k).toRingHom
        (ℓ (algebraMap A (Localization.AtPrime I) a)) =
      eA.toRingHom (algebraMap A (Localization.AtPrime I) a)
    rw [show ℓ (algebraMap A (Localization.AtPrime I) a) =
        algebraMap (extensionRing k) (Localization.AtPrime J) (inclusionMap k a) from
          Localization.localRingHom_to_map I J (inclusionMap k) hIJ a]
    change genericLocalizationEquiv k
        (algebraMap (extensionRing k) (Localization.AtPrime J) (inclusionMap k a)) =
      eA.toRingHom (algebraMap A (Localization.AtPrime I) a)
    rw [genericLocalizationEquiv_map, retraction_inclusion]
    exact (eA.commutes a).symm
  have hℓ : ℓ = (genericLocalizationEquiv k).symm.toRingHom.comp eA.toRingHom := by
    rw [← hcomp]
    ext x
    simp
  change Function.Bijective ℓ
  rw [hℓ]
  exact (genericLocalizationEquiv k).symm.bijective.comp eA.bijective

/-- The inclusion induces an isomorphism on local rings at the generic point. -/
private theorem projection_stalkMap_isIso (k : Type u) [Field k] :
    IsIso ((Scheme.Spec.map (CommRingCat.ofHom (inclusionMap k)).op).stalkMap
      (⟨projectionKernel k,
        projectionKernel_isPrime k⟩ : Spec (.of (extensionRing k)))) := by
  let A := baseRing k
  let J := projectionKernel k
  let q : PrimeSpectrum (extensionRing k) := ⟨J, projectionKernel_isPrime k⟩
  let p : PrimeSpectrum A := PrimeSpectrum.comap (CommRingCat.ofHom (inclusionMap k)).hom q
  have : IsDomain A := inferInstance
  have hIJ : p.asIdeal = Ideal.comap (inclusionMap k) J := by simp [p, q, J]
  have hM : p.asIdeal.primeCompl = nonZeroDivisors A := by
    ext a
    change a ∉ p.asIdeal ↔ a ∈ nonZeroDivisors A
    rw [mem_nonZeroDivisors_iff_ne_zero]
    change inclusionMap k a ∉ projectionKernel k ↔ a ≠ 0
    change retractionMap k (inclusionMap k a) ≠ 0 ↔ a ≠ 0
    simp [retraction_inclusion]
  have hloc : Function.Bijective (Localization.localRingHom p.asIdeal J
      (inclusionMap k) hIJ) := localRingHom_projection_isIso k p.asIdeal hM hIJ
  -- The localization semiring instances agree, but Lean must unfold their instance definitions.
  have hS :
      (inferInstance :
          CommRing (Localization.AtPrime p.asIdeal)).toCommSemiring.toSemiring.toNonAssocSemiring =
        (inferInstance : Semiring (Localization.AtPrime p.asIdeal)).toNonAssocSemiring := by
    with_reducible_and_instances rfl
  have hT :
      (inferInstance :
          CommRing (Localization.AtPrime q.asIdeal)).toCommSemiring.toSemiring.toNonAssocSemiring =
        (inferInstance : Semiring (Localization.AtPrime q.asIdeal)).toNonAssocSemiring := by
    with_reducible_and_instances rfl
  let f := CommRingCat.ofHom (inclusionMap k)
  let ℓ : @RingHom (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
      ((inferInstance :
        CommRing (Localization.AtPrime p.asIdeal)).toCommSemiring.toNonAssocSemiring)
      ((inferInstance :
        CommRing (Localization.AtPrime q.asIdeal)).toCommSemiring.toNonAssocSemiring) :=
    hS.symm ▸ hT.symm ▸ Localization.localRingHom p.asIdeal q.asIdeal
      f.hom (PrimeSpectrum.comap_asIdeal f.hom q)
  have hcat : IsIso (CommRingCat.ofHom ℓ) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (by simpa [q, f, ℓ] using hloc)
  let := hcat
  have hA : IsIso (CommRingCat.ofHom
      ((StructureSheaf.stalkIso (CommRingCat.of (baseRing k))
        (PrimeSpectrum.comap (CommRingCat.ofHom (inclusionMap k)).hom
          q)).symm.toRingEquiv.toRingHom)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (StructureSheaf.stalkIso (CommRingCat.of (baseRing k))
        (PrimeSpectrum.comap (CommRingCat.ofHom (inclusionMap k)).hom q)).symm.bijective
  let := hA
  have hC : IsIso (CommRingCat.ofHom
      ((StructureSheaf.stalkIso (CommRingCat.of (extensionRing k)) q).toRingEquiv.toRingHom)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (StructureSheaf.stalkIso (CommRingCat.of (extensionRing k)) q).bijective
  let := hC
  have hstalk := localRingHom_comp_stalkIso f q
  change IsIso ((Spec.sheafedSpaceMap (CommRingCat.ofHom (inclusionMap k))).hom.stalkMap q)
  rw [← hstalk]
  exact IsIso.comp_isIso' hA (IsIso.comp_isIso' hcat hC)

/-- The canonical inclusion `k[x] → B` induces a birational morphism on spectra. -/
@[stacks 01RQ "projection_birational"]
theorem inclusionMap_isBirational (k : Type u) [Field k] :
    IsBirational
      (Scheme.Spec.map (CommRingCat.ofHom (inclusionMap k)).op) := by
  have : IsDomain (baseRing k) := inferInstance
  let f := Scheme.Spec.map (CommRingCat.ofHom (inclusionMap k)).op
  have : IrreducibleSpace (Spec (.of (extensionRing k))) :=
    (isHomeomorph_comap_inclusionMap (k := k)).homeomorph.irreducibleSpace_iff.mpr inferInstance
  change Set.BijOn f (genericPoints (Spec (.of (extensionRing k))))
      (genericPoints (Spec (.of (baseRing k)))) ∧
    ∀ x, x ∈ genericPoints (Spec (.of (extensionRing k))) → IsIso (f.stalkMap x)
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    apply Set.bijOn_singleton.mpr
    rw [genericPoint_eq_projectionKernel k,
      genericPoint_eq_bot_of_affine (CommRingCat.of (baseRing k))]
    exact comap_inclusionMap_projectionKernel k
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    rw [genericPoint_eq_projectionKernel]
    exact projection_stalkMap_isIso k

/-- The retraction `B → k[x]`, setting every `y_a` to zero, induces a birational morphism on
spectra: the section `Spec k[x] ⟶ Spec B` is birational. -/
@[stacks 01RQ "section_birational"]
theorem retraction_isBirational (k : Type u) [Field k] :
    IsBirational
      (Scheme.Spec.map (CommRingCat.ofHom (retractionMap k)).op) := by
  let A := baseRing k
  let B := extensionRing k
  let f : Spec (.of A) ⟶ Spec (.of B) :=
    Scheme.Spec.map (CommRingCat.ofHom (retractionMap k)).op
  let H := (isHomeomorph_comap_inclusionMap k).homeomorph
  have hleft : (PrimeSpectrum.comap (inclusionMap k)).comp
      (PrimeSpectrum.comap (retractionMap k)) = id := by
    rw [← PrimeSpectrum.comap_comp]
    simp [retractionMap_comp_inclusionMap]
    rfl
  have hFH : ∀ p : PrimeSpectrum A,
      H (PrimeSpectrum.comap (retractionMap k) p) = p :=
    congrFun hleft
  let : IrreducibleSpace (Spec (.of B)) := H.irreducibleSpace_iff.mpr inferInstance
  change Set.BijOn f (genericPoints _) (genericPoints _) ∧
    ∀ x, x ∈ genericPoints _ → IsIso (f.stalkMap x)
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    apply Set.bijOn_singleton.mpr
    change PrimeSpectrum.comap (retractionMap k) _ = _
    exact H.injective ((hFH _).trans (homeomorph_genericPoint k).symm)
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    -- The stalk homomorphism is the localization homomorphism at the generic points.
    let p : PrimeSpectrum A := genericPoint (Spec (.of A))
    let q : PrimeSpectrum B := PrimeSpectrum.comap (retractionMap k) p
    let : Semiring (Localization.AtPrime p.asIdeal) :=
      (inferInstance : CommRing (Localization.AtPrime p.asIdeal)).toSemiring
    let : Semiring (Localization.AtPrime q.asIdeal) :=
      (inferInstance : CommRing (Localization.AtPrime q.asIdeal)).toSemiring
    have hp : p.asIdeal = ⊥ := by
      change (genericPoint (Spec (.of A)) : PrimeSpectrum A).asIdeal = ⊥
      rw [genericPoint_eq_bot_of_affine]
      simp
    have hq : q.asIdeal = projectionKernel k := by
      change Ideal.comap (retractionMap k) p.asIdeal = RingHom.ker (retractionMap k)
      rw [hp]
      ext b
      simp [RingHom.mem_ker]
    let eA : Localization.AtPrime p.asIdeal ≃+* FractionRing A :=
      IsLocalization.ringEquivOfRingEquiv
        (S := Localization.AtPrime p.asIdeal) (Q := FractionRing A)
        (R := A) (P := A) (M := p.asIdeal.primeCompl)
        (T := nonZeroDivisors A) (RingEquiv.refl A) (by
          ext a
          simp [hp, mem_nonZeroDivisors_iff_ne_zero])
    let eLoc : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime
        (projectionKernel k) :=
      IsLocalization.ringEquivOfRingEquiv
        (S := Localization.AtPrime q.asIdeal)
        (Q := Localization.AtPrime (projectionKernel k))
        (R := B) (P := B) (M := q.asIdeal.primeCompl)
        (T := (projectionKernel k).primeCompl)
        (RingEquiv.refl B) (by
          ext b
          simp [hq])
    let eB : Localization.AtPrime q.asIdeal ≃+* FractionRing A :=
      eLoc.trans (genericLocalizationEquiv k)
    have hIJ : q.asIdeal = p.asIdeal.comap (retractionMap k) := by
      simp [q]
    let g : Localization.AtPrime q.asIdeal →+* Localization.AtPrime p.asIdeal :=
      Localization.localRingHom q.asIdeal p.asIdeal (retractionMap k) hIJ
    have hgMap (b : B) :
        g (algebraMap B (Localization.AtPrime q.asIdeal) b) =
          algebraMap A (Localization.AtPrime p.asIdeal) ((retractionMap k) b) := by
      change Localization.localRingHom q.asIdeal p.asIdeal (retractionMap k) hIJ
        (algebraMap B (Localization.AtPrime q.asIdeal) b) = _
      rw [Localization.localRingHom_to_map]
    have heA (a : A) :
        eA (algebraMap A (Localization.AtPrime p.asIdeal) a) =
          algebraMap A (FractionRing A) a := by
      simp [eA]
    have heB (b : B) :
        eB (algebraMap B (Localization.AtPrime q.asIdeal) b) =
          algebraMap A (FractionRing A) ((retractionMap k) b) := by
      change genericLocalizationEquiv k
        (eLoc (algebraMap B (Localization.AtPrime q.asIdeal) b)) = _
      have heLocMap : eLoc (algebraMap B (Localization.AtPrime q.asIdeal) b) =
          algebraMap B (Localization.AtPrime (projectionKernel k)) b := by
        simp [eLoc]
      rw [heLocMap, genericLocalizationEquiv_map]
    have hmap : eA.toRingHom.comp g = eB.toRingHom := by
      refine IsLocalization.ringHom_ext q.asIdeal.primeCompl (RingHom.ext fun b ↦ ?_)
      change eA (g (algebraMap B (Localization.AtPrime q.asIdeal) b)) =
        eB (algebraMap B (Localization.AtPrime q.asIdeal) b)
      rw [hgMap, heA, heB]
    have hg : Function.Bijective g := (Function.Bijective.of_comp_iff' eA.bijective g).mp <| by
      rw [show ⇑eA ∘ g = eB from funext (RingHom.congr_fun hmap)]
      exact eB.bijective
    -- Transport the localized isomorphism through the canonical stalk isomorphisms.
    let locIso := Scheme.localRingHom_comp_stalkIso
      (CommRingCat.ofHom (retractionMap k)) (genericPoint (Spec (.of A)))
    change IsIso ((Spec.map (CommRingCat.ofHom (retractionMap k))).stalkMap
      (genericPoint (Spec (.of A))))
    rw [← locIso]
    let : IsIso (CommRingCat.ofHom g) := (ConcreteCategory.isIso_iff_bijective _).2 hg
    change IsIso ((Spec.stalkIso (CommRingCat.of B) q).hom ≫
      CommRingCat.ofHom g ≫ (Spec.stalkIso (CommRingCat.of A) p).inv)
    infer_instance

end AlgebraicGeometry.PolynomialRetract
