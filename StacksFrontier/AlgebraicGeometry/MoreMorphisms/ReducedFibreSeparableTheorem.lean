module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSeparableGeneric
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSeparableSolution
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTheorem
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduced fibre theorem with a separable extension

Let `A` be a Nagata Dedekind domain with fraction field `K` and let `f : X ⟶ Spec A` be flat,
quasi-compact and locally of finite type, such that the residue field at every generic point of
an irreducible component of `X` is separable over `K`.  **Then there is a finite separable
extension `L / K` such that, with `B` the integral closure of `A` in `L`, the normalization of
`X ×_{Spec A} Spec B` is smooth over `Spec B` at every generic point of every one of its
fibres.**  This is Tag 0BRR.

The proof is that of the reduced fibre theorem, Tag 09IL, with two changes.  The first paragraph
needs no extension at all: under the separability hypothesis the reduction of the generic fibre
already carries a dense smooth open
(`AlgebraicGeometry.exists_dense_open_smooth_reduction_pullback_of_isSeparableExtension`), so the
first replacement is along the integral closure of `A` in `K` itself.  The last paragraph uses the
separable form of elimination of ramification, Tag 0BRP, in place of Tag 09II; its separability
hypothesis at a bad point `x` — that the fraction field of `𝒪_{X, x}` is separable over `K` — is
supplied by the dense smooth open of the generic fibre
(`AlgebraicGeometry.isSeparableExtension_stalkFractionRing_of_dense_open_smooth`): the generic
point of the component through `x` lies in the smooth locus, where the local ring is a field
formally smooth over `K`.  The two normalized base changes are then composed exactly as in the
main theorem (`AlgebraicGeometry.smoothAt_asFiber_genericPoints_normalization_pullback_of_tower`).

## Main results

* `AlgebraicGeometry.isSeparableExtension_stalkFractionRing_of_dense_open_smooth`: over a
  Dedekind base, a dense smooth open of the generic fibre of a normal flat scheme makes the
  fraction field of every local ring separable over `K`.
* `AlgebraicGeometry.exists_finite_separable_forall_isSeparableSolution_of_dense_open_smooth`:
  one finite separable extension is a separable solution at every bad point.
* `exists_finiteSeparableExtension_smoothAt_asFiber_genericPoints_normalization_pullback`:
  Tag 0BRR for a fraction field in the scheme's own universe.
* `exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_pullback`:
  **Tag 0BRR.**

All declarations are in the namespace `AlgebraicGeometry`.

## Implementation notes

The separability hypothesis is stated as in the source, at the generic points of `X`, over the
residue field of `Spec A` at the image point and through the residue field map of `f`; flatness
makes that image the generic point of `Spec A`, whose residue field is `K`.  Separability is the
notion of Tag 030O, `Algebra.IsSeparableExtension`, which does not ask the extension to be
algebraic; the extension `L / K` produced is finite, and its separability is Mathlib's
`Algebra.IsSeparable`.

The conclusion has exactly the shape of
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`,
Tag 09IL, with separability of `L / K` added, and the fraction field is again allowed its own
universe.

## References

* [Stacks Project, Tag 0BRR](https://stacks.math.columbia.edu/tag/0BRR)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 0BRP](https://stacks.math.columbia.edu/tag/0BRP)
* [Stacks Project, Tag 04KS](https://stacks.math.columbia.edu/tag/04KS)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

/-- Every point of a quasi-sober space is a specialization of the generic point of an
irreducible component. -/
theorem exists_mem_genericPoints_specializes {α : Type*} [TopologicalSpace α] [QuasiSober α]
    (y : α) : ∃ η ∈ genericPoints α, η ⤳ y := by
  let c : irreducibleComponents α := ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
  exact ⟨(genericPoints.ofComponent c).1, (genericPoints.ofComponent c).2,
    (genericPoints.isGenericPoint_ofComponent c).specializes mem_irreducibleComponent⟩

namespace AlgebraicGeometry

/-- The local ring at a generalization which is a field is the fraction field: if `η ⤳ y` and
the local ring at `η` is a field while the local ring at `y` is a domain, then the
specialization map exhibits `𝒪_{X, η}` as the fraction field of `𝒪_{X, y}`. -/
theorem isFractionRing_stalkSpecializes {X : Scheme.{u}} {η y : X} (h : η ⤳ y)
    [IsDomain (X.presheaf.stalk y)] (hη : IsField (X.presheaf.stalk η)) :
    letI : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk y) (X.presheaf.stalk η) := by
  let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  set P := (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).under (X.presheaf.stalk y) with hP
  have : IsLocalization.AtPrime (X.presheaf.stalk η) P :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk y) (X.presheaf.stalk η)) :=
    IsLocalization.injective (M := P.primeCompl) _ (Ideal.primeCompl_le_nonZeroDivisors P)
  have hPbot : P = ⊥ := by
    rw [hP, Ideal.under, IsLocalRing.isField_iff_maximalIdeal_eq.1 hη]
    exact Ideal.comap_bot_of_injective _ hinj
  have hM : P.primeCompl = nonZeroDivisors (X.presheaf.stalk y) := by
    ext a
    simp [hPbot, mem_nonZeroDivisors_iff_ne_zero]
  rw [IsFractionRing, ← hM]
  infer_instance

section Separability

variable {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R))

/-- At a point over the generic point of a domain, the structure map of the fraction field over
the local ring of the base is bijective. -/
theorem bijective_algebraLocalizationAtPrimeBase (η : Y) (h : (g.base η).asIdeal = ⊥) :
    letI : (g.base η).asIdeal.IsPrime := (g.base η).isPrime
    letI := algebraLocalizationAtPrimeBase K g η
    Function.Bijective (algebraMap (Localization.AtPrime (g.base η).asIdeal) K) := by
  let : (g.base η).asIdeal.IsPrime := (g.base η).isPrime
  let := algebraLocalizationAtPrimeBase K g η
  have := isScalarTower_localizationAtPrimeBase K g η
  have := isFractionRing_localizationAtPrimeBase K g η
  refine ⟨IsFractionRing.injective _ K, fun k ↦ ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) k
  have hs : (s : R) ∈ (g.base η).asIdeal.primeCompl := by
    change (s : R) ∉ (g.base η).asIdeal
    rw [h]
    exact nonZeroDivisors.coe_ne_zero s
  refine ⟨IsLocalization.mk' (Localization.AtPrime (g.base η).asIdeal) r ⟨s, hs⟩, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq,
    IsScalarTower.algebraMap_apply R (Localization.AtPrime (g.base η).asIdeal) K,
    IsScalarTower.algebraMap_apply R (Localization.AtPrime (g.base η).asIdeal) K r, ← map_mul]
  congr 1
  exact IsLocalization.mk'_spec (Localization.AtPrime (g.base η).asIdeal) r ⟨s, hs⟩

variable [Flat g] [LocallyOfFiniteType g] [IsNormal Y]

/-- **A dense smooth open of the generic fibre makes every local ring's fraction field separable
over `K`.** Let `R` be a Dedekind domain with fraction field `K` and let `g : Y ⟶ Spec R` be
flat and locally of finite type with `Y` normal, whose generic fibre has a dense open subscheme
smooth over the residue field there. Then for every point `y` of `Y` the fraction field of the
local ring `𝒪_{Y, y}` is a separable extension of `K`.

The generic point `η` of the irreducible component through `y` lies over the generic point of
`Spec R`, by flatness, and is a generic point of the generic fibre, hence lies in the smooth
locus of `g`. So `K ⟶ 𝒪_{Y, η}` is formally smooth, and `𝒪_{Y, η}` is the fraction field of
the domain `𝒪_{Y, y}`; a formally smooth field extension is separable. -/
@[sga "1 II 5.7" "partial"]
theorem isSeparableExtension_stalkFractionRing_of_dense_open_smooth
    (U : (g.fiber (genericPoint (Spec (.of R)))).Opens)
    (hU : Dense (U : Set (g.fiber (genericPoint (Spec (.of R))))))
    (hsmooth : Smooth (U.ι ≫ g.fiberToSpecResidueField (genericPoint (Spec (.of R)))))
    (y : Y) :
    letI : (g.base y).asIdeal.IsPrime := (g.base y).isPrime
    letI := algebraStalkFractionRing K g y
    Algebra.IsSeparableExtension K (FractionRing (Y.presheaf.stalk y)) := by
  let : (g.base y).asIdeal.IsPrime := (g.base y).isPrime
  let := stalkAlgebraOfSpecHom g y
  let := algebraLocalizationAtPrimeBase K g y
  have := isScalarTower_localizationAtPrimeBase K g y
  have := isFractionRing_localizationAtPrimeBase K g y
  let := algebraStalkFractionRing K g y
  have := isScalarTower_stalkFractionRing K g y
  obtain ⟨η, hη, hηy⟩ := exists_mem_genericPoints_specializes y
  -- the generic point `η` lies over the generic point of the base, and in the smooth locus
  have hgη : g.base η = genericPoint (Spec (.of R)) := by
    have h := g.mem_genericPoints_of_flat hη
    rwa [genericPoints_eq_singleton] at h
  have hgηbot : (g.base η).asIdeal = ⊥ := by
    rw [hgη, genericPoint_eq_bot_of_affine]
    rfl
  have hgen : g.asFiber η ∈ genericPoints (g.fiber (g.base η)) := by
    refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun b hb ↦
      (g.fiberι _).isEmbedding.injective ?_
    rw [g.fiberι_asFiber]
    refine (mem_genericPoints_iff_forall_specializes_eq η).1 hη _ ?_
    simpa [g.fiberι_asFiber] using hb.map (g.fiberι _).continuous
  have hsm := mem_smoothLocus_of_mem_genericPoints_fiber_of_dense_open_smooth g _ U hU hsmooth
    hgη hgen
  rw [Scheme.Hom.mem_smoothLocus] at hsm
  let : (g.base η).asIdeal.IsPrime := (g.base η).isPrime
  have H1 : (localizationAtPrimeToStalk g η).hom.FormallySmooth :=
    (formallySmooth_comp_iff_of_isIso_left _ _).2 hsm
  -- the fraction field of `𝒪_{Y, y}` is `𝒪_{Y, η}`
  let : Algebra (Y.presheaf.stalk y) (Y.presheaf.stalk η) :=
    (Y.presheaf.stalkSpecializes hηy).hom.toAlgebra
  have := isFractionRing_stalkSpecializes hηy
    (isField_stalk_of_closure_mem_irreducibleComponents Y η hη)
  let eF : FractionRing (Y.presheaf.stalk y) ≃ₐ[Y.presheaf.stalk y] Y.presheaf.stalk η :=
    IsLocalization.algEquiv (nonZeroDivisors _) _ _
  -- the fraction field of `A` is the local ring of the base at the generic point
  let := algebraLocalizationAtPrimeBase K g η
  have := isScalarTower_localizationAtPrimeBase K g η
  let ea : Localization.AtPrime (g.base η).asIdeal ≃+* K :=
    RingEquiv.ofBijective _ (bijective_algebraLocalizationAtPrimeBase K g η hgηbot)
  have hcat : CommRingCat.ofHom
        (algebraMap (CommRingCat.of R) (Localization.AtPrime (g.base y).asIdeal)) ≫
      localizationAtPrimeToStalk g y ≫ Y.presheaf.stalkSpecializes hηy =
      CommRingCat.ofHom
        (algebraMap (CommRingCat.of R) (Localization.AtPrime (g.base η).asIdeal)) ≫
        localizationAtPrimeToStalk g η := by
    have h1 := Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) (g.base y)
    have h2 := Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) (g.base η)
    have e1 := congrArg (· ≫ g.stalkMap y ≫ Y.presheaf.stalkSpecializes hηy) h1
    have e2 := congrArg (· ≫ g.stalkMap η) h2
    simp only [Category.assoc] at e1 e2
    simp only [localizationAtPrimeToStalk, Category.assoc]
    have e3 : (Spec (.of R)).presheaf.germ ⊤ (g.base y) (by simp) ≫ g.stalkMap y ≫
        Y.presheaf.stalkSpecializes hηy =
        (Spec (.of R)).presheaf.germ ⊤ (g.base η) (by simp) ≫ g.stalkMap η := by
      rw [Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.germ_stalkMap]
      congr 1
      exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
    exact (e1.trans (congrArg (fun φ ↦ (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ) e3)).trans
      e2.symm
  have key : (eF.toRingEquiv.toRingHom.comp
      (algebraMap K (FractionRing (Y.presheaf.stalk y)))).comp ea.toRingHom =
      (localizationAtPrimeToStalk g η).hom := by
    apply IsLocalization.ringHom_ext (g.base η).asIdeal.primeCompl
    ext r
    have hc := congrArg (fun φ ↦ φ.hom r) hcat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hc
    simp only [RingHom.comp_apply]
    rw [show ea.toRingHom (algebraMap R _ r) = algebraMap R K r from
        (IsScalarTower.algebraMap_apply R _ K r).symm,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime (g.base y).asIdeal) K,
      ← IsScalarTower.algebraMap_apply (Localization.AtPrime (g.base y).asIdeal) K,
      IsScalarTower.algebraMap_apply (Localization.AtPrime (g.base y).asIdeal)
        (Y.presheaf.stalk y)]
    exact (eF.commutes _).trans hc
  have hφ : algebraMap K (FractionRing (Y.presheaf.stalk y)) =
      (eF.symm.toRingEquiv.toRingHom.comp (localizationAtPrimeToStalk g η).hom).comp
        ea.symm.toRingHom := by
    rw [← key]
    ext k
    simp
  have hfs : (algebraMap K (FractionRing (Y.presheaf.stalk y))).FormallySmooth := by
    rw [hφ]
    exact RingHom.FormallySmooth.respectsIso.2 _ ea.symm
      (RingHom.FormallySmooth.respectsIso.1 _ eF.symm.toRingEquiv H1)
  exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).1
    (RingHom.formallySmooth_algebraMap.1 hfs)

end Separability

/-! ### The bad points -/

section BadPoints

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [IsNormal X]

/-- **One finite separable extension solving every bad generic point at once.** Let `A` be a
Nagata Dedekind domain with fraction field `K` and let `f : X ⟶ Spec A` be flat, quasi-compact
and locally of finite type with `X` normal, whose generic fibre has a dense open subscheme `U`
smooth over the residue field there. Then there is a finite **separable** extension `K₁ / K`
which is a separable solution for the extension of discrete valuation rings `A_x → 𝒪_{X, x}` at
every point `x` outside the smooth locus of `f` which is a generic point of its own fibre, that
fibre not the generic one.

The bad points are finitely many by Tag 054X, and at each of them the fraction field of the
local ring is separable over `K`
(`AlgebraicGeometry.isSeparableExtension_stalkFractionRing_of_dense_open_smooth`), so the
separable form of elimination of ramification, Tag 0BRP, applies to all of them at once
(`AlgebraicGeometry.exists_finite_extension_forall_isSeparableSolution_stalk`). -/
theorem exists_finite_separable_forall_isSeparableSolution_of_dense_open_smooth
    [QuasiCompact f] (hA : IsNagataRing A)
    (U : (f.fiber (genericPoint (Spec (.of A)))).Opens)
    (hU : Dense (U : Set (f.fiber (genericPoint (Spec (.of A))))))
    (hsmooth : Smooth (U.ι ≫ f.fiberToSpecResidueField (genericPoint (Spec (.of A))))) :
    letI : LocallyOfFinitePresentation f := inferInstance
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁)
      (_ : Algebra.IsSeparable K K₁),
      ∀ x : X, x ∉ f.smoothLocus → ∀ (hs : (f.base x).asIdeal ≠ ⊥)
        (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x))),
        IsSeparableSolutionForStalk K f x hs hg K₁ := by
  classical
  have _ : LocallyOfFinitePresentation f := inferInstance
  set S : Set X := {x : X | (x ∉ f.smoothLocus ∧
    f.asFiber x ∈ genericPoints (f.fiber (f.base x))) ∧ (f.base x).asIdeal ≠ ⊥} with hS
  have hSfin : S.Finite :=
    (finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber f U hU hsmooth).subset
      fun _ hx => hx.1
  let _ : Fintype ↥S := hSfin.fintype
  let e : ↥S ≃ Fin (Fintype.card ↥S) := Fintype.equivFin ↥S
  let x' : Fin (Fintype.card ↥S) → X := fun i => (e.symm i : X)
  have hmem : ∀ i, x' i ∈ S := fun i => (e.symm i).2
  obtain ⟨K₁, hfield, halg, hmodfin, hsepK, hsol⟩ :=
    exists_finite_extension_forall_isSeparableSolution_stalk K f hA x'
      (fun i => (hmem i).2) (fun i => (hmem i).1.2)
      (fun i => isSeparableExtension_stalkFractionRing_of_dense_open_smooth K f U hU hsmooth _)
  let _ := hfield
  let _ := halg
  have _ := hmodfin
  refine ⟨K₁, hfield, halg, hmodfin, hsepK, fun x hx hs hg => ?_⟩
  have hxS : x ∈ S := ⟨⟨hx, hg⟩, hs⟩
  have hxe : x' (e ⟨x, hxS⟩) = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hxS⟩)
  exact isSeparableSolutionForStalk_congr K f hxe _ _ hs hg K₁ (hsol (e ⟨x, hxS⟩))

end BadPoints

/-! ### The reduced fibre theorem with a separable extension -/

/-- **The variant of the reduced fibre theorem with a separable extension, for a fraction field
in the scheme's own universe.**  Let `A` be a Nagata Dedekind domain with fraction field `K` and
let `f : X ⟶ Spec A` be flat, quasi-compact and locally of finite type, such that the residue
field at every generic point of an irreducible component of `X` is separable over the residue
field of `Spec A` below it.  Then there is a finite separable extension `L / K` such that, with
`B` the integral closure of `A` in `L`, the normalization of `X ×_{Spec A} Spec B` is smooth over
`Spec B` at every point which is a generic point of its own fibre.

The first paragraph of the proof needs no extension: the reduction of the generic fibre already
has a dense smooth open
(`AlgebraicGeometry.exists_dense_open_smooth_reduction_pullback_of_isSeparableExtension`), so `X`
is replaced by the normalization `Y₀` of its base change to the integral closure `B₀` of `A` in
`K` itself.  The last paragraph runs with the separable form of elimination of ramification
(`AlgebraicGeometry.exists_finite_separable_forall_isSeparableSolution_of_dense_open_smooth`),
and the two normalized base changes are composed as in the main theorem
(`AlgebraicGeometry.smoothAt_asFiber_genericPoints_normalization_pullback_of_tower`). -/
theorem exists_finiteSeparableExtension_smoothAt_asFiber_genericPoints_normalization_pullback
    {A : Type u} [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] (hA : IsNagataRing A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hsep : ∀ x : X, x ∈ genericPoints X →
      letI : Algebra ((Spec (.of A)).residueField (f x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension ((Spec (.of A)).residueField (f x)) (X.residueField x)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (_ : Algebra A L) (_ : IsScalarTower A K L),
      ∀ hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite,
      ∀ z : (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L)))) : Scheme.{u}).normalizationScheme hW,
      (Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L))))).asFiber z ∈
        genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map
          (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))).fiber
            ((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap A ↥(integralClosure A L))))).base z)) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))) z := by
  -- the first paragraph: the reduction of the generic fibre has a dense smooth open already
  obtain ⟨Z, ρ, hci, hsurj, hZred, -, U, hU, hsm⟩ :=
    exists_dense_open_smooth_reduction_pullback_of_isSeparableExtension K f hsep
  have := hci
  have := hZred
  let : IsDedekindDomain ↥(integralClosure A K) :=
    isDedekindDomain_integralClosure_of_isNagataRing K K hA
  have : IsFractionRing ↥(integralClosure A K) K :=
    integralClosure.isFractionRing_of_finite_extension K K
  have hB₀ : IsNagataRing ↥(integralClosure A K) := isNagataRing_integralClosure K K hA
  obtain ⟨Z', ρ', hci', hker', U', hU', hsm'⟩ :=
    exists_reduction_dense_open_smooth_pullbackLeftPullbackSndIso f
      (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A K))))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(integralClosure A K) K)))
      (Spec.map (CommRingCat.ofHom (algebraMap A K)))
      (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq A ↥(integralClosure A K) K])
      ρ hsurj U hU hsm
  have := hci'
  obtain ⟨V, hVdense, hVsmooth⟩ :=
    exists_dense_open_smooth_fiber_genericPoint_normalization_pullback K f _ _ ρ' hker' U' hU'
      hsm'
  obtain ⟨hnorm₀, hflat₀, hlft₀, hqc₀⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K K hA f
  have := hnorm₀
  have := hflat₀
  have := hlft₀
  have := hqc₀
  -- the last paragraph, with a separable solution at every bad point
  obtain ⟨L, hLfield, hLalg, hLfin, hLsep, hsol⟩ :=
    exists_finite_separable_forall_isSeparableSolution_of_dense_open_smooth K _
      hB₀ V hVdense hVsmooth
  let := hLfield
  let := hLalg
  have := hLfin
  let : Algebra ↥(integralClosure A K) L :=
    ((algebraMap K L).comp (algebraMap ↥(integralClosure A K) K)).toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := ↥(integralClosure A K)) (S := K) (A := L)
    fun _ ↦ rfl
  have hsmL := smoothAt_normalization_pullback_of_forall_isSolutionForStalk K _ hB₀ V hVdense
    hVsmooth L fun x hx hs hg ↦ (hsol x hx hs hg).isSolutionForStalk
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ⟨L, hLfield, hLalg, hLfin, hLsep, inferInstance, inferInstance,
    smoothAt_asFiber_genericPoints_normalization_pullback_of_tower K hA f K L rfl
      (fun _ ↦ hsmL)⟩

/-- **Stacks Project, Tag 0BRR (the reduced fibre theorem with a separable extension).**  Let `A`
be a Dedekind domain with fraction field `K` and let `f : X ⟶ Spec A` be flat, quasi-compact and
locally of finite type.  Assume `A` is a Nagata ring and that for every generic point `η` of an
irreducible component of `X` the residue field `κ(η)` is a separable extension of `K`.  Then there
is a finite separable extension `L / K` such that, with `B` the integral closure of `A` in `L`,
the normalization `Y` of `X ×_{Spec A} Spec B` is smooth over `Spec B` at every generic point of
every one of the fibres of `Y ⟶ Spec B`.

The separability hypothesis is stated over the residue field of `Spec A` at `f η`, through the
residue field map of `f`: since `f` is flat, `f η` is the generic point of `Spec A`, whose residue
field is the fraction field `K`, so this is the separability of `κ(η) / K` of the source, for the
notion of separability of Tag 030O which does not require `κ(η) / K` to be algebraic.

The fraction field is allowed its own universe: the statement is the one in the scheme's universe
transported along the `A`-algebra isomorphism `K ≃ₐ[A] FractionRing A`, as for Tag 09IL. -/
@[stacks 0BRR]
theorem exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_pullback
    {A : Type u} [CommRing A] [IsDedekindDomain A] (K : Type v) [Field K]
    [Algebra A K] [IsFractionRing A K] (hA : IsNagataRing A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hsep : ∀ x : X, x ∈ genericPoints X →
      letI : Algebra ((Spec (.of A)).residueField (f x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension ((Spec (.of A)).residueField (f x)) (X.residueField x)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (_ : Algebra A L) (_ : IsScalarTower A K L),
      ∃ hW : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u}).Opens,
        IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L)))) : Scheme.{u})) →
        (irreducibleComponents U).Finite,
      ∀ b : Spec (.of ↥(integralClosure A L)),
      ∀ y : (Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A ↥(integralClosure A L))))).fiber b,
      y ∈ genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map
        (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))).fiber b) →
      InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L)))))
        ((Scheme.normalization _ hW ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (algebraMap A ↥(integralClosure A L))))).fiberι b y) := by
  obtain ⟨L, hLfield, hFL, hFLfin, hFLsep, hAL, hAFL, hconc⟩ :=
    exists_finiteSeparableExtension_smoothAt_asFiber_genericPoints_normalization_pullback
      (FractionRing A) hA f hsep
  let := hLfield
  let := hFL
  have := hFLfin
  have := hFLsep
  let := hAL
  have := hAFL
  -- the two fraction fields of `A`, identified
  let e : K ≃ₐ[A] FractionRing A :=
    IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A)
  let : Algebra K (FractionRing A) := (e : K →+* FractionRing A).toAlgebra
  let : Algebra K L := ((algebraMap (FractionRing A) L).comp (e : K →+* FractionRing A)).toAlgebra
  have : IsScalarTower K (FractionRing A) L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite K (FractionRing A) :=
    Module.Finite.of_surjective (Algebra.linearMap K (FractionRing A)) fun x ↦
      ⟨e.symm x, e.apply_symm_apply x⟩
  have : FiniteDimensional K L := Module.Finite.trans (FractionRing A) L
  have : Algebra.IsSeparable K L :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) (by
      ext x
      change algebraMap (FractionRing A) L (e (e.symm x)) = _
      rw [e.apply_symm_apply]
      rfl)
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    have h1 : algebraMap K L (algebraMap A K a)
        = algebraMap (FractionRing A) L (e (algebraMap A K a)) := rfl
    rw [h1, e.commutes a, ← IsScalarTower.algebraMap_apply A (FractionRing A) L]
  -- the finiteness witness the normalization needs is a theorem, not a hypothesis
  have : IsDedekindDomain (integralClosure A L) :=
    isDedekindDomain_integralClosure_of_isNagataRing K L hA
  refine ⟨L, hLfield, inferInstance, inferInstance, inferInstance, hAL, inferInstance,
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A ↥(integralClosure A L))))),
    fun b y hy ↦ ?_⟩
  exact hconc _ _ (mem_genericPoints_asFiber_fiberι _ b y hy)

end AlgebraicGeometry

end
