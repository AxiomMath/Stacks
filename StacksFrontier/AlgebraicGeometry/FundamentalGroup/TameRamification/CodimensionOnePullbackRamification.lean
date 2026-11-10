module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar

/-!
# Ramification in codimension one survives the codimension-one pullback

A finite étale cover of a dense open subscheme is considered together with a morphism of locally
Noetherian schemes satisfying the boundary hypotheses of
`Stacks.FundamentalGroup.CodimensionOnePullbackSetup`.  If the cover is unramified, respectively
tamely ramified, over the ambient scheme in codimension one, then so is the pulled-back cover over
the source of the morphism.

## Main results

* `Stacks.FundamentalGroup.pulledBackCover_isUnramifiedInCodimensionOne`: the unramified
  conclusion of [Stacks, Tag 0EYD].
* `Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne`: the tamely ramified
  conclusion of the same tag.

The two statements of finiteness and étaleness that the tag also asserts are
`Stacks.FundamentalGroup.pulledBackCover_isFinite` and
`Stacks.FundamentalGroup.pulledBackCover_etale`, proved where the setup is introduced.

## Implementation notes

Fix a boundary point `ξ'` of the source and let `ξ` be its image, a boundary point of the ambient
scheme by hypothesis.  Write `A` and `B` for the two local rings, both discrete valuation rings.
The field-factor data at `ξ'` provides a morphism `Spec K' ⟶ U'` over `Spec B`, and its image in
the ambient scheme lies in the dense open; since the only other point of `Spec A` is the closed
one, which is not in the dense open, the map `A → K'` has trivial kernel.  So the generic point
`η` of `Spec A` lies in the dense open, and the residue field `κ(η)` is a fraction field of `A`:
this is the content of the first section, proved by exhibiting the canonical map from a fraction
field of `A` as an isomorphism onto `κ(η)`.

That makes `κ(η)` the field `K` of the source, and the residue field of the cover at the point `y`
below the given factor is a field factor of the generic fibre over `K`, finite and separable over
it because the cover is finite étale.  The commutative algebra input, Abhyankar's lemma in the
form of [Stacks, Tag 0EXY], then decomposes `K' ⊗_K κ(y)` into fields, each unramified,
respectively tamely ramified, over `B`.  The given factor `L'` is one of them: the image of
`K' ⊗_K κ(y)` in `L'` is a finite `K'`-subalgebra of a field and therefore a field, the cover
restricted to its spectrum maps to the pulled-back cover, and comparing that morphism with the
canonical map from the residue field at the point of the pulled-back cover shows the image is all
of `L'`.

## References

* [Stacks Project, Lemma 58.31.1 (0EYD)](https://stacks.math.columbia.edu/tag/0EYD)
* [Stacks Project, Lemma 15.113.6 (0EXY)](https://stacks.math.columbia.edu/tag/0EXY)
* [Stacks Project, Definition 15.112.1 (09E9)](https://stacks.math.columbia.edu/tag/09E9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace Stacks.FundamentalGroup

/-! ### The residue field at the generic point of the spectrum of a stalk -/

section GenericPoint

variable {X : Scheme.{u}} (x : X) [IsDomain (X.presheaf.stalk x)] {eta : X} (hx : eta ⤳ x)

/-- The canonical map from the stalk at `x` to the residue field at a generization of `x`. -/
private def stalkToResidueField : X.presheaf.stalk x ⟶ X.residueField eta :=
  X.presheaf.stalkSpecializes hx ≫ X.residue eta

omit [IsDomain (X.presheaf.stalk x)] in
private lemma specMap_stalkToResidueField :
    Spec.map (stalkToResidueField x hx) ≫ X.fromSpecStalk x = X.fromSpecResidueField eta := by
  rw [stalkToResidueField, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rfl

/-- A ring map from a domain to a field is injective if some point of the spectrum of the field
pulls back to the generic point. -/
private lemma injective_of_comap_eq_bot {R S : Type*} [CommRing R] [IsDomain R] [Field S]
    (φ : R →+* S) (t : PrimeSpectrum S) (h : PrimeSpectrum.comap φ t = ⊥) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot,
    ← Ideal.eq_bot_of_prime t.asIdeal]
  exact congrArg PrimeSpectrum.asIdeal h

private lemma stalkToResidueField_injective
    (heta : X.fromSpecStalk x (⊥ : PrimeSpectrum (X.presheaf.stalk x)) = eta) :
    Function.Injective (stalkToResidueField x hx).hom := by
  obtain ⟨y⟩ : Nonempty (Spec (X.residueField eta)) := inferInstance
  refine injective_of_comap_eq_bot _ y ?_
  apply (X.fromSpecStalk x).isEmbedding.injective
  rw [← Spec.map_apply, ← Scheme.Hom.comp_apply, specMap_stalkToResidueField, heta]
  exact Scheme.fromSpecResidueField_apply _ _

/-- The residue field at the generic point of `Spec 𝒪_{X, x}` is a fraction field of the
stalk at `x`. -/
private lemma isFractionRing_residueField
    (heta : X.fromSpecStalk x (⊥ : PrimeSpectrum (X.presheaf.stalk x)) = eta) :
    letI := (stalkToResidueField x hx).hom.toAlgebra
    IsFractionRing ((X.presheaf.stalk x : Type u)) ((X.residueField eta : Type u)) := by
  let : Algebra ((X.presheaf.stalk x : Type u)) ((X.residueField eta : Type u)) :=
    (stalkToResidueField x hx).hom.toAlgebra
  have hinj : Function.Injective (stalkToResidueField x hx).hom :=
    stalkToResidueField_injective x hx heta
  have : FaithfulSMul ((X.presheaf.stalk x : Type u)) ((X.residueField eta : Type u)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  set KA : Type u := FractionRing ((X.presheaf.stalk x : Type u)) with hKA
  let psi : KA →+* ((X.residueField eta : Type u)) := IsFractionRing.lift (K := KA) hinj
  have hpsi : ∀ t, psi (algebraMap ((X.presheaf.stalk x : Type u)) KA t)
      = (stalkToResidueField x hx).hom t := IsFractionRing.lift_algebraMap hinj
  let c : CommRingCat.of KA ⟶ X.residueField eta := CommRingCat.ofHom psi
  have hc : CommRingCat.ofHom (algebraMap ((X.presheaf.stalk x : Type u)) KA) ≫ c =
      stalkToResidueField x hx :=
    CommRingCat.hom_ext (RingHom.ext hpsi)
  have hiso : IsIso c := by
    refine isIso_of_specMap_comp_eq_fromSpecResidueField eta c
      (Spec.map (CommRingCat.ofHom (algebraMap ((X.presheaf.stalk x : Type u)) KA)) ≫
        X.fromSpecStalk x) ?_
    rw [← Category.assoc, ← Spec.map_comp, hc, specMap_stalkToResidueField]
  have hsurj : Function.Surjective psi := ((ConcreteCategory.isIso_iff_bijective c).mp hiso).2
  refine IsFractionRing.of_field ((X.presheaf.stalk x : Type u))
    ((X.residueField eta : Type u)) fun z => ?_
  obtain ⟨q, rfl⟩ := hsurj z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ((X.presheaf.stalk x : Type u)))
    (K := KA) q
  refine ⟨a, b, ?_⟩
  rw [map_div₀, hpsi, hpsi]
  rfl

end GenericPoint


/-! ### A field factor of a finite product of fields -/

private theorem exists_algEquiv_of_pi_surjective
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    {E : ι → Type*} [∀ i, Field (E i)] [∀ i, Algebra R (E i)]
    {F : Type*} [Field F] [Algebra R F]
    (f : (∀ i, E i) →ₐ[R] F) (hf : Function.Surjective f) :
    ∃ i, Nonempty (E i ≃ₐ[R] F) := by
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime f.toRingHom⟩ :
      PrimeSpectrum (∀ i, E i))
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  have hker : RingHom.ker (Pi.evalAlgHom R E i).toRingHom ≤ RingHom.ker f.toRingHom :=
    le_of_eq (congrArg PrimeSpectrum.asIdeal hq)
  let g := AlgHom.liftOfSurjective (Pi.evalAlgHom R E i)
    (Function.surjective_eval i) f hker
  exact ⟨i, ⟨AlgEquiv.ofBijective g
    ⟨g.injective, AlgHom.liftOfSurjective_surjective _ _ _ _ hf⟩⟩⟩

/-! ### The pulled-back cover -/

section Key

variable {X X' Y : Scheme.{u}} (g : X' ⟶ X) (U : X.Opens) (f : Y ⟶ U)

/-- The canonical morphism from the pulled-back cover to the inverse-image open subscheme,
unbundled: this is `Stacks.FundamentalGroup.CodimensionOnePullbackSetup.pulledBackCover` with the
data given separately rather than packaged, so that the boundary conditions at a single point can
be carried as instances. -/
private def pbCover : pullback (f ≫ U.ι) g ⟶ pullback g U.ι :=
  pullback.lift (pullback.snd (f ≫ U.ι) g) (pullback.fst (f ≫ U.ι) g ≫ f) (by
    simp only [Category.assoc, pullback.condition])


open IsDiscreteValuationRing in
/-- At a boundary point of `X'` lying over a boundary point of `X`, every field factor of the
generic fibre of the pulled-back cover is unramified, resp. tamely ramified, over the local ring
of `X'` as soon as every field factor downstairs is. -/
private lemma key [IsFinite f] [Etale f]
    (xi' : X') (hxi : g xi' ∉ U)
    [IsDomain (X.presheaf.stalk (g xi'))] [IsDiscreteValuationRing (X.presheaf.stalk (g xi'))]
    [IsDomain (X'.presheaf.stalk xi')] [IsDiscreteValuationRing (X'.presheaf.stalk xi')]
    (K' L' : Type u) [Field K'] [Field L']
    [Algebra (X'.presheaf.stalk xi') K'] [IsFractionRing (X'.presheaf.stalk xi') K']
    [Algebra K' L'] [FiniteDimensional K' L'] [Algebra.IsSeparable K' L']
    [Algebra (X'.presheaf.stalk xi') L'] [IsScalarTower (X'.presheaf.stalk xi') K' L']
    (hFF : IsFieldFactorAt (pullback.fst g U.ι) (pbCover g U f) xi' K' L') :
    ((∀ (K L : Type u) [Field K] [Field L]
        [Algebra (X.presheaf.stalk (g xi')) K] [IsFractionRing (X.presheaf.stalk (g xi')) K]
        [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
        [Algebra (X.presheaf.stalk (g xi')) L] [IsScalarTower (X.presheaf.stalk (g xi')) K L],
        IsFieldFactorAt U.ι f (g xi') K L →
          IsDiscreteValuationRing.IsUnramifiedWithRespectTo (X.presheaf.stalk (g xi')) K L) →
      IsDiscreteValuationRing.IsUnramifiedWithRespectTo (X'.presheaf.stalk xi') K' L') ∧
    ((∀ (K L : Type u) [Field K] [Field L]
        [Algebra (X.presheaf.stalk (g xi')) K] [IsFractionRing (X.presheaf.stalk (g xi')) K]
        [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
        [Algebra (X.presheaf.stalk (g xi')) L] [IsScalarTower (X.presheaf.stalk (g xi')) K L],
        IsFieldFactorAt U.ι f (g xi') K L →
          IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo (X.presheaf.stalk (g xi')) K L) →
      IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo (X'.presheaf.stalk xi') K' L') := by
  classical
  obtain ⟨w, v, hw, hv, e, he⟩ := hFF
  -- name the point of the pulled-back cover carrying the factor
  revert e he
  generalize hy' : v (IsLocalRing.closedPoint L') = y'
  intro e he
  -- the induced extension of local rings and its composite into `K'`
  let phi : X.presheaf.stalk (g xi') ⟶ CommRingCat.of K' :=
    g.stalkMap xi' ≫ CommRingCat.ofHom (algebraMap (X'.presheaf.stalk xi') K')
  have hphi : Spec.map phi ≫ X.fromSpecStalk (g xi')
      = w ≫ pullback.snd g U.ι ≫ U.ι := by
    have h1 : Spec.map phi
        = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk xi') K'))
          ≫ Spec.map (g.stalkMap xi') := Spec.map_comp _ _
    rw [h1, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ← hw, Category.assoc, pullback.condition]
  have hphibot : ∀ t : Spec (CommRingCat.of K'),
      Spec.map phi t = (⊥ : PrimeSpectrum (X.presheaf.stalk (g xi'))) := by
    intro t
    by_contra hb
    have himg : X.fromSpecStalk (g xi') (Spec.map phi t) ∈ Set.range U.ι.base := by
      refine ⟨(w ≫ pullback.snd g U.ι) t, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hphi, Scheme.Hom.comp_apply]
    have : (PrimeSpectrum.asIdeal (Spec.map phi t)).IsPrime := PrimeSpectrum.isPrime _
    rw [(PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal
      fun h => hb (PrimeSpectrum.ext h))) : Spec.map phi t = IsLocalRing.closedPoint _),
      Scheme.fromSpecStalk_closedPoint, Scheme.Opens.range_ι] at himg
    exact hxi himg
  -- the two projections of `v`
  have hv2 : v ≫ pullback.snd (f ≫ U.ι) g
      = Spec.map (CommRingCat.ofHom (algebraMap K' L')) ≫ w ≫ pullback.fst g U.ι := by
    have h1 : pullback.snd (f ≫ U.ι) g = pbCover g U f ≫ pullback.fst g U.ι :=
      (pullback.lift_fst _ _ _).symm
    rw [h1, ← Category.assoc, hv, Category.assoc]
  have hvfst : v ≫ pullback.fst (f ≫ U.ι) g ≫ (f ≫ U.ι)
      = Spec.map (CommRingCat.ofHom (algebraMap K' L')) ≫ Spec.map phi
        ≫ X.fromSpecStalk (g xi') := by
    rw [pullback.condition, ← Category.assoc, hv2, hphi, Category.assoc, Category.assoc,
      pullback.condition]
  -- the image in `X` of the point of `Y` carrying the factor is the generic point of `Spec A`
  have hpt : ∀ t : (Spec (CommRingCat.of L') : Scheme.{u}),
      X.fromSpecStalk (g xi') (⊥ : PrimeSpectrum (X.presheaf.stalk (g xi')))
        = (f ≫ U.ι) (pullback.fst (f ≫ U.ι) g (v t)) := by
    intro t
    have h := congrArg (fun m : Spec (CommRingCat.of L') ⟶ X => m t) hvfst
    simp only [Scheme.Hom.comp_apply, hphibot] at h
    exact h.symm
  have hetapt : X.fromSpecStalk (g xi') (⊥ : PrimeSpectrum (X.presheaf.stalk (g xi')))
      = (f ≫ U.ι) (pullback.fst (f ≫ U.ι) g y') := by
    rw [← hy']
    exact hpt (IsLocalRing.closedPoint L')
  have hspec : ((f ≫ U.ι) (pullback.fst (f ≫ U.ι) g y')) ⤳ g xi' := by
    rw [← hetapt]
    have h : X.fromSpecStalk (g xi') (⊥ : PrimeSpectrum (X.presheaf.stalk (g xi')))
        ∈ Set.range (X.fromSpecStalk (g xi')) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  -- the map from the residue field of `Y` at that point into `L'`
  obtain ⟨kL, hkL⟩ : ∃ kL : Y.residueField (pullback.fst (f ≫ U.ι) g y') ⟶ CommRingCat.of L',
      Spec.map kL ≫ Y.fromSpecResidueField (pullback.fst (f ≫ U.ι) g y')
        = v ≫ pullback.fst (f ≫ U.ι) g := by
    refine ⟨(pullback.fst (f ≫ U.ι) g).residueFieldMap y' ≫ CommRingCat.ofHom e.toRingHom, ?_⟩
    have h1 : Spec.map ((pullback.fst (f ≫ U.ι) g).residueFieldMap y'
          ≫ CommRingCat.ofHom e.toRingHom)
        = Spec.map (CommRingCat.ofHom e.toRingHom)
          ≫ Spec.map ((pullback.fst (f ≫ U.ι) g).residueFieldMap y') := Spec.map_comp _ _
    rw [h1, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, he]
  -- abbreviate the point of `Y` below the factor
  revert hetapt hspec kL hkL
  generalize pullback.fst (f ≫ U.ι) g y' = yy
  intro hetapt hspec kL hkL
  -- the residue field at that point is a fraction field of the local ring at `g xi'`
  let : Algebra (X.presheaf.stalk (g xi')) (X.residueField ((f ≫ U.ι) yy)) :=
    (stalkToResidueField (g xi') hspec).hom.toAlgebra
  have : IsFractionRing (X.presheaf.stalk (g xi')) (X.residueField ((f ≫ U.ι) yy)) :=
    isFractionRing_residueField (g xi') hspec hetapt
  let : Algebra (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy) :=
    ((f ≫ U.ι).residueFieldMap yy).hom.toAlgebra
  have : Module.Finite (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy) :=
    residueField_finite_of_locallyQuasiFinite (f ≫ U.ι) yy
  have : Algebra.IsSeparable (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy) := inferInstance
  let : Algebra (X.presheaf.stalk (g xi')) (Y.residueField yy) :=
    (stalkToResidueField (g xi') hspec ≫ (f ≫ U.ι).residueFieldMap yy).hom.toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g xi')) (X.residueField ((f ≫ U.ι) yy))
      (Y.residueField yy) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the field factor downstairs
  have hrange : Set.range (X.fromSpecResidueField ((f ≫ U.ι) yy)).base ⊆ Set.range U.ι.base := by
    rw [Scheme.range_fromSpecResidueField]
    rintro z hz
    rw [Set.mem_singleton_iff] at hz
    exact ⟨f yy, by rw [hz, Scheme.Hom.comp_apply]⟩
  have hw0 : (IsOpenImmersion.lift U.ι (X.fromSpecResidueField ((f ≫ U.ι) yy)) hrange) ≫ U.ι
      = X.fromSpecResidueField ((f ≫ U.ι) yy) := IsOpenImmersion.lift_fac _ _ _
  have hFF0 : IsFieldFactorAt U.ι f (g xi') (X.residueField ((f ≫ U.ι) yy))
      (Y.residueField yy) := by
    refine ⟨IsOpenImmersion.lift U.ι (X.fromSpecResidueField ((f ≫ U.ι) yy)) hrange,
      Y.fromSpecResidueField yy, ?_, ?_, ?_⟩
    · rw [hw0]
      exact (specMap_stalkToResidueField (g xi') hspec).symm
    · rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hw0]
      exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f ≫ U.ι) yy).symm
    · refine ⟨(Y.residueFieldCongr (Scheme.fromSpecResidueField_apply yy
        (IsLocalRing.closedPoint (Y.residueField yy)))).commRingCatIsoToRingEquiv, ?_⟩
      exact Scheme.residueFieldCongr_fromSpecResidueField
        (Scheme.fromSpecResidueField_apply yy (IsLocalRing.closedPoint (Y.residueField yy)))
  -- the extension of discrete valuation rings `A → B`
  let : Algebra (X.presheaf.stalk (g xi')) (X'.presheaf.stalk xi') :=
    (g.stalkMap xi').hom.toAlgebra
  let : Algebra (X.presheaf.stalk (g xi')) K' := phi.hom.toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g xi')) (X'.presheaf.stalk xi') K' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAK' : Function.Injective (algebraMap (X.presheaf.stalk (g xi')) K') :=
    injective_of_comap_eq_bot _ (⊥ : PrimeSpectrum K') (hphibot (⊥ : PrimeSpectrum K'))
  have : FaithfulSMul (X.presheaf.stalk (g xi')) (X'.presheaf.stalk xi') := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ?_
    have h1 := hAK'
    rw [IsScalarTower.algebraMap_eq (X.presheaf.stalk (g xi')) (X'.presheaf.stalk xi') K'] at h1
    exact Function.Injective.of_comp h1
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g xi')) (X'.presheaf.stalk xi')) :=
    inferInstanceAs (IsLocalHom (g.stalkMap xi').hom)
  have : IsDiscreteValuationRing.IsExtension (X.presheaf.stalk (g xi'))
    (X'.presheaf.stalk xi') := ⟨⟩
  -- the fraction field `K` of `A` maps into `K'` and into `L'`
  let : Algebra (X.residueField ((f ≫ U.ι) yy)) K' :=
    (IsFractionRing.lift (A := (X.presheaf.stalk (g xi')))
      (K := (X.residueField ((f ≫ U.ι) yy))) hAK').toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g xi')) (X.residueField ((f ≫ U.ι) yy)) K' :=
    IsScalarTower.of_algebraMap_eq fun t => (IsFractionRing.lift_algebraMap hAK' t).symm
  let : Algebra (X.residueField ((f ≫ U.ι) yy)) L' :=
    ((algebraMap K' L').comp (algebraMap (X.residueField ((f ≫ U.ι) yy)) K')).toAlgebra
  have : IsScalarTower (X.residueField ((f ≫ U.ι) yy)) K' L' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (X.presheaf.stalk (g xi')) L' := ((algebraMap K' L').comp phi.hom).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g xi')) K' L' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (X.presheaf.stalk (g xi'))
      (X.residueField ((f ≫ U.ι) yy)) L' :=
    IsScalarTower.of_algebraMap_eq fun t => by
      rw [IsScalarTower.algebraMap_apply (X.residueField ((f ≫ U.ι) yy)) K' L',
        ← IsScalarTower.algebraMap_apply (X.presheaf.stalk (g xi'))
          (X.residueField ((f ≫ U.ι) yy)) K']
      rfl
  have hAL : (stalkToResidueField (g xi') hspec ≫ (f ≫ U.ι).residueFieldMap yy) ≫ kL
      = phi ≫ CommRingCat.ofHom (algebraMap K' L') := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (g xi'))]
    simp only [Spec.map_comp, Category.assoc, specMap_stalkToResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Category.assoc (Spec.map kL), hkL, Category.assoc, ← hvfst]
  have hALe : ∀ t : (X.presheaf.stalk (g xi')),
      kL.hom (((f ≫ U.ι).residueFieldMap yy).hom ((stalkToResidueField (g xi') hspec).hom t))
        = algebraMap K' L' (phi.hom t) := by
    intro t
    have h := congrArg (fun m : X.presheaf.stalk (g xi') ⟶ CommRingCat.of L' => m.hom t) hAL
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h
  have hKL : ∀ z : (X.residueField ((f ≫ U.ι) yy)),
      kL.hom (algebraMap (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy) z)
        = algebraMap (X.residueField ((f ≫ U.ι) yy)) L' z := by
    have hext : kL.hom.comp (algebraMap (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy))
        = algebraMap (X.residueField ((f ≫ U.ι) yy)) L' := by
      refine IsFractionRing.ringHom_ext (A := (X.presheaf.stalk (g xi'))) ?_
      intro t
      change kL.hom (algebraMap (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy)
          (algebraMap (X.presheaf.stalk (g xi')) (X.residueField ((f ≫ U.ι) yy)) t))
        = algebraMap (X.residueField ((f ≫ U.ι) yy)) L'
          (algebraMap (X.presheaf.stalk (g xi')) (X.residueField ((f ≫ U.ι) yy)) t)
      rw [← IsScalarTower.algebraMap_apply (X.presheaf.stalk (g xi'))
        (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy),
        ← IsScalarTower.algebraMap_apply (X.presheaf.stalk (g xi'))
          (X.residueField ((f ≫ U.ι) yy)) L']
      exact hALe t
    exact fun z => congrFun (congrArg
      (fun r : (X.residueField ((f ≫ U.ι) yy)) →+* L' =>
        (r : (X.residueField ((f ≫ U.ι) yy)) → L')) hext) z
  -- the surjection from the tensor product onto `L'`
  let qK : (Y.residueField yy) →ₐ[(X.residueField ((f ≫ U.ι) yy))] L' :=
    { kL.hom with commutes' := hKL }
  let q : (K' ⊗[(X.residueField ((f ≫ U.ι) yy))] (Y.residueField yy)) →ₐ[K'] L' :=
    Algebra.TensorProduct.lift (Algebra.ofId K' L') qK fun _ _ => Commute.all _ _
  have hq1 : ∀ x : (Y.residueField yy), q (1 ⊗ₜ[(X.residueField ((f ≫ U.ι) yy))] x) = kL.hom x := by
    intro x
    rw [Algebra.TensorProduct.lift_tmul]
    change algebraMap K' L' 1 * kL.hom x = kL.hom x
    rw [map_one, one_mul]
  have : Module.Finite K' ↥q.range :=
    Module.Finite.of_surjective (AlgHom.toLinearMap q.rangeRestrict) q.rangeRestrict_surjective
  have : Algebra.IsIntegral K' ↥q.range := Algebra.IsIntegral.of_finite K' ↥q.range
  have hSfield : IsField ↥q.range := isField_of_isIntegral_of_isField' (Field.toIsField K')
  let : Field ↥q.range := hSfield.toField
  have hkLmem : ∀ x : (Y.residueField yy), kL.hom x ∈ q.range :=
    fun x => ⟨1 ⊗ₜ[(X.residueField ((f ≫ U.ι) yy))] x, hq1 x⟩
  let kS : (Y.residueField yy) →+* ↥q.range := kL.hom.codRestrict q.range hkLmem
  have hStep : (stalkToResidueField (g xi') hspec ≫ (f ≫ U.ι).residueFieldMap yy)
        ≫ CommRingCat.ofHom kS
      = phi ≫ CommRingCat.ofHom (algebraMap K' ↥q.range) :=
    CommRingCat.hom_ext (RingHom.ext fun t => Subtype.ext (hALe t))
  have hcondS : (Spec.map (CommRingCat.ofHom kS) ≫ Y.fromSpecResidueField yy) ≫ (f ≫ U.ι)
      = (Spec.map (CommRingCat.ofHom (algebraMap K' ↥q.range)) ≫ w ≫ pullback.fst g U.ι) ≫ g := by
    have h1 : Spec.map ((stalkToResidueField (g xi') hspec ≫ (f ≫ U.ι).residueFieldMap yy)
          ≫ CommRingCat.ofHom kS)
        = Spec.map (CommRingCat.ofHom kS)
          ≫ Spec.map (stalkToResidueField (g xi') hspec ≫ (f ≫ U.ι).residueFieldMap yy) :=
      Spec.map_comp _ _
    have h2 : Spec.map (stalkToResidueField (g xi') hspec ≫ (f ≫ U.ι).residueFieldMap yy)
        = Spec.map ((f ≫ U.ι).residueFieldMap yy)
          ≫ Spec.map (stalkToResidueField (g xi') hspec) := Spec.map_comp _ _
    have h3 : Spec.map (phi ≫ CommRingCat.ofHom (algebraMap K' ↥q.range))
        = Spec.map (CommRingCat.ofHom (algebraMap K' ↥q.range)) ≫ Spec.map phi :=
      Spec.map_comp _ _
    have hL : (Spec.map (CommRingCat.ofHom kS) ≫ Y.fromSpecResidueField yy) ≫ (f ≫ U.ι)
        = Spec.map ((stalkToResidueField (g xi') hspec ≫ (f ≫ U.ι).residueFieldMap yy)
          ≫ CommRingCat.ofHom kS) ≫ X.fromSpecStalk (g xi') := by
      rw [h1, h2]
      simp only [Category.assoc, specMap_stalkToResidueField,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [hL, hStep, h3, Category.assoc, hphi]
    simp only [Category.assoc]
    rw [pullback.condition]
  let a : Spec (CommRingCat.of ↥q.range) ⟶ pullback (f ≫ U.ι) g :=
    pullback.lift (Spec.map (CommRingCat.ofHom kS) ≫ Y.fromSpecResidueField yy)
      (Spec.map (CommRingCat.ofHom (algebraMap K' ↥q.range)) ≫ w ≫ pullback.fst g U.ι) hcondS
  have hSval : Spec.map (CommRingCat.ofHom (Subalgebra.val q.range).toRingHom) ≫ a = v := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp]
      change Spec.map kL ≫ Y.fromSpecResidueField yy = _
      rw [hkL]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← Spec.map_comp, hv2]
      rfl
  have hIso : IsIso (CommRingCat.ofHom
      (e.symm.toRingHom.comp (Subalgebra.val q.range).toRingHom) :
        CommRingCat.of ↥q.range ⟶
          (pullback (f ≫ U.ι) g).residueField y') := by
    refine isIso_of_specMap_comp_eq_fromSpecResidueField _ _ a ?_
    have h2 : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ :=
      CommRingCat.hom_ext (RingHom.ext e.symm_apply_apply)
    have h3 : Spec.map (CommRingCat.ofHom e.symm.toRingHom)
        ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
      rw [← Spec.map_comp, h2, Spec.map_id]
    calc Spec.map (CommRingCat.ofHom
            (e.symm.toRingHom.comp (Subalgebra.val q.range).toRingHom)) ≫ a
        = Spec.map (CommRingCat.ofHom e.symm.toRingHom)
            ≫ Spec.map (CommRingCat.ofHom (Subalgebra.val q.range).toRingHom) ≫ a := by
          rw [← Category.assoc]
          exact congrArg (· ≫ a) (Spec.map_comp
            (CommRingCat.ofHom (Subalgebra.val q.range).toRingHom)
            (CommRingCat.ofHom e.symm.toRingHom))
      _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ v := by rw [hSval]
      _ = Spec.map (CommRingCat.ofHom e.symm.toRingHom)
            ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
            ≫ (pullback (f ≫ U.ι) g).fromSpecResidueField
              y' := by rw [he]
      _ = (pullback (f ≫ U.ι) g).fromSpecResidueField y' := by
          rw [← Category.assoc, h3, Category.id_comp]
  have hSsurj : Function.Surjective (Subalgebra.val q.range) := by
    have hbij := (ConcreteCategory.isIso_iff_bijective _).mp hIso
    intro z
    obtain ⟨t, ht⟩ := hbij.2 (e.symm z)
    exact ⟨t, e.symm.injective ht⟩
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨t, ht⟩ := hSsurj z
    obtain ⟨x, hx⟩ := t.2
    exact ⟨x, hx.trans ht⟩
  -- Abhyankar's lemma
  obtain ⟨n, E, hEfield, hEalg, hEalgB, hEtower, hEfin, hEsep, hn, hEeq, hEunr, hEtame⟩ :=
    IsDiscreteValuationRing.exists_algEquiv_pi_field_and_ramification_goes_up
      (X.presheaf.stalk (g xi')) (X'.presheaf.stalk xi') (X.residueField ((f ≫ U.ι) yy)) K'
      (Y.residueField yy)
  let := hEfield
  let := hEalg
  let := hEalgB
  let := hEtower
  let := hEfin
  let := hEsep
  obtain ⟨d⟩ := hEeq
  obtain ⟨i, ⟨eps⟩⟩ := exists_algEquiv_of_pi_surjective (R := K')
    (q.comp d.symm.toAlgHom) (hqsurj.comp d.symm.surjective)
  let : Algebra L' (E i) := eps.symm.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower K' L' (E i) :=
    IsScalarTower.of_algebraMap_eq fun z => (eps.symm.commutes z).symm
  have hepsSurj : Function.Surjective (algebraMap L' (E i)) := eps.symm.surjective
  have : Module.Finite L' (E i) :=
    Module.Finite.of_surjective (Algebra.linearMap L' (E i)) hepsSurj
  have : Algebra.IsSeparable L' (E i) :=
    Algebra.IsSeparable.of_algHom (F := L') (E := E i) (E' := L')
      { eps.toRingEquiv.toRingHom with commutes' := fun z => eps.apply_symm_apply z }
  have : IsScalarTower (X'.presheaf.stalk xi') L' (E i) :=
    IsScalarTower.of_algebraMap_eq fun b => by
      rw [IsScalarTower.algebraMap_apply (X'.presheaf.stalk xi') K' (E i),
        IsScalarTower.algebraMap_apply (X'.presheaf.stalk xi') K' L']
      exact (eps.symm.commutes _).symm
  refine ⟨fun hun => ?_, fun htm => ?_⟩
  · exact (isUnramifiedWithRespectTo_of_tower_and_exists_isGalois_and_common_extension
      (X'.presheaf.stalk xi') K').1 L' (E i)
      (hEunr (hun (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy) hFF0) i)
  · exact isTamelyRamified_of_isTamelyRamified_tower (X'.presheaf.stalk xi') K' L' (E i)
      (hEtame (htm (X.residueField ((f ≫ U.ι) yy)) (Y.residueField yy) hFF0) i)

end Key

/-! ### The two conclusions of Tag 0EYD -/

private lemma transport_dvr {X : Scheme.{u}} {x y : X} (h : x = y)
    (hy : ∃ _ : IsDomain (X.presheaf.stalk y), IsDiscreteValuationRing (X.presheaf.stalk y)) :
    ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) := by
  subst h
  exact hy

/-- **Stacks 0EYD**, unramified half. If the cover `Y → U` is unramified over `X` in
codimension one, then the pulled-back cover is unramified over `X'` in codimension one. -/
@[stacks 0EYD "unramified_in_codimension_one"]
public theorem pulledBackCover_isUnramifiedInCodimensionOne
    (D : CodimensionOnePullbackSetup.{u})
    (h : IsUnramifiedInCodimensionOne D.U.ι D.f) :
    IsUnramifiedInCodimensionOne (pullback.fst D.g D.U.ι) D.pulledBackCover := by
  intro Z' hZ' hDB hVB K' L' _ _ _ _ _ _ _ _ _ hFF
  have := hDB
  have := hVB
  have := D.finite_f
  have := D.etale_f
  obtain ⟨Z, hZU, hZg⟩ := D.maps_boundary Z' hZ'
  obtain ⟨hDA, hVA⟩ := transport_dvr hZg (D.dvr_X Z hZU)
  have := hDA
  have := hVA
  have hh := h Z (by rwa [Scheme.Opens.range_ι])
  rw [← hZg] at hh hZU
  exact (key D.g D.U D.f Z'.genericPoint hZU K' L' hFF).1 (hh hDA hVA)

/-- **Stacks 0EYD**, tamely ramified half. If the cover `Y → U` is tamely ramified over `X` in
codimension one, then the pulled-back cover is tamely ramified over `X'` in codimension one. -/
@[stacks 0EYD "tamely_ramified_in_codimension_one",
  sga "1 XIII 2.0.2" "partial",
  sga "1 XIII 2.0.3" "more general"]
public theorem pulledBackCover_isTamelyRamifiedInCodimensionOne
    (D : CodimensionOnePullbackSetup.{u})
    (h : IsTamelyRamifiedInCodimensionOne D.U.ι D.f) :
    IsTamelyRamifiedInCodimensionOne (pullback.fst D.g D.U.ι) D.pulledBackCover := by
  intro Z' hZ' hDB hVB K' L' _ _ _ _ _ _ _ _ _ hFF
  have := hDB
  have := hVB
  have := D.finite_f
  have := D.etale_f
  obtain ⟨Z, hZU, hZg⟩ := D.maps_boundary Z' hZ'
  obtain ⟨hDA, hVA⟩ := transport_dvr hZg (D.dvr_X Z hZU)
  have := hDA
  have := hVA
  have hh := h Z (by rwa [Scheme.Opens.range_ι])
  rw [← hZg] at hh hZU
  exact (key D.g D.U D.f Z'.genericPoint hZU K' L' hFF).2 (hh hDA hVA)

end Stacks.FundamentalGroup
