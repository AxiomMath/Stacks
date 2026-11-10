module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.DevissageTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension

/-!
# Stacks 02TT for the affine line

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. This file proves the
generic decomposition of `StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage` for
affine-space bundles of rank one, which by the devissage gives Stacks 02TT in rank one, and in
particular the surjectivity of flat pullback along the projection `𝔸¹_B ⟶ B` for every base `B`.

This is the last paragraph of the proof of Stacks 02TT. Let `W ⊆ Y × 𝔸¹` be an integral closed
subscheme dominating an integral `Y`, with generic point `w`. If `W = Y × 𝔸¹` then `[W]` is the
flat pullback of `[Y]`. Otherwise, over an affine open `Spec A ⊆ Y` the point `w` is a nonzero
prime of `A[X]` lying over zero, and on a basic open `D(s)` of `Spec A[X]` its prime cycle is a
principal divisor (`Stacks.Chow.exists_principalCycle_polyBasicOpen_eq_single`); the points
outside `D(s)` lie over `V(s)`, away from the generic point of `Spec A`. So `[w]` is rationally
equivalent to a cycle not dominating the base, which is the generic decomposition.

The passage from an arbitrary rank-one bundle to `Spec A[X] ⟶ Spec A` is a chain of open
immersions and isomorphisms of the base and of the bundle, along which the generic decomposition
descends by `Stacks.Chow.hasGenericDecomposition_of_isOpenImmersion_square`.

## Main results

* `Stacks.Chow.hasGenericDecomposition_specMap_C` — the generic decomposition for
  `Spec A[X] ⟶ Spec A` over a domain `A`.
* `Stacks.Chow.genericDecompositionHolds_one` — the generic decomposition for every affine-space
  bundle of rank one over an integral base.
* `Stacks.Chow.flatPullbackChow_surjective_affineLine` — **Stacks 02TT** for the projection of
  the affine line `𝔸¹_B ⟶ B`.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-! ### `Spec A[X]` as the affine line over `Spec A` -/

section SpecPolynomial

variable (R : CommRingCat.{u})

/-- The isomorphism of `R`-algebras between polynomials in the one variable `ULift (Fin 1)` and
polynomials in one variable. -/
def mvPolynomialULiftFinOneEquiv : MvPolynomial (ULift.{u} (Fin 1)) R ≃ₐ[R] Polynomial R :=
  (MvPolynomial.renameEquiv R (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit.{u + 1})).trans
    (MvPolynomial.uniqueAlgEquiv R PUnit.{u + 1})

/-- The identification of `Spec R[X]` with the affine line over `Spec R`. -/
def specPolynomialToAffineLine :
    Spec (CommRingCat.of (Polynomial R)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec R) :=
  Spec.map (CommRingCat.ofHom (mvPolynomialULiftFinOneEquiv R).toRingHom) ≫
    (AffineSpace.SpecIso _ R).inv

/-- The identification of `Spec R[X]` with the affine line over `Spec R` is an isomorphism. -/
instance : IsIso (specPolynomialToAffineLine R) := by
  have : IsIso (CommRingCat.ofHom (mvPolynomialULiftFinOneEquiv R).toRingHom) :=
    (mvPolynomialULiftFinOneEquiv R).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold specPolynomialToAffineLine
  infer_instance

/-- The identification of `Spec R[X]` with the affine line over `Spec R` is one of schemes over
`Spec R`. -/
@[reassoc]
theorem specPolynomialToAffineLine_over :
    specPolynomialToAffineLine R ≫ (𝔸(ULift.{u} (Fin 1); Spec R) ↘ Spec R) =
      Spec.map (CommRingCat.ofHom (C : R →+* Polynomial R)) := by
  rw [specPolynomialToAffineLine, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_))
  change (mvPolynomialULiftFinOneEquiv R) (MvPolynomial.C a) = C a
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_eq]

/-- The structure morphism `Spec R[X] ⟶ Spec R` is locally of finite type. -/
instance : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (C : R →+* Polynomial R))) := by
  rw [← specPolynomialToAffineLine_over]
  infer_instance

/-- The structure morphism `Spec R[X] ⟶ Spec R` is flat. -/
instance : Flat (Spec.map (CommRingCat.ofHom (C : R →+* Polynomial R))) := by
  rw [← specPolynomialToAffineLine_over]
  infer_instance

/-- `Spec R[X] ⟶ Spec R` has relative dimension one, being isomorphic to the projection of the
affine line. -/
theorem relativeDimension_specMap_C :
    AlgebraicGeometry.RelativeDimension (Spec.map (CommRingCat.ofHom (C : R →+* Polynomial R)))
      1 := by
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat (specPolynomialToAffineLine R)
    (𝔸(ULift.{u} (Fin 1); Spec R) ↘ Spec R) (relativeDimension_of_isIso _)
    (relativeDimension_affineSpaceOver (Spec R) 1)
  rw [Nat.zero_add] at h
  have key : ∀ (g : Spec (CommRingCat.of (Polynomial R)) ⟶ Spec R) [LocallyOfFiniteType g],
      g = specPolynomialToAffineLine R ≫ (𝔸(ULift.{u} (Fin 1); Spec R) ↘ Spec R) →
        AlgebraicGeometry.RelativeDimension g 1 := by
    intro g _ hg
    subst hg
    exact h
  exact key _ (specPolynomialToAffineLine_over R).symm

end SpecPolynomial

/-! ### The generic decomposition for `Spec A[X] ⟶ Spec A` -/

/-- **The generic decomposition for the affine line over an affine integral base.** Let `A` be a
domain with `Spec A` locally of finite type over the base and let `w` be a point of `Spec A[X]`
of delta-dimension `k + 1` lying over the generic point of `Spec A`. Then `[w]` has a generic
decomposition for `Spec A[X] ⟶ Spec A`.

If `w` is the generic point, `[w]` is the flat pullback of the fundamental cycle of `Spec A`
(Stacks 02R8 gives the delta-dimension of `Spec A` as `k`). Otherwise `w` is a nonzero prime
lying over zero; on a basic open `D(s)`, `s ≠ 0`, its prime cycle is the principal divisor of a
rational function, hence rationally equivalent to zero there, and the points outside `D(s)` lie
over `V(s)`, away from the image of `w`. -/
theorem hasGenericDecomposition_specMap_C (C : ChowSituation.{u}) (R : CommRingCat.{u})
    [IsDomain R] (sR : Spec R ⟶ C.S) [LocallyOfFiniteType sR] (k : ℤ)
    (w : Spec (CommRingCat.of (Polynomial R)))
    (hw : relativeDimension C.dimensionFunction
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ sR) w =
        k + ((1 : ℕ) : ℤ))
    (hgen : ∀ b, (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).base w ⤳ b) :
    HasGenericDecomposition C
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ sR) sR
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) rfl 1
      (relativeDimension_specMap_C R) k w := by
  set q := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) with hqdef
  have : IsNoetherianRing R :=
    isLocallyNoetherian_Spec.mp (LocallyOfFiniteType.isLocallyNoetherian sR)
  have hqw : ((q.base w).asIdeal : Ideal R) =
      w.asIdeal.comap (Polynomial.C : R →+* Polynomial R) := rfl
  have hcomap : w.asIdeal.comap (Polynomial.C : R →+* Polynomial R) = ⊥ := by
    have h : (q.base w).asIdeal ≤ ⊥ :=
      (PrimeSpectrum.le_iff_specializes (q.base w) ⟨⊥, inferInstance⟩).mpr
        (hgen ⟨⊥, inferInstance⟩)
    exact le_bot_iff.mp (hqw ▸ h)
  by_cases hw0 : w.asIdeal = ⊥
  · -- `w` is the generic point: `[w]` is the flat pullback of the fundamental cycle.
    have hwgen : genericPoint (Spec (CommRingCat.of (Polynomial R))) = w :=
      (genericPoint_eq_bot_of_affine _).trans (PrimeSpectrum.ext hw0.symm)
    have hRgen : genericPoint (Spec R) = q.base w :=
      (genericPoint_eq_bot_of_affine _).trans (PrimeSpectrum.ext (hqw.trans hcomap).symm)
    have hdimX := schemeDeltaDimension_comp_eq_add C sR q 1 (relativeDimension_specMap_C R)
      fun V ↦ ⟨w, by
        have hV : (V : Set (Spec R)) = Set.univ := by
          simpa [irreducibleComponents_eq_singleton] using V.2
        rw [hV]
        trivial⟩
    rw [schemeDeltaDimension_eq_genericPoint, schemeDeltaDimension_eq_genericPoint, hwgen, hw,
      hRgen] at hdimX
    have hRk : relativeDimension C.dimensionFunction sR (q.base w) = k := by
      rw [← coe_add_coe_eq_coe_add] at hdimX
      have h := WithBotTop.coe_injective hdimX
      push_cast at h
      omega
    have hfund := flatPullback_fundamentalCycle C (q ≫ sR) sR q rfl 1
      (relativeDimension_specMap_C R) k (by
        rw [schemeDeltaDimension_eq_genericPoint, hRgen, hRk])
    refine ⟨hw, fundamentalCycle C sR k, 0, fun t ht ↦ absurd rfl ht, ?_⟩
    rw [hfund, sub_zero]
    convert zero_mem (rationalEquivalences C (q ≫ sR) (k + ((1 : ℕ) : ℤ)))
    rw [sub_eq_zero]
    refine Subtype.ext ?_
    have hid : (𝟙 (Spec (CommRingCat.of (Polynomial R))) :
        Spec (CommRingCat.of (Polynomial R)) ⟶ _).base
          (genericPoint (Spec (CommRingCat.of (Polynomial R)))) = w := hwgen
    rw [fundamentalCycle, cycleAssociatedToClosedSubscheme_eq_single C (q ≫ sR) (𝟙 _) _
      (by rw [hid, hw]), hid]
    refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
    rw [pointCycle_apply, @Function.locallyFinsuppWithin.single_apply _ _ _ (Classical.decEq _)]
  · -- `w` is a nonzero prime over zero: `[w]` is a principal divisor on `D(s)`.
    obtain ⟨s, hs0, hws, hdiv⟩ := exists_principalCycle_polyBasicOpen_eq_single w hcomap hw0
    set D := polyBasicOpen s with hD
    have : Nonempty D := ⟨⟨w, hws⟩⟩
    have : IsIntegral D.toScheme := isIntegral_of_isOpenImmersion D.ι
    have : IsLocallyNoetherian D.toScheme :=
      LocallyOfFiniteType.isLocallyNoetherian (D.ι ≫ q ≫ sR)
    obtain ⟨g, hg0, hgdiv⟩ := hdiv
    set wD : D.toScheme := ⟨w, hws⟩ with hwDdef
    have hgpt : ∀ y : D.toScheme, D.toScheme.ord g y =
        @ite _ (y = wD) (Classical.propDecidable _) 1 0 := by
      intro y
      have h1 : (principalCycle D.toScheme g) y = _ := congrArg (fun c ↦ c y) hgdiv
      rw [principalCycle_apply] at h1
      rw [h1]
      exact @Function.locallyFinsuppWithin.single_apply _ _ _ (Classical.decEq _) _ _ _ _
    have hrelD : AlgebraicGeometry.RelativeDimension (D.ι ≫ q) 1 := by
      have h := AlgebraicGeometry.RelativeDimension.comp_of_flat D.ι q
        (relativeDimension_of_isOpenImmersion D.ι) (relativeDimension_specMap_C R)
      rwa [Nat.zero_add] at h
    have hwD : D.ι.base wD = w := rfl
    rw [← hwD]
    refine hasGenericDecomposition_of_isOpenImmersion_square C (q ≫ sR) sR (D.ι ≫ q ≫ sR) sR q
      rfl 1 (relativeDimension_specMap_C R) D.ι rfl (𝟙 _) (Category.id_comp _) (D.ι ≫ q)
      (Category.assoc _ _ _) (Category.comp_id _).symm hrelD k wD ?_ ?_
    · -- points outside `D(s)` lie over `V(s)`, away from the image of `w`
      intro t ht heq
      refine ht ⟨⟨t, fun hts ↦ ?_⟩, rfl⟩
      have hst : s ∈ ((q.base t).asIdeal : Ideal R) := hts
      rw [heq, hwD, hqw, hcomap] at hst
      exact hs0 hst
    · have hwdim : relativeDimension C.dimensionFunction (D.ι ≫ q ≫ sR) wD =
          k + ((1 : ℕ) : ℤ) := by
        rw [relativeDimension_comp_isOpenImmersion, hwD, hw]
      refine ⟨hwdim, 0, 0, fun t ht ↦ absurd rfl ht, ?_⟩
      rw [map_zero, sub_zero, sub_zero]
      -- the delta-dimension of `D(s)` is `k + 2`
      have hcoh : Order.coheight wD = 1 := by
        by_contra hne
        have h0 := Scheme.ord_eq_zero_of_coheight_neq_one hne g
        have h1 := hgpt wD
        rw [h0, ite_eq_left rfl] at h1
        exact zero_ne_one h1
      have hn := schemeDeltaDimension_eq_genericPoint C (D.ι ≫ q ≫ sR)
      have hsub := (relativeDimension_eq_sub_one_iff_coheight_eq_one C (D.ι ≫ q ≫ sR) hn
        wD).mpr hcoh
      rw [hwdim] at hsub
      refine isRationallyEquivalentToZero_of_eq_principalCycle C (D.ι ≫ q ≫ sR)
        (k := k + ((1 : ℕ) : ℤ)) ?_ hg0 _ ?_
      · rw [hn]
        congr 1
        omega
      · refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
        rw [principalCycle_apply, hgpt y, pointCycle_apply]

/-! ### From an arbitrary rank-one bundle to `Spec A[X] ⟶ Spec A` -/

/-- The image of the first projection of a pullback square of schemes is the preimage of the
image of the opposite leg. -/
theorem range_fst_of_isPullback {P X Y S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (H : IsPullback fst snd f g) :
    Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  have hsurj : Function.Surjective H.isoPullback.hom.base := fun z ↦
    ⟨H.isoPullback.inv.base z, Scheme.inv_hom_apply _ z⟩
  rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_fst]

/-- Along an open immersion `mA : A' ⟶ A` over the base, the relative dimension of a point of
`A'` is that of its image. -/
theorem relativeDimension_eq_of_isOpenImmersion (C : ChowSituation.{u}) {A A' : Scheme.{u}}
    (sA : A ⟶ C.S) (mA : A' ⟶ A) [IsOpenImmersion mA] (sA' : A' ⟶ C.S) (hmA : mA ≫ sA = sA')
    (t : A') :
    relativeDimension C.dimensionFunction sA' t =
      relativeDimension C.dimensionFunction sA (mA.base t) := by
  rw [← hmA, relativeDimension_comp_isOpenImmersion]

/-- A point whose image under an open immersion specializes to every point of the target
specializes to every point of the source. -/
theorem specializes_of_isOpenImmersion {B B' : Scheme.{u}} (mB : B' ⟶ B) [IsOpenImmersion mB]
    {b : B'} (h : ∀ c : B, mB.base b ⤳ c) (c : B') : b ⤳ c :=
  mB.isOpenEmbedding.isInducing.specializes_iff.mp (h _)

/-- **The generic decomposition for affine-space bundles of rank one.** Every affine-space bundle
of rank one over an integral base has a generic decomposition in every degree at every point over
the generic point of the base.

The bundle is trivial over an open neighbourhood `U` of the image of the point
(`Stacks.Chow.hasGenericDecomposition_of_trivialization`); the trivial bundle `𝔸¹_U` restricts
to `𝔸¹_V` over an affine open `V ⊆ U`; and `𝔸¹_V` is isomorphic over `V ≅ Spec A` to
`Spec A[X] ⟶ Spec A`, where `Stacks.Chow.hasGenericDecomposition_specMap_C` applies. The
decomposition descends along each step by
`Stacks.Chow.hasGenericDecomposition_of_isOpenImmersion_square`. -/
theorem genericDecompositionHolds_one (C : ChowSituation.{u}) (k : ℤ) :
    GenericDecompositionHolds C 1 k := by
  intro A B sA _ sB _ q _ _ hq hr hbundle hB w hw hgen
  obtain ⟨U, hwU, e, he⟩ := hbundle (q.base w)
  set w0 : (q ⁻¹ᵁ U).toScheme := ⟨w, hwU⟩ with hw0def
  have hw0 : (q ⁻¹ᵁ U).ι.base w0 = w := rfl
  rw [← hw0]
  refine hasGenericDecomposition_of_trivialization C sA sB q hq 1 hr U e he k w0 ?_
  set pU := 𝔸(ULift.{u} (Fin 1); U.toScheme) ↘ U.toScheme with hpU
  set w1 := e.hom.base w0 with hw1def
  have hwe : e.inv.base w1 = w0 := Scheme.hom_inv_apply e w0
  have hmAs : (e.inv ≫ (q ⁻¹ᵁ U).ι) ≫ sA = pU ≫ U.ι ≫ sB := by
    rw [← hq, Category.assoc, ← Category.assoc (q ⁻¹ᵁ U).ι, ← morphismRestrict_ι, ← he]
    simp
  have hUw1 : U.ι.base (pU.base w1) = q.base w := by
    have h : (e.hom ≫ pU ≫ U.ι).base w0 = ((q ⁻¹ᵁ U).ι ≫ q).base w0 := by
      rw [← Category.assoc, he, morphismRestrict_ι]
    simp only [Scheme.Hom.comp_apply] at h
    exact h
  have hgen1 : ∀ c : U.toScheme, pU.base w1 ⤳ c :=
    specializes_of_isOpenImmersion U.ι (fun c ↦ hUw1 ▸ hgen c)
  have hdim1 : relativeDimension C.dimensionFunction (pU ≫ U.ι ≫ sB) w1 = k + ((1 : ℕ) : ℤ) := by
    rw [relativeDimension_eq_of_isOpenImmersion C sA (e.inv ≫ (q ⁻¹ᵁ U).ι) _ hmAs,
      Scheme.Hom.comp_apply, hwe, hw0, hw]
  -- an affine open of `U` around the image of `w1`
  obtain ⟨V, hV, hw1V⟩ : ∃ V : U.toScheme.Opens, IsAffineOpen V ∧ pU.base w1 ∈ V := by
    obtain ⟨-, ⟨W, hW, rfl⟩, hW1, -⟩ :=
      U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (pU.base w1))
        isOpen_univ
    exact ⟨W, hW, hW1⟩
  set pV := 𝔸(ULift.{u} (Fin 1); V.toScheme) ↘ V.toScheme with hpV
  have Hpb := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) V.ι
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin 1)) V.ι) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) Hpb.flip inferInstance
  have hrange2 := range_fst_of_isPullback Hpb
  obtain ⟨w2, hw2⟩ : w1 ∈ Set.range (AffineSpace.map (ULift.{u} (Fin 1)) V.ι).base := by
    rw [hrange2, Scheme.Opens.range_ι]
    exact hw1V
  have hmA2 : AffineSpace.map (ULift.{u} (Fin 1)) V.ι ≫ pU ≫ U.ι ≫ sB =
      pV ≫ V.ι ≫ U.ι ≫ sB := by
    rw [AffineSpace.map_over_assoc]
  have hpt2 : V.ι.base (pV.base w2) = pU.base w1 := by
    rw [← hw2, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, AffineSpace.map_over]
  rw [← hw2]
  refine hasGenericDecomposition_of_isOpenImmersion_square C (pU ≫ U.ι ≫ sB) (U.ι ≫ sB)
    (pV ≫ V.ι ≫ U.ι ≫ sB) (V.ι ≫ U.ι ≫ sB) pU rfl 1
    (relativeDimension_affineSpaceOver U.toScheme 1) (AffineSpace.map (ULift.{u} (Fin 1)) V.ι)
    hmA2 V.ι rfl pV rfl (AffineSpace.map_over V.ι)
    (relativeDimension_affineSpaceOver V.toScheme 1) k w2 (fun t ht heq ↦ ht ?_) ?_
  · rw [hrange2, Set.mem_preimage, heq, ← Scheme.Hom.comp_apply, AffineSpace.map_over,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hgen2 : ∀ c : V.toScheme, pV.base w2 ⤳ c :=
    specializes_of_isOpenImmersion V.ι (fun c ↦ hpt2 ▸ hgen1 c)
  have hdim2 : relativeDimension C.dimensionFunction (pV ≫ V.ι ≫ U.ι ≫ sB) w2 =
      k + ((1 : ℕ) : ℤ) := by
    rw [relativeDimension_eq_of_isOpenImmersion C _ _ _ hmA2, hw2, hdim1]
  -- the affine open `V` is `Spec R`, and `𝔸¹_V` is `Spec R[X]`
  have : Nonempty U.toScheme := ⟨pU.base w1⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : Nonempty V := ⟨⟨_, hw1V⟩⟩
  set R : CommRingCat.{u} := Γ(U.toScheme, V) with hR
  have : IsDomain R := IsIntegral.component_integral V
  set φ := hV.isoSpec with hφ
  have Hpb3 := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) φ.inv
  have : IsIso (AffineSpace.map (ULift.{u} (Fin 1)) φ.inv) := Hpb3.isIso_fst_of_isIso
  set mA3 := specPolynomialToAffineLine R ≫ AffineSpace.map (ULift.{u} (Fin 1)) φ.inv
    with hmA3def
  set qR := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) with hqR
  have hsq3 : mA3 ≫ pV = qR ≫ φ.inv := by
    rw [hmA3def, Category.assoc, AffineSpace.map_over, specPolynomialToAffineLine_over_assoc]
  have hmA3 : mA3 ≫ pV ≫ V.ι ≫ U.ι ≫ sB = qR ≫ φ.inv ≫ V.ι ≫ U.ι ≫ sB := by
    rw [← Category.assoc, hsq3, Category.assoc]
  set w3 := (inv mA3).base w2 with hw3def
  have hinv : ∀ t, mA3.base ((inv mA3).base t) = t := Scheme.inv_hom_apply (asIso mA3)
  have hw3 : mA3.base w3 = w2 := hinv w2
  rw [← hw3]
  refine hasGenericDecomposition_of_isOpenImmersion_square C (pV ≫ V.ι ≫ U.ι ≫ sB)
    (V.ι ≫ U.ι ≫ sB) (qR ≫ φ.inv ≫ V.ι ≫ U.ι ≫ sB) (φ.inv ≫ V.ι ≫ U.ι ≫ sB) pV rfl 1
    (relativeDimension_affineSpaceOver V.toScheme 1) mA3 hmA3 φ.inv rfl qR rfl hsq3
    (relativeDimension_specMap_C R) k w3 (fun t ht ↦ absurd ⟨_, hinv t⟩ ht) ?_
  refine hasGenericDecomposition_specMap_C C R (φ.inv ≫ V.ι ≫ U.ι ≫ sB) k w3 ?_ ?_
  · rw [← hmA3, relativeDimension_eq_of_isOpenImmersion C _ mA3 _ rfl, hw3, hdim2]
  · have hpt3 : φ.inv.base (qR.base w3) = pV.base w2 := by
      have h := congrArg (fun ψ : Spec (CommRingCat.of (Polynomial R)) ⟶ V.toScheme ↦
        ψ.base w3) hsq3
      simp only [Scheme.Hom.comp_apply] at h
      rw [← hw3]
      exact h.symm
    exact specializes_of_isOpenImmersion φ.inv (fun c ↦ hpt3 ▸ hgen2 c)

end Stacks.Chow

end
