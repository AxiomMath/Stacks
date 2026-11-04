module

public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.GaloisGenericFibreModel
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.GaloisEssentialImage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperResiduallyTrivial
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverNoetherianExtension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FractionFieldFibre
public import StacksFrontier.RingTheory.DiscreteValuationRing.StrictlyHenselianIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothSectionHenselian
public import StacksCore.Tactic.StacksAttribute

/-!
# Specialization maps in residue characteristic zero are isomorphisms

This file completes [Stacks, Tag 0C0Q]. What the library already had was the reduction of the tag
to one statement
(`AlgebraicGeometry.bijective_isSpecializationMap_of_ringChar_zero_of_forall_essImage_isGalois`):
over a strictly henselian discrete valuation ring `R` whose residue field is algebraically closed
of characteristic zero, every Galois object of `FÉt_{Y_η̄}` — `η̄` the geometric generic point of
`Spec R`, `h : Y ⟶ Spec R` smooth proper with geometrically connected fibres — is the base change
along `Y_η̄ ⟶ Y` of a finite étale cover of `Y`. That statement is proved here, which is the last
paragraph of the source's proof, and the tag is attached to the composition.

The route, with `K = Frac R` and `k̄` the algebraic closure of `K` inside the residue field of
`η̄`:

* the cover descends from `Y_η̄` to `Y_{k̄}` by [Stacks, Tag 0A49], re-presented over the tower
  `Spec k̄ ⟶ Spec K ⟶ Spec R`;
* it comes from a finite subextension `K(s)` of `k̄/K`;
* `h` has a section, which base changes to sections of all the stages, and the cover acquires a
  `K(t)`-rational point over that section at some larger stage `K(t)`; transporting the cover
  from the stage `s` to the stage `t` needs connectedness of the *total space* of the transported
  cover, which is
  `AlgebraicGeometry.AlgebraicExtensionLimit.connectedSpace_pullback_stageTransition` below;
* with `L = K(t)` and `B'` the integral closure of `R` in `L`, again a strictly henselian
  discrete valuation ring with the same residue field, the stage `Y_L` is the generic fibre of
  `Y_{B'} ⟶ Spec B'`, the two section-induced rational points agree, and the order of the Galois
  group is invertible on `Spec B'` because the residue characteristic is zero, so
  [Stacks, Tag 0EYJ] extends the cover over `Y_{B'}`;
* `R ⟶ B'` is residually trivial, so the extension descends to `Y` by [Stacks, Tag 0A48], and
  the base changes compose to `Y_η̄ ⟶ Y`.

## Main results

* `AlgebraicGeometry.connectedSpace_of_iso`, `AlgebraicGeometry.connectedSpace_left_of_iso` and
  `AlgebraicGeometry.connectedSpace_left_finiteEtaleBaseChange_of_isIso` — connectedness along an
  isomorphism of schemes, of finite étale covers, and after base change along an isomorphism.
* `AlgebraicGeometry.ringChar_quotient_maximalIdeal_eq_zero` — the characteristic of the
  scheme-theoretic residue field at the closed point of the spectrum of a local ring is the
  residue characteristic of the ring.
* `AlgebraicGeometry.AlgebraicExtensionLimit.connectedSpace_pullback_stageTransition` — a scheme
  over a stage stays connected after transport to a later stage, as soon as its transport to
  `X_{Kbar}` is connected.
* `AlgebraicGeometry.exists_isIso_comp_specMap_eq_fromSpecResidueField` — the residue field at
  the generic point of the spectrum of a domain is its fraction field, compatibly with the
  canonical morphism down to the spectrum.
* `AlgebraicGeometry.isPullback_fiberι_genericPoint_comp` — the generic fibre of a base change
  along a domain is a base change of the original family along the fraction field.
* `AlgebraicGeometry.exists_galoisCover_stage_model_of_isGalois` and
  `AlgebraicGeometry.exists_finiteEtale_model_of_galoisCover_stage` — the two halves of the
  descent, meeting at a Galois cover of a finite stage with a rational point over a section.
* `AlgebraicGeometry.exists_finiteEtale_model_of_isGalois_geometricGenericFibre` — the residual
  input of [Stacks, Tag 0C0Q].
* `AlgebraicGeometry.bijective_isSpecializationMap_of_ringChar_zero` — [Stacks, Tag 0C0Q].

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0C0P](https://stacks.math.columbia.edu/tag/0C0P)
* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory IsLocalRing

universe v u

namespace AlgebraicGeometry

/-! ### Connectedness along an isomorphism -/

/-- **An isomorphic scheme is connected.** The underlying map of an isomorphism is surjective,
and a continuous surjective image of a connected space is connected. -/
theorem connectedSpace_of_iso {A B : Scheme.{u}} (θ : A ≅ B) [ConnectedSpace ↥A] :
    ConnectedSpace ↥B := by
  have hsurj : Function.Surjective θ.hom.base := fun y ↦
    ⟨θ.inv.base y, by rw [← Scheme.Hom.comp_apply, θ.inv_hom_id]; rfl⟩
  rw [connectedSpace_iff_univ, ← Set.range_eq_univ.mpr hsurj]
  exact isConnected_range θ.hom.continuous

/-- **Isomorphic finite étale covers have isomorphic, hence equally connected, total spaces.** -/
theorem connectedSpace_left_of_iso {X : Scheme.{u}} {A B : FiniteEtaleOver X} (φ : A ≅ B)
    [ConnectedSpace ↥A.left] : ConnectedSpace ↥B.left :=
  connectedSpace_of_iso
    { hom := φ.hom.left
      inv := φ.inv.left
      hom_inv_id := congrArg (fun ψ : A ⟶ A ↦ ψ.left) φ.hom_inv_id
      inv_hom_id := congrArg (fun ψ : B ⟶ B ↦ ψ.left) φ.inv_hom_id }

/-- **The base change of a finite étale cover along an isomorphism of the base has connected
total space** as soon as the cover does: the projection to the cover is an isomorphism. -/
theorem connectedSpace_left_finiteEtaleBaseChange_of_isIso {S T : Scheme.{u}} (θ : T ⟶ S)
    [IsIso θ] (A : FiniteEtaleOver S) [ConnectedSpace ↥A.left] :
    ConnectedSpace ↥((finiteEtaleBaseChange θ).obj A).left := by
  have h1 : IsPullback (𝟙 A.left) (A.hom ≫ inv θ) A.hom θ :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.id_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩
  exact connectedSpace_of_iso (h1.isoIsPullback _ _ (IsPullback.of_hasPullback A.hom θ))

/-! ### The residue characteristic of a local ring, read on its spectrum -/

/-- **A local ring whose scheme-theoretic residue field at the closed point has characteristic
zero has residue characteristic zero.** The residue field of `Spec R` at the closed point is
isomorphic to the residue field of the prime ideal `m`
(`AlgebraicGeometry.Scheme.Spec.residueFieldIso`),
which receives `R ⧸ m` (`Ideal.ResidueField`), so characteristic zero passes down.

This is the bridge needed to feed `Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar`,
which is stated for `R ⧸ m`, from a hypothesis stated on `(Spec R).residueField`. -/
theorem ringChar_quotient_maximalIdeal_eq_zero {R : Type u} [CommRing R] [IsLocalRing R]
    (h : ringChar ((Spec (.of R)).residueField (closedPoint R)) = 0) :
    ringChar (R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
  rw [CharP.ringChar_zero_iff_CharZero] at h ⊢
  have h2 : CharZero ((IsLocalRing.maximalIdeal R).ResidueField) :=
    RingHom.charZero (Scheme.Spec.residueFieldIso (.of R) (closedPoint R)).inv.hom
  exact RingHom.charZero
    (algebraMap (R ⧸ IsLocalRing.maximalIdeal R) ((IsLocalRing.maximalIdeal R).ResidueField))

/-! ### The residue field of the generic point of an affine integral base -/

/-- **The canonical morphism out of the residue field at the generic point is the base change to
the fraction field.** For a domain `A` with fraction field `K` there is an isomorphism
`Spec κ(η) ≅ Spec K` over `Spec A`, i.e. one whose composite with `Spec K ⟶ Spec A` is
`AlgebraicGeometry.Scheme.fromSpecResidueField`.

This strengthens `AlgebraicGeometry.exists_isIso_isPullback_fiberι_genericPoint`, which records
only the cartesian square that follows: composing the square
`AlgebraicGeometry.isPullback_fiberι_fiberToSpecResidueField` with the isomorphism on the right
through `CategoryTheory.IsPullback.comp_isIso_right` gives that statement back. The equation over
`Spec A` is what identifies the rational point of a generic fibre given by a section with the
rational point of a base change to the fraction field. -/
@[ega "II 7.3.2" "partial"]
theorem exists_isIso_comp_specMap_eq_fromSpecResidueField {A : Type u} [CommRing A] [IsDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    ∃ i : Spec ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) ⟶ Spec (.of K),
      IsIso i ∧ i ≫ Spec.map (CommRingCat.ofHom (algebraMap A K))
        = (Spec (.of A)).fromSpecResidueField (genericPoint (Spec (.of A))) := by
  have _ : IsDomain (CommRingCat.of A) := inferInstanceAs (IsDomain A)
  let κ := (Spec (.of A)).residueField (genericPoint (Spec (.of A)))
  let _ : Algebra (CommRingCat.of A) κ :=
    specResidueFieldAlgebra (CommRingCat.of A) (genericPoint (Spec (.of A)))
  have _ : IsFractionRing (CommRingCat.of A) κ :=
    isFractionRing_specResidueField_genericPoint (CommRingCat.of A)
  let ψ : K ≃ₐ[A] κ := IsLocalization.algEquiv (nonZeroDivisors A) K κ
  let ι : CommRingCat.of K ≅ CommRingCat.of κ := ψ.toRingEquiv.toCommRingCatIso
  refine ⟨Spec.map ι.hom, inferInstance, ?_⟩
  have hcomp : CommRingCat.ofHom (algebraMap A K) ≫ ι.hom =
      CommRingCat.ofHom (algebraMap (CommRingCat.of A) κ) := by
    ext a
    exact ψ.commutes a
  rw [← Spec.map_comp, hcomp, ← fromSpecResidueField_eq_specMap]

/-! ### The stages of a base change along an algebraic extension, as base changes of the family -/

namespace AlgebraicExtensionLimit

variable (K Kbar : Type u) [Field K] [Field Kbar] [Algebra K Kbar]

/-- **A base change of a base change is a base change.** For `h : Y ⟶ S`, a morphism
`a : Z ⟶ S` and `c : W ⟶ Z`, the scheme `W ×_Z (Y ×_S Z)` is a base change of `h` along
`c ≫ a`. -/
theorem isPullback_pullback_comp {Y S Z W : Scheme.{u}} (h : Y ⟶ S) (a : Z ⟶ S) (c : W ⟶ Z) :
    IsPullback (pullback.snd c (pullback.snd h a) ≫ pullback.fst h a)
      (pullback.fst c (pullback.snd h a)) h (c ≫ a) :=
  (IsPullback.of_hasPullback c (pullback.snd h a)).flip.paste_horiz
    (IsPullback.of_hasPullback h a)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- **A cover of a stage stays connected after transport to a later stage** as soon as its
transport to `X_{Kbar}` is connected: the projection `X_{Kbar} ⟶ X_{K(t)}` is surjective
(`AlgebraicGeometry.AlgebraicExtensionLimit.flat_and_surjective_and_quasiCompact_bcProj`), the
projection from `X_{Kbar}` factors through the transition morphism
(`AlgebraicGeometry.AlgebraicExtensionLimit.bcProj_comp_stageTransition`), and so the base change
of a scheme over `X_{K(s)}` to `X_{Kbar}` surjects onto its base change to `X_{K(t)}`.

This is the connectedness obligation of `AlgebraicGeometry.FiniteEtaleGaloisCover.baseChange`
along a transition morphism of the stages: it asks for connectedness of the *total space* of the
transported cover, not of its base. -/
@[ega "III 4.3.4" "special case", ega "IV 4.4.1" "special case"]
theorem connectedSpace_pullback_stageTransition [Algebra.IsAlgebraic K Kbar]
    {s t : Finset Kbar} (e : Opposite.op t ⟶ Opposite.op s)
    {W : Scheme.{u}} (p : W ⟶ pullback (stageHom K Kbar s) f)
    [ConnectedSpace ↥(pullback p (AdjoinFinset.bcProj K Kbar f (Opposite.op s)))] :
    ConnectedSpace ↥(pullback p (stageTransition K Kbar f e)) := by
  have hbc : AdjoinFinset.bcProj K Kbar f (Opposite.op t) ≫ stageTransition K Kbar f e
      = AdjoinFinset.bcProj K Kbar f (Opposite.op s) :=
    bcProj_comp_stageTransition K Kbar f e
  let φ : pullback p (AdjoinFinset.bcProj K Kbar f (Opposite.op s)) ⟶
      pullback p (stageTransition K Kbar f e) :=
    pullback.lift (pullback.fst p (AdjoinFinset.bcProj K Kbar f (Opposite.op s)))
      (pullback.snd p (AdjoinFinset.bcProj K Kbar f (Opposite.op s)) ≫
        AdjoinFinset.bcProj K Kbar f (Opposite.op t)) (by
      rw [Category.assoc, hbc]
      exact pullback.condition)
  have hout : IsPullback (φ ≫ pullback.fst p (stageTransition K Kbar f e))
      (pullback.snd p (AdjoinFinset.bcProj K Kbar f (Opposite.op s))) p
      (AdjoinFinset.bcProj K Kbar f (Opposite.op t) ≫ stageTransition K Kbar f e) := by
    rw [hbc, show φ ≫ pullback.fst p (stageTransition K Kbar f e)
        = pullback.fst p (AdjoinFinset.bcProj K Kbar f (Opposite.op s)) from
      pullback.lift_fst _ _ _]
    exact IsPullback.of_hasPullback _ _
  have hsq : IsPullback φ (pullback.snd p (AdjoinFinset.bcProj K Kbar f (Opposite.op s)))
      (pullback.snd p (stageTransition K Kbar f e))
      (AdjoinFinset.bcProj K Kbar f (Opposite.op t)) :=
    IsPullback.of_right hout (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have hsurj : Surjective φ := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
    (flat_and_surjective_and_quasiCompact_bcProj K Kbar f (Opposite.op t)).2.1
  rw [connectedSpace_iff_univ, ← Set.range_eq_univ.mpr hsurj.1]
  exact isConnected_range φ.continuous

/-- **A Galois cover of a stage, transported to a later stage, acquires a rational point over the
section there**, and its transport to `X_{Kbar}` is unchanged. -/
theorem exists_stage_point_baseChange_stageTransition [Algebra.IsAlgebraic K Kbar]
    [IsAlgClosed Kbar] (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (s : Finset Kbar)
    [ConnectedSpace ↥(pullback (stageHom K Kbar s) f)] {G : Type u} [Group G] [Finite G]
    (V : FiniteEtaleGaloisCover (pullback (stageHom K Kbar s) f) G)
    [ConnectedSpace ↥(pullback V.obj.hom (AdjoinFinset.bcProj K Kbar f (Opposite.op s)))] :
    ∃ (t : Finset Kbar) (V' : FiniteEtaleGaloisCover (pullback (stageHom K Kbar t) f) G)
      (z : Spec (.of ↥(Algebra.adjoin K (t : Set Kbar))) ⟶ V'.obj.left),
      z ≫ V'.obj.hom = stageSection K Kbar f σ hσ t ∧
      Nonempty ((finiteEtaleBaseChange (AdjoinFinset.bcProj K Kbar f (Opposite.op t))).obj V'.obj ≅
        (finiteEtaleBaseChange (AdjoinFinset.bcProj K Kbar f (Opposite.op s))).obj V.obj) := by
  obtain ⟨t, e, w, hw⟩ := exists_stage_point_of_finiteEtaleGaloisCover K Kbar f σ hσ s V
  have hc : ConnectedSpace ↥((finiteEtaleBaseChange (stageTransition K Kbar f e)).obj
      V.obj).left :=
    connectedSpace_pullback_stageTransition K Kbar f e V.obj.hom
  let V' := V.baseChange (stageTransition K Kbar f e) hc
  let z : Spec (.of ↥(Algebra.adjoin K (t : Set Kbar))) ⟶ V'.obj.left :=
    pullback.lift w (stageSection K Kbar f σ hσ t) (by rw [stageSection_naturality]; exact hw)
  exact ⟨t, V', z, pullback.lift_snd _ _ _,
    ⟨((finiteEtaleBaseChangeComp (AdjoinFinset.bcProj K Kbar f (Opposite.op t))
      (stageTransition K Kbar f e) (AdjoinFinset.bcProj K Kbar f (Opposite.op s))
      (bcProj_comp_stageTransition K Kbar f e).symm).app V.obj).symm⟩⟩

end AlgebraicExtensionLimit

/-! ### The generic fibre of a base change along a ring of integers -/

/-- **The spectrum of a tower of two ring maps is the composite of the two spectra**, in the other
order. This is `AlgebraicGeometry.specMap_algebraMap_comp` with the three fields relaxed to
commutative rings, which is what a tower `R → Frac R → L` of a domain inside its fraction field
inside a finite extension needs. -/
theorem specMap_algebraMap_comp_of_isScalarTower (R B L : Type u) [CommRing R] [CommRing B]
    [CommRing L] [Algebra R B] [Algebra B L] [Algebra R L] [IsScalarTower R B L] :
    Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (by ext x; exact (IsScalarTower.algebraMap_apply R B L x).symm))

/-- The rational point of a generic fibre given by a section is a section of the structure
morphism of the generic fibre. -/
theorem genericFiberSection_fiberToSpecResidueField {S X : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) [IsIntegral S] :
    genericFiberSection f σ hσ ≫ f.fiberToSpecResidueField (genericPoint S) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- **The generic fibre of a base change along a domain is a base change of the original family
along the fraction field.** Let `h : Y ⟶ Spec R` be any morphism, let `B` be an `R`-algebra which
is a domain with fraction field `L`, and let `Spec B ⟶ Spec R` be the structure morphism. Then
the fibre of the base change `Y_B ⟶ Spec B` over the generic point of `Spec B`, mapped into `Y`
and into `Spec L` through an isomorphism `Spec κ(η) ≅ Spec L` over `Spec B`, is a base change of
`h` along `Spec L ⟶ Spec R`.

The square `AlgebraicGeometry.isPullback_fiberι_fiberToSpecResidueField` of the fibre is composed
on the right with the isomorphism (`CategoryTheory.IsPullback.comp_isIso_right`) and pasted with
the square of the base change `Y_B`. -/
theorem isPullback_fiberι_genericPoint_comp {R B L : Type u} [CommRing R] [CommRing B]
    [IsDomain B] [Field L] [Algebra R B] [Algebra B L] [Algebra R L] [IsScalarTower R B L]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R))
    (i : Spec ((Spec (.of B)).residueField (genericPoint (Spec (.of B)))) ⟶ Spec (.of L))
    [IsIso i]
    (hi : i ≫ Spec.map (CommRingCat.ofHom (algebraMap B L))
      = (Spec (.of B)).fromSpecResidueField (genericPoint (Spec (.of B)))) :
    IsPullback
      ((pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B)))).fiberι
          (genericPoint (Spec (.of B))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      ((pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B)))).fiberToSpecResidueField
          (genericPoint (Spec (.of B))) ≫ i)
      h (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
  have hfib : IsPullback
      ((pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B)))).fiberι
        (genericPoint (Spec (.of B))))
      ((pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B)))).fiberToSpecResidueField
        (genericPoint (Spec (.of B))) ≫ i)
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B L))) := by
    refine IsPullback.comp_isIso_right ?_
    rw [hi]
    exact isPullback_fiberι_fiberToSpecResidueField
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      (genericPoint (Spec (.of B)))
  have hpaste := hfib.paste_horiz
    (IsPullback.of_hasPullback h (Spec.map (CommRingCat.ofHom (algebraMap R B))))
  rwa [specMap_algebraMap_comp_of_isScalarTower R B L] at hpaste

/-! ### From a Galois cover of a finite stage to a cover of the family -/

/-- A section of `h` induces a section of any base change of `h`, over the given base morphism. -/
private theorem exists_lift_section_pullback {Y S T : Scheme.{u}} (h : Y ⟶ S) (g : T ⟶ S)
    (σ : S ⟶ Y) (hσ : σ ≫ h = 𝟙 S) :
    ∃ τ : T ⟶ pullback h g, τ ≫ pullback.snd h g = 𝟙 T ∧ τ ≫ pullback.fst h g = g ≫ σ :=
  ⟨pullback.lift (g ≫ σ) (𝟙 T) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

/-- **A Galois cover of `Y_L` with a rational point over a section extends and descends to `Y`.**
Let `R` be a strictly henselian discrete valuation ring of residue characteristic zero and with
algebraically closed residue field, let `K` be its fraction field and `L` a finite extension of
`K`, let `h : Y ⟶ Spec R` be smooth and proper with geometrically connected fibres and `σ` a
section of `h`, and let `V` be a finite étale Galois cover of `Spec L ×_{Spec K} Y_K` with finite
group `G` carrying an `L`-rational point over the section. Then `V` is the base change along
`Spec L ×_{Spec K} Y_K ⟶ Y` of a finite étale cover of `Y`.

Write `B' = ` the integral closure of `R` in `L`. It is again a strictly henselian discrete
valuation ring, module-finite over `R`
(`Stacks.Henselian.isDiscreteValuationRing_strictlyHenselian_module_finite_integralClosure`),
`L` is its fraction field, and `Spec B'` is integral, normal and Noetherian. The scheme
`Spec L ×_{Spec K} Y_K` is the generic fibre of `Y_{B'} ⟶ Spec B'`
(`AlgebraicGeometry.isPullback_fiberι_genericPoint_comp`), the section induces the same rational
point on both presentations, and the order of `G` is invertible on `Spec B'` because the residue
characteristic is zero
(`Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar`). So [Stacks, Tag 0EYJ] extends `V`
over `Y_{B'}`, and `R ⟶ B'` induces a bijection on residue fields, so that extension descends to
`Y`
(`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_bijective_residueField`,
[Stacks, Tag 0A48]).

The two hypotheses on the rational point are the two components of the single equation saying it
lies over the section: `hz₁` says it lies over the given `L`-point of the base and `hz₂` that its
image in `Y` is the section. -/
theorem exists_finiteEtale_model_of_galoisCover_stage (R K L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [StrictlyHenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra K L]
    [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L]
    (hchar : ringChar (R ⧸ IsLocalRing.maximalIdeal R) = 0)
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h] [GeometricallyConnected h]
    (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ h = 𝟙 _) (G : Type v) [Group G] [Finite G]
    (V : FiniteEtaleGaloisCover (pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))) G)
    (z : Spec (.of L) ⟶ V.obj.left)
    (hz₁ : z ≫ V.obj.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = 𝟙 _)
    (hz₂ : z ≫ V.obj.hom ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) :
    ∃ C : FiniteEtaleOver Y, Nonempty ((finiteEtaleBaseChange
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj C ≅ V.obj) := by
  -- characteristic zero, hence separability of `L/K`
  have hres0 : CharZero (ResidueField R) := by
    rw [CharP.ringChar_zero_iff_CharZero] at hchar
    exact hchar
  have : CharZero R := RingHom.charZero (IsLocalRing.residue R)
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  -- the integral closure of `R` in `L`
  obtain ⟨hdvr, hsh, hloc, hfrac, hfin⟩ :=
    Stacks.Henselian.isDiscreteValuationRing_strictlyHenselian_module_finite_integralClosure
      R K L
  have := hdvr
  have := hsh
  have := hloc
  have := hfrac
  have := hfin
  have : IsNormal (Spec (.of ↥(integralClosure R L))) :=
    isNormal_spec_of_isDiscreteValuationRing ↥(integralClosure R L)
  -- the section of the base change to `Spec B'`
  obtain ⟨σ', hσ'snd, hσ'fst⟩ := exists_lift_section_pullback h
    (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L)))) σ hσ
  -- the stage `Y_L` is the generic fibre of `Y_{B'} ⟶ Spec B'`
  obtain ⟨i, hiiso, hi⟩ :=
    exists_isIso_comp_specMap_eq_fromSpecResidueField (A := ↥(integralClosure R L)) L
  have := hiiso
  have Hstage : IsPullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))) h
      (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    have hp := AlgebraicExtensionLimit.isPullback_pullback_comp h
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    rwa [specMap_algebraMap_comp_of_isScalarTower R K L] at hp
  have Hfib : IsPullback
      ((pullback.snd h (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R L))))).fiberι
          (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L)))))
      ((pullback.snd h (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R L))))).fiberToSpecResidueField
          (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫ i)
      h (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    isPullback_fiberι_genericPoint_comp h i hi
  let m := Hstage.isoIsPullback _ _ Hfib
  have hmfst : m.hom ≫
        ((pullback.snd h (Spec.map (CommRingCat.ofHom
            (algebraMap R ↥(integralClosure R L))))).fiberι
            (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
          pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L)))))
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K L)))
            (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
          pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Hstage.isoIsPullback_hom_fst _ _ Hfib
  have hmsnd : m.hom ≫
        ((pullback.snd h (Spec.map (CommRingCat.ofHom
            (algebraMap R ↥(integralClosure R L))))).fiberToSpecResidueField
            (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫ i)
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
          (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    Hstage.isoIsPullback_hom_snd _ _ Hfib
  -- the two section-induced rational points agree across the comparison isomorphism
  have hiRL : i ≫ Spec.map (CommRingCat.ofHom (algebraMap R L))
      = (Spec (.of ↥(integralClosure R L))).fromSpecResidueField
          (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L))) := by
    rw [← specMap_algebraMap_comp_of_isScalarTower R ↥(integralClosure R L) L, ← Category.assoc,
      hi]
  have hgfs₁ : genericFiberSection
        (pullback.snd h (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R L))))) σ' hσ'snd ≫
        ((pullback.snd h (Spec.map (CommRingCat.ofHom
            (algebraMap R ↥(integralClosure R L))))).fiberι
            (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
          pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L)))))
      = (Spec (.of ↥(integralClosure R L))).fromSpecResidueField
          (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L))) ≫ σ := by
    rw [← Category.assoc, genericFiberSection_fiberι, Category.assoc, hσ'fst]
  have hgfs₂ : genericFiberSection
        (pullback.snd h (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R L))))) σ' hσ'snd ≫
        ((pullback.snd h (Spec.map (CommRingCat.ofHom
            (algebraMap R ↥(integralClosure R L))))).fiberToSpecResidueField
            (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫ i) = i := by
    rw [← Category.assoc, genericFiberSection_fiberToSpecResidueField, Category.id_comp]
  have hia : i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ
      = (Spec (.of ↥(integralClosure R L))).fromSpecResidueField
          (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L))) ≫ σ := by
    have h₁ : i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K))
        = (Spec (.of ↥(integralClosure R L))).fromSpecResidueField
            (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L))) := by
      rw [specMap_algebraMap_comp_of_isScalarTower R K L, hiRL]
    calc i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ
        = (i ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ σ := by
              simp only [Category.assoc]
      _ = ((Spec (.of ↥(integralClosure R L))).fromSpecResidueField
            (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L)))) ≫ σ := by
              rw [h₁]
      _ = (Spec (.of ↥(integralClosure R L))).fromSpecResidueField
            (genericPoint (Spec (.of ↥(integralClosure R L)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L))) ≫ σ :=
              Category.assoc _ _ _
  have hsec : genericFiberSection
        (pullback.snd h (Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(integralClosure R L))))) σ' hσ'snd
      = i ≫ (z ≫ V.obj.hom) ≫ m.hom := by
    refine Hfib.hom_ext ?_ ?_
    · simp only [Category.assoc, hgfs₁, hmfst, hz₂]
      exact hia.symm
    · simp only [Category.assoc, hgfs₂, hmsnd, hz₁, Category.comp_id]
  -- the Galois cover transported to the generic fibre, with its rational point
  have : ConnectedSpace ↥V.obj.left := V.connected
  have hc : ConnectedSpace ↥((finiteEtaleBaseChange m.inv).obj V.obj).left :=
    connectedSpace_left_finiteEtaleBaseChange_of_isIso m.inv V.obj
  let Z := V.baseChange m.inv hc
  have hZhom : Z.obj.hom = pullback.snd V.obj.hom m.inv := rfl
  let zZ : Spec ((Spec (.of ↥(integralClosure R L))).residueField
        (genericPoint (Spec (.of ↥(integralClosure R L))))) ⟶ Z.obj.left :=
    pullback.lift (i ≫ z)
      (genericFiberSection (pullback.snd h (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R L))))) σ' hσ'snd) (by
      rw [Iso.eq_comp_inv, hsec]
      simp only [Category.assoc])
  have hzZ : zZ ≫ Z.obj.hom = genericFiberSection
      (pullback.snd h (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R L))))) σ' hσ'snd := by
    rw [hZhom]
    exact pullback.lift_snd _ _ _
  -- the order of `G` is invertible on `Spec B'`
  have hcard : Nat.card G ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hcharB : ringChar (↥(integralClosure R L) ⧸
      IsLocalRing.maximalIdeal ↥(integralClosure R L)) = 0 := by
    rw [CharP.ringChar_zero_iff_CharZero]
    have : CharZero (ResidueField ↥(integralClosure R L)) :=
      RingHom.charZero (RingEquiv.ofBijective _
        (Stacks.Henselian.bijective_residueField_map_integralClosure R L)).symm.toRingHom
    exact this
  have hunit : IsUnit (Nat.card G : ↥(integralClosure R L)) :=
    Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar _ hcard (Or.inl hcharB)
  have hG : ∀ x : Spec (.of ↥(integralClosure R L)),
      IsUnit (Nat.card G : (Spec (.of ↥(integralClosure R L))).residueField x) :=
    fun x ↦ isUnit_natCast_specResidueField_of_isUnit hunit x
  -- Tag 0EYJ: the cover of the generic fibre extends over `Spec B'`
  obtain ⟨Y₀, ε, -⟩ :=
    FiniteEtaleGaloisCover.exists_extension_of_genericFiber_of_isNoetherian
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L)))))
      σ' hσ'snd G hG Z zZ hzZ
  -- the extension descends from `Y_{B'}` to `Y`
  have : (finiteEtaleBaseChange (pullback.fst h (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R L)))))).IsEquivalence :=
    isEquivalence_finiteEtaleBaseChange_pullback_fst_of_bijective_residueField R
      ↥(integralClosure R L)
      (Stacks.Henselian.bijective_residueField_map_integralClosure R L) h
  refine ⟨(finiteEtaleBaseChange (pullback.fst h (Spec.map (CommRingCat.ofHom
    (algebraMap R ↥(integralClosure R L)))))).objPreimage Y₀.obj, ?_⟩
  -- the three base changes compose
  let ζ : (finiteEtaleBaseChange m.hom).obj Z.obj ≅ V.obj :=
    ((finiteEtaleBaseChangeComp m.hom m.inv (𝟙 _) m.hom_inv_id.symm).app V.obj).symm ≪≫
      finiteEtaleBaseChangeId.app V.obj
  obtain ⟨ε₂⟩ := nonempty_iso_finiteEtaleBaseChange_comp m.hom
    ((pullback.snd h (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R L))))).fiberι
      (genericPoint (Spec (.of ↥(integralClosure R L))))) _ rfl ζ ε
  refine nonempty_iso_finiteEtaleBaseChange_comp _
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R L)))))
    _ ?_ ε₂ ((finiteEtaleBaseChange (pullback.fst h (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R L)))))).objObjPreimageIso Y₀.obj)
  rw [Category.assoc, hmfst]

/-! ### From a Galois cover of the geometric generic fibre to one of a finite stage -/

/-- **A Galois cover of a geometric generic fibre comes, with a rational point, from a finite
subextension of the algebraic closure of the fraction field.** Let `R` be a domain with fraction
field `K` and let `kbar` be an algebraic closure of `K`. Let `h : Y ⟶ Spec R` be proper with
geometrically connected fibres and with a section `σ`, and let `w : Spec Ω ⟶ Spec R` factor as
`Spec Ω ⟶ Spec kbar ⟶ Spec K ⟶ Spec R` along a ring homomorphism `χ : kbar ⟶ Ω` with `Ω`
algebraically closed. Then every Galois object `A` of `FÉt_{Y_Ω}` is, for some finite subset
`t ⊆ kbar`, the base change of a finite étale Galois cover `V` of the stage
`Spec K(t) ×_{Spec K} Y_K` which carries a `K(t)`-rational point over the section, along a
morphism `ρ : Y_Ω ⟶ Spec K(t) ×_{Spec K} Y_K` lying over `Y`.

This composes the descent to `Y_{kbar}`
(`AlgebraicGeometry.exists_isGalois_model_reassoc_of_isAlgClosed_tower`, which is [Stacks, Tag
0A49] re-associated), the descent of a Galois cover from `Y_{kbar}` to a finite stage
(`AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isGalois`),
the appearance of a rational point at a possibly larger stage
(`AlgebraicGeometry.AlgebraicExtensionLimit.exists_stage_point_of_finiteEtaleGaloisCover`), and
the transport of the cover to that larger stage, whose connectedness obligation is
`AlgebraicGeometry.AlgebraicExtensionLimit.connectedSpace_pullback_stageTransition`.

The two equations on the rational point are the components of its lying over the section: it is a
point of the base `Spec K(t)` and its image in `Y` is the section. -/
theorem exists_galoisCover_stage_model_of_isGalois {R : Type u} [CommRing R] [IsDomain R]
    (K kbar : Type u) [Field K] [Field kbar] [Algebra R K] [IsFractionRing R K]
    [Algebra K kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic K kbar]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) [IsProper h] [GeometricallyConnected h]
    (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ h = 𝟙 _)
    {Omega : Type u} [Field Omega] [IsAlgClosed Omega] (χ : kbar →+* Omega)
    (w : Spec (.of Omega) ⟶ Spec (.of R))
    (hw : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) = w)
    (A : FiniteEtaleOver (pullback h w)) [ConnectedSpace ↥(pullback h w)] [IsGalois A] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (t : Finset kbar)
      (V : FiniteEtaleGaloisCover (pullback (AlgebraicExtensionLimit.stageHom K kbar t)
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))) G)
      (z : Spec (.of ↥(Algebra.adjoin K (t : Set kbar))) ⟶ V.obj.left)
      (ρ : pullback h w ⟶ pullback (AlgebraicExtensionLimit.stageHom K kbar t)
        (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
      z ≫ V.obj.hom ≫ pullback.fst (AlgebraicExtensionLimit.stageHom K kbar t)
          (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = 𝟙 _ ∧
      z ≫ V.obj.hom ≫ pullback.snd (AlgebraicExtensionLimit.stageHom K kbar t)
            (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
          pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        = AlgebraicExtensionLimit.stageHom K kbar t ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ ∧
      Nonempty ((finiteEtaleBaseChange ρ).obj V.obj ≅ A) ∧
      ρ ≫ pullback.snd (AlgebraicExtensionLimit.stageHom K kbar t)
            (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
          pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        = pullback.fst h w := by
  have : CompactSpace ↥(pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  have : QuasiSeparatedSpace ↥(pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  have : ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap K kbar)))
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :=
    GeometricallyConnected.geometrically_connectedSpace
      (f := pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) _ _
      (IsPullback.of_hasPullback _ _).flip
  obtain ⟨q₁, B₁, _, ⟨ε₀⟩, hq₁⟩ :=
    exists_isGalois_model_reassoc_of_isAlgClosed_tower h
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) w χ hw A
  obtain ⟨s, V, ⟨ε₁⟩⟩ :=
    AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isGalois K kbar
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) B₁
  obtain ⟨σK, hσKsnd, hσKfst⟩ := exists_lift_section_pullback h
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) σ hσ
  have : ConnectedSpace ↥(pullback (AlgebraicExtensionLimit.stageHom K kbar s)
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :=
    AlgebraicExtensionLimit.connectedSpace_pullback_stageHom K kbar _ s
  have : ConnectedSpace ↥B₁.left := connectedSpace_left_of_isConnected B₁ inferInstance
  have : ConnectedSpace ↥(pullback V.obj.hom (AdjoinFinset.bcProj K kbar
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (Opposite.op s))) :=
    connectedSpace_left_of_iso ε₁.symm
  obtain ⟨t, V', z', hz', ⟨ε₂⟩⟩ :=
    AlgebraicExtensionLimit.exists_stage_point_baseChange_stageTransition K kbar
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) σK hσKsnd s V
  refine ⟨Aut B₁, inferInstance, inferInstance, t, V', z',
    q₁ ≫ AdjoinFinset.bcProj K kbar
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (Opposite.op t),
    ?_, ?_, nonempty_iso_finiteEtaleBaseChange_comp q₁ _ _ rfl ε₀ (ε₂ ≪≫ ε₁), ?_⟩
  · rw [← Category.assoc, hz', AlgebraicExtensionLimit.stageSection_fst]
  · rw [← Category.assoc, hz', ← Category.assoc,
      AlgebraicExtensionLimit.stageSection_snd, Category.assoc, hσKfst]
  · rw [Category.assoc, ← Category.assoc (AdjoinFinset.bcProj K kbar
      (pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (Opposite.op t)),
      AdjoinFinset.bcProj_snd]
    exact hq₁

/-! ### The residual input of Tag 0C0Q -/

/-- **Every Galois cover of the geometric generic fibre of a smooth proper family over a strictly
henselian discrete valuation ring of residue characteristic zero is a base change.** Let `R` be a
strictly henselian discrete valuation ring whose residue field is algebraically closed of
characteristic zero, let `h : Y ⟶ Spec R` be smooth and proper with geometrically connected
fibres, and let `η` be a geometric point of `Spec R` lying over the generic point. Then every
finite étale cover of the geometric generic fibre `Y_η̄` which is a Galois object of `FÉt_{Y_η̄}`
is isomorphic to the base change along `Y_η̄ ⟶ Y` of a finite étale cover of `Y`.

This is the last paragraph of the proof of [Stacks, Tag 0C0Q]. With `K = Frac R` and `kbar` the
algebraic closure of `K` inside the residue field of `η`
(`AlgebraicGeometry.exists_ringHom_algebraicClosure_of_liesOver_genericPoint`), the cover descends
to a Galois cover of a finite stage `Spec K(t) ×_{Spec K} Y_K` carrying a `K(t)`-rational point
over a section of `h` (`AlgebraicGeometry.exists_galoisCover_stage_model_of_isGalois`, the section
itself being `AlgebraicGeometry.exists_section_of_smooth_of_strictlyHenselian`), and that stage
cover extends over the integral closure of `R` in `K(t)` and descends to `Y`
(`AlgebraicGeometry.exists_finiteEtale_model_of_galoisCover_stage`). -/
theorem exists_finiteEtale_model_of_isGalois_geometricGenericFibre (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [StrictlyHenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) [IsProper h]
    [Smooth h] [GeometricallyConnected h] (η : GeometricPoint (Spec (.of R)))
    (A : FiniteEtaleOver (fiberOverGeometricPoint h η))
    (hchar : ringChar ((Spec (.of R)).residueField (closedPoint R)) = 0)
    (hη : η.hom default = genericPoint (Spec (.of R))) [IsGalois A] :
    ∃ B : FiniteEtaleOver Y,
      Nonempty ((finiteEtaleBaseChange (pullback.fst h η.hom)).obj B ≅ A) := by
  have hchar0 : ringChar (R ⧸ IsLocalRing.maximalIdeal R) = 0 :=
    ringChar_quotient_maximalIdeal_eq_zero hchar
  obtain ⟨σR, hσR⟩ :=
    exists_section_of_smooth_of_strictlyHenselian R h (h.surjective (closedPoint R))
  obtain ⟨χ, hχ⟩ := exists_ringHom_algebraicClosure_of_liesOver_genericPoint η.hom hη
  obtain ⟨G, _, _, t, V, z, ρ, hz₁, hz₂, ⟨εA⟩, hρ⟩ :=
    exists_galoisCover_stage_model_of_isGalois (FractionRing R)
      (AlgebraicClosure (FractionRing R)) h σR hσR χ η.hom hχ A
  let : Field ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    (AlgebraicExtensionLimit.isField_adjoin (FractionRing R)
      (AlgebraicClosure (FractionRing R)) t).toField
  have : FiniteDimensional (FractionRing R) ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    AlgebraicExtensionLimit.finiteDimensional_adjoin (FractionRing R)
      (AlgebraicClosure (FractionRing R)) t
  let : Algebra R ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    ((algebraMap (FractionRing R) ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R))))).comp
        (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) ↥(Algebra.adjoin (FractionRing R)
      (t : Set (AlgebraicClosure (FractionRing R)))) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨C, ⟨εC⟩⟩ := exists_finiteEtale_model_of_galoisCover_stage R (FractionRing R)
    ↥(Algebra.adjoin (FractionRing R) (t : Set (AlgebraicClosure (FractionRing R))))
    hchar0 h σR hσR G V z hz₁ hz₂
  exact ⟨C, nonempty_iso_finiteEtaleBaseChange_comp ρ _ (pullback.fst h η.hom) hρ.symm εA εC⟩

/-! ### Tag 0C0Q -/

/-- **[Stacks, Tag 0C0Q].** Let `f : X ⟶ S` be a smooth proper morphism with geometrically
connected fibres, let `s' ⇝ s` be a specialization of points of `S` realized by a specialization
map `sp : π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`, and suppose the residue characteristic of `s` is zero. Then
`sp` is bijective, i.e. an isomorphism of topological groups.

Surjectivity is [Stacks, Tag 0C0P]. Injectivity is reduced, by
`AlgebraicGeometry.bijective_isSpecializationMap_of_ringChar_zero_of_forall_essImage_isGalois`, to
the descent of the Galois covers of a geometric generic fibre over a strictly henselian discrete
valuation ring of residue characteristic zero, which is
`AlgebraicGeometry.exists_finiteEtale_model_of_isGalois_geometricGenericFibre`. -/
@[stacks 0C0Q "the whole statement, under the source's hypotheses only: `f` smooth and proper \
with geometrically connected fibres (`IsProper f`, `Smooth f`, `GeometricallyConnected f`), a \
specialization of points of `S` realized by a specialization map `sp` (`hsp`), and `κ(s)` of \
characteristic zero (`hchar`). The conclusion `Function.Bijective sp` is the source's \
conclusion that `sp` is an isomorphism: `sp` is a continuous homomorphism of profinite groups, \
so bijectivity is invertibility. Both halves are proved -- surjectivity through Tag 0C0P and \
injectivity through the descent of the Galois covers of a geometric generic fibre over a \
strictly henselian discrete valuation ring of residue characteristic zero.",
  sga "1 X 2.5" "more general",
  sga "1 X 3.8" "special case",
  sga "1 X 3.9"]
theorem bijective_isSpecializationMap_of_ringChar_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (hchar : ringChar (S.residueField (s.hom default)) = 0) :
    Function.Bijective sp :=
  bijective_isSpecializationMap_of_ringChar_zero_of_forall_essImage_isGalois f s' s x' x sp
    hsp hchar fun R _ _ _ _ _ _Y h _ _ _ η A hcharR hη _ ↦
      exists_finiteEtale_model_of_isGalois_geometricGenericFibre R h η A hcharR hη

end AlgebraicGeometry

end
