module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Scheme.Valuative.Specialization
public import StacksFrontier.AlgebraicGeometry.Topologies.V.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.StandardCoverings

/-!
# V coverings by a quasi-compact morphism

For a quasi-compact morphism of schemes, being a singleton V covering is equivalent to lifting
maps from valuation spectra after an extension of valuation rings. For any morphism of schemes,
that lifting condition is equivalent to lifting specializations after every base change.

## Main results

* `AlgebraicGeometry.isVCovering_iff_valuation_lifting` identifies the singleton V covering
  condition with valuation-ring lifting.
* `AlgebraicGeometry.valuation_lifting_iff_specialization_lifting` identifies valuation-ring
  lifting with lifting specializations after arbitrary base change.

## Implementation notes

The singleton family is indexed by `Unit`. An extension of valuation rings is an injective local
ring homomorphism, as in the definition of a standard V covering. In the specialization
condition the base-changed scheme is the categorical pullback, and its projection to the changed
base records the images of both points.

## References

* [Stacks Project, Tag 0ETN](https://stacks.math.columbia.edu/tag/0ETN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private lemma specMap_genericPoint_of_injective {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (e : R →+* S) (he : Function.Injective e) :
    Spec.map (CommRingCat.ofHom e) (genericPoint (Spec (.of S))) =
      genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  change PrimeSpectrum.comap e ⊥ = ⊥
  apply PrimeSpectrum.ext
  change RingHom.ker e = ⊥
  rwa [← RingHom.injective_iff_ker_eq_bot]

/-- A morphism from the spectrum of a local ring whose closed point lies in the range of an open
immersion factors through that open immersion. -/
private theorem exists_lift_of_closedPoint_mem {W : Type u} [CommRing W] [IsLocalRing W]
    {P Q : Scheme.{u}} (j : Q ⟶ P) [IsOpenImmersion j] (k : Spec (.of W) ⟶ P)
    (hk : k (IsLocalRing.closedPoint W) ∈ j.opensRange) :
    ∃ k' : Spec (.of W) ⟶ Q, k' ≫ j = k := by
  have hpre : k ⁻¹ᵁ j.opensRange = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem k hk
  refine ⟨IsOpenImmersion.lift j k ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ k ⁻¹ᵁ j.opensRange := by
    rw [hpre]
    exact Set.mem_univ _
  exact hz

/-- A morphism from the spectrum of a local ring factors through some member of any open
cover of its target. -/
private theorem exists_lift_openCover_of_isLocalRing {W : Type u} [CommRing W] [IsLocalRing W]
    {P : Scheme.{u}} (𝒰 : P.OpenCover) (k : Spec (.of W) ⟶ P) :
    ∃ (i : 𝒰.I₀) (k' : Spec (.of W) ⟶ 𝒰.X i), k' ≫ 𝒰.f i = k := by
  obtain ⟨x, hx⟩ := 𝒰.covers (k (IsLocalRing.closedPoint W))
  obtain ⟨k', hk'⟩ := exists_lift_of_closedPoint_mem (𝒰.f (𝒰.idx (k (IsLocalRing.closedPoint W)))) k
    ⟨x, hx⟩
  exact ⟨_, k', hk'⟩

/-- A singleton V covering lifts every map from a valuation spectrum after an extension of
valuation rings. -/
private theorem valuation_lifting_of_isVCovering {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hVC : AlgebraicGeometry.IsVCovering (fun _ : Unit ↦ X) (fun _ ↦ f)) :
    ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (.of V) ⟶ Y),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (e : V →+* W),
        AlgebraicGeometry.IsExtensionOfValuationRings e ∧
          ∃ (h : Spec (.of W) ⟶ X),
            Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f := by
  intro V _ _ _ g
  obtain ⟨U, hU, hclosed, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := g (IsLocalRing.closedPoint V)) (U := ⊤) (Set.mem_univ _)
  obtain ⟨gU, hgU⟩ := exists_lift_of_closedPoint_mem U.ι g
    (by rw [Scheme.Opens.opensRange_ι]; exact hclosed)
  let E : PreZeroHypercover Y :=
    { I₀ := Unit, X := fun _ ↦ X, f := fun _ ↦ f }
  obtain ⟨𝒰, _, _, hstd, ⟨φ⟩⟩ := (AlgebraicGeometry.isVCovering_iff E.X E.f).mp hVC U hU
  obtain ⟨W, _, _, _, e, hext, i, h, hcomm⟩ := hstd V gU
  let E_U := PreZeroHypercover.pullback₂ U.ι E
  let j : E_U.I₀ := φ.s₀ i
  let π : E_U.X j ⟶ X := pullback.fst _ _
  have hpb : π ≫ f = E_U.f j ≫ U.ι := pullback.condition
  refine ⟨W, inferInstance, inferInstance, inferInstance, e, hext, h ≫ φ.h₀ i ≫ π, ?_⟩
  rw [← hgU, reassoc_of% hcomm, ← φ.w₀ i]
  simp only [Category.assoc, hpb]
  rfl

/-- A quasi-compact morphism that lifts every map from a valuation spectrum after an extension
of valuation rings is a singleton V covering. -/
private theorem isVCovering_of_valuation_lifting {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (hl : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (.of V) ⟶ Y),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (e : V →+* W),
        AlgebraicGeometry.IsExtensionOfValuationRings e ∧
          ∃ (h : Spec (.of W) ⟶ X),
            Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f) :
    AlgebraicGeometry.IsVCovering (fun _ : Unit ↦ X) (fun _ ↦ f) := by
  rw [AlgebraicGeometry.isVCovering_iff]
  intro U hU
  have : IsAffine U.toScheme := hU
  let P : Scheme.{u} := pullback f U.ι
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f U.ι)
  let 𝒰 : P.OpenCover := P.affineCover.finiteSubcover
  let F : PreZeroHypercover.{u} U.toScheme :=
    { I₀ := 𝒰.I₀,
      X := 𝒰.X,
      f := fun i ↦ 𝒰.f i ≫ pullback.snd f U.ι }
  refine ⟨F, inferInstance, (fun i => inferInstance), ?_, ?_⟩
  · unfold AlgebraicGeometry.IsStandardVCovering
    change ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (.of V) ⟶ U.toScheme),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (e : V →+* W),
        AlgebraicGeometry.IsExtensionOfValuationRings e ∧
          ∃ (i : 𝒰.I₀) (h : Spec (.of W) ⟶ 𝒰.X i),
            Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ F.f i
    intro V _ _ _ g
    obtain ⟨W, _, _, _, e, hext, hX, hcomm⟩ := hl V (g ≫ U.ι)
    obtain ⟨i, k', hk'⟩ := exists_lift_openCover_of_isLocalRing 𝒰
      (pullback.lift hX (Spec.map (CommRingCat.ofHom e) ≫ g) (by simpa using hcomm.symm))
    refine ⟨W, inferInstance, inferInstance, inferInstance, e, hext, i, k', ?_⟩
    change _ = k' ≫ 𝒰.f i ≫ pullback.snd f U.ι
    rw [← Category.assoc, hk', pullback.lift_snd]
  · let E : PreZeroHypercover Y :=
      { I₀ := Unit, X := fun _ ↦ X, f := fun _ ↦ f }
    let φ : F.Hom (PreZeroHypercover.pullback₂ U.ι E) := {
      s₀ := fun _ ↦ (),
      h₀ := fun i ↦ pullback.lift
        (𝒰.f i ≫ pullback.fst f U.ι)
        (𝒰.f i ≫ pullback.snd f U.ι)
        (by simp [E, pullback.condition]),
      w₀ := fun i ↦ pullback.lift_snd _ _ _ }
    exact ⟨φ⟩

/-- A quasi-compact morphism is a singleton V covering exactly when every map from
a valuation spectrum lifts after an extension of valuation rings. -/
@[stacks 0ETN "part (1) iff part (2)"]
theorem isVCovering_iff_valuation_lifting {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] :
    AlgebraicGeometry.IsVCovering (fun _ : Unit ↦ X) (fun _ ↦ f) ↔
      (∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
        (g : Spec (.of V) ⟶ Y),
        ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
          (e : V →+* W),
          AlgebraicGeometry.IsExtensionOfValuationRings e ∧
            ∃ (h : Spec (.of W) ⟶ X),
              Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f) :=
  ⟨valuation_lifting_of_isVCovering f, isVCovering_of_valuation_lifting f⟩

/-- Valuation-ring lifting implies lifting every specialization after arbitrary base change. -/
private theorem specialization_lifting_of_valuation_lifting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hl : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (.of V) ⟶ Y),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (e : V →+* W),
        AlgebraicGeometry.IsExtensionOfValuationRings e ∧
          ∃ (h : Spec (.of W) ⟶ X),
            Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f) :
    ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (z' z : Z),
      z' ⤳ z →
        ∃ (w' w : (pullback g f : Scheme.{u})),
          (w' ⤳ w) ∧
            (pullback.fst g f) w' = z' ∧
              (pullback.fst g f) w = z := by
  intro Z g z' z hspec
  let K : Type u := Z.residueField z'
  let : Field K := inferInstance
  obtain ⟨A, _, _, _, t, eK, hη, hclosed, -⟩ :=
    AlgebraicGeometry.exists_valuation_ring_of_specializes Z hspec K (Iso.refl _).hom
  obtain ⟨W, _, _, _, e, hext, hX, hcomm⟩ := hl A (t ≫ g)
  have : IsLocalHom e := hext.2
  let p₀ : Spec (.of W) := IsLocalRing.closedPoint W
  let l : Spec (.of W) ⟶ pullback g f :=
    pullback.lift (Spec.map (CommRingCat.ofHom e) ≫ t) hX (by simpa using hcomm)
  refine ⟨l (genericPoint (Spec (.of W))), l p₀,
    (genericPoint_specializes p₀).map l.continuous, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply,
      specMap_genericPoint_of_injective e hext.1, hη]
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (congrArg t (IsLocalRing.comap_closedPoint e)).trans hclosed

/-- Lifting every specialization after arbitrary base change implies valuation-ring lifting. -/
private theorem valuation_lifting_of_specialization_lifting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hspec : ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (z' z : Z),
      z' ⤳ z →
        ∃ (w' w : (pullback g f : Scheme.{u})),
          (w' ⤳ w) ∧
            (pullback.fst g f) w' = z' ∧
              (pullback.fst g f) w = z) :
    ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (.of V) ⟶ Y),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (e : V →+* W),
        AlgebraicGeometry.IsExtensionOfValuationRings e ∧
          ∃ (h : Spec (.of W) ⟶ X),
            Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f := by
  intro V _ _ _ g
  let Z := Spec (.of V)
  obtain ⟨w', w, hww, hw'fst, hwfst⟩ := hspec Z g
    (genericPoint Z) (IsLocalRing.closedPoint V) (genericPoint_specializes _)
  let K : Type u := (pullback g f).residueField w'
  let : Field K := inferInstance
  obtain ⟨W, _, _, _, h, eK, hgeneric, hclosed, -⟩ :=
    AlgebraicGeometry.exists_valuation_ring_of_specializes (pullback g f) hww K (Iso.refl _).hom
  let e : V →+* W := (Spec.preimage (h ≫ pullback.fst g f)).hom
  have he : Spec.map (CommRingCat.ofHom e) = h ≫ pullback.fst g f := by simp [e]
  refine ⟨W, inferInstance, inferInstance, inferInstance, e, ?_, h ≫ pullback.snd g f, ?_⟩
  · constructor
    · rw [RingHom.injective_iff_ker_eq_bot]
      change Ideal.comap e ⊥ = ⊥
      have hegeneric : Spec.map (CommRingCat.ofHom e)
          (genericPoint (Spec (.of W))) = genericPoint Z := by
        rw [he]
        change pullback.fst g f (h (genericPoint (Spec (.of W)))) = _
        rw [hgeneric, hw'fst]
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine] at hegeneric
      change PrimeSpectrum.comap e ⊥ = (⊥ : PrimeSpectrum V) at hegeneric
      simpa only [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot] using
        congrArg PrimeSpectrum.asIdeal hegeneric
    · rw [IsLocalRing.isLocalHom_iff_comap_closedPoint]
      have heclosed : Spec.map (CommRingCat.ofHom e) (IsLocalRing.closedPoint W) =
          IsLocalRing.closedPoint V := by
        rw [he]
        change pullback.fst g f (h (IsLocalRing.closedPoint W)) = _
        rw [hclosed, hwfst]
      exact heclosed
  · rw [he]
    simp only [Category.assoc, pullback.condition]

/-- Valuation-ring lifting is equivalent to lifting every specialization after
arbitrary base change. -/
@[stacks 0ETN "part (2) iff part (3)"]
theorem valuation_lifting_iff_specialization_lifting {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (.of V) ⟶ Y),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (e : V →+* W),
        AlgebraicGeometry.IsExtensionOfValuationRings e ∧
          ∃ (h : Spec (.of W) ⟶ X),
            Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f) ↔
      (∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (z' z : Z),
        z' ⤳ z →
          ∃ (w' w : (pullback g f : Scheme.{u})),
            (w' ⤳ w) ∧
              (pullback.fst g f) w' = z' ∧
                (pullback.fst g f) w = z) :=
  ⟨specialization_lifting_of_valuation_lifting f, valuation_lifting_of_specialization_lifting f⟩

end AlgebraicGeometry
