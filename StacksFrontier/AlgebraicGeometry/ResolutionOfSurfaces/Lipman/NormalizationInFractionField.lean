module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.DominatingStageLocalRings
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeNormal
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Examples
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Examples.Localization

/-!
# The normalization of a modification of `Spec B` in the fraction field of a finite extension

Let `B → A` be a finite injective map of Noetherian complete local normal domains and
`g : Y ⟶ Spec B` a modification. The inductive step of the proof of [Stacks, Tag 0BGN] uses
the normalization `X` of `Y ×_{Spec B} Spec A`; this file constructs it as the normalization
of `Y` in `Spec L`, `L` the fraction field of `A`, and proves what the step needs about it:
`X` is a normal modification of `Spec A`, finite over `Y`, compatibly with `g`.

## Main results

* `AlgebraicGeometry.exists_lift_specMap_fractionRing`: `Spec L ⟶ Spec B` lifts through `g`.
* `AlgebraicGeometry.exists_normal_modification_finite_over`: the normalization `X`, with a
  modification `X ⟶ Spec A` and a finite morphism `X ⟶ Y` over `Spec B`.

## Implementation notes

The morphism `Spec L ⟶ Y` lands at the generic point of `Y`; it is obtained from an open of
`Spec B` over which `g` is an isomorphism ([Stacks, Tag 01RN] in the form
`AlgebraicGeometry.exists_dense_open_isIso_morphismRestrict_of_isBirational`). The map
`X ⟶ Spec A` comes from the universal property of relative normalization applied to the
integral morphism `Y ×_{Spec B} Spec A ⟶ Y`, and `X ⟶ Y` is finite by [Stacks, Tag 0AVK].
Birationality of `X ⟶ Spec A` is read off at the generic point: the stalk maps there compose to
the isomorphism `Frac A ≅ L`, and the second of them is a map of fields.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 0AVK](https://stacks.math.columbia.edu/tag/0AVK)
-/

@[expose] public section

open CategoryTheory Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The spectrum of a field mapping to the spectrum of a domain by an injective map lands at the
generic point. -/
theorem specMap_base_eq_genericPoint_of_injective {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] (φ : R →+* K) (hφ : Function.Injective φ) (x : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom φ)).base x = genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine]
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  change a ∈ Ideal.comap φ x.asIdeal ↔ a ∈ (⊥ : Ideal R)
  have := x.isPrime
  rw [Ideal.eq_bot_of_prime x.asIdeal, Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_bot,
    map_eq_zero_iff φ hφ]

/-- **A morphism from the spectrum of a field to the spectrum of a domain, by an injective ring
map, lifts through a modification.** -/
theorem exists_lift_specMap_fractionRing {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R))
    (hg : IsModification g) [IsLocallyNoetherian Y] :
    ∃ ι : Spec (.of K) ⟶ Y, ι ≫ g = Spec.map (CommRingCat.ofHom φ) := by
  have : IsIntegral Y := hg.source_isIntegral
  have : IsProper g := hg.isProper
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have : Finite (irreducibleComponents (Spec (.of R))) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  obtain ⟨V, hVd, hV⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational g
    hg.isBirational (Or.inl inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  have hgen : genericPoint (Spec (.of R)) ∈ V := by
    obtain ⟨y, hy⟩ := hVd.nonempty_iff.mpr (inferInstance : Nonempty (Spec (.of R)))
    exact ((genericPoint_spec (Spec (.of R))).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩
  have hrange : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ Set.range V.ι.base := by
    rintro _ ⟨x, rfl⟩
    rwa [V.range_ι, specMap_base_eq_genericPoint_of_injective φ hφ x]
  let t' := IsOpenImmersion.lift V.ι (Spec.map (CommRingCat.ofHom φ)) hrange
  refine ⟨t' ≫ inv (g ∣_ V) ≫ (g ⁻¹ᵁ V).ι, ?_⟩
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    IsOpenImmersion.lift_fac]

/-- For a field `K`, the evaluation `Γ(Spec K) ⟶ κ(x)`, precomposed with `ΓSpecIso`, is
surjective. -/
theorem surjective_ΓSpecIso_inv_comp_evaluation {K : Type u} [Field K] (x : Spec (.of K)) :
    Function.Surjective ((Scheme.ΓSpecIso (.of K)).inv ≫
      (Spec (.of K)).evaluation ⊤ x trivial).hom := by
  intro z
  obtain ⟨a, rfl⟩ := (Spec (.of K)).residue_surjective x z
  obtain ⟨U, hxU, s, rfl⟩ := (Spec (.of K)).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ :=
    eq_top_iff.mpr fun y _ => Subsingleton.elim (α := PrimeSpectrum K) y x ▸ hxU
  refine ⟨(Scheme.ΓSpecIso (.of K)).hom s, ?_⟩
  simp [Scheme.evaluation]

/-- The residue field extension at the point of `Spec L` of a morphism `ι : Spec L ⟶ Y` lying
over `Spec L ⟶ Spec B`, `L` essentially of finite type over `B`, is finitely generated. -/
theorem fg_top_residueFieldMap_of_comp_eq {R K : Type u} [CommRing R] [Field K] (φ : R →+* K)
    (hφ : φ.EssFiniteType) {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) (ι : Spec (.of K) ⟶ Y)
    (hι : ι ≫ g = Spec.map (CommRingCat.ofHom φ)) (x : Spec (.of K)) :
    letI := (ι.residueFieldMap x).hom.toAlgebra
    (⊤ : IntermediateField (Y.residueField (ι.base x)) ((Spec (.of K)).residueField x)).FG := by
  let := (ι.residueFieldMap x).hom.toAlgebra
  -- the structure map `R ⟶ κ(ι x)`
  let ρ : R →+* Y.residueField (ι.base x) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫
      Y.evaluation ⊤ (ι.base x) trivial).hom
  let : Algebra R (Y.residueField (ι.base x)) := ρ.toAlgebra
  let : Algebra R ((Spec (.of K)).residueField x) :=
    ((ι.residueFieldMap x).hom.comp ρ).toAlgebra
  have : IsScalarTower R (Y.residueField (ι.base x)) ((Spec (.of K)).residueField x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the composite `R ⟶ κ(x)` is `φ` followed by `K ⟶ κ(x)`
  have hcomp : (ι.residueFieldMap x).hom.comp ρ =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).evaluation ⊤ x trivial).hom.comp φ := by
    have h1 : Y.evaluation ⊤ (ι.base x) trivial ≫ ι.residueFieldMap x =
        ι.appTop ≫ (Spec (.of K)).evaluation ⊤ x trivial :=
      Scheme.evaluation_naturality (f := ι) (V := ⊤) x trivial
    have h2 : g.appTop ≫ ι.appTop = (Spec.map (CommRingCat.ofHom φ)).appTop := by
      rw [← hι]
      rfl
    have h3 : (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop =
        CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of K)).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫ Y.evaluation ⊤ (ι.base x) trivial ≫
      ι.residueFieldMap x).hom = _
    rw [h1, ← Category.assoc g.appTop, h2, ← Category.assoc, h3]
    rfl
  have hRK : (algebraMap R ((Spec (.of K)).residueField x)).EssFiniteType := by
    change ((ι.residueFieldMap x).hom.comp ρ).EssFiniteType
    rw [hcomp]
    exact hφ.comp (RingHom.FiniteType.of_surjective _
      (surjective_ΓSpecIso_inv_comp_evaluation x)).essFiniteType
  rw [RingHom.essFiniteType_algebraMap] at hRK
  exact IntermediateField.fg_top_iff.mpr
    (Algebra.EssFiniteType.of_comp R (Y.residueField (ι.base x)) _)

/-- If the function field map of `t ≫ f` is surjective, then that of `f` is bijective. -/
theorem bijective_functionFieldMap_of_surjective_comp {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] (t : Z ⟶ X) (f : X ⟶ Y) [IsDominant t] [IsDominant f]
    (h : Function.Surjective (functionFieldMap (t ≫ f))) :
    Function.Bijective (functionFieldMap f) := by
  rw [functionFieldMap_comp] at h
  refine ⟨(functionFieldMap f).injective, fun a => ?_⟩
  obtain ⟨b, hb⟩ := h (functionFieldMap t a)
  exact ⟨b, (functionFieldMap t).injective hb⟩

/-- A dominant morphism of integral schemes inducing a bijection of function fields is
birational. -/
theorem isBirational_of_bijective_functionFieldMap {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] (hff : Function.Bijective (functionFieldMap f)) :
    IsBirational f := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    refine ⟨fun x hx => ?_, fun x _ y _ _ => ?_, fun y hy => ?_⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact genericPoint_eq_of_isDominant f
    · rw [Set.mem_singleton_iff.mp ‹x ∈ _›, Set.mem_singleton_iff.mp ‹y ∈ _›]
    · exact ⟨genericPoint X, rfl, (Set.mem_singleton_iff.mp hy) ▸
        genericPoint_eq_of_isDominant f⟩
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    rw [ConcreteCategory.isIso_iff_bijective]
    let e := Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)
    rw [← Iso.inv_hom_id_assoc e (f.stalkMap (genericPoint X))]
    exact hff.comp (ConcreteCategory.bijective_of_isIso e.inv)

/-- If `t ≫ f` is birational, with `t` dominant, between integral schemes, then `f` is
birational. -/
theorem isBirational_of_isBirational_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (t : Z ⟶ X) (f : X ⟶ Y) [IsDominant t] (h : IsBirational (t ≫ f)) :
    IsBirational f := by
  have := h.isDominant
  have := IsDominant.of_comp t f
  exact isBirational_of_bijective_functionFieldMap f
    (bijective_functionFieldMap_of_surjective_comp t f h.surjective_functionFieldMap)

/-- The map from a ring to the fraction field of a module-finite algebra over it is essentially
of finite type. -/
theorem essFiniteType_algebraMap_fractionRing_comp (B A : Type u) [CommRing B] [CommRing A]
    [Algebra B A] [Module.Finite B A] :
    ((algebraMap A (FractionRing A)).comp (algebraMap B A)).EssFiniteType := by
  have h : (algebraMap A (FractionRing A)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization (FractionRing A) (nonZeroDivisors A)
  exact (RingHom.FiniteType.of_finite
    (RingHom.finite_algebraMap.mpr inferInstance)).essFiniteType.comp h

/-- **The normalization of a modification of `Spec B` in the fraction field of a finite
extension `A`.** Let `B → A` be a finite injective map of Noetherian complete local domains and
`g : Y ⟶ Spec B` a modification. There are a normal integral scheme `X`, a modification
`f : X ⟶ Spec A` and a finite morphism `π : X ⟶ Y` with `π ≫ g = f ≫ (Spec A ⟶ Spec B)`; the
morphism `Spec (Frac A) ⟶ X` is recorded as `t`, dominant, with `t ≫ π` lying over
`Spec (Frac A) ⟶ Spec B`. -/
theorem exists_normal_modification_finite_over (B A : Type u) [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] [CommRing A]
    [IsDomain A] [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B)) (hg : IsModification g) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (π : X ⟶ Y),
      IsModification f ∧ IsNormal X ∧ IsFinite π ∧
        π ≫ g = f ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
  have : IsIntegral Y := hg.source_isIntegral
  have : IsProper g := hg.isProper
  have : IsLocallyNoetherian (Spec (.of B)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let L := FractionRing A
  let φ : B →+* L := (algebraMap A L).comp (algebraMap B A)
  obtain ⟨ι, hι⟩ := exists_lift_specMap_fractionRing φ
    ((IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective B A)) g hg
  let P := pullback g (Spec.map (CommRingCat.ofHom (algebraMap B A)))
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap B A))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let f₁ : Spec (.of L) ⟶ P := pullback.lift ι (Spec.map (CommRingCat.ofHom (algebraMap A L)))
    (by rw [hι, ← Spec.map_comp]; rfl)
  have H : ι = f₁ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  have : QuasiCompact (ι ≫ g) := hι ▸ inferInstance
  have : QuasiSeparated (ι ≫ g) := hι ▸ inferInstance
  have : QuasiSeparated ι := QuasiSeparated.of_comp ι g
  have : QuasiCompact ι := QuasiCompact.of_comp ι g
  let X := ι.normalization
  let π : X ⟶ Y := ι.fromNormalization
  let d : X ⟶ P := ι.normalizationDesc f₁ (pullback.fst _ _) H
  have hdπ : d ≫ pullback.fst _ _ = π := ι.normalizationDesc_comp f₁ _ H
  let f : X ⟶ Spec (.of A) := d ≫ pullback.snd _ _
  -- finiteness of `π` (Tag 0AVK)
  have hπ : IsFinite π := isFinite_fromNormalization ι
    (isNagataScheme_of_locallyOfFiniteType_over_isPrecomplete B g)
    (finite_irreducibleComponents_of_isCompact _) fun x => fg_top_residueFieldMap_of_comp_eq φ
      (essFiniteType_algebraMap_fractionRing_comp B A) g ι hι x.1
  have : IsNormal (Spec (.of L)) := isNormal_spec_of_isNormalRing
    (IsNormalRing.of_isIntegrallyClosed L)
  have : LocallyOfFiniteType (d ≫ pullback.fst _ _) := hdπ ▸ inferInstance
  have : LocallyOfFiniteType d := locallyOfFiniteType_of_comp d (pullback.fst _ _)
  have : IsFinite d := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType d).mpr
    ⟨inferInstance, inferInstance⟩
  let t : Spec (.of L) ⟶ X := ι.toNormalization
  have hj : IsBirational (t ≫ f) := by
    rw [← Category.assoc, ι.toNormalization_normalizationDesc, pullback.lift_snd]
    exact localization_isBirational A (nonZeroDivisors A) zero_notMem_nonZeroDivisors
  refine ⟨X, f, π, ⟨isBirational_of_isBirational_comp t f hj, inferInstance, inferInstance⟩,
    isNormal_normalization ι (finite_irreducibleComponents_of_isCompact _), hπ, ?_⟩
  rw [← hdπ, Category.assoc, pullback.condition, Category.assoc]

end AlgebraicGeometry

end
