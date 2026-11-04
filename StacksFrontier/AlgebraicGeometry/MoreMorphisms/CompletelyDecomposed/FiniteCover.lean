module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.CompletelyDecomposed
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Finite decomposition of a completely decomposed morphism

A completely decomposed morphism locally of finite presentation over a quasi-compact and
quasi-separated base admits a finite family of immersions of finite presentation, jointly
surjective onto the base, over each of which the morphism acquires a section.

## Main results

* `AlgebraicGeometry.exists_finite_immersion_cover_with_sections`: the finite family exists.

## Implementation notes

The family is indexed by `Fin n`, the empty case included. Joint surjectivity is surjectivity
of the morphism from the coproduct, and a section over a member of the family is a right inverse
to the second projection of the base change.

Around a point `x` at which the residue field extension is trivial, finite presentation lets one
lift finitely many fractions of the residue field at `f x` to a single principal localization of
the base and then impose the finitely many relations defining the source; the resulting quotient
is an affine scheme whose map to the base is an immersion of finite presentation through `f x`,
and it lifts to the source by construction. The images of these immersions are constructible
subsets of the base, hence open for the constructible topology, which is compact on a spectral
space; a finite subcover of the base is therefore available.

## References

* [Stacks Project, Tag 0GTL](https://stacks.math.columbia.edu/tag/0GTL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A finite family of fractions lifts to one principal localization. -/
private lemma exists_lift_finite_family_to_localizationAway
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (h : ∀ x : K, ∃ r s : R, algebraMap R K s ≠ 0 ∧
      x * algebraMap R K s = algebraMap R K r)
    {ι : Type*} [Finite ι] (x : ι → K) :
    ∃ (s : R) (t : Localization.Away s →ₐ[R] K) (v : ι → Localization.Away s),
      ∀ i, t (v i) = x i := by
  classical
  let _ := Fintype.ofFinite ι
  choose r s hs he using fun i => h (x i)
  let a := ∏ i, s i
  have ha : algebraMap R K a ≠ 0 := by
    simpa [a] using Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  let t : Localization.Away a →ₐ[R] K :=
    IsLocalization.Away.liftAlgHom a (f := Algebra.ofId R K) (isUnit_iff_ne_zero.mpr ha)
  have hu (i : ι) : IsUnit (algebraMap R (Localization.Away a) (s i)) :=
    IsLocalization.Away.isUnit_of_dvd a (Finset.dvd_prod_of_mem s (Finset.mem_univ i))
  let v (i : ι) : Localization.Away a :=
    algebraMap R _ (r i) * ↑((hu i).unit⁻¹)
  refine ⟨a, t, v, fun i => ?_⟩
  apply mul_right_cancel₀ (hs i)
  rw [he i, ← t.commutes (s i), ← map_mul]
  have hv : v i * algebraMap R (Localization.Away a) (s i) =
      algebraMap R (Localization.Away a) (r i) := by
    dsimp [v]
    rw [mul_assoc, (hu i).val_inv_mul, mul_one]
  rw [hv, t.commutes]

/-- A map from a finitely presented algebra to a field of fractions factors through
a finitely presented quotient of a principal localization of the base. -/
private lemma exists_factor_through_localizationAway_quotient
    {R B K : Type*} [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra R K] [Algebra.FinitePresentation R B]
    (φ : B →ₐ[R] K)
    (h : ∀ x : K, ∃ r s : R, algebraMap R K s ≠ 0 ∧
      x * algebraMap R K s = algebraMap R K r) :
    ∃ (s : R) (J : Ideal (Localization.Away s)) (q : B →ₐ[R] (Localization.Away s ⧸ J))
      (t : (Localization.Away s ⧸ J) →ₐ[R] K), J.FG ∧ t.comp q = φ := by
  obtain ⟨n, F, hF, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := B)
  obtain ⟨s, t, v, hv⟩ :=
    exists_lift_finite_family_to_localizationAway h (fun i => φ (F (MvPolynomial.X i)))
  let E : MvPolynomial (Fin n) R →ₐ[R] Localization.Away s := MvPolynomial.aeval v
  have hE : t.comp E = φ.comp F := by
    ext i
    simpa [E] using hv i
  let J := Ideal.map E.toRingHom (RingHom.ker F.toRingHom)
  let G := (Ideal.Quotient.mkₐ R J).comp E
  have hG : RingHom.ker F.toRingHom ≤ RingHom.ker G.toRingHom := by
    intro z hz
    show Ideal.Quotient.mk J (E z) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem E.toRingHom hz)
  let q := F.liftOfSurjective hF G hG
  have ht : J ≤ RingHom.ker t.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    show t (E z) = 0
    change F z = 0 at hz
    simpa [hz] using DFunLike.congr_fun hE z
  let t' : (Localization.Away s ⧸ J) →ₐ[R] K := Ideal.Quotient.liftₐ J t ht
  refine ⟨s, J, q, t', hker.map E.toRingHom, ?_⟩
  ext b
  obtain ⟨z, rfl⟩ := hF b
  show t' (q (F z)) = φ (F z)
  rw [AlgHom.liftOfSurjective_apply]
  exact DFunLike.congr_fun hE z

/-- Every element of a residue field at a point of an affine open is a fraction of sections. -/
private lemma exists_fraction_evaluation {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (a : X.residueField x) :
    ∃ r s : Γ(X, U), X.evaluation U x x.2 s ≠ 0 ∧
      a * X.evaluation U x x.2 s = X.evaluation U x x.2 r := by
  have := hU.isLocalization_stalk x
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf x).asIdeal.primeCompl b
  refine ⟨r, s, ?_, ?_⟩
  · show (IsLocalRing.residue (X.presheaf.stalk x))
      (algebraMap Γ(X, U) (X.presheaf.stalk x) s) ≠ 0
    rw [Ne, IsLocalRing.residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf x).asIdeal]
    exact s.2
  · change b * X.presheaf.germ U x x.2 s = X.presheaf.germ U x x.2 r at e
    show (X.residue x) b * (X.residue x) (X.presheaf.germ U x x.2 s) =
      (X.residue x) (X.presheaf.germ U x x.2 r)
    rw [← map_mul, e]

/-- Evaluating a section of the target at the image point and transporting along the morphism
agree. -/
private lemma appLE_evaluation {X Y : Scheme} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (x : V) :
    f.appLE U V h ≫ X.evaluation V x x.2 =
      Y.evaluation U (f x) (h x.2) ≫ f.residueFieldMap x := by
  simp only [Scheme.evaluation, Scheme.Hom.appLE, Category.assoc,
    TopCat.Presheaf.germ_res_assoc, Scheme.residue_residueFieldMap]
  exact (f.germ_stalkMap_assoc U x (h x.2) (X.residue x)).symm

/-- The spectrum of the residue field at a point of an affine open maps into the ambient
scheme through the affine open. -/
private lemma SpecMap_evaluation_fromSpec {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) :
    Spec.map (X.evaluation U x x.2) ≫ hU.fromSpec = X.fromSpecResidueField x := by
  rw [Scheme.evaluation, Spec.map_comp, Category.assoc]
  show Spec.map (X.residue x) ≫ hU.fromSpecStalk x.2 = _
  rw [hU.fromSpecStalk_eq_fromSpecStalk]
  rfl

/-- A point with unchanged residue field extends to a lift on an affine immersion
of finite presentation. -/
private lemma exists_affine_immersion_lift_at {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiSeparatedSpace Y]
    (x : X) [IsIso (f.residueFieldMap x)] :
    ∃ (C : CommRingCat) (g : Spec C ⟶ Y) (l : Spec C ⟶ X),
      IsImmersion g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g ∧
      l ≫ f = g ∧ f x ∈ Set.range g := by
  obtain ⟨V, hV, hy, _⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
    (U := ⊤) (x := f x) trivial
  obtain ⟨U, hU, hx, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (U := f ⁻¹ᵁ V) (x := x) hy
  let R := Γ(Y, V)
  let B := Γ(X, U)
  let F : R ⟶ B := f.appLE V U hUV
  let : Algebra R B := F.hom.toAlgebra
  let : Algebra R (Y.residueField (f x)) := (Y.evaluation V (f x) hy).hom.toAlgebra
  have hc : F ≫ X.evaluation U x hx ≫ inv (f.residueFieldMap x) =
      Y.evaluation V (f x) hy := by
    rw [← Category.assoc, appLE_evaluation f hUV ⟨x, hx⟩, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  let φ : B →ₐ[R] Y.residueField (f x) :=
    { __ := (X.evaluation U x hx ≫ inv (f.residueFieldMap x)).hom
      commutes' := fun r => congrArg (fun k : R ⟶ Y.residueField (f x) => k r) hc }
  have : Algebra.FinitePresentation R B := f.finitePresentation_appLE hV hU hUV
  obtain ⟨s, J, q, t, hJ, _⟩ :=
    exists_factor_through_localizationAway_quotient φ (exists_fraction_evaluation hV ⟨f x, hy⟩)
  let C := CommRingCat.of (Localization.Away s ⧸ J)
  let i : R ⟶ C := CommRingCat.ofHom (algebraMap R C)
  let g : Spec C ⟶ Y := Spec.map i ≫ hV.fromSpec
  let l : Spec C ⟶ X := Spec.map (CommRingCat.ofHom q.toRingHom) ≫ hU.fromSpec
  have hi : i = CommRingCat.ofHom (algebraMap R (Localization.Away s)) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk J) := rfl
  have : IsImmersion (Spec.map i) := by
    rw [hi, Spec.map_comp]
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have : Algebra.FinitePresentation R C := Algebra.FinitePresentation.quotient hJ
  have : LocallyOfFinitePresentation (Spec.map i) :=
    (LocallyOfFinitePresentation.SpecMap_iff i).mpr (by
      show (algebraMap R C).FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance)
  refine ⟨C, g, l, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · dsimp [l, g]
    rw [Category.assoc, ← hV.SpecMap_appLE_fromSpec f hU hUV, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext r
    exact q.commutes r
  · let z : Spec C := Spec.map (CommRingCat.ofHom t.toRingHom)
      (IsLocalRing.closedPoint (Y.residueField (f x)))
    refine ⟨z, ?_⟩
    have hit : i ≫ CommRingCat.ofHom t.toRingHom = Y.evaluation V (f x) hy := by
      ext r
      exact t.commutes r
    have hh : Spec.map (CommRingCat.ofHom t.toRingHom) ≫ g =
        Y.fromSpecResidueField (f x) := by
      dsimp [g]
      rw [← Category.assoc, ← Spec.map_comp]
      calc
        _ = Spec.map (Y.evaluation V (f x) hy) ≫ hV.fromSpec :=
          congrArg (fun k : R ⟶ Y.residueField (f x) => Spec.map k ≫ hV.fromSpec) hit
        _ = _ := SpecMap_evaluation_fromSpec hV ⟨f x, hy⟩
    show (Spec.map (CommRingCat.ofHom t.toRingHom) ≫ g)
      (IsLocalRing.closedPoint (Y.residueField (f x))) = f x
    rw [hh]
    exact Y.fromSpecResidueField_apply (f x) _

/-- A morphism to `X` over `Y` gives a section of its pullback to the source `Y` scheme. -/
private lemma exists_section_of_map_over {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (q : Z ⟶ X) (hq : q ≫ f = g) :
    ∃ s : Z ⟶ pullback f g, s ≫ pullback.snd f g = 𝟙 Z :=
  have h : q ≫ f = 𝟙 Z ≫ g := by simpa using hq
  ⟨pullback.lift q (𝟙 Z) h, pullback.lift_snd q (𝟙 Z) h⟩

/-- An immersion of finite presentation into the target of `f`, together with a lift of it to
the source: the local datum out of which the finite family is built. -/
private structure LocalSectionData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The source of the immersion. -/
  Z : Scheme.{u}
  /-- The immersion into the target of `f`. -/
  g : Z ⟶ Y
  /-- `g` is an immersion. -/
  isImmersion : IsImmersion g
  /-- `g` is of finite presentation. -/
  finitePresentation : FinitePresentation g
  /-- The lift of `g` to the source of `f`. -/
  lift : Z ⟶ X
  /-- The lift is a morphism over the target. -/
  liftOver : lift ≫ f = g

private lemma LocalSectionData.transportPoint {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a b : LocalSectionData f) (h : a = b) (z : a.Z) :
    ∃ z' : b.Z, b.g z' = a.g z := by cases h; exact ⟨z, rfl⟩

/-- A constructible family of pointwise section neighborhoods contains a finite subfamily. -/
private theorem finite_cover_of_pointwise_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : ∀ y : Y, ∃ d : LocalSectionData f, y ∈ Set.range d.g) :
    ∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (g : ∀ i, Z i ⟶ Y),
      Surjective (Sigma.desc g) ∧
        (∀ i, IsImmersion (g i)) ∧
        (∀ i, FinitePresentation (g i)) ∧
        (∀ i, ∃ s : Z i ⟶ pullback f (g i),
          s ≫ pullback.snd f (g i) = 𝟙 (Z i)) := by
  classical
  have : SpectralSpace Y := ⟨⟩
  choose d hd using h
  have hconstructible (y : Y) : Topology.IsConstructible (Set.range (d y).g) := by
    have : LocallyOfFinitePresentation (d y).g := (d y).finitePresentation.1
    have : QuasiCompact (d y).g := (d y).finitePresentation.2.1
    convert Scheme.Hom.isConstructible_image (d y).g
      Topology.IsConstructible.univ using 1
    ext z
    simp
  have hopen (y : Y) : @IsOpen Y (constructibleTopology Y) (Set.range (d y).g) :=
    (hconstructible y).isOpen_constructibleTopology
  have hcompact : @IsCompact Y (constructibleTopology Y) Set.univ :=
    @isCompact_univ Y (constructibleTopology Y) (compactSpace_constructibleTopology Y)
  have hcover : (Set.univ : Set Y) ⊆ ⋃ y : Y, Set.range (d y).g :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hd y⟩
  obtain ⟨T, hT⟩ := @IsCompact.elim_finite_subcover Y (constructibleTopology Y)
    Set.univ Y hcompact (fun y => Set.range (d y).g) hopen hcover
  let D (i : Fin T.card) : LocalSectionData f := d (T.equivFin.symm i).1
  have hpoint (y : Y) : ∃ i : Fin T.card, ∃ z : (D i).Z, (D i).g z = y := by
    obtain ⟨y', hy'T, hz⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ y))
    obtain ⟨i, hi⟩ := T.equivFin.symm.surjective ⟨y', hy'T⟩
    obtain rfl : (T.equivFin.symm i).1 = y' := congrArg Subtype.val hi
    obtain ⟨z, rfl⟩ := hz
    exact ⟨i, z, rfl⟩
  refine ⟨T.card, fun i => (D i).Z, fun i => (D i).g, ?_, fun i => (D i).isImmersion,
    fun i => (D i).finitePresentation,
    fun i => exists_section_of_map_over f (D i).g (D i).lift (D i).liftOver⟩
  constructor
  intro y
  obtain ⟨i, z, hzy⟩ := hpoint y
  refine ⟨Sigma.ι (fun i => (D i).Z) i z, ?_⟩
  simpa [← Scheme.Hom.comp_apply] using hzy

/-- A completely decomposed morphism locally of finite presentation over a
quasi-compact, quasi-separated base has a finite surjective cover by immersions
of finite presentation on each of which the morphism admits a section. -/
@[stacks 0GTL]
theorem exists_finite_immersion_cover_with_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsCompletelyDecomposed f)
    [LocallyOfFinitePresentation f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (g : ∀ i, Z i ⟶ Y),
      Surjective (Sigma.desc g) ∧
        (∀ i, IsImmersion (g i)) ∧
        (∀ i, FinitePresentation (g i)) ∧
        (∀ i, ∃ s : Z i ⟶ pullback f (g i),
          s ≫ pullback.snd f (g i) = 𝟙 (Z i)) := by
  apply finite_cover_of_pointwise_sections f
  intro y
  obtain ⟨x, rfl, hx⟩ := hf y
  have := hx
  obtain ⟨C, g, l, hg, hlfp, hqc, hqs, hl, hy⟩ := exists_affine_immersion_lift_at f x
  exact ⟨⟨Spec C, g, hg, ⟨hlfp, hqc, hqs⟩, l, hl⟩, hy⟩

end AlgebraicGeometry

end
