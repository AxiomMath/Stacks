module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The extensive criterion for closed immersions of affine schemes

A morphism of affine schemes is a closed immersion exactly when every commutative square whose
left-hand side is the spectrum of an *injective* map of commutative rings admits a diagonal lift.
This is an "extensive" criterion: the test objects are arbitrary affine schemes, not subobjects of
the given ones.

The criterion is proved by reducing to the corresponding statement about rings. For a morphism of
affine schemes, being a closed immersion is surjectivity of the map on global sections, by
`AlgebraicGeometry.Scheme.Hom.app_surjective` one way and
`AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine` the other. On the ring side, a map
`φ : R ⟶ S` is surjective exactly when every square against an injective map of rings has a
diagonal lift: given surjectivity, the square forces the kernel of `φ` into the kernel of the map
out of `R`, so `RingHom.liftOfSurjective` provides the lift; conversely, applying the lifting
property to the inclusion of the range of `φ` produces a section through which every element of `S`
is hit. The passage between the two sides is the equivalence `AlgebraicGeometry.Spec.homEquiv`
together with the naturality of `AlgebraicGeometry.Scheme.isoSpec`.

## Main results

* `AlgebraicGeometry.isClosedImmersion_iff_lifts_injective_specMap`: a morphism of affine schemes
  is a closed immersion if and only if every square from the spectrum of an injective ring map has
  a diagonal lift.

## Implementation notes

The square and its two triangular identities are stated directly in the category of schemes. The
affine schemes in the lifting test are spectra of arbitrary commutative rings in the same universe
as the source and target schemes, so the criterion quantifies over `Type u` and not over a
subcategory of `AlgebraicGeometry.Scheme.{u}`.

## References

* [Stacks Project, Tag 0H2P](https://stacks.math.columbia.edu/tag/0H2P)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private theorem ringHom_surjective_iff_lifts
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    Function.Surjective φ ↔
      ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
        Function.Injective ψ →
        ∀ (α : R →+* A) (β : S →+* B), ψ.comp α = β.comp φ →
          ∃ liftMap : S →+* A, liftMap.comp φ = α ∧ ψ.comp liftMap = β := by
  constructor
  · intro hφ A B _ _ ψ hψ α β hsq
    have hker : RingHom.ker φ ≤ RingHom.ker α := by
      intro r hr
      apply hψ
      simpa [RingHom.comp_apply, RingHom.mem_ker.mp hr] using
        congrArg (fun f : R →+* B => f r) hsq
    let liftMap : S →+* A := φ.liftOfSurjective hφ ⟨α, hker⟩
    refine ⟨liftMap, RingHom.liftOfSurjective_comp φ hφ ⟨α, hker⟩, ?_⟩
    have hcomp : (ψ.comp liftMap).comp φ = β.comp φ := by
      rw [RingHom.comp_assoc, RingHom.liftOfSurjective_comp φ hφ ⟨α, hker⟩]
      exact hsq
    ext s
    obtain ⟨r, rfl⟩ := hφ s
    exact DFunLike.congr_fun hcomp r
  · intro h
    let ψ : R →+* φ.range := φ.rangeRestrict
    let ι : φ.range →+* S := φ.range.subtype
    obtain ⟨liftMap, _, hinclLift⟩ := h (A := φ.range) (B := S) ι
      (fun _ _ h => Subtype.ext h) ψ (RingHom.id S) (by ext r; rfl)
    intro s
    obtain ⟨r, hr⟩ := (liftMap s).property
    refine ⟨r, ?_⟩
    have hs := congrArg (fun f : S →+* S => f s) hinclLift
    exact hr.trans (by simpa [RingHom.comp_apply, ι] using hs)

/-- Two maps from a spectrum to an affine scheme are equal iff their transposes to global
sections are. -/
private theorem eq_iff_preimage_comp_isoSpec_hom {Z : Scheme.{u}} [IsAffine Z]
    {R : CommRingCat.{u}} (m n : Spec R ⟶ Z) :
    m = n ↔ Spec.preimage (m ≫ Z.isoSpec.hom) = Spec.preimage (n ≫ Z.isoSpec.hom) := by
  rw [← cancel_mono Z.isoSpec.hom]
  exact Spec.homEquiv.injective.eq_iff.symm

/-- Precomposing with `Spec.map ψ` postcomposes the transpose with `ψ`. -/
private theorem preimage_map_comp_comp_isoSpec_hom {Z : Scheme.{u}} [IsAffine Z]
    {R S : CommRingCat.{u}} (ψ : R ⟶ S) (l : Spec R ⟶ Z) :
    Spec.preimage ((Spec.map ψ ≫ l) ≫ Z.isoSpec.hom) = Spec.preimage (l ≫ Z.isoSpec.hom) ≫ ψ := by
  simp

/-- Postcomposing with `f` precomposes the transpose with `f.appTop`. -/
private theorem preimage_comp_comp_isoSpec_hom {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {R : CommRingCat.{u}} (f : X ⟶ Y) (l : Spec R ⟶ X) :
    Spec.preimage ((l ≫ f) ≫ Y.isoSpec.hom) = f.appTop ≫ Spec.preimage (l ≫ X.isoSpec.hom) := by
  rw [Category.assoc, ← Scheme.isoSpec_hom_naturality, ← Category.assoc, Spec.preimage_comp,
    Spec.preimage_map]

/-- The transpose of `Spec.map a` followed by `isoSpec.inv` is `a`. -/
private theorem preimage_map_comp_isoSpec_inv_comp_isoSpec_hom {Z : Scheme.{u}} [IsAffine Z]
    {R : CommRingCat.{u}} (a : Γ(Z, ⊤) ⟶ R) :
    Spec.preimage ((Spec.map a ≫ Z.isoSpec.inv) ≫ Z.isoSpec.hom) = a := by
  simp

private theorem surjective_appTop_of_spec_lifts
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
      Function.Injective ψ →
      ∀ (g : Spec (.of B) ⟶ X) (h : Spec (.of A) ⟶ Y),
        (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ f) →
        ∃ l : Spec (.of A) ⟶ X,
          (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ f = h)) :
    Function.Surjective f.appTop.hom := by
  apply (ringHom_surjective_iff_lifts f.appTop.hom).2
  intro A B _ _ ψ hψ α β hsq
  let αC : CommRingCat.of Γ(Y, ⊤) ⟶ CommRingCat.of A := CommRingCat.ofHom α
  let βC : CommRingCat.of Γ(X, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom β
  let ψC : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom ψ
  obtain ⟨g, hg⟩ : ∃ g : Spec (.of B) ⟶ X, Spec.preimage (g ≫ X.isoSpec.hom) = βC :=
    ⟨_, preimage_map_comp_isoSpec_inv_comp_isoSpec_hom βC⟩
  obtain ⟨k, hk⟩ : ∃ k : Spec (.of A) ⟶ Y, Spec.preimage (k ≫ Y.isoSpec.hom) = αC :=
    ⟨_, preimage_map_comp_isoSpec_inv_comp_isoSpec_hom αC⟩
  have hsqRing : αC ≫ ψC = f.appTop ≫ βC := by
    ext x
    exact congrArg (fun m => m x) hsq
  obtain ⟨l, hleft, hright⟩ := h A B ψ hψ g k (by
    rw [eq_iff_preimage_comp_isoSpec_hom (Z := Y), preimage_map_comp_comp_isoSpec_hom,
      preimage_comp_comp_isoSpec_hom, hk, hg]
    exact hsqRing)
  have hφ := (eq_iff_preimage_comp_isoSpec_hom _ _).1 hright
  have hψ := (eq_iff_preimage_comp_isoSpec_hom _ _).1 hleft
  rw [preimage_comp_comp_isoSpec_hom, hk] at hφ
  rw [preimage_map_comp_comp_isoSpec_hom, hg] at hψ
  exact ⟨(Spec.preimage (l ≫ X.isoSpec.hom)).hom, congrArg CommRingCat.Hom.hom hφ,
    congrArg CommRingCat.Hom.hom hψ⟩

private theorem spec_lifts_of_surjective_appTop
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hsurj : Function.Surjective f.appTop.hom) :
    ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
      Function.Injective ψ →
      ∀ (g : Spec (.of B) ⟶ X) (h : Spec (.of A) ⟶ Y),
        (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ f) →
        ∃ l : Spec (.of A) ⟶ X,
          (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ f = h) := by
  intro A B _ _ ψ hψ g k hsq
  have hsqRing := (eq_iff_preimage_comp_isoSpec_hom _ _).1 hsq
  rw [preimage_map_comp_comp_isoSpec_hom, preimage_comp_comp_isoSpec_hom] at hsqRing
  obtain ⟨liftMap, hφlift, hψlift⟩ := (ringHom_surjective_iff_lifts f.appTop.hom).1 hsurj
    A B ψ hψ _ _ (congrArg CommRingCat.Hom.hom hsqRing)
  let liftC : CommRingCat.of Γ(X, ⊤) ⟶ CommRingCat.of A := CommRingCat.ofHom liftMap
  have hl := preimage_map_comp_isoSpec_inv_comp_isoSpec_hom liftC
  refine ⟨Spec.map liftC ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [eq_iff_preimage_comp_isoSpec_hom, preimage_map_comp_comp_isoSpec_hom, hl]
    exact CommRingCat.hom_ext hψlift
  · rw [eq_iff_preimage_comp_isoSpec_hom, preimage_comp_comp_isoSpec_hom, hl]
    exact CommRingCat.hom_ext hφlift

private theorem spec_lifts_iff_surjective_global_sections
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    (∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
      Function.Injective ψ →
      ∀ (g : Spec (.of B) ⟶ X) (h : Spec (.of A) ⟶ Y),
        (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ f) →
        ∃ l : Spec (.of A) ⟶ X,
          (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ f = h)) ↔
      Function.Surjective f.appTop.hom :=
  ⟨surjective_appTop_of_spec_lifts f, spec_lifts_of_surjective_appTop f⟩

/-- An affine morphism is a closed immersion exactly when maps out of spectra lift
against every injective map of commutative rings. -/
@[stacks 0H2P]
theorem isClosedImmersion_iff_lifts_injective_specMap
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      ∀ (A B : Type u) [CommRing A] [CommRing B] (ψ : A →+* B),
        Function.Injective ψ →
        ∀ (g : Spec (.of B) ⟶ X) (h : Spec (.of A) ⟶ Y),
          (Spec.map (CommRingCat.ofHom ψ) ≫ h = g ≫ f) →
          ∃ l : Spec (.of A) ⟶ X,
            (Spec.map (CommRingCat.ofHom ψ) ≫ l = g) ∧ (l ≫ f = h) := by
  rw [spec_lifts_iff_surjective_global_sections f]
  constructor
  · intro hf
    exact Scheme.Hom.app_surjective f ⊤ (isAffineOpen_top Y)
  · exact IsClosedImmersion.of_surjective_of_isAffine f

end AlgebraicGeometry

end
