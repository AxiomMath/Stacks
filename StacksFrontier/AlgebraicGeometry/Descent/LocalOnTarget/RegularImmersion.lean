module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Immersion
public import StacksFrontier.AlgebraicGeometry.H1RegularIdealSheaf.Affine
public import StacksFrontier.AlgebraicGeometry.KoszulRegularIdealSheaf.Affine
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ZariskiLocal
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Affine
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# The regularity conditions on a quasi-compact immersion, read off affine opens

Stacks tag 0694 asserts that, for a *quasi-compact* immersion of schemes, each of the three
conditions Koszul-regular, `H₁`-regular and quasi-regular of Stacks tag 063J is local on the base
for the fpqc topology. The criterion of Stacks tag 02KP that
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` provides reduces that assertion to Zariski
locality, stability under flat base change and descent along surjective flat quasi-compact
morphisms, and each of those three steps is carried out on *affine* opens, where the condition in
question becomes a condition on a single ideal of a single ring.

This file supplies that translation. For `j : Z ⟶ X` a quasi-compact morphism of schemes, each of
the three conditions of Stacks tag 063D on the defining ideal sheaf of `j` is shown to be
equivalent to: around every point of the closure of the image of `j`, some affine open carries a
finite family which generates the kernel of `j` on sections there and which has the corresponding
ring-level regularity property. The three conditions are treated uniformly by abstracting over
that ring-level property, which is what `AlgebraicGeometry.KerGeneratedBy` does.

## Main definitions

* `AlgebraicGeometry.KerGeneratedBy`: for a predicate `Seq` on finite families of elements of a
  commutative ring, the condition that around every point of the closure of the image of `j` some
  affine open carries a family satisfying `Seq` which generates the kernel of `j` on sections.

## Main results

* `AlgebraicGeometry.mem_idealQuotientSupport_definingIdealOfHom_iff`: the support of the quotient
  of the structure sheaf by the defining ideal sheaf of `j` is the closure of the image of `j`.
* `AlgebraicGeometry.forall_isKoszulRegular_germFamily_iff` and
  `AlgebraicGeometry.forall_isH1Regular_germFamily_iff`: over an affine open, germwise
  Koszul-regularity, resp. `H₁`-regularity, of a family of sections at every point of the open is
  Koszul-regularity, resp. `H₁`-regularity, of the family in the ring of sections.
* `AlgebraicGeometry.isKoszulRegularIdealSheaf_iff_kerGeneratedBy`,
  `AlgebraicGeometry.isH1RegularIdealSheaf_iff_kerGeneratedBy` and
  `AlgebraicGeometry.isQuasiRegularIdealSheaf_iff_kerGeneratedBy`: parts (2), (3) and (4) of
  Stacks tag 063D for a defining ideal sheaf, in the affine-open form. These are the three
  instances of `AlgebraicGeometry.KerGeneratedBy`.

## Implementation notes

The three conditions of Stacks tag 063D that `Stacks.AlgebraicGeometry.RegularIdealSheaf`
records — and hence the three conditions on immersions of Stacks tag 063J — are *stalkwise*:
Koszul-regularity of an ideal sheaf asks for the vanishing of the Koszul homology of the germs of
a local generating sequence in every positive degree. Stacks tag 063G, as available for parts (2)
and (3) in `Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf.isKoszulRegularIdealSheaf_iff_affine`
and `Stacks.AlgebraicGeometry.H1RegularIdealSheaf.isH1RegularIdealSheaf_iff_affine`, is stated
instead for the sheaf-level local-exactness conditions
`Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf.IsKoszulRegularSequenceOn` and
`Stacks.AlgebraicGeometry.H1RegularIdealSheaf.IsH1RegularSequenceOn`, and nothing relates the two
formulations. That seam is bypassed here rather than bridged: the stalkwise condition is compared
with the ring-level one directly, in `forall_isKoszulRegular_germFamily_iff` and
`forall_isH1Regular_germFamily_iff`. Over an affine open the stalk at a point is the localization
of the ring of sections at the prime of that point, so one direction is flat base change for
Koszul homology (`Koszul.isKoszulRegular_map_of_flat`) and the other is the locality of
Koszul-regularity on the spectrum (`Koszul.isKoszulRegular_of_forall_localization_prime`), every
prime being the prime of a point. For part (4) no such step is needed: Stacks tag 063G is already
available for the stalkwise definition, as `Stacks.AlgebraicGeometry.RegularIdealSheaf`
`.isQuasiRegularIdealSheaf_iff_exists_affine_generators`.

The support of the quotient is identified with the closure of the image, which is where the
conditions are manifestly invariant under the operations a descent argument performs on `j`; for
a closed immersion it is the image itself. The identification needs nothing about the ideal
sheaf: the unit section lies in the defining ideal over an open `U` exactly when `Γ(Z, j⁻¹U)` is
the zero ring, which for a scheme happens exactly when `j⁻¹U` is empty.

What Stacks tag 0694 still needs beyond this file is the passage from these affine-open forms to
the three hypotheses of Stacks tag 02KP: invariance of the conditions under an isomorphism of the
ambient scheme, from which Zariski locality follows together with the two halves already
available in `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_resLE` and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_resLE`; the
immersion-level form of Stacks tag 067P, flat base change, which is available only at the level
of ideal sheaves; and the descent step along a surjective flat quasi-compact morphism, whose
ring-level input is `Koszul.regular_ideals_of_faithfullyFlat`, Stacks tag 068N.

## References

* [Stacks Project, Tag 0694](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 063D](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Tag 063G](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Tag 063J](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Tag 067P](https://stacks.math.columbia.edu/tag/067P)
* [Stacks Project, Tag 068N](https://stacks.math.columbia.edu/tag/068N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

/-! ### The support of the quotient by a defining ideal sheaf -/

/-- **The support of `O_X / J` for a defining ideal sheaf is the closure of the image.** A point
lies in the support of the quotient of the structure sheaf by the defining ideal sheaf of
`j : Z ⟶ X` exactly when every open neighbourhood of it meets the image of `j`: the unit section
lies in the defining ideal over an open `U` precisely when `Γ(Z, j⁻¹U)` is the zero ring, which
for a scheme happens precisely when `j⁻¹U` is empty. -/
theorem mem_idealQuotientSupport_definingIdealOfHom_iff {Z X : Scheme.{u}} (j : Z ⟶ X) (x : X) :
    x ∈ idealQuotientSupport X.toLocallyRingedSpace.toRingedSpace
        (RegularIdealSheaf.definingIdealOfHom j) ↔
      x ∈ closure (Set.range j.base) := by
  refine not_iff_not.mp ?_
  rw [notMem_idealQuotientSupport_iff]
  constructor
  · rintro ⟨U, hxU, h1⟩
    have h0 : (1 : Γ(Z, j ⁻¹ᵁ U)) = 0 := by
      simpa only [map_one] using (mem_definingIdealOfHom_iff_app j U (1 : Γ(X, U))).mp h1
    have hempty : ∀ z : Z, j.base z ∉ U := fun z hz =>
      one_ne_zero (α := Z.presheaf.stalk z)
        (by rw [← map_one (Z.presheaf.germ (j ⁻¹ᵁ U) z hz).hom, h0, map_zero])
    intro hcl
    exact (closure_minimal (s := Set.range j.base) (Set.range_subset_iff.mpr hempty)
      U.isOpen.isClosed_compl hcl) hxU
  · intro hcl
    refine ⟨⟨(closure (Set.range j.base))ᶜ, isClosed_closure.isOpen_compl⟩, hcl, ?_⟩
    have hbot : j ⁻¹ᵁ (⟨(closure (Set.range j.base))ᶜ, isClosed_closure.isOpen_compl⟩ : X.Opens)
        = ⊥ := le_antisymm (fun z hz => (hz (subset_closure ⟨z, rfl⟩)).elim) bot_le
    have hsub : Subsingleton
        Γ(Z, j ⁻¹ᵁ (⟨(closure (Set.range j.base))ᶜ, isClosed_closure.isOpen_compl⟩ : X.Opens)) := by
      rw [hbot]
      infer_instance
    exact (mem_definingIdealOfHom_iff_app j _ (1 : Γ(X, _))).mpr (Subsingleton.elim _ _)

/-! ### Points of an affine open and prime ideals -/

/-- A point of an affine open lies in the basic open of a section exactly when the section is
outside the prime ideal of that point. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (g : Γ(X, U)) (y : U) :
    (y : X) ∈ X.basicOpen g ↔ g ∉ (hU.primeIdealOf y).asIdeal := by
  have h : (hU.primeIdealOf y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g) ↔ ((y : X) ∈ X.basicOpen g) := by
    change hU.fromSpec (hU.primeIdealOf y) ∈ X.basicOpen g ↔ _
    rw [hU.fromSpec_primeIdealOf y]
  rw [← h, hU.fromSpec_preimage_basicOpen]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- A point of an affine open lies in the zero locus of an ideal of its ring of sections exactly
when that ideal is contained in the prime ideal of the point. -/
theorem mem_zeroLocus_iff_le_primeIdealOf {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (I : Ideal Γ(X, U)) (y : U) :
    (y : X) ∈ X.zeroLocus (U := U) (I : Set Γ(X, U)) ↔ I ≤ (hU.primeIdealOf y).asIdeal := by
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  refine ⟨fun h g hg => ?_, fun h g hg hy => ?_⟩
  · by_contra hgp
    exact h g hg ((mem_basicOpen_iff_notMem_primeIdealOf hU g y).mpr hgp)
  · exact (mem_basicOpen_iff_notMem_primeIdealOf hU g y).mp hy (h hg)

/-- Every prime ideal of the ring of sections of an affine open is the prime ideal of a point of
that open. -/
theorem exists_primeIdealOf_eq_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) : ∃ y : U, hU.primeIdealOf y = p :=
  (ConcreteCategory.bijective_of_isIso (Scheme.forgetToTop.map hU.isoSpec.hom)).2 p

/-! ### Germwise regularity over an affine open -/

/-- Germwise `Seq` over an affine open is `Seq` in the ring of sections, for a predicate `Seq` that
is stable under flat base change and holds as soon as it holds after localizing at every prime. -/
private theorem forall_seq_germFamily_iff
    (Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop)
    (hflat : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] {r : ℕ}
      (f : Fin r → R), Seq f → Seq fun j => algebraMap R S (f j))
    (hloc : ∀ {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R),
      (∀ (P : Ideal R) [P.IsPrime], Seq fun j => algebraMap R (Localization.AtPrime P) (f j)) →
        Seq f)
    (X : Scheme.{u}) {U : X.Opens} (hU : IsAffineOpen U) {r : ℕ} (f : Fin r → Γ(X, U)) :
    (∀ (y : X) (hy : y ∈ U), Seq (germFamily X.toLocallyRingedSpace.toRingedSpace U f y hy)) ↔
      Seq f := by
  constructor
  · intro h
    refine hloc f fun P hP => ?_
    obtain ⟨z, hz⟩ := exists_primeIdealOf_eq_of_isAffineOpen hU ⟨P, hP⟩
    let _ := X.presheaf.algebra_section_stalk z
    have hz' := hU.isLocalization_stalk z
    rw [hz] at hz'
    have _ := hz'
    let e : X.presheaf.stalk z.1 ≃ₐ[Γ(X, U)] Localization.AtPrime P :=
      IsLocalization.algEquiv P.primeCompl _ _
    let _ := e.toRingEquiv.toRingHom.toAlgebra
    have _ : Module.Flat (X.presheaf.stalk z.1) (Localization.AtPrime P) :=
      Module.Flat.of_linearEquiv (M := X.presheaf.stalk z.1)
        (LinearEquiv.ofBijective
          (Algebra.linearMap (X.presheaf.stalk z.1) (Localization.AtPrime P)) e.bijective).symm
    have hmap := hflat (S := Localization.AtPrime P)
      (germFamily X.toLocallyRingedSpace.toRingedSpace U f z.1 z.2) (h z.1 z.2)
    refine (funext fun i => ?_ : (fun k => algebraMap (X.presheaf.stalk z.1)
      (Localization.AtPrime P) (germFamily X.toLocallyRingedSpace.toRingedSpace U f z.1 z.2 k))
        = fun k => algebraMap Γ(X, U) (Localization.AtPrime P) (f k)) ▸ hmap
    change e (X.presheaf.germ U z.1 z.2 (f i)) = _
    exact e.commutes (f i)
  · intro hf y hy
    let _ := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : ↥U)
    have _ := hU.isLocalization_stalk (⟨y, hy⟩ : ↥U)
    have _ : Module.Flat Γ(X, U) (X.presheaf.stalk y) :=
      IsLocalization.flat (X.presheaf.stalk y) (hU.primeIdealOf (⟨y, hy⟩ : ↥U)).asIdeal.primeCompl
    exact hflat f hf

/-- **Koszul-regularity over an affine open is germwise Koszul-regularity.** For `U` an affine
open, a finite family of sections over `U` is Koszul-regular in `Γ(X, U)` exactly when its germs
are Koszul-regular in every local ring over `U`.

Each stalk over `U` is the localization of `Γ(X, U)` at the prime of the corresponding point, so
one direction is flat base change for Koszul homology and the other is the locality of
Koszul-regularity on the spectrum; every prime of `Γ(X, U)` is the prime of a point of `U`, which
is what makes the prime-indexed sufficient condition available. -/
theorem forall_isKoszulRegular_germFamily_iff (X : Scheme.{u}) {U : X.Opens}
    (hU : IsAffineOpen U) {r : ℕ} (f : Fin r → Γ(X, U)) :
    (∀ (y : X) (hy : y ∈ U),
        Koszul.IsKoszulRegular (germFamily X.toLocallyRingedSpace.toRingedSpace U f y hy)) ↔
      Koszul.IsKoszulRegular f :=
  forall_seq_germFamily_iff (fun f => Koszul.IsKoszulRegular f)
    Koszul.isKoszulRegular_map_of_flat Koszul.isKoszulRegular_of_forall_localization_prime X hU f

/-- **`H₁`-regularity over an affine open is germwise `H₁`-regularity.** The `H₁` counterpart of
`AlgebraicGeometry.forall_isKoszulRegular_germFamily_iff`, proved the same way from the `H₁`
forms of flat base change and of locality on the spectrum. -/
theorem forall_isH1Regular_germFamily_iff (X : Scheme.{u}) {U : X.Opens}
    (hU : IsAffineOpen U) {r : ℕ} (f : Fin r → Γ(X, U)) :
    (∀ (y : X) (hy : y ∈ U),
        Koszul.IsH1Regular (germFamily X.toLocallyRingedSpace.toRingedSpace U f y hy)) ↔
      Koszul.IsH1Regular f :=
  forall_seq_germFamily_iff (fun f => Koszul.IsH1Regular f)
    Koszul.isH1Regular_map_of_flat Koszul.isH1Regular_of_forall_localization_prime X hU f

/-! ### The affine-open form of the regularity conditions -/

/-- **The regularity conditions read off affine opens.** For a predicate `Seq` on finite families
of elements of a commutative ring, `KerGeneratedBy Seq j` says that around every point of the
closure of the image of `j` there is an affine open on which the kernel of `j` on sections is
generated by a finite family satisfying `Seq`. -/
def KerGeneratedBy (Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop)
    {Z X : Scheme.{u}} (j : Z ⟶ X) : Prop :=
  ∀ x : X, x ∈ closure (Set.range j.base) →
    ∃ (U : X.affineOpens) (_ : x ∈ (U : Set X)) (r : ℕ) (f : Fin r → Γ(X, U.1)),
      RingHom.ker (j.app U.1).hom = Ideal.span (Set.range f) ∧ Seq f

/-- The defining ideal sheaf of a quasi-compact morphism `j` has local generators with Koszul
exactness in the degrees `D` exactly when `KerGeneratedBy Seq j` holds, provided exactness in the
degrees `D` is germwise `Seq` and germwise `Seq` over an affine open is `Seq` on sections. -/
private theorem forall_exists_isKoszulSequenceExactOn_iff_kerGeneratedBy
    (D : ℕ → Prop) (Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop)
    {Z X : Scheme.{u}} (j : Z ⟶ X) [QuasiCompact j]
    (hgerm : ∀ (U : Opens X.toLocallyRingedSpace.toRingedSpace) {r : ℕ}
      (f : Fin r → X.presheaf.obj (op U)), IsKoszulSequenceExactOn _ U f D ↔
        ∀ (y : X) (hy : y ∈ U), Seq (germFamily X.toLocallyRingedSpace.toRingedSpace U f y hy))
    (haff : ∀ {U : X.Opens}, IsAffineOpen U → ∀ {r : ℕ} (f : Fin r → Γ(X, U)),
      (∀ (y : X) (hy : y ∈ U), Seq (germFamily X.toLocallyRingedSpace.toRingedSpace U f y hy)) ↔
        Seq f) :
    (∀ x ∈ idealQuotientSupport X.toLocallyRingedSpace.toRingedSpace
        (RegularIdealSheaf.definingIdealOfHom j),
      ∃ (U : X.Opens) (_ : x ∈ U) (r : ℕ) (f : Fin r → Γ(X, U)),
        IsKoszulSequenceExactOn _ U f D ∧ IsGeneratedByOn _ (RegularIdealSheaf.definingIdealOfHom j)
          U f) ↔
      KerGeneratedBy Seq j := by
  constructor
  · intro h x hx
    obtain ⟨U₀, hxU₀, r, f, hreg, hgen⟩ :=
      h x ((mem_idealQuotientSupport_definingIdealOfHom_iff j x).mpr hx)
    obtain ⟨V, hV, hxV, hVU₀⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
    refine ⟨⟨V, hV⟩, hxV, r, fun i => X.presheaf.map (homOfLE hVU₀).op (f i),
      ker_app_eq_span_range j hV _ (isGeneratedByOn_of_le U₀ f hgen V hVU₀), ?_⟩
    exact (haff hV _).mp ((hgerm V _).mp (hreg.of_le V hVU₀))
  · intro h x hx
    obtain ⟨U, hxU, r, f, hker, hreg⟩ :=
      h x ((mem_idealQuotientSupport_definingIdealOfHom_iff j x).mp hx)
    exact ⟨U.1, hxU, r, f, (hgerm U.1 f).mpr ((haff U.2 f).mpr hreg),
      isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span j U.2 f hker⟩

/-- **Part (2) of Stacks tag 063D for a defining ideal sheaf, in the affine-open form.** The
defining ideal sheaf of a quasi-compact morphism `j` is Koszul-regular exactly when, around every
point of the closure of the image of `j`, some affine open carries a Koszul-regular family
generating the kernel of `j` on sections there. This is the form of Stacks tag 063G that part (2)
of the condition on immersions of Stacks tag 063J consumes. -/
theorem isKoszulRegularIdealSheaf_iff_kerGeneratedBy {Z X : Scheme.{u}} (j : Z ⟶ X)
    [QuasiCompact j] :
    IsKoszulRegularIdealSheaf X.toLocallyRingedSpace.toRingedSpace
        (RegularIdealSheaf.definingIdealOfHom j) ↔
      KerGeneratedBy (fun f => Koszul.IsKoszulRegular f) j :=
  forall_exists_isKoszulSequenceExactOn_iff_kerGeneratedBy _ _ j
    (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular _)
    (forall_isKoszulRegular_germFamily_iff X)

/-- **Part (3) of Stacks tag 063D for a defining ideal sheaf, in the affine-open form.** The `H₁`
counterpart of `AlgebraicGeometry.isKoszulRegularIdealSheaf_iff_kerGeneratedBy`. -/
theorem isH1RegularIdealSheaf_iff_kerGeneratedBy {Z X : Scheme.{u}} (j : Z ⟶ X)
    [QuasiCompact j] :
    IsH1RegularIdealSheaf X.toLocallyRingedSpace.toRingedSpace
        (RegularIdealSheaf.definingIdealOfHom j) ↔
      KerGeneratedBy (fun f => Koszul.IsH1Regular f) j :=
  forall_exists_isKoszulSequenceExactOn_iff_kerGeneratedBy _ _ j
    (isKoszulSequenceExactOn_iff_forall_germ_isH1Regular _)
    (forall_isH1Regular_germFamily_iff X)

/-- **Part (4) of Stacks tag 063D for a defining ideal sheaf, in the affine-open form.** The
quasi-regular counterpart of
`AlgebraicGeometry.isKoszulRegularIdealSheaf_iff_kerGeneratedBy`, obtained from the form of
Stacks tag 063G already available for the quasi-regular condition. -/
theorem isQuasiRegularIdealSheaf_iff_kerGeneratedBy {Z X : Scheme.{u}} (j : Z ⟶ X)
    [QuasiCompact j] :
    IsQuasiRegularIdealSheaf X.toLocallyRingedSpace.toRingedSpace
        (RegularIdealSheaf.definingIdealOfHom j) ↔
      KerGeneratedBy (fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f)) j := by
  rw [isQuasiRegularIdealSheaf_iff_exists_affine_generators]
  refine forall_congr' fun x => ?_
  rw [mem_idealQuotientSupport_definingIdealOfHom_iff]
  refine imp_congr_right fun _ => ?_
  exact ⟨fun ⟨U, hxU, r, f, hgen, hreg⟩ =>
      ⟨U, hxU, r, f, ker_app_eq_span_range j U.2 f hgen, hreg⟩,
    fun ⟨U, hxU, r, f, hker, hreg⟩ =>
      ⟨U, hxU, r, f, isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span j U.2 f hker, hreg⟩⟩

/-! ### Flat stability of the three sequence conditions -/

/-- Koszul-regularity of a finite family is preserved by a flat ring homomorphism. -/
theorem isKoszulRegular_of_ringHomFlat {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Flat) {r : ℕ} (f : Fin r → A) (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular fun i => φ (f i) := by
  let _ := φ.toAlgebra
  have _ : Module.Flat A B := hφ
  simpa only [RingHom.algebraMap_toAlgebra] using Koszul.isKoszulRegular_map_of_flat (S := B) f hf

/-- `H₁`-regularity of a finite family is preserved by a flat ring homomorphism. -/
theorem isH1Regular_of_ringHomFlat {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Flat) {r : ℕ} (f : Fin r → A) (hf : Koszul.IsH1Regular f) :
    Koszul.IsH1Regular fun i => φ (f i) := by
  let _ := φ.toAlgebra
  have _ : Module.Flat A B := hφ
  simpa only [RingHom.algebraMap_toAlgebra] using Koszul.isH1Regular_map_of_flat (S := B) f hf

/-- Quasi-regularity of a finite family is preserved by a flat ring homomorphism: the base change
of `A` to `B` is `B` itself, which is what `IsBaseChange.linearMap` records. -/
theorem isQuasiRegular_of_ringHomFlat {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Flat) {r : ℕ} (f : Fin r → A)
    (hf : RingTheory.Sequence.IsQuasiRegular A (List.ofFn f)) :
    RingTheory.Sequence.IsQuasiRegular B (List.ofFn fun i => φ (f i)) := by
  let _ := φ.toAlgebra
  have _ : Module.Flat A B := hφ
  have hqr := RingTheory.Sequence.IsQuasiRegular.of_flat_of_isBaseChange (N := B)
    (IsBaseChange.linearMap (R := A) (S := B)) (rs := List.ofFn f) hf
  rw [List.map_ofFn] at hqr
  simpa only [Function.comp_def, RingHom.algebraMap_toAlgebra] using hqr

/-! ### Base change of the affine-open conditions -/

/-- **Flat base change for the affine-open regularity conditions.** If `j` is a closed immersion
whose kernel is locally generated by families satisfying a predicate stable under flat ring
homomorphisms, then the same holds for any base change of `j` along a flat morphism.

Around a point of the target of the base change, an affine open of the source of the flat
morphism contained in the preimage of a witnessing affine open downstairs gives a cartesian
square of affine schemes; the corresponding square of rings is cocartesian
(`Stacks.Flatness.isPushout_appLE_of_isPullback`), and the kernel of a cocartesian square whose
opposite leg is surjective is the extension of the kernel downstairs
(`Stacks.Flatness.ker_inl_of_isPushout`), so the witnessing family simply extends. -/
@[sga "6 VIII 2.6" "more general"]
theorem kerGeneratedBy_of_isPullback
    {Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z Z' W W' : Scheme.{u}} {a : Z' ⟶ Z} {j' : Z' ⟶ W'} {j : Z ⟶ W} {pr : W' ⟶ W}
    (h : IsPullback a j' j pr) [IsClosedImmersion j] [Flat pr]
    (hj : KerGeneratedBy Seq j) : KerGeneratedBy Seq j' := by
  have hcomm : ∀ z : Z', pr.base (j'.base z) = j.base (a.base z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]
  intro x' hx'
  have hx : pr.base x' ∈ closure (Set.range j.base) := by
    refine closure_mono ?_ (image_closure_subset_closure_image pr.continuous ⟨x', hx', rfl⟩)
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨a.base z, (hcomm z).symm⟩
  obtain ⟨V, hxV, r, f, hker, hseq⟩ := hj (pr.base x') hx
  obtain ⟨V', hV'aff, hx'V', hV'le⟩ :=
    Opens.isBasis_iff_nbhd.mp W'.isBasis_affineOpens (show x' ∈ pr ⁻¹ᵁ V.1 from hxV)
  have hsurj : Function.Surjective (j.appLE V.1 (j ⁻¹ᵁ V.1) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact j.app_surjective V.1 V.2
  have hker' := Stacks.Flatness.ker_inl_of_isPushout
    (Stacks.Flatness.isPushout_appLE_of_isPullback h.flip V.2 hV'aff hV'le) hsurj
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at hker'
  refine ⟨⟨V', hV'aff⟩, hx'V', r, fun i => (pr.appLE V.1 V' hV'le).hom (f i), ?_, ?_⟩
  · rw [hker', hker, Ideal.map_span, ← Set.range_comp]
    rfl
  · exact hSeq _ (HasRingHomProperty.appLE @Flat pr inferInstance V ⟨V', hV'aff⟩ hV'le) f hseq

/-- **Invariance of the affine-open regularity conditions under an isomorphism of the source.**
Precomposing with an isomorphism changes neither the closure of the image nor the kernel on
sections, since the comparison map of an isomorphism is injective on every open. -/
theorem kerGeneratedBy_iso_comp
    {Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}
    {Z Z' W : Scheme.{u}} (ε : Z' ≅ Z) (j : Z ⟶ W) (hj : KerGeneratedBy Seq j) :
    KerGeneratedBy Seq (ε.hom ≫ j) := by
  have hrange : Set.range (ε.hom ≫ j).base = Set.range j.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso ε.hom.base).2, Set.image_univ]
  intro x hx
  obtain ⟨U, hxU, r, f, hker, hseq⟩ := hj x (hrange ▸ hx)
  refine ⟨U, hxU, r, f, ?_, hseq⟩
  rw [← hker]
  exact RingHom.ker_comp_of_injective (f := (ε.hom.app (j ⁻¹ᵁ U.1)).hom) (j.app U.1).hom
    (ConcreteCategory.bijective_of_isIso (ε.hom.app (j ⁻¹ᵁ U.1))).1

end AlgebraicGeometry

end
