module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAffineSpaceProbe
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcGluing
public import StacksFrontier.AlgebraicGeometry.Sites.OverOpenSubfunctorGluing
public import StacksFrontier.RingTheory.MvPolynomial.BasisQuotientLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedFinite
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableDischarged

/-!
# The Hilbert functor of points of an affine space is representable

Let `S` be an affine scheme, `n` a type and `d` a natural number. The degree-`d` Hilbert functor
of points of the affine space `𝔸(n; S)` over `S` is representable. This is the case of an affine
space in the source's proof of [Stacks, Tag 0B99], which with Tag 0B97 gives Tag 0B99.

## The proof

For `f₁, …, f_d ∈ ℤ[x_i; i ∈ n]` the subfunctor `F_f` consists of the families in whose
structure sheaf the images of the `f_l` form a basis, locally on the base. The locus of the base
where this holds is open (`Stacks.Hilbert.AffineSpaceChart.goodLocus`) and compatible with base
change (`goodLocus_baseChange`); this is the openness condition of the gluing criterion and
rests on Nakayama's lemma in the form
`Stacks.Hilbert.BasisQuotient.exists_isBasisIdeal_away`. The loci cover, because every point has
a neighbourhood where some `d` monomials form a basis
(`Stacks.Hilbert.BasisQuotient.exists_isBasisIdeal_away_monomial`). Each `F_f` is represented by
`S × Spec(Univ f)`, where `Univ f` is the universal ring of
`Stacks.Hilbert.BasisQuotient.equiv`. The gluing criterion
`Stacks.OverGluing.isRepresentable_of_openSubfunctors` concludes.

## Main definitions

* `Stacks.Hilbert.AffineSpaceChart.goodLocus`: the open locus of the base over which the images of
  `f` form a basis of a family.
* `Stacks.Hilbert.AffineSpaceChart.basisSubfunctor`: the subfunctor `F_f` of families having basis
  `f` locally on the base.
* `Stacks.Hilbert.AffineSpaceChart.chart`: the scheme `S × Spec(Univ f)` over `S`.

## Main results

* `Stacks.Hilbert.AffineSpaceChart.goodLocus_baseChange`: the good locus is compatible with base
  change.
* `Stacks.Hilbert.AffineSpaceChart.basisSubfunctor_isRepresentable`: `F_f` is represented by the
  chart.
* `Stacks.Hilbert.AffineSpaceChart.isRepresentable_hilbertFunctorOfRank_affineSpace`: the Hilbert
  functor of points of an affine space over an affine base is representable.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open scoped TensorProduct
open Stacks.Hilbert.BasisQuotient (IsBasisIdeal)
open Stacks.Hilbert.AffineSpaceProbe (ambient probeIdeal)

universe u

namespace Stacks.Hilbert.AffineSpaceChart

variable {S : Scheme.{u}} (n : Type u) (d : ℕ)

/-- Base change of a family along a morphism of affine probes is extension of its ideal. -/
theorem probeIdeal_baseChange_homMk {A B : CommRingCat.{u}} {s : Spec A ⟶ S} {s' : Spec B ⟶ S}
    (v : Spec B ⟶ Spec A) (w : v ≫ s = s') (Z : HilbertFamily (ambient (S := S) n) (Over.mk s) d) :
    probeIdeal n s' (baseChange (ambient n) (Over.homMk v w : Over.mk s' ⟶ Over.mk s) Z).ideal =
      (probeIdeal n s Z.ideal).map (MvPolynomial.map (Spec.preimage v).hom) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = v := ⟨_, Spec.map_preimage v⟩
  subst w
  rw [Spec.preimage_map]
  exact AffineSpaceProbe.probeIdeal_comap n s φ Z.ideal

variable {n d} (f : Fin d → MvPolynomial n ℤ)

/-- A family over an object `T` presented as an affine scheme `Spec C ≅ T.left` *has basis `f`*
if the images of the `f l` form a basis of its ring of functions. -/
def Good {T : Over S} (ζ : HilbertFamily (ambient n) T d) : Prop :=
  ∃ (C : CommRingCat.{u}) (u : Spec C ⟶ T.left), IsIso u ∧
    IsBasisIdeal f (probeIdeal n (u ≫ T.hom)
      (baseChange (ambient n) (Over.homMk u rfl : Over.mk (u ≫ T.hom) ⟶ T) ζ).ideal)

/-- Having basis `f` is stable under base change, read in any affine presentation. -/
theorem isBasisIdeal_of_good {T T' : Over S} (β : T' ⟶ T) {ζ : HilbertFamily (ambient n) T d}
    (h : Good f ζ) {C' : CommRingCat.{u}} (u' : Spec C' ⟶ T'.left) :
    IsBasisIdeal f (probeIdeal n (u' ≫ T'.hom)
      (baseChange (ambient n) (Over.homMk u' rfl : Over.mk (u' ≫ T'.hom) ⟶ T')
        (baseChange (ambient n) β ζ)).ideal) := by
  obtain ⟨C, u, hu, hb⟩ := h
  let v : Spec C' ⟶ Spec C := u' ≫ β.left ≫ inv u
  have w : v ≫ (u ≫ T.hom) = u' ≫ T'.hom := by simp [v, Over.w β]
  have he : (Over.homMk u' rfl : Over.mk (u' ≫ T'.hom) ⟶ T') ≫ β =
      (Over.homMk v w : Over.mk (u' ≫ T'.hom) ⟶ Over.mk (u ≫ T.hom)) ≫ Over.homMk u rfl := by
    ext; simp [v]
  rw [← baseChange_comp, he, baseChange_comp, probeIdeal_baseChange_homMk]
  exact IsBasisIdeal.map f hb (Spec.preimage v).hom.toIntAlgHom

/-- A family having basis `f` still has basis `f` after base change, read in an affine
presentation of the new base. -/
theorem good_baseChange {T T' : Over S} (β : T' ⟶ T) {ζ : HilbertFamily (ambient n) T d}
    (h : Good f ζ) {C' : CommRingCat.{u}} (u' : Spec C' ⟶ T'.left) [IsIso u'] :
    Good f (baseChange (ambient n) β ζ) :=
  ⟨C', u', inferInstance, isBasisIdeal_of_good f β h u'⟩

/-- An open neighbourhood of a point inside a given open, which is the spectrum of a ring. -/
theorem exists_SpecProbe {Y : Scheme.{u}} (O : Y.Opens) {y : Y} (hy : y ∈ O) :
    ∃ (C : CommRingCat.{u}) (a : Spec C ⟶ Y), IsOpenImmersion a ∧ y ∈ Set.range a ∧
      Set.range a ⊆ O := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy O.isOpen
  refine ⟨_, hV.fromSpec, hV.isOpenImmersion_fromSpec, ?_, ?_⟩
  · rwa [hV.range_fromSpec]
  · rwa [hV.range_fromSpec]

/-- **The locus where a family has basis `f`**: the points having an affine open neighbourhood
over which the family has basis `f`. -/
def goodLocus {T : Over S} (ξ : HilbertFamily (ambient n) T d) : Set T.left :=
  {t | ∃ (Z : Over S) (α : Z ⟶ T), IsAffine Z.left ∧ IsOpenImmersion α.left ∧
    t ∈ Set.range α.left ∧ Good f (baseChange (ambient n) α ξ)}

/-- The locus where a family has basis `f` is open. -/
theorem isOpen_goodLocus {T : Over S} (ξ : HilbertFamily (ambient n) T d) :
    IsOpen (goodLocus f ξ) := by
  rw [isOpen_iff_forall_mem_open]
  rintro t ⟨Z, α, hZ, hα, ht, hg⟩
  exact ⟨Set.range α.left, fun t' ht' ↦ ⟨Z, α, hZ, hα, ht', hg⟩,
    α.left.isOpenEmbedding.isOpen_range, ht⟩

omit f in
/-- The quotient attached to a family over an affine probe is finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_probeIdeal {A : CommRingCat.{u}} {s : Spec A ⟶ S}
    (Z : HilbertFamily (ambient n) (Over.mk s) d) :
    Module.IsFiniteLocallyFreeOfRank A (MvPolynomial n A ⧸ probeIdeal n s Z.ideal) d :=
  (AffineSpaceProbe.isFiniteLocallyFreeOfRank_subschemeι_iff n s Z.ideal d).mp
    Z.isFiniteLocallyFreeOfRank

/-- A point of an affine open of the base lies in the good locus as soon as the images of the
`f l` form a basis over a basic open of the affine open around it. -/
private theorem mem_goodLocus_of_away_aux {T : Over S} (ξ : HilbertFamily (ambient n) T d)
    {A : CommRingCat.{u}} (a : Spec A ⟶ T.left) [IsOpenImmersion a] (x : Spec A) (g : A)
    (hg : g ∉ x.asIdeal)
    (hb : IsBasisIdeal f ((probeIdeal n (a ≫ T.hom)
      (baseChange (ambient n) (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) ξ).ideal).map
        (MvPolynomial.map (algebraMap A (Localization.Away g))))) :
    a x ∈ goodLocus f ξ := by
  let Ag := CommRingCat.of (Localization.Away g)
  let ι₀ : Spec Ag ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))
  have hmem : x ∈ Set.range ι₀ := by
    have hbo : x ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := hg
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hbo
    obtain ⟨y, hy⟩ := hbo
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hmem
  let γ : Over.mk (ι₀ ≫ a ≫ T.hom) ⟶ T := Over.homMk (ι₀ ≫ a) (by simp)
  refine ⟨Over.mk (ι₀ ≫ a ≫ T.hom), γ, inferInstanceAs (IsAffine (Spec _)),
    inferInstanceAs (IsOpenImmersion (ι₀ ≫ a)), ⟨y, ?_⟩, ?_⟩
  · change (ι₀ ≫ a) y = a x
    rw [Scheme.Hom.comp_apply, hy]
  · refine ⟨Ag, 𝟙 (Spec Ag), inferInstance, ?_⟩
    have w : ι₀ ≫ a ≫ T.hom = 𝟙 (Spec Ag) ≫ (Over.mk (ι₀ ≫ a ≫ T.hom)).hom := by simp
    have he : (Over.homMk (𝟙 (Spec Ag)) rfl :
        Over.mk (𝟙 (Spec Ag) ≫ (Over.mk (ι₀ ≫ a ≫ T.hom)).hom) ⟶ Over.mk (ι₀ ≫ a ≫ T.hom)) ≫ γ =
        (Over.homMk ι₀ w : Over.mk (𝟙 (Spec Ag) ≫ (Over.mk (ι₀ ≫ a ≫ T.hom)).hom) ⟶
          Over.mk (a ≫ T.hom)) ≫ Over.homMk a rfl := by
      ext
      simp [γ]
    rw [← baseChange_comp, he, baseChange_comp, probeIdeal_baseChange_homMk, Spec.preimage_map]
    convert hb using 2
    exact Subsingleton.elim _ _

/-- **The good locus is compatible with base change.** This is the openness condition (2)(b) of
the gluing criterion in the source's proof of Tag 0B99. -/
theorem goodLocus_baseChange {T Y : Over S} (h : Y ⟶ T) (ξ : HilbertFamily (ambient n) T d) :
    goodLocus f (baseChange (ambient n) h ξ) = h.left ⁻¹' goodLocus f ξ := by
  ext y
  constructor
  · rintro ⟨Z', α', hZ', hα', ⟨z', rfl⟩, hg'⟩
    obtain ⟨A, a, ha, ⟨x₀, hx₀⟩, -⟩ :=
      exists_SpecProbe (⊤ : T.left.Opens) (Set.mem_univ (h.left (α'.left z')))
    have hz'O : z' ∈ (α'.left ≫ h.left) ⁻¹ᵁ a.opensRange := by
      change (α'.left ≫ h.left) z' ∈ a.opensRange
      rw [Scheme.Hom.comp_apply]
      exact ⟨x₀, hx₀⟩
    obtain ⟨B, b, hb, ⟨z'', hz''⟩, hbO⟩ := exists_SpecProbe _ hz'O
    have hrange : Set.range (b ≫ α'.left ≫ h.left) ⊆ Set.range a := by
      rintro _ ⟨w, rfl⟩
      obtain ⟨v, hv⟩ := hbO ⟨w, rfl⟩
      exact ⟨v, hv⟩
    let l : Spec B ⟶ Spec A := IsOpenImmersion.lift a (b ≫ α'.left ≫ h.left) hrange
    have hl : l ≫ a = b ≫ α'.left ≫ h.left := IsOpenImmersion.lift_fac _ _ _
    let ζ := baseChange (ambient n) (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) ξ
    have hM := isFiniteLocallyFreeOfRank_probeIdeal ζ
    let : Algebra A B := (Spec.preimage l).hom.toAlgebra
    have hB : IsBasisIdeal f ((probeIdeal n (a ≫ T.hom) ζ.ideal).map
        (MvPolynomial.map (algebraMap A B))) := by
      have hb' := isBasisIdeal_of_good f (Over.homMk b rfl : Over.mk (b ≫ Z'.hom) ⟶ Z') hg'
        (𝟙 (Spec B))
      have w : l ≫ a ≫ T.hom = 𝟙 (Spec B) ≫ (Over.mk (b ≫ Z'.hom)).hom := by
        rw [reassoc_of% hl, Over.w h, Over.w α']
        simp
      have he : (((Over.homMk (𝟙 (Spec B)) rfl :
          Over.mk (𝟙 (Spec B) ≫ (Over.mk (b ≫ Z'.hom)).hom) ⟶ Over.mk (b ≫ Z'.hom)) ≫
            (Over.homMk b rfl : Over.mk (b ≫ Z'.hom) ⟶ Z')) ≫ α') ≫ h =
          (Over.homMk l w : Over.mk (𝟙 (Spec B) ≫ (Over.mk (b ≫ Z'.hom)).hom) ⟶
            Over.mk (a ≫ T.hom)) ≫ Over.homMk a rfl := by
        ext
        simp [hl]
      rw [← baseChange_comp, ← baseChange_comp, ← baseChange_comp, he, baseChange_comp,
        probeIdeal_baseChange_homMk] at hb'
      exact hb'
    obtain ⟨g, hg, hbasis⟩ := BasisQuotient.exists_isBasisIdeal_away hM z''.asIdeal hB
    have hlz : (l z'').asIdeal = z''.asIdeal.comap (algebraMap A B) := by
      conv_lhs => rw [← Spec.map_preimage l]
      rfl
    have := mem_goodLocus_of_away_aux f ξ a (l z'') g (by rw [hlz]; exact hg) hbasis
    rwa [← Scheme.Hom.comp_apply, hl, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz''] at this
  · rintro ⟨Z, α, hZ, hα, ⟨z, hz⟩, hg⟩
    have hyO : y ∈ h.left ⁻¹ᵁ α.left.opensRange := ⟨z, hz⟩
    obtain ⟨C, a, ha, hya, haO⟩ := exists_SpecProbe _ hyO
    have hrange : Set.range (a ≫ h.left) ⊆ Set.range α.left := by
      rintro _ ⟨w, rfl⟩
      obtain ⟨v, hv⟩ := haO ⟨w, rfl⟩
      exact ⟨v, by rw [hv, Scheme.Hom.comp_apply]⟩
    let l : Spec C ⟶ Z.left := IsOpenImmersion.lift α.left (a ≫ h.left) hrange
    have hl : l ≫ α.left = a ≫ h.left := IsOpenImmersion.lift_fac _ _ _
    let lam : Over.mk (a ≫ Y.hom) ⟶ Z := Over.homMk l (by
      change l ≫ Z.hom = a ≫ Y.hom
      rw [← Over.w α, reassoc_of% hl, Over.w h])
    refine ⟨Over.mk (a ≫ Y.hom), Over.homMk a rfl, inferInstanceAs (IsAffine (Spec C)), ha, hya,
      ?_⟩
    have he : (Over.homMk a rfl : Over.mk (a ≫ Y.hom) ⟶ Y) ≫ h = lam ≫ α := by
      ext
      simp [lam, hl]
    rw [← baseChange_comp, he, baseChange_comp]
    exact good_baseChange f lam hg (𝟙 (Spec C))

/-- A point lies in the good locus as soon as, over a basic open of an affine open neighbourhood,
the images of the `f l` form a basis. -/
theorem mem_goodLocus_of_away {T : Over S} (ξ : HilbertFamily (ambient n) T d) {A : CommRingCat.{u}}
    (a : Spec A ⟶ T.left) [IsOpenImmersion a] (x : Spec A) (g : A) (hg : g ∉ x.asIdeal)
    (hb : IsBasisIdeal f ((probeIdeal n (a ≫ T.hom)
      (baseChange (ambient n) (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) ξ).ideal).map
        (MvPolynomial.map (algebraMap A (Localization.Away g))))) :
    a x ∈ goodLocus f ξ :=
  mem_goodLocus_of_away_aux f ξ a x g hg hb

/-- **The good loci cover.** Every point of the base has, for some choice of `d` monomials, a
neighbourhood over which their images form a basis. -/
theorem exists_mem_goodLocus {T : Over S} (ξ : HilbertFamily (ambient n) T d) (t : T.left) :
    ∃ f : Fin d → MvPolynomial n ℤ, t ∈ goodLocus f ξ := by
  obtain ⟨A, a, ha, ⟨x, rfl⟩, -⟩ := exists_SpecProbe (⊤ : T.left.Opens) (Set.mem_univ t)
  have hM := isFiniteLocallyFreeOfRank_probeIdeal
    (baseChange (ambient n) (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) ξ)
  obtain ⟨α, g, hg, hb⟩ := BasisQuotient.exists_isBasisIdeal_away_monomial (R := ℤ) hM x.asIdeal
  exact ⟨_, mem_goodLocus_of_away _ ξ a x g hg hb⟩

/-- **The subfunctor `F_f`** of families having basis `f` locally on the base. -/
def basisSubfunctor : Subfunctor (hilbertFunctorOfRank (ambient (S := S) n) d) where
  obj T := {ξ | ∀ t, t ∈ goodLocus (T := T.unop) f ξ}
  map {T Y} h ξ hξ y := by
    have e := goodLocus_baseChange f h.unop (show HilbertFamily (ambient n) T.unop d from ξ)
    change y ∈ goodLocus f (baseChange (ambient n) h.unop ξ)
    rw [e]
    exact hξ _

/-- The base change of a family along `h` lies in `F_f` if and only if `h` maps every point into
the good locus of the family. -/
theorem baseChange_mem_basisSubfunctor_iff {T Y : Over S} (h : Y ⟶ T)
    (ξ : HilbertFamily (ambient n) T d) :
    (hilbertFunctorOfRank (ambient n) d).map h.op ξ ∈ (basisSubfunctor (S := S) f).obj (op Y) ↔
      ∀ y : Y.left, h.left y ∈ goodLocus f ξ := by
  change (∀ y, y ∈ goodLocus f (baseChange (ambient n) h ξ)) ↔ _
  rw [goodLocus_baseChange]
  rfl

omit f in
/-- **The Hilbert functor of points is a Zariski sheaf**, being an fpqc sheaf (Tag 0B95). -/
theorem isSheaf_zariskiTopology_hilbertFunctorOfRank (X : Over S) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (hilbertFunctorOfRank X d) := by
  have hy₁ : Presieve.IsSheaf Scheme.fpqcTopology.{u} (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hy₂ : Presieve.IsSheaf Scheme.zariskiTopology.{u} (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have h₁ := (Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf _ _ hy₁).1
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqcTopology_hilbertFunctorOfRank X d))
  exact (Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf _ _ hy₂).2
    (Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_fpqcTopology h₁)

section Chart

variable [IsAffine S]

/-- The ring of the chart representing `F_f`: `Γ(S) ⊗ Univ f`. -/
abbrev chartRing : CommRingCat.{u} := CommRingCat.of (Γ(S, ⊤) ⊗[ℤ] BasisQuotient.Univ f)

/-- The structure morphism of the chart. -/
def chartBase : Spec (chartRing (S := S) f) ⟶ S :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ S.isoSpec.inv

/-- The chart representing `F_f`, as a scheme over `S`. -/
abbrev chart : Over S := Over.mk (chartBase (S := S) f)

/-- The inclusion of the universal ring into the ring of the chart. -/
def incR : BasisQuotient.Univ f →ₐ[ℤ] chartRing (S := S) f :=
  RingHom.toIntAlgHom (Algebra.TensorProduct.includeRight.toRingHom :
    BasisQuotient.Univ f →+* Γ(S, ⊤) ⊗[ℤ] BasisQuotient.Univ f)

/-- A ring map out of the ring of the chart, as a map of `ℤ`-algebras. -/
def liftZ {A : CommRingCat.{u}} (ψ : chartRing (S := S) f ⟶ A) : chartRing (S := S) f →ₐ[ℤ] A :=
  { ψ.hom with commutes' := fun r ↦ by simp }

/-- The universal ideal over the chart. -/
def univIdeal : Ideal (MvPolynomial n (chartRing (S := S) f)) :=
  (BasisQuotient.equiv f (incR (S := S) f)).1

omit [IsAffine S] in
/-- The images of `f` form a basis modulo the universal ideal. -/
theorem univIdeal_isBasisIdeal : IsBasisIdeal f (univIdeal (S := S) f) :=
  (BasisQuotient.equiv f _).2

/-- There is a family over the chart whose ideal is the universal ideal. -/
theorem exists_univFamily : ∃ Z : HilbertFamily (ambient (S := S) n) (chart f) d,
    probeIdeal n (chartBase f) Z.ideal = univIdeal f := by
  obtain ⟨I, hI⟩ := AffineSpaceProbe.probeIdeal_surjective n (chartBase (S := S) f) (univIdeal f)
  have hJ : Module.IsFiniteLocallyFreeOfRank (chartRing (S := S) f)
      (MvPolynomial n (chartRing (S := S) f) ⧸ univIdeal (S := S) f) d :=
    .of_basis (BasisQuotient.basisOf f (univIdeal_isBasisIdeal f))
  refine ⟨⟨I, (AffineSpaceProbe.isFiniteLocallyFreeOfRank_subschemeι_iff n _ I d).mpr ?_⟩, hI⟩
  rwa [hI]

/-- The universal family over the chart. -/
def univFamily : HilbertFamily (ambient (S := S) n) (chart f) d := (exists_univFamily f).choose

/-- The ideal of the universal family is the universal ideal. -/
theorem probeIdeal_univFamily :
    probeIdeal n (chart (S := S) f).hom (univFamily f).ideal = univIdeal f :=
  (exists_univFamily f).choose_spec

/-- The ideal of the base change of the universal family along `k` is the ideal classified by the
ring map from the universal ring induced by `k`. -/
theorem probeIdeal_baseChange_univFamily {A : CommRingCat.{u}} {s : Spec A ⟶ S}
    (k : Over.mk s ⟶ chart (S := S) f) :
    probeIdeal n s (baseChange (ambient n) k (univFamily f)).ideal =
      (BasisQuotient.equiv f ((liftZ f (Spec.preimage k.left)).comp (incR f))).1 := by
  have hk : k = Over.homMk k.left (Over.w k) := by ext; rfl
  rw [BasisQuotient.equiv_comp]
  conv_lhs => rw [hk]
  rw [probeIdeal_baseChange_homMk, probeIdeal_univFamily, univIdeal]
  rfl

/-- The good locus of the universal family is the whole chart. -/
theorem univFamily_mem : ∀ t, t ∈ goodLocus f (univFamily (S := S) f) := by
  intro t
  refine ⟨chart f, 𝟙 _, inferInstanceAs (IsAffine (Spec _)), inferInstanceAs
    (IsOpenImmersion (𝟙 _)), ⟨t, rfl⟩, ⟨chartRing f, 𝟙 _, inferInstance, ?_⟩⟩
  rw [← baseChange_comp, probeIdeal_baseChange_univFamily]
  exact (BasisQuotient.equiv f _).2

/-- The morphism from the chart to `F_f`, pulling back the universal family. -/
def chartToSubfunctor : yoneda.obj (chart (S := S) f) ⟶ (basisSubfunctor (S := S) f).toFunctor where
  app T := ↾ fun k ↦ ⟨baseChange (ambient n) k (univFamily f), fun y ↦ by
    have e := goodLocus_baseChange f k (univFamily f)
    rw [e]
    exact univFamily_mem f _⟩
  naturality {T T'} g := by
    ext k
    exact Subtype.ext <| baseChange_comp (ambient n) g.unop k (univFamily f)

/-- The ring map `Γ(S) → A` of a morphism `Spec A ⟶ S` to the affine scheme `S`. -/
def sigma {A : CommRingCat.{u}} (s : Spec A ⟶ S) : CommRingCat.of Γ(S, ⊤) ⟶ A :=
  Spec.preimage (s ≫ S.isoSpec.hom)

/-- For a morphism `k` over `S` into the chart, the ring map of `k` restricted to `Γ(S)` is the
ring map of the structure morphism. -/
theorem preimage_comp_includeLeft {A : CommRingCat.{u}} {s : Spec A ⟶ S}
    (k : Over.mk s ⟶ chart (S := S) f) :
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ Spec.preimage k.left =
      sigma s := by
  apply Spec.map_injective
  have hw : k.left ≫ chartBase f = s := Over.w k
  rw [sigma, Spec.map_preimage, Spec.map_comp, Spec.map_preimage]
  calc k.left ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      (k.left ≫ chartBase f) ≫ S.isoSpec.hom := by simp [chartBase]
    _ = s ≫ S.isoSpec.hom := by rw [hw]

/-- On affine probes, the morphism from the chart to `F_f` is injective. -/
theorem chartToSubfunctor_injective (A : CommRingCat.{u}) (s : Spec A ⟶ S) :
    Function.Injective ((chartToSubfunctor (S := S) f).app (op (Over.mk s))) := by
  intro k k' hkk
  have h := congrArg (fun ζ : (basisSubfunctor (S := S) f).toFunctor.obj (op (Over.mk s)) ↦
    probeIdeal n s (ζ.1 : HilbertFamily (ambient n) (Over.mk s) d).ideal) hkk
  change probeIdeal n s (baseChange (ambient n) k (univFamily f)).ideal =
    probeIdeal n s (baseChange (ambient n) k' (univFamily f)).ideal at h
  rw [probeIdeal_baseChange_univFamily, probeIdeal_baseChange_univFamily] at h
  have hR := (BasisQuotient.equiv f).injective (Subtype.ext h)
  have hL := (preimage_comp_includeLeft f k).trans (preimage_comp_includeLeft f k').symm
  have hψ : Spec.preimage k.left = Spec.preimage k'.left := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have ha := congrArg (fun φ : CommRingCat.of Γ(S, ⊤) ⟶ A ↦ φ a) hL
      have hb := congrArg (fun φ : BasisQuotient.Univ f →ₐ[ℤ] A ↦ φ b) hR
      simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at ha
      have e : a ⊗ₜ[ℤ] b = Algebra.TensorProduct.includeLeftRingHom a *
          (Algebra.TensorProduct.includeRight b : Γ(S, ⊤) ⊗[ℤ] BasisQuotient.Univ f) := by
        simp
      rw [e, map_mul, map_mul]
      exact congrArg₂ (· * ·) ha hb
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact Over.OverMorphism.ext <| by
    rw [← Spec.map_preimage k.left, ← Spec.map_preimage k'.left, hψ]

/-- A family over an affine probe whose ideal has basis `f` is the base change of the universal
family along some morphism to the chart. -/
theorem exists_chart_lift {C : CommRingCat.{u}} (s : Spec C ⟶ S)
    (ζ : HilbertFamily (ambient n) (Over.mk s) d) (hζ : IsBasisIdeal f (probeIdeal n s ζ.ideal)) :
    ∃ k : Over.mk s ⟶ chart (S := S) f, baseChange (ambient n) k (univFamily f) = ζ := by
  let φ : BasisQuotient.Univ f →ₐ[ℤ] C := (BasisQuotient.equiv f).symm ⟨_, hζ⟩
  let ψ : Γ(S, ⊤) ⊗[ℤ] BasisQuotient.Univ f →ₐ[ℤ] C :=
    Algebra.TensorProduct.lift (sigma s).hom.toIntAlgHom φ fun _ _ ↦ Commute.all _ _
  have hk : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chartBase f = s := by
    have : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(S, ⊤) →+* Γ(S, ⊤) ⊗[ℤ] BasisQuotient.Univ f) ≫ CommRingCat.ofHom ψ.toRingHom =
          sigma s := by
      ext a
      simp [ψ]
    rw [chartBase, ← Category.assoc, ← Spec.map_comp, this, sigma, Spec.map_preimage,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let k : Over.mk s ⟶ chart (S := S) f := Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hk
  refine ⟨k, HilbertFamily.ext (AffineSpaceProbe.probeIdeal_injective n s ?_)⟩
  rw [probeIdeal_baseChange_univFamily]
  have hcomp : (liftZ f (Spec.preimage k.left)).comp (incR f) = φ := by
    ext b
    change (Spec.preimage (Spec.map (CommRingCat.ofHom ψ.toRingHom))).hom
      ((1 : Γ(S, ⊤)) ⊗ₜ[ℤ] b) = φ b
    rw [Spec.preimage_map, CommRingCat.hom_ofHom]
    change ψ ((1 : Γ(S, ⊤)) ⊗ₜ[ℤ] b) = φ b
    simp [ψ]
  rw [hcomp]
  change ((BasisQuotient.equiv f) ((BasisQuotient.equiv f).symm ⟨_, hζ⟩)).1 = _
  rw [Equiv.apply_symm_apply]

/-- **`F_f` is represented by the chart.** -/
theorem basisSubfunctor_isRepresentable :
    (basisSubfunctor (S := S) f).toFunctor.IsRepresentable := by
  have hsep : Presieve.IsSeparated (Scheme.zariskiTopology.over S)
      (basisSubfunctor (S := S) f).toFunctor := by
    intro Y R hR x y₁ y₂ h₁ h₂
    exact Subtype.ext ((isSheaf_zariskiTopology_hilbertFunctorOfRank (d := d)
      (ambient (S := S) n)).isSeparated R hR (fun Z g hg ↦ (x g hg).1) y₁.1 y₂.1
      (fun Z g hg ↦ congrArg Subtype.val (h₁ g hg)) (fun Z g hg ↦ congrArg Subtype.val (h₂ g hg)))
  have hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) (yoneda.obj (chart (S := S) f)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hbij := Stacks.OverGluing.bijective_app_of_probes (chartToSubfunctor (S := S) f) hF hsep
    (chartToSubfunctor_injective f) (by
      intro Y ξ y
      obtain ⟨Z, α, hZ, hα, hy, C, u, hu, hb⟩ := ξ.2 y
      let P : Over S := Over.mk (u ≫ Z.hom)
      let β : P ⟶ Y := Over.homMk u rfl ≫ α
      refine ⟨P, β, inferInstanceAs (IsOpenImmersion (u ≫ α.left)), ?_, ?_⟩
      · obtain ⟨z, rfl⟩ := hy
        obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso u.base).2 z
        exact ⟨c, rfl⟩
      · obtain ⟨k, hk⟩ := exists_chart_lift f (u ≫ Z.hom) _ hb
        refine ⟨k, Subtype.ext ?_⟩
        change baseChange (ambient n) k (univFamily f) =
          baseChange (ambient n) (Over.homMk u rfl ≫ α) ξ.1
        rw [hk]
        exact (baseChange_comp (ambient n) _ α ξ.1).symm)
  have : IsIso (chartToSubfunctor (S := S) f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y
    exact (isIso_iff_bijective _).mpr (hbij Y.unop)
  exact Functor.IsRepresentable.mk' (asIso (chartToSubfunctor (S := S) f))

end Chart

omit f in
/-- **The Hilbert functor of points of an affine space over an affine base is representable.** -/
theorem isRepresentable_hilbertFunctorOfRank_affineSpace [IsAffine S] :
    (hilbertFunctorOfRank (ambient (S := S) n) d).IsRepresentable :=
  Stacks.OverGluing.isRepresentable_of_openSubfunctors _
    (isSheaf_zariskiTopology_hilbertFunctorOfRank _)
    (fun f : Fin d → MvPolynomial n ℤ ↦ basisSubfunctor (S := S) f)
    (fun f ↦ basisSubfunctor_isRepresentable f)
    (fun f _T ξ ↦ ⟨goodLocus f ξ, isOpen_goodLocus f ξ⟩)
    (fun f _T _Y ξ h ↦ baseChange_mem_basisSubfunctor_iff f h ξ)
    (fun _T ξ t ↦ exists_mem_goodLocus ξ t)

end Stacks.Hilbert.AffineSpaceChart

namespace Stacks.Hilbert

/-- A representing object of the Hilbert functor gives the data of
`Stacks.Hilbert.RepresentsHilbertFunctorOfRank`. -/
def representsHilbertFunctorOfRankOfRepresentableBy {S : Scheme.{u}} {X H : Over S} {d : ℕ}
    (R : (hilbertFunctorOfRank X d).RepresentableBy H) : RepresentsHilbertFunctorOfRank X H d where
  family := R.homEquiv
  naturality g f := congrArg HilbertFamily.ideal (R.homEquiv_comp g f)

end Stacks.Hilbert

end
