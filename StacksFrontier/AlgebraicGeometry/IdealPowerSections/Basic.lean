module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections away from an ideal as a direct-limit target

For an ideal `I` of a commutative ring `A` and an `A`-module `M`, the inclusions between
successive powers of `I` make `n ↦ Hom_A(I ^ n, M)` into a direct system. This file constructs
the canonical map from its colimit to the sections of the quasi-coherent sheaf `M̃` over the
open complement of `V(I)`.

## Main definitions

* `complementVanishing`: the open subset `Spec(A) \ V(I)`.
* `idealPowersHom`: the direct system `n ↦ Hom_A(I ^ n, M)`.
* `fractionSectionFun`: for a family of numerators indexed by an ideal `J`, the dependent
  function on an open subset of `Spec(A) \ V(J)` whose value at a prime `p` is `num f / f ^ n`
  for any `f ∈ J` outside `p`.
* `sectionOfHom`: the section of `M̃` away from `V(I)` attached to an element of
  `Hom_A(I ^ n, M)`, and `sectionsCocone` the resulting cocone on `idealPowersHom`.
* `canonicalMapToSectionsData`: the canonical map from the colimit of `idealPowersHom` to the
  sections of `M̃` away from `V(I)`, together with its value on colimit representatives.
* `canonicalMapToSections`: the underlying map of that construction.

## Main results

* `canonicalMapToSections_restrict_ι` evaluates the canonical map on every basic open `D(f)`
  with `f ∈ I`: the representative `φ` of level `n` restricts to the fraction `φ(fⁿ) / fⁿ`.
* `canonicalMapToSections_injective_of_fg`: the canonical map is injective as soon as `I` is
  finitely generated. This is the second assertion of Tag 01PM.

## Implementation notes

The transition map from exponent `m` to exponent `n`, for `m ≤ n`, is precomposition with the
inclusion `I ^ n ⊆ I ^ m`. The target is expressed by evaluating Mathlib's tilde sheaf on the
open complement of the vanishing locus. The ring and the module have independent universes; both
are lifted to their maximum for Mathlib's tilde construction, and scalars are then restricted
back to `A`.

The section attached to a representative `φ` of level `n` is built pointwise. Over a prime `p`
not containing `I` one chooses some `f ∈ I` outside `p` and takes the fraction `φ(fⁿ)/fⁿ` in
`M_p`; this is independent of the choice of `f`, because for `f, g ∈ I` one has
`gⁿ · φ(fⁿ) = φ(gⁿfⁿ) = fⁿ · φ(gⁿ)`. Independence is isolated in `fractionSectionFun_apply`,
which is what makes the resulting function locally a fraction and makes the construction linear
in `φ` and compatible with the transition maps. No finite generation of `I` is needed here.

Finite generation of `I` enters only in the injectivity proof. There the vanishing of the section
attached to `φ : Hom_A(I ^ n, M)` says that for every `f ∈ I` some power of `f` kills `φ(fⁿ)`;
since `fⁿ • φ(a) = a • φ(fⁿ)` for `a ∈ I ^ n`, that power of `f` in fact annihilates the whole
image of `φ`. So `I` is contained in the radical of the annihilator of `Im φ`, and finite
generation turns this into `I ^ N ⊆ Ann(Im φ)` for a single `N`, whence `φ` restricted to
`I ^ (n + N) = I ^ n · I ^ N` vanishes and `φ` dies in the colimit.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.StructureSheaf

universe u v w

namespace Stacks.AlgebraicGeometry.IdealPowerSections

/-!
### Fractions with denominators the `n`-th powers of the elements of an ideal
-/

section Fraction

/-- For a linear map on an ideal `S`, the elements `b • φ a` and `a • φ b` agree whenever
`a` and `b` lie in `S`: both are `φ (a * b)`. -/
public lemma smul_apply_comm {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    {S : Ideal R} (φ : (S : Ideal R) →ₗ[R] N) {a b : R} (ha : a ∈ S) (hb : b ∈ S) :
    b • φ ⟨a, ha⟩ = a • φ ⟨b, hb⟩ := by
  rw [← map_smul, ← map_smul]
  congr 1
  exact Subtype.ext (mul_comm b a)

variable {R : Type w} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]
  {J : Ideal R} {U : Opens (PrimeSpectrum R)}

/-- A choice of element of `J` lying outside a given prime of `U`. -/
public noncomputable def wit (hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal) (x : ↥U) : ↥J :=
  ⟨(hU x.1 x.2).choose, (hU x.1 x.2).choose_spec.1⟩

/-- The chosen element of `J` does lie outside the prime. -/
public lemma wit_notMem (hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal) (x : ↥U) :
    (wit hU x : R) ∉ (x.1 : PrimeSpectrum R).asIdeal := (hU x.1 x.2).choose_spec.2

/-- The dependent function on `U` whose value at a prime `p` is the fraction `num f / fⁿ`,
where `f` is a chosen element of `J` outside `p`. -/
public noncomputable def fractionSectionFun (hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal) (n : ℕ)
    (num : ↥J → N) : ∀ x : ↥U, Localizations N x.1 := fun x =>
  LocalizedModule.mk (num (wit hU x))
    ⟨(wit hU x : R) ^ n, Submonoid.pow_mem _ (wit_notMem hU x) n⟩

/-- The defining property of `fractionSectionFun`: provided the numerators satisfy the
cross relation `bⁿ • num a = aⁿ • num b`, the value at `p` is `num f / fⁿ` for *every*
`f ∈ J` outside `p`, not merely for the chosen one. -/
public lemma fractionSectionFun_apply {hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal} {n : ℕ}
    {num : ↥J → N} (hnum : ∀ a b : ↥J, (b : R) ^ n • num a = (a : R) ^ n • num b) (x : ↥U)
    (f : ↥J) (hf : (f : R) ∉ (x.1 : PrimeSpectrum R).asIdeal) :
    fractionSectionFun hU n num x =
      LocalizedModule.mk (num f) ⟨(f : R) ^ n, Submonoid.pow_mem _ hf n⟩ :=
  LocalizedModule.mk_eq.mpr ⟨1, by simpa [Submonoid.smul_def] using hnum (wit hU x) f⟩

/-- Two such functions agree, possibly with different exponents, as soon as their numerators
satisfy the corresponding cross relation. -/
public lemma fractionSectionFun_congr {hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal} {n m : ℕ}
    {num₁ num₂ : ↥J → N} (h : ∀ a : ↥J, (a : R) ^ m • num₁ a = (a : R) ^ n • num₂ a) (x : ↥U) :
    fractionSectionFun hU n num₁ x = fractionSectionFun hU m num₂ x :=
  LocalizedModule.mk_eq.mpr ⟨1, by simpa [Submonoid.smul_def] using h (wit hU x)⟩

/-- `fractionSectionFun` is additive in the numerators. -/
public lemma fractionSectionFun_add {hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal} {n : ℕ}
    (num₁ num₂ : ↥J → N) (x : ↥U) :
    fractionSectionFun hU n (fun a => num₁ a + num₂ a) x =
      fractionSectionFun hU n num₁ x + fractionSectionFun hU n num₂ x := by
  rw [fractionSectionFun, fractionSectionFun, fractionSectionFun, LocalizedModule.mk_add_mk,
    ← smul_add]
  exact (LocalizedModule.mk_cancel_common_left _ _ _).symm

/-- `fractionSectionFun` is compatible with scaling the numerators. -/
public lemma fractionSectionFun_smul {hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal} {n : ℕ} (r : R)
    (num : ↥J → N) (x : ↥U) :
    fractionSectionFun hU n (fun a => r • num a) x = r • fractionSectionFun hU n num x :=
  (LocalizedModule.smul'_mk _ _ _).symm

/-- `fractionSectionFun` is locally a fraction, hence a section of the structure sheaf. -/
public lemma fractionSectionFun_mem {hU : ∀ p ∈ U, ∃ f ∈ J, f ∉ p.asIdeal} {n : ℕ}
    (hJU : ∀ f ∈ J, PrimeSpectrum.basicOpen f ≤ U) {num : ↥J → N}
    (hnum : ∀ a b : ↥J, (b : R) ^ n • num a = (a : R) ^ n • num b) :
    fractionSectionFun hU n num ∈ sectionsSubmodule N U := by
  intro x
  refine ⟨PrimeSpectrum.basicOpen (wit hU x : R), wit_notMem hU x,
    homOfLE (hJU _ (wit hU x).2), num (wit hU x), (wit hU x : R) ^ n, fun y => ?_⟩
  have hy : (wit hU x : R) ∉ (y.1 : PrimeSpectrum R).asIdeal := y.2
  refine ⟨Submonoid.pow_mem (y.1 : PrimeSpectrum R).asIdeal.primeCompl hy n, ?_⟩
  exact fractionSectionFun_apply hnum ⟨y.1, hJU _ (wit hU x).2 y.2⟩ (wit hU x) hy

end Fraction

/-!
### Scalar multiplication on the sections of a tilde sheaf
-/

/-- Scalar multiplication on the sections of `N^~` is computed pointwise in the localizations.
The `R`-module structure carried by `tilde N` is the one obtained from the sections of the
structure sheaf of `Spec R`, so this is not a definitional identity. -/
public lemma tilde_smul_val_apply {R : CommRingCat.{w}} (N : ModuleCat.{w} R)
    (V : Opens (PrimeSpectrum R)) (r : R)
    (s : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op V)) (x : ↥V) :
    (r • s).1 x = r • s.1 x :=
  congrFun (congrArg Subtype.val
    (((tilde.modulesSpecToSheafIso N).app (.op V)).hom.hom.map_smul r s)) x

/-!
### The canonical map of Tag 01PM
-/

variable (A : Type u) [CommRing A]

/-- The open subset `Spec(A) \ V(I)`. -/
public def complementVanishing (I : Ideal A) : (Spec (.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩

variable (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- The direct system whose term at `n` is `Hom_A(I ^ n, M)`, with transition maps induced by
the inclusions between powers of `I`. -/
public def idealPowersHom : ℕ ⥤ ModuleCat.{max u v} A where
  obj n := ModuleCat.of A ((I ^ n : Ideal A) →ₗ[A] M)
  map {m n} f := ModuleCat.ofHom <|
    LinearMap.lcomp A M (Submodule.inclusion (Ideal.pow_le_pow_right (leOfHom f)))
  map_id n := by
    ext φ x
    rfl
  map_comp {m n k} f g := by
    ext φ x
    rfl

/-- The ideal on the universe lift of `A`, corresponding to `I`. -/
public def liftedIdeal : Ideal (ULift.{v} A) :=
  I.comap ULift.ringEquiv.toRingHom

/-- Membership in the lifted ideal is membership of the underlying element. -/
public lemma mem_liftedIdeal {a : ULift.{v} A} : a ∈ liftedIdeal.{u, v} A I ↔ a.down ∈ I :=
  Ideal.mem_comap

/-- Sections of `M̃`, with ring and module lifted to a common universe and scalars restricted
back to `A`. -/
public noncomputable def sectionsPresheaf :
    (TopologicalSpace.Opens (PrimeSpectrum (ULift.{v} A)))ᵒᵖ ⥤ ModuleCat.{max u v} A :=
  (modulesSpecToSheaf.obj
    (tilde (R := .of (ULift.{v} A)) (ModuleCat.of (ULift.{v} A) (ULift.{u} M)))).presheaf ⋙
      ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom

/-- The `A`-module of sections of `M̃` on `Spec(A) \ V(I)`, using the canonical identification
`Spec(ULift A) ≅ Spec(A)`. -/
public noncomputable abbrev sectionsOnComplement : ModuleCat.{max u v} A :=
  (sectionsPresheaf A M).obj
    (.op (complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I)))

/-- A module element regarded as a section on the complement of `V(I)`. -/
public noncomputable def toComplement : M →ₗ[A] sectionsOnComplement A I M where
  toFun m := tilde.toOpen (R := .of (ULift.{v} A)) (ModuleCat.of (ULift.{v} A) (ULift.{u} M))
    (complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I)) (ULift.up m)
  map_add' _ _ := map_add _ _ _
  map_smul' r m :=
    (tilde.toOpen (R := .of (ULift.{v} A)) (ModuleCat.of (ULift.{v} A) (ULift.{u} M))
      (complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I))).hom.map_smul
        (ULift.up r) (ULift.up m)

/-- If `f ∈ I`, then `D(f)` is contained in the complement of `V(I)`. -/
public lemma basicOpen_le_complementVanishing (f : A) (hf : f ∈ I) :
    PrimeSpectrum.basicOpen f ≤ complementVanishing A I := by
  intro p hp hI
  exact hp (hI hf)

/-- Restriction of sections on the complement to `D(f)`, for `f ∈ I`. -/
public noncomputable def restrictToBasicOpen (f : A) (hf : f ∈ I) :
    sectionsOnComplement A I M ⟶
      (sectionsPresheaf A M).obj (.op (PrimeSpectrum.basicOpen (ULift.up f))) :=
  (sectionsPresheaf A M).map (homOfLE
    (basicOpen_le_complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I)
      (ULift.up f) hf)).op

/-- The fraction `m/fⁿ` in the sections of a tilde sheaf on `D(f)`. -/
public noncomputable def tildeBasicOpenFraction {R : CommRingCat.{w}} (N : ModuleCat.{w} R)
    (f : R) (n : ℕ) (m : N) :
    (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op (PrimeSpectrum.basicOpen f)) :=
  IsLocalizedModule.mk' (S := Submonoid.powers f)
    (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom m ⟨f ^ n, ⟨n, rfl⟩⟩

/-- A section of `N^~` on `D(g)` whose value at every point of `D(g)` is the fraction
`m / gⁿ` is the section `tildeBasicOpenFraction N g n m`. -/
public lemma tildeBasicOpenFraction_eq {R : CommRingCat.{w}} (N : ModuleCat.{w} R) (g : R)
    (n : ℕ) (m : N)
    (t : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op (PrimeSpectrum.basicOpen g)))
    (ht : ∀ (p : PrimeSpectrum R) (hp : g ∉ p.asIdeal), t.1 ⟨p, hp⟩ =
      (LocalizedModule.mk m ⟨g ^ n, Submonoid.pow_mem p.asIdeal.primeCompl hp n⟩ :
        Localizations (R := (R : Type w)) N p)) :
    tildeBasicOpenFraction N g n m = t := by
  refine IsLocalizedModule.mk'_eq_iff.mpr (Subtype.ext (funext fun y => ?_))
  rw [Submonoid.smul_def, tilde_smul_val_apply, ht y.1 y.2, LocalizedModule.smul'_mk]
  exact (LocalizedModule.mk_cancel
    (⟨g ^ n, Submonoid.pow_mem (y.1 : PrimeSpectrum R).asIdeal.primeCompl y.2 n⟩ :
      (y.1 : PrimeSpectrum R).asIdeal.primeCompl) m).symm

/-- The section `m/fⁿ` on the basic open `D(f)`. -/
public noncomputable def basicOpenFraction (f : A) (n : ℕ) (m : M) :
    (sectionsPresheaf A M).obj (.op (PrimeSpectrum.basicOpen (ULift.up f))) :=
  tildeBasicOpenFraction (R := .of (ULift.{v} A))
    (ModuleCat.of (ULift.{v} A) (ULift.{u} M)) (ULift.up f) n (ULift.up m)

/-- A map to sections together with its value on every colimit representative.
The formula is the algebraic description in the proof of Tag 01PM. -/
public structure CanonicalMapToSectionsData where
  /-- The map out of the direct limit. -/
  hom : colimit (idealPowersHom A I M) ⟶ sectionsOnComplement A I M
  /-- On `D(f)` the representative `φ` maps to `φ(fⁿ)/fⁿ`. -/
  restrict_ι (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] M) (f : A) (hf : f ∈ I) :
    restrictToBasicOpen A I M f hf (hom (colimit.ι (idealPowersHom A I M) n φ)) =
      basicOpenFraction A M f n (φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩)

/-! ### Construction of the canonical map -/

/-- Every prime of `Spec(ULift A)` outside the vanishing locus of the lifted ideal misses some
element of that ideal. -/
public lemma exists_mem_liftedIdeal_notMem :
    ∀ p ∈ complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I),
      ∃ g ∈ liftedIdeal.{u, v} A I, g ∉ p.asIdeal := fun _ hp =>
  Set.not_subset.mp hp

/-- Each basic open attached to an element of the lifted ideal lies in the complement of its
vanishing locus. -/
public lemma basicOpen_le_liftedComplement :
    ∀ g ∈ liftedIdeal.{u, v} A I,
      PrimeSpectrum.basicOpen g ≤
        complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I) := fun g hg =>
  basicOpen_le_complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I) g hg

/-- The numerators attached to `φ : Hom_A(I ^ n, M)`: the element `g` of the lifted ideal is
sent to `φ(gⁿ)`, lifted. -/
public def liftedNumerator (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] M) :
    ↥(liftedIdeal.{u, v} A I) → ULift.{u} M := fun a =>
  ULift.up (φ ⟨(a : ULift.{v} A).down ^ n,
    Ideal.pow_mem_pow ((mem_liftedIdeal A I).mp a.2) n⟩)

/-- The cross relation `bⁿ • φ(aⁿ) = aⁿ • φ(bⁿ)` making the fractions `φ(gⁿ)/gⁿ` agree. -/
public lemma liftedNumerator_cross (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] M)
    (a b : ↥(liftedIdeal.{u, v} A I)) :
    ((b : ULift.{v} A) ^ n) • liftedNumerator A I M n φ a =
      ((a : ULift.{v} A) ^ n) • liftedNumerator A I M n φ b := by
  refine ULift.ext ?_
  exact smul_apply_comm (S := I ^ n) φ
    (Ideal.pow_mem_pow ((mem_liftedIdeal A I).mp a.2) n)
    (Ideal.pow_mem_pow ((mem_liftedIdeal A I).mp b.2) n)

/-- The section of `M̃` on `Spec(A) \ V(I)` attached to `φ : Hom_A(I ^ n, M)`: over a prime `p`
its value is `φ(gⁿ)/gⁿ` for any `g ∈ I` outside `p`. -/
public noncomputable def sectionOfHom (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] M) :
    sectionsOnComplement A I M :=
  ⟨fractionSectionFun (exists_mem_liftedIdeal_notMem A I) n (liftedNumerator A I M n φ),
    fractionSectionFun_mem (basicOpen_le_liftedComplement A I)
      (liftedNumerator_cross A I M n φ)⟩

/-- `sectionOfHom` is additive in the representative. -/
public lemma sectionOfHom_add (n : ℕ) (φ ψ : (I ^ n : Ideal A) →ₗ[A] M) :
    sectionOfHom A I M n (φ + ψ) = sectionOfHom A I M n φ + sectionOfHom A I M n ψ :=
  Subtype.ext <| funext <|
    fractionSectionFun_add (liftedNumerator A I M n φ) (liftedNumerator A I M n ψ)

/-- `sectionOfHom` commutes with the `A`-action on the representative. -/
public lemma sectionOfHom_smul (n : ℕ) (c : A) (φ : (I ^ n : Ideal A) →ₗ[A] M) :
    sectionOfHom A I M n (c • φ) = c • sectionOfHom A I M n φ := by
  apply Subtype.ext
  funext x
  refine (fractionSectionFun_smul (ULift.up c) (liftedNumerator A I M n φ) x).trans ?_
  exact (tilde_smul_val_apply (R := .of (ULift.{v} A))
    (ModuleCat.of (ULift.{v} A) (ULift.{u} M))
    (complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I)) (ULift.up c)
    (sectionOfHom A I M n φ) x).symm

/-- Enlarging the exponent does not change the section: the representatives `φ` and
`φ ∘ (I ^ n ⊆ I ^ m)` of the direct system have the same image. -/
public lemma sectionOfHom_inclusion {m n : ℕ} (hmn : m ≤ n) (φ : (I ^ m : Ideal A) →ₗ[A] M) :
    sectionOfHom A I M n (φ ∘ₗ Submodule.inclusion (Ideal.pow_le_pow_right hmn)) =
      sectionOfHom A I M m φ := by
  apply Subtype.ext
  funext x
  refine fractionSectionFun_congr (fun a => ?_) x
  refine ULift.ext ?_
  exact smul_apply_comm (S := I ^ m) φ
    (Ideal.pow_le_pow_right hmn (Ideal.pow_mem_pow ((mem_liftedIdeal A I).mp a.2) n))
    (Ideal.pow_mem_pow ((mem_liftedIdeal A I).mp a.2) m)

/-- `sectionOfHom` is `A`-linear in the representative. -/
public noncomputable def sectionOfHomLinear (n : ℕ) :
    ((I ^ n : Ideal A) →ₗ[A] M) →ₗ[A] ↥(sectionsOnComplement A I M) where
  toFun := sectionOfHom A I M n
  map_add' := sectionOfHom_add A I M n
  map_smul' c φ := sectionOfHom_smul A I M n c φ

/-- The cocone on the direct system `idealPowersHom` formed by these sections. -/
public noncomputable def sectionsCocone : Cocone (idealPowersHom A I M) where
  pt := sectionsOnComplement A I M
  ι :=
    { app n := ModuleCat.ofHom (X := ↥((idealPowersHom A I M).obj n))
        (Y := ↥(sectionsOnComplement A I M)) (sectionOfHomLinear A I M n)
      naturality {m n} g := by
        refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
        exact sectionOfHom_inclusion A I M (leOfHom g) φ }

/-- **Stacks Project, Tag 01PM (`canonical_map`).** The canonical map
`colim_n Hom_A(I ^ n, M) → Γ(Spec(A) \ V(I), M̃)`. -/
@[stacks 01PM "canonical_map"]
public noncomputable def canonicalMapToSectionsData : CanonicalMapToSectionsData A I M where
  hom := colimit.desc _ (sectionsCocone A I M)
  restrict_ι n φ f hf := by
    have h1 : ∀ ψ : ↥((idealPowersHom A I M).obj n),
        (colimit.desc (idealPowersHom A I M) (sectionsCocone A I M))
          (colimit.ι (idealPowersHom A I M) n ψ) = sectionOfHom A I M n ψ := fun ψ => by
      rw [← ModuleCat.comp_apply, colimit.ι_desc]
      rfl
    refine Eq.trans (congrArg (fun s => (restrictToBasicOpen A I M f hf) s) (h1 φ)) ?_
    have hfI : (ULift.up f : ULift.{v} A) ∈ liftedIdeal.{u, v} A I :=
      (mem_liftedIdeal A I).mpr hf
    refine Eq.symm (tildeBasicOpenFraction_eq (R := .of (ULift.{v} A))
      (ModuleCat.of (ULift.{v} A) (ULift.{u} M)) (ULift.up f) n
      (ULift.up (φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩)) _ (fun p hp => ?_))
    exact fractionSectionFun_apply (liftedNumerator_cross A I M n φ)
      ⟨p, basicOpen_le_liftedComplement A I _ hfI hp⟩ ⟨ULift.up f, hfI⟩ hp

/-- The canonical map, with its local evaluation rule supplied by the construction. -/
@[stacks 01PM "canonical_map"]
public noncomputable def canonicalMapToSections :
    colimit (idealPowersHom A I M) ⟶ sectionsOnComplement A I M :=
  (canonicalMapToSectionsData A I M).hom

/-- On every basic open `D(f)` with `f ∈ I`, a colimit representative `φ` has image
`φ(fⁿ)/fⁿ`. -/
@[stacks 01PM "canonical_map"]
public theorem canonicalMapToSections_restrict_ι (n : ℕ)
    (φ : (I ^ n : Ideal A) →ₗ[A] M) (f : A) (hf : f ∈ I) :
    restrictToBasicOpen A I M f hf
      (canonicalMapToSections A I M (colimit.ι (idealPowersHom A I M) n φ)) =
        basicOpenFraction A M f n (φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩) :=
  (canonicalMapToSectionsData A I M).restrict_ι n φ f hf

/-!
### Injectivity of the canonical map

This is the second assertion of Tag 01PM. It is the only place where the ideal is required to be
finitely generated.
-/

/-- The fraction `m / gⁿ` vanishes on `D(g)` exactly when some power of `g` annihilates `m`. -/
public lemma tildeBasicOpenFraction_eq_zero_iff {R : CommRingCat.{w}} (N : ModuleCat.{w} R)
    (g : R) (n : ℕ) (m : N) :
    tildeBasicOpenFraction N g n m = 0 ↔ ∃ k : ℕ, g ^ k • m = 0 := by
  rw [tildeBasicOpenFraction, IsLocalizedModule.mk'_eq_zero']
  refine ⟨fun ⟨s, hs⟩ => ?_, fun ⟨k, hk⟩ => ⟨⟨g ^ k, ⟨k, rfl⟩⟩, by simpa [Submonoid.smul_def]⟩⟩
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  refine ⟨k, ?_⟩
  rw [Submonoid.smul_def, ← hk] at hs
  exact hs

/-- A power of `f` annihilating `φ (f ^ n)` already annihilates the whole image of `φ`: for
`a ∈ I ^ n` one has `f ^ n • φ a = a • φ (f ^ n)`. -/
public lemma pow_mem_annihilator_range (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] M) {f : A}
    (hf : f ∈ I) {k : ℕ} (hk : f ^ k • φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ = 0) :
    f ^ (k + n) ∈ (LinearMap.range φ).annihilator := by
  refine Submodule.mem_annihilator.mpr ?_
  rintro m ⟨a, rfl⟩
  have h : (f ^ n) • φ a = (a : A) • φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ :=
    smul_apply_comm (S := I ^ n) φ a.2 (Ideal.pow_mem_pow hf n)
  calc f ^ (k + n) • φ a = f ^ k • ((f ^ n) • φ a) := by rw [pow_add, mul_smul]
    _ = (a : A) • (f ^ k • φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩) := by rw [h, smul_comm]
    _ = 0 := by rw [hk, smul_zero]

/-- If for every `f ∈ I` some power of `f` annihilates `φ (f ^ n)` and `I` is finitely generated,
then `φ` vanishes on a higher power of `I`, hence dies in the colimit. -/
public lemma exists_comp_inclusion_eq_zero (hI : I.FG) (n : ℕ)
    (φ : (I ^ n : Ideal A) →ₗ[A] M)
    (h : ∀ (f : A) (hf : f ∈ I), ∃ k : ℕ, f ^ k • φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ = 0) :
    ∃ N : ℕ, φ ∘ₗ Submodule.inclusion
      (Ideal.pow_le_pow_right (I := I) (Nat.le_add_right n N)) = 0 := by
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (J := (LinearMap.range φ).annihilator)
    (fun f hf => by
      obtain ⟨k, hk⟩ := h f hf
      exact ⟨k + n, pow_mem_annihilator_range A I M n φ hf hk⟩) hI
  refine ⟨N, LinearMap.ext fun a => ?_⟩
  have hK : (I ^ n) * (I ^ N) ≤
      Submodule.map (Submodule.subtype (I ^ n : Ideal A)) (LinearMap.ker φ) :=
    Ideal.mul_le.mpr fun p hp m hm => by
      have hpm : (⟨p * m, Ideal.mul_mem_right _ _ hp⟩ : ↥(I ^ n : Ideal A)) =
          m • (⟨p, hp⟩ : ↥(I ^ n : Ideal A)) := Subtype.ext (mul_comm p m)
      have hzero : φ (⟨p * m, Ideal.mul_mem_right _ _ hp⟩ : ↥(I ^ n : Ideal A)) = 0 := by
        rw [hpm, map_smul]
        exact Submodule.mem_annihilator.mp (hN hm) _ ⟨⟨p, hp⟩, rfl⟩
      exact ⟨⟨p * m, Ideal.mul_mem_right _ _ hp⟩, hzero, rfl⟩
  have ha : (a : A) ∈ (I ^ n) * (I ^ N) := by
    rw [← pow_add]; exact a.2
  obtain ⟨b, hb, hba⟩ := hK ha
  have : Submodule.inclusion (Ideal.pow_le_pow_right (I := I) (Nat.le_add_right n N)) a = b :=
    Subtype.ext hba.symm
  simpa [this] using hb

/-- A representative of the colimit that is killed by the canonical map is killed, after a
power shift, already in the direct system. -/
public lemma exists_pow_smul_eq_zero_of_apply_eq_zero (n : ℕ)
    (φ : (I ^ n : Ideal A) →ₗ[A] M)
    (hz : canonicalMapToSections A I M (colimit.ι (idealPowersHom A I M) n φ) = 0)
    (f : A) (hf : f ∈ I) :
    ∃ k : ℕ, f ^ k • φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ = 0 := by
  have h1 := canonicalMapToSections_restrict_ι A I M n φ f hf
  rw [hz, map_zero] at h1
  have h2 : tildeBasicOpenFraction (R := .of (ULift.{v} A))
      (ModuleCat.of (ULift.{v} A) (ULift.{u} M)) (ULift.up f) n
      (ULift.up (φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩)) = 0 := h1.symm
  obtain ⟨k, hk⟩ := (tildeBasicOpenFraction_eq_zero_iff _ _ _ _).mp h2
  exact ⟨k, by simpa using congrArg ULift.down hk⟩

/-- **Stacks Project, Tag 01PM (`injective`).** The canonical map
`colim_n Hom_A(I ^ n, M) → Γ(Spec(A) \ V(I), M̃)` is injective when `I` is finitely generated. -/
@[stacks 01PM "injective"]
public theorem canonicalMapToSections_injective_of_fg (hI : I.FG) :
    Function.Injective (canonicalMapToSections A I M) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, 0}
      (forget AddCommGrpCat.{max u v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have h2 : PreservesColimit (idealPowersHom A I M)
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat ⋙ forget AddCommGrpCat) :=
    comp_preservesColimit _ _
  have hpres : PreservesColimit (idealPowersHom A I M) (forget (ModuleCat.{max u v} A)) :=
    HasForget₂.forget_comp (C := ModuleCat.{max u v} A) (D := AddCommGrpCat) ▸ h2
  have key : ∀ z : ↥(colimit (idealPowersHom A I M)),
      canonicalMapToSections A I M z = 0 → z = 0 := by
    intro z hz
    obtain ⟨n, φ, rfl⟩ := Concrete.colimit_exists_rep (idealPowersHom A I M) z
    obtain ⟨N, hN⟩ := exists_comp_inclusion_eq_zero A I M hI n φ
      (exists_pow_smul_eq_zero_of_apply_eq_zero A I M n φ hz)
    have hshift : colimit.ι (idealPowersHom A I M) n φ =
        colimit.ι (idealPowersHom A I M) (n + N)
          ((idealPowersHom A I M).map (homOfLE (Nat.le_add_right n N)) φ) := by
      rw [← ModuleCat.comp_apply, colimit.w]
    rw [hshift]
    have : (idealPowersHom A I M).map (homOfLE (Nat.le_add_right n N)) φ = 0 := hN
    rw [this, map_zero]
  have := (LinearMap.ker_eq_bot' (f := (canonicalMapToSections A I M).hom)).mpr key
  exact LinearMap.ker_eq_bot.mp this

end Stacks.AlgebraicGeometry.IdealPowerSections
