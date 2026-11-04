module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.EssentialFiniteness.ArtinianTarget
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.Smoothing.EssentiallySmooth

/-!
# Enlarging an Artinian local factorization to absorb a prescribed element

Let `D` be an Artinian local ring mapping to an Artinian local ring `T` by a flat local
homomorphism, both of characteristic a prime `p`, and let `y ∈ T`. This file produces a further
Artinian local ring `D'` and a factorization `D → D' → T` of the given map in which `D → D'` is
essentially smooth, `D' → T` is again flat and local, and some positive power `y ^ e` lies in the
image of `D'`.

That is Stacks 07FI, whose target `T` is `Λ_𝔮/𝔮ⁿΛ_𝔮` and whose `y` is the image of an element
`λ ∈ Λ`. The source's `D` comes from Lemma 07FH, together with the map `k[y₁,…,y_m]_𝔭/𝔭ⁿ → D`
which the lemma's displayed four-term factorization starts from; see the implementation notes for
how that part of the setup is represented here.

## Main results

* `Stacks.Smoothing.exists_essentiallySmooth_artinianLocal_enlargement`: the ring-theoretic
  content, stated for an arbitrary flat local map of Artinian local rings of characteristic `p`
  and an arbitrary element of its target.
* `Stacks.Smoothing.exists_essentiallySmooth_enlargement_containing_pow`: Stacks 07FI, the
  previous result read off at `T = Λ_𝔮/𝔮ⁿΛ_𝔮` and `y = λ`.
* `Stacks.Smoothing.exists_essentiallySmooth_enlargement_residueField`: the same enlargement with
  the residue field extension *prescribed* instead of manufactured, hence with no power-taking
  anywhere and no hypothesis on the characteristic. This is the form Stacks 07FT needs: it
  produces a factorization whose middle ring has a given formally smooth extension of `κ(D)` as
  its residue field.

## Implementation notes

*The argument.* Write `κ` for the residue field of `D` and `K` for that of `T`. Since `𝔪_D` is
nilpotent and `D` has prime characteristic, the residue map `D → κ` admits a ring-homomorphic
section `σ` (Lemma 09EZ, `IsLocalRing.exists_residueField_section_compatible`), so `D` is a
`κ`-algebra. Let `α ∈ K` be the residue of `y`. Over a field of characteristic `p` some positive
power of any element generates a formally smooth, essentially finite type subextension of `K`:
if `α` is transcendental take `κ(α)`, which is formally smooth because `α` is algebraically
independent; if `α` is algebraic, then `α` is purely inseparable over the separable closure of
`κ` in `κ(α)`, so `α ^ (p ^ m)` is separable over `κ` for some `m`, and a simple separable
extension is formally étale hence formally smooth. Call that subextension `L`. Formal smoothness
of `L/κ` lifts the inclusion `L → K` along the surjection `T → K` with nilpotent kernel to a map
`τ : L → T` compatible with `σ`, and `D' := D ⊗[κ] L` is then the ring wanted: it is Artinian
(finite over `L`, as `D` is a finite `κ`-module by Lemma 07DT(1) applied to `σ`) and local (it
surjects onto `L` with nilpotent kernel), `D → D'` is essentially smooth by base change, and the
pair `(D → T, τ)` induces `b' : D' → T` through which the given map factors. Flatness of `b'`
follows from flatness of the composite by the fibrewise criterion (Lemma 00MP, whose fibre
hypothesis is free here because `D'/𝔪_D D'` is a field). Finally `y ^ e` and `b' (1 ⊗ z)` have the
same residue in `K`, hence differ by a nilpotent, and in characteristic `p` raising to a large
`p`-power turns that difference into an equality: `y ^ (e · p ^ r)` is in the image of `b'`.

*How the setup of Lemma 07FH is represented.* The only part of that lemma's data on which the
conclusion of 07FI depends is the right-hand half of its factorization: the Artinian local `D`
and the flat local map `D → Λ_𝔮/𝔮ⁿΛ_𝔮`. Those are taken as hypotheses here, in exactly the
shape 07FH records them. The left-hand map `k[y₁,…,y_m]_𝔭/𝔭ⁿ → D` is not reproduced: it plays no
role in the conclusion beyond composing with the `D → D'` produced here, so the displayed
four-term factorization `k[y₁,…,y_m]_𝔭/𝔭ⁿ → D → D' → Λ_𝔮/𝔮ⁿΛ_𝔮` follows for *any* such map
from `b' ∘ c = b`, and omitting it makes the statement stronger rather than weaker. Likewise
`Λ_𝔮/𝔮ⁿΛ_𝔮` being local and Artinian is taken as a hypothesis rather than rederived, again as in
07FH; it is satisfied whenever `Λ` is Noetherian and `1 ≤ n`, so nothing here is vacuous.

*What "`λ^q ∈ D'`" means.* In the source `D'` is not a subring of `Λ_𝔮/𝔮ⁿΛ_𝔮`; the phrase means
that the image of `λ^q` comes from `D'`, which is what is proved. The reading is faithful because
`D' → Λ_𝔮/𝔮ⁿΛ_𝔮` is flat and local, hence injective, so `D'` is a subring of the target in the
only sense available.

*Where the two notions in the statement come from.* Essential smoothness is
`RingHom.IsEssentiallySmooth` of `StacksFrontier.RingTheory.Smoothing.EssentiallySmooth`, imported
rather than restated, so the chapter has a single notion of it. The target ring is written out as
`Λ_𝔮 ⧸ 𝔮ⁿΛ_𝔮` rather than through an abbreviation: `Stacks.Smoothing.primePowerQuotient` of
`StacksFrontier.RingTheory.Smoothing.InseparableResidueField` is a reducible abbreviation for exactly
this type, and spelling the type out keeps that abbreviation the library's only one while avoiding
an import of the whole of 07FG and 07FH, none of whose machinery this file's proof uses. A
consumer holding `Λ_𝔮/𝔮ⁿΛ_𝔮` in the abbreviated spelling can apply the theorem below unchanged,
the abbreviation being reducible.

*Generality.* The source assumes `λ ∉ 𝔮`; the proof never uses it, and the statement below is
correspondingly proved for every `λ ∈ Λ`. The source's exponent `q` is called `e` here, `q` being
taken by the prime ideal `𝔮`.

## References

* [Stacks Project, Tag 07FI](https://stacks.math.columbia.edu/tag/07FI)
* [Stacks Project, Tag 07FH](https://stacks.math.columbia.edu/tag/07FH)
* [Stacks Project, Tag 09EZ](https://stacks.math.columbia.edu/tag/09EZ)
* [Stacks Project, Tag 07DT](https://stacks.math.columbia.edu/tag/07DT)
* [Stacks Project, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP)
-/

@[expose] public section

universe u

namespace Stacks.Smoothing

open IntermediateField IsLocalRing TensorProduct

/-! ### Powers in the image of a map to an Artinian local ring of characteristic `p` -/

/-- Let `f : R → S` with `S` Artinian local of characteristic a prime `p`. If `y ∈ S` agrees with
`f x` modulo the maximal ideal, then a positive power of `y` is in the image of `f`: the
difference is nilpotent, and in characteristic `p` a high enough `p`-power of a difference is the
difference of the `p`-powers. -/
private lemma exists_pow_mem_range_of_sub_mem_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    (f : R →+* S) (p : ℕ) [Fact (Nat.Prime p)] [CharP S p] (x : R) (y : S)
    (h : y - f x ∈ maximalIdeal S) :
    ∃ e : ℕ, 0 < e ∧ ∃ z : R, f z = y ^ e := by
  have hdim : Ring.KrullDimLE 0 S := isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  obtain ⟨m, hm⟩ :=
    (Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr h : IsNilpotent (y - f x))
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt m (Fact.out (p := Nat.Prime p)).one_lt
  refine ⟨p ^ r, pow_pos (Fact.out (p := Nat.Prime p)).pos _, x ^ p ^ r, ?_⟩
  have hz : (y - f x) ^ p ^ r = 0 := pow_eq_zero_of_le hr.le hm
  rw [sub_pow_char_pow] at hz
  rw [map_pow]
  exact (sub_eq_zero.mp hz).symm

/-! ### Flatness and injectivity along local homomorphisms -/

/-- Fibrewise criterion in the Artinian local case: if `R → S → T` are local homomorphisms of
Artinian local rings, the image of `𝔪_R` in `S` is maximal, and `R → T` is flat, then `S → T` is
flat. The fibre hypothesis of Stacks 00MP is automatic, the fibre ring over `S/𝔪_R S` being a
module over a field. -/
private lemma flat_of_flat_comp_of_isMaximal_map_maximalIdeal
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [IsArtinianRing R] [IsArtinianRing S] [IsArtinianRing T]
    (f : R →+* S) (g : S →+* T) [IsLocalHom f] [IsLocalHom g]
    (hflat : RingHom.Flat (g.comp f))
    [((maximalIdeal R).map f).IsMaximal] : RingHom.Flat g := by
  let := f.toAlgebra
  let := g.toAlgebra
  let : Field (S ⧸ (maximalIdeal R).map f) := Ideal.Quotient.field _
  let : Algebra R T := (g.comp f).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Flat R T := RingHom.flat_algebraMap_iff.mp hflat
  have : Module.Flat (S ⧸ (maximalIdeal R).map f)
      (T ⧸ (maximalIdeal R).map f • (⊤ : Submodule S T)) :=
    have : Module.Free (S ⧸ (maximalIdeal R).map f)
        (T ⧸ (maximalIdeal R).map f • (⊤ : Submodule S T)) :=
      Module.Free.of_divisionRing _ _
    Module.Flat.of_free
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat
      (R := R) (S := S) (S' := T) (M := T)).2

/-- A ring surjecting onto a field with nilpotent kernel is local. -/
private lemma isLocalRing_of_surjective_field_of_nilpotent_ker
    {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f)) : IsLocalRing R := by
  have hmax := RingHom.ker_isMaximal_of_surjective f hf
  refine IsLocalRing.of_unique_max_ideal ⟨RingHom.ker f, hmax, fun J hJ => ?_⟩
  refine (hmax.eq_of_le hJ.ne_top fun x hx => ?_).symm
  obtain ⟨m, hm⟩ := hker
  have hxpow : x ^ m ∈ RingHom.ker f ^ m := Ideal.pow_mem_pow hx m
  rw [hm] at hxpow
  exact hJ.isPrime.mem_of_pow_mem m (by rw [hxpow]; exact J.zero_mem)

/-! ### Base change of an Artinian local ring along an extension of its residue field -/

section BaseChange

variable (D L : Type*) [CommRing D] [IsLocalRing D] [IsArtinianRing D] [Field L]
  [Algebra (ResidueField D) D] [Algebra (ResidueField D) L]

/-- `L ⊗[κ] D` is local, where `κ` is the residue field of `D` and `κ → D` is a section of the
residue map: it surjects onto `L` with nilpotent kernel, the kernel being generated by the
image of the nilpotent `𝔪_D`. -/
private lemma isLocalRing_tensorProduct_left
    (hsec : (residue D).comp (algebraMap (ResidueField D) D) = RingHom.id _) :
    IsLocalRing (TensorProduct (ResidueField D) L D) := by
  let F := ResidueField D
  let r : D →ₐ[F] F :=
    { residue D with
      commutes' := fun x => congrArg (fun h : F →+* F => h x) hsec }
  let g : (L ⊗[F] D) →ₐ[L] (L ⊗[F] F) := Algebra.TensorProduct.map (AlgHom.id L L) r
  let e : (L ⊗[F] F) ≃ₐ[L] L := Algebra.TensorProduct.rid F L L
  let f : (L ⊗[F] D) →+* L := (e.toAlgHom.comp g).toRingHom
  have hg : Function.Surjective g :=
    Algebra.TensorProduct.map_surjective (AlgHom.id L L) r (fun x => ⟨x, rfl⟩) residue_surjective
  have hf : Function.Surjective f := e.surjective.comp hg
  have hker : RingHom.ker g = Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker r) :=
    Algebra.TensorProduct.lTensor_ker r residue_surjective
  have hmax : RingHom.ker r = maximalIdeal D := IsLocalRing.ker_residue (R := D)
  have hnil : IsNilpotent (RingHom.ker f) := by
    have hD : IsNilpotent (maximalIdeal D) :=
      (isArtinianRing_iff_isNilpotent_maximalIdeal D).mp inferInstance
    have hmap : IsNilpotent (Ideal.map
        (Algebra.TensorProduct.includeRight : D →ₐ[F] (L ⊗[F] D)) (maximalIdeal D)) := by
      obtain ⟨m, hm⟩ := hD
      refine ⟨m, ?_⟩
      rw [← Ideal.map_pow, hm]
      exact Ideal.map_bot
    have hkerf : RingHom.ker f = RingHom.ker g := by
      ext x
      change e (g x) = 0 ↔ g x = 0
      rw [← map_zero e]
      exact e.injective.eq_iff
    rw [hkerf, hker, hmax]
    exact hmap
  exact isLocalRing_of_surjective_field_of_nilpotent_ker f hf hnil

/-- `L ⊗[κ] D` is Artinian: `D` is a finite `κ`-module by Stacks 07DT(1) applied to the section,
so the base change is a finite `L`-module. -/
private lemma isArtinianRing_tensorProduct_left
    (hsec : (residue D).comp (algebraMap (ResidueField D) D) = RingHom.id _) :
    IsArtinianRing (TensorProduct (ResidueField D) L D) := by
  let F := ResidueField D
  have hfin : (algebraMap F D).Finite :=
    (finite_iff_residue_finite (algebraMap F D)).2 (by rw [hsec]; exact RingHom.Finite.id _)
  let : Module.Finite F D := RingHom.finite_algebraMap.mp hfin
  let : Module.Finite L (L ⊗[F] D) := Module.Finite.base_change F L D
  exact IsArtinianRing.of_finite L _

/-- `D ⊗[κ] L` is local. -/
private lemma isLocalRing_tensorProduct_right
    (hsec : (residue D).comp (algebraMap (ResidueField D) D) = RingHom.id _) :
    IsLocalRing (TensorProduct (ResidueField D) D L) :=
  have := isLocalRing_tensorProduct_left D L hsec
  (Algebra.TensorProduct.comm (ResidueField D) L D).toRingEquiv.isLocalRing

/-- `D ⊗[κ] L` is Artinian. -/
private lemma isArtinianRing_tensorProduct_right
    (hsec : (residue D).comp (algebraMap (ResidueField D) D) = RingHom.id _) :
    IsArtinianRing (TensorProduct (ResidueField D) D L) :=
  have := isArtinianRing_tensorProduct_left D L hsec
  (Algebra.TensorProduct.comm (ResidueField D) L D).toRingEquiv.isArtinianRing

omit [IsArtinianRing D] in
/-- The image of `𝔪_D` in `D ⊗[κ] L` is maximal: it is the kernel of the surjection onto `L`
obtained by reducing the left factor. -/
private lemma isMaximal_map_maximalIdeal_includeLeft
    (hsec : (residue D).comp (algebraMap (ResidueField D) D) = RingHom.id _) :
    ((maximalIdeal D).map (Algebra.TensorProduct.includeLeftRingHom :
      D →+* TensorProduct (ResidueField D) D L)).IsMaximal := by
  let F := ResidueField D
  let r : D →ₐ[F] F :=
    { residue D with
      commutes' := fun x => congrArg (fun h : F →+* F => h x) hsec }
  let g : (D ⊗[F] L) →ₐ[F] (F ⊗[F] L) := Algebra.TensorProduct.map r (AlgHom.id F L)
  let e : (F ⊗[F] L) ≃ₐ[F] L := Algebra.TensorProduct.lid F L
  let f : (D ⊗[F] L) →+* L := (e.toAlgHom.comp g).toRingHom
  have hg : Function.Surjective g :=
    Algebra.TensorProduct.map_surjective r (AlgHom.id F L) residue_surjective (fun x => ⟨x, rfl⟩)
  have hf : Function.Surjective f := e.surjective.comp hg
  have hker : RingHom.ker g = Ideal.map Algebra.TensorProduct.includeLeft (RingHom.ker r) :=
    Algebra.TensorProduct.rTensor_ker r residue_surjective
  have hkerf : RingHom.ker f = RingHom.ker g := by
    ext x
    change e (g x) = 0 ↔ g x = 0
    rw [← map_zero e]
    exact e.injective.eq_iff
  have hmax : RingHom.ker r = maximalIdeal D := IsLocalRing.ker_residue (R := D)
  change (Ideal.map (Algebra.TensorProduct.includeLeft : D →ₐ[F] D ⊗[F] L)
    (maximalIdeal D)).IsMaximal
  rw [← hmax, ← hker, ← hkerf]
  exact RingHom.ker_isMaximal_of_surjective f hf

/-- `D → D ⊗[κ] L` is a local homomorphism: the image of `𝔪_D` is maximal, hence contained in the
maximal ideal of the local ring `D ⊗[κ] L`. -/
private lemma isLocalHom_includeLeft_tensorProduct_right
    (hsec : (residue D).comp (algebraMap (ResidueField D) D) = RingHom.id _) :
    IsLocalHom (Algebra.TensorProduct.includeLeftRingHom :
      D →+* TensorProduct (ResidueField D) D L) :=
  have := isLocalRing_tensorProduct_right D L hsec
  ((IsLocalRing.local_hom_TFAE _).out 3 1).mp
    (IsLocalRing.le_maximalIdeal (isMaximal_map_maximalIdeal_includeLeft D L hsec).ne_top)

end BaseChange

/-- Two maps out of `D` and out of `L` agreeing on `κ` induce a map out of `D ⊗[κ] L`. -/
private lemma exists_tensorProduct_lift
    {D T L : Type*} [CommRing D] [CommRing T] [CommRing L] [IsLocalRing D]
    (b : D →+* T) (σ : ResidueField D →+* D) [Algebra (ResidueField D) L] (τ : L →+* T)
    (hτ : τ.comp (algebraMap (ResidueField D) L) = b.comp σ) :
    letI := σ.toAlgebra
    ∃ f : (D ⊗[ResidueField D] L) →+* T,
      f.comp (Algebra.TensorProduct.includeLeftRingHom :
        D →+* TensorProduct (ResidueField D) D L) = b ∧
      ∀ z : L, f ((1 : D) ⊗ₜ[ResidueField D] z) = τ z := by
  let F := ResidueField D
  let : Algebra F D := σ.toAlgebra
  let : Algebra D T := b.toAlgebra
  let : Algebra F T := (b.comp σ).toAlgebra
  let : IsScalarTower F D T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let τAlg : L →ₐ[F] T :=
    { toRingHom := τ
      commutes' := fun x => congrArg (fun h : F →+* T => h x) hτ }
  let f : (D ⊗[F] L) →ₐ[D] T :=
    Algebra.TensorProduct.lift (Algebra.ofId D T) τAlg (fun _ _ => Commute.all _ _)
  refine ⟨f.toRingHom, ?_, ?_⟩
  · ext x
    change f (x ⊗ₜ[F] (1 : L)) = b x
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  · intro z
    change f ((1 : D) ⊗ₜ[F] z) = τ z
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

/-! ### Essential smoothness of a base change -/

/-- Over a Noetherian base, essential finite type upgrades to essential finite presentation. -/
lemma isEssentiallyOfFinitePresentation_of_essFiniteType
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.EssFiniteType R S] : IsEssentiallyOfFinitePresentation R S (algebraMap R S) := by
  unfold IsEssentiallyOfFinitePresentation
  rw [toAlgebra_algebraMap]
  refine ⟨Algebra.EssFiniteType.subalgebra R S, inferInstance, inferInstance, ?_,
    Algebra.EssFiniteType.submonoid R S, inferInstance,
    IsScalarTower.of_algebraMap_eq (fun _ => rfl), inferInstance⟩
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- Base change of an essentially smooth map of `F`-algebras along `F → D`, for `D` Noetherian:
`D → D ⊗[F] L` is essentially of finite presentation and formally smooth. -/
@[ega "0 19.3.5" "(iii), second conjunct"]
private lemma isEssentiallyOfFinitePresentation_and_formallySmooth_tensorProduct
    (F D L : Type u) [CommRing F] [CommRing D] [CommRing L] [Algebra F D] [Algebra F L]
    [IsNoetherianRing D] [Algebra.EssFiniteType F L] [Algebra.FormallySmooth F L] :
    IsEssentiallyOfFinitePresentation D (D ⊗[F] L)
      (Algebra.TensorProduct.includeLeftRingHom : D →+* D ⊗[F] L) ∧
    Algebra.FormallySmooth D (D ⊗[F] L) := by
  have : Algebra.EssFiniteType D (D ⊗[F] L) := Algebra.EssFiniteType.baseChange F L D
  have hfp := isEssentiallyOfFinitePresentation_of_essFiniteType (R := D) (S := D ⊗[F] L)
  have hfs : RingHom.FormallySmooth (algebraMap F L) :=
    RingHom.formallySmooth_algebraMap.mpr inferInstance
  have hbc : RingHom.FormallySmooth (algebraMap D (D ⊗[F] L)) :=
    RingHom.IsStableUnderBaseChange.tensorProduct
      RingHom.FormallySmooth.isStableUnderBaseChange D hfs
  exact ⟨hfp, RingHom.formallySmooth_algebraMap.mp hbc⟩

/-! ### Lifting a formally smooth residue field extension to the ring -/

/-- Let `T` be Artinian local with residue field `K`, let `σ` be a section of the residue map of
`D` and let `L/κ` be formally smooth. A `κ`-map `L → K` compatible with `D → T → K` lifts to a
`κ`-map `L → T`: the residue map `T → K` is surjective with nilpotent kernel. -/
private lemma exists_formallySmooth_lift_to_artinian
    {D T L : Type*} [CommRing D] [IsLocalRing D] [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    [CommRing L] (b : D →+* T) (σ : ResidueField D →+* D) [Algebra (ResidueField D) L]
    [Algebra.FormallySmooth (ResidueField D) L] (ι : L →+* ResidueField T)
    (hι : ι.comp (algebraMap (ResidueField D) L) = (residue T).comp (b.comp σ)) :
    ∃ τ : L →+* T,
      τ.comp (algebraMap (ResidueField D) L) = b.comp σ ∧ (residue T).comp τ = ι := by
  let F := ResidueField D
  let K := ResidueField T
  let : Algebra F T := (b.comp σ).toAlgebra
  let : Algebra F K := ((residue T).comp (b.comp σ)).toAlgebra
  let ιAlg : L →ₐ[F] K :=
    { toRingHom := ι
      commutes' := fun x => congrArg (fun h : F →+* K => h x) hι }
  let g : T →ₐ[F] K :=
    { toRingHom := residue T
      commutes' := fun _ => rfl }
  have hnil : IsNilpotent (RingHom.ker g) := by
    change IsNilpotent (RingHom.ker (residue T))
    rw [IsLocalRing.ker_residue]
    exact (isArtinianRing_iff_isNilpotent_maximalIdeal T).mp inferInstance
  let τAlg := Algebra.FormallySmooth.liftOfSurjective ιAlg g residue_surjective hnil
  refine ⟨τAlg.toRingHom, ?_, ?_⟩
  · ext x
    exact τAlg.commutes x
  · exact congrArg AlgHom.toRingHom
      (Algebra.FormallySmooth.comp_liftOfSurjective ιAlg g residue_surjective hnil)

/-! ### Essentially smooth subextensions generated by a power of an element -/

/-- A simple transcendental extension is essentially of finite type and formally smooth. -/
private lemma essFiniteType_and_formallySmooth_adjoin_of_transcendental
    (F K : Type*) [Field F] [Field K] [Algebra F K] {x : K} (hx : Transcendental F x) :
    Algebra.EssFiniteType F ↥F⟮x⟯ ∧ Algebra.FormallySmooth F ↥F⟮x⟯ := by
  refine ⟨IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)), ?_⟩
  have hi : AlgebraicIndependent F (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hfs := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hi
  rwa [Set.range_const] at hfs

/-- A simple separable algebraic extension is essentially of finite type and formally smooth,
being formally étale. -/
private lemma essFiniteType_and_formallySmooth_adjoin_of_isSeparable
    (F K : Type*) [Field F] [Field K] [Algebra F K] {x : K} (hx : IsSeparable F x) :
    Algebra.EssFiniteType F ↥F⟮x⟯ ∧ Algebra.FormallySmooth F ↥F⟮x⟯ := by
  refine ⟨IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)), ?_⟩
  let : Algebra.IsSeparable F ↥F⟮x⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F K).mpr hx
  let : Algebra.FormallyEtale F ↥F⟮x⟯ := Algebra.FormallyEtale.of_isSeparable F ↥F⟮x⟯
  infer_instance

/-- Over a field of characteristic `p`, a positive power of an algebraic element is separable:
the element is purely inseparable over the separable closure of `F` in `F(x)`. -/
private lemma exists_pow_isSeparable_of_isAlgebraic
    (F K : Type*) [Field F] [Field K] [Algebra F K] (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    {x : K} (hx : IsAlgebraic F x) : ∃ e : ℕ, 0 < e ∧ IsSeparable F (x ^ e) := by
  let S := F⟮x⟯
  let xs : S := ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩
  have : Algebra.IsAlgebraic F S := IntermediateField.isAlgebraic_adjoin_simple hx.isIntegral
  let Sep := separableClosure F S
  have : IsPurelyInseparable Sep S := inferInstance
  let : ExpChar Sep p := ExpChar.of_injective_algebraMap' F p
  obtain ⟨m, z, hz⟩ := IsPurelyInseparable.pow_mem Sep p xs
  refine ⟨p ^ m, pow_pos (Nat.Prime.pos Fact.out) _, ?_⟩
  have hzsep : IsSeparable F z := Algebra.IsSeparable.isSeparable F z
  have hzS : IsSeparable F ((algebraMap Sep S) z) :=
    hzsep.map (IsScalarTower.toAlgHom F Sep S) (FaithfulSMul.algebraMap_injective Sep S)
  have hzK : IsSeparable F ((IntermediateField.val S) ((algebraMap Sep S) z)) :=
    hzS.map (IntermediateField.val S) Subtype.val_injective
  simpa [xs, hz] using hzK

/-- Over a field `F` of characteristic `p`, every `x ∈ K` has a positive power lying in an
intermediate field which is essentially of finite type and formally smooth over `F`. -/
private lemma exists_essFiniteType_formallySmooth_intermediateField_pow_mem
    (F K : Type*) [Field F] [Field K] [Algebra F K] (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (x : K) :
    ∃ (e : ℕ) (_ : 0 < e) (L : IntermediateField F K),
      Algebra.EssFiniteType F L ∧ Algebra.FormallySmooth F L ∧ x ^ e ∈ L := by
  by_cases hx : IsAlgebraic F x
  · obtain ⟨e, he, hsep⟩ := exists_pow_isSeparable_of_isAlgebraic F K p hx
    obtain ⟨hess, hfs⟩ := essFiniteType_and_formallySmooth_adjoin_of_isSeparable F K hsep
    exact ⟨e, he, F⟮x ^ e⟯, hess, hfs, IntermediateField.mem_adjoin_simple_self F (x ^ e)⟩
  · obtain ⟨hess, hfs⟩ :=
      essFiniteType_and_formallySmooth_adjoin_of_transcendental F K (hx : Transcendental F x)
    exact ⟨1, Nat.one_pos, F⟮x⟯, hess, hfs, by
      simpa using IntermediateField.mem_adjoin_simple_self F x⟩

/-! ### The enlargement -/

/-- A flat local homomorphism is injective, being faithfully flat. -/
private lemma injective_of_flat_of_isLocalHom
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : RingHom.Flat f) : Function.Injective f := by
  let := f.toAlgebra
  have : Module.Flat R S := hf
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance).injective

/-- The base change `D ⊗[κ] L` of a flat local map `b : D → T` along a formally smooth, essentially
finite type residue field extension `L/κ`, with a `κ`-map `τ : L → T`, is an essentially smooth
enlargement of `D` through which `b` factors by a flat local map, and `τ` factors through it. -/
private lemma exists_tensorProduct_enlargement
    {D T : Type u} [CommRing D] [CommRing T] [IsLocalRing D] [IsArtinianRing D]
    [IsLocalRing T] [IsArtinianRing T] (b : D →+* T) [IsLocalHom b] (hb : RingHom.Flat b)
    (σ : ResidueField D →+* D) (hσ : (residue D).comp σ = RingHom.id _)
    (L : Type u) [Field L] [Algebra (ResidueField D) L]
    [Algebra.EssFiniteType (ResidueField D) L] [Algebra.FormallySmooth (ResidueField D) L]
    (τ : L →+* T) (hτ : τ.comp (algebraMap (ResidueField D) L) = b.comp σ) :
    ∃ (U : Type u) (_ : CommRing U) (_ : IsLocalRing U) (_ : IsArtinianRing U)
      (c : D →+* U) (bU : U →+* T) (_ : IsLocalHom c) (_ : IsLocalHom bU) (τ' : L →+* U),
      RingHom.IsEssentiallySmooth c ∧ RingHom.Flat bU ∧ bU.comp c = b ∧
        ∀ z : L, bU (τ' z) = τ z := by
  let : Algebra (ResidueField D) D := σ.toAlgebra
  let U := D ⊗[ResidueField D] L
  let : IsLocalRing U := isLocalRing_tensorProduct_right D L hσ
  let : IsArtinianRing U := isArtinianRing_tensorProduct_right D L hσ
  let c : D →+* U := Algebra.TensorProduct.includeLeftRingHom
  obtain ⟨bU, hbc, hbUz⟩ := exists_tensorProduct_lift b σ τ hτ
  let : IsLocalHom c := isLocalHom_includeLeft_tensorProduct_right D L hσ
  have hmax : ((maximalIdeal D).map c).IsMaximal := isMaximal_map_maximalIdeal_includeLeft D L hσ
  have hm : (maximalIdeal D).map c = maximalIdeal U := IsLocalRing.eq_maximalIdeal hmax
  let : IsLocalHom (bU.comp c) := hbc ▸ ‹IsLocalHom b›
  let : IsLocalHom bU := (IsLocalRing.local_hom_TFAE bU).out 3 1 |>.mp <| by
    rw [← hm, Ideal.map_map]
    exact IsLocalRing.map_maximalIdeal_le (bU.comp c)
  have hcsmooth : RingHom.IsEssentiallySmooth c := by
    let := c.toAlgebra
    change IsEssentiallyOfFinitePresentation D U c ∧ Algebra.FormallySmooth D U
    have hs := isEssentiallyOfFinitePresentation_and_formallySmooth_tensorProduct
      (ResidueField D) D L
    refine ⟨hs.1, ?_⟩
    have hca : c.toAlgebra = (Algebra.TensorProduct.leftAlgebra : Algebra D U) := by
      let : Algebra D U := Algebra.TensorProduct.leftAlgebra
      change (algebraMap D U).toAlgebra = _
      exact toAlgebra_algebraMap (R := D) (S := U)
    exact (congrArg (fun a : Algebra D U => @Algebra.FormallySmooth D U _ _ a) hca.symm).mp hs.2
  let := hmax
  exact ⟨U, inferInstance, inferInstance, inferInstance, c, bU, inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight : L →ₐ[ResidueField D] U).toRingHom, hcsmooth,
    flat_of_flat_comp_of_isMaximal_map_maximalIdeal c bU (hbc ▸ hb), hbc, hbUz⟩

/-- The construction step: given a formally smooth, essentially finite type extension `L` of the
residue field of `D`, a section `σ` of the residue map of `D`, a lift `τ : L → T` of the
inclusion compatible with `σ`, and an element `z ∈ L` whose image in `T` has the same residue as
`y ^ e`, the ring `D ⊗[κ] L` enlarges `D` as required. -/
private lemma exists_enlargement_of_residue_lift
    {D T : Type u} [CommRing D] [CommRing T] [IsLocalRing D] [IsArtinianRing D]
    [IsLocalRing T] [IsArtinianRing T] (b : D →+* T) [IsLocalHom b] (hbflat : RingHom.Flat b)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP T p]
    (σ : ResidueField D →+* D) (hσ : (residue D).comp σ = RingHom.id _)
    (L : Type u) [Field L] [Algebra (ResidueField D) L]
    [Algebra.EssFiniteType (ResidueField D) L] [Algebra.FormallySmooth (ResidueField D) L]
    (τ : L →+* T) (hτ : τ.comp (algebraMap (ResidueField D) L) = b.comp σ)
    (y : T) (e : ℕ) (he : 0 < e) (z : L)
    (hres : residue T (τ z) = residue T (y ^ e)) :
    ∃ (d : ℕ) (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
      (c : D →+* D') (b' : D' →+* T) (_ : IsLocalHom c) (_ : IsLocalHom b'),
      0 < d ∧ RingHom.IsEssentiallySmooth c ∧ RingHom.Flat b' ∧ b'.comp c = b ∧
        ∃ w : D', b' w = y ^ d := by
  obtain ⟨U, _, _, _, c, bU, _, _, τ', hc, hbU, hbc, hτ'⟩ :=
    exists_tensorProduct_enlargement b hbflat σ hσ L τ hτ
  have hmem : y ^ e - bU (τ' z) ∈ maximalIdeal T := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hτ', ← hres, sub_self]
  obtain ⟨e', he', w, hw⟩ := exists_pow_mem_range_of_sub_mem_maximalIdeal bU p (τ' z) (y ^ e) hmem
  exact ⟨e * e', U, inferInstance, inferInstance, inferInstance, c, bU, inferInstance,
    inferInstance, Nat.mul_pos he he', hc, hbU, hbc, w, by simpa only [pow_mul] using hw⟩

/-- **The ring-theoretic content of Stacks 07FI.** Let `D → T` be a flat local homomorphism of
Artinian local rings of characteristic a prime `p`, and let `y ∈ T`. Then it factors as
`D → D' → T` with `D'` Artinian local, `D → D'` essentially smooth and local, `D' → T` flat and
local, and some positive power of `y` in the image of `D'`. -/
theorem exists_essentiallySmooth_artinianLocal_enlargement
    {D T : Type u} [CommRing D] [CommRing T] [IsLocalRing D] [IsArtinianRing D]
    [IsLocalRing T] [IsArtinianRing T] (p : ℕ) [Fact (Nat.Prime p)] [CharP T p]
    (b : D →+* T) [IsLocalHom b] (hb : RingHom.Flat b) (y : T) :
    ∃ (e : ℕ) (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
      (c : D →+* D') (b' : D' →+* T) (_ : IsLocalHom c) (_ : IsLocalHom b'),
      0 < e ∧ RingHom.IsEssentiallySmooth c ∧ RingHom.Flat b' ∧ b'.comp c = b ∧
        ∃ w : D', b' w = y ^ e := by
  -- `b` is faithfully flat, being flat and local, hence injective.
  have hbinj : Function.Injective b := injective_of_flat_of_isLocalHom b hb
  let : CharP D p := b.charP hbinj p
  have hnil : IsNilpotent (maximalIdeal D) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal D).mp inferInstance
  obtain ⟨σ, hσ, -⟩ := IsLocalRing.exists_residueField_section_compatible.{u, u} D hnil
  let R := ResidueField D
  let K := ResidueField T
  let : CharP R p := σ.charP σ.injective p
  let : Algebra R K := (ResidueField.map b).toAlgebra
  obtain ⟨e, he, L, hess, hfs, hmem⟩ :=
    exists_essFiniteType_formallySmooth_intermediateField_pow_mem R K p (residue T y)
  let : Algebra.EssFiniteType R L := hess
  let : Algebra.FormallySmooth R L := hfs
  have hι : (IntermediateField.val L).toRingHom.comp (algebraMap R L) =
      (residue T).comp (b.comp σ) := by
    ext x
    have hs := congrArg (fun f : R →+* R => f x) hσ
    change residue D (σ x) = x at hs
    change (IntermediateField.val L) (algebraMap R L x) = residue T (b (σ x))
    rw [(IntermediateField.val L).commutes]
    change ResidueField.map b x = residue T (b (σ x))
    conv_lhs => rw [← hs]
    exact IsLocalRing.ResidueField.map_residue b (σ x)
  obtain ⟨τ, hτ, hτres⟩ :=
    exists_formallySmooth_lift_to_artinian b σ (IntermediateField.val L).toRingHom hι
  have hzres : residue T (τ ⟨residue T y ^ e, hmem⟩) = residue T (y ^ e) := by
    have hz := congrArg (fun f : L →+* K => f ⟨residue T y ^ e, hmem⟩) hτres
    change residue T (τ ⟨residue T y ^ e, hmem⟩) = (IntermediateField.val L) _ at hz
    rw [hz, map_pow]
    rfl
  exact exists_enlargement_of_residue_lift b hb p σ hσ L τ hτ y e he _ hzres

/-! ### The enlargement with a prescribed residue field, with no power-taking -/

/-- **The coefficient-field enlargement.** Let `b : D → T` be a flat local homomorphism of
Artinian local rings, let `σ` be a ring-theoretic section of the residue map of `D`, and let `L`
be a `κ(D)`-algebra which is a field, essentially of finite type and **formally smooth** over
`κ(D)`, together with a `κ(D)`-embedding `ι : L → κ(T)` compatible with `σ`. Then `b` factors as
`D → D' → T` with `D'` Artinian local, `D → D'` essentially smooth and local, `D' → T` flat,
local and injective, and `D'` carrying a ring map `τ : L → D'` which realizes `ι` on residues:
`residue T (b' (τ z)) = ι z` for every `z ∈ L`.

This differs from `Stacks.Smoothing.exists_essentiallySmooth_artinianLocal_enlargement` in two
ways, and both matter for Stacks 07FT. There no residue field is prescribed: `L` is manufactured
inside `κ(T)` from the residue of a single element `y ∈ T`, and because that residue may be
inseparable algebraic over `κ(D)` only a `p`-power of it generates a formally smooth
subextension — whence the exponent `e` in the conclusion `y ^ e ∈ range b'`, and whence a second
`p`-power, absorbed into the same `e`, used to turn an equality of residues into an equality in
`T`. Here `L` and the embedding are inputs, so no power is taken anywhere and no characteristic
hypothesis is needed: the conclusion is exactly that the residue field of `D'` is `ι(L)`.

The hypotheses added relative to that theorem are `σ`, `hσ` (a section of the residue map of `D`,
there produced from `CharP D p` by Lemma 09EZ), and the data `L`, `ι`, `hι` of the prescribed
residue field extension; the hypotheses `Fact (Nat.Prime p)` and `CharP T p` are dropped.

What this does **not** give is `y ∈ range b'` for an element `y ∈ T` whose residue lies in
`ι(L)`: it gives only `y - b' w ∈ 𝔪_T` for some `w : D'`. Closing that gap is the remaining step
of Stacks 07FT; see `StacksFrontier.RingTheory.Smoothing.CoefficientFieldEnlargement`. -/
theorem exists_essentiallySmooth_enlargement_residueField
    {D T : Type u} [CommRing D] [CommRing T] [IsLocalRing D] [IsArtinianRing D]
    [IsLocalRing T] [IsArtinianRing T] (b : D →+* T) [IsLocalHom b] (hb : RingHom.Flat b)
    (σ : ResidueField D →+* D) (hσ : (residue D).comp σ = RingHom.id _)
    (L : Type u) [Field L] [Algebra (ResidueField D) L]
    [Algebra.EssFiniteType (ResidueField D) L] [Algebra.FormallySmooth (ResidueField D) L]
    (ι : L →+* ResidueField T)
    (hι : ι.comp (algebraMap (ResidueField D) L) = (residue T).comp (b.comp σ)) :
    ∃ (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
      (c : D →+* D') (b' : D' →+* T) (_ : IsLocalHom c) (_ : IsLocalHom b') (τ : L →+* D'),
      RingHom.IsEssentiallySmooth c ∧ RingHom.Flat b' ∧ b'.comp c = b ∧
        Function.Injective b' ∧ (∀ z : L, residue T (b' (τ z)) = ι z) := by
  let : Algebra (ResidueField D) D := σ.toAlgebra
  obtain ⟨τT, hτT, hτTres⟩ := exists_formallySmooth_lift_to_artinian b σ ι hι
  obtain ⟨U, _, _, _, c, bU, _, _, τ', hc, hbU, hbc, hτ'⟩ :=
    exists_tensorProduct_enlargement b hb σ hσ L τT hτT
  refine ⟨U, inferInstance, inferInstance, inferInstance, c, bU, inferInstance, inferInstance,
    τ', hc, hbU, hbc, injective_of_flat_of_isLocalHom bU hbU, fun z => ?_⟩
  rw [hτ' z]
  exact congrArg (fun f : L →+* ResidueField T => f z) hτTres

/-- **Stacks 07FI.** Let `k` be a field of characteristic `p > 0`, let `Λ` be a `k`-algebra, let
`𝔮 ⊆ Λ` be a prime and `n : ℕ`, and suppose `Λ_𝔮/𝔮ⁿΛ_𝔮` is Artinian local — as it is in the
situation of Lemma 07FH. Let `D` be an Artinian local ring with a flat local map
`b : D → Λ_𝔮/𝔮ⁿΛ_𝔮`, the right-hand half of the factorization produced by that lemma. Then for
every `λ ∈ Λ` there is an integer `e > 0` and a factorization `D → D' → Λ_𝔮/𝔮ⁿΛ_𝔮` of `b` such
that `D → D'` is an essentially smooth local map of Artinian local rings, `D' → Λ_𝔮/𝔮ⁿΛ_𝔮` is
flat and local, and `λ ^ e` is in the image of `D'`. Composing with the source's
`k[y₁,…,y_m]_𝔭/𝔭ⁿ → D` gives the displayed four-term factorization. -/
@[stacks 07FI "the setup `as in Lemma 07FH` carried as the part of that lemma's data the \
conclusion speaks about; the left-hand map is omitted, which strengthens the statement, and \
the source's `λ ∉ 𝔮` is not assumed — see the implementation notes"]
theorem exists_essentiallySmooth_enlargement_containing_pow
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (Λ : Type u) [CommRing Λ] [Algebra k Λ] (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ)
    [IsLocalRing (Localization.AtPrime 𝔮 ⧸
      Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))]
    [IsArtinianRing (Localization.AtPrime 𝔮 ⧸
      Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))]
    {D : Type u} [CommRing D] [IsLocalRing D] [IsArtinianRing D]
    (b : D →+* (Localization.AtPrime 𝔮 ⧸
      Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)))
    [IsLocalHom b] (hb : RingHom.Flat b) (lam : Λ) :
    ∃ (e : ℕ) (D' : Type u) (_ : CommRing D') (_ : IsLocalRing D') (_ : IsArtinianRing D')
      (c : D →+* D') (b' : D' →+* (Localization.AtPrime 𝔮 ⧸
        Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)))
      (_ : IsLocalHom c) (_ : IsLocalHom b'),
      0 < e ∧ RingHom.IsEssentiallySmooth c ∧ RingHom.Flat b' ∧ b'.comp c = b ∧
        ∃ w : D', b' w = algebraMap Λ (Localization.AtPrime 𝔮 ⧸
          Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)) (lam ^ e) := by
  let : Fact (Nat.Prime p) := ⟨CharP.char_prime_of_ne_zero k (Nat.ne_of_gt hp)⟩
  let : CharP (Localization.AtPrime 𝔮 ⧸
      Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)) p :=
    CharP.of_ringHom_of_ne_zero
      ((Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))).comp
        ((algebraMap Λ (Localization.AtPrime 𝔮)).comp (algebraMap k Λ))) p (Nat.ne_of_gt hp)
  obtain ⟨e, D', hcr, hlr, har, c, b', hcl, hbl, he, hc, hbf, hcomp, w, hw⟩ :=
    exists_essentiallySmooth_artinianLocal_enlargement p b hb
      (algebraMap Λ (Localization.AtPrime 𝔮 ⧸
        Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)) lam)
  exact ⟨e, D', hcr, hlr, har, c, b', hcl, hbl, he, hc, hbf, hcomp, w, by rw [hw, map_pow]⟩

end Stacks.Smoothing

end
