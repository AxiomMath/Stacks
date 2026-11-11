module

public import Mathlib
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.RingTheory.Ext.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hom and Ext against a flat tensor factor

Let `R` be a commutative ring. For a finitely presented `R`-module `M` and a flat `R`-module `L`
the canonical map `Hom_R(M, N) ⊗_R L → Hom_R(M, N ⊗_R L)` is bijective, and if `M` is only
`(-d)`-pseudo-coherent the analogous comparison
`Ext^i_R(M, N) ⊗_R L → Ext^i_R(M, N ⊗_R L)` is bijective in every degree `i < d`.

Taking the tensor factor to be a flat algebra `S` over `R` turns those comparisons into
statements about scalar extension: the canonical map
`Ext^i_R(M, N) ⊗_R S → Ext^i_S(S ⊗_R M, S ⊗_R N)` is bijective in degree zero for a finitely
presented source, below the pseudo-coherence cutoff in general, and in every degree for a
finite source over a Noetherian ring.

## Main definitions

* `StacksDraft.PseudoCoherence.tensorElementHom`: the map `L → Hom_R(N, N ⊗_R L)` sending `l`
  to `n ↦ n ⊗ l`.
* `StacksDraft.PseudoCoherence.canonicalExtTensorComparison`: the canonical comparison
  `Ext^i_R(M, N) ⊗_R L → Ext^i_R(M, N ⊗_R L)`, obtained from `tensorElementHom` by
  postcomposition.
* `StacksDraft.PseudoCoherence.homBaseChangeComparison`: the canonical Hom base-change map
  `Hom_R(M, N) ⊗_R S → Hom_S(S ⊗_R M, S ⊗_R N)`, with the scalar ring as the right tensor
  factor.
* `StacksDraft.PseudoCoherence.uliftExtLinearEquiv₀`: the identification of degree-zero Ext
  between canonical universe lifts with Hom between the original modules.

## Main results

* `StacksDraft.PseudoCoherence.canonicalExtTensorComparison_bijective`: the Hom comparison is
  bijective for a finitely presented source, and the Ext comparison is bijective below the
  pseudo-coherence cutoff, Stacks 087Q.
* `StacksDraft.PseudoCoherence.canonicalExtTensorComparison_bijective_of_noetherian`: the Ext
  comparison is bijective in every degree for a finite module over a Noetherian ring.
* `StacksDraft.PseudoCoherence.baseChange_ext_bijective_of_pseudoCoherent`: the canonical Ext
  base-change comparison along a flat algebra, its uniqueness, its degree-zero identification
  with the Hom base-change map, and its bijectivity ranges, Stacks 087R.

## Implementation notes

The canonical Ext--tensor map is constructed by postcomposing an Ext class with the morphism
`N → N ⊗_R L`, `n ↦ n ⊗ l`, and then using the universal property of the tensor product; in
degree zero this is the usual Hom--tensor map. The Hom assertion is proved directly from a finite
presentation by the five lemma, and the Ext assertion by induction along a finite free resolution
of the source, using the long exact sequence attached to the syzygy short exact sequence.

The ring and the modules are allowed independent universes. Ext is computed on the canonical
universe lifts of the modules into a common module category, which is what lets finite free
modules fit without a smallness hypothesis on the ring; when the ring is *not* small relative to
that universe, pseudo-coherence from a negative degree already forces the source to vanish, and
the assertions hold for that reason.

For the base-change statement the rings and the modules again lie in independent universes, and
Ext is computed on their canonical lifts into a common module category. The comparison is
pinned down by the equation `c ∘ β = a` together with its uniqueness clause, where `c` is flat
base change for Ext and `a` is the Ext--tensor comparison followed by `n ⊗ s ↦ s ⊗ n`. The
degree-zero instance of that square, expressed through `uliftExtLinearEquiv₀`, is the Hom
base-change map on the original modules.

The flat base change for Ext that supplies `c` is Stacks 087N,
`extendScalarsExtComparison_bijective` in `StacksFrontier.RingTheory.Ext.BaseChange`, used here with
both module categories in the universe `max uR uS v`.

## References

* [Stacks Project, Tag 087Q](https://stacks.math.columbia.edu/tag/087Q)
* [Stacks Project, Tag 087R](https://stacks.math.columbia.edu/tag/087R)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace StacksDraft.PseudoCoherence

section TensorFactor

universe u v w x

variable (R : Type u) [CommRing R]

/-! ### The canonical Ext--tensor comparison -/

section Comparison

variable [Small.{v} R]

/-- The map `K → Hom_R(Y, Y ⊗ K)` sending `k` to `y ↦ y ⊗ k`. -/
def tensorElementHom (Y K : ModuleCat.{v} R) :
    K →ₗ[R] (Y ⟶ ModuleCat.of R (Y ⊗[R] K)) :=
  ModuleCat.homLinearEquiv.symm.toLinearMap.comp (TensorProduct.mk R Y K).flip

/-- The canonical comparison `Extⁱ_R(X,Y) ⊗_R K → Extⁱ_R(X,Y ⊗_R K)`.
It is defined for every tensor factor. -/
noncomputable def canonicalExtTensorComparison (X Y K : ModuleCat.{v} R) (i : ℕ) :
    (Abelian.Ext X Y i) ⊗[R] K →ₗ[R]
      Abelian.Ext X (ModuleCat.of R (Y ⊗[R] K)) i :=
  let kToExt : K →ₗ[R] Abelian.Ext Y (ModuleCat.of R (Y ⊗[R] K)) 0 :=
    (Abelian.Ext.linearEquiv₀ (R := R)).symm.toLinearMap.comp (tensorElementHom R Y K)
  TensorProduct.lift
    (((Abelian.Ext.bilinearCompOfLinear R X Y (ModuleCat.of R (Y ⊗[R] K))
      i 0 i (add_zero i)).flip.comp kToExt).flip)

/-- On pure tensors, the comparison is postcomposition by `y ↦ y ⊗ k`. -/
theorem canonicalExtTensorComparison_tmul (X Y K : ModuleCat.{v} R)
    (i : ℕ) (e : Abelian.Ext X Y i) (k : K) :
    canonicalExtTensorComparison R X Y K i (e ⊗ₜ[R] k) =
      e.comp (Abelian.Ext.mk₀ (tensorElementHom R Y K k)) (add_zero i) := by
  rfl

end Comparison

/-! ### The Hom comparison for a finitely presented source

The five lemma applied to a finite presentation of the source, using flatness of the tensor
factor to keep the presentation exact after tensoring. -/

/-- Precomposition with an exact pair of maps whose second member is surjective is exact. -/
private theorem exact_lcomp
    {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
    Function.Exact (LinearMap.lcomp R D g) (LinearMap.lcomp R D f) := by
  intro k
  constructor
  · intro hk
    have hker : g.ker ≤ k.ker := by
      intro b hb
      obtain ⟨a, rfl⟩ := (h b).mp hb
      exact DFunLike.congr_fun hk a
    refine ⟨((g.ker.liftQ k hker).comp
      (g.quotKerEquivOfSurjective hg).symm.toLinearMap), ?_⟩
    ext b
    simp
  · rintro ⟨k, rfl⟩
    ext a
    change k (g (f a)) = 0
    rw [(h (f a)).mpr ⟨a, rfl⟩, map_zero]

/-- The Hom--tensor map is natural in the source. -/
private theorem rTensorHomToHomRTensor_lcomp
    {A B N L : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup N] [AddCommGroup L]
    [Module R A] [Module R B] [Module R N] [Module R L]
    (f : A →ₗ[R] B) :
    (LinearMap.lcomp R (N ⊗[R] L) f).comp
        (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) B N L) =
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) A N L).comp
        ((LinearMap.lcomp R N f).rTensor L) := by
  ext k l a
  rfl

/-- The Hom--tensor map is bijective for a finite projective source, with no flatness needed. -/
private theorem rTensorHomToHomRTensor_bijective_of_finite_projective
    (M N L : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M N L) := by
  have he : ⇑(rTensorHomEquivHomRTensor R M N L) =
      ⇑(TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M N L) :=
    funext rTensorHomEquivHomRTensor_apply
  rw [← he]
  exact (rTensorHomEquivHomRTensor R M N L).bijective

/-- The Hom--tensor map is bijective for a finitely presented source and a flat tensor factor. -/
private theorem rTensorHomToHomRTensor_bijective_of_finitePresentation
    (M : Type v) (N : Type w) (L : Type x)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup L] [Module R L] [Module.Flat R L]
    (hM : Module.FinitePresentation R M) :
    Function.Bijective
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M N L) := by
  let := hM
  obtain ⟨n, m, g, f, hg, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  apply LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((LinearMap.lcomp R N g).rTensor L) ((LinearMap.lcomp R N f).rTensor L)
    (LinearMap.lcomp R (N ⊗[R] L) g) (LinearMap.lcomp R (N ⊗[R] L) f)
    _ (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) (Fin n → R) N L)
    (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) (Fin m → R) N L)
    (rTensorHomToHomRTensor_lcomp R g) (rTensorHomToHomRTensor_lcomp R f)
    (Module.Flat.rTensor_exact L (exact_lcomp R f g hg hfg))
    (exact_lcomp R f g hg hfg)
  · exact rTensorHomToHomRTensor_bijective_of_finite_projective R _ _ _
  · exact (rTensorHomToHomRTensor_bijective_of_finite_projective R _ _ _).1
  · exact Module.Flat.rTensor_preserves_injective_linearMap _
      (LinearMap.lcomp_injective_of_surjective g hg)
  · exact LinearMap.lcomp_injective_of_surjective g hg

/-! ### The Ext comparison along a finite free resolution

Degree zero is the Hom comparison; the inductive step compares the two long exact sequences
attached to a syzygy short exact sequence, using flatness of the tensor factor to keep the
source sequence exact. -/

section Ext

variable [Small.{v} R]

/-- The degree-zero identification sends the class of a morphism to that morphism. -/
private theorem linearEquiv₀_mk₀ {X Y : ModuleCat.{v} R} (f : X ⟶ Y) :
    Abelian.Ext.linearEquiv₀ (R := R) (Abelian.Ext.mk₀ f) = f :=
  (Abelian.Ext.linearEquiv₀ (R := R)).apply_symm_apply f

/-- In degree zero the Ext comparison is the Hom--tensor map. -/
private theorem canonicalExtTensorComparison_zero_bijective
    (X Y K : ModuleCat.{v} R)
    (hX : Function.Bijective
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) X Y K)) :
    Function.Bijective (canonicalExtTensorComparison R X Y K 0) := by
  let e : Abelian.Ext X Y 0 ≃ₗ[R] (X →ₗ[R] Y) :=
    Abelian.Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv
  let e' : Abelian.Ext X (ModuleCat.of R (Y ⊗[R] K)) 0 ≃ₗ[R]
      (X →ₗ[R] Y ⊗[R] K) :=
    Abelian.Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv
  have h : e'.toLinearMap.comp (canonicalExtTensorComparison R X Y K 0) =
      (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) X Y K).comp
        (e.toLinearMap.rTensor K) := by
    ext a k x
    obtain ⟨f, rfl⟩ := (Abelian.Ext.linearEquiv₀ (R := R)).symm.surjective a
    simp [e, e', canonicalExtTensorComparison_tmul, Abelian.Ext.mk₀_comp_mk₀,
      tensorElementHom, linearEquiv₀_mk₀]
    rfl
  have hb : Function.Bijective (e'.toLinearMap.comp
      (canonicalExtTensorComparison R X Y K 0)) := by
    rw [h]
    exact hX.comp (e.rTensor K).bijective
  exact (e'.bijective.of_comp_iff' _).mp hb

/-- The Ext comparison is natural for precomposition by a class in the source. -/
private theorem canonicalExtTensorComparison_precomp
    {X X' Y K : ModuleCat.{v} R} {a b c : ℕ}
    (f : Abelian.Ext X X' a) (h : a + b = c) :
    (f.precompOfLinear R (ModuleCat.of R (Y ⊗[R] K)) h).comp
        (canonicalExtTensorComparison R X' Y K b) =
      (canonicalExtTensorComparison R X Y K c).comp
        ((f.precompOfLinear R Y h).rTensor K) := by
  refine TensorProduct.ext (LinearMap.ext fun e => LinearMap.ext fun k => ?_)
  change f.comp (canonicalExtTensorComparison R X' Y K b (e ⊗ₜ[R] k)) h =
    canonicalExtTensorComparison R X Y K c ((f.comp e h) ⊗ₜ[R] k)
  rw [canonicalExtTensorComparison_tmul, canonicalExtTensorComparison_tmul]
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero f e _ h).symm

/-- Two consecutive maps of the contravariant long exact sequence of a short exact sequence. -/
@[sga "4½ Etat_0 1.1.2" "special case"]
private theorem ext_precomp_extClass_exact
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (Y : ModuleCat.{v} R) (n : ℕ) :
    Function.Exact ((Abelian.Ext.mk₀ S.f).precompOfLinear R Y (zero_add n))
      (hS.extClass.precompOfLinear R Y (by omega : 1 + n = n + 1)) := by
  intro a
  constructor
  · exact Abelian.Ext.contravariant_sequence_exact₁ hS Y a (by omega)
  · rintro ⟨b, rfl⟩
    exact hS.extClass_comp_assoc (h := by omega) b

/-- Precomposition by the extension class is surjective when the middle term is projective. -/
private theorem ext_precomp_extClass_surjective
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    [Projective S.X₂] (Y : ModuleCat.{v} R) (n : ℕ) :
    Function.Surjective
      (hS.extClass.precompOfLinear R Y (by omega : 1 + n = n + 1)) := fun a =>
  Abelian.Ext.contravariant_sequence_exact₃ hS Y a (Abelian.Ext.eq_zero_of_projective _) (by omega)

/-- The inductive step: bijectivity in degree `n` for the sub- and middle terms of a short exact
sequence with projective middle term gives bijectivity in degree `n + 1` for the quotient. -/
private theorem canonicalExtTensorComparison_bijective_of_shortExact
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    [Projective S.X₂] (Y K : ModuleCat.{v} R) [Module.Flat R K]
    (n : ℕ)
    (h₁ : Function.Bijective (canonicalExtTensorComparison R S.X₁ Y K n))
    (h₂ : Function.Surjective (canonicalExtTensorComparison R S.X₂ Y K n)) :
    Function.Bijective (canonicalExtTensorComparison R S.X₃ Y K (n + 1)) := by
  apply LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (((Abelian.Ext.mk₀ S.f).precompOfLinear R Y (zero_add n)).rTensor K)
    ((hS.extClass.precompOfLinear R Y (by omega : 1 + n = n + 1)).rTensor K)
    ((Abelian.Ext.mk₀ S.f).precompOfLinear R
      (ModuleCat.of R (Y ⊗[R] K)) (zero_add n))
    (hS.extClass.precompOfLinear R (ModuleCat.of R (Y ⊗[R] K))
      (by omega : 1 + n = n + 1))
    (canonicalExtTensorComparison R S.X₂ Y K n)
    (canonicalExtTensorComparison R S.X₁ Y K n) _
    (canonicalExtTensorComparison_precomp R _ _) (canonicalExtTensorComparison_precomp R _ _)
    (Module.Flat.rTensor_exact K (ext_precomp_extClass_exact R hS Y n))
    (ext_precomp_extClass_exact R hS _ n) h₂ h₁
  · exact LinearMap.rTensor_surjective K (ext_precomp_extClass_surjective R hS Y n)
  · exact ext_precomp_extClass_surjective R hS _ n

/-- For a finite projective source the comparison is bijective in every degree: degree zero is
the Hom--tensor map and the higher Ext groups vanish on both sides. -/
private theorem canonicalExtTensorComparison_bijective_of_finite_projective
    (X Y K : ModuleCat.{v} R)
    [Module.Finite R X] [Module.Projective R X] (i : ℕ) :
    Function.Bijective (canonicalExtTensorComparison R X Y K i) := by
  cases i with
  | zero =>
      exact canonicalExtTensorComparison_zero_bijective R X Y K
        (rTensorHomToHomRTensor_bijective_of_finite_projective R X Y K)
  | succ i =>
    let := Abelian.Ext.subsingleton_of_projective X Y i
    let := Abelian.Ext.subsingleton_of_projective X (ModuleCat.of R (Y ⊗[R] K)) i
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- Bijectivity in degree `i` from a resolution whose terms through degree `i + 1` are finite
projective, by induction on `i` along the syzygies of the resolution. -/
private theorem canonicalExtTensorComparison_bijective_of_resolution
    (Y K : ModuleCat.{v} R) [Module.Flat R K] (i : ℕ)
    (X : ModuleCat.{v} R) (F : ℕ → ModuleCat.{v} R)
    (f : ∀ n, F (n + 1) →ₗ[R] F n) (ε : F 0 →ₗ[R] X)
    (hε : Function.Surjective ε) (h₀ : Function.Exact (f 0) ε)
    (hf : ∀ n, Function.Exact (f (n + 1)) (f n))
    (hF : ∀ n ≤ i + 1, Module.Finite R (F n) ∧ Module.Projective R (F n)) :
    Function.Bijective (canonicalExtTensorComparison R X Y K i) := by
  induction i generalizing X F with
  | zero =>
    obtain ⟨_, _⟩ := hF 0 (by omega)
    let := (hF 1 (by omega)).1
    let := Module.finitePresentation_of_projective R (F 0)
    apply canonicalExtTensorComparison_zero_bijective R X Y K
    apply rTensorHomToHomRTensor_bijective_of_finitePresentation R X Y K
    apply Module.finitePresentation_of_surjective ε hε
    rw [h₀.linearMap_ker_eq]
    exact Submodule.fg_range (f 0)
  | succ i ih =>
    obtain ⟨_, _⟩ := hF 0 (by omega)
    let ε' : F 1 →ₗ[R] ε.ker := (f 0).codRestrict ε.ker
      (fun x => (h₀ _).mpr ⟨x, rfl⟩)
    have hε' : Function.Surjective ε' := by
      intro x
      obtain ⟨a, ha⟩ := (h₀ x).mp x.property
      exact ⟨a, Subtype.ext ha⟩
    have h₀' : Function.Exact (f 1) ε' := by
      intro x
      rw [Subtype.ext_iff]
      exact hf 0 x
    have hK := ih (ModuleCat.of R ε.ker) (fun n => F (n + 1))
      (fun n => f (n + 1)) ε' hε' h₀' (fun n => hf (n + 1))
      (fun n hn => hF (n + 1) (by omega))
    exact canonicalExtTensorComparison_bijective_of_shortExact R
      (LinearMap.shortExact_shortComplexKer hε) Y K i hK
      (canonicalExtTensorComparison_bijective_of_finite_projective R (F 0) Y K i).2

/-- Over a Noetherian ring the comparison is bijective in every degree for a finite source:
degree zero is the Hom comparison for the finitely presented source, and the inductive step runs
along a finite free cover, whose kernel is again finite. -/
private theorem canonicalExtTensorComparison_bijective_of_isNoetherianRing [IsNoetherianRing R]
    (X Y K : ModuleCat.{v} R) [Module.Finite R X] [Module.Flat R K] (i : ℕ) :
    Function.Bijective (canonicalExtTensorComparison R X Y K i) := by
  induction i generalizing X with
  | zero =>
    exact canonicalExtTensorComparison_zero_bijective R X Y K
      (rTensorHomToHomRTensor_bijective_of_finitePresentation R X Y K
        (Module.finitePresentation_of_finite R X))
  | succ i ih =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R X
    exact canonicalExtTensorComparison_bijective_of_shortExact R
      (LinearMap.shortExact_shortComplexKer hf) Y K i (ih _)
      (canonicalExtTensorComparison_bijective_of_finite_projective R (ModuleCat.of R P) Y K i).2

end Ext

/-! ### Stacks 087Q -/

/-- A resolution of a module is exact in the form needed by the inductive comparison. -/
private theorem moduleResolution_exact
    {M : Type v} [AddCommGroup M] [Module R M] (P : ModuleResolution R M) :
    Function.Surjective (P.π.f 0).hom ∧
    Function.Exact (P.complex.d 1 0).hom (P.π.f 0).hom ∧
    ∀ n, Function.Exact (P.complex.d (n + 2) (n + 1)).hom
      (P.complex.d (n + 1) n).hom := by
  let := P.quasiIso
  have hq := (ChainComplex.quasiIsoAt₀_iff P.π).mp (inferInstance : QuasiIsoAt P.π 0)
  have h := (ShortComplex.quasiIso_iff_of_zeros'
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R) (.down ℕ) 1 0 0).map P.π)
    (by exact P.complex.shape 0 0 (by simp))
    (HomologicalComplex.single_obj_d (.down ℕ) 0 (ModuleCat.of R M) 1 0)
    (HomologicalComplex.single_obj_d (.down ℕ) 0 (ModuleCat.of R M) 0 0)).mp hq
  refine ⟨(ModuleCat.epi_iff_surjective _).mp h.2,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.1, ?_⟩
  intro n
  have he : P.complex.ExactAt (n + 1) := by
    rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (ChainComplex.exactAt_succ_single_obj _ _)]
    infer_instance
  have he' := ((HomologicalComplex.exactAt_iff' P.complex (n + 2) (n + 1) n)
    (by simp only [ChainComplex.prev]; rfl) (by simp)).mp he
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he'

/-- A module that is pseudo-coherent from a negative degree either lives over a ring small
relative to its own universe, or vanishes. -/
private theorem small_or_subsingleton_of_isModulePseudoCoherentFrom
    [HasDerivedCategory (ModuleCat.{v} R)]
    (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) (hd : 0 < d)
    (hM : IsModulePseudoCoherentFrom (R := R) M (-(d : ℤ))) :
    Small.{v} R ∨ Subsingleton M := by
  classical
  obtain ⟨E, hE, α, hα, _⟩ := hM
  by_cases h : ∀ j, Subsingleton (E.X j)
  · right
    have hE₀ : CategoryTheory.Limits.IsZero (E.homology 0) :=
      (HomologicalComplex.ExactAt.of_isZero
        (ModuleCat.isZero_iff_subsingleton.mpr (h 0))).isZero_homology
    have hz : CategoryTheory.Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
          (DerivedCategory.Q.obj E)) :=
      hE₀.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) 0).app E)
    let := hα 0 (by omega)
    exact ModuleCat.subsingleton_of_isZero
      ((CategoryTheory.Limits.IsZero.of_epi
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map α) hz).of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) 0).app
            (ModuleCat.of R M)).symm)
  · left
    push Not at h
    obtain ⟨j, hj⟩ := h
    let : Nontrivial (E.X j) := hj
    let := (hE.finiteFree j).2
    exact small_of_injective (f := fun r : R => fun x : E.X j => r • x)
      (fun _ _ h => eq_of_smul_eq_smul (fun x => congrFun h x))

/-- Exactness of a pair of morphisms of modules is preserved by the universe lift functor. -/
private theorem exact_ulift
    {A B C : ModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Exact f.hom g.hom) :
    Function.Exact ((ModuleCat.uliftFunctor.{w} R).map f).hom
      ((ModuleCat.uliftFunctor.{w} R).map g).hom := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (h x.down).mp (congrArg ULift.down hx)
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  · rintro ⟨y, rfl⟩
    exact congrArg ULift.up ((h (f y.down)).mpr ⟨y.down, rfl⟩)

/-- **Stacks 087Q.** The canonical Hom--tensor map is bijective for a finitely presented
source and flat tensor factor. The canonical Ext--tensor map is bijective below the
pseudo-coherence cutoff for a flat tensor factor. -/
@[stacks 087Q,
  ega "0 6.2.2",
  sga "4 V 8.2.10" "modules over a ring",
  sga "6 I 3.7" "affine case, modules"]
theorem canonicalExtTensorComparison_bijective [HasDerivedCategory (ModuleCat.{v} R)] :
    ∀ (M : Type v) (N : Type w) (L : Type x)
        [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
        [AddCommGroup L] [Module R L] [Module.Flat R L],
        (Module.FinitePresentation R M →
          Function.Bijective
            (TensorProduct.rTensorHomToHomRTensor (RingHom.id R) M N L)) ∧
        (∀ (d : ℕ), IsModulePseudoCoherentFrom (R := R) M (-(d : ℤ)) →
          ∀ i < d, Function.Bijective
            (canonicalExtTensorComparison R (ModuleCat.of R (ULift.{max u v w x} M))
              (ModuleCat.of R (ULift.{max u v w x} N))
              (ModuleCat.of R (ULift.{max u v w x} L)) i)) := by
  intro M N L _ _ _ _ _ _ _
  refine ⟨rTensorHomToHomRTensor_bijective_of_finitePresentation R M N L, ?_⟩
  intro d hM i hi
  let X := ModuleCat.of R (ULift.{max u v w x} M)
  let Y := ModuleCat.of R (ULift.{max u v w x} N)
  let K := ModuleCat.of R (ULift.{max u v w x} L)
  let : Module.Flat R K := Module.Flat.of_linearEquiv (ULift.moduleEquiv : K ≃ₗ[R] L)
  rcases small_or_subsingleton_of_isModulePseudoCoherentFrom R M d (by omega) hM with hR | hZ
  · let := hR
    obtain ⟨P, hP⟩ :=
      ((modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
        (R := R) M).2.2.1 d).mp hM
    obtain ⟨hε, h₀, hf⟩ := moduleResolution_exact R P
    let U := ModuleCat.uliftFunctor.{max u v w x, v} R
    apply canonicalExtTensorComparison_bijective_of_resolution R Y K i X
      (fun n => U.obj (P.complex.X n))
      (fun n => (U.map (P.complex.d (n + 1) n)).hom) (U.map (P.π.f 0)).hom
    · intro x
      obtain ⟨a, ha⟩ := hε x.down
      exact ⟨ULift.up a, congrArg ULift.up ha⟩
    · exact exact_ulift R _ _ h₀
    · exact fun n => exact_ulift R _ _ (hf n)
    · intro n hn
      obtain ⟨_, _⟩ := hP n (by omega)
      exact ⟨Module.Finite.equiv (ULift.moduleEquiv.symm :
        P.complex.X n ≃ₗ[R] ULift.{max u v w x} (P.complex.X n)), inferInstance⟩
  · let := hZ
    exact canonicalExtTensorComparison_bijective_of_finite_projective R X Y K i

end TensorFactor

/-! ## Flat base change for Hom and Ext

For a flat algebra `S` over `R`, scalar extension commutes with Hom from a finitely presented
module and with Ext below the cutoff prescribed by pseudo-coherence; over a Noetherian ring it
commutes with Ext from a finite module in every degree. -/

section BaseChange

open CategoryTheory.Abelian

/-! ### Stacks 087R -/

universe uR uS uM uN w

/-- The canonical map `Hom_R(M, N) ⊗_R S → Hom_S(S ⊗_R M, S ⊗_R N)`, sending
`f ⊗ s` to `s` times the scalar extension of `f`. -/
noncomputable def homBaseChangeComparison
    (R : Type uR) (S : Type uS) (M : Type uM) (N : Type uN)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] :
    ((M →ₗ[R] N) ⊗[R] S) →ₗ[R] ((S ⊗[R] M) →ₗ[S] (S ⊗[R] N)) :=
  ((LinearMap.baseChangeHom R S M N).liftBaseChange S).restrictScalars R |>.comp
    (TensorProduct.comm R _ _).toLinearMap

/-- On pure tensors the Hom comparison sends `f ⊗ s` to `a ⊗ m ↦ as ⊗ f(m)`. -/
@[simp] theorem homBaseChangeComparison_tmul_apply
    (R : Type uR) (S : Type uS) (M : Type uM) (N : Type uN)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (s a : S) (m : M) :
    homBaseChangeComparison R S M N (f ⊗ₜ[R] s) (a ⊗ₜ[R] m) =
      (a * s) ⊗ₜ[R] f m := by
  simp [homBaseChangeComparison, TensorProduct.smul_tmul', mul_comm]

/-- Degree-zero Ext between canonical universe lifts is linearly equivalent to Hom between the
original modules, by transporting `Ext.linearEquiv₀` along `ULift.moduleEquiv`. -/
noncomputable def uliftExtLinearEquiv₀
    (R : Type uR) (M : Type uM) (N : Type uN)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Ext (ModuleCat.of R (ULift.{max uR uM uN w} M))
      (ModuleCat.of R (ULift.{max uR uM uN w} N)) 0 ≃ₗ[R] (M →ₗ[R] N) :=
  Ext.linearEquiv₀.trans (ModuleCat.homLinearEquiv.trans
    (LinearEquiv.arrowCongr ULift.moduleEquiv ULift.moduleEquiv))

/-- The degree-zero identification sends the class of a morphism to its underlying map on the
original modules. -/
@[simp] theorem uliftExtLinearEquiv₀_mk₀_apply
    (R : Type uR) (M : Type uM) (N : Type uN)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : ModuleCat.of R (ULift.{max uR uM uN w} M) ⟶
      ModuleCat.of R (ULift.{max uR uM uN w} N)) (m : M) :
    uliftExtLinearEquiv₀.{uR, uM, uN, w} R M N (Ext.mk₀ f) m = (f (ULift.up m)).down := by
  change ((Ext.linearEquiv₀ (R := R) (Ext.mk₀ f)) (ULift.up m)).down = _
  rw [linearEquiv₀_mk₀]

section Proof

universe v u

/-- Precomposition by an isomorphism is bijective on Ext groups. -/
private theorem precomp_iso_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]
    {X X' : C} (e : X ≅ X') (Y : C) (i : ℕ) :
    Function.Bijective ((Ext.mk₀ e.hom).precomp Y (zero_add i)) := by
  have h₁ : Function.LeftInverse ((Ext.mk₀ e.inv).precomp Y (zero_add i))
      ((Ext.mk₀ e.hom).precomp Y (zero_add i)) := by
    intro x
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add i)) (zero_add i) = x
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id,
      Ext.mk₀_id_comp]
  have h₂ : Function.RightInverse ((Ext.mk₀ e.inv).precomp Y (zero_add i))
      ((Ext.mk₀ e.hom).precomp Y (zero_add i)) := by
    intro x
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add i)) (zero_add i) = x
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id,
      Ext.mk₀_id_comp]
  exact ⟨h₁.injective, h₂.surjective⟩

/-- Postcomposition by an isomorphism is bijective on Ext groups. -/
private theorem postcomp_iso_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]
    (X : C) {Y Y' : C} (e : Y ≅ Y') (i : ℕ) :
    Function.Bijective ((Ext.mk₀ e.hom).postcomp X (add_zero i)) := by
  have h₁ : Function.LeftInverse ((Ext.mk₀ e.inv).postcomp X (add_zero i))
      ((Ext.mk₀ e.hom).postcomp X (add_zero i)) := by
    intro x
    change (x.comp (Ext.mk₀ e.hom) (add_zero i)).comp (Ext.mk₀ e.inv) (add_zero i) = x
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id,
      Ext.comp_mk₀_id]
  have h₂ : Function.RightInverse ((Ext.mk₀ e.inv).postcomp X (add_zero i))
      ((Ext.mk₀ e.hom).postcomp X (add_zero i)) := by
    intro x
    change (x.comp (Ext.mk₀ e.inv) (add_zero i)).comp (Ext.mk₀ e.hom) (add_zero i) = x
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id,
      Ext.comp_mk₀_id]
  exact ⟨h₁.injective, h₂.surjective⟩

/-- Flat base change for Ext, in the form produced by an arbitrary presentation of the extended
module: precomposition by the unit of the scalar adjunction after restriction of scalars is
bijective. -/
private theorem baseChangeComparison_bijective
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (X : ModuleCat.{max uR uS v} R)
    (Y Z : ModuleCat.{max uR uS v} S)
    (e : (ModuleCat.extendScalars f).obj X ≅ Y)
    (η : X ⟶ (ModuleCat.restrictScalars f).obj Y)
    (hη : (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS} f).unit.app X ≫
      (ModuleCat.restrictScalars f).map e.hom = η) (i : ℕ) :
    Function.Bijective (((Ext.mk₀ η).precomp
      ((ModuleCat.restrictScalars f).obj Z) (zero_add i)).comp
      ((ModuleCat.restrictScalars f).mapExtAddHom Y Z i)) := by
  have heq : ((Ext.mk₀ η).precomp
      ((ModuleCat.restrictScalars f).obj Z) (zero_add i)).comp
      ((ModuleCat.restrictScalars f).mapExtAddHom Y Z i) =
      (extendScalarsExtComparison.{uR, uS, max uR v} f X Z i).comp
        ((Ext.mk₀ e.hom).precomp Z (zero_add i)) := by
    ext x
    change (Ext.mk₀ η).comp (x.mapExactFunctor (ModuleCat.restrictScalars f)) (zero_add i) =
      (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS} f).unit.app X)).comp
        (((Ext.mk₀ e.hom).comp x (zero_add i)).mapExactFunctor
          (ModuleCat.restrictScalars f)) (zero_add i)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hη]
  rw [heq]
  exact (extendScalarsExtComparison_bijective.{uR, uS, max uR v} f hf X Z i).comp
    (precomp_iso_bijective e Z i)

end Proof

set_option maxHeartbeats 1600000 in
-- Scalar restriction and lifted tensor products require substantial typeclass elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 087R.** The canonical Ext base-change map is bijective in degree zero for finitely
presented modules, below the pseudo-coherence cutoff, and in every degree for finite modules
over a Noetherian ring.

The maps `η` and `t` are characterized on original elements by `m ↦ 1 ⊗ m` and
`n ⊗ s ↦ s ⊗ n`. The equation `c.comp β = a` and its uniqueness clause specify the canonical
comparison in every degree. The commuting square using `uliftExtLinearEquiv₀` transports `β`
in degree zero to `homBaseChangeComparison` on the original modules. -/
@[stacks 087R]
theorem baseChange_ext_bijective_of_pseudoCoherent
    (R : Type uR) (S : Type uS) (M : Type uM) (N : Type uN)
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [HasDerivedCategory (ModuleCat.{uM} R)] :
    let RM := ModuleCat.of R (ULift.{max uR uS uM uN} M)
    let RN := ModuleCat.of R (ULift.{max uR uS uM uN} N)
    let L := ModuleCat.of R (ULift.{max uR uS uM uN} S)
    let SM := ModuleCat.of S (ULift.{max uR uS uM uN} (S ⊗[R] M))
    let SN := ModuleCat.of S (ULift.{max uR uS uM uN} (S ⊗[R] N))
    let E := (ModuleCat.restrictScalars (algebraMap R S)).obj SN
    ∃ (η : RM ⟶ (ModuleCat.restrictScalars (algebraMap R S)).obj SM)
        (t : ModuleCat.of R (RN ⊗[R] L) ⟶ E),
      (∀ m : M, η (ULift.up m) = ULift.up ((1 : S) ⊗ₜ[R] m)) ∧
      (∀ (n : N) (s : S), t (ULift.up n ⊗ₜ[R] ULift.up s) =
        ULift.up (s ⊗ₜ[R] n)) ∧
      (∀ t' : ModuleCat.of R (RN ⊗[R] L) ⟶ E,
        (∀ (n : N) (s : S), t' (ULift.up n ⊗ₜ[R] ULift.up s) =
          ULift.up (s ⊗ₜ[R] n)) → t' = t) ∧
      ∀ i : ℕ,
        let c : Ext SM SN i →+ Ext RM E i :=
          ((Ext.mk₀ η).precomp E (zero_add i)).comp
            ((ModuleCat.restrictScalars (algebraMap R S)).mapExtAddHom SM SN i)
        let a : (Ext RM RN i) ⊗[R] S →+ Ext RM E i :=
          (((Ext.mk₀ t).postcomp RM (add_zero i)).comp
            (canonicalExtTensorComparison R RM RN L i).toAddMonoidHom).comp
              (TensorProduct.map (LinearMap.id : Ext RM RN i →ₗ[R] Ext RM RN i)
                (ULift.moduleEquiv.symm.toLinearMap : S →ₗ[R] L)).toAddMonoidHom
        ∃ β : (Ext RM RN i) ⊗[R] S →+ Ext SM SN i,
          c.comp β = a ∧
          (∀ γ : (Ext RM RN i) ⊗[R] S →+ Ext SM SN i,
            c.comp γ = a → γ = β) ∧
          (∀ (e : Ext RM RN i) (s r : S),
            β (e ⊗ₜ[R] (r * s)) = r • β (e ⊗ₜ[R] s)) ∧
          (∀ h : i = 0, ∀ x : (Ext RM RN 0) ⊗[R] S,
            uliftExtLinearEquiv₀.{uS, max uS uM, max uS uN, uR} S (S ⊗[R] M) (S ⊗[R] N)
                ((h ▸ β) x) =
              homBaseChangeComparison R S M N
                (TensorProduct.congr (uliftExtLinearEquiv₀.{uR, uM, uN, uS} R M N)
                  (LinearEquiv.refl R S) x)) ∧
          (i = 0 → Module.FinitePresentation R M → Function.Bijective β) ∧
          (∀ d : ℕ, IsModulePseudoCoherentFrom (R := R) M (-(d : ℤ)) →
            i < d → Function.Bijective β) ∧
          (IsNoetherianRing R → Module.Finite R M → Function.Bijective β) := by
  classical
  dsimp only
  let RM := ModuleCat.of R (ULift.{max uR uS uM uN} M)
  let RN := ModuleCat.of R (ULift.{max uR uS uM uN} N)
  let L := ModuleCat.of R (ULift.{max uR uS uM uN} S)
  let SM := ModuleCat.of S (ULift.{max uR uS uM uN} (S ⊗[R] M))
  let SN := ModuleCat.of S (ULift.{max uR uS uM uN} (S ⊗[R] N))
  let G := ModuleCat.restrictScalars.{max uR uS uM uN} (algebraMap R S)
  let E := G.obj SN
  let A := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : A ≃ₗ[S] S := LinearEquiv.refl S S
  let eM : (A ⊗[R] RM) ≃ₗ[S] SM :=
    (TensorProduct.AlgebraTensorModule.congr eA
      (ULift.moduleEquiv : RM ≃ₗ[R] M)).trans ULift.moduleEquiv.symm
  let e : (ModuleCat.extendScalars (algebraMap R S)).obj RM ≅ SM := eM.toModuleIso
  let η : RM ⟶ G.obj SM :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM uN, uR, uS}
      (algebraMap R S)).unit.app RM ≫ G.map e.hom
  have hη (m : M) : η (ULift.up m) = ULift.up ((1 : S) ⊗ₜ[R] m) := by
    change eM ((show A from (1 : S)) ⊗ₜ[R] (ULift.up m : RM)) = _
    exact congrArg ULift.up (TensorProduct.AlgebraTensorModule.congr_tmul eA
      (ULift.moduleEquiv : RM ≃ₗ[R] M) (show A from (1 : S)) (ULift.up m))
  let ι : ModuleCat.of R (ULift.{max uR uS uM uN} (S ⊗[R] N)) ≅ E :=
    LinearEquiv.toModuleIso (X₁ := ModuleCat.of R (ULift.{max uR uS uM uN} (S ⊗[R] N)))
      (X₂ := E) {
      toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r p => (algebraMap_smul S r p).symm }
  let te : ModuleCat.of R (RN ⊗[R] L) ≅ E :=
    ((TensorProduct.congr (ULift.moduleEquiv : RN ≃ₗ[R] N)
      (ULift.moduleEquiv : L ≃ₗ[R] S)).trans
        ((TensorProduct.comm R N S).trans ULift.moduleEquiv.symm)).toModuleIso ≪≫ ι
  let t := te.hom
  have ht (n : N) (s : S) : t (ULift.up n ⊗ₜ[R] ULift.up s) =
      ULift.up (s ⊗ₜ[R] n) := rfl
  refine ⟨η, t, hη, ht, ?_, ?_⟩
  · intro t' ht'
    refine ModuleCat.hom_ext (TensorProduct.ext ?_)
    ext n s
    exact (ht' n.down s.down).trans (ht n.down s.down).symm
  intro i
  let c : Ext SM SN i →+ Ext RM E i :=
    ((Ext.mk₀ η).precomp E (zero_add i)).comp (G.mapExtAddHom SM SN i)
  let a : (Ext RM RN i) ⊗[R] S →+ Ext RM E i :=
    (((Ext.mk₀ t).postcomp RM (add_zero i)).comp
      (canonicalExtTensorComparison R RM RN L i).toAddMonoidHom).comp
        (TensorProduct.map (LinearMap.id : Ext RM RN i →ₗ[R] Ext RM RN i)
          (ULift.moduleEquiv.symm.toLinearMap : S →ₗ[R] L)).toAddMonoidHom
  have hc : Function.Bijective c :=
    baseChangeComparison_bijective (algebraMap R S)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) RM SM SN e η rfl i
  let ce := AddEquiv.ofBijective c hc
  let β := ce.symm.toAddMonoidHom.comp a
  have hβ (x) : c (β x) = a x := ce.apply_symm_apply (a x)
  have ha (x : Ext RM RN i) (s : S) : a (x ⊗ₜ[R] s) =
      x.comp (Ext.mk₀ (tensorElementHom R RN L (ULift.up s) ≫ t))
        (add_zero i) := by
    change (x.comp (Ext.mk₀ (tensorElementHom R RN L (ULift.up s)))
      (add_zero i)).comp (Ext.mk₀ t) (add_zero i) = _
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  have hb (h : Function.Bijective (canonicalExtTensorComparison R RM RN L i)) :
      Function.Bijective β := by
    apply ce.symm.bijective.comp
    apply (postcomp_iso_bijective RM te i).comp
    apply h.comp
    exact (TensorProduct.congr (LinearEquiv.refl R (Ext RM RN i))
      (ULift.moduleEquiv.symm : S ≃ₗ[R] L)).bijective
  refine ⟨β, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact AddMonoidHom.ext hβ
  · exact fun γ hγ => AddMonoidHom.ext fun x =>
      hc.injective ((DFunLike.congr_fun hγ x).trans (hβ x).symm)
  · intro x s r
    apply hc.injective
    rw [hβ]
    change a (x ⊗ₜ[R] (r * s)) =
      (Ext.mk₀ η).comp ((r • β (x ⊗ₜ[R] s)).mapExactFunctor G) (zero_add i)
    rw [Ext.smul_eq_comp_mk₀, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      ← Ext.comp_assoc_of_third_deg_zero]
    change a (x ⊗ₜ[R] (r * s)) =
      (c (β (x ⊗ₜ[R] s))).comp (Ext.mk₀ (G.map (r • 𝟙 SN))) (add_zero i)
    rw [hβ, ha, ha, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    congr 2
  · intro hi
    subst i
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul z s =>
      obtain ⟨f, rfl⟩ := (Ext.linearEquiv₀ (R := R)).symm.surjective z
      let H := homBaseChangeComparison R S M N
        ((uliftExtLinearEquiv₀.{uR, uM, uN, uS} R M N (Ext.mk₀ f)) ⊗ₜ[R] s)
      let q : SM ⟶ SN := ModuleCat.ofHom
        (ULift.moduleEquiv.symm.toLinearMap.comp (H.comp ULift.moduleEquiv.toLinearMap))
      have hq : β ((Ext.mk₀ f) ⊗ₜ[R] s) = Ext.mk₀ q := by
        apply hc.injective
        rw [hβ, ha]
        change (Ext.mk₀ f).comp (Ext.mk₀ _) (add_zero 0) =
          (Ext.mk₀ η).comp ((Ext.mk₀ q).mapExactFunctor G) (zero_add 0)
        rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
        congr 1
        ext m
        change t (f m ⊗ₜ[R] ULift.up s) = q (η m)
        rw [ht (f m).down, hη m.down]
        change ULift.up (s ⊗ₜ[R] (f m).down) = ULift.up (H ((1 : S) ⊗ₜ[R] m.down))
        simp [H, homBaseChangeComparison_tmul_apply, uliftExtLinearEquiv₀_mk₀_apply]
      change uliftExtLinearEquiv₀.{uS, max uS uM, max uS uN, uR}
        S (S ⊗[R] M) (S ⊗[R] N)
        (β ((Ext.mk₀ f) ⊗ₜ[R] s)) = _
      rw [hq]
      apply LinearMap.ext
      intro y
      rw [uliftExtLinearEquiv₀_mk₀_apply]
      change H y = _
      rfl
  · intro hi hM
    subst i
    exact hb (canonicalExtTensorComparison_zero_bijective R RM RN L
      (rTensorHomToHomRTensor_bijective_of_finitePresentation R RM RN L
        (Module.FinitePresentation.of_equiv (ULift.moduleEquiv.symm : M ≃ₗ[R] RM))))
  · intro d hM hi
    exact hb ((canonicalExtTensorComparison_bijective R M N S).2 d hM i hi)
  · intro hR hM
    exact hb (canonicalExtTensorComparison_bijective_of_isNoetherianRing R RM RN L i)

/-- **Stacks 087Q for a finite module over a Noetherian ring.** Over a Noetherian ring the
syzygies of a finite module are again finite, so the canonical Ext--tensor comparison
`Extⁱ_R(M, N) ⊗_R L → Extⁱ_R(M, N ⊗_R L)` against a flat tensor factor is bijective in every
degree. -/
theorem canonicalExtTensorComparison_bijective_of_noetherian
    (R : Type uR) (M : Type uM) (N : Type uN) (L : Type uS)
    [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L] [Module.Flat R L]
    (i : ℕ) :
    Function.Bijective (canonicalExtTensorComparison R
      (ModuleCat.of R (ULift.{max uR uS uM uN} M))
      (ModuleCat.of R (ULift.{max uR uS uM uN} N))
      (ModuleCat.of R (ULift.{max uR uS uM uN} L)) i) :=
  canonicalExtTensorComparison_bijective_of_isNoetherianRing R
    (ModuleCat.of R (ULift.{max uR uS uM uN} M)) (ModuleCat.of R (ULift.{max uR uS uM uN} N))
    (ModuleCat.of R (ULift.{max uR uS uM uN} L)) i

end BaseChange

end StacksDraft.PseudoCoherence
