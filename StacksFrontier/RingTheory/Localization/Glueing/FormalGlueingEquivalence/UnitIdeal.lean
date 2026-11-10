module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.Modules
public import StacksFrontier.Topology.Sheaves.Glueing.Equivalence
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.LeftQuasiInverse
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.LeftQuasiInverse

/-!
# Formal glueing of module categories: the case of a unit ideal

When `f` generates the unit ideal, the canonical functor `Can` from `R`-modules to module glueing
data and the functor `H⁰` of compatible sections are already an equivalence: this is ordinary
glueing of modules along a Zariski cover. This file proves it, by showing that the projections
from compatible sections to the local pieces are localizations.

It then begins flat base change of module glueing data along `R → R'`: the canonical base-change
comparisons for the generic localization, the generic/local tensor product and the local/local
overlaps, and the base-changed overlap isomorphisms together with their compatibility with those
comparisons.

## Main results

* `FormalGlueing.canonicalFunctor_sections_areQuasiInverse_of_span_eq_top`: for a family
  generating the unit ideal, `Can` and `H⁰` are the forward and inverse functors of an
  equivalence.

## References

* [Stacks Project, Tag 05EP](https://stacks.math.columbia.edu/tag/05EP)
-/

section

namespace FormalGlueing

universe u v w

open CategoryTheory FormalGlueing TensorProduct Cech

attribute [local instance] restrictScalars_isScalarTower

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

private theorem iterated_localized_mk (M : Type*) [AddCommGroup M] [Module R M]
    (s t : Finset (Fin r)) (x : cechMod f M s) :
    (localizationComparisons f).iterated M t s
        (localizedMap f s (LocalizedModule.mkLinearMap (cechSub f t) M) x) =
      cechModCongr f (Finset.union_comm s t)
        ((localizationComparisons f).iterated M s t
          (LocalizedModule.mkLinearMap (cechSub f t) _ x)) := by
  have hu (a : cechSub f s) : IsUnit (algebraMap R
      (Module.End R (cechMod f M (t ∪ s))) a) :=
    IsLocalizedModule.map_units (S := Submonoid.closure (f '' (↑(t ∪ s) : Set (Fin r))))
      (LocalizedModule.mkLinearMap (cechSub f (t ∪ s)) M)
      ⟨a, cechSub_le_closure f Finset.subset_union_right a.2⟩
  have h : ((localizationComparisons f).iterated M t s).toLinearMap.comp
      (localizedMap f s (LocalizedModule.mkLinearMap (cechSub f t) M)) =
      (cechModCongr f (Finset.union_comm s t)).toLinearMap.comp
        (((localizationComparisons f).iterated M s t).toLinearMap.comp
          (LocalizedModule.mkLinearMap (cechSub f t) _)) := by
    apply IsLocalizedModule.ext (cechSub f s) (LocalizedModule.mkLinearMap (cechSub f s) M) hu
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, localizedMap_mk,
      iterated_mk, cechModCongr_mk]
  exact LinearMap.congr_fun h x

private theorem exists_compatible_family
    {ι : Type*} [Finite ι] (a : ι → R)
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module (Localization.Away (a i)) (M i)]
    [∀ i, IsScalarTower R (Localization.Away (a i)) (M i)]
    (T : ι → Submonoid R) (hT : T = fun i ↦ Submonoid.powers (a i))
    (ψ : ∀ i j, LocalizedModule (T j) (M i) ≃ₗ[R] LocalizedModule (T i) (M j))
    (hc : ∀ i j k (m : M i),
      LocalizedModule.map (T i) (LocalizedModule.mkLinearMap (T j) (M k))
        (ψ i k (LocalizedModule.mkLinearMap (T k) (M i) m)) =
      LocalizedModule.map (T i) (ψ j k).toLinearMap
        (LocalizedModule.map (T i) (LocalizedModule.mkLinearMap (T k) (M j))
          (ψ i j (LocalizedModule.mkLinearMap (T j) (M i) m))))
    (i : ι) (y : M i) :
    ∃ (n : ℕ) (m : ∀ j, M j), (a i) ^ n • y = m i ∧
      ∀ j k, ψ j k (LocalizedModule.mkLinearMap (T k) (M j) (m j)) =
        LocalizedModule.mkLinearMap (T j) (M k) (m k) := by
  classical
  let := Fintype.ofFinite ι
  subst T
  let D : ModuleGluingData ι a :=
    { M := M
      ψ := ψ
      cocycle i j k := by ext m; exact hc i j k m }
  have := ModuleGluingData.proj_isLocalizedModule D i
  obtain ⟨⟨m, b⟩, hb⟩ := IsLocalizedModule.surj (Submonoid.powers (a i)) (D.proj i) y
  obtain ⟨n, hn⟩ := b.2
  refine ⟨n, fun j ↦ D.proj j m, ?_, fun j k ↦ D.psi_apply_of_mem_gluedModule m j k⟩
  simpa only [Submonoid.smul_def, ← hn] using hb

private theorem local_transition_cocycle
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (i j k : Fin r) (m : restrictFromAway f i (X.localPiece i)) :
    localizedMap f {i} (LocalizedModule.mkLinearMap (cechSub f {j}) _)
        (X.alphaIJ i k (LocalizedModule.mkLinearMap (cechSub f {k}) _ m)) =
      localizedMap f {i} (X.alphaIJ j k).toLinearMap
        (localizedMap f {i} (LocalizedModule.mkLinearMap (cechSub f {k}) _)
          (X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ m))) := by
  have hc := LinearMap.congr_fun (X.cocycle i j k)
    (LocalizedModule.mkLinearMap (cechSub f ({j} ∪ {k})) _ m)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, iterated_symm_mk,
    localizedMap_mk, cechModCongr_mk] at hc
  apply ((localizationComparisons f).iterated
    (restrictFromAway f k (X.localPiece k)) {j} {i}).injective
  rw [iterated_localized_mk]
  rw [← iterated_localized_mk] at hc
  simp only [LinearEquiv.symm_apply_apply] at hc
  exact hc.symm

private def localSections
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    Submodule R (∀ i, restrictFromAway f i (X.localPiece i)) where
  carrier := {m | ∀ i j, X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ (m i)) =
    LocalizedModule.mkLinearMap (cechSub f {i}) _ (m j)}
  zero_mem' := by intro i j; simp
  add_mem' hx hy := by
    intro i j
    simpa only [Pi.add_apply, map_add] using congrArg₂ (· + ·) (hx i j) (hy i j)
  smul_mem' a m hm := by
    intro i j
    simpa only [Pi.smul_apply, map_smul] using congrArg (a • ·) (hm i j)

private noncomputable abbrev localSectionsProjection
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    localSections S f X →ₗ[R] restrictFromAway f i (X.localPiece i) :=
  (LinearMap.proj i).comp (localSections S f X).subtype

private theorem localSectionsProjection_surj
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r)
    (y : restrictFromAway f i (X.localPiece i)) :
    ∃ (n : ℕ) (m : localSections S f X), (f i) ^ n • y = localSectionsProjection S f X i m := by
  obtain ⟨n, m, hm, hc⟩ := exists_compatible_family f
    (fun i ↦ restrictFromAway f i (X.localPiece i)) (fun i ↦ cechSub f {i})
    (by ext i; simp only [cechSub, Finset.prod_singleton]) X.alphaIJ
    (local_transition_cocycle S f X) i y
  exact ⟨n, ⟨m, hc⟩, hm⟩

private theorem localSections_compatibility
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (m : localSections S f X) (i j : Fin r) :
    X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _
      (localSectionsProjection S f X i m)) =
      LocalizedModule.mkLinearMap (cechSub f {i}) _
        (localSectionsProjection S f X j m) := m.2 i j

private noncomputable def genericComparison
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    restrictFromTarget (R := R) S X.generic →ₗ[R]
      S ⊗[R] restrictFromAway f i (X.localPiece i) := by
  letI : Module R X.generic := Module.compHom _ (algebraMap R S)
  letI : IsScalarTower R S X.generic := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact ((X.alpha i).toLinearMap.comp
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _)).restrictScalars R

private theorem genericComparison_apply
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r)
    (x : restrictFromTarget (R := R) S X.generic) :
    genericComparison S f X i x = X.alpha i (LocalizedModule.mkLinearMap _ _ x) := rfl

private theorem genericComparison_isLocalized
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    IsLocalizedModule (Submonoid.powers (f i)) (genericComparison S f X i) := by
  let : Module R X.generic := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S X.generic := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := IsLocalizedModule.of_linearEquiv
    (Submonoid.powers (algebraMap R S (f i)))
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) X.generic)
    (X.alpha i)
  exact IsLocalizedModule.restrictScalars_powers (M := X.generic) (f i)
    ((X.alpha i).toLinearMap.comp (LocalizedModule.mkLinearMap _ X.generic))

private theorem comparison_difference_torsion
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (m : localSections S f X)
    (g : restrictFromTarget (R := R) S X.generic) (i : Fin r)
    (hi : genericComparison S f X i g = (1 : S) ⊗ₜ[R] localSectionsProjection S f X i m)
    (j : Fin r) :
    ∃ n : ℕ, (f i) ^ n •
      (genericComparison S f X j g - (1 : S) ⊗ₜ[R] localSectionsProjection S f X j m) = 0 := by
  let l := (LocalizedModule.mkLinearMap (cechSub f {i})
    (restrictFromAway f j (X.localPiece j))).lTensor S
  have := singletonLocalization_isLocalized f (restrictFromAway f j (X.localPiece j)) i
  have := isLocalized_lTensor S (Submonoid.powers (f i))
    (LocalizedModule.mkLinearMap (cechSub f {i}) (restrictFromAway f j (X.localPiece j)))
  have h : l (genericComparison S f X j g) =
      l ((1 : S) ⊗ₜ[R] localSectionsProjection S f X j m) := by
    have hc := X.alpha_compatibility i j g
    change TensorProduct.map LinearMap.id (X.alphaIJ i j).toLinearMap
      (TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (cechSub f {j}) _)
        (genericComparison S f X i g)) = l (genericComparison S f X j g) at hc
    rw [hi, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearEquiv.coe_coe, localSections_compatibility] at hc
    exact hc.symm
  obtain ⟨⟨a, n, hn⟩, ha⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h
  change (f i) ^ n = a at hn
  refine ⟨n, ?_⟩
  rw [smul_sub, sub_eq_zero, hn]
  exact ha

private theorem exists_section_of_glued
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (m : localSections S f X) (i : Fin r) :
    ∃ (n : ℕ) (x : sections S f X),
      (f i) ^ n • localSectionsProjection S f X i m = sectionsLocalProjection S f X i x := by
  have := genericComparison_isLocalized S f X i
  obtain ⟨⟨g, a⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers (f i))
    (genericComparison S f X i) ((1 : S) ⊗ₜ[R] localSectionsProjection S f X i m)
  obtain ⟨n, hn⟩ := a.2
  change (f i) ^ n = (a : R) at hn
  let m' := (f i) ^ n • m
  have hi : genericComparison S f X i g =
      (1 : S) ⊗ₜ[R] localSectionsProjection S f X i m' := by
    rw [← ha]
    simp only [m', map_smul, ← TensorProduct.tmul_smul, Submonoid.smul_def, hn]
  obtain ⟨N, hN⟩ := ModuleGluingData.exists_uniform_pow_annihilator (f i)
    (fun j ↦ genericComparison S f X j g -
      (1 : S) ⊗ₜ[R] localSectionsProjection S f X j m')
    (comparison_difference_torsion S f X m' g i hi)
  let x : sections S f X :=
    ⟨((f i) ^ N • g, fun j ↦ localSectionsProjection S f X j ((f i) ^ N • m')),
      ⟨by
        intro j
        change genericComparison S f X j ((f i) ^ N • g) =
          (1 : S) ⊗ₜ[R] localSectionsProjection S f X j ((f i) ^ N • m')
        rw [map_smul, map_smul, TensorProduct.tmul_smul]
        exact sub_eq_zero.mp (by simpa only [smul_sub] using hN j),
      fun j k ↦ localSections_compatibility S f X ((f i) ^ N • m') j k⟩⟩
  refine ⟨N + n, x, ?_⟩
  change (f i) ^ (N + n) • _ = localSectionsProjection S f X i ((f i) ^ N • m')
  simp only [m', map_smul, pow_add, mul_smul]

private theorem sectionsLocalProjection_zero_torsion
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r)
    (x : sections S f X) (hx : sectionsLocalProjection S f X i x = 0) :
    ∃ n : ℕ, (f i) ^ n • x = 0 := by
  have := genericComparison_isLocalized S f X i
  have hg : genericComparison S f X i x.1.1 = genericComparison S f X i 0 := by
    rw [map_zero]
    change X.alpha i (LocalizedModule.mkLinearMap _ _ x.1.1) = 0
    rw [x.2.1 i]
    change (1 : S) ⊗ₜ[R] sectionsLocalProjection S f X i x = 0
    rw [hx, TensorProduct.tmul_zero]
  obtain ⟨⟨a, n, hn⟩, ha⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers (f i)) hg
  change (f i) ^ n = a at hn
  have hloc j : LocalizedModule.mkLinearMap (cechSub f {i})
      (restrictFromAway f j (X.localPiece j)) (x.1.2 j) = 0 := by
    have h := x.2.2 i j
    change X.alphaIJ i j (LocalizedModule.mkLinearMap _ _
      (sectionsLocalProjection S f X i x)) = _ at h
    rw [hx, map_zero, map_zero] at h
    exact h.symm
  have hpow (j : Fin r) : ∃ n : ℕ, (f i) ^ n • x.1.2 j = 0 := by
    have := singletonLocalization_isLocalized f (restrictFromAway f j (X.localPiece j)) i
    obtain ⟨b, hb⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i))
      ((hloc j).trans (map_zero _).symm)
    obtain ⟨n, hn⟩ := b.2
    exact ⟨n, by simpa only [Submonoid.smul_def, ← hn, smul_zero] using hb⟩
  obtain ⟨N, hN⟩ := ModuleGluingData.exists_uniform_pow_annihilator (f i) x.1.2 hpow
  refine ⟨n + N, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (f i) ^ (n + N) • x.1.1 = 0
    rw [pow_add, mul_comm, mul_smul, hn]
    have ha' : a • x.1.1 = 0 := by simpa only [Submonoid.smul_def, smul_zero] using ha
    rw [ha', smul_zero]
  · funext j
    change (f i) ^ (n + N) • x.1.2 j = 0
    rw [pow_add, mul_smul, hN j, smul_zero]

private theorem sectionsLocalProjection_isLocalized
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) (i : Fin r) :
    IsLocalizedModule (Submonoid.powers (f i)) (sectionsLocalProjection S f X i) where
  map_units := localPiece_map_units S f X i
  surj y := by
    obtain ⟨n, m, hm⟩ := localSectionsProjection_surj S f X i y
    obtain ⟨N, x, hx⟩ := exists_section_of_glued S f X m i
    refine ⟨⟨x, ⟨(f i) ^ (N + n), ⟨N + n, rfl⟩⟩⟩, ?_⟩
    change (f i) ^ (N + n) • y = sectionsLocalProjection S f X i x
    rw [pow_add, mul_smul, hm]
    exact hx
  exists_of_eq {x y} h := by
    obtain ⟨n, hn⟩ := sectionsLocalProjection_zero_torsion S f X i (x - y) (by
      rw [map_sub, h, sub_self])
    refine ⟨⟨(f i) ^ n, ⟨n, rfl⟩⟩, ?_⟩
    exact sub_eq_zero.mp (by simpa only [smul_sub, Submonoid.smul_def] using hn)

/-- If a finite family generates the unit ideal and `R → S` is flat, then the canonical module
glueing functor and compatible sections are quasi-inverse equivalences of categories. -/
@[stacks 05EP]
public theorem canonicalFunctor_sections_areQuasiInverse_of_span_eq_top
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hf : Ideal.span (Set.range f) = ⊤) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    ∃ e : ModuleCat.{max u v w} R ≌ ModuleGlueingDatum.{u, v, w} S f c.comparison,
      e.functor = c.canonical ∧ e.inverse = c.sections :=
  canonicalFunctor_sections_areQuasiInverse_of_isLocalized S f hflat hf
    (sectionsLocalProjection_isLocalized S f)

end FormalGlueing


end

/-! ### Base change for module glueing data -/

section

namespace FormalGlueing

universe u v x w

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct
open scoped ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem isLocalized_baseChange
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (T : Submonoid A) (l : M →ₗ[A] N) [IsLocalizedModule T l] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B T) (l.baseChange B) := by
  have : IsLocalizedModule T ((l.baseChange B).restrictScalars A) :=
    FormalGlueing.isLocalized_lTensor B T l
  exact IsLocalizedModule.of_restrictScalars T (l.baseChange B)

private noncomputable def localizationBaseChange
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (T : Submonoid A) (M : Type*) [AddCommGroup M] [Module A M] :
    LocalizedModule (Algebra.algebraMapSubmonoid B T) (B ⊗[A] M) ≃ₗ[B]
      B ⊗[A] LocalizedModule T M := by
  letI := isLocalized_baseChange (B := B) T (LocalizedModule.mkLinearMap T M)
  exact IsLocalizedModule.iso _ ((LocalizedModule.mkLinearMap T M).baseChange B)

private theorem localizationBaseChange_mk
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (T : Submonoid A) (M : Type*) [AddCommGroup M] [Module A M] (b : B) (m : M) :
    localizationBaseChange B T M
      (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid B T) _ (b ⊗ₜ[A] m)) =
      b ⊗ₜ[A] LocalizedModule.mkLinearMap T M m := by
  let := isLocalized_baseChange (B := B) T (LocalizedModule.mkLinearMap T M)
  exact IsLocalizedModule.iso_mk_one _ _ _

private noncomputable def tensorBaseChangeAux
    (R S B M : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] :
    ((S ⊗[R] B) ⊗[S] M) ≃ₗ[R] B ⊗[R] M :=
  ((AlgebraTensorModule.rightComm R S S S M B).symm.restrictScalars R) ≪≫ₗ
    TensorProduct.congr ((TensorProduct.lid S M).restrictScalars R) (LinearEquiv.refl R B) ≪≫ₗ
    TensorProduct.comm R M B

private theorem tensorBaseChangeAux_tmul
    (R S B M : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (s : S) (b : B) (m : M) :
    tensorBaseChangeAux R S B M ((s ⊗ₜ[R] b) ⊗ₜ[S] m) = b ⊗ₜ[R] (s • m) := rfl

private theorem tensorBaseChangeAux_symm_tmul
    (R S B M : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (b : B) (m : M) :
    (tensorBaseChangeAux R S B M).symm (b ⊗ₜ[R] m) = (1 ⊗ₜ[R] b) ⊗ₜ[S] m := rfl

private noncomputable def pushoutTensorEquiv
    (R S B C M : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
    [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    (C ⊗[S] M) ≃ₗ[B] B ⊗[R] M := by
  let g : B ⊗[R] M →ₗ[B] C ⊗[S] M :=
    ((TensorProduct.mk S C M 1).restrictScalars R).liftBaseChange B
  let e : B ⊗[R] M ≃ₗ[R] C ⊗[S] M :=
    (tensorBaseChangeAux R S B M).symm ≪≫ₗ
      (TensorProduct.congr (Algebra.IsPushout.equiv R S B C).toLinearEquiv
        (LinearEquiv.refl S M)).restrictScalars R
  have he : g.restrictScalars R = e.toLinearMap := by
    ext b m
    simp [g, e, tensorBaseChangeAux_symm_tmul, Algebra.IsPushout.equiv_tmul,
      smul_tmul', Algebra.smul_def]
  exact (LinearEquiv.ofBijective g (by
    change Function.Bijective (g.restrictScalars R)
    rw [he]
    exact e.bijective)).symm

private theorem pushoutTensorEquiv_symm_tmul
    (R S B C M : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
    [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (b : B) (m : M) :
    (pushoutTensorEquiv R S B C M).symm (b ⊗ₜ[R] m) =
      algebraMap B C b ⊗ₜ[S] m := by
  change b • (1 ⊗ₜ[S] m : C ⊗[S] M) = _
  simp [smul_tmul', Algebra.smul_def]

private theorem pushoutTensorEquiv_tmul
    (R S B C M : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
    [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (b : B) (m : M) :
    pushoutTensorEquiv R S B C M (algebraMap B C b ⊗ₜ[S] m) = b ⊗ₜ[R] m := by
  rw [← pushoutTensorEquiv_symm_tmul R S B C M b m, LinearEquiv.apply_symm_apply]

private noncomputable abbrev awayMap {R : Type*} (B : Type*) [CommRing R] [CommRing B]
    [Algebra R B] (a : R) : Localization.Away a →+* Localization.Away (algebraMap R B a) :=
  IsLocalization.Away.map (Localization.Away a)
    (Localization.Away (algebraMap R B a)) (algebraMap R B) a

private theorem awayMap_tower {R : Type*} (B : Type*) [CommRing R] [CommRing B]
    [Algebra R B] (a : R) :
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap R B a)) :=
      (awayMap B a).toAlgebra
    IsScalarTower R (Localization.Away a) (Localization.Away (algebraMap R B a)) := by
  let : Algebra (Localization.Away a) (Localization.Away (algebraMap R B a)) :=
    (awayMap B a).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  change algebraMap B (Localization.Away (algebraMap R B a)) (algebraMap R B r) =
    awayMap B a (algebraMap R (Localization.Away a) r)
  symm
  exact IsLocalization.map_eq _ r

/-- `Away (f a)` over `B` is the pushout of `Away a` along `R → B`. -/
private theorem awayPushout {R : Type*} (B : Type*) [CommRing R] [CommRing B]
    [Algebra R B] (a : R) :
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap R B a)) :=
      (awayMap B a).toAlgebra
    let := awayMap_tower B a
    Algebra.IsPushout R (Localization.Away a) B (Localization.Away (algebraMap R B a)) := by
  let : Algebra (Localization.Away a) (Localization.Away (algebraMap R B a)) :=
    (awayMap B a).toAlgebra
  let := awayMap_tower B a
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
      (Localization.Away (algebraMap R B a)) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization.Away (algebraMap R B a)
        (Localization.Away (algebraMap R B a)))
  exact (Algebra.isPushout_of_isLocalization (Submonoid.powers a) (Localization.Away a)
    B (Localization.Away (algebraMap R B a))).symm

public theorem restrictScalars_tower {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat S) :
    let : Module R M := Module.compHom M (algebraMap R S)
    IsScalarTower R S M := by
  let : Module R M := Module.compHom M (algebraMap R S)
  exact ⟨fun r s m ↦ by
    change (r • s) • m = algebraMap R S r • (s • m)
    rw [Algebra.smul_def, mul_smul]⟩

private noncomputable def awayTensorEquiv {R : Type*} (B : Type*)
    [CommRing R] [CommRing B] [Algebra R B] (a : R)
    (M : ModuleCat (Localization.Away a)) :
    (ModuleCat.restrictScalars (algebraMap B (Localization.Away (algebraMap R B a)))).obj
        ((ModuleCat.extendScalars (awayMap B a)).obj M) ≃ₗ[B]
      B ⊗[R] (ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj M := by
  letI : Module R M := Module.compHom M (algebraMap R (Localization.Away a))
  letI : IsScalarTower R (Localization.Away a) M := restrictScalars_tower M
  letI : Algebra (Localization.Away a) (Localization.Away (algebraMap R B a)) :=
    (awayMap B a).toAlgebra
  letI := awayMap_tower B a
  letI := awayPushout B a
  exact (FormalGlueing.restrictModuleOfEquiv (R := B)
    (Localization.Away (algebraMap R B a))
    (Localization.Away (algebraMap R B a) ⊗[Localization.Away a] M)) ≪≫ₗ
      pushoutTensorEquiv R (Localization.Away a) B
        (Localization.Away (algebraMap R B a)) M

private noncomputable def localizedEquiv {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (T : Submonoid A) (e : M ≃ₗ[A] N) : LocalizedModule T M ≃ₗ[A] LocalizedModule T N :=
  LinearEquiv.ofBijective ((LocalizedModule.map T e.toLinearMap).restrictScalars A)
    ⟨LocalizedModule.map_injective T e.toLinearMap e.injective,
      LocalizedModule.map_surjective T e.toLinearMap e.surjective⟩

private theorem localizedEquiv_mk {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (T : Submonoid A) (e : M ≃ₗ[A] N) (m : M) :
    localizedEquiv T e (LocalizedModule.mkLinearMap T M m) =
      LocalizedModule.mkLinearMap T N (e m) := LocalizedModule.map_mk _ _ _ _

/-- Base change of the localization at `a` is the localization at its image. -/
private theorem isLocalized_baseChange_away {A : Type*} (B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] (a : A)
    (M : Type*) [AddCommGroup M] [Module A M] :
    IsLocalizedModule (Submonoid.powers (algebraMap A B a))
      ((LocalizedModule.mkLinearMap (Submonoid.powers a) M).baseChange B) := by
  simpa only [Algebra.algebraMapSubmonoid_powers] using
    isLocalized_baseChange (B := B) (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M)

/-- Base change of the Čech localization is the Čech localization of the images. -/
private theorem isLocalized_baseChange_cech {A : Type*} (B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} (f : Fin r → A)
    (M : Type*) [AddCommGroup M] [Module A M] (s : Finset (Fin r)) :
    IsLocalizedModule (Cech.cechSub (fun i ↦ algebraMap A B (f i)) s)
      ((LocalizedModule.mkLinearMap (Cech.cechSub f s) M).baseChange B) := by
  simpa only [Cech.cechSub, Algebra.algebraMapSubmonoid_powers, map_prod] using
    isLocalized_baseChange (B := B) (Cech.cechSub f s)
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)

private noncomputable def awayLocalizationBaseChange {A : Type*} (B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] (a : A)
    (M : Type*) [AddCommGroup M] [Module A M] :
    LocalizedModule.Away (algebraMap A B a) (B ⊗[A] M) ≃ₗ[B]
      B ⊗[A] LocalizedModule.Away a M := by
  haveI := isLocalized_baseChange_away B a M
  exact IsLocalizedModule.iso _ ((LocalizedModule.mkLinearMap (Submonoid.powers a) M).baseChange B)

private noncomputable def cechBaseChangeEquiv {A : Type*} (B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} (f : Fin r → A)
    (M : Type*) [AddCommGroup M] [Module A M] (s : Finset (Fin r)) :
    Cech.cechMod (fun i ↦ algebraMap A B (f i)) (B ⊗[A] M) s ≃ₗ[B]
      B ⊗[A] Cech.cechMod f M s := by
  haveI := isLocalized_baseChange_cech B f M s
  exact IsLocalizedModule.iso _ ((LocalizedModule.mkLinearMap (Cech.cechSub f s) M).baseChange B)

@[expose] public noncomputable def extendScalarsEquiv
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≃ₗ[B] B ⊗[A] M := by
  let N := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B N := restrictScalars_tower (ModuleCat.of B B)
  let e : N ≃ₗ[B] B :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact AlgebraTensorModule.congr e (LinearEquiv.refl A M)

private noncomputable abbrev genericLocalizationMap
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat S) :
    (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj M →ₗ[S ⊗[R] B]
      (S ⊗[R] B) ⊗[S] LocalizedModule.Away (algebraMap R S a) M :=
  ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S a)) M).baseChange
    (S ⊗[R] B)).comp (extendScalarsEquiv (S ⊗[R] B) M).toLinearMap

private theorem genericLocalization_isLocalized
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat S) :
    IsLocalizedModule (Submonoid.powers
      (algebraMap B (S ⊗[R] B) (algebraMap R B a))) (genericLocalizationMap S B a M) := by
  let T := Submonoid.powers (algebraMap R S a)
  let l := LocalizedModule.mkLinearMap T M
  have := isLocalized_baseChange (B := S ⊗[R] B) T l
  have h := IsLocalizedModule.of_linearEquiv_right (Algebra.algebraMapSubmonoid (S ⊗[R] B) T)
    (l.baseChange (S ⊗[R] B)) (extendScalarsEquiv (S ⊗[R] B) M)
  have ha : algebraMap B (S ⊗[R] B) (algebraMap R B a) =
      algebraMap S (S ⊗[R] B) (algebraMap R S a) := by
    simp [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  simpa only [ha, T, Algebra.algebraMapSubmonoid_powers] using h

private noncomputable def genericLocalizationEquiv
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat S) :
    LocalizedModule.Away (algebraMap B (S ⊗[R] B) (algebraMap R B a))
        ((ModuleCat.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj M) ≃ₗ[S ⊗[R] B]
      (S ⊗[R] B) ⊗[S] LocalizedModule.Away (algebraMap R S a) M := by
  letI := genericLocalization_isLocalized S B a M
  exact IsLocalizedModule.iso _ (genericLocalizationMap S B a M)

private theorem genericLocalizationEquiv_mk
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat S) (t : S ⊗[R] B) (m : M) :
    genericLocalizationEquiv S B a M
        (LocalizedModule.mkLinearMap (Submonoid.powers
          (algebraMap B (S ⊗[R] B) (algebraMap R B a))) _
            (t ⊗ₜ[S, Algebra.TensorProduct.includeLeftRingHom] m)) =
      t ⊗ₜ[S] LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S a)) M m := by
  let := genericLocalization_isLocalized S B a M
  exact IsLocalizedModule.iso_mk_one _ _ _

private noncomputable def genericLocalTensorEquiv
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat (Localization.Away a)) :
    (S ⊗[R] B) ⊗[B]
        (ModuleCat.restrictScalars (algebraMap B (Localization.Away (algebraMap R B a)))).obj
          ((ModuleCat.extendScalars (awayMap B a)).obj M) ≃ₗ[S ⊗[R] B]
      (S ⊗[R] B) ⊗[S]
        (S ⊗[R] (ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj M) :=
  AlgebraTensorModule.congr (LinearEquiv.refl (S ⊗[R] B) (S ⊗[R] B))
      (awayTensorEquiv B a M) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R B (S ⊗[R] B) (S ⊗[R] B) _ ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R S (S ⊗[R] B) (S ⊗[R] B) _).symm

private noncomputable def localOverlapEquiv
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    {r : ℕ} (f : Fin r → R) (i : Fin r) (M : ModuleCat (Localization.Away (f i)))
    (s : Finset (Fin r)) :
    Cech.cechMod (fun j ↦ algebraMap R B (f j))
        ((ModuleCat.restrictScalars (algebraMap B (Localization.Away (algebraMap R B (f i))))).obj
          ((ModuleCat.extendScalars (awayMap B (f i))).obj M)) s ≃ₗ[B]
      B ⊗[R] Cech.cechMod f
        ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).obj M) s :=
  localizedEquiv (Cech.cechSub (fun j ↦ algebraMap R B (f j)) s)
      (awayTensorEquiv B (f i) M) ≪≫ₗ
    cechBaseChangeEquiv B f _ s

private theorem awayTensorEquiv_tmul {R : Type*} (B : Type*)
    [CommRing R] [CommRing B] [Algebra R B] (a : R)
    (M : ModuleCat (Localization.Away a)) (b : B) (m : M) :
    awayTensorEquiv B a M
        ((algebraMap B (Localization.Away (algebraMap R B a)) b)
          ⊗ₜ[Localization.Away a, awayMap B a] m) =
      b ⊗ₜ[R]
        (show (ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj M from m) := by
  let : Module R M := Module.compHom M (algebraMap R (Localization.Away a))
  let : IsScalarTower R (Localization.Away a) M := restrictScalars_tower M
  let : Algebra (Localization.Away a) (Localization.Away (algebraMap R B a)) :=
    (awayMap B a).toAlgebra
  let := awayMap_tower B a
  let := awayPushout B a
  exact pushoutTensorEquiv_tmul R (Localization.Away a) B
    (Localization.Away (algebraMap R B a)) M b m

private theorem awayLocalizationBaseChange_mk {A : Type*} (B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] (a : A)
    (M : Type*) [AddCommGroup M] [Module A M] (b : B) (m : M) :
    awayLocalizationBaseChange B a M
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B a)) _ (b ⊗ₜ[A] m)) =
      b ⊗ₜ[A] LocalizedModule.mkLinearMap (Submonoid.powers a) M m := by
  have := isLocalized_baseChange_away B a M
  exact IsLocalizedModule.iso_mk_one _ _ _

private theorem cechBaseChangeEquiv_mk {A : Type*} (B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} (f : Fin r → A)
    (M : Type*) [AddCommGroup M] [Module A M] (s : Finset (Fin r)) (b : B) (m : M) :
    cechBaseChangeEquiv B f M s
        (LocalizedModule.mkLinearMap (Cech.cechSub (fun i ↦ algebraMap A B (f i)) s) _
          (b ⊗ₜ[A] m)) = b ⊗ₜ[A] LocalizedModule.mkLinearMap (Cech.cechSub f s) M m := by
  have := isLocalized_baseChange_cech B f M s
  exact IsLocalizedModule.iso_mk_one _ _ _

private theorem genericLocalTensorEquiv_tmul
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (a : R) (M : ModuleCat (Localization.Away a))
    (t : S ⊗[R] B) (m : M) :
    genericLocalTensorEquiv S B a M
        (t ⊗ₜ[B] ((1 : Localization.Away (algebraMap R B a))
          ⊗ₜ[Localization.Away a, awayMap B a] m)) =
      t ⊗ₜ[S] (1 ⊗ₜ[R]
        (show (ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj M from m)) := by
  have h := awayTensorEquiv_tmul B a M 1 m
  simp only [map_one] at h
  dsimp only [genericLocalTensorEquiv, LinearEquiv.trans_apply]
  rw [AlgebraTensorModule.congr_tmul, h]
  dsimp only [LinearEquiv.refl_apply]
  rw [AlgebraTensorModule.cancelBaseChange_tmul R B (S ⊗[R] B), one_smul,
    AlgebraTensorModule.cancelBaseChange_symm_tmul R S (S ⊗[R] B)]

private theorem localOverlapEquiv_mk
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    {r : ℕ} (f : Fin r → R) (i : Fin r) (M : ModuleCat (Localization.Away (f i)))
    (s : Finset (Fin r)) (m : M) :
    localOverlapEquiv B f i M s
        (LocalizedModule.mkLinearMap (Cech.cechSub (fun j ↦ algebraMap R B (f j)) s) _
          ((1 : Localization.Away (algebraMap R B (f i)))
            ⊗ₜ[Localization.Away (f i), awayMap B (f i)] m)) =
      1 ⊗ₜ[R] LocalizedModule.mkLinearMap (Cech.cechSub f s)
        ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).obj M) m := by
  have h := awayTensorEquiv_tmul B (f i) M 1 m
  simp only [map_one] at h
  dsimp only [localOverlapEquiv, LinearEquiv.trans_apply]
  rw [localizedEquiv_mk, h, cechBaseChangeEquiv_mk]

private noncomputable def baseChangeAlpha
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons f} (X : FormalGlueing.ModuleGlueingDatum S f c)
    (i : Fin r) :
    LocalizedModule.Away (algebraMap B (S ⊗[R] B) (algebraMap R B (f i)))
        ((ModuleCat.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj X.generic) ≃ₗ[S ⊗[R] B]
      (S ⊗[R] B) ⊗[B]
        FormalGlueing.restrictFromAway (fun j ↦ algebraMap R B (f j)) i
          ((ModuleCat.extendScalars (awayMap B (f i))).obj (X.localPiece i)) :=
  genericLocalizationEquiv S B (f i) X.generic ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl (S ⊗[R] B) (S ⊗[R] B)) (X.alpha i) ≪≫ₗ
    (genericLocalTensorEquiv S B (f i) (X.localPiece i)).symm

private noncomputable def baseChangeAlphaIJ
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons f} (X : FormalGlueing.ModuleGlueingDatum S f c)
    (i j : Fin r) :
    Cech.cechMod (fun k ↦ algebraMap R B (f k))
        (FormalGlueing.restrictFromAway (fun k ↦ algebraMap R B (f k)) i
          ((ModuleCat.extendScalars (awayMap B (f i))).obj (X.localPiece i))) {j} ≃ₗ[B]
      Cech.cechMod (fun k ↦ algebraMap R B (f k))
        (FormalGlueing.restrictFromAway (fun k ↦ algebraMap R B (f k)) j
          ((ModuleCat.extendScalars (awayMap B (f j))).obj (X.localPiece j))) {i} :=
  localOverlapEquiv B f i (X.localPiece i) {j} ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl B B) (X.alphaIJ i j) ≪≫ₗ
    (localOverlapEquiv B f j (X.localPiece j) {i}).symm

private theorem baseChangeAlpha_commutes
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons f} (X : FormalGlueing.ModuleGlueingDatum S f c)
    (i : Fin r) (d) :
    genericLocalTensorEquiv S B (f i) (X.localPiece i) (baseChangeAlpha S B f X i d) =
      TensorProduct.map LinearMap.id (X.alpha i).toLinearMap
        (genericLocalizationEquiv S B (f i) X.generic d) := by
  simp only [baseChangeAlpha, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

private theorem baseChangeAlphaIJ_commutes
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons f} (X : FormalGlueing.ModuleGlueingDatum S f c)
    (i j : Fin r) (d) :
    localOverlapEquiv B f j (X.localPiece j) {i} (baseChangeAlphaIJ S B f X i j d) =
      TensorProduct.map LinearMap.id (X.alphaIJ i j).toLinearMap
        (localOverlapEquiv B f i (X.localPiece i) {j} d) := by
  simp only [baseChangeAlphaIJ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

private theorem pushoutTensorEquiv_naturality
    (R S B C : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] [Algebra S C] [Algebra B C]
    [IsScalarTower R S C] [IsScalarTower R B C] [Algebra.IsPushout R S B C]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (g : M →ₗ[S] N) :
    (pushoutTensorEquiv R S B C N).toLinearMap.comp ((g.baseChange C).restrictScalars B) =
      ((g.restrictScalars R).baseChange B).comp (pushoutTensorEquiv R S B C M).toLinearMap := by
  ext z
  obtain ⟨z, rfl⟩ := (pushoutTensorEquiv R S B C M).symm.surjective z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul b m =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.restrictScalars_apply,
      pushoutTensorEquiv_symm_tmul, LinearMap.baseChange_tmul, pushoutTensorEquiv_tmul]

private theorem localizationBaseChange_naturality
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (T : Submonoid A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) :
    (localizationBaseChange B T N).toLinearMap.comp
        (LinearMap.restrictScalars B
          (LocalizedModule.map (Algebra.algebraMapSubmonoid B T) (g.baseChange B))) =
      (((LocalizedModule.map T g).restrictScalars A).baseChange B).comp
        (localizationBaseChange B T M).toLinearMap := by
  let h := isLocalized_baseChange (B := B) T (LocalizedModule.mkLinearMap T N)
  apply IsLocalizedModule.ext (Algebra.algebraMapSubmonoid B T)
    (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid B T) (B ⊗[A] M))
    (IsLocalizedModule.map_units ((LocalizedModule.mkLinearMap T N).baseChange B))
  apply AlgebraTensorModule.ext
  intro b m
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, localizationBaseChange_mk]
  erw [LocalizedModule.map_mk]
  change localizationBaseChange B T N
    (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid B T) _ (b ⊗ₜ[A] g m)) = _
  rw [localizationBaseChange_mk]
  exact congrArg (TensorProduct.mk A B (LocalizedModule T N) b)
    (LocalizedModule.map_mk T g m 1).symm

end FormalGlueing

end
