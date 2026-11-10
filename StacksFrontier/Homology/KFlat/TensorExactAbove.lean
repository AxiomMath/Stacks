module

public import StacksFrontier.Homology.KFlat.Closure
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Complexes of flat modules whose tensor products are exact in high degrees

Let `C` be a cochain complex of flat `R`-modules, not necessarily bounded, and let `m` be an
integer such that for every `R`-module `M` the termwise tensor product `C ⊗_R M` has no
cohomology in degrees `> m`. Then for every `k > m` the cycles `Z^k(C)` are flat, so every good
truncation `τ_{≤ k} C` with `k > m` is a bounded-above complex of flat modules. Since `C` is the
colimit of these truncations, `C` is K-flat, and consequently every derived extension of
scalars is computed on `C` termwise.

The flatness of `Z^k` is the Tor-free form of dimension shifting: exactness of `C ⊗ M` at `k`
for every `M` makes `Im(d^k) ⊗ M → C^{k+1} ⊗ M` injective, so `C^{k+1} / Im(d^k)` is flat; then
`Im(d^k)` and `Z^k = Ker(d^k)` are kernels of surjections between flat modules.

## Main results

* `CochainComplex.KFlat.flat_cycles_of_rTensor_exact`: the cycles in degree `k` are flat.
* `CochainComplex.KFlat.flat_truncLE_X_of_rTensor_exact`: the good truncation `τ_{≤ k} C` has
  flat terms.
* `CochainComplex.KFlat.kFlat_of_rTensor_exact` and
  `CochainComplex.KFlat.kFlat_of_isZero_homology_tensorComplex`: `C` is K-flat.
* `TotalDerivedExtensionScalars.comparison_isIso_of_isZero_homology_tensorComplex`, in the
  namespace `CochainComplex.DerivedExtensionScalars`: derived extension of scalars is computed
  termwise on `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w wR wA

namespace CochainComplex.KFlat

/-- The kernel of a surjective linear map between flat modules is flat. -/
@[ega "0 20.6.21" "more general"]
theorem flat_ker_of_surjective {R : Type u} [CommRing R] {A B : Type v} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [Module.Flat R A] [Module.Flat R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) : Module.Flat R (LinearMap.ker f) := by
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker f).subtype) (ModuleCat.ofHom f) (by
      ext x
      exact x.2)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2
        (LinearMap.exact_subtype_ker_map f)
      mono_f := (ModuleCat.mono_iff_injective _).2 (LinearMap.ker f).injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).2 hf }
  have : Module.Flat R S.X₂ := inferInstanceAs (Module.Flat R A)
  have : Module.Flat R S.X₃ := inferInstanceAs (Module.Flat R B)
  exact StacksDraft.TorAmplitude.flat_of_shortExact_left S hS

variable {R : Type u} [CommRing R]

/-- A submodule equal to the kernel of a surjection between flat modules is flat. -/
private theorem flat_of_ker_eq {A B : Type (max u v)} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Flat R A] [Module.Flat R B] (f : A →ₗ[R] B)
    (hf : Function.Surjective f) (N : Submodule R A) (hN : LinearMap.ker f = N) :
    Module.Flat R N := by
  subst hN
  exact flat_ker_of_surjective f hf

/-- **The cycles are flat.** Let `C` be a complex of flat `R`-modules and `k` a degree such that
for every `R`-module `M` the tensored complex `C ⊗ M` is exact at `k`. Then `Z^k(C)` is flat. -/
theorem flat_cycles_of_rTensor_exact (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (k : ℤ)
    (hk : ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M],
      Function.Exact (LinearMap.rTensor M (C.d (k - 1) k).hom)
        (LinearMap.rTensor M (C.d k (k + 1)).hom)) :
    Module.Flat R (C.cycles k) := by
  set g := (C.d k (k + 1)).hom with hg
  have hinj : ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M],
      Function.Injective (LinearMap.rTensor M (LinearMap.range g).subtype) := by
    intro M _ _
    refine StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact
      (C.d (k - 1) k).hom g ?_ M (hk M)
    rw [hg, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero]
  have hQ : Module.Flat R ((C.X (k + 1) : Type (max u v)) ⧸ LinearMap.range g) :=
    StacksDraft.TorAmplitude.Termwise.flat_quotient_of_rTensor_subtype_injective
      (LinearMap.range g) hinj
  have hrange : Module.Flat R (LinearMap.range g) :=
    flat_of_ker_eq (LinearMap.range g).mkQ (Submodule.mkQ_surjective _) _ (Submodule.ker_mkQ _)
  have hker : Module.Flat R (LinearMap.ker g) :=
    flat_of_ker_eq g.rangeRestrict g.surjective_rangeRestrict _ (LinearMap.ker_rangeRestrict g)
  let e : C.cycles k ≅ ModuleCat.of R (LinearMap.ker g) :=
    (C.cyclesIsKernel k (k + 1) (by simp)).conePointUniqueUpToIso (kernelIsKernel _) ≪≫
      ModuleCat.kernelIsoKer (C.d k (k + 1))
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- The good truncation `τ_{≤ k} C` of a complex of flat modules whose cycles in degree `k` are
flat has flat terms. -/
theorem flat_truncLE_X (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (k : ℤ) [Module.Flat R (C.cycles k)] (i : ℤ) :
    Module.Flat R ((C.truncLE k).X i) := by
  rcases lt_trichotomy i k with hi | hi | hi
  · exact Module.Flat.of_linearEquiv (C.truncLEXIso k i hi).toLinearEquiv
  · subst i
    exact Module.Flat.of_linearEquiv (C.truncLEXIsoCycles k).toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.1 ((C.truncLE k).isZero_of_isStrictlyLE k i hi)
    infer_instance

/-- The good truncation `τ_{≤ k} C` has flat terms as soon as `C` does and `C ⊗ M` is exact at
`k` for every `R`-module `M`. -/
theorem flat_truncLE_X_of_rTensor_exact (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (k : ℤ)
    (hk : ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M],
      Function.Exact (LinearMap.rTensor M (C.d (k - 1) k).hom)
        (LinearMap.rTensor M (C.d k (k + 1)).hom)) (i : ℤ) :
    Module.Flat R ((C.truncLE k).X i) := by
  have := flat_cycles_of_rTensor_exact C k hk
  exact flat_truncLE_X C k i

/-- The map `τ_{≤ n + k} L ⟶ τ_{≤ n + k + 1} L` of the tower of good truncations of `L` starting
in degree `n`. -/
def truncLEFromMapSucc {C : Type*} [Category* C] [Abelian C] (L : CochainComplex C ℤ) (n : ℤ)
    (k : ℕ) : L.truncLE (n + k) ⟶ L.truncLE (n + (k + 1 : ℕ)) := by
  haveI : (L.truncLE (n + k)).IsStrictlyLE (n + (k + 1 : ℕ)) :=
    CochainComplex.isStrictlyLE_of_le _ (n + k) _ (by omega)
  exact inv ((L.truncLE (n + k)).ιTruncLE (n + (k + 1 : ℕ))) ≫
    CochainComplex.truncLEMap (L.ιTruncLE (n + k)) (n + (k + 1 : ℕ))

/-- The transition maps of the tower of good truncations commute with the inclusions into `L`. -/
lemma truncLEFromMapSucc_comp_ι {C : Type*} [Category* C] [Abelian C] (L : CochainComplex C ℤ)
    (n : ℤ) (k : ℕ) :
    truncLEFromMapSucc L n k ≫ L.ιTruncLE (n + (k + 1 : ℕ)) = L.ιTruncLE (n + k) := by
  dsimp [truncLEFromMapSucc]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

/-- The tower `k ↦ τ_{≤ n + k} L` of good truncations of `L` starting in degree `n`. -/
def truncLEFromSequence {C : Type*} [Category* C] [Abelian C] (L : CochainComplex C ℤ) (n : ℤ) :
    ℕ ⥤ CochainComplex C ℤ :=
  Functor.ofSequence (truncLEFromMapSucc L n)

/-- The cocone on `truncLEFromSequence L n` with vertex `L`. -/
def truncLEFromCocone {C : Type*} [Category* C] [Abelian C] (L : CochainComplex C ℤ) (n : ℤ) :
    Cocone (truncLEFromSequence L n) :=
  Cocone.mk L
    (NatTrans.ofSequence (F := truncLEFromSequence L n) (G := (Functor.const ℕ).obj L)
      (fun k => L.ιTruncLE (n + k))
      (fun k => by
        dsimp only [truncLEFromSequence]
        rw [Functor.ofSequence_map_homOfLE_succ]
        exact (truncLEFromMapSucc_comp_ι L n k).trans (Category.comp_id _).symm))

/-- A complex is the colimit of its good truncations `τ_{≤ n + k}`, `k ∈ ℕ`. -/
def truncLEFromCocone_isColimit {C : Type*} [Category* C] [Abelian C] (L : CochainComplex C ℤ)
    (n : ℤ) : IsColimit (truncLEFromCocone L n) := by
  apply isColimit_of_eventually_iso_components
  intro i
  refine ⟨(i + 1 - n).toNat, fun k hk => ?_⟩
  have := Int.self_le_toNat (i + 1 - n)
  exact CochainComplex.isIso_ιTruncLE_f_of_lt L (n + (k : ℤ)) i (by omega)

/-- **K-flatness from exactness of the tensored complexes in high degrees.** A complex `C` of
flat `R`-modules such that `C ⊗ M` is exact in every degree `> m`, for every `R`-module `M`, is
K-flat: it is the colimit of its good truncations `τ_{≤ k} C`, `k > m`, which are bounded above
with flat terms. -/
theorem kFlat_of_rTensor_exact (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (m : ℤ)
    (hC : ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M] (k : ℤ), m < k →
      Function.Exact (LinearMap.rTensor M (C.d (k - 1) k).hom)
        (LinearMap.rTensor M (C.d k (k + 1)).hom)) :
    C.KFlat := by
  have hseq : ∀ k : ℕ, ((truncLEFromSequence C (m + 1)).obj k).KFlat := by
    intro k
    change (C.truncLE (m + 1 + k)).KFlat
    have : ∀ i, Module.Flat R ((C.truncLE (m + 1 + k)).X i) :=
      flat_truncLE_X_of_rTensor_exact C (m + 1 + k)
        (fun M _ _ => hC M (m + 1 + k) (by omega))
    exact kFlat_of_flat (C.truncLE (m + 1 + k)) (m + 1 + k)
  exact kFlat_of_iso ((colimit.isColimit _).coconePointUniqueUpToIso
    (truncLEFromCocone_isColimit C (m + 1))) (kFlat_colimit.{u, 0, 0, v} _ hseq)

/-- **K-flatness from vanishing of the cohomology of `C ⊗ M` in high degrees.** A complex `C` of
flat `R`-modules such that, for every `R`-module `M`, the termwise tensor product `C ⊗_R M` has
no cohomology in degrees `> m` is K-flat. -/
theorem kFlat_of_isZero_homology_tensorComplex (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (m : ℤ)
    (hC : ∀ (M : ModuleCat.{max u v} R) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex C M).homology k)) :
    C.KFlat := by
  refine kFlat_of_rTensor_exact C m fun M _ _ k hk => ?_
  have he := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hC (ModuleCat.of R M) k hk)
  rwa [HomologicalComplex.exactAt_iff' _ (k - 1) k (k + 1) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at he

end CochainComplex.KFlat

namespace CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars

/-- **Derived extension of scalars is computed termwise** on a complex `C` of flat `R`-modules
such that, for every `R`-module `M`, the termwise tensor product `C ⊗_R M` has no cohomology in
degrees `> m`: the comparison of `D` at `C` is an isomorphism, `C` being K-flat. No
boundedness of `C` is needed. -/
theorem comparison_isIso_of_isZero_homology_tensorComplex
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] {f : R →+* A}
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]
    (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f)
    (C : CochainComplex (ModuleCat.{max v u w} R) ℤ) [∀ i, Module.Flat R (C.X i)] (m : ℤ)
    (hC : ∀ (M : ModuleCat.{max v u w} R) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex C M).homology k)) :
    IsIso (D.comparison.app C) :=
  D.comparison_isIso_of_kFlat C
    (CochainComplex.KFlat.kFlat_of_isZero_homology_tensorComplex.{u, max v w} C m hC)

end CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars
