module

public import StacksFrontier.Homology.ExtendScalars.BaseChangeCancellation
public import StacksFrontier.Homology.ExtendScalars.HomologyBaseChange
public import StacksFrontier.RingTheory.Flat.DegreewiseChaseComplex

/-!
# The cycles of a complex base changed along the left coprojection

Let `R → S` be a ring map with `S` Noetherian, let `R → R'` be any ring map and let `E^•` be a
cochain complex of `S`-modules whose terms are flat over `R`.  Extension of scalars is a left
adjoint, so it preserves cokernels; the one thing it does not do for free is base change the
cycles, which are a kernel.  The degreewise chase of [stacks 0E2F] (2) supplies exactly that in
degree `n`: the cokernel of `E^n → E^{n+1}` is `R`-flat, so `Z^n ⊗_R R'` is the kernel of
`E^n ⊗_R R' → E^{n+1} ⊗_R R'`, which says that
`StacksDraft.HomologyBaseChange.cyclesComparison` along the left coprojection
`S → S ⊗_R R'` is an isomorphism.

## Main results

* `StacksDraft.DegreewiseChase.isIso_cyclesComparison_includeLeft` -- the comparison on
  degree-`n` cycles for the termwise extension of scalars along `S → S ⊗_R R'` is an
  isomorphism, under the residue-field exactness hypothesis of the chase one degree up.

## Implementation notes

The `R`-module structure on the terms of `E^•` and on its cycles is the one
`ModuleCat.restrictScalars` puts there, installed on the carriers so that `R → S → E^n` is a
tower; this is the structure both halves of the chase read.

The crossing from `⊗_R R'` to extension of scalars along `S → S ⊗_R R'` is
`StacksDraft.BaseChangeCancellation.cancelAddEquiv`, which is natural, so a ladder carries both
the injectivity and the exactness over.  Only the additive structure survives the crossing --
the two sides are modules over different rings -- and that is all that is needed, injectivity
and exactness being statements about the underlying additive groups.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 00ME](https://stacks.math.columbia.edu/tag/00ME)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe u

namespace StacksDraft.DegreewiseChase

noncomputable section

/-- A ladder whose two vertical maps are additive equivalences reflects injectivity. -/
private theorem injective_of_ladder_addEquiv {X₁ X₂ Y₁ Y₂ : Type*}
    [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup Y₁] [AddCommGroup Y₂]
    (e₁ : X₁ ≃+ Y₁) (e₂ : X₂ ≃+ Y₂) {f : X₁ →+ X₂} {g : Y₁ →+ Y₂}
    (comm : g.comp e₁.toAddMonoidHom = e₂.toAddMonoidHom.comp f)
    (hf : Function.Injective f) : Function.Injective g := by
  have key : ∀ x : X₁, g (e₁ x) = e₂ (f x) := fun x => by
    simpa using DFunLike.congr_fun comm x
  intro a b hab
  refine e₁.symm.injective (hf (e₂.injective ?_))
  rw [← key, ← key]
  simpa using hab

/-- The inclusion of the degree-`n` cycles has the kernel of the degree-`n` differential as its
image: the cycles are that kernel, read through `HomologicalComplex.liftCycles`. -/
private theorem exact_iCycles_d {S : Type u} [CommRing S]
    (E : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    Function.Exact (E.iCycles n) (E.d n (n + 1)) := by
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := by simp
  intro x
  refine ⟨fun hx => ?_, ?_⟩
  · have hk : ModuleCat.ofHom (LinearMap.toSpanSingleton S (E.X n) x) ≫ E.d n (n + 1) = 0 :=
      ModuleCat.hom_ext (LinearMap.ext_ring (by simpa using hx))
    refine ⟨E.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton S (E.X n) x)) (n + 1)
      hnext hk (1 : S), ?_⟩
    rw [← ModuleCat.comp_apply, E.liftCycles_i _ (n + 1) hnext hk]
    simp
  · rintro ⟨y, rfl⟩
    rw [← ModuleCat.comp_apply, E.iCycles_d n (n + 1)]
    simp

/-- **The comparison on cycles is an isomorphism once the cycles are the kernel after base
change.**  If the base change of the inclusion of the degree-`n` cycles is injective with the
kernel of the base-changed differential as its image, then
`StacksDraft.HomologyBaseChange.cyclesComparison` is an isomorphism in degree `n`.

Both sides sit over `(X^n)' = B' ⊗_B X^n` by monomorphisms and the triangle commutes, so the
comparison inherits injectivity from the base change of the inclusion of the cycles and
surjectivity from its image being the whole kernel. -/
private theorem isIso_cyclesComparison_of_exact {B B' : Type u} [CommRing B] [CommRing B']
    (φ : B →+* B') (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ)
    (hinj : Function.Injective ((ModuleCat.extendScalars φ).map (X.iCycles n)))
    (hex : Function.Exact ((ModuleCat.extendScalars φ).map (X.iCycles n))
      ((ModuleCat.extendScalars φ).map (X.d n (n + 1)))) :
    IsIso (HomologyBaseChange.cyclesComparison φ X n) := by
  have htri := fun x => congr($(HomologyBaseChange.cyclesComparison_iCycles φ X n) x)
  simp only [ModuleCat.comp_apply] at htri
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => hinj ?_, fun y => ?_⟩
  · rw [← htri a, ← htri b, hab]
  · have hy : ((HomologyBaseChange.extendComplex φ).obj X).d n (n + 1)
        (((HomologyBaseChange.extendComplex φ).obj X).iCycles n y) = 0 := by
      simpa using congr($(((HomologyBaseChange.extendComplex φ).obj X).iCycles_d n (n + 1)) y)
    obtain ⟨x, hx⟩ := (hex _).mp hy
    refine ⟨x, (ModuleCat.mono_iff_injective
      (((HomologyBaseChange.extendComplex φ).obj X).iCycles n)).1 inferInstance ?_⟩
    rw [htri x, hx]

/-- **The degree-`n` cycles base change along the left coprojection `S → S ⊗_R R'`.**  Let `S` be
a Noetherian `R`-algebra, let `R'` be any `R`-algebra and let `E^•` be a cochain complex of
`S`-modules whose terms are flat over `R` and whose term in degree `n + 1` is a finite
`S`-module.  If `E^n → E^{n+1} → E^{n+2}` stays exact in the middle after `⊗_R κ(𝔭)` for every
prime `𝔭` of `R`, then the canonical comparison
`(S ⊗_R R') ⊗_S Z^n(E^•) ⟶ Z^n((S ⊗_R R') ⊗_S E^•)` is an isomorphism.

The residue-field hypothesis is the chase of [stacks 0E2F] (2) one degree up: by
`StacksDraft.DegreewiseChase.flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField` it
makes the cokernel `Q^{n+1} = E^{n+1}/d(E^n)` flat over `R`, and then
`StacksDraft.DegreewiseChase.injective_and_exact_rTensor_ker_of_flat_cokernel` at the four-term
sequence `0 → Z^n → E^n → E^{n+1} → Q^{n+1} → 0` says that `Z^n ⊗_R R'` is the kernel of
`E^n ⊗_R R' → E^{n+1} ⊗_R R'`.  That is the statement wanted, read through the cancellation
`(S ⊗_R R') ⊗_S M = M ⊗_R R'`. -/
theorem isIso_cyclesComparison_includeLeft
    (R S R' : Type u) [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
    [IsNoetherianRing S]
    (E : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    [Module.Finite S (E.X (n + 1))]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (E.X i)))
    (hres : ∀ (p : Ideal R) [p.IsPrime],
      Function.Exact
        (LinearMap.rTensor (ResidueFieldAt R p)
          (((restrictBase R S).obj E).d n (n + 1)).hom)
        (LinearMap.rTensor (ResidueFieldAt R p)
          (((restrictBase R S).obj E).d (n + 1) (n + 2)).hom)) :
    IsIso (HomologyBaseChange.cyclesComparison
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] R') E n) := by
  let : ∀ M : ModuleCat S, Module R M :=
    fun M => ((ModuleCat.restrictScalars (algebraMap R S)).obj M).isModule
  have : ∀ M : ModuleCat S, IsScalarTower R S M :=
    fun _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R (E.X (n + 1)) := hflat (n + 1)
  have : Module.Flat R (E.X (n + 2)) := hflat (n + 2)
  have hgf : LinearMap.range (E.d n (n + 1)).hom ≤
      LinearMap.ker (E.d (n + 1) (n + 2)).hom := by
    rw [LinearMap.range_le_ker_iff]
    ext x
    exact congrArg (fun ψ => ModuleCat.Hom.hom ψ x) (E.d_comp_d n (n + 1) (n + 2))
  have hc : Function.Surjective (Submodule.mkQ (LinearMap.range (E.d n (n + 1)).hom)) :=
    Submodule.mkQ_surjective _
  have : Module.Finite S ((E.X (n + 1)) ⧸ LinearMap.range (E.d n (n + 1)).hom) :=
    Module.Finite.of_surjective (Submodule.mkQ _) hc
  have hfc : Function.Exact (E.d n (n + 1)).hom
      (Submodule.mkQ (LinearMap.range (E.d n (n + 1)).hom)) := by
    intro b
    simp [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hu : (Submodule.liftQ (LinearMap.range (E.d n (n + 1)).hom)
        (E.d (n + 1) (n + 2)).hom hgf) ∘ₗ
      (Submodule.mkQ (LinearMap.range (E.d n (n + 1)).hom)) = (E.d (n + 1) (n + 2)).hom :=
    Submodule.liftQ_mkQ _ _ _
  have key : Module.Flat R ((E.X (n + 1)) ⧸ LinearMap.range (E.d n (n + 1)).hom) ∧
      ∀ (N : Type u) [AddCommGroup N] [Module R N],
        Function.Exact (LinearMap.rTensor N (((E.d n (n + 1)).hom).restrictScalars R))
          (LinearMap.rTensor N (((E.d (n + 1) (n + 2)).hom).restrictScalars R)) :=
    flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField (R := R) (S := S)
      (f := (E.d n (n + 1)).hom) (g := (E.d (n + 1) (n + 2)).hom)
      (c := Submodule.mkQ (LinearMap.range (E.d n (n + 1)).hom))
      (u := Submodule.liftQ _ (E.d (n + 1) (n + 2)).hom hgf) hc hfc hu hres
  have := key.1
  obtain ⟨hinj, hex⟩ := injective_and_exact_rTensor_ker_of_flat_cokernel (R := R)
    (z := ((E.iCycles n).hom).restrictScalars R)
    (g := ((E.d n (n + 1)).hom).restrictScalars R)
    (w := (Submodule.mkQ (LinearMap.range (E.d n (n + 1)).hom)).restrictScalars R)
    ((ModuleCat.mono_iff_injective (E.iCycles n)).1 inferInstance) (exact_iCycles_d E n) hfc
    hc R'
  refine isIso_cyclesComparison_of_exact _ E n
    (injective_of_ladder_addEquiv _ _
      (BaseChangeCancellation.cancelAddEquiv_symm_naturality (R := R) (R' := R')
        (E.iCycles n)) hinj)
    ((Function.Exact.iff_of_ladder_addEquiv
      (BaseChangeCancellation.cancelAddEquiv (R := R) (R' := R') (E.cycles n)).symm
      (BaseChangeCancellation.cancelAddEquiv (R := R) (R' := R') (E.X n)).symm
      (BaseChangeCancellation.cancelAddEquiv (R := R) (R' := R') (E.X (n + 1))).symm
      (BaseChangeCancellation.cancelAddEquiv_symm_naturality (E.iCycles n))
      (BaseChangeCancellation.cancelAddEquiv_symm_naturality (E.d n (n + 1)))).mpr hex)

end

end StacksDraft.DegreewiseChase

end
