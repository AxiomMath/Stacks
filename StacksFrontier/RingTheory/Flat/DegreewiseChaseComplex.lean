module

public import StacksFrontier.RingTheory.Flat.DegreewiseChase

/-!
# The degreewise chase read on a complex

`StacksFrontier.RingTheory.Flat.DegreewiseChase` states the source's chase on three consecutive
modules and two maps: given `M₀ → M₁ → M₂` of finitely generated modules over a Noetherian
`R`-algebra `S`, with `M₂` flat over `R`, exactness in the middle after `⊗_R κ(𝔭)` at every prime
`𝔭` of `R` gives exactness in the middle after `⊗_R N` for *every* `R`-module `N`.

This file packages that at one degree of a cochain complex `E^•` of `S`-modules, which is the
shape the consumers have: the cokernel `Q^n` of `E^{n-1} → E^n` is built here, as the quotient of
`E^n` by the range of the differential, together with the three maps the chase asks for.  Nothing
about the complex beyond the single degree is used — no boundedness, no hypothesis in the other
degrees — because the chase itself is a three-term statement.

## Main results

* `StacksDraft.DegreewiseChase.exact_rTensor_of_exact_rTensor_residueField_complex` — the chase at
  one degree of a complex.

## Implementation notes

The `R`-module structure on the terms of `E^•` is the one `ModuleCat.restrictScalars` puts there,
so that the hypotheses and the conclusion are stated at the complex
`(ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _ |>.obj E`, which is the
complex of `R`-modules the chase runs on and the one
`StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor` reads.  Inside
the proof the same structure is installed on the carriers, where it is the scalar restriction
along `algebraMap R S` and makes `R → S → E^n` a tower.

## References

* [Stacks Project, Tag 00ME](https://stacks.math.columbia.edu/tag/00ME)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
-/

@[expose] public section

open CategoryTheory

universe u

namespace StacksDraft.DegreewiseChase

noncomputable section

/-- Scalar restriction along `R → S`, on complexes: the complex of `R`-modules underlying a
complex of `S`-modules, which is the one the degreewise chase runs on. -/
abbrev restrictBase (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (ModuleCat.restrictScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- **The degreewise chase at one degree of a complex.**  Let `S` be a Noetherian `R`-algebra and
`E^•` a cochain complex of `S`-modules whose term in degree `n` is a finite `S`-module and whose
term in degree `n + 1` is flat over `R`.  If `E^{n-1} → E^n → E^{n+1}` is exact in the middle
after `⊗_R κ(𝔭)` for every prime `𝔭` of `R`, then it is exact in the middle after `⊗_R N` for
every `R`-module `N`.

This is `StacksDraft.DegreewiseChase.flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField`
with the cokernel `Q^n = E^n / d(E^{n-1})` and its two maps supplied: the quotient map is
surjective with the differential as its kernel, and the next differential factors through it
because `d ∘ d = 0`.  Only the flatness of `E^{n+1}` is used, and only the finiteness of `E^n`:
the chase bounds the cokernel, which is a quotient of `E^n` sitting inside `E^{n+1}`. -/
theorem exact_rTensor_of_exact_rTensor_residueField_complex
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S]
    (E : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) [Module.Finite S (E.X n)]
    (hflat : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj (E.X (n + 1))))
    (hres : ∀ (p : Ideal R) [p.IsPrime],
      Function.Exact
        (LinearMap.rTensor (ResidueFieldAt R p)
          (((restrictBase R S).obj E).d (n - 1) n).hom)
        (LinearMap.rTensor (ResidueFieldAt R p)
          (((restrictBase R S).obj E).d n (n + 1)).hom))
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Exact (LinearMap.rTensor N (((restrictBase R S).obj E).d (n - 1) n).hom)
      (LinearMap.rTensor N (((restrictBase R S).obj E).d n (n + 1)).hom) := by
  let : Module R (E.X (n - 1)) :=
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (E.X (n - 1))).isModule
  let : Module R (E.X n) :=
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (E.X n)).isModule
  let : Module R (E.X (n + 1)) :=
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (E.X (n + 1))).isModule
  have : IsScalarTower R S (E.X (n - 1)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R S (E.X n) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R S (E.X (n + 1)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R (E.X (n + 1)) := hflat
  set f : (E.X (n - 1)) →ₗ[S] (E.X n) := (E.d (n - 1) n).hom with hf
  set g : (E.X n) →ₗ[S] (E.X (n + 1)) := (E.d n (n + 1)).hom with hg
  have hc : Function.Surjective (Submodule.mkQ (LinearMap.range f)) :=
    Submodule.mkQ_surjective _
  have : Module.Finite S ((E.X n) ⧸ LinearMap.range f) := .of_surjective _ hc
  have hfc : Function.Exact f (Submodule.mkQ (LinearMap.range f)) := by
    intro b
    simp [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hgf : LinearMap.range f ≤ LinearMap.ker g := by
    rw [LinearMap.range_le_ker_iff]
    have hdd := E.d_comp_d (n - 1) n (n + 1)
    ext x
    exact congrArg (fun φ => ModuleCat.Hom.hom φ x) hdd
  have hu : (Submodule.liftQ (LinearMap.range f) g hgf) ∘ₗ
      (Submodule.mkQ (LinearMap.range f)) = g := Submodule.liftQ_mkQ _ _ _
  have key := flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField
    (R := R) (S := S) (f := f) (g := g)
    (c := Submodule.mkQ (LinearMap.range f))
    (u := Submodule.liftQ (LinearMap.range f) g hgf) hc hfc hu hres
  exact key.2 N

end

end StacksDraft.DegreewiseChase

end
