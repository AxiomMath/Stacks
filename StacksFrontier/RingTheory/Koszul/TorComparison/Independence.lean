module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.RingTheory.Koszul.TorComparison.Resolution
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul complex computes `Tor`, and flat resolutions are interchangeable

Two things make a complex usable as a vehicle for computing `Tor^R_*(-, N)`: it must be a
resolution of the object in question, and tensoring with `N` must only see its quasi-isomorphism
class. The second is K-flatness: a bounded above complex of flat modules is K-flat
([Stacks, Tag 064K]), and a quasi-isomorphism between K-flat complexes stays a
quasi-isomorphism after termwise tensoring with a module. So any two bounded above flat
resolutions of the same object, and any quasi-isomorphism between them, give the same homology
after tensoring — the independence of `Tor` of the chosen flat resolution.

The Koszul complex of a sequence is such a complex. Read as a cochain complex concentrated in
nonpositive degrees via `ComplexShape.embeddingDownNat`, its terms `⋀ⁿ(Rʳ)` are finite free and
it is bounded above, hence K-flat; and when the sequence is Koszul-regular the augmentation onto
`R ⧸ (f₁, …, f_r)` is a quasi-isomorphism. Thus for a Koszul-regular sequence the Koszul complex
is a free resolution computing `Tor^R_*(R ⧸ (f₁, …, f_r), -)`, and comparing it with any other
bounded above flat resolution loses no information.

## Main definitions

* `Koszul.seqCochain`: the Koszul complex of `f₁, …, f_r` as a cochain complex of `R`-modules
  concentrated in degrees `≤ 0`.
* `Koszul.seqCochainAugmentation`: its augmentation onto `(R ⧸ (f₁, …, f_r))[0]`.

## Main results

* `Koszul.quasiIso_tensorModuleRight_map_of_flat`: **independence of the flat resolution.** A
  quasi-isomorphism between bounded above complexes of flat `R`-modules remains a
  quasi-isomorphism after termwise tensoring with any `R`-module.
* `Koszul.seqCochain_kFlat`: the Koszul cochain complex is K-flat.
* `Koszul.seqCochainAugmentation_quasiIso`: for a Koszul-regular sequence the Koszul cochain
  complex is a resolution of `R ⧸ (f₁, …, f_r)`.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-! ### Independence of the flat resolution -/

/-- **Independence of `Tor` of the chosen flat resolution.** A quasi-isomorphism between two
bounded above complexes of flat `R`-modules remains a quasi-isomorphism after termwise
tensoring with an `R`-module `N`. Consequently any two bounded above flat resolutions of the
same object, compared by a quasi-isomorphism, compute the same `Tor^R_*(-, N)`.

This is `StacksDraft.TorAmplitude.quasiIso_tensorModuleRight_map` fed by
[Stacks, Tag 064K] (`CochainComplex.KFlat.kFlat_of_flat`), which turns the two boundedness and
flatness hypotheses into K-flatness. -/
theorem quasiIso_tensorModuleRight_map_of_flat (N : ModuleCat.{u} R)
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (dX dY : ℤ)
    [X.IsStrictlyLE dX] [Y.IsStrictlyLE dY]
    (hX : ∀ i : ℤ, Module.Flat R (X.X i)) (hY : ∀ i : ℤ, Module.Flat R (Y.X i))
    (π : X ⟶ Y) [QuasiIso π] :
    QuasiIso (((StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).map π) := by
  have hXk : X.KFlat := CochainComplex.KFlat.kFlat_of_flat X dX
  have hYk : Y.KFlat := CochainComplex.KFlat.kFlat_of_flat Y dY
  exact StacksDraft.TorAmplitude.quasiIso_tensorModuleRight_map N π hXk hYk

/-! ### The Koszul complex as a bounded above cochain complex -/

/-- The Koszul complex `K_•(f₁, …, f_r)` read as a cochain complex of `R`-modules, with
`⋀ⁿ(Rʳ)` placed in cohomological degree `-n`; it is concentrated in degrees `≤ 0`. -/
def seqCochain (f : Fin r → R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat

/-- The Koszul cochain complex is strictly concentrated in degrees `≤ 0`. -/
instance instIsStrictlyLESeqCochain (f : Fin r → R) : (seqCochain f).IsStrictlyLE 0 :=
  inferInstanceAs
    (CochainComplex.IsStrictlyLE
      ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat) 0)

/-- Every term of the Koszul cochain complex is a projective `R`-module. -/
instance instProjectiveSeqCochainX (f : Fin r → R) (n : ℤ) :
    Projective ((seqCochain f).X n) :=
  inferInstanceAs
    (Projective
      (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X n))

/-- Every term of the Koszul cochain complex is a flat `R`-module: in the degrees it occupies it
is a term of the Koszul complex, which is free, and elsewhere it is zero. -/
instance instFlatSeqCochainX (f : Fin r → R) (n : ℤ) :
    Module.Flat R ((seqCochain f).X n) :=
  have : Projective ((seqCochain f).X n) := inferInstance
  inferInstance

/-- **The Koszul complex is K-flat.** It is bounded above and its terms are free, hence flat, so
[Stacks, Tag 064K] applies. -/
theorem seqCochain_kFlat (f : Fin r → R) : (seqCochain f).KFlat :=
  CochainComplex.KFlat.kFlat_of_flat (seqCochain f) 0

/-! ### The Koszul resolution as a cochain complex -/

/-- The augmentation of the Koszul cochain complex onto `R ⧸ (f₁, …, f_r)` placed in
cohomological degree `0`. -/
def seqCochainAugmentation (f : Fin r → R) :
    seqCochain f ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) :=
  HomologicalComplex.extendMap (augmentation f) ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) 0 0 (by simp)).hom

/-- **The Koszul complex of a Koszul-regular sequence is a bounded above free resolution of
`R ⧸ (f₁, …, f_r)`**: its augmentation `Koszul.seqCochainAugmentation` is a quasi-isomorphism.
Combined with `Koszul.seqCochain_kFlat` and `Koszul.quasiIso_tensorModuleRight_map_of_flat`, this
is what lets it compute `Tor^R_*(R ⧸ (f₁, …, f_r), -)`. -/
@[sga "3 III 4.6.1" "partial", sga "6 VII 1.2" "partial", sga "6 VIII 1.4" "partial"]
theorem seqCochainAugmentation_quasiIso (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) :
    QuasiIso (seqCochainAugmentation f) := by
  have : QuasiIso (augmentation f) := augmentation_quasiIso f hf
  have h₁ : QuasiIso
      (HomologicalComplex.extendMap (augmentation f) ComplexShape.embeddingDownNat) :=
    inferInstance
  have h₂ : QuasiIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (0 : ℕ) (0 : ℤ)
        (by simp)).hom :=
    quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h₁) (hφ' := h₂) _ _

end Koszul

end
