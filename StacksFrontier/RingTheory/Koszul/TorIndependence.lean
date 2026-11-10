module

public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# Tor independence of a Koszul-regular quotient

Let `R` be a commutative ring, let `f₁, …, f_r ∈ R` be a Koszul-regular sequence, and let
`C = R ⧸ (f₁, …, f_r)`. For an `R`-algebra `S`, the Koszul complex of `f` is a free resolution of
`C`, so `Tor_*^R(C, S)` is the Koszul homology `H_*(K_•(f) ⊗_R S)`
(`Koszul.torIsoHomologySeqComplexTensor`). Consequently `C` and `S` are Tor independent over `R`
— Tag 0660, `RingTheory.TorIndependence.TorIndependent` — as soon as the images
`f₁, …, f_r` of the sequence in `S` are again Koszul-regular, now as a sequence in `S`.

That last implication is the only content: the Koszul complex of the images is the base change
of the Koszul complex of `f`, so its homology computed over `S` is the Koszul homology of `f`
with coefficients in `S`, which is what Koszul-regularity *on* `S` of Tag 062E asks to vanish.
No flatness is involved: the comparison is a degreewise isomorphism of complexes, not a
base-change spectral sequence.

## Main results

* `RingTheory.TorIndependence.TorIndependent.symm`: Tor independence of rings in one universe is
  symmetric, by the balancing of Tag 00M3.
* `Koszul.isKoszulRegularOn_of_isKoszulRegular_map`: if the images of `f₁, …, f_r` in an
  `R`-algebra `S` form a Koszul-regular sequence of `S`, then `f₁, …, f_r` is Koszul-regular on
  `S` as an `R`-module.
* `Koszul.torIndependent_of_isKoszulRegular_map`: **a quotient of `R` by a Koszul-regular
  sequence is Tor independent of any `R`-algebra in which the sequence stays Koszul-regular.**

## Implementation notes

`Koszul.isKoszulRegularOn_iff_isZero_tor` is stated for `CategoryTheory.Tor'`, the derived
functor in the *first* variable, which is the one the Koszul resolution of the quotient computes;
`RingTheory.TorIndependence.TorIndependent` is stated for `CategoryTheory.Tor`, derived in the
second variable. The two are matched by the balancing isomorphism `Tor_iso_Tor'` of Tag 00M1, and
the resulting vanishing is for `Tor_i^R(C, S)`, so the conclusion has the quotient in the first
slot; `RingTheory.TorIndependence.TorIndependent.symm` is what puts it in the second.

Not to be confused with `StacksFrontier/RingTheory/Koszul/TorComparison/Independence.lean`, whose
"independence" is that of `Tor` of the chosen flat resolution; the independence here is Tor
independence of two algebras over their base, Tag 0660.

The degreewise comparison of `K_•(f) ⊗_R S` with the restriction of scalars of `K_•(f₁, …, f_r)`
over `S` is assembled from `KoszulC.extPow_baseChange_natEquiv`, which identifies
`S ⊗_R ⋀ⁿ(Rʳ)` with `⋀ⁿ(Sʳ)`, and `KoszulC.d_baseChange_comm`, which says that this
identification intertwines the two contraction differentials — the computation
`seqDual (φ ∘ f) = φ ∘ seqDual f`.

## References

* [Stacks Project, Tag 062E](https://stacks.math.columbia.edu/tag/062E)
* [Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660)
* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
* [Stacks Project, Tag 00M3](https://stacks.math.columbia.edu/tag/00M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

/-- **Tor independence is symmetric.** For rings in a common universe this is the balancing of
Tag 00M3, `Stacks.Tor.DoubleComplex.tor_symm_canonically_iso`: the two bifunctors
`(M, N) ↦ Tor_i^R(M, N)` and `(M, N) ↦ Tor_i^R(N, M)` are isomorphic. -/
theorem TorIndependent.symm {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (h : TorIndependent R A B) : TorIndependent R B A := by
  rw [torIndependent_iff_isZero_tor] at h ⊢
  intro i hi
  obtain ⟨e⟩ := tor_symm_canonically_iso R i
  exact (h i hi).of_iso ((e.app (ModuleCat.of R B)).app (ModuleCat.of R A))

end RingTheory.TorIndependence

namespace Koszul

/-- **A sequence whose image is Koszul-regular is Koszul-regular on the target.** Let `S` be an
`R`-algebra and let `f₁, …, f_r ∈ R` be such that the images `f₁, …, f_r` in `S` form a
Koszul-regular sequence of `S`. Then `f₁, …, f_r` is Koszul-regular *on* `S` in the sense of
Tag 062E: `H_i(K_•(f₁, …, f_r) ⊗_R S) = 0` for `i ≠ 0`.

The Koszul complex of the images, viewed as a complex of `R`-modules by restriction of scalars,
is degreewise isomorphic to `K_•(f) ⊗_R S`: the terms are matched by
`KoszulC.extPow_baseChange_natEquiv` and the differentials by `KoszulC.d_baseChange_comm`. -/
theorem isKoszulRegularOn_of_isKoszulRegular_map
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {r : ℕ} (f : Fin r → R)
    (hf : IsKoszulRegular (fun i => algebraMap R S (f i))) :
    IsKoszulRegularOn f S := by
  classical
  choose β hβ using fun n => KoszulC.extPow_baseChange_natEquiv (R := R) (S := S) (r := r) n
  let F := ModuleCat.restrictScalars (algebraMap R S)
  let D := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (seqComplex (fun i => algebraMap R S (f i)))
  let e : seqComplexTensor f S ≅ D :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => ((TensorProduct.comm R _ S).trans ((β n).restrictScalars R)).toModuleIso)
      (by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        change _ ≫ F.map ((seqComplex (fun k => algebraMap R S (f k))).d (j + 1) j) = _
        rw [seqComplex_d, seqComplexTensor_d]
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x s
        symm
        change β j (s ⊗ₜ[R] d (seqDual f) j x) =
          d (seqDual (fun k => algebraMap R S (f k))) j (β (j + 1) (s ⊗ₜ[R] x))
        have ht {n : ℕ} (y : ⋀[R]^n (Fin r → R)) : s ⊗ₜ[R] y = s • (1 ⊗ₜ[R] y) := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [ht, ht, map_smul, map_smul, map_smul, KoszulC.d_baseChange_comm f β hβ])
  intro i hi
  have hD : IsZero (D.homology i) :=
    (F.map_isZero (hf i hi)).of_iso
      (((seqComplex (fun k => algebraMap R S (f k))).sc i).mapHomologyIso F)
  exact hD.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso e)

/-- **A quotient by a Koszul-regular sequence is Tor independent of any algebra in which the
sequence stays Koszul-regular.** Let `R → C` be surjective with kernel `(f₁, …, f_r)` for a
Koszul-regular sequence `f`, and let `S` be an `R`-algebra in which the images of `f₁, …, f_r`
again form a Koszul-regular sequence. Then `Tor_i^R(C, S) = 0` for every `i > 0`, which is
Tag 0660 for the pair `C`, `S`.

The Koszul complex resolves `C` (`Koszul.seqProjectiveResolution`), so the `Tor` groups are the
Koszul homology with coefficients in `S` (`Koszul.isKoszulRegularOn_iff_isZero_tor`), and that
vanishes by `Koszul.isKoszulRegularOn_of_isKoszulRegular_map`. -/
theorem torIndependent_of_isKoszulRegular_map
    {R C S : Type u} [CommRing R] [CommRing C] [CommRing S] [Algebra R C] [Algebra R S]
    (h : Function.Surjective (algebraMap R C)) {r : ℕ} (f : Fin r → R)
    (hf : IsKoszulRegular f)
    (hI : RingHom.ker (algebraMap R C) = Ideal.span (Set.range f))
    (hS : IsKoszulRegular (fun i => algebraMap R S (f i))) :
    RingTheory.TorIndependence.TorIndependent R C S := by
  let e : (R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] C :=
    (Ideal.quotientEquivAlgOfEq R hI.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R C) h)
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  intro i hi
  have hz : IsZero (((Tor' (ModuleCat.{u} R) i).obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).obj (ModuleCat.of R S)) :=
    (isKoszulRegularOn_iff_isZero_tor f hf S).mp
      (isKoszulRegularOn_of_isKoszulRegular_map f hS) i (by omega)
  exact (hz.of_iso (((Tor_iso_Tor' R i).app
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).app (ModuleCat.of R S))).of_iso
    ((Functor.mapIso (Tor (ModuleCat.{u} R) i) e.toLinearEquiv.toModuleIso).app
      (ModuleCat.of R S)).symm

end Koszul

end
