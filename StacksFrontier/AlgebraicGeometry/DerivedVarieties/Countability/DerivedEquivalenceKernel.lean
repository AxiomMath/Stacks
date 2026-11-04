module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceFamilies
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceIsEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.CompositionIso
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelCategory

/-!
# A derived equivalence has a relative-equivalence kernel: the reduction

Let `K` be a field and let `X`, `Y` be smooth proper `K`-schemes with a `K`-linear exact
equivalence `F : D_perf(𝒪_X) ≌ D_perf(𝒪_Y)`. The second paragraph of the proof of
[Stacks, Tag 0G0Y] produces a Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over
`Spec K` (the input `AlgebraicGeometry.DerivedEquivalenceHasRelativeKernel` of the assembly
`AlgebraicGeometry.exists_countable_relativeEquivalenceKernels_of_hasRelativeKernel`).

This file reduces that input to two *object-wise* statements:

* `AlgebraicGeometry.ObjectwiseFourierMukaiOfEquivalence K`: every `K`-linear exact equivalence
  `F` as above agrees, object by object, with a Fourier-Mukai functor `Φ_M` of a perfect kernel
  `M` on `X ×_K Y`: `Φ_M(E) ≅ F(E)` for every perfect `E`;
* `AlgebraicGeometry.ObjectwiseIdentityKernelIsDiagonal K`: a perfect kernel `A` on `X ×_K X`
  with `Φ_A(E) ≅ E` for every perfect `E` is isomorphic to the diagonal kernel `Δ_*𝒪_X`.

Given both, apply the first to `F` and to its quasi-inverse, obtaining `M` and `M'`; then
`Φ_{M'} ∘ Φ_M` and `Φ_M ∘ Φ_{M'}` are object-wise the identity, so by composition of
Fourier-Mukai functors ([Stacks, Tag 0FYS]) the Fourier-Mukai functors of the two convolutions
of `M` and `M'` are object-wise the identity, and the second statement identifies both
convolutions with the diagonal kernels. That is the definition [Stacks, Tag 0G0I] of a
relative-equivalence kernel.

## Why object-wise statements

The source instead uses [Stacks, Tag 0G0D] (the equivalence is, up to replacing it by a sibling,
a Fourier-Mukai *functor*), [Stacks, Tag 0FYY] (3) (the right adjoint of `Φ_M` is a
Fourier-Mukai functor, by Grothendieck duality) and [Stacks, Tag 0G0E] (a kernel whose functor
is isomorphic to the identity *functor* is `Δ_*𝒪_X`). The object-wise route needs neither the
relative duality of 0FYY (3) nor the passage from siblings to isomorphic functors. Its second
statement is false over a general field — for `X = Spec L` with `L / K` a nontrivial Galois
extension, the graph of `Spec σ` for `σ ≠ 1` in the Galois group gives a kernel whose functor is
object-wise, but not naturally, the identity — and true over an algebraically closed field, which
is the generality of [Stacks, Tag 0G0Y]. The proof of the second statement is that of
[Stacks, Tag 0G0E] read object-wise, with its last step replaced by: an endomorphism of a reduced
scheme of finite type over an algebraically closed field which fixes every closed point is the
identity.

## Main definitions

* `AlgebraicGeometry.ObjectwiseFourierMukaiOfEquivalence`
* `AlgebraicGeometry.ObjectwiseIdentityKernelIsDiagonal`

## Main results

* `AlgebraicGeometry.fourierMukaiConvolutionObjIso`: object-wise composition of Fourier-Mukai
  functors ([Stacks, Tag 0FYS]) on objects with quasi-coherent cohomology.
* `AlgebraicGeometry.isRelativeEquivalenceKernel_of_objIso`: a pair of perfect kernels whose
  Fourier-Mukai functors are object-wise mutually inverse is a relative-equivalence kernel, given
  the second object-wise statement.
* `AlgebraicGeometry.derivedEquivalenceHasRelativeKernel_of_objectwise`: the reduction.

## References

* [Stacks Project, Tag 0G0Y](https://stacks.math.columbia.edu/tag/0G0Y)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The two object-wise statements -/

/-- **A derived equivalence is object-wise a Fourier-Mukai functor.** For smooth proper
`K`-schemes `X` and `Y`, every `K`-linear exact equivalence `F : D_perf(𝒪_X) ≌ D_perf(𝒪_Y)`
agrees object by object with the Fourier-Mukai functor of a perfect kernel `M` on `X ×_K Y`:
`Φ_M(E) ≅ F(E)` for every perfect `E`. Over an algebraically closed field this follows from
[Stacks, Tag 0G0B] and [Stacks, Tag 0G27] (whose automorphism is then the identity). -/
def ObjectwiseFourierMukaiOfEquivalence (K : Type u) [Field K] : Prop :=
  ∀ A B : Over (Spec (CommRingCat.of K)),
    Smooth A.hom → IsProper A.hom → Smooth B.hom → IsProper B.hom →
      letI : Linear K A.left.Modules := modulesLinear K A
      letI : Linear K B.left.Modules := modulesLinear K B
      ∀ e : PerfectDerivedCategory A.left ≌ PerfectDerivedCategory B.left,
        e.functor.Linear K → ∀ h : e.functor.CommShift ℤ, (letI := h; e.functor.IsTriangulated) →
          ∃ M : DerivedCategory (pullback A.hom B.hom).Modules,
            IsPerfect (X := (pullback A.hom B.hom).toRingedSpace) M ∧
              ∀ E : PerfectDerivedCategory A.left,
                Nonempty ((fourierMukai A.hom B.hom M).obj E.obj ≅ (e.functor.obj E).obj)

/-- **A kernel whose Fourier-Mukai functor is object-wise the identity is the diagonal.** For a
smooth proper `K`-scheme `X`, a perfect kernel `A` on `X ×_K X` with `Φ_A(E) ≅ E` for every
perfect `E` is isomorphic to `Δ_*𝒪_X`. This is [Stacks, Tag 0G0E] with its hypothesis read
object-wise; it holds over an algebraically closed field (see the module docstring for why not
in general). -/
def ObjectwiseIdentityKernelIsDiagonal (K : Type u) [Field K] : Prop :=
  ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)), Smooth f → IsProper f →
    ∀ A : DerivedCategory (pullback f f).Modules,
      IsPerfect (X := (pullback f f).toRingedSpace) A →
        (∀ E : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) E →
          Nonempty ((fourierMukai f f A).obj E ≅ E)) →
          Nonempty (diagonalKernel f ≅ A)

/-! ### Object-wise composition -/

section Composition

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- **Composition of Fourier-Mukai functors, object by object** ([Stacks, Tag 0FYS]). For `g`
flat, `X` and `Z` tor independent over `S`, `f` and `g` quasi-compact and quasi-separated, and
kernels with quasi-coherent cohomology, `Φ_{K'}(Φ_K(E)) ≅ Φ_{K ∘ K'}(E)` for every `E` with
quasi-coherent cohomology. -/
def fourierMukaiConvolutionObjIso [Flat g] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact h] [QuasiSeparated h]
    (htor : TorIndependent f h)
    {K : DerivedCategory (pullback f g).Modules} (hK : IsQCohAll K)
    {K' : DerivedCategory (pullback g h).Modules} (hK' : IsQCohAll K')
    (E : DerivedCategory X.Modules) (hE : IsQCohAll E) :
    (fourierMukai g h K').obj ((fourierMukai f g K).obj E) ≅
      (fourierMukai f h (fourierMukaiConvolution f g h K K')).obj E :=
  (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf))).mapIso
      ((quasiCoherentFourierMukaiCompNatIso f g h htor hK hK').app ⟨E, hE⟩)

end Composition

/-! ### Object-wise inverse kernels form a relative equivalence -/

section Inverse

variable {K : Type u} [Field K] {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  (g : Y ⟶ Spec (CommRingCat.of K))

/-- One half of `AlgebraicGeometry.isRelativeEquivalenceKernel_of_objIso`: if
`Φ_{M'} ∘ Φ_M` is object-wise the identity on perfect complexes, the convolution of `M` and `M'`
is the diagonal kernel. -/
lemma nonempty_diagonalKernel_iso_convolution_of_objIso
    (hdiag : ObjectwiseIdentityKernelIsDiagonal K)
    [Smooth f] [IsProper f] [Smooth g] [IsProper g]
    {M : DerivedCategory (pullback f g).Modules}
    (hM : IsPerfect (X := (pullback f g).toRingedSpace) M)
    {M' : DerivedCategory (pullback g f).Modules}
    (hM' : IsPerfect (X := (pullback g f).toRingedSpace) M')
    (hinv : ∀ E : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) E →
      Nonempty ((fourierMukai g f M').obj ((fourierMukai f g M).obj E) ≅ E)) :
    Nonempty (diagonalKernel f ≅ fourierMukaiConvolution f g f M M') := by
  have : IsNoetherian (pullback f f) := isNoetherian_of_locallyOfFiniteType (pullback.snd f f ≫ f)
  have : LocallyOfFinitePresentation g := inferInstance
  refine hdiag X f inferInstance inferInstance _
    (isPerfect_fourierMukaiConvolution_of_isNoetherian f g f hM hM') fun E hE => ?_
  obtain ⟨e⟩ := hinv E hE
  exact ⟨(fourierMukaiConvolutionObjIso f g f (torIndependent_of_flat_left f f)
    (isQCohAll_of_isPerfect hM) (isQCohAll_of_isPerfect hM') E
      (isQCohAll_of_isPerfect hE)).symm ≪≫ e⟩

/-- **Perfect kernels with object-wise mutually inverse Fourier-Mukai functors form a relative
equivalence** ([Stacks, Tag 0G0I]), over a field over which
`AlgebraicGeometry.ObjectwiseIdentityKernelIsDiagonal` holds. -/
theorem isRelativeEquivalenceKernel_of_objIso
    (hdiag : ObjectwiseIdentityKernelIsDiagonal K)
    [Smooth f] [IsProper f] [Smooth g] [IsProper g]
    {M : DerivedCategory (pullback f g).Modules}
    (hM : IsPerfect (X := (pullback f g).toRingedSpace) M)
    {M' : DerivedCategory (pullback g f).Modules}
    (hM' : IsPerfect (X := (pullback g f).toRingedSpace) M')
    (hX : ∀ E : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) E →
      Nonempty ((fourierMukai g f M').obj ((fourierMukai f g M).obj E) ≅ E))
    (hY : ∀ E : DerivedCategory Y.Modules, IsPerfect (X := Y.toRingedSpace) E →
      Nonempty ((fourierMukai f g M).obj ((fourierMukai g f M').obj E) ≅ E)) :
    IsRelativeEquivalenceKernel f g M :=
  ⟨hM, M', hM', nonempty_diagonalKernel_iso_convolution_of_objIso f g hdiag hM hM' hX,
    nonempty_diagonalKernel_iso_convolution_of_objIso g f hdiag hM' hM hY⟩

end Inverse

/-! ### The reduction -/

/-- If `Φ_M` agrees object-wise with `e` and `Φ_{M'}` with its inverse on perfect complexes, then
`Φ_{M'} ∘ Φ_M` is object-wise the identity on perfect complexes. -/
private lemma nonempty_fourierMukai_obj_iso_of_equivalence {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) {M : DerivedCategory (pullback f g).Modules}
    {M' : DerivedCategory (pullback g f).Modules}
    (e : PerfectDerivedCategory X ≌ PerfectDerivedCategory Y)
    (hM : ∀ E : PerfectDerivedCategory X,
      Nonempty ((fourierMukai f g M).obj E.obj ≅ (e.functor.obj E).obj))
    (hM' : ∀ E : PerfectDerivedCategory Y,
      Nonempty ((fourierMukai g f M').obj E.obj ≅ (e.inverse.obj E).obj))
    (E : DerivedCategory X.Modules) (hE : IsPerfect (X := X.toRingedSpace) E) :
    Nonempty ((fourierMukai g f M').obj ((fourierMukai f g M).obj E) ≅ E) := by
  obtain ⟨e₁⟩ := hM ⟨E, hE⟩
  obtain ⟨e₂⟩ := hM' (e.functor.obj ⟨E, hE⟩)
  exact ⟨(fourierMukai g f M').mapIso e₁ ≪≫ e₂ ≪≫
    (ObjectProperty.ι _).mapIso (e.unitIso.app ⟨E, hE⟩).symm⟩

/-- **The input `hkernel` of the assembly of [Stacks, Tag 0G0Y], from the two object-wise
statements.** If over `K` every `K`-linear exact equivalence of perfect derived categories of
smooth proper `K`-schemes is object-wise a Fourier-Mukai functor of a perfect kernel, and every
perfect kernel whose functor is object-wise the identity is the diagonal, then every such
equivalence has a Fourier-Mukai kernel of a relative equivalence over `Spec K`. -/
theorem derivedEquivalenceHasRelativeKernel_of_objectwise {K : Type u} [Field K]
    (hFM : ObjectwiseFourierMukaiOfEquivalence K) (hdiag : ObjectwiseIdentityKernelIsDiagonal K) :
    DerivedEquivalenceHasRelativeKernel K := by
  intro A B hAs hAp hBs hBp hequiv
  let : Linear K A.left.Modules := modulesLinear K A
  let : Linear K B.left.Modules := modulesLinear K B
  obtain ⟨e, hlin, hcs, htri⟩ := hequiv
  let := hcs
  let : e.inverse.CommShift ℤ := e.commShiftInverse ℤ
  have : e.CommShift ℤ := e.commShift_of_functor ℤ
  have : e.IsTriangulated := Equivalence.IsTriangulated.mk' e htri
  obtain ⟨M, hM, hME⟩ := hFM A B hAs hAp hBs hBp e hlin hcs htri
  obtain ⟨M', hM', hM'E⟩ := hFM B A hBs hBp hAs hAp e.symm
    (inferInstanceAs (e.inverse.Linear K)) (inferInstanceAs (e.inverse.CommShift ℤ))
    (inferInstanceAs (e.inverse.IsTriangulated))
  exact ⟨M, isRelativeEquivalenceKernel_of_objIso A.hom B.hom hdiag hM hM'
    (nonempty_fourierMukai_obj_iso_of_equivalence _ _ e hME hM'E)
    (nonempty_fourierMukai_obj_iso_of_equivalence _ _ e.symm hM'E hME)⟩

end AlgebraicGeometry
