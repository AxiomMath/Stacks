module

public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle

/-!
# Complexes of finite locally free modules with Tor-dimension-one cohomology

Let `X` be a scheme and let `E ∈ D(𝒪_X)` be represented by a complex `ℰ^•` of finite locally free
`𝒪_X`-modules which is bounded above. If every cohomology sheaf `H^i(E)` is a perfect
`𝒪_X`-module of Tor dimension at most one, then every image `Im(d^i)` and every kernel `Ker(d^i)`
of a differential of `ℰ^•` is again finite locally free. Consequently the three rows of the short
exact sequence of complexes
`0 ⟶ τ_{≤k-1}ℰ^• ⟶ τ_{≤k}ℰ^• ⟶ (Im(d^{k-1}) ⟶ Ker(d^k)) ⟶ 0`
representing the truncation triangle `τ_{≤k-1}E ⟶ τ_{≤k}E ⟶ H^k(E)[-k] ⟶ (τ_{≤k-1}E)[1]` are
bounded complexes of finite locally free modules.

## Main results

* `StacksDraft.Perfect.isFiniteLocallyFree_range_and_ker_of_torDimensionLE_one`: the images and
  kernels of the differentials are finite locally free.
* `StacksDraft.Perfect.isFiniteLocallyFree_truncLE_X_of_torDimensionLE_one`: every term of every
  row of the short exact sequence of successive truncations is finite locally free.

That this short exact sequence represents the truncation triangle, and that its rows are
`τ_{≤k-1}ℰ^•`, `τ_{≤k}ℰ^•` and `H^k(E)[-k]`, holds over any abelian category and is
`CochainComplex.nonempty_triangleOfSES_truncLE_iso`, `CochainComplex.nonempty_truncLE_truncLE_iso`
and `CochainComplex.nonempty_Q_shortComplexTruncLE_X₃_iso`.

## Implementation notes

The source's argument is a descending induction on the two short exact sequences
`0 ⟶ Im(d^i) ⟶ Ker(d^{i+1}) ⟶ H^{i+1}(E) ⟶ 0` and `0 ⟶ Ker(d^i) ⟶ ℰ^i ⟶ Im(d^i) ⟶ 0`, each time
concluding that the kernel of a surjection from a finite locally free module onto a perfect module
of Tor dimension at most one is finite locally free. That step is local and is done on the sheaf
level, with no reduction to affine opens: the kernel is flat by Tag 08CJ (3)
(`AlgebraicGeometry.isFlat_of_shortExact_hasTorAmplitude`), it is of finite presentation by
Tag 08CD (3) together with Tag 09V9, because a perfect object is pseudo-coherent, and a flat module
of finite presentation is finite locally free by Tag 05P2
(`AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude`).

In degree `k - 1` the third row is the cokernel of `τ_{≤k-1}ℰ^• ⟶ τ_{≤k}ℰ^•`; it is identified
with `Im(d^{k-1})` without computing that map, from the vanishing of the third row below `k - 1`
and of its cohomology in degree `k - 1`.

## References

* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- Finite local freeness of an `𝒪_X`-module. -/
private abbrev FLF (M : X.Modules) : Prop :=
  Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M

/-- An `𝒪_X`-module which is perfect of Tor dimension at most one: in degree zero it is a perfect
object of `D(𝒪_X)` with Tor amplitude in `[-1, 0]`. -/
private abbrev PT (M : X.Modules) : Prop :=
  IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj M) ∧
    HasTorAmplitude X.toRingedSpace ((DerivedCategory.singleFunctor X.Modules 0).obj M) (-1) 0

/-- Being perfect of Tor dimension at most one is invariant under isomorphism. -/
private theorem PT.of_iso {M N : X.Modules} (e : M ≅ N) (h : PT M) : PT N :=
  ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).mapIso e) h.1,
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} h.2
      ((DerivedCategory.singleFunctor X.Modules 0).mapIso e).symm⟩

/-- A perfect object of `D(𝒪_X)` is `m`-pseudo-coherent for every `m`: a quasi-isomorphism from
a strictly perfect complex is an isomorphism on cohomology in every degree. -/
private theorem isPseudoCoherentFrom_of_isPerfect (E : DerivedCategory X.Modules)
    (hE : IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m := by
  obtain ⟨K, hK, he⟩ := hE
  refine ⟨K, fun x => ?_, he⟩
  obtain ⟨I, U, hcover, hlocal⟩ := hK
  have hx : x ∈ iSup U := by simp [hcover]
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨P, hP, g, hg⟩ := hlocal i
  exact ⟨U i, hxi, P, hP, g, fun j _ => (quasiIsoAt_iff_isIso_homologyMap _ j).1 (hg.quasiIsoAt j),
    @IsIso.epi_of_iso _ _ _ _ _ ((quasiIsoAt_iff_isIso_homologyMap _ m).1 (hg.quasiIsoAt m))⟩

/-- A finite locally free module is perfect of Tor dimension at most one. -/
private theorem pt_of_flf (M : X.Modules) (hM : FLF M) : PT M :=
  ⟨isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM,
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree X M hM)
      (show (-1 : ℤ) ≤ 0 by omega) le_rfl⟩

/-- Finite local freeness is invariant under isomorphism. -/
private theorem flf_of_iso {M N : X.Modules} (e : M ≅ N) (h : FLF M) : FLF N :=
  Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso e (h := h)

/-- A zero module is finite locally free, being isomorphic to the free module on the empty set. -/
private theorem flf_of_isZero {M : X.Modules} (hM : IsZero M) : FLF M := by
  have h0 : IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}) := by
    rw [IsZero.iff_id_eq_zero]
    exact (SheafOfModules.freeHomEquiv _).injective (funext fun i => i.elim)
  exact Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso (h0.iso hM)

/-- **The inductive step of Stacks 0F8J.** In a short exact sequence `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` of
`𝒪_X`-modules with `ℬ` finite locally free and `𝒞` perfect of Tor dimension at most one, the
module `𝒜` is finite locally free.

`ℬ[0]` is `(-1)`-pseudo-coherent and `𝒞[0]` is `(-2)`-pseudo-coherent, both being perfect, so
`𝒜[0]` is `(-1)`-pseudo-coherent by Tag 08CD (3), that is, `𝒜` is of finite presentation by
Tag 09V9. A finitely presented kernel of a surjection from a finite locally free module onto a
module of Tor dimension at most one is finite locally free. -/
private theorem flf_X₁_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₂ : FLF S.X₂) (h₃ : PT S.X₃) : FLF S.X₁ := by
  have hL := isPseudoCoherentFrom_of_isPerfect _
    (isPerfect_singleFunctor_of_isFiniteLocallyFree X S.X₂ h₂) (-2 + 1)
  have hM := isPseudoCoherentFrom_of_isPerfect _ h₃.1 (-2)
  have h := RingedSpace.isPseudoCoherentFrom_obj₁_of_distinguished (X := X.toRingedSpace) (-2)
    hS.singleTriangle hS.singleTriangle_distinguished hL hM
  rw [show (-2 : ℤ) + 1 = -1 by norm_num] at h
  exact isFiniteLocallyFree_of_shortExact_hasTorAmplitude S hS h₂ h₃.2
    (RingedSpace.isFinitePresentation_of_isPseudoCoherentFrom_singleFunctor_zero_neg_one
      (X := X.toRingedSpace) S.X₁ h)

variable (K : CochainComplex X.Modules ℤ)

/-- **One step of the descending induction of Stacks 0F8J.** If `Ker(d^{j+1})` is finite locally
free, `H^{j+1}` is perfect of Tor dimension at most one and `ℰ^j` is finite locally free, then the
image of `ℰ^j ⟶ Ker(d^{j+1})` and `Ker(d^j)` are finite locally free.

The two short exact sequences are `0 ⟶ Im(d^j) ⟶ Ker(d^{j+1}) ⟶ H^{j+1} ⟶ 0`, exact because
`H^{j+1}` is the cokernel of `ℰ^j ⟶ Ker(d^{j+1})`, and `0 ⟶ Ker(d^j) ⟶ ℰ^j ⟶ Im(d^j) ⟶ 0`, exact
because `Ker(d^j)` is the kernel of `d^j`. -/
private theorem flf_step (j : ℤ) (hc : FLF (K.cycles (j + 1))) (hH : PT (K.homology (j + 1)))
    (hX : FLF (K.X j)) :
    FLF (image (K.toCycles j (j + 1)) : X.Modules) ∧ FLF (K.cycles j) := by
  let t := K.toCycles j (j + 1)
  have hz₁ : image.ι t ≫ K.homologyπ (j + 1) = 0 :=
    (cancel_epi (factorThruImage t)).1 (by simp [t])
  let S₀ := ShortComplex.mk t (K.homologyπ (j + 1)) (K.toCycles_comp_homologyπ j (j + 1))
  let S₁ := ShortComplex.mk (image.ι t) (K.homologyπ (j + 1)) hz₁
  let φ₁ : S₀ ⟶ S₁ :=
    { τ₁ := factorThruImage t
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hS₁ : S₁.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁).1
        (ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel j (j + 1) (by simp))) }
  have hIm := flf_X₁_of_shortExact S₁ hS₁ hc hH
  have hz₂ : K.iCycles j ≫ factorThruImage t = 0 :=
    (cancel_mono (image.ι t ≫ K.iCycles (j + 1))).1 (by simp [t])
  let S₂ := ShortComplex.mk (K.iCycles j) (factorThruImage t) hz₂
  let S₃ := ShortComplex.mk (K.iCycles j) (K.d j (j + 1)) (K.iCycles_d j (j + 1))
  let φ₂ : S₂ ⟶ S₃ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := image.ι t ≫ K.iCycles (j + 1)
      comm₂₃ := by simp [S₂, S₃, t] }
  have hS₂ : S₂.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂).2
        (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel j (j + 1) (by simp))) }
  exact ⟨hIm, flf_X₁_of_shortExact S₂ hS₂ hX (pt_of_flf _ hIm)⟩

/-- **The descending induction of Stacks 0F8J.** For a complex of finite locally free modules
which vanishes above degree `b` and whose cohomology modules are perfect of Tor dimension at most
one, the image of `ℰ^i ⟶ Ker(d^{i+1})` and `Ker(d^i)` are finite locally free for every `i`. Above
`b` the kernels vanish, which starts the induction. -/
private theorem flf_image_and_cycles (b : ℤ) [K.IsStrictlyLE b] (hterm : ∀ i, FLF (K.X i))
    (hH : ∀ i, PT (K.homology i)) (i : ℤ) :
    FLF (image (K.toCycles i (i + 1)) : X.Modules) ∧ FLF (K.cycles i) := by
  have hrec (n : ℕ) : ∀ j : ℤ, (b + 1 - j).toNat ≤ n → FLF (K.cycles j) := by
    induction n with
    | zero =>
      exact fun j hj => flf_of_isZero
        (IsZero.of_mono (K.iCycles j) (K.isZero_of_isStrictlyLE b j (by omega)))
    | succ n ih =>
      intro j hj
      by_cases hjb : b + 1 ≤ j
      · exact ih j (by omega)
      · exact (flf_step K j (ih (j + 1) (by omega)) (hH (j + 1)) (hterm j)).2
  exact flf_step K i (hrec _ (i + 1) le_rfl) (hH (i + 1)) (hterm i)

/-- The image of `ℰ^i ⟶ Ker(d^{i+1})` is the image of `d^i`, since `Ker(d^{i+1}) ⟶ ℰ^{i+1}` is a
monomorphism. -/
private def imageToCyclesIso (i : ℤ) :
    (image (K.toCycles i (i + 1)) : X.Modules) ≅ image (K.d i (i + 1)) :=
  image.isoStrongEpiMono (factorThruImage (K.toCycles i (i + 1)))
    (image.ι (K.toCycles i (i + 1)) ≫ K.iCycles (i + 1)) (by simp)

/-- The cycles in degree `i` are the kernel of `d^i`. -/
private def cyclesIsoKernel (i : ℤ) : K.cycles i ≅ kernel (K.d i (i + 1)) :=
  (K.cyclesIsKernel i (i + 1) (by simp)).conePointUniqueUpToIso (limit.isLimit _)

/-- The terms of `τ_{≤n}ℰ^•` are those of `ℰ^•` below `n`, the kernel of `d^n` in degree `n`, and
zero above `n`. -/
private theorem flf_truncLE_X (hterm : ∀ i, FLF (K.X i)) (n : ℤ) (hn : FLF (K.cycles n)) (i : ℤ) :
    FLF ((K.truncLE n).X i) := by
  rcases lt_trichotomy i n with hin | rfl | hin
  · exact flf_of_iso (K.truncLEXIso n i hin).symm (hterm i)
  · exact flf_of_iso (K.truncLEXIsoCycles i).symm hn
  · exact flf_of_isZero ((K.truncLE n).isZero_of_isStrictlyLE n i hin)

/-- The cohomology of `τ_{≤k}ℰ^•` is that of `ℰ^•` up to degree `k` and zero above, so it is
perfect of Tor dimension at most one as soon as that of `ℰ^•` is. -/
private theorem pt_homology_truncLE (hH : ∀ i, PT (K.homology i)) (k i : ℤ) :
    PT ((K.truncLE k).homology i) := by
  by_cases hik : i ≤ k
  · have : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE k) i) :=
      (quasiIsoAt_iff_isIso_homologyMap (K.ιTruncLE k) i).mp (K.quasiIsoAt_ιTruncLE k i hik)
    exact (hH i).of_iso (asIso (HomologicalComplex.homologyMap (K.ιTruncLE k) i)).symm
  · exact pt_of_flf _ (flf_of_isZero ((K.truncLE k).isZero_of_isLE k i (by omega)))

/-- An epimorphism followed by a monomorphism identifies its middle object with the image of the
composite. -/
private def isoImageOfEpiMono {A B C : X.Modules} (p : A ⟶ B) (m : B ⟶ C) (_hp : Epi p)
    (_hm : Mono m) : B ≅ image (p ≫ m) :=
  haveI : StrongEpi p := strongEpi_of_epi p
  image.isoStrongEpiMono p m rfl

/-- **The third row of the display of Stacks 0F8J.** The quotient of `ℰ^•` by `τ_{≤n}ℰ^•` is zero
below `n`, is `Im(d^n)` in degree `n` and is `ℰ^i` above `n`; so its terms are finite locally free
when those of `ℰ^•` and `Im(d^n)` are.

Below `n` the inclusion `τ_{≤n}ℰ^• ⟶ ℰ^•` is an isomorphism, and above `n` its source vanishes. In
degree `n` the quotient has vanishing cohomology and vanishing term in degree `n - 1`, so its
differential out of degree `n` is a monomorphism; composed with the projection from `ℰ^n` and the
inverse of the projection in degree `n + 1` it is `d^n`, which exhibits the quotient in degree `n`
as the image of `d^n`. -/
private theorem flf_shortComplexTruncLE_X₃_X (hterm : ∀ i, FLF (K.X i)) (n : ℤ)
    (himg : FLF (image (K.toCycles n (n + 1)) : X.Modules)) (i : ℤ) :
    FLF ((K.shortComplexTruncLE n).X₃.X i) := by
  let S := K.shortComplexTruncLE n
  have hS : S.ShortExact := K.shortComplexTruncLE_shortExact n
  have hSi (j : ℤ) : (S.map (HomologicalComplex.eval _ _ j)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS j
  have hlow (j : ℤ) (hj : j < n) : IsZero (S.X₃.X j) := by
    have : IsIso ((K.ιTruncLE n).f j) := K.isIso_ιTruncLE_f_of_lt n j hj
    have hepi : Epi (S.map (HomologicalComplex.eval _ _ j)).f :=
      inferInstanceAs (Epi ((K.ιTruncLE n).f j))
    have := (hSi j).epi_g
    exact IsZero.of_epi_eq_zero _ ((hSi j).exact.epi_f_iff.1 hepi)
  have hhigh (j : ℤ) (hj : n < j) : IsIso (S.g.f j) :=
    (hSi j).isIso_g_iff.2 ((K.truncLE n).isZero_of_isStrictlyLE n j hj)
  rcases lt_trichotomy i n with hin | rfl | hin
  · exact flf_of_isZero (hlow i hin)
  · have hex : S.X₃.ExactAt i := by
      simpa using (K.shortComplexTruncLE_X₃_isSupportedOutside
        (ComplexShape.embeddingUpIntLE i)).exactAt 0
    have hmono : Mono (S.X₃.d i (i + 1)) :=
      (((S.X₃.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).1 hex).mono_g
        ((hlow (i - 1) (by omega)).eq_of_src _ _))
    let eh := @asIso _ _ _ _ (S.g.f (i + 1)) (hhigh (i + 1) (by omega))
    have hcomm : S.g.f i ≫ S.X₃.d i (i + 1) ≫ eh.inv = S.X₂.d i (i + 1) := by
      rw [← Category.assoc, S.g.comm i (i + 1)]
      simp [eh]
    let e : S.X₃.X i ≅ image (S.X₂.d i (i + 1)) :=
      isoImageOfEpiMono (S.g.f i) (S.X₃.d i (i + 1) ≫ eh.inv) (hSi i).epi_g (mono_comp _ _) ≪≫
        image.eqToIso hcomm
    exact flf_of_iso (imageToCyclesIso K i ≪≫ e.symm) himg
  · exact flf_of_iso (@asIso _ _ _ _ (S.g.f i) (hhigh i hin)) (hterm i)

/-- The cohomology of a complex representing `E` is the cohomology of `E`. -/
private theorem pt_homology_of_iso (E : DerivedCategory X.Modules)
    (e : DerivedCategory.Q.obj K ≅ E)
    (hH : ∀ i : ℤ, PT ((DerivedCategory.homologyFunctor X.Modules i).obj E)) (i : ℤ) :
    PT (K.homology i) :=
  (hH i).of_iso (((DerivedCategory.homologyFunctorFactors X.Modules i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules i).mapIso e).symm

/-- **Stacks 0F8J.** Let `X` be a scheme and let `E ∈ D(𝒪_X)` be such that every cohomology module
`H^i(E)` is a perfect `𝒪_X`-module of Tor dimension at most one, that is, `H^i(E)` placed in degree
zero is a perfect object with Tor amplitude in `[-1, 0]`. Let `ℰ^•` be a complex of finite locally
free `𝒪_X`-modules which vanishes above degree `b` and represents `E`. Then `Im(d^i)` and
`Ker(d^i)` are finite locally free `𝒪_X`-modules for every `i`.

The source takes `E` perfect and `ℰ^•` bounded; neither the perfectness of `E` nor a lower bound
on `ℰ^•` is used. -/
@[stacks 0F8J "the images and kernels of the differentials"]
public theorem isFiniteLocallyFree_range_and_ker_of_torDimensionLE_one
    (E : DerivedCategory X.Modules) (K : CochainComplex X.Modules ℤ)
    (e : DerivedCategory.Q.obj K ≅ E) (b : ℤ) [K.IsStrictlyLE b]
    (hterm : ∀ i : ℤ,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (K.X i))
    (hH : ∀ i : ℤ,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) ∧
      HasTorAmplitude X.toRingedSpace ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) (-1) 0)
    (i : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (image (K.d i (i + 1)) : X.Modules) ∧
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (kernel (K.d i (i + 1)) : X.Modules) := by
  obtain ⟨hIm, hCyc⟩ := flf_image_and_cycles K b hterm (pt_homology_of_iso K E e hH) i
  exact ⟨flf_of_iso (imageToCyclesIso K i) hIm, flf_of_iso (cyclesIsoKernel K i) hCyc⟩

/-- **Stacks 0F8J, the truncation rows.** Under the hypotheses of
`StacksDraft.Perfect.isFiniteLocallyFree_range_and_ker_of_torDimensionLE_one`, fix `k` and let
`0 ⟶ τ_{≤k-1}(τ_{≤k}ℰ^•) ⟶ τ_{≤k}ℰ^• ⟶ Q ⟶ 0` be the short exact sequence of successive canonical
truncations. Every term of each of its three rows is a finite locally free `𝒪_X`-module.

The rows are `ℰ^a → ⋯ → ℰ^{k-2} → Ker(d^{k-1})`, `ℰ^a → ⋯ → ℰ^{k-1} → Ker(d^k)` and
`Im(d^{k-1}) → Ker(d^k)`, as displayed in the source. This short exact sequence represents the
distinguished triangle `τ_{≤k-1}E ⟶ τ_{≤k}E ⟶ H^k(E)[-k] ⟶ (τ_{≤k-1}E)[1]`, which is
`CochainComplex.nonempty_triangleOfSES_truncLE_iso`. -/
@[stacks 0F8J "the rows of the short exact sequences representing the truncation triangles"]
public theorem isFiniteLocallyFree_truncLE_X_of_torDimensionLE_one
    (E : DerivedCategory X.Modules) (K : CochainComplex X.Modules ℤ)
    (e : DerivedCategory.Q.obj K ≅ E) (b : ℤ) [K.IsStrictlyLE b]
    (hterm : ∀ i : ℤ,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (K.X i))
    (hH : ∀ i : ℤ,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) ∧
      HasTorAmplitude X.toRingedSpace ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) (-1) 0)
    (k i : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (((K.truncLE k).shortComplexTruncLE (k - 1)).X₁.X i) ∧
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (((K.truncLE k).shortComplexTruncLE (k - 1)).X₂.X i) ∧
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (((K.truncLE k).shortComplexTruncLE (k - 1)).X₃.X i) := by
  have hH' := pt_homology_of_iso K E e hH
  have hT : ∀ j, FLF ((K.truncLE k).X j) :=
    flf_truncLE_X K hterm k (flf_image_and_cycles K b hterm hH' k).2
  have hTc := flf_image_and_cycles (K.truncLE k) k hT (pt_homology_truncLE K hH' k) (k - 1)
  exact ⟨flf_truncLE_X (K.truncLE k) hT (k - 1) hTc.2 i, hT i,
    flf_shortComplexTruncLE_X₃_X (K.truncLE k) hT (k - 1) hTc.1 i⟩

end StacksDraft.Perfect

end
