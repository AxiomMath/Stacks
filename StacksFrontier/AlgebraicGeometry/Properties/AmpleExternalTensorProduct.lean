module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackCovering.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower
public import StacksFrontier.AlgebraicGeometry.Segre.ChartAffine

/-!
# The external tensor product on a fibre product of schemes

For schemes `X` and `Y` over a base `S`, the external tensor product of an `𝒪_X`-module `L` and
an `𝒪_Y`-module `N` is `pr₁^* L ⊗ pr₂^* N` on `X ×_S Y`. It is invertible as soon as `L` and `N`
are, and ample as soon as `L` and `N` are and `S` is quasi-separated. That is Stacks Tag 0DNK,
and this file proves it.

## Main definitions

* `Stacks.AmpleExternalTensor.externalTensor`: the module `pr₁^* L ⊗ pr₂^* N` on `X ×_S Y`.
* `Stacks.AmpleExternalTensor.externalTensorComparisonIso`: the external tensor product over a
  base `S` is the pullback, along the comparison morphism `X ×_S Y ⟶ X ×_T Y`, of the external
  tensor product over a larger base `T`.

## Main results

* `Stacks.AmpleExternalTensor.isAmple_externalTensor`: **Stacks Tag 0DNK.** For `S`
  quasi-separated and `L`, `N` ample, `pr₁^* L ⊗ pr₂^* N` is ample on `X ×_S Y`.
* `Stacks.AmpleExternalTensor.isAmple_externalTensor_of_isAffine`: the absolute case, over an
  arbitrary affine base.
* `Stacks.AmpleExternalTensor.isAmple_externalTensor_of_isAmple_absolute`: the descent step,
  from `X ×_{Spec ℤ} Y` to `X ×_S Y`.

## The proof, in the two halves the Stacks proof has

The **descent step** is Tag 0B3E along the comparison morphism `X ×_S Y ⟶ X ×_{Spec ℤ} Y`,
which is a quasi-compact immersion exactly because `S` is quasi-separated (Tag 01KR); the
external tensor product over `S` is its pullback of the external tensor product over `Spec ℤ`,
by `Stacks.AmpleExternalTensor.externalTensorComparisonIso`. This is the only place
quasi-separatedness is used.

The **absolute case** is proved over an arbitrary affine base `Z`, `Spec ℤ` being one. At a
point `z` of `X ×_Z Y` with projections `x` and `y`, ampleness gives `n ≥ 1` and `s` in
`Γ(X, L^{⊗ n})` with `X_s` an affine open around `x`, and `m ≥ 1` and `t` in `Γ(Y, N^{⊗ m})`
with `Y_t` affine around `y`. The two exponents are made equal before the sections are paired —
the step the Stacks proof leaves implicit, and the subject of the remark on its page — by
raising each section to a tensor power: `s^{⊗ m}` lives in `(L^{⊗ n})^{⊗ m} ≅ L^{⊗ nm}` and has
the nonvanishing locus of `s`. The pulled-back sections `pr₁^* s^{⊗ m}` and `pr₂^* t^{⊗ n}` are
then sections of the same power of the two factors, their tensor product is a section of
`(pr₁^* L ⊗ pr₂^* N)^{⊗ nm}` through
`Stacks.AmplePullbackPart1.tensorPowModuleTensorIso`, and its nonvanishing locus is
`pr₁^{-1} X_s ∩ pr₂^{-1} Y_t`, which contains `z` and is affine by Tag 01WD
(`Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf`) because the base is affine.
Quasi-compactness of `X ×_Z Y` is quasi-compactness of `X` and of `Y` over the affine, hence
quasi-separated, base.

## Implementation notes

**The section-level inputs are proved here, in the `Stacks.Ample` vocabulary.** The nonvanishing
locus of Tag 01CY has two spellings in this library: `Stacks.Ample.nonvanishingLocus`, taking a
global section, and `Stacks.SheafOfModules.nonvanishingLocus`, taking a restriction-compatible
family. The pullback of a section is developed for the first
(`Stacks.NonvanishingPullback.preimage_nonvanishingLocus`) and the pairing of two sections for
the second (`AlgebraicGeometry.tensorSections_nonvanishing_iff`). Rather than move the whole
argument across the boundary, only the pairing is carried over, in
`Stacks.AmpleExternalTensor.exists_tensorGlobalSection`, through
`Stacks.NonvanishingSpelling.sectionsEquiv`; the power of a section and the common-degree move
are then built from that pairing by induction, so Tag 01PT's own common-degree lemma
`AlgebraicGeometry.exists_section_power_nonvanishingOpen_eq`, which is stated in the other
vocabulary, is not needed.

**Isomorphisms whose source is written at the `SheafOfModules` spelling cannot be applied to a
section with `.hom.app` directly.** `Stacks.Ample.tensorPowModuleAddIso` and
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` have a source stated as a
`SheafOfModules` over the structure sheaf rather than at `X.Modules`, so the `≅` in their
statements is taken in the former category and `Hom.app` — which exists only for `X.Modules` —
is not available on it. Both are therefore re-ascribed to `X.Modules` by a local `let` before
use; the two categories are definitionally equal, so the ascription is all that is needed.

## References

* [Stacks Project, Tag 0DNK](https://stacks.math.columbia.edu/tag/0DNK)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01KR](https://stacks.math.columbia.edu/tag/01KR)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.RelativeVeryAmple

namespace Stacks.AmpleExternalTensor

universe u

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The pullback `pr₁^* L` of an `𝒪_X`-module to the fibre product `X ×_S Y`. -/
abbrev fstPullback (L : X.Modules) : (pullback f g).Modules :=
  (modulePullback (pullback.fst f g).toLRSHom.toShHom).obj L

/-- The pullback `pr₂^* N` of an `𝒪_Y`-module to the fibre product `X ×_S Y`. -/
abbrev sndPullback (N : Y.Modules) : (pullback f g).Modules :=
  (modulePullback (pullback.snd f g).toLRSHom.toShHom).obj N

/-- The external tensor product `pr₁^* L ⊗ pr₂^* N` on the fibre product `X ×_S Y`. -/
abbrev externalTensor (L : X.Modules) (N : Y.Modules) : (pullback f g).Modules :=
  tensorModules (pullback f g) (fstPullback f g L) (sndPullback f g N)

/-- The external tensor product of two invertible modules is invertible. -/
@[stacks 0DNK "invertibility: the half of Tag 0DNK's conclusion saying that
`pr₁^* L ⊗ pr₂^* N` is an invertible module on `X ×_S Y`. No hypothesis on `S` and no ampleness;
the ample half is `isAmple_externalTensor`."]
instance isInvertibleModule_externalTensor (L : X.Modules) (N : Y.Modules)
    [IsInvertibleModule X L] [IsInvertibleModule Y N] :
    IsInvertibleModule (pullback f g) (externalTensor f g L N) :=
  Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules (pullback f g)
    (fstPullback f g L) (sndPullback f g N)

section GlobalSections

variable (W : Scheme.{u})

/-- **A tensor product of global sections, and its nonvanishing locus.** For two
`𝒪_W`-modules `A` and `B` and global sections `a` of `A` and `b` of `B`, the section
`a ⊗ b` of `A ⊗ B` has nonvanishing locus `W_a ∩ W_b`: the germ of a tensor product of
sections generates the stalk modulo the maximal ideal exactly when both factors do.

The section is produced existentially because the only thing used downstream is its
nonvanishing locus. The construction is `AlgebraicGeometry.tensorSections`, read through
`Stacks.NonvanishingSpelling.sectionsEquiv`: that development states the pairing for
restriction-compatible families of sections, and a family over a scheme is the same thing as
one global section over `⊤`. -/
theorem exists_tensorGlobalSection (A B : W.Modules) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    ∃ c : Γ(tensorModules W A B, ⊤),
      nonvanishingLocus (tensorModules W A B) c =
        nonvanishingLocus A a ∩ nonvanishingLocus B b := by
  set σ := (Stacks.NonvanishingSpelling.sectionsEquiv W A).symm a
  set τ := (Stacks.NonvanishingSpelling.sectionsEquiv W B).symm b
  refine ⟨Stacks.NonvanishingSpelling.sectionsEquiv W (tensorModules W A B)
    (tensorSections A B σ τ), Set.ext fun x => ?_⟩
  refine Iff.trans (Set.ext_iff.mp
    (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq W (tensorModules W A B)
      (tensorSections A B σ τ)) x).symm ?_
  refine Iff.trans (tensorSections_nonvanishing_iff σ τ x) (and_congr ?_ ?_)
  · exact Set.ext_iff.mp
      (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq W A a) x
  · exact Set.ext_iff.mp
      (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq W B b) x

/-- A global section can be transported along an isomorphism without changing its nonvanishing
locus. -/
private theorem exists_globalSection_of_iso {M N : W.Modules} (e : M ≅ N) (c : Γ(M, ⊤)) :
    ∃ c' : Γ(N, ⊤), nonvanishingLocus N c' = nonvanishingLocus M c :=
  ⟨_, nonvanishingLocus_congr e c⟩

/-- **A positive tensor power of a global section has the same nonvanishing locus.** The
section `a^{⊗ (m + 1)}` of `A^{⊗ (m + 1)}` is built by repeatedly pairing with `a`, and each
pairing intersects the nonvanishing locus with itself. -/
theorem exists_powGlobalSection (A : W.Modules) [IsInvertibleModule W A] (a : Γ(A, ⊤))
    (m : ℕ) :
    ∃ c : Γ(tensorPowModule W A ((m : ℤ) + 1), ⊤),
      nonvanishingLocus (tensorPowModule W A ((m : ℤ) + 1)) c = nonvanishingLocus A a := by
  obtain ⟨a', ha'⟩ := exists_globalSection_of_iso W (tensorPowModuleOneIso W A).symm a
  induction m with
  | zero =>
      obtain ⟨c, hc⟩ := exists_globalSection_of_iso W (tensorPowModuleCongr W A
        (show (1 : ℤ) = ((0 : ℕ) : ℤ) + 1 by norm_num)) a'
      exact ⟨c, hc.trans ha'⟩
  | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨d, hd⟩ := exists_tensorGlobalSection W (tensorPowModule W A ((m : ℤ) + 1))
        (tensorPowModule W A 1) c a'
      let eAdd : tensorModules W (tensorPowModule W A ((m : ℤ) + 1)) (tensorPowModule W A 1) ≅
          tensorPowModule W A ((m : ℤ) + 1 + 1) := tensorPowModuleAddIso W A ((m : ℤ) + 1) 1
      obtain ⟨d', hd'⟩ := exists_globalSection_of_iso W eAdd d
      obtain ⟨e, he⟩ := exists_globalSection_of_iso W (tensorPowModuleCongr W A
        (show (m : ℤ) + 1 + 1 = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring)) d'
      exact ⟨e, by rw [he, hd', hd, hc, ha', Set.inter_self]⟩

/-- **Every positive multiple of a tensor power carries a section with the same nonvanishing
locus.** Given `s` a global section of `A^{⊗ n}` and `m ≥ 1`, the section
`s^{⊗ m}` of `(A^{⊗ n})^{⊗ m} ≅ A^{⊗ (n m)}` has the nonvanishing locus of `s`. This is what
lets two nonvanishing loci coming from sections of different powers be compared inside a
single common power. -/
theorem exists_globalSection_tensorPowModule_mul (A : W.Modules) [IsInvertibleModule W A]
    (n : ℕ) (s : Γ(tensorPowModule W A (n : ℤ), ⊤)) (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : Γ(tensorPowModule W A ((n * m : ℕ) : ℤ), ⊤),
      nonvanishingLocus (tensorPowModule W A ((n * m : ℕ) : ℤ)) c =
        nonvanishingLocus (tensorPowModule W A (n : ℤ)) s := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨c, hc⟩ := exists_powGlobalSection W (tensorPowModule W A (n : ℤ)) s j
  obtain ⟨c₁, hc₁⟩ := exists_globalSection_of_iso W (tensorPowModuleCongr W
    (tensorPowModule W A (n : ℤ)) (show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; ring)) c
  obtain ⟨c₂, hc₂⟩ := exists_globalSection_of_iso W (tensorPowModulePowIso W A (n : ℤ) (j + 1)) c₁
  obtain ⟨c₃, hc₃⟩ := exists_globalSection_of_iso W (tensorPowModuleCongr W A
    (show (n : ℤ) * ((j + 1 : ℕ) : ℤ) = ((n * (j + 1) : ℕ) : ℤ) by push_cast; ring)) c₂
  exact ⟨c₃, by rw [hc₃, hc₂, hc₁, hc]⟩

/-- **The pullback of a global section of a tensor power, and its nonvanishing locus.** The
section `p^* s` of `(p^* A)^{⊗ k}` is the image of `s` under the unit of the module-pullback
adjunction, read through Stacks Tag 01CD's comparison `p^*(A^{⊗ k}) ≅ (p^* A)^{⊗ k}`; its
nonvanishing locus is the inverse image of `W_s` by Stacks Tag 0H78. -/
theorem exists_pullbackGlobalSection_tensorPowModule {V : Scheme.{u}} (p : V ⟶ W)
    (A : W.Modules) [IsInvertibleModule W A] (k : ℕ)
    (s : Γ(tensorPowModule W A (k : ℤ), ⊤)) :
    ∃ c : Γ(tensorPowModule V ((modulePullback p.toLRSHom.toShHom).obj A) (k : ℤ), ⊤),
      nonvanishingLocus (tensorPowModule V ((modulePullback p.toLRSHom.toShHom).obj A) (k : ℤ)) c
        = p.base ⁻¹' nonvanishingLocus (tensorPowModule W A (k : ℤ)) s := by
  let ePull : Iso (C := V.Modules)
      ((modulePullback p.toLRSHom.toShHom).obj (tensorPowModule W A (k : ℤ)))
      (tensorPowModule V ((modulePullback p.toLRSHom.toShHom).obj A) (k : ℤ)) :=
    pullbackTensorPowModuleIso p A k
  refine ⟨ePull.hom.app ⊤
    (Stacks.NonvanishingPullback.pullbackGlobalSection p
      (tensorPowModule W A (k : ℤ)) s), ?_⟩
  exact (nonvanishingLocus_congr ePull _).trans
    (Stacks.NonvanishingPullback.preimage_nonvanishingLocus p
      (tensorPowModule W A (k : ℤ)) s).symm

end GlobalSections

section Absolute

variable {Z : Scheme.{u}}

/-- **Stacks Tag 0DNK over an affine base.** For `L` ample on `X`, `N` ample on `Y` and the
base `Z` affine, the external tensor product `pr₁^* L ⊗ pr₂^* N` is ample on `X ×_Z Y`.

This is the case Tag 0DNK's own proof reduces to, with `Z = Spec ℤ`; affineness of the base is
what it uses, through Tag 01WD's statement that in a fibre product over an affine base the
intersection of the preimages of two affine opens is affine.

At a point `z` with projections `x` and `y`, ampleness of `L` gives `n ≥ 1` and a section `s`
of `L^{⊗ n}` with `X_s` an affine open containing `x`, and ampleness of `N` gives `m ≥ 1` and
`t` of `N^{⊗ m}` with `Y_t` affine containing `y`. Both are carried into the common exponent
`n m` without changing their nonvanishing loci, pulled back to `X ×_Z Y`, and paired; the
result is a section of `(pr₁^* L ⊗ pr₂^* N)^{⊗ n m}` whose nonvanishing locus is
`pr₁^{-1} X_s ∩ pr₂^{-1} Y_t`, an affine open containing `z`. Quasi-compactness of the product
is quasi-compactness of `X` and `Y` over the affine, hence quasi-separated, base. -/
theorem isAmple_externalTensor_of_isAffine (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffine Z]
    (L : X.Modules) (N : Y.Modules) [IsInvertibleModule X L] [IsInvertibleModule Y N]
    (hL : IsAmple X L) (hN : IsAmple Y N) :
    IsAmple (pullback f g) (externalTensor f g L N) := by
  have : CompactSpace X := hL.1
  have : CompactSpace Y := hN.1
  refine ⟨inferInstance, fun z => ?_⟩
  obtain ⟨n, hn, s, U, hU, hxU, hUaff⟩ := hL.2 ((pullback.fst f g).base z)
  obtain ⟨m, hm, t, V, hV, hyV, hVaff⟩ := hN.2 ((pullback.snd f g).base z)
  obtain ⟨s', hs'⟩ := exists_globalSection_tensorPowModule_mul X L n s m hm
  obtain ⟨t₀, ht₀⟩ := exists_globalSection_tensorPowModule_mul Y N m t n hn
  obtain ⟨t', ht'⟩ := exists_globalSection_of_iso Y (tensorPowModuleCongr Y N
    (show ((m * n : ℕ) : ℤ) = ((n * m : ℕ) : ℤ) by push_cast; ring)) t₀
  obtain ⟨α, hα⟩ := exists_pullbackGlobalSection_tensorPowModule X (pullback.fst f g) L
    (n * m) s'
  obtain ⟨β, hβ⟩ := exists_pullbackGlobalSection_tensorPowModule Y (pullback.snd f g) N
    (n * m) t'
  obtain ⟨c, hc⟩ := exists_tensorGlobalSection (pullback f g)
    (tensorPowModule (pullback f g) (fstPullback f g L) ((n * m : ℕ) : ℤ))
    (tensorPowModule (pullback f g) (sndPullback f g N) ((n * m : ℕ) : ℤ)) α β
  refine ⟨n * m, Nat.one_le_iff_ne_zero.2 (by positivity),
    (Stacks.AmplePullbackPart1.tensorPowModuleTensorIso (pullback f g) (fstPullback f g L)
      (sndPullback f g N) (n * m)).symm.hom.app ⊤ c,
    pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V, ?_, ⟨hxU, hyV⟩,
    Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf f g hUaff hVaff⟩
  rw [nonvanishingLocus_congr, hc, hα, hβ, hs', ht', ht₀, ← hU, ← hV]
  rfl

end Absolute

section Reduction

variable (L : X.Modules) (N : Y.Modules)

/-- The comparison morphism `X ×_S Y ⟶ X ×_T Y` induced by a morphism `S ⟶ T` of bases. -/
abbrev baseChangeComparison {T : Scheme.{u}} (i : S ⟶ T) :
    pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.mapDesc f g i

/-- Pulling the external tensor product over a base `T` back along the comparison morphism
`X ×_S Y ⟶ X ×_T Y` returns the external tensor product over `S`: pullback commutes with the
tensor product, and each projection of `X ×_S Y` factors through the corresponding projection of
`X ×_T Y`. -/
def externalTensorComparisonIso {T : Scheme.{u}} (i : S ⟶ T) :
    (modulePullback (baseChangeComparison f g i).toLRSHom.toShHom).obj
        (externalTensor (f ≫ i) (g ≫ i) L N) ≅ externalTensor f g L N := by
  have hp : baseChangeComparison f g i ≫ pullback.fst (f ≫ i) (g ≫ i) = pullback.fst f g := by
    simp only [baseChangeComparison, pullback.mapDesc, pullback.map, pullback.lift_fst,
      Category.comp_id]
  have hq : baseChangeComparison f g i ≫ pullback.snd (f ≫ i) (g ≫ i) = pullback.snd f g := by
    simp only [baseChangeComparison, pullback.mapDesc, pullback.map, pullback.lift_snd,
      Category.comp_id]
  refine pullbackTensorModulesIso (baseChangeComparison f g i) _ _ ≪≫
    tensorModulesMapIso (pullback f g) ?_ ?_
  · exact (Scheme.Modules.pullbackComp (baseChangeComparison f g i)
      (pullback.fst (f ≫ i) (g ≫ i))).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L
  · exact (Scheme.Modules.pullbackComp (baseChangeComparison f g i)
      (pullback.snd (f ≫ i) (g ≫ i))).app N ≪≫ (Scheme.Modules.pullbackCongr hq).app N

variable [IsInvertibleModule X L] [IsInvertibleModule Y N]

/-- **Stacks Tag 0DNK, reduced to the absolute product: ampleness of an external tensor product
descends from `X ×_{Spec ℤ} Y`.** For `S` quasi-separated the comparison morphism
`X ×_S Y ⟶ X ×_{Spec ℤ} Y` is a quasi-compact immersion, and the external tensor product over
`S` is its pullback of the external tensor product over `Spec ℤ`, so ampleness transfers along
it by Tag 0B3E.

This is the half of Tag 0DNK that consumes quasi-separatedness. In place of the tag's hypothesis
that `L` and `N` are ample it assumes ampleness of the external tensor product on the absolute
product, so it does not state the tag on its own; the tag is carried by
`Stacks.AmpleExternalTensor.isAmple_externalTensor`, which discharges that hypothesis with
`Stacks.AmpleExternalTensor.isAmple_externalTensor_of_isAffine`. -/
theorem isAmple_externalTensor_of_isAmple_absolute [QuasiSeparatedSpace S]
    (h : IsAmple (pullback (f ≫ terminal.from S) (g ≫ terminal.from S))
      (externalTensor (f ≫ terminal.from S) (g ≫ terminal.from S) L N)) :
    IsAmple (pullback f g) (externalTensor f g L N) := by
  have hdiag : QuasiCompact (pullback.diagonal (terminal.from S)) := inferInstance
  have hjqc : QuasiCompact (baseChangeComparison f g (terminal.from S)) :=
    MorphismProperty.of_isPullback
      (pullback_map_diagonal_isPullback f g (terminal.from S)) hdiag
  have hji : IsImmersion (baseChangeComparison f g (terminal.from S)) := inferInstance
  have hPull := Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
    (baseChangeComparison f g (terminal.from S))
    (externalTensor (f ≫ terminal.from S) (g ≫ terminal.from S) L N) h (Or.inl ⟨hjqc, hji⟩)
  exact (isAmple_congr _ _ (externalTensorComparisonIso f g L N (terminal.from S))).mp hPull

/-- **Stacks Tag 0DNK.** Let `S` be a quasi-separated scheme, let `X` and `Y` be schemes over
`S`, let `L` be an ample invertible `𝒪_X`-module and `N` an ample invertible `𝒪_Y`-module. Then
`pr₁^* L ⊗_{𝒪_{X ×_S Y}} pr₂^* N` is an ample invertible module on `X ×_S Y`.

Invertibility is the instance `Stacks.AmpleExternalTensor.isInvertibleModule_externalTensor`,
which the statement of ampleness already presupposes. Ampleness is the composite of the two
halves proved above: the absolute case
`Stacks.AmpleExternalTensor.isAmple_externalTensor_of_isAffine`, taken at the terminal scheme
`Spec ℤ`, which is affine, and the descent
`Stacks.AmpleExternalTensor.isAmple_externalTensor_of_isAmple_absolute` along the quasi-compact
immersion `X ×_S Y ⟶ X ×_{Spec ℤ} Y`, which is where quasi-separatedness of `S` is used. -/
@[stacks 0DNK "the whole lemma: for `S` quasi-separated, `X` and `Y` schemes over `S`, `L` ample
invertible on `X` and `N` ample invertible on `Y`, the external tensor product
`pr₁^* L ⊗ pr₂^* N` is ample on `X ×_S Y`. Invertibility of that module, the other half of the
tag's conclusion, is the instance `isInvertibleModule_externalTensor` of this file, which the
statement uses. No hypothesis beyond the tag's own."]
theorem isAmple_externalTensor [QuasiSeparatedSpace S] (hL : IsAmple X L) (hN : IsAmple Y N) :
    IsAmple (pullback f g) (externalTensor f g L N) :=
  isAmple_externalTensor_of_isAmple_absolute f g L N
    (isAmple_externalTensor_of_isAffine (f ≫ terminal.from S) (g ≫ terminal.from S) L N hL hN)

end Reduction

end Stacks.AmpleExternalTensor

end
