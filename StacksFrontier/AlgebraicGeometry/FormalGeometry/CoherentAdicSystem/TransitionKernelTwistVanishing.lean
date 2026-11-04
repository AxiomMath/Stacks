module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded
public import StacksFrontier.AlgebraicGeometry.HighTwistVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound

/-!
# Uniform vanishing of `H¹` of the twisted transition kernels of a coherent adic system

**Stacks 0884.** Let `A` be a Noetherian ring and `I ⊆ A` an ideal, let `f : X ⟶ Spec A` be
proper, let `L` be an `f`-ample invertible sheaf and put `𝓘 = I · 𝒪_X`. Let `(F_n)` be an object
of `Coh(X, 𝓘)`. Then there is an integer `d₀` with

  `H¹(X, Ker(F_{n+1} ⟶ F_n) ⊗ L ^⊗ d) = 0`  for all `n ≥ 0` and all `d ≥ d₀`.

The point is the **uniformity**: one `d₀` serves every term of the system at once. That is what
makes the transition maps on `H⁰(X, F_n ⊗ L ^⊗ d)` surjective simultaneously, which is how the
source generates an arbitrary object of `Coh(X, 𝓘)` by the completion of a coherent module in the
proof of Stacks 0885.

## The route, and what is assumed

The source's proof is two steps. Put `B = ⨁ Iⁿ/Iⁿ⁺¹` and
`𝓑 = ⨁ 𝓘ⁿ/𝓘ⁿ⁺¹ = f^* B̃`. Then

* **Stacks 087Z**: the graded `𝓑`-module `𝓖 = ⨁ Ker(F_{n+1} ⟶ F_n)` is quasi-coherent of finite
  type. This is **proved unconditionally** in this library, as
  `Stacks.Coherent.finiteTypeAssociatedGradedData`, which produces a
  `Stacks.Coherent.AssociatedGradedData` — the graded algebra, the graded module, and
  isomorphisms of its homogeneous pieces with the transition kernels. It is discharged here, not
  assumed.
* **Stacks 0897 part (2)**: for such a graded module and an ample `L`, the twists
  `𝓖 ⊗ L ^⊗ d` have vanishing higher cohomology for `d ≫ 0`, uniformly in the degree. **This
  library does not carry 0897**, so it is the named hypothesis
  `Stacks.Coherent.HasAssociatedGradedTwistVanishing`, stated only for the associated graded
  algebra of an ideal sheaf — the single instance 0884 needs, and strictly weaker than 0897 (2)
  itself.

The source's hypothesis is that `L` be `f`-ample, while 0897 wants `L` ample; over the affine base
`Spec A` these agree by Stacks 01VK, which is proved
(`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`). So the hypothesis below is
stated, as in the source, for `Stacks.RelativeAmple.IsRelativelyAmple f L`, and the conversion is
performed rather than assumed.

## Main definitions

* `Stacks.Coherent.transitionKernel` — the source's `Ker(F_{n+1} ⟶ F_n)`, in the source's
  indexing.
* `Stacks.Coherent.HasAssociatedGradedTwistVanishing` — Stacks 0897 part (2) for the associated
  graded algebra of `I · 𝒪_X`; the one hypothesis of the theorem below.

## Main results

* `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule` — the vanishing, with
  `HasAssociatedGradedTwistVanishing` as its only hypothesis; a special case of
  `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_isRelativelyAmple`,
  which has the source's hypotheses only.

## Implementation notes

**Indexing.** `Stacks.Coherent.CoherentAdicSystems` is zero-indexed: its term `n` is the source's
`F_{n+1}`, the source's system starting at `F_1` with `F_0 = 0`. The source's
`Ker(F_{n+1} ⟶ F_n)` is therefore the zeroth term itself when `n = 0`, and the kernel of the
system's `n`-th transition map when `n > 0`. `Stacks.Coherent.transitionKernel` is that family,
and it is the `ℕ`-indexed part of the family `AssociatedGraded.lean` grades the associated graded
module by; that family is private there, so it is re-stated here rather than reused.

**The twist and the cohomology.** The twist is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` of Stacks 05NA applied to the tensor
powers of Stacks 01CU through `Stacks.Ample.tensorPowModule`, and `H¹(X, -)` is the repository's
`Hgroup X.ringCatSheaf ⊤ 1`, the right derived functor of global sections. This is the spelling of
`Stacks.HighTwistVanishing.HasHighTwistVanishing`, so the statement below is that property's
uniform-in-`n` strengthening along a coherent adic system, written in the same terms. Exponents
are integers, as the source's `d₀` is.

**No `Scheme.Modules` barrier is met.** The only transport needed is along an isomorphism of
`𝒪_X`-modules, and it is performed exactly as `Stacks.HighTwistVanishing.of_iso` does it: the
twist is the value of `(Stacks.SheafOfModules.Tensor.sheafTensor _).flip` on the nose, so
`Functor.mapIso` applies with no change of spelling and no `rw`.

**Local Noetherianity is not an extra hypothesis.** Stacks 087Z asks for `IsNoetherian X`, and
properness over a Noetherian affine base supplies it: `LocallyOfFiniteType f` gives
`IsLocallyNoetherian X`, and `UniversallyClosed f` gives `QuasiCompact f` and hence
`CompactSpace X`, as in `CompletionProjective.lean`.

**What this does not do.** It is the cohomological input to the generation statement `hGen` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjective.lean`, not that statement. Two
further steps of the proof of Stacks 0885 separate them: the long exact sequence turning this
`H¹` vanishing into surjectivity of `H⁰(X, F_{n+1} ⊗ L ^⊗ d) ⟶ H⁰(X, F_n ⊗ L ^⊗ d)`, and the
assembly of the lifted sections into a morphism out of the completion of
`(L ^⊗ (-d))^{⊕ t}`, which is then an epimorphism by Stacks 087Y
(`Stacks.Coherent.epi_iff_epi_app_zero`). The global generation of `F_1 ⊗ L ^⊗ d` that the
assembly starts from is clause (7) of Stacks 01Q3
(`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple`).

## References

* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace Stacks.Coherent

/-! ### The transition kernels, in the source's indexing -/

/-- **The source's `Ker(F_{n+1} ⟶ F_n)`** for an object `F` of `Coh(X, ℐ)`.

`CoherentAdicSystems` is zero-indexed, its term `n` being the source's `F_{n + 1}`; the source's
system begins at `F_1` and has `F_0 = 0`. So at `n = 0` the kernel is the zeroth term itself, and
at `n + 1` it is the kernel of the system's `n`-th transition map. -/
public def transitionKernel {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) : ℕ → X.Modules
  | 0 => F.obj.obj (op 0)
  | n + 1 => kernel (F.obj.map (homOfLE (Nat.le_succ n)).op)

/-! ### Stacks 0897 part (2) for the associated graded algebra of an ideal sheaf -/

/-- **Stacks 0897 part (2), for the associated graded algebra of `I · 𝒪_X`.**

Let `D` present the associated graded algebra `⨁ 𝓘ⁿ/𝓘ⁿ⁺¹` of `𝓘 = I · 𝒪_X` — this is what
`Stacks.Coherent.AssociatedGradedAlgebraData` pins down, its homogeneous pieces being identified
with `Iⁿ/Iⁿ⁺¹` on every affine open, linearly over the structure sheaf. The assertion is that for
every quasi-coherent graded `D.algebra`-module `M` of finite type and every ample `L` there is an
integer `d₀` with `Hᵖ(X, M_n ⊗ L ^⊗ d) = 0` for all `p > 0`, all degrees `n`, and all `d ≥ d₀` —
one `d₀` for all three at once.

This is the restriction of Stacks 0897 part (2) to the graded algebras 0884 needs it for, so
assuming it is weaker than assuming 0897. The source gets the finite generation of `B = ⨁ Iⁿ/Iⁿ⁺¹`
over `A`, which 0897 requires, from Noetherianity of `A`; it is not recorded here, being a
property of `D` rather than a further hypothesis to be met. -/
public def HasAssociatedGradedTwistVanishing (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : Prop :=
  Stacks.Ample.IsAmple X L →
    ∀ (D : AssociatedGradedAlgebraData (baseIdealSheaf A I f))
      (M : SheafOfModules.GradedModule D.algebra),
      (∀ n : ℤ, (M.piece n).IsQuasicoherent) → IsFiniteTypeOnAffine M →
      ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
        IsZero (Hgroup X.ringCatSheaf ⊤ p
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp
              _ (X.presheaf) (forget₂ CommRingCat RingCat)
                  ((isSheaf_structureRingPresheaf
                      X))⟩).obj ((M.piece n))).obj ((Stacks.Ample.tensorPowModule X L d)))))

/-! ### Stacks 0884 -/

/-- Vanishing of the cohomology of a twist is an isomorphism invariant of the module being
twisted: the twist is the value of `Stacks.SheafOfModules.Tensor.sheafTensor`, flipped, and
`Hᵖ(X, -)` is a functor, so `Functor.mapIso` transports it. -/
private theorem isZero_Hgroup_tensorPowModule_of_iso {X : Scheme.{u}} {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] {F G : X.Modules} (e : F ≅ G) (d : ℤ) (p : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ p
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) ((isSheaf_structureRingPresheaf X))⟩).obj (F)).obj ((Stacks.Ample.tensorPowModule X L d)))))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) ((isSheaf_structureRingPresheaf X))⟩).obj (G)).obj ((Stacks.Ample.tensorPowModule X L d))))) :=
  (Iso.isZero_iff ((Hfunctor X.ringCatSheaf ⊤ p).mapIso
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          ((isSheaf_structureRingPresheaf X))⟩).flip.obj
      (Stacks.Ample.tensorPowModule X L d)).mapIso e))).mp h

/-- A special case of
`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_isRelativelyAmple`, with
the extra hypothesis below. Let `A` be a Noetherian ring, `I ⊆ A` an ideal,
`f : X ⟶ Spec A` a proper morphism and `L` an invertible `𝒪_X`-module ample relative to `f`.
Let `𝓕` be an object of `Coh(X, 𝓘)` for `𝓘 = I · 𝒪_X`. Then there is an integer `d₀` such that

  `H¹(X, Ker(𝓕_{n+1} ⟶ 𝓕_n) ⊗ L ^⊗ d) = 0`

for every `n ≥ 0` and every `d ≥ d₀` — one `d₀` for the whole system.

The hypothesis is Stacks 0897 part (2) for the associated graded algebra of `𝓘`, as
`Stacks.Coherent.HasAssociatedGradedTwistVanishing`; nothing else is assumed. Stacks 087Z, which
exhibits `⨁ Ker(𝓕_{n+1} ⟶ 𝓕_n)` as a quasi-coherent graded module of finite type over that
algebra, is supplied by `Stacks.Coherent.finiteTypeAssociatedGradedData`, and relative ampleness
is converted to ampleness over the affine base by Stacks 01VK. -/
public theorem exists_isZero_Hgroup_transitionKernel_tensorPowModule
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f))
    (h0897 : HasAssociatedGradedTwistVanishing A I f L) :
    ∃ d₀ : ℤ, ∀ (n : ℕ) (d : ℤ), d₀ ≤ d →
      IsZero (Hgroup X.ringCatSheaf ⊤ 1
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) ((isSheaf_structureRingPresheaf X))⟩).obj ((transitionKernel 𝓕 n))).obj ((Stacks.Ample.tensorPowModule X L d))))) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := { }
  obtain ⟨D⟩ := finiteTypeAssociatedGradedData (baseIdealSheaf A I f) 𝓕
  have hample : Stacks.Ample.IsAmple X L :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp hL
  obtain ⟨d₀, hd₀⟩ :=
    h0897 hample D.toAssociatedGradedAlgebraData D.module D.moduleQuasicoherent D.finiteType
  refine ⟨d₀, fun n d hd => ?_⟩
  cases n <;> refine isZero_Hgroup_tensorPowModule_of_iso ?_ d 1 (hd₀ d hd 1 Nat.one_pos ?_)
  exacts [D.modulePieceZero, D.modulePieceSucc _]

end Stacks.Coherent

end
