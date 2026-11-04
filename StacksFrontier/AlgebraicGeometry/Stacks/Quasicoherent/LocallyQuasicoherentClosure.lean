module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian

/-!
# Colimits, kernels, cokernels and extensions of locally quasi-coherent modules (Stacks 06WM)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `LQCoh(𝒪_𝒳)` be the full
subcategory of the étale sheaves of `𝒪_𝒳`-modules which are locally quasi-coherent in the sense
of Stacks 06WJ.  This file proves the first three clauses of Stacks 06WM:

1. `LQCoh(𝒪_𝒳)` has colimits and they agree with colimits in `Mod(𝒳_ét, 𝒪_𝒳)`;
2. `LQCoh(𝒪_𝒳)` is abelian, with kernels and cokernels computed in `Mod(𝒳_ét, 𝒪_𝒳)`, so that its
   inclusion is exact;
3. in a short exact sequence of `Mod(𝒳_ét, 𝒪_𝒳)`, if two out of three terms are locally
   quasi-coherent so is the third.

Clause (4), the tensor product, is
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_tensorSheaf`, and clause (5), the internal Hom out
of a module of finite presentation, is
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_etaleInternalHom`.

The proof is the source's: local quasi-coherence is quasi-coherence of the restrictions
`x^*F|_{U_ét}`, the restriction functor commutes with limits and colimits
(`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian`), so it carries
each construction to the corresponding construction on the small étale site of `U`, where
Descent, Lemma 0GNB gives quasi-coherence.

## Main results

* `AlgebraicGeometry.Stack.locallyQuasicoherentModules_colimits`: **Stacks 06WM (1)**.
* `AlgebraicGeometry.Stack.locallyQuasicoherentModules_abelian`: **Stacks 06WM (2)**.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_twoOutOfThree`: **Stacks 06WM (3)**.

## Implementation notes

Sections of modules lie in the universe `u` of the schemes, as for sheaves of sets on the sites
of the source, and colimits are indexed by categories in that universe.  The ambient category
`Mod(𝒳_ét, 𝒪_𝒳)` has colimits and is abelian at that universe with no hypothesis on `𝒳`: every
slice `𝒳/x` is essentially small by Stacks 06W0, which is enough for abelian presheaves on the
associated étale site to have a sheafification whose weak equivalences are the locally bijective
maps (`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`); those instances are
supplied inside the proofs.

## References

* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Local quasi-coherence contains a zero object: the restrictions of a zero module are zero
modules, which are quasi-coherent. -/
instance containsZero_isLocallyQuasicoherent :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).ContainsZero :=
  haveI := hasSheafify_etaleAssociatedTopology B S hS p hp
  haveI := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  ⟨⊤_ _, terminalIsTerminal.isZero, ObjectProperty.prop_terminal _⟩

/-- Local quasi-coherence is closed under both kernels and cokernels. -/
private theorem isClosedUnder_kernels_and_cokernels :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderKernels ∧
      (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderCokernels := by
  have := hasSheafify_etaleAssociatedTopology B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  exact ⟨isClosedUnderKernels_isLocallyQuasicoherent B E h S hS p hp,
    isClosedUnderCokernels_isLocallyQuasicoherent B E h S hS p hp⟩

/-- **Stacks 06WM (1).** The category `LQCoh(𝒪_𝒳)` of locally quasi-coherent modules has
colimits, and they agree with colimits in `Mod(𝒳_ét, 𝒪_𝒳)`: local quasi-coherence is closed under
colimits computed in `Mod(𝒳_ét, 𝒪_𝒳)`, the full subcategory therefore has them, and its
inclusion preserves them. -/
@[stacks 06WM "(1): LQCoh(𝒪_𝒳) has colimits and they agree with colimits in Mod(𝒳_ét, 𝒪_𝒳)"]
theorem locallyQuasicoherentModules_colimits :
    (∀ (K : Type u) [Category.{u} K],
      (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderColimitsOfShape K) ∧
      HasColimitsOfSize.{u, u} (locallyQuasicoherentModules.{u, v, w, u} B E h S hS p hp) ∧
      PreservesColimitsOfSize.{u, u} (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).ι := by
  have := hasSheafify_etaleAssociatedTopology B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  have h := isClosedUnderColimitsOfShape_isLocallyQuasicoherent B E h S hS p hp
  refine ⟨fun K _ => h K, ⟨fun K _ => ?_⟩, ⟨fun {K} _ => ?_⟩⟩ <;> (have := h K; infer_instance)

/-- **Stacks 06WM (2).** The category `LQCoh(𝒪_𝒳)` is abelian, with kernels and cokernels
computed in `Mod(𝒳_ét, 𝒪_𝒳)`: local quasi-coherence is closed under kernels and cokernels, so
the full subcategory is abelian and its inclusion into `Mod(𝒳_ét, 𝒪_𝒳)` is exact. -/
@[stacks 06WM "(2): LQCoh(𝒪_𝒳) is abelian with kernels and cokernels computed in \
Mod(𝒳_ét, 𝒪_𝒳), i.e. the inclusion is exact"]
theorem locallyQuasicoherentModules_abelian :
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderKernels ∧
      (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsClosedUnderCokernels ∧
      Nonempty (Abelian (locallyQuasicoherentModules.{u, v, w, u} B E h S hS p hp)) ∧
      PreservesFiniteLimits (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).ι ∧
      PreservesFiniteColimits (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).ι := by
  have := hasSheafify_etaleAssociatedTopology B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  let P := isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp
  obtain ⟨_, _⟩ := isClosedUnder_kernels_and_cokernels B E h S hS p hp
  have : P.IsClosedUnderFiniteProducts :=
    isClosedUnderFiniteProducts_isLocallyQuasicoherent B E h S hS p hp
  have : P.ContainsZero := containsZero_isLocallyQuasicoherent B E h S hS p hp
  let hA : Abelian P.FullSubcategory := inferInstance
  have : HasFiniteBiproducts P.FullSubcategory := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts P.FullSubcategory := hasFiniteCoproducts_of_hasFiniteBiproducts _
  refine ⟨inferInstance, inferInstance, ⟨hA⟩, ?_, ?_⟩
  · have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) P.ι :=
      fun f => P.preservesKernels_ι f
    exact Functor.preservesFiniteLimits_of_preservesKernels P.ι
  · have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) P.ι :=
      fun f => P.preservesCokernels_ι f
    exact Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- **Stacks 06WM (3).** In a short exact sequence `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` of
`Mod(𝒳_ét, 𝒪_𝒳)`, if two of the three terms are locally quasi-coherent then so is the third.
A cokernel and a kernel of a morphism of locally quasi-coherent modules are locally
quasi-coherent by Stacks 06WM (2); for the middle term the restriction to the small étale site of
the scheme below an object is exact, so it carries the sequence to a short exact sequence there,
and an extension of quasi-coherent modules on a small étale site is quasi-coherent (Descent,
Lemma 0GNB). -/
@[stacks 06WM "(3): in a short exact sequence of Mod(𝒳_ét, 𝒪_𝒳), if two out of three terms are \
locally quasi-coherent so is the third"]
theorem isLocallyQuasicoherent_twoOutOfThree
    (T : ShortComplex (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))))
    (hT : T.ShortExact) :
    (IsLocallyQuasicoherent B E h S hS p hp T.X₁.val →
        IsLocallyQuasicoherent B E h S hS p hp T.X₂.val →
          IsLocallyQuasicoherent B E h S hS p hp T.X₃.val) ∧
      (IsLocallyQuasicoherent B E h S hS p hp T.X₂.val →
        IsLocallyQuasicoherent B E h S hS p hp T.X₃.val →
          IsLocallyQuasicoherent B E h S hS p hp T.X₁.val) ∧
      (IsLocallyQuasicoherent B E h S hS p hp T.X₁.val →
        IsLocallyQuasicoherent B E h S hS p hp T.X₃.val →
          IsLocallyQuasicoherent B E h S hS p hp T.X₂.val) := by
  have := hasSheafify_etaleAssociatedTopology B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  let P := isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp
  obtain ⟨_, _⟩ := isClosedUnder_kernels_and_cokernels B E h S hS p hp
  refine ⟨fun h₁ h₂ => P.prop_of_isColimit_cokernelCofork hT.gIsCokernel h₁ h₂,
    fun h₂ h₃ => P.prop_of_isLimit_kernelFork hT.fIsKernel h₂ h₃, fun h₁ h₃ => ?_⟩
  refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_
  let r := restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x
  exact (SheafOfModules.isQuasicoherentOnSite _).prop_X₂_of_shortExact (hT.map_of_exact r)
    ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 h₁ x)
    ((isLocallyQuasicoherent_iff B E h S hS p hp _).1 h₃ x)

end AlgebraicGeometry.Stack

end
