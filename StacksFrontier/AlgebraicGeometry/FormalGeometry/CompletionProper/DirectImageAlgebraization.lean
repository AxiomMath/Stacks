module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AlgebraizationHelpers
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMapQuotientAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ReductionCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GrothendieckExistenceII
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The map `α` of Stacks 088B, over an algebraizable system

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent
sheaves of ideals and set `ℐ = f^{-1}𝒥 𝒪_X`. Stacks 088B produces, for an object `(𝒢_n)` of
`Coh(Y, 𝒥)`, a coherent `𝒪_X`-module `𝓕` and an isomorphism `β : (f^*𝒢_n) ⟶ 𝓕^∧` in
`Coh(X, ℐ)`, a morphism

`α : (𝒢_n) ⟶ (f_*𝓕)^∧`

in `Coh(Y, 𝒥)` whose levelwise kernels and cokernels are annihilated by a power of `𝒦`.

This file builds `α`. It builds it in the position the source's proof reaches at its **last
paragraph**, after the reduction to an affine base `Y = Spec(B)` complete along `𝒥`: there `(𝒢_n)`
is the completion of a coherent module `𝒢` (an affine complete base makes every object of
`Coh(Y, 𝒥)` algebraizable, by Stacks 087W — this library's
`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete`), the isomorphism `β` descends by
Stacks 0883 to an
isomorphism `b : f^*𝒢 ⟶ 𝓕`, and

`α` is the completion of the composite `c : 𝒢 ⟶ f_*f^*𝒢 --f_*b--> f_*𝓕`

of the adjunction map with `f_*b`. The algebraization `𝒢` of `(𝒢_n)` and the descent `b` of `β`
are the two inputs taken as hypotheses; everything the source does with them — the construction
of `α`, the coherence of its target, the bound on the kernel and cokernel of `c` and the passage
from that bound to the levelwise bound on `α` — is proved. See the implementation notes for
exactly what stands between these hypotheses and the source's own.

## Main results

* `Stacks.Coherent.properDirectImageCompletionMap` — **the map `α`**, as the completion of
  `c : 𝒢 ⟶ f_*f^*𝒢 ⟶ f_*𝓕` read through the algebraization of `(𝒢_n)`.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_properDirectImageCompletionMap` — its
  levelwise kernels and cokernels are annihilated by a power of `𝒦`.
* `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage` — **the
  conclusion of Stacks 088B for an algebraizable system**: existence of `α` with the annihilation
  property, which is exactly the hypothesis `hα` of Stacks 088A
  (`Stacks.Coherent.essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower`).

## Implementation notes

The target of `α` is `(f_*𝓕)^∧`, and even to write it down one needs `f_*𝓕` to be coherent; that
is Stacks 02O5, available unconditionally as
`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`.

The bound on `c` is the closing paragraph of the source, already available as
`Stacks.Coherent.exists_pos_idealPowerMultiple_kernel_cokernel_eq_bot`. As there, the hypothesis
is in the form in which the source uses it at that point of the argument, namely that the
restriction of the adjunction map to `V = Y ∖ V(𝒦)` is an isomorphism — which the source deduces
from `f` being an isomorphism over `V`. The restriction of `c` is then an isomorphism too,
`f_*b` being one.

The passage from `Ker(c)`, `Coker(c)` to the levelwise `Ker(α_n)`, `Coker(α_n)` is the remark of
Stacks 0888 over sheaves: the `n`-th component of `c ^∧` is the reduction of `c` modulo
`𝒥 ⁿ⁺¹`, and the kernel and cokernel of a
reduction are annihilated by `𝒦 ²ᵗ` and `𝒦 ᵗ` respectively
(`Stacks.Algebraization.idealPowerMultiple_kernel_idealPowerQuotientMap_eq_bot` and
`Stacks.Algebraization.idealPowerMultiple_cokernel_idealPowerQuotientMap_eq_bot`). Composing with
the algebraization isomorphism `(𝒢_n) ≅ 𝒢 ^∧` changes neither the levelwise kernels nor the
levelwise cokernels, by `CategoryTheory.Limits.kernel.mapIso` and
`CategoryTheory.Limits.cokernel.mapIso`.

**What is still assumed, and why.** Two inputs are hypotheses rather than theorems here.

* The algebraization `𝒢` of `(𝒢_n)`, i.e. the isomorphism `e : (𝒢_n) ≅ 𝒢 ^∧`. Over an affine base
  complete along `𝒥` this is **not** an open problem here: it is
  `Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete`, Grothendieck existence in the
  affine case, proved unconditionally from Stacks 087W
  (`Stacks.Coherent.coherentAdicSystemsEquivFGModuleCat`). What is missing is the source's
  *reduction* to such a base — the first two paragraphs of its proof, where the uniqueness of `α`
  makes the question local on `Y` so that `Y` may be taken affine, and where the flat base change
  along `B ⟶ B ^∧` lets `B` be taken complete (More on Algebra 15.91.3 for the equivalence of the
  categories of modules killed by `J ⁿ` over `B` and over `B ^∧`). Neither the locality argument
  nor that descent is formalized, so `e` is a hypothesis here rather than being produced from the
  affine case.
* The descent `b : f^*𝒢 ⟶ 𝓕` of the source's `β : (f^*𝒢_n) ⟶ 𝓕 ^∧`. Full faithfulness of
  completion on `X` is unconditional for a proper morphism over a complete base,
  `Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper`, so it would supply `b`
  from `β` as soon as `β` were presented as a morphism *between completions on `X`*. That needs
  the compatibility of pullback with completion, `f^*(𝒢 ^∧) ≅ (f^*𝒢) ^∧`, which this library does
  not carry: `Stacks.Coherent.coherentAdicPullback` is termwise pullback and
  `Stacks.Coherent.exists_functor_idealPowerQuotient_iso` would give the comparison termwise,
  but no natural isomorphism of systems is assembled from it anywhere.

Because of those two, **no `@[stacks 088B]` attribute is attached to anything in this file**: the
statements below carry hypotheses standing in for content of the source's proof. The partial
attributions already recorded for the tag — the maps `γ_n` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/DirectImageComparison.lean` and the
closing paragraph of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ExceptionalAnnihilation.lean` — are
unchanged.

The maps `γ_n` of `Stacks.Coherent.directImageComparison` are *not* used. The source introduces
them to characterize `α` uniquely, and that characterization is what its reduction to the affine
case rests on; the statement of Stacks 088B asserts only that some `α` with the annihilation
property exists, which is also all that Stacks 088A consumes, so `α` is built here directly from
`c`. Relating the `α` built here to `γ` would again need `f^*(𝒢 ^∧) ≅ (f^*𝒢) ^∧`.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

/-- The kernel and cokernel of a morphism are annihilated by `𝒦 ᵗ` as soon as those of an
isomorphic morphism (a commuting square with isomorphic sides) are. -/
private theorem idealPowerMultiple_kernel_cokernel_eq_bot_of_square {Y : Scheme.{u}}
    (K : Y.IdealSheafData) {A B A' B' : Y.Modules} (φ : A ⟶ B) (φ' : A' ⟶ B') (e₁ : A ≅ A')
    (e₂ : B ≅ B') (w : φ ≫ e₂.hom = e₁.hom ≫ φ') {t : ℕ}
    (h : idealPowerMultiple K t (kernel φ') = ⊥ ∧ idealPowerMultiple K t (cokernel φ') = ⊥) :
    idealPowerMultiple K t (kernel φ) = ⊥ ∧ idealPowerMultiple K t (cokernel φ) = ⊥ :=
  ⟨idealPowerMultiple_eq_bot_of_iso K (kernel.mapIso φ φ' e₁ e₂ w) t h.1,
    idealPowerMultiple_eq_bot_of_iso K (cokernel.mapIso φ φ' e₁ e₂ w) t h.2⟩

/-- Composing a morphism of inverse systems with an isomorphism on the *source* changes neither
the levelwise kernels nor the levelwise cokernels, so it preserves annihilation of them by a
power of `𝒦`.

The companion `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff` does the same for
an isomorphism on the target. -/
public theorem isKernelCokernelAnnihilatedByPower_iso_comp {Y : Scheme.{u}}
    (K : Y.IdealSheafData) {A B C : ℕᵒᵖ ⥤ Y.Modules} (e : A ≅ B) (φ : B ⟶ C)
    (h : IsKernelCokernelAnnihilatedByPower K φ) :
    IsKernelCokernelAnnihilatedByPower K (e.hom ≫ φ) := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t, ht, fun n => idealPowerMultiple_kernel_cokernel_eq_bot_of_square K _ _
    (e.app (op n)) (Iso.refl _) (by simp) (h n)⟩

/-! ### The direct image of a coherent module along a proper morphism -/

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]

/-- The direct image of a coherent module along a proper morphism onto a locally Noetherian base,
as a coherent module. Coherence is [Stacks, Tag 02O5], unconditional. -/
public def properPushforwardCoherent
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf :=
  haveI : F.obj.IsCoherent := F.property
  ⟨(Scheme.Modules.pushforward f).obj F.obj,
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f F.obj⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Its underlying module is the direct image. -/
public theorem properPushforwardCoherent_obj
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (properPushforwardCoherent f F).obj = (Scheme.Modules.pushforward f).obj F.obj :=
  rfl

/-! ### The map `c : 𝒢 ⟶ f_*f^*𝒢 ⟶ f_*𝓕` and the map `α` -/

variable (J K : Y.IdealSheafData)
  (𝒢 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (b : (Scheme.Modules.pullback f).obj 𝒢.obj ≅ F.obj)

/-- **The map `c : 𝒢 ⟶ f_*f^*𝒢 --f_*b--> f_*𝓕` of the last paragraph of Stacks 088B**, as a
morphism of coherent `𝒪_Y`-modules: the adjunction map followed by the direct image of the
descended isomorphism `b : f^*𝒢 ⟶ 𝓕`. -/
public def properAdjunctionDescent : 𝒢 ⟶ properPushforwardCoherent f F :=
  ObjectProperty.homMk
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj ≫
      (Scheme.Modules.pushforward f).map b.hom)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Its underlying morphism is the composite. -/
public theorem properAdjunctionDescent_hom :
    (properAdjunctionDescent f 𝒢 F b).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj ≫
        (Scheme.Modules.pushforward f).map b.hom :=
  rfl

/-- **The map `α : (𝒢_n) ⟶ (f_*𝓕) ^∧` of Stacks 088B, for an algebraizable system.** Given an
algebraization `e : (𝒢_n) ≅ 𝒢 ^∧` of the system and a descent `b : f^*𝒢 ⟶ 𝓕` of the source's
isomorphism `β`, it is the completion of `c : 𝒢 ⟶ f_*f^*𝒢 ⟶ f_*𝓕`, read through `e`. -/
public def properDirectImageCompletionMap (G : CoherentAdicSystems J)
    (e : G.obj ≅ ((completionFunctor Y J).obj 𝒢).obj) :
    G.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj :=
  e.hom ≫ ((completionFunctor Y J).map (properAdjunctionDescent f 𝒢 F b)).hom

/-! ### The kernel and cokernel of `α` -/

/-- **The kernel and cokernel bound of Stacks 088B.** With `V = Y ∖ V(𝒦)`, suppose the
restriction to `V` of the adjunction map `𝒢 ⟶ f_*f^*𝒢` is an isomorphism — the form in which the
source uses that `f` is an isomorphism over `V`. Then the levelwise kernels and cokernels of
`α = ` `Stacks.Coherent.properDirectImageCompletionMap` are annihilated by a power of `𝒦`.

The restriction of `c = 𝒢 ⟶ f_*f^*𝒢 ⟶ f_*𝓕` to `V` is an isomorphism too, `f_*b` being one, so
`Stacks.Coherent.exists_pos_idealPowerMultiple_kernel_cokernel_eq_bot` — the closing paragraph of
the source — annihilates `Ker(c)` and `Coker(c)` by one positive power of `𝒦`. The levelwise
statement for `c ^∧` is
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_completionFunctor_map`, and composing with
`e` changes nothing. -/
public theorem isKernelCokernelAnnihilatedByPower_properDirectImageCompletionMap
    (G : CoherentAdicSystems J) (e : G.obj ≅ ((completionFunctor Y J).obj 𝒢).obj)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj))) :
    IsKernelCokernelAnnihilatedByPower K
      (properDirectImageCompletionMap f J 𝒢 F b G e) := by
  have : 𝒢.obj.IsCoherent := 𝒢.property
  have : F.obj.IsCoherent := F.property
  have : ((𝟭 Y.Modules).obj 𝒢.obj).IsCoherent := 𝒢.property
  have : ((Scheme.Modules.pullback f).obj 𝒢.obj).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback f 𝒢.obj
  have : ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj 𝒢.obj)).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _
  have : ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).obj 𝒢.obj).IsCoherent :=
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f
      ((Scheme.Modules.pullback f).obj 𝒢.obj)
  -- the closing paragraph of the source, applied to the adjunction map itself
  obtain ⟨t, ht, hker₀, hcok₀⟩ :=
    exists_pos_idealPowerMultiple_kernel_cokernel_eq_bot K
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj) hc
  -- `c` differs from the adjunction map by the isomorphism `f_*b`, which changes neither the
  -- kernel nor the cokernel
  obtain ⟨hker, hcok⟩ := idealPowerMultiple_kernel_cokernel_eq_bot_of_square K
    (properAdjunctionDescent f 𝒢 F b).hom
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj) (Iso.refl _)
    ((Scheme.Modules.pushforward f).mapIso b.symm)
    (by
      erw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.comp_id]) ⟨hker₀, hcok₀⟩
  exact isKernelCokernelAnnihilatedByPower_iso_comp K e _
    (isKernelCokernelAnnihilatedByPower_completionFunctor_map J K
      (properAdjunctionDescent f 𝒢 F b) ht hker hcok)

include b in
/-- **The conclusion of Stacks 088B for an algebraizable system.** Let `f : X ⟶ Y` be a proper
morphism of Noetherian schemes, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals, let
`(𝒢_n)` be an object of `Coh(Y, 𝒥)` algebraized by a coherent module `𝒢`, let `𝓕` be a coherent
`𝒪_X`-module and let `b : f^*𝒢 ⟶ 𝓕` be an isomorphism. If the restriction of the adjunction map
`𝒢 ⟶ f_*f^*𝒢` to `V = Y ∖ V(𝒦)` is an isomorphism, then there is a morphism

`α : (𝒢_n) ⟶ (f_*𝓕) ^∧`

of inverse systems of `𝒪_Y`-modules whose levelwise kernels and cokernels are annihilated by a
power of `𝒦`.

This is the shape in which [Stacks, Tag 088A] consumes the lemma, namely the pair of hypotheses
`α` and `hα` of
`Stacks.Coherent.essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower`. The two
hypotheses it carries beyond the source's — the algebraization of `(𝒢_n)` and the descent of `β`
— are discussed in the module docstring. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_properDirectImage
    (G : CoherentAdicSystems J) (e : G.obj ≅ ((completionFunctor Y J).obj 𝒢).obj)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj,
      IsKernelCokernelAnnihilatedByPower K α :=
  ⟨properDirectImageCompletionMap f J 𝒢 F b G e,
    isKernelCokernelAnnihilatedByPower_properDirectImageCompletionMap f J K 𝒢 F b G e hc⟩

/-! ### Over an affine base complete along `𝒥`: the algebraization is no longer assumed -/

/-- **Stacks 088B over an affine base complete along `𝒥`.** Let `Y` be affine with `Γ(Y, 𝒪_Y)`
Noetherian and complete with respect to an ideal `I`, put `𝒥 = I · 𝒪_Y`, let `f : X ⟶ Y` be
proper and let `𝒦 ⊆ 𝒪_Y` be a quasi-coherent sheaf of ideals. Then for every object `(𝒢_n)` of
`Coh(Y, 𝒥)` and every coherent `𝒪_X`-module `𝓕` there is a morphism

`α : (𝒢_n) ⟶ (f_*𝓕) ^∧`

with levelwise kernels and cokernels annihilated by a power of `𝒦`, provided only `hdesc`: that
*for some* algebraization `𝒢` of `(𝒢_n)` the source's isomorphism descends to an isomorphism
`b : f^*𝒢 ⟶ 𝓕` and the adjunction map `𝒢 ⟶ f_*f^*𝒢` restricts to an isomorphism on
`V = Y ∖ V(𝒦)`.

This is the position the source's proof occupies at its last paragraph, and here the
algebraization is **not** assumed: an affine base complete along `𝒥` makes every object of
`Coh(Y, 𝒥)` the completion of a coherent module, by
`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete` (Stacks 087W). So over such a base
the only input beyond the source's own is the descent of `β`, which is why
`f^*(𝒢 ^∧) ≅ (f^*𝒢) ^∧` is the single statement whose absence keeps Stacks 088B from being
unconditional here — see the module docstring. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAdicComplete
    [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (I : Ideal Γ(Y, ⊤)) [IsAdicComplete I Γ(Y, ⊤)]
    (G : CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop I))
    (hdesc : ∀ 𝒢 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
      (G.obj ≅ ((completionFunctor Y (Scheme.IdealSheafData.ofIdealTop I)).obj 𝒢).obj) →
        ∃ _ : (Scheme.Modules.pullback f).obj 𝒢.obj ≅ F.obj,
          IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒢.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor Y (Scheme.IdealSheafData.ofIdealTop I)).obj
        (properPushforwardCoherent f F)).obj,
      IsKernelCokernelAnnihilatedByPower K α := by
  obtain ⟨𝒢, ⟨eiso⟩⟩ :=
    essImage_completionFunctor_of_isAdicComplete Y I G
  have e : G.obj ≅ ((completionFunctor Y (Scheme.IdealSheafData.ofIdealTop I)).obj 𝒢).obj :=
    (ObjectProperty.ι (IsCoherentAdicSystem (Scheme.IdealSheafData.ofIdealTop I))).mapIso
      eiso.symm
  obtain ⟨b', hc⟩ := hdesc 𝒢 e
  exact exists_isKernelCokernelAnnihilatedByPower_properDirectImage f
    (Scheme.IdealSheafData.ofIdealTop I) K 𝒢 F b' G e hc

end Stacks.Coherent

end
