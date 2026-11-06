module

public import StacksFrontier.AlgebraicGeometry.Modules.DualBiproduct
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackMonoDualMap
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmple
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree

/-!
# A finite locally free module embeds in a complex of high twists of an ample module

Let `X` be a locally Noetherian scheme carrying an ample invertible module `L`, and let `ℰ` be a
finite locally free `𝒪_X`-module. For every bound `N` there are degrees `p, q ≥ N`, finite index
sets, and an exact sequence

`0 → ℰ → ((L^{⊗ -p})^{⊕ ιp})^∨ → ((L^{⊗ -q})^{⊕ ιq})^∨`

whose first map is moreover *universally* injective: it stays a monomorphism after pullback along
any morphism of schemes. The two duals are finite direct sums of `L^{⊗ p}` and of `L^{⊗ q}`.

This is the claim made, and left to the reader, in the proof of the implication (2) ⇒ (3) of
[Stacks, Tag 0EKP].

## Main results

* `Stacks.Algebraization.dualTensorPowIso` — the dual of a negative tensor power of an invertible
  module is the corresponding positive power.
* `Stacks.Algebraization.exists_epi_bicone_of_isAmple` — clause (8) of [Stacks, Tag 01Q3] with
  the degree of the twist bounded below: every quasi-coherent module of finite type is a quotient
  of a finite direct sum of copies of one arbitrarily negative twist of `L`.
* `Stacks.Algebraization.exists_dual_embedding` — the exact sequence above.

## Implementation notes

The source dualises a surjection `(L^{⊗ -p})^{⊕ r} ↠ ℰ^∨` and repeats the construction on the
cokernel. Here the second step is taken on the *kernel* `𝒦` of that surjection instead, which
avoids having to know that the cokernel of the dualised map is finite locally free: a surjection
`(L^{⊗ -q})^{⊕ s} ↠ 𝒦` makes the three-term complex
`(L^{⊗ -q})^{⊕ s} → (L^{⊗ -p})^{⊕ r} → ℰ^∨` exact at the middle, and left exactness of
`SheafHom(-, 𝒪_X)` on a right exact sequence — [Stacks, Tag 0GMY], available as
`Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_exact_of_exact_epi` — gives
the displayed sequence without any finiteness hypothesis on `𝒦` beyond the quasi-coherence and
finite type needed to apply ampleness to it, which hold because `𝒦` is coherent.

Exactness of the middle term is read off the kernel sequence of the surjection: precomposing the
kernel inclusion with an epimorphism does not change exactness, by
`CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`.

The first map of the displayed sequence is `ℰ ⟶ ℰ^∨∨ ⟶ ((L^{⊗ -p})^{⊕ r})^∨`, whose first leg is
invertible because a coherent finite locally free module on a locally Noetherian scheme is
reflexive.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.AlgebraicGeometry.ReflexiveModules

noncomputable section

universe u

namespace Stacks.Algebraization

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-! ### The dual of a negative twist -/

/-- **The dual of a negative tensor power of an invertible module is the positive power.** -/
public def dualTensorPowIso (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] (n : ℤ) :
    tensorPowModule X L n ≅ dualSheaf (tensorPowModule X L (-n)) :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    (tensorPowModule X L (-n)) (tensorPowModule X L n)
    (tensorPowModuleAddIso X L (-n) n ≪≫
      eqToIso (by rw [neg_add_cancel]) ≪≫ tensorPowModuleZeroIso X L)

/-! ### Presentations by arbitrarily negative twists -/

/-- **Clause (8) of [Stacks, Tag 01Q3] with the twist bounded below.** -/
public theorem exists_epi_bicone_of_isAmple (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) (N : ℤ) (F : X.Modules) (hqc : F.IsQuasicoherent)
    (hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} F) :
    ∃ (n : ℤ) (ι : Type u) (_ : Finite ι) (_ : N ≤ n)
      (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit) (p : b.pt ⟶ F),
      Epi p := by
  obtain ⟨n₀, hgen⟩ :=
    Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L hL F hqc hft
  obtain ⟨σ, hσ⟩ := hgen (max n₀ N) (le_max_left _ _)
  have := hσ
  obtain ⟨b, hb, p, hp, -⟩ := Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free L
    (max n₀ N) F (σ.π : Stacks.AmpleGlobalGeneration.freeModule X σ.I ⟶ _) σ.epi
  exact ⟨max n₀ N, σ.I, hσ, le_max_right _ _, b, hb, p, hp⟩

/-! ### Finite local freeness of a finite direct sum of twists -/

/-- A tensor power of an ample invertible module is finite locally free. -/
public theorem isFiniteLocallyFree_tensorPowModule (L : X.Modules) [IsInvertibleModule X L]
    (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (tensorPowModule X L n) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPowModule X L n) :=
    Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) (tensorPowModule X L n) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X _
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

/-! ### The embedding -/

/-- Precomposing the first map of an exact short complex with an epimorphism keeps it exact. -/
public theorem exact_mk_epi_comp {C : Type*} [Category C] [HasZeroMorphisms C] {A' A B D : C}
    (e : A' ⟶ A) [Epi e] {f : A ⟶ B} {g : B ⟶ D} {w : f ≫ g = 0}
    (h : (ShortComplex.mk f g w).Exact) :
    (ShortComplex.mk (e ≫ f) g (by rw [Category.assoc, w, comp_zero])).Exact := by
  let φ : ShortComplex.mk (e ≫ f) g (by rw [Category.assoc, w, comp_zero]) ⟶
      ShortComplex.mk f g w :=
    { τ₁ := e, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  have : Epi φ.τ₁ := ‹Epi e›
  have : IsIso φ.τ₂ := by dsimp only [φ]; infer_instance
  have : Mono φ.τ₃ := by dsimp only [φ]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h

/-- The kernel of a map of finite locally free modules on a locally Noetherian scheme is
quasi-coherent of finite type. -/
public theorem isQuasicoherent_isFiniteType_kernel_of_isFiniteLocallyFree [IsLocallyNoetherian X]
    {P F : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) P]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F]
    (f : P ⟶ F) : (kernel f).IsQuasicoherent ∧ (kernel f).IsFiniteType := by
  have : P.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X P
  have : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X F
  have hKc : _root_.SheafOfModules.IsCoherent (kernel f) :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel f
  exact @Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent X
    (kernel f) hKc

/-- **The universally exact sequence of the proof of [Stacks, Tag 0EKP] (2) ⇒ (3).** -/
public theorem exists_dual_embedding [IsLocallyNoetherian X] (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (N : ℤ) (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) E) :
    ∃ (p q : ℤ) (ιp ιq : Type u) (_ : Finite ιp) (_ : Finite ιq) (_ : N ≤ p) (_ : N ≤ q)
      (bp : Bicone fun _ : ιp => tensorPowModule X L (-p)) (_ : bp.IsBilimit)
      (bq : Bicone fun _ : ιq => tensorPowModule X L (-q)) (_ : bq.IsBilimit)
      (q₀ : bp.pt ⟶ dualSheaf E) (_ : Epi q₀)
      (β : dualSheaf bp.pt ⟶ dualSheaf bq.pt)
      (w : (toDoubleDual E ≫ dualMap q₀) ≫ β = 0),
      IsIso (toDoubleDual E) ∧ Mono (toDoubleDual E ≫ dualMap q₀) ∧
        (ShortComplex.mk (toDoubleDual E ≫ dualMap q₀) β w).Exact ∧
        ∀ (W : Scheme.{u}) (g : W ⟶ X),
          Mono ((Scheme.Modules.pullback g).map (toDoubleDual E ≫ dualMap q₀)) := by
  have hEd : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (dualSheaf E) := isFiniteLocallyFree_dualSheaf E hE
  obtain ⟨hEdqc, hEdft⟩ :=
    Stacks.AlgebraicGeometry.CoherentKernel.isQuasicoherent_isFiniteType_of_isFiniteLocallyFree
      (dualSheaf E)
  obtain ⟨p, ιp, hιp, hpN, bp, hbp, q₀, hq₀⟩ :=
    exists_epi_bicone_of_isAmple L hL N (dualSheaf E) hEdqc hEdft
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (tensorPowModule X L (-p)) := isFiniteLocallyFree_tensorPowModule L (-p)
  have hbpflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) bp.pt :=
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isBilimit_const _ hbp
  obtain ⟨hKqc, hKft⟩ := isQuasicoherent_isFiniteType_kernel_of_isFiniteLocallyFree q₀
  obtain ⟨q, ιq, hιq, hqN, bq, hbq, q₁, hq₁⟩ :=
    exists_epi_bicone_of_isAmple L hL N (kernel q₀) hKqc hKft
  -- the right exact three term complex
  have w0 : (q₁ ≫ kernel.ι q₀) ≫ q₀ = 0 := by simp
  have hex : (ShortComplex.mk (q₁ ≫ kernel.ι q₀) q₀ w0).Exact :=
    exact_mk_epi_comp q₁ (ShortComplex.kernelSequence_exact q₀)
  -- dualise
  have hepi' : Epi (C := _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O)) q₀ := hq₀
  obtain ⟨w', hex'⟩ :=
    Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_exact_of_exact_epi
      (schemeRingedSite X)
      (ShortComplex.mk (C := _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
        (q₁ ≫ kernel.ι q₀) q₀ w0)
      (SheafOfModules.unit (structureSheaf X.sheaf)) hex
  have w2 : dualMap q₀ ≫ dualMap (q₁ ≫ kernel.ι q₀) = 0 := w'
  have hex2 : (ShortComplex.mk (dualMap q₀) (dualMap (q₁ ≫ kernel.ι q₀)) w2).Exact := hex'
  have hmono : Mono (dualMap q₀) :=
    Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_mono_of_epi
      (schemeRingedSite X) q₀
  -- reflexivity of `E`
  have hrefl : IsIso (toDoubleDual E) :=
    Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree E
      ((Scheme.Modules.isFiniteLocallyFree_iff E).mpr hE)
  refine ⟨p, q, ιp, ιq, hιp, hιq, hpN, hqN, bp, hbp, bq, hbq, q₀, hq₀,
    dualMap (q₁ ≫ kernel.ι q₀), by rw [Category.assoc, w2, comp_zero], hrefl,
    @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hrefl) _ hmono, ?_, ?_⟩
  · exact exact_mk_epi_comp (toDoubleDual E) hex2
  · intro W g
    have : Mono ((Scheme.Modules.pullback g).map (dualMap q₀)) :=
      mono_pullback_map_dualMap_of_epi g q₀ hq₀ hbpflf hEd
    have hiso : IsIso ((Scheme.Modules.pullback g).map (toDoubleDual E)) :=
      ((Scheme.Modules.pullback g).mapIso (asIso (toDoubleDual E))).isIso_hom
    rw [Functor.map_comp]
    exact mono_comp _ _

end Stacks.Algebraization

end

end
