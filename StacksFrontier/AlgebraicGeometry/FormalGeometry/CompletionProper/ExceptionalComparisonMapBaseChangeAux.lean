module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.SupportSeparation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Reduction of the kernel–cokernel bound of Stacks 088B to a complete base

Let `Y` be a Noetherian scheme and `𝒥, 𝒦 ⊆ 𝒪_Y` quasi-coherent sheaves of ideals. The source's
proof of Stacks 088B establishes its kernel–cokernel bound over a base which is the spectrum of a
Noetherian ring complete along `𝒥`, and then descends it: the bound by *one fixed* power `𝒦 ᵗ` is
local on `Y`, so a finite affine covering with a common `t` suffices, and over an affine open
`U` with `B = Γ(Y, U)` and `I = 𝒥(U)` the flat morphism `Spec B^ ⟶ Y` out of the `I`-adic
completion both carries the datum to a complete base and reflects the annihilation, because
`B ⟶ B^` is an equivalence on the modules annihilated by a power of `I`.

This file provides the two halves of that descent which are independent of the construction of
the comparison map itself.

The **globalization** half is unconditional: on a Noetherian scheme one exponent per affine open
yields one exponent valid on the whole of `Y`, simultaneously for every member of a countable
family of sheaves of modules — which is what the levels of an inverse system are. This is the last
paragraph of the source's argument, and it is the reason Stacks 088B is stated for a Noetherian
rather than a locally Noetherian base.

The **chart** half records the flat morphism `Spec B^ ⟶ Y` attached to an affine open, together
with the three facts the complete case consumes: `B^` is Noetherian, it is complete along the
extension of `I`, and the morphism is flat.

The **reflection** half is stated for an abstract comparison on sections: if over an affine open
`U` of `X` there is an affine open `V` of `Y` with `V ≤ f⁻¹U` and a map `Γ(F, U) ⟶ Γ(f^*F, V)`
semilinear over `f.appLE U V` and with trivial kernel, then annihilation of `f^*F` by a power of
`𝒦.comap f` descends to annihilation of `F` by the same power of `𝒦`. The canonical comparison is
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, whose semilinearity is the `Γ(Y, V)`-linearity
of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, and triviality of its kernel for the
completion chart is the equivalence of categories the source cites.

## Main definitions

* `Stacks.Coherent.adicCompletionSections` — the `𝒥(U)`-adic completion of `Γ(Y, U)`.
* `Stacks.Coherent.adicCompletionChartOver` and `Stacks.Coherent.adicCompletionChart` — the
  **completion chart** `Spec Γ(Y, U)^ ⟶ U` and its composite with `U ⟶ Y`.

## Main results

* `Stacks.Coherent.exists_pos_forall_idealPowerMultiple_eq_bot_of_restrict` — one positive
  exponent for a whole family of sheaves of modules, from one exponent per affine open.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_restrict` — **the kernel–cokernel bound
  of Stacks 088B is local on a Noetherian base.**
* `Stacks.Coherent.isNoetherianRing_adicCompletionSections`,
  `Stacks.Coherent.isAdicComplete_adicCompletionSections` and
  `Stacks.Coherent.isNoetherian_specAdicCompletionSections` — the completed chart is a Noetherian
  scheme complete along the extension of `𝒥(U)`.
* `Stacks.Coherent.flat_adicCompletionChart` and
  `Stacks.Coherent.flat_adicCompletionChartOver` — **the completion chart is flat.**
* `Stacks.Coherent.smul_eq_zero_of_injective_sectionsComparison` and
  `Stacks.Coherent.idealPowerMultiple_eq_bot_of_pullback` — **annihilation by a fixed power
  descends along a morphism** admitting an injective semilinear comparison on sections, with no
  increase of the exponent.

## Implementation notes

The globalization is the argument of `Stacks.Algebraization.isPowerAnnihilated_of_restrict` run
for a family rather than a single sheaf: the exponents are extracted with `Exists.choose` from the
hypothesis, bounded above on the finite index set of a covering by `Finite.exists_le`, and raised
to a positive value by passing from `N` to `N + 1`. The predicate
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` is then assembled from its kernel and
cokernel halves by
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.of_exists_kernel_cokernel`.

`AdicCompletion.isNoetherianRing` and `AdicCompletion.flat_of_isNoetherian` are instances but
their hypothesis `IsNoetherianRing Γ(Y, U)` is not, since it is a consequence of
`AlgebraicGeometry.IsLocallyNoetherian` rather than an instance of it; it is supplied by
`Stacks.Coherent.isNoetherianRing_sections` at each use. Flatness of the chart is flatness of the
completion map, read through `AlgebraicGeometry.Flat.SpecMap_iff` and
`RingHom.flat_algebraMap_iff`, composed with flatness of the open immersion
`AlgebraicGeometry.IsAffineOpen.fromSpec`.

The reflection is stated with the comparison on sections as a parameter rather than as
`AlgebraicGeometry.Scheme.Modules.pullbackSection` itself. The semilinearity of the latter is a
consequence of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`, but that
identity lives in `(ModuleCat.extendScalars (f.appLE U V)).obj (ModuleCat.of Γ(X, U) Γ(F, U))`,
whose scalar action instance search does not recover once the object is unfolded to a bare
`TensorProduct`; parametrising keeps the descent independent of that bookkeeping and of which
comparison is used.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization

/-- The affine opens of a scheme, presented as the range of a family, are a basis of its
topology. -/
private lemma isBasis_affineOpens_range {Y : Scheme.{u}} :
    TopologicalSpace.Opens.IsBasis (Set.range fun A : Y.affineOpens => A.1) := by
  have heq : Set.range (fun A : Y.affineOpens => A.1) = Y.affineOpens := by
    ext W
    exact ⟨fun ⟨A, hA⟩ => hA ▸ A.property, fun hW => ⟨⟨W, hW⟩, rfl⟩⟩
  rw [heq]
  exact Y.isBasis_affineOpens

/-- **One exponent for a whole family, from one exponent per affine open.** On a Noetherian
scheme, if for every affine open `U` some power of `𝒦|_U` annihilates the restriction to `U` of
every member of a family `(M_k)` of sheaves of modules, then one positive power of `𝒦`
annihilates every member of the family.

Quasi-compactness extracts a finite affine covering from the basis of affine opens; the largest
of the finitely many exponents still annihilates each restriction by
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le`, and
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict` globalizes it one member at a
time. -/
public theorem exists_pos_forall_idealPowerMultiple_eq_bot_of_restrict {Y : Scheme.{u}}
    [IsNoetherian Y] (K : Y.IdealSheafData) (M : ℕ → Y.Modules)
    (h : ∀ U : Y.affineOpens, ∃ t : ℕ, ∀ k : ℕ,
      idealPowerMultiple (K.comap U.1.ι) t
        ((Scheme.Modules.restrictFunctor U.1.ι).obj (M k)) = ⊥) :
    ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ, idealPowerMultiple K t (M k) = ⊥ := by
  obtain ⟨κ, hκ, a, heq⟩ :=
    isBasis_affineOpens_range.exists_iSup_eq_of_isCompact (⊤ : Y.Opens) isCompact_univ
  obtain ⟨N, hN⟩ := Finite.exists_le fun j : κ => (h (a j)).choose
  refine ⟨N + 1, Nat.succ_pos _, fun k => ?_⟩
  refine idealPowerMultiple_eq_bot_of_restrict K (N + 1) (M k)
    (fun j : κ => (a j).1) heq.symm fun j => ?_
  exact idealPowerMultiple_eq_bot_of_le ((h (a j)).choose_spec k)
    ((hN j).trans (Nat.le_succ N))

/-- **The kernel–cokernel bound is local on a Noetherian base.** If over every affine open `U` of
a Noetherian scheme `Y` one exponent `t_U` makes `(𝒦|_U) ^ t_U` annihilate the restriction of
every levelwise kernel and cokernel of `α`, then one positive exponent does so globally.

This is the globalization step of the proof of Stacks 088B: the condition
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` demands a single exponent for all
levels *and* all of `Y` at once, while the local analysis over an affine open produces one
exponent per open. -/
public theorem isKernelCokernelAnnihilatedByPower_of_restrict {Y : Scheme.{u}} [IsNoetherian Y]
    (K : Y.IdealSheafData) {F G : ℕᵒᵖ ⥤ Y.Modules} (α : F ⟶ G)
    (h : ∀ U : Y.affineOpens, ∃ t : ℕ, ∀ k : ℕ,
      idealPowerMultiple (K.comap U.1.ι) t
          ((Scheme.Modules.restrictFunctor U.1.ι).obj (kernel (α.app (op k)))) = ⊥ ∧
        idealPowerMultiple (K.comap U.1.ι) t
          ((Scheme.Modules.restrictFunctor U.1.ι).obj (cokernel (α.app (op k)))) = ⊥) :
    IsKernelCokernelAnnihilatedByPower K α :=
  IsKernelCokernelAnnihilatedByPower.of_exists_kernel_cokernel
    (exists_pos_forall_idealPowerMultiple_eq_bot_of_restrict K
      (fun k => kernel (α.app (op k))) fun U => ⟨(h U).choose, fun k => ((h U).choose_spec k).1⟩)
    (exists_pos_forall_idealPowerMultiple_eq_bot_of_restrict K
      (fun k => cokernel (α.app (op k)))
      fun U => ⟨(h U).choose, fun k => ((h U).choose_spec k).2⟩)

/-! ### The adic completion of an affine chart -/

section Chart

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- The ring of sections over an affine open of a locally Noetherian scheme is Noetherian. -/
public theorem isNoetherianRing_sections (U : Y.affineOpens) : IsNoetherianRing Γ(Y, U.1) :=
  IsLocallyNoetherian.component_noetherian U

/-- **The `𝒥(U)`-adic completion of `Γ(Y, U)`**, for an affine open `U` of `Y`. The reduction of
Stacks 088B to a complete base is a base change along the spectrum of this ring. -/
public abbrev adicCompletionSections (J : Y.IdealSheafData) (U : Y.affineOpens) : Type u :=
  AdicCompletion (J.ideal U) Γ(Y, U.1)

/-- The adic completion of the sections over an affine open of a locally Noetherian scheme is a
Noetherian ring. -/
public theorem isNoetherianRing_adicCompletionSections (J : Y.IdealSheafData)
    (U : Y.affineOpens) : IsNoetherianRing (adicCompletionSections J U) :=
  have := isNoetherianRing_sections U
  AdicCompletion.isNoetherianRing _

/-- **The completed chart is complete.** The extension of `𝒥(U)` to the `𝒥(U)`-adic completion of
`Γ(Y, U)` makes that ring adically complete; the ideal is finitely generated because `Γ(Y, U)` is
Noetherian. -/
public theorem isAdicComplete_adicCompletionSections (J : Y.IdealSheafData) (U : Y.affineOpens) :
    IsAdicComplete
      ((J.ideal U).map (algebraMap Γ(Y, U.1) (adicCompletionSections J U)))
      (adicCompletionSections J U) :=
  have := isNoetherianRing_sections U
  AdicCompletion.isAdicComplete_self _ (Ideal.fg_of_isNoetherianRing _)

/-- The spectrum of the adic completion of `Γ(Y, U)` is a Noetherian scheme. -/
public theorem isNoetherian_specAdicCompletionSections (J : Y.IdealSheafData)
    (U : Y.affineOpens) :
    IsNoetherian (Spec (CommRingCat.of (adicCompletionSections J U))) :=
  have := isNoetherianRing_adicCompletionSections J U
  inferInstance

/-- **The completion chart over an affine open**, as a morphism into the open subscheme `U`: the
spectrum of the `𝒥(U)`-adic completion of `Γ(Y, U)`, mapped to `U` through the isomorphism of `U`
with the spectrum of its ring of sections. -/
public def adicCompletionChartOver (J : Y.IdealSheafData) (U : Y.affineOpens) :
    Spec (CommRingCat.of (adicCompletionSections J U)) ⟶ U.1.toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U.1) (adicCompletionSections J U))) ≫
    U.2.isoSpec.inv

/-- **The completion chart over an affine open**, as a morphism into `Y`. -/
public def adicCompletionChart (J : Y.IdealSheafData) (U : Y.affineOpens) :
    Spec (CommRingCat.of (adicCompletionSections J U)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U.1) (adicCompletionSections J U))) ≫
    U.2.fromSpec

omit [IsLocallyNoetherian Y] in
/-- The chart into `Y` is the chart into `U` followed by the open immersion of `U`. -/
public theorem adicCompletionChartOver_comp_ι (J : Y.IdealSheafData) (U : Y.affineOpens) :
    adicCompletionChartOver J U ≫ U.1.ι = adicCompletionChart J U := by
  rw [adicCompletionChartOver, adicCompletionChart, Category.assoc, U.2.isoSpec_inv_ι]

/-- The spectrum of the completion map `Γ(Y, U) ⟶ Γ(Y, U)^` is flat. -/
private theorem flat_specMap_adicCompletionSections (J : Y.IdealSheafData) (U : Y.affineOpens) :
    Flat (Spec.map
      (CommRingCat.ofHom (algebraMap Γ(Y, U.1) (adicCompletionSections J U)))) :=
  have := isNoetherianRing_sections U
  Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian (J.ideal U)))

/-- **The completion chart is flat.** The completion map of a Noetherian ring is flat, and the
inclusion of an affine open is an open immersion. -/
public theorem flat_adicCompletionChart (J : Y.IdealSheafData) (U : Y.affineOpens) :
    Flat (adicCompletionChart J U) :=
  have := flat_specMap_adicCompletionSections J U
  have := U.2.isOpenImmersion_fromSpec
  inferInstanceAs (Flat (_ ≫ U.2.fromSpec))

/-- **The completion chart over `U` is flat.** -/
public theorem flat_adicCompletionChartOver (J : Y.IdealSheafData) (U : Y.affineOpens) :
    Flat (adicCompletionChartOver J U) :=
  have := flat_specMap_adicCompletionSections J U
  inferInstanceAs (Flat (_ ≫ U.2.isoSpec.inv))

end Chart

/-! ### Descent of annihilation along a morphism -/

section Descent

open Stacks.AlgebraicGeometry.HigherDirectImageCoherent

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)

/-- **Descent of the annihilation of sections along a morphism.** Let `U` be an affine open of
`X`, let `V` be an affine open of `Y` with `V ≤ f⁻¹U`, and let `π` be a comparison on sections
from `U` to `V` which is semilinear over `f.appLE U V` and has trivial kernel. If
`(𝒦.comap f) ᵗ` annihilates `f^*F`, then `𝒦(U) ᵗ` annihilates the sections of `F` over `U`.

Semilinearity turns `r • a` into `(f.appLE U V) r` acting on `π a`, and
`Stacks.Algebraization.appLE_mem_comap_pow` puts that scalar in `(𝒦.comap f)(V) ᵗ`, where the
hypothesis kills it; triviality of the kernel of `π` returns the conclusion to `U`.

This is the step of the proof of Stacks 088B which reads the annihilation found over the
completed base back over the base itself. The canonical `π` is
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, whose semilinearity is the `Γ(Y, V)`-linearity
of `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`; the source's input is that it has
trivial kernel, because `B ⟶ B^` is an equivalence on the modules annihilated by a power
of `𝒥(U)`. -/
public theorem smul_eq_zero_of_injective_sectionsComparison (K : X.IdealSheafData) (t : ℕ)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (π : Γ(F, U.1) → Γ((Scheme.Modules.pullback f).obj F, V.1))
    (hπ : ∀ (s : Γ(X, U.1)) (x : Γ(F, U.1)), π (s • x) = (f.appLE U.1 V.1 hVU).hom s • π x)
    (hker : ∀ x : Γ(F, U.1), π x = 0 → x = 0)
    (h : idealPowerMultiple (K.comap f) t ((Scheme.Modules.pullback f).obj F) = ⊥)
    {r : Γ(X, U.1)} (hr : r ∈ K.ideal U ^ t) (a : Γ(F, U.1)) : r • a = 0 := by
  refine hker _ ?_
  rw [hπ]
  exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot h V
    (appLE_mem_comap_pow f K t U V hVU hr) _

/-- **Annihilation by a fixed power descends along a morphism.** If `F` is quasi-coherent and
every affine open `U` of `X` admits an affine open `V` of `Y` with `V ≤ f⁻¹U` and a semilinear
comparison on sections with trivial kernel, then annihilation of `f^*F` by `(𝒦.comap f) ᵗ`
descends to annihilation of `F` by `𝒦 ᵗ`, with the same exponent.

This is the shape in which the reduction of Stacks 088B to a complete base is undone: it is
applied levelwise to the kernels and cokernels of the comparison map, and the resulting uniform
exponent is globalized by
`Stacks.Coherent.exists_pos_forall_idealPowerMultiple_eq_bot_of_restrict`. -/
public theorem idealPowerMultiple_eq_bot_of_pullback [F.IsQuasicoherent] (K : X.IdealSheafData)
    (t : ℕ) (h : idealPowerMultiple (K.comap f) t ((Scheme.Modules.pullback f).obj F) = ⊥)
    (hcov : ∀ U : X.affineOpens, ∃ (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
      (π : Γ(F, U.1) → Γ((Scheme.Modules.pullback f).obj F, V.1)),
      (∀ (s : Γ(X, U.1)) (x : Γ(F, U.1)), π (s • x) = (f.appLE U.1 V.1 hVU).hom s • π x) ∧
        ∀ x : Γ(F, U.1), π x = 0 → x = 0) :
    idealPowerMultiple K t F = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_forall_smul_eq_zero K t F fun U r hr a => ?_
  obtain ⟨V, hVU, π, hπ, hker⟩ := hcov U
  exact smul_eq_zero_of_injective_sectionsComparison f F K t U V hVU π hπ hker h hr a

end Descent

end Stacks.Coherent

end
