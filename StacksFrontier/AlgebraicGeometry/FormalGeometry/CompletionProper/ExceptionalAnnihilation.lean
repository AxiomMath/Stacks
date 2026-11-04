module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic

/-!
# Annihilation off the exceptional locus

Let `Y` be a Noetherian scheme and `𝒦 ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals, and write
`V = Y ∖ V(𝒦)` for the open complement of the closed set it cuts out. A morphism of coherent
`𝒪_Y`-modules whose restriction to `V` is an isomorphism has kernel and cokernel supported on
`V(𝒦)`, hence annihilated by one power of `𝒦`.

## Main results

* `Stacks.Coherent.preservesFiniteLimits_restrictFunctor_opens`: restriction of sheaves of
  modules to an open subscheme is left exact.
* `Stacks.Coherent.supp_subset_compl_of_isZero_restrict`: a sheaf of modules vanishing on an
  open has support in the complement of that open.
* `Stacks.Coherent.isZero_restrict_kernel_of_isIso_restrict`,
  `Stacks.Coherent.isZero_restrict_cokernel_of_isIso_restrict`: the kernel and cokernel of a
  morphism which restricts to an isomorphism on an open vanish there.
* `Stacks.Coherent.supp_kernel_subset_support_of_isIso_restrict`,
  `Stacks.Coherent.supp_cokernel_subset_support_of_isIso_restrict`: the kernel and cokernel of a
  morphism which is an isomorphism over `Y ∖ V(𝒦)` are supported on `V(𝒦)`.
* `Stacks.Coherent.exists_pos_idealPowerMultiple_kernel_cokernel_eq_bot`: for coherent modules
  on a Noetherian scheme, one positive power of `𝒦` annihilates both the kernel and the cokernel.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

namespace Stacks.Coherent

variable {Y : Scheme.{u}}

/-! ### Exactness of restriction to an open -/

/-- Restriction of sheaves of modules to an open subscheme is left exact. -/
public theorem preservesFiniteLimits_restrictFunctor_opens (V : Y.Opens) :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor V.ι) :=
  have _ := AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat V.ι
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm

/-! ### Vanishing on an open is a support statement -/

/-- A sheaf of modules whose restriction to an open `V` is a zero object has support in the
complement of `V`. -/
public theorem supp_subset_compl_of_isZero_restrict (V : Y.Opens) (M : Y.Modules)
    (hM : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M)) :
    SheafOfModules.supp M ⊆ (V : Set Y)ᶜ := by
  rintro x ⟨a, ha⟩ hxV
  have hres : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hxV⟩ : V.toScheme)).obj
      ((Scheme.Modules.restrictFunctor V.ι).obj M).val.presheaf) :=
    Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hxV⟩ : V.toScheme))
      (Functor.map_isZero (Scheme.Modules.toPresheaf V.toScheme) hM)
  have hstalk : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj M.val.presheaf) :=
    hres.of_iso ((Scheme.Modules.restrictStalkNatIso V.ι (⟨x, hxV⟩ : V.toScheme)).app M).symm
  exact ha ((AddCommGrpCat.subsingleton_of_isZero hstalk).elim a 0)

/-! ### The kernel and cokernel vanish where the morphism is an isomorphism -/

/-- The kernel of a morphism of sheaves of modules whose restriction to an open `V` is an
isomorphism vanishes on `V`. -/
public theorem isZero_restrict_kernel_of_isIso_restrict (V : Y.Opens) {G H : Y.Modules}
    (c : G ⟶ H) (hc : IsIso ((Scheme.Modules.restrictFunctor V.ι).map c)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (kernel (C := Y.Modules) c)) := by
  have _ := preservesFiniteLimits_restrictFunctor_opens V
  have _ := hc
  exact IsZero.of_iso ((Preadditive.mono_iff_isZero_kernel
    ((Scheme.Modules.restrictFunctor V.ι).map c)).1 inferInstance)
    (PreservesKernel.iso (Scheme.Modules.restrictFunctor V.ι) c)

/-- The cokernel of a morphism of sheaves of modules whose restriction to an open `V` is an
isomorphism vanishes on `V`. -/
public theorem isZero_restrict_cokernel_of_isIso_restrict (V : Y.Opens) {G H : Y.Modules}
    (c : G ⟶ H) (hc : IsIso ((Scheme.Modules.restrictFunctor V.ι).map c)) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (cokernel (C := Y.Modules) c)) := by
  have _ := hc
  exact IsZero.of_iso ((Preadditive.epi_iff_isZero_cokernel
    ((Scheme.Modules.restrictFunctor V.ι).map c)).1 inferInstance)
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor V.ι) c)

/-! ### Support of the kernel and the cokernel -/

/-- A sheaf of modules vanishing over `Y ∖ V(𝒦)` is supported on `V(𝒦)`. -/
private theorem supp_subset_support_of_isZero_restrict (K : Y.IdealSheafData) {M : Y.Modules}
    (hM : IsZero ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).obj M)) :
    SheafOfModules.supp M ⊆ (K.support : Set Y) :=
  fun _ hx ↦ Classical.byContradiction <| supp_subset_compl_of_isZero_restrict _ M hM hx

/-- The kernel of a morphism which is an isomorphism over `Y ∖ V(𝒦)` is supported on `V(𝒦)`. -/
public theorem supp_kernel_subset_support_of_isIso_restrict (K : Y.IdealSheafData)
    {G H : Y.Modules} (c : G ⟶ H)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map c)) :
    SheafOfModules.supp (kernel (C := Y.Modules) c) ⊆ (K.support : Set Y) :=
  supp_subset_support_of_isZero_restrict K (isZero_restrict_kernel_of_isIso_restrict _ c hc)

/-- The cokernel of a morphism which is an isomorphism over `Y ∖ V(𝒦)` is supported on
`V(𝒦)`. -/
public theorem supp_cokernel_subset_support_of_isIso_restrict (K : Y.IdealSheafData)
    {G H : Y.Modules} (c : G ⟶ H)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map c)) :
    SheafOfModules.supp (cokernel (C := Y.Modules) c) ⊆ (K.support : Set Y) :=
  supp_subset_support_of_isZero_restrict K (isZero_restrict_cokernel_of_isIso_restrict _ c hc)

/-! ### Annihilation by a power of the ideal -/

/-- Let `Y` be a Noetherian scheme and `𝒦 ⊆ 𝒪_Y` a
quasi-coherent sheaf of ideals. If a morphism `c` of coherent `𝒪_Y`-modules restricts to an
isomorphism on the open `V = Y ∖ V(𝒦)`, then one positive power of `𝒦` annihilates both
`Ker(c)` and `Coker(c)`. -/
public theorem exists_pos_idealPowerMultiple_kernel_cokernel_eq_bot [IsNoetherian Y]
    (K : Y.IdealSheafData) {G H : Y.Modules} [G.IsCoherent] [H.IsCoherent] (c : G ⟶ H)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map c)) :
    ∃ t : ℕ, 0 < t ∧ idealPowerMultiple K t (kernel (C := Y.Modules) c) = ⊥ ∧
      idealPowerMultiple K t (cokernel (C := Y.Modules) c) = ⊥ := by
  have _ : (kernel (C := Y.Modules) c).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel c
  have _ : (cokernel (C := Y.Modules) c).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel c
  obtain ⟨n, hn⟩ := (AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset
    (kernel (C := Y.Modules) c) K).2 (supp_kernel_subset_support_of_isIso_restrict K c hc)
  obtain ⟨m, hm⟩ := (AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset
    (cokernel (C := Y.Modules) c) K).2 (supp_cokernel_subset_support_of_isIso_restrict K c hc)
  refine ⟨max n m + 1, Nat.succ_pos _,
    idealPowerMultiple_eq_bot_of_le hn ((le_max_left n m).trans (Nat.le_succ _)),
    idealPowerMultiple_eq_bot_of_le hm ((le_max_right n m).trans (Nat.le_succ _))⟩

end Stacks.Coherent

end
