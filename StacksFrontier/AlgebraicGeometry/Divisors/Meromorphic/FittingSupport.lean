module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AnnihilatorSupport

/-!
# The zeroth Fitting subscheme of a finite type quasi-coherent module

Let `F` be a finite type quasi-coherent module on a scheme `S`, let `Z₀` be the closed subscheme
cut out by its zeroth Fitting ideal and let `Z` be its scheme-theoretic support, the closed
subscheme cut out by the annihilator. Then `Z ⊆ Z₀` as closed subschemes, the two have the same
underlying closed set — the support of `F` — and `F` is the direct image of a finite type
quasi-coherent module on `Z₀`.

## Main results

* `AlgebraicGeometry.fittingIdeal_zero_le_annihilatorIdeal`: the inclusion of closed subschemes,
  read as the reverse inclusion of their defining ideal sheaves.
* `AlgebraicGeometry.fittingIdeal_zero_support_eq_supp`: the zeroth Fitting subscheme has the
  support of `F` as its underlying closed set.
* `AlgebraicGeometry.exists_module_on_fittingSubscheme`: `F` is the direct image of a finite type
  quasi-coherent module on the zeroth Fitting subscheme.

## Implementation notes

The scheme-theoretic support is `AlgebraicGeometry.annihilatorIdeal'`, whose underlying closed
set is the support of the module by `AlgebraicGeometry.supp_eq_annihilatorIdeal_support`; that
statement is the other half of the set-theoretic clause and carries the tag as well.

The primed name is the saturating construction in
`StacksDraft.AlgebraicGeometry.Divisors.AssociatedPoints.AnnihilatorSupport`, which takes no
hypotheses. It is distinct from the unprimed `AlgebraicGeometry.annihilatorIdeal` of
`…/SchemeTheoreticSupport/Basic.lean`, which builds the ideal directly and assumes
`[IsLocallyNoetherian X]` and `[F.IsCoherent]`; that one carries the `02OM` tag.

Both the inclusion and the equality of supports are checked on affine opens, where they become
the two ring-theoretic facts `Fit₀(M) ⊆ Ann(M)` and `V(Fit₀(M)) = Supp(M)` recorded in
`fittingIdeal_basic_properties`.

The descended module is not produced by hand: the inclusion of ideal sheaves says the kernel of
the comorphism of the closed immersion annihilates `F` section by section, so the unit of the
pullback–pushforward adjunction at `F` is an isomorphism by
`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`, and the descended module is the pullback
of `F`, which inherits quasi-coherence and finite type.

## References

* [Stacks Project, Tag 0CYX](https://stacks.math.columbia.edu/tag/0CYX)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- **Stacks Project, Tag 0CYX, part (1).** The scheme-theoretic support of a finite type
quasi-coherent module is a closed subscheme of the one cut out by its zeroth Fitting ideal:
over every affine open the zeroth Fitting ideal is contained in the annihilator. -/
@[stacks 0CYX "scheme_theoretic_inclusion"]
theorem fittingIdeal_zero_le_annihilatorIdeal : fittingIdeal F 0 ≤ annihilatorIdeal' F := by
  rw [Scheme.IdealSheafData.le_def]
  intro U
  let : Module.Finite Γ(S, U.1) Γ(F, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F U.2
  rw [fittingIdeal_ideal F 0 U, annihilatorIdeal_ideal F U]
  exact (fittingIdeal_basic_properties.{u, u, u, u}
    (R := Γ(S, U.1)) (M := Γ(F, U.1))).2.2.2.2.2.1

/-- On an affine open the zeroth Fitting ideal and the annihilator have the same zero locus: both
are the support of the module of sections there. -/
private theorem zeroLocus_fittingIdeal_zero_eq_zeroLocus_annihilatorIdeal (U : S.affineOpens)
    {x : S} (hx : x ∈ U.1) :
    (x ∈ S.zeroLocus (U := U.1) ((fittingIdeal F 0).ideal U) ↔
      x ∈ S.zeroLocus (U := U.1) ((annihilatorIdeal' F).ideal U)) := by
  let : Module.Finite Γ(S, U.1) Γ(F, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F U.2
  have hz : PrimeSpectrum.zeroLocus
        ((_root_.fittingIdeal (M := Γ(F, U.1)) (0 : ℤ) : Ideal Γ(S, U.1)) : Set Γ(S, U.1)) =
      PrimeSpectrum.zeroLocus
        ((Module.annihilator Γ(S, U.1) Γ(F, U.1) : Ideal Γ(S, U.1)) : Set Γ(S, U.1)) :=
    ((fittingIdeal_basic_properties.{u, u, u, u}
      (R := Γ(S, U.1)) (M := Γ(F, U.1))).2.2.2.2.2.2.1).trans Module.support_eq_zeroLocus
  have himg := congrArg (fun t : Set (PrimeSpectrum Γ(S, U.1)) => U.2.fromSpec '' t) hz
  rw [U.2.fromSpec_image_zeroLocus, U.2.fromSpec_image_zeroLocus] at himg
  rw [fittingIdeal_ideal F 0 U, annihilatorIdeal_ideal F U]
  have hx' := congrArg (fun A : Set S => x ∈ A) himg
  simpa [hx] using hx'

add_to_stacks 0CYX "underlying_support" AlgebraicGeometry.supp_eq_annihilatorIdeal_support

/-- **Stacks Project, Tag 0CYX, part (2).** The closed subscheme cut out by the zeroth Fitting
ideal of a finite type quasi-coherent module has the support of the module as its underlying
closed set, so it agrees there with the scheme-theoretic support. -/
@[stacks 0CYX "underlying_support", sga "7 VI 5.1" "more general"]
theorem fittingIdeal_zero_support_eq_supp :
    (fittingIdeal F 0).support = SheafOfModules.supp F := by
  rw [supp_eq_annihilatorIdeal_support]
  refine Set.ext fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [SetLike.mem_coe, SetLike.mem_coe,
    Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU,
    Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU]
  exact zeroLocus_fittingIdeal_zero_eq_zeroLocus_annihilatorIdeal F ⟨U, hU⟩ hxU

/-- The kernel of the comorphism of the closed immersion of the zeroth Fitting subscheme
annihilates the module, section by section: this is the inclusion of ideal sheaves of part (1),
read over affine opens and glued back by the sheaf condition. -/
private theorem smul_eq_zero_of_subschemeι_app_eq_zero
    (U : S.Opens) (a : Γ(S, U)) (ha : ((fittingIdeal F 0).subschemeι.app U).hom a = 0)
    (m : Γ(F, U)) : a • m = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (U := op U) F.isSheaf fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  have hVU' : V ≤ U := hVU
  refine ⟨V, hVU', hxV, ?_⟩
  have hker : ((fittingIdeal F 0).subschemeι.app V).hom (S.presheaf.map (homOfLE hVU').op a)
      = 0 := by
    have hnat := congrArg (fun k : Γ(S, U) ⟶ _ => k.hom a)
      ((fittingIdeal F 0).subschemeι.naturality (homOfLE hVU').op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    rw [ha, map_zero] at hnat
    exact hnat
  have hmem : S.presheaf.map (homOfLE hVU').op a ∈ (fittingIdeal F 0).ideal ⟨V, hV⟩ := by
    rw [← Scheme.IdealSheafData.ker_subschemeι_app]
    exact hker
  have hann : S.presheaf.map (homOfLE hVU').op a ∈ Module.annihilator Γ(S, V) Γ(F, V) := by
    rw [← annihilatorIdeal_ideal F ⟨V, hV⟩]
    exact Scheme.IdealSheafData.le_def.mp (fittingIdeal_zero_le_annihilatorIdeal F) _ hmem
  calc F.presheaf.map (homOfLE hVU').op (a • m)
      = S.presheaf.map (homOfLE hVU').op a • F.presheaf.map (homOfLE hVU').op m :=
        F.map_smul (homOfLE hVU') a m
    _ = 0 := Module.mem_annihilator.mp hann _
    _ = F.presheaf.map (homOfLE hVU').op 0 := by simp

/-- **Stacks Project, Tag 0CYX, part (3).** A finite type quasi-coherent module is the direct
image of a finite type quasi-coherent module on the closed subscheme cut out by its zeroth
Fitting ideal, namely of its own pullback there. -/
@[stacks 0CYX "module_on_fitting_subscheme"]
theorem exists_module_on_fittingSubscheme :
    ∃ (G : (fittingIdeal F 0).subscheme.Modules)
      (_ : (Scheme.Modules.pushforward (fittingIdeal F 0).subschemeι).obj G ≅ F),
      G.IsFiniteType ∧ G.IsQuasicoherent := by
  have hiso := Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero
    (fittingIdeal F 0).subschemeι F (smul_eq_zero_of_subschemeι_app_eq_zero F)
  have hft : ((Scheme.Modules.pullback (fittingIdeal F 0).subschemeι).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType
      (fittingIdeal F 0).subschemeι.toLRSHom.toShHom F
  have hqc : ((Scheme.Modules.pullback (fittingIdeal F 0).subschemeι).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
      (fittingIdeal F 0).subschemeι F
  exact ⟨(Scheme.Modules.pullback (fittingIdeal F 0).subschemeι).obj F,
    (@asIso _ _ _ _ _ hiso).symm, hft, hqc⟩

end AlgebraicGeometry

end
