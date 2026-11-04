module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.UnitIdealFromCover

/-!
# Lifting sections from a closed subscheme, and affine basic opens around a closed point

Let `X` be a scheme on which `H¹(X, 𝓘) = 0` for every quasi-coherent sheaf of ideals
`𝓘 ⊆ 𝒪_X`. Then for every closed subscheme `Z ⊆ X` the restriction map
`Γ(X, 𝒪_X) ⟶ Γ(Z, 𝒪_Z)` is surjective, and every closed point `x` of `X` lying in an open `U`
lies in a basic open `X_r ⊆ U` of a global section `r ∈ Γ(X, 𝒪_X)`.

## Main results

* `Stacks.SerreCriterion.surjective_appTop_subschemeι`: sections of a closed subscheme lift.
* `Stacks.SerreCriterion.exists_section_eq_one_eq_zero`: a scheme covered by two disjoint opens
  carries a global section which is `1` on the first and `0` on the second.
* `Stacks.SerreCriterion.exists_basicOpen_mem_le`: a closed point of `X` lying in an open `U`
  lies in a basic open of a global section contained in `U`.

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 01QO](https://stacks.math.columbia.edu/tag/01QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SerreCriterion

variable {X : Scheme.{u}}

/-- **Sections of a closed subscheme lift.** If the first cohomology of every quasi-coherent
sheaf of ideals on `X` vanishes, then every section of the structure sheaf of a closed
subscheme of `X` is the restriction of a global section of `𝒪_X`. -/
theorem surjective_appTop_subschemeι
    (hH₁ : ∀ J : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj J).IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj J)))
    (D : X.IdealSheafData) :
    Function.Surjective
      ((SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom).val.app
        (op ⊤)) := by
  have hepi : Epi (SheafOfModules.unitToPushforwardObjUnit
      D.subschemeι.toRingCatSheafHom) :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion
      D.subschemeι
  have hkerQC : (kernel (SheafOfModules.unitToPushforwardObjUnit
      D.subschemeι.toRingCatSheafHom)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf D.subschemeι
  have heq := Subobject.underlyingIso
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom))
  have hzero : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (kernel (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom))) :=
    (hH₁ (Subobject.mk (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        D.subschemeι.toRingCatSheafHom)))
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso heq.symm hkerQC)).of_iso
      ((Hfunctor X.ringCatSheaf ⊤ 1).mapIso heq.symm)
  exact Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one X ⊤
    (S := ShortComplex.mk (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        D.subschemeι.toRingCatSheafHom))
      (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)
      (kernel.condition _)) (ShortComplex.shortExact_mk_kernel_ι _) hzero

/-- **A scheme covered by two disjoint opens carries the indicator section of the first**: a
global section which restricts to `1` on `A` and to `0` on `B`. -/
theorem exists_section_eq_one_eq_zero (Y : Scheme.{u}) (A B : Y.Opens)
    (hcover : A ⊔ B = ⊤) (hdisj : A ⊓ B = ⊥) :
    ∃ s : Γ(Y, ⊤), Y.presheaf.map (homOfLE (show A ≤ ⊤ from le_top)).op s = 1 ∧
      Y.presheaf.map (homOfLE (show B ≤ ⊤ from le_top)).op s = 0 := by
  classical
  set O : Bool → Y.Opens := fun b => if b then A else B with hO
  have hcov : ⨆ b, O b = ⊤ := by
    rw [iSup_bool_eq]
    simpa [hO] using hcover
  have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.obj O (fun b => if b then 1 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [show Opens.infLELeft (O i) (O i) = Opens.infLERight (O i) (O i) from
        Subsingleton.elim _ _]
    · have hbot : O i ⊓ O j = ⊥ := by
        cases i <;> cases j <;> simp_all [inf_comm]
      have huniq : Unique (ToType (Y.presheaf.obj (op (O i ⊓ O j)))) := by
        rw [hbot]
        exact CategoryTheory.Limits.Concrete.uniqueOfTerminalOfPreserves _
          (TopCat.Sheaf.isTerminalOfEmpty Y.sheaf)
      exact (huniq.uniq _).trans (huniq.uniq _).symm
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' O ⊤
    (fun b => homOfLE (show O b ≤ ⊤ from le_top)) hcov.ge _ hcompat
  exact ⟨s, hs true, hs false⟩

/-- On a scheme whose quasi-coherent sheaves of ideals have vanishing `H¹`, a closed point `x`
lying in an open `U` lies in the basic open of a global section which is contained in `U`. -/
theorem exists_basicOpen_mem_le
    (hH₁ : ∀ J : Subobject (SheafOfModules.unit X.ringCatSheaf),
      (Subobject.underlying.obj J).IsQuasicoherent →
        IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj J)))
    (U : X.Opens) (x : X) (hxU : x ∈ U) (hxclosed : IsClosed ({x} : Set X)) :
    ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧ X.basicOpen r ≤ U := by
  classical
  set W : TopologicalSpace.Closeds X :=
    ⟨(U : Set X)ᶜ ∪ {x}, (U.isOpen.isClosed_compl).union hxclosed⟩ with hW
  set D : X.IdealSheafData := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal W with hD
  set i := D.subschemeι with hi
  set Xminusx : X.Opens := ⟨({x} : Set X)ᶜ, hxclosed.isOpen_compl⟩ with hXminusx
  have hrange : Set.range i.base = (W : Set X) := by
    rw [hi, hD, AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
    simp [hW]
  have hyW : ∀ y : D.subscheme, i.base y = x ∨ i.base y ∉ (U : Set X) := fun y => by
    simpa [hW] using (hrange ▸ Set.mem_range_self y : i.base y ∈ (W : Set X))
  have hcover : i ⁻¹ᵁ U ⊔ i ⁻¹ᵁ Xminusx = ⊤ :=
    eq_top_iff.2 fun y _ => (hyW y).elim (fun h => Or.inl (show i.base y ∈ U from h ▸ hxU))
      fun h => Or.inr fun hy => h (hy ▸ hxU)
  have hdisj : i ⁻¹ᵁ U ⊓ i ⁻¹ᵁ Xminusx = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    rcases hyW y with hyx | hyZ
    · exact absurd hy.2 (by simpa [hXminusx] using hyx)
    · exact absurd hy.1 hyZ
  obtain ⟨s, hsA, hsB⟩ :=
    exists_section_eq_one_eq_zero D.subscheme (i ⁻¹ᵁ U) (i ⁻¹ᵁ Xminusx) hcover hdisj
  obtain ⟨r, hr⟩ := surjective_appTop_subschemeι hH₁ D s
  obtain rfl : i.appTop r = s := hr
  have hres : ∀ V : D.subscheme.Opens,
      D.subscheme.basicOpen (D.subscheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (i.appTop r)) =
        V ⊓ D.subscheme.basicOpen (i.appTop r) := fun V =>
    AlgebraicGeometry.Scheme.basicOpen_res _ _ _
  have hA_le : i ⁻¹ᵁ U ≤ D.subscheme.basicOpen (i.appTop r) := by
    have := hres (i ⁻¹ᵁ U)
    rw [hsA, AlgebraicGeometry.Scheme.basicOpen_one] at this
    exact inf_eq_left.mp this.symm
  have hB_disj : i ⁻¹ᵁ Xminusx ⊓ D.subscheme.basicOpen (i.appTop r) = ⊥ := by
    have := hres (i ⁻¹ᵁ Xminusx)
    rw [hsB, AlgebraicGeometry.Scheme.basicOpen_zero] at this
    exact this.symm
  obtain ⟨y, hy⟩ : ∃ y : D.subscheme, i.base y = x := by
    have hxW : x ∈ (W : Set X) := Or.inr rfl
    simpa only [Set.mem_range] using (hrange ▸ hxW : x ∈ Set.range i.base)
  refine ⟨r, ?_, ?_⟩
  · have hxbasic : y ∈ i ⁻¹ᵁ X.basicOpen r := by
      rw [AlgebraicGeometry.Scheme.Hom.preimage_basicOpen_top i r]
      exact hA_le (show i.base y ∈ U from hy ▸ hxU)
    simpa [hy] using hxbasic
  · intro z hz
    by_contra hzu
    obtain ⟨y', rfl⟩ : z ∈ Set.range i.base := hrange ▸ (Or.inl hzu : z ∈ (W : Set X))
    have hyB : y' ∈ i ⁻¹ᵁ Xminusx := fun heq => hzu (heq ▸ hxU)
    have hybasic : y' ∈ D.subscheme.basicOpen (i.appTop r) := by
      rw [← AlgebraicGeometry.Scheme.Hom.preimage_basicOpen_top i r]
      exact hz
    have : y' ∈ i ⁻¹ᵁ Xminusx ⊓ D.subscheme.basicOpen (i.appTop r) := ⟨hyB, hybasic⟩
    simp [hB_disj] at this

end Stacks.SerreCriterion

end
