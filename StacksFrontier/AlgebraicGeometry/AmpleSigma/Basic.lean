module

public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.AffineLocus
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.SectionExtension.FiniteSet
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist

/-!
# Ampleness on a finite disjoint union of schemes

An invertible module on a finite disjoint union of schemes is ample as soon as its restriction to
every summand is. This is the assertion the proof of [Stacks, Tag 0B43] uses for its clause (4)
and whose proof the source omits, and it is what the finite surjection
`C₁ ⨿ … ⨿ C_t ⨿ x₁ ⨿ … ⨿ x_r ⟶ X` of the proof of [Stacks, Tag 0B5Y] needs beyond
[Stacks, Tag 0B5V].

## Main results

* `AlgebraicGeometry.isAmple_sigma_of_forall_isAmple_pullback_sigmaι`: **an invertible module on
  `∐ Z` whose restriction to every summand `Z j` is ample is ample.** The index type is finite;
  nothing else is assumed of the summands.
* `Stacks.AmpleSigma.exists_sectionsOfTop_pullback_eq`: **a prescribed global section on each
  summand comes from one global section on the disjoint union.** No compatibility condition: the
  summands do not meet.
* `Stacks.AmpleSigma.modulePullbackSection_sectionsOfTop_of_unitHom`: the pullback of a global
  section along a morphism of schemes, read off the pullback of the morphism out of the structure
  sheaf that the section names.
* `Stacks.AmpleSigma.le_opensRange_sigmaι_of_forall_disjoint`: an open of `∐ Z` missing every
  summand but the `j`th lies in the `j`th.

## The route

Ampleness is a pointwise condition ([Stacks, Tag 01PS],
`AlgebraicGeometry.Scheme.Modules.IsAmple`): the space is quasi-compact, and every point lies in
an affine nonvanishing locus of a global section of some positive tensor power. So no exponent has
to be made uniform over the summands. A point `x` of `∐ Z` is `Sigma.ι Z j y` for one summand
(`StacksTag09NE.exists_component_point_of_sigma`), ampleness on `Z j` supplies an exponent `n` and
a section `t` of `(N|_{Z j})^{⊗ n}` with `(Z j)_t` affine around `y`, and the three remaining steps
are:

* **`t` becomes a global section of `N^{⊗ n}` on `∐ Z`, vanishing on the other summands.** The
  tensor powers are matched by `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`, and the
  extension is `Stacks.AmpleSigma.exists_sectionsOfTop_pullback_eq`: restriction to the summands
  is a bijection on morphisms of modules over a coproduct
  (`AlgebraicGeometry.exists_hom_of_summandHoms`), a global section of a module is a morphism out
  of the structure sheaf (`AlgebraicGeometry.Scheme.Modules.unitHomEquivTop`), and the pullback of
  the structure sheaf is the structure sheaf
  (`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`).
* **Its nonvanishing locus is the image of `(Z j)_t`.** [Stacks, Tag 0H78],
  `Stacks.SheafOfModules.preimage_nonvanishingOpen`, computes the preimage of the locus on each
  summand: it is `(Z j)_t` on the `j`th and empty on the others, because the zero section vanishes
  everywhere. An open of `∐ Z` meeting only the `j`th summand is the image of its preimage there.
* **That image is affine.** `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`, the
  summand inclusion being an open immersion.

Quasi-compactness of `∐ Z` is the homeomorphism `AlgebraicGeometry.sigmaMk` with the topological
disjoint union of the summands, each quasi-compact because it carries an ample module.

## Implementation notes

**The extension by zero is taken on morphisms, not on sections.** The alternative is to glue the
section over the open `(Sigma.ι Z j).opensRange` against the zero section over its complement —
`Stacks.Tag0B5PClopenLift.exists_resTop_eq_of_disjoint_cover` does exactly that — but it produces
a section over an *open of* `∐ Z`, and turning the given global section on the scheme `Z j` into a
section over that open needs the comparison between pulling a module back along an open immersion
and restricting it, which this repository does not have. Restriction of *morphisms* to the
summands, on the other hand, is already known to be bijective, so going through
`unitHomEquivTop` needs no such comparison.

**The glue between a pulled-back section and a pulled-back morphism.**
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_sections_naturality` is stated for an arbitrary
morphism `k : f⁺ M ⟶ N` out of the pullback; at `k = 𝟙` it becomes
`Stacks.AmpleSigma.modulePullbackSection_sectionsOfTop_of_unitHom`, which is the form consumed
here, since `Stacks.SheafOfModules.modulePullbackSection` is built from the unit of `f^* ⊣ f_*`
and the unit is `Adjunction.homEquiv` at the identity.

## References

* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B43](https://stacks.math.columbia.edu/tag/0B43)
* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace Stacks.AmpleSigma

/-! ### The pullback of a global section, from the pullback of its classifying morphism -/

/-- **The pullback of a global section is read off the pullback of the morphism out of the
structure sheaf that the section names.** Let `f : X ⟶ Y`, let `c` be a global section of a module
`M` on `Y` and let `d` be a global section of `f⁺ M`. If the morphism `𝒪_X ⟶ f⁺ M` named by `d`,
precomposed with `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, is the pullback of the
morphism `𝒪_Y ⟶ M` named by `c`, then `d` is the pullback of `c`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_sections_naturality` at the identity of
`f⁺ M`: there `Adjunction.homEquiv` applied to the identity is the unit of `f^* ⊣ f_*`, which is
what `Stacks.SheafOfModules.modulePullbackSection` is built from. -/
public theorem modulePullbackSection_sectionsOfTop_of_unitHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (c : Γ(M, ⊤)) (d : Γ((Scheme.Modules.pullback f).obj M, ⊤))
    (h : (Scheme.Modules.pullbackUnitIso f).hom ≫
        Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj M) d
      = (Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop M c)) :
    modulePullbackSection f.toLRSHom M (sectionsOfTop M c)
      = sectionsOfTop ((Scheme.Modules.pullback f).obj M) d := by
  have hnat := Scheme.Modules.pullbackUnitIso_sections_naturality f M
    ((Scheme.Modules.pullback f).obj M) (𝟙 _) c
  rw [Category.comp_id] at hnat
  have e : (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ := by simp
  set d₀ := ((Scheme.Modules.pullback f).obj M).presheaf.map
    (eqToHom e).op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M
      ((Scheme.Modules.pullback f).obj M) (𝟙 _)).app ⊤ c) with hd₀
  have hdd : d = d₀ :=
    (Scheme.Modules.unitHomEquivTop _).injective
      ((Iso.cancel_iso_hom_left (Scheme.Modules.pullbackUnitIso f) _ _).mp
        (hnat.trans h.symm)).symm
  subst hdd
  have hid : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M
      ((Scheme.Modules.pullback f).obj M) (𝟙 _)) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
    rw [Adjunction.homEquiv_unit]
    simp
  have hres : ∀ x : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ ⊤),
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom e).op x = x := by
    intro x
    rw [show (eqToHom e).op
      = 𝟙 (op (⊤ : X.Opens)) from Subsingleton.elim _ _]
    simp
    rfl
  have key : Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom M (op ⊤) c = d₀ := by
    rw [hd₀, hid]
    exact (hres _).symm
  exact Stacks.AmpleReducedDimensionOne.sections_eq_of_eval_top
    ((modulePullbackSection_eval_top f.toLRSHom M (sectionsOfTop M c)).trans
      (((congrArg (fun y => Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom M (op ⊤) y)
          (sectionsOfTop_eval_top M c)).trans key).trans
        (sectionsOfTop_eval_top _ d₀).symm))

/-! ### Prescribing a global section on each summand -/

variable {ι : Type u} [Finite ι] (Z : ι → Scheme.{u})

omit [Finite ι] in
/-- **A prescribed global section on each summand comes from a single global section on the
disjoint union.** For a module `M` on `∐ Z` and an arbitrary family of global sections of the
restrictions `M|_{Z k}`, there is a global section of `M` pulling back to the `k`th member on the
`k`th summand.

There is no compatibility condition on the family, because the summands do not meet: restriction
to them is a bijection on morphisms of modules over a coproduct
(`AlgebraicGeometry.exists_hom_of_summandHoms`), and a global section of a module is a morphism
out of the structure sheaf. -/
public theorem exists_sectionsOfTop_pullback_eq (M : (∐ Z).Modules)
    (a : ∀ k : ι, Γ((Scheme.Modules.pullback (Sigma.ι Z k)).obj M, ⊤)) :
    ∃ c : Γ(M, ⊤), ∀ k : ι,
      modulePullbackSection (Sigma.ι Z k).toLRSHom M (sectionsOfTop M c)
        = sectionsOfTop ((Scheme.Modules.pullback (Sigma.ι Z k)).obj M) (a k) := by
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.exists_hom_of_summandHoms (Z := Z)
    (Scheme.unitModule (∐ Z)) M
    (fun k => (Scheme.Modules.pullbackUnitIso (Sigma.ι Z k)).hom ≫
      Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback (Sigma.ι Z k)).obj M) (a k))
  refine ⟨(Scheme.Modules.unitHomEquivTop M).symm ψ, fun k => ?_⟩
  refine modulePullbackSection_sectionsOfTop_of_unitHom (Sigma.ι Z k) M _ (a k) ?_
  rw [Equiv.apply_symm_apply]
  exact (hψ k).symm

/-! ### An open of a disjoint union sitting in one summand -/

/-- **An open of `∐ Z` disjoint from every summand but the `j`th lies in the `j`th.** Every point
of a coproduct of schemes lies on some summand
(`StacksTag09NE.exists_component_point_of_sigma`). -/
public theorem le_opensRange_sigmaι_of_forall_disjoint (W : (∐ Z).Opens) (j : ι)
    (hdisj : ∀ k, k ≠ j → Disjoint W (Sigma.ι Z k).opensRange) :
    W ≤ (Sigma.ι Z j).opensRange := by
  intro w hw
  obtain ⟨k, z, rfl⟩ := StacksTag09NE.exists_component_point_of_sigma Z w
  by_cases hkj : k = j
  · exact hkj ▸ ⟨z, rfl⟩
  · exact ((hdisj k hkj).le_bot (show (Sigma.ι Z k).base z ∈ W ⊓ (Sigma.ι Z k).opensRange from
      ⟨hw, ⟨z, rfl⟩⟩)).elim

end Stacks.AmpleSigma

/-! ### Ampleness on a finite disjoint union -/

namespace AlgebraicGeometry

/-- **An invertible module on a finite disjoint union of schemes whose restriction to every
summand is ample is ample.** No hypothesis on the summands beyond that: the index type is finite
and the restrictions are ample.

This is the assertion whose proof the source of [Stacks, Tag 0B43] omits in its clause (4), and
the input that the finite surjection from the disjoint union of the irreducible components needs
in the proof of [Stacks, Tag 0B5Y].

Ampleness is pointwise, so the exponents produced on the different summands never have to be
reconciled: for `x = Sigma.ι Z j y` only the exponent coming from `Z j` is used. The section
witnessing it on `Z j` is extended by zero over the other summands
(`Stacks.AmpleSigma.exists_sectionsOfTop_pullback_eq`), its nonvanishing locus is then the image
of the one on `Z j` ([Stacks, Tag 0H78] on each summand, and
`Stacks.AmpleSigma.le_opensRange_sigmaι_of_forall_disjoint`), and that image is affine because a
summand inclusion is an open immersion. -/
public theorem isAmple_sigma_of_forall_isAmple_pullback_sigmaι {ι : Type u} [Finite ι]
    (Z : ι → Scheme.{u}) (N : (∐ Z).Modules)
    (hN : SheafOfModules.IsInvertible (∐ Z).toRingedSpace.presheaf
      (structureSheafRing (∐ Z).toRingedSpace).property N)
    (hample : ∀ j : ι, @Scheme.Modules.IsAmple (Z j)
      ((Scheme.Modules.pullback (Sigma.ι Z j)).obj N)
      (SheafOfModules.isInvertible_pullback (Sigma.ι Z j) N)) :
    @Scheme.Modules.IsAmple (∐ Z) N hN := by
  classical
  have := hN
  have hcpt : ∀ j : ι, CompactSpace ↥(Z j) := fun j => (hample j).1
  refine ⟨(sigmaMk Z).compactSpace, fun x => ?_⟩
  obtain ⟨j, y, rfl⟩ := StacksTag09NE.exists_component_point_of_sigma Z x
  obtain ⟨n, hn, t, hyt, htaff⟩ := (hample j).2 y
  -- the tensor power on the disjoint union, and its comparison with the one on the summand
  set M : (∐ Z).Modules := Scheme.Modules.tensorPowerModules N (n : ℤ) with hM
  have : SheafOfModules.IsInvertible (Z j).toRingedSpace.presheaf
      (structureSheafRing (Z j).toRingedSpace).property
      ((Scheme.Modules.pullback (Sigma.ι Z j)).obj N) :=
    SheafOfModules.isInvertible_pullback (Sigma.ι Z j) N
  set P := Scheme.Modules.pullbackTensorPowerIso (Sigma.ι Z j) N n with hP
  -- the prescribed family: `t` on the `j`th summand, zero elsewhere
  set a : ∀ k : ι, Γ((Scheme.Modules.pullback (Sigma.ι Z k)).obj M, ⊤) :=
    Function.update (fun k => (0 : Γ((Scheme.Modules.pullback (Sigma.ι Z k)).obj M, ⊤))) j
      ((_root_.SheafOfModules.sectionsMap P.inv t).eval (op ⊤)) with ha
  obtain ⟨c, hc⟩ := Stacks.AmpleSigma.exists_sectionsOfTop_pullback_eq Z M a
  set s : M.sections := sectionsOfTop M c with hs
  set W : (∐ Z).Opens := nonvanishingOpen (X := (∐ Z).toRingedSpace) M s with hW
  -- off the `j`th summand the section vanishes
  have hother : ∀ k, k ≠ j → Disjoint W (Sigma.ι Z k).opensRange := by
    intro k hk
    refine disjoint_iff_inf_le.mpr fun w hw => ?_
    obtain ⟨z, rfl⟩ := hw.2
    have h1 := (preimage_nonvanishingLocus (Sigma.ι Z k).toLRSHom M s).subst (motive := (z ∈ ·))
      hw.1
    rw [hc k, show a k = 0 from Function.update_of_ne hk _ _] at h1
    exact (Set.eq_empty_iff_forall_notMem.mp (nonvanishingLocus_sectionsOfTop_zero
      (X := (Z k).toRingedSpace) ((Scheme.Modules.pullback (Sigma.ι Z k)).obj M)) z h1).elim
  have : Stacks.SheafOfModules.IsInvertible (Z j).presheaf
      (structureSheafRing (Z j).toRingedSpace).property
      ((Scheme.Modules.pullback (Sigma.ι Z j)).obj M) :=
    Stacks.Modules.isInvertible_pullback (Sigma.ι Z j) M
  -- on the `j`th summand the locus is the one `t` cuts out
  have hj : (Sigma.ι Z j) ⁻¹ᵁ W
      = nonvanishingOpen (X := (Z j).toRingedSpace)
        (tensorPower (Z j).toRingedSpace.presheaf
          (structureSheafRing (Z j).toRingedSpace).property
          ((Scheme.Modules.pullback (Sigma.ι Z j)).obj N) (n : ℤ)) t := by
    have haj : a j = (_root_.SheafOfModules.sectionsMap P.inv t).eval (op ⊤) :=
      Function.update_self _ _ _
    have hsecj : modulePullbackSection (Sigma.ι Z j).toLRSHom M s
        = _root_.SheafOfModules.sectionsMap P.inv t :=
      (hc j).trans ((congrArg
        (sectionsOfTop ((Scheme.Modules.pullback (Sigma.ι Z j)).obj M)) haj).trans
        (Stacks.SheafOfModules.Invertible.sectionsOfTop_eval_top_self _ _))
    exact (preimage_nonvanishingOpen (Sigma.ι Z j) M s).trans
      ((congrArg (fun σ => nonvanishingOpen (X := (Z j).toRingedSpace)
          ((Scheme.Modules.pullback (Sigma.ι Z j)).obj M) σ) hsecj).trans
        (nonvanishingOpen_sectionsMap (X := (Z j).toRingedSpace) P.symm t))
  -- the locus is the image of the one on the `j`th summand, hence affine
  have himg : (Sigma.ι Z j) ''ᵁ nonvanishingOpen (X := (Z j).toRingedSpace)
      (tensorPower (Z j).toRingedSpace.presheaf
        (structureSheafRing (Z j).toRingedSpace).property
        ((Scheme.Modules.pullback (Sigma.ι Z j)).obj N) (n : ℤ)) t = W := by
    rw [← hj, Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr
      (Stacks.AmpleSigma.le_opensRange_sigmaι_of_forall_disjoint Z W j hother)
  have haff : IsAffineOpen W := himg ▸ htaff.image_of_isOpenImmersion (Sigma.ι Z j)
  exact ⟨n, hn, s, hj.ge hyt, haff⟩

end AlgebraicGeometry

end
