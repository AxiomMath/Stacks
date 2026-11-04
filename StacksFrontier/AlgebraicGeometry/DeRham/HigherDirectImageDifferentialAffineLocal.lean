module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.OpenRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.AbelianCohomologyOverOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.AbelianHigherDirectImageMapZero
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence

/-!
# The de Rham differential on higher direct images is affine-local on the base

Let `f : X ⟶ S` be a morphism of schemes. The de Rham differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}`
is additive but not `𝒪_X`-linear; it induces a morphism of sheaves of abelian groups
`R^q f_* Ω^p_{X/S} ⟶ R^q f_* Ω^{p+1}_{X/S}`. This morphism vanishes as soon as, for every affine
open `V ⊆ S`, the de Rham differential of `f⁻¹(V) ⟶ Spec Γ(S, V)` vanishes on
`H^q(f⁻¹(V), -)`: the higher direct image is the sheafification of `V ↦ H^q(f⁻¹(V), -)`
([Stacks, Tag 072W]), cohomology over `f⁻¹(V)` is that of the restriction to the open subscheme
([Stacks, Tag 01E1]), and the forms of `f` restricted to `f⁻¹(V)` are those of
`f⁻¹(V) ⟶ Spec Γ(S, V)`, compatibly with `d` ([Stacks, Tag 0FL5]).

## Main results

* `AlgebraicGeometry.Scheme.Hom.higherDirectImage_map_deRham_d_eq_zero_of_affine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cohomology.SupportedComplexes (abelianRestrictOpen)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism `f⁻¹(V) ⟶ Spec Γ(S, V)` attached to an affine open `V` of the base. -/
abbrev restrictAffine {V : S.Opens} (hV : IsAffineOpen V) :
    (f ⁻¹ᵁ V).toScheme ⟶ Spec Γ(S, V) :=
  f ∣_ V ≫ hV.isoSpec.hom

/-- The square formed by `f⁻¹(V) ⟶ X`, `f`, `f.restrictAffine hV` and `Spec Γ(S, V) ≅ V ⟶ S`
commutes. -/
theorem restrictAffine_comm {V : S.Opens} (hV : IsAffineOpen V) :
    (f ⁻¹ᵁ V).ι ≫ f = f.restrictAffine hV ≫ (hV.isoSpec.inv ≫ V.ι) := by
  simp [restrictAffine, morphismRestrict_ι]

/-- The square formed by `f⁻¹(V) ⟶ X`, `f`, `f.restrictAffine hV` and `Spec Γ(S, V) ≅ V ⟶ S`
is a pullback square. -/
theorem isPullback_restrictAffine {V : S.Opens} (hV : IsAffineOpen V) :
    IsPullback (f ⁻¹ᵁ V).ι (f.restrictAffine hV) f (hV.isoSpec.inv ≫ V.ι) :=
  (isPullback_morphismRestrict f V).flip.of_iso (Iso.refl _) (Iso.refl _) hV.isoSpec
    (Iso.refl _) (by simp) (by simp [restrictAffine]) (by simp) (by simp)

/-- **The de Rham differential on higher direct images is affine-local on the base.** If for
every affine open `V ⊆ S` the de Rham differential `Ω^p ⟶ Ω^{p+1}` of `f⁻¹(V) ⟶ Spec Γ(S, V)`
induces zero on `H^q(f⁻¹(V), -)`, then the induced morphism
`R^q f_* Ω^p_{X/S} ⟶ R^q f_* Ω^{p+1}_{X/S}` of sheaves of abelian groups is zero. -/
theorem higherDirectImage_map_deRham_d_eq_zero_of_affine (p q : ℕ)
    (h : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      ((sectionsFunctor (f ⁻¹ᵁ V).toScheme.carrier ⊤).rightDerived q).map
        ((SheafOfModules.toSheaf _).map ((f.restrictAffine hV).deRhamComplex.d p (p + 1))) = 0) :
    (Stacks.Cohomology.AbelianSheaf.higherDirectImage f.base q).map
      ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d p (p + 1))) = 0 := by
  have key : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} (f ⁻¹ᵁ V) q).map
        ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d p (p + 1))) = 0 := by
    intro V hV
    have hiso : ∀ n : ℤ, IsIso (relativeDifferentialFormsMap (f ⁻¹ᵁ V).ι f (f.restrictAffine hV)
        (hV.isoSpec.inv ≫ V.ι) (f.restrictAffine_comm hV) n) := fun n =>
      isIso_relativeDifferentialFormsMap_of_isPullback _ _ _ _ (f.isPullback_restrictAffine hV) n
    refine Stacks.Cohomology.AbelianSheaf.cohomologyOver_map_eq_zero_of_restrict (f ⁻¹ᵁ V) _ q ?_
    exact (functor_map_restrict_deRham_d_eq_zero_iff (f ⁻¹ᵁ V) f (f.restrictAffine hV)
      (hV.isoSpec.inv ≫ V.ι) (f.restrictAffine_comm hV) hiso
      (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} ⊤ q) p).2 (h V hV)
  refine Stacks.Cohomology.AbelianSheaf.higherDirectImage_map_eq_zero_of_isBasis f.base _ q
    (Opens.isBasis_iff_nbhd.mpr fun {U x} hx => ?_)
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hx
  exact ⟨V, key V hV, hxV, hVU⟩

end AlgebraicGeometry.Scheme.Hom
