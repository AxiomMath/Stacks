module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.TildeBasicOpen
public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Sections over a principal open of a K-injective resolution

If `L̃₀ ⟶ I` is a quasi-isomorphism from the complex of sheaves associated to a complex `L₀` of
`R`-modules into a K-injective complex, then taking sections over `D(f)` gives a
quasi-isomorphism. This is the unbounded affine vanishing on `Spec R_f`, transported along the open
immersion `Spec R_f ⟶ Spec R` of `D(f)`.

## Main results

* `AlgebraicGeometry.AffineExt.quasiIso_sectionsS_map`: taking sections over `D(f)` carries a
  quasi-isomorphism `L̃₀ ⟶ I` into a K-injective complex to a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.AffineExt

variable (R : CommRingCat.{u})

/-- A principal open of `Spec R` is affine. -/
lemma isAffineOpen_basicOpen (f : R) : IsAffineOpen (basicOpen R f) :=
  IsAffineOpen.Spec_basicOpen f

/-- The open immersion `Spec R_f ⟶ Spec R` of the principal open `D(f)` is `Spec` of the
localization map. -/
lemma fromSpec_basicOpen (f : R) :
    (isAffineOpen_basicOpen R f).fromSpec = Spec.map (locMap R f) := by
  rw [← (isAffineOpen_top (Spec R)).map_fromSpec (IsAffineOpen.Spec_basicOpen f)
    (homOfLE le_top).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

/-- `Spec` of the localization map `R ⟶ R_f` is an open immersion. -/
instance (f : R) : IsOpenImmersion (Spec.map (locMap R f)) :=
  fromSpec_basicOpen R f ▸ IsAffineOpen.isOpenImmersion_fromSpec (isAffineOpen_basicOpen R f)

/-- **Affine vanishing over a principal open, for an unbounded complex.** Let `s : L̃₀ ⟶ I` be a
quasi-isomorphism from the complex of sheaves associated to a complex `L₀` of `R`-modules to a
K-injective complex. Then taking sections over `D(f)` carries `s` to a quasi-isomorphism of
complexes of `R_f`-modules. -/
theorem quasiIso_sectionsS_map (f : R) (L₀ : CochainComplex (ModuleCat.{u} R) ℤ)
    {I : CochainComplex (Spec R).Modules ℤ}
    (s : ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj L₀ ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) :
    QuasiIso (((sectionsS R (basicOpen R f)).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  let hU := isAffineOpen_basicOpen R f
  let j := Scheme.Modules.restrictFunctor (Spec.map (locMap R f))
  let c := ComplexShape.up ℤ
  have hI₂ := Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_of_isIso
    hU.isoSpec.inv _
    (Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_ι (basicOpen R f) I hI)
  have hJ : CochainComplex.IsKInjective ((j.mapHomologicalComplex c).obj I) :=
    (CochainComplex.isKInjective_iff_of_iso ((NatIso.mapHomologicalComplex
      (hU.restrictCompIso ≪≫ Scheme.Modules.restrictFunctorCongr (fromSpec_basicOpen R f)) c).app
        I)).1 hI₂
  have hΓt := quasiIso_globalSectionsOver_map_tilde (locRing R f)
    (((ModuleCat.extendScalars (locMap R f).hom).mapHomologicalComplex c).obj L₀)
    ((Stacks.AffineTilde.restrictTildeComplexIso (locMap R f) L₀).inv ≫
      (j.mapHomologicalComplex c).map s) hJ inferInstance
  let Γ := globalSectionsOver (A := locRing R f) (𝟙 (Spec (locRing R f)))
  have h₂ : QuasiIso ((Γ.mapHomologicalComplex c).map ((j.mapHomologicalComplex c).map s)) := by
    rw [Functor.map_comp] at hΓt
    exact quasiIso_of_comp_left ((Γ.mapHomologicalComplex c).map
      (Stacks.AffineTilde.restrictTildeComplexIso (locMap R f) L₀).inv) _
  let Φ : j ⋙ Γ ≅ sectionsS R (basicOpen R f) :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorCongr (fromSpec_basicOpen R f).symm) Γ ≪≫
      hU.restrictFromSpecGlobalSectionsIso
  exact (quasiIso_iff_of_arrow_mk_iso
    (((j ⋙ Γ).mapHomologicalComplex c).map s) _
    (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex Φ c) (Arrow.mk s))).1 h₂

end AlgebraicGeometry.AffineExt
