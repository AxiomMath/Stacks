module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToScheme
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Weak admissibility of the `𝔪`-adic topology of a complete local ring

A ring carrying the `I`-adic topology of an ideal `I` is weakly admissible as soon as it is
`I`-adically complete. In particular a Noetherian complete local ring `R` with its `𝔪`-adic
topology is a weakly admissible topological ring, the formal spectrum
`Spf R = colim_J Spec (R ⧸ J)` over a base scheme `S` is an affine formal algebraic space, and
restriction along `Spf R ⟶ Spec R` is a bijection from the `S`-morphisms `Spec R ⟶ X` to the
morphisms `Spf R ⟶ X` for every scheme `X` in the site.

## Main results

* `IsAdic.isLinearTopology`: an adic topology is a linear topology.
* `TopologicalRing.isWeaklyAdmissible_of_isAdicComplete`: an adically complete ring carrying
  that adic topology is weakly admissible.
* `AlgebraicGeometry.FormalSpace.isWeaklyAdmissible_maximalAdicTopology`: the `𝔪`-adic
  topology of a Noetherian complete local ring is weakly admissible.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum_maximalAdic`: the
  formal spectrum of a Noetherian complete local ring is an affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.existsUnique_equiv_specHom_formalSpectrumHom_maximalAdic`: the
  bijection between the morphisms out of `Spec R` and those out of `Spf R` to a scheme in the
  site.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AQG](https://stacks.math.columbia.edu/tag/0AQG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- An adic topology is a linear topology. -/
public theorem IsAdic.isLinearTopology {R : Type u} [CommRing R] [TopologicalSpace R]
    {I : Ideal R} (h : IsAdic I) : IsLinearTopology R R := by
  subst h
  exact Ideal.isLinearTopology I

/-- A ring carrying the `I`-adic topology and complete for `I` is weakly admissible. -/
public theorem TopologicalRing.isWeaklyAdmissible_of_isAdicComplete {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {I : Ideal R} (hadic : _root_.IsAdic I)
    (hc : IsAdicComplete I R) :
    @TopologicalRing.IsWeaklyAdmissible R _ _ _ (IsAdic.isLinearTopology hadic) :=
  let := IsAdic.isLinearTopology hadic
  TopologicalRing.isWeaklyAdmissible_of_isAdic hadic hc

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R]

/-- The `𝔪`-adic topology of a Noetherian complete local ring is a linear topology. -/
public theorem isLinearTopology_maximalAdicTopology
    (hR : IsNoetherianCompleteLocalRing R) :
    @IsLinearTopology R R _ _ _ (maximalAdicTopology hR) :=
  Ideal.isLinearTopology _

/-- The `𝔪`-adic topology of a Noetherian complete local ring is weakly admissible. -/
public theorem isWeaklyAdmissible_maximalAdicTopology
    (hR : IsNoetherianCompleteLocalRing R) :
    @TopologicalRing.IsWeaklyAdmissible R _ (maximalAdicTopology hR) _
      (isLinearTopology_maximalAdicTopology hR) :=
  @TopologicalRing.isWeaklyAdmissible_of_isAdicComplete R _ (maximalAdicTopology hR) _
    (@IsLocalRing.maximalIdeal R _ hR.isLocal) (isAdic_maximalAdicTopology hR) hR.isComplete

/-- The maximal ideal of a Noetherian complete local ring is a weak ideal of definition for its
`𝔪`-adic topology. -/
public theorem isWeakIdealOfDefinition_maximalAdicTopology
    (hR : IsNoetherianCompleteLocalRing R) :
    @TopologicalRing.IsWeakIdealOfDefinition R _ (maximalAdicTopology hR)
      (@IsLocalRing.maximalIdeal R _ hR.isLocal) :=
  @TopologicalRing.isWeakIdealOfDefinition_of_isAdic R _ (maximalAdicTopology hR) _ _
    (isAdic_maximalAdicTopology hR)

/-- The residue ring of a local ring is again a local ring. -/
public theorem isLocalRing_quotient_maximalIdeal [IsLocalRing R] :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R) :=
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- The formal spectrum of a Noetherian complete local ring over a base, formed from the
quotient system of its spectrum for the `𝔪`-adic topology, is an affine formal algebraic
space. -/
public theorem isAffineFormalAlgebraicSpace_formalSpectrum_maximalAdic
    (hR : IsNoetherianCompleteLocalRing R) (hRS : B.Contains (Spec (.of R)))
    (p : Spec (.of R) ⟶ S)
    (hB : @QuotientSystem.HasLargeSite B S hS R _ (maximalAdicTopology hR)
      (@quotientSystemOfSpec B S hS R _ (maximalAdicTopology hR) hRS p)) :
    IsAffineFormalAlgebraicSpace B S hS
      (@formalSpectrum B S hS R _ (maximalAdicTopology hR)
        (@quotientSystemOfSpec B S hS R _ (maximalAdicTopology hR) hRS p)) :=
  @isAffineFormalAlgebraicSpace_formalSpectrum B S hS R _ (maximalAdicTopology hR) _
    (isLinearTopology_maximalAdicTopology hR)
    (isWeaklyAdmissible_maximalAdicTopology hR) _ hB

/-- For a Noetherian complete local ring `R` over a base `S` and a scheme `X` in the site,
restriction along `Spf R ⟶ Spec R` is a bijection from the `S`-morphisms `Spec R ⟶ X` to the
morphisms `Spf R ⟶ X`, uniquely characterized by its restrictions to the quotient stages. -/
public theorem existsUnique_equiv_specHom_formalSpectrumHom_maximalAdic
    (hR : IsNoetherianCompleteLocalRing R) (hRS : B.Contains (Spec (.of R)))
    (p : Spec (.of R) ⟶ S)
    (X : Scheme.{u}) (hX : B.Contains X) (xS : X ⟶ S) :
    let Xo : BigFppfOver B S hS :=
      Over.mk (ObjectProperty.homMk xS : B.obj hX ⟶ B.obj hS)
    ∃! e : ((Over.mk p : Over S) ⟶ (Over.mk xS : Over S)) ≃
        (@formalSpectrum B S hS R _ (maximalAdicTopology hR)
            (@quotientSystemOfSpec B S hS R _ (maximalAdicTopology hR) hRS p) ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Xo),
      ∀ (f : (Over.mk p : Over S) ⟶ (Over.mk xS : Over S))
        (J : { I : Ideal R // @TopologicalRing.IsWeakIdealOfDefinition R _
          (maximalAdicTopology hR) I }),
        ∃ g : (BigAffineFppf.inclusion B S hS).obj
            (@QuotientSystem.stage B S hS R _ (maximalAdicTopology hR)
              (@quotientSystemOfSpec B S hS R _ (maximalAdicTopology hR) hRS p) J) ⟶ Xo,
          B.inclusion.map g.left =
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f.left ∧
            @formalSpectrumInclusion B S hS R _ (maximalAdicTopology hR)
                (@quotientSystemOfSpec B S hS R _ (maximalAdicTopology hR) hRS p)
                (OrderDual.toDual J) ≫ e f =
              (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g :=
  @existsUnique_equiv_specHom_formalSpectrumHom B S hS R _ (maximalAdicTopology hR) _
    (isLinearTopology_maximalAdicTopology hR)
    (isWeaklyAdmissible_maximalAdicTopology hR)
    (@quotientSystemOfSpec B S hS R _ (maximalAdicTopology hR) hRS p) p
    (@quotientSystemOfSpec_overS B S hS R _ (maximalAdicTopology hR) hRS p)
    (@IsLocalRing.maximalIdeal R _ hR.isLocal)
    (isWeakIdealOfDefinition_maximalAdicTopology hR)
    (@isLocalRing_quotient_maximalIdeal R _ hR.isLocal) X hX xS

end AlgebraicGeometry.FormalSpace

end
