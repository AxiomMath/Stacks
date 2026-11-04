module

public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections

/-!
# The structure sheaf has no sections supported on an effective Cartier divisor

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`D ⊆ X` be an effective Cartier divisor in the sense of Stacks 083B(2).  Then `𝒪_X` has no
nonzero local section whose support lies in the point set of `D`: a regular function on an
étale chart of `X` which vanishes off `D` vanishes.

## Main results

* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_structureSheaf_of_isEffectiveCartierDivisor`:
  the structure sheaf of `X`, viewed as an `𝒪_X`-module, has no nonzero local section supported
  on the point set of an effective Cartier divisor.

## Implementation notes

The sections of `𝒪_X` over a chart are by construction the global regular functions on the
chart, `AlgebraicGeometry.Space.structurePresheaf`, and that presheaf is literally the
composite of the chart functor with `AlgebraicGeometry.Scheme.Γ`; so restriction of a section
of `SheafOfModules.unit (AlgebraicGeometry.Space.structureRingSheaf …)` along a morphism of
charts *is* pullback of global functions along the underlying morphism of schemes, and no
comparison map intervenes.

This is deliberately stated for the structure sheaf and not for a general `𝒪_X`-module: what
density supplies is injectivity of restriction on *functions*, and
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_of_injective_etaleModulePullbackAdjunction_unit`
records that the corresponding statement for the module-level restriction unit is a genuinely
stronger input which this library does not have.

## References

* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 0836](https://stacks.math.columbia.edu/tag/0836)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes whose structure-sheaf map is a monomorphism is injective on global
sections. -/
private theorem injective_appTop_of_mono_c {A Y : Scheme.{u}} (f : A ⟶ Y) (h : Mono f.c) :
    Function.Injective f.appTop.hom :=
  (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.app ⊤)).mp
    ((NatTrans.mono_iff_mono_app f.c).mp h (op ⊤))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structure sheaf of an algebraic space has no section supported on an effective
Cartier divisor.**  Let `D ⊆ X` be an effective Cartier divisor on an algebraic space `X` over
a scheme `S`.  Then every local section of `𝒪_X` whose support maps into the point set of `D`
is zero. -/
theorem hasNoSectionsSupportedIn_structureSheaf_of_isEffectiveCartierDivisor
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    HasNoSectionsSupportedIn B S hS X (subspacePointSet B S hS X.1 D.1)
      (SheafOfModules.unit (structureRingSheaf B S hS X)) := by
  have hU : IsOpenImmersion B S hS (openComplement B S hS D.1).ι :=
    (isOpenSubspace_openComplement B S hS X.2 D.1 D.2).2
  have hmono : ∀ V : SmallEtale B S hS X.1,
      Mono ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).c :=
    (isSchemeTheoreticallyDense_iff_forall_chart_mono_c B S hS
        (openComplement B S hS D.1) hU).1
      (isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor B S hS X D hD)
  refine fun W s hs => ?_
  have hoi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd W.1.hom)) := hU.property_snd W.1.hom
  have hetale : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd W.1.hom)) := inferInstance
  let W' : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map (hU.rep.snd W.1.hom) ≫ W.1.hom),
      etale_comp_of_scheme B S hS (hU.rep.snd W.1.hom) W.1.hom hetale W.2⟩
  let i : W' ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk (hU.rep.snd W.1.hom) rfl)
  have himage : ImageInOpen B S hS X.1
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom ⁻¹'
        (subspacePointSet B S hS X.1 D.1)ᶜ) i := by
    intro y
    have key : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom
          (pointsMap B S hS (yoneda.obj (hU.rep.pullback W.1.hom))
            (yoneda.map (hU.rep.snd W.1.hom)) y) =
        pointsMap B S hS (openComplement B S hS D.1).toFunctor
            (openComplement B S hS D.1).ι
          (pointsMap B S hS (yoneda.obj (hU.rep.pullback W.1.hom))
            (hU.rep.fst W.1.hom) y) := by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hU.rep.w W.1.hom]
    show pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom
        (pointsMap B S hS (yoneda.obj (hU.rep.pullback W.1.hom))
          (yoneda.map (hU.rep.snd W.1.hom)) y) ∈ (subspacePointSet B S hS X.1 D.1)ᶜ
    rw [key]
    exact (range_pointsMap_ι_openComplement B S hS D.1).le (Set.mem_range_self _)
  have hzero : (SheafOfModules.unit (structureRingSheaf B S hS X)).val.map i.op s = 0 :=
    restrict_eq_zero_of_sectionSupportedIn_of_imageInOpen B S hS X
      (subspacePointSet B S hS X.1 D.1) (SheafOfModules.unit (structureRingSheaf B S hS X))
      W s hs W' i himage
  have hinj : Function.Injective
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hU.rep.snd W.1.hom)).op).hom := by
    rw [Scheme.Γ_map_op]
    exact injective_appTop_of_mono_c _ (hmono W)
  have hs0 : (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd W.1.hom)).op).hom s = 0 := hzero
  have h00 : (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd W.1.hom)).op).hom 0 = 0 := map_zero _
  exact hinj (hs0.trans h00.symm)

end Space

end AlgebraicGeometry

end
