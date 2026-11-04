module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeTorDimension
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartDerivedStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPrincipalityTransfer
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalkPerfect
public import StacksFrontier.Homology.Eta.Perfect.BoundedComplexPerfectModel
public import StacksFrontier.Homology.Eta.Perfect.SectionsBasisPresentation

/-!
# A finite free model of a good triple at a stalk

Let `(X, D, M)` be a triple as in Situation 0F8S, let `x ∈ X` and let `A = 𝒪_{X,x}` be the local
ring.  This file produces, at every point of a good triple, a bounded complex `C` of finite free
`A`-modules together with a generator `a` of the stalk `ℐ_x` of the ideal sheaf of `D` such that
`a` is a nonzerodivisor, every determinantal ideal `I_i(C, a)` is principal, and `C` represents
the derived stalk of `M` at `x`.

Away from `D` the stalk ideal is the unit ideal, so any generator is a unit and every
determinantal ideal is the unit ideal; the complex itself comes from the perfectness of `M`,
whose derived stalk is therefore a perfect object of `D(A)`, i.e. is represented by a bounded
complex of finite projective — hence, `A` being local, finite free — modules.  On `D` the
good-triple condition supplies an affine chart `(U, A₀, f, M^•)` through `x` with principal
determinantal ideals, and the complex is the base change `M^• ⊗_{A₀} A` along the germ map:
principality is inherited by Tags 0F8T and 0GSU, and the germ of `f` is a nonzerodivisor
generating `ℐ_x`.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.stalkFunctorAt`: the stalk functor at `x`,
  valued in modules over the local ring `𝒪_{X,x}`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.derivedStalk`: the derived stalk at `x` of the
  perfect object of the situation.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedStalk`: the derived stalk is a
  perfect object of the derived category of `𝒪_{X,x}`-modules.
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_boundedComplex_derivedStalk`: hence it is
  represented by a bounded complex of finite free `𝒪_{X,x}`-modules, in chosen bases.
* `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_q_baseChange_iso_derivedStalk`: the
  base change of a chart's complex along the germ map represents the derived stalk, at the model
  of the derived category the situation carries.
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_boundedComplex_generator_derivedStalk`:
  the statement described above.

## Implementation notes

The stalk functor is taken at the `OXMod` spelling of the category of `𝒪_X`-modules, which is
the spelling a situation carries its perfect object at, and with its scalars read over the
local ring `𝒪_{X,x}` through `AlgebraicGeometry.RingedSpace.ringCatStalkEquiv`; this is
`AlgebraicGeometry.RingedSpace.moduleStalkOver`, the functor
`AlgebraicGeometry.RingedSpace.isPerfect_moduleStalkOver_of_isPerfect` is stated for.  Written
instead at the `Scheme.Modules` spelling, the exactness instances the induced functor on derived
categories needs are not found; this is the clash recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge`.

A model of the derived category of `𝒪_{X,x}`-modules is carried as an instance hypothesis, at
the universe at which the situation carries its own: the statement cannot be made without one.

The comparison of the base change of the chart's complex along the germ map with the derived
stalk is
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.nonempty_q_baseChange_iso_derivedStalk`
of `ChartDerivedStalk.lean`, which is written at the standard model of the derived category of
`𝒪_{X,x}`-modules; the model a situation carries is an instance argument here, so that
comparison is first recast as a quasi-isomorphism,
`AffineChart.exists_quasiIso_baseChange_stalkComplex`, a statement about complexes alone, and
the isomorphism is formed again at the model in hand.  The germ map in it is identified with
`Stacks.Duality.affineGermRingHom` by `Stacks.Duality.affineGermRingHom_eq_germ`.

## References

* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0GSU](https://stacks.math.columbia.edu/tag/0GSU)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- **The comparison
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.nonempty_q_baseChange_iso_derivedStalk`,
realized by a quasi-isomorphism of complexes.**
The bounded complex `M^• ⊗_A 𝒪_{X,x}` is K-projective, so an isomorphism in the derived category
out of it is the image of a chain map (`StacksDraft.Perfect.exists_quasiIso_of_iso_Q`).  Being a
quasi-isomorphism is a statement about the complexes alone, so the conclusion is available at
every model of the derived category of `𝒪_{X,x}`-modules, not only at the standard one. -/
theorem exists_quasiIso_baseChange_stalkComplex (C : AffineChart S) (x : S.X)
    (hx : x ∈ (C.U.1 : Set S.X)) (E : CochainComplex S.X.Modules ℤ)
    (hE : Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj E ≅ S.M)) :
    ∃ ψ : (C.complex.baseChange
          (S.X.presheaf.germ (C.U : S.X.Opens) x hx).hom).toCochainComplex ⟶
        ((Stacks.Duality.schemeStalkModuleFunctor x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E,
      QuasiIso ψ := by
  rw [← Stacks.Duality.affineGermRingHom_eq_germ C.U.2 x hx]
  obtain ⟨e⟩ := C.nonempty_q_baseChange_iso_derivedStalk x hx E hE
  exact @StacksDraft.Perfect.exists_quasiIso_of_iso_Q _ _ (HasDerivedCategory.standard _) _ _ e

end AffineChart

variable (S : ComplexAndDivisorSituation.{u, d}) (x : S.X)

variable [HasDerivedCategory.{d} (ModuleCat.{u} (ToType (S.X.presheaf.stalk x)))]

/-- The stalk functor at `x`, valued in modules over the local ring `𝒪_{X,x}`. -/
abbrev stalkFunctorAt :
    OXMod.{u, u} S.X.toRingedSpace ⥤ ModuleCat.{u} (ToType (S.X.presheaf.stalk x)) :=
  RingedSpace.moduleStalkOver S.X.toRingedSpace x
    (RingedSpace.ringCatStalkEquiv S.X.toRingedSpace x).symm

/-- The derived stalk at `x` of the perfect object of the situation. -/
abbrev derivedStalk : DerivedCategory (ModuleCat.{u} (ToType (S.X.presheaf.stalk x))) :=
  (stalkFunctorAt S x).mapDerivedCategory.obj S.M

/-- **The derived stalk of a perfect object is perfect.**  This is Tag 0657 for the derived
stalk, carried by `AlgebraicGeometry.RingedSpace.isPerfect_moduleStalkOver_of_isPerfect`. -/
theorem isPerfect_derivedStalk : StacksDraft.Perfect.IsPerfect (S.derivedStalk x) :=
  RingedSpace.isPerfect_moduleStalkOver_of_isPerfect (X := S.X.toRingedSpace) x
    (RingedSpace.ringCatStalkEquiv S.X.toRingedSpace x).symm
    (stalkFunctorAt S x) (Iso.refl _) S.M S.isPerfect

/-- **The derived stalk is represented by a bounded complex of finite free modules.**  It is a
perfect object of the derived category of the local ring `𝒪_{X,x}`, so it is represented by a
bounded complex of finite projective modules; over a local ring a finite projective module is
free, and chosen bases turn the complex into a `BoundedComplex`. -/
theorem exists_boundedComplex_derivedStalk :
    ∃ C : BoundedComplex (ToType (S.X.presheaf.stalk x)),
      Nonempty (DerivedCategory.Q.obj C.toCochainComplex ≅ S.derivedStalk x) :=
  StacksDraft.Perfect.exists_boundedComplex_iso_of_isPerfect _ (S.isPerfect_derivedStalk x)

/-- **The base change of a chart's complex along the germ map represents the derived stalk**, at
the model of the derived category of `𝒪_{X,x}`-modules the situation is read at.

`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.exists_quasiIso_baseChange_stalkComplex`
gives a quasi-isomorphism from the base-changed complex to the degreewise stalk of a complex
representing the object; a quasi-isomorphism becomes invertible in every model, and the
degreewise stalk computes the derived stalk because the stalk functor is exact. -/
theorem nonempty_q_baseChange_iso_derivedStalk (C₀ : AffineChart S)
    (hx : x ∈ (C₀.U : Set S.X)) :
    Nonempty (DerivedCategory.Q.obj
        (C₀.complex.baseChange (S.X.presheaf.germ C₀.U.1 x hx).hom).toCochainComplex ≅
      S.derivedStalk x) := by
  obtain ⟨E, hE, -⟩ := C₀.represents
  obtain ⟨ψ, hψ⟩ := C₀.exists_quasiIso_baseChange_stalkComplex x hx E hE
  have := hψ
  exact ⟨(@asIso _ _ _ _ (DerivedCategory.Q.map ψ)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ).2 hψ)) ≪≫
    ((stalkFunctorAt S x).mapDerivedCategoryFactors.app E).symm ≪≫
    (stalkFunctorAt S x).mapDerivedCategory.mapIso hE.some⟩

/-- **A finite free model of a good triple at a stalk.**  At every point `x` of a good triple
`(X, D, M)` there are a bounded complex `C` of finite free `𝒪_{X,x}`-modules and a generator `a`
of the stalk `ℐ_x` of the ideal sheaf of `D` such that `a` is a nonzerodivisor, every
determinantal ideal `I_i(C, a)` is principal, and `C` represents the derived stalk of `M`
at `x`.

Away from `D` the stalk ideal is the unit ideal, so `a = 1` generates it and every determinantal
ideal contains `1`; the complex comes from the perfectness of `M`.  At a point of `D` the chart
supplied by goodness is base changed along the germ map: the germ of its equation generates
`ℐ_x` and is a nonzerodivisor, and principality of the determinantal ideals is inherited by base
change (Tags 0F8T and 0GSU).  That the base-changed complex represents the derived stalk is
`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_q_baseChange_iso_derivedStalk`. -/
theorem exists_boundedComplex_generator_derivedStalk (hgood : S.IsGoodTriple) :
    ∃ (C : BoundedComplex (ToType (S.X.presheaf.stalk x))) (a : ToType (S.X.presheaf.stalk x)),
      IdealSheafData.stalk S.D x = Ideal.span {a} ∧
        a ∈ nonZeroDivisors (ToType (S.X.presheaf.stalk x)) ∧
        (∀ i : ℤ, (idealI C a i).IsPrincipal) ∧
        Nonempty (DerivedCategory.Q.obj C.toCochainComplex ≅ S.derivedStalk x) := by
  by_cases hx : x ∈ S.D.supportSet
  · obtain ⟨C₀, hxC₀, hprin⟩ := hgood x hx
    exact ⟨C₀.complex.baseChange (S.X.presheaf.germ C₀.U.1 x hxC₀).hom,
      (S.X.presheaf.germ C₀.U.1 x hxC₀).hom C₀.f,
      IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span hxC₀ C₀.divisor_ideal,
      (isRegular_germ C₀.U x hxC₀ C₀.regular).mem_nonZeroDivisors,
      fun i => C₀.isPrincipal_determinantalIdeal_baseChange _ i (hprin i),
      S.nonempty_q_baseChange_iso_derivedStalk x C₀ hxC₀⟩
  · obtain ⟨C, hC⟩ := S.exists_boundedComplex_derivedStalk x
    have htop : IdealSheafData.stalk S.D x = ⊤ :=
      (IdealSheafData.stalk_eq_top_iff_notMem_support S.D x).mpr hx
    refine ⟨C, 1, by rw [htop, Ideal.span_singleton_one], one_mem _, fun i => ?_, hC⟩
    have htop' : idealI C (1 : ToType (S.X.presheaf.stalk x)) i = ⊤ := by
      refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
      simpa using pow_rank_mem_idealI C (1 : ToType (S.X.presheaf.stalk x)) i
    exact ⟨1, htop'.trans Ideal.span_singleton_one.symm⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
