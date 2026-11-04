module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.SupportedTensorPushforward

/-!
# The multiplication of Tag 0G75 wedged into the forms of Tag 0G88

[Stacks, Tag 0G88] pairs the Gysin class of a closed immersion with a differential form through
the map of sheaves

`i^{-1}Ω^p_{X/S} ⊗ ℋ^c_Z(Ω^c_{X/S}) ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`,

the multiplication of [Stacks, Tag 0G75] read in degree `c` and then wedged. Read on `X` — the
side of the closed subset on which this library's local cohomology sheaves live, so that
`ℋ^c_Z` is `Stacks.Perfect.SupportedFraction.supportCohomologySheaf` — it is

`Ω^p_{X/S} ⊗_{𝒪_X} i_*ℋ^c_Z(Ω^c_{X/S}) ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`,

and that map is `Stacks.Gysin.gysinWedgeTopDegreeMap` below. It exists at exactly the generality
of [Stacks, Tag 0G86], where `Z` is only *locally* cut out by `c` equations: no flatness, no
K-flatness, no truncation hypothesis and no global equations.

The two halves of the construction are both already available and this file only joins them.

* The degree-`c` read-off of the multiplication, with an ordinary multiplication of sheaves put
  on the end, is `Stacks.Cohomology.SupportedComplexes.supportedTopDegreeMulMap`. It takes the
  multiplication as an arbitrary morphism `w : A ⊗_{𝒪_X} ℱ ⟶ G`, because nothing about the de
  Rham complex enters the read-off.
* The multiplication to put there is the wedge product of the de Rham algebra. The sheaf
  `Ω^n_{X/S}` is by definition the degree-`n` piece of
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra`, a
  `SheafOfModules.GradedAlgebra`, and the wedge `Ω^p ⊗ Ω^c ⟶ Ω^{p+c}` is that algebra's
  multiplication in degrees `p` and `c`: `SheafOfModules.GradedAlgebra.mulSheaf`.

## Main definitions

* `Stacks.Gysin.gysinWedgeTopDegreeMap`: **the map of [Stacks, Tag 0G88] in the generality of
  [Stacks, Tag 0G86]**, `Ω^p ⊗_{𝒪_X} ℋ^c_Z(Ω^c) ⟶ ℋ^c_Z(Ω^{p+c})`.

## Main results

* `Stacks.Gysin.gysinWedgeTopDegreeMap_eq`: it is `supportedTopDegreeMulMap` at the wedge of the
  de Rham algebra, so it carries no information beyond the multiplication of [Stacks, Tag 0G75]
  and that wedge.

## Implementation notes

**Which wedge.** The wedge wanted here has an honest tensor product of two sheaves of forms as
its source. `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` is *not* it: that is right
multiplication by the fixed global form `df₁ ∧ ⋯ ∧ df_c` of a chosen family of equations,
`Ω^p ⟶ Ω^{p+c}`, which presupposes global equations and so is unavailable at Tag 0G86's
generality. The multiplication of a `SheafOfModules.GradedAlgebra` is given on local sections,
as a `SheafOfModules.BilinearMap`; `mulSheaf` is the morphism out of the tensor product *sheaf*
that it descends to, so the sheafification step between a bilinear map and a map out of the
tensor product is already done there and is not redone here.

**Quasi-coherence.** `supportedTopDegreeMulMap` needs its middle argument quasi-coherent, which
`Ω^c_{X/S}` is in every degree and for every morphism of schemes
(`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`, the per-degree form of
[Stacks, Tag 01CL]). It is a theorem rather than an instance, so it is supplied by `haveI`. The
degrees `p` and `c` of the two factors need nothing: `A` and `G` are arbitrary.

**What this does not do.** [Stacks, Tag 0G88] is not registered on this map, and should not be.
The source's proof reduces the tag to the commutativity of a square whose right-hand column is
this map, and then leaves the verification out — "reduced to an omitted computation with the
maps `γ^j`". In this library that omitted step is the identification, over an open on which
`f₁, …, f_c` cut out `Z`, of this map with `Stacks.Perfect.CechPairing.supportPair`, the
Čech-model pairing in which the already-proved global-equations case of the tag lives. No such
comparison exists here.

The handle for it is now in place, and the state of the rest is recorded in the module doc of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/SupportedTensorPushforward.lean`. The two halves of
the handle are
`Stacks.Cohomology.SupportedComplexes.eq_supportedTensorPushMap` — the multiplication of
[Stacks, Tag 0G75] on `X` is the *only* morphism with its counit, so a candidate has to be
checked against the counit and against nothing else — and
`Stacks.Cohomology.SupportedComplexes.cechToDerivedSupport_comp_counit`, which computes that
counit through the Čech model. In particular the obstruction recorded on an earlier round, that
`Stacks.Perfect.SupportedFraction.supportedFractionSource` is not epi on sections, is not where
the comparison is blocked: the identification can be made at the level of complexes, before any
degree-`c` cohomology sheaf is taken, and there no fraction class occurs.

## References

* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G75](https://stacks.math.columbia.edu/tag/0G75)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open Stacks.Cohomology.SupportedComplexes

universe u

-- As in `SupportedTensorPushforward.lean`: the standard model of the derived category is given a
-- priority that beats the locally small model arriving as a global instance through the imports,
-- because the read-off and `supportCohomologySheaf` are both elaborated at the standard model.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace Stacks.Gysin

variable {X S : Scheme.{u}} (π : X ⟶ S) (T : Set X) (hT : IsClosed T) (c : ℕ)
variable (hcut : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ f : Fin c → Γ(U.toScheme, ⊤),
  U.ι ⁻¹' T = Stacks.Perfect.CechDerivedSupport.equationsClosedSet f)

include hcut in
/-- **The map of [Stacks, Tag 0G88], at the generality of [Stacks, Tag 0G86].** For a morphism
`π : X ⟶ S` of schemes and a closed subset `T ⊆ X` that is only *locally* cut out by `c`
equations,

`Ω^p_{X/S} ⊗_{𝒪_X} ℋ^c_T(Ω^c_{X/S}) ⟶ ℋ^c_T(Ω^{p+c}_{X/S})`,

both local cohomology sheaves being
`Stacks.Perfect.SupportedFraction.supportCohomologySheaf`, that is `i_*ℋ^c_T` — the spelling the
Čech-model pairing and the Gysin class map of [Stacks, Tag 0G7Q] use.

This is the degree-`c` read-off of the multiplication of [Stacks, Tag 0G75],
`Stacks.Cohomology.SupportedComplexes.supportedTopDegreeMulMap`, with the wedge product of the
de Rham algebra as its multiplication. No flatness, no K-flatness, no truncation hypothesis and
no global equations are assumed: the read-off is unconditional at Tag 0G86's own hypothesis
`hcut`, and the wedge is the multiplication `SheafOfModules.GradedAlgebra.mulSheaf` of
`relativeDifferentialFormsAlgebra π` in degrees `p` and `c`, which is unconditional too. -/
def gysinWedgeTopDegreeMap (p : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
          (relativeDifferentialForms π p)).obj
        (Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT
          (relativeDifferentialForms π (c : ℤ)) (c : ℤ)) ⟶
      Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT
        (relativeDifferentialForms π (p + (c : ℤ))) (c : ℤ) :=
  haveI := AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms π c
  supportedTopDegreeMulMap T hT c hcut (relativeDifferentialForms π (c : ℤ))
    (relativeDifferentialForms π p) (relativeDifferentialForms π (p + (c : ℤ)))
    (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) p (c : ℤ))

include hcut in
/-- The map of [Stacks, Tag 0G88] is the degree-`c` read-off of the multiplication of
[Stacks, Tag 0G75] at the wedge of the de Rham algebra, so it carries no information beyond
those two. -/
theorem gysinWedgeTopDegreeMap_eq (p : ℤ) :
    gysinWedgeTopDegreeMap π T hT c hcut p =
      haveI := AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms π c
      supportedTopDegreeMulMap T hT c hcut (relativeDifferentialForms π (c : ℤ))
        (relativeDifferentialForms π p) (relativeDifferentialForms π (p + (c : ℤ)))
        (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) p (c : ℤ)) :=
  rfl

end Stacks.Gysin

end
