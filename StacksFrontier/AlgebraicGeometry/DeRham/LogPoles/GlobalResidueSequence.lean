module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.FormRestrictionStalk
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.SmoothDivisor
public import StacksFrontier.RingTheory.DeRham.LogPolesSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# The residue sequence of log poles for an arbitrary morphism and an effective Cartier divisor

Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an effective Cartier divisor,
recorded by its ideal sheaf `I`. Assume the de Rham complex of log poles is defined for
`Y ⊆ X` over `S` in the sense of [Stacks, Tag 0FMV],
`AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex`, whose two conditions are asserted at
the local ring `𝒪_{X, y}` of each point `y` of `Y` and for each local equation of `Y` there.
This file proves that then, at every point of the divisor and for every local equation `t`
there, the residue sequence of complexes

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`

is short exact. This is [Stacks, Tag 0FMW] for an arbitrary morphism of schemes and an arbitrary
effective Cartier divisor, read at the local rings of the divisor, assuming nothing beyond the
stalkwise condition of Tag 0FMV.

## Main results

* `AlgebraicGeometry.exists_germ_span_eq_ker_stalkMap`: an effective Cartier divisor has a local
  equation at every one of its points, so the quantification below is not empty.
* `AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex.exists_retraction_D`: the splitting
  condition of Tag 0FMV, read as a retraction of `g ↦ g · dt` on `Ω[𝒪_{X, y}⁄𝒪_{S, f y}]`.
* `AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex.isSMulRegular_exteriorPower`: the
  torsion-freeness condition of Tag 0FMV, read on `⋀^p Ω[𝒪_{X, y}⁄𝒪_{S, f y}]`.
* `AlgebraicGeometry.Scheme.Hom.quotientSpanGermEquivStalk`: the quotient of `𝒪_{X, y}` by a
  local equation is `𝒪_{Y, y}`, so the third term of the sequence below is the de Rham complex
  of the divisor.
* `AlgebraicGeometry.Scheme.Hom.shortExact_logShortComplex_stalk`: **Stacks Tag 0FMW** for an
  arbitrary morphism of schemes and an arbitrary effective Cartier divisor.

## Implementation notes

**How the affine principal case is used, and where the global retraction disappears.** The
affine case `Stacks.LogPoles.shortExact_logShortComplex` is stated for a ring map `A → R` and an
element `t ∈ R` cutting out the divisor, and it asks for two things *on `R` itself*: that
multiplication by `t` is injective on `⋀^p Ω[R⁄A]` for every `p`, and that `g ↦ g · dt` admits
an `R`-linear retraction. The second of those, the retraction `hsplit` of that statement, is a
global one, and the note on that declaration records why quantifying it over an affine cover
cannot work: local retractions of `g ↦ g · dt` do not assemble into one over an open.

Here the affine case is instantiated at `R = 𝒪_{X, y}` and `A = 𝒪_{S, f y}`, with `t` the germ
of a local equation, and at that `R` *both* of its conditions are exactly what Tag 0FMV asserts.
So no retraction over an open is needed and none is assumed: the two arguments of the affine
statement are discharged from `HasLogPolesDeRhamComplex` by
`HasLogPolesDeRhamComplex.isSMulRegular_exteriorPower` and
`HasLogPolesDeRhamComplex.exists_retraction_D`, and the divisor is principal where it is used —
at a local ring — while being only locally principal, as an effective Cartier divisor is, on `X`.

**The two transports.** Tag 0FMV states its conditions on the stalks of the sheaves `Ω_{X/S}`
and `Ω^p_{X/S}`, whereas the affine case reads them on `Ω[R⁄A]` and `⋀^p Ω[R⁄A]`. The
identifications are `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`,
which also carries the germ of `dt` to `d` of the germ of `t` by
`relativeDifferentialsStalkKaehlerEquiv_germ_d`, and its exterior power
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv`. Composing the
retraction with the inverse of the first, and transporting regularity along the inverse of the
second, is the whole of the two lemmas below;
`AlgebraicGeometry.Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth` runs the same two transports in
the opposite direction.

**The sheaf-level statement.** The sequence here is the residue sequence of complexes of
`𝒪_{S, f y}`-modules at a point of the divisor. The sequence of complexes of sheaves on `X` that
the source states is
`AlgebraicGeometry.Scheme.Hom.logResidueShortComplex_shortExact`
(`StacksFrontier/AlgebraicGeometry/DeRham/LogPoles/LogResidueSequence.lean`), on the sheaves
`AlgebraicGeometry.Scheme.Hom.logPolesForms` with the differential
`AlgebraicGeometry.Scheme.Hom.logD` and the residue `AlgebraicGeometry.Scheme.Hom.logRes`. The
paragraphs below record the route that was planned for that differential; the construction
that was carried out characterises `dφ` by the Leibniz rule `a · (dφ)(b) = a · d(φ b) - db ∧ φ(a)`
and glues its local solutions on charts of the ideal sheaf, without passing through stalks.

**What the differential would be defined by, and what of that is available.** The equation that
`ψ = dφ` has to satisfy, on an open where `ℐ` is generated by a nonzerodivisor `t`, is
`t · ψ(t) = t · d(φ t) − dt ∧ φ t`; the right-hand side is the Leibniz form
`Stacks.LogPoles.logLeibniz` of `φ`, which is `R`-bilinear on the ideal by
`Stacks.LogPoles.logLeibnizBilin` (`StacksFrontier/RingTheory/DeRham/LogPolesLeibniz.lean`) and so
mentions no equation; that bilinearity is the step at which `ℐ` being an *ideal* is used, through
`a · φ b = φ (a b) = b · φ a`. Over a ring, hence at each stalk, the equation has exactly one
solution and the solution again vanishes on the divisor —
`Stacks.LogPoles.existsUnique_smul_eq_leibniz` and
`Stacks.LogPoles.logPairMap_logPairD_mem_ker` — the divisibility behind existence being
`Stacks.LogPoles.wedgeLeft_D_mem_smul_top_of_mem_logSubmodule`, that `dt ∧ 𝒦^p ⊆ t · Ω^{p+1}`.
What is missing is only the passage from those stalkwise solutions to a *section* of
`SheafHom(ℐ, 𝒦^{p+1})` over an open, which is a local-global step and not an identity.

**The route for that passage, and the one thing it is waiting on.** The passage is a
factorization through a monomorphism, not a gluing. Write `Λ_p` for the morphism
`SheafHom(ℐ, 𝒦^p) ⟶ SheafHom(ℐ ⊗ ℐ, Ω^{p+1})` sending `φ` to `a ⊗ b ↦ a · d(φ b) − db ∧ φ a` —
well defined because that expression is `𝒪_X`-bilinear in `(a, b)`, which is
`Stacks.LogPoles.logLeibnizBilin` read on sections — and `μ_p` for the morphism
`SheafHom(ℐ, 𝒦^{p+1}) ⟶ SheafHom(ℐ ⊗ ℐ, Ω^{p+1})` sending `ψ` to `ψ ∘ (multiplication)`. Then
`Λ_p` factors through `μ_p`, because `μ_p` is a monomorphism and
`Λ_p ≫ cokernel.π μ_p = 0`; the factorization is the differential, and the vanishing is a
*stalkwise* condition, hence exactly the two lemmas named above. `μ_p` is `𝒪_X`-linear and so
within reach of the tensor-hom machinery already used for
`AlgebraicGeometry.Scheme.Hom.logPolesFormsInclusion`; `Λ_p` is only `f^{-1}𝒪_S`-linear in `φ`
(its defect is `dc ∧ (a · φ b)`), so both have to be read in `SheafOfModules (f^{-1}𝒪_S)` after
restriction of scalars, and `Λ_p` has to be built by hand as a section of a sheaf-hom — a
morphism of presheaves of modules on the slice site — since no `𝒪_X`-linear currying applies to
it.

**Both sectionwise inputs to the bilinearity of `Λ_p` are proved, in every degree.** An earlier
version of this paragraph said that the sectionwise Leibniz rule
`d (c • ω) = dc ∧ ω + c • dω` was absent for `p ≥ 1`; it is not. The Leibniz rule against a
scalar, for an *arbitrary* local section `ω` of `Ω^p`, is
`AlgebraicGeometry.SheafOfModules.d_smul`
(`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/LocalizedLeibniz.lean`), stated for an arbitrary
exterior-algebra package on `Ω` and an arbitrary
`AlgebraicGeometry.SheafOfModules.DeRhamDifferential`, hence available for `Ω^•_{X/S}` through
`AlgebraicGeometry.Scheme.Hom.deRhamAlgebras`. The anticommutation `d (dc ∧ ω) = − dc ∧ dω` is
`AlgebraicGeometry.SheafOfModules.d_formProduct_exactOne_left`
(`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/WedgeDifferentialLeft.lean`), the sheaf-level form of
the ring-level `KaehlerDifferential.deRhamDifferential_wedgeLeft_D`; it comes from the graded
Leibniz rule `AlgebraicGeometry.SheafOfModules.d_formProduct` with a closed left factor together
with the closedness `AlgebraicGeometry.SheafOfModules.d_exactOne_eq_zero` of an exact one-form.

Two things about how those two are stated. The degree transport `1 + p = p + 1` is carried in the
shape `AlgebraicGeometry.SheafOfModules.reindexForm`, so `dc ∧ ω` reads as
`reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω)`; and `d_smul` takes
`d ω` as an explicit argument with an equation naming it, because the terms of the complex are
restrictions of scalars and the `𝒪_X`-action by `c` is not found on `d.val.app U ω` by instance
resolution — instantiate it at `rfl`.

Its sectionwise value is assembled out of them:
`AlgebraicGeometry.SheafOfModules.logLeibnizFormBilin`
(`StacksFrontier/AlgebraicGeometry/DeRham/SheafLogLeibniz.lean`) is
`(a, b) ↦ a · d(ψ b) − d b ∧ ψ a` as an `𝒪_X(U)`-bilinear map, for an `𝒪_X(U)`-linear map `ψ`
from an ideal of the sections over `U` into `Ω^p(U)`. That is the sheaf-level counterpart of
`Stacks.LogPoles.logLeibnizBilin`, which is about the Kähler differentials of a *ring* and does
not imply it, `Ω^p(U)` being a section of a sheafification.

So what `Λ_p` is waiting on is only its own construction: running that bilinear map over the
objects of the slice site and checking naturality, which is what turns it into a section of
`SheafHom(ℐ ⊗ ℐ, Ω^{p+1})`, and then the stalkwise vanishing `Λ_p ≫ cokernel.π μ_p = 0`.

Once the differential and the residue exist as morphisms of sheaves, the short exactness needs no
new argument: it is degreewise by
`HomologicalComplex.shortExact_of_degreewise_shortExact` and then stalkwise by
`AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkwiseExactness.lean`), whose hypothesis at a
point of the divisor is `shortExact_logShortComplex_stalk` below. For a family of subsheaves of
the terms of a complex that the differentials preserve — which the log forms are *not*, being no
subsheaf of `Ω^•_{X/S}` — `SheafOfModules.Submodule.subcomplex`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SubmoduleSubcomplex.lean`) turns the sectionwise
stability statement into the subcomplex together with its degreewise monomorphic inclusion.

The other thing a sheaf-level reading needs — the identification of the stalk of
`AlgebraicGeometry.Scheme.Hom.logPolesForms` at `y` with the degree-`p` term
`Stacks.LogPoles.logFormsX` of the sequence below — is *not* absent, only unassembled: both of
its halves exist. On the sheaf side,
`AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkEquiv`
(`StacksFrontier/AlgebraicGeometry/DeRham/LogPoles/LogPolesFormsStalk.lean`) reads that stalk as a
module of linear maps between stalks, and
`AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkKerEquiv`
(`StacksFrontier/AlgebraicGeometry/DeRham/LogPoles/LogPolesFormsStalkKernel.lean`) refines it to
linear maps into the kernel of the stalk map. On the ring side,
`Stacks.LogPoles.homIdealEquivLogFormsR`
(`StacksFrontier/RingTheory/DeRham/LogPolesHom.lean`) identifies such a module of maps out of the
ideal with the log forms over `R`, and `Stacks.LogPoles.logFormsXKerEquiv` in that same file is
the kernel-side half it composes with. What is missing is only the **composite** of these, taken
at one point and one local equation — a bounded assembly of pieces that are all named, not two
lines but not an absence either. That composite is what would turn the statement proved here into
the stalkwise verification of a sheaf-level short exact sequence over that middle term, which is
the route `StacksFrontier/AlgebraicGeometry/DeRham/LogPoles/FormsSheaf.lean` was written for — once
the differential exists to make it a sequence of complexes.

**The third term.** The affine case spells the divisor's coordinate ring as the literal quotient
`R ⧸ (t)`. `AlgebraicGeometry.Scheme.Hom.quotientSpanGermEquivStalk` identifies it with
`𝒪_{Y, y}`, which is what makes the third term of the sequence the de Rham complex of the divisor
and not of an unrelated quotient.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the stalkwise condition
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0) and
  [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH), the two stalk
  identifications
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS), the local equation of an
  effective Cartier divisor
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeDifferentialStalkMap

universe u

namespace AlgebraicGeometry


/-- Composing `g ↦ g · v` with a linear map carrying `v` to `w` gives `g ↦ g · w`. -/
private theorem comp_toSpanSingleton_of_apply_eq {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) {v : M} {w : N} (hw : φ v = w) :
    φ ∘ₗ LinearMap.toSpanSingleton R M v = LinearMap.toSpanSingleton R N w :=
  LinearMap.ext fun a => by
    simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_smul, hw]

/-- **An effective Cartier divisor has a local equation at every one of its points**: a section
`t` of `𝒪_X` on a neighbourhood whose germ generates the ideal cut out in `𝒪_{X, y}`, that is
the kernel of `𝒪_{X, y} → 𝒪_{Y, y}`.

By the forward direction of [Stacks, Tag 01WS] the divisor is cut out on an affine open
neighbourhood by one section, and the stalk ideal is the image of the ideal of sections under the
germ map. -/
theorem exists_germ_span_eq_ker_stalkMap {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (y : I.subscheme) :
    ∃ (U : X.Opens) (hy : I.subschemeι y ∈ U) (t : Γ(X, U)),
      RingHom.ker (I.subschemeι.stalkMap y).hom =
        Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t} := by
  obtain ⟨V, hxV, g, _, hgen⟩ :=
    Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor I hI (I.subschemeι y)
  have hW : IsAffineOpen (I.subschemeι ⁻¹ᵁ (V : X.Opens)) := V.2.preimage I.subschemeι
  have hsurj : Function.Surjective
      (I.subschemeι.appLE (V : X.Opens) (I.subschemeι ⁻¹ᵁ (V : X.Opens)) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact Scheme.Hom.app_surjective _ (V : X.Opens) V.2
  refine ⟨(V : X.Opens), hxV, g, ?_⟩
  rw [Stacks.Flatness.ker_stalkMap_eq_map_germ I.subschemeι V.2 hW le_rfl hxV hxV hsurj,
    Scheme.Hom.appLE_eq_app, I.ker_subschemeι_app V, hgen, Ideal.map_span, Set.image_singleton]

namespace Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}

/-- **The splitting condition of Stacks Tag 0FMV, read on the Kähler differentials of the local
ring.** At a point `y` of the divisor and for a local equation `t` there, the map
`𝒪_{X, y} → Ω[𝒪_{X, y}⁄𝒪_{S, f y}]`, `g ↦ g · d(germ t)`, admits an `𝒪_{X, y}`-linear
retraction.

Tag 0FMV asserts this for the stalk of the sheaf `Ω_{X/S}` and the germ of `dt`; composing with
the inverse of
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, which carries that
germ to `d` of the germ of `t`, moves it onto `Ω[𝒪_{X, y}⁄𝒪_{S, f y}]`. -/
theorem HasLogPolesDeRhamComplex.exists_retraction_D (h : f.HasLogPolesDeRhamComplex I)
    (y : I.subscheme) (U : X.Opens) (hy : I.subschemeι y ∈ U) (t : Γ(X, U))
    (ht : RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t}) :
    letI : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) := algebraStalkMap f (I.subschemeι y)
    ∃ r : Ω[ToType (X.presheaf.stalk (I.subschemeι y))⁄
            ToType (S.presheaf.stalk (f (I.subschemeι y)))] →ₗ[
          ToType (X.presheaf.stalk (I.subschemeι y))]
          ToType (X.presheaf.stalk (I.subschemeι y)),
      r ∘ₗ LinearMap.toSpanSingleton _ _
          (KaehlerDifferential.D (ToType (S.presheaf.stalk (f (I.subschemeι y))))
            (ToType (X.presheaf.stalk (I.subschemeι y)))
            ((X.presheaf.germ U (I.subschemeι y) hy).hom t)) =
        LinearMap.id := by
  classical
  let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
      (ToType (X.presheaf.stalk (I.subschemeι y))) := algebraStalkMap f (I.subschemeι y)
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds (I.subschemeι y))) :=
    Classical.decEq _
  obtain ⟨r, hr⟩ :=
    HasLogPolesDeRhamComplex.exists_retraction_toSpanSingleton h y U hy t ht
  have hw : (relativeDifferentialsStalkKaehlerEquiv f (I.subschemeι y)).symm.toLinearMap
        (KaehlerDifferential.D (ToType (S.presheaf.stalk (f (I.subschemeι y))))
          (ToType (X.presheaf.stalk (I.subschemeι y)))
          ((X.presheaf.germ U (I.subschemeι y) hy).hom t)) =
      TopCat.Presheaf.germ (relativeDifferentials f).presheaf U (I.subschemeι y) hy
        ((universalRelativeDerivation f).d t) :=
    (LinearEquiv.symm_apply_eq _).mpr
      (relativeDifferentialsStalkKaehlerEquiv_germ_d f (I.subschemeι y)
        (OrderDual.toDual (⟨U, hy⟩ : TopologicalSpace.OpenNhds (I.subschemeι y))) t).symm
  have hcomp := comp_toSpanSingleton_of_apply_eq
    (relativeDifferentialsStalkKaehlerEquiv f (I.subschemeι y)).symm.toLinearMap hw
  exact ⟨r ∘ₗ (relativeDifferentialsStalkKaehlerEquiv f (I.subschemeι y)).symm.toLinearMap,
    (LinearMap.comp_assoc _ _ _).trans ((congrArg (fun g => r ∘ₗ g) hcomp).trans hr)⟩

/-- **The torsion-freeness condition of Stacks Tag 0FMV, read on the exterior powers of the
Kähler differentials of the local ring.** At a point `y` of the divisor and for a local equation
`t` there, multiplication by the germ of `t` is injective on
`⋀^p Ω[𝒪_{X, y}⁄𝒪_{S, f y}]` for every `p`.

Tag 0FMV asserts this for the stalk of the sheaf `Ω^p_{X/S}`, which
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialFormsStalkKaehlerEquiv` identifies with
that exterior power. -/
theorem HasLogPolesDeRhamComplex.isSMulRegular_exteriorPower (h : f.HasLogPolesDeRhamComplex I)
    (y : I.subscheme) (U : X.Opens) (hy : I.subschemeι y ∈ U) (t : Γ(X, U))
    (ht : RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t}) :
    letI : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) := algebraStalkMap f (I.subschemeι y)
    ∀ p : ℕ,
      IsSMulRegular (↥(⋀[ToType (X.presheaf.stalk (I.subschemeι y))]^p
          Ω[ToType (X.presheaf.stalk (I.subschemeι y))⁄
            ToType (S.presheaf.stalk (f (I.subschemeι y)))]))
        ((X.presheaf.germ U (I.subschemeι y) hy).hom t) := by
  classical
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds (I.subschemeι y))) :=
    Classical.decEq _
  intro p
  let := moduleStalkRelativeDifferentialForms f (I.subschemeι y) p
  exact IsSMulRegular.of_injective
    (relativeDifferentialFormsStalkKaehlerEquiv f (I.subschemeι y) p).symm.toLinearMap
    (relativeDifferentialFormsStalkKaehlerEquiv f (I.subschemeι y) p).symm.injective
    (HasLogPolesDeRhamComplex.isSMulRegular h y U hy t ht p)

/-- **The quotient of `𝒪_{X, y}` by a local equation of the divisor is `𝒪_{Y, y}`.** The stalk
map of the closed immersion is surjective and its kernel is generated by the germ of the
equation, so it factors through an isomorphism. -/
def quotientSpanGermEquivStalk (y : I.subscheme) (U : X.Opens) (hy : I.subschemeι y ∈ U)
    (t : Γ(X, U))
    (ht : RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t}) :
    (ToType (X.presheaf.stalk (I.subschemeι y)) ⧸
        Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t}) ≃+*
      ToType (I.subscheme.presheaf.stalk y) :=
  (Ideal.quotEquivOfEq ht.symm).trans
    (RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective y))

/-- **Stacks Project, Tag 0FMW.** Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an
effective Cartier divisor, recorded by its ideal sheaf `I`, with the de Rham complex of log poles
defined for `Y ⊆ X` over `S` in the sense of [Stacks, Tag 0FMV]. Then at every point `y` of `Y`
and for every local equation `t` of `Y` at `y` the residue sequence of complexes

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`

of `𝒪_{S, f y}`-modules, built from the germ of `t` over `R = 𝒪_{X, y}`, is short exact. The
three terms are the de Rham complex of `R`, the complex of log poles
`Stacks.LogPoles.logComplex` of the germ of `t`, and the shift of the de Rham complex of
`R ⧸ (germ t)`, which `AlgebraicGeometry.Scheme.Hom.quotientSpanGermEquivStalk` identifies with
`𝒪_{Y, y}`.

The divisor is only locally principal, and the equation `t` is a local one: both conditions the
affine case of Tag 0FMW asks on the ring are supplied at the local ring by Tag 0FMV, so nothing
is assumed about `g ↦ g · dt` on an open of `X`. Local equations exist at every point of an
effective Cartier divisor by `AlgebraicGeometry.exists_germ_span_eq_ker_stalkMap`.

The source states a short exact sequence of complexes of sheaves on `X`; the module docstring
records what would be needed to read this one as its stalkwise verification. Of the two pieces
only the first is genuinely absent: `AlgebraicGeometry.Scheme.Hom.logPolesForms` carries no
differential, so there is no sheaf-level complex. The identification of its stalk with
`Stacks.LogPoles.logFormsX` is unassembled rather than missing — its sheaf-side and ring-side
halves are `AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkEquiv`,
`AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkKerEquiv`,
`Stacks.LogPoles.homIdealEquivLogFormsR` and `Stacks.LogPoles.logFormsXKerEquiv`, and what is
owed is their composite. -/
@[stacks 0FMW "for an arbitrary morphism of schemes and an effective Cartier divisor whose log \
poles complex is defined in the sense of 0FMV, the short exactness of the residue sequence of \
complexes at each point of the divisor and each local equation there"]
theorem shortExact_logShortComplex_stalk (h : f.HasLogPolesDeRhamComplex I) (y : I.subscheme)
    (U : X.Opens) (hy : I.subschemeι y ∈ U) (t : Γ(X, U))
    (ht : RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U (I.subschemeι y) hy).hom t}) :
    letI : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (ToType (X.presheaf.stalk (I.subschemeι y))) := algebraStalkMap f (I.subschemeι y)
    (Stacks.LogPoles.logShortComplex
        (A := ToType (S.presheaf.stalk (f (I.subschemeι y))))
        (R := ToType (X.presheaf.stalk (I.subschemeι y)))
        (HasLogPolesDeRhamComplex.isSMulRegular_exteriorPower h y U hy t ht)
        (HasLogPolesDeRhamComplex.exists_retraction_D h y U hy t ht)).ShortExact := by
  let : Algebra (ToType (S.presheaf.stalk (f (I.subschemeι y))))
      (ToType (X.presheaf.stalk (I.subschemeι y))) := algebraStalkMap f (I.subschemeι y)
  exact Stacks.LogPoles.shortExact_logShortComplex
    (A := ToType (S.presheaf.stalk (f (I.subschemeι y))))
    (R := ToType (X.presheaf.stalk (I.subschemeι y))) _ _

end Scheme.Hom

end AlgebraicGeometry

end
