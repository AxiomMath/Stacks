module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExtZeroOfIsLE
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentActingGroup
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BoundedAboveKFlatResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The acting group of clause (2) of Stacks 08U8 at the *derived* pullback

Let `g : (X₂, 𝒪_{X₂}) ⟶ (X₁, 𝒪_{X₁})` and `f₁ : (X₁, 𝒪_{X₁}) ⟶ (S₁, 𝒪_{S₁})` be morphisms of
ringed spaces and let `𝒢₂` be an `𝒪_{X₂}`-module.  Clause (2) of **Stacks 08U8** writes the group
acting on the morphisms `X'₂ ⟶ X'₁` three ways,

`Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂) = Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)
  = Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`,

the third with the **derived** pullback `Lg^*` of **Stacks 06YJ**.  The first two groups, and the
third with the degreewise pullback in place of `Lg^*`, are identified in
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentActingGroup.lean`.  This file
identifies the third group as the source writes it, and so closes the display: the group
`Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)` is `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`, with no hypothesis
beyond the two morphisms.

Composed with the `Ext⁰` form of the source's own reduction step — which replaces
`𝖭𝖫_{𝒪_{X₁}/𝒪_{S₁}}` by `𝖭𝖫(α)` for a presentation `α`, and is
`Stacks.SheafOfModules.presentationNaiveCotangentExtZeroAddEquiv` — it gives the passage

`Ext⁰_{𝒪_{X₁}}(𝖭𝖫(α), g_*𝒢₂) = Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`

that the source's proof makes between its reduced situation and the group of its display.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentHomologyZeroIsoDifferentials`: `H⁰(𝖭𝖫_{B/A}) = Ω_{B/A}`
  read in the derived category, for sheaves of rings on a site.
* `AlgebraicGeometry.RingedSpaceThickening.homologyZeroNaiveCotangentIsoDifferentials`: the same
  at a morphism of ringed spaces, `H⁰(𝖭𝖫_{X₁/S₁}) = Ω_{X₁/S₁}`.

## Main results

* `Stacks.Cohomology.KFlatDerivedPullback.extZeroDerivedPullbackAddEquiv`: for a complex `K` of
  `𝒪_{X₁}`-modules living in cohomological degrees `≤ 0`,
  `Ext⁰_{𝒪_{X₂}}(Lg^*K, 𝒢₂) = Hom_{𝒪_{X₁}}(H⁰(K), g_*𝒢₂)`.
* `Stacks.Cohomology.KFlatDerivedPullback.extDerivedPullback_eq_zero_of_neg`: the groups
  `Ext^i_{𝒪_{X₂}}(Lg^*K, 𝒢₂)` vanish for `i < 0`.
* `AlgebraicGeometry.RingedSpaceThickening.extZeroDerivedPullbackNaiveCotangentAddEquiv`: the
  acting group of clause (2) of **Stacks 08U8** with the source's derived pullback,
  `Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂) = Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`.
* `AlgebraicGeometry.RingedSpaceThickening.presentationExtZeroDerivedPullbackAddEquiv`: the
  passage `Ext⁰_{𝒪_{X₁}}(𝖭𝖫(α), g_*𝒢₂) = Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`.

## Implementation notes

### What is proved, and with what hypotheses

Nothing is assumed beyond the two morphisms of ringed spaces and — for the statements about a
presentation — that `α` presents `𝒪_{X₁}` as a quotient of a polynomial algebra, which is the
source's own hypothesis on `α`.  In particular the flatness of the degree `0` term of
`𝖭𝖫_{X₁/S₁}` that the source's reduction step invokes is *not* needed here, and the comparison
`Lg^*𝖭𝖫_{X₁/S₁} ⟶ g^*𝖭𝖫_{X₁/S₁}` is not used: the route below computes `Ext⁰` out of the derived
pullback directly.  (That flatness is in any case a theorem of this library,
`Stacks.SheafOfModules.isFlat_ringedSpace_naiveCotangentComplex_X_zero`, not a hypothesis.)

What is *not* proved is the source's intermediate assertion that the canonical map
`Lg^*𝖭𝖫_{X₁/S₁} ⟶ g^{-1}𝖭𝖫_{X₁/S₁} ⊗_{g^{-1}𝒪_{X₁}} 𝒪_{X₂}` induces an isomorphism on
cohomology sheaves in degrees `0` *and* `-1`; only the consequence in degree `0`, which is what
clause (2) uses, is obtained, and it is obtained without that map.  The degree `-1` half belongs
to the `Ext¹` of clause (1).

### The route

`Ext⁰` out of an object of the derived category living in degrees `≤ 0` is `Hom` out of its
`H⁰` (**Stacks 06XS**, as `StacksDraft.ExtZero.extZeroAddEquiv`), so the whole statement is the
computation of `H⁰(Lg^*K)`.  A K-flat resolution computes `Lg^*`, and by **Stacks 05T7** the
resolution of a complex with no cohomology above `0` may be taken with no *terms* above `0`
(`Stacks.Cohomology.KFlatDerivedPullback.exists_boundedAbove_kFlatResolution`).  For such a
resolution `L` the derived pullback is the degreewise one, `Lg^*K = g^*L`, which again has no
terms above `0`, so its `H⁰` is the cokernel of `g^*(L^{-1} ⟶ L⁰)`.  The adjunction `g^* ⊣ g_*`
then moves a homomorphism out of that cokernel to a homomorphism out of `coker(L^{-1} ⟶ L⁰)` —
that is, out of `H⁰(L) = H⁰(K)` — with values in `g_*𝒢₂`; this step is
`CategoryTheory.Adjunction.cokernelHomAddEquiv`, which needs only the universal property of the
cokernel and the hom-set bijection, not that `g^*` preserve cokernels.

The resolution `L` is *chosen*, so the identification is not canonical, and the statement is
given in two forms: `nonempty_extZeroDerivedPullbackAddEquiv`, which is honest about that, and
`extZeroDerivedPullbackAddEquiv`, its `Nonempty.some`.  The source's argument makes the same
choice, in the words "`Lg^*` is the left derived functor of `g^*`".

### Spellings

`𝖭𝖫_{X₁/S₁}` is `AlgebraicGeometry.RingedSpace.naiveCotangentComplex f₁` and `Lg^*𝖭𝖫_{X₁/S₁}` is
`AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangent g f₁` of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedExt.lean`, with the same
ascription of the ambient category of modules that that file uses and for the same reason.
`Ω_{X₁/S₁}` is `AlgebraicGeometry.RingedSpaceThickening.relativeDifferentials f₁`, the object
that `actingGroupEquivPushforward` identifies the acting group with; `g_*` is the right adjoint
`RingedSpaceModuleAdjunction.modulePushforward g` of the `g^*` that `Lg^*` derives, rather than
the composite spelling `pushedModule` of `NaiveCotangentActingGroup.lean`, since it is the
latter's `g^*` whose derived functor is not in play here.

The identification `H⁰(𝖭𝖫_{B/A}) = Ω_{B/A}` is assembled once at a generic site, as
`canonicalConormalCokernelAdjEquiv` is and for the reason recorded there: at a concrete ringed
space the two spellings of `coker(conormal map of the canonical presentation)` do not join
within the heartbeat budget, while the same composite formed at the generic site costs nothing.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), `H⁰(NL) = Ω`
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), `NL(α)` and its
  comparison with `NL`
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ), the derived pullback
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS), `Ext` between complexes
  with disjoint homology ranges
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096), `g^* ⊣ g_*`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules (inverseImageBaseRingOnMiddle ringedSpaceStructureMap
  canonicalConormalSequence canonicalConormalCokernelIsoDifferentials naiveCotangentComplex)
open AlgebraicGeometry.SheafOfModules ( moduleOfDifferentialsOfSite)

universe v u w z t

/-! ## `Ext⁰` out of the derived pullback of a complex living in degrees `≤ 0` -/

namespace Stacks.Cohomology.KFlatDerivedPullback

attribute [local instance] HasDerivedCategory.standard

variable {X₁ X₂ : RingedSpace.{u, u}} (g : X₂ ⟶ X₁)
  (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X₁)) ℤ) [K.IsLE 0]

section ExtZero

/-- **`Ext⁰` out of the derived pullback of a complex living in degrees `≤ 0`.**  For a complex
`K` of `𝒪_{X₁}`-modules with no cohomology above degree `0`, an identification
`e : H⁰(K) ≅ W` and an `𝒪_{X₂}`-module `𝒢`,

`Ext⁰_{𝒪_{X₂}}(Lg^*K, 𝒢) = Hom_{𝒪_{X₁}}(W, g_*𝒢)`.

The derived pullback lives in degrees `≤ 0` as well, so an `Ext⁰`-class out of it is a
homomorphism out of its `H⁰`; a K-flat resolution `L` of `K` with no terms above degree `0`
computes that `H⁰` as `coker(g^*(L^{-1} ⟶ L⁰))`, and the adjunction `g^* ⊣ g_*` turns a
homomorphism out of it into one out of `coker(L^{-1} ⟶ L⁰) = H⁰(L) = H⁰(K)` with values in
`g_*𝒢`.

The resolution is chosen, so the identification is not canonical; see the implementation
notes. -/
theorem nonempty_extZeroDerivedPullbackAddEquiv
    {W : SheafOfModules.{u} (structureSheafRing X₁)}
    (e : (DerivedCategory.homologyFunctor _ 0).obj (DerivedCategory.Q.obj K) ≅ W)
    (G : SheafOfModules.{u} (structureSheafRing X₂)) :
    Nonempty (DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj K))
        ((DerivedCategory.singleFunctor _ 0).obj G) 0 ≃+
      (W ⟶ (modulePushforward g).obj G)) := by
  obtain ⟨L, l, hl, hLE, hKF⟩ := exists_boundedAbove_kFlatResolution X₁ 0 K
  have := hl
  have := hLE
  have : IsIso (DerivedCategory.Q.map l) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ l).2 hl
  have := isStrictlyLE_mapHomologicalComplex g 0 L
  have : ((derivedPullback g).obj (DerivedCategory.Q.obj K)).IsLE 0 :=
    isLE_derivedPullback_Q_obj g 0 K
  let eQ : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj K := asIso (DerivedCategory.Q.map l)
  let dpIso : (derivedPullback g).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    (derivedPullback g).mapIso eQ.symm ≪≫
      Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfKFlat g L hKF
  let ePulled := (DerivedCategory.homologyFunctor _ 0).mapIso dpIso ≪≫
    StacksDraft.ExtZero.derivedHomologyZeroIsoCokernel
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
      (CochainComplex.isZero_of_isStrictlyLE _ 0 1 (by omega))
  let eW : W ≅ cokernel (L.d (-1) 0) :=
    e.symm ≪≫ (DerivedCategory.homologyFunctor _ 0).mapIso eQ.symm ≪≫
      StacksDraft.ExtZero.derivedHomologyZeroIsoCokernel L
        (L.isZero_of_isStrictlyLE 0 1 (by omega))
  exact ⟨((StacksDraft.ExtZero.extZeroAddEquiv _ ePulled G).trans
    (Adjunction.cokernelHomAddEquiv (modulePullbackPushforwardAdjunction g)
      (L.d (-1) 0) G)).trans
    (StacksDraft.TwoTermExt.precompAddEquiv eW ((modulePushforward g).obj G))⟩

/-- **`Ext⁰_{𝒪_{X₂}}(Lg^*K, 𝒢) = Hom_{𝒪_{X₁}}(H⁰(K), g_*𝒢)`** for a complex `K` of
`𝒪_{X₁}`-modules living in cohomological degrees `≤ 0`.  This is
`nonempty_extZeroDerivedPullbackAddEquiv` with the choice of K-flat resolution made. -/
def extZeroDerivedPullbackAddEquiv
    {W : SheafOfModules.{u} (structureSheafRing X₁)}
    (e : (DerivedCategory.homologyFunctor _ 0).obj (DerivedCategory.Q.obj K) ≅ W)
    (G : SheafOfModules.{u} (structureSheafRing X₂)) :
    DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj K))
        ((DerivedCategory.singleFunctor _ 0).obj G) 0 ≃+
      (W ⟶ (modulePushforward g).obj G) :=
  (nonempty_extZeroDerivedPullbackAddEquiv g K e G).some

end ExtZero

/-- **`Ext^i_{𝒪_{X₂}}(Lg^*K, 𝒢)` vanishes for `i < 0`**, for a complex `K` of `𝒪_{X₁}`-modules
living in cohomological degrees `≤ 0`: so does `Lg^*K`, and `𝒢[0]` lives in degrees `≥ 0`. -/
theorem extDerivedPullback_eq_zero_of_neg
    (G : SheafOfModules.{u} (structureSheafRing X₂)) {i : ℤ} (hi : i < 0)
    (ξ : DerivedCategory.Ext ((derivedPullback g).obj (DerivedCategory.Q.obj K))
      ((DerivedCategory.singleFunctor _ 0).obj G) i) : ξ = 0 :=
  have : ((derivedPullback g).obj (DerivedCategory.Q.obj K)).IsLE 0 :=
    isLE_derivedPullback_Q_obj g 0 K
  StacksDraft.ExtZero.ext_eq_zero_of_neg _ G hi ξ

end Stacks.Cohomology.KFlatDerivedPullback

/-! ## `H⁰` of the naive cotangent complex, at a generic site -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  [HasDerivedCategory.{t}
    (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))]

/-- **`H⁰(𝖭𝖫_{B/A}) = Ω_{B/A}`, read in the derived category.**  The naive cotangent complex is
the two-term complex of the conormal map of the canonical presentation, so its `H⁰` is the
cokernel of that map, which is `Ω_{B/A}` by the degree `0` half of **Stacks 08TY**. -/
def naiveCotangentHomologyZeroIsoDifferentials :
    (DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) 0).obj
      (DerivedCategory.Q.obj (naiveCotangentComplex.{v, u, w, z} J A B a)) ≅
      moduleOfDifferentialsOfSite.{v, u, w, z} A B a :=
  StacksDraft.TwoTermExt.homologyZeroTwoTermIso.{max w u v z,
      max (w + 1) (u + 1) (v + 1) (z + 1), t}
      (canonicalConormalSequence.{v, u, w, z} J A B a).f ≪≫
    canonicalConormalCokernelIsoDifferentials.{v, u, w, z} J A B a

end Stacks.SheafOfModules

/-! ## The acting group of clause (2) of Stacks 08U8 with the derived pullback -/

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

variable {X₁ X₂ S₁ : RingedSpace.{u, u}} (g : X₂ ⟶ X₁) (f₁ : X₁ ⟶ S₁)
  (G : SheafOfModules.{u} (structureSheafRing X₂))

/-- `𝖭𝖫_{X₁/S₁}` has no terms outside degrees `-1` and `0`, so in particular none above
degree `0`: it is `HomologicalComplex.double` of the conormal map of the canonical
presentation. -/
instance isStrictlyLE_naiveCotangentComplex :
    CochainComplex.IsStrictlyLE
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing X₁)) ℤ from
        AlgebraicGeometry.RingedSpace.naiveCotangentComplex f₁) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact AlgebraicGeometry.RingedSpace.naiveCotangentComplex_isZero_X f₁ i (by omega) (by omega)

/-- **`H⁰(𝖭𝖫_{X₁/S₁}) = Ω_{X₁/S₁}`**, the degree `0` half of **Stacks 08TY** at a morphism of
ringed spaces, read in the derived category of `𝒪_{X₁}`-modules. -/
def homologyZeroNaiveCotangentIsoDifferentials :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X₁)) 0).obj
        ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X₁))).obj
          (show CochainComplex (SheafOfModules.{u} (structureSheafRing X₁)) ℤ from
            AlgebraicGeometry.RingedSpace.naiveCotangentComplex f₁)) ≅
      (show SheafOfModules.{u} (structureSheafRing X₁) from relativeDifferentials f₁) :=
  Stacks.SheafOfModules.naiveCotangentHomologyZeroIsoDifferentials.{u, u, u, u, u + 1}
    (Opens.grothendieckTopology X₁.carrier) (inverseImageBaseRingOnMiddle f₁) X₁.sheaf
    (ringedSpaceStructureMap f₁)

/-- **Stacks Project, Tag 08U8, clause (2): the acting group as the source writes it, with the
derived pullback.**  The group under which the morphisms `X'₂ ⟶ X'₁` fitting into the source's
diagram form a principal homogeneous space is

`Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂) = Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`,

the outer two groups of the source's display.  Nothing is assumed beyond the two morphisms of
ringed spaces: the flatness of the degree `0` term of `𝖭𝖫_{X₁/S₁}` that the source's reduction
step invokes is not needed, because `Ext⁰` out of `Lg^*𝖭𝖫_{X₁/S₁}` is computed here directly
rather than through the comparison with the degreewise pullback. -/
def extZeroDerivedPullbackNaiveCotangentAddEquiv :
    DerivedCategory.Ext (derivedPullbackNaiveCotangent g f₁)
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X₂)) 0).obj G)
        0 ≃+
      ((show SheafOfModules.{u} (structureSheafRing X₁) from relativeDifferentials f₁) ⟶
        (modulePushforward g).obj G) :=
  Stacks.Cohomology.KFlatDerivedPullback.extZeroDerivedPullbackAddEquiv g
    (show CochainComplex (SheafOfModules.{u} (structureSheafRing X₁)) ℤ from
      AlgebraicGeometry.RingedSpace.naiveCotangentComplex f₁)
    (homologyZeroNaiveCotangentIsoDifferentials f₁) G

/-- `Ext^i_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)` vanishes for `i < 0`: the naive cotangent complex lives
in cohomological degrees `≤ 0`, hence so does its derived pullback. -/
theorem extDerivedPullbackNaiveCotangent_eq_zero_of_neg {i : ℤ} (hi : i < 0)
    (ξ : DerivedCategory.Ext (derivedPullbackNaiveCotangent g f₁)
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X₂)) 0).obj G) i) :
    ξ = 0 :=
  Stacks.Cohomology.KFlatDerivedPullback.extDerivedPullback_eq_zero_of_neg g
    (show CochainComplex (SheafOfModules.{u} (structureSheafRing X₁)) ℤ from
      AlgebraicGeometry.RingedSpace.naiveCotangentComplex f₁) G hi ξ

/-! ### The passage from `𝖭𝖫(α)` to `Lg^*𝖭𝖫_{X₁/S₁}` -/

section Presentation

variable (E : Functor (Opens X₁.carrier)ᵒᵖ (Type u))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology X₁.carrier)
    X₁.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X₁.carrier)
    (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X₁.carrier)
      (inverseImageBaseRingOnMiddle f₁) X₁.sheaf (ringedSpaceStructureMap f₁) E α).hom]

/-- `Ext⁰_{𝒪_{X₁}}(𝖭𝖫(α), g_*𝒢₂) = Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`, the degree `0` half of
**Stacks 08TY** at the presentation `α`, with the ambient category of `𝒪_{X₁}`-modules written
in the spelling the derived pullback uses. -/
def presentationExtZeroAddEquivRelativeDifferentials :
    Stacks.SheafOfModules.presentationNaiveCotangentExt.{u, u, u, u, u + 1}
        (Opens.grothendieckTopology X₁.carrier) (inverseImageBaseRingOnMiddle f₁) X₁.sheaf
        (ringedSpaceStructureMap f₁) E α ((modulePushforward g).obj G) 0 ≃+
      ((show SheafOfModules.{u} (structureSheafRing X₁) from relativeDifferentials f₁) ⟶
        (modulePushforward g).obj G) :=
  Stacks.SheafOfModules.presentationNaiveCotangentExtZeroAddEquiv.{u, u, u, u, u + 1}
    (Opens.grothendieckTopology X₁.carrier) (inverseImageBaseRingOnMiddle f₁) X₁.sheaf
    (ringedSpaceStructureMap f₁) E α ((modulePushforward g).obj G)

/-- **Stacks Project, Tag 08U8: the passage from `𝖭𝖫(α)` to `Lg^*𝖭𝖫_{X₁/S₁}`.**  For a
presentation `α` of `𝒪_{X₁}` as a quotient of a polynomial algebra over `f₁⁻¹𝒪_{S₁}`,

`Ext⁰_{𝒪_{X₁}}(𝖭𝖫(α), g_*𝒢₂) = Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`.

Both sides are `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`: on the left because `𝖭𝖫(α)` lives in degrees
`≤ 0` with `H⁰(𝖭𝖫(α)) = Ω_{X₁/S₁}` (the source's **Stacks 08TY** and **Stacks 08TL**), on the
right by `extZeroDerivedPullbackNaiveCotangentAddEquiv`.  This is the identification the
source's proof makes between the group of its display and the group of its reduced situation;
the only hypothesis is that `α` is a presentation. -/
def presentationExtZeroDerivedPullbackAddEquiv :
    Stacks.SheafOfModules.presentationNaiveCotangentExt.{u, u, u, u, u + 1}
        (Opens.grothendieckTopology X₁.carrier) (inverseImageBaseRingOnMiddle f₁) X₁.sheaf
        (ringedSpaceStructureMap f₁) E α ((modulePushforward g).obj G) 0 ≃+
      DerivedCategory.Ext (derivedPullbackNaiveCotangent g f₁)
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X₂)) 0).obj G)
        0 :=
  (presentationExtZeroAddEquivRelativeDifferentials g f₁ G E α).trans
    (extZeroDerivedPullbackNaiveCotangentAddEquiv g f₁ G).symm

end Presentation

end AlgebraicGeometry.RingedSpaceThickening

end
