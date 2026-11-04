module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltration

/-!
# The cokernel of the exterior-power filtration of the Euler sequence

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree, write `X = ℙⁿ_R`,
`E = 𝒪_X(-1)^{⊕ (n+1)}` and `a = ⋀^{p+1}(eulerFirstArrow R n) : ⋀^{p+1} Ω_{X/R} ⟶ ⋀^{p+1} E`.
The exterior-power filtration induced by the Euler sequence is the sequence

`0 ⟶ ⋀^{p+1} Ω_{X/R} --a--> ⋀^{p+1} E ⟶ ⋀^p Ω_{X/R} ⟶ 0`,

and its third arrow is not given by a formula: the value of a morphism `⋀^{p+1} E ⟶ ⋀^p Ω_{X/R}`
on a wedge of local sections requires a splitting of the Euler sequence, which exists only
locally. The third term is therefore a *quotient*, and the sequence is the cokernel sequence of
`a`.

**This file provides the cokernel sequence and identifies its stalks.** Since `a` is a
monomorphism (`Stacks.AlgebraicGeometry.ProjEulerSequence.mono_exteriorPowerMap_eulerFirstArrow`)
the cokernel sequence of `a` is short exact, and short exactness is a stalkwise condition, so at
every point the stalk of `coker a` is the stalk of `⋀^{p+1} E` modulo the image of the stalk of
`a`. That image is cut out by the stalkwise projection
`Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkProj` onto `⋀^p(Ω_x)`, so the stalk of
the cokernel projection and that projection have the same kernel and are both surjective: the
stalk of `coker a` is `⋀^p(Ω_x)`, with the identification induced by either surjection.

The steps that would turn this into a short exact sequence ending in `⋀^p Ω_{X/R}` are the
morphism `coker a ⟶ ⋀^p Ω_{X/R}` or `⋀^p Ω_{X/R} ⟶ coker a` and the proof that it is an
isomorphism; the implementation notes record precisely which morphism is available and what is
missing.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_cokernelSequence`: the cokernel sequence
  of a monomorphism of sheaves of modules is short exact.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkMapL_cokernelπ_stalkMapL`,
  `Stacks.AlgebraicGeometry.ProjEulerSequence.surjective_stalkMapL_cokernelπ` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.exists_stalkMapL_eq_of_stalkMapL_cokernelπ_eq_zero`:
  **the stalk functor carries a cokernel to a cokernel** — at every point the stalk of the
  cokernel projection of a monomorphism is surjective with kernel the image of the stalk of the
  monomorphism.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_eulerWedgeCokernelSequence`: **the
  cokernel sequence `0 ⟶ ⋀^{p+1} Ω_{X/R} ⟶ ⋀^{p+1} E ⟶ coker ⟶ 0` of the exterior-power
  filtration of the Euler sequence is short exact**, for every `p`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkMapL_eulerWedgeCokernelπ_eq_zero_iff`: **the
  stalk of that cokernel projection has the same kernel as the stalkwise projection onto
  `⋀^p(Ω_x)`**, which with
  `Stacks.AlgebraicGeometry.ProjEulerSequence.surjective_eulerWedgeStalkProj` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.surjective_stalkMapL_eulerWedgeCokernelπ`
  identifies the stalk of the cokernel with `⋀^p(Ω_x)`.

## Implementation notes

**Why the global arrow is not here, stated as an obstruction.** Descending a morphism out of
`coker a` through the universal property needs a cofork, that is a morphism
`k : ⋀^{p+1} E ⟶ ⋀^p Ω_{X/R}` with `a ≫ k = 0`; that morphism *is* the arrow being constructed,
so the descent cannot be started in that direction. The available direction is the other one.
`⋀^p Ω_{X/R} ⊗ 𝒪_X` is the cokernel of `⋀^p Ω_{X/R} ⊗ Ω_{X/R} ⟶ ⋀^p Ω_{X/R} ⊗ E`, because the
tensor product of sheaves of modules is right exact — this is
`Stacks.SheafOfModules.TopWedge.relCokernelIsColimit` with `tensorLeftFunctor` in place of the
exterior presentation — and the morphism
`⋀^p Ω_{X/R} ⊗ E ⟶ ⋀^p Ω_{X/R} ⊗ ⋀^1 E ⟶ ⋀^{p+1} E ⟶ coker a`, built from the exterior generator
of `E` and `Stacks.SheafOfModules.TopWedge.wedgeHom`, kills that relation because
`f(ω) ∧ f(t) = ⋀^{p+1}f(ω ∧ t)` lies in the image of `a`. Descending it gives
`⋀^p Ω_{X/R} ⊗ 𝒪_X ⟶ coker a`, which is the wedge-and-lift formula of the source read in the
second factor. Proving that morphism an isomorphism stalkwise then needs the stalk of `wedgeHom`
to be the wedge multiplication of the exterior powers of the stalk — the multiplicative analogue
of `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap`, which exists only in the
degreewise form and would need the *ungraded* algebra comparison of Tag 01CH to be multiplicative
on homogeneous products. That is the missing lemma.

**The stalk of a cokernel.** No interchange of the stalk functor with cokernels is proved
directly: the cokernel sequence is short exact, short exactness is stalkwise
(`AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact`), and a short exact
sequence of modules is exactly the statement that the second arrow is surjective with kernel the
image of the first. So the three stalk statements below are read off that one equivalence rather
than off `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` and its colimit
counterpart.

**The vanishing of the composite of the two stalk maps** is the `zero` field of the mapped short
complex, applied to a germ by `congrArg`; it is not a separate computation. This is the pattern
of `Stacks.AlgebraicGeometry.ProjEulerSequence.prodEquivOfStalkSplitting_stalkMapL`, and it works
because the morphism part of the stalk functor and `PresheafOfModules.stalkMapL` are the same
function definitionally, which `AlgebraicGeometry.SheafOfModules.stalkMap_hom_eq_stalkMapL` is
needed for only where a rewrite is wanted.

**The sheaf of rings must be spelled `ringSheafOfComm`, that is as `sheafCompose` of the
forgetful functor.** `ShortComplex.map` needs `Functor.PreservesZeroMorphisms` of the stalk
functor, and at the `CategoryTheory.Sheaf.toRingCat` spelling of the same sheaf instance search
for it does not merely fail, it exhausts the typeclass heartbeat budget. This is the first hazard
recorded in `StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StalkSplitting`, met again here.

**Monomorphy is an explicit hypothesis, not an instance.** `Mono u` for a morphism of
`X.Modules` and `Mono u` for the same morphism read in
`SheafOfModules (ringSheafOfComm Osharp)` differ in their category argument, which is
definitionally but not syntactically the same, so the instance provided by
`mono_exteriorPowerMap_eulerFirstArrow` is not found by search for the general lemmas below. They
therefore take `Mono u` as an ordinary argument, where a definitional check suffices.

**The abelian structure needs two prerequisites.** Mathlib's `SheafOfModules.instAbelian` asks
for `HasSheafify` and `WEqualsLocallyBijective` for abelian-group-valued presheaves; on the site
of opens of a topological space both hold because that site is essentially small, and without
them registered `HasCokernel` is not found and the cokernel cannot even be written down. The two
local instances below are the ones
`StacksFrontier/AlgebraicGeometry/Meromorphic/IdealTimesModule.lean` uses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- Sheafification of abelian-group-valued presheaves exists on the site of opens of a
topological space, that site being essentially small. This is one of the two prerequisites of
Mathlib's abelian structure on sheaves of modules. -/
instance hasSheafify_opensGrothendieckTopology (Y : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the site of opens of a topological space the local weak equivalences of
abelian-group-valued presheaves are the locally bijective morphisms, that site being essentially
small. This is the other prerequisite of the abelian structure. -/
instance wEqualsLocallyBijective_opensGrothendieckTopology (Y : TopCat.{u}) :
    (Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-! ### The cokernel sequence of a monomorphism of sheaves of modules, and its stalks -/

section Cokernel

variable {X : TopCat.{u}} {Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M N : SheafOfModules.{u} (ringSheafOfComm Oc)} (u : M ⟶ N) (y : ↥X)

/-- **The cokernel sequence of a monomorphism of sheaves of modules is short exact.** The
category is abelian, so the cokernel projection is an epimorphism and the sequence is exact in
the middle. -/
theorem shortExact_cokernelSequence (hu : Mono u) :
    (ShortComplex.cokernelSequence u).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact u) hu inferInstance

/-- The complex of stalks of the cokernel sequence is a complex: the stalk of the cokernel
projection kills the image of the stalk of the monomorphism. -/
theorem stalkMapL_cokernelπ_stalkMapL
    (z : ↑(TopCat.Presheaf.stalk M.val.presheaf y)) :
    PresheafOfModules.stalkMapL y (Limits.cokernel.π u).val
        (PresheafOfModules.stalkMapL y u.val z) = 0 :=
  congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ z)
    ((ShortComplex.cokernelSequence u).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).zero

/-- The stalk functor carries the cokernel sequence of a monomorphism to a short exact sequence. -/
private theorem shortExact_map_stalkFunctor_cokernelSequence (hu : Mono u) :
    ((ShortComplex.cokernelSequence u).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).ShortExact :=
  (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact
    (ShortComplex.cokernelSequence u)).1 (shortExact_cokernelSequence u hu) y

/-- **The stalk of the cokernel projection of a monomorphism is surjective**, short exactness of
the cokernel sequence being a stalkwise condition. -/
theorem surjective_stalkMapL_cokernelπ (hu : Mono u) :
    Function.Surjective (PresheafOfModules.stalkMapL y (Limits.cokernel.π u).val) := by
  have h := shortExact_map_stalkFunctor_cokernelSequence u y hu
  intro q
  exact (h.moduleCat_surjective_g q).elim fun w hw => ⟨w, hw⟩

/-- **The stalk of the cokernel projection of a monomorphism has kernel the image of the stalk of
the monomorphism**, short exactness of the cokernel sequence being a stalkwise condition. -/
theorem exists_stalkMapL_eq_of_stalkMapL_cokernelπ_eq_zero (hu : Mono u)
    (w : ↑(TopCat.Presheaf.stalk N.val.presheaf y))
    (hw : PresheafOfModules.stalkMapL y (Limits.cokernel.π u).val w = 0) :
    ∃ z, PresheafOfModules.stalkMapL y u.val z = w := by
  have h := shortExact_map_stalkFunctor_cokernelSequence u y hu
  exact ((ShortComplex.moduleCat_exact_iff _).1 h.exact w hw).elim fun z hz => ⟨z, hz⟩

end Cokernel

/-! ### The cokernel of the exterior-power filtration of the Euler sequence -/

section Euler

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n p : ℕ)

/-- **The cokernel sequence of the exterior-power filtration of the Euler sequence is short
exact**: `0 ⟶ ⋀^{p+1} Ω_{X/R} ⟶ ⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)}) ⟶ coker ⟶ 0`. The first arrow is a
monomorphism by `mono_exteriorPowerMap_eulerFirstArrow`. -/
theorem shortExact_eulerWedgeCokernelSequence :
    (ShortComplex.cokernelSequence (Scheme.Modules.exteriorPowerMap
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
      ((p + 1 : ℕ) : ℤ))).ShortExact :=
  shortExact_cokernelSequence (Oc := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
      (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ))
    (mono_exteriorPowerMap_eulerFirstArrow R n (p + 1))

variable (x : ProjectiveSpectrum.top (polyGrading R n))

/-- **The stalk of the cokernel projection of the filtration is surjective.** -/
theorem surjective_stalkMapL_eulerWedgeCokernelπ :
    Function.Surjective (PresheafOfModules.stalkMapL x
      (Limits.cokernel.π (Scheme.Modules.exteriorPowerMap
        (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
        ((p + 1 : ℕ) : ℤ))).val) :=
  surjective_stalkMapL_cokernelπ
    (Oc := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
      (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)) x
    (mono_exteriorPowerMap_eulerFirstArrow R n (p + 1))

/-- **The stalk of the cokernel projection of the filtration has the same kernel as the stalkwise
projection onto `⋀^p(Ω_x)`.** Both kernels are the image of the stalk of `⋀^{p+1}` of the first
arrow of the Euler sequence: for the cokernel projection by stalkwise short exactness of the
cokernel sequence, for the stalkwise projection by
`exists_stalkMapL_eq_of_eulerWedgeStalkProj_eq_zero` and `eulerWedgeStalkProj_stalkMapL`.

With `surjective_eulerWedgeStalkProj` and `surjective_stalkMapL_eulerWedgeCokernelπ` this says
the stalk of `coker (⋀^{p+1} eulerFirstArrow)` at `x` is `⋀^p(Ω_x)`: two surjections out of the
stalk of `⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)})` with the same kernel. -/
theorem stalkMapL_eulerWedgeCokernelπ_eq_zero_iff
    (w : ↑(TopCat.Presheaf.stalk (Scheme.Modules.exteriorPower
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n)
      ((p + 1 : ℕ) : ℤ)).val.presheaf x)) :
    PresheafOfModules.stalkMapL x
          (Limits.cokernel.π (Scheme.Modules.exteriorPowerMap
            (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
            ((p + 1 : ℕ) : ℤ))).val w = 0
      ↔ eulerWedgeStalkProj R n p x w = 0 := by
  constructor
  · intro hw
    obtain ⟨z, rfl⟩ := exists_stalkMapL_eq_of_stalkMapL_cokernelπ_eq_zero
      (Oc := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
      (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)) x
      (mono_exteriorPowerMap_eulerFirstArrow R n (p + 1)) w hw
    exact eulerWedgeStalkProj_stalkMapL R n p x z
  · intro hw
    obtain ⟨z, rfl⟩ := exists_stalkMapL_eq_of_eulerWedgeStalkProj_eq_zero R n p x w hw
    exact stalkMapL_cokernelπ_stalkMapL
      (Oc := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
      (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)) x z

end Euler

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
