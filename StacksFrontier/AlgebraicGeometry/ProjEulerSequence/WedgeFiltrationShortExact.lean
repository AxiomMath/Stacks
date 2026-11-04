module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationArrow
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exterior-power filtration of the Euler sequence is short exact

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = ℙⁿ_R`,
`E = 𝒪_X(-1)^{⊕ (n+1)}` and `Ω = Ω_{X/R}`. The Euler sequence exhibits `Ω` as a subsheaf of `E`
with invertible quotient, and the induced two-step filtration of the degree-`p+1` exterior power
ought to be a short exact sequence

`0 ⟶ ⋀^{p+1} Ω --a--> ⋀^{p+1} E --b--> ⋀^p Ω ⟶ 0`

whose first arrow is `⋀^{p+1}` of the first arrow of the Euler sequence.
`StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltration` proves the sequence at every
stalk, where it splits, and
`StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationArrow` computes the stalk of the
Koszul contraction `ι_g : ⋀^{p+1} E ⟶ ⋀^p E` against the second arrow `g` of the Euler sequence:
at every point the value of `ι_g` is the image, under `⋀^p` of the first arrow, of the stalkwise
projection of the filtration.

**This file constructs the global quotient arrow `b` and proves the sequence short exact.** The
arrow is obtained by factoring `ι_g` through the monomorphism `a' : ⋀^p Ω ⟶ ⋀^p E`. Sheaves of
modules form an abelian category, so `a'` is the kernel of its cokernel projection, and the
stalkwise statement just quoted says exactly that `ι_g` is killed by that projection — vanishing
of a morphism of sheaves being a stalkwise condition. The factorization `b` then has stalk the
stalkwise projection of the filtration, because `a'` is injective on every stalk, and the three
remaining clauses are the stalk statements already proved in `WedgeFiltration`: the complex
condition from `eulerWedgeStalkProj_stalkMapL`, exactness in the middle from
`exists_stalkMapL_eq_of_eulerWedgeStalkProj_eq_zero`, epimorphy from
`surjective_eulerWedgeStalkProj`. Monomorphy of the first arrow is
`mono_exteriorPowerMap_eulerFirstArrow`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.factorThruMono`: the factorization of a morphism of
  sheaves of modules through a monomorphism whose stalk maps have the same image.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeQuotient`: **the quotient arrow**
  `b : ⋀^{p+1} E ⟶ ⋀^p Ω` of the exterior-power filtration of the Euler sequence.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkMapL_comp` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.eq_zero_of_stalkMapL_eq_zero`: the stalk map of a
  composite is the composite of the stalk maps, and **a morphism of sheaves of modules all of
  whose stalk maps vanish is zero.**
* `Stacks.AlgebraicGeometry.ProjEulerSequence.comp_cokernelπ_eq_zero` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.factorThruMono_comp`: a morphism whose stalk maps
  take values in the images of the stalk maps of a monomorphism is killed by its cokernel
  projection, and therefore factors through it.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkMapL_factorThruMono`: **the stalk map of the
  factorization**, pinned by injectivity of the stalk map of the monomorphism.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkEquivSelf_stalkMapL_exteriorPowerMap`:
  the stalk of `⋀^p` of the first arrow of the Euler sequence is `⋀^p` of its stalk.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeQuotient_comp_exteriorPowerMap` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.projFormsStalkEquiv_stalkMapL_eulerWedgeQuotient`:
  **the two properties that pin the quotient arrow down** — followed by `⋀^p` of the first arrow
  of the Euler sequence it is the Koszul contraction, and its stalk is the stalkwise projection
  of the filtration.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.exteriorPowerMap_comp_eulerWedgeQuotient`,
  `Stacks.AlgebraicGeometry.ProjEulerSequence.epi_eulerWedgeQuotient` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.exact_eulerWedgeFiltration`: the three clauses of
  short exactness besides monomorphy of the first arrow.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_eulerWedgeFiltration`: **the
  exterior-power filtration of the Euler sequence of `ℙⁿ_R` is a short exact sequence**
  `0 ⟶ ⋀^{p+1} Ω_{X/R} ⟶ ⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)}) ⟶ ⋀^p Ω_{X/R} ⟶ 0`, for every `p`.

## Implementation notes

**The arrow is a factorization, not a descent.** Descending a morphism out of a cokernel needs a
cofork, that is the arrow being constructed, so the universal property cannot be used in that
direction; this is the obstruction recorded in
`StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal`. The available direction
is to factor the Koszul contraction *into* `⋀^p Ω_{X/R}` through the monomorphism
`⋀^p Ω_{X/R} ⟶ ⋀^p(𝒪_X(-1)^{⊕ (n+1)})`, which needs no cofork and no tensor product. The
abelian-category input is `CategoryTheory.Abelian.monoLift`; the route through
`⋀^p Ω_{X/R} ⊗ 𝒪_X` that `WedgeFiltrationGlobal` describes, and the stalk of `wedgeHom` it would
have needed, are not used.

**Vanishing of a morphism is checked with `TopCat.Presheaf.section_ext`.** No interchange of the
stalk functor with kernels or cokernels is needed: a section of a sheaf all of whose germs vanish
is zero, and the germ of the image of a section is the stalk map of its germ, so
`eq_zero_of_stalkMapL_eq_zero` follows from the sheaf condition on the target alone.

**Monomorphy is an explicit argument and the sheaf of rings is spelled `ringSheafOfComm`.** Both
are the hazards recorded in `WedgeFiltrationGlobal`: `Mono u` for a morphism of `X.Modules` and
for the same morphism read in `SheafOfModules (ringSheafOfComm 𝒪)` differ in their category
argument, so it is taken as an ordinary argument, and `ShortComplex.map` finds
`Functor.PreservesZeroMorphisms` of the stalk functor only at the `sheafCompose` spelling. The
sheaf of commutative rings is supplied as `(Oc := …)` throughout, recovering it from that
spelling being a unification problem under a projection.

**`rw` may not be used on a goal whose morphisms mix the two spellings.** The quotient arrow is
produced by a general construction stated over `ringSheafOfComm 𝒪`, while the first arrow of the
sequence is `AlgebraicGeometry.Scheme.Modules.exteriorPowerMap`, stated over the structure sheaf
of the scheme; elaboration accepts the mixture by definitional unfolding, but `rw` re-checks
type-correctness of its target at `implicit` transparency, where the `HasSheafCompose` proof
terms carried by the two spellings do not match, and fails. The stalkwise criteria for epimorphy
and exactness are therefore applied as terms, through the `.2` of the equivalence, rather than
with `rw`.

**No `@[stacks]` attribute.** The sequence proved here is not an assertion of a Stacks tag: Tag
01CJ is the exterior-power presentation of a short exact sequence, of which this is the special
case of an invertible quotient, and Tag 062K is the definition of the Koszul complex. Choosing a
covering set is a judgement for the integrator.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! #### Composites and vanishing of stalk maps -/

section Stalkwise

variable {X : TopCat.{u}} {Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (ringSheafOfComm Oc)}

/-- **The stalk map of a composite is the composite of the stalk maps**, read on an element of
the stalk. Every element of a stalk is a germ, where both sides are the germ of the image of a
section under the composite. -/
theorem stalkMapL_comp (y : ↥X) (v : F ⟶ G) (w : G ⟶ H)
    (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y)) :
    PresheafOfModules.stalkMapL y (v ≫ w).val z =
      PresheafOfModules.stalkMapL y w.val (PresheafOfModules.stalkMapL y v.val z) := by
  refine (TopCat.Presheaf.exists_germ_eq F.val.presheaf z).elim fun U h1 => h1.elim fun hU h2 =>
    h2.elim fun s hs => ?_
  subst hs
  refine Eq.trans (PresheafOfModules.stalkMapL_germ y (v ≫ w).val U hU s) ?_
  refine Eq.trans (PresheafOfModules.stalkMapL_germ y w.val U hU (v.val.app (op U) s)).symm ?_
  exact congrArg (PresheafOfModules.stalkMapL y w.val)
    (PresheafOfModules.stalkMapL_germ y v.val U hU s).symm

/-- **A morphism of sheaves of modules all of whose stalk maps vanish is zero.** A section of a
sheaf all of whose germs vanish is zero, and the germ of the image of a section is the stalk map
of its germ. -/
theorem eq_zero_of_stalkMapL_eq_zero (v : F ⟶ G)
    (hv : ∀ (y : ↥X) (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y)),
      PresheafOfModules.stalkMapL y v.val z = 0) : v = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  have hsec : v.val.app V s = 0 :=
    TopCat.Presheaf.section_ext
      ((AlgebraicGeometry.SheafOfModules.toTopSheaf (ringSheafOfComm Oc)).obj G) V.unop
      (v.val.app V s) 0 fun y hy =>
        Eq.trans (PresheafOfModules.stalkMapL_germ y v.val V.unop hy s).symm
          (Eq.trans (hv y _) (map_zero _).symm)
  exact hsec

end Stalkwise

/-! #### Factoring a morphism through a monomorphism -/

section Factor

variable {X : TopCat.{u}} {Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (ringSheafOfComm Oc)}

/-- A morphism whose stalk maps take values in the images of the stalk maps of `u` is killed by
the cokernel projection of `u`: vanishing is stalkwise, and the stalk of the cokernel projection
kills the image of the stalk of `u`. -/
theorem comp_cokernelπ_eq_zero (u : H ⟶ G) (v : F ⟶ G)
    (hv : ∀ (y : ↥X) (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y)),
      ∃ q, PresheafOfModules.stalkMapL y u.val q = PresheafOfModules.stalkMapL y v.val z) :
    v ≫ Limits.cokernel.π u = 0 := by
  refine eq_zero_of_stalkMapL_eq_zero _ fun y z => ?_
  refine Eq.trans (stalkMapL_comp y v (Limits.cokernel.π u) z) ?_
  refine (hv y z).elim fun q hq => ?_
  refine Eq.trans (congrArg (PresheafOfModules.stalkMapL y (Limits.cokernel.π u).val) hq.symm) ?_
  exact stalkMapL_cokernelπ_stalkMapL u y q

/-- **A morphism factors through a monomorphism with the same stalkwise image.** Sheaves of
modules form an abelian category, so a monomorphism is the kernel of its cokernel projection, and
the morphism is killed by that projection. -/
def factorThruMono (u : H ⟶ G) (hu : Mono u) (v : F ⟶ G)
    (hv : ∀ (y : ↥X) (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y)),
      ∃ q, PresheafOfModules.stalkMapL y u.val q = PresheafOfModules.stalkMapL y v.val z) :
    F ⟶ H :=
  haveI := hu
  Abelian.monoLift u v (comp_cokernelπ_eq_zero u v hv)

/-- The defining property of `factorThruMono`. -/
theorem factorThruMono_comp (u : H ⟶ G) (hu : Mono u) (v : F ⟶ G)
    (hv : ∀ (y : ↥X) (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y)),
      ∃ q, PresheafOfModules.stalkMapL y u.val q = PresheafOfModules.stalkMapL y v.val z) :
    factorThruMono u hu v hv ≫ u = v :=
  have := hu
  Abelian.monoLift_comp u v (comp_cokernelπ_eq_zero u v hv)

/-- **The stalk map of the factorization**, pinned by the stalk map of the monomorphism, which is
injective. -/
theorem stalkMapL_factorThruMono (u : H ⟶ G) (hu : Mono u) (v : F ⟶ G)
    (hv : ∀ (y : ↥X) (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y)),
      ∃ q, PresheafOfModules.stalkMapL y u.val q = PresheafOfModules.stalkMapL y v.val z)
    (y : ↥X) (z : ↑(TopCat.Presheaf.stalk F.val.presheaf y))
    (q : ↑(TopCat.Presheaf.stalk H.val.presheaf y))
    (hq : PresheafOfModules.stalkMapL y u.val q = PresheafOfModules.stalkMapL y v.val z) :
    PresheafOfModules.stalkMapL y (factorThruMono u hu v hv).val z = q := by
  have hmono := (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap u).1 hu y
  have hinj : Function.Injective (PresheafOfModules.stalkMapL y u.val) := fun a b hab =>
    hmono (((SheafOfModules.stalkMap_hom_eq_stalkMapL y u a).trans hab).trans
      (SheafOfModules.stalkMap_hom_eq_stalkMapL y u b).symm)
  refine hinj (Eq.trans ?_ hq.symm)
  refine Eq.trans (stalkMapL_comp y (factorThruMono u hu v hv) u z).symm ?_
  exact congrArg (fun φ : F ⟶ G => PresheafOfModules.stalkMapL y φ.val z)
    (factorThruMono_comp u hu v hv)

end Factor

/-! ### The quotient arrow of the filtration, and short exactness -/

section Euler

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The stalk of `⋀^p` of the first arrow of the Euler sequence is `⋀^p` of its stalk**, read
through the comparison isomorphisms of Tag 01CH on both sides. This is
`SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap` for the first arrow. -/
theorem eulerWedgeStalkEquivSelf_stalkMapL_exteriorPowerMap (p : ℕ)
    (x : ProjectiveSpectrum.top (polyGrading R n))
    (z : projWedgeGerm R n x ((p : ℕ) : ℤ)) :
    eulerWedgeStalkEquivSelf R n p x
        (PresheafOfModules.stalkMapL x (Scheme.Modules.exteriorPowerMap
          (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
          ((p : ℕ) : ℤ)).val z) =
      exteriorPower.map p (PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val)
        (projFormsStalkEquiv R n p x z) :=
  SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (projDifferentials R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (projDifferentials R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n))
    (eulerFirstArrow R n) p x z

/-- **The value of the Koszul contraction at a stalk is the value of `⋀^p` of the first arrow of
the Euler sequence at the stalkwise projection of the filtration.** This is the stalkwise
factorization that the global factorization is read off. -/
theorem stalkMapL_exteriorPowerMap_projFormsStalkEquiv_symm (p : ℕ)
    (x : ProjectiveSpectrum.top (polyGrading R n))
    (w : eulerWedgeGerm R n x ((p + 1 : ℕ) : ℤ)) :
    PresheafOfModules.stalkMapL x (Scheme.Modules.exteriorPowerMap
          (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
          ((p : ℕ) : ℤ)).val
        ((projFormsStalkEquiv R n p x).symm (eulerWedgeStalkProj R n p x w)) =
      PresheafOfModules.stalkMapL x (eulerWedgeContraction R n p).val w := by
  refine (eulerWedgeStalkEquivSelf R n p x).injective ?_
  refine Eq.trans (eulerWedgeStalkEquivSelf_stalkMapL_exteriorPowerMap R n p x _) ?_
  refine Eq.trans (congrArg (exteriorPower.map p
      (PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val))
    ((projFormsStalkEquiv R n p x).apply_symm_apply _)) ?_
  exact (eulerWedgeStalkEquivSelf_stalkMapL_eulerWedgeContraction R n p x w).symm

/-- **The quotient arrow `b : ⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)}) ⟶ ⋀^p Ω_{X/R}` of the exterior-power
filtration of the Euler sequence.**

It is the Koszul contraction against the Euler surjection, factored through the monomorphism
`⋀^p Ω_{X/R} ⟶ ⋀^p(𝒪_X(-1)^{⊕ (n+1)})`; the factorization exists because at every stalk the
value of the contraction is a value of that monomorphism, by
`stalkMapL_exteriorPowerMap_projFormsStalkEquiv_symm`. -/
@[sga "7 XI 1.1"]
def eulerWedgeQuotient (p : ℕ) :=
  factorThruMono (Oc := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
      (eulerFirstArrow R n) ((p : ℕ) : ℤ))
    (mono_exteriorPowerMap_eulerFirstArrow R n p)
    (eulerWedgeContraction R n p)
    fun y q => ⟨_, stalkMapL_exteriorPowerMap_projFormsStalkEquiv_symm R n p y q⟩

/-- **The defining property of the quotient arrow**: followed by `⋀^p` of the first arrow of the
Euler sequence it is the Koszul contraction. That arrow is a monomorphism, so this determines
`eulerWedgeQuotient`. -/
theorem eulerWedgeQuotient_comp_exteriorPowerMap (p : ℕ) :
    eulerWedgeQuotient R n p ≫ Scheme.Modules.exteriorPowerMap
        (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n) ((p : ℕ) : ℤ) =
      eulerWedgeContraction R n p :=
  factorThruMono_comp _ _ _ _

/-- **The stalk of the quotient arrow is the stalkwise projection of the filtration**, under the
comparison isomorphism `(⋀^p Ω_{X/R})ₓ ≅ ⋀^p(Ω_x)` of Tag 01CH. Every statement about the
quotient arrow below is read off this one. -/
theorem projFormsStalkEquiv_stalkMapL_eulerWedgeQuotient (p : ℕ)
    (x : ProjectiveSpectrum.top (polyGrading R n))
    (w : eulerWedgeGerm R n x ((p + 1 : ℕ) : ℤ)) :
    projFormsStalkEquiv R n p x
        (PresheafOfModules.stalkMapL x (eulerWedgeQuotient R n p).val w) =
      eulerWedgeStalkProj R n p x w := by
  have h : PresheafOfModules.stalkMapL x (eulerWedgeQuotient R n p).val w =
      (projFormsStalkEquiv R n p x).symm (eulerWedgeStalkProj R n p x w) :=
    stalkMapL_factorThruMono _ _ _ _ x w _
      (stalkMapL_exteriorPowerMap_projFormsStalkEquiv_symm R n p x w)
  refine Eq.trans (congrArg (projFormsStalkEquiv R n p x) h) ?_
  exact (projFormsStalkEquiv R n p x).apply_symm_apply _

/-- **The exterior-power filtration is a complex**: `⋀^{p+1}` of the first arrow of the Euler
sequence followed by the quotient arrow is zero. Vanishing is stalkwise, and at a stalk this is
`eulerWedgeStalkProj_stalkMapL`. -/
theorem exteriorPowerMap_comp_eulerWedgeQuotient (p : ℕ) :
    Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
        (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ) ≫ eulerWedgeQuotient R n p = 0 := by
  refine eq_zero_of_stalkMapL_eq_zero
    (Oc := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) _ fun x z => ?_
  refine Eq.trans (stalkMapL_comp x _ _ z) ?_
  refine (projFormsStalkEquiv R n p x).injective ?_
  refine Eq.trans (projFormsStalkEquiv_stalkMapL_eulerWedgeQuotient R n p x _) ?_
  exact Eq.trans (eulerWedgeStalkProj_stalkMapL R n p x z) (map_zero _).symm

/-- **The quotient arrow is an epimorphism**: epimorphy is stalkwise and the stalkwise projection
of the filtration is surjective. -/
theorem epi_eulerWedgeQuotient (p : ℕ) : Epi (eulerWedgeQuotient R n p) :=
  (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
      (eulerWedgeQuotient R n p)).2 fun x v =>
    (surjective_eulerWedgeStalkProj R n p x (projFormsStalkEquiv R n p x v)).elim fun w hw =>
      ⟨w, Eq.trans (SheafOfModules.stalkMap_hom_eq_stalkMapL x (eulerWedgeQuotient R n p) w)
        ((projFormsStalkEquiv R n p x).injective
          (Eq.trans (projFormsStalkEquiv_stalkMapL_eulerWedgeQuotient R n p x w) hw))⟩

/-- **The exterior-power filtration is exact in the middle**: exactness is stalkwise, and at a
stalk this is `exists_stalkMapL_eq_of_eulerWedgeStalkProj_eq_zero`. -/
theorem exact_eulerWedgeFiltration (p : ℕ) :
    (ShortComplex.mk (Scheme.Modules.exteriorPowerMap
        (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
        ((p + 1 : ℕ) : ℤ)) (eulerWedgeQuotient R n p)
      (exteriorPowerMap_comp_eulerWedgeQuotient R n p)).Exact := by
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun z hz => ?_
  have hzero : eulerWedgeStalkProj R n p x z = 0 := by
    refine Eq.trans (projFormsStalkEquiv_stalkMapL_eulerWedgeQuotient R n p x z).symm ?_
    refine Eq.trans (congrArg (projFormsStalkEquiv R n p x) ?_) (map_zero _)
    exact Eq.trans
      (SheafOfModules.stalkMap_hom_eq_stalkMapL x (eulerWedgeQuotient R n p) z).symm hz
  refine (exists_stalkMapL_eq_of_eulerWedgeStalkProj_eq_zero R n p x z hzero).elim
    fun q hq => ⟨q, ?_⟩
  exact Eq.trans (SheafOfModules.stalkMap_hom_eq_stalkMapL x
    (Scheme.Modules.exteriorPowerMap (X := AlgebraicGeometry.Proj (polyGrading R n))
      (eulerFirstArrow R n) ((p + 1 : ℕ) : ℤ)) q) hq

/-- **The exterior-power filtration of the Euler sequence of `ℙⁿ_R` is a short exact sequence**

`0 ⟶ ⋀^{p+1} Ω_{X/R} ⟶ ⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)}) ⟶ ⋀^p Ω_{X/R} ⟶ 0`,

for every `p`. The first arrow is `⋀^{p+1}` of the first arrow of the Euler sequence and the
second is `eulerWedgeQuotient`, the Koszul contraction against the Euler surjection factored
through `⋀^p` of the first arrow. -/
theorem shortExact_eulerWedgeFiltration (p : ℕ) :
    (ShortComplex.mk (Scheme.Modules.exteriorPowerMap
        (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)
        ((p + 1 : ℕ) : ℤ)) (eulerWedgeQuotient R n p)
      (exteriorPowerMap_comp_eulerWedgeQuotient R n p)).ShortExact :=
  ShortComplex.ShortExact.mk' (exact_eulerWedgeFiltration R n p)
    (mono_exteriorPowerMap_eulerFirstArrow R n (p + 1)) (epi_eulerWedgeQuotient R n p)

end Euler

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
