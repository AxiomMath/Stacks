module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MultiplicationIdealProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionsProductAnnihilator
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Infinitesimal deformations of modules on ringed topoi: the flatness criterion of Stacks 08MQ

Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `𝒥 = Ker(t^♯) ⊂ O_{ℬ'}`, let `ℱ'` be an
`O'`-module and set `ℱ = i^*ℱ'`. Stacks 08MQ says that for `ℱ` flat over `O_ℬ` and `(f, f')`
strict, `ℱ'` is flat over `O_{ℬ'}` if and only if the canonical map

`f^*𝒥 ⊗_O ℱ ⟶ I·ℱ'`

is an isomorphism, and that in that case both factors of

`f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ ⟶ I·ℱ'`

are isomorphisms. This file proves that.

## Main results

* `Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`: Stacks 08MQ, the equivalence
  together with the final statement, with strictness and flatness over the base in the spellings
  of this file; `Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap_of_isStrict` restates
  it with the library's spellings of the two hypotheses.

## The spellings the statement is written in

Flatness over `O_ℬ` is flatness over `f⁻¹O_ℬ`, and flatness over `O_{ℬ'}` is flatness over
`f⁻¹O_{ℬ'}`: that is the reading of both flatness conditions the source opens its proof with,
and it is how `Deformation.ToposThickening.baseModule` and
`Deformation.ToposThickening.reducedBaseModule` present `ℱ'` and `ℱ`.

`ℱ = i^*ℱ'` is presented by the short exact sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ ℱ ⟶ 0`, which is the
sequence of Stacks 08MP and the form in which this tree carries the identification (see
`Deformation.ToposThickening.HasFlatLift`): a cokernel of the inclusion of the ideal product is
exactly the pullback `i^*ℱ'` read on the thickened topos.

The source of the canonical map is `f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`, which is the source's own expression
for `f^*𝒥 ⊗_O ℱ` — "*observe that `f^*𝒥 ⊗_O ℱ = f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`*", the identity this tree
records as `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`. The middle term
`I ⊗_O ℱ` and the target `I·ℱ'` are the objects the source names. The two factors are defined
over the two rings `f⁻¹O_ℬ` and `O'` that the two halves of the square make `ℱ` a module over,
so the canonical map itself is read over `f⁻¹O_{ℬ'}`, the corner both of them restrict to.

Strictness is `Deformation.ToposThickening.IsStrictPullbackIdealMap`, Definition 08M9: the
canonical map of ideals `(f')^*𝒥 ⟶ I` of Situation 08M7 is an epimorphism.

## How the proof goes

The equivalence is the flatness criterion of Stacks 08M4,
`Stacks.SheafOfModules.FlatSquareZero.isFlat_iff_reduction_isFlat_and_multiplication_mono`,
applied to the square-zero extension of sheaves of rings `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ` with ideal
`f⁻¹𝒥`, which
`StacksFrontier.Deformation.ToposThickening.BaseThickeningInverseImage` assembles. Three of its
hypotheses are about that extension alone; the fourth, that the reduction `ℱ' ⟶ ℱ` is a cokernel
of multiplication by `f⁻¹𝒥`, is where strictness enters, through the identity
`(f⁻¹𝒥)·ℱ' = I·ℱ'`. The criterion's multiplication map `mu` is then the canonical map of the tag
followed by the inclusion of `I·ℱ'`
(`Deformation.ToposThickening.canonicalMap_comp_idealProductSubmodule_ι`), so its injectivity is
the invertibility of the canonical map: surjectivity of the canonical map is unconditional,
being the identity `(f⁻¹𝒥)·ℱ' = I·ℱ'` again.

The final statement is the opening sentence of the source's proof. Its one subtlety is that in
the spelling used here the first factor is the map of ideals `f⁻¹𝒥 ⟶ I` tensored with `ℱ` *over
`f⁻¹O_ℬ`*, and that map of ideals is not surjective — only its `O`-span is; see
`Deformation.ToposThickening.epi_canonicalFirstFactor` for how the `O`-scalars are recovered
from the second half of the factor.

## Implementation notes

The map of ideals `f⁻¹𝒥 ⟶ I` of Situation 08M7 is `f⁻¹O_ℬ`-linear but not visibly so: a section
of `f⁻¹O_ℬ` is only locally the reduction of a section of `f⁻¹O_{ℬ'}`, so the linearity cannot
be checked section by section. It is obtained instead from the `O'`-linear map of ideals
`(f')^*𝒥 ⟶ I` that this tree already builds, by the fullness of restriction of scalars along a
locally surjective morphism of sheaves of rings
(`Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective`).

Equalities of morphisms are transported along the equality of the two routes around the square
of structure maps by `Deformation.ToposThickening.squareTransport`, whose endpoints are written
as iterated restrictions of scalars rather than as a restriction along a composite: the two are
the same object, but a composite written with the second spelling is not type-correct at the
`implicit` transparency level, which is the level `rw` builds its motive at.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u v' u' w vS uS wS vS' uS' wS' vA uA

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

section Generic

open Stacks.FlatChangeOfRings (extendScalars extendScalarsAdjunction ringSheafMap)

variable {C : Type uA} [Category.{vA} C] {J : GrothendieckTopology C}

/-- **Transport of a restriction of scalars along an equality of ring maps.** -/
noncomputable def restrictScalarsEqHom {R₀ R : Sheaf J RingCat.{w}} {m₁ m₂ : R₀ ⟶ R}
    (h : m₁ = m₂) (M : SheafOfModules.{w} R) :
    (SheafOfModules.restrictScalars m₁).obj M ⟶ (SheafOfModules.restrictScalars m₂).obj M :=
  eqToHom (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj M) h)

/-- The transport does nothing to a section. -/
theorem restrictScalarsEqHom_val_app {R₀ R : Sheaf J RingCat.{w}} {m₁ m₂ : R₀ ⟶ R}
    (h : m₁ = m₂) (M : SheafOfModules.{w} R) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars m₁).obj M).val.obj U) :
    (restrictScalarsEqHom h M).val.app U x = x := by
  subst h
  rfl

/-- The transport is natural. -/
theorem restrictScalarsEqHom_naturality {R₀ R : Sheaf J RingCat.{w}} {m₁ m₂ : R₀ ⟶ R}
    (h : m₁ = m₂) {M N : SheafOfModules.{w} R} (g : M ⟶ N) :
    restrictScalarsEqHom h M ≫ (SheafOfModules.restrictScalars m₂).map g =
      (SheafOfModules.restrictScalars m₁).map g ≫ restrictScalarsEqHom h N := by
  subst h
  simp [restrictScalarsEqHom]

/-- The transport along an equality and along its inverse cancel. -/
theorem restrictScalarsEqHom_trans {R₀ R : Sheaf J RingCat.{w}} {m₁ m₂ : R₀ ⟶ R}
    (h : m₁ = m₂) (M : SheafOfModules.{w} R) :
    restrictScalarsEqHom h M ≫ restrictScalarsEqHom h.symm M = 𝟙 _ := by
  subst h
  simp [restrictScalarsEqHom]

/-- **Restriction of scalars reflects monomorphisms**, being faithful. -/
theorem mono_of_mono_restrictScalars_map {R₀ R : Sheaf J RingCat.{w}} (m : R₀ ⟶ R)
    {M N : SheafOfModules.{w} R} (g : M ⟶ N)
    (h : Mono ((SheafOfModules.restrictScalars m).map g)) : Mono g :=
  (SheafOfModules.restrictScalars m).mono_of_mono_map h

/-- **Restriction of scalars reflects epimorphisms**, being faithful: it does not change the
underlying morphism of presheaves of abelian groups. -/
theorem epi_of_epi_restrictScalars_map {R₀ R : Sheaf J RingCat.{w}} (m : R₀ ⟶ R)
    {M N : SheafOfModules.{w} R} (g : M ⟶ N)
    (h : Epi ((SheafOfModules.restrictScalars m).map g)) : Epi g :=
  (SheafOfModules.restrictScalars m).epi_of_epi_map h

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Restriction of scalars along a composite is the composite of the restrictions, on
morphisms. -/
theorem restrictScalars_map_comp_ringSheafMap {O₀ O₁ O₂ : Sheaf J CommRingCat.{w}}
    (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂)
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)} (g : M ⟶ N) :
    (SheafOfModules.restrictScalars (ringSheafMap a)).map
        ((SheafOfModules.restrictScalars (ringSheafMap b)).map g) =
      (SheafOfModules.restrictScalars (ringSheafMap (a ≫ b))).map g := rfl

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₀ O₁ O₂ O₃ : Sheaf J CommRingCat.{w}} (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₃) (d : O₀ ⟶ O₂)
  (c : O₂ ⟶ O₃)

/-- The unit of the extension of scalars, with its target written as a restriction of scalars
of an extension of scalars rather than as the composite functor applied to the module. The two
are the same object, but a composite written with the first spelling is not type-correct at the
`implicit` transparency level, so the spelling is crossed once, here. -/
noncomputable def extendScalarsUnit
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    N ⟶ (SheafOfModules.restrictScalars (ringSheafMap c)).obj ((extendScalars c).obj N) :=
  (extendScalarsAdjunction c).unit.app N

/-- The adjoint transpose of a morphism out of an extension of scalars, computed through the
unit. -/
theorem extendScalarsUnit_comp_map
    {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)}
    (κ : (extendScalars c).obj N ⟶ M) :
    extendScalarsUnit c N ≫ (SheafOfModules.restrictScalars (ringSheafMap c)).map κ =
      (extendScalarsAdjunction c).homEquiv N M κ :=
  (Adjunction.homEquiv_unit (adj := extendScalarsAdjunction c) (f := κ)).symm

variable (hsq : ringSheafMap (a ≫ b) = ringSheafMap (d ≫ c))

/-- The transport of a module from `O₃` to `O₀` along the two sides of a commuting square of
sheaves of rings, in the uncomposed spelling. -/
noncomputable def squareTransport
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)) :
    (SheafOfModules.restrictScalars (ringSheafMap d)).obj
        ((SheafOfModules.restrictScalars (ringSheafMap c)).obj M) ⟶
      (SheafOfModules.restrictScalars (ringSheafMap a)).obj
        ((SheafOfModules.restrictScalars (ringSheafMap b)).obj M) :=
  restrictScalarsEqHom hsq.symm M

/-- `Deformation.ToposThickening.squareTransport` in the other direction. -/
noncomputable def squareTransportSymm
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)) :
    (SheafOfModules.restrictScalars (ringSheafMap a)).obj
        ((SheafOfModules.restrictScalars (ringSheafMap b)).obj M) ⟶
      (SheafOfModules.restrictScalars (ringSheafMap d)).obj
        ((SheafOfModules.restrictScalars (ringSheafMap c)).obj M) :=
  restrictScalarsEqHom hsq M

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The transport does nothing to a section. -/
theorem squareTransportSymm_val_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars (ringSheafMap a)).obj
      ((SheafOfModules.restrictScalars (ringSheafMap b)).obj M)).val.obj U) :
    (squareTransportSymm a b d c hsq M).val.app U x = x :=
  restrictScalarsEqHom_val_app hsq M U x

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The transport does nothing to a section. -/
theorem squareTransport_val_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)) (U : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars (ringSheafMap d)).obj
      ((SheafOfModules.restrictScalars (ringSheafMap c)).obj M)).val.obj U) :
    (squareTransport a b d c hsq M).val.app U x = x :=
  restrictScalarsEqHom_val_app hsq.symm M U x

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The two transports cancel. -/
theorem squareTransportSymm_comp_squareTransport
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)) :
    squareTransportSymm a b d c hsq M ≫ squareTransport a b d c hsq M = 𝟙 _ :=
  restrictScalarsEqHom_trans hsq M

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The two transports cancel, the other way round. -/
theorem squareTransport_comp_squareTransportSymm
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)) :
    squareTransport a b d c hsq M ≫ squareTransportSymm a b d c hsq M = 𝟙 _ :=
  restrictScalarsEqHom_trans hsq.symm M

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The transport is invertible. -/
theorem isIso_squareTransportSymm
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)) :
    IsIso (squareTransportSymm a b d c hsq M) :=
  ⟨⟨squareTransport a b d c hsq M, squareTransportSymm_comp_squareTransport a b d c hsq M,
    squareTransport_comp_squareTransportSymm a b d c hsq M⟩⟩

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The transport is natural. -/
theorem squareTransport_naturality
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)} (g : M ⟶ N) :
    squareTransport a b d c hsq M ≫
        (SheafOfModules.restrictScalars (ringSheafMap a)).map
          ((SheafOfModules.restrictScalars (ringSheafMap b)).map g) =
      (SheafOfModules.restrictScalars (ringSheafMap d)).map
          ((SheafOfModules.restrictScalars (ringSheafMap c)).map g) ≫
        squareTransport a b d c hsq N :=
  restrictScalarsEqHom_naturality hsq.symm g

/-- **The comparison of the two extensions of scalars around a commuting square of sheaves of
rings**, applied to a module pulled back from one corner: the adjoint transpose of the unit of
the extension of scalars along the other side of the square. -/
noncomputable def extendRestrictCompare
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    (extendScalars a).obj ((SheafOfModules.restrictScalars (ringSheafMap d)).obj N) ⟶
      (SheafOfModules.restrictScalars (ringSheafMap b)).obj ((extendScalars c).obj N) :=
  ((extendScalarsAdjunction a).homEquiv
      ((SheafOfModules.restrictScalars (ringSheafMap d)).obj N)
      ((SheafOfModules.restrictScalars (ringSheafMap b)).obj ((extendScalars c).obj N))).symm
    ((SheafOfModules.restrictScalars (ringSheafMap d)).map (extendScalarsUnit c N) ≫
      squareTransport a b d c hsq ((extendScalars c).obj N))

/-- **The comparison absorbs the adjoint transpose on the far side of the square.** Both sides
are the adjoint transpose along `a` of one and the same morphism out of `N`, so the identity is
a triangle identity for the extension of scalars along `c`. -/
theorem extendRestrictCompare_comp_map
    {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₃)}
    (k : N ⟶ (SheafOfModules.restrictScalars (ringSheafMap c)).obj M) :
    extendRestrictCompare a b d c hsq N ≫
        (SheafOfModules.restrictScalars (ringSheafMap b)).map
          (((extendScalarsAdjunction c).homEquiv N M).symm k) =
      ((extendScalarsAdjunction a).homEquiv
          ((SheafOfModules.restrictScalars (ringSheafMap d)).obj N)
          ((SheafOfModules.restrictScalars (ringSheafMap b)).obj M)).symm
        ((SheafOfModules.restrictScalars (ringSheafMap d)).map k ≫
          squareTransport a b d c hsq M) := by
  refine ((extendScalarsAdjunction a).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, extendRestrictCompare, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Category.assoc, squareTransport_naturality, ← Category.assoc,
    ← Functor.map_comp, extendScalarsUnit_comp_map, Equiv.apply_symm_apply]

/-- **Moving a scalar across a pure tensor over a commutative ring.** Stated in a minimal
context, so that the module and scalar-tower instances it needs are the canonical ones; at the
sections of a sheaf of commutative rings they are reachable only after the ring structure has
been crossed from `CommRingCat` to `RingCat`, which makes the instance search at the use site
fragile. -/
private theorem tmul_smul_comm {R : Type w} [CommRing R] {M N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (r : R) (z : M) (n : N) :
    (r • z) ⊗ₜ[R] n = z ⊗ₜ[R] (r • n) :=
  TensorProduct.smul_tmul r z n

/-- **A factorisation of a morphism through a subobject killed by its cokernel is an epimorphism.**
If `ι` is a monomorphism killed by the cokernel of `f` and `e ≫ ι = f`, then `e` is the
corestriction of `f` to the image, which is an epimorphism. -/
private theorem epi_of_comp_mono_eq_of_comp_cokernel_π_eq_zero {𝒜 : Type*} [Category 𝒜]
    [Abelian 𝒜] {A B K : 𝒜} (f : A ⟶ B) (ι : K ⟶ B) [Mono ι] (hι : ι ≫ cokernel.π f = 0)
    (e : A ⟶ K) (he : e ≫ ι = f) : Epi e := by
  have hu : kernel.lift (cokernel.π f) ι hι ≫ Abelian.image.ι f = ι := kernel.lift_ι _ _ _
  have : Mono (kernel.lift (cokernel.π f) ι hι) := mono_of_mono_fac hu
  have hfac : e ≫ kernel.lift (cokernel.π f) ι hι = Abelian.factorThruImage f := by
    rw [← cancel_mono (Abelian.image.ι f), Category.assoc, hu, he, Abelian.image.fac]
  have : Epi (kernel.lift (cokernel.π f) ι hι) := by
    have : Epi (e ≫ kernel.lift (cokernel.π f) ι hι) := by rw [hfac]; infer_instance
    exact epi_of_epi e _
  have : IsIso (kernel.lift (cokernel.π f) ι hι) := isIso_of_mono_of_epi _
  rw [show e = Abelian.factorThruImage f ≫ inv (kernel.lift (cokernel.π f) ι hι) by
    rw [← hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
  infer_instance

end Generic

section IdealMap

include comm

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- The two routes around the square of structure maps on the thickened topos agree, read as
morphisms of the underlying sheaves of rings. -/
theorem ringMap_fSharpInverseImage_comp_fSharp :
    ringMap (f'.fSharpInverseImage ≫ i.fSharp) =
      ringMap (inverseImageBaseReduction t f' ≫
        inverseImageReducedStructureMap i t f f' comm) :=
  congrArg (fun m ↦ ringMap m)
    (inverseImageBaseReduction_comp_inverseImageReducedStructureMap i t f f' comm).symm

/-- The adjoint transpose of the canonical map of ideals `(f')^*𝒥 ⟶ I` of Situation 08M7, read
as a morphism of `f⁻¹O_{ℬ'}`-modules `f⁻¹𝒥 ⟶ I`. -/
noncomputable def inverseImageBaseIdealToIdealRestricted :
    (SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).obj
        (inverseImageBaseIdeal t f' ht) ⟶
      (SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).obj
        ((SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj hi.I) :=
  ((Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage).homEquiv
        ((SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).obj
          (inverseImageBaseIdeal t f' ht))
        ((SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap i.fSharp)).obj hi.I))
      (pullbackBaseIdealMap i t f f' hi ht comm) ≫
    squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
      (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) hi.I

/-- **The map `f⁻¹𝒥 ⟶ I` of Situation 08M7.** Situation 08M7 obtains it from the structure map
`(f')^♯ : f⁻¹O_{ℬ'} ⟶ O'`, which carries `f⁻¹𝒥` into `I`; here it is obtained instead as the
adjoint transpose of the canonical map of ideals `(f')^*𝒥 ⟶ I`, which is the same map, and then
read as a morphism of `f⁻¹O_ℬ`-modules.

That last step is the point of the construction. The map is `f⁻¹O_ℬ`-linear, but not visibly so:
a section of `f⁻¹O_ℬ` is only *locally* the reduction of a section of `f⁻¹O_{ℬ'}`, so the
linearity cannot be checked section by section. It is supplied instead by the fullness of
restriction of scalars along the locally surjective reduction `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ`
(`Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective`), which says exactly
that an `f⁻¹O_{ℬ'}`-linear map between `f⁻¹O_ℬ`-modules is already `f⁻¹O_ℬ`-linear. -/
noncomputable def inverseImageBaseIdealToIdeal :
    inverseImageBaseIdeal t f' ht ⟶
      (SheafOfModules.restrictScalars
        (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj hi.I :=
  letI : Sheaf.IsLocallySurjective (ringMap (inverseImageBaseReduction t f')) :=
    ⟨(isLocallySurjective_inverseImageBaseReduction t f' ht).imageSieve_mem⟩
  (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      (ringMap (inverseImageBaseReduction t f'))).preimage
    (inverseImageBaseIdealToIdealRestricted i t f f' hi ht comm)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
/-- `Deformation.ToposThickening.inverseImageBaseIdealToIdeal` is, as a morphism of
`f⁻¹O_{ℬ'}`-modules, the adjoint transpose of the canonical map of ideals. -/
theorem restrictScalars_map_inverseImageBaseIdealToIdeal :
    (SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).map
        (inverseImageBaseIdealToIdeal i t f f' hi ht comm) =
      inverseImageBaseIdealToIdealRestricted i t f f' hi ht comm := by
  let : Sheaf.IsLocallySurjective (ringMap (inverseImageBaseReduction t f')) :=
    ⟨(isLocallySurjective_inverseImageBaseReduction t f' ht).imageSieve_mem⟩
  exact (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
    (ringMap (inverseImageBaseReduction t f'))).map_preimage _

end IdealMap

section Strict

include comm

/-- **`f^*𝒥`**, the pullback along `f` of the square-zero ideal of the thickening of the base:
the inverse image `f⁻¹𝒥`, which is a module over `f⁻¹O_ℬ` because `𝒥` is a module over `O_ℬ`,
with its scalars extended along the structure map `f⁻¹O_ℬ ⟶ O` of `f`. This is the pullback of
Stacks 03D6. -/
noncomputable abbrev reducedPullbackBaseIdeal :
    SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) :=
  (Stacks.FlatChangeOfRings.extendScalars (inverseImageReducedStructureMap i t f f' comm)).obj
    (inverseImageBaseIdeal t f' ht)

/-- **The canonical map of ideals `f^*𝒥 ⟶ I` of Situation 08M7**, as a morphism of `O`-modules:
the adjoint transpose of the map `f⁻¹𝒥 ⟶ I`. -/
noncomputable def reducedPullbackBaseIdealMap :
    reducedPullbackBaseIdeal i t f f' ht comm ⟶ hi.I :=
  ((Stacks.FlatChangeOfRings.extendScalarsAdjunction
      (inverseImageReducedStructureMap i t f f' comm)).homEquiv
      (inverseImageBaseIdeal t f' ht) hi.I).symm
    (inverseImageBaseIdealToIdeal i t f f' hi ht comm)

/-- **The comparison `(f')^*𝒥 ⟶ f^*𝒥` of the two pullbacks of Situation 08M7.** -/
noncomputable abbrev pullbackBaseIdealToReduced :
    pullbackBaseIdeal t f' ht ⟶
      (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
        (reducedPullbackBaseIdeal i t f f' ht comm) :=
  extendRestrictCompare f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
    (inverseImageReducedStructureMap i t f f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) (inverseImageBaseIdeal t f' ht)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
/-- **The two readings of the canonical map of ideals of Situation 08M7 agree**: the map
`(f')^*𝒥 ⟶ I` is the comparison `(f')^*𝒥 ⟶ f^*𝒥` followed by the map `f^*𝒥 ⟶ I`. Both are
adjoint transposes of the same map `f⁻¹𝒥 ⟶ I`. -/
theorem pullbackBaseIdealToReduced_comp_map :
    pullbackBaseIdealToReduced i t f f' ht comm ≫
        (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
          (reducedPullbackBaseIdealMap i t f f' hi ht comm) =
      pullbackBaseIdealMap i t f f' hi ht comm := by
  rw [pullbackBaseIdealToReduced, reducedPullbackBaseIdealMap,
    extendRestrictCompare_comp_map, restrictScalars_map_inverseImageBaseIdealToIdeal,
    inverseImageBaseIdealToIdealRestricted, Category.assoc,
    squareTransportSymm_comp_squareTransport, Category.comp_id]
  exact Equiv.symm_apply_apply _ _

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
/-- **Strictness makes the canonical map of ideals `f^*𝒥 ⟶ I` an epimorphism.** Strictness of
Stacks 08M9 is surjectivity of `(f')^*𝒥 ⟶ I`, which factors through `f^*𝒥` by
`Deformation.ToposThickening.pullbackBaseIdealToReduced_comp_map`; a composite is an
epimorphism only if its second factor is, and restriction of scalars reflects epimorphisms
because it is faithful. -/
theorem epi_reducedPullbackBaseIdealMap
    (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm) :
    Epi (reducedPullbackBaseIdealMap i t f f' hi ht comm) := by
  have h1 : Epi (pullbackBaseIdealMap i t f f' hi ht comm) := hstrict
  have h2 : Epi (pullbackBaseIdealToReduced i t f f' ht comm ≫
      (SheafOfModules.restrictScalars (ringMap i.fSharp)).map
        (reducedPullbackBaseIdealMap i t f f' hi ht comm)) := by
    rw [pullbackBaseIdealToReduced_comp_map]
    exact h1
  have := h2
  exact epi_of_epi_restrictScalars_map (ringMap i.fSharp) _
    (epi_of_epi (pullbackBaseIdealToReduced i t f f' ht comm) _)

end Strict

section Factors

open Stacks.SheafOfModules.FlatSquareZero (reductionTensorMap)

variable (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- Every local section of the square-zero ideal is killed by the structure map. -/
theorem fSharp_incl_apply (U : X'.Cᵒᵖ) (a : hi.I.val.obj U) :
    i.fSharp.hom.app U
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U from hi.incl.val.app U a) = 0 :=
  (hi.kernel U _).2 ⟨a, rfl⟩

variable (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)
  (hq : (idealProductSubmodule hi F').ι ≫ q = 0)

include hq

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The reduction kills the multiplication map of the thickening.** The reduction kills the
ideal product `I·ℱ'` by assumption, and a morphism out of `ℱ'` killing the ideal product kills
the multiplication map. -/
theorem multiplicationMap_comp_eq_zero_of_idealProduct :
    multiplicationMap i.fSharp hi.I F' hi.incl ≫ q = 0 :=
  Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_comp_eq_zero
    i.fSharp hi.I F' hi.incl q hq

variable (hqex : (ShortComplex.mk (idealProductSubmodule hi F').ι q hq).ShortExact)

include hqex

/-- **The reduction `ℱ' ⟶ ℱ` is a cokernel of the multiplication map `I ⊗_{O'} ℱ' ⟶ ℱ'`.** It is
a cokernel of the inclusion of the ideal product by the short exactness of
`0 ⟶ I·ℱ' ⟶ ℱ' ⟶ ℱ ⟶ 0`, and the two have the same cokernels. -/
noncomputable def isColimitCokernelCoforkMultiplication :
    IsColimit (CokernelCofork.ofπ q
      (multiplicationMap_comp_eq_zero_of_idealProduct i hi F F' q hq)) :=
  Stacks.SheafOfModules.FlatSquareZero.cokernelCofork_multiplicationMap_isColimit
    i.fSharp hi.I F' hi.incl q hq hqex.gIsCokernel
    (multiplicationMap_comp_eq_zero_of_idealProduct i hi F F' q hq)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **`I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ` is an isomorphism**: tensoring with the ideal does not see the
difference between `ℱ'` and its reduction, because the ideal is square zero. This is the
reduction comparison of Stacks 08M4 for the thickening `i`. -/
theorem isIso_reductionTensorMap_thickening :
    IsIso (reductionTensorMap i.fSharp hi.I F' F q) :=
  Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_isIso i.fSharp hi.surjective
    hi.I hi.I F' F hi.incl (fSharp_incl_apply i hi)
    q (multiplicationMap_comp_eq_zero_of_idealProduct i hi F F' q hq)
    (isColimitCokernelCoforkMultiplication i hi F F' q hq hqex)

/-- **The multiplication map `I ⊗_{O'} ℱ' ⟶ ℱ'` corestricted to the ideal product `I·ℱ'`.** The
inclusion of `I·ℱ'` is a kernel of the reduction, which the multiplication map is killed by. -/
noncomputable def multiplicationToIdealProduct :
    ((sheafTensor.{u', v', w, w, w} X'.O).flip.obj F').obj
        ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I) ⟶
      (idealProductSubmodule hi F').toSheafOfModules :=
  (KernelFork.IsLimit.lift' hqex.fIsKernel (multiplicationMap i.fSharp hi.I F' hi.incl)
    (multiplicationMap_comp_eq_zero_of_idealProduct i hi F F' q hq)).1

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The corestriction is the multiplication map. -/
theorem multiplicationToIdealProduct_comp_ι :
    multiplicationToIdealProduct i hi F F' q hq hqex ≫ (idealProductSubmodule hi F').ι =
      multiplicationMap i.fSharp hi.I F' hi.incl :=
  (KernelFork.IsLimit.lift' hqex.fIsKernel (multiplicationMap i.fSharp hi.I F' hi.incl)
    (multiplicationMap_comp_eq_zero_of_idealProduct i hi F F' q hq)).2

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The multiplication map is surjective onto the ideal product `I·ℱ'`.**

This is the one point at which the ideal product being a *sheaf* submodule is used rather than
its generators. The image of the multiplication map is a sheaf submodule of `ℱ'` containing
every generator `α·x` of `I·ℱ'`, so it contains `I·ℱ'`; concretely, the inclusion of `I·ℱ'` is
killed by the cokernel of the multiplication map
(`Stacks.SheafOfModules.FlatSquareZero.imageProductSubmodule_ι_comp_eq_zero`), so it factors
through the image, and the factorisation is a monomorphism and an epimorphism, hence invertible.
No local sum of products is written down. -/
theorem epi_multiplicationToIdealProduct :
    Epi (multiplicationToIdealProduct i hi F F' q hq hqex) :=
  epi_of_comp_mono_eq_of_comp_cokernel_π_eq_zero (multiplicationMap i.fSharp hi.I F' hi.incl)
    (idealProductSubmodule hi F').ι
    (Stacks.SheafOfModules.FlatSquareZero.imageProductSubmodule_ι_comp_eq_zero
      i.fSharp hi.I F' hi.incl _ (cokernel.condition _)) _
    (multiplicationToIdealProduct_comp_ι i hi F F' q hq hqex)

/-- **The second factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of Stacks 08MQ.** On a pure tensor
`α ⊗ q(x)` it is `α·x`, which is independent of the lift `x` of the section of `ℱ` because the
ideal is square zero; formally, that independence is the invertibility of the reduction
comparison `I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ`, and the map is multiplication read through its inverse. -/
noncomputable def canonicalSecondFactor :
    (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) ⟶
      (idealProductSubmodule hi F').toSheafOfModules :=
  letI := isIso_reductionTensorMap_thickening i hi F F' q hq hqex
  inv (reductionTensorMap i.fSharp hi.I F' F q) ≫
    multiplicationToIdealProduct i hi F F' q hq hqex

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The second factor is surjective.** -/
theorem epi_canonicalSecondFactor :
    Epi (canonicalSecondFactor i hi F F' q hq hqex) := by
  let := isIso_reductionTensorMap_thickening i hi F F' q hq hqex
  let := epi_multiplicationToIdealProduct i hi F F' q hq hqex
  rw [canonicalSecondFactor]
  infer_instance

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The reduction comparison followed by the second factor is multiplication.** This is the
characterisation of the second factor: on a pure tensor `α ⊗ q(x)` of `I ⊗_O ℱ` its value in
`ℱ'` is `α·x`. -/
theorem reductionTensorMap_comp_canonicalSecondFactor :
    reductionTensorMap i.fSharp hi.I F' F q ≫ canonicalSecondFactor i hi F F' q hq hqex ≫
        (idealProductSubmodule hi F').ι =
      multiplicationMap i.fSharp hi.I F' hi.incl := by
  let := isIso_reductionTensorMap_thickening i hi F F' q hq hqex
  rw [canonicalSecondFactor, Category.assoc, ← Category.assoc
    (reductionTensorMap i.fSharp hi.I F' F q), IsIso.hom_inv_id, Category.id_comp,
    multiplicationToIdealProduct_comp_ι]

end Factors

section BaseCriterion

open Stacks.SheafOfModules.FlatSquareZero (reductionTensorMap multiplicationMap_tmul)
open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit
  unitToRestrictScalarsUnit_val_app)

/-- **A morphism out of `G` killing every product `ii(a)·x` kills the multiplication map.** A
morphism out of the sheafified tensor product is determined by its values on the images of pure
tensors, through the sheafification adjunction the multiplication map is itself defined by, and
on `a ⊗ x` the value is `ii(a)·x`.

This is `Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_comp_eq_zero` with the
hypothesis weakened from "kills the ideal product `I·G`" to "kills the generators of the ideal
product", which is what is available when the target is a module over a quotient ring rather
than a submodule of `G`. -/
theorem multiplicationMap_comp_eq_zero_of_smul {C : Type uA} [Category.{vA} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {O' O : Sheaf J CommRingCat.{w}} (fr : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (ii : (SheafOfModules.restrictScalars (ringMap fr)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')} (g : G ⟶ Z)
    (hg : ∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U),
      g.val.app U
        ((show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from ii.val.app U a) •
            x) = 0) :
    multiplicationMap fr I G ii ≫ g = 0 := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a x
  change g.val.app U ((multiplicationMap fr I G ii).val.app U
    (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
        (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap fr)).obj I).val
          G.val)).app U
      (a ⊗ₜ[O'.obj.obj U] x))) = 0
  rw [multiplicationMap_tmul fr I G ii U (show I.val.obj U from a) x]
  exact hg U _ x

variable (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))

/-- **`ℱ'` read as a module over `f⁻¹O_{ℬ'}`.** Flatness of `ℱ'` over `O_{ℬ'}` is, by
definition, flatness of this module. -/
noncomputable abbrev baseModule :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')) :=
  (SheafOfModules.restrictScalars (ringMap f'.fSharpInverseImage)).obj F'

/-- **`ℱ` read as a module over `f⁻¹O_ℬ`.** Flatness of `ℱ` over `O_ℬ` is, by definition,
flatness of this module. -/
noncomputable abbrev reducedBaseModule :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
        (inverseImageReducedBaseRing t f')) :=
  (SheafOfModules.restrictScalars
    (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj F

variable (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)

/-- **The reduction `ℱ' ⟶ ℱ`, read as a morphism of `f⁻¹O_{ℬ'}`-modules.** This is the map
Stacks 08M4 consumes as its `q`; the transport is the equality of the two routes around the
square of structure maps. -/
noncomputable def baseReductionMap :
    baseModule f' F' ⟶ (SheafOfModules.restrictScalars
      (ringMap (inverseImageBaseReduction t f'))).obj
        (reducedBaseModule i t f f' comm F) :=
  (SheafOfModules.restrictScalars
      (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map q ≫
    squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
      (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) F

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The reduction kills the multiplication map of the pulled-back base ideal.** Its target is
a module over the quotient `f⁻¹O_ℬ`, and every section of `f⁻¹𝒥` is killed by the reduction
`f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ`, so each generator `j·x` is sent to `ρ(j)·q(x) = 0`. -/
theorem multiplicationMap_comp_baseReductionMap :
    multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
        (baseModule f' F') (inverseImageBaseIdealIncl t f' ht) ≫
      baseReductionMap i t f f' comm F F' q = 0 := by
  refine multiplicationMap_comp_eq_zero_of_smul _ _ _ _ _ fun U z x ↦ ?_
  refine Eq.trans (show (baseReductionMap i t f f' comm F F' q).val.app U
        ((show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U z) • x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U z) •
        (baseReductionMap i t f f' comm F F' q).val.app U x from
    map_smul _ _ _) ?_
  exact Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero
    (ringMap (inverseImageBaseReduction t f')) _ U _
    (inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht U z) _

/-- The unit presenting `(f')^*𝒥` as the extension of scalars of `f⁻¹𝒥`. -/
noncomputable abbrev pullbackBaseIdealUnit :
    (SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).obj
        (inverseImageBaseIdeal t f' ht) ⟶
      (SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).obj
          (pullbackBaseIdeal t f' ht) :=
  extendScalarsUnit f'.fSharpInverseImage
    ((SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).obj
      (inverseImageBaseIdeal t f' ht))

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The composite `f⁻¹𝒥 ⟶ (f')^*𝒥 ⟶ O'` is `(f')^♯` applied to the sections of `f⁻¹𝒥`.** This
is the normalisation `Deformation.ToposThickening.pullbackBaseIdealToStructure` is defined
by. -/
theorem pullbackBaseIdealUnit_comp_toStructure :
    pullbackBaseIdealUnit t f' ht ≫
        (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
            (pullbackBaseIdealToStructure t f' ht) =
      inverseImageBaseIdealIncl t f' ht ≫
        unitToRestrictScalarsUnit (ringMap f'.fSharpInverseImage) :=
  (extendScalarsUnit_comp_map f'.fSharpInverseImage
    (pullbackBaseIdealToStructure t f' ht)).trans (Equiv.apply_symm_apply _ _)

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- The sectionwise form of
`Deformation.ToposThickening.pullbackBaseIdealUnit_comp_toStructure`. -/
theorem pullbackBaseIdealToStructure_unit_apply (U : X'.Cᵒᵖ)
    (z : (inverseImageBaseIdeal t f' ht).val.obj U) :
    Stacks.SheafOfModules.ringValue (pullbackBaseIdealToStructure t f' ht) U
        ((pullbackBaseIdealUnit t f' ht).val.app U z) =
      f'.fSharpInverseImage.hom.app U
        (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U z) :=
  (congrArg (fun m ↦ m.val.app U z) (pullbackBaseIdealUnit_comp_toStructure t f' ht)).trans
    (unitToRestrictScalarsUnit_val_app (ringMap f'.fSharpInverseImage) U _)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
/-- **`(f⁻¹𝒥)·ℱ' = I·ℱ'` for a strict morphism of thickenings**, with the left-hand side written
as the submodule generated by the products `(f')^♯(j)·x` of a section `j` of `f⁻¹𝒥` with a
section `x` of `ℱ'`.

This is the sentence of the source's proof that the strictness of `(f, f')` together with
`ℱ = i^*ℱ'` gives `ℱ = ℱ'/(f⁻¹𝒥)ℱ'`. Strictness enters exactly once, as surjectivity of
`(f')^*𝒥 ⟶ I`: precomposing a map into the structure sheaf with an epimorphism does not change
the submodule it multiplies out. That `(f')^*𝒥` multiplies out no more than the image of
`f⁻¹𝒥` does is
`Stacks.SheafOfModules.imageProductSubmodule_eq_unitImageSections`, and needs no pure-tensor
decomposition of `(f')^*𝒥`. -/
theorem idealProductSubmodule_eq_sectionsProductSubmodule
    (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm) :
    idealProductSubmodule hi F' =
      Stacks.SheafOfModules.sectionsProductSubmodule
        (Stacks.SheafOfModules.unitImageSections (pullbackBaseIdealUnit t f' ht)
          (pullbackBaseIdealToStructure t f' ht)) F' := by
  have : Epi (pullbackBaseIdealMap i t f f' hi ht comm) := hstrict
  have h1 : Stacks.SheafOfModules.imageProductSubmodule
        (pullbackBaseIdealToStructure t f' ht) F' =
      Stacks.SheafOfModules.sectionsProductSubmodule
        (Stacks.SheafOfModules.unitImageSections (pullbackBaseIdealUnit t f' ht)
          (pullbackBaseIdealToStructure t f' ht)) F' :=
    Stacks.SheafOfModules.imageProductSubmodule_eq_unitImageSections
      (pullbackBaseIdealUnit t f' ht)
      (fun Z g hg ↦ Stacks.SheafOfModules.restrictScalars_unit_cancel_zero
        (Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage) _ Z g hg)
      (pullbackBaseIdealToStructure t f' ht) F'
  have h2 : Stacks.SheafOfModules.imageProductSubmodule
      (pullbackBaseIdealToStructure t f' ht) F' = idealProductSubmodule hi F' := by
    rw [← pullbackBaseIdealMap_comp_incl i t f f' hi ht comm]
    exact Stacks.SheafOfModules.imageProductSubmodule_comp_of_epi
      (pullbackBaseIdealMap i t f f' hi ht comm) hi.incl F'
  exact h2.symm.trans h1

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The family of sections `(f')^♯(j)` is stable under restriction.** -/
theorem unitImageSections_restrict {U V : X'.Cᵒᵖ} (h : U ⟶ V)
    {a : (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U}
    (ha : a ∈ Stacks.SheafOfModules.unitImageSections (pullbackBaseIdealUnit t f' ht)
      (pullbackBaseIdealToStructure t f' ht) U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.map h a ∈
      Stacks.SheafOfModules.unitImageSections (pullbackBaseIdealUnit t f' ht)
        (pullbackBaseIdealToStructure t f' ht) V := by
  obtain ⟨j, rfl⟩ := ha
  exact ⟨((SheafOfModules.restrictScalars
      (ringMap (inverseImageBaseReduction t f'))).obj
        (inverseImageBaseIdeal t f' ht)).val.restrictₛₗ h j,
    (congrArg (Stacks.SheafOfModules.ringValue (pullbackBaseIdealToStructure t f' ht) V)
          (PresheafOfModules.naturality_apply (pullbackBaseIdealUnit t f' ht).val h j)).trans
      (Stacks.SheafOfModules.ringValue_restrictₛₗ (pullbackBaseIdealToStructure t f' ht) h _)⟩

variable (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)
  {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f'))}
  (k : baseModule f' F' ⟶ Z)
  (hk : multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
    (baseModule f' F') (inverseImageBaseIdealIncl t f' ht) ≫ k = 0)

omit [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] [HasSheafify X'.J AddCommGrpCat.{w}] in
include hk in
/-- A morphism out of `ℱ'` killing the multiplication map of `f⁻¹𝒥` kills every generator
`(f')^♯(j)·x` of `(f⁻¹𝒥)·ℱ'`. -/
theorem apply_smul_eq_zero_of_multiplicationMap (U : X'.Cᵒᵖ)
    (z : (inverseImageBaseIdeal t f' ht).val.obj U) (m : (baseModule f' F').val.obj U) :
    k.val.app U
        ((show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U z) • m) = 0 := by
  have h0 : (multiplicationMap (inverseImageBaseReduction t f')
        (inverseImageBaseIdeal t f' ht) (baseModule f' F')
        (inverseImageBaseIdealIncl t f' ht) ≫ k).val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f'))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj)).unit.app
          (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
            (ringMap (inverseImageBaseReduction t f'))).obj
            (inverseImageBaseIdeal t f' ht)).val
            (baseModule f' F').val)).app U
        (z ⊗ₜ[(inverseImageBaseRing f').obj.obj U] m)) = 0 := by
    rw [hk]
    rfl
  have h1 : k.val.app U
      ((multiplicationMap (inverseImageBaseReduction t f')
          (inverseImageBaseIdeal t f' ht) (baseModule f' F')
          (inverseImageBaseIdealIncl t f' ht)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj)).unit.app
            (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
              (ringMap (inverseImageBaseReduction t f'))).obj
              (inverseImageBaseIdeal t f' ht)).val
              (baseModule f' F').val)).app U
          (z ⊗ₜ[(inverseImageBaseRing f').obj.obj U] m))) = 0 := h0
  exact (congrArg (fun y ↦ k.val.app U y)
    (multiplicationMap_tmul (inverseImageBaseReduction t f')
      (inverseImageBaseIdeal t f' ht) (baseModule f' F')
      (inverseImageBaseIdealIncl t f' ht) U z m).symm).trans h1

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hk in
/-- **A morphism out of `ℱ'` killing the multiplication map of `f⁻¹𝒥` kills the ideal product
`I·ℱ'`.** The two submodules agree for a strict morphism of thickenings, and the morphism is
linear only over `f⁻¹O_{ℬ'}`, so its kernel is not an `O'`-submodule of `ℱ'`; the locality
argument is carried by
`Stacks.SheafOfModules.apply_eq_zero_of_mem_sectionsProductSubmodule`. -/
theorem restrictScalars_idealProductSubmodule_comp_eq_zero
    (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm) :
    (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
        (idealProductSubmodule hi F').ι ≫ k = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_))
  have hm : (m.1 : F'.val.obj U) ∈
      (Stacks.SheafOfModules.sectionsProductSubmodule
        (Stacks.SheafOfModules.unitImageSections (pullbackBaseIdealUnit t f' ht)
          (pullbackBaseIdealToStructure t f' ht)) F').obj U := by
    rw [← idealProductSubmodule_eq_sectionsProductSubmodule i t f f' hi ht comm F' hstrict]
    exact m.2
  refine Stacks.SheafOfModules.apply_eq_zero_of_mem_sectionsProductSubmodule
    (fun U a b ↦ ?_) _
    (fun {U V} h {a} ha ↦ unitImageSections_restrict t f' ht h ha) k
    (fun U a ha n ↦ ?_) hm
  · let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U) := by
      change CommRing (X'.O.obj.obj U)
      infer_instance
    exact mul_comm a b
  · obtain ⟨j, rfl⟩ := ha
    change Stacks.SheafOfModules.restrictedApply k U
      (Stacks.SheafOfModules.ringValue (pullbackBaseIdealToStructure t f' ht) U
        ((pullbackBaseIdealUnit t f' ht).val.app U j) • n) = 0
    rw [pullbackBaseIdealToStructure_unit_apply t f' ht U j]
    exact apply_smul_eq_zero_of_multiplicationMap t f' ht F' k hk U j n

variable (hq : (idealProductSubmodule hi F').ι ≫ q = 0)
  (hqex : (ShortComplex.mk (idealProductSubmodule hi F').ι q hq).ShortExact)
  (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasWeakSheafify X'.J AddCommGrpCat.{w}] in
include hqex in
/-- The sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ ℱ ⟶ 0` is still short exact read over `f⁻¹O_{ℬ'}`:
restriction of scalars is exact. -/
theorem shortExact_map_restrictScalars_idealProduct :
    ((ShortComplex.mk (idealProductSubmodule hi F').ι q hq).map
      (SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage))).ShortExact :=
  Stacks.SheafOfModules.ChangeOfRings.shortExact_map_restrictScalars _ hqex

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasWeakSheafify X'.J AddCommGrpCat.{w}] in
include hqex in
/-- The reduction, read over `f⁻¹O_{ℬ'}`, is an epimorphism. -/
theorem epi_baseReductionMap : Epi (baseReductionMap i t f f' comm F F' q) := by
  have : Epi ((SheafOfModules.restrictScalars
      (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map q) :=
    (shortExact_map_restrictScalars_idealProduct i f' hi F F' q hq hqex).epi_g
  have := isIso_squareTransportSymm f'.fSharpInverseImage i.fSharp
    (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) F
  rw [baseReductionMap]
  infer_instance

include hqex hstrict in
/-- **The reduction `ℱ' ⟶ ℱ` is a cokernel of the multiplication map `f⁻¹𝒥 ⊗ ℱ' ⟶ ℱ'`.**

This is the hypothesis Stacks 08M4 consumes, and the point at which strictness is used: the
reduction is a cokernel of the inclusion of `I·ℱ'` by assumption, and for a strict morphism of
thickenings `(f⁻¹𝒥)·ℱ' = I·ℱ'`, so a morphism killing the multiplication map of `f⁻¹𝒥` already
kills `I·ℱ'` and therefore factors through the reduction. -/
noncomputable def isColimitCokernelCoforkBaseReduction :
    IsColimit (CokernelCofork.ofπ (baseReductionMap i t f f' comm F F' q)
      (multiplicationMap_comp_baseReductionMap i t f f' ht comm F F' q)) := by
  haveI := epi_baseReductionMap i t f f' hi comm F F' q hq hqex
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {A} kk hkk ↦ ?_
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    (shortExact_map_restrictScalars_idealProduct i f' hi F F' q hq hqex).gIsCokernel
    kk (restrictScalars_idealProductSubmodule_comp_eq_zero i t f f' hi ht comm F' kk hkk hstrict)
  refine ⟨squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
      (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) F ≫ l, ?_⟩
  rw [baseReductionMap, Category.assoc, ← Category.assoc
      (squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
        (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) F),
    squareTransportSymm_comp_squareTransport, Category.id_comp]
  exact hl

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hqex hstrict in
/-- **The reduction comparison `f⁻¹𝒥 ⊗ ℱ' ⟶ f⁻¹𝒥 ⊗ ℱ` is an isomorphism.** -/
theorem isIso_reductionTensorMapBase :
    IsIso (reductionTensorMap (inverseImageBaseReduction t f')
      (inverseImageBaseIdeal t f' ht) (baseModule f' F')
      (reducedBaseModule i t f f' comm F) (baseReductionMap i t f f' comm F F' q)) :=
  Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_isIso
    (inverseImageBaseReduction t f')
    (isLocallySurjective_inverseImageBaseReduction t f' ht)
    (inverseImageBaseIdeal t f' ht) (inverseImageBaseIdeal t f' ht)
    (baseModule f' F') (reducedBaseModule i t f f' comm F)
    (inverseImageBaseIdealIncl t f' ht)
    (inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht)
    (baseReductionMap i t f f' comm F F' q)
    (multiplicationMap_comp_baseReductionMap i t f f' ht comm F F' q)
    (isColimitCokernelCoforkBaseReduction i t f f' hi ht comm F F' q hq hqex hstrict)

include hqex hstrict in
/-- **The multiplication map `mu` of Stacks 08M4 for the pulled-back base ideal**: the map
`f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ ⟶ ℱ'` whose injectivity Stacks 08M4 makes equivalent to flatness of `ℱ'`
over `O_{ℬ'}`. On a pure tensor `j ⊗ q(x)` it is `(f')^♯(j)·x`. -/
noncomputable def baseMultiplicationFactor :
    (SheafOfModules.restrictScalars (ringMap (inverseImageBaseReduction t f'))).obj
        (((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).flip.obj
          (reducedBaseModule i t f f' comm F)).obj (inverseImageBaseIdeal t f' ht)) ⟶
      baseModule f' F' :=
  letI := isIso_reductionTensorMapBase i t f f' hi ht comm F F' q hq hqex hstrict
  inv (reductionTensorMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
      (baseModule f' F') (reducedBaseModule i t f f' comm F)
      (baseReductionMap i t f f' comm F F' q)) ≫
    multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
      (baseModule f' F') (inverseImageBaseIdealIncl t f' ht)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hqex hstrict in
/-- The reduction comparison followed by `mu` is multiplication. -/
theorem reductionTensorMap_comp_baseMultiplicationFactor :
    reductionTensorMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
          (baseModule f' F') (reducedBaseModule i t f f' comm F)
          (baseReductionMap i t f f' comm F F' q) ≫
        baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict =
      multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
        (baseModule f' F') (inverseImageBaseIdealIncl t f' ht) := by
  let := isIso_reductionTensorMapBase i t f f' hi ht comm F F' q hq hqex hstrict
  rw [baseMultiplicationFactor, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hqex hstrict in
/-- **`mu` on a pure tensor**, which is the normalisation Stacks 08M4 pins it down by. -/
theorem baseMultiplicationFactor_tmul (U : X'.Cᵒᵖ)
    (a : (inverseImageBaseIdeal t f' ht).val.obj U) (x : (baseModule f' F').val.obj U) :
    (baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                (inverseImageReducedBaseRing t f')).obj)).unit.app
            (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
              (reducedBaseModule i t f f' comm F).val)).app U
          (a ⊗ₜ[(inverseImageReducedBaseRing t f').obj.obj U]
            ((baseReductionMap i t f f' comm F F' q).val.app U x))) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U a) • x := by
  have h := congrArg (fun φ : ((sheafTensor.{u', v', w, w, w} (inverseImageBaseRing f')).flip.obj
    (baseModule f' F')).obj ((SheafOfModules.restrictScalars
        (ringMap (inverseImageBaseReduction t f'))).obj (inverseImageBaseIdeal t f' ht)) ⟶
      baseModule f' F' ↦ φ.val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj)).unit.app
            (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
              (ringMap (inverseImageBaseReduction t f'))).obj
              (inverseImageBaseIdeal t f' ht)).val
              (baseModule f' F').val)).app U
          (a ⊗ₜ[(inverseImageBaseRing f').obj.obj U] x)))
    (reductionTensorMap_comp_baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict)
  have h1 : (baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict).val.app U
      ((reductionTensorMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
          (baseModule f' F') (reducedBaseModule i t f f' comm F)
          (baseReductionMap i t f f' comm F F' q)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj)).unit.app
            (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
              (ringMap (inverseImageBaseReduction t f'))).obj
              (inverseImageBaseIdeal t f' ht)).val
              (baseModule f' F').val)).app U
          (a ⊗ₜ[(inverseImageBaseRing f').obj.obj U] x))) =
      (multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
          (baseModule f' F') (inverseImageBaseIdealIncl t f' ht)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj)).unit.app
            (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
              (ringMap (inverseImageBaseReduction t f'))).obj
              (inverseImageBaseIdeal t f' ht)).val
              (baseModule f' F').val)).app U
          (a ⊗ₜ[(inverseImageBaseRing f').obj.obj U] x)) := h
  exact (congrArg (fun y ↦
      (baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict).val.app U y)
    (Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_tmul
      (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht) (baseModule f' F')
      (reducedBaseModule i t f f' comm F) (baseReductionMap i t f f' comm F F' q)
      U a x).symm).trans
    (h1.trans (multiplicationMap_tmul (inverseImageBaseReduction t f')
      (inverseImageBaseIdeal t f' ht) (baseModule f' F')
      (inverseImageBaseIdealIncl t f' ht) U a x))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hqex hstrict in
/-- **Stacks 08M4 applied to the pulled-back thickening of the base.** `ℱ'` is flat over
`O_{ℬ'}` if and only if `ℱ` is flat over `O_ℬ` and the map `f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ ⟶ ℱ'` is
injective.

The data Stacks 08M4 asks for is assembled from the inverse image of the thickening of the
base: the reduction `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ` is locally surjective, `f⁻¹𝒥` is sectionwise exactly
its kernel, its sections multiply to zero, and the reduction `ℱ' ⟶ ℱ` is a cokernel of
multiplication by `f⁻¹𝒥` — the last by strictness. -/
theorem isFlat_baseModule_iff :
    AlgebraicGeometry.SheafOfModules.IsFlat (baseModule f' F') ↔
      (AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F) ∧
        Mono (baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict)) :=
  Stacks.SheafOfModules.FlatSquareZero.isFlat_iff_reduction_isFlat_and_multiplication_mono
    (inverseImageBaseReduction t f')
    (isLocallySurjective_inverseImageBaseReduction t f' ht)
    (inverseImageBaseIdeal t f' ht) (baseModule f' F')
    (reducedBaseModule i t f f' comm F) (inverseImageBaseIdealIncl t f' ht)
    (inverseImageBaseReduction_inverseImageBaseIdealIncl t f' ht)
    (existsUnique_inverseImageBaseIdeal_section t f' ht)
    (mul_eq_zero_of_inverseImageBaseIdeal t f' ht)
    (multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
      (baseModule f' F') (inverseImageBaseIdealIncl t f' ht))
    (multiplicationMap_tmul (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
      (baseModule f' F') (inverseImageBaseIdealIncl t f' ht))
    (baseReductionMap i t f f' comm F F' q)
    (multiplicationMap_comp_baseReductionMap i t f f' ht comm F F' q)
    (isColimitCokernelCoforkBaseReduction i t f f' hi ht comm F F' q hq hqex hstrict)
    (baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict)
    (baseMultiplicationFactor_tmul i t f f' hi ht comm F F' q hq hqex hstrict)

end BaseCriterion





section FirstFactorEpi

open Stacks.SheafOfModules.FlatSquareZero (reductionTensorMap reductionTensorMap_tmul
  reductionTensorMap_epi)

variable (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  {T : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))}

include comm

/-- A pure tensor of `I ⊗_O ℱ` pushed through a morphism out of it that is linear only over
`f⁻¹O_ℬ`. -/
private noncomputable def idealTensorApply
    (g : (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
              X.O)).flip.obj F).obj hi.I) ⟶ T)
    (U : X'.Cᵒᵖ) (z : hi.I.val.obj U) (m : F.val.obj U) : T.val.obj U :=
  g.val.app U (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
      (PresheafOfModules.tensorObj hi.I.val
        F.val)).app U (z ⊗ₜ m))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasSheafify X'.J AddCommGrpCat.{w}] in
private lemma idealTensorApply_zero_left
    (g : (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
              X.O)).flip.obj F).obj hi.I) ⟶ T)
    (U : X'.Cᵒᵖ) (m : F.val.obj U) :
    idealTensorApply i t f f' hi comm F g U 0 m = 0 := by
  let : Module ((((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj ⋙
      forget₂ CommRingCat RingCat).obj U) (hi.I.val.obj U) := (hi.I.val.obj U).isModule
  let : Module ((((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj ⋙
      forget₂ CommRingCat RingCat).obj U) (F.val.obj U) := (F.val.obj U).isModule
  refine Eq.trans (congrArg (fun y ↦ g.val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val
            F.val)).app U y)) (TensorProduct.zero_tmul _ m)) ?_
  exact (congrArg (fun y ↦ g.val.app U y) (map_zero _)).trans (map_zero _)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasSheafify X'.J AddCommGrpCat.{w}] in
private lemma idealTensorApply_add_left
    (g : (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
              X.O)).flip.obj F).obj hi.I) ⟶ T)
    (U : X'.Cᵒᵖ) (z z' : hi.I.val.obj U) (m : F.val.obj U) :
    idealTensorApply i t f f' hi comm F g U (z + z') m =
      idealTensorApply i t f f' hi comm F g U z m +
        idealTensorApply i t f f' hi comm F g U z' m := by
  let : Module ((((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj ⋙
      forget₂ CommRingCat RingCat).obj U) (hi.I.val.obj U) := (hi.I.val.obj U).isModule
  let : Module ((((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj ⋙
      forget₂ CommRingCat RingCat).obj U) (F.val.obj U) := (F.val.obj U).isModule
  refine Eq.trans (congrArg (fun y ↦ g.val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val
            F.val)).app U y))
    (TensorProduct.add_tmul z z' m)) ?_
  exact (congrArg (fun y ↦ g.val.app U y) (map_add _ _ _)).trans (map_add _ _ _)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasSheafify X'.J AddCommGrpCat.{w}] in
private lemma idealTensorApply_smul_left
    (g : (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
              X.O)).flip.obj F).obj hi.I) ⟶ T)
    (U : X'.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U)
    (z : hi.I.val.obj U) (m : F.val.obj U) :
    idealTensorApply i t f f' hi comm F g U (r • z) m =
      idealTensorApply i t f f' hi comm F g U z (r • m) := by
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U) :=
    inferInstanceAs (CommRing (((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U))
  exact congrArg (fun y ↦ g.val.app U
    (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
        (PresheafOfModules.tensorObj hi.I.val
          F.val)).app U y)) (tmul_smul_comm r z m)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasSheafify X'.J AddCommGrpCat.{w}] in
private lemma idealTensorApply_restrict
    (g : (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
              X.O)).flip.obj F).obj hi.I) ⟶ T)
    {U V : X'.Cᵒᵖ} (h : U ⟶ V) (z : hi.I.val.obj U) (m : F.val.obj U) :
    T.val.restrictₛₗ h (idealTensorApply i t f f' hi comm F g U z m) =
      idealTensorApply i t f f' hi comm F g V (hi.I.val.restrictₛₗ h z)
        (F.val.restrictₛₗ h m) :=
  (PresheafOfModules.naturality_apply g.val h _).symm.trans
    (congrArg (g.val.app V)
      (PresheafOfModules.naturality_apply ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val
            F.val)) h
        (z ⊗ₜ m)).symm)

/-- The sections of `I` which `g` kills against every section of `ℱ`, after every restriction.
This is an `O`-submodule even though the kernel of `g` is only an `f⁻¹O_ℬ`-submodule: an
`O`-scalar moves from the left factor of the tensor product to the right one. -/
private noncomputable def tensorAnnihilatorPresubmodule
    (g : (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
              X.O)).flip.obj F).obj hi.I) ⟶ T) :
    hi.I.val.Submodule where
  obj U :=
    { carrier := {z : hi.I.val.obj U | ∀ (V : X'.Cᵒᵖ) (h : U ⟶ V) (m : F.val.obj V),
        idealTensorApply i t f f' hi comm F g V (hi.I.val.restrictₛₗ h z) m = 0}
      zero_mem' := fun V h m => by
        rw [map_zero, idealTensorApply_zero_left]
      add_mem' := fun {z z'} hz hz' V h m => by
        rw [map_add, idealTensorApply_add_left, hz V h m, hz' V h m, add_zero]
      smul_mem' := fun r {z} hz V h m => by
        refine Eq.trans (congrArg (fun y ↦ idealTensorApply i t f f' hi comm F g V y m)
          ((hi.I.val.restrictₛₗ h).map_smulₛₗ r z)) ?_
        exact (idealTensorApply_smul_left i t f f' hi comm F g V _ _ m).trans (hz V h _) }
  map := fun {U U'} k z hz V h m => by
    rw [Stacks.SheafOfModules.restrictₛₗ_restrictₛₗ]
    exact hz V (k ≫ h) m

/-- The sections `g` kills form a *sheaf* submodule: the condition quantifies over all
restrictions, and `T` is separated. -/
private noncomputable def tensorAnnihilatorSubmodule
    (g : (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj
              X.O)).flip.obj F).obj hi.I) ⟶ T) :
    hi.I.Submodule where
  toSubmodule := tensorAnnihilatorPresubmodule i t f f' hi comm F g
  isSheaf := by
    intro U z hz V h m
    apply T.isSheaf.isSeparated _ _ (X'.J.pullback_stable h.unop hz)
    intro W k hk
    have hmem : hi.I.val.restrictₛₗ (h ≫ k.op) z ∈
        (tensorAnnihilatorPresubmodule i t f f' hi comm F g).obj (Opposite.op W) := by
      rw [show h ≫ k.op = (k ≫ h.unop).op from rfl]
      exact hk
    change T.val.restrictₛₗ k.op
        (idealTensorApply i t f f' hi comm F g V (hi.I.val.restrictₛₗ h z) m) =
      T.val.restrictₛₗ k.op 0
    rw [map_zero, idealTensorApply_restrict, Stacks.SheafOfModules.restrictₛₗ_restrictₛₗ]
    have hz' := hmem (Opposite.op W) (𝟙 _) (F.val.restrictₛₗ k.op m)
    rwa [PresheafOfModules.restrictₛₗ_id_apply] at hz'

end FirstFactorEpi

section FirstFactor

open Stacks.SheafOfModules.FlatSquareZero (reductionTensorMap reductionTensorMap_tmul)

variable (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include comm in
/-- **The map `f⁻¹𝒥 ⟶ I` of Situation 08M7, on sections**: a local section `j` of `f⁻¹𝒥` goes to
the unique section of `I` whose image in `O'` is `(f')^♯(j)`. -/
theorem incl_inverseImageBaseIdealToIdeal_apply (U : X'.Cᵒᵖ)
    (z : (inverseImageBaseIdeal t f' ht).val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U from
      hi.incl.val.app U
        ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z)) =
      f'.fSharpInverseImage.hom.app U
        (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
          (inverseImageBaseIdealIncl t f' ht).val.app U z) := by
  have h1 : (inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z =
      (inverseImageBaseIdealToIdealRestricted i t f f' hi ht comm).val.app U z :=
    congrArg (fun φ ↦ φ.val.app U z)
      (restrictScalars_map_inverseImageBaseIdealToIdeal i t f f' hi ht comm)
  have h2 : (inverseImageBaseIdealToIdealRestricted i t f f' hi ht comm).val.app U z =
      (squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
          (inverseImageReducedStructureMap i t f f' comm)
          (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) hi.I).val.app U
        ((((Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage).homEquiv
            ((SheafOfModules.restrictScalars
                (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).obj
              (inverseImageBaseIdeal t f' ht))
            ((SheafOfModules.restrictScalars
                (Stacks.FlatChangeOfRings.ringSheafMap i.fSharp)).obj hi.I))
          (pullbackBaseIdealMap i t f f' hi ht comm)).val.app U z) := rfl
  have h3 : (inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z =
      (pullbackBaseIdealMap i t f f' hi ht comm).val.app U
        ((pullbackBaseIdealUnit t f' ht).val.app U z) := by
    rw [h1, h2, squareTransportSymm_val_app]
    exact congrArg (fun φ ↦ φ.val.app U z)
      (Adjunction.homEquiv_unit
        (adj := Stacks.FlatChangeOfRings.extendScalarsAdjunction f'.fSharpInverseImage)
        (f := pullbackBaseIdealMap i t f f' hi ht comm))
  rw [h3]
  exact (congrArg (fun φ ↦ φ.val.app U ((pullbackBaseIdealUnit t f' ht).val.app U z))
      (pullbackBaseIdealMap_comp_incl i t f f' hi ht comm)).trans
    (pullbackBaseIdealToStructure_unit_apply t f' ht U z)

include comm in
/-- **The first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` of the canonical map of Stacks 08MQ.**

The source is written as `f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`, which is the source's own expression for
`f^*𝒥 ⊗_O ℱ` — "observe that `f^*𝒥 ⊗_O ℱ = f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`", the identity recorded in this
tree as `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`. In that spelling the map
is the map of ideals `f⁻¹𝒥 ⟶ I` of Situation 08M7 tensored with `ℱ`, followed by the comparison
that moves the scalars of the tensor product from `f⁻¹O_ℬ` up to `O`; on a pure tensor it is
`j ⊗ m ↦ λ(j) ⊗ m`, which is what the map `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` does. -/
noncomputable def canonicalFirstFactor :
    ((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).flip.obj
      (reducedBaseModule i t f f' comm F)).obj (inverseImageBaseIdeal t f' ht) ⟶
      (SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) :=
  ((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).flip.obj
    (reducedBaseModule i t f f' comm F)).map
      (inverseImageBaseIdealToIdeal i t f f' hi ht comm) ≫
    reductionTensorMap (inverseImageReducedStructureMap i t f f' comm) hi.I
      (reducedBaseModule i t f f' comm F) F (𝟙 _)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include comm in
/-- **The first factor on a pure tensor**: `j ⊗ m ↦ λ(j) ⊗ m`. -/
theorem canonicalFirstFactor_tmul (U : X'.Cᵒᵖ)
    (z : (inverseImageBaseIdeal t f' ht).val.obj U)
    (m : (reducedBaseModule i t f f' comm F).val.obj U) :
    (canonicalFirstFactor i t f f' hi ht comm F).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                (inverseImageReducedBaseRing t f')).obj)).unit.app
            (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
              (reducedBaseModule i t f f' comm F).val)).app U (z ⊗ₜ m)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val
            F.val)).app U
        ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z ⊗ₜ m) := by
  have hnat : (((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).flip.obj
    (reducedBaseModule i t f f' comm F)).map
        (inverseImageBaseIdealToIdeal i t f f' hi ht comm)).val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              (inverseImageReducedBaseRing t f')).obj)).unit.app
          (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
            (reducedBaseModule i t f f' comm F).val)).app U (z ⊗ₜ m)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              (inverseImageReducedBaseRing t f')).obj)).unit.app
          (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
            (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj hi.I).val
            (reducedBaseModule i t f f' comm F).val)).app U
        ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z ⊗ₜ m) :=
    PresheafOfModules.unit_naturality_apply _ U _
  have h2 : (canonicalFirstFactor i t f f' hi ht comm F).val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              (inverseImageReducedBaseRing t f')).obj)).unit.app
          (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
            (reducedBaseModule i t f f' comm F).val)).app U (z ⊗ₜ m)) =
      (reductionTensorMap (inverseImageReducedStructureMap i t f f' comm) hi.I
          (reducedBaseModule i t f f' comm F) F (𝟙 _)).val.app U
        ((((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).flip.obj
          (reducedBaseModule i t f f' comm F)).map
            (inverseImageBaseIdealToIdeal i t f f' hi ht comm)).val.app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                  (inverseImageReducedBaseRing t f')).obj)).unit.app
              (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
                (reducedBaseModule i t f f' comm F).val)).app U (z ⊗ₜ m))) := rfl
  rw [h2, hnat]
  exact reductionTensorMap_tmul (inverseImageReducedStructureMap i t f f' comm) hi.I
    (reducedBaseModule i t f f' comm F) F (𝟙 _) U _ m

variable (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
  (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj F)
  (hq : (idealProductSubmodule hi F').ι ≫ q = 0)
  (hqex : (ShortComplex.mk (idealProductSubmodule hi F').ι q hq).ShortExact)
  (hstrict : IsStrictPullbackIdealMap i t f f' hi ht comm)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}] in
include comm in
/-- The reduction `ℱ' ⟶ ℱ` read over `f⁻¹O_{ℬ'}` does nothing to a section. -/
theorem baseReductionMap_val_app (U : X'.Cᵒᵖ) (x : (baseModule f' F').val.obj U) :
    (baseReductionMap i t f f' comm F F' q).val.app U x = q.val.app U x :=
  squareTransportSymm_val_app f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
    (inverseImageReducedStructureMap i t f f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) F U _

include hqex in
/-- **The canonical map `f^*𝒥 ⊗_O ℱ ⟶ I·ℱ'` of Stacks 08MQ**, read over `f⁻¹O_{ℬ'}`, which is
where its two factors compose: the first is a morphism of `f⁻¹O_ℬ`-modules and the second a
morphism of `O'`-modules, and both rings map to `O` along the two sides of the square. -/
noncomputable def canonicalMap :
    (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).obj
        (((sheafTensor.{u', v', w, w, w} (inverseImageReducedBaseRing t f')).flip.obj
          (reducedBaseModule i t f f' comm F)).obj (inverseImageBaseIdeal t f' ht)) ⟶
      (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).obj
        (idealProductSubmodule hi F').toSheafOfModules :=
  (SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
      (canonicalFirstFactor i t f f' hi ht comm F) ≫
    squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
        (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I) ≫
      (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
        (canonicalSecondFactor i hi F F' q hq hqex)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hqex in
/-- **The canonical map, on a pure tensor**: `j ⊗ q(x) ↦ (f')^♯(j)·x`, read inside `I·ℱ'`. -/
theorem canonicalMap_val_app_tmul (U : X'.Cᵒᵖ)
    (a : (inverseImageBaseIdeal t f' ht).val.obj U) (x : (baseModule f' F').val.obj U) :
    (idealProductSubmodule hi F').ι.val.app U
        ((canonicalMap i t f f' hi ht comm F F' q hq hqex).val.app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                  (inverseImageReducedBaseRing t f')).obj)).unit.app
              (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
                (reducedBaseModule i t f f' comm F).val)).app U
            (a ⊗ₜ (baseReductionMap i t f f' comm F F' q).val.app U x))) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBaseRing f')).obj.obj U from
        (inverseImageBaseIdealIncl t f' ht).val.app U a) • x := by
  have e1 : (canonicalMap i t f f' hi ht comm F F' q hq hqex).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                (inverseImageReducedBaseRing t f')).obj)).unit.app
            (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
              (reducedBaseModule i t f f' comm F).val)).app U
          (a ⊗ₜ (baseReductionMap i t f f' comm F F' q).val.app U x)) =
      (canonicalSecondFactor i hi F F' q hq hqex).val.app U
        ((squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
            (inverseImageReducedStructureMap i t f f' comm)
            (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
            (((sheafTensor.{u',
              v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
              hi.I)).val.app U
          ((canonicalFirstFactor i t f f' hi ht comm F).val.app U
            (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                    (inverseImageReducedBaseRing t f')).obj)).unit.app
                (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
                  (reducedBaseModule i t f f' comm F).val)).app U
              (a ⊗ₜ (baseReductionMap i t f f' comm F F' q).val.app U x)))) := rfl
  have e2 : (canonicalMap i t f f' hi ht comm F F' q hq hqex).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                (inverseImageReducedBaseRing t f')).obj)).unit.app
            (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
              (reducedBaseModule i t f f' comm F).val)).app U
          (a ⊗ₜ (baseReductionMap i t f f' comm F F' q).val.app U x)) =
      (canonicalSecondFactor i hi F F' q hq hqex).val.app U
        ((canonicalFirstFactor i t f f' hi ht comm F).val.app U
          (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                  (inverseImageReducedBaseRing t f')).obj)).unit.app
              (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
                (reducedBaseModule i t f f' comm F).val)).app U
            (a ⊗ₜ (baseReductionMap i t f f' comm F F' q).val.app U x))) :=
    e1.trans (congrArg ((canonicalSecondFactor i hi F F' q hq hqex).val.app U)
      (squareTransport_val_app f'.fSharpInverseImage i.fSharp
        (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I)
        U _))
  rw [e2]
  refine Eq.trans (congrArg (fun z ↦ (idealProductSubmodule hi F').ι.val.app U
      ((canonicalSecondFactor i hi F F' q hq hqex).val.app U z))
    (canonicalFirstFactor_tmul i t f f' hi ht comm F U a
      ((baseReductionMap i t f f' comm F F' q).val.app U x))) ?_
  rw [baseReductionMap_val_app]
  refine Eq.trans (congrArg (fun z ↦ (idealProductSubmodule hi F').ι.val.app U
        ((canonicalSecondFactor i hi F F' q hq hqex).val.app U z))
      (Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_tmul i.fSharp hi.I F' F q U
        ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U a) x).symm) ?_
  refine Eq.trans (congrArg (fun φ ↦ φ.val.app U
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X'.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj)).unit.app
          (PresheafOfModules.tensorObj
              ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val
            F'.val)).app U
        ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U a ⊗ₜ x)))
    (reductionTensorMap_comp_canonicalSecondFactor i hi F F' q hq hqex)) ?_
  refine Eq.trans (Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_tmul
    i.fSharp hi.I F' hi.incl U
    ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U a) x) ?_
  exact congrArg (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj.obj U ↦
      r • (show F'.val.obj U from x))
    (incl_inverseImageBaseIdealToIdeal_apply i t f f' hi ht comm U a)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hqex hstrict in
/-- **The canonical map of Stacks 08MQ followed by the inclusion of `I·ℱ'` is the multiplication
map `mu` of Stacks 08M4.** Both are determined by their values on the images of the pure tensors
`j ⊗ q(x)`, where both are `(f')^♯(j)·x`. -/
theorem canonicalMap_comp_idealProductSubmodule_ι :
    canonicalMap i t f f' hi ht comm F F' q hq hqex ≫
        (SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (idealProductSubmodule hi F').ι =
      baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict := by
  let := isIso_reductionTensorMapBase i t f f' hi ht comm F F' q hq hqex hstrict
  have key : reductionTensorMap (inverseImageBaseReduction t f')
          (inverseImageBaseIdeal t f' ht) (baseModule f' F')
          (reducedBaseModule i t f f' comm F) (baseReductionMap i t f f' comm F F' q) ≫
        (canonicalMap i t f f' hi ht comm F F' q hq hqex ≫
          (SheafOfModules.restrictScalars
              (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
            (idealProductSubmodule hi F').ι) =
      multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
        (baseModule f' F') (inverseImageBaseIdealIncl t f' ht) := by
    refine Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_eq_of_tmul _ _ _ _ _
      fun U a x ↦ ?_
    refine Eq.trans (congrArg (fun z ↦ (idealProductSubmodule hi F').ι.val.app U
        ((canonicalMap i t f f' hi ht comm F F' q hq hqex).val.app U z))
      (Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_tmul
        (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht) (baseModule f' F')
        (reducedBaseModule i t f f' comm F) (baseReductionMap i t f f' comm F F' q) U a x)) ?_
    exact canonicalMap_val_app_tmul i t f f' hi ht comm F F' q hq hqex U a x
  exact (cancel_epi (reductionTensorMap (inverseImageBaseReduction t f')
      (inverseImageBaseIdeal t f' ht) (baseModule f' F')
      (reducedBaseModule i t f f' comm F) (baseReductionMap i t f f' comm F F' q))).mp
    (key.trans (reductionTensorMap_comp_baseMultiplicationFactor
      i t f f' hi ht comm F F' q hq hqex hstrict).symm)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hqex hstrict in
/-- **The canonical map of Stacks 08MQ is surjective onto `I·ℱ'`.**

This is the identity `(f⁻¹𝒥)·ℱ' = I·ℱ'` of a strict morphism of thickenings, read through the
identification of the canonical map with the multiplication map of Stacks 08M4: the image of
multiplication by `f⁻¹𝒥` is a sheaf submodule of `ℱ'` containing every generator of `I·ℱ'`, so
it contains `I·ℱ'`, and the inclusion of `I·ℱ'` is therefore killed by the cokernel of
multiplication. No local sum of products is written down. -/
theorem epi_canonicalMap : Epi (canonicalMap i t f f' hi ht comm F F' q hq hqex) := by
  let := isIso_reductionTensorMapBase i t f f' hi ht comm F F' q hq hqex hstrict
  have : (SheafOfModules.restrictScalars
      (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have : Epi (reductionTensorMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
      (baseModule f' F') (reducedBaseModule i t f f' comm F)
      (baseReductionMap i t f f' comm F F' q) ≫
        canonicalMap i t f f' hi ht comm F F' q hq hqex) := by
    refine epi_of_comp_mono_eq_of_comp_cokernel_π_eq_zero
      (multiplicationMap (inverseImageBaseReduction t f') (inverseImageBaseIdeal t f' ht)
        (baseModule f' F') (inverseImageBaseIdealIncl t f' ht))
      ((SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (idealProductSubmodule hi F').ι)
      (restrictScalars_idealProductSubmodule_comp_eq_zero i t f f' hi ht comm F' _
        (cokernel.condition _) hstrict) _ ?_
    rw [Category.assoc, canonicalMap_comp_idealProductSubmodule_ι i t f f' hi ht comm F F' q hq
      hqex hstrict, reductionTensorMap_comp_baseMultiplicationFactor i t f f' hi ht comm F F' q
      hq hqex hstrict]
  exact epi_of_epi (reductionTensorMap (inverseImageBaseReduction t f')
    (inverseImageBaseIdeal t f' ht) (baseModule f' F')
    (reducedBaseModule i t f f' comm F) (baseReductionMap i t f f' comm F F' q)) _

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hstrict in
/-- **Strictness makes the first factor `f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ` surjective.**

This is the opening sentence of the source's proof: *the map `f^*𝒥 ⟶ I` is surjective as
`(f, f')` is a strict morphism of thickenings.*

The deduction is not simply right exactness of the tensor product, because in the spelling used
here the first factor is the map of ideals `f⁻¹𝒥 ⟶ I` tensored with `ℱ` *over `f⁻¹O_ℬ`*, and
that map of ideals is not surjective — only its `O`-span is. The `O`-scalars are supplied by the
second half of the factor, the comparison that moves the tensor product from `f⁻¹O_ℬ` up to `O`:
the sections of `I` which kill `g` against every section of `ℱ` form an `O`-submodule `N` of `I`
precisely because an `O`-scalar crosses the tensor product, the map `f⁻¹𝒥 ⟶ I` lands in `N`, so
`f^*𝒥 ⟶ I` factors through `N` by adjunction, and strictness makes that factorisation
surjective. Hence `N = I` and `g = 0`. -/
theorem epi_canonicalFirstFactor :
    Epi (canonicalFirstFactor i t f f' hi ht comm F) := by
  have hkappa : Epi (reducedPullbackBaseIdealMap i t f f' hi ht comm) :=
    epi_reducedPullbackBaseIdealMap i t f f' hi ht comm hstrict
  have hrtm : Epi (reductionTensorMap (inverseImageReducedStructureMap i t f f' comm) hi.I
      (reducedBaseModule i t f f' comm F) F (𝟙 _)) :=
    Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_epi _ _ _ _ _
  rw [Preadditive.epi_iff_cancel_zero]
  intro T g hg
  -- every section of `I` kills `g` against every section of `ℱ`
  have hmemAll : ∀ (U : X'.Cᵒᵖ) (z : hi.I.val.obj U),
      z ∈ (tensorAnnihilatorSubmodule i t f f' hi comm F g).obj U := by
    -- the map of ideals `f⁻¹𝒥 ⟶ I` lands in the annihilator
    have hin : ∀ (U : X'.Cᵒᵖ) (z : (inverseImageBaseIdeal t f' ht).val.obj U),
        ∃ b : (tensorAnnihilatorSubmodule i t f f' hi comm F g).obj U,
          ((SheafOfModules.restrictScalars
              (ringMap (inverseImageReducedStructureMap i t f f' comm))).map
            (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι).val.app U b =
            (inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z := by
      intro U z
      refine ⟨⟨(inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z, ?_⟩, rfl⟩
      intro V h m
      have hnat : hi.I.val.restrictₛₗ h
            ((inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app U z) =
          (inverseImageBaseIdealToIdeal i t f f' hi ht comm).val.app V
            ((inverseImageBaseIdeal t f' ht).val.restrictₛₗ h z) :=
        (PresheafOfModules.naturality_apply
          (inverseImageBaseIdealToIdeal i t f f' hi ht comm).val h z).symm
      rw [hnat]
      have hzero : (canonicalFirstFactor i t f f' hi ht comm F ≫ g).val.app V
          (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                  (inverseImageReducedBaseRing t f')).obj)).unit.app
              (PresheafOfModules.tensorObj (inverseImageBaseIdeal t f' ht).val
                (reducedBaseModule i t f f' comm F).val)).app V
            ((inverseImageBaseIdeal t f' ht).val.restrictₛₗ h z ⊗ₜ m)) = 0 := by
        rw [hg]
        rfl
      refine Eq.trans ?_ hzero
      exact (congrArg (fun y ↦ g.val.app V y)
        (canonicalFirstFactor_tmul i t f f' hi ht comm F V
          ((inverseImageBaseIdeal t f' ht).val.restrictₛₗ h z) m)).symm
    obtain ⟨lift, hlift, _⟩ := Stacks.SheafOfModules.existsUnique_factorThrough
      ((SheafOfModules.restrictScalars
          (ringMap (inverseImageReducedStructureMap i t f f' comm))).map
        (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι)
      (fun U => Subtype.val_injective)
      (inverseImageBaseIdealToIdeal i t f f' hi ht comm) hin
    have hfac : ((Stacks.FlatChangeOfRings.extendScalarsAdjunction
          (inverseImageReducedStructureMap i t f f' comm)).homEquiv
          (inverseImageBaseIdeal t f' ht)
          (tensorAnnihilatorSubmodule i t f f' hi comm F g).toSheafOfModules).symm lift ≫
        (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι =
        reducedPullbackBaseIdealMap i t f f' hi ht comm := by
      rw [reducedPullbackBaseIdealMap, ← hlift,
        Adjunction.homEquiv_naturality_right_symm]
    have hcompEpi : Epi (((Stacks.FlatChangeOfRings.extendScalarsAdjunction
          (inverseImageReducedStructureMap i t f f' comm)).homEquiv
          (inverseImageBaseIdeal t f' ht)
          (tensorAnnihilatorSubmodule i t f f' hi comm F g).toSheafOfModules).symm lift ≫
        (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι) := by
      rw [hfac]
      exact hkappa
    have : Epi ((tensorAnnihilatorSubmodule i t f f' hi comm F g).ι) :=
      epi_of_epi (((Stacks.FlatChangeOfRings.extendScalarsAdjunction
        (inverseImageReducedStructureMap i t f f' comm)).homEquiv
        (inverseImageBaseIdeal t f' ht)
        (tensorAnnihilatorSubmodule i t f f' hi comm F g).toSheafOfModules).symm lift) _
    have : IsIso ((tensorAnnihilatorSubmodule i t f f' hi comm F g).ι) :=
      isIso_of_mono_of_epi _
    intro U z
    have hz : (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι.val.app U
        ((inv (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι).val.app U z) = z :=
      congrArg (fun φ ↦ φ.val.app U z)
        (IsIso.inv_hom_id (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι)
    exact hz ▸ ((inv (tensorAnnihilatorSubmodule i t f f' hi comm F g).ι).val.app U z).2
  -- therefore the reduction comparison composed with `g` is zero, and it is an epimorphism
  have hcomp : reductionTensorMap (inverseImageReducedStructureMap i t f f' comm) hi.I
      (reducedBaseModule i t f f' comm F) F (𝟙 _) ≫ g = 0 := by
    apply (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f')).obj)).injective
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    have hval : (reductionTensorMap (inverseImageReducedStructureMap i t f f' comm) hi.I
          (reducedBaseModule i t f f' comm F) F (𝟙 _) ≫ g).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageReducedBaseRing t f'))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                (inverseImageReducedBaseRing t f')).obj)).unit.app
            (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars
              (ringMap (inverseImageReducedStructureMap i t f f' comm))).obj hi.I).val
              (reducedBaseModule i t f f' comm F).val)).app U (a ⊗ₜ x)) =
        idealTensorApply i t f f' hi comm F g U a x :=
      congrArg (fun y ↦ g.val.app U y)
        (reductionTensorMap_tmul (inverseImageReducedStructureMap i t f f' comm) hi.I
          (reducedBaseModule i t f f' comm F) F (𝟙 _) U a x)
    refine Eq.trans hval ?_
    exact (congrArg (fun y ↦ idealTensorApply i t f f' hi comm F g U y x)
      (PresheafOfModules.restrictₛₗ_id_apply hi.I.val U a)).symm.trans
      (hmemAll U a U (𝟙 U) x)
  exact (cancel_epi (reductionTensorMap (inverseImageReducedStructureMap i t f f' comm) hi.I
    (reducedBaseModule i t f f' comm F) F (𝟙 _))).mp (hcomp.trans (comp_zero).symm)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})] in
include hstrict in
/-- **Stacks 08MQ.** Let `(f, f')` be a morphism of first order thickenings of ringed topoi as
in Situation 08M7, let `ℱ'` be an `O'`-module and let `ℱ = i^*ℱ'`, presented by the short exact
sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ ℱ ⟶ 0`. Assume `ℱ` is flat over `O_ℬ` and that `(f, f')` is strict
(Stacks 08M9). Then the following are equivalent:

1. `ℱ'` is flat over `O_{ℬ'}`, and
2. the canonical map `f^*𝒥 ⊗_O ℱ ⟶ I·ℱ'` is an isomorphism.

Moreover, in this case the two factors

`f^*𝒥 ⊗_O ℱ ⟶ I ⊗_O ℱ ⟶ I·ℱ'`

are isomorphisms.

Flatness over `O_ℬ` is flatness over `f⁻¹O_ℬ` and flatness over `O_{ℬ'}` is flatness over
`f⁻¹O_{ℬ'}`, which is how the two flatness conditions are written; the source of the canonical
map is `f⁻¹𝒥 ⊗_{f⁻¹O_ℬ} ℱ`, which is the source's own expression for `f^*𝒥 ⊗_O ℱ`, and the
canonical map itself is read over `f⁻¹O_{ℬ'}`, the corner of the square both of its factors are
defined over.

The equivalence is the flatness criterion of Stacks 08M4 applied to the square-zero extension of
sheaves of rings `f⁻¹O_{ℬ'} ⟶ f⁻¹O_ℬ` with ideal `f⁻¹𝒥`: strictness identifies `ℱ` with
`ℱ'/(f⁻¹𝒥)ℱ'`, which is the cokernel datum that criterion consumes, and the canonical map
composed with the inclusion of `I·ℱ'` is the multiplication map whose injectivity the criterion
makes equivalent to flatness. The final statement is the opening sentence of the source's proof:
the map `f^*𝒥 ⟶ I` is surjective because `(f, f')` is strict, so the first factor is surjective,
and a surjection whose composite with the second factor is invertible is invertible, after which
so is the second factor.

Strictness and flatness of `ℱ` over `O_ℬ` are taken here in the two spellings native to this
file, `Deformation.ToposThickening.IsStrictPullbackIdealMap` and flatness of
`Deformation.ToposThickening.reducedBaseModule`.
`Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap_of_isStrict` is the same statement
with the two hypotheses in the spellings of the rest of the library — strictness as
`Deformation.ToposThickening.MorphismOfThickenings.IsStrict` of Stacks 08M9 and flatness as
`Deformation.ToposThickening.IsFlatOverBase` — and is the one registered for Stacks 08MQ. -/
theorem isFlat_iff_isIso_canonicalMap
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F)) :
    (AlgebraicGeometry.SheafOfModules.IsFlat (baseModule f' F') ↔
        IsIso (canonicalMap i t f f' hi ht comm F F' q hq hqex)) ∧
      (IsIso (canonicalMap i t f f' hi ht comm F F' q hq hqex) →
        IsIso (canonicalFirstFactor i t f f' hi ht comm F) ∧
          IsIso (canonicalSecondFactor i hi F F' q hq hqex)) := by
  have : (SheafOfModules.restrictScalars
      (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have : (SheafOfModules.restrictScalars
      (Stacks.FlatChangeOfRings.ringSheafMap
        (inverseImageBaseReduction t f'))).PreservesEpimorphisms :=
    CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
  have hepi1 : Epi (canonicalFirstFactor i t f f' hi ht comm F) :=
    epi_canonicalFirstFactor i t f f' hi ht comm F hstrict
  have hepi2 : Epi (canonicalSecondFactor i hi F F' q hq hqex) :=
    epi_canonicalSecondFactor i hi F F' q hq hqex
  have hepi : Epi (canonicalMap i t f f' hi ht comm F F' q hq hqex) :=
    epi_canonicalMap i t f f' hi ht comm F F' q hq hqex hstrict
  have := isIso_squareTransportSymm f'.fSharpInverseImage i.fSharp
    (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
    (((sheafTensor.{u',
      v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I)
  have : IsIso (squareTransport f'.fSharpInverseImage i.fSharp
      (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
      (((sheafTensor.{u',
        v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I)) :=
    ⟨⟨squareTransportSymm f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
        (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm) _,
      squareTransport_comp_squareTransportSymm _ _ _ _ _ _,
      squareTransportSymm_comp_squareTransport _ _ _ _ _ _⟩⟩
  have hmu := canonicalMap_comp_idealProductSubmodule_ι i t f f' hi ht comm F F' q hq hqex hstrict
  have hassoc : canonicalMap i t f f' hi ht comm F F' q hq hqex =
      ((SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
          (canonicalFirstFactor i t f f' hi ht comm F) ≫
        squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
          (inverseImageReducedStructureMap i t f f' comm)
          (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
          (((sheafTensor.{u',
            v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
            hi.I)) ≫
      (SheafOfModules.restrictScalars
          (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
        (canonicalSecondFactor i hi F F' q hq hqex) := by
    rw [canonicalMap, Category.assoc]
  refine ⟨⟨fun hflat ↦ ?_, fun hiso ↦ ?_⟩, fun hiso ↦ ?_⟩
  · have : Mono (baseMultiplicationFactor i t f f' hi ht comm F F' q hq hqex hstrict) :=
      ((isFlat_baseModule_iff i t f f' hi ht comm F F' q hq hqex hstrict).mp hflat).2
    have : Mono (canonicalMap i t f f' hi ht comm F F' q hq hqex ≫
        (SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (idealProductSubmodule hi F').ι) := by
      rw [hmu]; infer_instance
    have : Mono (canonicalMap i t f f' hi ht comm F F' q hq hqex) :=
      mono_of_mono (canonicalMap i t f f' hi ht comm F F' q hq hqex)
        ((SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (idealProductSubmodule hi F').ι)
    exact isIso_of_mono_of_epi _
  · refine (isFlat_baseModule_iff i t f f' hi ht comm F F' q hq hqex hstrict).mpr ⟨hF, ?_⟩
    have := hiso
    rw [← hmu]
    infer_instance
  · have := hiso
    have hcm : Mono (((SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
            (canonicalFirstFactor i t f f' hi ht comm F) ≫
          squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
            (inverseImageReducedStructureMap i t f f' comm)
            (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
            (((sheafTensor.{u',
              v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
              hi.I)) ≫
        (SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (canonicalSecondFactor i hi F F' q hq hqex)) := by
      rw [← hassoc]
      infer_instance
    have hm : Mono (((SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
          (canonicalFirstFactor i t f f' hi ht comm F) ≫
        squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
          (inverseImageReducedStructureMap i t f f' comm)
          (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
          (((sheafTensor.{u',
            v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
            hi.I))) :=
      mono_of_mono _ ((SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (canonicalSecondFactor i hi F F' q hq hqex))
    have : Mono ((SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
          (canonicalFirstFactor i t f f' hi ht comm F)) :=
      mono_of_mono _ (squareTransport f'.fSharpInverseImage i.fSharp
        (inverseImageBaseReduction t f') (inverseImageReducedStructureMap i t f f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
        (((sheafTensor.{u',
          v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I))
    have : Mono (canonicalFirstFactor i t f f' hi ht comm F) :=
      mono_of_mono_restrictScalars_map
        (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f')) _ inferInstance
    have hiso1 : IsIso (canonicalFirstFactor i t f f' hi ht comm F) :=
      isIso_of_mono_of_epi _
    refine ⟨hiso1, ?_⟩
    have : IsIso ((SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
          (canonicalFirstFactor i t f f' hi ht comm F) ≫
        squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
          (inverseImageReducedStructureMap i t f f' comm)
          (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
          (((sheafTensor.{u',
            v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
            hi.I)) := inferInstance
    have : IsIso ((SheafOfModules.restrictScalars
        (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
          (canonicalSecondFactor i hi F F' q hq hqex)) := by
      rw [show (SheafOfModules.restrictScalars
            (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage)).map
              (canonicalSecondFactor i hi F F' q hq hqex) =
          inv ((SheafOfModules.restrictScalars
              (Stacks.FlatChangeOfRings.ringSheafMap (inverseImageBaseReduction t f'))).map
                (canonicalFirstFactor i t f f' hi ht comm F) ≫
            squareTransport f'.fSharpInverseImage i.fSharp (inverseImageBaseReduction t f')
              (inverseImageReducedStructureMap i t f f' comm)
              (ringMap_fSharpInverseImage_comp_fSharp i t f f' comm)
              (((sheafTensor.{u',
                v', w, w, w} ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
                hi.I)) ≫ canonicalMap i t f f' hi ht comm F F' q hq hqex from by
        rw [hassoc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]]
      infer_instance
    have : Mono (canonicalSecondFactor i hi F F' q hq hqex) :=
      mono_of_mono_restrictScalars_map
        (Stacks.FlatChangeOfRings.ringSheafMap f'.fSharpInverseImage) _ inferInstance
    exact isIso_of_mono_of_epi _

end FirstFactor

end Deformation.ToposThickening

end


