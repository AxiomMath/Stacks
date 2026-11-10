module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafifiedDifferential
public import StacksFrontier.RingTheory.Koszul.IteratedContraction

/-!
# Two Koszul differentials anticommute

A functional `φ` on a module, on a presheaf of modules, or on a sheaf of modules gives rise to a
Koszul differential on the corresponding exterior algebra: contraction by `φ`. That differential
squares to zero. This file records the finer fact that the differentials of *two* functionals
anticommute,

`d_φ ∘ d_ψ = - d_ψ ∘ d_φ`,

of which squaring to zero is the case `ψ = φ` in characteristic different from two, but which does
not follow from it in general.

The statement is proved once, at the level of the exterior algebra of a module, where it is
`Koszul.contraction_contraction_comm` of
`StacksFrontier.RingTheory.Koszul.IteratedContraction`, and then carried through the two gradings
and the sheafification exactly as the laws of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafifiedDifferential` are: a graded version on the
`ℤ`-indexed exterior powers, a sectionwise version on the exterior powers of a presheaf of
modules, and a version on the degreewise sheafification.

## Main results

* `Koszul.intPowD_comp_intPowD_comm`: **the graded Koszul differentials of two functionals
  anticommute** on the `ℤ`-indexed exterior powers of a module.
* `PresheafOfModules.exteriorKoszulD_comp_exteriorKoszulD_comm` and
  `PresheafOfModules.exteriorKoszulDOf_comp_exteriorKoszulDOf_comm`: the same for the sectionwise
  exterior powers of a presheaf of modules, in the consecutive and in the independently named
  degrees.
* `SheafOfModules.koszulD_comp_koszulD_comm`: **the Koszul differentials of two functionals on
  the exterior algebra `⋀(F)` of a sheaf of modules anticommute.**

## Implementation notes

**Why this is not a consequence of squaring to zero.** Over a ring in which `2` is invertible one
recovers anticommutativity from `d_{φ+ψ} ∘ d_{φ+ψ} = 0` by polarization, since contraction is
linear in the functional. Over a general commutative ring that argument gives only
`d_φ d_ψ + d_ψ d_φ = 0`, which is the assertion, so nothing is lost; but it is not obtained from
the squaring law of a single functional, and `CliffordAlgebra.contractLeft_comm` proves it
directly by the same induction (`CliffordAlgebra.left_induction`) that proves the squaring law.

**The negation on the right-hand side is the negation of a morphism, not of a section.** At each
of the three levels the two sides are morphisms in an additive category, and each proof has to
move that negation inside the evaluation on local sections. At the graded module level this is
`LinearMap.neg_apply` followed by `Submodule.coe_neg`. At the presheaf and sheaf levels the
additive structure on morphisms is the pointwise one, so evaluating a negated morphism on a
section is `rfl`; the sheaf-level proof states that step as an explicit `rfl`-proved rewrite
rather than leaving it to `simp`, because the piece of `⋀(F)` is a sheafification and `simp` has
no lemma for its negation. The remaining negation is moved across the sheafification unit by
`map_neg`, the unit being a morphism of modules on sections.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules Stacks Stacks.GradedAlgebra

open scoped ExteriorAlgebra

/-! ## The exterior algebra of a module -/

namespace Koszul

universe u v

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- **The graded Koszul differentials of two functionals anticommute.** On the `ℤ`-indexed
exterior power of degree `n + 2` the composite of the differential of `ψ` with that of `φ` is the
negative of the composite taken in the other order. For `ψ = φ` the two sides are equal to each
other, and each is zero by `Koszul.intPowD_comp_intPowD`; that identity is not a consequence of
this one. -/
theorem intPowD_comp_intPowD_comm (φ ψ : Module.Dual R E) (n : ℤ) :
    (intPowD φ n).comp (intPowD ψ (n + 1)) = -(intPowD ψ n).comp (intPowD φ (n + 1)) :=
  LinearMap.ext fun x => Subtype.ext <| by
    rw [LinearMap.neg_apply, Submodule.coe_neg]
    exact contraction_contraction_comm φ ψ (x : ExteriorAlgebra R E)

end Koszul

/-! ## The sectionwise exterior algebra of a presheaf of modules -/

namespace PresheafOfModules

universe v u w a

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- **The sectionwise Koszul differentials of two functionals anticommute**, in the consecutive
degrees in which the differential is defined. -/
theorem exteriorKoszulD_comp_exteriorKoszulD_comm
    (φ ψ : ExteriorFunctional.{v, u, w, a} F) (n : ℤ) :
    exteriorKoszulD F ψ (n + 1) ≫ exteriorKoszulD F φ n =
      -(exteriorKoszulD F φ (n + 1) ≫ exteriorKoszulD F ψ n) := by
  refine hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine exteriorAlgebraPieceVal_injective n F X ?_
  change Koszul.contraction (φ.dual X) (Koszul.contraction (ψ.dual X)
      (exteriorAlgebraPieceVal (n + 1 + 1) F X x)) = _
  rw [Koszul.contraction_contraction_comm]
  rfl

variable {F}

/-- **The sectionwise Koszul differentials of two functionals anticommute**, with the three
degrees named independently and the identities relating them taken as hypotheses, as in
`PresheafOfModules.exteriorKoszulDOf`. -/
theorem exteriorKoszulDOf_comp_exteriorKoszulDOf_comm
    (φ ψ : ExteriorFunctional.{v, u, w, a} F) {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    exteriorKoszulDOf ψ h ≫ exteriorKoszulDOf φ h' =
      -(exteriorKoszulDOf φ h ≫ exteriorKoszulDOf ψ h') := by
  subst h'
  subst h
  exact exteriorKoszulD_comp_exteriorKoszulD_comm F φ ψ r

end PresheafOfModules

/-! ## The exterior algebra of a sheaf of modules -/

namespace SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))
  (φ ψ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val)

/-- **The Koszul differentials of two functionals on the exterior algebra `⋀(F)` of a sheaf of
modules anticommute.** Each side is a morphism from the homogeneous piece of degree `p` to the one
of degree `r`, and the identity is checked on the unit images of sectionwise exterior forms, which
determine a morphism out of a degreewise sheafification. -/
theorem koszulD_comp_koszulD_comm {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    koszulD J F ψ h ≫ koszulD J F φ h' = -(koszulD J F φ h ≫ koszulD J F ψ h') := by
  refine sheafification_hom_ext_apply (𝟙 (toRingCat J Osharp).obj) fun X s => ?_
  have key : ∀ a b : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val,
      (koszulD J F a h').val.app X ((koszulD J F b h).val.app X (exteriorUnit J F p X s)) =
        exteriorUnit J F r X (Hom.app (PresheafOfModules.exteriorKoszulDOf b h ≫
          PresheafOfModules.exteriorKoszulDOf a h') X s) := fun a b => by
    rw [koszulD_exteriorUnit, koszulD_exteriorUnit, ← PresheafOfModules.comp_app_apply]
  change (koszulD J F φ h').val.app X ((koszulD J F ψ h).val.app X (exteriorUnit J F p X s)) =
    -((koszulD J F ψ h').val.app X ((koszulD J F φ h).val.app X (exteriorUnit J F p X s)))
  rw [key, key, PresheafOfModules.exteriorKoszulDOf_comp_exteriorKoszulDOf_comm φ ψ h h',
    show Hom.app (-(PresheafOfModules.exteriorKoszulDOf φ h ≫
          PresheafOfModules.exteriorKoszulDOf ψ h')) X s =
        -(Hom.app (PresheafOfModules.exteriorKoszulDOf φ h ≫
          PresheafOfModules.exteriorKoszulDOf ψ h') X s) from rfl]
  exact map_neg _ _

end SheafOfModules

end
