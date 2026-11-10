module

public import StacksFrontier.Deformation.ToposThickening.RingedToposLiftDiagramMorphisms
public import StacksFrontier.Deformation.ToposThickening.LiftingDerivationGroup
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivations
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedRhoEquivSupplement
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivationTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08UG, clause (2): the morphisms form a principal homogeneous space

For the general diagram `Deformation.ToposThickening.RingedToposLiftDiagram` of
[Stacks Project, Tag 08UG], the morphisms `(Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` fitting into (08UH)
compatibly with `ν` form a principal homogeneous space under
`Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)`, as soon as there is one.

The proof is the source's reduction. Those morphisms are the lifts of the one-site diagram on
`𝒞₂` (`RingedToposLiftDiagram.compatibleLiftEquiv`), on which
`Hom_{g⁻¹𝒪₁}(Ω_{g⁻¹𝒪₁/g⁻¹f₁⁻¹𝒪_{ℬ₁}}, 𝒢₂)` acts simply transitively
(`Deformation.ToposThickening.FirstOrderLiftDiagram.existsUnique_translateHom`). That group is
the source's group, by the two identifications of its display:
`Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂) = Hom_{g⁻¹𝒪₁}(g⁻¹Ω_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)` is the adjunction
`g⁻¹ ⊣ g_*` on sheaves of modules (Stacks 03D3), and
`g⁻¹Ω_{𝒪₁/𝒪_{ℬ₁}} = Ω_{g⁻¹𝒪₁/g⁻¹f₁⁻¹𝒪_{ℬ₁}}` is Modules on Sites, Lemma 08TQ.

## Main definitions

* `Deformation.ToposThickening.RingedToposLiftDiagram.differentials₁`: `Ω_{𝒪₁/𝒪_{ℬ₁}}`, the
  sheaf of relative differentials of `f₁^♯ : f₁⁻¹𝒪_{ℬ₁} ⟶ 𝒪₁`.
* `RingedToposLiftDiagram.pushedIdeal₁`: `g_*𝒢₂`, as an `𝒪₁`-module.
* `RingedToposLiftDiagram.actingGroupEquiv`: the identification of
  `Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)` with the acting group of the one-site diagram.
* `RingedToposLiftDiagram.translate`: the action on the morphisms fitting into (08UH).
* `RingedToposLiftDiagram.pullbackDifferentialsHomEquiv` and `RingedToposLiftDiagram.extZeroEquiv`:
  the two further groups of the source's display,
  `Hom_{𝒪₂}(g^*Ω_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)` and `Ext⁰_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`, identified with
  `Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)` by additive equivalences.

## Main results

* `RingedToposLiftDiagram.translate_zero`, `translate_add`, `existsUnique_translate`:
  **Stacks 08UG, clause (2)**.

## Implementation notes

`g_*𝒢₂` is the pushforward of sheaves of modules along a morphism of ringed topoi of
Stacks 03D6, `Stacks.Sheaves.RingedToposModules.pushforwardModules`: the direct image of `𝒢₂`
read as a `g⁻¹𝒪₁`-module through `g^♯`. The first equality of the source's display,
`Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂) = Hom_{𝒪₂}(g^*Ω_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`, is
`RingedToposLiftDiagram.pullbackDifferentialsHomEquiv`.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.RingedToposModules (inverseImageModules directImageModules
  inverseImageAdjDirectImageModules inverseImageDifferentialsIso)

universe u

namespace Deformation.ToposThickening.RingedToposLiftDiagram

variable {X₁ X₂ B₁ B₂ : RingedTopos.{u, u, u}}
  [X₁.J.HasSheafCompose (forget RingCat.{u})] [X₂.J.HasSheafCompose (forget RingCat.{u})]
  [B₁.J.HasSheafCompose (forget RingCat.{u})] [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{u})] [X₂.J.HasSheafCompose (forget CommRingCat.{u})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X₂.J AddCommGrpCat.{u}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : RingedToposLiftDiagram X₁ X₂ B₁ B₂)

/-- `Ω_{𝒪₁/𝒪_{ℬ₁}}`: the sheaf of relative differentials of `f₁^♯ : f₁⁻¹𝒪_{ℬ₁} ⟶ 𝒪₁` on `𝒞₁`. -/
abbrev differentials₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) :=
  moduleOfDifferentialsOfSite.{u, u, u, u} ((inverseImageCommRingFunctor D.S₁.f.toToposHom).obj
    B₁.O) X₁.O D.S₁.f.fSharpInverseImage

/-- `g_*𝒢₂`, the pushforward of the `𝒪₂`-module `𝒢₂` along the morphism of ringed topoi `g`
(Stacks 03D6, part (1)): the direct image of `𝒢₂` read as a `g⁻¹𝒪₁`-module through `g^♯`. -/
abbrev pushedIdeal₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) :=
  (Stacks.Sheaves.RingedToposModules.pushforwardModules D.g.toRingedToposModulesHom).obj D.S₂.G

/-- **The identification of the source's acting group**:
`Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂) = Hom_{g⁻¹𝒪₁}(g⁻¹Ω_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`
`= Hom_{g⁻¹𝒪₁}(Ω_{g⁻¹𝒪₁/g⁻¹f₁⁻¹𝒪_{ℬ₁}}, 𝒢₂)`, by the adjunction `g⁻¹ ⊣ g_*` of Stacks 03D3 and
the identification `g⁻¹Ω ≅ Ω` of Stacks 08TQ. The target is the acting group of the one-site
diagram. -/
def actingGroupEquiv :
    (differentials₁ D ⟶ pushedIdeal₁ D) ≃+
      (FirstOrderLiftDiagram.frontDifferentials.{u, u, u} (toFirstOrderLiftDiagram D) ⟶
        FirstOrderLiftDiagram.pushedIdeal.{u, u, u} (toFirstOrderLiftDiagram D)) :=
  haveI : (inverseImageModules D.g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)).Additive :=
    CategoryTheory.Sheaf.inverseImageTargetModules_additive.{u, u, u, u, u, u} X₂.J X₁.J
      D.g.toToposHom (B := X₁.O)
  ((inverseImageAdjDirectImageModules D.g.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)).homAddEquiv _ _).symm.trans
    (Stacks.Cohomology.precompAddEquiv (inverseImageDifferentialsIso.{u, u, u, u, u, u}
      D.g.toToposHom D.S₁.f.fSharpInverseImage))

/-- **The first equality of the display of Stacks 08UG, clause (2)**:
`Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂) = Hom_{𝒪₂}(g^*Ω_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`, the adjunction `g^* ⊣ g_*` of
sheaves of modules of Stacks 03D7. -/
@[stacks 08UG "clause (2), the first equality of the display: Hom_{O_1}(Omega_{O_1/O_{B_1}}, \
g_* G_2) = Hom_{O_2}(g^* Omega_{O_1/O_{B_1}}, G_2), as an additive equivalence, for genuine \
morphisms of ringed topoi"]
def pullbackDifferentialsHomEquiv :
    (D.g.toRingedToposModulesHom.pullbackModules.obj (differentials₁ D) ⟶
      (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O) from D.S₂.G)) ≃+
      (differentials₁ D ⟶ pushedIdeal₁ D) :=
  haveI := (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    D.g.toRingedToposModulesHom).left_adjoint_additive
  (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    D.g.toRingedToposModulesHom).homAddEquiv _ _

variable [HasSheafify X₁.J AddCommGrpCat.{u}] [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X₂.J AddCommGrpCat.{u}]
  [HasWeakSheafify X₁.J CommRingCat.{u}] [HasWeakSheafify X₂.J CommRingCat.{u}] in
/-- **The second equality of the display of Stacks 08UG, clause (2)**:
`Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂) = Ext⁰_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`, as an additive
equivalence: Stacks 0GQ8 in degree `0`, `Ext⁰(NL, 𝒢) = Hom(Ω, 𝒢)` on `𝒞₂`, and the identification
`actingGroupEquiv`. `Lg^*` is the derived pullback of Tag 06YY, at the model
`HasDerivedCategory.standard` at which it is constructed. -/
@[stacks 08UG "clause (2), the second equality of the display: Ext^0_{O_2}(Lg^* \
NL_{O_1/O_{B_1}}, G_2) = Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2), as an additive equivalence, \
for genuine morphisms of ringed topoi"]
def extZeroEquiv :
    @DerivedCategory.Ext _ _ _ (HasDerivedCategory.standard _)
      ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback D.g).obj
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj
          (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X₁.J
            ((inverseImageCommRingFunctor D.S₁.f.toToposHom).obj B₁.O) X₁.O
            D.S₁.f.fSharpInverseImage)))
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj D.S₂.G) 0 ≃+
      (differentials₁ D ⟶ pushedIdeal₁ D) :=
  (LiftingMorphismDerived.extZeroDifferentialsAddEquiv (f := D.S₁.f) (G := D.S₂.G) D.g).trans
    (actingGroupEquiv D).symm

/-- **The action of `Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)` on the morphisms fitting into (08UH)
compatibly with `ν`**: a homomorphism `a` translates the comorphism `φ : g⁻¹𝒪'₁ ⟶ 𝒪'₂` of such
a morphism by the derivation `g⁻¹𝒪'₁ ⟶ g⁻¹𝒪₁ ⟶ g⁻¹Ω_{𝒪₁/𝒪_{ℬ₁}} ⟶ 𝒢₂` adjoint to `a`. -/
def translate (p : CompatibleLift D) (a : differentials₁ D ⟶ pushedIdeal₁ D) :
    CompatibleLift D :=
  (compatibleLiftEquiv D).symm (FirstOrderLiftDiagram.translateHom.{u, u, u}
    (toFirstOrderLiftDiagram D) (compatibleLiftEquiv D p) (actingGroupEquiv D a))

omit [HasWeakSheafify X₂.J AddCommGrpCat.{u}]
  [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks Project, Tag 08UG**, clause (2): the zero homomorphism acts trivially. -/
@[stacks 08UG "clause (2), for genuine morphisms of ringed topoi: triviality of the action of 0 \
in the principal homogeneous space structure under Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2)"]
theorem translate_zero (p : CompatibleLift D) : translate D p 0 = p := by
  rw [translate, map_zero, FirstOrderLiftDiagram.translateHom_zero.{u, u, u},
    Equiv.symm_apply_apply]

omit [HasWeakSheafify X₂.J AddCommGrpCat.{u}]
  [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks Project, Tag 08UG**, clause (2): the action is additive. -/
@[stacks 08UG "clause (2), for genuine morphisms of ringed topoi: additivity of the action in \
the principal homogeneous space structure under Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2)"]
theorem translate_add (p : CompatibleLift D) (a b : differentials₁ D ⟶ pushedIdeal₁ D) :
    translate D (translate D p a) b = translate D p (a + b) := by
  rw [translate, translate, translate, Equiv.apply_symm_apply,
    FirstOrderLiftDiagram.translateHom_add.{u, u, u}, map_add]

omit [HasWeakSheafify X₂.J AddCommGrpCat.{u}]
  [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks Project, Tag 08UG**, clause (2). If there is a morphism of ringed topoi
`(Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` fitting into (08UH) compatibly with `ν`, the set of all such
morphisms is a principal homogeneous space under `Hom_{𝒪₁}(Ω_{𝒪₁/𝒪_{ℬ₁}}, g_*𝒢₂)`: any one of
them is carried to any other by exactly one homomorphism. -/
@[stacks 08UG "clause (2) for genuine morphisms of ringed topoi between four arbitrary ringed \
topoi: the morphisms fitting into (08UH) compatibly with nu are a principal homogeneous space \
under Hom_{O_1}(Omega_{O_1/O_{B_1}}, g_* G_2), with the action translate_zero, translate_add"]
theorem existsUnique_translate (p q : CompatibleLift D) :
    ∃! a : differentials₁ D ⟶ pushedIdeal₁ D, translate D p a = q := by
  obtain ⟨b, hb, hb'⟩ := FirstOrderLiftDiagram.existsUnique_translateHom.{u, u, u}
    (toFirstOrderLiftDiagram D) (compatibleLiftEquiv D p) (compatibleLiftEquiv D q)
  refine ⟨(actingGroupEquiv D).symm b, ?_, fun a ha => ?_⟩
  · change (compatibleLiftEquiv D).symm (FirstOrderLiftDiagram.translateHom.{u, u, u}
      (toFirstOrderLiftDiagram D) (compatibleLiftEquiv D p)
        (actingGroupEquiv D ((actingGroupEquiv D).symm b))) = q
    rw [AddEquiv.apply_symm_apply, hb, Equiv.symm_apply_apply]
  · refine (AddEquiv.eq_symm_apply _).2 (hb' _ ?_)
    subst ha
    exact ((compatibleLiftEquiv D).apply_symm_apply _).symm

end Deformation.ToposThickening.RingedToposLiftDiagram

end
