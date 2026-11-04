module

public import StacksFrontier.CategoryTheory.Sites.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact
public import StacksFrontier.CategoryTheory.Sites.Point.SkyscraperStalkSplitting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.ConstantInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a constant sheaf of abelian groups is constant

Let `f : Sh(C, J) ⟶ Sh(D, K)` be a morphism of topoi. Its inverse image acts on sheaves of
abelian groups through `CategoryTheory.Sites.abelianInverseImage`: the additive operations of an
abelian sheaf are read as the operations of an internal commutative group object in sheaves of
sets, the left exact `f⁻¹` carries those to operations again, and the result is read back
sectionwise. This file proves that if both sites have a final object then that functor carries
the constant abelian sheaf on an abelian group to the constant abelian sheaf on that group, and
hence carries constant abelian sheaves to constant abelian sheaves.

The proof is the one used for sheaves of sets in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.ConstantInverseImage`:
both `C_K ⋙ f⁻¹` and `C_J` are left adjoint to the global sections functor of `C`, by
`CategoryTheory.constantSheafAdj` and by
`Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward`, so uniqueness of left
adjoints identifies them once the two right adjoints are identified. What that costs over the
case of sets is the identification `f_* ⋙ Γ_D ≅ Γ_C` for abelian sheaves, and the point of the
file is that it needs no new arithmetic: the comparison of sections is the one already proved
for sheaves of sets, `Stacks.ConstantSheaf.pushforwardSectionsIso`, and it is carried to abelian
groups by `CategoryTheory.Functor.mapCommGrpNatIso`, which makes every natural isomorphism of
finite-product-preserving functors into an isomorphism of the induced functors on commutative
group objects. Additivity is therefore never checked by hand.

The one genuinely new comparison is `Stacks.Sites.AbelianPullback.evaluationInternalIso`: the
abelian group of sections of an abelian presheaf over an object is the group of sections of its
internalization. It is the identity on elements, and additive because the monoidal structure of
an evaluation functor is computed on elements, which is
`CategoryTheory.Functor.Monoidal.μ_fst` and `.μ_snd`.

## Main definitions

* `Stacks.Sites.AbelianPullback.evaluationInternalIso` — evaluating an abelian presheaf commutes
  with internalizing its group operations.
* `Stacks.Sites.AbelianPullback.sectionsInternalIso` — the same for the sections of an abelian
  sheaf over an object of the site.
* `Stacks.ConstantSheaf.abelianPushforwardSectionsIso` — global sections on `D` of the direct
  image of an abelian sheaf are global sections on `C`.

## Main results

* `MorphismOfTopoi.abelianConstantSheafIso` — **Stacks 093R** for a single constant sheaf of
  abelian groups: `C_K ⋙ f⁻¹ ≅ C_J` on `AddCommGrpCat`.
* `MorphismOfTopoi.isConstant_abelianInverseImage` — **Stacks 093R** for constant sheaves of
  abelian groups: the inverse image of a constant abelian sheaf is constant.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf
open Stacks.Topos.Skyscraper

universe w v u v' u'

namespace Stacks.Sites.AbelianPullback

attribute [local instance] cartesianPresheafTypes braidedPresheafTypes cartesianSheafTypes
  braidedSheafTypes braidedSheafToPresheafTypes

/-- Evaluation of presheaves of sets at an object preserves finite products, hence is braided for
the pointwise cartesian monoidal structures. -/
local instance braidedEvaluationTypes {C : Type u} [Category.{v} C] (U : Cᵒᵖ) :
    ((evaluation Cᵒᵖ (Type w)).obj U).Braided :=
  .ofChosenFiniteProducts _

variable {C : Type u} [Category.{v} C]

/-- Evaluating an abelian presheaf at an object commutes with internalizing its group
operations: the abelian group of sections over `U` is the commutative group object of sections
over `U` of the internalization. The comparison is the identity on elements, and it is additive
because the monoidal structure of an evaluation functor is computed on elements. -/
public def evaluationInternalIso (U : Cᵒᵖ) :
    presheafCommGrp ⋙ ((evaluation Cᵒᵖ (Type w)).obj U).mapCommGrp ⋙
        commGrpAddEquivalence.functor ≅
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U := by
  refine NatIso.ofComponents (fun A => AddEquiv.toAddCommGrpIso
    { toFun := Additive.toMul
      invFun := Additive.ofMul
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := ?_ }) ?_
  · intro x y
    let A' := presheafCommGrp.obj A
    let ev := (evaluation Cᵒᵖ (Type w)).obj U
    let : ev.Monoidal := (inferInstance : ev.Braided).toMonoidal
    let add := @Add.add (A.obj U) inferInstance
    change add ((Functor.LaxMonoidal.μ ev A'.X A'.X ≫ ev.map
        (CartesianMonoidalCategory.fst A'.X A'.X)) (x, y))
      ((Functor.LaxMonoidal.μ ev A'.X A'.X ≫ ev.map
        (CartesianMonoidalCategory.snd A'.X A'.X)) (x, y)) = add x y
    exact congrArg₂ add
      (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        (Functor.Monoidal.μ_fst ev A'.X A'.X) (x, y))
      (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        (Functor.Monoidal.μ_snd ev A'.X A'.X) (x, y))
  · intro A B g
    rfl

/-- The sections of an abelian sheaf over an object of the site are the sections of its
internalization: pass to the underlying presheaf with `sheafToPresheafInternalIso` and evaluate
with `evaluationInternalIso`. -/
public def sectionsInternalIso (J : GrothendieckTopology C) (T : C) :
    (sheafSections J AddCommGrpCat.{w}).obj (op T) ≅
      internalSheaf J ⋙ (sheafToPresheaf J (Type w) ⋙
        (evaluation Cᵒᵖ (Type w)).obj (op T)).mapCommGrp ⋙ commGrpAddEquivalence.functor :=
  Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{w})
      (evaluationInternalIso (op T)).symm ≪≫
    Functor.isoWhiskerRight (sheafToPresheafInternalIso J)
      (((evaluation Cᵒᵖ (Type w)).obj (op T)).mapCommGrp ⋙ commGrpAddEquivalence.functor) ≪≫
    Functor.isoWhiskerLeft (internalSheaf J)
      (Functor.isoWhiskerRight Functor.mapCommGrpCompIso.symm commGrpAddEquivalence.functor)

end Stacks.Sites.AbelianPullback

namespace Stacks.ConstantSheaf

open Stacks.Sites.AbelianPullback

attribute [local instance] cartesianPresheafTypes braidedPresheafTypes cartesianSheafTypes
  braidedSheafTypes braidedSheafToPresheafTypes braidedEvaluationTypes

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- The direct image functor of a morphism of topoi preserves limits indexed by categories in
`Type`. -/
local instance : PreservesLimitsOfSize.{0, 0} f.pushforward :=
  f.adj.rightAdjoint_preservesLimits

/-- The direct image functor of a morphism of topoi preserves finite limits. -/
local instance : PreservesFiniteLimits f.pushforward := inferInstance

/-- The direct image functor of a morphism of topoi is braided monoidal for the cartesian
monoidal structures. -/
local instance : f.pushforward.Braided := .ofChosenFiniteProducts _

/-- The inverse image functor of a morphism of topoi preserves finite limits. -/
local instance : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits

/-- **Global sections of the direct image of an abelian sheaf.** If both sites have a final
object, the abelian group of global sections on `D` of the direct image of an abelian sheaf is
its abelian group of global sections on `C`, naturally in the sheaf.

Both sides are read on internal commutative group objects by
`Stacks.Sites.AbelianPullback.sectionsInternalIso`, where the statement becomes the image under
`CategoryTheory.Functor.mapCommGrp` of the comparison already proved for sheaves of sets,
`Stacks.ConstantSheaf.pushforwardSectionsIso`. No additivity has to be checked. -/
public def abelianPushforwardSectionsIso {T : C} (hT : IsTerminal T)
    {T' : D} (hT' : IsTerminal T') :
    Stacks.Topos.AbelianPushforward.abelianPushforward J f ⋙
        (sheafSections K AddCommGrpCat.{w}).obj (op T') ≅
      (sheafSections J AddCommGrpCat.{w}).obj (op T) := by
  let ps : f.pushforward ⋙ (sheafToPresheaf K (Type w) ⋙ (evaluation Dᵒᵖ (Type w)).obj (op T')) ≅
      sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj (op T) :=
    pushforwardSectionsIso f.adj (inverseImageTerminalIso f.inverseImage) hT hT'
  exact Functor.isoWhiskerLeft (Stacks.Topos.AbelianPushforward.abelianPushforward J f)
      (sectionsInternalIso K T') ≪≫
    Functor.isoWhiskerLeft (internalSheaf J ⋙ f.pushforward.mapCommGrp)
      (Functor.isoWhiskerRight (externalInternalIso K)
        ((sheafToPresheaf K (Type w) ⋙ (evaluation Dᵒᵖ (Type w)).obj (op T')).mapCommGrp ⋙
          commGrpAddEquivalence.functor)) ≪≫
    Functor.isoWhiskerLeft (internalSheaf J)
      (Functor.isoWhiskerRight Functor.mapCommGrpCompIso.symm commGrpAddEquivalence.functor) ≪≫
    Functor.isoWhiskerLeft (internalSheaf J)
      (Functor.isoWhiskerRight (Functor.mapCommGrpNatIso ps) commGrpAddEquivalence.functor) ≪≫
    (sectionsInternalIso J T).symm

end Stacks.ConstantSheaf

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  {T : C} (hT : IsTerminal T) {T' : D} (hT' : IsTerminal T')

/-- **Stacks 093R, the constant abelian case.** The inverse image of a morphism of topoi between
the topoi of sheaves of sets on two sites with final objects carries the constant sheaf of
abelian groups on an abelian group to the constant sheaf of abelian groups on that group.

Both `C_K ⋙ f⁻¹` and `C_J` are left adjoint to the global sections functor of `C`, the first by
`Stacks.ConstantSheaf.abelianPushforwardSectionsIso`, so they agree. -/
public def abelianConstantSheafIso :
    constantSheaf K AddCommGrpCat.{w} ⋙ CategoryTheory.Sites.abelianInverseImage f ≅
      constantSheaf J AddCommGrpCat.{w} :=
  (((constantSheafAdj K AddCommGrpCat.{w} hT').comp
      (Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward J f)).ofNatIsoRight
    (Stacks.ConstantSheaf.abelianPushforwardSectionsIso f hT hT')).leftAdjointUniq
      (constantSheafAdj J AddCommGrpCat.{w} hT)

include f hT hT' in
/-- **Stacks 093R, the constant abelian case.** The inverse image of a constant sheaf of abelian
groups along a morphism of topoi is constant. -/
@[stacks 093R "constant sheaves of abelian groups, for an arbitrary morphism of topoi"]
public lemma isConstant_abelianInverseImage (G : Sheaf K AddCommGrpCat.{w}) [Sheaf.IsConstant K G] :
    Sheaf.IsConstant J ((CategoryTheory.Sites.abelianInverseImage f).obj G) := by
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant K G
  exact Sheaf.isConstant_of_iso J
    ((CategoryTheory.Sites.abelianInverseImage f).mapIso e.symm ≪≫
      (abelianConstantSheafIso f hT hT').app E)

end MorphismOfTopoi

end
