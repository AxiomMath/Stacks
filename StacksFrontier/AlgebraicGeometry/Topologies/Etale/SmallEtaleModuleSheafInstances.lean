module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafification and inverse image for module sheaves on small étale sites

Let `B` be a big étale site with schemes in `Type u`, let `Λ` be a ring, and let the module
sections live in a universe `w` containing `u`. This file proves the three existence statements
on which constructibility of sheaves of `Λ`-modules on small étale sites (Stacks 03RW) and the
constructible derived category (Stacks 095W) are formulated:

* presheaves of `Λ`-modules on the small étale site `S_ét` admit a sheafification;
* the same holds on every slice `S_ét / V` with the localized topology;
* for every morphism `f : T ⟶ S` the direct image along small étale base change is a right
  adjoint, so the inverse image `f⁻¹` exists.

## Main results

* `CategoryTheory.hasSheafify_moduleCat_of_essentiallySmall`: presheaves of `Λ`-modules with
  sections in `Type w` on a site which is essentially small at `w` admit a sheafification.
* `CategoryTheory.isRightAdjoint_sheafPushforwardContinuous_moduleCat_of_essentiallySmall`: for a
  continuous functor between sites which are essentially small at `w`, the direct image of
  sheaves of `Λ`-modules with sections in `Type w` has a left adjoint.
* `AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat_of_univLE`,
  `AlgebraicGeometry.SmallEtale.hasSheafify_over_moduleCat_of_univLE` and
  `AlgebraicGeometry.smallEtaleBaseChange_isRightAdjoint_sheafPushforward_moduleCat`: the three
  statements above on small étale sites, as instances.

## Implementation notes

The small étale category of Stacks 021B has objects in `Type (u + 1)` and morphisms in `Type u`,
and it is essentially small at `u` (`AlgebraicGeometry.SmallEtale.essentiallySmall`), hence at
every `w` with `UnivLE.{u, w}`. Sheafification is transported from a small model by
`CategoryTheory.hasSheafifyEssentiallySmallSite`, where it is the plus construction for
`Stacks.ModuleSheaf.hasSheafify_moduleCat`. The inverse image is the sheafified left Kan
extension `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`; the Kan extension is
pointwise, each comma category `CostructuredArrow G.op Y` being essentially small at `w`, so its
colimits exist in `ModuleCat.{w} Λ`.

The universe hypothesis `UnivLE.{u, w}` is the only input, and it is what the statements need:
the covering sieves of an étale scheme can have as many members as `Type u` allows, so the
sections of a sheafification need not fit in a smaller universe. Instance search discharges it
for `w = max u w'` through `UnivLE.self` and `univLE_of_max`.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r v u v' u'

namespace CategoryTheory

/-- Presheaves of `Λ`-modules with sections in `Type w` on a site which is essentially small at
`w` admit a sheafification, and it is left exact. It is computed on a small model of the site by
the plus construction and transported back along the equivalence. -/
public theorem hasSheafify_moduleCat_of_essentiallySmall {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{w} C] (Λ : Type r) [Ring Λ] :
    HasSheafify J (ModuleCat.{w} Λ) :=
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J) (ModuleCat.{w} Λ) :=
    Stacks.ModuleSheaf.hasSheafify_moduleCat.{w} Λ _
  hasSheafifyEssentiallySmallSite.{v, w, u, max r (w + 1), w} J _

/-- For a continuous functor `G` between sites which are both essentially small at `w`, the
direct image of sheaves of `Λ`-modules with sections in `Type w` is a right adjoint. Its left
adjoint is the sheafification of the pointwise left Kan extension along `G.op`, which exists
because every comma category `CostructuredArrow G.op Y` is essentially small at `w`. -/
@[sga "4 Vbis 1.3.7" "special case"]
public theorem isRightAdjoint_sheafPushforwardContinuous_moduleCat_of_essentiallySmall
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (G : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] (Λ : Type r) [Ring Λ] :
    (G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J K).IsRightAdjoint := by
  have := hasSheafify_moduleCat_of_essentiallySmall.{w} K Λ
  have : ∀ F : Cᵒᵖ ⥤ ModuleCat.{w} Λ, G.op.HasLeftKanExtension F := fun F => by
    have : G.op.HasPointwiseLeftKanExtension F := fun Y =>
      have := hasColimitsOfShape_of_essentiallySmall.{w} (CostructuredArrow G.op Y)
        (ModuleCat.{w} Λ)
      HasColimitsOfShape.has_colimit _
    infer_instance
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G (ModuleCat.{w} Λ)
    J K).isRightAdjoint

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- The small étale category of `S` is essentially small at every universe containing `u`: it is
essentially small at `u`, and both the isomorphism classes and the morphism types are then
`w`-small. -/
public theorem SmallEtale.essentiallySmall_of_univLE [UnivLE.{u, w}] (S : B.Scheme) :
    EssentiallySmall.{w} (SmallEtale B S.obj S.property) := by
  obtain ⟨hskel, -⟩ := (essentiallySmall_iff.{u} (SmallEtale B S.obj S.property)).mp inferInstance
  exact (essentiallySmall_iff _).mpr ⟨Small.trans_univLE.{u, w} _, inferInstance⟩

/-- Presheaves of `Λ`-modules on the small étale site of `S` admit a sheafification, for module
sections in any universe containing that of the schemes. -/
public instance SmallEtale.hasSheafify_moduleCat_of_univLE [UnivLE.{u, w}] (S : B.Scheme) :
    HasSheafify (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} Λ) :=
  have := SmallEtale.essentiallySmall_of_univLE.{w} B S
  hasSheafify_moduleCat_of_essentiallySmall.{w} _ Λ

/-- Presheaves of `Λ`-modules on the slice of the small étale site of `S` over an étale
`S`-scheme `V`, with the localized topology, admit a sheafification, for module sections in any
universe containing that of the schemes. -/
public instance SmallEtale.hasSheafify_over_moduleCat_of_univLE [UnivLE.{u, w}] (S : B.Scheme)
    (V : SmallEtale B S.obj S.property) :
    HasSheafify ((SmallEtale.topology B S.obj S.property).over V) (ModuleCat.{w} Λ) :=
  have := SmallEtale.essentiallySmall_of_univLE.{w} B S
  have := Stacks.essentiallySmall_over.{w} V
  hasSheafify_moduleCat_of_essentiallySmall.{w} _ Λ

/-- For a morphism `f : T ⟶ S` of the big étale site, the direct image of sheaves of
`Λ`-modules along small étale base change `S_ét → T_ét` is a right adjoint: the inverse image
`f⁻¹` exists, for module sections in any universe containing that of the schemes. -/
public instance smallEtaleBaseChange_isRightAdjoint_sheafPushforward_moduleCat [UnivLE.{u, w}]
    {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  have := SmallEtale.essentiallySmall_of_univLE.{w} B S
  have := SmallEtale.essentiallySmall_of_univLE.{w} B T
  isRightAdjoint_sheafPushforwardContinuous_moduleCat_of_essentiallySmall.{w} _ _ _ Λ

end AlgebraicGeometry
