module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaFree

/-!
# The projection formula at a cokernel, and at a presented module

Let `h : T ⟶ S` be a morphism of schemes and `G` a sheaf of `𝒪_T`-modules.  The
projection-formula morphism of `StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula`,

`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`,

is a natural transformation in `H` between the two functors recorded in
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaFree`.  That file proves the dévissage
step at a *coproduct*, which needs only quasi-compactness of `h`, and deduces the case of a free
module on the target.  This file proves the dévissage step at a *finite colimit*, in particular at
a *cokernel*, and combines the two: the projection formula holds at every module on the target
that is the cokernel of a morphism of free modules.

The extra input the cokernel step needs, and the coproduct step does not, is right exactness of
the pushforward.  It is taken here as the hypothesis
`PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePushforward h.toLRSHom.toShHom)`,
which is Stacks 01SB in the affine case and is open — see the implementation notes — and is
discharged unconditionally for a **closed immersion** by
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`.  So for a
closed immersion the results below are unconditional.

## Main results

* `CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone`: a natural transformation invertible
  on a diagram is invertible at a colimit of that diagram, provided both functors carry the
  colimit cocone to a colimit cocone.  The two witnesses are explicit arguments.
* In `Stacks.AlgebraicGeometry.ProjectionFormula`,
  `preservesFiniteColimits_tensorPushforwardFunctor` and
  `isColimitMapCoconePullbackTensorPushforwardFunctorFinite`: right exactness of the two sides of
  the projection-formula morphism.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isColimit`: the
  dévissage step at an arbitrary finite colimit.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_cokernel`: the dévissage
  step at a cokernel.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_freePresentation`:
  the projection formula at a module presented as the cokernel of a morphism of free modules.
* In the same namespace,
  `isIso_projectionFormulaMap_of_freePresentation_of_isClosedImmersion`: the same for a closed
  immersion, with no hypothesis on the pushforward.

## Implementation notes

**Why the two witnesses are explicit.**  `CategoryTheory.Limits.isColimitOfPreserves` and
`StacksDraft.CompactDevissage.isIso_app_of_isColimit` take the preservation facts as *instance*
arguments.  Instance search does not find them here, for the reasons recorded in
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaFree`: the pushforward has the two
spellings `AlgebraicGeometry.Scheme.Modules.pushforward` and
`RingedSpaceModuleAdjunction.modulePushforward`, and `CategoryTheory.tensorLeft` is stated at a
second spelling of the ring of scalars.  So the colimit-preservation facts are applied through
their fields, and the dévissage lemma takes the two resulting `IsColimit` terms as explicit
arguments.

**The universe of the shape.**  Tag 05NB
(`Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits`) is stated as
`PreservesColimitsOfSize.{a, z}` with the *shape* type universe `z` tied to the universe of the
module sections, whereas `CategoryTheory.Limits.PreservesFiniteColimits` quantifies over shapes in
`Type 0` — and `CategoryTheory.Limits.WalkingParallelPair`, the shape of a cokernel, lives there.
`CategoryTheory.Limits.PreservesColimitsOfSize.preservesFiniteColimits` crosses that gap, but only
with the two shape universes supplied explicitly: left to inference it reports `failed to infer
universe levels`.

**What is still missing for Stacks 0FZE.**  Two things, and neither is supplied here.

* Right exactness of `modulePushforward` for an *affine* morphism.  **The instance hypothesis
  `[PreservesFiniteColimits (modulePushforward h.toLRSHom.toShHom)]` carried by the three
  declarations below cannot be met for a general affine morphism, and the affine case of Stacks
  0FZE is therefore not reachable through them.**  That functor is on the *full* module
  category, where the statement is false: for `h : 𝔸¹_k ⟶ Spec k`, which is affine, take the
  subsheaf `K ⊆ 𝒪_X` with `K(V) = 𝒪_X(V)` for `x ∉ V` and `K(V) = 0` for `x ∈ V`; then
  `𝒪_X / K` is the skyscraper at `x` with value `𝒪_{X,x}`, and the epimorphism
  `𝒪_X ↠ 𝒪_X / K` becomes `k[t] ↪ k[t]_{(t)}` on global sections, which is not surjective.
  A *closed immersion* is the case where the hypothesis does hold, by
  `Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`, so
  the two unconditional results below are exactly the closed-immersion case and the three
  conditional ones are usable only there.

  The true statement replaces right exactness on all modules by preservation of cokernels *of
  morphisms of quasi-coherent modules*, which is proved in
  `StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact`; the affine case of the
  dévissage built on it is
  `StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAffineCokernel`.  Note also that this
  is *not* an assertion of Stacks 01SB: that
  tag asserts the equivalence `QCoh(𝒪_X) ≃ QCoh(f_*𝒪_X)` and that an `f_*𝒪_X`-module is
  quasi-coherent over `𝒪_S` exactly when it is over `f_*𝒪_X`.  Exactness on quasi-coherent
  modules is a consequence of that equivalence, not one of its clauses — and routing 0FZE
  through the equivalence would be circular, since the equivalence is not cheaper than 0FZE.
* A presentation of a quasi-coherent `H` by free `𝒪_S`-modules.  A quasi-coherent module on a
  general scheme is not globally generated, so no such presentation exists without first making
  the statement local on `S` — the second missing step listed in
  `StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula`.  The results below therefore
  take the presentation as a hypothesis.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace CategoryTheory.NatTrans

variable {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D}

/-- Invertibility of a natural transformation at an object only depends on the isomorphism class
of that object. -/
lemma isIso_app_of_iso (τ : F ⟶ G) {X Y : C} (e : X ≅ Y) (hX : IsIso (τ.app X)) :
    IsIso (τ.app Y) := by
  rw [show τ.app Y = inv (F.map e.hom) ≫ τ.app X ≫ G.map e.hom by
    rw [← τ.naturality e.hom, IsIso.inv_hom_id_assoc]]
  infer_instance

/-- A natural transformation which is an isomorphism at every object of a diagram is an
isomorphism at a colimit of that diagram, provided both functors carry the colimit cocone to a
colimit cocone.

This is `StacksDraft.CompactDevissage.isIso_app_of_isColimit` with the two preservation facts as
*explicit* arguments instead of instance arguments, and the general-shape form of
`CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan`. -/
lemma isIso_app_of_isColimit_mapCocone {J : Type*} [Category J] {Z : J ⥤ C} (τ : F ⟶ G)
    (c : Cocone Z) (hF : IsColimit (F.mapCocone c)) (hG : IsColimit (G.mapCocone c))
    (h : ∀ j, IsIso (τ.app (Z.obj j))) : IsIso (τ.app c.pt) := by
  let e : Z ⋙ F ≅ Z ⋙ G :=
    NatIso.ofComponents (fun j => asIso (τ.app (Z.obj j))) fun _ => τ.naturality _
  have heq : τ.app c.pt = (hF.coconePointsIsoOfNatIso hG e).hom := by
    refine hF.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact τ.naturality (c.ι.app j)
  rw [heq]
  infer_instance

end CategoryTheory.NatTrans

namespace Stacks.AlgebraicGeometry.ProjectionFormula

open RingedSpaceModuleAdjunction Stacks.SheafOfModules.TensorColimits

universe u

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-! ### Right exactness of the two sides -/

/-- The source `H ↦ h_*G ⊗_{𝒪_S} H` of the projection-formula morphism is right exact: it
preserves all colimits, by Tag 05NB. -/
lemma preservesFiniteColimits_tensorPushforwardFunctor
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) :
    PreservesFiniteColimits (tensorPushforwardFunctor h G) := by
  have hsize : PreservesColimitsOfSize.{0, u} (tensorPushforwardFunctor h G) :=
    tensorLeft_preservesColimits (Opens.grothendieckTopology S.carrier) S.toRingedSpace.sheaf
      ((modulePushforward h.toLRSHom.toShHom).obj G)
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The source functor carries a colimit cocone of a finite diagram to a colimit cocone. -/
def isColimitMapCoconeTensorPushforwardFunctorFinite
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {J : Type} [SmallCategory J]
    [FinCategory J] {Z : J ⥤ SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} {c : Cocone Z}
    (hc : IsColimit c) : IsColimit ((tensorPushforwardFunctor h G).mapCocone c) :=
  (((preservesFiniteColimits_tensorPushforwardFunctor h G).preservesFiniteColimits
    J).preservesColimit.preserves hc).some

/-- The pullback along a morphism of schemes is right exact: it is a left adjoint. -/
lemma preservesFiniteColimits_modulePullback :
    PreservesFiniteColimits (modulePullback h.toLRSHom.toShHom) := by
  have hsize : PreservesColimitsOfSize.{0, 0} (modulePullback h.toLRSHom.toShHom) :=
    (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The target `H ↦ h_*(G ⊗_{𝒪_T} h^*H)` carries a colimit cocone of a finite diagram to a
colimit cocone, as soon as the pushforward is right exact: the pullback is a left adjoint,
tensoring is Tag 05NB, and right exactness of the pushforward is the hypothesis.

As in the coproduct case
`Stacks.AlgebraicGeometry.ProjectionFormula.isColimitMapCoconePullbackTensorPushforwardFunctor`
the three witnesses are applied through their fields rather than through
`CategoryTheory.Limits.isColimitOfPreserves`, which takes them as instance arguments. -/
def isColimitMapCoconePullbackTensorPushforwardFunctorFinite
    [PreservesFiniteColimits (modulePushforward h.toLRSHom.toShHom)]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {J : Type} [SmallCategory J]
    [FinCategory J] {Z : J ⥤ SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} {c : Cocone Z}
    (hc : IsColimit c) : IsColimit ((pullbackTensorPushforwardFunctor h G).mapCocone c) := by
  have hpull : PreservesColimitsOfShape J (modulePullback h.toLRSHom.toShHom) :=
    (preservesFiniteColimits_modulePullback h).preservesFiniteColimits J
  have hsize : PreservesColimitsOfSize.{0, u}
      ((Stacks.SheafOfModules.Tensor.sheafTensor (J := Opens.grothendieckTopology T.carrier)
        T.toRingedSpace.sheaf).obj G) :=
    tensorLeft_preservesColimits (Opens.grothendieckTopology T.carrier) T.toRingedSpace.sheaf G
  have hten : PreservesColimitsOfShape J
      ((Stacks.SheafOfModules.Tensor.sheafTensor (J := Opens.grothendieckTopology T.carrier)
        T.toRingedSpace.sheaf).obj G) :=
    (PreservesColimitsOfSize.preservesFiniteColimits _).preservesFiniteColimits J
  have hpush : PreservesColimitsOfShape J (modulePushforward h.toLRSHom.toShHom) :=
    PreservesFiniteColimits.preservesFiniteColimits J
  exact (hpush.preservesColimit.preserves
    (hten.preservesColimit.preserves
      (hpull.preservesColimit.preserves hc).some).some).some

/-! ### The dévissage step at a finite colimit, and at a cokernel -/

/-- **The dévissage step for Stacks Tag 0FZE at a finite colimit.**  If the projection-formula
morphism is invertible at every object of a finite diagram of modules on the target, and the
pushforward is right exact, then it is invertible at a colimit of that diagram. -/
lemma isIso_projectionFormulaMap_of_isColimit
    [PreservesFiniteColimits (modulePushforward h.toLRSHom.toShHom)]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {J : Type} [SmallCategory J]
    [FinCategory J] {Z : J ⥤ SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} {c : Cocone Z}
    (hc : IsColimit c) (hZ : ∀ j, IsIso (projectionFormulaMap h G (Z.obj j))) :
    IsIso (projectionFormulaMap h G c.pt) :=
  CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone (projectionFormulaNatTrans h G) c
    (isColimitMapCoconeTensorPushforwardFunctorFinite h G hc)
    (isColimitMapCoconePullbackTensorPushforwardFunctorFinite h G hc) hZ

/-- Invertibility of the projection-formula morphism at a module on the target only depends on
the isomorphism class of that module. -/
lemma isIso_projectionFormulaMap_of_iso
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    {H H' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (e : H ≅ H')
    (hH : IsIso (projectionFormulaMap h G H)) : IsIso (projectionFormulaMap h G H') :=
  CategoryTheory.NatTrans.isIso_app_of_iso (projectionFormulaNatTrans h G) e hH

/-- **The dévissage step for Stacks Tag 0FZE at a cokernel.**  If the projection-formula morphism
is invertible at the source and the target of a morphism `g` of modules on the target, and the
pushforward is right exact, then it is invertible at `cokernel g`. -/
lemma isIso_projectionFormulaMap_cokernel
    [PreservesFiniteColimits (modulePushforward h.toLRSHom.toShHom)]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    {H₁ H₂ : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (g : H₁ ⟶ H₂)
    (h₁ : IsIso (projectionFormulaMap h G H₁)) (h₂ : IsIso (projectionFormulaMap h G H₂)) :
    IsIso (projectionFormulaMap h G (cokernel g)) :=
  isIso_projectionFormulaMap_of_isColimit h G (colimit.isColimit (parallelPair g 0))
    fun | .zero => h₁ | .one => h₂

/-! ### The projection formula at a presented module -/

/-- **The projection formula for a module presented by free modules on the target.**  Let
`h : T ⟶ S` be a quasi-compact morphism of schemes whose pushforward of sheaves of modules is
right exact, let `G` be any sheaf of `𝒪_T`-modules, and let `H` be a sheaf of `𝒪_S`-modules
isomorphic to the cokernel of a morphism between two free modules `𝒪_S^{(κ)} ⟶ 𝒪_S^{(ι)}`.  Then
the projection-formula morphism is invertible at `H` — with no affineness and no quasi-coherence.

Both free cases come from
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_free` and the cokernel
step from
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_cokernel`. -/
lemma isIso_projectionFormulaMap_of_freePresentation [QuasiCompact h]
    [PreservesFiniteColimits (modulePushforward h.toLRSHom.toShHom)]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {ι κ : Type u}
    (c₁ : Cofan (fun _ : κ => SheafOfModules.unit (structureSheafRing S.toRingedSpace)))
    (hc₁ : IsColimit c₁)
    (c₂ : Cofan (fun _ : ι => SheafOfModules.unit (structureSheafRing S.toRingedSpace)))
    (hc₂ : IsColimit c₂) (g : c₁.pt ⟶ c₂.pt)
    {H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (e : cokernel g ≅ H) :
    IsIso (projectionFormulaMap h G H) :=
  isIso_projectionFormulaMap_of_iso h G e
    (isIso_projectionFormulaMap_cokernel h G g
      (isIso_projectionFormulaMap_free h G c₁ hc₁)
      (isIso_projectionFormulaMap_free h G c₂ hc₂))

/-- **The projection formula for a closed immersion and a presented module.**  For a closed
immersion the two hypotheses of
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_freePresentation` hold
unconditionally: a closed immersion is affine, hence quasi-compact, and its pushforward of sheaves
of modules is right exact.  So the projection formula holds at every module on the target
presented by free modules, for every sheaf of modules on the source. -/
lemma isIso_projectionFormulaMap_of_freePresentation_of_isClosedImmersion [IsClosedImmersion h]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)) {ι κ : Type u}
    (c₁ : Cofan (fun _ : κ => SheafOfModules.unit (structureSheafRing S.toRingedSpace)))
    (hc₁ : IsColimit c₁)
    (c₂ : Cofan (fun _ : ι => SheafOfModules.unit (structureSheafRing S.toRingedSpace)))
    (hc₂ : IsColimit c₂) (g : c₁.pt ⟶ c₂.pt)
    {H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (e : cokernel g ≅ H) :
    IsIso (projectionFormulaMap h G H) :=
  isIso_projectionFormulaMap_of_freePresentation h G c₁ hc₁ c₂ hc₂ g e

/-- **The cokernel dévissage step for a closed immersion**, with no hypothesis on the
pushforward. -/
lemma isIso_projectionFormulaMap_cokernel_of_isClosedImmersion [IsClosedImmersion h]
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    {H₁ H₂ : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (g : H₁ ⟶ H₂)
    (h₁ : IsIso (projectionFormulaMap h G H₁)) (h₂ : IsIso (projectionFormulaMap h G H₂)) :
    IsIso (projectionFormulaMap h G (cokernel g)) :=
  isIso_projectionFormulaMap_cokernel h G g h₁ h₂

end Stacks.AlgebraicGeometry.ProjectionFormula

end
