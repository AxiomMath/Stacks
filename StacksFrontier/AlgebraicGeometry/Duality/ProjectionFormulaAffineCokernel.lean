module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis
public import StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula at a cokernel, for an affine morphism

`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel` proves the dévissage step for
Stacks 0FZE at a cokernel under the hypothesis
`PreservesFiniteColimits (modulePushforward h.toLRSHom.toShHom)`, right exactness of the direct
image on *all* sheaves of modules, and discharges it only for a closed immersion.  That
hypothesis is false for a general affine morphism — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact` for the counterexample — so
it cannot be the route to the affine case.

This file replaces it by what is true: for an affine morphism the direct image preserves
cokernels of morphisms of *quasi-coherent* modules
(`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero`), and that is
all the dévissage uses, because the modules occurring in it are quasi-coherent as soon as `G` and
the two modules presenting `H` are.  So the cokernel step, and with it the projection formula at a
module presented by free modules on the target, hold for every affine morphism with no hypothesis
on the pushforward.

## Main results

All four are in the namespace `Stacks.AlgebraicGeometry.ProjectionFormula`.

* `isQuasicoherent_pullbackTensor`: for `G` and `H` quasi-coherent, so is `G ⊗_{𝒪_T} h^*H`.
* `isColimitMapCoconePullbackTensorPushforwardFunctorCokernel`: the target
  `H ↦ h_*(G ⊗_{𝒪_T} h^*H)` of the projection-formula morphism carries a colimit cocone of a
  parallel pair of quasi-coherent modules to a colimit cocone, for an affine `h`.
* `isIso_projectionFormulaMap_cokernel_of_isAffineHom`: **the dévissage step at a cokernel for
  an affine morphism**, with no hypothesis on the pushforward.
* `isIso_projectionFormulaMap_of_freePresentation_of_isAffineHom`: **the projection formula for
  an affine morphism, a quasi-coherent `G`, and a module on the target presented as the cokernel
  of a morphism of free modules.**

## Implementation notes

**The three colimit-preservation facts are applied through their fields**, as in
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaFree` and
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel`, because instance search does
not cross the two spellings of the pushforward or the second spelling of the ring of scalars
that `tensorLeft` uses.  For the same reason every quasi-coherence hypothesis is an *explicit*
argument and is passed positionally: the modules here are typed over
`structureSheafRing S.toRingedSpace`, which is definitionally
`S.ringCatSheaf` but not syntactically, so `SheafOfModules.IsQuasicoherent` at the one spelling
is not found by search when it is wanted at the other.

**Why the shape-free preservation statement is the one used.**  The diagram the pushforward is
presented with here is `parallelPair g 0 ⋙ h^* ⋙ (G ⊗ -)`, which is not syntactically a
`parallelPair`; identifying it with one by
`CategoryTheory.Limits.diagramIsoParallelPair` leaves the second arrow as the image of the zero
morphism, and `CategoryTheory.tensorLeft` carries no `Functor.PreservesZeroMorphisms` instance,
so that image cannot be seen to vanish.  Hence
`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_walkingParallelPair`, which is
stated for an arbitrary diagram of shape `WalkingParallelPair` with quasi-coherent objects and
needs no such instance, is the form consumed.

**What is still missing for Stacks 0FZE**, after this file: a presentation of a quasi-coherent
`H` on `S` by free `𝒪_S`-modules.  A quasi-coherent module on a general scheme is not globally
generated, so that step needs the statement to be made local on `S` — the second missing input
listed in `StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula`.  The right exactness
that the same list names as the other missing input is supplied here, with the correction that
it is right exactness on quasi-coherent modules and not on all of them.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.AlgebraicGeometry.ProjectionFormula

open RingedSpaceModuleAdjunction Stacks.SheafOfModules.TensorColimits

universe u

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-! ### Quasi-coherence of the modules occurring in the dévissage -/

/-- The module `G ⊗_{𝒪_T} h^*H` is quasi-coherent as soon as `G` and `H` are: the pullback of a
quasi-coherent module is quasi-coherent, and so is a tensor product of quasi-coherent modules
(Tag 01CE). -/
lemma isQuasicoherent_pullbackTensor
    {G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)} (hG : G.IsQuasicoherent)
    {H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hH : H.IsQuasicoherent) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((T.toRingedSpace)).presheaf, ((T.toRingedSpace)).IsSheaf⟩).obj (G)).obj
        (((modulePullback h.toLRSHom.toShHom).obj H)))).IsQuasicoherent :=
  @_root_.AlgebraicGeometry.tensorSheaf_isQuasicoherent T.toRingedSpace G _ hG
    (Stacks.Modules.isQuasicoherent_pullback h H hH)

/-! ### Right exactness of the target of the projection-formula morphism -/

/-- The target `H ↦ h_*(G ⊗_{𝒪_T} h^*H)` of the projection-formula morphism carries a colimit
cocone of a parallel pair of quasi-coherent modules on the target to a colimit cocone, for an
affine morphism `h` and a quasi-coherent `G`.

The pullback is a left adjoint, tensoring is Tag 05NB, and the pushforward preserves the
cokernel of a morphism of quasi-coherent modules because `h` is affine. -/
def isColimitMapCoconePullbackTensorPushforwardFunctorCokernel [IsAffineHom h]
    {G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)} (hG : G.IsQuasicoherent)
    {H₁ H₂ : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hH₁ : H₁.IsQuasicoherent)
    (hH₂ : H₂.IsQuasicoherent) (g : H₁ ⟶ H₂) {c : Cocone (parallelPair g 0)} (hc : IsColimit c) :
    IsColimit ((pullbackTensorPushforwardFunctor h G).mapCocone c) := by
  have hpull : PreservesColimitsOfShape WalkingParallelPair
      (modulePullback h.toLRSHom.toShHom) :=
    ((modulePullbackPushforwardAdjunction
      h.toLRSHom.toShHom).leftAdjoint_preservesColimits).preservesColimitsOfShape
  have hten : PreservesColimitsOfShape WalkingParallelPair
      ((Stacks.SheafOfModules.Tensor.sheafTensor (J := (Opens.grothendieckTopology T.carrier))
        (T.toRingedSpace.sheaf)).obj G) := by
    have hsize : PreservesColimitsOfSize.{0, u}
        ((Stacks.SheafOfModules.Tensor.sheafTensor (J := (Opens.grothendieckTopology T.carrier))
          (T.toRingedSpace.sheaf)).obj G) :=
      tensorLeft_preservesColimits (Opens.grothendieckTopology T.carrier) T.toRingedSpace.sheaf G
    exact (PreservesColimitsOfSize.preservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor (J := (Opens.grothendieckTopology T.carrier))
        (T.toRingedSpace.sheaf)).obj G)).preservesFiniteColimits WalkingParallelPair
  set Φ : SheafOfModules.{u} (structureSheafRing S.toRingedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing T.toRingedSpace) :=
    modulePullback h.toLRSHom.toShHom ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor (J := (Opens.grothendieckTopology T.carrier))
        (T.toRingedSpace.sheaf)).obj G
  have hpush : PreservesColimit (parallelPair g 0 ⋙ Φ)
      (modulePushforward h.toLRSHom.toShHom) :=
    @Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_walkingParallelPair T S h ‹_›
      (parallelPair g 0 ⋙ Φ) (isQuasicoherent_pullbackTensor h hG hH₁)
      (isQuasicoherent_pullbackTensor h hG hH₂)
  exact (hpush.preserves
    (hten.preservesColimit.preserves
      (hpull.preservesColimit.preserves hc).some).some).some

/-! ### The dévissage step at a cokernel, and the presented case -/

/-- **The dévissage step for Stacks Tag 0FZE at a cokernel, for an affine morphism.**  Let
`h : T ⟶ S` be an affine morphism of schemes, `G` a quasi-coherent `𝒪_T`-module and
`g : H₁ ⟶ H₂` a morphism of quasi-coherent `𝒪_S`-modules.  If the projection-formula morphism is
invertible at `H₁` and at `H₂`, it is invertible at `cokernel g`.

There is no hypothesis on the pushforward: right exactness on the modules that occur is
`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero`. -/
lemma isIso_projectionFormulaMap_cokernel_of_isAffineHom [IsAffineHom h]
    {G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)} (hG : G.IsQuasicoherent)
    {H₁ H₂ : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hH₁ : H₁.IsQuasicoherent)
    (hH₂ : H₂.IsQuasicoherent) (g : H₁ ⟶ H₂)
    (h₁ : IsIso (projectionFormulaMap h G H₁)) (h₂ : IsIso (projectionFormulaMap h G H₂)) :
    IsIso (projectionFormulaMap h G (cokernel g)) :=
  CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone (projectionFormulaNatTrans h G)
    (colimit.cocone (parallelPair g 0))
    (isColimitMapCoconeTensorPushforwardFunctorFinite h G (colimit.isColimit (parallelPair g 0)))
    (isColimitMapCoconePullbackTensorPushforwardFunctorCokernel h hG hH₁ hH₂ g
      (colimit.isColimit (parallelPair g 0)))
    (fun j => match j with
      | WalkingParallelPair.zero => h₁
      | WalkingParallelPair.one => h₂)

/-- **The projection formula for an affine morphism and a presented module.**  Let `h : T ⟶ S`
be an affine morphism of schemes, `G` a quasi-coherent `𝒪_T`-module, and `H` an `𝒪_S`-module
isomorphic to the cokernel of a morphism between two free modules `𝒪_S^{(κ)} ⟶ 𝒪_S^{(ι)}`.  Then
the projection-formula morphism `h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` is invertible.

Both free cases are `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_free`,
which needs only quasi-compactness, and the cokernel step is
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_cokernel_of_isAffineHom`.
The two free modules are quasi-coherent because the structure sheaf is and quasi-coherence is
stable under colimits. -/
@[sga "3 VIB 11.1" "special case"]
lemma isIso_projectionFormulaMap_of_freePresentation_of_isAffineHom [IsAffineHom h]
    {G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)} (hG : G.IsQuasicoherent)
    {ι κ : Type u}
    (c₁ : Cofan (fun _ : κ => SheafOfModules.unit (structureSheafRing S.toRingedSpace)))
    (hc₁ : IsColimit c₁)
    (c₂ : Cofan (fun _ : ι => SheafOfModules.unit (structureSheafRing S.toRingedSpace)))
    (hc₂ : IsColimit c₂) (g : c₁.pt ⟶ c₂.pt)
    {H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (e : cokernel g ≅ H) :
    IsIso (projectionFormulaMap h G H) :=
  have hunit : (SheafOfModules.unit.{u} (structureSheafRing S.toRingedSpace)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  have h₁ : c₁.pt.IsQuasicoherent :=
    QuasicoherentColimits.isQuasicoherent_of_isColimit (fun _ => hunit) hc₁
  have h₂ : c₂.pt.IsQuasicoherent :=
    QuasicoherentColimits.isQuasicoherent_of_isColimit (fun _ => hunit) hc₂
  isIso_projectionFormulaMap_of_iso h G e
    (isIso_projectionFormulaMap_cokernel_of_isAffineHom h hG h₁ h₂ g
      (isIso_projectionFormulaMap_free h G c₁ hc₁)
      (isIso_projectionFormulaMap_free h G c₂ hc₂))

end Stacks.AlgebraicGeometry.ProjectionFormula

end
