module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyPresheafRestriction

/-!
# Cohomology of the structure sheaf along an open immersion

Let `f : Y ⟶ X` be an open immersion of schemes. For every open `U` of `Y`, the cohomology of
`𝒪_X` over the open `f(U)` of `X` is the cohomology of `𝒪_Y` over `U`, and these identifications
are compatible with the restriction maps: they form an isomorphism of cohomology presheaves on
`Y`. Since an isomorphism of schemes is an open immersion, this contains the invariance of the
cohomology of the structure sheaf under isomorphisms, naturally in the restriction maps.

Cohomology over an open is Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf` of the abelian sheaf
underlying the structure sheaf, the model in which the Mayer–Vietoris sequence
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact` is stated.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.structureAbelianSheafRestrictionIso`: the restriction of the
  abelian sheaf `𝒪_X` along `f` is `𝒪_Y`.
* `AlgebraicGeometry.Scheme.Hom.structureSheafCohomologyPresheafIso`: the isomorphism of
  cohomology presheaves `U ↦ Hⁿ(f(U), 𝒪_X)` and `U ↦ Hⁿ(U, 𝒪_Y)`.

## Implementation notes

The comparison is `Stacks.Cohomology.BiggerSite.cohomologyPresheafRestrictionIso` at the
open-image functor `f.opensFunctor`, which is continuous and cocontinuous and preserves fibre
products and equalizers, followed by the identification of the restricted structure sheaf given
by `AlgebraicGeometry.Scheme.Hom.appIso`.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe w u

namespace CategoryTheory.Limits

/-- **A functor between preorders preserves equalizers.** An equalizer of a parallel pair in a
preorder is its source, up to isomorphism, and so is the image of that equalizer. -/
theorem preservesLimitsOfShape_walkingParallelPair_of_preorder {C D : Type*} [Preorder C]
    [Preorder D] (F : C ⥤ D) : PreservesLimitsOfShape WalkingParallelPair F where
  preservesLimit {K} := ⟨fun {c} hc => ⟨Preorder.isLimitOfIsGLB _ _
    ⟨Preorder.conePt_mem_lowerBounds _ _, fun W hW => by
      have hc' := Preorder.isGLB_of_isLimit K hc
      have h0 : K.obj WalkingParallelPair.zero ≤ c.pt := hc'.2 (by
        rintro _ ⟨j, rfl⟩
        cases j
        · exact le_rfl
        · exact (K.map WalkingParallelPairHom.left).le)
      exact (hW ⟨WalkingParallelPair.zero, rfl⟩).trans (F.map (homOfLE h0)).le⟩⟩⟩

end CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

instance : PreservesLimitsOfShape WalkingParallelPair f.opensFunctor :=
  preservesLimitsOfShape_walkingParallelPair_of_preorder _

/-- **The restriction of `𝒪_X` along an open immersion `f : Y ⟶ X` is `𝒪_Y`**, as abelian
sheaves on `Y`: over an open `U` of `Y` it is `Γ(X, f(U)) ≅ Γ(Y, U)`, given by
`AlgebraicGeometry.Scheme.Hom.appIso`. -/
def structureAbelianSheafRestrictionIso :
    (f.opensFunctor.sheafPushforwardContinuous Ab.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj X.sheaf) ≅
      (sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj Y.sheaf :=
  let e : f.opensFunctor.op ⋙ X.presheaf ≅ Y.presheaf :=
    NatIso.ofComponents (fun U => f.appIso U.unop) (fun i => f.appIso_hom_naturality i)
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight e (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) Ab.{u})]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology Y) Ab.{u})]

/-- **Cohomology of the structure sheaf along an open immersion, naturally in the open.** For an
open immersion `f : Y ⟶ X` the cohomology presheaf `U ↦ Hⁿ(f(U), 𝒪_X)` on `Y` is isomorphic to
`U ↦ Hⁿ(U, 𝒪_Y)`. -/
def structureSheafCohomologyPresheafIso (n : ℕ) :
    f.opensFunctor.op ⋙
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
            X.sheaf).cohomologyPresheaf.{w} n ≅
      ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
            Y.sheaf).cohomologyPresheaf.{w} n :=
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) Ab.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  have : ∀ P : (Y.Opens)ᵒᵖ ⥤ Ab.{u}, f.opensFunctor.op.HasPointwiseLeftKanExtension P :=
    fun P => Stacks.Cohomology.BiggerSite.hasPointwiseLeftKanExtension_op _ P
  have : ∀ P : (Y.Opens)ᵒᵖ ⥤ Ab.{u}, f.opensFunctor.op.HasPointwiseRightKanExtension P :=
    fun P => Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op _ P
  have : (f.opensFunctor.sheafPushforwardContinuous Ab.{u} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f.opensFunctor Ab.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isRightAdjoint
  have := Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) f.opensFunctor Ab.{u}
  have := Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) f.opensFunctor
  Stacks.Cohomology.BiggerSite.cohomologyPresheafRestrictionIso _ _ f.opensFunctor _ n ≪≫
    (Sheaf.cohomologyPresheafFunctor _ n).mapIso (f.structureAbelianSheafRestrictionIso)

end AlgebraicGeometry.Scheme.Hom

end
