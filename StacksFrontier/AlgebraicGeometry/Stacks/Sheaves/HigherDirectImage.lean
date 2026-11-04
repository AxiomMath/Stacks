module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Higher direct images on the sites of a category fibred in groupoids

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of fibred categories over the big fppf category of a scheme
`S`, and let `τ` be a topology on the underlying category of schemes. Stacks 075G computes the
higher direct images `R^i f_* ℱ` of an abelian sheaf on `𝒳` as the sheaves associated to the
presheaves of cohomology of the 2-fibres of `f`. This file proves the *sheafification* half of
that statement: `R^i f_*` is the sheafification of the derived presheaf direct image.

The presheaf direct image is the right Kan extension along `f.op`, and direct image of sheaves
is that Kan extension followed by sheafification. Sheafification is exact and preserves
injectives are not needed: it is enough that it preserve homology, which it does, so deriving
the composite is deriving the Kan extension and then sheafifying. Deriving the *presheaf* direct
image rather than only computing its values is what pins down the restriction maps of the
cohomology presheaf, and not merely its values up to unrelated isomorphisms.

## Main definitions

* `AlgebraicGeometry.Stack.derivedPresheafDirectImage`: the derived presheaf direct image,
  including its restriction maps.

## Main results

* `AlgebraicGeometry.Stack.additive_sheafPushforwardCocontinuous`: direct image of abelian
  sheaves is additive.
* `AlgebraicGeometry.Stack.derivedDirectImageIsoSheafifyDerivedPresheafDirectImage`:
  **Stacks 075G**, the sheafification formula for abelian sheaves.

## Implementation notes

The source states Stacks 075G for a 1-morphism of algebraic stacks, with a footnote that it
should hold for any 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf`. The
sheafification half needs even less: only that `f` be a 1-morphism of *fibred* categories, which
is what makes it cocontinuous for the inherited topologies (Stacks 06NW) and so makes the direct
image the Kan extension on underlying presheaves. That is the generality used here; the
algebraic-stack case is its instance. As elsewhere in this directory, `τ` is an arbitrary
topology on `B.Schemes` rather than one of the source's five.

The identification of the composite of two right derived functors is
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` (Stacks 015Z), applied with the
identity comparison, and the transport of a derived functor along a natural isomorphism is
`Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso`.

## References

* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂ a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)

/-- The derived presheaf direct image: the right derived functor of the composite of the
inclusion of sheaves into presheaves with the right Kan extension along `F.op`. -/
noncomputable abbrev derivedPresheafDirectImage
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, F.op.HasPointwiseRightKanExtension G]
    [HasSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{a}]
    [HasInjectiveResolutions (Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{a})] (n : ℕ) :
    Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{a} ⥤ 𝒴ᵒᵖ ⥤ AddCommGrpCat.{a} :=
  letI := (F.op.ranAdjunction AddCommGrpCat.{a}).right_adjoint_additive
  letI := (sheafificationAdjunction (associatedTopology B S hS p τ)
    AddCommGrpCat.{a}).right_adjoint_additive
  (sheafToPresheaf (associatedTopology B S hS p τ) AddCommGrpCat.{a} ⋙ F.op.ran).rightDerived n

/-- Direct image of abelian sheaves along a 1-morphism of fibred categories is additive: on
underlying presheaves it is the right Kan extension along `F.op`, which is a right adjoint. -/
theorem additive_sheafPushforwardCocontinuous
    [p.IsFibered] [q.IsFibered] (hF : p.IsFibredOneMorphism q F)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, F.op.HasPointwiseRightKanExtension G]
    [HasSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{a}]
    [HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{a}] :
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
    (F.sheafPushforwardCocontinuous AddCommGrpCat.{a}
      (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).Additive := by
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := (F.op.ranAdjunction AddCommGrpCat.{a}).right_adjoint_additive
  let := Functor.additive_of_iso
    (hF.directImageCompSheafToPresheafIso (τ.over (B.obj hS)) AddCommGrpCat.{a}).symm
  exact Functor.additive_of_comp_faithful _
    (sheafToPresheaf (associatedTopology B S hS q τ) AddCommGrpCat.{a})

/-- **Stacks 075G.** Higher direct image of abelian sheaves is the sheafification of the
derived presheaf direct image. -/
@[stacks 075G "abelian sheafification formula"]
noncomputable def derivedDirectImageIsoSheafifyDerivedPresheafDirectImage
    [p.IsFibered] [q.IsFibered] (hF : p.IsFibredOneMorphism q F) (n : ℕ)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, F.op.HasPointwiseRightKanExtension G]
    [HasSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{a}]
    [HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{a}]
    [HasInjectiveResolutions (Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{a})] :
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
    letI := additive_sheafPushforwardCocontinuous B S hS p q F τ hF
    (F.sheafPushforwardCocontinuous AddCommGrpCat.{a}
        (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).rightDerived n ≅
      derivedPresheafDirectImage B S hS p F τ n ⋙
        presheafToSheaf (associatedTopology B S hS q τ) AddCommGrpCat.{a} := by
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := additive_sheafPushforwardCocontinuous B S hS p q F τ hF
  let JX := associatedTopology B S hS p τ
  let JY := associatedTopology B S hS q τ
  let P := F.sheafPushforwardCocontinuous AddCommGrpCat.{a} JX JY
  let G := sheafToPresheaf JX AddCommGrpCat.{a} ⋙ F.op.ran
  let T := presheafToSheaf JY AddCommGrpCat.{a}
  let : G.Additive := by
    let := (F.op.ranAdjunction AddCommGrpCat.{a}).right_adjoint_additive
    let := (sheafificationAdjunction JX AddCommGrpCat.{a}).right_adjoint_additive
    infer_instance
  let hcomp : P ≅ G ⋙ T :=
    (Functor.rightUnitor P).symm ≪≫
      Functor.isoWhiskerLeft P (sheafificationNatIso JY AddCommGrpCat.{a}) ≪≫
      (Functor.associator P (sheafToPresheaf JY AddCommGrpCat.{a}) T).symm ≪≫
      Functor.isoWhiskerRight
        (hF.directImageCompSheafToPresheafIso (τ.over (B.obj hS)) AddCommGrpCat.{a}) T
  let : T.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels T
  exact Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso hcomp n ≪≫
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso G T (G ⋙ T) (Iso.refl _) n).symm

end AlgebraicGeometry.Stack

end
