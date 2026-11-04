module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackMorphismOfSites

/-!
# Stacks 05V1 for sheaves of modules, at the point of the target site

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi whose underlying functor of
the sites is a morphism of sites, let `Φ` be a point of `C`, and let `Ψ` be the point of `C'`
attached to `Φ` by part (2) of Stacks 00YA, so that the stalk functor of `Ψ` on sheaves of sets
is the inverse image along `f` followed by the stalk functor of `Φ`.

For every sheaf of `O'`-modules `G` the stalk at `Φ` of the inverse image `f^{-1}G` of Stacks
03D2 is then the stalk of `G` at `Ψ`, semilinearly over the corresponding isomorphism
`O'_Ψ ≅ (f^{-1}O')_Φ` of stalk rings.  This is the half of Stacks 05V5 that does not involve the
structure map of `f`: the comparison

`(f^*G)_Φ ≅ G_Ψ ⊗_{O'_Ψ} O_Φ`

of Stacks 05V5 is this identification followed by extension of scalars along the stalk at `Φ`
of the inverse-image form `f^{-1}O' ⟶ O` of the structure map.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetStalkRingEquiv`: the
  isomorphism `O'_Ψ ≅ (f^{-1}O')_Φ` of stalk rings.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetStalkAddEquiv`: the
  isomorphism `G_Ψ ≅ (f^{-1}G)_Φ` of stalk modules.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetStalkNatIso`: the same
  comparison as a natural isomorphism of stalk functors.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetStalkAddEquiv_smul`: the
  isomorphism of stalk modules is semilinear over the isomorphism of stalk rings.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetStalkAddEquiv_naturality`:
  it is natural in the sheaf of modules.

## Implementation notes

Everything here is the general statement of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkInverseImageModules.lean` specialised along
`Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetPointStalkIso`, which is the
identification of stalk functors on sheaves of sets that part (2) of Stacks 00YA produces
together with the point `Ψ`.  The left exactness of the inverse image is supplied by the field
of the morphism of topoi, made a local instance.

The stalk rings appearing here are the `RingCat`-valued stalks of the sheaves of rings
underlying the two structure sheaves, not the `CommRingCat`-valued stalks
`Stacks.Sheaves.KFlatStalkCriterion.structureStalk` in which the hypothesis
`Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.StalkBaseChange` is phrased.  The
two are identified by `Stacks.commRingSheafFiberIso`; that identification, the extension of
scalars along the stalk of the structure map, and the passage from one degree to a complex are
what still separate this from `StalkBaseChange`.

## References

* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.StalkInverseImage

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y) (hu : f.u.IsMorphismOfSites.{u} Y.J X.J)
  (Φ : X.J.Point.{u})

/-- **The isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of stalk rings** at the point `Ψ` of the target site
attached to `Φ`. -/
def targetStalkRingEquiv :
    ((targetPoint f hu Φ).presheafFiber (A := RingCat.{u})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ≃+*
      (Φ.presheafFiber (A := RingCat.{u})).obj
        (inverseImageRingSheaf (f.toToposHom hu)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj :=
  stalkRingEquiv (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ
    (targetPoint f hu Φ) (targetPointStalkIso f hu Φ)

variable (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **Module-level Stacks 05V1 at the named point of the target site.**  The stalk at `Φ` of
the inverse image of a sheaf of `O'`-modules is the stalk of that sheaf at `Ψ`, as an
isomorphism of additive groups; it is semilinear over `targetStalkRingEquiv`. -/
@[stacks 05V1 "for sheaves of modules, at the point of the target site attached to a point of
the source site by part (2) of Stacks 00YA"]
def targetStalkAddEquiv :
    (Stacks.sheafModuleFiber (targetPoint f hu Φ)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G ≃+
      (Stacks.sheafModuleFiber Φ
          (inverseImageRingSheaf (f.toToposHom hu)
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj
        ((inverseImageModules (f.toToposHom hu)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) :=
  stalkAddEquiv (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ
    (targetPoint f hu Φ) (targetPointStalkIso f hu Φ) G

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 05V1 for sheaves of modules at the named point.**  The isomorphism of stalk
modules is semilinear over the isomorphism of stalk rings. -/
@[stacks 05V1 "semilinearity, at the point of the target site attached to a point of the source
site"]
theorem targetStalkAddEquiv_smul
    (r : ((targetPoint f hu Φ).presheafFiber (A := RingCat.{u})).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
    (m : (Stacks.sheafModuleFiber (targetPoint f hu Φ)
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) :
    targetStalkAddEquiv f hu Φ G (r • m) =
      targetStalkRingEquiv f hu Φ r • targetStalkAddEquiv f hu Φ G m :=
  stalkAddEquiv_smul (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ
    (targetPoint f hu Φ) (targetPointStalkIso f hu Φ) G r m

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] in
/-- The isomorphism of stalk modules is natural in the sheaf of modules. -/
theorem targetStalkAddEquiv_naturality
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (α : G ⟶ G')
    (m : (Stacks.sheafModuleFiber (targetPoint f hu Φ)
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) :
    targetStalkAddEquiv f hu Φ G'
        ((Stacks.sheafModuleFiber (targetPoint f hu Φ)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map α m) =
      (Stacks.sheafModuleFiber Φ
            (inverseImageRingSheaf (f.toToposHom hu)
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((inverseImageModules (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map α)
        (targetStalkAddEquiv f hu Φ G m) :=
  stalkAddEquiv_naturality (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ
    (targetPoint f hu Φ) (targetPointStalkIso f hu Φ) α m

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Module-level Stacks 05V1 at the named point, as a natural isomorphism of stalk
functors.**  The stalk functor at `Ψ` is the inverse image of sheaves of modules followed by
the stalk functor at `Φ` and restriction of scalars along the isomorphism of stalk rings.

This is the form a statement about complexes consumes:
`CategoryTheory.NatIso.mapHomologicalComplex` carries it to an isomorphism of the degreewise
functors on cochain complexes. -/
@[stacks 05V1 "for sheaves of modules, as a natural isomorphism of stalk functors, at the point
of the target site attached to a point of the source site"]
def targetStalkNatIso :
    Stacks.sheafModuleFiber (targetPoint f hu Φ) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      inverseImageModules (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        Stacks.sheafModuleFiber Φ
            (inverseImageRingSheaf (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          ModuleCat.restrictScalars (targetStalkRingEquiv f hu Φ).toRingHom :=
  stalkNatIso (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ (targetPoint f hu Φ)
    (targetPointStalkIso f hu Φ)

end Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites

end

end
