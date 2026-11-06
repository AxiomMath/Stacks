module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FactorizationThroughAnAuxiliaryTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi

/-!
# The change-of-rings half of Stacks 05VD

Stacks 05VD says that the pullback `f^*` of sheaves of modules along a morphism of ringed topoi
carries a flat module to a flat module. Write `f^* ≅ g^* ⋙ h^*`, where `g : X' ⟶ Y`,
`StacksPullbackFactorization.auxHomG`, has the same underlying continuous functor as `f` and the
adjunction unit as its structure map, and `h^*` is extension of scalars along `f⁻¹O_Y ⟶ O_X`.
This file proves that `h^*` preserves flatness (Tag 05V4), so that `f^*M` is flat as soon as
`g^*M` is.

## Main results

All of the following live in the namespace `Stacks.Sheaves.DerivedPullback.FlatExtendScalars`.

* `extendScalarsIsoChangeOfRings`: the abstract extension of scalars
  (`Stacks.Sheaves.ModuleAdjunction.extendScalars`, a left adjoint) and the sheafified
  sectionwise tensor product (`Stacks.Sheaves.ChangeOfRings.changeOfRings`) are isomorphic.
* `isFlat_extendScalars`: **Tag 05V4 for the abstract extension of scalars.**
* `isFlat_pullbackTopos_auxHomH`: the ring-theoretic half `h^*` of the factorization preserves
  flatness.
* `isFlat_pullbackTopos_of_isFlat_pullbackTopos_auxHomG`: **the reduction.** If `g^*M` is flat
  over `f⁻¹O_Y` then `f^*M` is flat over `O_X`.
* `pullbackPreservesIsFlat_of_auxHomG`: the same, as an implication between the two instances
  of `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat`.

## Implementation notes

`Stacks.Sheaves.RingedToposModules.extendScalars` is `Stacks.Sheaves.ChangeOfRings.changeOfRings`
by `rfl`, so `Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor` identifies the abstract
extension of scalars with the one Tag 05V4 is stated for. The sheaf-condition argument it takes
is `(Stacks.commRingSheafToRingSheaf O).property`, at
`Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O.obj`, not `O.property`, which is at
`O.obj`.

The reduction holds for an arbitrary `AlgebraicGeometry.RingedToposSiteHom`, with no
morphism-of-sites hypothesis. In `pullbackPreservesIsFlat_of_auxHomG` the hypothesis
`(auxHomG f).u.IsMorphismOfSites Y.J (auxTopos f).J` is `f.u.IsMorphismOfSites Y.J X.J`, since
`(auxHomG f).u = f.u` and `(auxTopos f).J = X.J` by `rfl`.

Both ringed topoi are at `RingedTopos.{u, u, u}`, with the site, the rings and the modules in one
universe `u`, as `SheafOfModules.pullback`, `CategoryTheory.Functor.IsMorphismOfSites` and
`Stacks.Sheaves.ModuleAdjunction.extendScalars` require.

## References

* [The Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [The Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [The Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [The Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [The Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [The Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.FlatExtendScalars

/-! ### Tag 05V4 for the abstract extension of scalars -/

section ChangeOfRings

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O₁ O₂ : Sheaf J CommRingCat.{u}}

/-- The abstract extension of scalars along `α`, the left adjoint of restriction of scalars, is
isomorphic to the sheafified sectionwise tensor product
`Stacks.Sheaves.ChangeOfRings.changeOfRings`. -/
def extendScalarsIsoChangeOfRings (α : O₁ ⟶ O₂) :
    Stacks.Sheaves.ModuleAdjunction.extendScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)
      ≅ Stacks.Sheaves.ChangeOfRings.changeOfRings.{u, u, u} J α :=
  Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor (J := J) α.hom
    (Stacks.commRingSheafToRingSheaf O₁).property (Stacks.commRingSheafToRingSheaf O₂).property

/-- **Stacks Tag 05V4 for the abstract extension of scalars.** The left adjoint of restriction
of scalars along a morphism of sheaves of commutative rings carries a flat sheaf of modules to
a flat sheaf of modules. -/
theorem isFlat_extendScalars (α : O₁ ⟶ O₂)
    (G : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf O₁))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O₁) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O₂)
      ((Stacks.Sheaves.ModuleAdjunction.extendScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj G) :=
  AlgebraicGeometry.SheafOfModules.IsFlat.of_iso O₂
    ((extendScalarsIsoChangeOfRings α).app G).symm
    (Stacks.FlatChangeOfRings.isFlat_extendScalars.{u, u, u} α G hG)

end ChangeOfRings

/-! ### The reduction of Tag 05VD to the inverse image -/

section Reduction

open StacksPullbackFactorization

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The ring-theoretic half `h^*` of the factorization `f^* ≅ g^* ⋙ h^*` preserves flatness. -/
theorem isFlat_pullbackTopos_auxHomH (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (auxTopos f).O) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((auxHomH f).pullbackTopos.obj G) :=
  isFlat_extendScalars (auxHomH f).fSharp G hG

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The reduction of Stacks 05VD to the inverse image.** If the inverse image `g^*M` of `M`
is flat over `f⁻¹O_Y`, then the pullback `f^*M` is flat over `O_X`. -/
theorem isFlat_pullbackTopos_of_isFlat_pullbackTopos_auxHomG
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (auxTopos f).O)
      ((auxHomG f).pullbackTopos.obj M)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (f.pullbackTopos.obj M) :=
  AlgebraicGeometry.SheafOfModules.IsFlat.of_iso X.O ((pullbackFactorIso f).app M)
    (isFlat_pullbackTopos_auxHomH f ((auxHomG f).pullbackTopos.obj M) hM)

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 05VD for `f` follows from Stacks 05VD for `g`.**
`Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat` at the auxiliary ringed
topos `X' = (X.C, X.J, f⁻¹O_Y)` implies it at `X`. -/
theorem pullbackPreservesIsFlat_of_auxHomG (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (h : Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat (auxHomG f)) :
    Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat f := fun hmos M hM =>
  isFlat_pullbackTopos_of_isFlat_pullbackTopos_auxHomG f M (h hmos M hM)

end Reduction

end Stacks.Sheaves.DerivedPullback.FlatExtendScalars

end

end
