module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Abelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero commutes with the étale-to-pro-étale comparison

Let `j : U ⟶ X` be an étale morphism of schemes and let `ε` be the comparison morphism from the
small pro-étale site of a scheme to its small étale site, that is, the morphism of sites given
by the inclusion `AlgebraicGeometry.Scheme.etaleToProetale` of étale objects among the weakly
étale ones.  For an abelian sheaf `G` on `U_étale` there are two ways of producing an abelian
sheaf on `X_proétale`: extend by zero on the étale sites and pull back along `ε`, or pull back
along `ε` and extend by zero on the pro-étale sites.  They agree.

## Main definitions

* `AlgebraicGeometry.ProEtale.epsilonDirectImage` and
  `AlgebraicGeometry.ProEtale.epsilonInverseImage` are `ε_*` and `ε^{-1}` on abelian sheaves,
  and `AlgebraicGeometry.ProEtale.epsilonAdjunction` is the adjunction `ε^{-1} ⊣ ε_*` between
  them.

## Main results

* `AlgebraicGeometry.ProEtale.smallEtaleCompose_comp_etaleToProetale`: the square of sites
  commutes, `j ∘ (-)` followed by the inclusion of étale objects being the inclusion of étale
  objects followed by `j ∘ (-)`.
* `AlgebraicGeometry.ProEtale.proetaleRestriction_comp_epsilonDirectImage`: consequently
  `ε_* j^{-1}_{proétale} = j^{-1}_{étale} ε_*`.
* `AlgebraicGeometry.ProEtale.epsilonInverseImageExtensionByZeroIso`: **Stacks Tag 09AF**,
  `ε^{-1} j_! ≅ j_! ε^{-1}` as functors from abelian sheaves on `U_étale` to abelian sheaves
  on `X_proétale`.
* `AlgebraicGeometry.ProEtale.epsilonInverseImageExtensionByZeroObjIso` is the same statement
  evaluated at a sheaf `G`, the form in which the source states it.

## Implementation notes

`ε_*` is restriction along the inclusion of sites, so the commuting square of sites gives the
equality of the two composites of restrictions on the nose, by `rfl`: the identification
`CategoryTheory.Functor.sheafPushforwardContinuousComp` of a composite of restrictions with the
restriction along the composite is the identity isomorphism.
Both `ε^{-1} j_!` and `j_! ε^{-1}` are then left adjoint to that one functor, and the
isomorphism is uniqueness of left adjoints.

The two extension-by-zero functors are the ones the library already has:
`Stacks.EtaleCohomology.extensionByZero` of Tag 03S3 on the small étale sites and
`AlgebraicGeometry.ProEtale.Abelian.extensionByZero` of Tag 09AE on the small pro-étale sites.
An étale morphism is weakly étale, so the latter applies to `j`.

Sheafification of abelian presheaves on either small site is available because both sites are
essentially small, and the library already has both: on the small étale site as the global
instance `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`, and on the small pro-étale
site as `AlgebraicGeometry.ProEtale.hasSheafify_proetale`, made a local instance here.
So no declaration below carries a sheafification hypothesis.

## References

* [Stacks Project, Tag 09AF](https://stacks.math.columbia.edu/tag/09AF)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 09AE](https://stacks.math.columbia.edu/tag/09AE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace AlgebraicGeometry.ProEtale

attribute [local instance] hasSheafify_proetale

/-! ### The comparison morphism on abelian sheaves -/

variable (X : Scheme.{u})

/-- The direct image `ε_*` of abelian sheaves along the comparison morphism from the small
pro-étale site of `X` to its small étale site: restriction along the inclusion of the étale
objects among the weakly étale ones. -/
abbrev epsilonDirectImage :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  X.etaleToProetale.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The inverse image `ε^{-1}` of abelian sheaves along the comparison morphism: the
sheafification of the left Kan extension along the inclusion of the small étale site into the
small pro-étale site. -/
abbrev epsilonInverseImage :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
    AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The comparison morphism is a morphism of sites: `ε^{-1} ⊣ ε_*` on abelian sheaves. -/
def epsilonAdjunction : epsilonInverseImage.{u, v} X ⊣ epsilonDirectImage.{u, v} X :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-! ### The commuting square of sites -/

variable {X} {U : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- An étale `U`-scheme, pushed to an étale `X`-scheme and then viewed as a weakly étale
`X`-scheme, is the same as one viewed as a weakly étale `U`-scheme and then pushed to a weakly
étale `X`-scheme: the square of sites underlying Stacks Tag 09AF commutes. -/
theorem smallEtaleCompose_comp_etaleToProetale :
    Scheme.Etale.smallEtaleCompose j ⋙ X.etaleToProetale =
      U.etaleToProetale ⋙ proetalePostcompose j :=
  rfl

/-- `ε_* j^{-1} = j^{-1} ε_*`: restriction of abelian pro-étale sheaves along `j` followed by
the comparison direct image is the comparison direct image followed by restriction of abelian
étale sheaves along `j`.  Both are restriction along the one composite of
`AlgebraicGeometry.ProEtale.smallEtaleCompose_comp_etaleToProetale`. -/
theorem proetaleRestriction_comp_epsilonDirectImage :
    Abelian.proetaleRestriction.{u, v} j ⋙ epsilonDirectImage.{u, v} U =
      epsilonDirectImage.{u, v} X ⋙ Stacks.EtaleCohomology.etaleRestriction.{u, v} j :=
  rfl

/-! ### Extension by zero commutes with the comparison -/

/-- **Stacks Tag 09AF.** For an étale morphism `j : U ⟶ X`, pulling back along the comparison
morphism `ε` of the small pro-étale and small étale sites commutes with extension by zero:
`ε^{-1} j_! ≅ j_! ε^{-1}` on abelian sheaves.  Both sides are left adjoint to
`ε_* j^{-1} = j^{-1} ε_*`. -/
@[stacks 09AF "the natural isomorphism eps^{-1} j_! = j_! eps^{-1}"]
def epsilonInverseImageExtensionByZeroIso :
    Stacks.EtaleCohomology.extensionByZero.{u, v} j ⋙ epsilonInverseImage.{u, v} X ≅
      epsilonInverseImage.{u, v} U ⋙ Abelian.extensionByZero.{u, v} j :=
  Adjunction.leftAdjointUniq
    ((Stacks.EtaleCohomology.extensionByZeroAdj.{u, v} j).comp (epsilonAdjunction.{u, v} X))
    (((epsilonAdjunction.{u, v} U).comp (Abelian.extensionByZero_adjunction.{u, v} j)).ofNatIsoRight
      (eqToIso (proetaleRestriction_comp_epsilonDirectImage.{u, v} j)))

/-- **Stacks Tag 09AF**, evaluated at an abelian sheaf `G` on `U_étale`:
`ε^{-1} j_! G = j_! ε^{-1} G` as abelian sheaves on `X_proétale`.  This is the form in which the
source states the lemma. -/
@[stacks 09AF "at an abelian sheaf G on U_etale: eps^{-1} j_! G = j_! eps^{-1} G"]
def epsilonInverseImageExtensionByZeroObjIso
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (epsilonInverseImage.{u, v} X).obj
        ((Stacks.EtaleCohomology.extensionByZero.{u, v} j).obj G) ≅
      (Abelian.extensionByZero.{u, v} j).obj ((epsilonInverseImage.{u, v} U).obj G) :=
  (epsilonInverseImageExtensionByZeroIso.{u, v} j).app G

end AlgebraicGeometry.ProEtale

end
