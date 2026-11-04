module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Localization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AbelianSheafification
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Adjunction.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of abelian sheaves on the small pro-étale site

A weakly étale morphism of schemes induces restriction of abelian sheaves on the small
pro-étale sites. This restriction has a left adjoint, extension by zero.

## Main definitions

* `AlgebraicGeometry.ProEtale.Abelian.proetaleRestriction` is restriction of abelian sheaves
  along the postcomposition functor of small pro-étale sites.
* `AlgebraicGeometry.ProEtale.Abelian.extensionByZero` is the extension-by-zero functor.
* `AlgebraicGeometry.ProEtale.Abelian.sheafifiedExtensionByZero` is the same functor given by
  an explicit construction: sheafification of the left Kan extension.

## Main results

* `AlgebraicGeometry.ProEtale.Abelian.exists_extensionByZero` asserts existence of a left
  adjoint to restriction.
* `AlgebraicGeometry.ProEtale.Abelian.extensionByZero_adjunction` is its defining adjunction
  to restriction.
* `AlgebraicGeometry.ProEtale.Abelian.sheafifiedExtensionByZeroAdjunction` is the defining
  adjunction of the explicitly constructed functor.
* `AlgebraicGeometry.ProEtale.Abelian.extensionByZeroIsoSheafified` identifies the two.

## Implementation notes

Restriction is precomposition on sheaves along the canonical postcomposition functor
`AlgebraicGeometry.ProEtale.proetalePostcompose`. Existence of a left adjoint is the
mathematical assertion; the extension-by-zero functor is a choice of it, and its defining
adjunction is supplied by the existence witness. The coefficient universe contains the
universe of the small pro-étale site, so the required coproducts of abelian groups are
available.

The left adjoint is moreover available as concrete data: `sheafifiedExtensionByZero` is the
composite of the forgetful functor to presheaves, left Kan extension along the opposite of
postcomposition, and sheafification, and `sheafifiedExtensionByZeroAdjunction` is its
adjunction to restriction. Uniqueness of left adjoints then pins the chosen functor down to a
canonical isomorphism with this construction.

## References

* [Stacks Project, Tag 09AE](https://stacks.math.columbia.edu/tag/09AE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ProEtale.Abelian

/-- Restriction of abelian sheaves on small pro-étale sites. -/
@[implicit_reducible]
def proetaleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v} := by
  letI := proetalePostcompose_isContinuous j
  exact (proetalePostcompose j).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- Restriction of abelian pro-étale sheaves has a left adjoint. -/
@[stacks 09AE "extension_by_zero_abelian", sga "4 IV 11.3.1" "pro-étale site, Ab"]
theorem exists_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    Nonempty (Σ F : Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v},
        F ⊣ proetaleRestriction j) := by
  let : (proetalePostcompose j).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    proetalePostcompose_isContinuous j
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
    hasSheafify_proetale.{u, v} X
  exact ⟨⟨Functor.sheafPullbackConstruction.sheafPullback
      (proetalePostcompose j) AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X),
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (proetalePostcompose j) AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)⟩⟩

/-- Extension by zero of abelian sheaves on the small pro-étale site. -/
@[implicit_reducible]
def extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  (Classical.choice (exists_extensionByZero j)).1

/-- Extension by zero is left adjoint to restriction. -/
def extensionByZero_adjunction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    extensionByZero j ⊣ proetaleRestriction j :=
  (Classical.choice (exists_extensionByZero j)).2

/-- Extension by zero of abelian sheaves on the small pro-étale site, as an explicit functor:
the composite of the inclusion of sheaves into presheaves, left Kan extension along the
opposite of postcomposition by `j`, and sheafification. -/
@[implicit_reducible, stacks 09AE "(2), the functor j_! : Ab(U_proetale) -> Ab(X_proetale) \
called extension by zero, as explicit data: the sheafification of the left Kan extension \
along the opposite of postcomposition by j"]
def sheafifiedExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    Sheaf (Scheme.ProEt.topology U) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} := by
  haveI := proetalePostcompose_isContinuous j
  haveI := hasSheafify_proetale.{u, v} X
  exact Functor.sheafPullbackConstruction.sheafPullback
    (proetalePostcompose j) AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The explicit extension-by-zero functor is left adjoint to restriction. -/
@[stacks 09AE "(2), the adjunction j_! ⊣ j^{-1} on abelian sheaves, witnessing that restriction \
along a weakly étale morphism has extension by zero as a left adjoint"]
def sheafifiedExtensionByZeroAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    sheafifiedExtensionByZero.{u, v} j ⊣ proetaleRestriction.{u, v} j := by
  haveI := proetalePostcompose_isContinuous j
  haveI := hasSheafify_proetale.{u, v} X
  exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proetalePostcompose j) AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The chosen extension-by-zero functor is canonically isomorphic to the explicit
sheafified left Kan extension, by uniqueness of left adjoints. -/
def extensionByZeroIsoSheafified {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    extensionByZero.{u, v} j ≅ sheafifiedExtensionByZero.{u, v} j :=
  (extensionByZero_adjunction.{u, v} j).leftAdjointUniq
    (sheafifiedExtensionByZeroAdjunction.{u, v} j)

end AlgebraicGeometry.ProEtale.Abelian

end
