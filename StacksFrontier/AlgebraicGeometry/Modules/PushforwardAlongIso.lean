module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartRestriction
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections

/-!
# Relative differential forms under pushforward along an isomorphism

Pushing modules forward along an isomorphism of schemes is an equivalence whose inverse is the
inverse image (`AlgebraicGeometry.Scheme.Modules.pushforwardEquivOfIso`,
`AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforward`). For relative differential forms this
gives: pushing the forms of `g ≫ q` forward along an isomorphism `g` returns the forms of `q`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pushforwardRestrictObjIso`: restricting a module along an
  isomorphism and pushing it forward again returns it.
* `AlgebraicGeometry.Scheme.Modules.pushforwardRelativeFormsIsoOfIso`:
  `g_*Ω^n_{g ≫ q} ≅ Ω^n_q` for an isomorphism `g`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.DifferentialsRestrict

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {Y X : Scheme.{u}}

/-- **Restricting a module along an isomorphism and pushing it forward again returns it.** -/
def pushforwardRestrictObjIso (e : Y ≅ X) (N : X.Modules) :
    (pushforward e.hom).obj (restrict N e.hom) ≅ N :=
  (pushforward e.hom).mapIso
      ((restrictFunctorIsoPullback e.hom).app N ≪≫ (pullbackIsoPushforward e.symm).app N) ≪≫
    (pushforwardComp e.inv e.hom ≪≫ pushforwardCongr e.inv_hom_id ≪≫
      pushforwardId X).app N

/-- **The relative differential forms of a composite through an isomorphism, pushed forward along
that isomorphism, are the relative differential forms of the other factor**: `g_*Ω^n_{g ≫ q}`
is `Ω^n_q`. -/
def pushforwardRelativeFormsIsoOfIso {S : Scheme.{u}} (e : Y ≅ X) (q : X ⟶ S) (n : ℤ) :
    (pushforward e.hom).obj (relativeDifferentialForms (e.hom ≫ q) n) ≅
      relativeDifferentialForms q n :=
  (pushforward e.hom).mapIso
      (restrictFormsIso e.hom q (e.hom ≫ q) (𝟙 S) (by simp) n).symm ≪≫
    pushforwardRestrictObjIso e (relativeDifferentialForms q n)

end AlgebraicGeometry.Scheme.Modules

end
