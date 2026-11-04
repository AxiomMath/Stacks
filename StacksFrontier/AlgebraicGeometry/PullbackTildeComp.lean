module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComposition

/-!
# The affine pullback comparison at a single module, under composition of ring maps

Let `f : R ⟶ S` and `g : S ⟶ T` be homomorphisms of commutative rings. Tag 01I9 identifies the
pullback of the associated sheaf `M^~` of an `R`-module `M` along `Spec f` with the associated
sheaf of the extension of scalars `S ⊗_R M`, and that identification is compatible with
composition: pulling back along `Spec (f ≫ g)` and extending scalars from `R` to `T` in one step
agrees with doing each of the two steps in turn, read through
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `ModuleCat.extendScalarsComp`. This file
records that compatibility at a single module, as an equation between morphisms of sheaves of
modules on `Spec T`.

The compatibility itself, as an equality of natural isomorphisms of functors
`ModuleCat R ⥤ (Spec T).Modules`, is `AlgebraicGeometry.pullbackTildeIso_comp`, proved in
`StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComposition`; nothing is reproved
here. What that statement leaves implicit is its value at a module: both of its sides are built
from `CategoryTheory.Functor.isoWhiskerLeft`, `CategoryTheory.Functor.isoWhiskerRight` and the
associator, so a consumer holding a concrete morphism out of `(Spec (f ≫ g))^* (M^~)` must first
evaluate four whiskerings and three associators at `M` before the equation can be used. The
three results below perform that evaluation once.

## Main results

* `AlgebraicGeometry.pullbackTildeIso_hom_app_comp`: the component at `M` of the affine pullback
  comparison for `f ≫ g`, as the composite of the factorization
  `AlgebraicGeometry.pullbackSpecMapCompIso` of the pullback, the pullback along `Spec g` of the
  comparison for `f`, the comparison for `g` at `S ⊗_R M`, and the associated sheaf of the
  inverse of `ModuleCat.extendScalarsComp`.
* `AlgebraicGeometry.pullbackTildeIso_hom_app_comp_pullbackComp`: the same equation with
  `AlgebraicGeometry.pullbackSpecMapCompIso` unfolded into
  `AlgebraicGeometry.Scheme.Modules.pullbackCongr` applied to `AlgebraicGeometry.Spec.map_comp`
  followed by the inverse of `AlgebraicGeometry.Scheme.Modules.pullbackComp`.
* `AlgebraicGeometry.pullbackTildeIso_app_comp`: the same statement as an equality of
  isomorphisms rather than of their forward morphisms. This is the form to use when the inverse
  direction is wanted: applying `congrArg CategoryTheory.Iso.inv` to it gives the inverse of the
  comparison for `f ≫ g` as the reversed composite of the inverses, with no simplification of
  `(pullbackTildeIso R T (f ≫ g)).inv` needed.

## Implementation notes

The first statement is a componentwise reading of one equality of isomorphisms, obtained by
`CategoryTheory.NatTrans.congr_app` applied to `congrArg Iso.hom` of
`AlgebraicGeometry.pullbackTildeIso_comp`. Forming `congrArg` on the projection `Iso.hom` rather
than on the anonymous function `fun e => e.hom.app M` matters: in the latter the domain of the
function is still a metavariable when the projection is elaborated, and field notation then
fails.

The simp set that evaluates the whiskerings and associators is kept as small as it can be. This
is not cosmetic. Rewriting a hypothesis of this size builds a chain of `Eq.mpr` whose motives
carry the whole sheaf-of-modules expression, and the budget that chain consumes is the same
budget the kernel then needs to typecheck the finished term; one superfluous rewrite is enough
to turn the result into a `(kernel) deterministic timeout` with no elaboration error to point
at. The inverse direction is why the third statement is phrased at the level of isomorphisms
instead of being a fourth lemma about `(pullbackTildeIso R T (f ≫ g)).inv`: reaching that lemma
the same way as the first costs a simp set containing `Iso.trans_inv`, which reassociates the
composite as it rewrites, and every simp set tried along that route left the kernel too little
budget to typecheck the result. Packaging the component as an isomorphism avoids the question —
`CategoryTheory.Iso.ext` is one application and no rewriting at all, and both directions are
then `congrArg` away.

The unfolding of `AlgebraicGeometry.pullbackSpecMapCompIso` is isolated in a `have ... := rfl`
and only then rewritten, rather than being performed by `simp [pullbackSpecMapCompIso]`. The
objects on the two sides must also be spelled `(tilde.functor R).obj M` and not `tilde M`: these
are definitionally equal, but the composite of the two factors elaborated at the second spelling
is not type-correct at the transparency `rw` uses, and the rewrite fails.

Nothing here is a new input to the library's mathematics. The implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel` list the composition
compatibility of Tag 01I9 among the results the library does not have; that list was written in
the same change that added `AlgebraicGeometry.pullbackTildeIso_comp`, and is stale on this
point. The compatibility is one of the two inputs to the cocycle identity for part (2) of
Tag 08DW, which in turn is what makes the determinant construction of Tag 0FJX compatible with
derived pullback.

The shared universe is imposed by Mathlib's `tilde.functor` and the scheme-module API; the
statements hold in every such universe.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/
@[expose] public noncomputable section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory
open scoped ChangeOfRings

universe u

/-- The affine pullback comparison for `f ≫ g`, at an `R`-module `M`: it is the factorization
`pullbackSpecMapCompIso` of the pullback along `Spec (f ≫ g)`, followed by the pullback along
`Spec g` of the comparison for `f`, followed by the comparison for `g` at `S ⊗_R M`, followed by
the associated sheaf of the inverse of `ModuleCat.extendScalarsComp`. -/
public theorem pullbackTildeIso_hom_app_comp (R S T : CommRingCat.{u}) (f : R ⟶ S) (g : S ⟶ T)
    (M : ModuleCat R) :
    (pullbackTildeIso R T (f ≫ g)).hom.app M =
      (pullbackSpecMapCompIso R S T f g).hom.app ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullback (Spec.map g)).map ((pullbackTildeIso R S f).hom.app M) ≫
        (pullbackTildeIso S T g).hom.app ((ModuleCat.extendScalars f.hom).obj M) ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (pullbackTildeIso_comp R S T f g)) M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp] at h
  exact h

/-- The affine pullback comparison for `f ≫ g`, at an `R`-module `M`, with the factorization of
the pullback along `Spec (f ≫ g)` spelled out as `Scheme.Modules.pullbackCongr` applied to
`Spec.map_comp`, followed by the inverse of `Scheme.Modules.pullbackComp`. -/
public theorem pullbackTildeIso_hom_app_comp_pullbackComp (R S T : CommRingCat.{u}) (f : R ⟶ S)
    (g : S ⟶ T) (M : ModuleCat R) :
    (pullbackTildeIso R T (f ≫ g)).hom.app M =
      (Scheme.Modules.pullbackCongr (Spec.map_comp f g)).hom.app ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv.app
          ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullback (Spec.map g)).map ((pullbackTildeIso R S f).hom.app M) ≫
        (pullbackTildeIso S T g).hom.app ((ModuleCat.extendScalars f.hom).obj M) ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) := by
  have e : (pullbackSpecMapCompIso R S T f g).hom.app ((tilde.functor R).obj M) =
      (Scheme.Modules.pullbackCongr (Spec.map_comp f g)).hom.app ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv.app
          ((tilde.functor R).obj M) := rfl
  rw [pullbackTildeIso_hom_app_comp R S T f g M, e, Category.assoc]

/-- The affine pullback comparison for `f ≫ g`, at an `R`-module `M`, as an equality of
isomorphisms: the comparison at `M` is the factorization `pullbackSpecMapCompIso` of the pullback
along `Spec (f ≫ g)`, followed by the pullback along `Spec g` of the comparison for `f`, followed
by the comparison for `g` at `S ⊗_R M`, followed by the associated sheaf of the inverse of
`ModuleCat.extendScalarsComp`. Apply `congrArg CategoryTheory.Iso.inv` for the inverses. -/
public theorem pullbackTildeIso_app_comp (R S T : CommRingCat.{u}) (f : R ⟶ S) (g : S ⟶ T)
    (M : ModuleCat R) :
    (pullbackTildeIso R T (f ≫ g)).app M =
      (pullbackSpecMapCompIso R S T f g).app ((tilde.functor R).obj M) ≪≫
        (Scheme.Modules.pullback (Spec.map g)).mapIso ((pullbackTildeIso R S f).app M) ≪≫
        (pullbackTildeIso S T g).app ((ModuleCat.extendScalars f.hom).obj M) ≪≫
        (tilde.functor T).mapIso ((ModuleCat.extendScalarsComp f.hom g.hom).app M).symm :=
  Iso.ext (pullbackTildeIso_hom_app_comp R S T f g M)

end AlgebraicGeometry
