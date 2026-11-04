module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom sheaf of a space, as a `SheafHom`, and its stalks

Let `(X, O_X)` be a topological space carrying a sheaf `O_X` of commutative rings, and let `F`
and `G` be sheaves of `O_X`-modules. The internal Hom sheaf `Hom_{O_X}(F, G)` of Stacks 03EM is
available on the ringed site of `X` as `AlgebraicGeometry.RingedSite.internalHomSheaf`, where it
is the sheaf of modules whose sections over an open `U` are the `O_U`-module maps `F|_U ⟶ G|_U`.

That description of the sections is exactly the datum packaged by the structure `SheafHom` of
Stacks 01CO, and it is what the stalk comparison of Stacks 01CP consumes. This file supplies the
missing link: the internal Hom sheaf of the ringed site, together with the identification of its
sections, as a term of `SheafHom`; and the resulting identification of its stalk at a point `x`,
when `F` is of finite presentation, with the module of `O_{X,x}`-linear maps `F_x →ₗ G_x`.

## Main definitions

* `Stacks.SheafOfModules.internalHomSheafHom`: `Hom_{O_X}(F, G)` as a term of `SheafHom`.
* `Stacks.SheafOfModules.internalHomSheafStalkEquiv`: for `F` of finite presentation, the
  `O_{X,x}`-linear identification `Hom_{O_X}(F, G)_x ≃ (F_x →ₗ[O_{X,x}] G_x)`.

## Main statements

* `Stacks.SheafOfModules.internalHomSheafStalkEquiv_germ`: the identification carries the germ of
  a local homomorphism, evaluated at the germ of a local section, to the germ of the value.

## Implementation notes

The internal Hom sheaf of the ringed site is *not* the internal hom `PresheafOfModules.ihom`
packaged by `Stacks.Cohomology.SheafHomComplex.sheafHom`: the former has underlying presheaf
`Stacks.SheafOfModules.internalHom` and the latter has `PresheafOfModules.ihom`, and the two are
not definitionally equal. So the `SheafHom` datum for the site-level sheaf has to be built, and
not obtained by transporting the existing one; the construction below is the one used for the
dual sheaf in `Stacks.AlgebraicGeometry.Reflexive.dualSheafHom`, with the target generalised from
the structure sheaf to an arbitrary `G`.

Both naturality axioms hold by `rfl` after the sections are named: a section of the internal Hom
sheaf over `U` *is* a linear natural family on the slice over `U`, so restricting the family and
restricting the morphism it names are the same operation, and likewise for the scalar action.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  (F G : SheafOfModules.{u} (structureSheaf Rc))

/-- **The internal Hom sheaf of a space in the sense of Stacks 01CO.** The sheaf
`Hom_{O_X}(F, G)` of the ringed site of `X`, together with the identification of its sections
over every open `U` with the `O_U`-module maps `F|_U ⟶ G|_U`, and the two axioms saying that this
identification is compatible with restriction and with the action of the structure sheaf. -/
@[ega "0 4.1.5" "special case"]
def internalHomSheafHom : SheafHom Rc F G where
  obj := RingedSite.internalHomSheaf (ringedSite Rc) F G
  sectionsEquiv U := by
    change ((restrFun Rc.obj U).obj F.val ⟶ (restrFun Rc.obj U).obj G.val) ≃+
      (F.over U ⟶ G.over U)
    let e : (F.over U ⟶ G.over U) ≃
        ((restrFun Rc.obj U).obj F.val ⟶ (restrFun Rc.obj U).obj G.val) :=
      (SheafOfModules.fullyFaithfulForget ((structureSheaf Rc).over U)).homEquiv
        (X := F.over U) (Y := G.over U)
    exact
      { toFun := e.symm
        invFun := e
        left_inv := e.apply_symm_apply
        right_inv := e.symm_apply_apply
        map_add' := by
          intro f g
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          rfl }
  restrict_natural := by
    intro U V hVU s W hWV m
    change ((homRestr Rc.obj F.val G.val (homOfLE hVU) s).app
      (op (Over.mk (homOfLE hWV)))) m = _
    rfl
  smul_natural := by
    intro U c s W hWU m
    change ((smulHom Rc.obj F.val G.val U c s).app (op (Over.mk (homOfLE hWU)))) m = _
    rfl

/-- The underlying sheaf of modules of `internalHomSheafHom` is the internal Hom sheaf of the
ringed site of `X`. -/
theorem internalHomSheafHom_obj :
    (internalHomSheafHom Rc F G).obj = RingedSite.internalHomSheaf (ringedSite Rc) F G :=
  rfl

/-- The identification of sections of `internalHomSheafHom` is the identity on the underlying
natural families: the morphism `F|_U ⟶ G|_U` named by a section `s` over `U` has, at the identity
of `U`, the component of `s` at the identity of `U`. -/
theorem internalHomSheafHom_sectionsEquiv_app {U : Opens X}
    (s : (RingedSite.internalHomSheaf (ringedSite Rc) F G).val.obj (op U))
    (m : (commVal (Rc := Rc) F).obj (op U)) :
    ((internalHomSheafHom Rc F G).sectionsEquiv U s).val.app (op (Over.mk (𝟙 U))) m
      = s.app (op (Over.mk (𝟙 U))) m :=
  rfl

variable [F.IsFinitePresentation]

/-- **The stalk of an internal Hom sheaf at a finitely presented source (Stacks 01CP).** For `F`
of finite presentation, the stalk of `Hom_{O_X}(F, G)` at a point `x` is the module of
`O_{X,x}`-linear maps `F_x →ₗ G_x`. -/
@[ega "0 5.2.6"]
def internalHomSheafStalkEquiv (x : X) :
    modStalk (RingedSite.internalHomSheaf (ringedSite Rc) F G) x ≃ₗ[ringStalk Rc x]
      (modStalk F x →ₗ[ringStalk Rc x] modStalk G x) :=
  (sheafHomStalkLinearEquivOfFinitePresentation (internalHomSheafHom Rc F G) x).equiv

/-- **The stalk identification of Stacks 01CP on germs.** The identification carries the germ at
`x` of a local homomorphism `s`, evaluated at the germ at `x` of a local section `m`, to the germ
at `x` of the value of `s` on `m`. -/
theorem internalHomSheafStalkEquiv_germ (x : X) (U : Opens X) (hxU : x ∈ U)
    (s : (RingedSite.internalHomSheaf (ringedSite Rc) F G).val.obj (op U))
    (m : (commVal (Rc := Rc) F).obj (op U)) :
    internalHomSheafStalkEquiv Rc F G x
        (germAt (RingedSite.internalHomSheaf (ringedSite Rc) F G) U x hxU s)
        (germAt F U x hxU m)
      = germAt G U x hxU (s.app (op (Over.mk (𝟙 U))) m) :=
  (sheafHomStalkLinearEquivOfFinitePresentation (internalHomSheafHom Rc F G) x).germ_apply
    U hxU s m

end Stacks.SheafOfModules

end
