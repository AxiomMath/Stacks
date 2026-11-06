module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensorSectionGerm

/-!
# The germ decomposition of the presheaf fibre of `f_{p!}F`, `Λ`-linearly

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring and let `F` be a sheaf of `Λ`-modules on `X_étale`. The fibre at a geometric point `ȳ` of
`Y` of the *presheaf* `f_{p!}F` is the direct sum of the stalks of `F` over the geometric fibre,
by the germ decomposition `AlgebraicGeometry.SmallEtale.finiteSupportStalkToFiberStalks` of
Stacks 0F6P. That decomposition is a map of abelian groups; this file lifts it to the
`Λ`-modules, so that it can be tensored with a stalk of a sheaf of `Λ`-modules.

The point of lifting *this* map, rather than transporting the sheaf-level decomposition
`AlgebraicGeometry.SmallEtale.modShriekStalkIso`, is that the germ formula on a generator
(`AlgebraicGeometry.SmallEtale.modFiniteSupportGenerator_comp_presheafFiber`) is stated for it.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modFiniteSupportFiberIso` — **the fibre of `f_{p!}F`
  decomposes over the geometric fibre, `Λ`-linearly.**

## Main results

* `AlgebraicGeometry.SmallEtale.modFiniteSupportFiberIso_generator` — **the decomposition on a
  generator** is the family of germs of the supported section.

## Implementation notes

The `Λ`-linearity is naturality of `finiteSupportStalkToFiberStalks` applied to multiplication
by a scalar on the underlying abelian sheaf: the scalar action on the fibre of a presheaf of
`Λ`-modules is the fibre of the scalar action on that presheaf, and the scalar action on
`⨁_{f(x̄) = ȳ} F_x̄` is summandwise the scalar action on the stalks.

Nothing here carries a `stacks` attribute: this is one step of the stalk computation behind
[Stacks, Tag 0GKF].

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace Stacks

/-- **A commuting square transported along a leading factor.** If `n` and `g` are intertwined by
`i`, and `g` and `m` by `k`, then `n` and `m` are intertwined by `i ≫ k`. Isolated as a statement
about abstract morphisms so that it applies to terms whose types agree only up to unfolding a
definition. -/
public theorem comp_intertwine {C : Type*} [Category* C] {A P Q : C} (i : A ⟶ P) (k : P ⟶ Q)
    (m : Q ⟶ Q) (n : A ⟶ A) (g : P ⟶ P) (h1 : n ≫ i = i ≫ g) (h2 : g ≫ k = k ≫ m) :
    (i ≫ k) ≫ m = n ≫ i ≫ k := by
  rw [Category.assoc, ← h2, ← Category.assoc, ← h1, Category.assoc]

end Stacks

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **The germ decomposition of the fibre of the presheaf `f_{p!}F`, as a map of abelian
groups.** The comparison of the fibre formed in `Λ`-modules with the abelian fibre, followed by
the germ decomposition of Stacks 0F6P. -/
public def modFiniteSupportFiberAbIso (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (s : GeometricPoint Y.obj) :
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).obj
        ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber.obj
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ≅
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).obj
        ((moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj F) :=
  (((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).app
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)).symm ≪≫
    finiteSupportStalkIso.{u, max (u + 1) v} B f s
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) (fun _ => inferInstance)

/-- **The fibre of the presheaf `f_{p!}F` decomposes over the geometric fibre, `Λ`-linearly.**
The germ decomposition of Stacks 0F6P is `Λ`-linear: the scalar action on the fibre of a
presheaf of `Λ`-modules is the fibre of the scalar action on that presheaf, and the germ
decomposition is natural in the abelian sheaf. -/
public def modFiniteSupportFiberIso (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (s : GeometricPoint Y.obj) :
    (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.obj
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) ≅
      (moduleFiberStalks.{u, v, max (u + 1) v} B Λ f s).obj F :=
  ModuleCat.isoMk (modFiniteSupportFiberAbIso B Λ f F s) fun r => by
    have hnat := ((geometricPointSitePoint B Y.obj Y.property s).presheafFiberCompIso
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})).inv.naturality
      (Stacks.ModuleCatLift.presheafModuleSmul Λ
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) r)
    simp only [Functor.comp_map,
      Stacks.ModuleCatLift.presheafFiber_map_presheafModuleSmul] at hnat
    exact Stacks.comp_intertwine _ _ _ _ _ hnat
      (finiteSupportStalkToFiberStalks_natural.{u, max (u + 1) v} B f s (fun _ => inferInstance)
        (Stacks.ModuleCatLift.sheafScalarEnd Λ (SmallEtale.topology B X.obj X.property) F r).asHom)

/-- **The `Λ`-linear germ decomposition on a generator** is the family of germs of the supported
section: this is `AlgebraicGeometry.SmallEtale.modFiniteSupportGenerator_comp_presheafFiber`,
read through the `Λ`-linear lift. -/
public theorem modFiniteSupportGenerator_comp_modFiniteSupportFiberIso
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (s : GeometricPoint Y.obj)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1) :
    modFiniteSupportGenerator B Λ f F U.1 E ≫
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)) ≫
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}).map
          (modFiniteSupportFiberIso B Λ f F s).hom =
      fiberStalkHom.{u, max (u + 1) v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) U.1 U.2 E :=
  modFiniteSupportGenerator_comp_presheafFiber B Λ f F s U E

/-- **The `Λ`-linear germ decomposition on a generator**, on elements: the germ of the generator
`(Z, a)` goes to the family of germs of `a` over the geometric fibre. -/
public theorem modFiniteSupportFiberIso_generator
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (s : GeometricPoint Y.obj)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      U.1).obj E) :
    (modFiniteSupportFiberIso B Λ f F s).hom
        ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)
          (modFiniteSupportGenerator B Λ f F U.1 E a)) =
      fiberStalkSum.{u, max (u + 1) v} B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) U.1 U.2 E a :=
  ConcreteCategory.congr_hom
    (modFiniteSupportGenerator_comp_modFiniteSupportFiberIso B Λ f F s U E) a

end AlgebraicGeometry.SmallEtale

end
