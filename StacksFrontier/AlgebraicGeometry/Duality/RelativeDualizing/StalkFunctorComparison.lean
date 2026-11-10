module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunction

/-!
# The two stalk functors on sheaves of modules of a scheme agree

Let `X` be a scheme and `x` a point of `X`. The repository carries two functors
`X.Modules ⥤ ModuleCat 𝒪_{X,x}` taking the stalk at `x`:

* `Stacks.Duality.schemeStalkModuleFunctor`, which is
  `AlgebraicGeometry.SheafOfModules.stalkFunctor` — a colimit taken in modules over the
  `RingCat`-valued stalk of the sheaf of rings — followed by restriction of scalars along
  `SemilinearStalk.commStalkIso`;
* `Stacks.ModuleSkyscraper.modulesStalkFunctor`, which is the stalk of the underlying presheaf of
  modules taken directly over the `CommRingCat`-valued stalk `𝒪_{X,x} = X.presheaf.stalk x`.

This file identifies them.

## Main definitions

* `Stacks.Duality.schemeStalkModuleIso` — the comparison at one sheaf of modules, as an
  isomorphism of `𝒪_{X,x}`-modules.
* `Stacks.Duality.schemeStalkModuleFunctorIso` — **the two stalk functors are isomorphic**, as
  functors `X.Modules ⥤ ModuleCat 𝒪_{X,x}`.

## Main results

* `Stacks.Duality.commStalkIso_inv_smul` — the scalar action obtained by restricting along
  `SemilinearStalk.commStalkIso` is the native action of `𝒪_{X,x}` on the stalk.
* `Stacks.Duality.schemeStalkModuleFunctorIso_germ` and
  `Stacks.Duality.schemeStalkModuleFunctorIso_inv_germ` — **the comparison matches germs**: both
  directions send the germ of a section `s ∈ Γ(G, U)` at `x` to the germ of `s` at `x`. This is
  what makes the isomorphism usable, since a germ is the only description either side offers of a
  general element of the stalk (`TopCat.Presheaf.exists_germ_eq`).

## Implementation notes

This file exists because the repository carries two parallel stalk functors on the sheaves of
modules of a scheme, with the same source and the same target, built from different colimits, and
nothing compared them; a proof needing to move between them had no way to do so. Neither functor is
removed here — the choice between them is discussed in the module documentation of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackStalkColimit.lean`, where the
`CommRingCat`-valued stalk is load-bearing because `ModuleCat.extendScalars` and
`AlgebraicGeometry.Scheme.Modules.IsAssociatedPoint` are stated over it — and unifying them is a
refactor of both developments rather than a change to either.

The comparison is the identity on underlying sets. Both functors compute the stalk of the *same*
presheaf of abelian groups, namely `G.val.presheaf`, through the *same* filtered colimit
`TopCat.Presheaf.stalk (C := AddCommGrpCat)`, and both send a morphism to the map that colimit
induces; the two differ only in the ring the result is read over. So the content is entirely the
scalar comparison `Stacks.Duality.commStalkIso_inv_smul`, which is the existing abelian-group-level
comparison `SemilinearStalk.comm_smul_eq` — "on the stalk the `CommRingCat` and `RingCat` actions
agree through `SemilinearStalk.commStalkRingEquiv`" — read along the inverse of
`SemilinearStalk.commStalkIso`. Nothing is rebuilt: `comm_smul_eq` already reduces an arbitrary
stalk element to a germ, so no second germ induction is performed, and the germ formulas and the
naturality square hold by `rfl`.

The action installed by `ModuleCat.restrictScalars` along a ring map `f` is `Module.compHom`, so
the action of `r` is the action of `f r` definitionally; this is why `commStalkIso_inv_smul` is
stated about the `RingCat`-stalk action of `(SemilinearStalk.commStalkIso R y).inv.hom r` directly
rather than about `ModuleCat.restrictScalars`. For the same reason the statement is made for a
presheaf of modules over `R ⋙ forget₂ CommRingCat RingCat` rather than for a sheaf of modules on a
scheme: that is the shape the two module structures on the stalk are registered for, so instance
search finds them without unfolding `AlgebraicGeometry.Scheme.ringCatSheaf`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Duality

/-- The action of the `CommRingCat`-valued stalk `R_y` on the stalk of a presheaf of modules
obtained by restricting the `RingCat`-stalk action along `SemilinearStalk.commStalkIso` is the
native action of `R_y`. This is `SemilinearStalk.comm_smul_eq` read along the inverse of the
comparison isomorphism. -/
theorem commStalkIso_inv_smul {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) (y : Y)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (r : R.stalk y) (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf y) :
    (SemilinearStalk.commStalkIso R y).inv.hom r • m = r • m := by
  have h : SemilinearStalk.commStalkRingEquiv R y
      ((SemilinearStalk.commStalkIso R y).inv.hom r) = r := by
    change ((SemilinearStalk.commStalkIso R y).inv ≫
      (SemilinearStalk.commStalkIso R y).hom).hom r = r
    rw [Iso.inv_hom_id]
    rfl
  refine Eq.trans ?_ (congrArg (fun t => t • m) h)
  exact (SemilinearStalk.comm_smul_eq R y M _ m).symm

variable {X : Scheme.{u}} (x : X)

/-- **The two stalk modules agree.** For a sheaf of `𝒪_X`-modules `G`, the stalk at `x` computed by
`Stacks.Duality.schemeStalkModuleFunctor` is the stalk computed by
`Stacks.ModuleSkyscraper.modulesStalkFunctor`, as a module over `𝒪_{X,x}`. The underlying map is
the identity of `TopCat.Presheaf.stalk G.val.presheaf x`; the content is
`Stacks.Duality.commStalkIso_inv_smul`. -/
def schemeStalkModuleIso (G : X.Modules) :
    (schemeStalkModuleFunctor x).obj G ≅
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj G :=
  LinearEquiv.toModuleIso (show (schemeStalkModuleFunctor x).obj G ≃ₗ[X.presheaf.stalk x]
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj G from
    { toFun := fun m => m
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => commStalkIso_inv_smul X.presheaf x G.val r m })

/-- **The two stalk functors on sheaves of modules of a scheme agree.** -/
def schemeStalkModuleFunctorIso :
    schemeStalkModuleFunctor x ≅ Stacks.ModuleSkyscraper.modulesStalkFunctor X x :=
  NatIso.ofComponents (schemeStalkModuleIso x) fun _ => rfl

/-- **The comparison matches germs.** -/
theorem schemeStalkModuleFunctorIso_germ (G : X.Modules) (U : X.Opens) (hx : x ∈ U) (s : Γ(G, U)) :
    ((schemeStalkModuleFunctorIso x).hom.app G).hom
        (show (schemeStalkModuleFunctor x).obj G from
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) G.val.presheaf U x hx).hom s) =
      (show (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj G from
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) G.val.presheaf U x hx).hom s) :=
  rfl

/-- `Stacks.Duality.schemeStalkModuleFunctorIso_germ` for the inverse direction. -/
theorem schemeStalkModuleFunctorIso_inv_germ (G : X.Modules) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(G, U)) :
    ((schemeStalkModuleFunctorIso x).inv.app G).hom
        (show (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj G from
          (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) G.val.presheaf U x hx).hom s) =
      (show (schemeStalkModuleFunctor x).obj G from
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) G.val.presheaf U x hx).hom s) :=
  rfl

end Stacks.Duality

end
