module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleFibrewise
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSheafEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# A sheaf of `π^{-1}O`-modules on `Δ × C` *is* a simplicial sheaf of `O`-modules

`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialModuleFibrewise.lean` reads a
sheaf of `π^{-1}O`-modules on the simplicial site `Δ × C` of Stacks 09D0 as a simplicial sheaf
of `O`-modules, by restricting it to the fibres `{n} × C`. This file proves that this reading is
an **equivalence of categories**, by constructing its inverse: uncurrying.

It is the module-coefficient form of
`Stacks.SimplicialModules.simplicialSheafEquivalence`, whose coefficients are of the form
`Sheaf J A` and which therefore does not apply to sheaves of modules.

## Main definitions

* `Stacks.SimplicialModules.uncurryModPresheaf`: the presheaf of `π^{-1}O`-modules obtained by
  uncurrying a simplicial sheaf of `O`-modules.
* `Stacks.SimplicialModules.uncurryMod`: the same, read as a sheaf of modules.
* `Stacks.SimplicialModules.simplicialModuleEquivalence`: **the equivalence.**

## Implementation notes

As for the coefficient-free `Stacks.SimplicialModules.simplicialSheafEquivalence`, both round
trips are the identity on underlying data, so every component of the unit and the counit is
`CategoryTheory.Iso.refl`, and what has to be checked is only that these components are natural.
All the naturality checks reduce to the single equation
`CategoryTheory.Functor.map_op_prod_fst_comp_snd`, which factors the restriction of a presheaf on
a product along `(φ, ψ)` as the restriction along `(φ, 𝟙)` followed by the restriction along
`(𝟙, ψ)`.

No base change of scalars appears anywhere: the structure sheaf on `Δ × C` is `π^{-1}O`, so a
section of it over `(n, U)` *is* a section of `O` over `U`, and
`Stacks.SimplicialModules.fibreRingMap` is the identity. This is what makes the uncurried
presheaf of modules a presheaf of modules over `π^{-1}O` on the nose, with the restriction maps
of the two variables composed in either order.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SimplicialModules

open Stacks.Cohomology.DerivedLowerShriek

universe w

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})

/-! ### Uncurrying -/

/-- **The uncurrying of a simplicial sheaf of `O`-modules**, as a presheaf of
`π^{-1}O`-modules on `Δ × C`: the sections over `(n, U)` are the sections of `G_n` over `U`,
which are `O(U)`-modules, and `O(U)` is the sections of `π^{-1}O` over `(n, U)`. The restriction
along `(φ, ψ)` is the structure map of `G` at `φ` followed by the restriction of `G_n` along
`ψ`. -/
def uncurryModPresheaf (G : CategoryTheory.SimplicialObject (SheafOfModules.{w} O)) :
    PresheafOfModules.{w} (projectionRing C J O).obj where
  obj X := (G.obj (op X.unop.1)).val.obj (op X.unop.2)
  map {X Y} f := (G.map (f.unop.1).op).val.app (op X.unop.2) ≫
    (G.obj (op Y.unop.1)).val.map (f.unop.2).op
  map_comp {X Y Z} f g := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
    change (G.obj (op Z.unop.1)).val.map ((f.unop.2).op ≫ (g.unop.2).op)
          ((G.map ((f.unop.1).op ≫ (g.unop.1).op)).val.app (op X.unop.2) x) =
        (G.obj (op Z.unop.1)).val.map (g.unop.2).op
          ((G.map (g.unop.1).op).val.app (op Y.unop.2)
            ((G.obj (op Y.unop.1)).val.map (f.unop.2).op
              ((G.map (f.unop.1).op).val.app (op X.unop.2) x)))
    rw [G.map_comp, PresheafOfModules.map_comp_apply,
      PresheafOfModules.naturality_apply]
    rfl

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- On sections, the restriction maps of the uncurried presheaf of modules are the structure map
of `G` followed by a restriction inside a single degree. -/
theorem uncurryModPresheaf_map_apply
    (G : CategoryTheory.SimplicialObject (SheafOfModules.{w} O))
    {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y)
    (x : (uncurryModPresheaf C J O G).obj X) :
    (uncurryModPresheaf C J O G).map f x =
      (G.obj (op Y.unop.1)).val.map (f.unop.2).op
        ((G.map (f.unop.1).op).val.app (op X.unop.2) x) :=
  rfl

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The uncurried presheaf of modules is a sheaf for the topology `Δ × C` inherits from `(C, J)`
along the projection: being a sheaf there is the levelwise condition
(`CategoryTheory.Presheaf.isSheaf_inheritedTopology_prodSnd`), and in the level `n` the uncurried
presheaf is the underlying abelian presheaf of the sheaf of modules `G_n`. -/
theorem isSheaf_uncurryModPresheaf
    (G : CategoryTheory.SimplicialObject (SheafOfModules.{w} O)) :
    Presheaf.IsSheaf (projectionTopology C J) (uncurryModPresheaf C J O G).presheaf := by
  refine Presheaf.isSheaf_inheritedTopology_prodSnd J _ fun n => ?_
  refine (Presheaf.isSheaf_of_iso_iff
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} f => ?_) :
      (Functor.prodSectionSnd n).op ⋙ (uncurryModPresheaf C J O G).presheaf ≅
        (G.obj (op n)).val.presheaf)).2 (G.obj (op n)).isSheaf
  ext x
  change (G.obj (op n)).val.map f ((G.map (𝟙 (op n))).val.app (op X.unop) x) =
    (G.obj (op n)).val.map f x
  rw [G.map_id]
  rfl

/-- **A simplicial sheaf of `O`-modules read as a sheaf of `π^{-1}O`-modules on `Δ × C`**, by
uncurrying. This is the inverse of `Stacks.SimplicialModules.fibrewiseMod`. -/
def uncurryMod :
    CategoryTheory.SimplicialObject (SheafOfModules.{w} O) ⥤
      SheafOfModules.{w} (projectionRing C J O) where
  obj G := ⟨uncurryModPresheaf C J O G, isSheaf_uncurryModPresheaf C J O G⟩
  map {G G'} η :=
    ⟨{ app := fun X => (η.app (op X.unop.1)).val.app (op X.unop.2)
       naturality := fun {X Y} f => by
         refine ModuleCat.hom_ext
           (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
         change (η.app (op Y.unop.1)).val.app (op Y.unop.2)
               ((G.obj (op Y.unop.1)).val.map (f.unop.2).op
                 ((G.map (f.unop.1).op).val.app (op X.unop.2) x)) =
             (G'.obj (op Y.unop.1)).val.map (f.unop.2).op
               ((G'.map (f.unop.1).op).val.app (op X.unop.2)
                 ((η.app (op X.unop.1)).val.app (op X.unop.2) x))
         rw [PresheafOfModules.naturality_apply]
         refine congrArg _ ?_
         exact congrArg (fun u : G.obj (op X.unop.1) ⟶ G'.obj (op Y.unop.1) =>
           (u.val.app (op X.unop.2)) x) (η.naturality (f.unop.1).op) }⟩
  map_id G := rfl
  map_comp η θ := rfl

/-! ### The equivalence -/

/-- Uncurrying the fibres of a sheaf of `π^{-1}O`-modules gives it back: both round trips are the
identity on sections, and the only thing to check is that the identity is natural, which is the
factorisation `CategoryTheory.Functor.map_op_prod_fst_comp_snd`. -/
def fibrewiseModUncurryIso :
    𝟭 (SheafOfModules.{w} (projectionRing C J O)) ≅
      fibrewiseMod C J O ⋙ uncurryMod C J O :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun {X Y} f => by
        refine ModuleCat.hom_ext
          (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
        change M.val.presheaf.map
              (CategoryTheory.Prod.mkHom f.unop.1 f.unop.2).op x =
            M.val.presheaf.map
              (CategoryTheory.Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
              (M.val.presheaf.map
                (CategoryTheory.Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x)
        rw [Functor.map_op_prod_fst_comp_snd M.val.presheaf f.unop.1 f.unop.2]
        rfl)))
    (fun {M N} φ => by
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun X => ?_))
      refine ModuleCat.hom_ext
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      rfl)

/-- The fibres of the uncurrying of a simplicial sheaf of `O`-modules are the sheaves of modules
one started with. -/
def uncurryModFibrewiseIso :
    uncurryMod C J O ⋙ fibrewiseMod C J O ≅
      𝟭 (CategoryTheory.SimplicialObject (SheafOfModules.{w} O)) :=
  NatIso.ofComponents
    (fun G => NatIso.ofComponents
      (fun n => (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun {U V} ψ => by
          refine ModuleCat.hom_ext
            (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
          change (G.obj n).val.map ψ ((G.map (𝟙 n)).val.app U x) = (G.obj n).val.map ψ x
          rw [G.map_id]
          rfl)))
      (fun {m n} α => by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U => ?_))
        refine ModuleCat.hom_ext
          (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
        change (G.obj n).val.presheaf.map (𝟙 U) ((G.map α).val.app U x) =
          (G.map α).val.app U x
        rw [CategoryTheory.Functor.map_id]
        rfl))
    (fun {G G'} η => by
      refine NatTrans.ext (funext fun n => ?_)
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U => ?_))
      refine ModuleCat.hom_ext
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      rfl)

/-- **Stacks 09D0 at module coefficients.** A sheaf of `π^{-1}O`-modules on `Δ × C` *is* a
simplicial sheaf of `O`-modules on `C`: levelwise restriction to the fibres and uncurrying are an
equivalence of categories. This is the module-coefficient form of
`Stacks.SimplicialModules.simplicialSheafEquivalence`. -/
def simplicialModuleEquivalence :
    SheafOfModules.{w} (projectionRing C J O) ≌
      CategoryTheory.SimplicialObject (SheafOfModules.{w} O) :=
  CategoryTheory.Equivalence.mk (fibrewiseMod C J O) (uncurryMod C J O)
    (fibrewiseModUncurryIso C J O) (uncurryModFibrewiseIso C J O)

end Stacks.SimplicialModules

end
