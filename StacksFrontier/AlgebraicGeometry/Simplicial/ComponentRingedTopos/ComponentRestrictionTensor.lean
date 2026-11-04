module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTensorComplex
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject

/-!
# Restriction to a simplicial component commutes with the tensor product of sheaves of modules

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`g_n` the inclusion of the degree-`n` component. For sheaves of `O`-modules `A` and `B` there is
a comparison

`g_n^*(A ⊗_O B) ≅ g_n^*A ⊗_{O_n} g_n^*B`,

natural in `A` and in `B`. This is **Stacks 03EL** at `g_n`, on sheaves of modules rather than on
total complexes, and it is the sheaf-level statement that
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorTotalIso` is the total-complex
analogue of.

It is stated between the two uncurried bifunctors on `Mod(O) × Mod(O)`, so that naturality in
both variables is part of its type, matching
`CategoryTheory.SimplicialSiteSituation.componentDerivedTensorIso` in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ComponentDerivedTensor.lean`, the
derived statement whose shape the consumers expect.

## Main definitions

* `Stacks.SheafOfModules.sheafTensorUncurryIso`: the curried tensor bifunctor of Tag 06YM,
  uncurried, against the uncurried tensor bifunctor Tag 03EL is stated for.
* `CategoryTheory.SimplicialSiteSituation.componentPullbackTensorIso`: Tag 03EL at the component
  morphism of ringed topoi, with its endpoints written at the *two-field* pullback functor.
* `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso`: the comparison
  displayed above.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso_hom_app_factors`: the
  comparison at a pair of sheaves of modules, split into the five factors of its definition.
* `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorIso_hom_app`: the same, with
  the two factors comparing the tensor bifunctors — which are identities — removed, so that only
  the identification of Tag 0D72 and Tag 03EL at `g_n` are left.

## Implementation notes

Nothing is reproved. As in `ComponentTensorComplex.lean`, restriction to a component is *not* a
pullback along a morphism of sites — `componentFunctor S n : 𝒞_n ⥤ 𝒞_total` is continuous *and*
cocontinuous and points at the source — so what applies is the development for the two-field
morphism of ringed topoi `AlgebraicGeometry.RingedToposHom`, which asks for no functor of sites.
Tag 03EL in that form is `Stacks.SheafOfModules.pullbackTensorIso`, used here at
`CategoryTheory.SimplicialSiteSituation.componentRingedToposHom`, and the comparison is its
transport along `CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso`,
the identification of `g_n^*` with literal restriction. The transport is a whiskering on each
side, by that identification on the left and by its square on the two tensor factors — so by
`CategoryTheory.NatIso.prod` of it with itself — on the right.

The one thing that has to be built is the *spelling* of the tensor bifunctor.
`Stacks.SheafOfModules.pullbackTensorIso` is stated against the uncurried
`AlgebraicGeometry.SheafOfModules.tensorSheafBifunctor`, whereas the simplicial-component
development is stated against the curried `Stacks.SheafOfModules.Tensor.sheafTensor` of Tag 06YM.
On objects the two bifunctors are the same sheafification of the same sectionwise tensor product,
so `sheafTensorUncurryIso` has identity components; on morphisms they differ, the uncurried one
spelling the action on `(a, b)` as `a ⊗ₘ b` and the uncurried-from-curried one as
`a ▷ _ ≫ _ ◁ b`, and the identification of the two is exactly the existing bridge lemma
`Stacks.SheafOfModules.tensorSheafBifunctor_map_eq`.

That naturality square cannot be proved by `rw`. Rewriting with `Iso.refl_hom` and
`Category.comp_id` leaves a goal that is no longer type-correct at `implicit` transparency,
because the equality of the two bifunctors' values on objects holds only at *default*
transparency; `rw`'s pattern match then fails with an application type mismatch. The proof is
therefore written as a term, `Category.comp_id` and `Category.id_comp` being applied by
`Eq.trans` against the goal rather than used to transform it.

*Why the third factor is given its own name.* `componentRestrictionTensorIso` is a five-fold
`Iso.trans`, and its consumers need it taken apart again at a pair of sheaves of modules. Which
junctions can be split is decided by the *spelling* of the functor sitting there, because the
split is an equation between morphisms and the two sides of a junction have to present the same
object with the same category instance. Four of the five junctions are already spelled the same
way on both sides. The one that is not is the junction below Tag 03EL: `pullbackTensorIso` is
stated at the four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` of a
`ModulesHom`, whereas the identification of Tag 0D72 — and therefore the whiskering of
`CategoryTheory.NatIso.prod` of it with itself on the other side of that junction — is stated at
the two-field `AlgebraicGeometry.RingedToposHom.pullbackModules`. The two functors are the same
term, the second being defined as the first at `toModulesHom`, but their *types* are written
through two spellings of the sheaf of rings (`Stacks.ringSheaf` and
`Stacks.Sheaves.RingedToposModules.structureRingSheaf`), and unifying two such spellings inside a
`Hom` type sends the unifier into an unbounded congruence: the split at that junction exceeds the
recursion limit, by `rfl` and by `rw [NatTrans.comp_app]` alike, and `simp only` stops there
having peeled the junctions above it.

So the third factor is named, `componentPullbackTensorIso`, with its two endpoint functors written
out at the two-field spelling. The retyping is accepted — it is the same unification the chain
performed anyway — and it is what carries the pin: with it in place every junction of the chain
is spelled identically on both sides and the whole five-fold split goes through. Unfolding
`componentPullbackTensorIso` inside the split's proof undoes the pin and the recursion limit comes
back, so the proof of `componentRestrictionTensorIso_hom_app_factors` deliberately does not list
it among the definitions it unfolds.

*Why the two identity factors are removed in a second step.* The factors comparing the two tensor
bifunctors have identity components, so two of the five drop out. They cannot be dropped by
`simp [Functor.map_id, Category.comp_id]`: rewriting a component to `𝟙` produces an identity
whose category instance is the one the *isomorphism* lives at, and `Functor.map_id` and
`Category.comp_id` then do not match the composition, whose instance comes from the neighbouring
factor. Each is therefore discharged by hand, as a `congrArg` against an identity stated with its
object written out at the spelling the composition uses.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe w v u

namespace Stacks.SheafOfModules

section Uncurry

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- **The two tensor bifunctors on sheaves of modules agree.** Uncurrying the curried tensor
bifunctor of Tag 06YM gives the uncurried tensor bifunctor
`AlgebraicGeometry.SheafOfModules.tensorSheafBifunctor` that Tag 03EL is stated against.

Both are the sheafification of the sectionwise tensor product of the underlying presheaves of
modules, so the comparison is the identity on objects; on a pair of morphisms the two spellings
differ and are identified by `Stacks.SheafOfModules.tensorSheafBifunctor_map_eq`. -/
def sheafTensorUncurryIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O) ≅
      Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O) :=
  Iso.refl _

end Uncurry

end Stacks.SheafOfModules

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasWeakSheafifyComponent hasSheafifyTotal
  GrothendieckTopology.hasSheafify_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **Stacks 03EL at the component morphism of ringed topoi**, with both endpoints written at the
two-field pullback functor `AlgebraicGeometry.RingedToposHom.pullbackModules`.

This is `Stacks.SheafOfModules.pullbackTensorIso` at
`CategoryTheory.SimplicialSiteSituation.componentRingedToposHom`, nothing more: the two-field
pullback functor is *defined* as the four-field one at `toModulesHom`, so the retyping is the
identity on terms. It exists because the four-field and two-field spellings write the same functor
through two spellings of the sheaf of rings, and a junction of `componentRestrictionTensorIso`
whose two sides disagree about which cannot be taken apart again. The module docstring records the
measurements. -/
def componentPullbackTensorIso :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)) ⋙
      (componentRingedToposHom S O n).toModulesHom.pullbackModules ≅
    ((componentRingedToposHom S O n).toModulesHom.pullbackModules).prod
        ((componentRingedToposHom S O n).toModulesHom.pullbackModules) ⋙
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)) :=
  Stacks.SheafOfModules.pullbackTensorIso (componentRingedToposHom S O n).toModulesHom

/-- **Stacks 03EL at the inclusion of a simplicial component, on sheaves of modules.**
Restriction to the degree-`n` component commutes with the tensor product:

`g_n^*(A ⊗_O B) ≅ g_n^*A ⊗_{O_n} g_n^*B`

for sheaves of `O`-modules `A` and `B`. It is stated between the two uncurried bifunctors on
`Mod(O) × Mod(O)`, so that naturality in both variables is part of its type.

This is `Stacks.SheafOfModules.pullbackTensorIso` — Tag 03EL for a morphism of ringed topoi — at
`CategoryTheory.SimplicialSiteSituation.componentRingedToposHom`, transported along
`CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso`, which is Tag
0D72: the identification of the pullback of modules along `g_n` with literal restriction of
sections.

Its third factor is `CategoryTheory.SimplicialSiteSituation.componentPullbackTensorIso` rather
than `Stacks.SheafOfModules.pullbackTensorIso` itself; that is the same term, retyped so that
every junction of the chain is spelled the same way on both sides, which is what lets the chain be
taken apart again at a pair of sheaves of modules. -/
def componentRestrictionTensorIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O) ⋙
        S.componentModulesRestriction O n ≅
      (S.componentModulesRestriction O n).prod (S.componentModulesRestriction O n) ⋙
        Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O) :=
  Functor.isoWhiskerLeft _ (componentPullbackModulesRestrictionIso S O n).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.SheafOfModules.sheafTensorUncurryIso (S.totalRingedTopos O).O) _ ≪≫
    componentPullbackTensorIso S O n ≪≫
    Functor.isoWhiskerRight (NatIso.prod (componentPullbackModulesRestrictionIso S O n)
      (componentPullbackModulesRestrictionIso S O n)) _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.SheafOfModules.sheafTensorUncurryIso (S.componentRingedTopos O n).O).symm

/-- **The comparison of Stacks 03EL at a simplicial component, split into the five factors of its
definition**, read at a pair of sheaves of `O`-modules: the identification of Stacks 0D72 at
`A ⊗_O B`, the comparison of the two tensor bifunctors carried along `g_n^*`, Stacks 03EL at
`g_n`, the identification of Stacks 0D72 in each tensor factor, and the comparison of the two
tensor bifunctors on the component. -/
theorem componentRestrictionTensorIso_hom_app_factors
    (A B : (S.totalRingedTopos O).Modules) :
    (componentRestrictionTensorIso S O n).hom.app (A, B) =
      (componentPullbackModulesRestrictionIso S O n).inv.app
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)).obj (A, B)) ≫
        (componentRingedToposHom S O n).toModulesHom.pullbackModules.map
            ((Stacks.SheafOfModules.sheafTensorUncurryIso
              (S.totalRingedTopos O).O).hom.app (A, B)) ≫
          (componentPullbackTensorIso S O n).hom.app (A, B) ≫
            ((Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O))).map
                (((componentPullbackModulesRestrictionIso S O n).hom.app A,
                  (componentPullbackModulesRestrictionIso S O n).hom.app B) :
                    (((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
                        (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B) :
                          _ × _) ⟶
                      ((S.componentModulesRestriction O n).obj A,
                        (S.componentModulesRestriction O n).obj B)) ≫
              (Stacks.SheafOfModules.sheafTensorUncurryIso
                  (S.componentRingedTopos O n).O).inv.app
                ((S.componentModulesRestriction O n).obj A,
                  (S.componentModulesRestriction O n).obj B) := by
  simp only [componentRestrictionTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, NatIso.prod_hom, NatTrans.prod, Prod.mkHom,
    Functor.prod_obj]

/-- **The comparison of Stacks 03EL at a simplicial component, at a pair of sheaves of
`O`-modules.** It is the identification of Stacks 0D72 at `A ⊗_O B`, inverted, then Stacks 03EL at
`g_n`, then the identification of Stacks 0D72 in each tensor factor.

This is `…componentRestrictionTensorIso_hom_app_factors` with the two factors comparing the
uncurried tensor bifunctor of Tag 06YM with the one of Tag 03EL removed: both have identity
components, since the two bifunctors agree on objects. -/
theorem componentRestrictionTensorIso_hom_app (A B : (S.totalRingedTopos O).Modules) :
    (componentRestrictionTensorIso S O n).hom.app (A, B) =
      (componentPullbackModulesRestrictionIso S O n).inv.app
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)).obj (A, B)) ≫
        (componentPullbackTensorIso S O n).hom.app (A, B) ≫
          ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O))).map
            (((componentPullbackModulesRestrictionIso S O n).hom.app A,
              (componentPullbackModulesRestrictionIso S O n).hom.app B) :
                (((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj A,
                    (componentRingedToposHom S O n).toModulesHom.pullbackModules.obj B) : _ × _) ⟶
                  ((S.componentModulesRestriction O n).obj A,
                    (S.componentModulesRestriction O n).obj B)) :=
  have htotal : (componentRingedToposHom S O n).toModulesHom.pullbackModules.map
        ((Stacks.SheafOfModules.sheafTensorUncurryIso
          (S.totalRingedTopos O).O).hom.app (A, B)) =
      𝟙 ((componentRingedToposHom S O n).toModulesHom.pullbackModules.obj
        (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O))).obj (A, B))) :=
    (congrArg (componentRingedToposHom S O n).toModulesHom.pullbackModules.map
        (show (Stacks.SheafOfModules.sheafTensorUncurryIso
              (S.totalRingedTopos O).O).hom.app (A, B) =
          𝟙 (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O))).obj
            (A, B)) from rfl)).trans
      ((componentRingedToposHom S O n).toModulesHom.pullbackModules.map_id _)
  have hcomponent : (Stacks.SheafOfModules.sheafTensorUncurryIso
          (S.componentRingedTopos O n).O).inv.app
        ((S.componentModulesRestriction O n).obj A,
          (S.componentModulesRestriction O n).obj B) =
      𝟙 (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O))).obj
          ((S.componentModulesRestriction O n).obj A,
            (S.componentModulesRestriction O n).obj B)) := rfl
  (componentRestrictionTensorIso_hom_app_factors S O n A B).trans
    (congrArg (fun k => (componentPullbackModulesRestrictionIso S O n).inv.app
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)).obj (A, B)) ≫ k)
      ((congrArg (fun k => k ≫ _) htotal).trans
        ((Category.id_comp _).trans
          (congrArg (fun k => (componentPullbackTensorIso S O n).hom.app (A, B) ≫ k)
            ((congrArg (fun k => _ ≫ k) hcomponent).trans (Category.comp_id _))))))

end CategoryTheory.SimplicialSiteSituation

end
