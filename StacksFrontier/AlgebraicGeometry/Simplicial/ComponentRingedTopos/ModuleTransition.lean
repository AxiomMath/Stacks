module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The transition of component modules on a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
A sheaf of `O`-modules restricts to a sheaf of `Oₙ`-modules on every component, and a simplex
map `φ : m ⟶ n` compares the restrictions in degrees `m` and `n`: on sections over an object `V`
of degree `m` the comparison is restriction of the module along the total-category arrow
`(φ, 𝟙)`, which is additive and `Oₘ(V)`-semilinear. Read as a map of modules on the degree-`m`
component this is the direct-image transition; its mate under the pullback-pushforward
adjunction of the transition morphism of ringed topoi is the map `f_φ^*ℱₘ ⟶ ℱₙ` that the source
writes, and whose invertibility defines a cartesian module.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.restrictTransitionModulesApp`: the direct-image
  transition of component modules.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules`: its mate, the pullback
  transition `f_φ^*ℱₘ ⟶ ℱₙ`.
* `CategoryTheory.SimplicialSiteSituation.IsCartesianModule`: **Stacks 07TF (2)**, a cartesian
  sheaf of modules.

## Main results

* `CategoryTheory.SimplicialSiteSituation.restrict_map_moduleAddHom` and
  `.restrict_map_moduleSMulHom`: restriction of modules to a component carries the addition and
  the scalar action of a module to those of its restriction.
* `CategoryTheory.SimplicialSiteSituation.moduleAddObj_restrict` and
  `.moduleSMulObj_restrict`: the same two facts in the form the transported module structures
  need.
* `CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom_fSharpRing_forget`: the
  structure map of the transition morphism of ringed topoi is, on underlying sheaves of sets,
  the direct-image transition at the sheaf of rings.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules_adj`: the mate of the pullback
  transition is the direct-image transition.

## Implementation notes

The two cases of the situation are not separated here. The underlying morphism of sheaves of
sets is the direct-image transition
`CategoryTheory.SimplicialSiteSituation.restrictTransition` of Stacks 09WF, which is already
defined uniformly, and the two obligations that make it a morphism of sheaves of modules —
additivity and semilinearity on sections — are instances of
`CategoryTheory.Sheaf.moduleAddObj_naturality` and `.moduleSMulObj_naturality` for the
restriction and the direct image whiskered with the sections functor, both of which preserve
finite products. So nothing in this file inspects whether the transitions of `S` are continuous
or cocontinuous functors.

What those two naturality statements compare are the *transported* module structures, and
`CategoryTheory.Sheaf.moduleAddObj` is not definitionally the addition on sections: the product
comparison it goes through is sealed. On the degree-`m` side the identification is
`CategoryTheory.Sheaf.sectionsFunctor_map_moduleAddHom`, because restriction followed by
sections over `V` is, on the nose, sections over the degree-`m` object `V` of the total site.
On the direct-image side it is `AlgebraicGeometry.RingedToposHom.pushforwardModules_add` and
`Stacks.Sheaves.RingedToposModules.moduleSMulObj_pushforwardModules` together with
`moduleAddObj_restrict` and `moduleSMulObj_restrict`, which are the restriction-side companions
of `Stacks.Sheaves.ToposPullback.moduleAdd_map_aux'` and `.moduleSMul_map_aux'` and are proved
here. Those four lemmas, and the comparison of structure maps, are public rather than private
because they occur in the body of an exposed `def`.

The transitions are given at one module at a time rather than as natural transformations of the
restriction functors. Naturality is not needed to state either the transition or cartesianness,
and packaging the transition as a natural transformation makes the elaborator unify the
underlying morphism of sheaves of sets against the unfolded `ofSheafHom` term in the naturality
square, which exhausts its heartbeats; the per-module form elaborates in seconds.

Throughout, the identifications between the restriction of modules over `RingCat` and the
modules of the component ringed topos over `CommRingCat` hold by `rfl`, through
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf_structureRingSheaf`; no hand-pinned
universe constraints and no comparison isomorphism are needed. The structure sheaf is therefore
a sheaf of *commutative* rings, which is the level at which this development has ringed topoi,
their morphisms and the pullback of modules, where the source says "sheaf of rings".

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### Restriction of modules carries the module operations -/

section Restrict

variable (O : Sheaf S.totalTopology RingCat.{u}) (n : SimplexCategory)
  (M : SheafOfModules.{u} O)

/-- A morphism out of a binary product of sheaves of sets, restricted to the degree-`n`
component, is the product comparison followed by a morphism `f'` as soon as `f` and `f'` act on
sections by the same operation `op`. -/
private theorem restrict_map_eq_prodComparison_comp
    {A B C : Sheaf S.totalTopology (Type u)} (f : A ⨯ B ⟶ C)
    (f' : (S.restrict n).obj A ⨯ (S.restrict n).obj B ⟶ (S.restrict n).obj C)
    (op : ∀ X : (S.component n)ᵒᵖ,
      (Sheaf.sectionsFunctor S.totalTopology ((S.inclusion n).op.obj X)).obj A →
      (Sheaf.sectionsFunctor S.totalTopology ((S.inclusion n).op.obj X)).obj B →
      (Sheaf.sectionsFunctor S.totalTopology ((S.inclusion n).op.obj X)).obj C)
    (hf : ∀ X a b, (Sheaf.sectionsFunctor S.totalTopology ((S.inclusion n).op.obj X)).map f
      (Functor.prodObjMk a b) = op X a b)
    (hf' : ∀ X a b, (Sheaf.sectionsFunctor (S.componentTopology n) X).map f'
      (Functor.prodObjMk a b) = op X a b) :
    (S.restrict n).map f = prodComparison (S.restrict n) A B ≫ f' := by
  refine Sheaf.hom_ext_sections fun X p => ?_
  exact (congrArg ((Sheaf.sectionsFunctor S.totalTopology ((S.inclusion n).op.obj X)).map f)
    (Functor.prodObjMk_map_fst_map_snd
      (P := Sheaf.sectionsFunctor S.totalTopology ((S.inclusion n).op.obj X)) p).symm).trans
    ((hf _ _ _).trans ((hf' _ _ _).symm.trans (congrArg
      ((Sheaf.sectionsFunctor (S.componentTopology n) X).map f')
      (Functor.map_prodComparison_apply
        (P := Sheaf.sectionsFunctor (S.componentTopology n) X) (S.restrict n) _ _ p).symm)))

/-- Restriction of a sheaf of modules to the degree-`n` component carries its addition to the
addition of the restriction, the two products being compared by the product comparison of the
restriction functor. -/
theorem restrict_map_moduleAddHom :
    (S.restrict n).map (Sheaf.moduleAddHom.{u, u, u} O M) =
      prodComparison (S.restrict n) (Sheaf.moduleSheaf.{u, u, u} O M)
          (Sheaf.moduleSheaf.{u, u, u} O M) ≫
        Sheaf.moduleAddHom.{u, u, u} (S.componentRingSheaf O n)
          ((S.componentModuleRestriction O n).obj M) :=
  S.restrict_map_eq_prodComparison_comp n _ _ (fun _ a b => a + b)
    (fun _ => Sheaf.sectionsFunctor_map_moduleAddHom O M _) fun X =>
      Sheaf.sectionsFunctor_map_moduleAddHom (S.componentRingSheaf O n)
        ((S.componentModuleRestriction O n).obj M) X

/-- Restriction of a sheaf of modules to the degree-`n` component carries its scalar action to
the action of the restriction over the restricted sheaf of rings. -/
theorem restrict_map_moduleSMulHom :
    (S.restrict n).map (Sheaf.moduleSMulHom.{u, u, u} O M) =
      prodComparison (S.restrict n) (Sheaf.ringSheaf.{u, u, u} O)
          (Sheaf.moduleSheaf.{u, u, u} O M) ≫
        Sheaf.moduleSMulHom.{u, u, u} (S.componentRingSheaf O n)
          ((S.componentModuleRestriction O n).obj M) :=
  S.restrict_map_eq_prodComparison_comp n _ _ (fun _ a b => a • b)
    (fun _ => Sheaf.sectionsFunctor_map_moduleSMulHom O M _) fun X =>
      Sheaf.sectionsFunctor_map_moduleSMulHom (S.componentRingSheaf O n)
        ((S.componentModuleRestriction O n).obj M) X

variable (P : Sheaf (S.componentTopology n) (Type u) ⥤ Type u) [PreservesFiniteProducts P]

/-- A product-preserving functor after restriction to the degree-`n` component sends `f` on a pair
to what it sends `f'` on the pair, when `f` restricts to the product comparison followed by `f'`. -/
private theorem restrict_comp_map_prodObjMk
    {A B C : Sheaf S.totalTopology (Type u)} (f : A ⨯ B ⟶ C)
    (f' : (S.restrict n).obj A ⨯ (S.restrict n).obj B ⟶ (S.restrict n).obj C)
    (h : (S.restrict n).map f = prodComparison (S.restrict n) A B ≫ f')
    (a : P.obj ((S.restrict n).obj A)) (b : P.obj ((S.restrict n).obj B)) :
    (S.restrict n ⋙ P).map f (Functor.prodObjMk (P := S.restrict n ⋙ P) a b) =
      P.map f' (Functor.prodObjMk (P := P) a b) := by
  refine Eq.trans (congrArg (fun m => P.map m (Functor.prodObjMk (P := S.restrict n ⋙ P) a b))
    h) (Eq.trans (P.map_comp_apply _ _ _) (congrArg (P.map f') ?_))
  exact (Functor.map_prodComparison_apply (P := P) (S.restrict n) _ _ _).trans
    (congrArg₂ Functor.prodObjMk (Functor.map_fst_prodObjMk (P := S.restrict n ⋙ P) a b)
      (Functor.map_snd_prodObjMk (P := S.restrict n ⋙ P) a b))

/-- The addition transported along restriction to the degree-`n` component followed by a
finite-product-preserving functor is the addition of the restricted module transported along
that functor. -/
theorem moduleAddObj_restrict
    (a b : P.obj (Sheaf.moduleSheaf.{u, u, u} (S.componentRingSheaf O n)
      ((S.componentModuleRestriction O n).obj M))) :
    Sheaf.moduleAddObj O M (S.restrict n ⋙ P) a b =
      Sheaf.moduleAddObj (S.componentRingSheaf O n)
        ((S.componentModuleRestriction O n).obj M) P a b :=
  S.restrict_comp_map_prodObjMk n P _ _ (S.restrict_map_moduleAddHom O n M) a b

/-- The scalar action transported along restriction to the degree-`n` component followed by a
finite-product-preserving functor is the action of the restricted module transported along that
functor. -/
theorem moduleSMulObj_restrict
    (r : P.obj (Sheaf.ringSheaf.{u, u, u} (S.componentRingSheaf O n)))
    (a : P.obj (Sheaf.moduleSheaf.{u, u, u} (S.componentRingSheaf O n)
      ((S.componentModuleRestriction O n).obj M))) :
    Sheaf.moduleSMulObj O M (S.restrict n ⋙ P) r a =
      Sheaf.moduleSMulObj (S.componentRingSheaf O n)
        ((S.componentModuleRestriction O n).obj M) P r a :=
  S.restrict_comp_map_prodObjMk n P _ _ (S.restrict_map_moduleSMulHom O n M) r a

end Restrict

/-! ### The transition of component modules -/

section Transition

variable (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The sheaf of rings underlying a sheaf of commutative rings on the total site: the sheaf over
which the sheaves of modules of the total ringed topos are taken. -/
noncomputable abbrev totalRingSheaf : Sheaf S.totalTopology RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O

variable {m n : SimplexCategory} (φ : m ⟶ n)

/-- The structure map of the transition morphism of ringed topoi, in direct-image form and on
underlying sheaves of sets, is the direct-image transition of Stacks 09WF at the sheaf of rings.
This is the form in which the scalar action on a direct image of modules reads it. -/
theorem transitionRingedToposHom_fSharpRing_forget :
    (sheafCompose (S.componentTopology m) (forget RingCat.{u})).map
        (S.transitionRingedToposHom O φ).fSharpRing =
      (S.restrictTransition φ).app (Sheaf.ringSheaf.{u, u, u} (S.totalRingSheaf O)) :=
  S.transitionFSharpSet O φ

/-- **Stacks 09WF** for sheaves of modules, at one module: the comparison of the degree-`m` and
degree-`n` restrictions of a sheaf of `O`-modules, landing in the direct image along the
transition morphism of ringed topoi. Its underlying morphism of sheaves of sets is the
direct-image transition of sheaves of sets. -/
noncomputable def restrictTransitionModulesApp (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (S.componentModuleRestriction (S.totalRingSheaf O) m).obj M ⟶
      (S.transitionRingedToposHom O φ).pushforwardModules.obj
        ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M) :=
  ofSheafHom.{u, u, u}
    ((S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))
    (fun X x y => by
      have h1 : Sheaf.moduleAddObj (S.totalRingSheaf O) M
          (S.restrict m ⋙ Sheaf.sectionsFunctor (S.componentTopology m) X) x y = x + y :=
        Sheaf.sectionsFunctor_map_moduleAddHom (S.totalRingSheaf O) M _ x y
      have key := Sheaf.moduleAddObj_naturality (S.totalRingSheaf O) M
        (Functor.whiskerRight (S.restrictTransition φ)
          (Sheaf.sectionsFunctor (S.componentTopology m) X)) x y
      rw [h1] at key
      refine key.trans (Eq.trans (S.moduleAddObj_restrict (S.totalRingSheaf O) n M
        ((S.transitionMorphism φ).pushforward ⋙
          Sheaf.sectionsFunctor (S.componentTopology m) X) _ _) ?_)
      exact ((S.transitionRingedToposHom O φ).pushforwardModules_add
        ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M) X _ _).symm)
    (fun X r x => by
      have h1 : Sheaf.moduleSMulObj (S.totalRingSheaf O) M
          (S.restrict m ⋙ Sheaf.sectionsFunctor (S.componentTopology m) X) r x = r • x :=
        Sheaf.sectionsFunctor_map_moduleSMulHom (S.totalRingSheaf O) M _ r x
      have hs : (Sheaf.sectionsFunctor (S.componentTopology m) X).map
            ((sheafCompose (S.componentTopology m) (forget RingCat.{u})).map
              (S.transitionRingedToposHom O φ).fSharpRing) r =
          (Functor.whiskerRight (S.restrictTransition φ)
            (Sheaf.sectionsFunctor (S.componentTopology m) X)).app
              (Sheaf.ringSheaf.{u, u, u} (S.totalRingSheaf O)) r :=
        congrArg (fun w => (Sheaf.sectionsFunctor (S.componentTopology m) X).map w r)
          (S.transitionRingedToposHom_fSharpRing_forget O φ)
      have key := Sheaf.moduleSMulObj_naturality (S.totalRingSheaf O) M
        (Functor.whiskerRight (S.restrictTransition φ)
          (Sheaf.sectionsFunctor (S.componentTopology m) X)) r x
      rw [h1] at key
      refine key.trans (Eq.trans (S.moduleSMulObj_restrict (S.totalRingSheaf O) n M
        ((S.transitionMorphism φ).pushforward ⋙
          Sheaf.sectionsFunctor (S.componentTopology m) X) _ _) ?_)
      rw [← hs]
      exact ((S.transitionRingedToposHom O φ).pushforwardModules_smul
        ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M) X r
        ((Sheaf.sectionsFunctor (S.componentTopology m) X).map
          ((S.restrictTransition φ).app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) x)).symm)

/-- **Stacks 09WF** for sheaves of modules: the transition `f_φ^*ℱₘ ⟶ ℱₙ` between the
restrictions of a sheaf of `O`-modules to the components of degrees `m` and `n`, obtained as the
mate of the direct-image transition under the pullback-pushforward adjunction of the transition
morphism of ringed topoi. This is the map the source writes `f_φ^*ℱₘ → ℱₙ`. -/
@[stacks 09WF "module transition"]
noncomputable def fiberTransitionModules (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).obj
        ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj M) ⟶
      (S.componentModuleRestriction (S.totalRingSheaf O) n).obj M :=
  ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv _ _).symm
    (S.restrictTransitionModulesApp O φ M)

/-- The mate of the pullback transition of component modules is the direct-image transition. -/
theorem fiberTransitionModules_adj (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv _ _)
        (S.fiberTransitionModules O φ M) =
      S.restrictTransitionModulesApp O φ M :=
  ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv _ _).apply_symm_apply _

end Transition

/-! ### Cartesian modules -/

/-- **Stacks 07TF (2).** A sheaf of `O`-modules on the total site of a simplicial-site situation
is *cartesian* if every canonical transition `f_φ^*ℱₘ ⟶ ℱₙ` between its restrictions to the
components is an isomorphism. -/
@[stacks 07TF "cartesian modules"]
abbrev IsCartesianModule (O : Sheaf S.totalTopology CommRingCat.{u})
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), IsIso (S.fiberTransitionModules O φ M)

end CategoryTheory.SimplicialSiteSituation

end
