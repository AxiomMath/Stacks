module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem.ModuleCompositorAssoc

/-!
# The cocycle law for the compositor of derived pullbacks

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. This file climbs the last rung of the ladder begun in
the sibling file `DerivedCocycleSystem/ModuleCompositorAssoc.lean`:
the cocycle, or pentagon, law

`Lf_φ^*(c_{χ,ψ}) ∘ c_{χ ≫ ψ, φ} = c_{ψ,φ} ∘ c_{χ, ψ ≫ φ}`

for the compositor of derived pullbacks. That the compositor is invertible is Stacks 0D6D and is
proved in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/DerivedPullbackComposition.lean`;
its coherence is proved here. The law passes from the unbounded homotopy categories to the
derived categories by the universal property of a left derived functor: both sides of the law are
natural transformations into `Lf_{χ ≫ ψ ≫ φ}^*`, so they agree as soon as they agree after
restriction along the localization, where they reduce to the homotopy-category law. The result,
`derivedModulePasteIso_assoc`, holds at an arbitrary object of the derived category and not only at
one in the image of the localization, which is what the universal property buys.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.derivedModulePasteIso` and `.derivedModulePasteIsoOfEq`:
  the
  compositor of derived pullbacks read as an identification `Lf_φ^* Lf_ψ^* K ≅ Lf_{ψ ≫ φ}^* K`
  of objects, and the same at a chosen factorization of a simplex map.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedModulePasteIso_assoc`: **the cocycle law for the
  compositor of derived pullbacks**, the coherence input of Stacks 0GMF.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompComparison_assoc`: the same law
  as an equality of natural transformations, which is what the universal property proves.

## Implementation notes

*Where the transports are, and where they are not.* Composition in the simplex category is
associative by `rfl`, so `f_{(χ ≫ ψ) ≫ φ}` and `f_{χ ≫ ψ ≫ φ}` are the same functor and the
laws read at an object have the same type as written: no transport appears in
`pushforwardCompSymm_assoc_app`, in `transitionPushforwardModulesCompIso_assoc_app`, in
`transitionPullbackModulesCompIso_inv_assoc_app`, in `transitionPullbackHomotopyComp_assoc`, in
`derivedModulePasteIso_assoc` or in `pairDerivedModuleTransition_comp`. A transport *is* carried in
the two
laws stated as equalities of natural isomorphisms, because that is the shape
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc` consumes and because the two spellings of
the triple composite, while the same simplex map, are not the same term; and the compositor at a
chosen factorization, `derivedModulePasteIsoOfEq`, carries one by construction, which is how the
vertex and edge identifications of a simplex are built.

*The devices that keep the elaborator inside its default budget.* Three, used throughout the
construction of Stacks 0GMF, and its files are organized around them.

First, *opaque definitions at each level*, as in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/DerivedPullback.lean`.
`componentModuleSheaf`, `transitionPullbackHomotopy`, `transitionPullbackHomotopyComp`,
`derivedTransitionCompPrefix`, `derivedEdgeSource`, `derivedEdgeTarget` and
`derivedEdgeMapPaste` are plain `def`s, never `abbrev`s: each stops the unifier at a definition
boundary instead of letting it descend through `componentRingedTopos`,
`Stacks.SheafOfModules.Tensor.ringSheaf` and `sheafCompose` to the `ConcreteCategory` instances on
every instance argument of every occurrence, and each shortens the statements that mention it
enough for them to elaborate.

Second, *cross a definitional-but-not-syntactic boundary by rewriting, never by a term-mode
application*. Each such boundary is isolated in a `rfl` lemma of its own —
`componentModuleSheaf_transitionPushforwardModules_map`, `transitionPullbackHomotopy_eq`,
`transitionPullbackHomotopyComp_eq`, `transitionPullbackHomotopy_map` — and the step that needs
it rewrites with that lemma first, so that the final match is syntactic. For example, on
`derivedTransitionComp_fac_app`, whose proof would otherwise close by applying
`CategoryTheory.SimplicialSiteSituation.derivedTransitionCompCounit_app` directly: one such
rewrite takes it from 185 880 heartbeats to 83 821.

Third, *generic lemmas whose objects are free variables, applied and never unfolded*, as in the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AssociatedDerivedSystem.lean`. The reassociated
variants `derivedTransitionComparison_naturality_qh_assoc`, `derivedTransitionComp_fac_app_assoc`
and `derivedEdgeTransport_map_assoc` carry a free trailing morphism for the same reason — so that
the step that uses them needs no associativity rewrite of its own.

*A pitfall.* `rw [Category.assoc]` with no arguments will happily rewrite
`(χ ≫ ψ) ≫ φ` **in the simplex category**, inside the types, and the resulting motive is not
type-correct. Every associativity step here therefore pins its arguments, and
`Functor.congr_map F (Category.assoc _ _ _).symm` is what replaces a rewrite under `F.map`,
where the motive would fail anyway because `(Qh ⋙ Lf_ψ^*).obj` and `Lf_ψ^*.obj (f_χ^*.obj _)`
are differently spelled.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0GMF](https://stacks.math.columbia.edu/tag/0GMF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules (pushforwardModules
  pullbackAdjPushforwardModules hom_ext_moduleSheafFunctor
  moduleSheafFunctor_map_pushforwardModules_map)
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### Associativity of the canonical comparison of derived pullbacks -/

/-- The defining factorization of the canonical comparison of derived pullbacks, read at a
complex and with the comparison for the composite written out: this is
`CategoryTheory.SimplicialSiteSituation.derivedTransitionComp_fac` composed with
`.derivedTransitionCompCounit_app`. -/
theorem derivedTransitionComp_fac_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O l).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionCompComparison O ψ φ).app (DerivedCategory.Qh.obj K) ≫
        (S.derivedTransitionComparison O (ψ ≫ φ)).app K =
      (S.derivedTransitionPullback O φ).map ((S.derivedTransitionComparison O ψ).app K) ≫
        (S.derivedTransitionComparison O φ).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj K) ≫
          DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O ψ φ).app K) := by
  rw [S.transitionPullbackHomotopyComp_eq O ψ φ]
  exact (NatTrans.congr_app (S.derivedTransitionComp_fac O ψ φ) K).trans
    (S.derivedTransitionCompCounit_app O ψ φ K)

/-- Naturality of the canonical comparison `Lf_φ^* ⟶ f_φ^*`, read through the localization: the
comparison carries the derived pullback of the image of a map of complexes to the image of its
degreewise pullback. -/
theorem derivedTransitionComparison_naturality_qh {m n : SimplexCategory} (φ : m ⟶ n)
    {A B : HomotopyCategory (S.componentRingedTopos O m).Modules (ComplexShape.up ℤ)}
    (g : A ⟶ B) :
    (S.derivedTransitionPullback O φ).map (DerivedCategory.Qh.map g) ≫
        (S.derivedTransitionComparison O φ).app B =
      (S.derivedTransitionComparison O φ).app A ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).map g) :=
  (S.derivedTransitionComparison O φ).naturality g

/-- The part common to the two routes through a threefold composite of derived pullbacks: the
three canonical comparisons `Lf^* ⟶ f^*` applied in turn. It is an opaque `def` so that the
statements of the two routes are short enough to elaborate. -/
def derivedTransitionCompPrefix {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m)
    (φ : m ⟶ n) (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionPullback O φ).obj
        ((S.derivedTransitionPullback O ψ).obj
          ((S.derivedTransitionPullback O χ).obj (DerivedCategory.Qh.obj K))) ⟶
      DerivedCategory.Qh.obj
        ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).obj
          ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj
            ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K))) :=
  (S.derivedTransitionPullback O φ).map
      ((S.derivedTransitionPullback O ψ).map ((S.derivedTransitionComparison O χ).app K) ≫
        (S.derivedTransitionComparison O ψ).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)) ≫
    (S.derivedTransitionComparison O φ).app
      ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj
        ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K))

/-- The route through `χ ≫ ψ`, first step: the comparison for the composite is replaced by its
defining factorization and the two derived pullbacks of comparisons are merged. -/
theorem derivedTransitionCompComparison_assoc_left₁ {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionPullback O φ).map
          ((S.derivedTransitionCompComparison O χ ψ).app (DerivedCategory.Qh.obj K)) ≫
        (S.derivedTransitionCompComparison O (χ ≫ ψ) φ).app (DerivedCategory.Qh.obj K) ≫
          (S.derivedTransitionComparison O ((χ ≫ ψ) ≫ φ)).app K =
      (S.derivedTransitionPullback O φ).map
            ((S.derivedTransitionCompComparison O χ ψ).app (DerivedCategory.Qh.obj K) ≫
              (S.derivedTransitionComparison O (χ ≫ ψ)).app K) ≫
          (S.derivedTransitionComparison O φ).app
              ((pullbackMapHomotopy (S.transitionRingedToposHom O (χ ≫ ψ))).obj K) ≫
            DerivedCategory.Qh.map
              ((S.transitionPullbackHomotopyComp O (χ ≫ ψ) φ).app K) := by
  rw [S.derivedTransitionComp_fac_app O (χ ≫ ψ) φ K, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp]

/-- The route through `χ ≫ ψ`, second step: the comparison for `χ ≫ ψ` is replaced by its
defining factorization and the degreewise compositor is split off. -/
theorem derivedTransitionCompComparison_assoc_mid {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ))
    {Z : DerivedCategory (S.componentRingedTopos O n).Modules}
    (R : (S.derivedTransitionPullback O φ).obj
      ((pullbackOnHomotopy (S.transitionRingedToposHom O (χ ≫ ψ))).obj K) ⟶ Z) :
    (S.derivedTransitionPullback O φ).map
          ((S.derivedTransitionCompComparison O χ ψ).app (DerivedCategory.Qh.obj K) ≫
            (S.derivedTransitionComparison O (χ ≫ ψ)).app K) ≫ R =
      (S.derivedTransitionPullback O φ).map
            ((S.derivedTransitionPullback O ψ).map
                ((S.derivedTransitionComparison O χ).app K) ≫
              (S.derivedTransitionComparison O ψ).app
                ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)) ≫
          (S.derivedTransitionPullback O φ).map
              (DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O χ ψ).app K)) ≫ R := by
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    S.derivedTransitionComp_fac_app O χ ψ K]
  exact congrArg (fun t ↦ (S.derivedTransitionPullback O φ).map t ≫ R)
    (Category.assoc _ _ _).symm

/-- Naturality of the canonical comparison through the localization, reassociated. The trailing
morphism is typed through the opaque degreewise pullback, so that rewriting with this lemma
matches the statements of the two routes. -/
theorem derivedTransitionComparison_naturality_qh_assoc {m n : SimplexCategory} (φ : m ⟶ n)
    {A B : HomotopyCategory (S.componentRingedTopos O m).Modules (ComplexShape.up ℤ)}
    (g : A ⟶ B) {Z : DerivedCategory (S.componentRingedTopos O n).Modules}
    (h : DerivedCategory.Qh.obj
      ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).obj B) ⟶ Z) :
    (S.derivedTransitionPullback O φ).map (DerivedCategory.Qh.map g) ≫
        (S.derivedTransitionComparison O φ).app B ≫ h =
      (S.derivedTransitionComparison O φ).app A ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).map g) ≫ h :=
  (S.derivedTransitionComparison O φ).naturality_assoc g h

/-- The route through `χ ≫ ψ`, third step: the degreewise compositor for `χ, ψ` is carried past
the comparison for `φ` by naturality and merged with the compositor for `χ ≫ ψ, φ`. -/
theorem derivedTransitionCompComparison_assoc_left₂ {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionPullback O φ).map
          (DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O χ ψ).app K)) ≫
        (S.derivedTransitionComparison O φ).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O (χ ≫ ψ))).obj K) ≫
          DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O (χ ≫ ψ) φ).app K) =
      (S.derivedTransitionComparison O φ).app
          ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj
            ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)) ≫
        DerivedCategory.Qh.map
          ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).map
              ((S.transitionPullbackHomotopyComp O χ ψ).app K) ≫
            (S.transitionPullbackHomotopyComp O (χ ≫ ψ) φ).app K) := by
  rw [S.derivedTransitionComparison_naturality_qh_assoc O φ
      ((S.transitionPullbackHomotopyComp O χ ψ).app K)
      (DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O (χ ≫ ψ) φ).app K)),
    ← CategoryTheory.Functor.map_comp DerivedCategory.Qh]
  rfl

/-- **The route through `χ ≫ ψ`.** Comparing the threefold composite of derived pullbacks with
the derived pullback along the composite simplex map through `χ ≫ ψ` is the common prefix
followed by the degreewise compositors taken in that order. -/
theorem derivedTransitionCompComparison_assoc_left {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionPullback O φ).map
          ((S.derivedTransitionCompComparison O χ ψ).app (DerivedCategory.Qh.obj K)) ≫
        (S.derivedTransitionCompComparison O (χ ≫ ψ) φ).app (DerivedCategory.Qh.obj K) ≫
          (S.derivedTransitionComparison O ((χ ≫ ψ) ≫ φ)).app K =
      S.derivedTransitionCompPrefix O χ ψ φ K ≫
        DerivedCategory.Qh.map
          ((pullbackMapHomotopy (S.transitionRingedToposHom O φ)).map
              ((S.transitionPullbackHomotopyComp O χ ψ).app K) ≫
            (S.transitionPullbackHomotopyComp O (χ ≫ ψ) φ).app K) := by
  simp only [derivedTransitionCompPrefix]
  rw [S.derivedTransitionCompComparison_assoc_left₁ O χ ψ φ K,
    S.derivedTransitionCompComparison_assoc_mid O χ ψ φ K,
    S.derivedTransitionCompComparison_assoc_left₂ O χ ψ φ K]
  exact (Category.assoc _ _ _).symm

/-- Naturality of the canonical comparison of derived pullbacks, reassociated. -/
theorem derivedTransitionCompComparison_naturality_assoc {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) {A B : DerivedCategory (S.componentRingedTopos O l).Modules} (g : A ⟶ B)
    {Z : DerivedCategory (S.componentRingedTopos O n).Modules}
    (h : (S.derivedTransitionPullback O (ψ ≫ φ)).obj B ⟶ Z) :
    (S.derivedTransitionCompComparison O ψ φ).app A ≫
        (S.derivedTransitionPullback O (ψ ≫ φ)).map g ≫ h =
      (S.derivedTransitionPullback O φ).map ((S.derivedTransitionPullback O ψ).map g) ≫
        (S.derivedTransitionCompComparison O ψ φ).app B ≫ h := by
  rw [← Category.assoc, ← (S.derivedTransitionCompComparison O ψ φ).naturality g, Category.assoc]
  rfl

/-- The route through `ψ ≫ φ`, first step: the comparison for the composite is replaced by its
defining factorization and the comparison for `χ` is carried through by naturality. -/
theorem derivedTransitionCompComparison_assoc_right₁ {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionCompComparison O ψ φ).app
          ((S.derivedTransitionPullback O χ).obj (DerivedCategory.Qh.obj K)) ≫
        (S.derivedTransitionCompComparison O χ (ψ ≫ φ)).app (DerivedCategory.Qh.obj K) ≫
          (S.derivedTransitionComparison O (χ ≫ ψ ≫ φ)).app K =
      (S.derivedTransitionPullback O φ).map
            ((S.derivedTransitionPullback O ψ).map
              ((S.derivedTransitionComparison O χ).app K)) ≫
          (S.derivedTransitionCompComparison O ψ φ).app
              (DerivedCategory.Qh.obj
                ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)) ≫
            (S.derivedTransitionComparison O (ψ ≫ φ)).app
                ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K) ≫
              DerivedCategory.Qh.map
                ((S.transitionPullbackHomotopyComp O χ (ψ ≫ φ)).app K) := by
  rw [S.derivedTransitionComp_fac_app O χ (ψ ≫ φ) K]
  exact S.derivedTransitionCompComparison_naturality_assoc O ψ φ
    ((S.derivedTransitionComparison O χ).app K) _

/-- The defining factorization of the canonical comparison, reassociated. -/
theorem derivedTransitionComp_fac_app_assoc {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O l).Modules (ComplexShape.up ℤ))
    {Z : DerivedCategory (S.componentRingedTopos O n).Modules}
    (T : (pullbackOnHomotopy (S.transitionRingedToposHom O (ψ ≫ φ))).obj K ⟶ Z) :
    (S.derivedTransitionCompComparison O ψ φ).app (DerivedCategory.Qh.obj K) ≫
        (S.derivedTransitionComparison O (ψ ≫ φ)).app K ≫ T =
      (S.derivedTransitionPullback O φ).map ((S.derivedTransitionComparison O ψ).app K) ≫
        (S.derivedTransitionComparison O φ).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj K) ≫
          DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O ψ φ).app K) ≫ T := by
  rw [← Category.assoc
      ((S.derivedTransitionCompComparison O ψ φ).app (DerivedCategory.Qh.obj K))
      ((S.derivedTransitionComparison O (ψ ≫ φ)).app K) T,
    S.derivedTransitionComp_fac_app O ψ φ K]
  simp only [Category.assoc]

/-- The route through `ψ ≫ φ`, second step: the comparison for `ψ ≫ φ` is replaced by its
defining factorization and the two degreewise compositors are merged. -/
theorem derivedTransitionCompComparison_assoc_right₂ {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionCompComparison O ψ φ).app
          (DerivedCategory.Qh.obj
            ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)) ≫
        (S.derivedTransitionComparison O (ψ ≫ φ)).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K) ≫
          DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O χ (ψ ≫ φ)).app K) =
      (S.derivedTransitionPullback O φ).map
          ((S.derivedTransitionComparison O ψ).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)) ≫
        (S.derivedTransitionComparison O φ).app
            ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj
              ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)) ≫
          DerivedCategory.Qh.map
            ((S.transitionPullbackHomotopyComp O ψ φ).app
                ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K) ≫
              (S.transitionPullbackHomotopyComp O χ (ψ ≫ φ)).app K) := by
  rw [S.derivedTransitionComp_fac_app_assoc O ψ φ
      ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K)
      (DerivedCategory.Qh.map ((S.transitionPullbackHomotopyComp O χ (ψ ≫ φ)).app K)),
    ← CategoryTheory.Functor.map_comp DerivedCategory.Qh]

/-- **The route through `ψ ≫ φ`.** Comparing the threefold composite of derived pullbacks with
the derived pullback along the composite simplex map through `ψ ≫ φ` is the common prefix
followed by the degreewise compositors taken in that order. -/
theorem derivedTransitionCompComparison_assoc_right {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionCompComparison O ψ φ).app
          ((S.derivedTransitionPullback O χ).obj (DerivedCategory.Qh.obj K)) ≫
        (S.derivedTransitionCompComparison O χ (ψ ≫ φ)).app (DerivedCategory.Qh.obj K) ≫
          (S.derivedTransitionComparison O (χ ≫ ψ ≫ φ)).app K =
      S.derivedTransitionCompPrefix O χ ψ φ K ≫
        DerivedCategory.Qh.map
          ((S.transitionPullbackHomotopyComp O ψ φ).app
              ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K) ≫
            (S.transitionPullbackHomotopyComp O χ (ψ ≫ φ)).app K) := by
  simp only [derivedTransitionCompPrefix]
  rw [S.derivedTransitionCompComparison_assoc_right₁ O χ ψ φ K,
    S.derivedTransitionCompComparison_assoc_right₂ O χ ψ φ K,
    ← Category.assoc
      ((S.derivedTransitionPullback O φ).map
        ((S.derivedTransitionPullback O ψ).map ((S.derivedTransitionComparison O χ).app K)))
      ((S.derivedTransitionPullback O φ).map
        ((S.derivedTransitionComparison O ψ).app
          ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K))) _,
    ← CategoryTheory.Functor.map_comp (S.derivedTransitionPullback O φ)]
  exact (Category.assoc _ _ _).symm

/-- The cocycle law for the compositor of degreewise pullbacks, read at a complex. -/
theorem transitionPullbackHomotopyComp_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    (pullbackMapHomotopy (S.transitionRingedToposHom O φ)).map
          ((S.transitionPullbackHomotopyComp O χ ψ).app K) ≫
        (S.transitionPullbackHomotopyComp O (χ ≫ ψ) φ).app K =
      (S.transitionPullbackHomotopyComp O ψ φ).app
          ((pullbackMapHomotopy (S.transitionRingedToposHom O χ)).obj K) ≫
        (S.transitionPullbackHomotopyComp O χ (ψ ≫ φ)).app K := by
  have h := NatTrans.congr_app (S.transitionPullbackHomotopyComp_assoc O χ ψ φ) K
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp] at h
  exact h

/-- **The cocycle law for the canonical comparison of derived pullbacks, read at a complex.**
The two routes through a threefold composite agree because they have the same prefix and their
degreewise compositors satisfy the cocycle law. -/
theorem derivedTransitionCompComparison_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : HomotopyCategory (S.componentRingedTopos O k).Modules (ComplexShape.up ℤ)) :
    ((S.derivedTransitionPullback O φ).map
            ((S.derivedTransitionCompComparison O χ ψ).app (DerivedCategory.Qh.obj K)) ≫
          (S.derivedTransitionCompComparison O (χ ≫ ψ) φ).app (DerivedCategory.Qh.obj K)) ≫
        (S.derivedTransitionComparison O ((χ ≫ ψ) ≫ φ)).app K =
      ((S.derivedTransitionCompComparison O ψ φ).app
            ((S.derivedTransitionPullback O χ).obj (DerivedCategory.Qh.obj K)) ≫
          (S.derivedTransitionCompComparison O χ (ψ ≫ φ)).app (DerivedCategory.Qh.obj K)) ≫
        (S.derivedTransitionComparison O ((χ ≫ ψ) ≫ φ)).app K := by
  rw [Category.assoc _ _ ((S.derivedTransitionComparison O ((χ ≫ ψ) ≫ φ)).app K)]
  exact ((S.derivedTransitionCompComparison_assoc_left O χ ψ φ K).trans
      ((congrArg (fun t ↦ S.derivedTransitionCompPrefix O χ ψ φ K ≫ DerivedCategory.Qh.map t)
          (S.transitionPullbackHomotopyComp_assoc_app O χ ψ φ K)).trans
        (S.derivedTransitionCompComparison_assoc_right O χ ψ φ K).symm)).trans
    (Category.assoc
      ((S.derivedTransitionCompComparison O ψ φ).app
        ((S.derivedTransitionPullback O χ).obj (DerivedCategory.Qh.obj K)))
      ((S.derivedTransitionCompComparison O χ (ψ ≫ φ)).app (DerivedCategory.Qh.obj K))
      ((S.derivedTransitionComparison O ((χ ≫ ψ) ≫ φ)).app K)).symm

/-- **The cocycle law for the canonical comparison of derived pullbacks** of Stacks 0D6D. Both
sides are natural transformations into the derived pullback along the threefold composite, which
is a left derived functor, so they agree as soon as they agree after restriction along the
localization. -/
theorem derivedTransitionCompComparison_assoc {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    Functor.whiskerRight (S.derivedTransitionCompComparison O χ ψ)
            (S.derivedTransitionPullback O φ) ≫
          S.derivedTransitionCompComparison O (χ ≫ ψ) φ =
      Functor.whiskerLeft (S.derivedTransitionPullback O χ)
          (S.derivedTransitionCompComparison O ψ φ) ≫
        S.derivedTransitionCompComparison O χ (ψ ≫ φ) := by
  refine Functor.leftDerived_ext (S.derivedTransitionPullback O (χ ≫ ψ ≫ φ))
    (S.derivedTransitionComparison O (χ ≫ ψ ≫ φ))
    (targetQuasiIso (S.componentRingedTopos O k)) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  simp only [Functor.whiskerLeft, Functor.whiskerRight, NatTrans.comp_app]
  exact S.derivedTransitionCompComparison_assoc_app O χ ψ φ K

/-! ### The compositor as an identification of objects -/

/-- The canonical identification `Lf_φ^* Lf_ψ^* K ≅ Lf_{ψ ≫ φ}^* K` given by the compositor of
derived pullbacks of Stacks 0D6D. -/
def derivedModulePasteIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedTransitionPullback O φ).obj ((S.derivedTransitionPullback O ψ).obj X) ≅
      (S.derivedTransitionPullback O (ψ ≫ φ)).obj X :=
  (S.derivedTransitionCompIso O ψ φ).app X

/-- The compositor is natural in the object. -/
theorem derivedModulePasteIso_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    {X Y : DerivedCategory (S.componentRingedTopos O l).Modules} (f : X ⟶ Y) :
    (S.derivedTransitionPullback O φ).map ((S.derivedTransitionPullback O ψ).map f) ≫
        (S.derivedModulePasteIso O ψ φ Y).hom =
      (S.derivedModulePasteIso O ψ φ X).hom ≫ (S.derivedTransitionPullback O (ψ ≫ φ)).map f :=
  (S.derivedTransitionCompIso O ψ φ).hom.naturality f

/-- **The cocycle law for the compositor of derived pullbacks, as an identification of
objects.** This is the form Stacks 0GMF consumes: the two ways of identifying a threefold
derived pullback of an object with its derived pullback along the composite simplex map agree.
No transport appears, composition in the simplex category being associative by `rfl`. -/
theorem derivedModulePasteIso_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : DerivedCategory (S.componentRingedTopos O k).Modules) :
    (S.derivedModulePasteIso O ψ φ ((S.derivedTransitionPullback O χ).obj X)).hom ≫
        (S.derivedModulePasteIso O χ (ψ ≫ φ) X).hom =
      (S.derivedTransitionPullback O φ).map (S.derivedModulePasteIso O χ ψ X).hom ≫
        (S.derivedModulePasteIso O (χ ≫ ψ) φ X).hom := by
  have h := NatTrans.congr_app (S.derivedTransitionCompComparison_assoc O χ ψ φ) X
  simp only [Functor.whiskerLeft, Functor.whiskerRight, NatTrans.comp_app] at h
  exact h.symm

/-! ### The compositor at a chosen factorization -/

/-- The compositor of derived pullbacks, written at a chosen factorization `ψ ≫ φ = θ` of a
simplex map. -/
def derivedModulePasteIsoOfEq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n)
    (h : ψ ≫ φ = θ) (X : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedTransitionPullback O φ).obj ((S.derivedTransitionPullback O ψ).obj X) ≅
      (S.derivedTransitionPullback O θ).obj X :=
  S.derivedModulePasteIso O ψ φ X ≪≫
    eqToIso (congrArg (fun t ↦ (S.derivedTransitionPullback O t).obj X) h)

/-- The compositor at a factorization is natural in the object. -/
theorem derivedModulePasteIsoOfEq_naturality {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (θ : l ⟶ n) (h : ψ ≫ φ = θ)
    {X Y : DerivedCategory (S.componentRingedTopos O l).Modules} (f : X ⟶ Y) :
    (S.derivedTransitionPullback O φ).map ((S.derivedTransitionPullback O ψ).map f) ≫
        (S.derivedModulePasteIsoOfEq O ψ φ θ h Y).hom =
      (S.derivedModulePasteIsoOfEq O ψ φ θ h X).hom ≫ (S.derivedTransitionPullback O θ).map f := by
  subst h
  simpa only [derivedModulePasteIsoOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
    using S.derivedModulePasteIso_naturality O ψ φ f

/-- At the tautological factorization the compositor at a factorization is the compositor. -/
theorem derivedModulePasteIsoOfEq_rfl {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : DerivedCategory (S.componentRingedTopos O l).Modules) :
    S.derivedModulePasteIsoOfEq O ψ φ (ψ ≫ φ) rfl X = S.derivedModulePasteIso O ψ φ X := by
  refine Iso.ext ?_
  simp only [derivedModulePasteIsoOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]

/-- **The cocycle law for the compositor at factorizations.** -/
theorem derivedModulePasteIsoOfEq_assoc {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m)
    (φ : m ⟶ n) (χψ : k ⟶ m) (ψφ : l ⟶ n) (χψφ : k ⟶ n) (h₁ : χ ≫ ψ = χψ)
    (h₂ : ψ ≫ φ = ψφ) (h₃ : χψ ≫ φ = χψφ) (h₄ : χ ≫ ψφ = χψφ)
    (K : DerivedCategory (S.componentRingedTopos O k).Modules) :
    (S.derivedTransitionPullback O φ).map (S.derivedModulePasteIsoOfEq O χ ψ χψ h₁ K).hom ≫
        (S.derivedModulePasteIsoOfEq O χψ φ χψφ h₃ K).hom =
      (S.derivedModulePasteIsoOfEq O ψ φ ψφ h₂ ((S.derivedTransitionPullback O χ).obj K)).hom ≫
        (S.derivedModulePasteIsoOfEq O χ ψφ χψφ h₄ K).hom := by
  subst h₁ h₂ h₃
  simp only [derivedModulePasteIsoOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  erw [eqToHom_refl, Category.comp_id]
  exact (S.derivedModulePasteIso_assoc O χ ψ φ K).symm

end CategoryTheory.SimplicialSiteSituation

end
