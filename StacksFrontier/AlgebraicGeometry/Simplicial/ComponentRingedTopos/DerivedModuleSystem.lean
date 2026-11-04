module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullback

/-!
# Simplicial systems of the derived category of modules (Stacks 0D9N)

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. A *simplicial system of the derived category of modules* consists of an object `K_n`
of `D(O_n)` for every simplicial degree `n` together with a map `K_φ : Lf_φ^* K_m ⟶ K_n` for
every simplex map `φ : m ⟶ n`, subject to the cocycle condition

`K_{ψ ≫ φ} = K_φ ∘ Lf_φ^* K_ψ`

read through the canonical identification `Lf_{ψ ≫ φ}^* = Lf_ψ^* Lf_φ^*`. The system is
*cartesian* when every `K_φ` is an isomorphism, and a morphism of systems is a map in every
degree commuting with every transition.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem`: **Stacks 0D9N**, the
  data `(1)`, `(2)` and the cocycle condition.
* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.Cartesian`: the
  cartesian condition.
* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.Hom`: morphisms of
  simplicial systems of the derived category of modules.

## Main results

* `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.category`: systems form
  a category, with degreewise identities and composition;
  `SimplicialDerivedModuleSystem.evaluation` reads off a fixed simplicial degree and
  `SimplicialDerivedModuleSystem.isoMk` assembles an isomorphism of systems from compatible
  degreewise isomorphisms.

## Implementation notes

*The cocycle condition is written through the canonical comparison map.* The source states it
as an equality of maps out of `Lf_{ψ ≫ φ}^* K_l`, having identified that functor with
`Lf_ψ^* ⋙ Lf_φ^*`; that identification is Stacks 0D6D. This tree has the canonical comparison
`CategoryTheory.SimplicialSiteSituation.derivedTransitionCompComparison` in that direction but
not its invertibility, which needs a resolving class of K-flat complexes. The condition is
therefore stated by composing with the comparison, which is literally the source's equation
pulled back along it, and which agrees with the source's condition as soon as 0D6D is
available. Nothing is quantified over and no comparison is chosen: the condition refers to the
one canonical map, pinned by
`CategoryTheory.SimplicialSiteSituation.derivedTransitionComp_fac`.

*The identity law is not a field*, exactly as in the source: Stacks 0D9N imposes the cocycle
condition and nothing else, as Stacks 0D9G does for the abelian analogue
`CategoryTheory.SimplicialDerivedSystem`.

*The existence of `Lf_φ^*` is Stacks 06YY* and is carried as an instance-implicit hypothesis;
see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/DerivedPullback.lean`.

## References

* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]

/-- **Stacks 0D9N.** A simplicial system of the derived category of modules for a sheaf of
commutative rings `O` on the total site of a simplicial-site situation: an object `K_n` of the
derived category of `O_n`-modules in every simplicial degree `n`, a map
`K_φ : Lf_φ^* K_m ⟶ K_n` for every simplex map `φ : m ⟶ n`, and the cocycle condition
`K_{ψ ≫ φ} = K_φ ∘ Lf_φ^* K_ψ` under the canonical identification of `Lf_{ψ ≫ φ}^*` with
`Lf_ψ^* ⋙ Lf_φ^*`. -/
@[stacks 0D9N "the data of a simplicial system and its cocycle condition"]
structure SimplicialDerivedModuleSystem where
  /-- An object of the unbounded derived category of modules in each simplicial degree. -/
  obj : ∀ n : SimplexCategory, DerivedCategory ((S.componentRingedTopos O n).Modules)
  /-- The map `K_φ : Lf_φ^* K_m ⟶ K_n` attached to a simplex map `φ : m ⟶ n`, where `Lf_φ^*`
  is the derived pullback along the induced morphism of ringed topoi. -/
  map : ∀ {m n : SimplexCategory} (φ : m ⟶ n), (S.derivedTransitionPullback O φ).obj (obj m) ⟶ obj n
  /-- The cocycle condition `K_{ψ ≫ φ} = K_φ ∘ Lf_φ^* K_ψ`, read through the canonical
  comparison `Lf_ψ^* Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` of derived pullbacks. -/
  map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    (S.derivedTransitionCompComparison O ψ φ).app (obj l) ≫ map (ψ ≫ φ) =
      (S.derivedTransitionPullback O φ).map (map ψ) ≫ map φ

namespace SimplicialDerivedModuleSystem

variable {S} {O}

/-- **Stacks 0D9N.** A simplicial system of the derived category of modules is *cartesian* if
all of its transition maps `K_φ` are isomorphisms. -/
@[stacks 0D9N "cartesian systems"]
abbrev Cartesian (K : SimplicialDerivedModuleSystem S O) : Prop :=
  ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ)

/-- **Stacks 0D9N.** A morphism of simplicial systems of the derived category of modules: a
morphism in every simplicial degree commuting with all of the transition maps. -/
@[stacks 0D9N "morphisms of simplicial systems"]
structure Hom (K L : SimplicialDerivedModuleSystem S O) where
  /-- The morphism in each simplicial degree. -/
  app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n
  /-- Compatibility with the derived transition maps. -/
  naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    K.map φ ≫ app n = (S.derivedTransitionPullback O φ).map (app m) ≫ L.map φ

/-- A morphism of simplicial systems is determined by its degreewise components. -/
@[ext] theorem hom_ext {K L : SimplicialDerivedModuleSystem S O} (f g : Hom K L)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Simplicial systems of the derived category of modules form a category, with degreewise
identities and composition. -/
noncomputable instance category : Category (SimplicialDerivedModuleSystem S O) where
  Hom := Hom
  id K := ⟨fun n ↦ 𝟙 (K.obj n), by intros; simp⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, by
    intro m n φ
    rw [← Category.assoc, f.naturality, Category.assoc, g.naturality, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]⟩
  id_comp _ := hom_ext _ _ fun _ ↦ Category.id_comp _
  comp_id _ := hom_ext _ _ fun _ ↦ Category.comp_id _
  assoc _ _ _ := hom_ext _ _ fun _ ↦ Category.assoc _ _ _

/-- Evaluation of a simplicial system of the derived category of modules in a fixed simplicial
degree. -/
def evaluation (n : SimplexCategory) :
    SimplicialDerivedModuleSystem S O ⥤
      DerivedCategory ((S.componentRingedTopos O n).Modules) where
  obj K := K.obj n
  map f := f.app n

/-- Degreewise isomorphisms compatible with the transition maps assemble into an isomorphism of
simplicial systems. -/
def isoMk (K L : SimplicialDerivedModuleSystem S O) (e : ∀ n, K.obj n ≅ L.obj n)
    (h : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ (e n).hom = (S.derivedTransitionPullback O φ).map (e m).hom ≫ L.map φ) :
    K ≅ L where
  hom := ⟨fun n ↦ (e n).hom, h⟩
  inv := ⟨fun n ↦ (e n).inv, by
    intro m n φ
    refine (cancel_mono (e n).hom).1 ?_
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h φ, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]⟩
  hom_inv_id := hom_ext _ _ fun _ ↦ Iso.hom_inv_id _
  inv_hom_id := hom_ext _ _ fun _ ↦ Iso.inv_hom_id _

end SimplicialDerivedModuleSystem

end CategoryTheory.SimplicialSiteSituation

end
