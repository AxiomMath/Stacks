module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Exact direct image of abelian sheaves along a continuous functor

Let `G : C ⥤ D` be a continuous functor of sites and let `P` be a property of objects of `C`
covering every object. If a locally surjective morphism of sheaves of types on `D` is surjective
on sections over `G.obj U` for every `U` with `P U`, then the direct image
`Sheaf D ⥤ Sheaf C` of abelian sheaves is exact.

Direct image is precomposition with `G.op`, so it preserves finite limits — this is
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous` — and its sections over
an object `U` of `C` are the sections over `G.obj U`. A surjection of abelian sheaves on `D` is
locally surjective, hence surjective on sections over the weakly contractible object `G.obj U`;
as `P` covers every object of `C`, the direct image of that surjection is locally surjective and
so again a surjection.
A functor of abelian categories preserving kernels and epimorphisms is exact.

## Main results

* `Stacks.WeaklyContractible.preservesEpimorphisms_sheafPushforwardContinuous`: it preserves
  surjections as soon as the covering family lands in weakly contractible objects.
* `Stacks.WeaklyContractible.exact_sheafPushforwardContinuous`: it is exact.

## Implementation notes

Weak contractibility of the objects `G.obj U` enters as the surjectivity statement it is defined
by, at the value universe of the abelian sheaves, rather than through
`CategoryTheory.GrothendieckTopology.IsWeaklyContractible`: the latter is stated at the morphism
universe of the site and transported to other universes only for a site that is small at that
universe, which the pro-étale sites of schemes are not.

## References

* [Stacks Project, Tag 0945](https://stacks.math.columbia.edu/tag/0945)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u v' u'

namespace Stacks.WeaklyContractible

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) [G.IsContinuous J K]

variable [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [K.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- If every object of `C` is covered by objects `U` with `P U`, and a locally surjective
morphism of sheaves of types on `D` is surjective on sections over each `G.obj U`, then direct
image of abelian sheaves preserves surjections. -/
theorem preservesEpimorphisms_sheafPushforwardContinuous
    (P : ObjectProperty C) (hP : J.HasEnoughObjects P)
    (hG : ∀ {U : C}, P U → ∀ (F F' : Sheaf K (Type t)) (φ : F ⟶ F'),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op (G.obj U)))) :
    (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).PreservesEpimorphisms := by
  constructor
  intro F F' φ hφ
  have hloc : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{t} φ).2 hφ
  let forgetAb := sheafCompose K (forget AddCommGrpCat.{t})
  have hset : Sheaf.IsLocallySurjective (forgetAb.map φ) := by
    change Presheaf.IsLocallySurjective K
      (Functor.whiskerRight φ.hom (forget AddCommGrpCat.{t}))
    infer_instance
  have hsurj : ∀ ⦃U : C⦄, P U →
      Function.Surjective (((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).map
        φ).hom.app (op U)) :=
    fun _ hU => hG hU (forgetAb.obj F) (forgetAb.obj F') (forgetAb.map φ) hset
  let ψ := (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).map φ
  exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{t} ψ).mp
    (Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective (φ := ψ.hom) J
      hP hsurj)

/-- **Exactness of direct image on a site covered by weakly contractible objects.** If a
continuous functor carries a covering family of objects to weakly contractible objects, its
direct image of abelian sheaves is exact. -/
theorem exact_sheafPushforwardContinuous
    (P : ObjectProperty C) (hP : J.HasEnoughObjects P)
    (hG : ∀ {U : C}, P U → ∀ (F F' : Sheaf K (Type t)) (φ : F ⟶ F'),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op (G.obj U)))) :
    exactFunctor (Sheaf K AddCommGrpCat.{t}) (Sheaf J AddCommGrpCat.{t})
      (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K) := by
  let L := G.sheafPushforwardContinuous AddCommGrpCat.{t} J K
  have _ : PreservesFiniteLimits L := inferInstance
  have _ : L.PreservesEpimorphisms :=
    preservesEpimorphisms_sheafPushforwardContinuous J K G P hP hG
  have _ : L.Additive := L.additive_of_preserves_binary_products
  have _ : L.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels L
  exact (exactFunctor_iff L).2
    ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology L⟩

end Stacks.WeaklyContractible

end
