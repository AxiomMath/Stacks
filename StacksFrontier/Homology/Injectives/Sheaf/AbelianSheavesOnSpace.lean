module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Injective abelian sheaves on a topological space

The category of sheaves of abelian groups on a topological space `X` has enough injectives,
and the injective embeddings can be chosen functorially. This is Tag 01DG.

Both statements come from the fact that abelian sheaves on `X` form a Grothendieck abelian
category: the site of opens of `X` is essentially small, so sheafification exists and
`Sheaf.isGrothendieckAbelian_of_essentiallySmall` applies, and a Grothendieck abelian category
has enough injectives. For the functorial statement one uses, in addition, the functorial
factorization of the monomorphisms by their right lifting property: factoring the zero map
`A ⟶ 0` functorially gives a monomorphism `A ⟶ Z A` whose cofibre has the right lifting
property against all monomorphisms, and for a map to the zero object that property is exactly
injectivity of `Z A`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Injectives.abelianSheaf_enoughInjectives`: every abelian sheaf on `X` embeds into an
  injective abelian sheaf.
* `Stacks.Injectives.abelianSheaf_hasFunctorialInjectiveEmbeddings`: the functorial
  strengthening.

## Implementation notes

Abelian sheaves on `X` are represented by `TopCat.Sheaf AddCommGrpCat X`. The two assertions
of the source are recorded separately, the first as an instance so that it is available to
instance search.

## References

* [Stacks Project, Tag 01DG](https://stacks.math.columbia.edu/tag/01DG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped ZeroObject

universe u v

namespace Stacks.Injectives

/-- **Stacks 01DG.** The category of abelian sheaves on a topological space has enough
injectives. -/
@[stacks 01DG "enough injectives"]
instance abelianSheaf_enoughInjectives (X : TopCat.{u}) :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{max u v} X) := by
  let : Limits.PreservesLimits (forget AddCommGrpCat.{max u v}) :=
    AddCommGrpCat.forget_preservesLimits
  let : ∀ U : Opens X, Small.{u} ((Opens.grothendieckTopology X).Cover U)ᵒᵖ :=
    fun _ => inferInstance
  let J := Opens.grothendieckTopology X
  let : HasSheafify J AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite J AddCommGrpCat
  let : Abelian (TopCat.Sheaf AddCommGrpCat.{max u v} X) := sheafIsAbelian
  exact @IsGrothendieckAbelian.enoughInjectives.{max u v, max u v, max (u + 1) (v + 1)}
    _ _ _ (Sheaf.isGrothendieckAbelian_of_essentiallySmall J AddCommGrpCat)

/-- **Stacks 01DG.** Abelian sheaves on a topological space admit functorial injective
embeddings. -/
@[stacks 01DG "functorial injective embeddings"]
theorem abelianSheaf_hasFunctorialInjectiveEmbeddings (X : TopCat.{u}) :
    HasFunctorialInjectiveEmbeddings (TopCat.Sheaf AddCommGrpCat.{max u v} X) := by
  let : Limits.PreservesLimits (forget AddCommGrpCat.{max u v}) :=
    AddCommGrpCat.forget_preservesLimits
  let : ∀ U : Opens X, Small.{u} ((Opens.grothendieckTopology X).Cover U)ᵒᵖ :=
    fun _ => inferInstance
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite (Opens.grothendieckTopology X) AddCommGrpCat
  let C := TopCat.Sheaf AddCommGrpCat.{max u v} X
  let : Abelian C := by dsimp only [C]; infer_instance
  have groth : IsGrothendieckAbelian.{max u v} C :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall (Opens.grothendieckTopology X) AddCommGrpCat
  let z : C ⥤ Arrow C :=
    { obj := fun A => Arrow.mk (0 : A ⟶ 0)
      map := fun f => Arrow.homMk f (𝟙 _) (by simp) }
  let d := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms C) (MorphismProperty.monomorphisms C).rlp
  let E : C ⥤ Arrow C :=
    { obj := fun A => Arrow.mk (d.i.app (z.obj A))
      map := fun f => Arrow.homMk f (d.Z.map (z.map f)) (d.i.naturality (z.map f)) }
  refine ⟨E, ?_, ?_, ?_⟩
  · change E ⋙ Arrow.leftFunc = 𝟭 C
    exact CategoryTheory.Functor.ext (h_obj := by intro A; rfl) (h_map := by intro A B f; rfl)
  · change ∀ A, Mono (E.obj A).hom
    exact fun A => d.hi (z.obj A)
  · change ∀ A, Injective (E.obj A).right
    intro A
    rw [injective_iff_rlp_monomorphisms_zero]
    exact (Limits.isZero_zero C).eq_of_tgt (d.p.app (z.obj A)) 0 ▸ d.hp (z.obj A)

end Stacks.Injectives
