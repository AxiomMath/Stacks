module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.Topology.Separation.Connected

/-!
# Profinite spaces are the compact Hausdorff totally disconnected spaces

A cofiltered limit of finite discrete spaces is Hausdorff, compact and totally disconnected, since
the limit sits inside the product as the closed subspace of compatible families. Conversely a
compact Hausdorff totally disconnected space is the limit of its `DiscreteQuotient` diagram.

## Main results

* `IsProfinite`: the Stacks Project's definition — homeomorphic to a cofiltered limit of finite
  discrete topological spaces.
* `TopCat.limit_t2Space_of_discrete`, `TopCat.limit_compactSpace_of_finite_discrete`,
  `TopCat.limit_totallyDisconnectedSpace_of_discrete`: the three properties of such a limit.
* `isProfinite_of_t2_compact_totallyDisconnected`, `isProfinite_iff` (Stacks 08ZY): a space is
  profinite iff it is Hausdorff, quasi-compact and totally disconnected.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- A topological space `X` is *profinite* (in the sense of Stacks 08ZW) iff it is homeomorphic to
a cofiltered limit of finite discrete topological spaces. -/
def IsProfinite (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (F : J ⥤ TopCat.{u}),
    (∀ j, Finite (F.obj j)) ∧ (∀ j, DiscreteTopology (F.obj j)) ∧
    Nonempty (X ≃ₜ (limit F : TopCat.{u}))

namespace TopCat

variable {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{u})

/-- The limit of a diagram of discrete topological spaces in `TopCat` is Hausdorff. -/
lemma limit_t2Space_of_discrete (hd : ∀ j, DiscreteTopology (F.obj j)) :
    T2Space (limit F : TopCat.{u}) := by
  have : ∀ j, T2Space (F.obj j) := fun j => (hd j).toT2Space
  -- The limit embeds, via its projections, injectively and continuously into the product.
  have hinj : Function.Injective (fun (x : (limit F : TopCat.{u})) (j : J) => limit.π F j x) :=
    fun x y h => Limits.Concrete.limit_ext F x y fun j => congrFun h j
  exact T2Space.of_injective_continuous hinj (continuous_pi fun j => (limit.π F j).hom.continuous)

/-- The set of compatible families is closed in the product when each factor is discrete: it is the
intersection, over all morphisms `f : j ⟶ k`, of the closed sets `{u | F.map f (u j) = u k}`. -/
lemma isClosed_limitCone_setOf (hd : ∀ j, DiscreteTopology (F.obj j)) :
    IsClosed {u : ∀ j, F.obj j | ∀ {j k} (f : j ⟶ k), F.map f (u j) = u k} := by
  rw [show {u : ∀ j, F.obj j | ∀ {j k} (f : j ⟶ k), F.map f (u j) = u k}
        = ⋂ (j : J), ⋂ (k : J), ⋂ (f : j ⟶ k),
            {u : ∀ i, F.obj i | F.map f (u j) = u k} from
    Set.ext fun _ => by simp [Set.mem_iInter]]
  refine isClosed_iInter fun j => isClosed_iInter fun k => isClosed_iInter fun f => ?_
  have : T2Space (F.obj k) := (hd k).toT2Space
  exact isClosed_eq ((F.map f).hom.continuous.comp (continuous_apply j)) (continuous_apply k)

/-- The limit of a diagram of finite discrete spaces is compact. -/
lemma limit_compactSpace_of_finite_discrete
    (hf : ∀ j, Finite (F.obj j)) (hd : ∀ j, DiscreteTopology (F.obj j)) :
    CompactSpace (limit F : TopCat.{u}) := by
  have : ∀ j, CompactSpace (F.obj j) := fun j => @Finite.compactSpace _ _ (hf j)
  have : CompactSpace ((TopCat.limitCone F).pt : TopCat.{u}) :=
    isCompact_iff_compactSpace.mp (isClosed_limitCone_setOf F hd).isCompact
  exact (TopCat.homeoOfIso
    ((TopCat.limitConeIsLimit F).conePointUniqueUpToIso (limit.isLimit F))).compactSpace

/-- The limit of a diagram of discrete spaces is totally disconnected: it embeds into the product,
which is totally disconnected. -/
lemma limit_totallyDisconnectedSpace_of_discrete
    (hd : ∀ j, DiscreteTopology (F.obj j)) :
    TotallyDisconnectedSpace (limit F : TopCat.{u}) := by
  have : ∀ j, TotallyDisconnectedSpace (F.obj j) := fun _ => inferInstance
  have hcont : Continuous (fun (x : (limit F : TopCat.{u})) (j : J) => (limit.π F j) x) :=
    continuous_pi fun j => (limit.π F j).hom.continuous
  have hinj : Function.Injective
      (fun (x : (limit F : TopCat.{u})) (j : J) => (limit.π F j) x) :=
    fun _ _ h => Concrete.limit_ext _ _ _ (congrFun h)
  refine ⟨fun S _ hS => Set.subsingleton_of_image hinj S ?_⟩
  exact TotallyDisconnectedSpace.isTotallyDisconnected_univ _ (Set.subset_univ _)
    (hS.image _ hcont.continuousOn)

end TopCat

/-- A Hausdorff, compact, totally disconnected space is a cofiltered limit of finite discrete
spaces, namely the limit of its `DiscreteQuotient` diagram. -/
theorem isProfinite_of_t2_compact_totallyDisconnected
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] : IsProfinite X := by
  let P : Profinite.{u} := Profinite.of X
  exact ⟨DiscreteQuotient X, inferInstance, inferInstance,
    P.diagram ⋙ Profinite.toTopCat,
    fun j => show Finite (P.fintypeDiagram.obj j) from inferInstance,
    fun j => show DiscreteTopology (FintypeCat.toProfinite.obj (P.fintypeDiagram.obj j))
      from inferInstance,
    ⟨TopCat.homeoOfIso (IsLimit.conePointUniqueUpToIso
      (isLimitOfPreserves Profinite.toTopCat P.asLimit) (limit.isLimit _))⟩⟩

/-- **Stacks 08ZY.** For a topological space `X` the following are equivalent: (1) `X` is a
profinite space; (2) `X` is Hausdorff, quasi-compact and totally disconnected. -/
@[stacks 08ZY]
theorem isProfinite_iff (X : Type u) [TopologicalSpace X] :
    IsProfinite X ↔
      (T2Space X ∧ CompactSpace X ∧ TotallyDisconnectedSpace X) := by
  refine ⟨fun ⟨_, _, _, F, hfin, hdisc, ⟨φ⟩⟩ => ?_, fun ⟨_, _, _⟩ =>
    isProfinite_of_t2_compact_totallyDisconnected X⟩
  have := TopCat.limit_t2Space_of_discrete F hdisc
  have := TopCat.limit_compactSpace_of_finite_discrete F hfin hdisc
  have := TopCat.limit_totallyDisconnectedSpace_of_discrete F hdisc
  exact ⟨φ.symm.t2Space, φ.symm.compactSpace, φ.symm.totallyDisconnectedSpace⟩
