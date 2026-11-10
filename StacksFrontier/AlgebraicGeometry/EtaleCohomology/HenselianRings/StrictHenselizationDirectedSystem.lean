module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# The strict henselization as a limit over a directed set with a least element

Let `B` be a big étale site containing a scheme `S` and `s` a geometric point of `S`. The strict
henselization `Spec 𝒪^{sh}_{S,s}` is the limit of the small cofinal family of affine étale
neighbourhoods of `s` (`AlgebraicGeometry.strictHenselizationAffineConeIsLimit`), indexed by a
small cofiltered category. By Deligne's lemma (`CategoryTheory.IsFiltered.exists_directed`, Stacks
0032) that category receives an initial functor from the opposite of a directed set, which may
moreover be taken to have a least element. This file records that reindexing: an inverse system
of affine étale neighbourhoods of `s` over a directed set with a least element, whose limit is the
strict henselization.

## Main definitions

* `AlgebraicGeometry.nbhdIndex`: the directed set with a least element, for a final functor `G`
  from a directed set (`AlgebraicGeometry.exists_directed_nbhd` provides one).
* `AlgebraicGeometry.nbhdSystem`: the neighbourhoods, as an inverse system of objects of the small
  étale site of `S`.
* `AlgebraicGeometry.nbhdCone`: the strict henselization as a cone over it.

## Main results

* `AlgebraicGeometry.nbhdConeIsLimit`: it is a limit cone.
* `AlgebraicGeometry.nbhdCone_π_comp_hom`: its legs lie over `S` through
  `AlgebraicGeometry.strictHenselizationToBase`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- There is a final functor from a nonempty directed set to the opposite of the category of
affine étale neighbourhoods of `s`. -/
theorem exists_directed_nbhd :
    ∃ (α : Type u) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (G : α ⥤ (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ), G.Final :=
  IsFiltered.exists_directed _

variable {α : Type u} [PartialOrder α] [IsDirected α (· ≤ ·)]
  (G : α ⥤ (etaleNeighborhoodAffineIndex B S hS s)ᵒᵖ) [G.Final] (a₀ : α)

/-- The directed set of neighbourhoods above a chosen one: it has a least element. -/
def nbhdIndex (a₀ : α) : Type u := {a : α // a₀ ≤ a}

/-- The partial order on `nbhdIndex a₀` induced from `α`. -/
instance : PartialOrder (nbhdIndex a₀) := Subtype.partialOrder _

/-- The least element of `nbhdIndex a₀` is `a₀`. -/
instance : OrderBot (nbhdIndex a₀) where
  bot := ⟨a₀, le_rfl⟩
  bot_le a := a.2

/-- `nbhdIndex a₀` is directed. -/
instance : IsDirected (nbhdIndex a₀) (· ≤ ·) where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-- `nbhdIndex a₀` is nonempty. -/
instance : Nonempty (nbhdIndex a₀) := ⟨⊥⟩

/-- The inclusion of the neighbourhoods above the chosen one. -/
def nbhdIncl : nbhdIndex a₀ ⥤ α :=
  (Subtype.mono_coe (fun a : α => a₀ ≤ a)).functor

/-- The inclusion `nbhdIncl a₀` is a final functor. -/
instance : (nbhdIncl a₀).Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun a => ?_) (fun {d c} f g => ?_)
  · obtain ⟨b, hab, hb⟩ := directed_of (· ≤ ·) a a₀
    exact ⟨⟨b, hb⟩, ⟨homOfLE hab⟩⟩
  · exact ⟨c, 𝟙 _, Subsingleton.elim _ _⟩

/-- **The affine étale neighbourhoods of `s`, indexed by a directed set with a least element.** -/
def nbhdIndexFunctor : (nbhdIndex a₀)ᵒᵖ ⥤ etaleNeighborhoodAffineIndex B S hS s :=
  (nbhdIncl a₀ ⋙ G).leftOp

/-- The functor `nbhdIndexFunctor B S hS s G a₀` is initial. -/
instance : (nbhdIndexFunctor B S hS s G a₀).Initial := by
  unfold nbhdIndexFunctor
  infer_instance

/-- The neighbourhoods as an inverse system of objects of the small étale site of `S`. -/
def nbhdSystem : (nbhdIndex a₀)ᵒᵖ ⥤ S.Etale :=
  nbhdIndexFunctor B S hS s G a₀ ⋙ etaleNeighborhoodAffineInclusion B S hS s ⋙
    Functor.Elements.π _ ⋙ SmallEtale.toEtaleSite B S hS

/-- The strict henselization as a cone over the system of neighbourhoods; its apex is
`strictHenselization B S hS s` itself. -/
abbrev nbhdCone : Cone (nbhdSystem B S hS s G a₀ ⋙ Scheme.Etale.forget S ⋙ Over.forget S) where
  pt := strictHenselization B S hS s
  π := ((strictHenselizationAffineCone B S hS s).whisker (nbhdIndexFunctor B S hS s G a₀)).π

/-- **The strict henselization is the limit of the system of neighbourhoods.** -/
def nbhdConeIsLimit : IsLimit (nbhdCone B S hS s G a₀) :=
  (Functor.Initial.isLimitWhiskerEquiv (nbhdIndexFunctor B S hS s G a₀)
    (strictHenselizationAffineCone B S hS s)).symm (strictHenselizationAffineConeIsLimit B S hS s)

omit [IsDirected α (· ≤ ·)] [G.Final] in
/-- The apex of `nbhdCone` is the strict henselization. -/
theorem nbhdCone_pt : (nbhdCone B S hS s G a₀).pt = strictHenselization B S hS s := rfl

omit [IsDirected α (· ≤ ·)] [G.Final] in
/-- Each leg of `nbhdCone`, followed by the structure morphism of the neighbourhood to `S`, is
`strictHenselizationToBase`. -/
theorem nbhdCone_π_comp_hom (i : (nbhdIndex a₀)ᵒᵖ) :
    (nbhdCone B S hS s G a₀).π.app i ≫ ((nbhdSystem B S hS s G a₀).obj i).hom =
      strictHenselizationToBase B S hS s :=
  strictHenselizationAffineCone_π_comp_hom_eq B S hS s _

/-- Each neighbourhood in `nbhdSystem` is an affine scheme. -/
instance (i : (nbhdIndex a₀)ᵒᵖ) : IsAffine ((nbhdSystem B S hS s G a₀).obj i).left :=
  isAffine_etaleNeighborhoodAffineDiagram_obj B S hS s _

end AlgebraicGeometry
