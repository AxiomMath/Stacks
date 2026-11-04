module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeLimitQcqs
public import StacksCore.Tactic.StacksAttribute

/-!
# A closed immersion as a limit of closed immersions of finite presentation

Let `f : X ⟶ Y` be a closed immersion into a quasi-compact, quasi-separated scheme.  The
quasi-coherent ideal sheaf data `f.ker` is the supremum of the finitely generated ideal sheaf
data below it, each of which cuts out a closed subscheme of `Y` whose closed immersion is of
finite presentation.  Those closed subschemes form a directed inverse system over `Y` with
limit `X`.

## Main results

* `AlgebraicGeometry.isLimit_of_iSup_ker_eq`: a cone over a cofiltered diagram of closed
  subschemes of `Y`, whose legs compose with the structure morphisms to one closed immersion
  `f`, is a limit cone as soon as the supremum of the ideal sheaves of the structure morphisms
  is the ideal sheaf of `f`.
* `AlgebraicGeometry.exists_isLimit_closedImmersion_finitePresentation`: the directed inverse
  system of closed immersions of finite presentation with limit the given closed subscheme.

## Implementation notes

The inverse system is indexed by the opposite of
`Stacks.Flatness.FinitePresentationSubscheme f.ker`, the ideal sheaf data below `f.ker` whose
closed immersion is of finite presentation, ordered by inclusion.  That index type is a subtype
of `Y.IdealSheafData` and so already lives in the universe of the schemes; no transport to a
small model is needed.  It is directed and nonempty by
`Stacks.Flatness.finitePresentationSubscheme_isFiltered`, and
`Stacks.Flatness.le_iSup_finitePresentationSubscheme` — which is Tag 01PG for ideal sheaf data —
supplies the supremum.

The limit statement is proved directly rather than transported from
`Stacks.Flatness.isLimitSubschemeCone`, which is the same mathematics for the canonical closed
subscheme `f.ker.subscheme` but as a cone in `CategoryTheory.Over Y`.  Transporting it would
require both that `CategoryTheory.Over.forget` reflects this limit and an identification of `X`
with `f.ker.subscheme`; the direct argument below uses only that a cone over a cofiltered
diagram of schemes over `Y` induces a single morphism to `Y`, which then kills the supremum and
so factors uniquely through `f`.

The lift out of a cone, and the two properties characterising it, are given names of their own
rather than being written inside the construction of the limit cone: elaborating all three
fields of `CategoryTheory.Limits.IsLimit` in a single declaration costs more than two hundred
times the heartbeats the three separate declarations cost between them, and exceeds the default
budget.

## References

* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry

/-! ### A cone of closed subschemes is a limit when the ideal sheaves exhaust -/

section ConeLimit

variable {J : Type v} [Category.{w} J] [IsCofiltered J] {D : J ⥤ Scheme.{u}}
  {X Y : Scheme.{u}} (f : X ⟶ Y) (t : D ⟶ (Functor.const J).obj Y)

/-- All the legs of a cone over a cofiltered diagram of schemes over `Y` induce the same
morphism to `Y`. -/
theorem cone_comp_eq_of_isCofiltered (s : Cone D) (i j : J) :
    s.π.app i ≫ t.app i = s.π.app j ≫ t.app j := by
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  rw [← s.w a, ← s.w b]
  simp only [Category.assoc, NatTrans.naturality, Functor.const_obj_map]

/-- The ideal sheaf of the morphism to `Y` induced by a cone contains the ideal sheaf of `f`,
when the latter is the supremum of the ideal sheaves of the diagram. -/
theorem ker_le_cone_comp_ker (hsup : (⨆ j, (t.app j).ker) = f.ker) (s : Cone D) (j₀ : J) :
    f.ker ≤ (s.π.app j₀ ≫ t.app j₀).ker := by
  rw [← hsup]
  refine iSup_le fun j => ?_
  rw [cone_comp_eq_of_isCofiltered t s j₀ j]
  exact Scheme.Hom.le_ker_comp _ _

/-- The morphism from the vertex of a cone to `X`, through which the morphism to `Y` that the
cone induces factors. -/
noncomputable def coneLift_of_iSup_ker_eq [IsClosedImmersion f]
    (hsup : (⨆ j, (t.app j).ker) = f.ker) (s : Cone D) (j₀ : J) : s.pt ⟶ X :=
  IsClosedImmersion.lift f (s.π.app j₀ ≫ t.app j₀) (ker_le_cone_comp_ker f t hsup s j₀)

/-- The lift out of a cone composed with `f` is the morphism to `Y` that the cone induces. -/
@[simp]
theorem coneLift_of_iSup_ker_eq_fac [IsClosedImmersion f]
    (hsup : (⨆ j, (t.app j).ker) = f.ker) (s : Cone D) (j₀ : J) :
    coneLift_of_iSup_ker_eq f t hsup s j₀ ≫ f = s.π.app j₀ ≫ t.app j₀ :=
  IsClosedImmersion.lift_fac _ _ _

section Limit

variable [IsClosedImmersion f]

/-- The lift out of a cone is compatible with the legs of the cone over `X`. -/
theorem coneLift_of_iSup_ker_eq_comp_app {p : (Functor.const J).obj X ⟶ D}
    (hpt : ∀ j, p.app j ≫ t.app j = f) (hsup : (⨆ j, (t.app j).ker) = f.ker)
    (hmono : ∀ j, Mono (t.app j)) (s : Cone D) (j₀ j : J) :
    coneLift_of_iSup_ker_eq f t hsup s j₀ ≫ p.app j = s.π.app j := by
  have := hmono j
  refine (cancel_mono (t.app j)).1 ?_
  rw [Category.assoc, hpt j, coneLift_of_iSup_ker_eq_fac]
  exact cone_comp_eq_of_isCofiltered t s j₀ j

/-- The lift out of a cone is the only morphism compatible with the legs of the cone over
`X`. -/
theorem eq_coneLift_of_iSup_ker_eq {p : (Functor.const J).obj X ⟶ D}
    (hpt : ∀ j, p.app j ≫ t.app j = f) (hsup : (⨆ j, (t.app j).ker) = f.ker)
    (s : Cone D) (j₀ : J) (m : s.pt ⟶ X) (hm : ∀ j, m ≫ p.app j = s.π.app j) :
    m = coneLift_of_iSup_ker_eq f t hsup s j₀ := by
  refine (cancel_mono f).1 ?_
  rw [coneLift_of_iSup_ker_eq_fac, ← hpt j₀, ← Category.assoc, hm]

/-- A cone over a cofiltered diagram of closed subschemes of `Y` is a limit cone as soon as its
legs compose with the structure morphisms to one closed immersion `f` whose ideal sheaf is the
supremum of the ideal sheaves of those structure morphisms.

A cone over the diagram induces one morphism to `Y`, independent of the leg it is computed from;
that morphism kills every ideal sheaf of the diagram, hence their supremum, hence factors
uniquely through `f`. -/
noncomputable def isLimit_of_iSup_ker_eq (p : (Functor.const J).obj X ⟶ D)
    (hpt : ∀ j, p.app j ≫ t.app j = f) (hsup : (⨆ j, (t.app j).ker) = f.ker)
    (hmono : ∀ j, Mono (t.app j)) : IsLimit (Cone.mk X p) :=
  let j₀ : J := (IsCofiltered.nonempty (C := J)).some
  { lift := fun s => coneLift_of_iSup_ker_eq f t hsup s j₀
    fac := fun s j => coneLift_of_iSup_ker_eq_comp_app f t hpt hsup hmono s j₀ j
    uniq := fun s m hm => eq_coneLift_of_iSup_ker_eq f t hpt hsup s j₀ m hm }

end Limit

end ConeLimit

/-! ### The system of finitely presented closed subschemes containing a closed subscheme -/

section FinitePresentationSystem

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ideal sheaf data below the ideal sheaf of `f` whose closed subscheme has a closed
immersion of finite presentation, ordered by inclusion.  This is the index of the inverse system
of [Stacks, Tag 09ZP]. -/
private abbrev kerFinitePresentationIndex := Stacks.Flatness.FinitePresentationSubscheme f.ker

/-- The zero ideal sheaf, which cuts out `Y` itself, is an index: the identity is of finite
presentation. -/
private instance : Nonempty (kerFinitePresentationIndex f) :=
  ⟨⟨⊥, Stacks.Flatness.finitePresentation_subschemeι_bot, bot_le⟩⟩

/-- The indices are directed: the sum of two of them is one, because the scheme-theoretic
intersection of two finitely presented closed subschemes is finitely presented. -/
private instance : IsDirected (kerFinitePresentationIndex f) (· ≤ ·) :=
  ⟨fun A B => ⟨⟨A.1 ⊔ B.1,
    Stacks.Flatness.finitePresentation_subschemeι_sup A.2.1 B.2.1, sup_le A.2.2 B.2.2⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

/-- The ideal sheaf of the closed immersion of a stage is contained in that of `f`. -/
private theorem ker_subschemeι_le (A : kerFinitePresentationIndex f) :
    (A.1).subschemeι.ker ≤ f.ker :=
  (Scheme.IdealSheafData.ker_subschemeι A.1).le.trans A.2.2

/-- The inverse system over `Y` of the finitely presented closed subschemes of `Y` containing
the closed subscheme `f` cuts out.  Its transition morphisms are the inclusions of closed
subschemes.

This is `Stacks.Flatness.subschemeDiagram` composed with `CategoryTheory.Over.forget`, written
out rather than composed: the objects and the morphisms of this diagram occur throughout the
argument below, and reading them off a composite of two functors costs a definitional unfolding
of `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, which is built from glue data and is
expensive. -/
private noncomputable def kerFinitePresentationDiagram :
    (kerFinitePresentationIndex f)ᵒᵖ ⥤ Scheme.{u} where
  obj A := (A.unop.1).subscheme
  map g := Scheme.IdealSheafData.inclusion g.unop.le
  map_id _ := Scheme.IdealSheafData.inclusion_id _
  map_comp _ _ := (Scheme.IdealSheafData.inclusion_comp _ _).symm

/-- The transition morphisms of the system are the inclusions of closed subschemes, so they
commute with the closed immersions into `Y`. -/
private theorem kerFinitePresentationDiagram_map_comp_subschemeι
    {A B : (kerFinitePresentationIndex f)ᵒᵖ} (g : A ⟶ B) :
    (kerFinitePresentationDiagram f).map g ≫ (B.unop.1).subschemeι =
      (A.unop.1).subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι g.unop.le

/-- The closed immersions into `Y` of the stages of the system, as a morphism to the constant
diagram on `Y`. -/
private noncomputable def kerFinitePresentationStructure :
    kerFinitePresentationDiagram f ⟶ (Functor.const (kerFinitePresentationIndex f)ᵒᵖ).obj Y where
  app A := (A.unop.1).subschemeι
  naturality _ _ g := (kerFinitePresentationDiagram_map_comp_subschemeι f g).trans
    (Category.comp_id _).symm

/-- The closed immersions of the stages of the system into `Y` are closed immersions. -/
private theorem isClosedImmersion_kerFinitePresentationStructure_app
    (A : (kerFinitePresentationIndex f)ᵒᵖ) :
    IsClosedImmersion ((kerFinitePresentationStructure f).app A) :=
  inferInstanceAs (IsClosedImmersion ((A.unop.1).subschemeι))

/-- The closed immersions of the stages of the system into `Y` are monomorphisms. -/
private theorem mono_kerFinitePresentationStructure_app
    (A : (kerFinitePresentationIndex f)ᵒᵖ) :
    Mono ((kerFinitePresentationStructure f).app A) :=
  inferInstanceAs (Mono ((A.unop.1).subschemeι))

/-- The ideal sheaf of the closed immersion of a stage into `Y` is the ideal sheaf data indexing
that stage. -/
private theorem ker_kerFinitePresentationStructure_app
    (A : (kerFinitePresentationIndex f)ᵒᵖ) :
    ((kerFinitePresentationStructure f).app A).ker = (A.unop.1 : Y.IdealSheafData) :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- The closed immersion of `X` into a stage of the system. -/
private noncomputable def kerFinitePresentationLift [IsClosedImmersion f]
    (A : kerFinitePresentationIndex f) : X ⟶ (A.1).subscheme :=
  IsClosedImmersion.lift (A.1).subschemeι f (ker_subschemeι_le f A)

@[simp]
private theorem kerFinitePresentationLift_fac [IsClosedImmersion f]
    (A : kerFinitePresentationIndex f) :
    kerFinitePresentationLift f A ≫ (A.1).subschemeι = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The closed immersion of `X` into a stage composed with a transition morphism of the system
is the closed immersion of `X` into the later stage. -/
private theorem kerFinitePresentationLift_comp_map [IsClosedImmersion f]
    {A B : (kerFinitePresentationIndex f)ᵒᵖ} (g : A ⟶ B) :
    kerFinitePresentationLift f A.unop ≫ (kerFinitePresentationDiagram f).map g =
      kerFinitePresentationLift f B.unop := by
  refine (cancel_mono ((B.unop.1).subschemeι)).1 ?_
  exact (Category.assoc _ _ _).trans <|
    (congrArg _ (kerFinitePresentationDiagram_map_comp_subschemeι f g)).trans <|
    (kerFinitePresentationLift_fac f A.unop).trans (kerFinitePresentationLift_fac f B.unop).symm

/-- The closed immersions of `X` into the stages of the system, as a morphism from the constant
diagram on `X`. -/
private noncomputable def kerFinitePresentationProjection [IsClosedImmersion f] :
    (Functor.const (kerFinitePresentationIndex f)ᵒᵖ).obj X ⟶ kerFinitePresentationDiagram f where
  app A := kerFinitePresentationLift f A.unop
  naturality _ B g := (Category.id_comp (kerFinitePresentationLift f B.unop)).trans
    (kerFinitePresentationLift_comp_map f g).symm

private theorem kerFinitePresentationProjection_comp_structure [IsClosedImmersion f]
    (A : (kerFinitePresentationIndex f)ᵒᵖ) :
    (kerFinitePresentationProjection f).app A ≫ (kerFinitePresentationStructure f).app A = f :=
  kerFinitePresentationLift_fac f A.unop

/-- The ideal sheaves of the stages of the system have supremum the ideal sheaf of `f`.  This is
[Stacks, Tag 01PG] for ideal sheaf data on a quasi-compact and quasi-separated scheme. -/
private theorem iSup_ker_kerFinitePresentationStructure [CompactSpace Y]
    [QuasiSeparatedSpace Y] :
    (⨆ A, ((kerFinitePresentationStructure f).app A).ker) = f.ker := by
  refine le_antisymm
    (iSup_le fun A => ker_subschemeι_le f A.unop) ?_
  refine (Stacks.Flatness.le_iSup_finitePresentationSubscheme f.ker).trans (iSup_le fun A => ?_)
  exact le_iSup_of_le (Opposite.op A)
    (ker_kerFinitePresentationStructure_app f (Opposite.op A)).ge

end FinitePresentationSystem

/-! ### Tag 09ZP -/

/-- A closed immersion into a quasi-compact and quasi-separated scheme `Y` is a directed inverse
limit, over `Y`, of closed immersions of finite presentation into `Y`.

The system is the system of closed subschemes of `Y` cut out by the ideal sheaf data below
`f.ker` whose closed immersion is of finite presentation.  Those are directed and have supremum
`f.ker` ([Stacks, Tag 01PG] for ideal sheaf data), and a cone of closed subschemes whose ideal
sheaves have supremum `f.ker` has `X` as its limit. -/
@[stacks 09ZP]
theorem exists_isLimit_closedImmersion_finitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Functor Iᵒᵖ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D) (_ : IsLimit (Cone.mk X p)),
      p ≫ t = (Functor.const Iᵒᵖ).map f ∧
        ∀ i, IsClosedImmersion (t.app i) ∧ FinitePresentation (t.app i) := by
  have : IsFiltered (kerFinitePresentationIndex f) :=
    Stacks.Flatness.finitePresentationSubscheme_isFiltered f.ker
  refine ⟨kerFinitePresentationIndex f, inferInstance, inferInstance, inferInstance,
    kerFinitePresentationDiagram f, kerFinitePresentationStructure f,
    kerFinitePresentationProjection f,
    isLimit_of_iSup_ker_eq f (kerFinitePresentationStructure f)
      (kerFinitePresentationProjection f) (kerFinitePresentationProjection_comp_structure f)
      (iSup_ker_kerFinitePresentationStructure f)
      (mono_kerFinitePresentationStructure_app f),
    NatTrans.ext (funext (kerFinitePresentationProjection_comp_structure f)),
    fun A => ⟨isClosedImmersion_kerFinitePresentationStructure_app f A, A.unop.2.1⟩⟩

end AlgebraicGeometry

end
