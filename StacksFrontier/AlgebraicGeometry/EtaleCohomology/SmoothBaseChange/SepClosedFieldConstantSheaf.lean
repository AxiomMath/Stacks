module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian sheaves on the spectrum of a separably closed field are constant

Let `Ω` be a separably closed field. Every scheme étale over `Spec Ω` is covered by sections of
its structure morphism, so the terminal object `Spec Ω` of the small étale site is a cover-dense
subsite all by itself. Consequently taking global sections is fully faithful on abelian sheaves
on `(Spec Ω)_étale`, and every such sheaf is the constant sheaf on its global sections.

This is the case of a separably closed field of the description of abelian sheaves on
`Spec(K)_étale` as discrete Galois modules ([Stacks, Tag 04JQ]): the absolute Galois group of a
separably closed field is trivial.

## Main definitions

* `Stacks.EtaleCohomology.SepClosedField.terminal` — the terminal object `Spec Ω ⟶ Spec Ω` of the
  small étale site.
* `Stacks.EtaleCohomology.SepClosedField.pointFunctor` — the inclusion of the one-object category
  at it.

## Main results

* `Stacks.EtaleCohomology.SepClosedField.isCoverDense_pointFunctor` — every object of the small
  étale site of `Spec Ω` is covered by maps out of the terminal object.
* `Stacks.EtaleCohomology.SepClosedField.isIso_counit_app` — every abelian sheaf on
  `(Spec Ω)_étale` is the constant sheaf on its global sections, by the counit of
  `CategoryTheory.constantSheafAdj`.

## References

* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The class of étale morphisms of schemes contains the identities, so that the identity of a
scheme is an object of its small étale site, and indeed its terminal object. -/
instance containsIdentities_etale :
    MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
    RingHom.Etale.containsIdentities :
      MorphismProperty.IsMultiplicative (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities

namespace SepClosedField

variable (Ω : Type u) [Field Ω]

/-- The terminal object `Spec Ω ⟶ Spec Ω` of the small étale site of `Spec Ω`. -/
abbrev terminal : (Spec (.of Ω)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))

/-- `Spec Ω ⟶ Spec Ω` is terminal in the small étale site of `Spec Ω`. -/
def terminalIsTerminal : IsTerminal (terminal Ω) :=
  MorphismProperty.Over.mkIdTerminal _ _

/-- The inclusion, into the small étale site of `Spec Ω`, of the one-object category at its
terminal object. -/
abbrev pointFunctor : Discrete PUnit.{1} ⥤ (Spec (.of Ω)).Etale :=
  (Functor.const _).obj (terminal Ω)

/-- The inclusion `pointFunctor Ω` of the terminal object is full. -/
instance : (pointFunctor Ω).Full where
  map_surjective {X Y} f := ⟨eqToHom (Subsingleton.elim X Y),
    (terminalIsTerminal Ω).hom_ext _ _⟩

variable [IsSepClosed Ω]

/-- **Every object of the small étale site of `Spec Ω` is covered by maps out of the terminal
object**, `Ω` being separably closed: every point of a scheme étale over `Spec Ω` is the image of
a section of the structure morphism. -/
@[sga "4 VIII 3.2" "partial"]
instance isCoverDense_pointFunctor :
    (pointFunctor Ω).IsCoverDense (smallEtaleTopology (Spec (.of Ω))) where
  is_cover U := by
    refine (smallEtaleTopology _).superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun σ : terminal Ω ⟶ U => σ)).2 ?_)
    · intro V f hf
      obtain ⟨_, h, _, ⟨σ⟩, rfl⟩ := hf
      exact ⟨⟨⟨⟨⟩⟩, h, σ, rfl⟩⟩
    · refine Set.eq_univ_of_forall fun x => ?_
      have hpt : Subsingleton ↥(Spec (.of Ω)) := inferInstance
      obtain ⟨l, hl, hlx⟩ := exists_fac_of_etale_of_isSepClosed U.hom (𝟙 (Spec (.of Ω))) x
        (hpt.elim _ _)
      exact Set.mem_iUnion.2 ⟨MorphismProperty.Over.homMk l (hl.trans rfl),
        ⟨(default : ↥(Spec (.of Ω))), hlx⟩⟩

/-- **Global sections are fully faithful on abelian sheaves on `(Spec Ω)_étale`.** A map of
sheaves is determined by, and can be prescribed through, its value on the terminal object, which
is a cover-dense subsite. -/
def sectionsFullyFaithful :
    ((sheafSections (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u + 1}).obj
      (op (terminal Ω))).FullyFaithful where
  preimage {F G} g :=
    ⟨Functor.IsCoverDense.restrictHomEquivHom (G := pointFunctor Ω) (ℱ := F.obj) (ℱ' := G)
      { app := fun _ => g, naturality := fun _ _ _ => by simp }⟩
  map_preimage {F G} g := by
    have := congrArg (fun φ => φ.app (op ⟨⟨⟩⟩))
      ((Functor.IsCoverDense.restrictHomEquivHom (G := pointFunctor Ω) (ℱ := F.obj)
        (ℱ' := G)).symm_apply_apply
          { app := fun _ => g, naturality := fun _ _ _ => by simp })
    exact this
  preimage_map {F G} φ := by
    ext1
    refine (Functor.IsCoverDense.restrictHomEquivHom (G := pointFunctor Ω) (ℱ := F.obj)
      (ℱ' := G)).apply_eq_iff_eq_symm_apply.2 ?_
    ext ⟨⟨⟨⟩⟩⟩
    rfl

/-- Global sections are full on abelian sheaves on `(Spec Ω)_étale`. -/
instance : ((sheafSections (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u + 1}).obj
    (op (terminal Ω))).Full :=
  (sectionsFullyFaithful Ω).full

/-- Global sections are faithful on abelian sheaves on `(Spec Ω)_étale`. -/
instance : ((sheafSections (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u + 1}).obj
    (op (terminal Ω))).Faithful :=
  (sectionsFullyFaithful Ω).faithful

/-- **Every abelian sheaf on the small étale site of the spectrum of a separably closed field is
constant**: the counit `Γ(F) ⟶ F` of the adjunction between the constant sheaf functor and global
sections is an isomorphism. -/
instance isIso_counit_app (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u + 1}) :
    IsIso ((constantSheafAdj (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u + 1}
      (terminalIsTerminal Ω)).counit.app F) :=
  inferInstance

end SepClosedField

end Stacks.EtaleCohomology

end
