module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PseudoTorsors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules

/-!
# Isomorphism classes of torsors under a sheaf of groups

Let `(C, J)` be a site and let `G` be a sheaf of (possibly non-commutative) groups on it. The
first cohomology `H¹(C, G)` of `G` is the set of isomorphism classes of `G`-torsors (Stacks,
Cohomology on Sites, Section 21.4): two `G`-torsors are identified when there is a
`G`-equivariant isomorphism of sheaves between them. For an abelian sheaf this is the set which
Stacks 03AJ identifies with the first cohomology group.

Every morphism of `G`-torsors is an isomorphism, so two torsors define the same class as soon as
there is any equivariant morphism between them.

## Main definitions

* `SheafOfGroups.torsorSetoid`: equivariant isomorphism of `G`-torsors, as a setoid.
* `SheafOfGroups.TorsorClasses`: the set `H¹(C, G)` of isomorphism classes of `G`-torsors.

## Main results

* `PseudoTorsor.Hom.bijective_app_of_nonempty`: a morphism of pseudo-torsors is bijective on the
  sections over an object over which its source has a section.
* `PseudoTorsor.Hom.isIso_of_isTorsor`: every morphism out of a torsor is an isomorphism.
* `SheafOfGroups.TorsorClasses.mk_eq_mk_of_hom`: an equivariant morphism between two torsors
  identifies their classes.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 03AG](https://stacks.math.columbia.edu/tag/03AG)
-/

@[expose] public section

open CategoryTheory Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace PseudoTorsor

variable {G : SheafOfGroups.{w} J}

/-- A morphism of pseudo-torsors is bijective on the sections over an object over which its
source has a section. -/
theorem Hom.bijective_app_of_nonempty {F F' : PseudoTorsor.{t} G} (e : F.Hom F') (U : Cᵒᵖ)
    (s₀ : F.presheaf.obj U) : Function.Bijective (e.hom.app U) := by
  refine ⟨fun s s' h => ?_, fun s' => ?_⟩
  · obtain ⟨a, ha, _⟩ := F.simplyTransitive U ⟨s⟩ s s'
    have hg : F'.act U a (e.hom.app U s) = e.hom.app U s :=
      (e.map_act U a s).symm.trans ((congrArg (e.hom.app U) ha).trans h.symm)
    have ha1 : a = 1 := (F'.simplyTransitive U ⟨e.hom.app U s⟩
      (e.hom.app U s) (e.hom.app U s)).unique hg (F'.one_act U _)
    simpa only [ha1, F.one_act] using ha
  · obtain ⟨a, ha, _⟩ := F'.simplyTransitive U ⟨e.hom.app U s₀⟩ (e.hom.app U s₀) s'
    exact ⟨F.act U a s₀, (e.map_act U a s₀).trans ha⟩

/-- Every morphism out of a torsor is an isomorphism: it is bijective on the sections over the
members of a covering over which the source has sections, hence everywhere. -/
theorem Hom.isIso_of_isTorsor {F F' : PseudoTorsor.{t} G} (hF : F.IsTorsor) (e : F.Hom F') :
    e.IsIso := by
  change CategoryTheory.IsIso e.hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  apply (isIso_iff_bijective _).2
  obtain ⟨S, hS, hs⟩ := hF U.unop
  exact Stacks.Cohomology.Torsors.Generators.bijective_of_bijective_on_cover J F.isSheaf
    F'.isSheaf S hS e.hom
    fun V f hf => by
      obtain ⟨s⟩ := hs hf
      exact e.bijective_app_of_nonempty (op V) s

/-- The identity morphism of a pseudo-torsor. -/
def Hom.id (F : PseudoTorsor.{t} G) : F.Hom F where
  hom := 𝟙 _
  map_act _ _ _ := rfl

/-- The composite of two morphisms of pseudo-torsors. -/
def Hom.comp {F F' F'' : PseudoTorsor.{t} G} (e : F.Hom F') (e' : F'.Hom F'') : F.Hom F'' where
  hom := e.hom ≫ e'.hom
  map_act U g s := by
    simp only [NatTrans.comp_app, types_comp_apply, e.map_act, e'.map_act]

/-- The inverse of an isomorphism of pseudo-torsors. -/
noncomputable def Hom.inv {F F' : PseudoTorsor.{t} G} (e : F.Hom F') (he : e.IsIso) :
    F'.Hom F :=
  haveI : CategoryTheory.IsIso e.hom := he
  { hom := CategoryTheory.inv e.hom
    map_act := fun U g s => by
      apply (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1
      rw [e.map_act]
      simp }

end PseudoTorsor

namespace SheafOfGroups

variable (G : SheafOfGroups.{w} J)

/-- Equivariant isomorphism of `G`-torsors, as an equivalence relation: two torsors are related
when there is a morphism of pseudo-torsors between them whose underlying morphism of sheaves is an
isomorphism. -/
def torsorSetoid : Setoid {F : PseudoTorsor.{t} G // F.IsTorsor} where
  r F F' := ∃ e : F.1.Hom F'.1, e.IsIso
  iseqv :=
    { refl := fun F => ⟨PseudoTorsor.Hom.id F.1, inferInstanceAs (IsIso (𝟙 _))⟩
      symm := fun {F F'} ⟨e, he⟩ => ⟨e.inv he, by
        have : IsIso e.hom := he
        change IsIso (CategoryTheory.inv e.hom)
        infer_instance⟩
      trans := fun {F F' F''} ⟨e, he⟩ ⟨e', he'⟩ => ⟨e.comp e', by
        have : IsIso e.hom := he
        have : IsIso e'.hom := he'
        exact inferInstanceAs (IsIso (e.hom ≫ e'.hom))⟩ }

/-- **The first cohomology of a sheaf of groups.** The set `H¹(C, G)` of isomorphism classes of
`G`-torsors, the torsors having their sections in the universe `t`. -/
def TorsorClasses : Type _ :=
  Quotient (torsorSetoid.{t} G)

variable {G}

/-- The class of a `G`-torsor in `H¹(C, G)`. -/
def TorsorClasses.mk (F : PseudoTorsor.{t} G) (hF : F.IsTorsor) : TorsorClasses.{t} G :=
  Quotient.mk _ ⟨F, hF⟩

/-- Every element of `H¹(C, G)` is the class of a torsor. -/
theorem TorsorClasses.mk_surjective (c : TorsorClasses.{t} G) :
    ∃ (F : PseudoTorsor.{t} G) (hF : F.IsTorsor), TorsorClasses.mk F hF = c := by
  obtain ⟨⟨F, hF⟩, rfl⟩ := Quotient.exists_rep c
  exact ⟨F, hF, rfl⟩

/-- Two torsors have the same class exactly when they are equivariantly isomorphic. -/
theorem TorsorClasses.mk_eq_mk_iff {F F' : PseudoTorsor.{t} G} (hF : F.IsTorsor)
    (hF' : F'.IsTorsor) :
    TorsorClasses.mk F hF = TorsorClasses.mk F' hF' ↔ ∃ e : F.Hom F', e.IsIso :=
  Quotient.eq (r := torsorSetoid G)

/-- An equivariant morphism between two torsors identifies their classes: it is an isomorphism
by `PseudoTorsor.Hom.isIso_of_isTorsor`. -/
theorem TorsorClasses.mk_eq_mk_of_hom {F F' : PseudoTorsor.{t} G} (hF : F.IsTorsor)
    (hF' : F'.IsTorsor) (e : F.Hom F') : TorsorClasses.mk F hF = TorsorClasses.mk F' hF' :=
  (TorsorClasses.mk_eq_mk_iff hF hF').2 ⟨e, e.isIso_of_isTorsor hF⟩

end SheafOfGroups
