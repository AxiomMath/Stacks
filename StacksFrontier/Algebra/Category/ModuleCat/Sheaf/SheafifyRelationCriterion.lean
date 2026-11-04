module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitRelations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations
import StacksCore.Tactic.StacksAttribute

/-!
# The local equational criterion passes to a sheafification

`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitRelations` states the local
equational criterion of Stacks 08FC part (2) for a *presheaf* of modules over a presheaf of
rings (`Stacks.ModuleUp.HasLocalRelationFactorizations`) and shows that the presheaf-level
pullback `u_p` of Stacks 00VC transports it.  The proof of Stacks 05VD needs the criterion for
`f^{-1}F = (u_p F)^#` over `f^{-1}O = (u_p O)^#`, i.e. after sheafifying both the ring and the
module.  This file supplies that step, in the generality in which Mathlib's sheafification of a
presheaf of modules is stated: a locally bijective map `α : R₀ ⟶ R.obj` of presheaves of rings
and a locally bijective map `φ : M₀.presheaf ⟶ A.obj` of presheaves of abelian groups.

The argument is the one the source performs with the words "after replacing `U` by the members
of a covering": a relation among sections of the sheafification is pulled back to a covering on
which all `2n` sections lift, then to a further covering on which the lifted relation already
holds in `M₀`, and the presheaf criterion is applied there.  Three successive coverings are
composed with `CategoryTheory.GrothendieckTopology.transitive`.

## Main definitions

* `Stacks.ModuleUp.relationSieve`: the sieve of arrows along which a given relation admits a
  finite-free factorisation of the sections annihilating it.  Its only purpose is to turn the
  existential `Stacks.ModuleUp.LocallyFactorsRelation` into a *membership* statement, which is
  what the transitivity axiom of a Grothendieck topology consumes.
* `Stacks.ModuleUp.toSheafifyApp`: the sheafification unit on sections, with its result type
  ascribed at the sheafified module rather than at the target presheaf of abelian groups.

## Main results

* `Stacks.ModuleUp.locallyFactorsRelation_iff_relationSieve_mem`: the local factorisation
  property of a relation holds iff `relationSieve` is a covering sieve.
* `Stacks.ModuleUp.exists_covering_lift_family`: **finitely many sections lift simultaneously**
  on a covering sieve, along a locally surjective morphism of presheaves with values in any
  concrete category.  This is the "fusion" step; it is used once for the ring and once for the
  module.
* `Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify`: **the criterion passes to the
  sheafification.**
* `Stacks.ModuleUp.hasLocalSingleRelationFactorizations_of_presheaf`: the converse
  repackaging to `Stacks.ModuleUp.hasLocalRelationFactorizations_of_sheaf`, reading the
  presheaf-level criterion as part (2) of Stacks 08FC for a sheaf of modules over a sheaf of
  commutative rings.

## Implementation notes

**Why `relationSieve` has to exist.** `LocallyFactorsRelation` is an existential over covering
sieves, while `GrothendieckTopology.transitive` needs one fixed sieve whose pullbacks are
covering.  The sieve of *all* arrows along which the factorisation exists is the universal
choice, and it is a sieve because the factorisation data restricts; that is the content of its
`downward_closed` field.

**Why `toSheafifyApp` is a `def` with an ascribed type.** `φ.app X` has codomain
`A.obj.obj X`, which is the carrier of `(PresheafOfModules.sheafify α φ).val.obj X` but is not a
spelling at which the `Module (R.obj.obj X)` instance is found, so `α.app X a • φ.app X m` does
not elaborate.  A type *ascription* does not help; a `def` with a declared result type does.
This is the discipline of `SiteUpColimitRelations`, applied to one further boundary.

**No reassociation is needed.** The three coverings compose along `h' ≫ g ≫ f`, and
`(h' ≫ g ≫ f).op = (f.op ≫ g.op) ≫ h'.op` by `rfl`, so the two applications of
`sectionRestrict_trans` fire without an intervening `Category.assoc`.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
-/

@[expose] public section

open CategoryTheory Opposite

universe w

namespace Stacks.ModuleUp

/-! ### Restriction of the factorisation data, and the sieve it cuts out -/

section RelationSieve

variable {C : Type w} [SmallCategory C] (O : Cᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)

/-- Functoriality of a presheaf of rings, applied to a section. -/
theorem presheafMap_comp_apply {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : O.obj X) :
    O.map (f ≫ g) x = O.map g (O.map f x) :=
  (ConcreteCategory.congr_hom (O.map_comp f g) x).trans
    (ConcreteCategory.comp_apply (O.map f) (O.map g) x)

/-- Functoriality of `Stacks.ModuleUp.sectionRestrict`. -/
theorem sectionRestrict_trans {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (m : G.obj X) :
    sectionRestrict O G (f ≫ g) m = sectionRestrict O G g (sectionRestrict O G f m) :=
  (ConcreteCategory.congr_hom ((underlyingAb O G).map_comp f g) m).trans
    (ConcreteCategory.comp_apply ((underlyingAb O G).map f) ((underlyingAb O G).map g) m)

/-- Restriction maps the zero section to zero. -/
theorem sectionRestrict_eq_zero {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    sectionRestrict O G f (0 : G.obj X) = 0 :=
  map_zero ((underlyingAb O G).map f).hom

/-- Restriction of a relation: a linear combination restricts to the linear combination of the
restrictions. -/
theorem sectionRestrict_sum_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) {n : ℕ}
    (a : Fin n → O.obj X) (m : Fin n → G.obj X) :
    sectionRestrict O G f (∑ i : Fin n, a i • m i)
      = ∑ i : Fin n, O.map f (a i) • sectionRestrict O G f (m i) := by
  rw [sectionRestrict_sum]
  exact Finset.sum_congr rfl fun i _ => sectionRestrict_smul O G f (a i) (m i)

/-- The sieve of arrows `g : V ⟶ U` along which the relation recorded by `a` among the sections
`s` admits a finite-free factorisation of `s` by a matrix annihilating `a`.

`Stacks.ModuleUp.LocallyFactorsRelation` says that *some* covering sieve consists of such
arrows; by `Stacks.ModuleUp.locallyFactorsRelation_iff_relationSieve_mem` that is the same as
this one being covering. -/
def relationSieve (U : C) {n : ℕ}
    (a : Fin n → O.obj (op U)) (s : Fin n → G.obj (op U)) : Sieve U where
  arrows V g := ∃ (l : ℕ) (t : Fin l → G.obj (op V)) (B : Fin l → Fin n → O.obj (op V)),
    (∀ i, sectionRestrict O G g.op (s i) = ∑ k : Fin l, B k i • t k) ∧
    (∀ k, ∑ i : Fin n, B k i * O.map g.op (a i) = 0)
  downward_closed := by
    rintro V W g ⟨l, t, B, h1, h2⟩ h
    refine ⟨l, fun k => sectionRestrict O G h.op (t k), fun k i => O.map h.op (B k i), ?_, ?_⟩
    · intro i
      rw [show (h ≫ g).op = g.op ≫ h.op from rfl, sectionRestrict_trans, h1 i,
        sectionRestrict_sum]
      exact Finset.sum_congr rfl fun k _ => sectionRestrict_smul O G h.op (B k i) (t k)
    · intro k
      have e : ∑ i : Fin n, O.map h.op (B k i) * O.map (h ≫ g).op (a i)
          = O.map h.op (∑ i : Fin n, B k i * O.map g.op (a i)) := by
        rw [map_sum (O.map h.op).hom]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul (O.map h.op).hom,
          show (h ≫ g).op = g.op ≫ h.op from rfl, presheafMap_comp_apply]
      rw [e, h2 k, map_zero]

variable {K : GrothendieckTopology C}

/-- A relation factors locally exactly when the arrows along which it factors form a covering
sieve. -/
theorem locallyFactorsRelation_iff_relationSieve_mem (U : C) {n : ℕ}
    (a : Fin n → O.obj (op U)) (s : Fin n → G.obj (op U)) :
    LocallyFactorsRelation K O G U a s ↔ relationSieve O G U a s ∈ K U := by
  refine ⟨fun h => ?_, fun h => ⟨relationSieve O G U a s, h, ?_⟩⟩
  · obtain ⟨T, hT, hfac⟩ := h
    refine K.superset_covering ?_ hT
    intro V g hg
    exact hfac g hg
  · intro V g hg
    exact hg

end RelationSieve

/-! ### Simultaneous local lifting of a finite family of sections -/

section Lift

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {A : Type*} [Category.{w} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]

/-- **Finitely many sections lift simultaneously on a covering sieve.**

Along a locally surjective morphism `f : F ⟶ G` of presheaves with values in a concrete
category, a finite family of sections of `G` over `U` admits a covering sieve of `U` each member
of which lifts *all* of them.  This is the step the source performs by replacing `U` by the
members of a covering; the fusion over the family is a finite intersection of the individual
image sieves. -/
theorem exists_covering_lift_family {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    [Presheaf.IsLocallySurjective J f] {U : C} {n : ℕ} (s : Fin n → ToType (G.obj (op U))) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
      ∃ t : Fin n → ToType (F.obj (op V)), ∀ i, f.app _ (t i) = G.map g.op (s i) := by
  induction n with
  | zero => exact ⟨⊤, J.top_mem U, fun V g _ => ⟨Fin.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
      obtain ⟨S, hS, hlift⟩ := ih (fun i => s i.succ)
      refine ⟨Presheaf.imageSieve f (s 0) ⊓ S,
        J.intersection_covering (Presheaf.imageSieve_mem J f (s 0)) hS, ?_⟩
      intro V g hg
      obtain ⟨t, ht⟩ := hlift g hg.2
      exact ⟨Fin.cases (Presheaf.localPreimage f (s 0) g hg.1) t,
        Fin.cases (Presheaf.app_localPreimage f (s 0) g hg.1) ht⟩

end Lift

/-! ### The criterion passes to the sheafification -/

section Sheafify

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  {M₀ : PresheafOfModules.{w} R₀} {A : Sheaf J AddCommGrpCat.{w}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

/-- The sheafification unit on sections, **at the result type of the sheafified module**.

This is `φ.app X`, recorded by `toSheafifyApp_eq` as a `rfl`; the `def` exists for its declared
result type, at which the scalar action of `R.obj.obj X` is found. -/
noncomputable def toSheafifyApp (X : Cᵒᵖ) (m : M₀.obj X) :
    (PresheafOfModules.sheafify α φ).val.obj X :=
  φ.app X m

/-- `Stacks.ModuleUp.toSheafifyApp α φ X` is `φ.app X`. -/
theorem toSheafifyApp_eq (X : Cᵒᵖ) (m : M₀.obj X) : toSheafifyApp α φ X m = φ.app X m := rfl

/-- The sheafification unit is semilinear over `α`. -/
theorem toSheafifyApp_smul (X : Cᵒᵖ) (a : R₀.obj X) (m : M₀.obj X) :
    toSheafifyApp α φ X (a • m) = α.app X a • toSheafifyApp α φ X m :=
  ((PresheafOfModules.toSheafify α φ).app X).hom.map_smul a m

/-- The sheafification unit on sections commutes with finite sums. -/
theorem toSheafifyApp_sum {X : Cᵒᵖ} {n : ℕ} (m : Fin n → M₀.obj X) :
    toSheafifyApp α φ X (∑ i, m i) = ∑ i, toSheafifyApp α φ X (m i) :=
  map_sum (φ.app X).hom _ _

/-- The sheafification unit commutes with restriction. -/
theorem toSheafifyApp_restrict {X Y : Cᵒᵖ} (g : X ⟶ Y) (m : M₀.obj X) :
    toSheafifyApp α φ Y (sectionRestrict R₀ M₀ g m)
      = sectionRestrict R.obj (PresheafOfModules.sheafify α φ).val g (toSheafifyApp α φ X m) :=
  NatTrans.naturality_apply φ g m

omit [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] in
/-- Naturality of the sheafification unit of the structure ring, on sections. -/
theorem ringUnitApp_naturality {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : R₀.obj X) :
    α.app Y (R₀.map g a) = R.obj.map g (α.app X a) :=
  NatTrans.naturality_apply α g a

/-- `Stacks.ModuleUp.exists_covering_lift_family` for the sheafification unit of a presheaf of
modules, **with the lifts typed at `M₀` and the restrictions at the sheafified module**.

The restatement is forced: `exists_covering_lift_family` produces lifts at the spelling
`M₀.presheaf.obj (op V)` and restrictions at `A.obj.map`, and while both are definitionally the
spellings used here, a goal mixing them is not type-correct at `implicit` transparency, so `rw`
refuses it.  The proof is the general lemma read through `exact`, which is defeq-tolerant. -/
theorem exists_covering_lift_family_sheafify {U : C} {n : ℕ}
    (s : Fin n → (PresheafOfModules.sheafify α φ).val.obj (op U)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
      ∃ t : Fin n → M₀.obj (op V), ∀ i, toSheafifyApp α φ (op V) (t i)
        = sectionRestrict R.obj (PresheafOfModules.sheafify α φ).val g.op (s i) :=
  exists_covering_lift_family J φ s

/-- **The local equational criterion of Stacks 08FC part (2) passes to the sheafification.**

If every single relation among sections of the presheaf of modules `M₀` over the presheaf of
rings `R₀` factors locally through a finite free module by a matrix annihilating it, then the
same holds for the sheafification `PresheafOfModules.sheafify α φ` over the sheaf of rings `R`.

The three coverings of the source's "after replacing `U` by the members of a covering" are
composed here: `exists_covering_lift_family` lifts the `2n` sections, local injectivity of `φ`
makes the lifted relation hold in `M₀`, and the hypothesis is applied at that stage. -/
theorem hasLocalRelationFactorizations_sheafify
    (h : HasLocalRelationFactorizations J R₀ M₀) :
    HasLocalRelationFactorizations J R.obj (PresheafOfModules.sheafify α φ).val := by
  intro U n a s hrel
  rw [locallyFactorsRelation_iff_relationSieve_mem]
  obtain ⟨S₁, hS₁, hlift₁⟩ := exists_covering_lift_family J α a
  obtain ⟨S₂, hS₂, hlift₂⟩ := exists_covering_lift_family_sheafify α φ s
  refine J.transitive (J.intersection_covering hS₁ hS₂) _ ?_
  intro V f hf
  obtain ⟨a', ha'⟩ := hlift₁ f hf.1
  obtain ⟨s', hs'⟩ := hlift₂ f hf.2
  have key : ∀ i : Fin n, toSheafifyApp α φ (op V) (a' i • s' i)
      = R.obj.map f.op (a i) •
        sectionRestrict R.obj (PresheafOfModules.sheafify α φ).val f.op (s i) := fun i => by
    rw [toSheafifyApp_smul α φ (op V) (a' i) (s' i), ha' i, hs' i]
  have h0 : toSheafifyApp α φ (op V) (∑ i : Fin n, a' i • s' i) = 0 :=
    calc toSheafifyApp α φ (op V) (∑ i : Fin n, a' i • s' i)
        = ∑ i : Fin n, toSheafifyApp α φ (op V) (a' i • s' i) :=
          toSheafifyApp_sum α φ _
      _ = ∑ i : Fin n, R.obj.map f.op (a i) •
            sectionRestrict R.obj (PresheafOfModules.sheafify α φ).val f.op (s i) :=
          Finset.sum_congr rfl fun i _ => key i
      _ = sectionRestrict R.obj (PresheafOfModules.sheafify α φ).val f.op
            (∑ i : Fin n, a i • s i) :=
          (sectionRestrict_sum_smul R.obj _ f.op a s).symm
      _ = 0 := by rw [hrel, sectionRestrict_eq_zero]
  have hvanish : φ.app (op V) (∑ i : Fin n, a' i • s' i)
      = φ.app (op V) (0 : M₀.obj (op V)) :=
    h0.trans (map_zero (φ.app (op V)).hom).symm
  refine J.transitive (Presheaf.equalizerSieve_mem J φ _ _ hvanish) _ ?_
  intro W g hg
  have hg' : ∑ i : Fin n, R₀.map g.op (a' i) • sectionRestrict R₀ M₀ g.op (s' i) = 0 :=
    (sectionRestrict_sum_smul R₀ M₀ g.op (fun i => a' i) (fun i => s' i)).symm.trans
      (hg.trans (map_zero (M₀.presheaf.map g.op).hom))
  obtain ⟨T, hT, hfac⟩ := h W n (fun i => R₀.map g.op (a' i))
    (fun i => sectionRestrict R₀ M₀ g.op (s' i)) hg'
  rw [← Sieve.pullback_comp]
  refine J.superset_covering ?_ hT
  intro W' h' hh'
  obtain ⟨l, t₀, B₀, hB1, hB2⟩ := hfac h' hh'
  refine ⟨l, fun k => toSheafifyApp α φ (op W') (t₀ k),
    fun k i => α.app (op W') (B₀ k i), ?_, ?_⟩
  · intro i
    rw [show (h' ≫ g ≫ f).op = (f.op ≫ g.op) ≫ h'.op from rfl,
      sectionRestrict_trans, sectionRestrict_trans, ← hs' i,
      ← toSheafifyApp_restrict α φ g.op (s' i),
      ← toSheafifyApp_restrict α φ h'.op (sectionRestrict R₀ M₀ g.op (s' i)),
      hB1 i, toSheafifyApp_sum]
    exact Finset.sum_congr rfl fun k _ => toSheafifyApp_smul α φ (op W') (B₀ k i) (t₀ k)
  · intro k
    have hai : ∀ i : Fin n, R.obj.map (h' ≫ g ≫ f).op (a i)
        = α.app (op W') (R₀.map h'.op (R₀.map g.op (a' i))) := fun i => by
      rw [show (h' ≫ g ≫ f).op = (f.op ≫ g.op) ≫ h'.op from rfl,
        presheafMap_comp_apply, presheafMap_comp_apply, ← ha' i,
        ringUnitApp_naturality, ringUnitApp_naturality]
    rw [← map_zero (α.app (op W')).hom, ← hB2 k]
    simp only [map_sum, map_mul, hai]

end Sheafify

/-! ### Reading the presheaf-level criterion as part (2) of Stacks 08FC -/

section OfPresheaf

variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  {O : Sheaf J CommRingCat.{w}} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The presheaf-level local equational criterion gives the sheaf-level one** of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`.

This is the converse of `Stacks.ModuleUp.hasLocalRelationFactorizations_of_sheaf`: the two
statements are the same condition read at two spellings, and this direction is what lets the
output of `Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify` be fed to
`Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations`. -/
theorem hasLocalSingleRelationFactorizations_of_presheaf
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O))
    (hF : HasLocalRelationFactorizations J (Stacks.commRingSheafToRingSheaf O).obj F.val) :
    Stacks.SheafOfModules.HasLocalSingleRelationFactorizations O F := by
  intro U n a s hrel
  obtain ⟨S, hS, hfac⟩ := hF U n a s hrel
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨l, t, B, h1, h2⟩ := hfac f hf
  exact ⟨l, t, B, fun i => h1 i, fun k _ => h2 k⟩

end OfPresheaf

end Stacks.ModuleUp

end
