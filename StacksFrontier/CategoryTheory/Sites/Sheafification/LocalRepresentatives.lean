module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local representatives for sections of a sheafification

Let `(C, J)` be a site. The unit `P ⟶ P^#` of sheafification is locally surjective: every
section of `P^#` over `U` is, locally on `U`, the image of a section of `P`. Mathlib knows this
when the target category satisfies `J.WEqualsLocallyBijective`, or — for set-valued presheaves —
when the sections live in the universe `max u v` fixed by the site. Neither hypothesis is
available when the carrier universe is unrelated to the site, which is the situation in which
constant sheaves on a large site are used, so the two instances are reproved here with
`HasWeakSheafify` as the only hypothesis.

The argument is the usual one, run inside the presheaf category rather than through
sheafification in `Type`: the sections which are locally in the image of `φ : P ⟶ Q` form a
subpresheaf `R ⊆ Q` (a subgroup in each degree, in the abelian case), `R` is a sheaf as soon as
`Q` is, and `P ⟶ R` extends over the sheafification by the universal property. That extension
splits the inclusion `R ⟶ Q`, so `R` is all of `Q` — which says exactly that every section of
`Q` is locally in the image.

From local surjectivity one gets simultaneous representatives for a *finite* tuple of sections:
a finite intersection of covering sieves is covering, so finitely many sections can be
represented over one covering family, and the family may be shrunk to its members that are not
sheaf-theoretically empty without losing the covering property.

## Main results

* `Stacks.Sheafification.isLocallySurjective_toSheafify_addCommGrp` and
  `Stacks.Sheafification.isLocallySurjective_toSheafify_type`: the sheafification unit is
  locally surjective, for abelian-group-valued and set-valued presheaves respectively, with no
  relation assumed between the carrier universe and the site.
* `Stacks.Sheafification.exists_cover_representatives`: finitely many sections of the target of
  a locally surjective morphism have simultaneous representatives on a covering family none of
  whose members is sheaf-theoretically empty.
* `Stacks.Sheafification.exists_cover_constant_representatives`: the case of the constant sheaf
  on a set `B`, where the representatives are elements of `B`.
* `Stacks.Sheafification.constantSection_injective_of_nonempty`: over an object whose
  localization is nonempty, distinct elements of `B` give distinct sections of the constant
  sheaf.

## Implementation notes

"Sheaf-theoretically empty" is spelled `(⊥ : Sieve V) ∈ J V`, the empty sieve being a covering
sieve. This avoids assuming the site small, which a characterisation through the localized topos
being trivial would require.

The conclusion is a covering *family* `V i ⟶ U` rather than a covering sieve: a sieve on an
object that is not sheaf-theoretically empty may still contain arrows whose source is, so the
emptiness condition cannot be imposed on a sieve.

`Stacks.Sheafification.exists_cover_representatives` is stated for an arbitrary concrete
category whose carrier universe is independent of the site, so that it applies to both of the
instances above.

## References

* [Stacks Project, Tag 00WK](https://stacks.math.columbia.edu/tag/00WK)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology hiding sheafify toSheafify
open Opposite

namespace Stacks.Sheafification

universe v u w v' u' t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A finite intersection of covering sieves is a covering sieve. -/
@[sga "4 II 1.1.1"]
lemma finsetInf_covering {U : C} {ι : Type*}
    (t : Finset ι) (S : ι → Sieve U) (hS : ∀ i, S i ∈ J U) :
    (t.inf S) ∈ J U := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hS i) ih

section LocallySurjective

/-- Images of sections of `P` under `φ : P ⟶ Q` are covered by the top sieve. -/
private lemma imageSieve_app_mem {P Q : Cᵒᵖ ⥤ Ab.{w}} (φ : P ⟶ Q) {X : Cᵒᵖ} (a : P.obj X) :
    Presheaf.imageSieve φ (φ.app X a) ∈ J X.unop := by
  rw [Presheaf.imageSieve_app]
  exact J.top_mem _

/-- The sections of `Q` which are locally in the image of `φ : P ⟶ Q` form a subgroup in each
degree. -/
private def localImageSubgroup {P Q : Cᵒᵖ ⥤ Ab.{w}} (φ : P ⟶ Q) (X : Cᵒᵖ) :
    AddSubgroup (Q.obj X) where
  carrier := {s | Presheaf.imageSieve φ s ∈ J X.unop}
  zero_mem' := by
    simpa using imageSieve_app_mem J φ (0 : P.obj X)
  add_mem' := by
    intro s t hs ht
    apply J.superset_covering _ (J.intersection_covering hs ht)
    rintro Y f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a + b, by simp only [map_add, ha, hb]⟩
  neg_mem' := by
    intro s hs
    apply J.superset_covering _ hs
    rintro Y f ⟨a, ha⟩
    exact ⟨-a, by simp only [map_neg, ha]⟩

/-- The subpresheaf of sections locally in the image of `φ : P ⟶ Q`. -/
private def localImage {P Q : Cᵒᵖ ⥤ Ab.{w}} (φ : P ⟶ Q) : Cᵒᵖ ⥤ Ab.{w} where
  obj X := AddCommGrpCat.of (localImageSubgroup J φ X)
  map {X Y} f := AddCommGrpCat.ofHom
    ((Q.map f).hom.restrict (by
      intro s hs
      change Presheaf.imageSieve φ (Q.map f s) ∈ J Y.unop
      rw [← Presheaf.pullback_imageSieve]
      exact J.pullback_stable f.unop hs))
  map_id X := by
    ext x
    change Q.map (𝟙 X) x.val = x.val
    simp
  map_comp f g := by
    ext x
    change Q.map (f ≫ g) x.val = Q.map g (Q.map f x.val)
    simp

/-- The inclusion of the subpresheaf of sections locally in the image. -/
private def localImageι {P Q : Cᵒᵖ ⥤ Ab.{w}} (φ : P ⟶ Q) : localImage J φ ⟶ Q where
  app X := AddCommGrpCat.ofHom (localImageSubgroup J φ X).subtype

/-- The factorization of `φ` through the sections locally in its image. -/
private def toLocalImage {P Q : Cᵒᵖ ⥤ Ab.{w}} (φ : P ⟶ Q) : P ⟶ localImage J φ where
  app X := AddCommGrpCat.ofHom
    ((φ.app X).hom.codRestrict (localImageSubgroup J φ X) (imageSieve_app_mem J φ))
  naturality X Y f := by
    ext s
    exact Subtype.ext (NatTrans.naturality_apply φ f s)

private lemma localImage_isSheaf {P Q : Cᵒᵖ ⥤ Ab.{w}} (φ : P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) : Presheaf.IsSheaf J (localImage J φ) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget Ab)
  change Presheaf.IsSheaf J
    (((Subfunctor.range (Functor.whiskerRight φ (forget Ab))).sheafify J).toFunctor)
  rw [isSheaf_iff_isSheaf_of_type]
  apply Subfunctor.sheafify_isSheaf
  rw [← isSheaf_iff_isSheaf_of_type]
  exact HasSheafCompose.isSheaf (F := forget Ab) Q hQ

/-- Sheafification of abelian presheaves is locally surjective, independently of the
universe of the underlying groups. No set-valued sheafification is needed. -/
instance isLocallySurjective_toSheafify_addCommGrp [HasWeakSheafify J Ab.{w}]
    (P : Cᵒᵖ ⥤ Ab.{w}) : Presheaf.IsLocallySurjective J (toSheafify J P) where
  imageSieve_mem {U} s := by
    let φ := toSheafify J P
    have hR : Presheaf.IsSheaf J (localImage J φ) :=
      localImage_isSheaf J φ ((presheafToSheaf J Ab).obj P).property
    let l := CategoryTheory.sheafifyLift J (toLocalImage J φ) hR
    have hl : l ≫ localImageι J φ = 𝟙 _ := by
      refine CategoryTheory.sheafify_hom_ext J _ _ ((presheafToSheaf J Ab).obj P).property ?_
      rw [← Category.assoc, CategoryTheory.toSheafify_sheafifyLift]
      ext X x
      rfl
    have he : (l.app (op U) s).val = s :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hl (op U)) s
    rw [← he]
    exact (l.app (op U) s).property

/-- Set-valued sheafification is locally surjective in any carrier universe in which
weak sheafification exists. -/
instance isLocallySurjective_toSheafify_type [HasWeakSheafify J (Type w)]
    (P : Cᵒᵖ ⥤ Type w) : Presheaf.IsLocallySurjective J (toSheafify J P) where
  imageSieve_mem {U} s := by
    let φ := toSheafify J P
    let R := (Subfunctor.range φ).sheafify J
    have hR : Presheaf.IsSheaf J R.toFunctor := by
      rw [isSheaf_iff_isSheaf_of_type]
      exact Subfunctor.sheafify_isSheaf _
        ((isSheaf_iff_isSheaf_of_type J _).mp ((presheafToSheaf J (Type w)).obj P).property)
    let l := CategoryTheory.sheafifyLift J (Subfunctor.toRangeSheafify J φ) hR
    have hl : l ≫ R.ι = 𝟙 _ := by
      refine CategoryTheory.sheafify_hom_ext J _ _ ((presheafToSheaf J (Type w)).obj P).property ?_
      rw [← Category.assoc, CategoryTheory.toSheafify_sheafifyLift]
      ext X x
      rfl
    have he : (l.app (op U) s).val = s :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hl (op U)) s
    rw [← he]
    exact (l.app (op U) s).property

end LocallySurjective

/-- Finitely many sections of the target of a locally surjective morphism have
simultaneous representatives on a cover with no sheaf-theoretically empty members.
In particular this applies to sheafification of sets or abelian groups in any universe. -/
lemma exists_cover_representatives
    {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type t}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{t} D FD]
    {P Q : Cᵒᵖ ⥤ D} (φ : P ⟶ Q) [Presheaf.IsLocallySurjective J φ] (U : C)
    {r : ℕ} (s : Fin r → ToType (Q.obj (op U))) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
        ∀ i, (¬ (⊥ : Sieve (V i)) ∈ J (V i)) ∧
          ∀ j, ∃ b : ToType (P.obj (op (V i))),
            Q.map (f i).op (s j) =
              φ.app (op (V i)) b := by
  classical
  let S₀ : Fin r → Sieve U := fun j => Presheaf.imageSieve φ (s j)
  have hS₀ : ∀ j, S₀ j ∈ J U := fun j =>
    Presheaf.imageSieve_mem (J := J) (f := φ) (s := s j)
  let S := Finset.univ.inf S₀
  have hS : S ∈ J U :=
    finsetInf_covering J Finset.univ S₀ hS₀
  let K : J.Cover U := ⟨S, hS⟩
  let I : Type (max u v) := {a : K.Arrow // ¬ (⊥ : Sieve a.Y) ∈ J a.Y}
  let V : I → C := fun i => i.val.Y
  let f : ∀ i, V i ⟶ U := fun i => i.val.f
  let T : Sieve U := Sieve.ofArrows V f
  have hT : T ∈ J U := by
    apply J.transitive hS T
    intro Y g hg
    by_cases hempty : (⊥ : Sieve Y) ∈ J Y
    · exact J.superset_covering bot_le hempty
    · rw [Sieve.pullback_eq_top_of_mem T (Sieve.ofArrows_mk V f ⟨⟨Y, g, hg⟩, hempty⟩)]
      exact J.top_mem Y
  refine ⟨I, V, f, hT, fun i => ⟨i.property, fun j => ?_⟩⟩
  obtain ⟨b, hb⟩ : S₀ j (f i) :=
    (Finset.inf_le (Finset.mem_univ j) : Finset.univ.inf S₀ ≤ S₀ j) (Y := V i) (f i) i.val.hf
  exact ⟨b, hb.symm⟩

/-- Finitely many sections of a constant sheaf admit simultaneous constant descriptions
on a covering family with no sheaf-theoretically empty members. -/
lemma exists_cover_constant_representatives (B : Type w) [HasWeakSheafify J (Type w)] (U : C)
    {r : ℕ} (s : Fin r → (sheafify J ((Functor.const Cᵒᵖ).obj B)).obj (op U)) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
        ∀ i, (¬ (⊥ : Sieve (V i)) ∈ J (V i)) ∧
          ∀ j, ∃ b : B,
            (sheafify J ((Functor.const Cᵒᵖ).obj B)).map (f i).op (s j) =
              (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op (V i)) b :=
  exists_cover_representatives J (toSheafify J ((Functor.const Cᵒᵖ).obj B)) U s

/-- Over an object with nonempty localization, the canonical map from a set to sections
of its constant sheaf is injective. -/
lemma constantSection_injective_of_nonempty [HasWeakSheafify J (Type (max u v))]
    (B : Type (max u v)) (U : C)
    (hU : ¬ (⊥ : Sieve U) ∈ J U) :
    Function.Injective (fun b : B =>
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op U) b) := by
  intro x y hxy
  by_contra hne
  exact hU (J.superset_covering (fun _ _ hf => (hne hf).elim)
    (Presheaf.equalizerSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj B)) (X := op U) x y hxy))

end Stacks.Sheafification
