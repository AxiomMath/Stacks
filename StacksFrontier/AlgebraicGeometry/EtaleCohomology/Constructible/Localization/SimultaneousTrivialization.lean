module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Morphisms

/-!
# Simultaneous trivialization of locally constant sheaves of sets

Let `J` be a Grothendieck topology on `C`. A finite family of sheaves of sets, each of which is
constant with value in a class `P` of sets on a covering of every object, is constant with values
in `P` simultaneously on one covering of every object. In particular a finite family of
(finite) locally constant sheaves of sets is simultaneously constant on a covering of every
object. Tag 093R is about the inverse image along an arbitrary morphism of topoi; this is its
localization case, in simultaneous form.

A trivialization over `Y` restricts to one over `X` along `f : X ⟶ Y` whenever the comparison map
`Stacks.ConstantSheaf.constantSheafOverMapComparison` along `f` is an isomorphism: this holds for
a subsingleton value along every morphism, and for every value along a morphism over which some
sheaf, trivialized above it, is constant on a nontrivial set.

## Main definitions

* `Stacks.ConstantSheaf.overPullbackIsoOfSubsingleton` — the restriction of a trivialization
  with subsingleton value along an arbitrary morphism of the site.
* `Stacks.ConstantSheaf.overPullbackIsoOfDetector` — the restriction of a trivialization along a
  morphism which carries a detector.
* `Stacks.ConstantSheaf.IsConstantWith` — the restriction of a sheaf to the localization at an
  object is the constant sheaf on a set satisfying `P`.

## Main results

* `Stacks.ConstantSheaf.exists_cover_forall_isConstantWith` — a finite family of sheaves of sets,
  each trivializable with values in `P` on a covering of every object, is trivializable
  simultaneously, with values in `P`, on a covering of every object.
* `Stacks.ConstantSheaf.exists_cover_isConstantWith_pair` — the case of two sheaves.
* `Stacks.ConstantSheaf.exists_cover_forall_isConstant` and
  `Stacks.ConstantSheaf.exists_cover_forall_finite_isConstant` — the same for a finite family of
  locally constant, respectively finite locally constant, sheaves of sets.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ConstantSheaf

universe w v u t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

omit [∀ U : C, HasWeakSheafify (J.over U) (Type w)] in
/-- The covering family consisting of the identity of an object is a covering family. -/
public lemma sieve_ofArrows_id_mem (V : C) :
    Sieve.ofArrows (fun _ : PUnit.{max u v + 1} => V) (fun _ => 𝟙 V) ∈ J V := by
  apply J.superset_covering _ (J.top_mem _)
  intro W k _
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, k, by simp⟩

/-- A trivialization of `H` over `V` by the set `B` gives, over any object `W` above `V`, a
locally surjective map onto the restriction of `H` from the constant presheaf on `B`. -/
public def constantUnitOfTrivialization {V W : C} (g : W ⟶ V) (H : Sheaf J (Type w)) (B : Type w)
    (eH : (constantSheaf (J.over V) (Type w)).obj B ≅ (J.overPullback (Type w) V).obj H) :
    (Functor.const (Over W)ᵒᵖ).obj B ⟶ ((J.overPullback (Type w) W).obj H).obj :=
  Functor.whiskerLeft (Over.map g).op
    (CategoryTheory.toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj B) ≫ eH.hom.hom)

/-- The map `Stacks.ConstantSheaf.constantUnitOfTrivialization J g H B eH` is locally
surjective. -/
public lemma isLocallySurjective_constantUnitOfTrivialization {V W : C} (g : W ⟶ V)
    (H : Sheaf J (Type w)) (B : Type w)
    (eH : (constantSheaf (J.over V) (Type w)).obj B ≅ (J.overPullback (Type w) V).obj H) :
    Presheaf.IsLocallySurjective (J.over W) (constantUnitOfTrivialization J g H B eH) := by
  have hunit : Presheaf.IsLocallySurjective (J.over V)
      (CategoryTheory.toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj B)) :=
    Stacks.Sheafification.isLocallySurjective_toSheafify_type (J.over V) _
  have hiso : Presheaf.IsLocallySurjective (J.over V) eH.hom.hom :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun R ↦
      (ConcreteCategory.bijective_of_isIso (eH.hom.hom.app R)).surjective
  have hcomp : Presheaf.IsLocallySurjective (J.over V)
      (CategoryTheory.toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj B) ≫ eH.hom.hom) :=
    @Presheaf.isLocallySurjective_comp _ _ (J.over V)
      _ _ _ _ _ _ _ _ _ _ _ hunit hiso
  exact Presheaf.isLocallySurjective_whisker (J.over W) (J.over V) (Over.map g) _

/-- The restriction along an arbitrary morphism `f : X ⟶ Y` of a trivialization over `Y` whose
constant value is a subsingleton. -/
public def overPullbackIsoOfSubsingleton {X Y : C} (f : X ⟶ Y) (G : Sheaf J (Type w))
    (A : Type w) [Subsingleton A]
    (e : (constantSheaf (J.over Y) (Type w)).obj A ≅ (J.overPullback (Type w) Y).obj G) :
    (constantSheaf (J.over X) (Type w)).obj A ≅ (J.overPullback (Type w) X).obj G :=
  have := constantSheafOverMapComparison_isIso_of_subsingleton J f A
  asIso (constantSheafOverMapComparison J f A) ≪≫ (J.overMapPullback (Type w) f).mapIso e

/-- The restriction along `f : X ⟶ Y` of a trivialization over `Y` by `A`, given a detector for
`f`: a sheaf `H`, trivialized over some object `V` above which `Y` sits, whose restriction to `X`
is the constant sheaf on a nontrivial set `D`. -/
public def overPullbackIsoOfDetector {V X Y : C} (g : Y ⟶ V) (f : X ⟶ Y)
    (G H : Sheaf J (Type w)) (A B D : Type w) [Nontrivial D]
    (eH : (constantSheaf (J.over V) (Type w)).obj B ≅ (J.overPullback (Type w) V).obj H)
    (eD : (constantSheaf (J.over X) (Type w)).obj D ≅ (J.overPullback (Type w) X).obj H)
    (eG : (constantSheaf (J.over Y) (Type w)).obj A ≅ (J.overPullback (Type w) Y).obj G) :
    (constantSheaf (J.over X) (Type w)).obj A ≅ (J.overPullback (Type w) X).obj G :=
  have := isLocallySurjective_constantUnitOfTrivialization J g H B eH
  have := constantSheafOverMapComparison_isIso_of_detector J f A B D
    ((J.overPullback (Type w) Y).obj H) (constantUnitOfTrivialization J g H B eH) eD
  asIso (constantSheafOverMapComparison J f A) ≪≫ (J.overMapPullback (Type w) f).mapIso eG

/-- `IsConstantWith J P F V` says that the restriction of the sheaf `F` to the localization of
the site at `V` is the constant sheaf on a set satisfying `P`. -/
public abbrev IsConstantWith (P : Type w → Prop) (F : Sheaf J (Type w)) (V : C) : Prop :=
  ∃ A : Type w, P A ∧ Nonempty ((constantSheaf (J.over V) (Type w)).obj A ≅
    (J.overPullback (Type w) V).obj F)

/-- A finite family of sheaves of sets, each of which becomes constant with value in a class `P`
on a covering of every object, becomes constant with value in `P` simultaneously on a covering of
every object. -/
public theorem exists_cover_forall_isConstantWith {ι : Type t} (P : Type w → Prop)
    (F : ι → Sheaf J (Type w))
    (hF : ∀ (i : ι) (U : C), ∃ (I : Type (max u v)) (X : I → C) (f : ∀ j, X j ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ j, IsConstantWith J P (F i) (X j))
    (s : Finset ι) (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ j, X j ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ j, ∀ i ∈ s, IsConstantWith J P (F i) (X j) := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
      exact ⟨PUnit.{max u v + 1}, fun _ => U, fun _ => 𝟙 U, sieve_ofArrows_id_mem J U, by simp⟩
  | @insert a s _ ih =>
      let Q : C → Prop := fun Z => ∀ i ∈ insert a s, IsConstantWith J P (F i) Z
      obtain ⟨I₁, V, f₁, hf₁, hV⟩ := ih U
      apply exists_cover_trans J (P := Q) hf₁
      intro j₁
      obtain ⟨I₂, W, f₂, hf₂, hW⟩ := hF a (V j₁)
      apply exists_cover_trans J (P := Q) hf₂
      intro j₂
      obtain ⟨I₃, W', f₃, hf₃, hW'⟩ := ih (W j₂)
      apply exists_cover_trans J (P := Q) hf₃
      intro j₃
      by_cases hnt : ∃ i ∈ s, ∃ A : Type w, P A ∧ Nontrivial A ∧
          Nonempty ((constantSheaf (J.over (W' j₃)) (Type w)).obj A ≅
            (J.overPullback (Type w) (W' j₃)).obj (F i))
      · obtain ⟨i₀, hi₀, D, _, _, ⟨eD⟩⟩ := hnt
        obtain ⟨B, _, ⟨eB⟩⟩ := hV j₁ i₀ hi₀
        obtain ⟨A, hPA, ⟨eA⟩⟩ := hW j₂
        refine ⟨PUnit.{max u v + 1}, fun _ => W' j₃, fun _ => 𝟙 _,
          sieve_ofArrows_id_mem J _, fun _ i hi => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact ⟨A, hPA, ⟨overPullbackIsoOfDetector J (f₂ j₂) (f₃ j₃)
            (F i) (F i₀) A B D eB eD eA⟩⟩
        · exact hW' j₃ i hi
      · obtain ⟨I₄, W'', f₄, hf₄, hW''⟩ := hF a (W' j₃)
        refine ⟨I₄, W'', f₄, hf₄, fun j₄ i hi => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hW'' j₄
        · obtain ⟨A, hPA, ⟨e⟩⟩ := hW' j₃ i hi
          have hA : Subsingleton A := (subsingleton_or_nontrivial A).resolve_right fun h ↦
            hnt ⟨i, hi, A, hPA, h, ⟨e⟩⟩
          exact ⟨A, hPA, ⟨overPullbackIsoOfSubsingleton J (f₄ j₄) (F i) A e⟩⟩

/-- Two sheaves of sets, each of which becomes constant with value in `P` on a covering of every
object, become constant with values in `P` simultaneously on a covering of every object. -/
public theorem exists_cover_isConstantWith_pair (P : Type w → Prop) (F G : Sheaf J (Type w))
    (hF : ∀ U : C, ∃ (I : Type (max u v)) (X : I → C) (f : ∀ j, X j ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ j, IsConstantWith J P F (X j))
    (hG : ∀ U : C, ∃ (I : Type (max u v)) (X : I → C) (f : ∀ j, X j ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ j, IsConstantWith J P G (X j))
    (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ j, X j ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ j,
        IsConstantWith J P F (X j) ∧ IsConstantWith J P G (X j) := by
  classical
  obtain ⟨I, X, f, hf, h⟩ := exists_cover_forall_isConstantWith J P
    (fun b : Bool => bif b then F else G)
    (fun b => by cases b with | false => exact hG | true => exact hF)
    Finset.univ U
  exact ⟨I, X, f, hf, fun j =>
    ⟨h j true (Finset.mem_univ _), h j false (Finset.mem_univ _)⟩⟩

/-- A finite family of locally constant sheaves of sets is simultaneously constant on a covering
of every object. -/
public theorem exists_cover_forall_isConstant {ι : Type t} [Finite ι] (F : ι → Sheaf J (Type w))
    [hF : ∀ i, IsLocallyConstant J (F i)] (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ j, X j ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ j, ∀ i,
        Sheaf.IsConstant (J.over (X j)) ((J.overPullback (Type w) (X j)).obj (F i)) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨I, X, f, hf, h⟩ := exists_cover_forall_isConstantWith J (fun _ => True) F
    (fun i U => by
      obtain ⟨I, X, f, hf, h⟩ := (hF i).exists_cover U
      refine ⟨I, X, f, hf, fun j => ?_⟩
      obtain ⟨A, ⟨e⟩⟩ := (h j).mem_essImage
      exact ⟨A, trivial, ⟨e⟩⟩)
    Finset.univ U
  refine ⟨I, X, f, hf, fun j i => ?_⟩
  obtain ⟨A, -, ⟨e⟩⟩ := h j i (Finset.mem_univ i)
  exact ⟨⟨A, ⟨e⟩⟩⟩

/-- A finite family of finite locally constant sheaves of sets is simultaneously constant, with
finite constant values, on a covering of every object. -/
public theorem exists_cover_forall_finite_isConstant {ι : Type t} [Finite ι]
    (F : ι → Sheaf J (Type w)) [hF : ∀ i, IsFiniteLocallyConstant J (F i)] (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ j, X j ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ j, ∀ i, ∃ A : Type w, Finite A ∧
        Nonempty ((constantSheaf (J.over (X j)) (Type w)).obj A ≅
          (J.overPullback (Type w) (X j)).obj (F i)) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨I, X, f, hf, h⟩ := exists_cover_forall_isConstantWith J Finite F
    (fun i U => IsFiniteLocallyConstant.exists_finite_cover
      (J := J) (FD := TypeCat.Fun) (CD := fun A : Type w => A) (F := F i) U)
    Finset.univ U
  exact ⟨I, X, f, hf, fun j i => h j i (Finset.mem_univ i)⟩

end Stacks.ConstantSheaf

end
