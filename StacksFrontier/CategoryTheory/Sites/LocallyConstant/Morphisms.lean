module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of locally constant sheaves of sets

Let `J` be a Grothendieck topology on `C`. A map `φ : F ⟶ G` of locally constant sheaves of
sets whose source is *finite* locally constant is, locally on the site, induced by a map of
sets: over every object `U` there is a covering `{X i ⟶ U}` and, on each member, local
trivializations `F|_{X i} ≅ A̲` and `G|_{X i} ≅ B̲` of the two sheaves together with a map of sets
`g : A ⟶ B` whose associated map of constant sheaves is `φ|_{X i}`. This is Stacks 093S (1).

The proof goes through two local inputs. Finitely many sections of the target of a locally
surjective map have simultaneous representatives on a covering whose members are not covered
by the empty sieve (`Stacks.Sheafification.exists_cover_representatives`), and the unit of
set-valued sheafification is locally surjective; together these let a trivialization of `F`
over one object be compared with a trivialization of `G` over another by comparing *constant*
sections. The finiteness of `A` is what makes "finitely many sections" enough: the map `g` is
read off from representatives of the images of the `A`-many constant sections of `F`.

The passage from a trivialization over an object to one over an object above it is
`constantSheafOverMapComparison`, the canonical map from the constant sheaf on `C/X` to the
restriction along `Over.map f` of the constant sheaf on `C/Y`. It is always locally
surjective, and it is an isomorphism as soon as the sections of the restricted target are
separated by constant sections of a nontrivial constant sheaf; the two lemmas
`constantSheafOverMapComparison_isIso_of_detector` and
`constantSheafOverMapComparison_isIso_of_subsingleton` cover the two cases that arise.

## Main results

* `Stacks.ConstantSheaf.exists_cover_restrict_eq_constantSheaf_map`: locally on the site, a
  morphism of locally constant sheaves of sets with finite locally constant source is induced
  by a map of sets.

## Implementation notes

The statement is proved over an *arbitrary* object of the site rather than only over a final
object, which is how the source phrases it; the version over a final object is the special
case. No finality hypothesis is used anywhere.

The degenerate cases are handled rather than excluded. Over a member of a covering which is
itself covered by the empty sieve every sheaf is terminal, so the empty covering already
witnesses the conclusion; and when the local constant value of the target is a subsingleton
the map of sets is produced from nonemptiness of the target value, which is forced because the
object is not covered by the empty sieve.

The `Quiver` instance coming from `CategoryTheory.catToReflQuiver` is removed for the final
statement, so that the arrow `A ⟶ B` in the conclusion is the morphism of types and not a
reflexive-quiver arrow; this keeps the statement the one the source makes.

## References

* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ConstantSheaf

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

omit [∀ U : C, HasWeakSheafify (J.over U) (Type w)] in
/-- If two distinct elements `b₀ ≠ b₁` of `A` have the same image in the sections over `U` of the
constant sheaf on `A`, then any two elements of `B` have the same image in the sections over `U`
of the constant sheaf on `B`. -/
lemma constant_unit_map_eq_of_pair_eq [HasWeakSheafify J (Type w)]
    (A B : Type w) (U : C) {b₀ b₁ : A} (hne : b₀ ≠ b₁)
    (h : (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj A)).app
      (Opposite.op U) b₀ =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj A)).app
        (Opposite.op U) b₁) (b b' : B) :
    (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app
      (Opposite.op U) b =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app
        (Opposite.op U) b' := by
  classical
  let g : A ⟶ B := TypeCat.ofHom (fun t => if t = b₀ then b else b')
  have hg := congrArg
    (((constantSheaf J (Type w)).map g).hom.app (Opposite.op U)) h
  have hn := CategoryTheory.toSheafify_naturality J ((Functor.const Cᵒᵖ).map g)
  have hn₀ := congrArg (fun t => t.app (Opposite.op U) b₀) hn
  have hn₁ := congrArg (fun t => t.app (Opposite.op U) b₁) hn
  have h₀ : g b₀ = b := by simp [g]
  have h₁ : g b₁ = b' := by simp [g, Ne.symm hne]
  change (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app
      (Opposite.op U) (g b₀) = _ at hn₀
  change (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app
      (Opposite.op U) (g b₁) = _ at hn₁
  rw [h₀] at hn₀
  rw [h₁] at hn₁
  exact hn₀.trans (hg.trans hn₁.symm)

/-- Two sections `s t` of a sheaf `F`, which locally have representatives under a locally
surjective map `η` from a constant presheaf, are equal as soon as any such representatives have
equal images under `η`. -/
private theorem eq_of_const_representatives_eq
    {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    (B : Type w) (F : Sheaf K (Type w))
    (η : (Functor.const Dᵒᵖ).obj B ⟶ F.obj)
    [Presheaf.IsLocallySurjective K η] {U : D} (s t : F.obj.obj (Opposite.op U))
    (h : ∀ (V : D) (g : V ⟶ U) (b b' : B), F.obj.map g.op s = η.app (Opposite.op V) b →
      F.obj.map g.op t = η.app (Opposite.op V) b' →
        η.app (Opposite.op V) b = η.app (Opposite.op V) b') :
    s = t := by
  obtain ⟨I, V, f, hf, hv⟩ := Stacks.Sheafification.exists_cover_representatives
    K η U ![s, t]
  apply ((isSheaf_iff_isSheaf_of_type K F.obj).mp F.property).isSeparated _ hf |>.ext
  intro W k hk
  obtain ⟨i, a, rfl⟩ := Sieve.ofArrows.exists hk
  obtain ⟨b, hb⟩ := (hv i).2 0
  obtain ⟨b', hb'⟩ := (hv i).2 1
  simp only [op_comp, Functor.map_comp, types_comp_apply]
  apply congrArg (F.obj.map a.op)
  exact hb.trans ((h _ _ b b' hb hb').trans hb'.symm)

omit [∀ U : C, HasWeakSheafify (J.over U) (Type w)] in
/-- If `η` is a locally surjective map from the constant presheaf on `B` to a sheaf `F`, and all
elements of `B` have the same image under `η` over `U`, then `F(U)` has at most one element. -/
lemma subsingleton_sections_of_const_eq
    (B : Type w) (F : Sheaf J (Type w))
    (η : (Functor.const Cᵒᵖ).obj B ⟶ F.obj)
    [Presheaf.IsLocallySurjective J η] (U : C)
    (h : ∀ b b', η.app (Opposite.op U) b = η.app (Opposite.op U) b') :
    Subsingleton (F.obj.obj (Opposite.op U)) :=
  ⟨fun s t => eq_of_const_representatives_eq J B F η s t fun _ g b b' _ _ =>
    (NatTrans.naturality_apply η g.op b).trans
      ((congrArg (F.obj.map g.op) (h b b')).trans (NatTrans.naturality_apply η g.op b').symm)⟩

omit [∀ U : C, HasWeakSheafify (J.over U) (Type w)] in
/-- Let `η` be a locally surjective map from the constant presheaf on `A` to a sheaf `F`, and
`φ : F ⟶ G`. If, over every object, two constant sections `η a` and `η b` with equal images under
`φ` are already equal, then every component of `φ` is injective. -/
lemma injective_of_const_eq_imp
    (A : Type w) (F G : Sheaf J (Type w))
    (η : (Functor.const Cᵒᵖ).obj A ⟶ F.obj)
    [Presheaf.IsLocallySurjective J η] (φ : F ⟶ G)
    (h : ∀ (U : C) (a b : A),
      φ.hom.app (Opposite.op U) (η.app _ a) =
        φ.hom.app (Opposite.op U) (η.app _ b) →
      η.app (Opposite.op U) a = η.app (Opposite.op U) b) :
    ∀ U, Function.Injective (φ.hom.app U) := fun U s t hst =>
  eq_of_const_representatives_eq J A F η s t fun _ g a b hb hb' =>
    h _ a b (by rw [← hb, ← hb', NatTrans.naturality_apply φ.hom g.op s,
      NatTrans.naturality_apply φ.hom g.op t, hst])

/-- The comparison from the constant sheaf to the restriction of a constant sheaf. -/
noncomputable def constantSheafOverMapComparison {X Y : C} (f : X ⟶ Y)
    (B : Type w) : (constantSheaf (J.over X) (Type w)).obj B ⟶
      (J.overMapPullback (Type w) f).obj ((constantSheaf (J.over Y) (Type w)).obj B) :=
  ⟨sheafifyLift (J.over X)
    (Functor.whiskerLeft (Over.map f).op
      (CategoryTheory.toSheafify (J.over Y) ((Functor.const (Over Y)ᵒᵖ).obj B)))
    ((J.overMapPullback (Type w) f).obj
      ((constantSheaf (J.over Y) (Type w)).obj B)).property⟩

/-- The unit of sheafification on `C/X` followed by `constantSheafOverMapComparison J f B` is the
unit of sheafification on `C/Y` whiskered along `Over.map f`. -/
lemma constantSheafOverMapComparison_unit {X Y : C} (f : X ⟶ Y) (B : Type w) :
    CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj B) ≫
      (constantSheafOverMapComparison J f B).hom =
        Functor.whiskerLeft (Over.map f).op
          (CategoryTheory.toSheafify (J.over Y) ((Functor.const (Over Y)ᵒᵖ).obj B)) :=
  toSheafify_sheafifyLift _ _ _

/-- The map `constantSheafOverMapComparison J f B` is locally surjective. -/
lemma constantSheafOverMapComparison_locallySurjective {X Y : C} (f : X ⟶ Y)
    (B : Type w) : Sheaf.IsLocallySurjective (constantSheafOverMapComparison J f B) := by
  let η := CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj B)
  have : Presheaf.IsLocallySurjective (J.over X)
      (η ≫ (constantSheafOverMapComparison J f B).hom) := by
    dsimp only [η]
    rw [constantSheafOverMapComparison_unit]
    exact Presheaf.isLocallySurjective_whisker (J.over X) (J.over Y) (Over.map f) _
  exact Presheaf.isLocallySurjective_of_isLocallySurjective (J.over X) η _

/-- If two constant sections of the constant sheaf on `A` with equal images under
`constantSheafOverMapComparison J f A` are already equal, then it is an isomorphism. -/
private theorem isIso_constantSheafOverMapComparison_of_const_eq_imp
    {X Y : C} (f : X ⟶ Y) (A : Type w)
    (h : ∀ (R : Over X) (a b : A),
      (constantSheafOverMapComparison J f A).hom.app (Opposite.op R)
          ((CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj A)).app _ a) =
        (constantSheafOverMapComparison J f A).hom.app (Opposite.op R)
          ((CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj A)).app _ b) →
      (CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj A)).app
          (Opposite.op R) a =
        (CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj A)).app
          (Opposite.op R) b) :
    IsIso (constantSheafOverMapComparison J f A) := by
  have := Stacks.Sheafification.isLocallySurjective_toSheafify_type (J.over X)
    ((Functor.const (Over X)ᵒᵖ).obj A)
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp
    ⟨Presheaf.isLocallyInjective_of_injective (J.over X) _
      (injective_of_const_eq_imp (J.over X) A _ _
        (CategoryTheory.toSheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj A)) _ h),
      constantSheafOverMapComparison_locallySurjective J f A⟩

/-- Let `H` be a sheaf on `C/Y` admitting a locally surjective map from the constant presheaf on
`B`. If the restriction of `H` along `Over.map f` is isomorphic to the constant sheaf on a
nontrivial type `D`, then `constantSheafOverMapComparison J f A` is an isomorphism. -/
lemma constantSheafOverMapComparison_isIso_of_detector
    {X Y : C} (f : X ⟶ Y) (A B D : Type w) [Nontrivial D]
    (H : Sheaf (J.over Y) (Type w))
    (θ : (Functor.const (Over Y)ᵒᵖ).obj B ⟶ H.obj)
    [Presheaf.IsLocallySurjective (J.over Y) θ]
    (e : (constantSheaf (J.over X) (Type w)).obj D ≅
      (J.overMapPullback (Type w) f).obj H) :
    IsIso (constantSheafOverMapComparison J f A) := by
  refine isIso_constantSheafOverMapComparison_of_const_eq_imp J f A (by
      intro R a b hab
      by_cases heq : a = b
      · exact congrArg _ heq
      let R' := (Over.map f).obj R
      have hu (t : A) := congrArg (fun k => k.app (Opposite.op R) t)
        (constantSheafOverMapComparison_unit J f A)
      have hy : (CategoryTheory.toSheafify (J.over Y)
          ((Functor.const (Over Y)ᵒᵖ).obj A)).app (Opposite.op R') a =
          (CategoryTheory.toSheafify (J.over Y)
          ((Functor.const (Over Y)ᵒᵖ).obj A)).app (Opposite.op R') b :=
        (hu a).symm.trans (hab.trans (hu b))
      have hθ : ∀ b b', θ.app (Opposite.op R') b = θ.app (Opposite.op R') b' := by
        intro b₀ b₁
        have hh := constant_unit_map_eq_of_pair_eq (J.over Y) A B R' heq hy b₀ b₁
        have hh' := congrArg ((sheafifyLift (J.over Y) θ H.property).app
          (Opposite.op R')) hh
        have hl := toSheafify_sheafifyLift (J.over Y) θ H.property
        exact (congrArg (fun k => k.app (Opposite.op R') b₀) hl).symm.trans
          (hh'.trans (congrArg (fun k => k.app (Opposite.op R') b₁) hl))
      let _ : Subsingleton (((J.overMapPullback (Type w) f).obj H).obj.obj
          (Opposite.op R)) :=
        subsingleton_sections_of_const_eq (J.over Y) B H θ R' hθ
      obtain ⟨d₀, d₁, hd⟩ := exists_pair_ne D
      have hd' : (CategoryTheory.toSheafify (J.over X)
          ((Functor.const (Over X)ᵒᵖ).obj D)).app (Opposite.op R) d₀ =
          (CategoryTheory.toSheafify (J.over X)
          ((Functor.const (Over X)ᵒᵖ).obj D)).app (Opposite.op R) d₁ := by
        apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (Opposite.op R))).injective
        exact Subsingleton.elim _ _
      exact constant_unit_map_eq_of_pair_eq (J.over X) D A R hd hd' a b)

/-- For a subsingleton type `A`, the map `constantSheafOverMapComparison J f A` is an
isomorphism. -/
lemma constantSheafOverMapComparison_isIso_of_subsingleton
    {X Y : C} (f : X ⟶ Y) (A : Type w) [Subsingleton A] :
    IsIso (constantSheafOverMapComparison J f A) := by
  exact isIso_constantSheafOverMapComparison_of_const_eq_imp J f A
    (fun R a b _ => congrArg _ (Subsingleton.elim a b))

omit [∀ U : C, HasWeakSheafify (J.over U) (Type w)] in
/-- If `{X i ⟶ U}` is a covering family and each `X i` has a covering family by objects
satisfying `P`, then `U` has a covering family by objects satisfying `P`. -/
lemma exists_cover_trans {U : C} {P : C → Prop}
    {I : Type (max u v)} {X : I → C} {f : ∀ i, X i ⟶ U}
    (hf : Sieve.ofArrows X f ∈ J U)
    (h : ∀ i, ∃ (I' : Type (max u v)) (Y : I' → C) (g : ∀ j, Y j ⟶ X i),
      Sieve.ofArrows Y g ∈ J (X i) ∧ ∀ j, P (Y j)) :
    ∃ (I' : Type (max u v)) (Y : I' → C) (g : ∀ j, Y j ⟶ U),
      Sieve.ofArrows Y g ∈ J U ∧ ∀ j, P (Y j) := by
  classical
  choose I' Y g hg hP using h
  let Z : (Σ i, I' i) → C := fun j => Y j.1 j.2
  let k : ∀ j, Z j ⟶ U := fun j => g j.1 j.2 ≫ f j.1
  refine ⟨_, Z, k, ?_, fun j => hP j.1 j.2⟩
  apply J.transitive hf
  intro W a ha
  obtain ⟨i, b, rfl⟩ := Sieve.ofArrows.exists ha
  have hi : (Sieve.ofArrows Z k).pullback (f i) ∈ J (X i) := by
    apply J.superset_covering _ (hg i)
    intro V c hc
    obtain ⟨j, d, rfl⟩ := Sieve.ofArrows.exists hc
    apply (Sieve.mem_ofArrows_iff Z k _).mpr
    exact ⟨⟨i, j⟩, d, Category.assoc _ _ _⟩
  simpa only [Sieve.pullback_comp] using J.pullback_stable b hi

private abbrev ConstantMapAt (F G : Sheaf J (Type w)) (φ : F ⟶ G) (V : C) : Prop :=
  ∃ (A B : Type w), Finite A ∧
    ∃ (g : A ⟶ B)
      (eF : (constantSheaf (J.over V) (Type w)).obj A ≅
        (J.overPullback (Type w) V).obj F)
      (eG : (constantSheaf (J.over V) (Type w)).obj B ≅
        (J.overPullback (Type w) V).obj G),
      (constantSheaf (J.over V) (Type w)).map g ≫ eG.hom =
        eF.hom ≫ (J.overPullback (Type w) V).map φ

private lemma constant_map_at_of_subsingleton_target
    (F G : Sheaf J (Type w)) (φ : F ⟶ G) (V : C) (A B : Type w)
    [Finite A] [Subsingleton B] (hV : ¬ (⊥ : Sieve V) ∈ J V)
    (eF : (constantSheaf (J.over V) (Type w)).obj A ≅
      (J.overPullback (Type w) V).obj F)
    (eG : (constantSheaf (J.over V) (Type w)).obj B ≅
      (J.overPullback (Type w) V).obj G) : ConstantMapAt J F G φ V := by
  classical
  let ψ := eF.hom ≫ (J.overPullback (Type w) V).map φ ≫ eG.inv
  let η : (Functor.const (Over V)ᵒᵖ).obj B ⟶
      ((constantSheaf (J.over V) (Type w)).obj B).obj :=
    CategoryTheory.toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj B)
  have hη : Presheaf.IsLocallySurjective (J.over V) η := by
    dsimp only [η]
    exact Stacks.Sheafification.isLocallySurjective_toSheafify_type (J.over V) _
  have hb (a : A) : Nonempty B := by
    by_contra h
    let R : Over V := Over.mk (𝟙 V)
    let s := ψ.hom.app (Opposite.op R)
      ((CategoryTheory.toSheafify (J.over V)
        ((Functor.const (Over V)ᵒᵖ).obj A)).app (Opposite.op R) a)
    have hi := Presheaf.imageSieve_mem (J := J.over V) (f := η) (s := s)
    have he : Presheaf.imageSieve η s = ⊥ := by
      apply le_antisymm _ bot_le
      intro W k hk
      obtain ⟨b, _⟩ := hk
      exact (h ⟨b⟩).elim
    rw [he, GrothendieckTopology.mem_over_iff] at hi
    rw [map_bot] at hi
    change (⊥ : Sieve V) ∈ J V at hi
    exact hV hi
  let g : A ⟶ B := TypeCat.ofHom (fun a => (hb a).some)
  refine ⟨A, B, inferInstance, g, eF, eG, ?_⟩
  apply (cancel_mono eG.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Sheaf.hom_ext
  ext R a
  let _ : Subsingleton (((constantSheaf (J.over V) (Type w)).obj B).obj.obj
      (Opposite.op R.unop)) := by
    apply subsingleton_sections_of_const_eq (J.over V) B
      ((constantSheaf (J.over V) (Type w)).obj B) η R.unop
    exact fun b b' => congrArg _ (@Subsingleton.elim B inferInstance b b')
  exact Subsingleton.elim _ _

private lemma exists_cover_constant_map_of_subsingleton_target
    (F G : Sheaf J (Type w)) (φ : F ⟶ G)
    [IsFiniteLocallyConstant J F] (U : C) (B : Type w) [Subsingleton B]
    (eG : (constantSheaf (J.over U) (Type w)).obj B ≅
      (J.overPullback (Type w) U).obj G) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i, ConstantMapAt J F G φ (X i) := by
  classical
  obtain ⟨I, X, f, hf, hF⟩ := IsFiniteLocallyConstant.exists_finite_cover
    (J := J) (FD := TypeCat.Fun) (CD := fun A : Type w => A) (F := F) U
  apply exists_cover_trans J (P := ConstantMapAt J F G φ) hf
  intro i
  by_cases hi : (⊥ : Sieve (X i)) ∈ J (X i)
  · refine ⟨PEmpty, PEmpty.elim, (fun j => j.elim), ?_, fun i => i.elim⟩
    apply J.superset_covering _ hi
    exact bot_le
  · obtain ⟨A, hA, ⟨eF⟩⟩ := hF i
    let _ : Finite A := hA
    let _ := constantSheafOverMapComparison_isIso_of_subsingleton J (f i) B
    let eG' : (constantSheaf (J.over (X i)) (Type w)).obj B ≅
        (J.overPullback (Type w) (X i)).obj G :=
      asIso (constantSheafOverMapComparison J (f i) B) ≪≫
        (J.overMapPullback (Type w) (f i)).mapIso eG
    refine ⟨PUnit, fun _ => X i, fun _ => 𝟙 _, ?_, fun _ => ?_⟩
    · apply J.superset_covering _ (J.top_mem _)
      intro W k _
      exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, k, by simp⟩
    · exact constant_map_at_of_subsingleton_target J F G φ (X i) A B hi eF eG'

private lemma exists_cover_constant_map
    (F G : Sheaf J (Type w)) (φ : F ⟶ G)
    [IsFiniteLocallyConstant J F] [IsLocallyConstant J G] (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i, ConstantMapAt J F G φ (X i) := by
  classical
  obtain ⟨I, Y, f, hf, hG⟩ := IsLocallyConstant.exists_cover
    (J := J) (F := G) U
  apply exists_cover_trans J (P := ConstantMapAt J F G φ) hf
  intro i
  obtain ⟨B, ⟨eB⟩⟩ := (hG i).mem_essImage
  let θ := CategoryTheory.toSheafify (J.over (Y i))
    ((Functor.const (Over (Y i))ᵒᵖ).obj B) ≫ eB.hom.hom
  let _ : Presheaf.IsLocallySurjective (J.over (Y i)) θ := by
    dsimp only [θ]
    have hunit : Presheaf.IsLocallySurjective (J.over (Y i))
        (CategoryTheory.toSheafify (J.over (Y i))
          ((Functor.const (Over (Y i))ᵒᵖ).obj B)) :=
      Stacks.Sheafification.isLocallySurjective_toSheafify_type (J.over (Y i)) _
    have hsurj : Presheaf.IsLocallySurjective (J.over (Y i)) eB.hom.hom := by
      apply Presheaf.isLocallySurjective_of_surjective
      intro R
      exact (ConcreteCategory.bijective_of_isIso (eB.hom.hom.app R)).surjective
    exact @Presheaf.isLocallySurjective_comp _ _ (J.over (Y i))
      _ _ _ _ _ _ _ _ _ _ _ hunit hsurj
  obtain ⟨I', Z, g, hg, hF⟩ := IsFiniteLocallyConstant.exists_finite_cover
    (J := J) (FD := TypeCat.Fun) (CD := fun A : Type w => A) (F := F) (Y i)
  apply exists_cover_trans J (P := ConstantMapAt J F G φ) hg
  intro j
  obtain ⟨A, hA, ⟨eA⟩⟩ := hF j
  let _ : Finite A := hA
  let _ := Fintype.ofFinite A
  let e := Fintype.equivFin A
  let ξ := CategoryTheory.toSheafify (J.over (Z j))
    ((Functor.const (Over (Z j))ᵒᵖ).obj A) ≫ eA.hom.hom ≫
      ((J.overPullback (Type w) (Z j)).map φ).hom
  let R : Over (Y i) := Over.mk (g j)
  let T : Over (Z j) := Over.mk (𝟙 (Z j))
  obtain ⟨L, W, k, hk, hm⟩ := Stacks.Sheafification.exists_cover_representatives
    (J.over (Y i)) θ R (fun a => ξ.app (Opposite.op T) (e.symm a))
  let p : ∀ l, (W l).left ⟶ Z j := fun l => (k l).left
  have hcover : Sieve.ofArrows (fun l => (W l).left) p ∈ J (Z j) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hk
    change Sieve.ofArrows (fun l => (W l).left) p ∈ J (Z j) at hk
    exact hk
  have hrep (l : L) (a : A) : ∃ b : B,
      ξ.app (Opposite.op (Over.mk (p l))) a = θ.app (Opposite.op (W l)) b := by
    obtain ⟨b, hb⟩ := (hm l).2 (e a)
    refine ⟨b, ?_⟩
    let z : Over.mk (p l) ⟶ T := Over.homMk (p l) (by simp [T])
    calc
      _ = ((J.overPullback (Type w) (Z j)).obj G).obj.map z.op
          (ξ.app (Opposite.op T) a) := NatTrans.naturality_apply ξ z.op a
      _ = _ := by
        change G.obj.map (p l).op (ξ.app (Opposite.op T) a) = _
        change G.obj.map (p l).op (ξ.app (Opposite.op T) (e.symm (e a))) = _ at hb
        simpa only [Equiv.symm_apply_apply] using hb
  choose m hm' using hrep
  apply exists_cover_trans J (P := ConstantMapAt J F G φ) hcover
  intro l
  obtain ⟨N, Q, h, hh, hQ⟩ := IsLocallyConstant.exists_cover
    (J := J) (F := G) (W l).left
  apply exists_cover_trans J (P := ConstantMapAt J F G φ) hh
  intro t
  obtain ⟨D, ⟨eD⟩⟩ := (hQ t).mem_essImage
  rcases subsingleton_or_nontrivial D with hD | hD
  · let _ := hD
    exact exists_cover_constant_map_of_subsingleton_target J F G φ (Q t) D eD
  · let _ := hD
    let q : Q t ⟶ Z j := h t ≫ p l
    let r : Q t ⟶ Y i := h t ≫ (W l).hom
    let θZ : (Functor.const (Over (Z j))ᵒᵖ).obj B ⟶
        ((J.overPullback (Type w) (Z j)).obj G).obj :=
      Functor.whiskerLeft (Over.map (g j)).op θ
    let _ : Presheaf.IsLocallySurjective (J.over (Z j)) θZ :=
      Presheaf.isLocallySurjective_whisker (J.over (Z j)) (J.over (Y i))
        (Over.map (g j)) θ
    let _ := constantSheafOverMapComparison_isIso_of_detector J q A B D
      ((J.overPullback (Type w) (Z j)).obj G) θZ eD
    let _ := constantSheafOverMapComparison_isIso_of_detector J r B B D
      ((J.overPullback (Type w) (Y i)).obj G) θ eD
    let eF : (constantSheaf (J.over (Q t)) (Type w)).obj A ≅
        (J.overPullback (Type w) (Q t)).obj F :=
      asIso (constantSheafOverMapComparison J q A) ≪≫
        (J.overMapPullback (Type w) q).mapIso eA
    let eG : (constantSheaf (J.over (Q t)) (Type w)).obj B ≅
        (J.overPullback (Type w) (Q t)).obj G :=
      asIso (constantSheafOverMapComparison J r B) ≪≫
        (J.overMapPullback (Type w) r).mapIso eB
    have huF : CategoryTheory.toSheafify (J.over (Q t))
        ((Functor.const (Over (Q t))ᵒᵖ).obj A) ≫ eF.hom.hom =
        Functor.whiskerLeft (Over.map q).op
          (CategoryTheory.toSheafify (J.over (Z j))
            ((Functor.const (Over (Z j))ᵒᵖ).obj A) ≫ eA.hom.hom) := by
      exact congrArg (fun z => z ≫ ((J.overMapPullback (Type w) q).mapIso eA).hom.hom)
        (constantSheafOverMapComparison_unit J q A)
    have huG : CategoryTheory.toSheafify (J.over (Q t))
        ((Functor.const (Over (Q t))ᵒᵖ).obj B) ≫ eG.hom.hom =
        Functor.whiskerLeft (Over.map r).op θ := by
      exact congrArg (fun z => z ≫ ((J.overMapPullback (Type w) r).mapIso eB).hom.hom)
        (constantSheafOverMapComparison_unit J r B)
    have hmap : ConstantMapAt J F G φ (Q t) := by
      refine ⟨A, B, hA, TypeCat.ofHom (m l), eF, eG, ?_⟩
      apply Sheaf.hom_ext
      apply sheafify_hom_ext (J.over (Q t)) _ _
        ((J.overPullback (Type w) (Q t)).obj G).property
      have hnat : (Functor.const (Over (Q t))ᵒᵖ).map (TypeCat.ofHom (m l)) ≫
          CategoryTheory.toSheafify (J.over (Q t))
            ((Functor.const (Over (Q t))ᵒᵖ).obj B) =
          CategoryTheory.toSheafify (J.over (Q t))
              ((Functor.const (Over (Q t))ᵒᵖ).obj A) ≫
            CategoryTheory.sheafifyMap (J.over (Q t))
              ((Functor.const (Over (Q t))ᵒᵖ).map (TypeCat.ofHom (m l))) :=
        CategoryTheory.toSheafify_naturality _ _
      have key : (Functor.const (Over (Q t))ᵒᵖ).map (TypeCat.ofHom (m l)) ≫
          Functor.whiskerLeft (Over.map r).op θ =
          Functor.whiskerLeft (Over.map q).op
              (CategoryTheory.toSheafify (J.over (Z j))
                ((Functor.const (Over (Z j))ᵒᵖ).obj A) ≫ eA.hom.hom) ≫
            ((J.overPullback (Type w) (Q t)).map φ).hom := by
        ext S a
        let z : (Over.map q).obj S.unop ⟶ Over.mk (p l) :=
          Over.homMk (S.unop.hom ≫ h t) (by simp [q])
        let y : (Over.map r).obj S.unop ⟶ W l :=
          Over.homMk (S.unop.hom ≫ h t) (by simp [r])
        change θ.app (Opposite.op ((Over.map r).obj S.unop)) (m l a) =
          ξ.app (Opposite.op ((Over.map q).obj S.unop)) a
        have hleft := NatTrans.naturality_apply θ y.op (m l a)
        have hright := NatTrans.naturality_apply ξ z.op a
        change _ = G.obj.map (S.unop.hom ≫ h t).op
          (θ.app (Opposite.op (W l)) (m l a)) at hleft
        change _ = G.obj.map (S.unop.hom ≫ h t).op
          (ξ.app (Opposite.op (Over.mk (p l))) a) at hright
        exact hleft.trans ((congrArg _ (hm' l a).symm).trans hright.symm)
      set cg := (Functor.const (Over (Q t))ᵒᵖ).map (TypeCat.ofHom (m l))
      set tsA := CategoryTheory.toSheafify (J.over (Q t))
        ((Functor.const (Over (Q t))ᵒᵖ).obj A) with htsA
      set tsB := CategoryTheory.toSheafify (J.over (Q t))
        ((Functor.const (Over (Q t))ᵒᵖ).obj B) with htsB
      set sm := CategoryTheory.sheafifyMap (J.over (Q t)) cg
      set pphi := ((J.overPullback (Type w) (Q t)).map φ).hom
      have e1 : tsA ≫ sm ≫ eG.hom.hom = (tsA ≫ sm) ≫ eG.hom.hom :=
        (Category.assoc _ _ _).symm
      have e2 : (tsA ≫ sm) ≫ eG.hom.hom = (cg ≫ tsB) ≫ eG.hom.hom :=
        congrArg (fun z => z ≫ eG.hom.hom) hnat.symm
      have e3 : (cg ≫ tsB) ≫ eG.hom.hom = cg ≫ tsB ≫ eG.hom.hom :=
        Category.assoc _ _ _
      have e4 : cg ≫ tsB ≫ eG.hom.hom = cg ≫ Functor.whiskerLeft (Over.map r).op θ :=
        congrArg (fun z => cg ≫ z) huG
      have e6 : Functor.whiskerLeft (Over.map q).op
            (CategoryTheory.toSheafify (J.over (Z j))
              ((Functor.const (Over (Z j))ᵒᵖ).obj A) ≫ eA.hom.hom) ≫ pphi =
          (tsA ≫ eF.hom.hom) ≫ pphi :=
        congrArg (fun z => z ≫ pphi) huF.symm
      have e7 : (tsA ≫ eF.hom.hom) ≫ pphi = tsA ≫ eF.hom.hom ≫ pphi :=
        Category.assoc _ _ _
      exact e1.trans (e2.trans (e3.trans (e4.trans (key.trans (e6.trans e7)))))
    refine ⟨PUnit, fun _ => Q t, fun _ => 𝟙 _, ?_, fun _ => hmap⟩
    apply J.superset_covering _ (J.top_mem _)
    intro V a _
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, a, by simp⟩

/-- A morphism of locally constant sheaves of sets whose source is finite locally constant is, on
a covering of any object, obtained from a map of sets. -/
@[stacks 093S "sets", sga "4 IX 2.1" "(i)"]
lemma exists_cover_restrict_eq_constantSheaf_map
    (F G : Sheaf J (Type w)) (φ : F ⟶ G)
    [IsFiniteLocallyConstant J F] [IsLocallyConstant J G] (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i,
        ∃ (A B : Type w), Finite A ∧
          ∃ (g : A ⟶ B)
            (eF : (constantSheaf (J.over (X i)) (Type w)).obj A ≅
              (J.overPullback (Type w) (X i)).obj F)
            (eG : (constantSheaf (J.over (X i)) (Type w)).obj B ≅
              (J.overPullback (Type w) (X i)).obj G),
              (constantSheaf (J.over (X i)) (Type w)).map g ≫ eG.hom =
                eF.hom ≫ (J.overPullback (Type w) (X i)).map φ := by
  exact exists_cover_constant_map J F G φ U

end Stacks.ConstantSheaf
