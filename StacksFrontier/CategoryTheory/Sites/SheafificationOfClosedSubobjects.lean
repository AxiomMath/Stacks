module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Sheafification for concrete categories with closed subobjects

This file abstracts the argument of Stacks 0AI4 for sheaves of topological spaces, topological
abelian groups, topological rings and topological modules. Let `A` be a concrete category in
which

* certain subsets of the underlying sets of objects are *closed* (for topological groups: the
  subgroups), closed subsets are stable under images, preimages, intersections and nonempty
  directed unions, and every closed subset carries the induced subobject
  (`HasClosedSubobjects`); and
* the objects whose underlying set has cardinality at most `κ` are, up to isomorphism, indexed
  by a small type (`HasSmallModels`).

For a presheaf `F` and a sheaf `G` with values in `A`, every map `F ⟶ G` factors through the
subsheaf `G' ⊆ G` of sections which locally lie in the image of `F`, and the cardinalities of
the values of `G'` are bounded by a cardinal depending only on the site and on `F`
(`exists_bounded_subsheaf_factorization_of_closedSubobjects`). If `A` has limits, preserved by
the forgetful functor, the adjoint functor theorem then gives sheafification
(`hasWeakSheafify_of_closedSubobjects`).
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe a t w v u

namespace CategoryTheory

/-- A concrete category `A` *has closed subobjects* if a class of subsets of the underlying sets
of its objects is singled out, stable under images, preimages, intersections and nonempty
directed unions, such that every such subset is the underlying set of a subobject through which
every morphism with image in that subset factors. -/
class HasClosedSubobjects (A : Type a) [Category.{t} A] {FA : A → A → Type t} {CA : A → Type t}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] where
  /-- The closed subsets of the underlying set of `X`. -/
  IsClosedSub : ∀ X : A, Set (ToType X) → Prop
  isClosedSub_range {X Y : A} (f : X ⟶ Y) : IsClosedSub Y (Set.range ⇑f)
  isClosedSub_preimage {X Y : A} (f : X ⟶ Y) {S : Set (ToType Y)} :
    IsClosedSub Y S → IsClosedSub X (⇑f ⁻¹' S)
  isClosedSub_sInter {X : A} (𝒮 : Set (Set (ToType X))) :
    (∀ S ∈ 𝒮, IsClosedSub X S) → IsClosedSub X (⋂₀ 𝒮)
  isClosedSub_sUnion {X : A} (𝒮 : Set (Set (ToType X))) : 𝒮.Nonempty →
    DirectedOn (· ⊆ ·) 𝒮 → (∀ S ∈ 𝒮, IsClosedSub X S) → IsClosedSub X (⋃₀ 𝒮)
  /-- The subobject carried by a closed subset. -/
  sub (X : A) (S : Set (ToType X)) (hS : IsClosedSub X S) : A
  /-- The inclusion of the subobject carried by a closed subset. -/
  subι (X : A) (S : Set (ToType X)) (hS : IsClosedSub X S) : sub X S hS ⟶ X
  injective_subι (X : A) (S : Set (ToType X)) (hS : IsClosedSub X S) :
    Function.Injective ⇑(subι X S hS)
  range_subι (X : A) (S : Set (ToType X)) (hS : IsClosedSub X S) :
    Set.range ⇑(subι X S hS) = S
  /-- A morphism with image in a closed subset factors through its subobject. -/
  subLift {E X : A} (S : Set (ToType X)) (hS : IsClosedSub X S) (f : E ⟶ X) :
    Set.range ⇑f ⊆ S → (E ⟶ sub X S hS)
  subLift_subι {E X : A} (S : Set (ToType X)) (hS : IsClosedSub X S) (f : E ⟶ X)
    (h : Set.range ⇑f ⊆ S) : subLift S hS f h ≫ subι X S hS = f

/-- The objects of a concrete category `A` whose underlying set has cardinality at most `κ` are,
up to isomorphism, the members of a family indexed by a type `Model κ` in the universe of the
underlying sets. -/
class HasSmallModels (A : Type a) [Category.{t} A] {FA : A → A → Type t} {CA : A → Type t}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] where
  /-- The indexing type of the models of cardinality at most `κ`. -/
  Model : Cardinal.{t} → Type t
  /-- The object attached to a model. -/
  toObj {κ : Cardinal.{t}} : Model κ → A
  exists_iso (κ : Cardinal.{t}) (X : A) :
    Cardinal.mk (ToType X) ≤ κ → ∃ m : Model κ, Nonempty (toObj m ≅ X)

namespace HasClosedSubobjects

variable {A : Type a} [Category.{t} A] {FA : A → A → Type t} {CA : A → Type t}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasClosedSubobjects A]

@[reassoc (attr := simp)]
lemma subLift_subι' {E X : A} (S : Set (ToType X)) (hS : IsClosedSub X S) (f : E ⟶ X)
    (h : Set.range ⇑f ⊆ S) : subLift S hS f h ≫ subι X S hS = f :=
  subLift_subι S hS f h

instance (X : A) (S : Set (ToType X)) (hS : IsClosedSub X S) : Mono (subι X S hS) :=
  ConcreteCategory.mono_of_injective _ (injective_subι X S hS)

lemma subι_mem {X : A} {S : Set (ToType X)} (hS : IsClosedSub X S)
    (z : ToType (sub X S hS)) : subι X S hS z ∈ S := by
  have := Set.mem_range_self (f := ⇑(subι X S hS)) z
  rwa [range_subι] at this

end HasClosedSubobjects

open HasClosedSubobjects

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type a} [Category.{max u v w} A] {FA : A → A → Type (max u v w)} {CA : A → Type (max u v w)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- **Stacks 0AI4** (bounded subsheaf), for a concrete category with closed subobjects whose
forgetful functor preserves limits: every map from a fixed presheaf `F` to a sheaf factors
through a subsheaf whose values have cardinality bounded by a cardinal `κ` depending only on
the site and on `F`. The subsheaf is the sheaf of sections which locally lie in the image of
`F`, with the induced structure. -/
theorem exists_bounded_subsheaf_factorization_of_closedSubobjects [HasClosedSubobjects A]
    [PreservesLimitsOfSize.{v, max v u} (forget A)] (F : Cᵒᵖ ⥤ A) :
    ∃ κ : Cardinal.{max u v w}, ∀ (G : Sheaf J A) (f : F ⟶ G.obj),
      ∃ (G' : Sheaf J A) (i : G' ⟶ G), Mono i ∧
        (∀ U : Cᵒᵖ, Cardinal.mk (ToType (G'.obj.obj U)) ≤ κ) ∧
          ∃ f' : F ⟶ G'.obj, f' ≫ i.hom = f := by
  classical
  let κ : Cardinal.{max u v w} :=
    ⨆ U : C, Cardinal.mk (∀ (Y : C) (_ : Y ⟶ U), Option (ToType (F.obj (op Y))))
  refine ⟨κ, fun G f => ?_⟩
  -- Separatedness of `G` on underlying sets.
  have hP : Presieve.IsSheaf J (G.obj ⋙ forget A) :=
    (isSheaf_iff_isSheaf_of_type J _).1
      (Presheaf.isSheaf_comp_of_isSheaf J G.obj (forget A) G.property)
  have hsep : ∀ {U : C} (R : Sieve U), R ∈ J U → ∀ s t : ToType (G.obj.obj (op U)),
      (∀ (Y : C) (g : Y ⟶ U), R g → G.obj.map g.op s = G.obj.map g.op t) → s = t :=
    fun R hR s t h =>
      ((hP.isSheafFor R.arrows (by rwa [Sieve.generate_sieve])).isSeparatedFor).ext
        fun Y g hg => h Y g hg
  have hcomp : ∀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (s : ToType (G.obj.obj (op Z))),
      G.obj.map (a ≫ b).op s = G.obj.map a.op (G.obj.map b.op s) := by
    intro X Y Z a b s
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  -- The sections which lie in the image of `F` on a given sieve.
  let TR : ∀ {U : C}, Sieve U → Set (ToType (G.obj.obj (op U))) := fun {U} R =>
    {s | ∀ (Y : C) (g : Y ⟶ U), R g → G.obj.map g.op s ∈ Set.range ⇑(f.app (op Y))}
  -- The sections which locally lie in the image of `F`.
  let T : ∀ U : C, Set (ToType (G.obj.obj (op U))) := fun U => {s | ∃ R ∈ J U, s ∈ TR R}
  have hTR : ∀ {U : C} (R : Sieve U), TR R =
      ⋂₀ {S' | ∃ (Y : C) (g : Y ⟶ U), R g ∧
        S' = ⇑(G.obj.map g.op) ⁻¹' Set.range ⇑(f.app (op Y))} := by
    intro U R
    ext s
    simp only [Set.mem_sInter, Set.mem_ofPred_eq]
    constructor
    · rintro h S' ⟨Y, g, hg, rfl⟩
      exact h Y g hg
    · intro h Y g hg
      exact h _ ⟨Y, g, hg, rfl⟩
  have hT : ∀ U : C, IsClosedSub _ (T U) := by
    intro U
    have : T U = ⋃₀ ((fun R : Sieve U => TR R) '' {R | R ∈ J U}) := by
      ext s
      simp only [Set.mem_sUnion, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨R, hR, hs⟩
        exact ⟨_, ⟨R, hR, rfl⟩, hs⟩
      · rintro ⟨_, ⟨R, hR, rfl⟩, hs⟩
        exact ⟨R, hR, hs⟩
    rw [this]
    refine isClosedSub_sUnion _ ⟨_, ⊤, J.top_mem U, rfl⟩ ?_ ?_
    · rintro _ ⟨R, hR, rfl⟩ _ ⟨R', hR', rfl⟩
      refine ⟨TR (R ⊓ R'), ⟨_, J.intersection_covering hR hR', rfl⟩, ?_, ?_⟩
      · exact fun s hs Y g hg => hs Y g hg.1
      · exact fun s hs Y g hg => hs Y g hg.2
    · rintro _ ⟨R, -, rfl⟩
      change IsClosedSub _ (TR R)
      rw [hTR]
      refine isClosedSub_sInter _ ?_
      rintro _ ⟨Y, g, -, rfl⟩
      exact isClosedSub_preimage _ (isClosedSub_range _)
  have hres : ∀ {U V : C} (g : V ⟶ U) {s}, s ∈ T U → G.obj.map g.op s ∈ T V := by
    rintro U V g s ⟨R, hR, hs⟩
    refine ⟨R.pullback g, J.pullback_stable g hR, fun Y h hh => ?_⟩
    rw [← hcomp]
    exact hs Y (h ≫ g) hh
  have hloc : ∀ {U : C} (S : Sieve U), S ∈ J U → ∀ s : ToType (G.obj.obj (op U)),
      (∀ (Y : C) (g : Y ⟶ U), S g → G.obj.map g.op s ∈ T Y) → s ∈ T U := by
    intro U S hS s h
    choose R hR hRs using h
    refine ⟨Sieve.bind S fun Y g hg => R Y g hg,
      J.bind_covering hS fun Y g hg => hR Y g hg, ?_⟩
    rintro Z k ⟨Y, h, g, hg, hh, rfl⟩
    rw [hcomp]
    exact hRs Y g hg Z h hh
  -- The subpresheaf `G'`.
  let mapG' : ∀ (U V : Cᵒᵖ) (_ : U ⟶ V),
      sub (G.obj.obj U) (T U.unop) (hT U.unop) ⟶ sub (G.obj.obj V) (T V.unop) (hT V.unop) :=
    fun U V g => subLift (X := G.obj.obj V) (T V.unop) (hT V.unop)
      (subι (G.obj.obj U) (T U.unop) (hT U.unop) ≫ G.obj.map g) (by
        rintro _ ⟨z, rfl⟩
        rw [ConcreteCategory.comp_apply]
        exact hres g.unop (subι_mem (hT U.unop) z))
  have hmapι : ∀ (U V : Cᵒᵖ) (g : U ⟶ V), mapG' U V g ≫ subι (G.obj.obj V) (T V.unop) (hT V.unop)
      = subι (G.obj.obj U) (T U.unop) (hT U.unop) ≫ G.obj.map g :=
    fun U V g => subLift_subι _ _ _ _
  let G' : Cᵒᵖ ⥤ A :=
    { obj U := sub (G.obj.obj U) (T U.unop) (hT U.unop)
      map {U V} g := mapG' U V g
      map_id U := by
        rw [← cancel_mono (subι (G.obj.obj U) (T U.unop) (hT U.unop)), hmapι, Functor.map_id,
          Category.comp_id, Category.id_comp]
      map_comp {U V W} g h := by
        rw [← cancel_mono (subι (G.obj.obj W) (T W.unop) (hT W.unop))]
        have key : (mapG' U V g ≫ mapG' V W h) ≫ subι (G.obj.obj W) (T W.unop) (hT W.unop) =
            subι (G.obj.obj U) (T U.unop) (hT U.unop) ≫ G.obj.map (g ≫ h) := by
          rw [Category.assoc, hmapι, ← Category.assoc, hmapι, Functor.map_comp, Category.assoc]
        exact (hmapι U W (g ≫ h)).trans key.symm }
  let ι' : G' ⟶ G.obj :=
    { app U := subι (G.obj.obj U) (T U.unop) (hT U.unop)
      naturality {U V} g := hmapι U V g }
  have hG' : Presheaf.IsSheaf J G' := by
    intro E X S hS x hx
    let α : G' ⋙ coyoneda.obj (op E) ⟶ G.obj ⋙ coyoneda.obj (op E) :=
      Functor.whiskerRight ι' (coyoneda.obj (op E))
    let y : S.arrows.FamilyOfElements (G.obj ⋙ coyoneda.obj (op E)) := x.map α
    obtain ⟨t, ht, hu⟩ := G.property E S hS y (hx.map α)
    change E ⟶ G.obj.obj (op X) at t
    have hmem : Set.range ⇑t ⊆ T X := by
      rintro _ ⟨e, rfl⟩
      refine hloc S hS _ fun Y g hg => ?_
      have h1 : t ≫ G.obj.map g.op = x g hg ≫ ι'.app (op Y) := ht g hg
      rw [← ConcreteCategory.comp_apply, h1, ConcreteCategory.comp_apply]
      exact subι_mem (hT Y) _
    let t' : E ⟶ G'.obj (op X) := subLift (T X) (hT X) t hmem
    have hti : t' ≫ ι'.app (op X) = t := subLift_subι _ _ _ _
    have hamalg (s : E ⟶ G'.obj (op X)) :
        x.IsAmalgamation s ↔ y.IsAmalgamation (s ≫ ι'.app (op X)) := by
      refine forall₃_congr fun Y r hr => ?_
      change s ≫ G'.map r.op = x r hr ↔
        (s ≫ ι'.app (op X)) ≫ G.obj.map r.op = x r hr ≫ ι'.app (op Y)
      rw [Category.assoc, ← ι'.naturality, ← Category.assoc, cancel_mono]
    refine ⟨t', (hamalg t').2 (hti ▸ ht), fun s₁ hs₁ => ?_⟩
    rw [← cancel_mono (ι'.app (op X)), hti]
    exact (hu _ ((hamalg s₁).1 hs₁)).trans (hu t ht).symm
  let G'' : Sheaf J A := ⟨G', hG'⟩
  let i : G'' ⟶ G := ObjectProperty.homMk ι'
  have hi : Mono i :=
    (sheafToPresheaf J A).mono_of_mono_map (NatTrans.mono_of_mono_app ι')
  have hbase : ∀ (U : Cᵒᵖ), Set.range ⇑(f.app U) ⊆ T U.unop := by
    rintro U _ ⟨a, rfl⟩
    refine ⟨⊤, J.top_mem _, fun Y g _ => ⟨F.map g.op a, ?_⟩⟩
    rw [← ConcreteCategory.comp_apply, f.naturality, ConcreteCategory.comp_apply]
  let f' : F ⟶ G' :=
    { app U := subLift (T U.unop) (hT U.unop) (f.app U) (hbase U)
      naturality {U V} g := by
        have hV : subLift (T V.unop) (hT V.unop) (f.app V) (hbase V) ≫ ι'.app V = f.app V :=
          subLift_subι _ _ _ _
        have hU : subLift (T U.unop) (hT U.unop) (f.app U) (hbase U) ≫ ι'.app U = f.app U :=
          subLift_subι _ _ _ _
        rw [← cancel_mono (ι'.app V), Category.assoc, Category.assoc, ι'.naturality, hV,
          ← Category.assoc, hU]
        exact f.naturality g }
  refine ⟨G'', i, hi, fun U => ?_, f', ?_⟩
  · -- The size bound.
    have hz : ∀ z : ToType (G'.obj U), ∃ R ∈ J U.unop, subι _ _ (hT U.unop) z ∈ TR R :=
      fun z => subι_mem (hT U.unop) z
    choose R hR hRs using hz
    choose b hb using hRs
    let code : ToType (G'.obj U) → ∀ (Y : C) (_ : Y ⟶ U.unop), Option (ToType (F.obj (op Y))) :=
      fun z Y g => if h : R z g then some (b z Y g h) else none
    have hinj : Function.Injective code := by
      intro z₁ z₂ h
      apply injective_subι
      refine hsep (R z₁) (hR z₁) _ _ fun Y g hg => ?_
      have h' := congrFun (congrFun h Y) g
      simp only [code, dite_eq_left hg] at h'
      by_cases hg₂ : R z₂ g
      · rw [dite_eq_left hg₂] at h'
        rw [← hb z₁ Y g hg, ← hb z₂ Y g hg₂, Option.some_inj.1 h']
      · rw [dite_eq_right hg₂] at h'
        exact absurd h' (Option.some_ne_none _)
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    exact le_ciSup (f := fun U : C =>
      Cardinal.mk (∀ (Y : C) (_ : Y ⟶ U), Option (ToType (F.obj (op Y)))))
      Cardinal.bddAbove_of_small U.unop
  · ext U : 2
    exact subLift_subι _ _ _ _

private structure ModelPresheaf [inst : HasSmallModels A] (κ : Cardinal.{max u v w}) where
  obj : Cᵒᵖ → inst.Model κ
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : inst.toObj (obj X) ⟶ inst.toObj (obj Y)
  map_id' (X : Cᵒᵖ) : map (𝟙 X) = 𝟙 _
  map_comp' {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ≫ map g

private def ModelPresheaf.toPresheaf [inst : HasSmallModels A] {κ : Cardinal.{max u v w}}
    (S : ModelPresheaf (C := C) (A := A) κ) : Cᵒᵖ ⥤ A where
  obj X := inst.toObj (S.obj X)
  map := S.map
  map_id := S.map_id'
  map_comp := S.map_comp'

variable (J) in
/-- **Stacks 0AI4** (existence of sheafification), for a concrete category `A` with closed
subobjects and small models, which has limits preserved by its forgetful functor: the inclusion
of `A`-valued sheaves into presheaves has a left adjoint. -/
theorem hasWeakSheafify_of_closedSubobjects [HasClosedSubobjects A] [inst : HasSmallModels A]
    [HasLimitsOfSize.{max u v w, max u v w} A]
    [PreservesLimitsOfSize.{v, max v u} (forget A)] : HasWeakSheafify J A := by
  let G := sheafToPresheaf J A
  have hG : SolutionSetCondition.{max u v w} G := by
    intro F
    obtain ⟨κ, hκ⟩ := exists_bounded_subsheaf_factorization_of_closedSubobjects (J := J) F
    let ι : Type (max u v w) := Σ S : ModelPresheaf (C := C) (A := A) κ,
      {f : F ⟶ S.toPresheaf // Presheaf.IsSheaf J S.toPresheaf}
    let B : ι → Sheaf J A := fun i => ⟨i.1.toPresheaf, i.2.2⟩
    let f₀ : ∀ i, F ⟶ G.obj (B i) := fun i => i.2.1
    refine ⟨ι, B, f₀, fun H f => ?_⟩
    obtain ⟨H', m, -, hsize, f', hf'⟩ := hκ H f
    choose mo hmo using fun X : Cᵒᵖ => inst.exists_iso κ (H'.obj.obj X) (hsize X)
    let e : ∀ X : Cᵒᵖ, inst.toObj (mo X) ≅ H'.obj.obj X := fun X => (hmo X).some
    let S : ModelPresheaf (C := C) (A := A) κ :=
      { obj := mo
        map {X Y} g := (e X).hom ≫ H'.obj.map g ≫ (e Y).inv
        map_id' X := by rw [Functor.map_id, Category.id_comp, Iso.hom_inv_id]
        map_comp' f g := by
          rw [Functor.map_comp]
          simp only [Category.assoc, Iso.inv_hom_id_assoc] }
    let eS : S.toPresheaf ≅ H'.obj :=
      NatIso.ofComponents e (fun {X Y} g => by
        change ((e X).hom ≫ H'.obj.map g ≫ (e Y).inv) ≫ (e Y).hom = (e X).hom ≫ H'.obj.map g
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hS : Presheaf.IsSheaf J S.toPresheaf := (Presheaf.isSheaf_of_iso_iff eS).2 H'.property
    refine ⟨⟨S, ⟨f' ≫ eS.inv, hS⟩⟩,
      (⟨eS.hom⟩ : (⟨S.toPresheaf, hS⟩ : Sheaf J A) ⟶ H') ≫ m, ?_⟩
    change (f' ≫ eS.inv) ≫ (eS.hom ≫ m.hom) = f
    rw [Category.assoc, Iso.inv_hom_id_assoc, hf']
  exact isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG

end

end CategoryTheory
