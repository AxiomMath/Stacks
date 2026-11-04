module

public import Mathlib.CategoryTheory.Limits.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProCategory
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMajorant
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Isomorphisms in the category of pro-objects, read levelwise

An inverse sequence `F : ℕᵒᵖ ⥤ 𝒟` determines a pro-object of `𝒟`, namely
`CategoryTheory.ProSeq.of F`, and that pro-object is used through its functor of points
`N ↦ colim_n Mor(F_n, N)`. Two inverse sequences are *pro-isomorphic* when the pro-objects they
determine are isomorphic in `Pro-𝒟`, equivalently — `ProSeq` being a full subcategory of
`𝒟 ⥤ Type v` opposite — when their functors of points are isomorphic.

That description of a pro-isomorphism says nothing levelwise, and a levelwise description is what
is needed to push a pro-isomorphism forward along a functor `𝒟 ⥤ 𝒞`, which does not act on the
functors of points at all. This file extracts one: an isomorphism of functors of points yields
increasing reindexings `α`, `β` and compatible morphisms `F_{α m} ⟶ G_m`, `G_{β m} ⟶ F_m` whose
two composites are transition morphisms, i.e. a `ProIso` — the explicit form of a
pro-isomorphism. The extraction is the only non-formal step: a class in a filtered colimit of
`Hom`-sets is represented at some stage, and the representatives of the successive identities can
be corrected to a compatible family by a diagonal argument.

With the levelwise form available, a pro-isomorphism pushes forward along any functor, composes,
and — against a constant sequence — says exactly that the sequence is an essentially constant
pro-object in the sense of Stacks 05PZ.

## Main definitions

* `CategoryTheory.Pro.seqHomColim`: the functor of points `N ↦ colim_n Mor(F_n, N)` of the
  pro-object of an inverse sequence, with the colimit over the sequence's own index category.
* `CategoryTheory.Pro.seqStage`: the class of a morphism `F_n ⟶ N` in that colimit.
* `CategoryTheory.Pro.SequentialRep`: a compatible family of levelwise morphisms, with the
  reindexing it is carried by.

## Main results

* `CategoryTheory.Pro.seqHomColimIso`: the functor of points of `ProSeq.of F` is
  `Pro.seqHomColim F`.
* `CategoryTheory.Pro.proIsoOfSeqHomColimIso`: an isomorphism of functors of points is a
  levelwise pro-isomorphism.
* `CategoryTheory.ProSeq.proIsoOfIso`: an isomorphism `ProSeq.of F ≅ ProSeq.of G` in `Pro-𝒟` is a
  levelwise pro-isomorphism, and `CategoryTheory.ProSeq.isoOfSeqHomColimIso` is the converse
  passage from an isomorphism of functors of points.
* `CategoryTheory.Pro.proIsoWhiskerRight`, `CategoryTheory.Pro.proIsoOfNatIso`,
  `CategoryTheory.Pro.proIsoTrans`: pushforward of a pro-isomorphism along a functor, the
  pro-isomorphism underlying an isomorphism of sequences, and composition.
* `CategoryTheory.Pro.isEssentiallyConstantPro_of_proIso_const`: a sequence pro-isomorphic to a
  constant sequence is an essentially constant pro-object (Stacks 05PZ).

## References

* [Stacks Project, Tag 05PX](https://stacks.math.columbia.edu/tag/05PX)
* [Stacks Project, Tag 05PZ](https://stacks.math.columbia.edu/tag/05PZ)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [-instance] CategoryTheory.Limits.instCategoryULiftHomULiftOfSmallCategory

universe v v' u u'

/-- Transition morphisms of an inverse sequence compose to a transition morphism. -/
public lemma tr_comp {D : Type u} [Category.{v} D] (F : ℕᵒᵖ ⥤ D) {a b c : ℕ}
    (h₁ : b ≤ a) (h₂ : c ≤ b) :
    InverseSequence.tr F h₁ ≫ InverseSequence.tr F h₂ = InverseSequence.tr F (h₂.trans h₁) := by
  show F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op = _
  rw [← F.map_comp]
  congr 1

namespace CategoryTheory.Pro

variable {𝒟 : Type u} [Category.{v} 𝒟]

/-- The functor of points `N ↦ colim_n Mor(F_n, N)` of the pro-object of an inverse sequence
`F : ℕᵒᵖ ⥤ 𝒟`, the colimit being taken over the index category of the sequence itself.

It is an abbreviation so that the universal property of the colimit applies to it unchanged. -/
@[sga "4 I 8.10" "partial", sga "4 IV 6.5.2" "special case"]
public abbrev seqHomColim (F : ℕᵒᵖ ⥤ 𝒟) : 𝒟 ⥤ Type v := colimit (F.op ⋙ coyoneda)

/-- The class of a morphism `f : F_n ⟶ N` in `colim_m Mor(F_m, N)`. -/
public def seqStage (F : ℕᵒᵖ ⥤ 𝒟) {N : 𝒟} {n : ℕ} (f : F.obj (op n) ⟶ N) :
    (seqHomColim F).obj N :=
  (colimit.ι (F.op ⋙ coyoneda) (op (op n))).app N f

/-- Precomposing with a transition morphism does not change the class. -/
public lemma seqStage_transition (F : ℕᵒᵖ ⥤ 𝒟) {N : 𝒟} {n m : ℕ} (h : n ≤ m)
    (f : F.obj (op n) ⟶ N) : seqStage F (InverseSequence.tr F h ≫ f) = seqStage F f := by
  have he := congrArg (fun t => t.app N) (colimit.w (F.op ⋙ coyoneda) (homOfLE h).op.op)
  exact ConcreteCategory.congr_hom he f

/-- Every class in `colim_n Mor(F_n, N)` is the class of a morphism at some stage. -/
public lemma seqStage_surjective (F : ℕᵒᵖ ⥤ 𝒟) (N : 𝒟) (x : (seqHomColim F).obj N) :
    ∃ (n : ℕ) (f : F.obj (op n) ⟶ N), x = seqStage F f := by
  obtain ⟨⟨⟨n⟩⟩, f, h⟩ := FunctorToTypes.jointly_surjective' (F.op ⋙ coyoneda) N x
  exact ⟨n, f, h⟩

/-- Two morphisms with the same class agree after precomposition with transition morphisms. -/
public lemma seqStage_eq (F : ℕᵒᵖ ⥤ 𝒟) {N : 𝒟} {n m : ℕ} (f : F.obj (op n) ⟶ N)
    (g : F.obj (op m) ⟶ N) (h : seqStage F f = seqStage F g) :
    ∃ (k : ℕ) (hn : n ≤ k) (hm : m ≤ k),
      InverseSequence.tr F hn ≫ f = InverseSequence.tr F hm ≫ g := by
  let E := colimitObjIsoColimitCompEvaluation (F.op ⋙ coyoneda) N
  have he : (((colimit.ι (F.op ⋙ coyoneda) (op (op n))).app N) ≫ E.hom) f =
      (((colimit.ι (F.op ⋙ coyoneda) (op (op m))).app N) ≫ E.hom) g :=
    congrArg E.hom h
  simp only [E, colimitObjIsoColimitCompEvaluation_ι_app_hom] at he
  obtain ⟨⟨⟨k⟩⟩, a, b, hab⟩ := Types.FilteredColimit.colimit_eq_iff _ |>.mp he
  exact ⟨k, leOfHom a.unop.unop, leOfHom b.unop.unop, hab⟩

/-- The functor of points sends `g : N ⟶ P` to postcomposition with `g`. -/
public lemma seqHomColim_map_seqStage (F : ℕᵒᵖ ⥤ 𝒟) {N P : 𝒟} {n : ℕ}
    (f : F.obj (op n) ⟶ N) (g : N ⟶ P) :
    (seqHomColim F).map g (seqStage F f) = seqStage F (f ≫ g) := by
  simpa [seqStage] using (ConcreteCategory.congr_hom
    ((colimit.ι (F.op ⋙ coyoneda) (op (op n))).naturality g) f).symm

/-- A transformation of functors of points is determined by the images of the classes of the
identities: it sends the class of `g` to the class of `f ≫ g`, where `f` represents the image of
the class of the identity. -/
public lemma transformation_seqStage {F G : ℕᵒᵖ ⥤ 𝒟} (η : seqHomColim G ⟶ seqHomColim F)
    {N : 𝒟} {n m : ℕ} (f : F.obj (op m) ⟶ G.obj (op n))
    (h : η.app _ (seqStage G (𝟙 (G.obj (op n)))) = seqStage F f) (g : G.obj (op n) ⟶ N) :
    η.app N (seqStage G g) = seqStage F (f ≫ g) := by
  have hn := ConcreteCategory.congr_hom (η.naturality g) (seqStage G (𝟙 _))
  dsimp at hn
  rwa [seqHomColim_map_seqStage, Category.id_comp, h, seqHomColim_map_seqStage] at hn

/-- A compatible family of morphisms `F_{index n} ⟶ G_n`, carried by a strictly increasing
reindexing. This is the levelwise form of a morphism of pro-objects from `F` to `G`. -/
public structure SequentialRep (F G : ℕᵒᵖ ⥤ 𝒟) where
  /-- The reindexing at which the morphism to level `n` is defined. -/
  index : ℕ → ℕ
  /-- The reindexing is strictly increasing. -/
  index_strict : StrictMono index
  /-- The reindexing increases every index. -/
  index_le : ∀ n, n ≤ index n
  /-- The levelwise morphisms. -/
  component : ∀ n, F.obj (op (index n)) ⟶ G.obj (op n)
  /-- The levelwise morphisms commute with the transition morphisms. -/
  naturality : ∀ {n m : ℕ} (h : n ≤ m),
    InverseSequence.tr F (index_strict.monotone h) ≫ component n =
      component m ≫ InverseSequence.tr G h

/-- A levelwise family *represents* a transformation of functors of points when it sends the
class of each identity to the class of the corresponding component. -/
public def SequentialRep.Represents {F G : ℕᵒᵖ ⥤ 𝒟} (r : SequentialRep F G)
    (η : seqHomColim G ⟶ seqHomColim F) : Prop :=
  ∀ n, η.app _ (seqStage G (𝟙 (G.obj (op n)))) = seqStage F (r.component n)

/-- Compatibility of a levelwise family with the successor transitions gives compatibility with
all transitions. -/
public lemma successor_naturality {F G : ℕᵒᵖ ⥤ 𝒟} (m : ℕ → ℕ) (hm : Monotone m)
    (f : ∀ n, F.obj (op (m n)) ⟶ G.obj (op n))
    (hf : ∀ n, InverseSequence.tr F (hm (Nat.le_succ n)) ≫ f n =
      f (n + 1) ≫ InverseSequence.tr G (Nat.le_succ n))
    {i j : ℕ} (h : i ≤ j) : InverseSequence.tr F (hm h) ≫ f i = f j ≫ InverseSequence.tr G h := by
  induction j, h using Nat.le_induction with
  | base => simp [InverseSequence.tr]
  | succ j h ih =>
    rw [← tr_comp F (hm (Nat.le_succ j)) (hm h), Category.assoc, ih, ← Category.assoc, hf j,
      Category.assoc, tr_comp]

/-- Every transformation of functors of points is represented by a levelwise family. The
representatives of the successive identities exist stagewise; they are made compatible by passing
to a common strictly increasing reindexing. -/
public lemma exists_sequentialRep {F G : ℕᵒᵖ ⥤ 𝒟} (η : seqHomColim G ⟶ seqHomColim F) :
    ∃ r : SequentialRep F G, r.Represents η := by
  classical
  choose p f hf using fun n => seqStage_surjective F (G.obj (op n)) (η.app _ (seqStage G (𝟙 _)))
  have hc (n : ℕ) :
      seqStage F (f n) = seqStage F (f (n + 1) ≫ InverseSequence.tr G (Nat.le_succ n)) := by
    rw [← hf n, ← transformation_seqStage η (f (n + 1)) (hf (n + 1))]
    congr 1
    simpa only [Category.comp_id] using (seqStage_transition G (Nat.le_succ n) (𝟙 _)).symm
  choose k hk hk' heq using fun n => seqStage_eq F _ _ (hc n)
  obtain ⟨m, hm, hb⟩ := StacksDraft.InverseSystem.exists_strict_majorant (fun n => max (p n) (k n))
  have hp (n : ℕ) : p n ≤ m n := (le_max_left _ _).trans (hb n)
  have hkn (n : ℕ) : k n ≤ m n := (le_max_right _ _).trans (hb n)
  let g (n : ℕ) := InverseSequence.tr F (hp n) ≫ f n
  have hg (n : ℕ) :
      InverseSequence.tr F (hm.monotone (Nat.le_succ n)) ≫ g n =
        g (n + 1) ≫ InverseSequence.tr G (Nat.le_succ n) := by
    have hn : k n ≤ m (n + 1) := (hkn n).trans (hm.monotone (Nat.le_succ n))
    have hh := congrArg (fun z => InverseSequence.tr F hn ≫ z) (heq n)
    simpa only [g, ← Category.assoc, tr_comp] using hh
  exact ⟨⟨m, hm, hm.id_le, g, fun h => successor_naturality m hm.monotone g hg h⟩,
    fun n => (hf n).trans (seqStage_transition F (hp n) (f n)).symm⟩

/-- Composition of levelwise families. -/
public def SequentialRep.comp {F G H : ℕᵒᵖ ⥤ 𝒟} (r : SequentialRep F G) (s : SequentialRep G H) :
    SequentialRep F H where
  index := r.index ∘ s.index
  index_strict := r.index_strict.comp s.index_strict
  index_le := fun n => (s.index_le n).trans (r.index_le (s.index n))
  component := fun n => r.component (s.index n) ≫ s.component n
  naturality := by
    intro n m h
    dsimp
    calc
      _ = (r.component (s.index m) ≫ InverseSequence.tr G (s.index_strict.monotone h)) ≫
          s.component n := by
            simpa only [Category.assoc] using congrArg (fun z => z ≫ s.component n)
              (r.naturality (s.index_strict.monotone h))
      _ = r.component (s.index m) ≫ (s.component m ≫ InverseSequence.tr H h) := by
            rw [Category.assoc, s.naturality h]
      _ = _ := by simp only [Category.assoc]

/-- The composition of levelwise families represents the composition of the transformations they
represent. -/
public lemma SequentialRep.comp_represents {F G H : ℕᵒᵖ ⥤ 𝒟} (r : SequentialRep F G)
    (s : SequentialRep G H) (η : seqHomColim G ⟶ seqHomColim F)
    (θ : seqHomColim H ⟶ seqHomColim G) (hr : r.Represents η) (hs : s.Represents θ) :
    (r.comp s).Represents (θ ≫ η) := by
  intro n
  show η.app _ (θ.app _ (seqStage H (𝟙 _))) = _
  rw [hs n]
  exact transformation_seqStage η (r.component (s.index n)) (hr (s.index n)) (s.component n)

/-- A levelwise family representing the identity is a transition morphism past some index. -/
public lemma eventual_identity {F : ℕᵒᵖ ⥤ 𝒟} (r : SequentialRep F F)
    (hr : r.Represents (𝟙 (seqHomColim F))) (n : ℕ) :
    ∃ k : ℕ, ∃ hk : r.index n ≤ k,
      InverseSequence.tr F hk ≫ r.component n = InverseSequence.tr F ((r.index_le n).trans hk) := by
  have he : seqStage F (r.component n) = seqStage F (𝟙 (F.obj (op n))) := by
    simpa [SequentialRep.Represents] using (hr n).symm
  obtain ⟨k, hk, hn, h⟩ := seqStage_eq F (r.component n) (𝟙 (F.obj (op n))) he
  exact ⟨k, hk, by simpa only [Category.comp_id] using h⟩

/-- An isomorphism of functors of points is a levelwise pro-isomorphism: a representative of each
direction, corrected to a common reindexing at which the two composites become transition
morphisms. -/
public def proIsoOfSeqHomColimIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : seqHomColim F ≅ seqHomColim G) :
    InverseSequence.ProIso F G := by
  classical
  let r := Classical.choose (exists_sequentialRep e.inv)
  have hr := Classical.choose_spec (exists_sequentialRep e.inv)
  let s := Classical.choose (exists_sequentialRep e.hom)
  have hs := Classical.choose_spec (exists_sequentialRep e.hom)
  have hF : (r.comp s).Represents (𝟙 (seqHomColim F)) := by
    simpa only [e.hom_inv_id] using r.comp_represents s e.inv e.hom hr hs
  have hG : (s.comp r).Represents (𝟙 (seqHomColim G)) := by
    simpa only [e.inv_hom_id] using s.comp_represents r e.hom e.inv hs hr
  choose kF hkF heF using fun n => eventual_identity (r.comp s) hF n
  choose kG hkG heG using fun n => eventual_identity (s.comp r) hG n
  let b : ℕ → ℕ := fun n => max (r.index n) (max (s.index n) (max (kF n) (kG n)))
  let a := Classical.choose (StacksDraft.InverseSystem.exists_strict_majorant b)
  have ha := (Classical.choose_spec (StacksDraft.InverseSystem.exists_strict_majorant b)).1
  have hab := (Classical.choose_spec (StacksDraft.InverseSystem.exists_strict_majorant b)).2
  have hra (n : ℕ) : r.index n ≤ a n := (le_max_left _ _).trans (hab n)
  have hsa (n : ℕ) : s.index n ≤ a n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hab n))
  have hkFa (n : ℕ) : kF n ≤ a n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hab n)))
  have hkGa (n : ℕ) : kG n ≤ a n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hab n)))
  let φ (n : ℕ) : F.obj (op (a n)) ⟶ G.obj (op n) := InverseSequence.tr F (hra n) ≫ r.component n
  let ψ (n : ℕ) : G.obj (op (a n)) ⟶ F.obj (op n) := InverseSequence.tr G (hsa n) ≫ s.component n
  have hφ {i j : ℕ} (h : i ≤ j) :
      InverseSequence.tr F (ha.monotone h) ≫ φ i = φ j ≫ InverseSequence.tr G h := by
    dsimp [φ]
    rw [← Category.assoc, tr_comp, Category.assoc, ← r.naturality h, ← Category.assoc, tr_comp]
  have hψ {i j : ℕ} (h : i ≤ j) :
      InverseSequence.tr G (ha.monotone h) ≫ ψ i = ψ j ≫ InverseSequence.tr F h := by
    dsimp [ψ]
    rw [← Category.assoc, tr_comp, Category.assoc, ← s.naturality h, ← Category.assoc, tr_comp]
  refine
    { α := a
      β := a
      αmono := ha.monotone
      βmono := ha.monotone
      αle := ha.id_le
      βle := ha.id_le
      φ := φ
      ψ := ψ
      φnat := hφ
      ψnat := hψ
      ψφ := ?_
      φψ := ?_ }
  · intro n
    have hna : s.index n ≤ a n := hsa n
    have hka : kF n ≤ a (a n) := (hkFa n).trans (ha.monotone (ha.id_le n))
    have hkFr : r.index (s.index n) ≤ kF n := hkF n
    change (InverseSequence.tr F (hra (a n)) ≫ r.component (a n)) ≫
      (InverseSequence.tr G (hsa n) ≫ s.component n) = InverseSequence.tr F _
    rw [Category.assoc,
      ← Category.assoc (r.component (a n)) (InverseSequence.tr G hna) (s.component n),
      ← r.naturality hna, ← Category.assoc, ← Category.assoc, tr_comp]
    have he := congrArg (fun t => InverseSequence.tr F hka ≫ t) (heF n)
    dsimp only [SequentialRep.comp, Function.comp_apply] at he
    rw [← Category.assoc (InverseSequence.tr F hka) (InverseSequence.tr F hkFr)
      (r.component (s.index n) ≫ s.component n), tr_comp] at he
    rw [tr_comp] at he
    simpa only [Category.assoc] using he
  · intro n
    have hna : r.index n ≤ a n := hra n
    have hka : kG n ≤ a (a n) := (hkGa n).trans (ha.monotone (ha.id_le n))
    have hkGr : s.index (r.index n) ≤ kG n := hkG n
    change (InverseSequence.tr G (hsa (a n)) ≫ s.component (a n)) ≫
      (InverseSequence.tr F (hra n) ≫ r.component n) = InverseSequence.tr G _
    rw [Category.assoc,
      ← Category.assoc (s.component (a n)) (InverseSequence.tr F hna) (r.component n),
      ← s.naturality hna, ← Category.assoc, ← Category.assoc, tr_comp]
    have he := congrArg (fun t => InverseSequence.tr G hka ≫ t) (heG n)
    dsimp only [SequentialRep.comp, Function.comp_apply] at he
    rw [← Category.assoc (InverseSequence.tr G hka) (InverseSequence.tr G hkGr)
      (s.component (r.index n) ≫ r.component n), tr_comp] at he
    rw [tr_comp] at he
    simpa only [Category.assoc] using he

/-- The functor of points of the pro-object `ProSeq.of F`, whose index category is lifted to the
morphism universe of `𝒟`, is the colimit `Pro.seqHomColim F` over the index category of the
sequence itself: the lifting is an equivalence of index categories. -/
public def seqHomColimIso (F : ℕᵒᵖ ⥤ 𝒟) :
    Pro.coyonedaColim (Pro.liftedInverseSequence F) ≅ seqHomColim F :=
  HasColimit.isoOfEquivalence (ULiftHomULiftCategory.equiv ℕᵒᵖ).symm.op (Iso.refl _)

end CategoryTheory.Pro

namespace CategoryTheory.Pro

open CategoryTheory.Limits Opposite

/-- A pro-isomorphism pushes forward along any functor. -/
public def proIsoWhiskerRight {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟]
    {F G : ℕᵒᵖ ⥤ 𝒞} (e : InverseSequence.ProIso F G) (H : 𝒞 ⥤ 𝒟) :
    InverseSequence.ProIso (F ⋙ H) (G ⋙ H) where
  α := e.α
  β := e.β
  αmono := e.αmono
  βmono := e.βmono
  αle := e.αle
  βle := e.βle
  φ n := H.map (e.φ n)
  ψ n := H.map (e.ψ n)
  φnat h := by
    change H.map (InverseSequence.tr F (e.αmono h)) ≫ H.map (e.φ _) =
      H.map (e.φ _) ≫ H.map (InverseSequence.tr G h)
    rw [← H.map_comp, e.φnat h, H.map_comp]
  ψnat h := by
    change H.map (InverseSequence.tr G (e.βmono h)) ≫ H.map (e.ψ _) =
      H.map (e.ψ _) ≫ H.map (InverseSequence.tr F h)
    rw [← H.map_comp, e.ψnat h, H.map_comp]
  ψφ n := by rw [← H.map_comp, e.ψφ n]; rfl
  φψ n := by rw [← H.map_comp, e.φψ n]; rfl

/-- An isomorphism of inverse sequences is in particular a pro-isomorphism. -/
public def proIsoOfNatIso {𝒞 : Type u} [Category.{v} 𝒞] {F G : ℕᵒᵖ ⥤ 𝒞} (e : F ≅ G) :
    InverseSequence.ProIso F G where
  α := id
  β := id
  αmono := monotone_id
  βmono := monotone_id
  αle := fun _ => le_rfl
  βle := fun _ => le_rfl
  φ n := (e.app (op n)).hom
  ψ n := (e.app (op n)).inv
  φnat h := by simp [InverseSequence.tr]
  ψnat h := by simp [InverseSequence.tr]
  ψφ n := by simp [InverseSequence.tr]
  φψ n := by simp [InverseSequence.tr]

/-- Pro-isomorphisms compose. -/
public def proIsoTrans {𝒞 : Type u} [Category.{v} 𝒞] {F G H : ℕᵒᵖ ⥤ 𝒞}
    (p : InverseSequence.ProIso F G) (q : InverseSequence.ProIso G H) :
    InverseSequence.ProIso F H where
  α n := p.α (q.α n)
  β n := q.β (p.β n)
  αmono := fun _ _ h => p.αmono (q.αmono h)
  βmono := fun _ _ h => q.βmono (p.βmono h)
  αle n := (q.αle n).trans (p.αle (q.α n))
  βle n := (p.βle n).trans (q.βle (p.β n))
  φ n := p.φ (q.α n) ≫ q.φ n
  ψ n := q.ψ (p.β n) ≫ p.ψ n
  φnat := by
    intro m m' h
    calc
      _ = (InverseSequence.tr F (p.αmono (q.αmono h)) ≫ p.φ (q.α m)) ≫ q.φ m := by
            simp [Category.assoc]
      _ = (p.φ (q.α m') ≫ InverseSequence.tr G (q.αmono h)) ≫ q.φ m := by
            rw [p.φnat (m := q.α m) (m' := q.α m') (q.αmono h)]
      _ = p.φ (q.α m') ≫ (InverseSequence.tr G (q.αmono h) ≫ q.φ m) := by simp [Category.assoc]
      _ = p.φ (q.α m') ≫ (q.φ m' ≫ InverseSequence.tr H h) := by rw [q.φnat (m := m) (m' := m') h]
      _ = _ := by simp [Category.assoc]
  ψnat := by
    intro m m' h
    calc
      _ = (InverseSequence.tr H (q.βmono (p.βmono h)) ≫ q.ψ (p.β m)) ≫ p.ψ m := by
            simp [Category.assoc]
      _ = (q.ψ (p.β m') ≫ InverseSequence.tr G (p.βmono h)) ≫ p.ψ m := by
            rw [q.ψnat (m := p.β m) (m' := p.β m') (p.βmono h)]
      _ = q.ψ (p.β m') ≫ (InverseSequence.tr G (p.βmono h) ≫ p.ψ m) := by simp [Category.assoc]
      _ = q.ψ (p.β m') ≫ (p.ψ m' ≫ InverseSequence.tr F h) := by rw [p.ψnat (m := m) (m' := m') h]
      _ = _ := by simp [Category.assoc]
  ψφ := by
    intro m
    have hq : p.β m ≤ q.α (q.β (p.β m)) := (q.βle (p.β m)).trans (q.αle (q.β (p.β m)))
    calc
      _ = p.φ (q.α (q.β (p.β m))) ≫ (q.φ (q.β (p.β m)) ≫ q.ψ (p.β m)) ≫ p.ψ m := by
            simp [Category.assoc]
      _ = p.φ (q.α (q.β (p.β m))) ≫ InverseSequence.tr G hq ≫ p.ψ m := by rw [q.ψφ (p.β m)]
      _ = InverseSequence.tr F (p.αmono hq) ≫ p.φ (p.β m) ≫ p.ψ m := by
            rw [reassoc_of% (p.φnat (m := p.β m) (m' := q.α (q.β (p.β m))) hq).symm]
      _ = InverseSequence.tr F (p.αmono hq) ≫
          InverseSequence.tr F (le_trans (p.βle m) (p.αle (p.β m))) := by
            simpa [Category.assoc] using
              congrArg (fun f => InverseSequence.tr F (p.αmono hq) ≫ f) (p.ψφ m)
      _ = InverseSequence.tr F ((le_trans (p.βle m) (p.αle (p.β m))).trans (p.αmono hq)) := by
            rw [tr_comp]
  φψ := by
    intro m
    have hp : q.α m ≤ p.β (p.α (q.α m)) := (p.αle (q.α m)).trans (p.βle (p.α (q.α m)))
    calc
      _ = q.ψ (p.β (p.α (q.α m))) ≫ (p.ψ (p.α (q.α m)) ≫ p.φ (q.α m)) ≫ q.φ m := by
            simp [Category.assoc]
      _ = q.ψ (p.β (p.α (q.α m))) ≫ InverseSequence.tr G hp ≫ q.φ m := by rw [p.φψ (q.α m)]
      _ = InverseSequence.tr H (q.βmono hp) ≫ q.ψ (q.α m) ≫ q.φ m := by
            rw [reassoc_of% (q.ψnat (m := q.α m) (m' := p.β (p.α (q.α m))) hp).symm]
      _ = InverseSequence.tr H (q.βmono hp) ≫
          InverseSequence.tr H (le_trans (q.αle m) (q.βle (q.α m))) := by
            simpa [Category.assoc] using
              congrArg (fun f => InverseSequence.tr H (q.βmono hp) ≫ f) (q.φψ m)
      _ = InverseSequence.tr H ((le_trans (q.αle m) (q.βle (q.α m))).trans (q.βmono hp)) := by
            rw [tr_comp]

/-- **Stacks 05PZ.** An inverse sequence pro-isomorphic to a constant sequence is an essentially
constant pro-object: the maps to the constant value assemble into a cone, which is witnessed at
the index `α 0`. -/
public lemma isEssentiallyConstantPro_of_proIso_const {𝒞 : Type u} [Category.{v} 𝒞]
    {F : ℕᵒᵖ ⥤ 𝒞} {A : 𝒞} (e : InverseSequence.ProIso F ((Functor.const ℕᵒᵖ).obj A)) :
    CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro F := by
  let c : Cone F :=
    { pt := A
      π :=
        { app := fun i => e.ψ i.unop
          naturality := by
            intro i j f
            cases i with
            | op n =>
              cases j with
              | op m =>
                have h : m ≤ n := leOfHom f.unop
                have hf : f = (homOfLE h).op := by subsingleton
                subst hf
                simpa [InverseSequence.tr] using e.ψnat h } }
  refine ⟨c, op (e.α 0), e.φ 0, ?_, ?_⟩
  · show e.ψ (e.α 0) ≫ e.φ 0 = 𝟙 A
    simpa [InverseSequence.tr] using e.φψ 0
  · intro j
    cases j with
    | op n =>
      have hni : n ≤ e.α (e.β n) := (e.βle n).trans (e.αle (e.β n))
      have hii : e.α 0 ≤ e.α (e.β n) := e.αmono (Nat.zero_le _)
      refine ⟨op (e.α (e.β n)), (homOfLE hii).op, (homOfLE hni).op, ?_⟩
      have hφ : InverseSequence.tr F hii ≫ e.φ 0 = e.φ (e.β n) := by
        simpa [InverseSequence.tr] using e.φnat (m := 0) (m' := e.β n) (Nat.zero_le _)
      show InverseSequence.tr F hni = InverseSequence.tr F hii ≫ e.φ 0 ≫ e.ψ n
      rw [reassoc_of% hφ, e.ψφ n]

end CategoryTheory.Pro

namespace CategoryTheory.ProSeq

open CategoryTheory.Limits Opposite

variable {𝒟 : Type u} [Category.{v} 𝒟]

/-- An isomorphism of the pro-objects of two inverse sequences is a levelwise
pro-isomorphism. -/
public def proIsoOfIso {F G : ℕᵒᵖ ⥤ 𝒟} (i : ProSeq.of F ≅ ProSeq.of G) :
    InverseSequence.ProIso F G :=
  Pro.proIsoOfSeqHomColimIso
    ((Pro.seqHomColimIso F).symm ≪≫
      ((IsSequentialProObject 𝒟).ι.mapIso i.unop).symm ≪≫ Pro.seqHomColimIso G)

/-- An isomorphism of functors of points is an isomorphism of pro-objects: `ProSeq` is a full
subcategory of `𝒟 ⥤ Type v` opposite. -/
public def isoOfSeqHomColimIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : Pro.seqHomColim F ≅ Pro.seqHomColim G) :
    ProSeq.of F ≅ ProSeq.of G :=
  (ObjectProperty.isoMk _
    (Pro.seqHomColimIso F ≪≫ e ≪≫ (Pro.seqHomColimIso G).symm)).op.symm

end CategoryTheory.ProSeq

end
