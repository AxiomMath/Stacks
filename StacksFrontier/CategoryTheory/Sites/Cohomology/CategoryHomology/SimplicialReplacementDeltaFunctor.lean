module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacement
import StacksCore.Tactic.StacksAttribute

/-!
# The homology δ-functor of the simplicial replacement

Let `C` be a small category. The simplicial replacement `K_•(F)` of an abelian-group-valued
presheaf `F` on `C`, built as `Stacks.CategoryHomology.simplicialReplacementComplex`, is
functorial in `F`: a morphism `η : F ⟶ G` acts on `⨁_{Uₙ → ⋯ → U₀} F(U₀)` as the direct sum of
the components of `η`. Because a direct sum of exact sequences of abelian groups is exact, this
functor carries a short exact sequence of presheaves to a degreewise short exact sequence of
chain complexes, hence to a short exact sequence of complexes. Its homology functors therefore
come with the connecting maps of the associated long exact sequence, and those data form a
homological δ-functor — the first half of Stacks 08PG's computation of `H_n(C, -)`.

The chaotic topology on `C` is the bottom Grothendieck topology, for which every presheaf is a
sheaf; `CategoryTheory.sheafBotEquivalence` identifies abelian sheaves for it with
abelian-group-valued presheaves, and the sheaf-level functor below is the presheaf-level one
transported along that equivalence.

## Main definitions

* `Stacks.CategoryHomology.HomologicalDeltaFunctor`: a δ-functor with *homological* connecting
  maps `Fₙ₊₁(X₃) ⟶ Fₙ(X₁)`, indexed by `ℕ`.
* `Stacks.CategoryHomology.replacementGroupMap`: the degreewise map on replacement groups
  induced by a morphism of presheaves.
* `Stacks.CategoryHomology.simplicialReplacementComplexFunctor` and
  `replacementComplexFunctor`: the simplicial replacement complex as a functor on presheaves,
  bundled with its prescribed value on objects and on morphisms.
* `Stacks.CategoryHomology.chaoticAbSheafEquivalence` and
  `chaoticSheafReplacementComplexFunctor`: the same functor on abelian sheaves for the chaotic
  topology.

## Main results

* `Stacks.CategoryHomology.replacementGroupMap_of`: the computation rule for
  `replacementGroupMap` on a generator, the companion of `replacementMap_on_generator`.
* `Stacks.CategoryHomology.simplicialReplacementComplexFunctor_map_shortExact`: the functor
  preserves short exact sequences.
* `Stacks.CategoryHomology.simplicialReplacementHomologyDeltaFunctor`: its homology functors,
  with the natural connecting maps, form a homological δ-functor whose degree-`n` functor is
  homology in degree `n`.
* `Stacks.CategoryHomology.directSum_exact`: a direct sum of exact sequences of abelian groups
  is exact — the one computation the exactness statement rests on.

## Implementation notes

**Why a new δ-functor notion.** `CategoryTheory.DeltaFunctor` of
`StacksCore/CategoryTheory/Abelian/DeltaFunctor/Basic.lean` is Stacks 010Q, which is
*cohomological*: its connecting maps go `Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)`. The source here takes homology of
chain complexes, so the connecting maps go the other way, and `HomologicalDeltaFunctor` records
that version. It is not a weakening: every clause of 010Q has its counterpart, with
`epi_map_g` in place of 010Q's `mono_map_f` as the degree-`0` end of the long exact sequence.

**Which clause of the tag this file carries.** Stacks 08PG's covering set is four parts: the
simplicial replacement complex itself (`Stacks.CategoryHomology.simplicialReplacementComplex`),
this δ-functor, the identification of the replacement of `j_{U!}ℤ_U` with the free chains on the
nerve of `C/U` (`Stacks.CategoryHomology.representableReplacementComplexIsoFreeNerve`), and the
acyclicity that makes the δ-functor universal. All four are in the library, so the tag is
carried, split by note across them; `simplicialReplacementHomologyDeltaFunctor` states
this file's clause, and the two results it rests on — functoriality and preservation of short
exact sequences — are its inputs rather than separate clauses.

**Rewriting through the replacement.** Nothing here unfolds `replacementMap`. Doing so leaves a
term in which `SimplexCategory.toCat.obj Δ` has to be read as `Fin (Δ.len + 1)` with
`Preorder.smallCategory`, which is true only definitionally and not at the transparency a
rewrite motive is built at. Instead every computation goes through
`replacementMap_on_generator` and its companion `replacementGroupMap_of`, with their arguments
given explicitly so that no unification has to identify `(x.whiskerLeft θ).right` with
`x.obj (θ.obj (Fin.last _))`. `simplicialReplacement_map` is the bridge that lets a rewrite see
the `map` field of the structure instance at all.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public section

open CategoryTheory

universe u v u' v'

namespace Stacks.CategoryHomology


/-- A homological delta-functor indexed by `ℕ`: additive functors together with natural
connecting morphisms such that the resulting homology sequence is exact. -/
structure HomologicalDeltaFunctor
    (A : Type u) [Category.{v} A] [Preadditive A]
    (B : Type u') [Category.{v'} B] [Preadditive B] where
  /-- The functor in homological degree `n`. -/
  functor : ℕ → A ⥤ B
  /-- Every functor in the family is additive. -/
  [additive : ∀ n, (functor n).Additive]
  /-- The connecting map associated to a short exact sequence. -/
  δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
    (functor (n + 1)).obj S.X₃ ⟶ (functor n).obj S.X₁
  /-- The map into a connecting map composes to zero. -/
  map_g_δ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    (functor (n + 1)).map S.g ≫ δ hS n = 0
  /-- A connecting map followed by the next map composes to zero. -/
  δ_map_f : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    δ hS n ≫ (functor n).map S.f = 0
  /-- The degree-zero functor carries the final map of a short exact sequence to an
  epimorphism, giving exactness at the terminal term of the homological long exact
  sequence. -/
  epi_map_g : ∀ {S : ShortComplex A}, S.ShortExact → Epi ((functor 0).map S.g)
  /-- Each three-term sequence in a fixed degree is exact. -/
  exact_map : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
    (S.map (functor n)).Exact
  /-- Exactness at `Fⁿ⁺¹(X₃)` in the long homology sequence. -/
  exact_δ₁ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((functor (n + 1)).map S.g) (δ hS n) (map_g_δ hS n)).Exact
  /-- Exactness at `Fⁿ(X₁)` in the long homology sequence. -/
  exact_δ₂ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk (δ hS n) ((functor n).map S.f) (δ_map_f hS n)).Exact
  /-- Connecting maps are natural in morphisms of short exact sequences. -/
  δ_naturality : ∀ {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ),
    (functor (n + 1)).map φ.τ₃ ≫ δ hT n = δ hS n ≫ (functor n).map φ.τ₁

variable {C : Type u} [SmallCategory C]

/-- The degreewise map on simplicial replacement groups induced by a morphism of presheaves. -/
noncomputable def replacementGroupMap
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (η : F ⟶ G) (n : ℕ) :
    replacementGroup F n ⟶
      replacementGroup G n :=
  AddCommGrpCat.ofHom <| DirectSum.map fun x => (η.app (Opposite.op x.right)).hom

/-- The simplicial operator of `simplicialReplacement` is `replacementMap`, by definition.
Stated as a lemma because `simplicialReplacement` is a structure instance, so a rewrite cannot
see through its `map` field. -/
lemma simplicialReplacement_map (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) {Δ Γ : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Γ) : (simplicialReplacement F).map f = replacementMap F f := rfl

/-- The value of `replacementGroupMap` on the generator of the summand indexed by `x`: it is
the component of `η` at `x.right`, in the same summand. This is the computation rule for
`replacementGroupMap`, the companion of `replacementMap_on_generator`. -/
lemma replacementGroupMap_of {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (η : F ⟶ G) (n : ℕ)
    (x : ComposableArrows C n) (a : F.obj (Opposite.op x.right)) :
    replacementGroupMap η n ((@DirectSum.of (ComposableArrows C n)
        (fun z => F.obj (Opposite.op z.right)) _ (Classical.decEq _) x) a) =
      (@DirectSum.of (ComposableArrows C n)
        (fun z => G.obj (Opposite.op z.right)) _ (Classical.decEq _) x)
        ((η.app (Opposite.op x.right)) a) := by
  classical
  show (DirectSum.map fun z => (η.app (Opposite.op z.right)).hom)
    (DirectSum.of (fun z : ComposableArrows C n => F.obj (Opposite.op z.right)) x a) = _
  rw [DirectSum.map_of]

/-- **Stacks Project, Tag 08PG (functoriality).** The functor from
abelian-group-valued presheaves to their simplicial replacement chain complexes, together
with its prescribed value on every object. -/
noncomputable def simplicialReplacementComplexFunctor :
    { K : (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ ChainComplex AddCommGrpCat.{max u v} ℕ //
      (∀ F, K.obj F =
        simplicialReplacementComplex F) ∧
      (∀ {F G} (η : F ⟶ G) (n : ℕ)
          (hF : K.obj F =
            simplicialReplacementComplex F)
          (hG : K.obj G =
            simplicialReplacementComplex G),
        eqToHom (congrArg (fun L => L.X n) hF.symm) ≫ (K.map η).f n ≫
          eqToHom (congrArg (fun L => L.X n) hG) = replacementGroupMap η n) ∧
      K.Additive } := by
  classical
  let smap : ∀ {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}}, (F ⟶ G) →
      (simplicialReplacement F ⟶
        simplicialReplacement G) :=
    fun {F G} η ↦
    { app := fun Δ ↦ replacementGroupMap η Δ.unop.len
      naturality := by
        classical
        intro Δ Γ f
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext'
        intro x
        apply AddMonoidHom.ext
        intro a
        simp only [AddMonoidHom.comp_apply, ConcreteCategory.comp_apply]
        rw [simplicialReplacement_map, simplicialReplacement_map,
          replacementMap_on_generator F f x a,
          replacementGroupMap_of η Γ.unop.len (x.whiskerLeft (simplexIndexMap f.unop))
            ((F.map (Opposite.op (x.map (homOfLE (Fin.le_last _))))) a),
          replacementGroupMap_of η Δ.unop.len x a,
          replacementMap_on_generator G f x ((η.app (Opposite.op x.right)) a)]
        refine congrArg _ ?_
        let k : Fin (Δ.unop.len + 1) := (simplexIndexMap f.unop).obj (Fin.last Γ.unop.len)
        have h := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
          (η.naturality (Opposite.op (x.map (homOfLE (Fin.le_last k)))))) a
        rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
        change (η.app (Opposite.op (x.obj k))).hom
            ((F.map (Opposite.op (x.map (homOfLE (Fin.le_last k))))).hom a) =
          (G.map (Opposite.op (x.map (homOfLE (Fin.le_last k))))).hom
            ((η.app (Opposite.op x.right)).hom a)
        exact h }
  let K : (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ ChainComplex AddCommGrpCat.{max u v} ℕ :=
    { obj := fun F ↦
        simplicialReplacementComplex F
      map := fun η ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map (smap η)
      map_id := by
        intro F
        ext n x
        change (DirectSum.map (fun _ ↦ AddMonoidHom.id _)) x = x
        rw [DirectSum.map_id]
        rfl
      map_comp := by
        intro F G H η θ
        ext n x
        simp [smap, replacementGroupMap] }
  refine ⟨K, fun F ↦ rfl, ?_, ?_⟩
  · intro F G η n hF hG
    change (smap η).app (Opposite.op { len := n }) = _
    rfl
  · constructor
    intro F G η θ
    ext n x
    change (DirectSum.map (fun i ↦ (η.app (Opposite.op i.right)).hom +
        (θ.app (Opposite.op i.right)).hom)) x =
      (DirectSum.map (fun i ↦ (η.app (Opposite.op i.right)).hom)) x +
        (DirectSum.map (fun i ↦ (θ.app (Opposite.op i.right)).hom)) x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [DirectSum.map_of, DirectSum.map_of, DirectSum.map_of,
        AddMonoidHom.add_apply, map_add]
    | add x y hx hy => simp only [map_add, hx, hy]; ac_rfl

/-- The underlying simplicial replacement complex functor. -/
noncomputable abbrev replacementComplexFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ ChainComplex AddCommGrpCat.{max u v} ℕ :=
  (simplicialReplacementComplexFunctor (C := C)).1

/-- The simplicial replacement complex functor is additive. -/
noncomputable instance : (replacementComplexFunctor (C := C)).Additive :=
  (simplicialReplacementComplexFunctor (C := C)).property.2.2

/-- Abelian sheaves on the chaotic site, displayed as presheaves by the canonical
equivalence. -/
noncomputable def chaoticAbSheafEquivalence :
    Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{v} ≌
      Cᵒᵖ ⥤ AddCommGrpCat.{v} := by
  rw [GrothendieckTopology.trivial_eq_bot]
  exact CategoryTheory.sheafBotEquivalence AddCommGrpCat.{v}

/-- The simplicial replacement complex functor on abelian sheaves for the chaotic topology.
It is the explicitly specified presheaf functor transported along the canonical equivalence. -/
noncomputable abbrev chaoticSheafReplacementComplexFunctor :
    Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{v} ⥤
      ChainComplex AddCommGrpCat.{max u v} ℕ :=
  (chaoticAbSheafEquivalence (C := C)).functor ⋙ replacementComplexFunctor (C := C)

/-- A direct sum of exact sequences `A i → B i → D i` of abelian groups is exact. -/
theorem directSum_exact {ι : Type*} {A B D : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (D i)]
    (f : ∀ i, A i →+ B i) (g : ∀ i, B i →+ D i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.map f) (DirectSum.map g) := by
  have hi : ∀ i, (f i).range = (g i).ker := fun i ↦ AddSubgroup.ext fun y ↦ (h i y).symm
  intro y
  show y ∈ (DirectSum.map g).ker ↔ y ∈ (DirectSum.map f).range
  rw [DirectSum.ker_map, DirectSum.range_map]
  simp only [hi]

/-- **Stacks Project, Tag 08PG (exactness).** The simplicial replacement complex functor
sends short exact sequences of abelian sheaves on the chaotic site to short exact sequences
of complexes. -/
theorem simplicialReplacementComplexFunctor_map_shortExact
    {S : ShortComplex (Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{v})}
    (hS : S.ShortExact) :
    (S.map (chaoticSheafReplacementComplexFunctor (C := C))).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let E := (chaoticAbSheafEquivalence (C := C)).functor
  have hcomp (i : ComposableArrows C n) :
      ((S.map E).map ((evaluation Cᵒᵖ AddCommGrpCat).obj (Opposite.op i.right))).ShortExact :=
    (hS.map_of_exact E).map_of_exact _
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · show (ShortComplex.mk (replacementGroupMap (E.map S.f) n)
      (replacementGroupMap (E.map S.g) n) _).Exact
    rw [ShortComplex.ab_exact_iff_function_exact]
    exact directSum_exact _ _ fun i ↦
      (ShortComplex.ab_exact_iff_function_exact _).1 (hcomp i).exact
  · rw [AddCommGrpCat.mono_iff_injective]
    exact (DirectSum.map_injective _).2 fun i ↦
      (AddCommGrpCat.mono_iff_injective _).1 (hcomp i).mono_f
  · rw [AddCommGrpCat.epi_iff_surjective]
    exact (DirectSum.map_surjective _).2 fun i ↦
      (AddCommGrpCat.epi_iff_surjective _).1 (hcomp i).epi_g

/-- **Stacks Project, Tag 08PG (delta-functor).** Homology of the simplicial replacement,
with the natural connecting maps of degreewise short exact sequences, is a homological
delta-functor.  Its functor in degree `n` is exactly homology in degree `n`. -/
@[stacks 08PG "delta_functor"]
noncomputable def simplicialReplacementHomologyDeltaFunctor :
    { D : HomologicalDeltaFunctor
        (Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{v})
        AddCommGrpCat.{max u v} //
      ∀ n, D.functor n = chaoticSheafReplacementComplexFunctor (C := C) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.down ℕ) n } :=
  by
    let build (K : Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{v} ⥤
        ChainComplex AddCommGrpCat.{max u v} ℕ) [K.Additive]
        (hK : ∀ {S : ShortComplex
          (Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{v})},
          S.ShortExact → (S.map K).ShortExact) :
        HomologicalDeltaFunctor
          (Sheaf (GrothendieckTopology.trivial C) AddCommGrpCat.{v})
          AddCommGrpCat.{max u v} := by
      refine {
        functor := fun n ↦ K ⋙ HomologicalComplex.homologyFunctor _ _ n
        additive := fun n ↦ inferInstance
        δ := fun hS n ↦ (hK hS).δ (n + 1) n rfl
        map_g_δ := fun hS n ↦ (hK hS).comp_δ (n + 1) n rfl
        δ_map_f := fun hS n ↦ (hK hS).δ_comp (n + 1) n rfl
        epi_map_g := ?_
        exact_map := fun hS n ↦ (hK hS).homology_exact₂ n
        exact_δ₁ := fun hS n ↦ (hK hS).homology_exact₃ (n + 1) n rfl
        exact_δ₂ := fun hS n ↦ (hK hS).homology_exact₁ (n + 1) n rfl
        δ_naturality := fun hS hT φ n ↦
          (HomologicalComplex.HomologySequence.δ_naturality
            (K.mapShortComplex.map φ) (hK hS) (hK hT) (n + 1) n rfl).symm
      }
      intro S hS
      let : Epi ((K.map S.g).f 0) :=
        ((hK hS).map_of_exact (HomologicalComplex.eval _ _ 0)).epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (K.map S.g) 0
        (by intro j; simp)
    let : (chaoticAbSheafEquivalence.{u, v} (C := C)).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    let : (chaoticSheafReplacementComplexFunctor (C := C)).Additive := by
      dsimp only [chaoticSheafReplacementComplexFunctor]
      infer_instance
    exact ⟨build _ (fun hS ↦ simplicialReplacementComplexFunctor_map_shortExact hS),
      fun n ↦ rfl⟩

end Stacks.CategoryHomology
