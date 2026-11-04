module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived colimits with their coprojections

Let `D` be a pre-triangulated category and let `(Kₙ, fₙ)` be a system of objects of `D`, that is
a functor `F : ℕ ⥤ D`, whose direct sum `∐ Kₙ` exists. A *derived colimit datum* for the system
is an object `K` of `D` together with morphisms `iₙ : Kₙ ⟶ K` satisfying `iₙ₊₁ ∘ fₙ = iₙ` and a
morphism `c : K ⟶ (∐ Kₙ)⟦1⟧` such that
$$ \bigoplus K_n \xrightarrow{1 - f_n} \bigoplus K_n \xrightarrow{(i_n)} K \xrightarrow{c}
   \bigoplus K_n[1] $$
is a distinguished triangle, where the second map is the one the universal property of the direct
sum attaches to the family `(iₙ)`. Two derived colimit data for one system are isomorphic by an
isomorphism matching the coprojections and the morphism `c`.

This is the refinement of `CategoryTheory.Pretriangulated.IsHomotopyColimit` — Definition 090Z,
which quantifies the two outer maps of the triangle away — that *names* them. It is what a
consumer needs in order to say which cone a derived-colimit presentation carries: nothing can be
pinned to the structural map of an existential.

## Main definitions

* `CategoryTheory.Pretriangulated.IsHomotopyColimitWithCoprojections`: the data `(K, iₙ, c)` is
  a derived colimit datum for the system `F : ℕ ⥤ D`.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_of_isHomotopyColimitWithCoprojections`: two derived
  colimit data for one system are isomorphic, compatibly with the coprojections and with `c`.
* `CategoryTheory.Pretriangulated.exists_isHomotopyColimitWithCoprojections`: a derived colimit
  datum exists as soon as the direct sum does.
* `CategoryTheory.Pretriangulated.IsHomotopyColimit.exists_coprojections`: a derived colimit in
  the sense of Definition 090Z carries a derived colimit datum, so the refinement is a refinement
  of the *presentation* and not of the class of objects presented.

## Implementation notes

The cone condition `iₙ₊₁ ∘ fₙ = iₙ` is a consequence of the triangle being distinguished — it is
the composite of its first two maps being zero, read on the `n`-th summand — but it is part of
the source's description of the data, so it is part of the definition here and
`CategoryTheory.Pretriangulated.isHomotopyColimitWithCoprojections_of_distTriang` builds a datum
from the triangle alone.

The first map of the triangle is spelled exactly as in
`CategoryTheory.Pretriangulated.IsHomotopyColimit`, so that forgetting the named maps is
`⟨_, _, h.mem_distTriang⟩` and no comparison of two spellings of `1 - fₙ` is ever needed.

Uniqueness is only up to a *non-unique* isomorphism: TR3 produces the comparison from the
identity on the two copies of the direct sum, and nothing pins it. That is why the conclusion is
an existential and why no `hocolim` notation is introduced. The comparison is an isomorphism by
the five lemma for distinguished triangles, `isIso₃_of_isIso₁₂` of Lemma 13.4.3.

Only `Pretriangulated D` is assumed although the source says triangulated: the statement mentions
the distinguished triangles and the additive structure, never the octahedron axiom.

Dually, a derived limit with its projections named is
`NoetherianAdicCompletion.IsDerivedLimitWithProjections`.

## References

* [Stacks Project, Tag 0CRH](https://stacks.math.columbia.edu/tag/0CRH) (Remark 13.33.2)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A) (Lemma 13.4.3)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open Limits

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A derived colimit datum for a system of objects**, [Stacks, Tag 0CRH]: an object `K` of a
pre-triangulated category `D` endowed with morphisms `iₙ : Kₙ ⟶ K` out of the terms of a system
`F : ℕ ⥤ D` whose direct sum exists, satisfying `iₙ₊₁ ∘ fₙ = iₙ` for the transition maps
`fₙ = F.map (homOfLE (Nat.le_succ n))`, together with a morphism `c : K ⟶ (∐ Kₙ)⟦1⟧` making
`∐ Kₙ ⟶ ∐ Kₙ ⟶ K ⟶ (∐ Kₙ)⟦1⟧` a distinguished triangle, where the first map is `1 - fₙ` on the
`n`-th summand and the second is `Sigma.desc i`.

This is `CategoryTheory.Pretriangulated.IsHomotopyColimit` with the two maps the latter
existentially quantifies named. -/
public def IsHomotopyColimitWithCoprojections (F : ℕ ⥤ D) [HasCoproduct F.obj] (K : D)
    (i : ∀ n : ℕ, F.obj n ⟶ K) (c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧) : Prop :=
  (∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)) ≫ i (n + 1) = i n) ∧
    Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) (Sigma.desc i) c ∈ distTriang D

namespace IsHomotopyColimitWithCoprojections

variable {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D} {i : ∀ n : ℕ, F.obj n ⟶ K}
  {c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}

/-- The defining distinguished triangle of a derived colimit datum. -/
theorem mem_distTriang (h : IsHomotopyColimitWithCoprojections F K i c) :
    Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) (Sigma.desc i) c ∈
      distTriang D :=
  h.2

/-- **The coprojections of a derived colimit datum form a cocone on the system.** -/
theorem map_comp_ι (h : IsHomotopyColimitWithCoprojections F K i c) (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫ i (n + 1) = i n :=
  h.1 n

/-- Forgetting the coprojections and the morphism to the shifted direct sum gives the predicate
of Definition 090Z. -/
theorem isHomotopyColimit (h : IsHomotopyColimitWithCoprojections F K i c) :
    IsHomotopyColimit F K :=
  ⟨Sigma.desc i, c, h.mem_distTriang⟩

end IsHomotopyColimitWithCoprojections

/-- The cocone condition on the coprojections is automatic: it is the composite of the first two
maps of the defining triangle being zero, read on the `n`-th summand. So a derived colimit datum
is produced by the distinguished triangle alone. -/
theorem isHomotopyColimitWithCoprojections_of_distTriang {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    (i : ∀ n : ℕ, F.obj n ⟶ K) (c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) (Sigma.desc i) c ∈
      distTriang D) :
    IsHomotopyColimitWithCoprojections F K i c := by
  refine ⟨fun n ↦ ?_, hT⟩
  have hz := comp_distTriang_mor_zero₁₂ _ hT
  have hz' := congrArg (fun f ↦ Sigma.ι F.obj n ≫ f) hz
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, comp_zero] at hz'
  rw [← Category.assoc, Sigma.ι_desc, Preadditive.sub_comp, Category.assoc, Sigma.ι_desc,
    Sigma.ι_desc] at hz'
  exact (sub_eq_zero.mp hz').symm

/-- A distinguished triangle on `p : ∐ Kₙ ⟶ K` gives the datum with coprojections `ι ≫ p`. -/
private theorem isHomotopyColimitWithCoprojections_of_distTriang_comp {F : ℕ ⥤ D}
    [HasCoproduct F.obj] {K : D} (p : (∐ F.obj) ⟶ K) (c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) p c ∈ distTriang D) :
    IsHomotopyColimitWithCoprojections F K (fun n ↦ Sigma.ι F.obj n ≫ p) c := by
  refine isHomotopyColimitWithCoprojections_of_distTriang _ _ ?_
  rwa [show (Sigma.desc fun n ↦ Sigma.ι F.obj n ≫ p) = p from
    Sigma.hom_ext _ _ fun n ↦ Sigma.ι_desc _ _]

/-- **A derived colimit datum exists as soon as the direct sum of the system does.** Completing
the difference map `1 - fₙ` to a distinguished triangle (TR1) gives an object with a structural
map, and its coprojections are the composites of the coprojections of the direct sum with that
map. -/
theorem exists_isHomotopyColimitWithCoprojections (F : ℕ ⥤ D) [HasCoproduct F.obj] :
    ∃ (K : D) (i : ∀ n : ℕ, F.obj n ⟶ K) (c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧),
      IsHomotopyColimitWithCoprojections F K i c := by
  obtain ⟨K, p, c, hT⟩ := distinguished_cocone_triangle
    (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1))
  exact ⟨K, _, c, isHomotopyColimitWithCoprojections_of_distTriang_comp _ _ hT⟩

/-- **A derived colimit in the sense of Definition 090Z carries a derived colimit datum.** The
coprojections are the composites of the coprojections of the direct sum with the structural map
of the defining triangle. -/
theorem IsHomotopyColimit.exists_coprojections {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    (h : IsHomotopyColimit F K) :
    ∃ (i : ∀ n : ℕ, F.obj n ⟶ K) (c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧),
      IsHomotopyColimitWithCoprojections F K i c := by
  obtain ⟨p, c, hT⟩ := h
  exact ⟨_, c, isHomotopyColimitWithCoprojections_of_distTriang_comp _ _ hT⟩

/-- **[Stacks, Tag 0CRH]: a derived colimit datum is unique up to a compatible isomorphism.**
Let `(Kₙ, fₙ)` be a system of objects of a pre-triangulated category whose direct sum exists, and
let `(K, iₙ, c)` and `(K', i'ₙ, c')` be two derived colimit data for it: objects endowed with
coprojections satisfying `iₙ₊₁ ∘ fₙ = iₙ` and with a morphism to `(∐ Kₙ)⟦1⟧` completing
`∐ Kₙ --(1 - fₙ)--> ∐ Kₙ --(iₙ)--> · --c-->` to a distinguished triangle. Then there is an
isomorphism `φ : K ≅ K'` with `φ ∘ iₙ = i'ₙ` for every `n` and `c' ∘ φ = c`.

The existence of a morphism `φ` completing the identity of the first two terms to a morphism of
the two triangles is TR3, and that it is invertible is the five lemma for distinguished triangles
(Lemma 13.4.3). The isomorphism is not unique: nothing pins the completion TR3 produces. -/
@[stacks 0CRH]
theorem exists_iso_of_isHomotopyColimitWithCoprojections {F : ℕ ⥤ D} [HasCoproduct F.obj]
    {K : D} {i : ∀ n : ℕ, F.obj n ⟶ K} {c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    (h : IsHomotopyColimitWithCoprojections F K i c)
    {K' : D} {i' : ∀ n : ℕ, F.obj n ⟶ K'} {c' : K' ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    (h' : IsHomotopyColimitWithCoprojections F K' i' c') :
    ∃ φ : K ≅ K', (∀ n : ℕ, i n ≫ φ.hom = i' n) ∧ φ.hom ≫ c' = c := by
  obtain ⟨ψ, hψ₂, hψ₃⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk _ (Sigma.desc i) c) (Triangle.mk _ (Sigma.desc i') c')
    h.mem_distTriang h'.mem_distTriang (𝟙 _) (𝟙 _) (by simp)
  have hdesc : Sigma.desc i ≫ ψ = Sigma.desc i' := by
    simpa only [Triangle.mk_mor₂, Category.id_comp] using hψ₂
  have hc : ψ ≫ c' = c := by
    refine Eq.symm ?_
    simpa only [Triangle.mk_mor₃, CategoryTheory.Functor.map_id, Category.comp_id] using hψ₃
  have hiso : IsIso ψ :=
    isIso₃_of_isIso₁₂
      (Triangle.homMk (Triangle.mk _ (Sigma.desc i) c) (Triangle.mk _ (Sigma.desc i') c')
        (𝟙 _) (𝟙 _) ψ (by simp) hψ₂ hψ₃)
      h.mem_distTriang h'.mem_distTriang
      (by simp only [Triangle.homMk_hom₁]; infer_instance)
      (by simp only [Triangle.homMk_hom₂]; infer_instance)
  refine ⟨@asIso _ _ _ _ ψ hiso, fun n ↦ ?_, hc⟩
  calc i n ≫ ψ = (Sigma.ι F.obj n ≫ Sigma.desc i) ≫ ψ := by rw [Sigma.ι_desc]
    _ = Sigma.ι F.obj n ≫ Sigma.desc i' := by rw [Category.assoc, hdesc]
    _ = i' n := Sigma.ι_desc _ _

/-! ### Transport -/

/-- **A derived colimit datum is carried along by a pointwise identification of its
coprojections.** The predicate depends on the family of coprojections only through its values, so
a family agreeing with one at every level is again a family of coprojections for the same
object and the same morphism to the shifted direct sum.

This is what a consumer needing the coprojections in a *particular* spelling applies: the datum
produced by composing the constructions — `IsHomotopyColimitWithCoprojections.of_iso` after
[Stacks, Tag 0949] — carries the coprojections in the shape its construction leaves them, and
the identification with the canonical maps is a chase that is easier to run one level at a time
than inside the `CategoryTheory.Limits.Sigma.desc` of the defining triangle. -/
theorem IsHomotopyColimitWithCoprojections.of_eq_coprojections {F : ℕ ⥤ D} [HasCoproduct F.obj]
    {K : D} {i : ∀ n : ℕ, F.obj n ⟶ K} {c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    (h : IsHomotopyColimitWithCoprojections F K i c) {i' : ∀ n : ℕ, F.obj n ⟶ K}
    (hi : ∀ n : ℕ, i n = i' n) : IsHomotopyColimitWithCoprojections F K i' c := by
  have hfam : i = i' := funext hi
  subst hfam
  exact h

/-- **A derived colimit datum transports along an isomorphism of the object.** -/
theorem IsHomotopyColimitWithCoprojections.of_iso {F : ℕ ⥤ D} [HasCoproduct F.obj]
    {K : D} {i : ∀ n : ℕ, F.obj n ⟶ K} {c : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    (h : IsHomotopyColimitWithCoprojections F K i c) {K' : D} (e : K ≅ K') :
    IsHomotopyColimitWithCoprojections F K' (fun n ↦ i n ≫ e.hom) (e.inv ≫ c) := by
  refine isHomotopyColimitWithCoprojections_of_distTriang _ _ ?_
  have hlift : (Sigma.desc fun n ↦ i n ≫ e.hom) = Sigma.desc i ≫ e.hom := by
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    rw [Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc]
  rw [hlift]
  refine isomorphic_distinguished _ h.mem_distTriang _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_)
  · dsimp
    rw [Category.comp_id, Category.id_comp]
  · dsimp
    rw [Category.id_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
  · dsimp
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end CategoryTheory.Pretriangulated

end
