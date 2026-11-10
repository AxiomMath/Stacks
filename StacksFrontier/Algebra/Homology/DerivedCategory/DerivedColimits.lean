module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.CountableCoproducts
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived colimits: a homological functor, a compact object, termwise colimits, subsequences

Let `D` be a pre-triangulated category and let `(Kₙ, fₙ)` be a system of objects of `D`, that is a
functor `F : ℕ ⥤ D`, whose direct sum `∐ Kₙ` exists. Recall (Definition 090Z,
`CategoryTheory.Pretriangulated.IsHomotopyColimit`) that `K` is a *derived colimit*, or homotopy
colimit, of the system when there is a distinguished triangle
`∐ Kₙ --(1 - fₙ)--> ∐ Kₙ --p--> K --q--> (∐ Kₙ)⟦1⟧`, and that the coprojections of such a `K` are
the maps `iₙ = σₙ ≫ p`, where `σₙ` is the `n`-th coprojection of the direct sum.

This file proves that a derived colimit is computed as an ordinary colimit by any functor that
commutes with countable direct sums and is exact in the triangulated sense:
$$ H(\operatorname{hocolim} K_n) = \operatorname{colim} H(K_n) $$
for `H : D ⥤ A` homological into an abelian category with exact colimits over `ℕ`, hence in
particular
$$ \operatorname{colim} \operatorname{Hom}(K, L_n) = \operatorname{Hom}(K, \operatorname{hocolim}
L_n) $$
for an object `K` whose corepresentable functor commutes with countable direct sums — a compact
object, for instance. Both are proved by applying `H` to the defining triangle and to its two
rotations, which gives the five-term exact sequence
`⊕ H Kₙ --(1 - H fₙ)--> ⊕ H Kₙ --H p--> H K --H q--> ⊕ H (Kₙ⟦1⟧) --(1 - H (fₙ⟦1⟧))--> ⊕ H (Kₙ⟦1⟧)`;
its last map is a monomorphism by Lemma 093W, so `H q = 0`, `H p` is an epimorphism, and `H p`
exhibits `H K` as the cokernel of `1 - H fₙ`, which is `colim H Kₙ` by Lemma 093W again.

Finally, over an abelian category `A` in which colimits over `ℕ` exist and are exact, the derived
colimit of a system of cochain complexes is computed by the termwise colimit: the image
`Q (colim Lₙ)` of `colimit L` under the localization functor `Q : C(A) ⥤ D(A)` is a derived colimit
of the system `Q Lₙ` in the derived category. Here the short exact sequence of complexes
`0 → ⊕ Lₙ → ⊕ Lₙ → colim Lₙ → 0` of Lemma 093W gives a distinguished triangle in `D(A)` (Lemma
0152), and the termwise direct sums are direct sums in `D(A)` by Lemma 0A5L, which turns that
triangle into the one Definition 090Z asks for.

Lastly, a derived colimit is unchanged by passage to a subsequence. Write the system as
`(K m, f m)` and let `n 0 < n 1 < n 2 < ⋯` be a strictly increasing sequence of indices; the
subsystem `(K (n i), g i)` has transition maps the composites
`g i = f (n (i + 1) - 1) ∘ ⋯ ∘ f (n i)`. If both direct sums `⊕ K m` and `⊕ K (n i)` exist, `K` is
a derived colimit of the system with structure map `p` and `K'` is one of the subsystem with
structure map `p'`, then the two derived colimits agree: there is an isomorphism `e : K' ≅ K`, i.e.
`hocolim K (n i) ⟶ hocolim K m`, compatible with the coprojections out of the members of the
subsystem, in that `K (n i) ⟶ K' ⟶ K` equals `K (n i) ⟶ K` for every `i`.

Following the source, the two defining distinguished triangles are compared by two morphisms of
the underlying two-term complexes, in both directions:

* the natural inclusion `∐ K (n i) ⟶ ∐ K m` together with the map whose `i`-th component is the
  telescope `K (n i) ⟶ K (n i) ⊕ ⋯ ⊕ K (n (i + 1) - 1)` of transition maps;
* the map whose `m`-th component is the transition map `K m ⟶ K (n (idx m))` into the first
  member of the subsequence at or beyond `m`, together with the natural projection, whose `m`-th
  component is the coprojection of `K m` if `m` is a member of the subsequence and zero otherwise.

One composite is the identity on the nose; the other differs from the identity by the boundary of
the telescope homotopy `-(K m ⟶ K m ⊕ ⋯ ⊕ K (n (idx m) - 1))`. TR3 turns the two comparisons into
morphisms `e : K' ⟶ K` and `e' : K ⟶ K'`, and both composites `e ≫ e'` and `e' ≫ e` are then
identities on the second and third maps of the respective triangle. Such an endomorphism of the
third object of a distinguished triangle differs from the identity by a square-zero endomorphism,
hence is invertible; so `e ≫ e'` and `e' ≫ e` are isomorphisms and therefore so is `e`.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_colimit_of_isHomotopyColimit`: a homological functor
  commuting with countable direct sums carries a derived colimit to a colimit.
* `CategoryTheory.Pretriangulated.exists_iso_colimit_preadditiveCoyoneda_of_isHomotopyColimit`:
  the case of the additive corepresentable functor `Hom(K, -)`.
* `DerivedCategory.isHomotopyColimit_Q_obj_colimit`: the image of the termwise colimit of a system
  of complexes is a derived colimit of the system in the derived category.
* `CategoryTheory.Pretriangulated.exists_iso_of_isHomotopyColimit_of_strictMono`: a derived
  colimit of the subsystem indexed by a strictly increasing `n : ℕ → ℕ` is isomorphic to a
  derived colimit of the whole system, by an isomorphism commuting with the coprojections.

## Implementation notes

The statements about a functor and about a subsequence spell out the defining distinguished
triangle of a derived colimit rather than citing `IsHomotopyColimit F K`, because their
conclusions pin the coprojections
`iₙ = Sigma.ι F.obj n ≫ p`, which are built from the structure map `p` that the predicate
quantifies away. Nothing is lost: `IsHomotopyColimit F K` is exactly `∃ p q, hK`. Likewise the
source's equality `H K = colim H Kₙ` is stated as the existence of an isomorphism matching the
coprojections; that isomorphism is unique, since a map out of `colimit (F ⋙ H)` is determined by
its composites with the `colimit.ι`, so the existential form says exactly that the canonical map
`colim H Kₙ ⟶ H K` is invertible, without having to name the cocone whose compatibility is itself
a consequence of the triangle.

"Countable direct sums" is read as `ℕ`-indexed ones: exactness of colimits over `ℕ` in `A` is
`HasExactColimitsOfShape ℕ A`, and a functor commuting with countable direct sums is
`PreservesColimitsOfShape (Discrete ℕ) H`. Only the direct sum of the system at hand is assumed to
exist, in place of the source's blanket "having countable direct sums"; the direct sums of the
shifted family, which the proofs use, exist because the shift is an equivalence. Only a
pre-triangulated category is assumed, although the source says triangulated: the statements
mention the distinguished triangles and the additive structure, and never the octahedron axiom.

For `Hom(K, -)` it is the *additive* corepresentable functor
`preadditiveCoyoneda.obj (Opposite.op K) : D ⥤ AddCommGrpCat` that is used: the coproduct of the
morphism *sets* in `Type` is their disjoint union, so morphism sets would give the wrong statement.
Its homologicity is Lemma 0149, already an instance in Mathlib. The one hypothesis of the general
statement that instance search does not supply for `AddCommGrpCat.{v}` is exactness of colimits
over `ℕ`: AB5 holds there for shapes in `Type v` while `ℕ` lives in `Type 0`, so the size of the
shape has to be lowered first, which is `hasExactColimitsOfShape_addCommGrpCat`.

For the termwise colimit, `colimit L` is the source's `colim Lₙ`: colimits of complexes are
computed degreewise, so no separate degreewise construction is needed, and the choice of colimit
is immaterial because the conclusion is invariant under isomorphism. Lemma 0A5L enters as
`derivedCategory_Q_preservesCoproductsOfShape`, preservation of countable coproducts by `Q`,
rather than as an `IsColimit` for the termwise cofan: in that form Mathlib's `sigmaComparison` API
supplies the identification `∐ Q Kⱼ ≅ Q (∐ Kⱼ)` together with its compatibility with the
coprojections, so no cocone transport is needed. What the source's hypothesis on `A` — colimits
over `ℕ` exist and are exact — gives is that countable direct sums exist and are exact, which is
what 0A5L consumes; that implication is
`hasExactCountableDirectSums_of_hasExactColimitsOfShape_nat` below.

The subsystem indexed by `n` is the composite `hn.monotone.functor ⋙ F`, whose object at `i` is
`F.obj (n i)` and whose transition map at `i` is `F.map (homOfLE (hn.monotone (Nat.le_succ i)))`:
because `ℕ` is a poset category, that single morphism *is* the source's composite
`g i = f (n (i + 1) - 1) ∘ ⋯ ∘ f (n i)`, so no separate datum is needed. The source indexes the
sequence from `1`; here it is indexed from `0`. Strict monotonicity of `n : ℕ → ℕ` gives `i ≤ n i`,
hence that the subsequence is cofinal, which is what makes the two derived colimits agree; no
separate cofinality hypothesis is imposed. The conclusion is stated summand by summand, as the
source's square is; it is equivalent, by `Limits.Sigma.hom_ext`, to the single equation
`p' ≫ e.hom = Limits.Sigma.desc (fun i ↦ Limits.Sigma.ι F.obj (n i)) ≫ p`, saying that `e` is
compatible with the natural inclusion `⊕ K (n i) ⟶ ⊕ K m`, which is the map `a` of the source's
proof.

The index `Stacks.DerivedColimit.Subsequence.idx hn m` is the least `i` with `m ≤ n i`; it is the
  source's `i` in
`n_{i - 1} < m ≤ n_i`, and the source's case distinction "`m` is or is not a member of the
subsequence" is `n (idx hn m) = m` or not. The telescope `Stacks.DerivedColimit.Subsequence.tele F
  m c : K m ⟶ ∐ K m`, the
sum of the coprojections of `K m, …, K (m + c - 1)` composed after the transition maps out of
`K m`, is defined by recursion on the length `c` rather than as a sum over an interval: the
recursion makes both the identity
`tele F m c ≫ (1 - f) = ι m - (K m ⟶ K (m + c)) ≫ ι (m + c)` and the splitting off of the first
coprojection definitional, and it keeps the endpoint `m + c` out of dependent positions.

The step of the proof of Lemma 0CRJ that the source leaves to the reader, "`id - ψ ∘ φ` has square
zero by Lemma 05QP", is `Stacks.DerivedColimit.Subsequence.isIso_of_mor₂_comp_eq`, proved from the
  exactness of
`Hom(-, W)` on a distinguished triangle: an endomorphism `γ` of the third object with
`mor₂ ≫ γ = mor₂` and `γ ≫ mor₃ = mor₃` has `γ - 1` factoring through `mor₃` and killed by
`mor₃`, hence `(γ - 1) ^ 2 = 0`.

## References

* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK) (Lemma 13.33.7).
* [Stacks Project, Tag 094A](https://stacks.math.columbia.edu/tag/094A) (Lemma 13.33.8), deduced
  there from Tags 0149 and 0CRK.
* [Stacks Project, Tag 0949](https://stacks.math.columbia.edu/tag/0949) (Lemma 13.33.8); Tags
  090Z, 093W, 0A5L and 0152 are the ingredients of its proof.
* [Stacks Project, Tag 0CRJ](https://stacks.math.columbia.edu/tag/0CRJ) (Lemma 13.33.4); Tags
  090Z, 014A and 05QP are the ingredients of its proof.
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

/-! ### Coproducts, comparison maps and the map `1 - f`

Facts about a functor and a coproduct that Mathlib does not record, used below to move `IsIso` and
`Mono` across a coproduct and to compare the map `1 - fₙ` of a system with that of its image
system.
-/

section Sigma

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- `Limits.ι_comp_sigmaComparison` for a family of the form `(F ⋙ G).obj`. -/
private lemma ι_comp_sigmaComparison' (F : ℕ ⥤ C) [HasCoproduct F.obj] (G : C ⥤ D)
    [HasColimitsOfShape (Discrete ℕ) D] (n : ℕ) :
    Sigma.ι (F ⋙ G).obj n ≫ sigmaComparison G F.obj = G.map (Sigma.ι F.obj n) :=
  ι_comp_sigmaComparison G F.obj n

end Sigma

section OneSubShift

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]

/-- `Stacks.CountableCoproducts.oneSubShift_comp_sigmaComparison` with the map of the image system
written as `Stacks.CountableCoproducts.oneSubShift (F ⋙ G)`; it is the same morphism. -/
private lemma oneSubShift_comp_sigmaComparison' (G : C ⥤ D) [G.Additive] (F : ℕ ⥤ C)
    [HasCoproduct F.obj] [HasColimitsOfShape (Discrete ℕ) D] :
    Stacks.CountableCoproducts.oneSubShift (F ⋙ G) ≫ sigmaComparison G F.obj
      = sigmaComparison G F.obj ≫ G.map (Stacks.CountableCoproducts.oneSubShift F) :=
  Stacks.CountableCoproducts.oneSubShift_comp_sigmaComparison G F

/-- `G (1 - f)` is conjugate, along the comparison isomorphism, to the map `1 - f` of the image
system `n ↦ G (Kₙ)`. -/
private lemma map_oneSubShift_eq (F : ℕ ⥤ C) [HasCoproduct F.obj] (G : C ⥤ D) [G.Additive]
    [HasColimitsOfShape (Discrete ℕ) D] [PreservesColimitsOfShape (Discrete ℕ) G] :
    G.map (Stacks.CountableCoproducts.oneSubShift F) = inv (sigmaComparison G F.obj) ≫
      Stacks.CountableCoproducts.oneSubShift (F ⋙ G) ≫ sigmaComparison G F.obj := by
  rw [oneSubShift_comp_sigmaComparison']
  simp

end OneSubShift

/-- If `G` is additive and commutes with countable direct sums, then `G (1 - f)` is a
monomorphism, by Lemma 093W applied to the image system `n ↦ G (Kₙ)`. -/
private lemma mono_map_oneSubShift {C : Type*} [Category C] [Preadditive C] {D : Type*}
    [Category D] [Abelian D] [HasColimitsOfShape ℕ D] [HasColimitsOfShape (Discrete ℕ) D]
    (hexact : PreservesFiniteLimits (colim : (ℕ ⥤ D) ⥤ D)) (F : ℕ ⥤ C) [HasCoproduct F.obj]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfShape (Discrete ℕ) G] :
    Mono (G.map (Stacks.CountableCoproducts.oneSubShift F)) := by
  have : Mono (Stacks.CountableCoproducts.oneSubShift (F ⋙ G)) :=
    Stacks.CountableCoproducts.mono_oneSubShift hexact _
  rw [map_oneSubShift_eq]
  infer_instance

end CategoryTheory

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

section Homological

variable {A : Type u'} [Category.{v'} A] [Abelian A] [HasColimitsOfShape ℕ A]
  [HasExactColimitsOfShape ℕ A]

/-- **Stacks 0CRK**. Let `F : ℕ ⥤ D` be a system of objects `K n = F.obj n` of a pre-triangulated
category whose direct sum `∐ K n` exists, let `A` be an abelian category in which colimits over
`ℕ` exist and are exact, and let `H : D ⥤ A` be a homological functor commuting with countable
direct sums. If `K` is a derived colimit of the system with structure map `p : ∐ K n ⟶ K`
(Definition 090Z), then `H K = colim H (K n)`: there is an isomorphism
`e : colim H (K n) ≅ H K` such that for every `n` the `n`-th coprojection of the colimit followed
by `e` is `H` applied to the coprojection `K n ⟶ K` of the derived colimit. -/
@[stacks 0CRK]
public theorem exists_iso_colimit_of_isHomotopyColimit
    (F : ℕ ⥤ D) [HasCoproduct F.obj] (H : D ⥤ A) [H.IsHomological]
    [PreservesColimitsOfShape (Discrete ℕ) H]
    {K : D} (p : ∐ F.obj ⟶ K) (q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hK : Triangle.mk (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι F.obj n -
        F.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F.obj (n + 1)) p q ∈ distTriang D) :
    ∃ e : colimit (F ⋙ H) ≅ H.obj K, ∀ n : ℕ,
      colimit.ι (F ⋙ H) n ≫ e.hom = H.map (Limits.Sigma.ι F.obj n ≫ p) := by
  have : HasColimitsOfShape (Discrete ℕ) A :=
    Stacks.CountableCoproducts.hasColimitsOfShape_discrete_of_hasColimitsOfShape_nat
  have hexact : PreservesFiniteLimits (colim : (ℕ ⥤ A) ⥤ A) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  replace hK : Triangle.mk (Stacks.CountableCoproducts.oneSubShift F) p q ∈ distTriang D := hK
  have h₁₂ : Stacks.CountableCoproducts.oneSubShift F ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hK
  have h₂₃ : p ≫ q = 0 := comp_distTriang_mor_zero₂₃ _ hK
  have h₃₁ : q ≫ (Stacks.CountableCoproducts.oneSubShift F)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hK
  -- The five-term exact sequence obtained by applying `H` to the triangle and its two rotations.
  have hex : (ShortComplex.mk (H.map (Stacks.CountableCoproducts.oneSubShift F)) (H.map p)
      (by rw [← H.map_comp, h₁₂, H.map_zero])).Exact :=
    H.map_distinguished_exact _ hK
  have hex₂ : (ShortComplex.mk (H.map p) (H.map q)
      (by rw [← H.map_comp, h₂₃, H.map_zero])).Exact :=
    H.map_distinguished_exact _ (rot_of_distTriang _ hK)
  have hex₃ : (ShortComplex.mk (H.map q) (H.map (-((Stacks.CountableCoproducts.oneSubShift F)⟦(1 :
    ℤ)⟧')))
      (by rw [← H.map_comp, Preadditive.comp_neg, h₃₁, neg_zero, H.map_zero])).Exact :=
    H.map_distinguished_exact _ (rot_of_distTriang _ (rot_of_distTriang _ hK))
  -- The last map is a monomorphism, by Lemma 093W for the system `n ↦ H ((K n)⟦1⟧)`, so `H q = 0`
  -- and `H p` is an epimorphism presenting `H K` as the cokernel of `1 - H f`.
  have hq : H.map q = 0 := by
    have : Mono (H.map ((Stacks.CountableCoproducts.oneSubShift F)⟦(1 : ℤ)⟧')) :=
      mono_map_oneSubShift hexact F (shiftFunctor D (1 : ℤ) ⋙ H)
    refine hex₃.mono_g_iff.1 ?_
    change Mono (H.map (-((Stacks.CountableCoproducts.oneSubShift F)⟦(1 : ℤ)⟧')))
    rw [H.map_neg]
    infer_instance
  have : Epi (H.map p) := hex₂.epi_f hq
  obtain ⟨w, hSE⟩ := Stacks.CountableCoproducts.shortExact_oneSubShift_piMap hexact (F ⋙ H)
  have : Epi (Stacks.CountableCoproducts.piMap (F ⋙ H)) := hSE.epi_g
  -- The two presentations of `H K` and of `colim H (K n)` as cokernels of `1 - H f`, each
  -- factored through the other; the factorizations are inverse because both maps cancel.
  obtain ⟨α, hα⟩ := hSE.exact.desc' (sigmaComparison H F.obj ≫ H.map p) (by
    rw [← Category.assoc, oneSubShift_comp_sigmaComparison', Category.assoc, ← H.map_comp, h₁₂,
      H.map_zero, comp_zero])
  obtain ⟨β, hβ⟩ := hex.desc' (inv (sigmaComparison H F.obj) ≫ Stacks.CountableCoproducts.piMap (F ⋙
    H)) (by
    change H.map (Stacks.CountableCoproducts.oneSubShift F) ≫ inv (sigmaComparison H F.obj) ≫ _ = 0
    rw [map_oneSubShift_eq]
    simp [w])
  refine ⟨⟨α, β, ?_, ?_⟩, fun n ↦ ?_⟩
  · refine (cancel_epi (Stacks.CountableCoproducts.piMap (F ⋙ H))).1 ?_
    rw [Category.comp_id, ← Category.assoc, hα, Category.assoc, hβ]
    simp
  · refine (cancel_epi (H.map p)).1 ?_
    rw [Category.comp_id, ← Category.assoc, hβ, Category.assoc, hα]
    simp
  · rw [← Stacks.CountableCoproducts.ι_piMap, Category.assoc, hα, ← Category.assoc,
    ι_comp_sigmaComparison',
      ← H.map_comp]

end Homological

/-- Colimits over a small filtered category are exact in `AddCommGrpCat.{v}`.

Mathlib's AB5 instance for `AddCommGrpCat.{v}` serves shapes in `Type v`
(`AB5OfSize.{v, v} AddCommGrpCat.{v}`), and a category with exact filtered colimits of one size
has them for every smaller size (`AB5OfSize_of_univLE`); here the shape `J` is in `Type 0`. -/
@[sga "3 I 3.1.1" "special case", sga "6 II 3.1" "special case"]
private lemma hasExactColimitsOfShape_addCommGrpCat (J : Type) [SmallCategory J] [IsFiltered J] :
    HasExactColimitsOfShape J AddCommGrpCat.{v} :=
  (AB5OfSize_of_univLE.{0, 0, v, v} AddCommGrpCat.{v}).ofShape J

/-- **Stacks 094A**. Let `F : ℕ ⥤ D` be a system of objects `L n = F.obj n` of a pre-triangulated
category whose direct sum `∐ L n` exists, and let `K` be an object of `D` such that
`Hom(K, -) = preadditiveCoyoneda.obj (Opposite.op K)` commutes with countable direct sums, i.e.
for every countable family `E : ℕ → D` the canonical map `⨁ (K ⟶ E n) ⟶ (K ⟶ ∐ E)` is bijective.
If `L` is a derived colimit of the system with structure map `p : ∐ L n ⟶ L` (Definition 090Z),
then `Hom(K, L) = colim Hom(K, L n)`: there is an isomorphism of abelian groups
`e : colim Hom(K, L n) ≅ Hom(K, L)` such that for every `n` the `n`-th coprojection of the colimit
followed by `e` is composition with the coprojection `L n ⟶ L` of the derived colimit.

This is Lemma 0CRK for the homological functor `H = Hom(K, -)`. -/
@[stacks 094A]
public theorem exists_iso_colimit_preadditiveCoyoneda_of_isHomotopyColimit
    (F : ℕ ⥤ D) [HasCoproduct F.obj] (K : D)
    [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (Opposite.op K))]
    {L : D} (p : ∐ F.obj ⟶ L) (q : L ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hL : Triangle.mk (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι F.obj n -
        F.map (homOfLE (Nat.le_succ n)) ≫ Limits.Sigma.ι F.obj (n + 1)) p q ∈ distTriang D) :
    ∃ e : colimit (F ⋙ preadditiveCoyoneda.obj (Opposite.op K)) ≅
        (preadditiveCoyoneda.obj (Opposite.op K)).obj L, ∀ n : ℕ,
      colimit.ι (F ⋙ preadditiveCoyoneda.obj (Opposite.op K)) n ≫ e.hom =
        (preadditiveCoyoneda.obj (Opposite.op K)).map (Limits.Sigma.ι F.obj n ≫ p) :=
  have : HasExactColimitsOfShape ℕ AddCommGrpCat.{v} :=
    hasExactColimitsOfShape_addCommGrpCat ℕ
  exists_iso_colimit_of_isHomotopyColimit F (preadditiveCoyoneda.obj (Opposite.op K)) p q hL

end CategoryTheory.Pretriangulated

/-! ### From exact colimits over `ℕ` to the hypothesis of Lemma 0A5L -/

namespace ExactCountableDirectSums

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- If colimits over `ℕ` exist in `A`, then countable direct sums exist: a countable coproduct is
the sequential colimit of the finite subsums. -/
private theorem hasCountableCoproducts_of_hasColimitsOfShape_nat [HasColimitsOfShape ℕ A] :
    HasCountableCoproducts A := by
  refine ⟨fun J _ => ?_⟩
  have : HasColimitsOfShape (Finset (Discrete J)) A :=
    Functor.Final.hasColimitsOfShape_of_final
      (IsFiltered.sequentialFunctor (Finset (Discrete J)))
  exact ⟨fun F => HasColimit.mk (CoproductsFromFiniteFiltered.liftToFinsetColimitCocone F)⟩

/-- If colimits over `ℕ` exist and are exact in `A`, then countable direct sums exist and are
exact, which is the hypothesis Lemma 0A5L consumes. -/
private theorem hasExactCountableDirectSums_of_hasExactColimitsOfShape_nat
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] :
    HasExactCountableDirectSums A := by
  have hc : HasCountableCoproducts A := hasCountableCoproducts_of_hasColimitsOfShape_nat A
  have : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  have := CountableAB4.of_countableAB5 A
  exact ⟨hc, fun J _ => ⟨inferInstance, inferInstance⟩⟩

end ExactCountableDirectSums

open ExactCountableDirectSums in
/-- **Stacks 0949**. Let `A` be an abelian category in which colimits over `ℕ` exist and are
exact, and let `L : ℕ ⥤ CochainComplex A ℤ` be a system of complexes of `A`. Then the image
under `Q : CochainComplex A ℤ ⥤ D(A)` of the termwise colimit `colimit L` is a derived colimit
(homotopy colimit, Definition 090Z) of the system `L ⋙ Q` in `D(A)`, **with the images of the
colimit coprojections `Lₙ ⟶ colim Lₙ` as its coprojections**: the second map of the defining
triangle is the image of the canonical `⊕ Lₙ ⟶ colim Lₙ`, whose restriction to the `n`-th
summand is the coprojection of the colimit. -/
public theorem DerivedCategory.isHomotopyColimitWith_Q_obj_colimit {A : Type u} [Category.{v} A]
    [Abelian A] [HasDerivedCategory.{w} A] [HasColimitsOfShape ℕ A]
    [HasExactColimitsOfShape ℕ A] (L : ℕ ⥤ CochainComplex A ℤ)
    [HasCoproduct (L ⋙ DerivedCategory.Q).obj] :
    IsHomotopyColimitWith (L ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj (colimit L))
      (fun n ↦ DerivedCategory.Q.map (colimit.ι L n)) := by
  have hA : HasExactCountableDirectSums A :=
    hasExactCountableDirectSums_of_hasExactColimitsOfShape_nat A
  have : HasCountableCoproducts A := hA.hasCoproducts
  have : HasCoproduct fun n => DerivedCategory.Q.obj (L.obj n) :=
    ‹HasCoproduct (L ⋙ DerivedCategory.Q).obj›
  have := derivedCategory_Q_preservesCoproductsOfShape A hA ℕ
  -- The short exact sequence `0 → ⊕ Lₙ → ⊕ Lₙ → colim Lₙ → 0` of complexes (Lemma 093W, applied
  -- in the abelian category of complexes, where colimits are computed termwise).
  obtain ⟨w, hSE⟩ := Stacks.CountableCoproducts.shortExact_oneSubShift_piMap
    (A := CochainComplex A ℤ) inferInstance L
  -- `Q (⊕ Lₙ)` is the direct sum of the `Q Lₙ` in `D(A)` (Lemma 0A5L): the comparison map is an
  -- isomorphism, compatible with the coprojections by `ι_comp_sigmaComparison`.
  set e := asIso (sigmaComparison (DerivedCategory.Q (C := A)) L.obj)
  -- Transport the distinguished triangle of the short exact sequence along that identification.
  refine ⟨e.hom ≫ DerivedCategory.Q.map (Stacks.CountableCoproducts.piMap L),
    DerivedCategory.triangleOfSESδ hSE ≫
      (shiftFunctor (DerivedCategory A) (1 : ℤ)).map e.inv, ?_, fun n ↦ ?_⟩
  · refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hSE) _
      (Triangle.isoMk _ _ e e (Iso.refl _) ?_ ?_ ?_)
    · exact Stacks.CountableCoproducts.oneSubShift_comp_sigmaComparison DerivedCategory.Q L
    · exact Category.comp_id _
    · exact (by rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] :
          (DerivedCategory.triangleOfSESδ hSE ≫
              (shiftFunctor (DerivedCategory A) (1 : ℤ)).map e.inv) ≫
            (shiftFunctor (DerivedCategory A) (1 : ℤ)).map e.hom
              = 𝟙 (DerivedCategory.Q.obj (colimit L)) ≫ DerivedCategory.triangleOfSESδ hSE)
  · have hι : Sigma.ι (L ⋙ DerivedCategory.Q).obj n ≫
        sigmaComparison (DerivedCategory.Q (C := A)) L.obj =
        DerivedCategory.Q.map (Sigma.ι L.obj n) :=
      ι_comp_sigmaComparison (DerivedCategory.Q (C := A)) L.obj n
    rw [← Category.assoc, show e.hom = sigmaComparison (DerivedCategory.Q (C := A)) L.obj from rfl,
      hι, ← Functor.map_comp, Stacks.CountableCoproducts.ι_piMap]

open ExactCountableDirectSums in
/-- **Stacks 0949**. Let `A` be an abelian category in which colimits over `ℕ` exist and are
exact, and let `L : ℕ ⥤ CochainComplex A ℤ` be a system of complexes of `A`. Then the image
under `Q : CochainComplex A ℤ ⥤ D(A)` of the termwise colimit `colimit L` is a derived colimit
(homotopy colimit, Definition 090Z) of the system `L ⋙ Q` in `D(A)`. -/
@[stacks 0949]
public theorem DerivedCategory.isHomotopyColimit_Q_obj_colimit {A : Type u} [Category.{v} A]
    [Abelian A] [HasDerivedCategory.{w} A] [HasColimitsOfShape ℕ A]
    [HasExactColimitsOfShape ℕ A] (L : ℕ ⥤ CochainComplex A ℤ)
    [HasCoproduct (L ⋙ DerivedCategory.Q).obj] :
    IsHomotopyColimit (L ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj (colimit L)) :=
  (DerivedCategory.isHomotopyColimitWith_Q_obj_colimit L).isHomotopyColimit

/-! ### Functoriality of derived colimits -/

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- The endomorphism `1 - shift` of the coproduct of a sequential system is natural in the
system. -/
private lemma oneSubShift_naturality {F G : ℕ ⥤ D} [HasCoproduct F.obj]
    [HasCoproduct G.obj] (a : F ⟶ G) :
    Stacks.CountableCoproducts.oneSubShift F ≫ Limits.Sigma.map (fun n ↦ a.app n) =
      Limits.Sigma.map (fun n ↦ a.app n) ≫ Stacks.CountableCoproducts.oneSubShift G := by
  ext n
  conv_lhs =>
    rw [← Category.assoc, Stacks.CountableCoproducts.ι_oneSubShift, Preadditive.sub_comp,
      Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_map]
  conv_rhs =>
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc,
      Stacks.CountableCoproducts.ι_oneSubShift, Preadditive.comp_sub]
  rw [← Category.assoc, a.naturality]
  rw [Category.assoc]

/-- **Stacks 0CRI.** A morphism of sequential systems induces a morphism between chosen
homotopy colimits. It commutes with every canonical coprojection and completes the morphism of
the two defining distinguished triangles. -/
@[stacks 0CRI]
public theorem exists_hom_of_isHomotopyColimit {F G : ℕ ⥤ D} [HasCoproduct F.obj]
    [HasCoproduct G.obj] (a : F ⟶ G) {K L : D}
    (p : ∐ F.obj ⟶ K) (q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hK : Triangle.mk (Stacks.CountableCoproducts.oneSubShift F) p q ∈ distTriang D)
    (p' : ∐ G.obj ⟶ L) (q' : L ⟶ (∐ G.obj)⟦(1 : ℤ)⟧)
    (hL : Triangle.mk (Stacks.CountableCoproducts.oneSubShift G) p' q' ∈ distTriang D) :
    ∃ b : K ⟶ L,
      (∀ n : ℕ, Sigma.ι F.obj n ≫ p ≫ b = a.app n ≫ Sigma.ι G.obj n ≫ p') ∧
      b ≫ q' = q ≫ (Limits.Sigma.map (fun n ↦ a.app n))⟦(1 : ℤ)⟧' := by
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism
    (Triangle.mk (Stacks.CountableCoproducts.oneSubShift F) p q)
    (Triangle.mk (Stacks.CountableCoproducts.oneSubShift G) p' q') hK hL
    (Limits.Sigma.map (fun n ↦ a.app n)) (Limits.Sigma.map (fun n ↦ a.app n))
    (oneSubShift_naturality a)
  refine ⟨b, ?_, hb₂.symm⟩
  change p ≫ b = Limits.Sigma.map (fun n ↦ a.app n) ≫ p' at hb₁
  intro n
  rw [hb₁, ← Category.assoc, Limits.Sigma.ι_map, Category.assoc]

end CategoryTheory.Pretriangulated

/-! ### Passage to a subsequence

The two comparison morphisms of two-term complexes used to compare the defining triangle of a
derived colimit of a system with that of a derived colimit of the subsystem indexed by a strictly
increasing `n : ℕ → ℕ`, and the invertibility criterion that turns them into an isomorphism of the
derived colimits. All of it is auxiliary to Lemma 0CRJ below.
-/

namespace Stacks.DerivedColimit.Subsequence

variable {D : Type u} [Category.{v} D]

section Transition

/-- Transition maps of a system `F : ℕ ⥤ D` compose to a transition map. -/
private lemma map_comp_map (F : ℕ ⥤ D) {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    F.map (homOfLE h₁) ≫ F.map (homOfLE h₂) = F.map (homOfLE (h₁.trans h₂)) := by
  rw [← F.map_comp]; rfl

private lemma map_comp_map_assoc (F : ℕ ⥤ D) {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) {X : D}
    (g : F.obj c ⟶ X) :
    F.map (homOfLE h₁) ≫ F.map (homOfLE h₂) ≫ g = F.map (homOfLE (h₁.trans h₂)) ≫ g := by
  rw [← Category.assoc, map_comp_map]

/-- The transition map of a system from an index to itself is the identity. -/
private lemma map_self (F : ℕ ⥤ D) {a : ℕ} (h : a ≤ a) : F.map (homOfLE h) = 𝟙 (F.obj a) := by
  rw [show homOfLE h = 𝟙 a from rfl, F.map_id]

/-- The transition maps of the subsystem indexed by `n` are transition maps of the system. -/
private lemma sub_map (F : ℕ ⥤ D) {n : ℕ → ℕ} (hn : StrictMono n) {i j : ℕ} (h : i ≤ j) :
    (hn.monotone.functor ⋙ F).map (homOfLE h) = F.map (homOfLE (hn.monotone h)) := rfl

end Transition

section Index

/-- `idx hn m` is the least index `i` with `m ≤ n i`. -/
private def idx {n : ℕ → ℕ} (hn : StrictMono n) (m : ℕ) : ℕ :=
  Nat.find (⟨m, hn.id_le m⟩ : ∃ i, m ≤ n i)

private lemma le_n_idx {n : ℕ → ℕ} (hn : StrictMono n) (m : ℕ) : m ≤ n (idx hn m) :=
  Nat.find_spec (⟨m, hn.id_le m⟩ : ∃ i, m ≤ n i)

private lemma idx_le {n : ℕ → ℕ} (hn : StrictMono n) {m i : ℕ} (h : m ≤ n i) : idx hn m ≤ i :=
  Nat.find_min' _ h

private lemma idx_apply {n : ℕ → ℕ} (hn : StrictMono n) (i : ℕ) : idx hn (n i) = i :=
  le_antisymm (idx_le hn le_rfl) (hn.le_iff_le.mp (le_n_idx hn (n i)))

private lemma idx_succ_of_eq {n : ℕ → ℕ} (hn : StrictMono n) {m : ℕ} (h : n (idx hn m) = m) :
    idx hn (m + 1) = idx hn m + 1 := by
  have h1 : idx hn m ≤ idx hn (m + 1) :=
    idx_le hn ((Nat.le_succ m).trans (le_n_idx hn (m + 1)))
  have h2 : idx hn (m + 1) ≤ idx hn m + 1 := by
    refine idx_le hn ?_
    have := hn (show idx hn m < idx hn m + 1 by omega)
    omega
  have h3 : idx hn (m + 1) ≠ idx hn m := by
    intro h4
    have h5 := le_n_idx hn (m + 1)
    rw [h4, h] at h5
    omega
  omega

private lemma idx_succ_of_ne {n : ℕ → ℕ} (hn : StrictMono n) {m : ℕ} (h : n (idx hn m) ≠ m) :
    idx hn (m + 1) = idx hn m := by
  have h1 : idx hn m ≤ idx hn (m + 1) :=
    idx_le hn ((Nat.le_succ m).trans (le_n_idx hn (m + 1)))
  have h2 : idx hn (m + 1) ≤ idx hn m := by
    refine idx_le hn ?_
    have := le_n_idx hn m
    omega
  omega

/-- An index strictly between two consecutive members of the subsequence is not a member. -/
private lemma n_idx_ne {n : ℕ → ℕ} (hn : StrictMono n) {i m : ℕ} (h1 : n i < m)
    (h2 : m < n (i + 1)) : n (idx hn m) ≠ m := by
  intro h
  have ha : i < idx hn m := hn.lt_iff_lt.mp (by omega)
  have hb : idx hn m < i + 1 := hn.lt_iff_lt.mp (by omega)
  omega

end Index

section Telescope

variable [Preadditive D]

/-- The telescope `tele F m c : K m ⟶ ∐ K m` of length `c` at `m`: the sum, for `m ≤ k < m + c`,
of the coprojection of `K k` composed after the transition map `K m ⟶ K k`. -/
private noncomputable def tele (F : ℕ ⥤ D) [HasCoproduct F.obj] :
    (m c : ℕ) → (F.obj m ⟶ ∐ F.obj)
  | _, 0 => 0
  | m, c + 1 => Sigma.ι F.obj m + F.map (homOfLE (Nat.le_succ m)) ≫ tele F (m + 1) c

private lemma tele_zero (F : ℕ ⥤ D) [HasCoproduct F.obj] (m : ℕ) : tele F m 0 = 0 := rfl

private lemma tele_succ (F : ℕ ⥤ D) [HasCoproduct F.obj] (m c : ℕ) :
    tele F m (c + 1) =
      Sigma.ι F.obj m + F.map (homOfLE (Nat.le_succ m)) ≫ tele F (m + 1) c := rfl

/-- The telescope of length `c` at `m` composed with `1 - f` is the difference of the
coprojection of `K m` and of the coprojection of `K (m + c)` composed after `K m ⟶ K (m + c)`. -/
private lemma tele_comp_oneSubShift (F : ℕ ⥤ D) [HasCoproduct F.obj] :
    ∀ (c m N : ℕ) (_ : m + c = N) (hle : m ≤ N),
      tele F m c ≫ Stacks.CountableCoproducts.oneSubShift F =
        Sigma.ι F.obj m - F.map (homOfLE hle) ≫ Sigma.ι F.obj N := by
  intro c
  induction c with
  | zero =>
    intro m N h hle
    obtain rfl : m = N := by omega
    rw [tele_zero, zero_comp, map_self, Category.id_comp, sub_self]
  | succ c ih =>
    intro m N h hle
    rw [tele_succ, Preadditive.add_comp, Stacks.CountableCoproducts.ι_oneSubShift, Category.assoc,
      ih (m + 1) N (by omega) (by omega), Preadditive.comp_sub,
      map_comp_map_assoc F (Nat.le_succ m) (show m + 1 ≤ N by omega)]
    abel

end Telescope

section Comparison

variable [Preadditive D] (F : ℕ ⥤ D) [HasCoproduct F.obj] {n : ℕ → ℕ} (hn : StrictMono n)
  [HasCoproduct (hn.monotone.functor ⋙ F).obj]

/-- The natural inclusion `∐ K (n i) ⟶ ∐ K m`. -/
private noncomputable def sigmaIncl : ∐ (hn.monotone.functor ⋙ F).obj ⟶ ∐ F.obj :=
  Sigma.desc fun i ↦ Sigma.ι F.obj (n i)

/-- The telescope comparison `∐ K (n i) ⟶ ∐ K m`, on the `i`-th summand the telescope from
`n i` to `n (i + 1)`. -/
private noncomputable def sigmaTele : ∐ (hn.monotone.functor ⋙ F).obj ⟶ ∐ F.obj :=
  Sigma.desc fun i ↦ tele F (n i) (n (i + 1) - n i)

/-- The truncation `∐ K m ⟶ ∐ K (n i)`, on the `m`-th summand the transition map into the first
member `K (n (idx hn m))` of the subsequence at or beyond `m`. -/
private noncomputable def sigmaTrunc : ∐ F.obj ⟶ ∐ (hn.monotone.functor ⋙ F).obj :=
  Sigma.desc fun m ↦ F.map (homOfLE (le_n_idx hn m)) ≫
    Sigma.ι (hn.monotone.functor ⋙ F).obj (idx hn m)

/-- The natural projection `∐ K m ⟶ ∐ K (n i)`, the coprojection on the summands belonging to
the subsequence and zero on the others. -/
private noncomputable def sigmaProj : ∐ F.obj ⟶ ∐ (hn.monotone.functor ⋙ F).obj :=
  Sigma.desc fun m ↦ if n (idx hn m) = m then F.map (homOfLE (le_n_idx hn m)) ≫
    Sigma.ι (hn.monotone.functor ⋙ F).obj (idx hn m) else 0

/-- The homotopy `∐ K m ⟶ ∐ K m`, on the `m`-th summand minus the telescope from `m` to
`n (idx hn m)`. -/
private noncomputable def sigmaHtpy : ∐ F.obj ⟶ ∐ F.obj :=
  Sigma.desc fun m ↦ -tele F m (n (idx hn m) - m)

omit [Preadditive D] in
private lemma ι_comp_sigmaIncl (i : ℕ) :
    Sigma.ι (hn.monotone.functor ⋙ F).obj i ≫ sigmaIncl F hn = Sigma.ι F.obj (n i) := by
  simp [sigmaIncl]

private lemma ι_comp_sigmaTele (i : ℕ) :
    Sigma.ι (hn.monotone.functor ⋙ F).obj i ≫ sigmaTele F hn =
      tele F (n i) (n (i + 1) - n i) := by
  simp [sigmaTele]

omit [Preadditive D] in
private lemma ι_comp_sigmaTrunc (m : ℕ) :
    Sigma.ι F.obj m ≫ sigmaTrunc F hn = F.map (homOfLE (le_n_idx hn m)) ≫
      Sigma.ι (hn.monotone.functor ⋙ F).obj (idx hn m) := by
  simp [sigmaTrunc]

private lemma ι_comp_sigmaProj (m : ℕ) :
    Sigma.ι F.obj m ≫ sigmaProj F hn = if n (idx hn m) = m then
      F.map (homOfLE (le_n_idx hn m)) ≫
        Sigma.ι (hn.monotone.functor ⋙ F).obj (idx hn m) else 0 := by
  simp [sigmaProj]

omit [HasCoproduct (hn.monotone.functor ⋙ F).obj] in
private lemma ι_comp_sigmaHtpy (m : ℕ) :
    Sigma.ι F.obj m ≫ sigmaHtpy F hn = -tele F m (n (idx hn m) - m) := by
  simp [sigmaHtpy]

omit [Preadditive D] [HasCoproduct F.obj] in
/-- Transporting a coprojection of `∐ K (n i)` along an equality of indices. -/
private lemma map_comp_ι_congr {i j m : ℕ} (h : i = j) (h1 : m ≤ n i) (h2 : m ≤ n j) :
    F.map (homOfLE h1) ≫ Sigma.ι (hn.monotone.functor ⋙ F).obj i =
      F.map (homOfLE h2) ≫ Sigma.ι (hn.monotone.functor ⋙ F).obj j := by
  subst h; rfl

/-- Transporting a telescope along an equality of its starting index. -/
private lemma map_comp_tele {m k : ℕ} (h : m = k) (hle : m ≤ k) (c : ℕ) :
    F.map (homOfLE hle) ≫ tele F k c = tele F m c := by
  subst h
  rw [map_self, Category.id_comp]

/-- The first comparison square: the natural inclusion and the telescope form a morphism from the
two-term complex of the subsystem to that of the system. -/
private lemma oneSubShift_comp_sigmaIncl :
    Stacks.CountableCoproducts.oneSubShift (hn.monotone.functor ⋙ F) ≫ sigmaIncl F hn =
      sigmaTele F hn ≫ Stacks.CountableCoproducts.oneSubShift F := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  have hle : n i ≤ n (i + 1) := (hn (show i < i + 1 by omega)).le
  rw [← Category.assoc, Stacks.CountableCoproducts.ι_oneSubShift, ← Category.assoc,
    ι_comp_sigmaTele,
    tele_comp_oneSubShift F _ _ _ (by omega) hle, Preadditive.sub_comp, Category.assoc,
    ι_comp_sigmaIncl, ι_comp_sigmaIncl, sub_map F hn]

/-- The second comparison square: the natural projection and the truncation form a morphism from
the two-term complex of the system to that of the subsystem. -/
private lemma oneSubShift_comp_sigmaTrunc :
    Stacks.CountableCoproducts.oneSubShift F ≫ sigmaTrunc F hn =
      sigmaProj F hn ≫ Stacks.CountableCoproducts.oneSubShift (hn.monotone.functor ⋙ F) := by
  refine Sigma.hom_ext _ _ fun m ↦ ?_
  conv_lhs => rw [← Category.assoc, Stacks.CountableCoproducts.ι_oneSubShift, Preadditive.sub_comp,
    Category.assoc,
    ι_comp_sigmaTrunc, ι_comp_sigmaTrunc]
  conv_rhs => rw [← Category.assoc, ι_comp_sigmaProj]
  by_cases h : n (idx hn m) = m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), Category.assoc,
    Stacks.CountableCoproducts.ι_oneSubShift,
      Preadditive.comp_sub, sub_map F hn,
      map_comp_ι_congr F hn (idx_succ_of_eq hn h) (le_n_idx hn (m + 1))
        (show m + 1 ≤ n (idx hn m + 1) by
          have := le_n_idx hn (m + 1); rw [idx_succ_of_eq hn h] at this; exact this),
      map_comp_map_assoc, map_comp_map_assoc]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), zero_comp,
      map_comp_ι_congr F hn (idx_succ_of_ne hn h) (le_n_idx hn (m + 1))
        (show m + 1 ≤ n (idx hn m) by have := le_n_idx hn m; omega),
      map_comp_map_assoc, sub_self]

omit [Preadditive D] in
/-- The truncation is a section of the natural inclusion. -/
private lemma sigmaIncl_comp_sigmaTrunc :
    sigmaIncl F hn ≫ sigmaTrunc F hn = 𝟙 (∐ (hn.monotone.functor ⋙ F).obj) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, ι_comp_sigmaIncl, ι_comp_sigmaTrunc, Category.comp_id,
    map_comp_ι_congr F hn (idx_apply hn i) (le_n_idx hn (n i)) le_rfl, map_self,
    Category.id_comp]

/-- A telescope none of whose indices belongs to the subsequence is killed by the natural
projection. -/
private lemma tele_comp_sigmaProj_eq_zero :
    ∀ (c m : ℕ) (_ : ∀ k, m ≤ k → k < m + c → n (idx hn k) ≠ k),
      tele F m c ≫ sigmaProj F hn = 0 := by
  intro c
  induction c with
  | zero => intro m _; rw [tele_zero, zero_comp]
  | succ c ih =>
    intro m hm
    rw [tele_succ, Preadditive.add_comp, ι_comp_sigmaProj,
      ite_eq_right_of_eq_false _ _ (eq_false (hm m le_rfl (by omega))), Category.assoc,
      ih (m + 1) (fun k hk1 hk2 ↦ hm k (by omega) (by omega)), comp_zero, add_zero]

/-- The natural projection is a retraction of the telescope comparison. -/
private lemma sigmaTele_comp_sigmaProj :
    sigmaTele F hn ≫ sigmaProj F hn = 𝟙 (∐ (hn.monotone.functor ⋙ F).obj) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  have hlt : n i < n (i + 1) := hn (show i < i + 1 by omega)
  rw [← Category.assoc, ι_comp_sigmaTele, Category.comp_id,
    show n (i + 1) - n i = (n (i + 1) - (n i + 1)) + 1 by omega, tele_succ,
    Preadditive.add_comp, ι_comp_sigmaProj,
    ite_eq_left_of_eq_true _ _ (eq_true (show n (idx hn (n i)) = n i by rw [idx_apply hn i])),
    Category.assoc,
    tele_comp_sigmaProj_eq_zero F hn (n (i + 1) - (n i + 1)) (n i + 1)
      (fun k hk1 hk2 ↦ n_idx_ne hn (i := i) (by omega) (by omega)), comp_zero, add_zero,
    map_comp_ι_congr F hn (idx_apply hn i) (le_n_idx hn (n i)) le_rfl, map_self,
    Category.id_comp]

/-- The inclusion after the truncation differs from the identity by the boundary of the
homotopy. -/
private lemma sigmaTrunc_comp_sigmaIncl :
    sigmaTrunc F hn ≫ sigmaIncl F hn =
      𝟙 (∐ F.obj) + sigmaHtpy F hn ≫ Stacks.CountableCoproducts.oneSubShift F := by
  refine Sigma.hom_ext _ _ fun m ↦ ?_
  have hm := le_n_idx hn m
  rw [← Category.assoc, ι_comp_sigmaTrunc, Category.assoc, ι_comp_sigmaIncl,
    Preadditive.comp_add, Category.comp_id, ← Category.assoc, ι_comp_sigmaHtpy,
    Preadditive.neg_comp, tele_comp_oneSubShift F _ _ _ (by omega) hm]
  abel

/-- The telescope comparison after the natural projection differs from the identity by the
boundary of the homotopy. -/
private lemma sigmaProj_comp_sigmaTele :
    sigmaProj F hn ≫ sigmaTele F hn =
      𝟙 (∐ F.obj) + Stacks.CountableCoproducts.oneSubShift F ≫ sigmaHtpy F hn := by
  refine Sigma.hom_ext _ _ fun m ↦ ?_
  have hm := le_n_idx hn m
  rw [← Category.assoc, ι_comp_sigmaProj, Preadditive.comp_add, Category.comp_id,
    ← Category.assoc, Stacks.CountableCoproducts.ι_oneSubShift, Preadditive.sub_comp,
      Category.assoc,
    ι_comp_sigmaHtpy, ι_comp_sigmaHtpy, Preadditive.comp_neg]
  by_cases h : n (idx hn m) = m
  · have hlt : m < n (idx hn m + 1) := by
      have := hn (show idx hn m < idx hn m + 1 by omega)
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), Category.assoc, ι_comp_sigmaTele,
      map_comp_tele F h.symm, idx_succ_of_eq hn h, show n (idx hn m) - m = 0 by omega, tele_zero,
      show n (idx hn m + 1) - n (idx hn m) = (n (idx hn m + 1) - (m + 1)) + 1 by omega, tele_succ]
    abel
  · have hlt : m < n (idx hn m) := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), zero_comp, idx_succ_of_ne hn h,
      show n (idx hn m) - m = (n (idx hn m) - (m + 1)) + 1 by omega, tele_succ]
    abel

end Comparison

section Triangle

variable [Preadditive D]

/-- An endomorphism differing from the identity by a square-zero endomorphism is invertible. -/
private lemma isIso_one_add_of_sq_eq_zero {X : D} {f : X ⟶ X} (hf : f ≫ f = 0) :
    IsIso (𝟙 X + f) := by
  refine ⟨𝟙 X - f, ?_, ?_⟩ <;>
    simp [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_sub, hf]

variable [HasZeroObject D] [HasShift D ℤ] [∀ i : ℤ, (shiftFunctor D i).Additive]
  [Pretriangulated D]

/-- An endomorphism of the third object of a distinguished triangle which is the identity on the
second and the third map of the triangle is an isomorphism: it differs from the identity by a
square-zero endomorphism. This is the step of [Stacks, Tag 0CRJ] deduced there from
[Stacks, Lemma 05QP]. -/
private lemma isIso_of_mor₂_comp_eq {T : Triangle D} (hT : T ∈ distTriang D)
    {γ : T.obj₃ ⟶ T.obj₃} (h₂ : T.mor₂ ≫ γ = T.mor₂) (h₃ : γ ≫ T.mor₃ = T.mor₃) : IsIso γ := by
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₃ T hT (γ - 𝟙 T.obj₃) (by
    rw [Preadditive.comp_sub, h₂, Category.comp_id, sub_self])
  have hnil : (γ - 𝟙 T.obj₃) ≫ (γ - 𝟙 T.obj₃) = 0 := by
    nth_rw 2 [hψ]
    rw [← Category.assoc, Preadditive.sub_comp, h₃, Category.id_comp, sub_self, zero_comp]
  have h := isIso_one_add_of_sq_eq_zero hnil
  rwa [show 𝟙 T.obj₃ + (γ - 𝟙 T.obj₃) = γ by abel] at h

end Triangle

end Stacks.DerivedColimit.Subsequence

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

open Stacks.DerivedColimit.Subsequence in
/-- **Stacks 0CRJ**. Let `F : ℕ ⥤ D` be a system of objects `K m = F.obj m` of a
pre-triangulated category, let `n : ℕ → ℕ` be strictly increasing, and assume the direct sums
`∐ K m` and `∐ K (n i)` exist. If `K` is a derived colimit of the system with structure map `p`
and `K'` is a derived colimit of the subsystem `(K (n i))` with structure map `p'` (Definition
090Z), then there is an isomorphism `e : K' ≅ K`, i.e. `hocolim K (n i) ⟶ hocolim K m`, such
that for every `i` the composition `K (n i) ⟶ K' ⟶ K` of the coprojection with `e` is the
coprojection `K (n i) ⟶ K`. -/
@[stacks 0CRJ]
public theorem exists_iso_of_isHomotopyColimit_of_strictMono
    (F : ℕ ⥤ D) [HasCoproduct F.obj] {n : ℕ → ℕ} (hn : StrictMono n)
    [HasCoproduct (hn.monotone.functor ⋙ F).obj]
    {K : D} (p : ∐ F.obj ⟶ K) (q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hK : Triangle.mk (Limits.Sigma.desc fun m ↦ Limits.Sigma.ι F.obj m -
        F.map (homOfLE (Nat.le_succ m)) ≫ Limits.Sigma.ι F.obj (m + 1)) p q ∈ distTriang D)
    {K' : D} (p' : ∐ (hn.monotone.functor ⋙ F).obj ⟶ K')
    (q' : K' ⟶ (∐ (hn.monotone.functor ⋙ F).obj)⟦(1 : ℤ)⟧)
    (hK' : Triangle.mk (Limits.Sigma.desc fun i ↦
      Limits.Sigma.ι (hn.monotone.functor ⋙ F).obj i -
        (hn.monotone.functor ⋙ F).map (homOfLE (Nat.le_succ i)) ≫
          Limits.Sigma.ι (hn.monotone.functor ⋙ F).obj (i + 1)) p' q' ∈ distTriang D) :
    ∃ e : K' ≅ K, ∀ i : ℕ,
      Limits.Sigma.ι (hn.monotone.functor ⋙ F).obj i ≫ p' ≫ e.hom =
        Limits.Sigma.ι F.obj (n i) ≫ p := by
  have hT : Triangle.mk (Stacks.CountableCoproducts.oneSubShift F) p q ∈ distTriang D := hK
  have hT' : Triangle.mk (Stacks.CountableCoproducts.oneSubShift (hn.monotone.functor ⋙ F)) p' q' ∈
    distTriang D := hK'
  obtain ⟨E, hp, hq⟩ : ∃ E : K' ⟶ K, p' ≫ E = sigmaIncl F hn ≫ p ∧
      q' ≫ (sigmaTele F hn)⟦(1 : ℤ)⟧' = E ≫ q :=
    complete_distinguished_triangle_morphism _ _ hT' hT (sigmaTele F hn) (sigmaIncl F hn)
      (oneSubShift_comp_sigmaIncl F hn)
  obtain ⟨E', hp', hq'⟩ : ∃ E' : K ⟶ K', p ≫ E' = sigmaTrunc F hn ≫ p' ∧
      q ≫ (sigmaProj F hn)⟦(1 : ℤ)⟧' = E' ≫ q' :=
    complete_distinguished_triangle_morphism _ _ hT hT' (sigmaProj F hn) (sigmaTrunc F hn)
      (oneSubShift_comp_sigmaTrunc F hn)
  have hdp : Stacks.CountableCoproducts.oneSubShift F ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hqd : q ≫ (Stacks.CountableCoproducts.oneSubShift F)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hT
  have hEE : IsIso (E ≫ E') := by
    refine isIso_of_mor₂_comp_eq hT' ?_ ?_
    · change p' ≫ E ≫ E' = p'
      rw [← Category.assoc, hp, Category.assoc, hp', ← Category.assoc,
        sigmaIncl_comp_sigmaTrunc, Category.id_comp]
    · change (E ≫ E') ≫ q' = q'
      rw [Category.assoc, ← hq', ← Category.assoc, ← hq, Category.assoc,
        ← CategoryTheory.Functor.map_comp, sigmaTele_comp_sigmaProj,
        CategoryTheory.Functor.map_id, Category.comp_id]
  have hE'E : IsIso (E' ≫ E) := by
    refine isIso_of_mor₂_comp_eq hT ?_ ?_
    · change p ≫ E' ≫ E = p
      rw [← Category.assoc, hp', Category.assoc, hp, ← Category.assoc,
        sigmaTrunc_comp_sigmaIncl, Preadditive.add_comp, Category.id_comp, Category.assoc,
        hdp, comp_zero, add_zero]
    · change (E' ≫ E) ≫ q = q
      rw [Category.assoc, ← hq, ← Category.assoc, ← hq', Category.assoc,
        ← CategoryTheory.Functor.map_comp, sigmaProj_comp_sigmaTele,
        CategoryTheory.Functor.map_add, Preadditive.comp_add, CategoryTheory.Functor.map_id,
        Category.comp_id, CategoryTheory.Functor.map_comp, ← Category.assoc, hqd, zero_comp,
        add_zero]
  have hu : E ≫ E' ≫ inv (E ≫ E') = 𝟙 K' := by
    rw [← Category.assoc, IsIso.hom_inv_id]
  have hl : (inv (E' ≫ E) ≫ E') ≫ E = 𝟙 K := by
    rw [Category.assoc, IsIso.inv_hom_id]
  have hlu : inv (E' ≫ E) ≫ E' = E' ≫ inv (E ≫ E') :=
    calc inv (E' ≫ E) ≫ E'
        = (inv (E' ≫ E) ≫ E') ≫ E ≫ E' ≫ inv (E ≫ E') := by rw [hu, Category.comp_id]
      _ = ((inv (E' ≫ E) ≫ E') ≫ E) ≫ E' ≫ inv (E ≫ E') := by simp only [Category.assoc]
      _ = E' ≫ inv (E ≫ E') := by rw [hl, Category.id_comp]
  refine ⟨⟨E, E' ≫ inv (E ≫ E'), hu, ?_⟩, fun i ↦ ?_⟩
  · rw [← hlu]; exact hl
  · change Sigma.ι (hn.monotone.functor ⋙ F).obj i ≫ p' ≫ E = Sigma.ι F.obj (n i) ≫ p
    rw [hp, ← Category.assoc, ι_comp_sigmaIncl]

end CategoryTheory.Pretriangulated
