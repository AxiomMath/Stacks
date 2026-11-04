module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Fin.Basic
public import StacksFrontier.CategoryTheory.Triangulated.ZeroRetract

/-!
# Operations on full subcategories of a triangulated category

Let `C` be a triangulated category. A full subcategory of `C` is a property of its objects, and
the Stacks project attaches three operations to such subcategories: the *extension product*
`P ⋆ Q`, the full subcategory of the objects `X` fitting into a distinguished triangle
`A ⟶ X ⟶ B ⟶ A⟦1⟧` with `A ∈ P` and `B ∈ Q`; the closure `add(P)` under finite direct sums; and
the closure `smd(P)` under direct summands. This file proves the basic properties of these
operations, and the two bounds on the towers `smd(add(E)^{⋆ n})` that the applications use.

The extension product is associative, by the octahedron axiom TR4: given distinguished triangles
`A ⟶ X ⟶ B` with `A ∈ P`, `B ∈ Q` and `X ⟶ Y ⟶ D` with `D ∈ R`, TR4 completes `A ⟶ X ⟶ Y` to
`A ⟶ Y ⟶ Z` and supplies `B ⟶ Z ⟶ D`, which exhibits `Y` in `P ⋆ (Q ⋆ R)`, and symmetrically in
the other direction. So the iterated products `P^{⋆ n}` are unambiguous. Extensions of summands
are summands of extensions: if `A₁ ⟶ X ⟶ B₁` is distinguished with `A₁ ⊕ A₂ ∈ P` and
`B₁ ⊕ B₂ ∈ Q`, then `A₁ ⊕ A₂ ⟶ A₂ ⊕ X ⊕ B₂ ⟶ B₁ ⊕ B₂` is distinguished, so `X` is a summand of
an object of `P ⋆ Q`; hence `smd(P ⋆ Q)` sees `P` and `Q` only through `smd(P)` and `smd(Q)`.
Together with the fact that `⋆` and `smd` preserve closure under direct sums, this makes the
tower `Cₙ = smd(P^{⋆ n})` of a subcategory `P` closed under direct sums a tower of strictly full
subcategories closed under direct sums and direct summands, additive in the number of factors:
`C_{n + m} = smd(Cₙ ⋆ C_m)`.

The tower is then bounded from both sides. In the derived category of an abelian category, an
object `K` whose cohomology is concentrated in the degrees `[a, b]` is built from its `b - a + 1`
cohomology objects by `b - a` extensions — the truncation triangles of the canonical
t-structure — so if each `H^i(K)` is a summand of a finite direct sum of objects of `E`, then `K`
lies in `smd(add(E[a, b])^{⋆ (b - a + 1)})`, where `E[a, b]` is `E` placed in the degrees
`a, …, b`; the same holds for an object represented by a complex whose terms in `[a, b]` are such
summands, the extensions now coming from the stupid filtration of that complex. Conversely a
homological functor `H` only ever sees a bounded window of cohomology on such a tower: the
objects with `H`-cohomology in a fixed window are closed under isomorphisms, direct sums, direct
summands and extensions — the last by the long exact cohomology sequence of a distinguished
triangle — and shifting by `-j` translates the window by `j`, so if `H^i(E) = 0` for `E ∈ E` and
`i ∉ [a, b]`, then `H^i(X) = 0` for every `X ∈ smd(add(E[c, d])^{⋆ n})` and every
`i ∉ [a + c, b + d]`.

## Main results

* `ObjectProperty.retractClosure_extensionProductIter_isClosedUnderBinaryProducts_and_add`: the
  tower `smd(P^{⋆ (n + 1)})` is strictly full, closed under direct sums and under direct
  summands, and additive in the number of factors.
* `DerivedCategory.prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X`: an
  object of the derived category with cohomology in `smd(add(E))` concentrated in `[a, b]`, or
  represented by a complex with terms in `smd(add(E))` concentrated in `[a, b]`, lies in
  `smd(add(E[a, b])^{⋆ (b - a + 1)})`.
* `CategoryTheory.Functor.isZero_obj_shift_of_retractClosure_extensionProductIter`: the window of
  a homological functor on the tower `smd(add(E[c, d])^{⋆ n})` is `[a + c, b + d]`.

## Implementation notes

The source's `smd`, `add`, `⋆` and `⋆ n` are `ObjectProperty.retractClosure`,
`ObjectProperty.binaryProductsClosure`, `ObjectProperty.extensionProduct` and
`ObjectProperty.extensionProductIter`. Reading `smd` as retract closure costs nothing: in a
pretriangulated category a distinguished triangle whose first map is a split monomorphism splits
(`Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`), so a retract of `Y` is a direct
summand of `Y`. Direct sums are taken as categorical binary products, which is what they are in a
preadditive category; "strictly full" is `ObjectProperty.IsClosedUnderIsomorphisms`, "closed
under direct summands" is `ObjectProperty.IsStableUnderRetracts`, and "closed under direct sums"
is `ObjectProperty.IsClosedUnderBinaryProducts`, i.e. closure under limits of shape
`Discrete WalkingPair`. The stronger `ObjectProperty.IsClosedUnderFiniteProducts` would be false,
as it also demands a zero object, which `smd(P^{⋆ (n + 1)}) = ⊥` for `P = ⊥` does not have.

Mathlib's indexing counts extensions rather than factors: `P.extensionProductIter n` is the
source's `P^{⋆ (n + 1)}`, so the source's `b - a + 1` factors appear as the exponent
`(b - a).toNat`, and a statement for all `n : ℕ` covers the source's `n ≥ 1` and additionally the
case of no extension at all.


In `retractClosure_extensionProductIter_isClosedUnderBinaryProducts_and_add` the base of the
tower is an arbitrary subcategory `P` closed under direct sums rather than literally an `add(A)`.
The source's `Cₙ` is the case `P = A.binaryProductsClosure`, for which the hypothesis is
automatic, and the extra generality is used: the tower on which Mathlib's
`ObjectProperty.triangEnvelopeIter` is built has base `smd(add(A[-∞, ∞]))`, closed under direct
sums but not of the form `add(-)`.

In the derived category, `E[a, b]` is spelled `⨆ i ∈ Set.Icc a b, E.map (singleFunctor C i)`,
the objects isomorphic to some `Y ∈ E` placed in a cohomological degree `i ∈ [a, b]`; this is the
source's subcategory because `(singleFunctors C).shiftIso (-i) i 0` identifies
`((singleFunctor C 0).obj Y)⟦-i⟧` with `(singleFunctor C i).obj Y`. Its hypotheses are Mathlib's
t-structure and support classes: `H^i(K) = 0` for `i ∉ [a, b]` is `[K.IsGE a] [K.IsLE b]`, and
`K^i = 0` for `i ∉ [a, b]` is `[L.IsStrictlyGE a] [L.IsStrictlyLE b]`. "`K` can be represented by
a complex `K^•`" is stated as the conclusion for `Q.obj L` for every such complex `L`, which is
the same statement because the conclusion is a retract closure, hence closed under isomorphisms.
Parts (1) and (3) of [Stacks, Tag 0FX7] are the cases `E ≤ smd(add(E))` of its parts (2) and (4),
so only the latter two are stated; they are independent, since the cohomology of a complex with
terms in `smd(add(E))` need not lie in `smd(add(E))`. Finally `smd(add(E))` is read in `C` rather
than in `D(C)`: the two agree on objects of `C`, because `singleFunctor C 0` is fully faithful and
additive and a summand in `D(C)` of an object of `C` has cohomology in degree `0` only.

For a homological functor the shift range is spelled `⨆ j ∈ Set.Icc c d, E.isoClosure.shift j`;
`ObjectProperty.shift j` is the *inverse* image under `⟦j⟧`, so this is the class of objects
isomorphic to some `E⟦-j⟧` with `E ∈ E`, the source's convention including its minus sign. Two
departures from [Stacks, Tag 0FX8]. The shift range is an arbitrary interval `[c, d]` rather than
the symmetric `[-m, m]`; no step uses symmetry, and the source itself uses the asymmetric form in
the proof of [Stacks, Tag 0FZ7]. And the window is `[a + c, b + d]`, independent of the number `n`
of factors, rather than the source's `[-m + na, m + nb]`: since the objects with cohomology in a
fixed window are closed under extensions, the window does not grow with `n`. The source's window
contains the sharp one exactly when `a ≤ 0 ≤ b`, and for `a > 0` the source's claim is false —
with `m = 0`, `n = 2` and `a = b > 0`, the object `E ⊕ E` lies in `add(E[0, 0])^{⋆ 2}` and has
`H^a(E ⊕ E) ≠ 0` while `a ∉ [2a, 2b]`. The form proved here implies the source's whenever the
latter holds.

## References

* [Stacks project, Tag 0FX0](https://stacks.math.columbia.edu/tag/0FX0), Section 13.35
* [Stacks project, Tag 0FX3](https://stacks.math.columbia.edu/tag/0FX3), Lemma 13.35.3
* [Stacks project, Tag 0FX4](https://stacks.math.columbia.edu/tag/0FX4), Lemma 13.35.4
* [Stacks project, Tag 0FX7](https://stacks.math.columbia.edu/tag/0FX7), Lemma 13.35.7
* [Stacks project, Tag 0FX8](https://stacks.math.columbia.edu/tag/0FX8), Lemma 13.35.8
* [Stacks project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7), Lemma 13.38.7
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

section

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The product of a `WalkingPair`-indexed family is the binary product of its two values. -/
private noncomputable def _root_.CategoryTheory.Limits.piWalkingPairIsoProd
    (f : WalkingPair → C) : ∏ᶜ f ≅ f .left ⨯ f .right :=
  HasLimit.isoOfNatIso (diagramIsoPair (Discrete.functor f))

/-- A property of objects closed under isomorphisms and under the chosen binary product of two
objects satisfying it is closed under binary products. -/
lemma isClosedUnderBinaryProducts_of_prop_prod (Q : ObjectProperty C)
    [Q.IsClosedUnderIsomorphisms] (h : ∀ ⦃X Y : C⦄, Q X → Q Y → Q (X ⨯ Y)) :
    Q.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact Q.prop_of_iso (IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      (h (p.prop_diag_obj ⟨WalkingPair.left⟩) (p.prop_diag_obj ⟨WalkingPair.right⟩))

/-- The binary product of two retracts. -/
private noncomputable def _root_.CategoryTheory.Retract.prod {A A' B B' : C}
    (r : Retract A A') (r' : Retract B B') : Retract (A ⨯ B) (A' ⨯ B') where
  i := Limits.prod.map r.i r'.i
  r := Limits.prod.map r.r r'.r
  retract := by rw [Limits.prod.map_map, r.retract, r'.retract, Limits.prod.map_id_id]

/-- The summand closure of a property of objects closed under direct sums is closed under
direct sums. This is [Stacks, Tag 0FX3] (2), for an arbitrary property in place of `add(A)`. -/
lemma isClosedUnderBinaryProducts_retractClosure (Q : ObjectProperty C)
    [Q.IsClosedUnderBinaryProducts] : Q.retractClosure.IsClosedUnderBinaryProducts := by
  refine isClosedUnderBinaryProducts_of_prop_prod _ ?_
  rintro X Y ⟨X', hX', ⟨rX⟩⟩ ⟨Y', hY', ⟨rY⟩⟩
  exact ⟨X' ⨯ Y', Q.prop_prod _ _ hX' hY', ⟨rX.prod rY⟩⟩

/-- The extension product of two properties of objects closed under direct sums is closed under
direct sums. This is [Stacks, Tag 0FX3] (1), for arbitrary properties in place of `add(A)` and
`add(B)`. -/
lemma isClosedUnderBinaryProducts_extensionProduct (P Q : ObjectProperty C)
    [P.IsClosedUnderBinaryProducts] [Q.IsClosedUnderBinaryProducts] :
    (extensionProduct P Q).IsClosedUnderBinaryProducts := by
  refine isClosedUnderBinaryProducts_of_prop_prod _ ?_
  rintro X Y ⟨A, B, f, g, h, hT, hA, hB⟩ ⟨A', B', f', g', h', hT', hA', hB'⟩
  let F : WalkingPair → Triangle C :=
    fun j => j.casesOn (Triangle.mk f g h) (Triangle.mk f' g' h')
  refine (extensionProduct P Q).prop_of_iso (piWalkingPairIsoProd (fun j => (F j).obj₂))
    ⟨_, _, (productTriangle F).mor₁, (productTriangle F).mor₂, (productTriangle F).mor₃,
      productTriangle_distinguished F ?_, P.prop_pi _ ?_, Q.prop_pi _ ?_⟩ <;>
  rintro (_ | _) <;> assumption

/-- Every stage of the tower of extension products of a property of objects closed under direct
sums is closed under direct sums. -/
private lemma isClosedUnderBinaryProducts_extensionProductIter (P : ObjectProperty C)
    [P.IsClosedUnderBinaryProducts] (n : ℕ) :
    (P.extensionProductIter n).IsClosedUnderBinaryProducts := by
  induction n with
  | zero => rw [extensionProductIter_zero]; infer_instance
  | succ n hn =>
    rw [extensionProductIter_succ]
    exact isClosedUnderBinaryProducts_extensionProduct P _

/-- For a full subcategory `P` of a triangulated category which is closed under direct sums,
the subcategory `smd(P^{⋆ (n + 1)})` of direct summands of `n`-fold extensions of objects of
`P` is strictly full, closed under direct sums and closed under direct summands, and these
subcategories are additive in the number of factors:
`smd(P^{⋆ (n + m + 1)}) = smd(smd(P^{⋆ (n + 1)}) ⋆ smd(P^{⋆ (m + 1)}))`. Taking
`P = add(A)` this is the Stacks project's `Cₙ = smd(add(A)^{⋆ n})`, strictly full, closed under
direct sums and direct summands, with `C_{n + m} = smd(Cₙ ⋆ C_m)`. -/
@[stacks 0FX4]
theorem retractClosure_extensionProductIter_isClosedUnderBinaryProducts_and_add
    (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts] [IsTriangulated C] (n m : ℕ) :
    (P.extensionProductIter n).retractClosure.IsClosedUnderIsomorphisms ∧
      (P.extensionProductIter n).retractClosure.IsClosedUnderBinaryProducts ∧
      (P.extensionProductIter n).retractClosure.IsStableUnderRetracts ∧
      (P.extensionProductIter (n + m + 1)).retractClosure =
        (extensionProduct (P.extensionProductIter n).retractClosure
          (P.extensionProductIter m).retractClosure).retractClosure := by
  have := isClosedUnderBinaryProducts_extensionProductIter P n
  refine ⟨inferInstance, isClosedUnderBinaryProducts_retractClosure _, inferInstance, ?_⟩
  rw [add_right_comm n m 1, P.extensionProductIter_add (n := n + 1) (m := m) (n' := n) rfl]
  exact (retractClosure_extensionProduct_retractClosure_retractClosure _ _).symm

end

section InverseImage

variable {C D : Type*} [Category C] [Category D]

/-- The inverse image under a functor of a property of objects stable under retracts is stable
under retracts: a functor carries a retract diagram to a retract diagram. -/
lemma isStableUnderRetracts_inverseImage (Q : ObjectProperty D) [Q.IsStableUnderRetracts]
    (F : C ⥤ D) : (Q.inverseImage F).IsStableUnderRetracts where
  of_retract h hY := Q.prop_of_retract (h.map F) hY

end InverseImage

section InverseImageExact

variable {C D : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- The inverse image under an exact functor of a property of objects closed under binary
products and isomorphisms is closed under binary products: the product `X ⨯ Y` is the middle
vertex of a distinguished triangle `X ⟶ X ⨯ Y ⟶ Y ⟶ X⟦1⟧` whose third map vanishes, so the image
of that triangle splits `F(X ⨯ Y)` as the biproduct of `F X` and `F Y`. -/
lemma isClosedUnderBinaryProducts_inverseImage (Q : ObjectProperty D)
    [Q.IsClosedUnderBinaryProducts] [Q.IsClosedUnderIsomorphisms] :
    (Q.inverseImage F).IsClosedUnderBinaryProducts := by
  have : (Q.inverseImage F).IsClosedUnderIsomorphisms :=
    { of_iso := fun e hX => Q.prop_of_iso (F.mapIso e) hX }
  refine isClosedUnderBinaryProducts_of_prop_prod _ ?_
  intro X Y hX hY
  have hT := F.map_distinguished _ (binaryProductTriangle_distinguished X Y)
  have hzero : (F.mapTriangle.obj (binaryProductTriangle X Y)).mor₃ = 0 := by
    change F.map (0 : Y ⟶ X⟦(1 : ℤ)⟧) ≫ (F.commShiftIso (1 : ℤ)).hom.app X = 0
    rw [F.map_zero, zero_comp]
  obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT hzero
  exact Q.prop_of_iso e.symm
    (Q.prop_of_iso (biprod.isoProd _ _).symm (Q.prop_prod _ _ hX hY))

end InverseImageExact

/-- A functor preserving binary products sends a direct summand of a finite direct sum of
objects of `E` to a direct summand of a finite direct sum of objects of the image of `E`. -/
private lemma retractClosure_binaryProductsClosure_map {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) L] (E : ObjectProperty C) {Y : C}
    (hY : E.binaryProductsClosure.retractClosure Y) :
    ((E.map L).binaryProductsClosure).retractClosure (L.obj Y) := by
  obtain ⟨Z, hZ, ⟨r⟩⟩ := hY
  exact ⟨L.obj Z, limitsClosure_le (Q := (E.map L).binaryProductsClosure.inverseImage L)
    (fun X hX => le_limitsClosure _ _ _ ⟨X, hX, ⟨Iso.refl _⟩⟩) Z hZ, ⟨r.map _⟩⟩

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ShortComplex

open Limits

variable {A : Type*} [Category A] [Abelian A] (S : ShortComplex A)

/-- A short complex `0 ⟶ X₂ ⟶ X₃ ⟶ 0` whose second map is an isomorphism is short exact. -/
lemma shortExact_of_isZero_X₁_of_isIso_g (h₁ : IsZero S.X₁) (hg : IsIso S.g) :
    S.ShortExact where
  exact := by rw [S.exact_iff_mono (h₁.eq_of_src _ _)]; infer_instance
  mono_f := ⟨fun _ _ _ => h₁.eq_of_tgt _ _⟩
  epi_g := inferInstance

/-- A short complex `X₁ ⟶ X₂ ⟶ 0` whose first map is an isomorphism is short exact. -/
lemma shortExact_of_isIso_f_of_isZero_X₃ (hf : IsIso S.f) (h₃ : IsZero S.X₃) :
    S.ShortExact where
  exact := by rw [S.exact_iff_epi (h₃.eq_of_tgt _ _)]; infer_instance
  mono_f := inferInstance
  epi_g := ⟨fun _ _ _ => h₃.eq_of_src _ _⟩

end CategoryTheory.ShortComplex

namespace CategoryTheory.Pretriangulated

open Limits

variable {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
  [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]

/-- A distinguished triangle stays distinguished when its first term is replaced by an isomorphic
object. -/
lemma mk_mem_distTriang_of_iso (T : Triangle A) (hT : T ∈ distTriang A) {Y : A}
    (e : Y ≅ T.obj₁) :
    Triangle.mk (e.hom ≫ T.mor₁) T.mor₂ (T.mor₃ ≫ (shiftFunctor A (1 : ℤ)).map e.inv)
      ∈ distTriang A :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (by simp)
    (by simp) (by simp [← Functor.map_comp]))

end CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory

open CategoryTheory Limits Pretriangulated ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- In a distinguished triangle whose third term has cohomology in degrees `≥ n`, the first
morphism induces isomorphisms in cohomology in degrees `< n`. -/
private lemma isIso_homologyFunctor_map_mor₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (n i : ℤ) [T.obj₃.IsGE n] (hi : i < n) :
    IsIso ((homologyFunctor C i).map T.mor₁) := by
  have : Epi ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (isZero_of_isGE T.obj₃ n i hi).eq_of_tgt _ _
  have : Mono ((homologyFunctor C i).map T.mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)]
    exact (isZero_of_isGE T.obj₃ n (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle whose first term has cohomology in degrees `≤ n`, the second
morphism induces isomorphisms in cohomology in degrees `> n`. -/
private lemma isIso_homologyFunctor_map_mor₂ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (n i : ℤ) [T.obj₁.IsLE n] (hi : n < i) :
    IsIso ((homologyFunctor C i).map T.mor₂) := by
  have : Epi ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl]
    exact (isZero_of_isLE T.obj₁ n (i + 1) (by omega)).eq_of_tgt _ _
  have : Mono ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff T hT i]
    exact (isZero_of_isLE T.obj₁ n i hi).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- The truncation `τ_{< b} K ⟶ K` of the canonical t-structure is an isomorphism on cohomology
in the degrees `i < b`. -/
lemma isIso_homologyFunctor_map_truncLTι (b i : ℤ) (hi : i < b) (K : DerivedCategory C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLTι b).app K)) :=
  isIso_homologyFunctor_map_mor₁ ((TStructure.t.triangleLTGE b).obj K)
    (TStructure.t.triangleLTGE_distinguished b K) b i hi

/-- The truncation `K ⟶ τ_{≥ b} K` of the canonical t-structure is an isomorphism on cohomology
in the degrees `b ≤ i`. -/
lemma isIso_homologyFunctor_map_truncGEπ (b i : ℤ) (hi : b ≤ i) (K : DerivedCategory C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ b).app K)) :=
  isIso_homologyFunctor_map_mor₂ ((TStructure.t.triangleLTGE b).obj K)
    (TStructure.t.triangleLTGE_distinguished b K) (b - 1) i (by omega)

/-- An extension of an object of `smd(G^{⋆ (q + 1)})` by an object of `smd(G^{⋆ (p + 1)})` lies in
`smd(G^{⋆ (p + q + 2)})`. The number of factors is a side condition `p + q + 1 = m`, so that no
arithmetic is left at the call sites. -/
private lemma retractClosure_extensionProductIter_of_distTriang
    (G : ObjectProperty (DerivedCategory C)) [G.IsClosedUnderBinaryProducts] {p q m : ℕ}
    (hm : p + q + 1 = m) (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : (G.extensionProductIter p).retractClosure T.obj₁)
    (h₃ : (G.extensionProductIter q).retractClosure T.obj₃) :
    (G.extensionProductIter m).retractClosure T.obj₂ := by
  subst hm
  rw [(retractClosure_extensionProductIter_isClosedUnderBinaryProducts_and_add G p q).2.2.2]
  exact le_retractClosure _ _ ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, h₁, h₃⟩

/-- An object of the derived category whose cohomology is concentrated in a single degree `a` and
lies there in a class `F` closed under isomorphisms is in `smd(G)`, as soon as `G` contains the
objects of `F` placed in degree `a`. -/
private lemma retractClosure_of_isGE_of_isLE (F : ObjectProperty C)
    [F.IsClosedUnderIsomorphisms] (G : ObjectProperty (DerivedCategory C)) (a : ℤ)
    (hG : ∀ Y : C, F Y → G.retractClosure ((singleFunctor C a).obj Y))
    (X : DerivedCategory C) [X.IsGE a] [X.IsLE a]
    (hX : F ((homologyFunctor C a).obj X)) :
    G.retractClosure X := by
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X a
  refine G.retractClosure.prop_of_iso e.symm (hG Y (F.prop_of_iso ?_ hX))
  exact (homologyFunctor C a).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C a).app Y

/-- Part (2) of [Stacks, Tag 0FX7]: an object of the derived category whose cohomology is
concentrated in `[a, a + n]` and lies there in a class `F` closed under isomorphisms is a
summand of an `n`-fold extension of objects of `G`, as soon as `G` contains the objects of `F`
placed in the degrees `a, …, a + n`. -/
private lemma retractClosure_extensionProductIter_of_isGE_of_isLE (F : ObjectProperty C)
    [F.IsClosedUnderIsomorphisms] (G : ObjectProperty (DerivedCategory C))
    [G.IsClosedUnderBinaryProducts] (a : ℤ) (n : ℕ)
    (hG : ∀ i : ℤ, a ≤ i → i ≤ a + n → ∀ Y : C, F Y →
      G.retractClosure ((singleFunctor C i).obj Y)) :
    ∀ (b : ℤ), a + n = b → ∀ (K : DerivedCategory C) [K.IsGE a] [K.IsLE b],
      (∀ i : ℤ, a ≤ i → i ≤ b → F ((homologyFunctor C i).obj K)) →
      (G.extensionProductIter n).retractClosure K := by
  induction n with
  | zero =>
    intro b hb K hge hle hK
    obtain rfl : a = b := by omega
    exact retractClosure_of_isGE_of_isLE F G a (fun Y hY => hG a le_rfl (by omega) Y hY) K
      (hK a le_rfl le_rfl)
  | succ n ih =>
    intro b hb K hge hle hK
    have h₁ : (G.extensionProductIter n).retractClosure ((TStructure.t.truncLT b).obj K) := by
      refine ih (fun i hi hi' Y hY => hG i hi (by omega) Y hY) (b - 1) (by omega) _
        (fun i hi hi' => ?_)
      have := isIso_homologyFunctor_map_truncLTι b i (by omega) K
      exact F.prop_of_iso
        (asIso ((homologyFunctor C i).map ((TStructure.t.truncLTι b).app K))).symm
        (hK i hi (by omega))
    have h₃ : (G.extensionProductIter 0).retractClosure ((TStructure.t.truncGE b).obj K) := by
      have := isIso_homologyFunctor_map_truncGEπ b b le_rfl K
      rw [extensionProductIter_zero]
      exact retractClosure_of_isGE_of_isLE F G b (fun Y hY => hG b (by omega) (by omega) Y hY) _
        (F.prop_of_iso (asIso ((homologyFunctor C b).map ((TStructure.t.truncGEπ b).app K)))
          (hK b (by omega) le_rfl))
    exact retractClosure_extensionProductIter_of_distTriang G (p := n) (q := 0) (by omega)
      ((TStructure.t.triangleLTGE b).obj K) (TStructure.t.triangleLTGE_distinguished b K) h₁ h₃

section StupidTrunc

open ComplexShape HomologicalComplex

/-- The embedding of the degrees `≤ m` into `ℤ` sends the index `m - i` to a given degree
`i ≤ m`. -/
lemma embeddingUpIntLE_f_toNat (m i : ℤ) (hi : i ≤ m) :
    (embeddingUpIntLE m).f (m - i).toNat = i := by
  change m - ((m - i).toNat : ℤ) = i; omega

omit [HasDerivedCategory.{w} C] in
/-- The stupid truncation of `L` in the degrees `≤ m` vanishes in the degrees `> m`. -/
lemma isZero_stupidTrunc_X_of_lt (L : CochainComplex C ℤ) {m i : ℤ} (hi : m < i) :
    IsZero ((L.stupidTrunc (embeddingUpIntLE m)).X i) :=
  L.isZero_stupidTrunc_X _ i ((notMem_range_embeddingUpIntLE_iff _ i).2 (by omega))

omit [HasDerivedCategory.{w} C] in
/-- A cochain complex `L` which vanishes in the degrees `> b` receives a morphism from its
degree-`b` term placed in degree `b` which is an isomorphism in degree `b`. -/
lemma exists_hom_from_single_isIso_f (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] :
    ∃ ι : (single C (ComplexShape.up ℤ) b).obj (L.X b) ⟶ L, IsIso (ι.f b) := by
  refine ⟨mkHomFromSingle (𝟙 (L.X b)) (fun k hk => ?_), ?_⟩
  · simp only [ComplexShape.up_Rel] at hk
    exact (L.isZero_of_isStrictlyLE b k (by omega)).eq_of_tgt _ _
  · rw [mkHomFromSingle_f, Category.comp_id]
    infer_instance

omit [HasDerivedCategory.{w} C] in
/-- A cochain complex `L` which vanishes in the degrees `> b` maps to its stupid truncation in
the degrees `≤ b - 1` by a morphism which is an isomorphism in every degree other than `b`. -/
lemma exists_hom_to_stupidTrunc_isIso_f (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] :
    ∃ π : L ⟶ L.stupidTrunc (embeddingUpIntLE (b - 1)), ∀ i : ℤ, i ≠ b → IsIso (π.f i) := by
  have hlift : (embeddingUpIntLE (b - 1)).HasLift
      (𝟙 (L.restriction (embeddingUpIntLE (b - 1)))) :=
    fun _ hj _ _ => (hj.false_of_isTruncLE).elim
  refine ⟨(embeddingUpIntLE (b - 1)).liftExtend _ hlift, fun i hi => ?_⟩
  by_cases hib : i ≤ b - 1
  · refine ((embeddingUpIntLE (b - 1)).isIso_liftExtend_f_iff _ hlift
      (embeddingUpIntLE_f_toNat (b - 1) i hib)).2 ?_
    rw [HomologicalComplex.id_f]
    infer_instance
  · exact (L.isZero_of_isStrictlyLE b i (by omega)).isIso (isZero_stupidTrunc_X_of_lt L
      (show b - 1 < i by omega)) _

/-- The stupid filtration in the top degree: a cochain complex `L` which vanishes in degrees
`> b` is an extension, in the derived category, of its stupid truncation in the degrees `≤ b - 1`
by its degree-`b` term placed in degree `b`. -/
lemma exists_distTriang_singleFunctor_obj_X_stupidTrunc (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] :
    ∃ (f : (singleFunctor C b).obj (L.X b) ⟶ Q.obj L)
      (g : Q.obj L ⟶ Q.obj (L.stupidTrunc (embeddingUpIntLE (b - 1))))
      (h : Q.obj (L.stupidTrunc (embeddingUpIntLE (b - 1))) ⟶
        ((singleFunctor C b).obj (L.X b))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory C) := by
  obtain ⟨ι, hιb⟩ := exists_hom_from_single_isIso_f L b
  obtain ⟨π, hπ⟩ := exists_hom_to_stupidTrunc_isIso_f L b
  have hMb : IsZero ((L.stupidTrunc (embeddingUpIntLE (b - 1))).X b) :=
    isZero_stupidTrunc_X_of_lt L (by omega)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi; exact hMb.eq_of_tgt _ _
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi).eq_of_src _ _
  have hSE : (ShortComplex.mk ι π hcomp).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => by
      by_cases hi : i = b
      · subst hi
        exact ShortComplex.shortExact_of_isIso_f_of_isZero_X₃ _ hιb hMb
      · exact ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _
          (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi) (hπ i hi)
  exact ⟨_, _, _, mk_mem_distTriang_of_iso _ (triangleOfSES_distinguished hSE)
    ((singleFunctorIsoCompQ C b).app (L.X b))⟩

/-- Part (4) of [Stacks, Tag 0FX7]: a cochain complex which vanishes outside `[a, a + n]` and
whose terms there lie in a class `F` closed under isomorphisms defines a summand of an `n`-fold
extension of objects of `G`, as soon as `G` contains the objects of `F` placed in the degrees
`a, …, a + n`. -/
private lemma retractClosure_extensionProductIter_of_isStrictlyGE_of_isStrictlyLE
    (F : ObjectProperty C) [F.IsClosedUnderIsomorphisms] (G : ObjectProperty (DerivedCategory C))
    [G.IsClosedUnderBinaryProducts] (a : ℤ) (n : ℕ)
    (hG : ∀ i : ℤ, a ≤ i → i ≤ a + n → ∀ Y : C, F Y →
      G.retractClosure ((singleFunctor C i).obj Y)) :
    ∀ (b : ℤ), a + n = b → ∀ (L : CochainComplex C ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b],
      (∀ i : ℤ, a ≤ i → i ≤ b → F (L.X i)) →
      (G.extensionProductIter n).retractClosure (Q.obj L) := by
  induction n with
  | zero =>
    intro b hb L hge hle hL
    obtain rfl : a = b := by omega
    obtain ⟨Y, ⟨e⟩⟩ := CochainComplex.exists_iso_single L a
    rw [extensionProductIter_zero]
    refine G.retractClosure.prop_of_iso
      (((singleFunctorIsoCompQ C a).app Y).symm ≪≫ (Q.mapIso e).symm)
      (hG a le_rfl (by omega) Y (F.prop_of_iso ?_ (hL a le_rfl le_rfl)))
    exact (HomologicalComplex.eval C _ a).mapIso e ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a Y
  | succ n ih =>
    intro b hb L hge hle hL
    obtain ⟨f, g, h, hT⟩ := exists_distTriang_singleFunctor_obj_X_stupidTrunc L b
    refine retractClosure_extensionProductIter_of_distTriang G (p := 0) (q := n) (by omega) _
      hT ?_ ?_
    · rw [extensionProductIter_zero]
      exact hG b (by omega) (by omega) _ (hL b (by omega) le_rfl)
    · exact ih (fun i hi hi' Y hY => hG i hi (by omega) Y hY) (b - 1) (by omega) _
        (fun i hi hi' => F.prop_of_iso
          (L.stupidTruncXIso _ (embeddingUpIntLE_f_toNat (b - 1) i hi')).symm
          (hL i hi (by omega)))

end StupidTrunc

/-- Let `C` be an abelian category and `E` a class of objects of `C`, viewed inside the derived
category `D(C)`. Let `a ≤ b`. (1) If the cohomology of `K : D(C)` vanishes outside `[a, b]` and
each `H^i(K)` with `i ∈ [a, b]` is a direct summand of a finite direct sum of objects of `E`, then
`K` is a direct summand of a `(b - a)`-fold extension of finite direct sums of objects of `E`
placed in degrees `[a, b]`, that is, `K ∈ smd(add(E[a, b])^{⋆ (b - a + 1)})`. (2) The same
conclusion holds for `K = Q.obj L` when `L` is a cochain complex vanishing outside `[a, b]` whose
terms `L^i` with `i ∈ [a, b]` are direct summands of finite direct sums of objects of `E`. The
special cases where the objects `H^i(K)`, resp. `L^i`, are themselves in `E` are parts (1) and (3)
of [Stacks, Tag 0FX7]. -/
@[stacks 0FX7]
theorem prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X
    (E : ObjectProperty C) {a b : ℤ} (hab : a ≤ b) :
    (∀ (K : DerivedCategory C) [K.IsGE a] [K.IsLE b],
        (∀ i ∈ Set.Icc a b,
          E.binaryProductsClosure.retractClosure ((homologyFunctor C i).obj K)) →
        ((⨆ i ∈ Set.Icc a b,
            E.map (singleFunctor C i)).binaryProductsClosure.extensionProductIter
          (b - a).toNat).retractClosure K) ∧
    (∀ (L : CochainComplex C ℤ) [L.IsStrictlyGE a] [L.IsStrictlyLE b],
        (∀ i ∈ Set.Icc a b, E.binaryProductsClosure.retractClosure (L.X i)) →
        ((⨆ i ∈ Set.Icc a b,
            E.map (singleFunctor C i)).binaryProductsClosure.extensionProductIter
          (b - a).toNat).retractClosure (Q.obj L)) := by
  have key : ∀ i : ℤ, a ≤ i → i ≤ a + ((b - a).toNat : ℤ) → ∀ Y : C,
      E.binaryProductsClosure.retractClosure Y →
      (⨆ i ∈ Set.Icc a b,
        E.map (singleFunctor C i)).binaryProductsClosure.retractClosure
          ((singleFunctor C i).obj Y) := by
    intro i hi hi' Y hY
    refine monotone_retractClosure ?_ _ (retractClosure_binaryProductsClosure_map _ E hY)
    exact limitsClosure_monotone _ (le_iSup₂ (f := fun (i : ℤ) (_ : i ∈ Set.Icc a b) =>
      E.map (singleFunctor C i)) i (Set.mem_Icc.2 ⟨hi, by omega⟩))
  refine ⟨fun K _ _ hK => ?_, fun L _ _ hL => ?_⟩
  · exact retractClosure_extensionProductIter_of_isGE_of_isLE _ _ a (b - a).toNat key b
      (by omega) K (fun i hi hi' => hK i (Set.mem_Icc.2 ⟨hi, hi'⟩))
  · exact retractClosure_extensionProductIter_of_isStrictlyGE_of_isStrictlyLE _ _ a
      (b - a).toNat key b (by omega) L (fun i hi hi' => hL i (Set.mem_Icc.2 ⟨hi, hi'⟩))

end DerivedCategory

namespace CategoryTheory.Functor

open Limits Pretriangulated ObjectProperty

section Window

variable {C : Type*} [Category C] [HasShift C ℤ] {A : Type*} [Category A] (H : C ⥤ A)

/-- Given `H : C ⥤ A` with `C` equipped with a `ℤ`-shift, and with the convention
`H^i(X) = H(X⟦i⟧)`, this is the class of objects `X` of `C` whose `H`-cohomology is concentrated
in the window `[u, v]`, i.e. such that `H^i(X) = 0` for `i ∉ [u, v]`. -/
private def concentratedIn (u v : ℤ) : ObjectProperty C :=
  fun X ↦ ∀ i ∉ Set.Icc u v, IsZero (H.obj (X⟦i⟧))

/-- A wider window is a weaker condition. -/
private lemma concentratedIn_le_concentratedIn {u v u' v' : ℤ} (hu : u' ≤ u) (hv : v ≤ v') :
    concentratedIn H u v ≤ concentratedIn H u' v' :=
  fun _ hX i hi ↦ hX i fun hi' ↦ hi (Set.Icc_subset_Icc hu hv hi')

/-- Composing two shifts: `H^i(X⟦j⟧) = H^{j + i}(X)`. -/
lemma isZero_obj_shift_shift_iff (X : C) {i j k : ℤ} (h : j + i = k) :
    IsZero (H.obj ((X⟦j⟧)⟦i⟧)) ↔ IsZero (H.obj (X⟦k⟧)) :=
  (Iso.isZero_iff (H.mapIso ((shiftFunctorAdd' C j i k h).app X))).symm

/-- Shifting by `j` translates the window by `j`. -/
private lemma concentratedIn_shift (u v j : ℤ) :
    (concentratedIn H u v).shift j = concentratedIn H (u + j) (v + j) := by
  ext X
  exact ⟨fun hX i hi ↦ (isZero_obj_shift_shift_iff H X (i := i - j) (by omega)).1
      (hX _ (by simp only [Set.mem_Icc] at hi ⊢; omega)),
    fun hX i hi ↦ (isZero_obj_shift_shift_iff H X (k := j + i) rfl).2
      (hX _ (by simp only [Set.mem_Icc] at hi ⊢; omega))⟩

private instance isClosedUnderIsomorphisms_concentratedIn (u v : ℤ) :
    (concentratedIn H u v).IsClosedUnderIsomorphisms where
  of_iso e hX i hi := (hX i hi).of_iso ((CategoryTheory.shiftFunctor C i ⋙ H).mapIso e.symm)

private instance isStableUnderRetracts_concentratedIn (u v : ℤ) :
    (concentratedIn H u v).IsStableUnderRetracts where
  of_retract r hY i hi := (hY i hi).of_retract (r.map (CategoryTheory.shiftFunctor C i ⋙ H))

private instance isClosedUnderLimitsOfShape_concentratedIn [HasZeroMorphisms A] (u v : ℤ)
    (J : Type*) [Category J]
    [∀ i : ℤ, PreservesLimitsOfShape J (CategoryTheory.shiftFunctor C i ⋙ H)] :
    (concentratedIn H u v).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le X := by
    rintro ⟨h⟩ i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (CategoryTheory.shiftFunctor C i ⋙ H) h.isLimit).hom_ext
      fun j ↦ (h.prop_diag_obj j i hi).eq_of_tgt _ _

/-- The shifts by `j ∈ [c, d]` of a class `E` of objects with cohomology in `[a, b]` have their
cohomology in `[a + c, b + d]`. This is the window arithmetic of [Stacks, Tag 0FX8]. -/
private lemma iSup_shift_le_concentratedIn {E : ObjectProperty C} {a b : ℤ}
    (hE : E ≤ concentratedIn H a b) (c d : ℤ) :
    ⨆ j ∈ Set.Icc c d, E.shift j ≤ concentratedIn H (a + c) (b + d) := by
  refine iSup₂_le fun j hj ↦ ?_
  rw [Set.mem_Icc] at hj
  calc E.shift j ≤ (concentratedIn H a b).shift j := fun _ hX ↦ hE _ hX
    _ = concentratedIn H (a + j) (b + j) := concentratedIn_shift H a b j
    _ ≤ concentratedIn H (a + c) (b + d) :=
        concentratedIn_le_concentratedIn H (by omega) (by omega)

end Window

section Pretriangulated

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type*} [Category A] [Abelian A]

/-- Objects with cohomology in a fixed window are closed under extensions: if
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is distinguished and `H^i(X₁) = H^i(X₃) = 0`, then `H^i(X₂) = 0`. -/
private instance isTriangulatedClosed₂_concentratedIn (H : C ⥤ A) [H.IsHomological] (u v : ℤ) :
    (concentratedIn H u v).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ i hi ↦
    (H.map_distinguished_exact _ (Triangle.shift_distinguished T hT i)).isZero_of_both_zeros
      ((h₁ i hi).eq_of_src _ _) ((h₃ i hi).eq_of_tgt _ _)

/-- Let `H : C ⥤ A` be a homological functor from a triangulated category to an abelian category,
with `H^i(X) = H(X⟦i⟧)`, and let `E` be a class of objects of `C` such that `H^i(E) = 0` for
`E ∈ E` and `i ∉ [a, b]`. Then every object `X` which is a direct summand of an `n`-fold extension
of finite direct sums of objects `E⟦-j⟧` with `E ∈ E` and `j ∈ [c, d]` satisfies `H^i(X) = 0` for
`i ∉ [a + c, b + d]`. In the notation of [Stacks, Tag 0FX0], for
`X ∈ smd(add(E[c, d])^{⋆ (n + 1)})` we have `H^i(X) = 0` for `i ∉ [a + c, b + d]`; the window does
not depend on the number of extensions, so it is sharper than the window `[-m + na, m + nb]` of
[Stacks, Tag 0FX8], which it implies for `a ≤ 0 ≤ b`, `c = -m`, `d = m`. -/
@[stacks 0FX8]
theorem isZero_obj_shift_of_retractClosure_extensionProductIter
    (H : C ⥤ A) [H.IsHomological] (E : ObjectProperty C) {a b : ℤ}
    (hE : ∀ ⦃Y : C⦄, E Y → ∀ i ∉ Set.Icc a b, IsZero (H.obj (Y⟦i⟧)))
    (c d : ℤ) (n : ℕ) {X : C}
    (hX : ((⨆ j ∈ Set.Icc c d,
      E.isoClosure.shift j).binaryProductsClosure.extensionProductIter n).retractClosure X)
    {i : ℤ} (hi : i ∉ Set.Icc (a + c) (b + d)) :
    IsZero (H.obj (X⟦i⟧)) :=
  (retractClosure_le_iff _ _).2 (extensionProductIter_le_of_isTriangulatedClosed₂ _
    (limitsClosure_le (iSup_shift_le_concentratedIn H
      ((isoClosure_le_iff _ _).2 fun _ hY ↦ hE hY) c d)) n) X hX i hi

end Pretriangulated

end CategoryTheory.Functor

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Stacks project Lemma 13.35.3 (Tag 0FX3), part of Section 13.35
"Operations on full subcategories" (Tag 0FX0).

Let `T` be a triangulated category. We identify full subcategories of `T`
with subsets of `Ob(T)`, the class of objects of `T`. A triangulated category
is in particular additive, so every finite collection of objects has a direct
sum (biproduct); in particular for any two objects `X, X'` the direct sum
`X ⊕ X'` exists.

A full subcategory `C` (i.e. a subclass `C ⊆ Ob(T)`) is said to be **closed
under (finite) direct sums** when for all `X, X' ∈ C` we have `X ⊕ X' ∈ C`.
(Closure under binary direct sums, together with the zero object being a direct
sum of the empty family, gives closure under all finite direct sums; the
essential content is the binary case, which is the form used below.)

Given full subcategories `A, B ⊆ Ob(T)`:

1. `smd A`: the full subcategory of objects isomorphic to a direct summand of
   an object of `A`. Precisely, `X ∈ smd A` iff there exist `A ∈ A` and an
   object `Y` together with an isomorphism `A ≅ X ⊕ Y`.

2. `add A`: the full subcategory of objects isomorphic to a finite direct sum
   of objects of `A`. Precisely, `X ∈ add A` iff there exist `n ≥ 0` and
   objects `A_1, …, A_n ∈ A` together with an isomorphism
   `X ≅ A_1 ⊕ ⋯ ⊕ A_n`. (The case `n = 0` gives the zero object.)

3. `A ⋆ B` (star / extension): the full subcategory of objects `X` that fit
   into a distinguished triangle `A → X → B → A[1]` with `A ∈ A` and `B ∈ B`.

Main statements:

1. `add A ⋆ add B` is closed under direct sums.
2. `smd (add A)` is closed under direct sums.
-/

open CategoryTheory CategoryTheory.Pretriangulated
  Limits

-- We work in a triangulated category, modeled as a pretriangulated category
-- with the additive structure (finite biproducts) that always exists.
variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasFiniteBiproducts C]

-- Main Definition(s)

/-- A full subcategory (subset of objects) is *closed under (binary) direct
sums* when for all `X, X' ∈ 𝒞` we have `X ⊞ X' ∈ 𝒞`. As explained in the
problem, this binary form captures the essential content of closure under all
finite direct sums. -/
def ClosedUnderDirectSums (𝒞 : Set C) : Prop :=
  ∀ ⦃X X' : C⦄, X ∈ 𝒞 → X' ∈ 𝒞 → (X ⊞ X') ∈ 𝒞

/-- `smd 𝒜` consists of all objects `X` that are isomorphic to a direct
summand of an object of `𝒜`: there exist `A ∈ 𝒜` and an object `Y` with an
isomorphism `A ≅ X ⊞ Y`. -/
def smd (𝒜 : Set C) : Set C :=
  {X | ∃ (A : C) (Y : C), A ∈ 𝒜 ∧ Nonempty (A ≅ X ⊞ Y)}

/-- `add 𝒜` consists of all objects `X` that are isomorphic to a finite direct
sum of objects of `𝒜`: there exist `n : ℕ`, a family `f : Fin n → C` with each
`f i ∈ 𝒜`, and an isomorphism `X ≅ ⨁ f`. The case `n = 0` yields the zero
object. -/
def add (𝒜 : Set C) : Set C :=
  {X | ∃ (n : ℕ) (f : Fin n → C), (∀ i, f i ∈ 𝒜) ∧ Nonempty (X ≅ ⨁ f)}

/-- The extension (star) operation `𝒜 ⋆ ℬ` consists of all objects `X` that fit
into a distinguished triangle `A → X → B → A[1]` with `A ∈ 𝒜` and `B ∈ ℬ`.
We allow an isomorphism `T.obj₂ ≅ X` so that the subcategory is closed under
isomorphism (full subcategories are closed under isomorphism). -/
def starOp (𝒜 ℬ : Set C) : Set C :=
  {X | ∃ T : Triangle C, T ∈ distinguishedTriangles ∧ T.obj₁ ∈ 𝒜 ∧ T.obj₃ ∈ ℬ ∧
        Nonempty (T.obj₂ ≅ X)}

@[inherit_doc] infixr:65 " ⋆ " => starOp

-- Helper lemmas

/-- Splitting a finite biproduct over a sum index type into a binary biproduct.
This realizes `⨁ (A_1 ⊕ ⋯) ≅ (⨁ f) ⊞ (⨁ g)` and is the algebraic core behind
"`add 𝒜` is closed under direct sums" (concatenating two finite families). -/
noncomputable def biproductSumIso (n m : ℕ) (f : Fin n → C) (g : Fin m → C) :
    ⨁ (Sum.elim f g) ≅ (⨁ f) ⊞ (⨁ g) where
  hom := biproduct.desc (fun ij => (match ij with
    | Sum.inl i => biproduct.ι f i ≫ biprod.inl
    | Sum.inr j => biproduct.ι g j ≫ biprod.inr :
      Sum.elim f g ij ⟶ (⨁ f) ⊞ (⨁ g)))
  inv := biprod.desc
    (biproduct.desc (fun i => biproduct.ι (Sum.elim f g) (Sum.inl i)))
    (biproduct.desc (fun j => biproduct.ι (Sum.elim f g) (Sum.inr j)))
  hom_inv_id := by
    apply biproduct.hom_ext'
    rintro (i | j) <;> simp [biproduct.ι_desc_assoc]
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biproduct.hom_ext'
      intro i; simp [biproduct.ι_desc_assoc]
    · apply biproduct.hom_ext'
      intro j; simp [biproduct.ι_desc_assoc]

/-- `add 𝒜` is closed under binary direct sums. If `X ≅ ⨁ f` (`f : Fin n → 𝒜`)
and `X' ≅ ⨁ g` (`g : Fin m → 𝒜`), then `X ⊞ X'` is iso to the biproduct over the
concatenated family `Sum.elim f g` reindexed along `finSumFinEquiv`, all of whose
members lie in `𝒜`. -/
theorem add_closedUnderDirectSums (𝒜 : Set C) : ClosedUnderDirectSums (add 𝒜) := by
  rintro X X' ⟨n, f, hf, ⟨ex⟩⟩ ⟨m, g, hg, ⟨ey⟩⟩
  refine ⟨n + m, fun k => Sum.elim f g (finSumFinEquiv.symm k), ?_, ⟨?_⟩⟩
  · intro k
    rcases h : finSumFinEquiv.symm k with i | j
    · simpa [h] using hf i
    · simpa [h] using hg j
  · -- X ⊞ X' ≅ ⨁ (combined family)
    refine biprod.mapIso ex ey ≪≫ (biproductSumIso n m f g).symm ≪≫ ?_
    refine eqToIso ?_ ≪≫ biproduct.reindex finSumFinEquiv
      (fun k => Sum.elim f g (finSumFinEquiv.symm k))
    congr 1
    funext x
    simp

/-- Rearrangement isomorphism for a four-fold binary biproduct:
`(X ⊞ Y) ⊞ (X' ⊞ Y') ≅ (X ⊞ X') ⊞ (Y ⊞ Y')`. Used in statement (2) to exhibit
`X ⊞ X'` as a summand of `(X ⊞ Y) ⊞ (X' ⊞ Y')`. -/
noncomputable def biprodRearrange (X Y X' Y' : C) :
    (X ⊞ Y) ⊞ (X' ⊞ Y') ≅ (X ⊞ X') ⊞ (Y ⊞ Y') where
  hom := biprod.lift
    (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  inv := biprod.lift
    (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

omit [HasShift C ℤ] in
omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- `add 𝒜` is closed under isomorphism. -/
theorem add_iso {𝒜 : Set C} {X X' : C} (h : X ∈ add 𝒜) (e : Nonempty (X' ≅ X)) :
    X' ∈ add 𝒜 := by
  obtain ⟨n, f, hf, ⟨ex⟩⟩ := h
  obtain ⟨e⟩ := e
  exact ⟨n, f, hf, ⟨e ≪≫ ex⟩⟩

/-- The biproduct over `Fin 2` splits as a binary biproduct `⨁ g ≅ g 0 ⊞ g 1`. -/
noncomputable def finBiprod2 (g : Fin 2 → C) : ⨁ g ≅ g 0 ⊞ g 1 where
  hom := biprod.lift (biproduct.π g 0) (biproduct.π g 1)
  inv := biprod.desc (biproduct.ι g 0) (biproduct.ι g 1)
  hom_inv_id := by
    apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    fin_cases i <;> fin_cases j <;> simp
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

/-- The product over `Fin 2` splits as a binary biproduct `(∏ᶜ g) ≅ g 0 ⊞ g 1`.
Used to identify the legs of `productTriangle ![T, T']` with binary biproducts. -/
noncomputable def finProd2 (g : Fin 2 → C) : (∏ᶜ g) ≅ g 0 ⊞ g 1 :=
  (biproduct.isoProduct g).symm ≪≫ finBiprod2 g

-- Main Statement(s)

/-- **Stacks 0FX3 (1).** `add 𝒜 ⋆ add ℬ` is closed under direct sums:
for all `X, X' ∈ add 𝒜 ⋆ add ℬ` we have `X ⊞ X' ∈ add 𝒜 ⋆ add ℬ`.

Proof (as in the source): pick distinguished triangles `T : A → X → B → A[1]`
and `T' : A' → X' → B' → A'[1]` with `A, A' ∈ add 𝒜`, `B, B' ∈ add ℬ`. The product
triangle `productTriangle ![T, T']` is distinguished (`productTriangle_distinguished`),
its legs are the `Fin 2`-products of the legs of `T, T'`, which via `finProd2` are the
binary biproducts `A ⊞ A'`, `X ⊞ X'`, `B ⊞ B'`. Since `add` is closed under `⊞`
(`add_closedUnderDirectSums`) and under iso (`add_iso`), `A ⊞ A' ∈ add 𝒜`,
`B ⊞ B' ∈ add ℬ`, and the middle object is iso to `X ⊞ X'`. -/
@[stacks 0FX3 "(1)"]
theorem closedUnderDirectSums_add_star_add (𝒜 ℬ : Set C) :
    ClosedUnderDirectSums (add 𝒜 ⋆ add ℬ) := by
  rintro X X' ⟨T, hT, hT1, hT3, ⟨eX⟩⟩ ⟨T', hT', hT'1, hT'3, ⟨eX'⟩⟩
  -- product triangle over Fin 2
  set F : Fin 2 → Triangle C := ![T, T'] with hF
  have hFd : ∀ j, F j ∈ distinguishedTriangles := by
    intro j; fin_cases j
    · simpa [hF] using hT
    · simpa [hF] using hT'
  have hdist := productTriangle_distinguished F hFd
  refine ⟨productTriangle F, hdist, ?_, ?_, ?_⟩
  · -- obj₁ ∈ add 𝒜
    refine add_iso (X := T.obj₁ ⊞ T'.obj₁) (add_closedUnderDirectSums 𝒜 hT1 hT'1) ⟨?_⟩
    exact finProd2 (fun j => (F j).obj₁)
  · -- obj₃ ∈ add ℬ
    refine add_iso (X := T.obj₃ ⊞ T'.obj₃) (add_closedUnderDirectSums ℬ hT3 hT'3) ⟨?_⟩
    exact finProd2 (fun j => (F j).obj₃)
  · -- obj₂ ≅ X ⊞ X'
    exact ⟨finProd2 (fun j => (F j).obj₂) ≪≫ biprod.mapIso eX eX'⟩

/-- **Stacks 0FX3 (2).** `smd (add 𝒜)` is closed under direct sums:
for all `X, X' ∈ smd (add 𝒜)` we have `X ⊞ X' ∈ smd (add 𝒜)`.

Proof (as in the source): write `A ≅ X ⊞ Y`, `A' ≅ X' ⊞ Y'` with
`A, A' ∈ add 𝒜`. Then `A ⊞ A' ∈ add 𝒜` (`add_closedUnderDirectSums`) and
`A ⊞ A' ≅ (X ⊞ Y) ⊞ (X' ⊞ Y') ≅ (X ⊞ X') ⊞ (Y ⊞ Y')` (`biprodRearrange`),
exhibiting `X ⊞ X'` as a direct summand of `A ⊞ A' ∈ add 𝒜`. -/
@[stacks 0FX3 "(2)"]
theorem closedUnderDirectSums_smd_add (𝒜 : Set C) :
    ClosedUnderDirectSums (smd (add 𝒜)) := by
  rintro X X' ⟨A, Y, hA, ⟨eA⟩⟩ ⟨A', Y', hA', ⟨eA'⟩⟩
  refine ⟨A ⊞ A', Y ⊞ Y', add_closedUnderDirectSums 𝒜 hA hA', ⟨?_⟩⟩
  exact biprod.mapIso eA eA' ≪≫ biprodRearrange X Y X' Y'

end

end
