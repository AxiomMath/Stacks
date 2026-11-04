module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.KernelCoimage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered injective resolutions of bounded below filtered complexes

Let `𝒜` be an abelian category with enough injectives and let `K^•` be a filtered cochain complex
of `𝒜`, bounded below and with each `K^n` of finite filtration, i.e. an object of
`K^+(Fil^f(𝒜))`. This file proves [Stacks, Tag 05TW]: there is a filtered quasi-isomorphism
`α : K^• ⟶ I^•` which is a strict monomorphism, with `I^•` bounded below by the same degree and
every `I^n` filtered injective.

The source's construction is a Cartan–Eilenberg resolution, in two halves. Writing `d = d_K`, the
short exact sequences `0 → Ker(d^i) → K^i → Coim(d^i) → 0` of `Fil^f(𝒜)` and the maps
`u_i : Coim(d^i) → Ker(d^{i + 1})` factor the differential of `K^•` into strict monomorphisms and
strict epimorphisms. The first half resolves `Ker(d^i)` and `Coim(d^i)` separately (Lemma 05TT),
lifts `u_i` to the resolutions (Lemma 05TU) and fills in the short exact sequences by termwise
split short exact sequences of resolutions (Lemma 05TV); this produces the `ResolutionSystem`
below, filtered quasi-isomorphisms `ε_i : K^i[0] ⟶ I_i^•` and morphisms `d_i : I_i^• ⟶ I_{i + 1}^•`
with `d_i ≫ d_{i + 1} = 0` commuting with the differential of `K^•`. The second half takes the
total complex of the double complex `I^{i, n} = I_i^n` (Homology, Definition 012Z); the map to it
is a filtered quasi-isomorphism because `gr^p` is additive, hence commutes with the total complex,
and by Homology, Lemma 0133.

## Main results

* `CochainComplex.exists_mono_isStrictHom_filteredQuasiIso_isStrictlyGE_injective_gradedPiece`:
  Lemma 05TW.

## Implementation notes

*What this reuses.* The first half is assembled from the three lemmas of
`StacksFrontier/Algebra/Homology/DerivedCategory/Filtered/`:
`CochainComplex.exists_filteredQuasiIso_isStrictlyGE_injective_gradedPiece` (05TT),
`CochainComplex.exists_hom_comp_eq_of_filteredQuasiIso_of_injective_gradedPiece` (05TU) and
`CochainComplex.exists_termwiseSplit_shortExact_of_filteredQuasiIso_of_injective_gr` (05TV) with
its post-processing
`CochainComplex.isStrictlyGE_isDegreewiseFinite_injective_gr_filteredQuasiIso_of_termwiseSplit`,
applied to the filtered objects
`CategoryTheory.FilteredObject.kernelFil`, `coimageFil` and the connecting map `coimKer` of a
filtered complex, placed in degree `0` by `CategoryTheory.FilteredObject.singleFil`. The second
half uses [Stacks, Tag 05S3] (`CochainComplex.quasiIso_natTrans_app_of_filteredQuasiIso`) and
Weibel's acyclic assembly lemma (`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map`,
[Stacks, Tag 0133]).

*The source's shift is not performed.* The source replaces `K^•` by a shift so that `K^n = 0` for
`n < 0` and concludes only that `I^•` is bounded below. The bound `a` is carried through instead:
the resolutions `I_i^•` of the terms are concentrated in degrees `≥ 0` and are zero for `i < a`, so
the double complex `I^{i, n}` is supported in `i ≥ a`, `n ≥ 0` and its total complex vanishes below
`a`. This is the same construction, with the shift left implicit.

*No recursion, and no resolution below the bound.* The resolutions of the terms are chosen for all
`i` at once: `Ker(d^i)` and `Coim(d^i)` are resolved independently, and the differentials
`d_i = v_i ≫ g_i ≫ u_{i + 1}` square to zero because `u_{i + 1} ≫ v_{i + 1} = 0`, not because
`d_K^i ≫ d_K^{i + 1} = 0`, which is why the source factors the differential of `K^•` through `Coim`
and `Ker`. For `i < a` the term `K^i` vanishes and `K^i[0]` itself is taken as its resolution, so
that `I_i^•` is zero there.

*The total complex needs no infinite coproducts.* The double complex `I^{i, n}` is supported in
`i ≥ a`, `n ≥ 0`, so each antidiagonal `i + n = m` meets its support in a finite set and the
coproducts defining `Tot(I^{•, •})` are finite biproducts; they therefore exist over an arbitrary
abelian category (`StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded`). The same finiteness is
what makes the filtration steps `Tot(F^p I^{•, •})` subobjects of `Tot(I^{•, •})`: a coproduct of
monomorphisms in an abelian category need not be one, an infinite coproduct need not be exact, but
a coproduct over a finite set is a biproduct, hence a product, and a product of monomorphisms is a
monomorphism; this is `mono_mapMap_of_isZero_of_notMem` and `mono_totalMap_of_isZero`. Being a
biproduct also computes the intersection of `Tot(F^p I^{•, •})^n` with a summand of
`Tot(I^{•, •})^n` summandwise (`mapObjIsoBiproduct`, `isPullback_ιMapObj`,
`isPullback_ιTotal_of_isZero`), which is what makes the comparison map strict.

*The second half.* The total complex `Tot(I^{•, •})` is `ResolutionSystem.totalObj` and the
comparison map into it is `ResolutionSystem.totalα`, a monomorphism by
`ResolutionSystem.mono_totalα_hom`. The total complex vanishes below `a`
(`ResolutionSystem.isStrictlyGE_totalObj`), each of its terms has finite filtration
(`ResolutionSystem.isDegreewiseFinite_totalObj`) and its graded pieces consist of injective objects
(`ResolutionSystem.injective_gradedPiece_totalObj`) — in degree `n` such a piece is the cokernel of
a monomorphism between the injective objects `Tot(F^{p + 1} I^{•, •})^n` and `Tot(F^p I^{•, •})^n`,
those being finite biproducts of the `F^p I_i^k`, which are injective because every step of a
finite filtration with injective graded pieces is (`injective_filtration_obj_X`). That the
comparison map is a filtered quasi-isomorphism and strict is
`filteredQuasiIso_isStrictHom_totalα`: the filtration steps of the `ε_i` are quasi-isomorphisms by
[Stacks, Tag 05S3], hence so are those of `α` by Weibel's acyclic assembly lemma, and so is
`gr^p(α)` by the homology sequence of the two sequences `F^{p + 1} ⟶ F^p ⟶ gr^p`; strictness is the
strictness of the `ε_i` in degree `0` pasted with that summandwise intersection.

## References

* [Stacks Project, Tag 05TW](https://stacks.math.columbia.edu/tag/05TW)
* [Stacks Project, Tag 05TT](https://stacks.math.columbia.edu/tag/05TT)
* [Stacks Project, Tag 05TU](https://stacks.math.columbia.edu/tag/05TU)
* [Stacks Project, Tag 05TV](https://stacks.math.columbia.edu/tag/05TV)
* [Stacks Project, Tag 05S1](https://stacks.math.columbia.edu/tag/05S1)
* [Stacks Project, Tag 05S3](https://stacks.math.columbia.edu/tag/05S3)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory Limits Opposite FilteredObject
open CochainComplex.FilteredInjective.Degreewise CochainComplex.FilteredInjective.TermwiseSplit

universe v u

namespace CochainComplex.FilteredInjectiveResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-! ### Filtered objects in a fixed degree, and filtered objects placed in a degree -/

@[local simp]
private lemma evalD_natTrans_app (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) (i : ℤᵒᵖ) :
    (evalD K n).natTrans.app i = (K.filtration.obj i).d n (n + 1) :=
  rfl

/-- A finite filtration stays finite when the filtered object is placed in a degree: in that degree
the filtration is the given one, and `HomologicalComplex.single` preserves isomorphisms and zero
objects. This is the whole-filtration finiteness [Stacks, Tag 05TT] takes, of which
`CategoryTheory.FilteredObject.isDegreewiseFinite_singleFil` is the degreewise consequence. -/
private lemma isFinite_singleFil (j : ℤ) {A : FilteredObject 𝒜 ℤᵒᵖ}
    (hA : A.filtration.IsFinite) : ((singleFil j).obj A).filtration.IsFinite := by
  refine .of_exists ?_ ?_
  · obtain ⟨p, hp⟩ := hA.exists_isIso_ι
    have := hp
    exact ⟨p, inferInstanceAs (IsIso ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map
      (A.filtration.ι.app (op p))))⟩
  · obtain ⟨q, hq⟩ := hA.exists_isZero_obj
    exact ⟨q, Functor.map_isZero (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j) hq⟩

/-- A filtration step of a filtered complex vanishes if the complex does, the structure map being a
monomorphism. -/
private lemma isZero_filtration_obj_of_isZero {J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (hJ : IsZero J.X) (p : ℤᵒᵖ) : IsZero (J.filtration.obj p) :=
  IsZero.of_mono (J.filtration.ι.app p) hJ

/-- A filtration step of a filtered complex vanishes in a degree where the complex does. -/
private lemma isZero_filtration_obj_X_of_isZero {J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    {n : ℤ} (hJ : IsZero (J.X.X n)) (p : ℤᵒᵖ) : IsZero ((J.filtration.obj p).X n) :=
  IsZero.of_mono ((J.filtration.ι.app p).f n) hJ

/-! ### Coproducts of families with finite support -/

/-- A morphism of graded objects which is a monomorphism in each degree induces a monomorphism on
the coproducts `X.mapObj p j ⟶ Y.mapObj p j` over any degree `j` outside a finite subset of whose
fibre the source vanishes: there the coproduct is a finite biproduct, hence also a product, and a
product of monomorphisms is a monomorphism. In general a coproduct of monomorphisms need not be
one, an infinite coproduct in an abelian category need not be exact. -/
private lemma mono_mapMap_of_isZero_of_notMem {I J : Type*} {X Y : GradedObject I 𝒜} (φ : X ⟶ Y)
    (p : I → J) [X.HasMap p] [Y.HasMap p] (hφ : ∀ i, Mono (φ i)) (j : J) (S : Finset I)
    (hX : ∀ i, p i = j → i ∉ S → IsZero (X i)) : Mono (GradedObject.mapMap φ p j) := by
  classical
  have : HasFiniteBiproducts 𝒜 := Limits.HasFiniteBiproducts.of_hasFiniteProducts
  set uX : X.mapObj p j ⟶ (⨁ fun s : S => X s) :=
    X.descMapObj p (fun i _ => if h : i ∈ S then biproduct.ι (fun s : S => X s) ⟨i, h⟩ else 0)
      with huX
  set uY : Y.mapObj p j ⟶ (⨁ fun s : S => Y s) :=
    Y.descMapObj p (fun i _ => if h : i ∈ S then biproduct.ι (fun s : S => Y s) ⟨i, h⟩ else 0)
      with huY
  have hsplit : uX ≫ biproduct.desc (fun s : S => X.ιMapObjOrZero p s j) = 𝟙 _ := by
    apply GradedObject.mapObj_ext
    intro i hi
    by_cases h : i ∈ S
    · simp [huX, h, GradedObject.ιMapObjOrZero_eq _ _ _ _ hi]
    · have := hX i hi h
      simp [huX, this.eq_zero_of_src (X.ιMapObj p i j hi)]
  have : IsSplitMono uX := ⟨⟨_, hsplit⟩⟩
  have : Mono (biproduct.map (fun s : S => φ s.1)) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro Z g hg
    refine biproduct.hom_ext _ _ (fun s => ?_)
    have := hφ s.1
    rw [← cancel_mono (φ s.1)]
    simpa using congrArg (fun t => t ≫ biproduct.π _ s) hg
  have hsq : GradedObject.mapMap φ p j ≫ uY = uX ≫ biproduct.map (fun s : S => φ s.1) := by
    apply GradedObject.mapObj_ext
    intro i hi
    by_cases h : i ∈ S
    · simp [huX, huY, h]
    · simp [huX, huY, h]
  have : Mono (GradedObject.mapMap φ p j ≫ uY) := by rw [hsq]; infer_instance
  exact mono_of_mono _ uY

/-- A morphism of bicomplexes which is a monomorphism in each bidegree induces a monomorphism of
total complexes, as soon as the source is supported in `i ≥ a`, `n ≥ 0`: each antidiagonal
meets that support in a finite set, over which the coproduct defining the total complex is a
biproduct. -/
private lemma mono_totalMap_of_isZero
    {K L : HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (φ : K ⟶ L)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (hφ : ∀ i n : ℤ, Mono ((φ.f i).f n)) (a : ℤ)
    (h₁ : ∀ i n : ℤ, i < a → IsZero ((K.X i).X n))
    (h₂ : ∀ i n : ℤ, n < 0 → IsZero ((K.X i).X n)) :
    Mono (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) := by
  classical
  refine HomologicalComplex.mono_of_mono_f _ (fun m => ?_)
  have hf : (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f m =
      GradedObject.mapMap (HomologicalComplex₂.toGradedObjectMap φ) _ m := rfl
  rw [hf]
  refine mono_mapMap_of_isZero_of_notMem _ _ (fun x => hφ x.1 x.2) m
    (Finset.Icc a m ×ˢ Finset.Icc 0 (m - a)) (fun x hx hxS => ?_)
  obtain ⟨i, n⟩ := x
  have hm : i + n = m := by simpa using hx
  by_cases hi : i < a
  · exact h₁ i n hi
  · by_cases hn : n < 0
    · exact h₂ i n hn
    · exact absurd (by simp only [Finset.mem_product, Finset.mem_Icc]; omega) hxS

/-! ### The complex of resolutions of the terms -/

/-- The data the source's construction produces from a bounded below filtered complex `K^•` before
the total complex is formed: filtered injective resolutions `ε_i : K^i[0] ⟶ I_i^•` of the terms,
strict monomorphisms in degree `0`, together with morphisms `d_i : I_i^• ⟶ I_{i + 1}^•` squaring
to zero and commuting with the differential of `K^•`.

The maps `d_i` are `α_{i + 1} ≫ u_i^• ≫ β_i` in the source's notation; they square to zero
because `β_i ≫ α_i = 0`, not because `d_K^i ≫ d_K^{i + 1} = 0`, which is why the source factors
the differential of `K^•` through `Coim` and `Ker` rather than lifting it directly. -/
private structure ResolutionSystem (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ) where
  /-- The resolving complexes `I_i^•`. -/
  obj : ℤ → FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ
  /-- Each `I_i^•` vanishes in negative degrees. -/
  isStrictlyGE : ∀ i : ℤ, (obj i).X.IsStrictlyGE 0
  /-- `I_i^• = 0` for `i < a`, so that the total complex vanishes below `a`. -/
  isZero : ∀ i : ℤ, i < a → IsZero (obj i).X
  /-- Every term of every `I_i^•` has finite filtration. -/
  isFinite : ∀ i n : ℤ, ∃ p q : ℤ, IsIso (((obj i).filtration.ι.app (op p)).f n) ∧
    IsZero (((obj i).filtration.obj (op q)).X n)
  /-- Every term of every `I_i^•` is filtered injective. -/
  injective : ∀ i p n : ℤ,
    Injective (((FilteredObject.gr p).obj (obj i)).X n)
  /-- The resolutions `ε_i : K^i[0] ⟶ I_i^•` of the terms. -/
  ε : ∀ i : ℤ, (singleFil 0).obj (evalFil K i) ⟶ obj i
  /-- Each `ε_i` is a filtered quasi-isomorphism. -/
  filteredQuasiIso_ε : ∀ i : ℤ, CochainComplex.filteredQuasiIso 𝒜 (ε i)
  /-- Each `ε_i` is strict. -/
  isStrictHom_ε : ∀ i : ℤ, FilteredObject.IsStrictHom (ε i)
  /-- Each `K^i ⟶ I_i^0` is a monomorphism. -/
  mono_ε : ∀ i : ℤ, Mono ((ε i).hom.f 0)
  /-- The differentials `d_i : I_i^• ⟶ I_{i + 1}^•` of the complex of resolutions. -/
  d : ∀ i : ℤ, obj i ⟶ obj (i + 1)
  /-- The differentials square to zero. -/
  d_comp_d : ∀ i : ℤ, (d i).hom ≫ (d (i + 1)).hom = 0
  /-- The resolutions form a morphism of complexes of complexes. -/
  comm : ∀ i : ℤ, ε i ≫ d i = (singleFil 0).map (evalD K i) ≫ ε (i + 1)

/-- The differentials of a `ResolutionSystem` compose to zero on every filtration step: the
structure maps `F^p I_i^• ⟶ I_i^•` are monomorphisms and the squares commute, so this follows
from `d_i ≫ d_{i + 1} = 0` on the underlying complexes. -/
private lemma ResolutionSystem.natTrans_comp_natTrans
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (i : ℤ)
    (p : ℤᵒᵖ) : (S.d i).natTrans.app p ≫ (S.d (i + 1)).natTrans.app p = 0 := by
  rw [← cancel_mono ((S.obj (i + 1 + 1)).filtration.ι.app p)]
  simp [S.d_comp_d i]

/-- The double complex `I^{i, n} = I_i^n` of a `ResolutionSystem`, whose total complex is the
resolution of [Stacks, Tag 05TW]. -/
private noncomputable abbrev ResolutionSystem.doubleComplex
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CochainComplex.of (fun i => (S.obj i).X) (fun i => (S.d i).hom) S.d_comp_d

/-- The `p`-th filtration step of the double complex of a `ResolutionSystem`, the double complex
`F^p I^{i, n}`. -/
private noncomputable abbrev ResolutionSystem.doubleComplexStep
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CochainComplex.of (fun i => (S.obj i).filtration.obj p)
    (fun i => (S.d i).natTrans.app p) (fun i => S.natTrans_comp_natTrans i p)

/-! ### The support of the double complex, and its total complex -/

/-- The terms of a `ResolutionSystem` vanish in negative degrees, `I_i^n = 0` for `n < 0`. -/
private lemma ResolutionSystem.isZero_X_obj
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (i : ℤ)
    {n : ℤ} (hn : n < 0) : IsZero ((S.obj i).X.X n) := by
  have := S.isStrictlyGE i
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 n hn

/-- The terms of a `ResolutionSystem` vanish below its bound, `I_i^n = 0` for `i < a`. -/
private lemma ResolutionSystem.isZero_X_obj_of_lt
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) {i : ℤ}
    (hi : i < a) (n : ℤ) : IsZero ((S.obj i).X.X n) :=
  Functor.map_isZero (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) (S.isZero i hi)

/-- The filtration steps of a term of a `ResolutionSystem` vanish in negative degrees: their
structure maps into that term are degreewise monomorphisms. -/
private lemma ResolutionSystem.isZero_X_filtration_obj
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (i : ℤ)
    (p : ℤᵒᵖ) {n : ℤ} (hn : n < 0) : IsZero (((S.obj i).filtration.obj p).X n) :=
  isZero_filtration_obj_X_of_isZero (S.isZero_X_obj i hn) p

/-- The filtration steps of a term of a `ResolutionSystem` vanish below its bound. -/
private lemma ResolutionSystem.isZero_X_filtration_obj_of_lt
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) {i : ℤ}
    (hi : i < a) (p : ℤᵒᵖ) (n : ℤ) : IsZero (((S.obj i).filtration.obj p).X n) :=
  isZero_filtration_obj_X_of_isZero (S.isZero_X_obj_of_lt hi n) p

/-- The double complex `I^{i, n} = I_i^n` has a total complex: it is supported in `i ≥ a`,
`n ≥ 0`, so only finite coproducts are involved. -/
private lemma ResolutionSystem.hasTotal_doubleComplex
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    S.doubleComplex.HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded _ a (fun i _ hn => S.isZero_X_obj i hn)
    (fun i hi => S.isZero i hi)

/-- Every filtration step `F^p I^{i, n}` of the double complex of a `ResolutionSystem` has a total
complex, for the same reason as the double complex itself. -/
private lemma ResolutionSystem.hasTotal_doubleComplexStep
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    (S.doubleComplexStep p).HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded _ a
    (fun i _ hn => S.isZero_X_filtration_obj i p hn)
    (fun i hi => isZero_filtration_obj_of_isZero (S.isZero i hi) p)

/-! ### The total complex as a filtered complex -/

attribute [local instance] ResolutionSystem.hasTotal_doubleComplex
  ResolutionSystem.hasTotal_doubleComplexStep

/-- The structure map `F^p I^{•, •} ⟶ I^{•, •}` of double complexes, degreewise the structure map
`F^p I_i^• ⟶ I_i^•` of the filtration of `I_i^•`. -/
private noncomputable def ResolutionSystem.stepι
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    S.doubleComplexStep p ⟶ S.doubleComplex :=
  CochainComplex.ofHom (fun i => (S.obj i).filtration.ι.app p)
    (fun i => by
      simp [doubleComplex, doubleComplexStep])

/-- The transition map `F^q I^{•, •} ⟶ F^p I^{•, •}` of double complexes attached to `p ≤ q`,
degreewise the transition map of the filtration of `I_i^•`. -/
private noncomputable def ResolutionSystem.stepMap
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) {p q : ℤᵒᵖ}
    (h : p ⟶ q) : S.doubleComplexStep p ⟶ S.doubleComplexStep q :=
  CochainComplex.ofHom (fun i => (S.obj i).filtration.diagram.map h)
    (fun i => by
      simp [doubleComplexStep])

@[local simp]
private lemma ResolutionSystem.stepMap_comp_stepι
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) {p q : ℤᵒᵖ}
    (h : p ⟶ q) : S.stepMap h ≫ S.stepι q = S.stepι p := by
  apply HomologicalComplex.hom_ext
  intro i
  dsimp only [doubleComplexStep, doubleComplex, stepMap, stepι, CochainComplex.of,
    HomologicalComplex.comp_f]
  exact (S.obj i).filtration.diagram_map_comp_ι_app h

/-- The total complex of `F^p I^{•, •}` is a subcomplex of the total complex of `I^{•, •}`: the
antidiagonals of the support are finite, so `mono_totalMap_of_isZero` applies. -/
private lemma ResolutionSystem.mono_total_stepι
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    Mono (HomologicalComplex₂.total.map (S.stepι p) (ComplexShape.up ℤ)) :=
  mono_totalMap_of_isZero _
    (fun i n => inferInstanceAs (Mono (((S.obj i).filtration.ι.app p).f n))) a
    (fun _ n hi => S.isZero_X_filtration_obj_of_lt hi p n)
    (fun i _ hn => S.isZero_X_filtration_obj i p hn)

/-- The filtration of `Tot(I^{•, •})` by the total complexes `Tot(F^p I^{•, •})`. -/
@[implicit_reducible]
private noncomputable def ResolutionSystem.totalFiltration
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    Filtration (S.doubleComplex.total (ComplexShape.up ℤ)) ℤᵒᵖ where
  toMonoOver :=
    { obj := fun p =>
        { obj := Over.mk (HomologicalComplex₂.total.map (S.stepι p) (ComplexShape.up ℤ))
          property := S.mono_total_stepι p }
      map := fun {p q} h => MonoOver.homMk
        (HomologicalComplex₂.total.map (S.stepMap h) (ComplexShape.up ℤ))
        (by
          dsimp only [MonoOver.arrow, Over.mk_hom]
          rw [← HomologicalComplex₂.total.map_comp, S.stepMap_comp_stepι])
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }

/-- The filtered complex `Tot(I^{•, •})` of a `ResolutionSystem`, the resolution of
[Stacks, Tag 05TW]. -/
@[implicit_reducible]
private noncomputable def ResolutionSystem.totalObj
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := S.doubleComplex.total (ComplexShape.up ℤ)
  filtration := S.totalFiltration

/-! ### The comparison map into the total complex -/

/-- A morphism out of a complex concentrated in degree `0`, read in degree `0`: the map
`A ⟶ C^0` underlying `φ : A[0] ⟶ C^•`. -/
private noncomputable def singleDesc (A : 𝒜) {C : CochainComplex 𝒜 ℤ}
    (φ : (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A ⟶ C) : A ⟶ C.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ φ.f 0

/-- A morphism out of a complex concentrated in degree `0` lands in the cycles: `A ⟶ C^0 ⟶ C^1`
vanishes because `A[0]` has zero differentials. -/
private lemma singleDesc_comp_d (A : 𝒜) {C : CochainComplex 𝒜 ℤ}
    (φ : (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A ⟶ C) :
    singleDesc A φ ≫ C.d 0 1 = 0 := by
  simp [singleDesc]

/-- Reading a commutative square of complexes concentrated in degree `0` in degree `0`. -/
private lemma singleDesc_comp {A B : 𝒜} {C C' : CochainComplex 𝒜 ℤ}
    (φ : (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A ⟶ C)
    (φ' : (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B ⟶ C') (g : A ⟶ B)
    (δ : C ⟶ C')
    (h : φ ≫ δ = (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).map g ≫ φ') :
    singleDesc A φ ≫ δ.f 0 = g ≫ singleDesc B φ' := by
  have h0 := HomologicalComplex.congr_hom h 0
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self] at h0
  simp [singleDesc, h0]

/-- The map `K^n ⟶ I_n^0` underlying the resolution `ε_n : K^n[0] ⟶ I_n^•`. -/
private noncomputable def ResolutionSystem.εZero
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (n : ℤ) :
    K.X.X n ⟶ (S.obj n).X.X 0 :=
  singleDesc (K.X.X n) (S.ε n).hom

/-- The map `F^p K^n ⟶ F^p I_n^0` underlying `ε_n`. -/
private noncomputable def ResolutionSystem.εZeroStep
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ)
    (n : ℤ) : (K.filtration.obj p).X n ⟶ ((S.obj n).filtration.obj p).X 0 :=
  singleDesc ((K.filtration.obj p).X n) ((S.ε n).natTrans.app p)

/-- The resolutions of the terms commute with the differential of `K^•` in degree `0`, which is
the `comm` field of a `ResolutionSystem` read in degree `0`. -/
private lemma ResolutionSystem.εZero_comp
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (n : ℤ) :
    S.εZero n ≫ (S.d n).hom.f 0 = K.X.d n (n + 1) ≫ S.εZero (n + 1) := by
  refine singleDesc_comp _ _ _ _ ?_
  have h := congrArg FilteredObject.Hom.hom (S.comm n)
  simp only [FilteredObject.comp_hom, singleFil_map_hom, evalD_hom] at h
  exact h

/-- The `comm` field of a `ResolutionSystem` on the `p`-th filtration step. -/
private lemma ResolutionSystem.ε_natTrans_comm
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (n : ℤ)
    (p : ℤᵒᵖ) : (S.ε n).natTrans.app p ≫ (S.d n).natTrans.app p =
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).map ((K.filtration.obj p).d n (n + 1)) ≫
        (S.ε (n + 1)).natTrans.app p := by
  have h := congrArg (fun f => FilteredObject.Hom.natTrans f |>.app p) (S.comm n)
  simp only [FilteredObject.comp_natTrans, NatTrans.comp_app, singleFil_map_natTrans_app,
    evalD_natTrans_app] at h
  exact h

/-- The same on the filtration steps. -/
private lemma ResolutionSystem.εZeroStep_comp
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ)
    (n : ℤ) : S.εZeroStep p n ≫ ((S.d n).natTrans.app p).f 0 =
      (K.filtration.obj p).d n (n + 1) ≫ S.εZeroStep p (n + 1) :=
  singleDesc_comp _ _ _ _ (S.ε_natTrans_comm n p)

/-- The resolutions of the terms are compatible with the filtration, in degree `0`. -/
private lemma ResolutionSystem.εZeroStep_comp_ι
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ)
    (n : ℤ) : S.εZeroStep p n ≫ ((S.obj n).filtration.ι.app p).f 0 =
      (K.filtration.ι.app p).f n ≫ S.εZero n := by
  refine singleDesc_comp _ _ _ _ ?_
  have h := (S.ε n).comm p
  simp only [singleFil_filtration_ι_app, evalFil_ι_app] at h
  exact h

/-- The map `X^• ⟶ Tot(L^{•, •})` into the corner summands attached to a family of maps
`ε n : X^n ⟶ L^{n, 0}` landing in the cycles of the columns and commuting with the differentials:
in degree `n` it is `ε n` followed by the inclusion of the summand `L^{n, 0}`, which commutes with
the differentials because the `d₁`-component is the commutation hypothesis and the `d₂`-component
vanishes on the cycles. -/
private noncomputable def totalHomOfCorner {X : CochainComplex 𝒜 ℤ}
    (L : HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [L.HasTotal (ComplexShape.up ℤ)] (ε : ∀ n : ℤ, X.X n ⟶ (L.X n).X 0)
    (hε : ∀ n : ℤ, ε n ≫ (L.X n).d 0 1 = 0)
    (hεd : ∀ n : ℤ, ε n ≫ (L.d n (n + 1)).f 0 = X.d n (n + 1) ≫ ε (n + 1)) :
    X ⟶ L.total (ComplexShape.up ℤ) :=
  CochainComplex.ofHom (fun n => ε n ≫ L.ιTotal (ComplexShape.up ℤ) n 0 n (by simp))
    (fun n => by
      have hd₁ := HomologicalComplex₂.d₁_eq L (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) 0 (n + 1) (by simp)
      have hd₂ := HomologicalComplex₂.d₂_eq L (ComplexShape.up ℤ) n
        (show (ComplexShape.up ℤ).Rel 0 1 by simp) (n + 1) (by simp)
      have hz : ε n ≫ (L.X n).d 0 1 ≫
          L.ιTotal (ComplexShape.up ℤ) n 1 (n + 1) (by simp) = 0 := by
        rw [← Category.assoc, hε n, zero_comp]
      have hc : ε n ≫ (L.d n (n + 1)).f 0 ≫
          L.ιTotal (ComplexShape.up ℤ) (n + 1) 0 (n + 1) (by simp) =
          X.d n (n + 1) ≫ ε (n + 1) ≫
            L.ιTotal (ComplexShape.up ℤ) (n + 1) 0 (n + 1) (by simp) := by
        rw [← Category.assoc, ← Category.assoc, hεd n]
      rw [HomologicalComplex₂.total_d, Category.assoc]
      simp [hd₁, hd₂, hz, hc])

/-- The comparison map `K^• ⟶ Tot(I^{•, •})` of [Stacks, Tag 05TW], in degree `n` the map
`K^n ⟶ I^{n, 0} = I_n^0` into the corner summand. -/
private noncomputable def ResolutionSystem.totalHom
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    K.X ⟶ S.totalObj.X :=
  totalHomOfCorner S.doubleComplex S.εZero (fun _ => singleDesc_comp_d _ _)
    (fun n => by simpa using S.εZero_comp n)

/-- The comparison map `F^p K^• ⟶ Tot(F^p I^{•, •})`, the filtration step of `totalHom`. -/
private noncomputable def ResolutionSystem.totalHomStep
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    K.filtration.obj p ⟶ S.totalObj.filtration.obj p :=
  totalHomOfCorner (S.doubleComplexStep p) (S.εZeroStep p) (fun _ => singleDesc_comp_d _ _)
    (fun n => by simpa using S.εZeroStep_comp p n)

private lemma ResolutionSystem.totalHom_f
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (n : ℤ) :
    S.totalHom.f n = S.εZero n ≫ S.doubleComplex.ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  rfl

private lemma ResolutionSystem.totalHomStep_f
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ)
    (n : ℤ) : (S.totalHomStep p).f n =
      S.εZeroStep p n ≫ (S.doubleComplexStep p).ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  rfl

/-! ### The comparison map as a morphism of filtered complexes -/

/-- The inclusion of a summand in a total complex is a split monomorphism: the map out of the
total complex which is the identity on that summand and zero on every other one retracts it. -/
private lemma isSplitMono_ιTotal
    {L : HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [L.HasTotal (ComplexShape.up ℤ)] (i n m : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, n) = m) :
    IsSplitMono (L.ιTotal (ComplexShape.up ℤ) i n m h) := by
  classical
  refine ⟨⟨L.totalDesc (fun j₁ j₂ _ =>
    if hj : j₁ = i ∧ j₂ = n then (L.XXIsoOfEq _ _ _ hj.1 hj.2).hom else 0), ?_⟩⟩
  rw [HomologicalComplex₂.ι_totalDesc]
  simp

@[local simp]
private lemma ResolutionSystem.totalObj_filtration_ι_app
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    S.totalObj.filtration.ι.app p =
      HomologicalComplex₂.total.map (S.stepι p) (ComplexShape.up ℤ) :=
  rfl

/-- The comparison maps are compatible with the filtration: `F^p K^• ⟶ Tot(F^p I^{•, •})` followed
by the inclusion of `Tot(F^p I^{•, •})` in `Tot(I^{•, •})` is `F^p K^• ⟶ K^• ⟶ Tot(I^{•, •})`. This
is `εZeroStep_comp_ι` on the corner summands, read through `ιTotal_map`. -/
private lemma ResolutionSystem.totalHomStep_comp_ι
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    S.totalHomStep p ≫ S.totalObj.filtration.ι.app p =
      K.filtration.ι.app p ≫ S.totalHom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  have h3 : ((S.stepι p).f n).f 0 = ((S.obj n).filtration.ι.app p).f 0 := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, totalHomStep_f, totalHom_f,
    totalObj_filtration_ι_app, Category.assoc, HomologicalComplex₂.ιTotal_map, h3, ← Category.assoc,
    S.εZeroStep_comp_ι p n, Category.assoc]

/-- The comparison map `K^• ⟶ Tot(I^{•, •})` of [Stacks, Tag 05TW] as a morphism of filtered
complexes: `totalHom` on the underlying complexes and `totalHomStep` on the filtration steps. -/
private noncomputable def ResolutionSystem.totalα
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    K ⟶ S.totalObj := by
  with_implicit exact (FilteredObject.homMk S.totalHom (fun p => S.totalHomStep p)
    (fun p => S.totalHomStep_comp_ι p))

@[local simp]
private lemma ResolutionSystem.totalα_hom_f
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (n : ℤ) :
    S.totalα.hom.f n =
      S.εZero n ≫ S.doubleComplex.ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  rfl

/-- The map `K^n ⟶ I_n^0` is a monomorphism: it is `ε_n` in degree `0` after the canonical
isomorphism `(K^n[0])^0 ≅ K^n`. -/
private lemma ResolutionSystem.mono_εZero
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (n : ℤ) :
    Mono (S.εZero n) := by
  have hm : Mono ((S.ε n).hom.f 0) := S.mono_ε n
  have h : S.εZero n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X.X n)).inv ≫
        (S.ε n).hom.f 0 := rfl
  rw [h]
  exact @mono_comp _ _ _ _ _ _ inferInstance _ hm

/-- The comparison map `K^• ⟶ Tot(I^{•, •})` is a monomorphism: in degree `n` it is the
monomorphism `K^n ⟶ I_n^0` followed by the inclusion of the corner summand, which splits. -/
private lemma ResolutionSystem.mono_totalα_hom
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    Mono S.totalα.hom := by
  refine HomologicalComplex.mono_of_mono_f _ (fun n => ?_)
  have hm := S.mono_εZero n
  have hs : IsSplitMono (S.doubleComplex.ιTotal (ComplexShape.up ℤ) n 0 n (by simp)) :=
    isSplitMono_ιTotal n 0 n _
  rw [S.totalα_hom_f n]
  exact @mono_comp _ _ _ _ _ _ hm _ (@IsSplitMono.mono _ _ _ _ _ hs)

/-- `Tot(I^{•, •})` vanishes below `a`, the bound of the given `ResolutionSystem`. -/
private lemma ResolutionSystem.isStrictlyGE_totalObj
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    S.totalObj.X.IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro m hm
  exact StacksDraft.TotalComplexQuasiIso.isZero_total_X _ a (fun i _ hn => S.isZero_X_obj i hn)
    (fun i hi => S.isZero i hi) m hm

/-! ### Finiteness of the filtration of the total complex -/

/-- A transition map of a filtration followed by the structure map of the larger step, read in a
degree, is the structure map of the smaller step. -/
private lemma filtration_diagram_map_f_comp_ι_app_f {X : CochainComplex 𝒜 ℤ}
    (F : Filtration X ℤᵒᵖ) {i j : ℤᵒᵖ} (h : i ⟶ j) (n : ℤ) :
    (F.diagram.map h).f n ≫ (F.ι.app j).f n = (F.ι.app i).f n := by
  rw [← HomologicalComplex.comp_f, F.diagram_map_comp_ι_app]

/-- A filtration of a complex which exhausts a degree at some index exhausts it at every smaller
index: the transition map `F^p ⟶ F^{p'}` followed by `F^{p'} ⟶ X` is `F^p ⟶ X`, so `F^{p'} ⟶ X`
is a split epimorphism there, and it is always a monomorphism. -/
private lemma isIso_filtration_ι_f_of_le {X : CochainComplex 𝒜 ℤ} (F : Filtration X ℤᵒᵖ)
    {p p' : ℤ} (h : p' ≤ p) (n : ℤ) (hp : IsIso ((F.ι.app (op p)).f n)) :
    IsIso ((F.ι.app (op p')).f n) := by
  have := hp
  have : IsSplitEpi ((F.ι.app (op p')).f n) :=
    ⟨⟨inv ((F.ι.app (op p)).f n) ≫ (F.diagram.map (homOfLE h).op).f n, by
      rw [Category.assoc, filtration_diagram_map_f_comp_ι_app_f, IsIso.inv_hom_id]⟩⟩
  exact isIso_of_mono_of_epi _

/-- A filtration of a complex which vanishes in a degree at some index vanishes there at every
larger index: the transition map `F^{q'} ⟶ F^q` is a monomorphism, both being subobjects of the
ambient complex. -/
private lemma isZero_filtration_obj_X_of_le {X : CochainComplex 𝒜 ℤ} (F : Filtration X ℤᵒᵖ)
    {q q' : ℤ} (h : q ≤ q') (n : ℤ) (hq : IsZero ((F.obj (op q)).X n)) :
    IsZero ((F.obj (op q')).X n) := by
  have : Mono ((F.diagram.map (homOfLE h).op).f n) := by
    have hm : Mono ((F.diagram.map (homOfLE h).op).f n ≫ (F.ι.app (op q)).f n) := by
      rw [filtration_diagram_map_f_comp_ι_app_f]; infer_instance
    exact mono_of_mono _ ((F.ι.app (op q)).f n)
  exact IsZero.of_mono ((F.diagram.map (homOfLE h).op).f n) hq

omit [Abelian 𝒜] in
/-- A morphism of graded objects whose components over a degree `j` are all isomorphisms induces an
isomorphism of the coproducts over `j`: the inverses assemble into an inverse. -/
private lemma isIso_mapMap_of_isIso {I J : Type*} {X Y : GradedObject I 𝒜} (φ : X ⟶ Y)
    (p : I → J) [X.HasMap p] [Y.HasMap p] (j : J) (hφ : ∀ i, p i = j → IsIso (φ i)) :
    IsIso (GradedObject.mapMap φ p j) := by
  refine ⟨⟨Y.descMapObj p (fun i hi => @inv _ _ _ _ (φ i) (hφ i hi) ≫ X.ιMapObj p i j hi),
    ?_, ?_⟩⟩ <;>
  · ext i hi
    have := hφ i hi
    simp

/-- A graded object whose components over a degree `j` all vanish has zero coproduct over `j`. -/
private lemma isZero_mapObj_of_isZero {I J : Type*} {X : GradedObject I 𝒜} (p : I → J)
    [X.HasMap p] (j : J) (hX : ∀ i, p i = j → IsZero (X i)) : IsZero (X.mapObj p j) := by
  rw [IsZero.iff_id_eq_zero]
  ext i hi
  exact (hX i hi).eq_of_src _ _

/-- A summand of a biproduct of monomorphisms is the intersection of the ambient biproduct with the
corresponding summand of the target: a map into `⨁ X` whose image in `⨁ Y` lands in `Y s₀` has all
its other components killed by the monomorphisms `φ s`, so it factors through `X s₀`. -/
private lemma isPullback_biproduct_ι {S : Type*} [Finite S]
    [HasFiniteBiproducts 𝒜] (X Y : S → 𝒜) (φ : ∀ s, X s ⟶ Y s) (hφ : ∀ s, Mono (φ s)) (s₀ : S) :
    IsPullback (biproduct.ι X s₀) (φ s₀) (biproduct.map φ) (biproduct.ι Y s₀) := by
  classical
  have hι : IsSplitMono (biproduct.ι Y s₀) := ⟨⟨biproduct.π Y s₀, by simp⟩⟩
  refine IsPullback.mk' (by simp) (fun {T u v} h₁ _ => ?_) (fun {T} x y hxy => ?_)
  · have : Mono (biproduct.ι X s₀) := (⟨⟨biproduct.π X s₀, by simp⟩⟩ : IsSplitMono _).mono
    exact (cancel_mono (biproduct.ι X s₀)).1 h₁
  · have hzero : ∀ s, s ≠ s₀ → x ≫ biproduct.π X s = 0 := fun s hs => by
      have := hφ s
      rw [← cancel_mono (φ s), zero_comp, Category.assoc, ← biproduct.map_π φ s, ← Category.assoc,
        hxy, Category.assoc, biproduct.ι_π_ne _ (Ne.symm hs), comp_zero]
    have hfst : (x ≫ biproduct.π X s₀) ≫ biproduct.ι X s₀ = x := by
      refine biproduct.hom_ext _ _ (fun s => ?_)
      by_cases hs : s = s₀
      · subst hs; simp
      · rw [Category.assoc, biproduct.ι_π_ne _ (Ne.symm hs), comp_zero, hzero s hs]
    refine ⟨x ≫ biproduct.π X s₀, hfst, ?_⟩
    rw [← cancel_mono (biproduct.ι Y s₀), Category.assoc, ← biproduct.ι_map φ s₀,
      ← Category.assoc, hfst, hxy]

/-- A graded object which vanishes outside a finite subset `S` of the fibre of `p` over `j` has
that fibre's coproduct a biproduct over `S`: the two obvious maps are mutually inverse. -/
private noncomputable def mapObjIsoBiproduct {I J : Type*} [HasFiniteBiproducts 𝒜]
    (X : GradedObject I 𝒜) (p : I → J) [X.HasMap p] (j : J) (S : Finset I)
    (hS : ∀ i ∈ S, p i = j) (hX : ∀ i, p i = j → i ∉ S → IsZero (X i)) :
    X.mapObj p j ≅ ⨁ (fun s : S => X s) where
  hom := by
    classical
    exact X.descMapObj p
      (fun i _ => if h : i ∈ S then biproduct.ι (fun s : S => X s) ⟨i, h⟩ else 0)
  inv := biproduct.desc (fun s => X.ιMapObj p s j (hS s s.2))
  hom_inv_id := by
    classical
    apply GradedObject.mapObj_ext
    intro i hi
    by_cases h : i ∈ S
    · simp [h]
    · have := hX i hi h
      simp [this.eq_zero_of_src (X.ιMapObj p i j hi)]
  inv_hom_id := by
    classical
    refine biproduct.hom_ext' _ _ (fun s => ?_)
    simp [s.2]

/-- A morphism of graded objects which is a monomorphism in each degree meets each summand of the
coproduct over a degree `j` in the corresponding summand of its source, provided source and target
vanish outside a finite subset `S` of the fibre: the coproducts are then biproducts over `S`, where
the intersection is computed summandwise. -/
private lemma isPullback_ιMapObj {I J : Type*} {X Y : GradedObject I 𝒜} (φ : X ⟶ Y) (p : I → J)
    [X.HasMap p] [Y.HasMap p] (hφ : ∀ i, Mono (φ i)) (j : J) (S : Finset I)
    (hS : ∀ i ∈ S, p i = j) (hX : ∀ i, p i = j → i ∉ S → IsZero (X i))
    (hY : ∀ i, p i = j → i ∉ S → IsZero (Y i)) {i₀ : I} (hi₀ : i₀ ∈ S) :
    IsPullback (X.ιMapObj p i₀ j (hS i₀ hi₀)) (φ i₀) (GradedObject.mapMap φ p j)
      (Y.ιMapObj p i₀ j (hS i₀ hi₀)) := by
  classical
  have : HasFiniteBiproducts 𝒜 := Limits.HasFiniteBiproducts.of_hasFiniteProducts
  refine (isPullback_biproduct_ι (fun s : S => X s) (fun s : S => Y s) (fun s => φ s)
    (fun s => hφ s) ⟨i₀, hi₀⟩).of_iso' (Iso.refl _) (mapObjIsoBiproduct X p j S hS hX)
    (Iso.refl _) (mapObjIsoBiproduct Y p j S hS hY) (by simp [mapObjIsoBiproduct, hi₀])
    (by simp) ?_ (by simp [mapObjIsoBiproduct, hi₀])
  apply GradedObject.mapObj_ext
  intro i hi
  by_cases h : i ∈ S
  · simp [mapObjIsoBiproduct, h]
  · simp [mapObjIsoBiproduct, (hX i hi h).eq_zero_of_src (X.ιMapObj p i j hi)]

/-- A morphism of bicomplexes which is a monomorphism in each bidegree meets each summand of the
total complex of its target in the corresponding summand of its source, as soon as both bicomplexes
are supported in `i ≥ a`, `n ≥ 0`: each antidiagonal meets that support in a finite set, over which
the coproducts defining the total complexes are biproducts. -/
private lemma isPullback_ιTotal_of_isZero
    {Z Z' : HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (φ : Z ⟶ Z')
    [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)]
    (hφ : ∀ i n : ℤ, Mono ((φ.f i).f n)) (a : ℤ)
    (h₁ : ∀ i n : ℤ, i < a → IsZero ((Z.X i).X n))
    (h₂ : ∀ i n : ℤ, n < 0 → IsZero ((Z.X i).X n))
    (h₁' : ∀ i n : ℤ, i < a → IsZero ((Z'.X i).X n))
    (h₂' : ∀ i n : ℤ, n < 0 → IsZero ((Z'.X i).X n)) (i₀ n₀ m : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i₀, n₀) = m) :
    IsPullback (Z.ιTotal (ComplexShape.up ℤ) i₀ n₀ m h) ((φ.f i₀).f n₀)
      ((HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f m)
      (Z'.ιTotal (ComplexShape.up ℤ) i₀ n₀ m h) := by
  classical
  set S : Finset (ℤ × ℤ) :=
    insert (i₀, n₀) ((Finset.Icc a m ×ˢ Finset.Icc 0 (m - a)).filter fun x => x.1 + x.2 = m)
  have hS : ∀ x ∈ S, ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) x = m := by
    intro x hx
    rcases Finset.mem_insert.1 hx with hx | hx
    · rw [hx]; exact h
    · simpa using (Finset.mem_filter.1 hx).2
  have hzero : ∀ (W : HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
      (∀ i n : ℤ, i < a → IsZero ((W.X i).X n)) → (∀ i n : ℤ, n < 0 → IsZero ((W.X i).X n)) →
      ∀ x : ℤ × ℤ, ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) x = m
        → x ∉ S → IsZero ((W.X x.1).X x.2) := by
    intro W hW₁ hW₂ x hx hxS
    have hm : x.1 + x.2 = m := by simpa using hx
    by_cases hi : x.1 < a
    · exact hW₁ _ _ hi
    · by_cases hn : x.2 < 0
      · exact hW₂ _ _ hn
      · refine absurd (show x ∈ S from Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨?_, hm⟩)) hxS
        simp only [Finset.mem_product, Finset.mem_Icc]
        omega
  exact isPullback_ιMapObj (HomologicalComplex₂.toGradedObjectMap φ) _ (fun x => hφ x.1 x.2) m S hS
    (hzero Z h₁ h₂) (hzero Z' h₁' h₂') (Finset.mem_insert_self _ _)

/-- A commutative square of cochain complexes which is a pullback square in each degree is a
pullback square, provided the map opposite to the one whose universal property is used is a
degreewise monomorphism: the degreewise lifts then commute with the differentials because that
monomorphism cancels the two composites. -/
private lemma isPullback_of_degreewise {P A B C : CochainComplex 𝒜 ℤ} {t : P ⟶ A} {l : P ⟶ B}
    {r : A ⟶ C} {b : B ⟶ C} (w : t ≫ r = l ≫ b) (hl : ∀ n : ℤ, Mono (l.f n))
    (h : ∀ n : ℤ, IsPullback (t.f n) (l.f n) (r.f n) (b.f n)) : IsPullback t l r b := by
  have hmono : Mono l := HomologicalComplex.mono_of_mono_f l hl
  refine IsPullback.mk' w (fun {_} {_ _} _ h₂ => (cancel_mono l).1 h₂) (fun {_} x y hxy => ?_)
  have hxy' : ∀ n : ℤ, x.f n ≫ r.f n = y.f n ≫ b.f n := fun n => by
    simpa using HomologicalComplex.congr_hom hxy n
  refine ⟨⟨fun n => (h n).lift (x.f n) (y.f n) (hxy' n), fun n m _ => ?_⟩,
    HomologicalComplex.hom_ext _ _ (fun n => (h n).lift_fst _ _ _),
    HomologicalComplex.hom_ext _ _ (fun n => (h n).lift_snd _ _ _)⟩
  have := hl m
  rw [← cancel_mono (l.f m), Category.assoc, Category.assoc, (h m).lift_snd,
    ← HomologicalComplex.Hom.comm l n m, ← Category.assoc, (h n).lift_snd,
    HomologicalComplex.Hom.comm y n m]

/-- Every term of `Tot(I^{•, •})` has finite filtration. The antidiagonal `i + n = m` meets the
support `i ≥ a`, `n ≥ 0` of the double complex in the finite set `a ≤ i ≤ m`, so one index below
all the finitely many indices exhausting the `I_i^n` there exhausts `Tot^m`, and one index above
all the finitely many indices killing them kills it; outside the support both `F^p I_i^n` and
`I_i^n` vanish, so the comparison map is an isomorphism there for every index. -/
private lemma ResolutionSystem.isDegreewiseFinite_totalObj
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (m : ℤ) :
    ∃ p q : ℤ, IsIso ((S.totalObj.filtration.ι.app (op p)).f m) ∧
      IsZero ((S.totalObj.filtration.obj (op q)).X m) := by
  classical
  have hfin : ∀ i : ℤ, IsIso (((S.obj i).filtration.ι.app
        (op (S.isFinite i (m - i)).choose)).f (m - i)) ∧
      IsZero (((S.obj i).filtration.obj
        (op (S.isFinite i (m - i)).choose_spec.choose)).X (m - i)) :=
    fun i => (S.isFinite i (m - i)).choose_spec.choose_spec
  obtain ⟨M, hM⟩ :=
    ((Finset.Icc a m).image fun i => -(S.isFinite i (m - i)).choose).exists_le
  obtain ⟨N, hN⟩ :=
    ((Finset.Icc a m).image fun i => (S.isFinite i (m - i)).choose_spec.choose).exists_le
  refine ⟨-M, N, ?_, ?_⟩
  · have hf : (S.totalObj.filtration.ι.app (op (-M))).f m =
        GradedObject.mapMap
          (HomologicalComplex₂.toGradedObjectMap (S.stepι (op (-M)))) _ m := rfl
    rw [hf]
    refine isIso_mapMap_of_isIso _ _ m (fun x hx => ?_)
    obtain ⟨i, n⟩ := x
    have he : HomologicalComplex₂.toGradedObjectMap (S.stepι (op (-M))) (i, n) =
        ((S.obj i).filtration.ι.app (op (-M))).f n := rfl
    have hmn : i + n = m := by simpa using hx
    rw [he]
    by_cases hi : i < a
    · exact IsZero.isIso (S.isZero_X_filtration_obj_of_lt hi (op (-M)) n)
        (S.isZero_X_obj_of_lt hi n) _
    · by_cases hn : n < 0
      · exact IsZero.isIso (S.isZero_X_filtration_obj i (op (-M)) hn)
          (S.isZero_X_obj i hn) _
      · have hmem : i ∈ Finset.Icc a m := by simp only [Finset.mem_Icc]; omega
        have h0 : -(S.isFinite i (m - i)).choose ≤ M := hM _ (Finset.mem_image_of_mem _ hmem)
        have hn' : n = m - i := by omega
        subst hn'
        exact isIso_filtration_ι_f_of_le _ (by omega) _ (hfin i).1
  · have hz : (S.totalObj.filtration.obj (op N)).X m =
        (S.doubleComplexStep (op N)).toGradedObject.mapObj
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) m := rfl
    rw [hz]
    refine isZero_mapObj_of_isZero _ m (fun x hx => ?_)
    obtain ⟨i, n⟩ := x
    have he : (S.doubleComplexStep (op N)).toGradedObject (i, n) =
        ((S.obj i).filtration.obj (op N)).X n := rfl
    have hmn : i + n = m := by simpa using hx
    rw [he]
    by_cases hi : i < a
    · exact S.isZero_X_filtration_obj_of_lt hi (op N) n
    · by_cases hn : n < 0
      · exact S.isZero_X_filtration_obj i (op N) hn
      · have hmem : i ∈ Finset.Icc a m := by simp only [Finset.mem_Icc]; omega
        have h0 : (S.isFinite i (m - i)).choose_spec.choose ≤ N :=
          hN _ (Finset.mem_image_of_mem _ hmem)
        have hn' : n = m - i := by omega
        subst hn'
        exact isZero_filtration_obj_X_of_le _ h0 _ (hfin i).2

/-! ### Injectivity of the graded pieces of the total complex -/

/-- The cokernel of a monomorphism between injective objects is injective: the sequence
`0 ⟶ X ⟶ Y ⟶ Coker ⟶ 0` is short exact with injective first term, hence split, so the cokernel is
a retract of `Y`. -/
private lemma injective_cokernel_of_mono {X Y : 𝒜} (f : X ⟶ Y) [Mono f] [Injective X]
    [Injective Y] : Injective (cokernel f) := by
  have hse : (ShortComplex.mk f (cokernel.π f) (by simp)).ShortExact :=
    { exact := ShortComplex.exact_cokernel f
      mono_f := inferInstance
      epi_g := inferInstance }
  exact Retract.injective ⟨hse.splittingOfInjective.s, cokernel.π f, hse.splittingOfInjective.s_g⟩

/-- The transition map `F^{p + 1} X^• ⟶ F^p X^•` of a filtration of a complex, the morphism whose
cokernel is `gr^p X^•`. -/
private noncomputable abbrev filtrationStep (J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤ) :
    J.filtration.obj (op (p + 1)) ⟶ J.filtration.obj (op p) :=
  J.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op

/-- The transition maps of a filtration are monomorphisms in each degree, being factors of the
monomorphisms `F^p X^• ⟶ X^•` there. -/
private lemma mono_filtrationStep_f (J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ) :
    Mono ((filtrationStep J p).f n) :=
  inferInstance

/-- `gr^p X^•` is in each degree the cokernel of the transition map read in that degree: cokernels
of complexes are computed degreewise. -/
private noncomputable def gradedPieceXIso (J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ) :
    ((FilteredObject.gr p).obj J).X n ≅
      cokernel ((filtrationStep J p).f n) :=
  Limits.PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
    (filtrationStep J p)

/-- **Every step of a filtration by filtered injective objects consists of injective objects.**
In a degree where the filtration is finite, run down from an index where the step vanishes: each
step is an extension of the injective graded piece `gr^p` by the step above it, and an extension of
an injective object splits, so injectivity propagates. This is what makes the terms of
`Tot(F^p I^{•, •})` injective, and hence the graded pieces of `Tot(I^{•, •})` injective. -/
private lemma injective_filtration_obj_X (J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ)
    (hinj : ∀ p : ℤ, Injective (((FilteredObject.gr p).obj J).X n))
    {q : ℤ} (hq : IsZero ((J.filtration.obj (op q)).X n)) (p : ℤ) :
    Injective ((J.filtration.obj (op p)).X n) := by
  suffices h : ∀ k : ℕ, ∀ r : ℤ, q ≤ r + k → Injective ((J.filtration.obj (op r)).X n) by
    exact h (q - p).toNat p (by omega)
  intro k
  induction k with
  | zero =>
      intro r hr
      exact (isZero_filtration_obj_X_of_le J.filtration (by omega) n hq).injective
  | succ k ih =>
      intro r hr
      by_cases hqr : q ≤ r
      · exact (isZero_filtration_obj_X_of_le J.filtration hqr n hq).injective
      · have h1 : Injective ((J.filtration.obj (op (r + 1))).X n) := ih (r + 1) (by omega)
        have h2 : Injective (cokernel ((filtrationStep J r).f n)) :=
          Injective.of_iso (gradedPieceXIso J r n) (hinj r)
        have hm : Mono ((filtrationStep J r).f n) := mono_filtrationStep_f J r n
        have hse : (ShortComplex.mk ((filtrationStep J r).f n)
            (cokernel.π ((filtrationStep J r).f n)) (cokernel.condition _)).ShortExact :=
          { exact := ShortComplex.exact_cokernel _
            mono_f := hm
            epi_g := inferInstance }
        exact Injective.of_iso hse.splittingOfInjective.isoBinaryBiproduct.symm inferInstance

/-- Every term of `Tot(F^p I^{•, •})` is an injective object: the double complex `F^p I^{•, •}` is
supported in `i ≥ a`, `n ≥ 0`, so each term of its total complex is a finite biproduct of the
`F^p I_i^n`, and those are injective by `injective_filtration_obj_X`. -/
private lemma ResolutionSystem.injective_total_doubleComplexStep
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p m : ℤ) :
    Injective (((S.doubleComplexStep (op p)).total (ComplexShape.up ℤ)).X m) := by
  refine StacksDraft.TotalComplexQuasiIso.injective_total_X_of_bounded _ a
    (fun i n hn => S.isZero_X_filtration_obj i (op p) hn)
    (fun i hi => isZero_filtration_obj_of_isZero (S.isZero i hi) (op p))
    (fun i n => ?_) m
  obtain ⟨-, q, -, hq⟩ := S.isFinite i n
  exact injective_filtration_obj_X (S.obj i) n (fun r => S.injective i r n) hq p

/-- **Every graded piece of `Tot(I^{•, •})` consists of injective objects.** In degree `n` the
piece is the cokernel of `Tot(F^{p + 1} I^{•, •})^n ⟶ Tot(F^p I^{•, •})^n`, a monomorphism between
injective objects, hence injective. -/
private lemma ResolutionSystem.injective_gradedPiece_totalObj
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p n : ℤ) :
    Injective (((FilteredObject.gr p).obj S.totalObj).X n) := by
  have h1 : Injective ((S.totalObj.filtration.obj (op (p + 1))).X n) :=
    S.injective_total_doubleComplexStep (p + 1) n
  have h2 : Injective ((S.totalObj.filtration.obj (op p)).X n) :=
    S.injective_total_doubleComplexStep p n
  have hm : Mono ((filtrationStep S.totalObj p).f n) := mono_filtrationStep_f _ _ _
  exact Injective.of_iso (gradedPieceXIso S.totalObj p n).symm (injective_cokernel_of_mono _)

/-! ### The comparison map is a strict filtered quasi-isomorphism -/

section Comparison

open StacksDraft.TotalComplexQuasiIso

/-- Strictness of `ε_n` read in degree `0`: `F^p K^n` is the intersection of `K^n` with
`F^p I_n^0`. Evaluation in degree `0` preserves the pullback square of `isStrictHom_ε`, and the
isomorphisms `(A[0])^0 ≅ A` identify the evaluated square with this one. -/
private lemma ResolutionSystem.isPullback_εZeroStep
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ)
    (n : ℤ) : IsPullback (S.εZeroStep p n) ((K.filtration.ι.app p).f n)
      (((S.obj n).filtration.ι.app p).f 0) (S.εZero n) := by
  have := S.isStrictHom_ε n
  have hiso : IsPullback
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((K.filtration.obj p).X n)).inv
      ((K.filtration.ι.app p).f n)
      (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).map
        ((K.filtration.ι.app p).f n)).f 0)
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X.X n)).inv :=
    IsPullback.of_horiz_isIso
      ⟨by rw [HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]; rfl⟩
  exact hiso.paste_horiz ((IsStrictHom.isPullback (S.ε n) p).map
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) 0))

/-- `K^i = 0` for `i < a`: the term is a subobject of `I_i^0`, which vanishes with `I_i^•`. -/
private lemma ResolutionSystem.isZero_X_of_lt
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) {i : ℤ}
    (hi : i < a) : IsZero (K.X.X i) := by
  have := S.mono_εZero i
  exact IsZero.of_mono (S.εZero i) (S.isZero_X_obj_of_lt hi 0)

/-- `F^p K^i = 0` for `i < a`, the step being a subobject of `K^i`. -/
private lemma ResolutionSystem.isZero_X_filtration_of_lt
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) {i : ℤ}
    (hi : i < a) (p : ℤᵒᵖ) : IsZero ((K.filtration.obj p).X i) :=
  isZero_filtration_obj_X_of_isZero (S.isZero_X_of_lt hi) p

/-- Each `K^i` has finite filtration, the hypothesis of [Stacks, Tag 05TW] recovered from the
resolution system. Strictness of `ε_i` in degree `0` makes `F^p K^i` the intersection of `K^i` with
`F^p I_i^0`, so it is all of `K^i` at an index where the filtration of `I_i^0` exhausts; and it is
zero at an index where that filtration vanishes, `K^i` being a subobject of `I_i^0`. -/
private lemma ResolutionSystem.isFinite_eval
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (i : ℤ) :
    (evalFil K i).filtration.IsFinite := by
  obtain ⟨p, q, hp, hq⟩ := S.isFinite i 0
  refine .of_exists ⟨p, ?_⟩ ⟨q, ?_⟩
  · have := hp
    exact (S.isPullback_εZeroStep (op p) i).isIso_snd_of_isIso
  · have := S.mono_εZero i
    have h0 : (K.filtration.ι.app (op q)).f i = 0 := by
      rw [← cancel_mono (S.εZero i), zero_comp, ← S.εZeroStep_comp_ι (op q) i,
        hq.eq_zero_of_tgt (S.εZeroStep (op q) i), zero_comp]
    have hz : IsZero ((K.filtration.obj (op q)).X i) := by
      rw [IsZero.iff_id_eq_zero, ← cancel_mono ((K.filtration.ι.app (op q)).f i), Category.id_comp,
        h0, comp_zero]
    exact hz

/-- **Step (1).** Every filtration step of every `ε_i` is a quasi-isomorphism: `ε_i` is a filtered
quasi-isomorphism between complexes whose filtrations are degreewise finite, which is
[Stacks, Tag 05S3] in the form `quasiIso_natTrans_app_of_filteredQuasiIso`. -/
private lemma ResolutionSystem.quasiIso_ε_natTrans_app
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (i : ℤ)
    (p : ℤᵒᵖ) : QuasiIso ((S.ε i).natTrans.app p) :=
  CochainComplex.quasiIso_natTrans_app_of_filteredQuasiIso (S.ε i) (S.filteredQuasiIso_ε i)
    (isDegreewiseFinite_singleFil 0 (S.isFinite_eval i)) (S.isFinite i) p

/-- The complex `F^p K^•` placed in second degree `0` has a total complex: it is supported in
`i ≥ a`, `n ≥ 0`. -/
private lemma ResolutionSystem.hasTotal_singleRowZero
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    (singleRowZero (K.filtration.obj p)).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded _ a (fun i n hn => isZero_singleRowZero_X_X _ i n hn)
    (fun _ hi => Functor.map_isZero (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0)
      (S.isZero_X_filtration_of_lt hi p))

/-- The morphism of double complexes `F^p K^•[0] ⟶ F^p I^{•, •}` whose column `i` is the filtration
step `F^p ε_i` of the resolution of the term `K^i`: a morphism of double complexes by the `p`-th
component of the `comm` field of the resolution system. -/
private noncomputable def ResolutionSystem.stepε
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    singleRowZero (K.filtration.obj p) ⟶ S.doubleComplexStep p :=
  CochainComplex.ofHom (fun i => (S.ε i).natTrans.app p) (fun i => by
    simp only [doubleComplexStep, CochainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
    exact S.ε_natTrans_comm i p)

/-- The filtration step of the comparison map is the total complex of `stepε`, read through the
identification of `F^p K^•` with `Tot(F^p K^•[0])`: in each degree both maps are `F^p ε_n` in
degree `0` followed by the inclusion of the corner summand. -/
private lemma ResolutionSystem.totalHomStep_eq
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ)
    [(singleRowZero (K.filtration.obj p)).HasTotal (ComplexShape.up ℤ)] :
    S.totalHomStep p = totalSingleRowZeroUnit (K.filtration.obj p) ≫
      HomologicalComplex₂.total.map (S.stepε p) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [HomologicalComplex.comp_f, totalHomStep_f]
  dsimp only [totalSingleRowZeroUnit]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  rfl

/-- **Step (2).** Each filtration step of the comparison map is a quasi-isomorphism: it is the
total complex of `stepε`, whose columns are quasi-isomorphisms by step (1) and whose two double
complexes are supported in `i ≥ a`, `n ≥ 0`, so Weibel's acyclic assembly lemma
([Stacks, Tag 0133], `quasiIso_total_map`) applies. -/
private lemma ResolutionSystem.quasiIso_totalHomStep
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤᵒᵖ) :
    QuasiIso (S.totalHomStep p) := by
  have := S.hasTotal_singleRowZero p
  have : IsIso (totalSingleRowZeroUnit (K.filtration.obj p)) :=
    isIso_totalSingleRowZeroUnit (K.filtration.obj p)
  have : QuasiIso (HomologicalComplex₂.total.map (S.stepε p) (ComplexShape.up ℤ)) :=
    quasiIso_total_map _ a (fun i n hn => isZero_singleRowZero_X_X _ i n hn)
      (fun i hi => Functor.map_isZero (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0)
        (S.isZero_X_filtration_of_lt hi p))
      (fun i n hn => S.isZero_X_filtration_obj i p hn)
      (fun i hi => isZero_filtration_obj_of_isZero (S.isZero i hi) p)
      (fun i => S.quasiIso_ε_natTrans_app i p)
  rw [S.totalHomStep_eq p]
  infer_instance

/-- The short exact sequence `0 → F^{p + 1} X^• → F^p X^• → gr^p X^• → 0` of a filtered complex:
`gr^p` is by definition the cokernel of the transition map, which is a degreewise monomorphism. -/
private noncomputable abbrev gradedPieceSES (J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤ) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk (filtrationStep J p) (cokernel.π (filtrationStep J p)) (cokernel.condition _)

private lemma shortExact_gradedPieceSES (J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p : ℤ) :
    (gradedPieceSES J p).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := HomologicalComplex.mono_of_mono_f _ (mono_filtrationStep_f J p)
  epi_g := inferInstance

/-- The comparison map as a morphism of the sequences `F^{p + 1} → F^p → gr^p` of `K^•` and of
`Tot(I^{•, •})`: on the two left-hand terms its filtration steps, on the quotients `gr^p(α)`. -/
@[simps τ₁ τ₂]
private noncomputable def ResolutionSystem.gradedPieceSESMap
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) (p : ℤ) :
    gradedPieceSES K p ⟶ gradedPieceSES S.totalObj p where
  τ₁ := S.totalα.natTrans.app (op (p + 1))
  τ₂ := S.totalα.natTrans.app (op p)
  τ₃ := (FilteredObject.gr p).map S.totalα
  comm₁₂ :=
    (S.totalα.natTrans.naturality (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op).symm
  comm₂₃ := (grMapπ_map _ _).symm

/-- **Step (3).** The comparison map is a filtered quasi-isomorphism: it is a morphism of the two
short exact sequences `F^{p + 1} → F^p → gr^p`, a quasi-isomorphism on the two left-hand terms by
step (2), hence one on the quotients. -/
private lemma ResolutionSystem.filteredQuasiIso_totalα
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    CochainComplex.filteredQuasiIso 𝒜 S.totalα := by
  intro p
  have : QuasiIso (S.gradedPieceSESMap p).τ₁ := by
    rw [gradedPieceSESMap_τ₁]
    exact S.quasiIso_totalHomStep (op (p + 1))
  have : QuasiIso (S.gradedPieceSESMap p).τ₂ := by
    rw [gradedPieceSESMap_τ₂]
    exact S.quasiIso_totalHomStep (op p)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ (S.gradedPieceSESMap p)
    (shortExact_gradedPieceSES K p) (shortExact_gradedPieceSES S.totalObj p) inferInstance
    inferInstance

/-- **Step (4).** The comparison map is strict: in degree `n` the square `F^p K^n ⟶ K^n`,
`Tot(F^p I^{•, •})^n ⟶ Tot(I^{•, •})^n` is the pullback square of `isStrictHom_ε` in degree `0`
pasted with the intersection of `Tot(F^p I^{•, •})^n` with the corner summand `I_n^0`, which is
`F^p I_n^0` because the antidiagonal meets the support of the double complex in a finite set, so
that intersection is computed summandwise. -/
private lemma ResolutionSystem.isStrictHom_totalα
    {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} {a : ℤ} (S : ResolutionSystem K a) :
    FilteredObject.IsStrictHom S.totalα where
  isPullback p := by
    refine isPullback_of_degreewise (S.totalα.comm p) (fun n => inferInstance) (fun n => ?_)
    have h3 : ((S.stepι p).f n).f 0 = ((S.obj n).filtration.ι.app p).f 0 := rfl
    have hcorner := isPullback_ιTotal_of_isZero (S.stepι p)
      (fun i k => inferInstanceAs (Mono (((S.obj i).filtration.ι.app p).f k))) a
      (fun _ k hi => S.isZero_X_filtration_obj_of_lt hi p k)
      (fun i _ hk => S.isZero_X_filtration_obj i p hk)
      (fun _ k hi => S.isZero_X_obj_of_lt hi k) (fun i _ hk => S.isZero_X_obj i hk) n 0 n (by simp)
    rw [h3] at hcorner
    exact (S.isPullback_εZeroStep p n).paste_horiz hcorner

end Comparison

/-! ### Strictness and monomorphy in degree `0` of a filtered quasi-isomorphism

[Stacks, Tag 05TV] produces the resolution `ε_i : K^i[0] ⟶ M_i` of a term of `K^•` as a filtered
quasi-isomorphism; a `ResolutionSystem` also needs it to be a strict monomorphism in degree `0`.
Both come from the steps `F^p ε_i` being quasi-isomorphisms ([Stacks, Tag 05S3]). For an index `q`
below `p` the sequences `0 → F^p → F^q → F^q/F^p → 0` of `K^i[0]` and of `M_i` are short exact and
`ε_i` is a quasi-isomorphism on the two left-hand terms, hence on the quotients; those are
concentrated in degrees `≥ 0` and the source in degree `0`, so `F^q/F^p(ε_i)` is a monomorphism in
degree `0`, which makes the square `F^p K^i ⟶ F^q K^i`, `F^p M_i^0 ⟶ F^q M_i^0` a pullback. Taking
`q` below an index exhausting the filtration of `K^i` turns that into the strictness square in
degree `0`, and the same monomorphy in degree `0` gives `Mono (ε_i)^0`.
-/

section Strictness

variable {B M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}

/-- Cokernels of complexes are computed degreewise, so the cokernel of a morphism of complexes
vanishes in a degree where its target does. -/
private lemma isZero_cokernel_X_of_isZero {C₁ C₂ : CochainComplex 𝒜 ℤ} (g : C₁ ⟶ C₂) {n : ℤ}
    (h : IsZero (C₂.X n)) : IsZero ((cokernel g).X n) :=
  have : Epi (g.f n) := h.epi _
  IsZero.of_iso (isZero_cokernel_of_epi (g.f n))
    (PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) g)

/-- A graded piece of a zero filtered complex vanishes in every degree. -/
private lemma isZero_gradedPiece_X_of_isZero {J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (hJ : IsZero J.X) (p n : ℤ) :
    IsZero (((FilteredObject.gr p).obj J).X n) :=
  isZero_cokernel_X_of_isZero _ (isZero_filtration_obj_X_of_isZero
    (Functor.map_isZero (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) hJ) _)

/-- The square of two filtration steps of a filtered quasi-isomorphism out of a complex
concentrated in degree `0` is a pullback: the induced map of quotients is a quasi-isomorphism, so a
monomorphism in degree `0`, and in every other degree its source vanishes. -/
private lemma isPullback_diagram_map (b : B ⟶ M) (hB : ∀ n : ℤ, n ≠ 0 → IsZero (B.X.X n))
    (hMm : IsZero (M.X.X (-1))) (hBfin : B.filtration.IsDegreewiseFinite)
    (hMfin : M.filtration.IsDegreewiseFinite) (hb : CochainComplex.filteredQuasiIso 𝒜 b)
    {i j : ℤᵒᵖ} (f : i ⟶ j) :
    IsPullback (b.natTrans.app i) (B.filtration.diagram.map f) (M.filtration.diagram.map f)
      (b.natTrans.app j) := by
  have hq₁ : QuasiIso (b.natTrans.app i) :=
    CochainComplex.quasiIso_natTrans_app_of_filteredQuasiIso b hb hBfin hMfin i
  have hq₂ : QuasiIso (b.natTrans.app j) :=
    CochainComplex.quasiIso_natTrans_app_of_filteredQuasiIso b hb hBfin hMfin j
  have hτ₃ : QuasiIso (cokernel.map (B.filtration.diagram.map f) (M.filtration.diagram.map f)
      (b.natTrans.app i) (b.natTrans.app j) (b.natTrans.naturality f)) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ (stepShortComplexMap f b)
      (stepShortComplex_shortExact f B) (stepShortComplex_shortExact f M) hq₁ hq₂
  have hzB : ∀ n : ℤ, n ≠ 0 → IsZero ((cokernel (B.filtration.diagram.map f)).X n) := fun n hn =>
    isZero_cokernel_X_of_isZero _ (isZero_filtration_obj_X_of_isZero (hB n hn) j)
  refine isPullback_of_mono_cokernel_map (b.natTrans.naturality f)
    (HomologicalComplex.mono_of_mono_f _ (fun n => ?_))
  by_cases hn : n = 0
  · subst hn
    have := hτ₃
    exact mono_f_zero_of_quasiIso _ (hzB 1 one_ne_zero) (hzB (-1) (by norm_num))
      (isZero_cokernel_X_of_isZero _ (isZero_filtration_obj_X_of_isZero hMm j))
  · exact (hzB n hn).mono _

/-- The strictness square in degree `0` of a filtered quasi-isomorphism out of a complex
concentrated in degree `0`: the square of `isPullback_diagram_map` for an index `q` below both `p`
and an index exhausting the filtration of `B^0`, evaluated in degree `0` and pasted with the square
at `q`, whose left edge is then an isomorphism. -/
private lemma isPullback_natTrans_app_f_zero (b : B ⟶ M) (hB : ∀ n : ℤ, n ≠ 0 → IsZero (B.X.X n))
    (hMm : IsZero (M.X.X (-1))) (hBfin : B.filtration.IsDegreewiseFinite)
    (hMfin : M.filtration.IsDegreewiseFinite) (hb : CochainComplex.filteredQuasiIso 𝒜 b)
    (i : ℤᵒᵖ) :
    IsPullback ((b.natTrans.app i).f 0) ((B.filtration.ι.app i).f 0)
      ((M.filtration.ι.app i).f 0) (b.hom.f 0) := by
  obtain ⟨p⟩ := i
  obtain ⟨r, -, hr, -⟩ := hBfin 0
  have hiso : IsIso ((B.filtration.ι.app (op (min r p))).f 0) :=
    isIso_filtration_ι_f_of_le B.filtration (min_le_left r p) 0 hr
  have hsq : IsPullback ((b.natTrans.app (op p)).f 0)
      ((B.filtration.diagram.map (homOfLE (min_le_right r p)).op).f 0)
      ((M.filtration.diagram.map (homOfLE (min_le_right r p)).op).f 0)
      ((b.natTrans.app (op (min r p))).f 0) :=
    (isPullback_diagram_map b hB hMm hBfin hMfin hb (homOfLE (min_le_right r p)).op).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) 0)
  have hbot : IsPullback ((b.natTrans.app (op (min r p))).f 0)
      ((B.filtration.ι.app (op (min r p))).f 0) ((M.filtration.ι.app (op (min r p))).f 0)
      (b.hom.f 0) :=
    IsPullback.of_vert_isIso_mono ⟨HomologicalComplex.congr_hom (b.comm (op (min r p))) 0⟩
  have hpaste := hsq.paste_vert hbot
  rwa [filtration_diagram_map_f_comp_ι_app_f, filtration_diagram_map_f_comp_ι_app_f] at hpaste

/-- A filtered quasi-isomorphism out of a complex concentrated in degree `0` is strict: in degree
`0` this is `isPullback_natTrans_app_f_zero`, and in every other degree the two left-hand objects
of the square vanish, so its left edge is an isomorphism. -/
private lemma isStrictHom_of_filteredQuasiIso (b : B ⟶ M)
    (hB : ∀ n : ℤ, n ≠ 0 → IsZero (B.X.X n)) (hMm : IsZero (M.X.X (-1)))
    (hBfin : B.filtration.IsDegreewiseFinite) (hMfin : M.filtration.IsDegreewiseFinite)
    (hb : CochainComplex.filteredQuasiIso 𝒜 b) : FilteredObject.IsStrictHom b where
  isPullback i := by
    refine isPullback_of_degreewise (b.comm i) (fun n => inferInstance) (fun n => ?_)
    by_cases hn : n = 0
    · subst hn
      exact isPullback_natTrans_app_f_zero b hB hMm hBfin hMfin hb i
    · have h2 : IsIso ((B.filtration.ι.app i).f n) :=
        (isZero_filtration_obj_X_of_isZero (hB n hn) i).isIso (hB n hn) _
      exact IsPullback.of_vert_isIso_mono ⟨HomologicalComplex.congr_hom (b.comm i) n⟩

/-- A filtered quasi-isomorphism out of a complex concentrated in degree `0` is a monomorphism in
degree `0`: it is so on the filtration step where the filtration of `B^0` is exhausted, that step
being a quasi-isomorphism out of a complex concentrated in degree `0`. -/
private lemma mono_hom_f_zero (b : B ⟶ M) (hB : ∀ n : ℤ, n ≠ 0 → IsZero (B.X.X n))
    (hMm : IsZero (M.X.X (-1))) (hBfin : B.filtration.IsDegreewiseFinite)
    (hMfin : M.filtration.IsDegreewiseFinite) (hb : CochainComplex.filteredQuasiIso 𝒜 b) :
    Mono (b.hom.f 0) := by
  obtain ⟨r, -, hr, -⟩ := hBfin 0
  have hq : QuasiIso (b.natTrans.app (op r)) :=
    CochainComplex.quasiIso_natTrans_app_of_filteredQuasiIso b hb hBfin hMfin (op r)
  have hm : Mono ((b.natTrans.app (op r)).f 0) :=
    mono_f_zero_of_quasiIso _
      (isZero_filtration_obj_X_of_isZero (hB 1 one_ne_zero) _)
      (isZero_filtration_obj_X_of_isZero (hB (-1) (by norm_num)) _)
      (isZero_filtration_obj_X_of_isZero hMm _)
  have hfac : (b.natTrans.app (op r)).f 0 ≫ (M.filtration.ι.app (op r)).f 0 =
      (B.filtration.ι.app (op r)).f 0 ≫ b.hom.f 0 :=
    HomologicalComplex.congr_hom (b.comm (op r)) 0
  have hmc : Mono ((B.filtration.ι.app (op r)).f 0 ≫ b.hom.f 0) := by
    rw [← hfac]
    have := hm
    infer_instance
  have he : b.hom.f 0 = inv ((B.filtration.ι.app (op r)).f 0) ≫
      ((B.filtration.ι.app (op r)).f 0 ≫ b.hom.f 0) := (IsIso.inv_hom_id_assoc _ _).symm
  rw [he]
  have := hmc
  infer_instance

end Strictness

/-! ### The two halves of the construction -/

/-- **The first half of the source's construction**, Lemmas 05TT, 05TU and 05TV: the short exact
sequences `0 → Ker(d_K^i) → K^i → Coim(d_K^i) → 0` of `Fil^f(𝒜)` and the maps
`u_i : Coim(d_K^i) → Ker(d_K^{i + 1})`, resolved termwise and assembled into a complex of filtered
injective resolutions of the terms of `K^•`.

For each `i` independently: `Ker(d^i)` and `Coim(d^i)`, with the filtrations induced from `K^i`,
are resolved by [Stacks, Tag 05TT] as `I_i` and `J_i`, which asks for their filtrations to be
finite — they are, `K^i` having finite filtration. The short exact sequence
`0 → Ker(d^i) → K^i → Coim(d^i) → 0`, whose graded pieces are short exact by
`shortExact_gradedPiece_kernelFilι_coimageFilπ`, is then filled in by [Stacks, Tag 05TV]: it
produces `M_i` with `u_i : I_i ⟶ M_i`, `v_i : M_i ⟶ J_i` and `ε_i : K^i[0] ⟶ M_i`, and its
post-processing gives the properties of `M_i` and that `ε_i` is a filtered quasi-isomorphism.
Finally `g_i : J_i ⟶ I_{i + 1}` is the [Stacks, Tag 05TU] lift of the connecting map
`coimKer K i : Coim(d^i) ⟶ Ker(d^{i + 1})` along the two 05TT resolutions, and
`d_i = v_i ≫ g_i ≫ u_{i + 1}`. The differentials square to zero because
`u_{i + 1} ≫ v_{i + 1} = 0`, and `comm` holds because the 05TU lift commutes on the nose and
`coimageFilπ ≫ coimKer ≫ kernelFilι` is the differential.

For `i < a` the term `K^i` vanishes, so `K^i[0]` is itself a resolution of it, and taking
`M_i = K^i[0]` with `ε_i` the identity is what makes `I_i^•` zero there. -/
private theorem exists_resolutionSystem [EnoughInjectives 𝒜]
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ) [K.X.IsStrictlyGE a]
    (hK : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n)) :
    Nonempty (ResolutionSystem K a) := by
  classical
  have hfin : ∀ i : ℤ, (evalFil K i).filtration.IsFinite := isFinite_eval hK
  have hker : ∀ i : ℤ, (kernelFil (evalD K i)).filtration.IsFinite := fun i =>
    kernelFil_filtration_isFinite _ (hfin i)
  have hcoim : ∀ i : ℤ, (coimageFil (evalD K i)).filtration.IsFinite := fun i =>
    coimageFil_filtration_isFinite _ (hfin i)
  -- the composite `Ker(d^i) ⟶ K^i ⟶ Coim(d^i)` vanishes
  have hcompz : ∀ i : ℤ,
      (kernelFilι (evalD K i) ≫ coimageFilπ (evalD K i)).hom = 0 := fun i => by
    rw [FilteredObject.comp_hom, coimageFilπ_hom]
    exact cokernel.condition _
  have hcomp : ∀ i : ℤ, ((singleFil 0).map (kernelFilι (evalD K i))).hom ≫
      ((singleFil 0).map (coimageFilπ (evalD K i))).hom = 0 := fun i => by
    rw [singleFil_map_hom, singleFil_map_hom, ← Functor.map_comp, ← FilteredObject.comp_hom,
      hcompz i, Functor.map_zero]
  have hgr : ∀ (i p : ℤ) (h : (gr p).map
        ((singleFil 0).map (kernelFilι (evalD K i))) ≫
      (gr p).map
        ((singleFil 0).map (coimageFilπ (evalD K i))) = 0),
      (ShortComplex.mk _ _ h).ShortExact := fun i p h =>
    shortExact_gradedPiece_singleFil_map 0 _ _ (hcompz i)
      (fun p _ => shortExact_gradedPiece_kernelFilι_coimageFilπ _ p) p h
  -- 05TT, applied to the kernels and to the coimages
  have hres : ∀ A : FilteredObject 𝒜 ℤᵒᵖ, A.filtration.IsFinite →
      ∃ (I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : (singleFil 0).obj A ⟶ I),
        CochainComplex.filteredQuasiIso 𝒜 α ∧ I.X.IsStrictlyGE 0 ∧
        (∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
          IsZero ((I.filtration.obj (op q)).X n)) ∧
        ∀ p n : ℤ, Injective (((gr p).obj I).X n) := by
    intro A hA
    obtain ⟨I, α, hqis, hge, hI⟩ :=
      CochainComplex.exists_filteredQuasiIso_isStrictlyGE_injective_gradedPiece
        ((singleFil 0).obj A) (isFinite_singleFil 0 hA)
    exact ⟨I, α, hqis, hge, fun n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).1,
      fun p n => ((isFilteredInjective_evalFil_iff I n).1 (hI n)).2 p⟩
  choose IK αK hIKqis hIKge hIKfin hIKinj using fun i : ℤ => hres _ (hker i)
  choose JC γC hJCqis hJCge hJCfin hJCinj using fun i : ℤ => hres _ (hcoim i)
  -- 05TV and its post-processing, applied to the short exact sequence of the `i`-th term
  have hstage : ∀ i : ℤ, ∃ (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (u : IK i ⟶ M)
      (v : M ⟶ JC i) (ε : (singleFil 0).obj (evalFil K i) ⟶ M),
      M.X.IsStrictlyGE 0 ∧ (i < a → IsZero M.X) ∧
      (∀ n : ℤ, ∃ p q : ℤ, IsIso ((M.filtration.ι.app (op p)).f n) ∧
        IsZero ((M.filtration.obj (op q)).X n)) ∧
      (∀ p n : ℤ, Injective (((gr p).obj M).X n)) ∧
      CochainComplex.filteredQuasiIso 𝒜 ε ∧ FilteredObject.IsStrictHom ε ∧
      Mono (ε.hom.f 0) ∧ u.hom ≫ v.hom = 0 ∧
      (singleFil 0).map (kernelFilι (evalD K i)) ≫ ε = αK i ≫ u ∧
      ε ≫ v = (singleFil 0).map (coimageFilπ (evalD K i)) ≫ γC i := by
    intro i
    by_cases hia : i < a
    · have hz : IsZero ((singleFil 0).obj (evalFil K i)).X :=
        Functor.map_isZero (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0)
          (K.X.isZero_of_isStrictlyGE a i hia)
      refine ⟨(singleFil 0).obj (evalFil K i),
        FilteredObject.homMk 0 (fun _ => 0) (fun _ => hz.eq_of_tgt _ _),
        FilteredObject.homMk 0 (fun _ => 0)
          (fun x => (isZero_filtration_obj_of_isZero hz x).eq_of_src _ _), 𝟙 _,
        inferInstance, fun _ => hz, isDegreewiseFinite_singleFil 0 (hfin i),
        fun p n => (isZero_gradedPiece_X_of_isZero hz p n).injective,
        fun p => by rw [CategoryTheory.Functor.map_id]; infer_instance, inferInstance,
        (Functor.map_isZero (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) 0) hz).mono _,
        by simp, FilteredObject.hom_ext (hz.eq_of_tgt _ _),
        FilteredObject.hom_ext (hz.eq_of_src _ _)⟩
    · have := hIKge i
      have := hJCge i
      obtain ⟨M, u, v, ε, huv, hSE, hαb, hbv, hsplit⟩ :=
        CochainComplex.exists_termwiseSplit_shortExact_of_filteredQuasiIso_of_injective_gr
          ((singleFil 0).map (kernelFilι (evalD K i)))
          ((singleFil 0).map (coimageFilπ (evalD K i))) (αK i) (γC i) (hcomp i)
          (fun p => hgr i p _) (hIKqis i) (hJCqis i)
          (isDegreewiseFinite_singleFil 0 (hker i)) (isDegreewiseFinite_singleFil 0 (hfin i))
          (isDegreewiseFinite_singleFil 0 (hcoim i)) (hJCfin i)
          (fun n => (isFilteredInjective_evalFil_iff _ n).2 ⟨hIKfin i n, fun p => hIKinj i p n⟩)
      obtain ⟨hMge, hMfin, hMinj, hεqis⟩ :=
        isStrictlyGE_isDegreewiseFinite_injective_gr_filteredQuasiIso_of_termwiseSplit
          ((singleFil 0).map (kernelFilι (evalD K i)))
          ((singleFil 0).map (coimageFilπ (evalD K i))) (αK i) (γC i) u v ε (hcomp i) (hgr i)
          (hIKqis i) (hJCqis i) (hIKfin i) (hJCfin i) (hIKinj i) (hJCinj i) huv hSE hαb hbv hsplit
      have := hMge
      have hBz : ∀ n : ℤ, n ≠ 0 → IsZero (((singleFil 0).obj (evalFil K i)).X.X n) := fun n hn =>
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn
      have hMm : IsZero (M.X.X (-1)) := M.X.isZero_of_isStrictlyGE 0 (-1) (by norm_num)
      exact ⟨M, u, v, ε, hMge, fun h => absurd h hia, hMfin, hMinj, hεqis,
        isStrictHom_of_filteredQuasiIso ε hBz hMm
          (isDegreewiseFinite_singleFil 0 (hfin i)) hMfin hεqis,
        mono_hom_f_zero ε hBz hMm (isDegreewiseFinite_singleFil 0 (hfin i)) hMfin hεqis,
        huv, hαb, hbv⟩
  choose M u v ε hMge hMzero hMfin hMinj hεqis hεstrict hεmono huv hαb hbv using hstage
  -- 05TU: the lift of the connecting map to the chosen resolutions
  have hlift : ∀ i : ℤ, ∃ g : JC i ⟶ IK (i + 1),
      γC i ≫ g = (singleFil 0).map (coimKer K i) ≫ αK (i + 1) := by
    intro i
    have := hIKge (i + 1)
    exact CochainComplex.exists_hom_comp_eq_of_filteredQuasiIso_of_injective_gradedPiece
      ((singleFil 0).map (coimKer K i)) (γC i) (αK (i + 1)) (hJCqis i)
      (isDegreewiseFinite_singleFil 0 (hcoim i)) (hJCfin i) (fun n =>
        (isFilteredInjective_evalFil_iff _ n).2 ⟨hIKfin (i + 1) n, fun p => hIKinj (i + 1) p n⟩)
  choose g hg using hlift
  refine ⟨{ obj := M
            isStrictlyGE := hMge
            isZero := hMzero
            isFinite := hMfin
            injective := hMinj
            ε := ε
            filteredQuasiIso_ε := hεqis
            isStrictHom_ε := hεstrict
            mono_ε := hεmono
            d := fun i => v i ≫ g i ≫ u (i + 1)
            d_comp_d := fun i => ?_
            comm := fun i => ?_ }⟩
  · have h := huv (i + 1)
    simp only [FilteredObject.comp_hom, Category.assoc]
    rw [← Category.assoc (u (i + 1)).hom, h, zero_comp, comp_zero, comp_zero]
  · have h1 := hbv i
    have h2 := hg i
    have h3 := hαb (i + 1)
    have key : (singleFil 0).map (coimageFilπ (evalD K i)) ≫ (singleFil 0).map (coimKer K i) ≫
        (singleFil 0).map (kernelFilι (evalD K (i + 1))) = (singleFil 0).map (evalD K i) := by
      rw [← Functor.map_comp, ← Functor.map_comp, coimageFilπ_comp_coimKer_comp_kernelFilι]
    rw [← key]
    simp only [Category.assoc, reassoc_of% h1, reassoc_of% h2]
    rw [← h3]

/-- **The two `gr`-level clauses of the second half**: the comparison map `α = totalα` is a
filtered quasi-isomorphism, and it is strict. Everything else the conclusion asks for is
`ResolutionSystem.mono_totalα_hom`, `ResolutionSystem.isStrictlyGE_totalObj`,
`ResolutionSystem.isDegreewiseFinite_totalObj` and
`ResolutionSystem.injective_gradedPiece_totalObj`.

*The filtered quasi-isomorphism*, in three steps. (1) Every filtration step of every `ε_i` is a
quasi-isomorphism, which is [Stacks, Tag 05S3] in the form
`CochainComplex.quasiIso_natTrans_app_of_filteredQuasiIso`: `ε_i` is a filtered quasi-isomorphism
between complexes with degreewise finite filtrations, the filtration of `K^i` being finite because
strictness of `ε_i` in degree `0` makes `F^p K^i` the intersection of `K^i` with `F^p I_i^0`
(`ResolutionSystem.isFinite_eval`). (2) Each filtration step of `α` is then a quasi-isomorphism:
`ResolutionSystem.totalHomStep p` is `totalSingleRowZeroUnit (F^p K^•)` followed by the total
complex of the morphism of double complexes `ResolutionSystem.stepε p`, whose column `i` is
`(ε i).natTrans.app p` — a morphism of double complexes by the `p`-th component of `comm i`, and
equal to `totalHomStep p` by `ιTotal_map`, both maps being `εZeroStep ≫ ιTotal` in each degree. So
`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map`, which is [Stacks, Tag 0133] in the form of
Weibel's acyclic assembly lemma, applies: the columns are quasi-isomorphisms by (1) and both double
complexes are supported in `i ≥ a`, `n ≥ 0`. (3) `gr^p(α)` is a quasi-isomorphism: `gr^p` is by
definition the cokernel of `F^{p + 1} ⟶ F^p`, so `F^{p + 1} ⟶ F^p ⟶ gr^p` is short exact
(`ShortComplex.exact_cokernel`, the first map a monomorphism by `mono_filtrationStep_f` and the
second an epimorphism) both for `K^•` and for `Tot(I^{•, •})`, and `α` is a morphism of these two
short exact sequences which is a quasi-isomorphism on the two left-hand terms by (2), so
`HomologicalComplex.HomologySequence.quasiIso_τ₃` gives it on the quotients.

*Strictness.* (4) Each square `F^p K^• ⟶ K^•`, `Tot(F^p I^{•, •}) ⟶ Tot(I^{•, •})` is a pullback,
which is checked degree by degree, the vertical maps being degreewise monomorphisms
(`isPullback_of_degreewise`): in degree `n` the square is the strictness `isStrictHom_ε` of `ε_n`
read in degree `0` (`ResolutionSystem.isPullback_εZeroStep`) pasted with the fact that the
subobject `Tot(F^p I^{•, •})^n ⟶ Tot(I^{•, •})^n` meets the corner summand `I_n^0` in `F^p I_n^0`.
That last square is `isPullback_ιTotal_of_isZero`: the antidiagonal `i + k = n` meets the support
in a finite set, so the coproducts are biproducts and the intersection is computed summandwise. -/
private theorem filteredQuasiIso_isStrictHom_totalα
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ) (S : ResolutionSystem K a) :
    CochainComplex.filteredQuasiIso 𝒜 S.totalα ∧ FilteredObject.IsStrictHom S.totalα :=
  ⟨S.filteredQuasiIso_totalα, S.isStrictHom_totalα⟩

/-- The `gr`-level clauses of the second half of the source's construction: the comparison map is a
filtered quasi-isomorphism, it is strict, and the graded pieces of the total complex are injective.
The last clause is proved, `gr^p(Tot(I^{•, •}))^n` being the cokernel of a monomorphism between the
injective objects `Tot(F^{p + 1} I^{•, •})^n` and `Tot(F^p I^{•, •})^n`; the first two are
`filteredQuasiIso_isStrictHom_totalα`. -/
private theorem gradedPiece_totalα
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ) (S : ResolutionSystem K a) :
    CochainComplex.filteredQuasiIso 𝒜 S.totalα ∧ FilteredObject.IsStrictHom S.totalα ∧
      ∀ p n : ℤ, Injective (((FilteredObject.gr p).obj
        S.totalObj).X n) :=
  ⟨(filteredQuasiIso_isStrictHom_totalα K a S).1,
    (filteredQuasiIso_isStrictHom_totalα K a S).2,
    fun p n => S.injective_gradedPiece_totalObj p n⟩

/-- **The second half of the source's construction**, Homology, Definition 012Z and Lemma 0133:
the total complex of the double complex `I^{i, n} = I_i^n` of a `ResolutionSystem`, and the fact
that `K^• ⟶ Tot(I^{•, •})` is a filtered quasi-isomorphism, `gr^p` being additive, hence
commuting with the total complex. -/
private theorem exists_of_resolutionSystem
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ) [K.X.IsStrictlyGE a]
    (S : ResolutionSystem K a) :
    ∃ (I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : K ⟶ I)
      (_ : CochainComplex.filteredQuasiIso 𝒜 α) (_ : Mono α.hom)
      (_ : FilteredObject.IsStrictHom α) (_ : I.X.IsStrictlyGE a)
      (_ : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
            IsZero ((I.filtration.obj (op q)).X n)),
      ∀ p n : ℤ, Injective (((FilteredObject.gr p).obj I).X n) := by
  obtain ⟨hqis, hstrict, hinj⟩ := gradedPiece_totalα K a S
  exact ⟨S.totalObj, S.totalα, hqis, S.mono_totalα_hom, hstrict, S.isStrictlyGE_totalObj,
    S.isDegreewiseFinite_totalObj, hinj⟩

end CochainComplex.FilteredInjectiveResolution

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

open FilteredInjectiveResolution in
/-- **Stacks 05TW.** Let `𝒜` be an abelian category with enough injectives and let `K^•` be a
filtered cochain complex of `𝒜` with `K^n = 0` for `n < a` and with each `K^n` of finite
filtration, i.e. an object of `K^+(Fil^f(𝒜))`. Then there is a filtered quasi-isomorphism
`α : K^• ⟶ I^•`, that is, one whose graded pieces `gr^p(α)` are all quasi-isomorphisms, which is
moreover a strict monomorphism — degreewise, each `K^n ⟶ I^n` is a monomorphism with
`F^p K^n = (K^n) ∩ F^p I^n` — where `I^•` is a complex of filtered injective objects with
`I^n = 0` for `n < a`: every term `(I^n, F^• I^n)` is a filtered injective object of
`Fil^f(𝒜)`. -/
@[stacks 05TW, ega "0 13.6.2" "existence of resolution"]
public theorem exists_mono_isStrictHom_filteredQuasiIso_isStrictlyGE_injective_gradedPiece
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (a : ℤ) [K.X.IsStrictlyGE a]
    (hK : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
      IsZero ((K.filtration.obj (op q)).X n)) :
    ∃ (I : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (α : K ⟶ I)
      (_ : CochainComplex.filteredQuasiIso 𝒜 α) (_ : Mono α.hom)
      (_ : FilteredObject.IsStrictHom α) (_ : I.X.IsStrictlyGE a),
      ∀ n : ℤ, (evalFil I n).IsFilteredInjective := by
  obtain ⟨S⟩ := exists_resolutionSystem K a hK
  obtain ⟨I, α, h₁, h₂, h₃, h₄, hfin, hinj⟩ := exists_of_resolutionSystem K a S
  exact ⟨I, α, h₁, h₂, h₃, h₄,
    fun n => (isFilteredInjective_evalFil_iff I n).2 ⟨hfin n, fun p => hinj p n⟩⟩

end CochainComplex

end
