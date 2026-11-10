module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 09V7: a locally bounded above complex of pseudo-coherent `𝒪_X`-modules

Let `X` be a ringed space and let `𝒦` be a complex of `𝒪_X`-modules whose term in degree `i`,
viewed in degree `i` in the derived category, is `m`-pseudo-coherent for every `i` — equivalently,
whose term `𝒦^i` is `(m - i)`-pseudo-coherent, which is how the source phrases it. If `𝒦` is
locally bounded above then `𝒦` is `m`-pseudo-coherent. This is Stacks 09V7, whose proof the
source omits with the hint "use Lemma 08CD and truncations".

The globally bounded above form is also the one ingredient of the forward half of Stacks 09VA
that is not a formal consequence of the material already in the library: pushing a strictly perfect
complex `𝒫`
on `Z` forward along a closed immersion `i : Z ⟶ X` produces a bounded complex of `𝒪_X`-modules
whose terms are direct summands of `(i_*𝒪_Z)^{⊕n}`, and the hypothesis of Stacks 09VA is about
`i_*𝒪_Z` itself, so what is needed is exactly the passage from the terms to the complex.

## Main results

* `CochainComplex.exists_distTriang_single_stupidTruncLE`: the distinguished triangle in
  `D(C)` splitting the top term off a complex bounded above by `b`, namely
  `𝒦^b[-b] ⟶ 𝒦 ⟶ σ^{≤ b-1}𝒦 ⟶ 𝒦^b[-b+1]`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_bounded`: a bounded complex with
  `m`-pseudo-coherent terms is `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_boundedAbove`: the same for a
  complex which is only bounded above.
* `AlgebraicGeometry.RingedSpace.derivedRestrictSingleFunctorIso`: restricting a module placed
  in a single degree is restricting it and then placing it in that degree.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero`: a
  module which is `(m - j)`-pseudo-coherent in degree zero is `m`-pseudo-coherent in degree `j`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_locally_boundedAbove`: Stacks
  09V7 itself.

## Implementation notes

The triangle is produced from a short exact sequence of complexes rather than from a mapping
cone. The sequence is the stupid truncation one,
`0 ⟶ 𝒦^b[-b] ⟶ 𝒦 ⟶ σ^{≤ b-1}𝒦 ⟶ 0`: its first map is
`HomologicalComplex.mkHomFromSingle` on the identity of `𝒦^b`, its second is
`ComplexShape.Embedding.liftExtend` on the identity of the restriction, and it is degreewise
split because in every degree one of the two maps is an isomorphism and the opposite outer term
is zero (`CategoryTheory.ShortComplex.Splitting.ofIsIsoOfIsZero` and `ofIsZeroOfIsIso`). Mathlib
turns such a sequence into a distinguished triangle with `DerivedCategory.triangleOfSES`, and
the first vertex is transported from `Q(𝒦^b[-b])` to `DerivedCategory.singleFunctor` along
`DerivedCategory.singleFunctorIsoCompQ`.

The bounded case is an induction on the number of degrees between the two bounds, with the
space fixed: the lower bound stays put while the upper bound descends, so no localization is
involved and no restriction functor appears. The bounded-above case then needs no second
triangle: the inclusion of the stupid truncation in degrees `≥ m` is an isomorphism on
cohomology above `m` and an epimorphism in degree `m`
(`CochainComplex.isIso_homologyMap_stupidTruncGEIncl` and
`CochainComplex.epi_homologyMap_stupidTruncGEIncl`), so it is an `m`-pseudo-coherent
approximation in the sense of
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_approximation`, and its source is
bounded.

The passage from "bounded above" to "locally bounded above" is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`, which needs the
hypothesis on the terms to be carried to the open subspace. That is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` followed by
`derivedRestrictSingleFunctorIso`, which commutes the restriction functor on `D(𝒪_X)` past
`DerivedCategory.singleFunctor`; the identification of the two complexes underneath is Mathlib's
`HomologicalComplex.singleMapHomologicalComplex`.

Mathlib's `ComplexShape.embeddingUpIntLE b` is indexed by `ℕ` through `n ↦ b - n`, so the index
realizing a degree `i ≤ b` is `(b - i).toNat`; `DerivedCategory.embeddingUpIntLE_f_toNat` records
that, and every use of `HomologicalComplex.stupidTruncXIso` below goes through it.

## References

* [Stacks Project, Lemma 20.46.14 (Tag 09V7)](https://stacks.math.columbia.edu/tag/09V7)
* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.46.10 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect

universe d d' u v₁ u₁

namespace CategoryTheory

/-- Replacing the first vertex of a distinguished triangle by an isomorphic object again gives a
distinguished triangle. -/
public theorem Pretriangulated.mem_distTriang_mk_of_iso_obj₁ {A : Type u₁} [Category.{v₁} A]
    [Limits.HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor A n).Additive] [Pretriangulated A] (T : Triangle A)
    (hT : T ∈ distTriang A) {Y : A} (e : Y ≅ T.obj₁) :
    Triangle.mk (e.hom ≫ T.mor₁) T.mor₂
      (T.mor₃ ≫ (CategoryTheory.shiftFunctor A (1 : ℤ)).map e.inv) ∈ distTriang A :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (by simp)
    (by simp) (by simp [← Functor.map_comp]))

/-- A morphism of complexes which is an isomorphism on cohomology in degree `j` becomes one
after passing to the derived category, the two notions of cohomology being matched by
`DerivedCategory.homologyFunctorFactors`. -/
public theorem isIso_homologyFunctor_map_Q_map {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{d} C] {A B : CochainComplex C ℤ} (φ : A ⟶ B) (j : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap φ j)) :
    IsIso ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map φ)) :=
  (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C j) φ).mpr h

/-- A morphism of complexes which is an epimorphism on cohomology in degree `j` becomes one
after passing to the derived category. -/
public theorem epi_homologyFunctor_map_Q_map {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{d} C] {A B : CochainComplex C ℤ} (φ : A ⟶ B) (j : ℤ)
    (h : Epi (HomologicalComplex.homologyMap φ j)) :
    Epi ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map φ)) :=
  (NatIso.epi_map_iff (DerivedCategory.homologyFunctorFactors C j) φ).mpr h

end CategoryTheory

namespace CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-! ### The stupid truncation in degrees `≤ b` -/

/-- The stupid truncation in degrees `≤ b` vanishes in every degree above `b`. -/
public theorem isZero_stupidTruncLE_X (L : CochainComplex C ℤ) {b i : ℤ} (hi : b < i) :
    IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntLE b)).X i) :=
  L.isZero_stupidTrunc_X _ i ((ComplexShape.notMem_range_embeddingUpIntLE_iff _ i).2 (by omega))

/-- A complex bounded above by `b` receives a map from its degree-`b` term placed in degree `b`
which is an isomorphism in degree `b`. -/
public theorem exists_hom_from_single_isIso_f (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] :
    ∃ ι : (HomologicalComplex.single C (ComplexShape.up ℤ) b).obj (L.X b) ⟶ L,
      IsIso (ι.f b) := by
  refine ⟨HomologicalComplex.mkHomFromSingle (𝟙 (L.X b)) (fun k hk => ?_), ?_⟩
  · simp only [ComplexShape.up_Rel] at hk
    exact (L.isZero_of_isStrictlyLE b k (by omega)).eq_of_tgt _ _
  · rw [HomologicalComplex.mkHomFromSingle_f, Category.comp_id]
    infer_instance

/-- A complex bounded above by `b` maps to its stupid truncation in degrees `≤ b - 1` by a map
which is an isomorphism in every degree other than `b`. -/
public theorem exists_hom_to_stupidTruncLE_isIso_f (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] :
    ∃ π : L ⟶ L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1)),
      ∀ i : ℤ, i ≠ b → IsIso (π.f i) := by
  have hlift : (ComplexShape.embeddingUpIntLE (b - 1)).HasLift
      (𝟙 (L.restriction (ComplexShape.embeddingUpIntLE (b - 1)))) :=
    fun _ hj _ _ => (hj.false_of_isTruncLE).elim
  refine ⟨(ComplexShape.embeddingUpIntLE (b - 1)).liftExtend _ hlift, fun i hi => ?_⟩
  by_cases hib : i ≤ b - 1
  · refine ((ComplexShape.embeddingUpIntLE (b - 1)).isIso_liftExtend_f_iff _ hlift
      (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i hib)).2 ?_
    rw [HomologicalComplex.id_f]
    infer_instance
  · exact (L.isZero_of_isStrictlyLE b i (by omega)).isIso
      (isZero_stupidTruncLE_X L (show b - 1 < i by omega)) _

variable [HasDerivedCategory.{d} C]

/-- **The distinguished triangle splitting the top term off a complex bounded above.** For a
complex `L` with `L^i = 0` for `i > b`, the degree-`b` term placed in degree `b`, the complex
itself and its stupid truncation in degrees `≤ b - 1` form a distinguished triangle in `D(C)`.

The underlying short exact sequence of complexes is degreewise split: in degree `b` the first
map is an isomorphism and the third term is zero, and in every other degree the first term is
zero and the second map is an isomorphism. -/
public theorem exists_distTriang_single_stupidTruncLE (L : CochainComplex C ℤ) (b : ℤ)
    [L.IsStrictlyLE b] :
    ∃ (f : (DerivedCategory.singleFunctor C b).obj (L.X b) ⟶ DerivedCategory.Q.obj L)
      (g : DerivedCategory.Q.obj L ⟶
        DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))))
      (h : DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))) ⟶
        ((DerivedCategory.singleFunctor C b).obj (L.X b))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory C) := by
  obtain ⟨ι, hιb⟩ := exists_hom_from_single_isIso_f L b
  obtain ⟨π, hπ⟩ := exists_hom_to_stupidTruncLE_isIso_f L b
  have hMb : IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))).X b) :=
    isZero_stupidTruncLE_X L (by omega)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi
      exact hMb.eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i
        hi).eq_of_src _ _
  have hSE : (ShortComplex.mk ι π hcomp).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => by
      by_cases hi : i = b
      · subst hi
        exact (ShortComplex.Splitting.ofIsIsoOfIsZero _ hιb hMb).shortExact
      · exact (ShortComplex.Splitting.ofIsZeroOfIsIso _
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi)
          (hπ i hi)).shortExact
  exact ⟨_, _, _, Pretriangulated.mem_distTriang_mk_of_iso_obj₁ _
    (DerivedCategory.triangleOfSES_distinguished hSE)
    ((DerivedCategory.singleFunctorIsoCompQ C b).app (L.X b))⟩

end CochainComplex

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- An `𝒪_X`-module which is `(m - j)`-pseudo-coherent in degree zero is `m`-pseudo-coherent
when placed in degree `j`: placing it in degree `j` is shifting by `-j`, and shifting by `-j`
shifts the pseudo-coherence bound by `j`.

The two spellings are what separates the statement of Stacks 09V7, whose hypothesis is that the
term `𝒦^i` is `(m - i)`-pseudo-coherent, from the form the induction below uses, where the term
sits in its own degree. -/
public theorem isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero (M : OXMod.{u, u} X)
    (m j : ℤ)
    (h : IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M) (m - j)) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) j).obj M) m := by
  have hshift : IsPseudoCoherentFrom
      (((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M)⟦(-j : ℤ)⟧) m := by
    simpa using h.shift (-j)
  exact hshift.ofIso
    (((DerivedCategory.singleFunctors (OXMod.{u, u} X)).shiftIso (-j) j 0 (by omega)).app M)

/-- A zero `𝒪_X`-module placed in any degree is `m`-pseudo-coherent. -/
private theorem isPseudoCoherentFrom_single_of_isZero (M : OXMod.{u, u} X) (i m : ℤ)
    (hM : IsZero M) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).obj M) m :=
  IsPseudoCoherent.isPseudoCoherentFrom
    (isPseudoCoherent_of_isZero (Functor.map_isZero _ hM)) m

/-- **A bounded complex of `m`-pseudo-coherent `𝒪_X`-modules is `m`-pseudo-coherent**: the
bounded case of Stacks 09V7.

The hypothesis is that the term in degree `i`, placed in degree `i` in the derived category, is
`m`-pseudo-coherent — equivalently, that `𝒦^i` is `(m - i)`-pseudo-coherent in degree zero,
which is how the source phrases it.

Induction on the number of degrees between the two bounds. The upper bound descends one step at
a time along the distinguished triangle
`CochainComplex.exists_distTriang_single_stupidTruncLE`, whose outer terms are the top term in
its degree and the stupid truncation one degree lower, and Stacks 08CD part (2) gives the
complex from them. When the two bounds coincide the complex is isomorphic to its only term
placed in that degree. -/
public theorem isPseudoCoherentFrom_Q_of_bounded (m : ℤ) (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (hbdd : ∃ a b : ℤ, (∀ p : ℤ, p < a → IsZero (K.X p)) ∧ ∀ p : ℤ, b < p → IsZero (K.X p))
    (hK : ∀ i : ℤ, IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).obj (K.X i)) m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  have main : ∀ (n : ℕ) (a b : ℤ) (_ : a + n = b) (L : CochainComplex (OXMod.{u, u} X) ℤ)
      (_ : L.IsStrictlyGE a) (_ : L.IsStrictlyLE b)
      (_ : ∀ i : ℤ, IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).obj (L.X i)) m),
      IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m := by
    intro n
    induction n with
    | zero =>
        intro a b hab L hge hle hL
        have hb : b = a := by omega
        subst hb
        let _ : L.IsStrictlyGE b := hge
        let _ : L.IsStrictlyLE b := hle
        obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single L b
        exact (hL b).ofIso ((DerivedCategory.singleFunctor (OXMod.{u, u} X) b).mapIso
            ((HomologicalComplex.eval _ (ComplexShape.up ℤ) b).mapIso e ≪≫
              HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b M) ≪≫
          (DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} X) b).app M ≪≫
          DerivedCategory.Q.mapIso e.symm)
    | succ n ih =>
        intro a b hab L hge hle hL
        let _ : L.IsStrictlyLE b := hle
        obtain ⟨f, g, h, hT⟩ := CochainComplex.exists_distTriang_single_stupidTruncLE L b
        refine isPseudoCoherentFrom_obj₂_of_distinguished m (Triangle.mk f g h) hT (hL b) ?_
        refine ih a (b - 1) (by omega) _ ?_ inferInstance ?_
        · rw [CochainComplex.isStrictlyGE_iff] at hge ⊢
          intro i hi
          exact IsZero.of_iso (hge i hi)
            (L.stupidTruncXIso _ (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i (by omega)))
        · intro i
          by_cases hi : i ≤ b - 1
          · exact (hL i).ofIso ((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).mapIso
              (L.stupidTruncXIso _
                (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i hi)).symm)
          · exact isPseudoCoherentFrom_single_of_isZero _ i m
              (CochainComplex.isZero_stupidTruncLE_X L (show b - 1 < i by omega))
  obtain ⟨a, b, ha, hb⟩ := hbdd
  exact main (max a b - a).toNat a (max a b) (by omega) K
    ((CochainComplex.isStrictlyGE_iff K a).mpr ha)
    ((CochainComplex.isStrictlyLE_iff K (max a b)).mpr fun p hp => hb p (by omega)) hK

/-- **A complex of `m`-pseudo-coherent `𝒪_X`-modules which is bounded above is
`m`-pseudo-coherent**: Stacks 09V7 for a globally bounded above complex.

The inclusion of the stupid truncation in degrees `≥ m` is an isomorphism on cohomology in every
degree above `m` and an epimorphism in degree `m`, so it is an `m`-pseudo-coherent approximation
in the sense of `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_approximation`; its
source is bounded, with the same terms in degrees `≥ m` and zero below, so
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_bounded` applies to it. -/
public theorem isPseudoCoherentFrom_Q_of_boundedAbove (m : ℤ)
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (b : ℤ) (hb : ∀ p : ℤ, b < p → IsZero (K.X p))
    (hK : ∀ i : ℤ, IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).obj (K.X i)) m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  have hzero : ∀ i : ℤ, i < m →
      IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE m)).X i) := fun i hi =>
    CochainComplex.isZero_stupidTruncGE_X K m i hi
  have hiso : ∀ i : ℤ, m ≤ i →
      ((K.stupidTrunc (ComplexShape.embeddingUpIntGE m)).X i ≅ K.X i) := fun i hi =>
    K.stupidTruncXIso _ (show (ComplexShape.embeddingUpIntGE m).f (i - m).toNat = i by
      rw [ComplexShape.embeddingUpIntGE_f]; omega)
  refine isPseudoCoherentFrom_of_approximation m
    (isPseudoCoherentFrom_Q_of_bounded m _ ⟨m, max m b, hzero, fun p hp => ?_⟩
      fun i => ?_)
    (DerivedCategory.Q.map (CochainComplex.stupidTruncGEIncl K m)) (fun j hj => ?_) ?_
  · by_cases hpm : m ≤ p
    · exact IsZero.of_iso (hb p (by omega)) (hiso p hpm)
    · exact hzero p (by omega)
  · by_cases him : m ≤ i
    · exact (hK i).ofIso ((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).mapIso
        (hiso i him).symm)
    · exact isPseudoCoherentFrom_single_of_isZero _ i m (hzero i (by omega))
  · exact isIso_homologyFunctor_map_Q_map _ j
      (CochainComplex.isIso_homologyMap_stupidTruncGEIncl K m j hj)
  · exact epi_homologyFunctor_map_Q_map _ m (CochainComplex.epi_homologyMap_stupidTruncGEIncl K m)

/-! ### The locally bounded above case -/

variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **Restricting an `𝒪_X`-module placed in degree `j` to an open subspace is restricting the
module and then placing it in degree `j`.**

Both sides are computed by a complex: the left one by restricting the complex `M[-j]`
degreewise (`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso`), the right one by
`M|_U[-j]`, and `HomologicalComplex.singleMapHomologicalComplex` identifies the two. -/
public def derivedRestrictSingleFunctorIso (U : Opens X.carrier) (j : ℤ) (M : OXMod.{u, u} X) :
    (derivedRestrictModules X U).obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) j).obj M) ≅
      (DerivedCategory.singleFunctor
          (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) j).obj ((restrictModules X U).obj M) :=
  (derivedRestrictModules X U).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} X) j).app M) ≪≫
    derivedRestrictModulesObjQIso X U
      ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) j).obj M) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (restrictModules X U) (ComplexShape.up ℤ) j).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) j).app _).symm

/-- **Stacks 09V7 in the derived category.** A complex of `m`-pseudo-coherent `𝒪_X`-modules which
is bounded above on a neighbourhood of every point represents an `m`-pseudo-coherent object of
`D(𝒪_X)`.

`m`-pseudo-coherence is local on `X`
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`), and on an open subspace
where the complex is bounded above the restricted complex has the restricted terms, which are
still `m`-pseudo-coherent in their degrees by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` and
`AlgebraicGeometry.RingedSpace.derivedRestrictSingleFunctorIso`. -/
public theorem isPseudoCoherentFrom_Q_of_locally_boundedAbove (m : ℤ)
    (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (hbdd : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ b : ℤ, ∀ p : ℤ, b < p →
      IsZero ((restrictComplex K U).X p))
    (hK : ∀ i : ℤ, IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).obj (K.X i)) m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  refine isPseudoCoherentFrom_of_local_restrict _ m fun x => ?_
  obtain ⟨U, hxU, b, hb⟩ := hbdd x
  refine ⟨U, hxU, (isPseudoCoherentFrom_Q_of_boundedAbove m (restrictComplex K U) b hb
    fun i => ?_).ofIso (derivedRestrictModulesObjQIso X U K).symm⟩
  exact (isPseudoCoherentFrom_derivedRestrictModules _ m (hK i) U).ofIso
    (derivedRestrictSingleFunctorIso U i (K.X i))

/-- **Stacks 09V7.** Let `X` be a ringed space, let `m` be an integer and let `𝒦` be a complex of
`𝒪_X`-modules which is bounded above on a neighbourhood of every point and whose term `𝒦^i` is
`(m - i)`-pseudo-coherent for every `i`. Then `𝒦` is an `m`-pseudo-coherent complex.

The hypothesis on the terms is turned into the form the induction uses by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero`, and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_locally_boundedAbove` is read back on
the complex through Stacks 08CC part (2). -/
@[stacks 09V7, sga "5 VIII 5.1" "'if' direction"]
public theorem isPseudoCoherentComplexFrom_of_locally_boundedAbove (m : ℤ)
    (K : CochainComplex (OXMod.{u, u} X) ℤ)
    (hbdd : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ b : ℤ, ∀ p : ℤ, b < p →
      IsZero ((restrictComplex K U).X p))
    (hK : ∀ i : ℤ, IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj (K.X i)) (m - i)) :
    IsPseudoCoherentComplexFrom K m :=
  isPseudoCoherentComplexFrom_of_iso _ m
    (isPseudoCoherentFrom_Q_of_locally_boundedAbove m K hbdd fun i =>
      isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero (K.X i) m i (hK i)) K (Iso.refl _)

end AlgebraicGeometry.RingedSpace

end
