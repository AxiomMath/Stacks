module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.StupidTruncation
public import StacksFrontier.Algebra.Homology.SpectralSequence.Renumbering
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoConvergence
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoFilteredComplex
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The Ext spectral sequences of the truncation filtrations of a complex

Let `A` be a Grothendieck abelian category and let `M`, `K` be objects of its derived category.
Any cochain complex `K^•` representing `K` can be filtered by its canonical truncations,
`F^pK^• = τ_{≤ -p}K^•`, and the Ext spectral sequence into that filtered complex has graded
pieces `gr^pK^•`, which represent `H^{-p}(K)[p]`. Its first page is therefore
`E_1^{p, q} = Ext^{2p + q}(M, H^{-p}(K))`.

Renumbering by `(i, j) ↦ (-j, i + 2j)`, which also moves the first page to the second, turns this
into a spectral sequence `(E'_r, d'_r)_{r ≥ 2}` with `(E'_2)^{i, j} = Ext^i(M, H^j(K))`; its
differential on page `r` has bidegree `(r, -r + 1)` by the definition of
`CohomologicalSpectralSequence`. Total degree is preserved by the renumbering, `(-j) + (i + 2j)
= i + j`.

Filtering `K^•` instead by its brutal truncations, `F^pK^• = σ_{≥ p}K^•`, whose graded pieces are
the terms `K^p[-p]`, gives a spectral sequence with `E_1^{p, q} = Ext^q(M, K^p)`. If `M` is
bounded above in the derived category and `K^•` is bounded below, that spectral sequence is
bounded and converges to `Ext^{p + q}(M, K^•)`: the brutal truncation `σ_{≥ p}K^•` is
`p`-coconnective, so Ext out of a bounded-above `M` into it vanishes for `p ≫ 0`, while for
`p` below the bound of `K^•` the inclusion `σ_{≥ p}K^• ⟶ K^•` is already an isomorphism.

## Main definitions

* `Stacks.Injectives.canonicalExtSpectralSequenceInto`: the Ext spectral sequence of the
  canonical truncation filtration of a representative of `K`.
* `Stacks.Injectives.extAddEquivOfShiftIso`: an identification of the second argument of an Ext
  group with a shift, moved into the degree.
* `Stacks.Injectives.canonicalExtSpectralSequenceIntoE₁`: the identification
  `E_1^{p, q} = Ext^{2p + q}(M, H^{-p}(K))`.
* `Stacks.Injectives.renumberedCanonicalExtSpectralSequenceInto`: the same spectral sequence
  renumbered to begin at page two.
* `Stacks.Injectives.renumberedCanonicalExtSpectralSequenceIntoE₂`: the identification
  `(E'_2)^{i, j} = Ext^i(M, H^j(K))`.
* `Stacks.Injectives.stupidExtSpectralSequenceInto`: the Ext spectral sequence of the brutal
  truncation filtration of a complex.
* `Stacks.Injectives.stupidExtSpectralSequenceIntoE₁`: the identification
  `E_1^{p, q} = Ext^q(M, K^p)`.

## Main results

* `Stacks.Injectives.canonicalExtSpectralSequenceInto_isBounded` and
  `Stacks.Injectives.canonicalExtSpectralSequenceInto_convergesToExt`: for `M ∈ D^-(A)` and
  `K ∈ D^+(A)` the canonical-truncation spectral sequence is bounded and converges to
  `Ext^{p + q}(M, K)`, the abutment carrying the filtration
  `Stacks.Injectives.extIntoFiltration` by the images of `Ext^n(M, τ_{≤ -p}K)`.
* `Stacks.Injectives.renumberedCanonicalExtSpectralSequenceInto_isBounded` and
  `Stacks.Injectives.renumberedCanonicalExtSpectralSequenceInto_convergesToExt`: the same two
  assertions for `(E'_r, d'_r)_{r ≥ 2}`, where the graded piece at `(i, j)` is the step of the
  filtration from `-j + 1` to `-j` in total degree `i + j`.
* `Stacks.Injectives.stupidExtSpectralSequenceInto_isBounded` and
  `Stacks.Injectives.stupidExtSpectralSequenceInto_hasPageInfinityAt`: for `M` bounded above and
  `K^•` bounded below the brutal-truncation spectral sequence is bounded and has an infinity page
  everywhere.
* `Stacks.Injectives.stupidExtSpectralSequenceInto_convergesToExt`: that spectral sequence
  converges to `Ext^{p + q}(M, K^•)` with the same filtration of the abutment.

## Implementation notes

The two hypotheses of Tag 0G1X are supplied for the canonical truncation filtration by
`Stacks.Injectives.canonical_subsingleton_ext` and
`Stacks.Injectives.canonical_bijective_extPostcomp`. The first holds because `K ∈ D^+(A)` makes
`τ_{≤ -p}K` *zero* for `p ≫ 0`, not merely coconnective; the second because the cofibre of
`τ_{≤ -p}K^• ⟶ K^•`, which is `(-p + 1)`-connective, admits no map from `M ∈ D^-(A)` in degrees
`n` and `n - 1` once `p ≪ 0`. The shift of a distinguished triangle carries the sign `(-1)^n` on
each of its maps, which is removed by `Stacks.Injectives.bijective_comp_of_units_smul`.

The spectral sequence is definitionally the construction of Tag 0G1X applied to the canonical
truncation filtration, not merely some spectral sequence with an isomorphic first page, so every
page, differential and page-turning isomorphism is specified. Likewise the renumbered one is
definitionally `CategoryTheory.SpectralSequence.truncationRenumber` of it.

The identifications are additive equivalences rather than isomorphisms of `AddCommGrpCat`, as are
those of Tag 0G1X that they are built from; this is what keeps the Grothendieck universe `w'`,
the derived-category Hom universe `w` and the morphism universe `v` of `A` independent.

The two degrees occurring in a first-page identification, `-p` and `2p + q`, are extra arguments
constrained by equations rather than written out, so that the renumbered statement is a direct
instantiation at `p = -j`, `q = i + 2j` and no arithmetic has to be transported across an
identification of page objects.

## References

* [Stacks Project, Tag 0G1Y](https://stacks.math.columbia.edu/tag/0G1Y)
* [Stacks Project, Tag 0G1X](https://stacks.math.columbia.edu/tag/0G1X)
-/

@[expose] public noncomputable section

universe w' w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.SpectralSequence Opposite

namespace Stacks.Injectives

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

/-- **Stacks 0G1Y.** The Ext spectral sequence into the canonical truncation filtration
`F^pK^• = τ_{≤ -p}K^•` of a cochain complex, a cohomological spectral sequence
`(E_r, d_r)_{r ≥ 1}`. -/
@[stacks 0G1Y "canonical_e1"]
def canonicalExtSpectralSequenceInto (M : DerivedCategory A) (K' : CochainComplex A ℤ) :
    CohomologicalSpectralSequence AddCommGrpCat.{v} 1 :=
  (extSpectralSequenceInto.{w', w} M (CochainComplex.canonicalTruncationFiltration K')).1

/-- The spectral sequence of the canonical truncation filtration is the Ext spectral sequence of
Tag 0G1X applied to that filtered complex, so every page, differential and page-turning
isomorphism is specified. -/
theorem canonicalExtSpectralSequenceInto_eq (M : DerivedCategory A)
    (K' : CochainComplex A ℤ) :
    canonicalExtSpectralSequenceInto.{w', w} M K' =
      extIntoSpectralSequence.{w', w} M (CochainComplex.canonicalTruncationFiltration K') :=
  rfl

/-- An identification of the second argument of an Ext group with a shift moves the shift into
the degree: for `e : X ≅ H⟦p⟧`, `Ext^n(M, X) = Ext^{p + n}(M, H)`. -/
def extAddEquivOfShiftIso {M X H : DerivedCategory A} (n m p : ℤ) (hm : p + n = m)
    (e : X ≅ H⟦p⟧) :
    DerivedCategory.Ext M X n ≃+ DerivedCategory.Ext M H m :=
  homCongrAddEquiv (Iso.refl M) ((shiftFunctor (DerivedCategory A) n).mapIso e ≪≫
    ((shiftFunctorAdd' (DerivedCategory A) p n m hm).app H).symm)

/-- **Stacks 0G1Y.** For a representative `K^•` of `K`, the first page of the canonical Ext
spectral sequence into `K` is `E_1^{p, q} = Ext^{2p + q}(M, H^{-p}(K))`. The degrees `n = -p`
and `m = 2p + q` are arguments constrained by equations. -/
@[stacks 0G1Y "canonical_e1", ega "0 11.4.3" "''E₂, T = Hom(M,-)"]
def canonicalExtSpectralSequenceIntoE₁ (M K : DerivedCategory A) (K' : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj K' ≅ K) (p q n m : ℤ) (hn : n = -p) (hm : m = 2 * p + q) :
    ((canonicalExtSpectralSequenceInto.{w', w} M K').page 1).X (p, q) ≃+
      DerivedCategory.Ext M ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A n).obj K)) m :=
  ((extSpectralSequenceInto.{w', w} M
      (CochainComplex.canonicalTruncationFiltration K')).2 p q).trans
    (extAddEquivOfShiftIso (p + q) m p (by omega)
      (CochainComplex.canonicalGradedPieceIso K' p n hn ≪≫
        (shiftFunctor (DerivedCategory A) p).mapIso
          ((DerivedCategory.singleFunctor A 0).mapIso
            ((DerivedCategory.homologyFunctor A n).mapIso e))))

/-- **Stacks 0G1Y.** The canonical Ext spectral sequence into `K`, renumbered by
`(i, j) ↦ (-j, i + 2j)` so that its first page becomes the second: a cohomological spectral
sequence `(E'_r, d'_r)_{r ≥ 2}` whose differential on page `r` has bidegree `(r, -r + 1)`. -/
@[stacks 0G1Y "renumbered_e2"]
def renumberedCanonicalExtSpectralSequenceInto (M : DerivedCategory A)
    (K' : CochainComplex A ℤ) :
    CohomologicalSpectralSequence AddCommGrpCat.{v} 2 :=
  truncationRenumber (canonicalExtSpectralSequenceInto.{w', w} M K')

/-- **Stacks 0G1Y.** For a representative `K^•` of `K`, the second page of the renumbered
canonical Ext spectral sequence into `K` is `(E'_2)^{i, j} = Ext^i(M, H^j(K))`. -/
@[stacks 0G1Y "renumbered_e2"]
def renumberedCanonicalExtSpectralSequenceIntoE₂ (M K : DerivedCategory A)
    (K' : CochainComplex A ℤ) (e : DerivedCategory.Q.obj K' ≅ K) (i j : ℤ) :
    ((renumberedCanonicalExtSpectralSequenceInto.{w', w} M K').page 2).X (i, j) ≃+
      DerivedCategory.Ext M ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A j).obj K)) i :=
  ((truncationRenumber_pageXIso (canonicalExtSpectralSequenceInto.{w', w} M K') i j 2 1
      (by omega) le_rfl (by omega)).addCommGroupIsoToAddEquiv).trans
    (canonicalExtSpectralSequenceIntoE₁.{w', w} M K K' e (-j) (i + 2 * j) j i
      (by omega) (by omega))

/-- **Stacks 0G1Y.** The Ext spectral sequence into the brutal truncation filtration
`F^pK^• = σ_{≥ p}K^•` of a cochain complex, a cohomological spectral sequence
`(E_r, d_r)_{r ≥ 1}`. -/
@[stacks 0G1Y "stupid_e1"]
def stupidExtSpectralSequenceInto (M : DerivedCategory A) (K' : CochainComplex A ℤ) :
    CohomologicalSpectralSequence AddCommGrpCat.{v} 1 :=
  (extSpectralSequenceInto.{w', w} M (CochainComplex.stupidTruncationFiltration K')).1

/-- The spectral sequence of the brutal truncation filtration is the Ext spectral sequence of
Tag 0G1X applied to that filtered complex, so every page, differential and page-turning
isomorphism is specified. -/
theorem stupidExtSpectralSequenceInto_eq (M : DerivedCategory A) (K' : CochainComplex A ℤ) :
    stupidExtSpectralSequenceInto.{w', w} M K' =
      extIntoSpectralSequence.{w', w} M (CochainComplex.stupidTruncationFiltration K') :=
  rfl

/-- **Stacks 0G1Y.** The first page of the Ext spectral sequence of the brutal truncation
filtration of `K^•` is `E_1^{p, q} = Ext^q(M, K^p)`. -/
@[stacks 0G1Y "stupid_e1"]
def stupidExtSpectralSequenceIntoE₁ (M : DerivedCategory A) (K' : CochainComplex A ℤ)
    (p q : ℤ) :
    ((stupidExtSpectralSequenceInto.{w', w} M K').page 1).X (p, q) ≃+
      DerivedCategory.Ext M ((DerivedCategory.singleFunctor A 0).obj (K'.X p)) q :=
  ((extSpectralSequenceInto.{w', w} M
      (CochainComplex.stupidTruncationFiltration K')).2 p q).trans
    (extAddEquivOfShiftIso (p + q) q (-p) (by omega)
      (CochainComplex.stupidGradedPieceDerivedIso K' p))

omit [IsGrothendieckAbelian.{w', v, u} A] in
/-- Postcomposition with an isomorphism is a bijection on Ext groups. -/
private theorem bijective_extPostcomp_of_isIso (M : DerivedCategory A)
    {X Y : DerivedCategory A} (f : X ⟶ Y) [IsIso f] (n : ℤ) :
    Function.Bijective (extPostcomp M n f) := by
  refine ⟨fun x y hxy => (cancel_mono ((shiftFunctor (DerivedCategory A) n).map f)).1 hxy,
    fun y => ⟨y ≫ inv ((shiftFunctor (DerivedCategory A) n).map f), ?_⟩⟩
  simp [extPostcomp]

/-- Below the bound of a complex bounded below, the inclusion of a brutal truncation is an
isomorphism. -/
private theorem isIso_ιStupidTrunc_of_le {A : Type u} [Category.{v} A] [Abelian A]
    (K' : CochainComplex A ℤ) (a p : ℤ) (hK : K'.IsStrictlyGE a) (hpa : p ≤ a) :
    IsIso (HomologicalComplex.ιStupidTrunc K' (ComplexShape.embeddingUpIntGE p)) := by
  have hdeg (i : ℤ) : IsIso ((HomologicalComplex.ιStupidTrunc K'
      (ComplexShape.embeddingUpIntGE p)).f i) := by
    by_cases hip : p ≤ i
    · rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f K' p i hip]
      infer_instance
    · exact Limits.IsZero.isIso
        (K'.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE p) i
          (by rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]; omega))
        ((CochainComplex.isStrictlyGE_iff K' a).mp hK i (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

omit [IsGrothendieckAbelian.{w', v, u} A] in
/-- For `M` bounded above, Ext out of `M` into the brutal truncations of a complex vanishes in
each degree once the truncation degree is large enough. -/
private theorem stupid_subsingleton_ext (M : DerivedCategory A) (K' : CochainComplex A ℤ)
    (hM : DerivedCategory.TStructure.t.minus M) (n : ℤ) :
    ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p → Subsingleton (DerivedCategory.Ext M (DerivedCategory.Q.obj
      ((CochainComplex.stupidTruncationFiltration K').filtration.obj (op p))) n) := by
  obtain ⟨N, hMle⟩ := hM
  refine ⟨N + n + 1, fun p hp ↦ ?_⟩
  have hGE :
      (DerivedCategory.Q.obj (K'.stupidTrunc (ComplexShape.embeddingUpIntGE p))).IsGE p := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    have := CochainComplex.isStrictlyGE_of_ge
      (K'.stupidTrunc (ComplexShape.embeddingUpIntGE p)) p p le_rfl
    infer_instance
  have hshift := DerivedCategory.TStructure.t.isGE_shift
    (DerivedCategory.Q.obj (K'.stupidTrunc (ComplexShape.embeddingUpIntGE p))) p n (p - n)
    (by omega)
  exact ⟨fun f g ↦ by
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f N (p - n) (by omega) hMle hshift,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g N (p - n) (by omega) hMle hshift]⟩

omit [IsGrothendieckAbelian.{w'} A] in
/-- For `K^•` bounded below, the maps `Ext^n(M, σ_{≥ p}K^•) ⟶ Ext^n(M, K^•)` are bijective once
the truncation degree is below the bound. -/
private theorem stupid_bijective_extPostcomp (M : DerivedCategory A)
    (K' : CochainComplex A ℤ) (hK : CochainComplex.plus A K') (n : ℤ) :
    ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ → Function.Bijective (extPostcomp M n (DerivedCategory.Q.map
      ((CochainComplex.stupidTruncationFiltration K').filtration.ι.app (op p)))) := by
  obtain ⟨a, hKGE⟩ := (CochainComplex.plus_iff A K').mp hK
  refine ⟨a, fun p hp ↦ ?_⟩
  have hι : IsIso (HomologicalComplex.ιStupidTrunc K'
    (ComplexShape.embeddingUpIntGE p)) := isIso_ιStupidTrunc_of_le K' a p hKGE hp
  have hQ : IsIso (DerivedCategory.Q.map
      ((CochainComplex.stupidTruncationFiltration K').filtration.ι.app (op p))) := by
    rw [CochainComplex.stupidTruncationFiltration_filtration_ι_app]
    exact Functor.map_isIso (F := DerivedCategory.Q)
      (f := HomologicalComplex.ιStupidTrunc K' (ComplexShape.embeddingUpIntGE p))
  exact bijective_extPostcomp_of_isIso M _ n

/-- **Stacks 0G1Y.** If `M` is bounded above in the derived category and `K^•` is bounded below,
the Ext spectral sequence of the brutal truncation filtration of `K^•` is bounded. -/
@[stacks 0G1Y "stupid_convergence"]
theorem stupidExtSpectralSequenceInto_isBounded (M : DerivedCategory A)
    (K' : CochainComplex A ℤ) (hM : DerivedCategory.TStructure.t.minus M)
    (hK : CochainComplex.plus A K') :
    IsBounded (stupidExtSpectralSequenceInto.{w', w} M K') :=
  extSpectralSequenceInto_isBounded.{w', w} M (CochainComplex.stupidTruncationFiltration K')
    (stupid_subsingleton_ext M K' hM) (stupid_bijective_extPostcomp M K' hK)

/-- **Stacks 0G1Y.** Under the same hypotheses the brutal-truncation Ext spectral sequence has an
infinity page at every bidegree. -/
@[stacks 0G1Y "stupid_convergence"]
theorem stupidExtSpectralSequenceInto_hasPageInfinityAt (M : DerivedCategory A)
    (K' : CochainComplex A ℤ) (hM : DerivedCategory.TStructure.t.minus M)
    (hK : CochainComplex.plus A K') (pq : ℤ × ℤ) :
    (stupidExtSpectralSequenceInto.{w', w} M K').HasPageInfinityAt pq :=
  extSpectralSequenceInto_hasPageInfinityAt.{w', w} M
    (CochainComplex.stupidTruncationFiltration K')
    (stupid_subsingleton_ext M K' hM)
    (stupid_bijective_extPostcomp M K' hK) pq

/-- **Stacks 0G1Y, convergence of the brutal-truncation spectral sequence.** Under the same
hypotheses it converges to `Ext^{p + q}(M, K^•)`: the decreasing filtration
`Stacks.Injectives.extIntoFiltration` of each `Ext^n(M, K^•)` is finite and the infinity page at
`(p, q)` is its `p`-th graded piece in total degree `p + q`. -/
@[stacks 0G1Y "stupid_convergence"]
theorem stupidExtSpectralSequenceInto_convergesToExt (M : DerivedCategory A)
    (K' : CochainComplex A ℤ) (hM : DerivedCategory.TStructure.t.minus M)
    (hK : CochainComplex.plus A K') :
    let E := stupidExtSpectralSequenceInto.{w', w} M K'
    let F := extIntoFiltration M (CochainComplex.stupidTruncationFiltration K')
    ∃ hF : ∀ n : ℤ, Antitone (F n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
      (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
      ∀ p q : ℤ, Nonempty
        ((E.pageInfinity (p, q) : Type v) ≃+
          ((Limits.cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega))) : AddCommGrpCat.{w}) : Type w)) :=
  extSpectralSequenceInto_convergesToExt.{w', w} M
    (CochainComplex.stupidTruncationFiltration K')
    (stupid_subsingleton_ext M K' hM)
    (stupid_bijective_extPostcomp M K' hK)

/-! ### Boundedness and convergence of the canonical-truncation spectral sequences -/

omit [IsGrothendieckAbelian.{w'} A] in
/-- An object of the derived category which is both `n`-coconnective and `(n + 1)`-connective is
zero. -/
private theorem isZero_of_isLE_of_isGE (X : DerivedCategory A) (n : ℤ)
    (hLE : X.IsLE n) (hGE : X.IsGE (n + 1)) : Limits.IsZero X := by
  have hz : Limits.IsZero ((DerivedCategory.TStructure.t.truncLE n).obj X) :=
    (DerivedCategory.TStructure.t.isGE_iff_isZero_truncLE_obj n (n + 1) rfl X).1 hGE
  exact Limits.IsZero.of_iso hz (asIso ((DerivedCategory.TStructure.t.truncLEι n).app X)).symm

omit [IsGrothendieckAbelian.{w'} A] in
/-- Ext into a zero object vanishes. -/
private theorem subsingleton_ext_of_isZero (M : DerivedCategory A) {X : DerivedCategory A}
    (hX : Limits.IsZero X) (n : ℤ) : Subsingleton (DerivedCategory.Ext M X n) :=
  ⟨fun f g => ((shiftFunctor (DerivedCategory A) n).map_isZero hX).eq_of_tgt f g⟩

omit [IsGrothendieckAbelian.{w'} A] in
/-- For a complex whose homology lives in degrees `≥ b`, the canonical truncation `τ_{≤ m}K^•` is
zero in the derived category as soon as `m < b`. -/
private theorem isZero_Q_truncLE (K' : CochainComplex A ℤ) (b m : ℤ)
    (hK : (DerivedCategory.Q.obj K').IsGE b) (hm : m + 1 ≤ b) :
    Limits.IsZero (DerivedCategory.Q.obj (K'.truncLE m)) := by
  have hK' : K'.IsGE b := (DerivedCategory.isGE_Q_obj_iff K' b).1 hK
  have hK'' : K'.IsGE (m + 1) := (CochainComplex.isGE_iff K' (m + 1)).2 (fun i hi =>
    (CochainComplex.isGE_iff K' b).1 hK' i (by omega))
  have hac : (K'.truncLE m).Acyclic :=
    (CochainComplex.acyclic_truncLE_iff K' m (m + 1) rfl).2 hK''
  refine isZero_of_isLE_of_isGE _ 0 ?_ ?_
  · exact (DerivedCategory.isLE_Q_obj_iff _ 0).2
      ((CochainComplex.isLE_iff _ 0).2 (fun i _ => hac i))
  · exact (DerivedCategory.isGE_Q_obj_iff _ 1).2
      ((CochainComplex.isGE_iff _ 1).2 (fun i _ => hac i))

omit [IsGrothendieckAbelian.{w'} A] in
/-- For `K ∈ D^+(A)`, Ext out of `M` into the canonical truncations `τ_{≤ -p}K^•` vanishes in each
degree once `p` is large enough: those truncations are then zero. -/
private theorem canonical_subsingleton_ext (M K : DerivedCategory A) (K' : CochainComplex A ℤ)
    (e : DerivedCategory.Q.obj K' ≅ K) (hK : DerivedCategory.TStructure.t.plus K) (n : ℤ) :
    ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p → Subsingleton (DerivedCategory.Ext M (DerivedCategory.Q.obj
      ((CochainComplex.canonicalTruncationFiltration K').filtration.obj (op p))) n) := by
  obtain ⟨b, hKge⟩ := hK
  have : K.IsGE b := hKge
  have hKge' : (DerivedCategory.Q.obj K').IsGE b :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm b
  exact ⟨-b + 1, fun p hp =>
    subsingleton_ext_of_isZero M (isZero_Q_truncLE K' b (-p) hKge' (by omega)) n⟩

omit [IsGrothendieckAbelian.{w'} A] in
/-- In a distinguished triangle whose third object receives no map from `M`, in its own degree and
one below, post-composition with the first map is bijective on the maps out of `M`. -/
private theorem bijective_comp_mor₁ (M : DerivedCategory A)
    (T : Pretriangulated.Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A))
    (h₃ : ∀ f : M ⟶ T.obj₃, f = 0)
    (h₃' : ∀ f : M ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0) :
    Function.Bijective (fun g : M ⟶ T.obj₁ => g ≫ T.mor₁) := by
  refine ⟨fun g₁ g₂ hg => ?_, fun f => ?_⟩
  · have hd : (g₁ - g₂) ≫ T.mor₁ = 0 := by
      rw [Preadditive.sub_comp, show g₁ ≫ T.mor₁ = g₂ ≫ T.mor₁ from hg, sub_self]
    obtain ⟨k, hk⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T.invRotate
      (Pretriangulated.inv_rot_of_distTriang _ hT) (g₁ - g₂) hd
    refine sub_eq_zero.1 ?_
    rw [hk, h₃' k]
    exact zero_comp
  · obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f (h₃ (f ≫ T.mor₂))
    exact ⟨g, hg.symm⟩

omit [IsGrothendieckAbelian.{w'} A] in
/-- Post-composition with a morphism is bijective on the maps out of `M` as soon as
post-composition with a unit multiple of it is: the shift of a distinguished triangle carries the
sign `(-1)^n` on each of its maps. -/
private theorem bijective_comp_of_units_smul (M : DerivedCategory A)
    {X Y : DerivedCategory A} (f : X ⟶ Y) (ε : ℤˣ)
    (h : Function.Bijective (fun g : M ⟶ X => g ≫ (ε • f))) :
    Function.Bijective (fun g : M ⟶ X => g ≫ f) := by
  have hε : Function.Bijective (fun k : M ⟶ Y => ε • k) :=
    ⟨fun a b hab => by simpa using congrArg (fun x : M ⟶ Y => ε⁻¹ • x) hab,
      fun k => ⟨ε⁻¹ • k, by simp [smul_smul]⟩⟩
  have hcomp : (fun g : M ⟶ X => g ≫ (ε • f)) =
      (fun k : M ⟶ Y => ε • k) ∘ (fun g : M ⟶ X => g ≫ f) := by
    funext g
    simp
  rw [hcomp] at h
  exact (Function.Bijective.of_comp_iff' hε _).1 h

omit [IsGrothendieckAbelian.{w'} A] in
/-- For `M ∈ D^-(A)`, the inclusion `τ_{≤ -p}K^• ⟶ K^•` of a canonical truncation induces a
bijection on `Ext^n(M, -)` once `p` is small enough: the cofibre of that inclusion is then too
connective to receive a map from `M`, in degree `n` and in degree `n - 1`. -/
private theorem canonical_bijective_extPostcomp (M : DerivedCategory A)
    (K' : CochainComplex A ℤ) (hM : DerivedCategory.TStructure.t.minus M) (n : ℤ) :
    ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ → Function.Bijective (extPostcomp M n (DerivedCategory.Q.map
      ((CochainComplex.canonicalTruncationFiltration K').filtration.ι.app (op p)))) := by
  obtain ⟨a, hMle⟩ := hM
  refine ⟨-a - n - 1, fun p hp => ?_⟩
  have hS : (K'.shortComplexTruncLE (-p)).ShortExact := K'.shortComplexTruncLE_shortExact (-p)
  have hSO : (K'.shortComplexTruncLE (-p)).X₃.IsSupportedOutside
      (ComplexShape.embeddingUpIntLE (-p)) :=
    HomologicalComplex.shortComplexTruncLE_X₃_isSupportedOutside K'
      (ComplexShape.embeddingUpIntLE (-p))
  have hX₃ : (K'.shortComplexTruncLE (-p)).X₃.IsGE (-p + 1) :=
    ((ComplexShape.Embedding.embeddingUpInt_areComplementary (-p) (-p + 1)
      rfl).isSupportedOutside₁_iff _).1 hSO
  have hQX₃ : (DerivedCategory.Q.obj (K'.shortComplexTruncLE (-p)).X₃).IsGE (-p + 1) :=
    (DerivedCategory.isGE_Q_obj_iff _ (-p + 1)).2 hX₃
  have hshift :
      ((DerivedCategory.Q.obj (K'.shortComplexTruncLE (-p)).X₃)⟦n⟧).IsGE (-p + 1 - n) :=
    DerivedCategory.TStructure.t.isGE_shift _ (-p + 1) n (-p + 1 - n) (by omega)
  have hshift' :
      (((DerivedCategory.Q.obj (K'.shortComplexTruncLE (-p)).X₃)⟦n⟧)⟦(-1 : ℤ)⟧).IsGE
        (-p + 2 - n) :=
    DerivedCategory.TStructure.t.isGE_shift _ (-p + 1 - n) (-1) (-p + 2 - n) (by omega)
  exact bijective_comp_of_units_smul M _ n.negOnePow (bijective_comp_mor₁ M
    ((Pretriangulated.Triangle.shiftFunctor (DerivedCategory A) n).obj
      (DerivedCategory.triangleOfSES hS))
    (Pretriangulated.Triangle.shift_distinguished _
      (DerivedCategory.triangleOfSES_distinguished hS) n)
    (fun f => DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f a (-p + 1 - n) (by omega)
      hMle hshift)
    (fun f => DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f a (-p + 2 - n) (by omega)
      hMle hshift'))

/-- **Stacks 0G1Y, boundedness of the canonical spectral sequence.** For `M ∈ D^-(A)` and
`K ∈ D^+(A)` the Ext spectral sequence of the canonical truncation filtration of a complex
representing `K` is bounded: in total degree `d` its first page
`E_1^{p, d - p} = Ext^{p + d}(M, H^{-p}(K))` vanishes unless `-a - d ≤ p ≤ -b`, where `M` lives in
degrees `≤ a` and `K` in degrees `≥ b`. -/
@[stacks 0G1Y "canonical_convergence"]
theorem canonicalExtSpectralSequenceInto_isBounded (M K : DerivedCategory A)
    (K' : CochainComplex A ℤ) (e : DerivedCategory.Q.obj K' ≅ K)
    (hM : DerivedCategory.TStructure.t.minus M)
    (hK : DerivedCategory.TStructure.t.plus K) :
    IsBounded (canonicalExtSpectralSequenceInto.{w', w} M K') := by
  obtain ⟨a, hMle⟩ := hM
  obtain ⟨b, hKge⟩ := hK
  have : K.IsGE b := hKge
  intro d
  refine (Set.finite_Icc (-a - d) (-b)).subset fun p hp => ?_
  have hzero : Subsingleton (DerivedCategory.Ext M
      ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A (-p)).obj K)) (p + d)) → False := by
    intro hsub
    have : Subsingleton
        (((canonicalExtSpectralSequenceInto.{w', w} M K').page 1).X (p, d - p) : Type v) :=
      (canonicalExtSpectralSequenceIntoE₁.{w', w} M K K' e p (d - p) (-p) (p + d) rfl
        (by omega)).toEquiv.subsingleton
    exact hp (Limits.IsZero.of_iso (AddCommGrpCat.isZero_of_subsingleton _) (Iso.refl _))
  refine ⟨?_, ?_⟩
  · by_contra hlt
    refine hzero ?_
    have hGEshift : (((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A (-p)).obj K))⟦p + d⟧).IsGE (-(p + d)) :=
      DerivedCategory.TStructure.t.isGE_shift _ 0 (p + d) (-(p + d)) (by omega)
    exact ⟨fun f g => by
      rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f a (-(p + d)) (by omega)
          hMle hGEshift,
        DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g a (-(p + d)) (by omega)
          hMle hGEshift]⟩
  · by_contra hlt
    exact hzero (subsingleton_ext_of_isZero M ((DerivedCategory.singleFunctor A 0).map_isZero
      ((DerivedCategory.isGE_iff K b).1 hKge (-p) (by omega))) (p + d))

/-- **Stacks 0G1Y, convergence of the canonical spectral sequence.** For `M ∈ D^-(A)` and
`K ∈ D^+(A)` the Ext spectral sequence of the canonical truncation filtration converges to
`Ext^{p + q}(M, K)`: the decreasing filtration `Stacks.Injectives.extIntoFiltration` of each
`Ext^n(M, K)` is finite and the infinity page at `(p, q)` is its `p`-th graded piece in total
degree `p + q`. -/
@[stacks 0G1Y "canonical_convergence"]
theorem canonicalExtSpectralSequenceInto_convergesToExt (M K : DerivedCategory A)
    (K' : CochainComplex A ℤ) (e : DerivedCategory.Q.obj K' ≅ K)
    (hM : DerivedCategory.TStructure.t.minus M)
    (hK : DerivedCategory.TStructure.t.plus K) :
    let E := canonicalExtSpectralSequenceInto.{w', w} M K'
    let F := extIntoFiltration M (CochainComplex.canonicalTruncationFiltration K')
    ∃ hF : ∀ n : ℤ, Antitone (F n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
      (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
      ∀ p q : ℤ, Nonempty
        ((E.pageInfinity (p, q) : Type v) ≃+
          ((Limits.cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega))) : AddCommGrpCat.{w}) : Type w)) :=
  extSpectralSequenceInto_convergesToExt.{w', w} M
    (CochainComplex.canonicalTruncationFiltration K')
    (canonical_subsingleton_ext M K K' e hK)
    (canonical_bijective_extPostcomp M K' hM)

/-- **Stacks 0G1Y, boundedness after renumbering.** For `M ∈ D^-(A)` and `K ∈ D^+(A)` the
renumbered canonical Ext spectral sequence `(E'_r, d'_r)_{r ≥ 2}` is bounded. -/
@[stacks 0G1Y "canonical_convergence"]
theorem renumberedCanonicalExtSpectralSequenceInto_isBounded (M K : DerivedCategory A)
    (K' : CochainComplex A ℤ) (e : DerivedCategory.Q.obj K' ≅ K)
    (hM : DerivedCategory.TStructure.t.minus M)
    (hK : DerivedCategory.TStructure.t.plus K) :
    IsBounded (renumberedCanonicalExtSpectralSequenceInto.{w', w} M K') :=
  truncationRenumber_finite_not_isZero_page_two (canonicalExtSpectralSequenceInto.{w', w} M K')
    (canonicalExtSpectralSequenceInto_isBounded.{w', w} M K K' e hM hK)

/-- **Stacks 0G1Y, convergence after renumbering.** For `M ∈ D^-(A)` and `K ∈ D^+(A)` the
renumbered canonical Ext spectral sequence converges to `Ext^{i + j}(M, K)`: the infinity page at
`(i, j)` is the graded piece of `Stacks.Injectives.extIntoFiltration` from `-j + 1` to `-j` in
total degree `i + j`. -/
@[stacks 0G1Y "canonical_convergence"]
theorem renumberedCanonicalExtSpectralSequenceInto_convergesToExt (M K : DerivedCategory A)
    (K' : CochainComplex A ℤ) (e : DerivedCategory.Q.obj K' ≅ K)
    (hM : DerivedCategory.TStructure.t.minus M)
    (hK : DerivedCategory.TStructure.t.plus K) :
    let E := renumberedCanonicalExtSpectralSequenceInto.{w', w} M K'
    let F := extIntoFiltration M (CochainComplex.canonicalTruncationFiltration K')
    ∃ hF : ∀ n : ℤ, Antitone (F n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
      (∀ i j : ℤ, E.HasPageInfinityAt (i, j)) ∧
      ∀ i j : ℤ, Nonempty
        ((E.pageInfinity (i, j) : Type v) ≃+
          ((Limits.cokernel (Subobject.ofLE (F (i + j) (-j + 1)) (F (i + j) (-j))
              (hF (i + j) (by omega))) : AddCommGrpCat.{w}) : Type w)) := by
  obtain ⟨hF, hfinite, hpages, hgraded⟩ :=
    canonicalExtSpectralSequenceInto_convergesToExt.{w', w} M K K' e hM hK
  refine ⟨hF, hfinite, fun i j => ?_, fun i j => ?_⟩
  · have := hpages (-j) (i + 2 * j)
    exact truncationRenumber_hasPageInfinityAt _ i j
  · have := hpages (-j) (i + 2 * j)
    obtain ⟨i₀⟩ := hgraded (-j) (i + 2 * j)
    rw [show -j + (i + 2 * j) = i + j by omega] at i₀
    exact ⟨((truncationRenumber_pageInfinityIso
      (canonicalExtSpectralSequenceInto.{w', w} M K') i j).addCommGroupIsoToAddEquiv).trans i₀⟩

end Stacks.Injectives

end
