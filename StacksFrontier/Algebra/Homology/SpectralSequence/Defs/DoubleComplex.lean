module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Convergence criteria for the spectral sequence of a filtered complex

Let `𝒜` be an abelian category and let `(K^•, F)` be a filtered complex of `𝒜`, with spectral
sequence `(E_r, d_r)_{r ≥ 0}` ([Stacks, Tag 012M]) and induced filtration
`F^pH^n(K^•) = Im(H^n(F^pK^•) → H^n(K^•))` ([Stacks, Tag 012P]). Following [Stacks, Tag 012U],
the spectral sequence

* *weakly converges* to `H^*(K^•)` if `gr^pH^n(K^•) = E_∞^{p, n - p}` via [Stacks, Tag 012Q] for
  all `p` and `n`, that is, if the stable cycles and boundaries exist and the two inclusions
  ```
 Ker(d) ∩ F^pK^n + F^{p + 1}K^n ⊆ Z_∞^{p, n - p},  B_∞^{p, n - p} ⊆ Im(d) ∩ F^pK^n + F^{p + 1}K^n
  ```
  are equalities ([Stacks, Tag 012V]);
* *abuts* to `H^*(K^•)` if moreover `⋂_p F^pH^n(K^•) = 0` and `⋃_p F^pH^n(K^•) = H^n(K^•)` for
  every `n`;
* *converges* to `H^*(K^•)` if it is regular, abuts to `H^*(K^•)`, and
  `H^n(K^•) = lim_p H^n(K^•)/F^pH^n(K^•)` for every `n`.

## Main definitions

* `CategoryTheory.Filtration.IsComplete`: a filtration `F` of `X` is complete if `X` is the limit
  of the quotients `X/F^i`.
* `CochainComplex.Filtered.WeaklyConvergesToHomology`,
  `CochainComplex.Filtered.AbutsToHomology`, `CochainComplex.Filtered.ConvergesToHomology`: the
  three convergence notions for the spectral sequence of a filtered complex.

## Implementation notes

*The notions are stated on the filtered complex.* The spectral sequence of a filtered complex is
determined by it, and every notion of [Stacks, Tag 012U] is a condition on the subobjects
```
Z_r^{p, q} = F^pK^n ∩ d^{-1}(F^{p + r}K^{n + 1}),    B_r^{p, q} = F^pK^n ∩ d(F^{p - r}K^{n - 1})
```
of `K^n`, `n = p + q`, taken modulo `F^{p + 1}K^n`, and on the induced filtration of cohomology.
The source's `Z_r^{p, q}` and `B_r^{p, q}` are subobjects of `gr^pK^n = K^n/F^{p + 1}K^n`; they are
presented here by their preimages `Z_r^{p, q} + F^{p + 1}K^n` and `B_r^{p, q} + F^{p + 1}K^n` in
`K^n`, and the index `r` of `B_r` is shifted by one, which does not change their union. Both
families are indexed by `r : ℕ`, which is cofinal in the source's indexing.

*Stable cycles and boundaries as bounds.* The existence of `Z_∞ = ⋂_r Z_r` and `B_∞ = ⋃_r B_r`
together with the equalities `Z_∞ = Ker(d) ∩ F^pK^n + F^{p + 1}K^n` and
`B_∞ = Im(d) ∩ F^pK^n + F^{p + 1}K^n` is phrased as `IsGLB` and `IsLUB` in `Subobject (K^n)`, so
no completeness of the subobject lattices is assumed. By [Stacks, Tag 012V] this is exactly the
condition that `gr^pH^n(K^•) = E_∞^{p, n - p}` via [Stacks, Tag 012Q]; it is the form in which
convergence is concluded in [Stacks, Tag 0132]
(`HomologicalComplex₂.isBounded_and_converges_totalFiltration₁`).

*Regularity.* The source defines regularity ([Stacks, Tag 0BDU]) by the vanishing of the
differentials `d_r^{p, q}` for `r ≫ 0`. For the spectral sequence of a filtered complex this is
equivalent ([Stacks, Tag 0BDV]) to the stabilisation of `Z_r^{p, q}` for `r ≫ 0`, which is the
form used here, as it refers to the filtered complex alone.

*Completeness.* `H^n(K^•) = lim_p H^n(K^•)/F^pH^n(K^•)` is the statement that the cone from
`H^n(K^•)` to the diagram of quotients by the steps of the induced filtration is a limit cone.

## References

* [Stacks Project, Tag 012U](https://stacks.math.columbia.edu/tag/012U)
* [Stacks Project, Tag 012Q](https://stacks.math.columbia.edu/tag/012Q)
* [Stacks Project, Tag 012V](https://stacks.math.columbia.edu/tag/012V)
* [Stacks Project, Tag 0BDU](https://stacks.math.columbia.edu/tag/0BDU)
* [Stacks Project, Tag 0BDV](https://stacks.math.columbia.edu/tag/0BDV)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Filtration

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]
  {I : Type*} [Category* I] {X : C}

/-- The diagram `i ↦ X/F^iX` of quotients of `X` by the steps of a filtration `F`. -/
@[simps]
noncomputable def quotientDiagram (F : Filtration X I) : I ⥤ C where
  obj i := cokernel (F.ι.app i)
  map {i j} f := cokernel.map (F.ι.app i) (F.ι.app j) (F.diagram.map f) (𝟙 X) (by simp)
  map_id i := by
    ext
    simp
  map_comp {i j k} f g := by
    ext
    simp

/-- The cone from `X` to the quotients `X/F^iX`, by the projections. -/
@[simps]
noncomputable def quotientCone (F : Filtration X I) : Cone F.quotientDiagram where
  pt := X
  π :=
    { app i := cokernel.π (F.ι.app i)
      naturality {i j} f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, quotientDiagram_map]
        exact (cokernel.π_desc _ _ _).symm }

/-- A filtration `F` of `X` is *complete* if `X = lim_i X/F^iX`, that is, if the cone of
projections `X ⟶ X/F^iX` is a limit cone. -/
def IsComplete (F : Filtration X I) : Prop :=
  Nonempty (IsLimit F.quotientCone)

end CategoryTheory.Filtration

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C] (K : Filtered C)

/-- The step `F^pK^n` of a filtered complex, as a subobject of `K^n`. -/
noncomputable abbrev step (p n : ℤ) : Subobject (K.X.X n) :=
  Subobject.mk ((K.filtration.ι.app (op p)).f n)

/-- **The spectral sequence of a filtered complex weakly converges to `H^*(K^•)`**
([Stacks, Tag 012U]): for all `p` and `n`, the intersection over `r` of
`Z_r^{p, n - p} + F^{p + 1}K^n = F^pK^n ∩ d^{-1}(F^{p + r}K^{n + 1}) + F^{p + 1}K^n` is
`Ker(d) ∩ F^pK^n + F^{p + 1}K^n`, and the union over `r` of
`B_r^{p, n - p} + F^{p + 1}K^n = F^pK^n ∩ d(F^{p - r}K^{n - 1}) + F^{p + 1}K^n` is
`Im(d) ∩ F^pK^n + F^{p + 1}K^n`; by [Stacks, Tag 012V] this says
`gr^pH^n(K^•) = E_∞^{p, n - p}`. -/
@[ega "0 11.1.3" "special case"]
def WeaklyConvergesToHomology : Prop :=
  ∀ p n : ℤ,
    IsGLB (Set.range fun r : ℕ =>
        K.step p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (K.step (p + r) (n + 1)) ⊔
          K.step (p + 1) n)
      (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n ⊔ K.step (p + 1) n) ∧
    IsLUB (Set.range fun r : ℕ =>
        K.step p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (K.step (p - r) (n - 1)) ⊔
          K.step (p + 1) n)
      (imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n ⊔ K.step (p + 1) n)

/-- **The spectral sequence of a filtered complex abuts to `H^*(K^•)`** ([Stacks, Tag 012U]): it
weakly converges to `H^*(K^•)`, and for every `n` the induced filtration of `H^n(K^•)` is
separated, `⋂_p F^pH^n(K^•) = 0`, and exhaustive, `⋃_p F^pH^n(K^•) = H^n(K^•)`. -/
def AbutsToHomology : Prop :=
  K.WeaklyConvergesToHomology ∧
    ∀ n : ℤ, (K.inducedFiltration n).IsSeparated ∧ (K.inducedFiltration n).IsExhaustive

/-- **The spectral sequence of a filtered complex is regular** ([Stacks, Tag 0BDU], in the form of
[Stacks, Tag 0BDV]): for all `p` and `n`, the subobjects
`Z_r^{p, n - p} + F^{p + 1}K^n = F^pK^n ∩ d^{-1}(F^{p + r}K^{n + 1}) + F^{p + 1}K^n` of `K^n`
are constant for `r ≫ 0`. -/
def HasRegularSpectralSequence : Prop :=
  ∀ p n : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
    K.step p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (K.step (p + r) (n + 1)) ⊔
        K.step (p + 1) n =
      K.step p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (K.step (p + b) (n + 1)) ⊔
        K.step (p + 1) n

/-- **The spectral sequence of a filtered complex converges to `H^*(K^•)`** ([Stacks, Tag 012U]):
it is regular, it abuts to `H^*(K^•)`, and `H^n(K^•) = lim_p H^n(K^•)/F^pH^n(K^•)` for every
`n`. -/
def ConvergesToHomology : Prop :=
  K.HasRegularSpectralSequence ∧ K.AbutsToHomology ∧ ∀ n : ℤ, (K.inducedFiltration n).IsComplete

variable {K}

/-- If the spectral sequence of `K` abuts to `H^*(K^•)`, it weakly converges to `H^*(K^•)`. -/
lemma AbutsToHomology.weaklyConvergesToHomology (h : K.AbutsToHomology) :
    K.WeaklyConvergesToHomology :=
  h.1

/-- If the spectral sequence of `K` abuts to `H^*(K^•)`, then the induced filtration of `H^n(K^•)`
is separated: `⋂_p F^pH^n(K^•) = 0`. -/
lemma AbutsToHomology.isSeparated (h : K.AbutsToHomology) (n : ℤ) :
    (K.inducedFiltration n).IsSeparated :=
  (h.2 n).1

/-- If the spectral sequence of `K` abuts to `H^*(K^•)`, then the induced filtration of `H^n(K^•)`
is exhaustive: `⋃_p F^pH^n(K^•) = H^n(K^•)`. -/
lemma AbutsToHomology.isExhaustive (h : K.AbutsToHomology) (n : ℤ) :
    (K.inducedFiltration n).IsExhaustive :=
  (h.2 n).2

/-- If the spectral sequence of `K` converges to `H^*(K^•)`, it is regular. -/
lemma ConvergesToHomology.hasRegularSpectralSequence (h : K.ConvergesToHomology) :
    K.HasRegularSpectralSequence :=
  h.1

/-- If the spectral sequence of `K` converges to `H^*(K^•)`, it abuts to `H^*(K^•)`. -/
lemma ConvergesToHomology.abutsToHomology (h : K.ConvergesToHomology) : K.AbutsToHomology :=
  h.2.1

/-- If the spectral sequence of `K` converges to `H^*(K^•)`, it weakly converges to `H^*(K^•)`. -/
lemma ConvergesToHomology.weaklyConvergesToHomology (h : K.ConvergesToHomology) :
    K.WeaklyConvergesToHomology :=
  h.abutsToHomology.weaklyConvergesToHomology

/-- If the spectral sequence of `K` converges to `H^*(K^•)`, then the induced filtration of
`H^n(K^•)` is complete: `H^n(K^•) = lim_p H^n(K^•)/F^pH^n(K^•)`. -/
lemma ConvergesToHomology.isComplete (h : K.ConvergesToHomology) (n : ℤ) :
    (K.inducedFiltration n).IsComplete :=
  h.2.2 n

end CochainComplex.Filtered
