module

public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.AffineMorphismVanishing

/-!
# Right exactness of the top higher direct image

Let `f : X ⟶ Y` be a morphism of schemes and `d : ℕ` a degree above which every higher direct
image of a quasi-coherent module vanishes:

  `R ⁱ f_* G = 0` for every `i > d` and every quasi-coherent `G`.

Then `R ᵈ f_*` is **right exact** on short exact sequences of modules whose first term is
quasi-coherent: the long exact sequence of the higher direct images reads

  `⋯ ⟶ R ᵈ f_* B ⟶ R ᵈ f_* C ⟶ R ᵈ⁺¹ f_* A = 0`,

so `R ᵈ f_* B ⟶ R ᵈ f_* C` is an epimorphism.

This is the engine of [Stacks, Tag 0EX3]: the source deduces both the tensor identity
`R ᵈ f_*(F ⊗ f^* G) ≅ R ᵈ f_* F ⊗ G` and the base-change isomorphism from right exactness of the
top direct image, by comparing the two right exact functors on a presentation of the coefficient
module. Neither of those two conclusions is proved here, so no `stacks` attribute is attached;
see the implementation notes for what each of them still owes.

## Main results

* `Stacks.TopDirectImageRightExact.epi_rightDerived_map_g`: the homological statement, for an
  arbitrary additive functor between abelian categories with enough injectives in the source and
  at Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`. The only hypothesis is the
  vanishing of `R ᵈ⁺¹ F` at the *first* term of the sequence; nothing is assumed in the other
  degrees.
* `Stacks.TopDirectImageRightExact.epi_rightDerivedPlus_map_g`: the same at the `ℤ`-indexed
  `CategoryTheory.Functor.rightDerivedPlus`, which is the indexing in which this library's
  higher-direct-image theory and the standing situation of [Stacks, Tag 0EX3] are stated.
* `Stacks.TopDirectImageRightExact.epi_pushforward_rightDerivedPlus_map_g`: **right exactness of
  the top higher direct image of a morphism of schemes**, with the vanishing hypothesis in the
  exact shape [Stacks, Tag 0EX3] states it — quantified over all degrees `i > d` and all
  quasi-coherent modules.
* `Stacks.TopDirectImageRightExact.epi_pushforward_rightDerivedPlus_map`: the same conclusion for
  a single epimorphism with quasi-coherent kernel, which is the form a consumer applies.

## Implementation notes

**Why the long exact sequence is reached through the `ℕ`-indexing.** The long exact sequence is
available as a cohomological `δ`-functor ([Stacks, Tag 010Q]) only for Mathlib's `ℕ`-indexed
right derived functors, namely
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`. Its field `exact_δ₁` is
exactness of `R ᵈ F(B) ⟶ R ᵈ F(C) ⟶ R ᵈ⁺¹ F(A)`, and that is the three-term window this file
needs: with the right-hand term a zero object the connecting morphism is zero, so
`CategoryTheory.ShortComplex.Exact.epi_f` gives the epimorphism. The transfer to the `ℤ`-indexing
is `Stacks.DerivedIndexing.rightDerivedIso`, with vanishing carried across by
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`.

**The quasi-coherence hypothesis is on the first term only.** `R ᵈ⁺¹ f_*` is evaluated at `S.X₁`
and nowhere else, so quasi-coherence of the middle and quotient terms is not needed and is not
assumed. This matters for a consumer that builds the sequence as a kernel sequence: only the
kernel has to be recognised as quasi-coherent.

**What the two open labels of Tag 0EX3 still need.** Right exactness is the engine of
the source's argument and not the statement of either label.

* The *tensor* label asserts an isomorphism
  `R ᵈ f_*(F ⊗ f^* G) ≅ R ᵈ f_* F ⊗ G` **together with** its characterization on local pure
  tensors. What this file supplies is that both sides are right exact in `G`; what is owed is the
  comparison map itself, the agreement of the two functors on free modules, and the dévissage
  from a local presentation of `G` to the general case.
* The *base change* label asserts that a canonical map built from derived base change
  ([Stacks, Tag 08HY]) and the derived-to-ordinary pullback comparison ([Stacks, Tag 06YJ]) is
  invertible. That needs the comparison of ordinary pullback of `R ᵈ f_*` with the top cohomology
  of derived pullback of derived pushforward, which is a statement about the derived category and
  is not a consequence of right exactness alone.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v v' u u'

namespace Stacks.TopDirectImageRightExact

/-! ### The homological engine -/

section Abstract

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
  [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

/-- **Right exactness of the top right derived functor, `ℕ`-indexed.** For a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `R ᵈ⁺¹ F(A) = 0`, the map `R ᵈ F(B) ⟶ R ᵈ F(C)` is an epimorphism.

This is the three-term window `R ᵈ F(B) ⟶ R ᵈ F(C) ⟶ R ᵈ⁺¹ F(A)` of the long exact sequence of
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`: the connecting morphism
lands in a zero object, hence vanishes, and exactness then forces the first map to be epi. No
hypothesis is placed on `F` beyond additivity, and none on the sequence in any other degree. -/
theorem epi_rightDerived_map_g {S : ShortComplex C} (hS : S.ShortExact) (d : ℕ)
    (h : IsZero ((F.rightDerived (d + 1)).obj S.X₁)) :
    Epi ((F.rightDerived d).map S.g) :=
  ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F).exact_δ₁ hS d).epi_f
    (h.eq_of_tgt _ _)

/-- **Right exactness of the top right derived functor, `ℤ`-indexed.** The statement of
`Stacks.TopDirectImageRightExact.epi_rightDerived_map_g` at
`CategoryTheory.Functor.rightDerivedPlus`, which is the indexing this library's
higher-direct-image theory is written in. The two indexings are compared by
`Stacks.DerivedIndexing.rightDerivedIso`. -/
theorem epi_rightDerivedPlus_map_g {S : ShortComplex C} (hS : S.ShortExact) (d : ℕ)
    (h : IsZero ((F.rightDerivedPlus ((d : ℤ) + 1)).obj S.X₁)) :
    Epi ((F.rightDerivedPlus (d : ℤ)).map S.g) :=
  (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso
      (Stacks.DerivedIndexing.rightDerivedIso F d) S.g).1
    (epi_rightDerived_map_g F hS d
      ((Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff F
        (m := (d : ℤ) + 1) (n := d + 1) (by push_cast; ring) S.X₁).1 h))

end Abstract

/-! ### The top higher direct image of a morphism of schemes -/

section Schemes

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
  (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ G : X.Modules, G.IsQuasicoherent →
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj G))

include hvan

/-- **Right exactness of the top higher direct image.** Let `f : X ⟶ Y` be a morphism of schemes
and `d : ℕ` a degree above which every higher direct image of a quasi-coherent module vanishes.
Then for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒪_X`-modules with `A` quasi-coherent,
`R ᵈ f_* B ⟶ R ᵈ f_* C` is an epimorphism.

The vanishing hypothesis is in the shape [Stacks, Tag 0EX3] states it, quantified over every
degree `i > d` and every quasi-coherent module; only the instance `i = d + 1` at `A` is used. -/
theorem epi_pushforward_rightDerivedPlus_map_g {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) :
    Epi (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map S.g) :=
  epi_rightDerivedPlus_map_g _ hS d (hvan ((d : ℤ) + 1) (by omega) S.X₁ h₁)

/-- **Right exactness of the top higher direct image, at one epimorphism.** Let `φ : B ⟶ C` be an
epimorphism of `𝒪_X`-modules presented as the quotient map of an exact sequence
`A ⟶ B ⟶ C` with `A ⟶ B` a monomorphism and `A` quasi-coherent. Then `R ᵈ f_* φ` is an
epimorphism.

This is `Stacks.TopDirectImageRightExact.epi_pushforward_rightDerivedPlus_map_g` with the short
complex unpacked, which is the form in which the deduction of [Stacks, Tag 0EX3] from right
exactness consumes it: there `φ` is a surjection onto the coefficient module from a module on
which the comparison being built is already known to be invertible, and the sub-object is
identified by hand rather than taken as `CategoryTheory.Limits.kernel`.

The short exact sequence is assembled as an explicit structure instance rather than through
`CategoryTheory.ShortComplex.ShortExact.mk'`. Both the `mk'` spelling and the
`CategoryTheory.ShortComplex.kernelSequence` spelling exhaust the default heartbeat budget here,
because each leaves the `Mono` and `Epi` arguments to instance search in `X.Modules`, where that
search does not finish; naming the two instances in the fields closes the declaration in
seconds. -/
theorem epi_pushforward_rightDerivedPlus_map_of_exact {A B C : X.Modules} (ι : A ⟶ B) (φ : B ⟶ C)
    (hzero : ι ≫ φ = 0) [Mono ι] [Epi φ] (hex : (ShortComplex.mk ι φ hzero).Exact)
    (hA : A.IsQuasicoherent) :
    Epi (((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).map φ) :=
  epi_pushforward_rightDerivedPlus_map_g f d hvan (S := ShortComplex.mk ι φ hzero)
    { exact := hex, mono_f := ‹Mono ι›, epi_g := ‹Epi φ› } hA

end Schemes

end Stacks.TopDirectImageRightExact

end
