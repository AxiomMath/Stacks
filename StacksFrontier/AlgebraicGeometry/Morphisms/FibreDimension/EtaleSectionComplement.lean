module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleSectionDecomposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Splitting off a section of an étale morphism, and the fibre degrees of what is left

Let `q : T ⟶ S` be an étale separated morphism of schemes admitting a section `σ : S ⟶ T`. Such a
section is an open immersion, because the diagonal of an unramified morphism is one, and a closed
immersion, because closed immersions cancel on the right against separated morphisms. Its image is
therefore open and closed, and `T` is the disjoint union of that image with the complementary open
subscheme. This file introduces that complement, `AlgebraicGeometry.sectionComplement`, and proves
the facts about it which an induction on a bound for the degrees of the fibres of an étale
morphism consumes: it is a closed subscheme, it is affine when `T` is, it is complementary to the
image of the section, and — the point — passing from `q` to its restriction to the complement
*drops a bound on the fibre degrees by one*.

This is the second step of the inductive argument in the second proof of Stacks Project, Tag 04DZ:
"the disjoint union decomposition arises because by construction the étale morphism of affine
schemes `U ×_Y W ⟶ W_X` has a section. OK, and now we see that the morphism `R ⟶ X ×_Y W` is an
étale morphism of affine schemes whose fibres have degree universally bounded by `n - 1`." Nothing
affine is used for the degree drop, so it is proved for an arbitrary étale separated morphism.

The diagonal of an étale separated morphism is the section of the second projection
`T ×_S T ⟶ T` which
`StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalComplement` splits off, so
the results there are the case `q := pullback.snd t t`, `σ := pullback.diagonal t` of the results
here, phrased in terms of `AlgebraicGeometry.diagonalComplement`, which names the complementary
open subscheme of the pullback rather than of an abstract total space.

## Main definitions

* `AlgebraicGeometry.sectionComplement`: for an étale separated `q : T ⟶ S` with a section `σ`,
  the open subscheme of `T` complementary to the image of `σ`. This is the `R` of the proof of
  Stacks Project, Tag 04DZ.

## Main results

* `AlgebraicGeometry.isClopen_range_section`: the image of a section of an étale separated
  morphism is open and closed.
* `AlgebraicGeometry.isClosed_sectionComplement`: the complement is a closed subset, so that
  `AlgebraicGeometry.nonempty_isColimit_binaryCofanMk_sectionComplement` exhibits `T` as the
  disjoint union of the image of the section and that complement.
* `AlgebraicGeometry.isAffine_sectionComplement`: the complement of a section inside an affine
  scheme is affine, being a closed subscheme of it.
* `AlgebraicGeometry.boundsFiberDegrees_sectionComplement`: **the degree drop.** If `n + 1` bounds
  the degrees of the fibres of an étale separated `q : T ⟶ S` admitting a section, then `n` bounds
  the degrees of the fibres of the restriction of `q` to the complement of that section.

## Implementation notes

The degree drop is stated with the bound written `n + 1` rather than as a subtraction, so that no
truncated subtraction appears and the hypothesis `n ≥ 1` of the source argument is carried by the
shape of the statement. This is the convention of
`AlgebraicGeometry.boundsFiberDegrees_diagonalComplement`.

The bookkeeping is done on the number of points of the base changes to the spectra of fields,
which is what Stacks Project, Tag 03WU identifies a fibre-degree bound with for an étale morphism,
rather than on the ranks themselves. No quasi-compactness hypothesis is needed anywhere, so the
proof does not go through `AlgebraicGeometry.boundsFiberDegrees_iff_finrank_fiber_le`.

A section of a separated morphism is a closed immersion; the development's public form of that
statement, `Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section`, lives in
the relative-`Proj` tree and is not reachable from here without importing it, so the two lines of
Mathlib's `AlgebraicGeometry.IsClosedImmersion.of_comp` are used directly instead.

### The source's descent step does not apply as written

The third step of Tag 04DZ's second proof takes the
étale `W ⟶ Y` supplied by property (C), a descent datum on `W`, and concludes "by Descent, Lemma
0245 we see that the comparison is effective (recall that all schemes above are affine)". But
`{W ⟶ Y}` is **not** an fpqc covering of `Y`. Property (C) gives `W ⟶ Y` étale with
`X ×_Y W ⟶ U` surjective; since the comparison composes with the projection, the image of
`X ×_Y W ⟶ X` is exactly the image of `U`, so the image of `W` in `Y` is the open set cut out by
it, which is all of `Y` only when the étale morphism `U ⟶ X` is surjective, and it is not.
Enlarging `W` does not repair this: any further étale `Z ⟶ Y` joined to the family needs a map
`X ×_Y Z ⟶ U` over `X`, which forces the image of `Z` back inside that same open set, and taking
`Z := Y` would need a section of `U ⟶ X`.

The repair, which
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase` carries out, is
to descend over the open subscheme `Y₀ ⊆ Y` cut out by the image of `W`, where `W ⟶ Y₀` is
surjective by construction as well as affine and étale, hence a one-member fpqc covering; the
étale `Y₀`-scheme obtained there is étale over `Y` through the open immersion, and the base
change of `X` to `Y₀` is where `U` lives. The reduction to `Y₀` is made before property (C) is
applied, by replacing `Y` by the open subscheme cut out by the image of `U ⟶ X`: that makes
`U ⟶ X` surjective and hence the `W ⟶ Y` which property (C) then produces surjective too. It
works only because the development's form of Tag 0245,
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom`, carries no affineness
hypothesis on the base: `Y₀` is in general merely quasi-affine, so the affine-base form
`isFamilyEffective_of_forall_isAffineHom` would not serve. The cost is a layer the source does
not have — the restriction of the whole situation to `Y₀`, and a final comparison that is itself
descended along the fpqc cover rather than read off, by Tag 040L.

## References

* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 01KT](https://stacks.math.columbia.edu/tag/01KT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {T S : Scheme.{u}} (q : T ⟶ S) (σ : S ⟶ T)

/-- A section of a separated morphism of schemes is a closed immersion: the composite `σ ≫ q` is
the identity, hence a closed immersion, and closed immersions cancel on the right against
separated morphisms. -/
@[ega "I 5.4.4" "special case",
  ega "I 5.4.6",
  ega "IV 16.2.3" "special case",
  sga "3 II 4.11.4" "more general",
  sga "3 VIB 5.1" "more general",
  sga "3 VIB 5.6.3" "(i) ⇒ (ii)"]
theorem isClosedImmersion_section [IsSeparated q] (hσ : σ ≫ q = 𝟙 S) : IsClosedImmersion σ :=
  have : IsClosedImmersion (σ ≫ q) := by rw [hσ]; infer_instance
  IsClosedImmersion.of_comp σ q

/-- The open subscheme of `T` complementary to the image of a section `σ` of a separated morphism
`q : T ⟶ S`. Its underlying set is open because a section of a separated morphism is a closed
immersion.

This is the `R` of the second proof of Stacks Project, Tag 04DZ, where `q` is in addition étale,
so that the image of the section is open as well (`AlgebraicGeometry.isClopen_range_section`) and
this open subscheme is also a closed subscheme. -/
noncomputable def sectionComplement [IsSeparated q] (hσ : σ ≫ q = 𝟙 S) : T.Opens :=
  ⟨(Set.range σ.base)ᶜ,
    isOpen_compl_iff.mpr (isClosedImmersion_section q σ hσ).isClosedEmbedding.isClosed_range⟩

/-- The underlying set of `AlgebraicGeometry.sectionComplement` is the complement of the image of
the section. -/
theorem coe_sectionComplement [IsSeparated q] (hσ : σ ≫ q = 𝟙 S) :
    ((sectionComplement q σ hσ : T.Opens) : Set T) = (Set.range σ.base)ᶜ :=
  rfl

/-- The complement of the image of a section of an étale separated morphism is a closed subset of
the total space, that image being open by part (1) of Stacks Project, Tag 02GE. -/
theorem isClosed_sectionComplement [Etale q] [IsSeparated q] (hσ : σ ≫ q = 𝟙 S) :
    IsClosed ((sectionComplement q σ hσ : T.Opens) : Set T) :=
  (isClopen_range_section q σ hσ).2.isClosed_compl

/-- **`T` is the disjoint union of the image of a section and its complement.** The two open
subschemes are complementary by construction, and an étale separated morphism makes the image of
the section open, so both inclusions are open immersions. -/
theorem nonempty_isColimit_binaryCofanMk_sectionComplement [Etale q] [IsSeparated q]
    (hσ : σ ≫ q = 𝟙 S) :
    Nonempty (IsColimit (BinaryCofan.mk σ (sectionComplement q σ hσ).ι)) := by
  have : IsOpenImmersion σ := Unramified.section_isOpenImmersion q σ hσ
  refine nonempty_isColimit_binaryCofanMk_of_isCompl σ (sectionComplement q σ hσ).ι ?_
  rw [Scheme.Opens.opensRange_ι]
  refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩ <;>
    exact TopologicalSpace.Opens.ext (by simp [sectionComplement, Scheme.Hom.opensRange])

/-- **The complement of a section inside an affine scheme is affine.** The complement is a closed
subset of the total space, by `AlgebraicGeometry.isClosed_sectionComplement`, so the inclusion of
the corresponding open subscheme is a closed immersion, hence an affine morphism, and a scheme
admitting an affine morphism to an affine scheme is affine. -/
theorem isAffine_sectionComplement [Etale q] [IsSeparated q] [IsAffine T] (hσ : σ ≫ q = 𝟙 S) :
    IsAffine (sectionComplement q σ hσ).toScheme :=
  have : IsClosedImmersion (sectionComplement q σ hσ).ι :=
    IsClosedImmersion.of_isPreimmersion _
      (by simpa using isClosed_sectionComplement q σ hσ)
  isAffine_of_isAffineHom (sectionComplement q σ hσ).ι

/-- If `s` is a nonempty subset of a type with at most `n + 1` elements, then its complement has
at most `n` elements. -/
private theorem _root_.Cardinal.mk_compl_le_of_nonempty {X : Type*} {s : Set X} (hs : s.Nonempty)
    {n : ℕ} (hX : Cardinal.mk X ≤ ((n + 1 : ℕ) : Cardinal)) : Cardinal.mk ↥sᶜ ≤ n := by
  have hkey : (1 : Cardinal) + Cardinal.mk ↥sᶜ ≤ ((n + 1 : ℕ) : Cardinal) :=
    (add_le_add (Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr hs.to_subtype))
      le_rfl).trans ((Cardinal.mk_sum_compl s).trans_le hX)
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp
    ((le_trans (self_le_add_left _ 1) hkey).trans_lt (Cardinal.lt_aleph0.2 ⟨n + 1, rfl⟩))
  rw [hm] at hkey ⊢
  have : (1 : ℕ) + m ≤ n + 1 := by exact_mod_cast hkey
  exact_mod_cast (show m ≤ n by omega)

/-- **The degree drop of the second proof of Stacks Project, Tag 04DZ.** Let `q : T ⟶ S` be an
étale separated morphism of schemes whose fibre degrees are bounded by `n + 1`, and let `σ` be a
section of `q`. Then the fibre degrees of the restriction of `q` to the complement of the image of
`σ` are bounded by `n`.

For an étale morphism Stacks Project, Tag 03WU turns a fibre-degree bound into a bound on the
number of points of every base change to the spectrum of a field, and over such a base change the
source splits, by `AlgebraicGeometry.isClopen_range_section`, into the part over the image of the
section and the part over its complement. The first of these is nonempty, because the section
induces a point of the base change over every point of the spectrum; so the second has at most `n`
points, and Stacks Project, Tag 03WU converts that back into a bound on fibre degrees. -/
theorem boundsFiberDegrees_sectionComplement [Etale q] [IsSeparated q] (hσ : σ ≫ q = 𝟙 S) (n : ℕ)
    (h : BoundsFiberDegrees q ((n + 1 : ℕ) : ℤ)) :
    BoundsFiberDegrees ((sectionComplement q σ hσ).ι ≫ q) ((n : ℕ) : ℤ) := by
  have hcard := ((etale_boundsFiberDegrees_tfae q (n + 1)).out 1 2).mp h
  refine ((etale_boundsFiberDegrees_tfae ((sectionComplement q σ hσ).ι ≫ q) n).out 2 1).mp ?_
  intro k _ g
  set h₁ : pullback q g ⟶ T := pullback.fst q g
  set R : Set T := Set.range σ.base
  -- the base change of `q` along `g` has at most `n + 1` points
  have hAle : Cardinal.mk ↥(pullback q g) ≤ ((n + 1 : ℕ) : Cardinal) :=
    (Cardinal.mk_congr (pullbackSymmetry q g).hom.homeomorph.toEquiv).trans_le (hcard k g)
  -- the goal counts the points of that base change lying off the section
  have hinj : Function.Injective (pullback.snd (sectionComplement q σ hσ).ι h₁).base :=
    (inferInstance :
      IsOpenImmersion (pullback.snd (sectionComplement q σ hσ).ι h₁)).base_open.injective
  have hgoal : Cardinal.mk ↥(pullback g ((sectionComplement q σ hσ).ι ≫ q))
      = Cardinal.mk ↥((h₁.base ⁻¹' R)ᶜ) := by
    have e1 : pullback g ((sectionComplement q σ hσ).ι ≫ q)
        ≅ pullback ((sectionComplement q σ hσ).ι ≫ q) g := pullbackSymmetry _ _
    have e2 : pullback ((sectionComplement q σ hσ).ι ≫ q) g
        ≅ pullback (sectionComplement q σ hσ).ι h₁ :=
      (pullbackRightPullbackFstIso q g (sectionComplement q σ hσ).ι).symm
    have e3 : Cardinal.mk ↥(pullback (sectionComplement q σ hσ).ι h₁)
        = Cardinal.mk ↥(Set.range (pullback.snd (sectionComplement q σ hσ).ι h₁).base) :=
      (Cardinal.mk_range_eq _ hinj).symm
    have e4 : Set.range (pullback.snd (sectionComplement q σ hσ).ι h₁).base
        = (h₁.base ⁻¹' R)ᶜ := by
      rw [IsOpenImmersion.range_pullbackSnd]
      simp only [sectionComplement, Scheme.Opens.opensRange_ι]
      rw [← Set.preimage_compl]
      rfl
    rw [Cardinal.mk_congr e1.hom.homeomorph.toEquiv,
      Cardinal.mk_congr e2.hom.homeomorph.toEquiv, e3, e4]
  rw [hgoal]
  -- the part over the image of the section is nonempty, `σ` being a section
  have hne : (h₁.base ⁻¹' R).Nonempty := by
    obtain ⟨x⟩ : Nonempty (Spec (.of k) : Scheme.{u}) := inferInstance
    let a : (Spec (.of k) : Scheme.{u}) ⟶ pullback q g :=
      pullback.lift (g ≫ σ) (𝟙 _) (by simp [hσ])
    have hx : h₁.base (a.base x) = σ.base (g.base x) := by
      simpa using congrArg (fun m : (Spec (.of k) : Scheme.{u}) ⟶ T => m.base x)
        (pullback.lift_fst _ _ _ : a ≫ h₁ = g ≫ σ)
    exact ⟨a.base x, g.base x, hx.symm⟩
  exact_mod_cast Cardinal.mk_compl_le_of_nonempty hne hAle

end AlgebraicGeometry

end
