module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageFppfVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSerreQuotient
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeColimits

/-!
# The quasi-coherent direct image along an affine morphism (Stacks 0GQY)

Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks (**Stacks 0CHQ**). **Stacks 0GQY**
says that the higher quasi-coherent direct images `Rⁱf_{QCoh,*}`, `i > 0`, vanish, and that
`f_{QCoh,*}` is exact and commutes with direct sums and with all colimits.

The functors are those of **Stacks 077A**,
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage`: the composites
`Q ∘ f_* ∘ i` and `Q ∘ Rⁱf_* ∘ i` of the inclusion `i : QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)`, the direct images
of modules on the fppf sites and the coherator `Q` of **Stacks 0778**.

## Main results

* `AlgebraicGeometry.Stack.preservesFiniteColimits_affineLqcohSheafFbcPushforward` and
  `AlgebraicGeometry.Stack.preservesColimitsOfSize_affineLqcohSheafFbcPushforward`: the direct
  image `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` of an affine `f` is right exact and commutes with
  all colimits.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageIsoOfIsAffineHom`:
  `f_{QCoh,*}` is the composite `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒴) → QCoh(𝒪_𝒴)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isZero_quasicoherentHigherDirectImage_of_isAffineHom`,
  `preservesFiniteLimits_and_preservesFiniteColimits_quasicoherentDirectImage_of_isAffineHom`,
  `preservesColimitsOfShape_discrete_quasicoherentDirectImage_of_isAffineHom`
  and
  `preservesColimitsOfSize_quasicoherentDirectImage_of_isAffineHom`:
  the four assertions of **Stacks 0GQY**, and
  `isZero_quasicoherentHigherDirectImage_and_exact_preservesColimits_of_isAffineHom`:
  all four together.

## Indexing and universes

Modules are on the fppf sites at the module universe `u` of the schemes, and colimits are indexed
by categories `J : Type u` with morphisms in `u`, the colimits `LQCoh^fbc(𝒪_𝒳)` has (**Stacks
0771** (5)). Direct sums are coproducts indexed by `ι : Type u`.

## References

* [Stacks Project, Tag 0GQY](https://stacks.math.columbia.edu/tag/0GQY)
* [Stacks Project, Tag 0GQI](https://stacks.math.columbia.edu/tag/0GQI)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (S : Scheme.{u})
  (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsAffineHom B S hS f)

/-- **The direct image `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` of an affine 1-morphism is right
exact**: it preserves finite colimits. -/
theorem preservesFiniteColimits_affineLqcohSheafFbcPushforward :
    PreservesFiniteColimits (affineLqcohSheafFbcPushforward B E h S hS f hf) := by
  let L := lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳
  let L' := lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴
  have : ∀ {X Y : L.FullSubcategory} (g : X ⟶ Y), PreservesLimit (parallelPair g 0) L.ι :=
    fun g => L.preservesKernels_ι g
  have : HasFiniteBiproducts L.FullSubcategory := Abelian.hasFiniteBiproducts
  have : HasFiniteProducts L.FullSubcategory := hasFiniteProducts_of_hasFiniteBiproducts _
  have : PreservesFiniteLimits L.ι := Functor.preservesFiniteLimits_of_preservesKernels L.ι
  have hshort : ∀ Sq : ShortComplex L.FullSubcategory, Sq.ShortExact →
      (Sq.map (affineLqcohSheafFbcPushforward B E h S hS f hf ⋙ L'.ι)).ShortExact :=
    fun Sq hSq => (stacks0GQI B E h S hS f hf).1 Sq (hSq.map_of_exact L.ι)
  have key := (Functor.exact_tfae (affineLqcohSheafFbcPushforward B E h S hS f hf ⋙ L'.ι)).out 1 4
  have : PreservesFiniteColimits (affineLqcohSheafFbcPushforward B E h S hS f hf ⋙ L'.ι) :=
    (key.1 hshort).2
  exact preservesFiniteColimits_of_reflects_of_preserves _ L'.ι

/-- **The direct image `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` of an affine 1-morphism commutes
with all colimits** indexed in the universe of the site. -/
theorem preservesColimitsOfSize_affineLqcohSheafFbcPushforward :
    PreservesColimitsOfSize.{u, u} (affineLqcohSheafFbcPushforward B E h S hS f hf) := by
  have := (lqcohSheafFbc_hasColimits_and_agree B E h S hS 𝒳).1
  have := preservesFiniteColimits_affineLqcohSheafFbcPushforward B E h S hS f hf
  have : ∀ ι : Type u, PreservesColimitsOfShape (Discrete ι)
      (affineLqcohSheafFbcPushforward B E h S hS f hf) :=
    (stacks0GQI B E h S hS f hf).2.1
  exact preservesColimits_of_preservesCoequalizers_and_coproducts _

namespace AlgebraicStacks

/-- **`f_{QCoh,*}` through `LQCoh^fbc` for an affine `f`**: the quasi-coherent direct image of
**Stacks 077A** is the composite `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒴) → QCoh(𝒪_𝒴)` of
the inclusion, the direct image `f_*` of **Stacks 0GQI** and the coherator `Q` of
**Stacks 0778**. -/
def quasicoherentDirectImageIsoOfIsAffineHom :
    quasicoherentDirectImage B S hS f ≅
      ObjectProperty.ιOfLE (isQuasicoherentOnSite_le_lqcohSheafFbc B S hS 𝒳 E h) ⋙
        affineLqcohSheafFbcPushforward B E h S hS f hf ⋙
          ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coherator B S hS 𝒴) :=
  Iso.refl _

include hf in
/-- **Stacks 0GQY, the vanishing**: for an affine 1-morphism `f` of algebraic stacks and `i > 0`,
the higher quasi-coherent direct image `Rⁱf_{QCoh,*}` is zero. -/
theorem isZero_quasicoherentHigherDirectImage_of_isAffineHom (i : ℕ) (hi : 0 < i)
    (F : quasicoherentModules B S hS 𝒳) :
    IsZero ((quasicoherentHigherDirectImage B S hS f i).obj F) := by
  have : (coherator B S hS 𝒴).IsRightAdjoint := (coheratorAdjunction B S hS 𝒴).isRightAdjoint
  exact (coherator B S hS 𝒴).map_isZero
    ((stacks0GQI B (associatedBigEtaleSite B) rfl S hS f hf).2.2 i hi _
      (lqcohSheafFbcFppfModules_quasicoherentInclusion B _ rfl S hS 𝒳 F))

include hf in
/-- **Stacks 0GQY, all colimits**: for an affine 1-morphism `f` of algebraic stacks,
`f_{QCoh,*}` commutes with all colimits indexed in the universe of the site. -/
theorem preservesColimitsOfSize_quasicoherentDirectImage_of_isAffineHom :
    PreservesColimitsOfSize.{u, u} (quasicoherentDirectImage B S hS f) := by
  let E := associatedBigEtaleSite B
  have h : E.cutoff = B.cutoff := rfl
  have := (lqcohSheafFbcCoheratorAdjunction B S hS 𝒳 E h).leftAdjoint_preservesColimits
  have := preservesColimitsOfSize_affineLqcohSheafFbcPushforward B E h S hS f hf
  have : PreservesColimitsOfSize.{u, u}
      ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coherator B S hS 𝒴) :=
    ⟨fun {J} _ => preservesColimitsOfShape_lqcohSheafFbc_ι_comp_coherator B S hS 𝒴 E h J⟩
  exact preservesColimits_of_natIso (quasicoherentDirectImageIsoOfIsAffineHom B E h S hS f hf).symm

include hf in
/-- **Stacks 0GQY, exactness**: for an affine 1-morphism `f` of algebraic stacks, `f_{QCoh,*}`
is exact: it preserves finite limits and finite colimits. -/
theorem preservesFiniteLimits_and_preservesFiniteColimits_quasicoherentDirectImage_of_isAffineHom :
    PreservesFiniteLimits (quasicoherentDirectImage B S hS f) ∧
      PreservesFiniteColimits (quasicoherentDirectImage B S hS f) :=
  have := (quasicoherentPullbackDirectImageAdjunction B S hS f).rightAdjoint_preservesLimits.{0, 0}
  have := preservesColimitsOfSize_quasicoherentDirectImage_of_isAffineHom B S hS f hf
  ⟨PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _,
    PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _⟩

include hf in
/-- **Stacks 0GQY, direct sums**: for an affine 1-morphism `f` of algebraic stacks,
`f_{QCoh,*}` commutes with direct sums indexed by any `ι : Type u`. -/
theorem preservesColimitsOfShape_discrete_quasicoherentDirectImage_of_isAffineHom (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (quasicoherentDirectImage B S hS f) :=
  have := preservesColimitsOfSize_quasicoherentDirectImage_of_isAffineHom B S hS f hf
  inferInstance

include hf in
/-- **Stacks 0GQY.** Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks. Then

1. the functors `Rⁱf_{QCoh,*}`, `i > 0`, vanish;
2. `f_{QCoh,*}` is exact: it preserves finite limits and finite colimits;
3. `f_{QCoh,*}` commutes with direct sums (indexed by any `ι : Type u`);
4. `f_{QCoh,*}` commutes with all colimits (indexed by categories `J : Type u` with morphisms in
   `u`).

The functors are those of **Stacks 077A**, `quasicoherentHigherDirectImage` and
`quasicoherentDirectImage`, at module universe `u`. -/
@[stacks 0GQY "the whole lemma, for an affine 1-morphism f of algebraic stacks and the functors \
  R^i f_{QCoh,*} and f_{QCoh,*} of Stacks 077A: R^i f_{QCoh,*} = 0 for i > 0; f_{QCoh,*} is exact \
  (preserves finite limits and finite colimits); it commutes with direct sums; it commutes with \
  all colimits (indexed in the universe u of the site)"]
theorem isZero_quasicoherentHigherDirectImage_and_exact_preservesColimits_of_isAffineHom :
    (∀ (i : ℕ), 0 < i → ∀ F : quasicoherentModules B S hS 𝒳,
        IsZero ((quasicoherentHigherDirectImage B S hS f i).obj F)) ∧
      (PreservesFiniteLimits (quasicoherentDirectImage B S hS f) ∧
        PreservesFiniteColimits (quasicoherentDirectImage B S hS f)) ∧
      (∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) (quasicoherentDirectImage B S hS f)) ∧
      PreservesColimitsOfSize.{u, u} (quasicoherentDirectImage B S hS f) :=
  ⟨isZero_quasicoherentHigherDirectImage_of_isAffineHom B S hS f hf,
    preservesFiniteLimits_and_preservesFiniteColimits_quasicoherentDirectImage_of_isAffineHom
      B S hS f hf,
    preservesColimitsOfShape_discrete_quasicoherentDirectImage_of_isAffineHom B S hS f hf,
    preservesColimitsOfSize_quasicoherentDirectImage_of_isAffineHom B S hS f hf⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
