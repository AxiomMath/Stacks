module

public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularityGlobalGeneration

/-!
# Multiplication by a degree-one form on a twist, pulled back along a morphism

`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul n S ℱ s d` is the
arrow `ℱ(d) ⟶ ℱ(d + 1)` on `ℙⁿ_S` obtained by multiplying by a global section `s` of `𝒪(1)` and
then regrouping `𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d + 1)`. This file proves that **a pullback carries it to
multiplication by the restricted section**: for a morphism `g : ℙᵐ_S ⟶ ℙⁿ_S` and identifications
`θ_d : g^*(𝒪_{ℙⁿ}(d)) ≅ 𝒪_{ℙᵐ}(d)` compatible with that one regrouping,

`g^*(s · -) ≫ c_{d+1} = c_d ≫ (σ · -)`,  where  `c_d = (01CD) ≫ (- ⊗ θ_d)`,

for every module `ℱ` at once, `σ` being the restriction of `s`. This is the square of sheaves
that [Stacks, Tag 08A7] needs, in the spelling `twistSectionMul` rather than
`…ProjectiveSpaceSectionMulShape.mulSection` — see the "What remains" section of
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionPackageConstruction.lean`,
where the missing piece is recorded as "(1) The same statement for `…twistSectionMul` rather than
for `mulSection`".

## Main results

* `Stacks.AlgebraicGeometry.PullbackTwistSectionMul.pullbackTensorComparison_twistMul`: **the
  square on a morphism of ringed spaces**, for the four-fold composite
  `ρ⁻¹ ≫ ◁τ ≫ α ≫ ◁m` that `twistSectionMul` is, with `m : 𝒜 ⊗ ℬ ⟶ 𝒟` an arbitrary
  "regrouping". The two hypotheses are the restricted multiplier and the compatibility of `m`
  with the comparison of [Stacks, Tag 01CD], and nothing else enters.
* `…PullbackTwistSectionMul.pullback_twistSectionMul`: **the square on `ℙⁿ_S`**, in a single
  degree `d`, from `θ_d`, `θ_1`, `θ_{d+1}` and the regrouping square relating them.
* `…PullbackTwistSectionMul.exists_pullback_twistSectionMul`: the same for a family `θ` over all
  of `ℤ` satisfying the regrouping square in every degree, with the restriction `σ` of `s`
  produced: one `σ` and one family serve every module `ℱ` and every degree `d` at once.
* `…PullbackTwistSectionMul.exists_pullbackTwistIso_succ`: **the regrouping square can be solved
  for `θ_{d+1}`.** Given `θ_d` and `θ_1` there is a `θ_{d+1}` making it commute, so the family of
  the previous item exists on `{d₀, d₀ + 1, …}` for any base degree `d₀`.
* `…PullbackTwistSectionMul.exists_pullback_twistSectionMul_succ`: **the square in a single
  degree with no compatibility hypothesis**, from `θ_d` and `θ_1` alone, by solving for
  `θ_{d+1}`. This is the form a consumer at a fixed degree — `d = -1` for [Stacks, Tag 08A0] —
  can use directly.
* `…PullbackTwistSectionMul.twistSectionMul_eq` and `…twistAssocIso_hom_eq`: `twistSectionMul`
  and `AlgebraicGeometry.twistAssocIso` written in the monoidal structure of [Stacks, Tag 01CA],
  which is the structure the coherences of [Stacks, Tag 01CD] are available in.
* `…PullbackTwistSectionMul.tensorProductAssociator_eq`: the fixed associativity constraint of
  the tensor product sheaf **is** the associator of that structure.

## The mathematics

There is none beyond the coherence of [Stacks, Tag 01CD].
`AlgebraicGeometry.twistSectionMul_eq_mulSectionOne_comp` splits `twistSectionMul n S ℱ s d` as
multiplication of `ℱ(d)` by `s` followed by `AlgebraicGeometry.twistAssocIso`, which is the
associator followed by the regrouping; the pullback of the first factor is
`Stacks.AlgebraicGeometry.PullbackSectionMul.pullback_mulSection`, the pullback of the associator
is `Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator`, and the regrouping is
the hypothesis. What glues the three is the naturality of multiplication by a section in the
module (`AlgebraicGeometry.mulSectionOne_naturality`) together with one instance each of
`CategoryTheory.MonoidalCategory.whisker_exchange` and
`CategoryTheory.MonoidalCategory.associator_naturality`.

## Implementation notes

**No coherence between the two regrouping isomorphisms is needed, and none is proved.** The
square relates the regrouping `𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d + 1)` upstairs to the one downstairs through
`θ_d`, `θ_1` and `θ_{d+1}`; it does *not* compare two regroupings on the same space, which is the
coherence that `StacksFrontier/AlgebraicGeometry/Constructions/ProjectiveSpaceSectionMulShape.lean`
avoids and this development does not have. The compatibility that *is* assumed,
`hθ` of `pullback_twistSectionMul`, is an instance of [Stacks, Tag 01MY] — which is proved, in
every pair of integer degrees, as
`Stacks.AlgebraicGeometry.ProjMapCard.twistMap_comp_pullbackTwistMultiplication` for the twists
of `Proj` and the comparison maps along a homomorphism of graded rings — and, for the tensor
powers of Tag 01CU in nonnegative degrees, as
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso`.

**Why `exists_pullbackTwistIso_succ` is legitimate and the corresponding step for `res` is not.**
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionPackageConstruction.lean`
records that `c_{d+1}` cannot be *defined* from
`c_d` by the square of that file, because solving for it would need multiplication by `σ` to be
epi or split and it is neither. Solving the *regrouping* square for `θ_{d+1}` is a different
matter: every arrow in it — the pullback of the regrouping, the comparison of Tag 01CD, the
tensor product of `θ_d` with `θ_1`, and the regrouping downstairs — is an isomorphism, so
`θ_{d+1}` is determined, and it is an identification of twists alone, independent of `ℱ`. That
independence is what lets one family serve every module.

**What this does not give in one step: a multiplicative family over all of `ℤ`.** The step above
constructs `θ_{d+1}` from `θ_d`, never `θ_d` from `θ_{d+1}`: the latter would need `θ_d` to be
extracted from `θ_d ⊗ θ_1`, i.e. the functor `- ⊗ 𝒪_{ℙᵐ}(1)` to be full on the hom-set in
question. That is true — tensoring with an invertible module is an equivalence, which the library
has as `Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor` — and this paragraph
previously said the bridge to that spelling "is not available". **That is no longer so**: the
bridge is `Stacks.AlgebraicGeometry.PullbackTwistRegrouping.whiskerRight_eq_tensorRightModules`
(`StacksFrontier/AlgebraicGeometry/Variety/Projective/PullbackTwistRegroupingFamily.lean:85`), which
identifies right whiskering in the Tag 01CA structure with `TensorPower.tensorRightFunctor.map`,
whence `exists_iso_whiskerRight_eq` (`:96`) and the downward step
`exists_pullbackTwistIso_pred` (`:127`).

A family of identifications over all of `ℤ` *is* available, as
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso`, built from the
degree-one input of [Stacks, Tag 089Z] through `𝒪(1)^{⊗ d} ≅ 𝒪(d)` and
`…HyperplaneTwistSequence.pullbackTensorPowModuleIntIso`. It is still not proved that *that*
family satisfies the regrouping square `hθ` below, and proving it would run into the following
obstruction:
the multiplicativity of `pullbackTensorPowModuleIntIso` against
`Stacks.Ample.tensorPowModuleAddIso` is proved in the nonnegative degrees only
(`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso`), while the negative
degrees of `pullbackTensorPowModuleIntIso` come from uniqueness of a tensor inverse
(`…pullbackTensorPowModuleNegSuccIso`), which supplies no equation to compute with.

**That obstruction no longer blocks anything**, because `hθ` is not obtained for
`pullbackTwistOverIso` at all: a family satisfying it is *built*, anchored at degree one, by
`Stacks.AlgebraicGeometry.PullbackTwistRegrouping.exists_regroupingFamily`
(`StacksFrontier/AlgebraicGeometry/Variety/Projective/PullbackTwistRegroupingFamily.lean:206`),
whose members need not be `pullbackTwistOverIso` in any degree — and nothing asks them to be,
since post-composing an identification of twists with an automorphism leaves every clause of the
restriction package intact. So `exists_pullback_twistSectionMul` below is unconditional over all
of `ℤ` as it stands, and the earlier claim that `hθ` was "the only thing between it and an
unconditional statement" has been discharged rather than merely restated.

**The monoidal structures.** As in
`StacksFrontier/AlgebraicGeometry/Constructions/PullbackSectionMultiplication.lean`:
`twistSectionMul`, `AlgebraicGeometry.mulSectionOne` and `AlgebraicGeometry.twistAssocIso` are
written in `Stacks.SheafOfModules.sheafTensorMonoidal`, whose associator is the fixed constraint
`Stacks.SheafOfModules.Invertible.tensorProductAssociator`, while the coherences of Tag 01CD live
in `Stacks.PullbackGradedAlgebra.monoidalCategory`. `tensorProductAssociator_eq` below is the
missing third bridge, after that file's `tensorProductRightUnitor_eq` and
`sheafifyWhiskerLeft_eq_whiskerLeft`; it is proved the same way, from
`Stacks.SheafOfModules.tensorProductAssociator_eq_comparison` against
`Stacks.SheafOfModules.Strict.associator_eq`. Every crossing between the two spellings is made
once, inside a proof given by `:=`, for the reason that file's implementation notes record.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU) — the multiplication maps
  on the twists.
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY) — the comparison maps on
  twists are compatible with the multiplication maps.
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistOverMulIso)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication (sectionHom twistSectionMul)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape (mulSection)
open Stacks.RelativeVeryAmple (tensorModules tensorModulesMapIso pullbackTensorModulesIso)

universe v u w

namespace Stacks.AlgebraicGeometry.PullbackTwistSectionMul

/-! ### The fixed associativity constraint is the associator of the strict structure -/

section Bridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The fixed associativity constraint of the tensor product sheaf is the associator of
`Stacks.SheafOfModules.Strict.monoidalCategory`.** Both are the localized associator conjugated
by `Stacks.SheafOfModules.tensorObjIso`. -/
theorem tensorProductAssociator_hom_eq
    (M N P : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Invertible.tensorProductAssociator O hO M N P).hom =
      (MonoidalCategoryStruct.associator
        (self := Stacks.SheafOfModules.Strict.monoidalCategoryStruct O hO) M N P).hom := by
  rw [Stacks.SheafOfModules.Strict.associator_eq,
    Stacks.SheafOfModules.tensorProductAssociator_eq_comparison]

end Bridge

attribute [local instance] Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

/-- `Stacks.SheafOfModules.Invertible.tensorProductAssociator` on a scheme **is** the associator
of [Stacks, Tag 01CA]. -/
theorem tensorProductAssociator_eq (X : Scheme.{u}) (A B D : X.Modules) :
    Stacks.SheafOfModules.Invertible.tensorProductAssociator X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B D = α_ A B D :=
  Iso.ext (tensorProductAssociator_hom_eq _ _ A B D)

/-! ### The square on a morphism of ringed spaces -/

section Pullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Multiplication by a morphism out of the monoidal unit is natural in the module.** The
right unitor is natural and the two whiskerings commute; this is
`AlgebraicGeometry.mulSectionOne_naturality` in the monoidal structure of [Stacks, Tag 01CA]. -/
theorem rightUnitorInv_whiskerLeft_naturality
    {M N B : SheafOfModules.{u} (structureRingSheaf X)} (w : M ⟶ N)
    (τ : 𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) ⟶ B) :
    w ≫ (ρ_ N).inv ≫ N ◁ τ = ((ρ_ M).inv ≫ M ◁ τ) ≫ w ▷ B := by
  rw [MonoidalCategory.rightUnitor_inv_naturality_assoc, ← MonoidalCategory.whisker_exchange,
    Category.assoc]

/-- **The one piece of monoidal coherence the square needs.** Moving a morphism `p` out of a
whiskering past the associator and a tensor product of two morphisms: a whisker exchange, the
second description of a tensor product of morphisms, and the naturality of the associator in its
last two arguments.

Isolated with the objects as variables: at the concrete objects the source of `p` is the pullback
of a tensor product and its target a tensor product of pullbacks, and nothing can be rewritten
across that. -/
theorem whiskerRight_associator_tensorHom {E : Type u} [Category.{v} E] [MonoidalCategory E]
    {W U A A' B B' : E} (p : W ⟶ U ⊗ A) (θA : A ⟶ A') (θB : B ⟶ B') :
    p ▷ B ≫ (α_ U A B).hom ≫ U ◁ (θA ⊗ₘ θB) =
      W ◁ θB ≫ (p ≫ U ◁ θA) ▷ B' ≫ (α_ U A' B').hom := by
  have h3 := MonoidalCategory.associator_naturality (𝟙 U) θA θB
  simp only [MonoidalCategory.id_tensorHom] at h3
  calc p ▷ B ≫ (α_ U A B).hom ≫ U ◁ (θA ⊗ₘ θB)
      = p ▷ B ≫ ((U ◁ θA) ⊗ₘ θB) ≫ (α_ U A' B').hom := by rw [h3]
    _ = p ▷ B ≫ ((U ⊗ A) ◁ θB ≫ (U ◁ θA) ▷ B') ≫ (α_ U A' B').hom := by
          rw [← MonoidalCategory.tensorHom_def']
    _ = (p ▷ B ≫ (U ⊗ A) ◁ θB) ≫ (U ◁ θA) ▷ B' ≫ (α_ U A' B').hom := by
          simp only [Category.assoc]
    _ = (W ◁ θB ≫ p ▷ B') ≫ (U ◁ θA) ▷ B' ≫ (α_ U A' B').hom := by
          rw [MonoidalCategory.whisker_exchange]
    _ = W ◁ θB ≫ (p ≫ U ◁ θA) ▷ B' ≫ (α_ U A' B').hom := by
          simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]

variable (F A B D : SheafOfModules.{u} (structureRingSheaf Y))

/-- The pullback of a regrouping `α ≫ ℱ ◁ m`, followed by the comparison of [Stacks, Tag 01CD]
and `θD`, is the comparison on `(ℱ ⊗ 𝒜) ⊗ ℬ` followed by the associator and the regrouping `m'`. -/
private theorem pullbackTensorComparison_associator_whiskerLeft_comp
    {A' B' D' : SheafOfModules.{u} (structureRingSheaf X)}
    (m : A ⊗ B ⟶ D) (m' : A' ⊗ B' ⟶ D')
    (θA : (pullbackFunctor f).obj A ⟶ A') (θB : (pullbackFunctor f).obj B ⟶ B')
    (θD : (pullbackFunctor f).obj D ⟶ D')
    (hm : (pullbackFunctor f).map m ≫ θD =
      pullbackTensorComparison f A B ≫ (θA ⊗ₘ θB) ≫ m') :
    (pullbackFunctor f).map ((α_ F A B).hom ≫ F ◁ m) ≫
        pullbackTensorComparison f F D ≫ (pullbackFunctor f).obj F ◁ θD =
      (pullbackTensorComparison f (F ⊗ A) B ≫
          pullbackTensorComparison f F A ▷ (pullbackFunctor f).obj B) ≫
        (α_ ((pullbackFunctor f).obj F) ((pullbackFunctor f).obj A)
            ((pullbackFunctor f).obj B)).hom ≫
          (pullbackFunctor f).obj F ◁ ((θA ⊗ₘ θB) ≫ m') :=
  calc (pullbackFunctor f).map ((α_ F A B).hom ≫ F ◁ m) ≫
          pullbackTensorComparison f F D ≫ (pullbackFunctor f).obj F ◁ θD
      = (pullbackFunctor f).map (α_ F A B).hom ≫
          ((pullbackFunctor f).map (F ◁ m) ≫ pullbackTensorComparison f F D) ≫
            (pullbackFunctor f).obj F ◁ θD := by
        rw [CategoryTheory.Functor.map_comp]
        simp only [Category.assoc]
    _ = (pullbackFunctor f).map (α_ F A B).hom ≫
          (pullbackTensorComparison f F (A ⊗ B) ≫
              (pullbackFunctor f).obj F ◁ (pullbackFunctor f).map m) ≫
            (pullbackFunctor f).obj F ◁ θD := by
        rw [pullbackTensorComparison_naturality_right]
    _ = (pullbackFunctor f).map (α_ F A B).hom ≫
          pullbackTensorComparison f F (A ⊗ B) ≫
            (pullbackFunctor f).obj F ◁ ((pullbackFunctor f).map m ≫ θD) := by
        rw [MonoidalCategory.whiskerLeft_comp]
        simp only [Category.assoc]
    _ = (pullbackFunctor f).map (α_ F A B).hom ≫
          pullbackTensorComparison f F (A ⊗ B) ≫
            (pullbackFunctor f).obj F ◁ (pullbackTensorComparison f A B ≫
              (θA ⊗ₘ θB) ≫ m') := by
        rw [hm]
    _ = ((pullbackFunctor f).map (α_ F A B).hom ≫
          pullbackTensorComparison f F (A ⊗ B) ≫
            (pullbackFunctor f).obj F ◁ pullbackTensorComparison f A B) ≫
          (pullbackFunctor f).obj F ◁ ((θA ⊗ₘ θB) ≫ m') := by
        rw [MonoidalCategory.whiskerLeft_comp]
        simp only [Category.assoc]
    _ = (pullbackTensorComparison f (F ⊗ A) B ≫
          (pullbackTensorComparison f F A ▷ (pullbackFunctor f).obj B) ≫
            (α_ ((pullbackFunctor f).obj F) ((pullbackFunctor f).obj A)
              ((pullbackFunctor f).obj B)).hom) ≫
          (pullbackFunctor f).obj F ◁ ((θA ⊗ₘ θB) ≫ m') := by
        rw [pullbackTensorComparison_associator]
    _ = (pullbackTensorComparison f (F ⊗ A) B ≫
          pullbackTensorComparison f F A ▷ (pullbackFunctor f).obj B) ≫
          (α_ ((pullbackFunctor f).obj F) ((pullbackFunctor f).obj A)
              ((pullbackFunctor f).obj B)).hom ≫
            (pullbackFunctor f).obj F ◁ ((θA ⊗ₘ θB) ≫ m') := by
        simp only [Category.assoc]

/-- **A pullback carries multiplication by a section followed by a regrouping to multiplication
by the restricted section followed by the regrouping downstairs.**

The arrow `(ρ_ (ℱ ⊗ 𝒜))⁻¹ ≫ (ℱ ⊗ 𝒜) ◁ τ ≫ α ≫ ℱ ◁ m` is the shape of
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`: multiplication
by `τ : 𝟙_ ⟶ ℬ` on `ℱ ⊗ 𝒜`, then the associator, then a regrouping `m : 𝒜 ⊗ ℬ ⟶ 𝒟`. The two
hypotheses are that `τ'` is the restriction of `τ` along `θB` and that `m` is carried to `m'` by
the comparison of [Stacks, Tag 01CD] together with `θA`, `θB` and `θD`; nothing else is assumed,
and in particular no two regroupings on the same space are ever compared.

The comparison on either side of the square is the comparison of Tag 01CD on `ℱ` and the twist,
followed by whiskering with the identification of the twist. -/
theorem pullbackTensorComparison_twistMul
    {A' B' D' : SheafOfModules.{u} (structureRingSheaf X)}
    (m : A ⊗ B ⟶ D) (m' : A' ⊗ B' ⟶ D')
    (τ : 𝟙_ (SheafOfModules.{u} (structureRingSheaf Y)) ⟶ B)
    (τ' : 𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) ⟶ B')
    (θA : (pullbackFunctor f).obj A ⟶ A') (θB : (pullbackFunctor f).obj B ⟶ B')
    (θD : (pullbackFunctor f).obj D ⟶ D')
    (hτ : τ' = inv (pullbackUnitComparison f) ≫ (pullbackFunctor f).map τ ≫ θB)
    (hm : (pullbackFunctor f).map m ≫ θD =
      pullbackTensorComparison f A B ≫ (θA ⊗ₘ θB) ≫ m') :
    (pullbackFunctor f).map (((ρ_ (F ⊗ A)).inv ≫ (F ⊗ A) ◁ τ) ≫
          ((α_ F A B).hom ≫ F ◁ m)) ≫
        pullbackTensorComparison f F D ≫ (pullbackFunctor f).obj F ◁ θD =
      (pullbackTensorComparison f F A ≫ (pullbackFunctor f).obj F ◁ θA) ≫
        ((ρ_ ((pullbackFunctor f).obj F ⊗ A')).inv ≫
            ((pullbackFunctor f).obj F ⊗ A') ◁ τ') ≫
          ((α_ ((pullbackFunctor f).obj F) A' B').hom ≫
            (pullbackFunctor f).obj F ◁ m') := by
  -- the multiplication half, with the restricted multiplier substituted
  have hmul := Stacks.AlgebraicGeometry.PullbackSectionMul.pullbackTensorComparison_mulSection_comp
    f (F ⊗ A) B τ θB
  rw [← hτ] at hmul
  -- the right-hand side, with multiplication moved to the front
  have hR := rightUnitorInv_whiskerLeft_naturality
    (pullbackTensorComparison f F A ≫ (pullbackFunctor f).obj F ◁ θA) τ'
  -- the coherence, at the comparison of Tag 01CD on `ℱ` and `𝒜`
  have hK := whiskerRight_associator_tensorHom (pullbackTensorComparison f F A) θA θB
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [pullbackTensorComparison_associator_whiskerLeft_comp f F A B D m m' θA θB θD hm]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hK, reassoc_of% hmul, reassoc_of% hR]

end Pullback

/-! ### The square on projective space -/

section Projective

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable (n m : ℕ) (S : Scheme.{u})

/-- **`AlgebraicGeometry.twistAssocIso` written in the monoidal structure of [Stacks, Tag
01CA]**: the associator followed by whiskering with the regrouping `𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d + 1)`. -/
theorem twistAssocIso_hom_eq (F : (projectiveSpaceOver n S).Modules) (d : ℤ) :
    (AlgebraicGeometry.twistAssocIso n S F d).hom =
      (α_ F (twistOver n S d) (twistOver n S 1)).hom ≫
        F ◁ (twistOverMulIso n S d 1).hom :=
  (congrArg (fun x ↦ x ≫ (tensorModulesMapIso (projectiveSpaceOver n S) (Iso.refl F)
          (twistOverMulIso n S d 1)).hom)
      (congrArg Iso.hom (tensorProductAssociator_eq (projectiveSpaceOver n S) F
        (twistOver n S d) (twistOver n S 1)))).trans
    (congrArg (fun y ↦ (α_ F (twistOver n S d) (twistOver n S 1)).hom ≫ y)
      (Stacks.AlgebraicGeometry.PullbackSectionMul.tensorModulesMapIso_refl_hom
        (projectiveSpaceOver n S) F (twistOverMulIso n S d 1)))

/-- **`AlgebraicGeometry.mulSectionOne` written in the monoidal structure of [Stacks, Tag
01CA]**: the inverse right unitor followed by whiskering with `s` read as a morphism out of the
monoidal unit.

`AlgebraicGeometry.mulSectionOne` multiplies by
`…ProjectiveSpaceSectionMultiplication.tensorRightOfUnitHom`, the native tensor bifunctor at a
pair whose first component is an identity, and that is the one step by which it differs from the
whiskering — `…ProjectiveSpaceSectionMultiplication.tensorRightOfUnitHom_eq_map` is the law which
takes it, and it is applied here rather than left to the unifier. -/
theorem mulSectionOne_eq (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    AlgebraicGeometry.mulSectionOne n S
        (tensorModules (projectiveSpaceOver n S) F (twistOver n S d)) s =
      (ρ_ (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))).inv ≫
        tensorModules (projectiveSpaceOver n S) F (twistOver n S d) ◁
          sectionHom (twistOver n S 1) s :=
  ((congrArg (fun unitor ↦ unitor ≫
          Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.tensorRightOfUnitHom n S
            (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
            (sectionHom (twistOver n S 1) s))
        (congrArg Iso.inv
          (Stacks.AlgebraicGeometry.PullbackSectionMul.tensorProductRightUnitor_eq
            (projectiveSpaceOver n S)
            (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))))).trans
      (congrArg (fun multiplication ↦
          (ρ_ (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))).inv ≫
            multiplication)
        (Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.tensorRightOfUnitHom_eq_map
          n S (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
          (sectionHom (twistOver n S 1) s)))).trans
    (congrArg (fun whiskering ↦
        (ρ_ (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))).inv ≫ whiskering)
      (Stacks.AlgebraicGeometry.PullbackSectionMul.sheafifyWhiskerLeft_eq_whiskerLeft _ _
        (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))
        (sectionHom (twistOver n S 1) s)))

/-- **`…ProjectiveSpaceSectionMultiplication.twistSectionMul` written in the monoidal structure
of [Stacks, Tag 01CA]**: multiplication by `s` on `ℱ(d)`, then the associator, then the
regrouping of the two twists. -/
theorem twistSectionMul_eq (F : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) (d : ℤ) :
    twistSectionMul n S F s d =
      ((ρ_ (tensorModules (projectiveSpaceOver n S) F (twistOver n S d))).inv ≫
          tensorModules (projectiveSpaceOver n S) F (twistOver n S d) ◁
            sectionHom (twistOver n S 1) s) ≫
        ((α_ F (twistOver n S d) (twistOver n S 1)).hom ≫
          F ◁ (twistOverMulIso n S d 1).hom) :=
  (AlgebraicGeometry.twistSectionMul_eq_mulSectionOne_comp n S F s d).trans
    ((congrArg (fun x ↦ x ≫ (AlgebraicGeometry.twistAssocIso n S F d).hom)
        (mulSectionOne_eq n S F s d)).trans
      (congrArg (fun y ↦ ((ρ_ (tensorModules (projectiveSpaceOver n S) F
                (twistOver n S d))).inv ≫
            tensorModules (projectiveSpaceOver n S) F (twistOver n S d) ◁
              sectionHom (twistOver n S 1) s) ≫ y)
        (twistAssocIso_hom_eq n S F d)))

variable (g : projectiveSpaceOver m S ⟶ projectiveSpaceOver n S)

/-- Every global section of `𝒪(1)` has a restriction along `g` and an identification `θ1`. -/
private theorem exists_sectionHom_eq_restrict
    (θ1 : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (s : (twistOver n S 1).sections) :
    ∃ t : (twistOver m S 1).sections, sectionHom (twistOver m S 1) t =
      inv (pullbackUnitComparison g.toLRSHom.toShHom) ≫
        (Scheme.Modules.pullback g).map (sectionHom (twistOver n S 1) s) ≫ θ1.hom :=
  ⟨_, Equiv.symm_apply_apply (twistOver m S 1).unitHomEquiv _⟩

/-- **The regrouping square of degree `(d, 1)` determines `θ_{d + 1}` from `θ_d` and `θ_1`.**
Every arrow in it is an isomorphism, so the equation can be solved; and what it produces is an
identification of twists, with no module in it, so the same `θ_{d+1}` serves every `ℱ`.

This is what makes the hypothesis of
`Stacks.AlgebraicGeometry.PullbackTwistSectionMul.pullback_twistSectionMul` satisfiable, by
induction, from any single degree upwards. It is *not* the step that
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionPackageConstruction.lean`
records as unavailable: that one asks for the
square of multiplication by a section to be solved, and multiplication by a section is neither
epi nor split. -/
theorem exists_pullbackTwistIso_succ (d : ℤ)
    (θd : (Scheme.Modules.pullback g).obj (twistOver n S d) ≅ twistOver m S d)
    (θ1 : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1) :
    ∃ θ : (Scheme.Modules.pullback g).obj (twistOver n S (d + 1)) ≅
        twistOver m S (d + 1),
      (Scheme.Modules.pullback g).map (twistOverMulIso n S d 1).hom ≫ θ.hom =
        (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1)).hom ≫
          (θd.hom ⊗ₘ θ1.hom) ≫ (twistOverMulIso m S d 1).hom := by
  refine ⟨((Scheme.Modules.pullback g).mapIso (twistOverMulIso n S d 1)).symm ≪≫
    pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1) ≪≫
    (θd ⊗ᵢ θ1) ≪≫ twistOverMulIso m S d 1, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv]
  rw [← Category.assoc ((Scheme.Modules.pullback g).map (twistOverMulIso n S d 1).hom),
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

/-- **Restriction along `g` carries multiplication by a degree-one form on a twist to
multiplication by the restricted form**, in a single degree `d`.

The identifications of the three twists in play are `θd`, `θ1` and `θd1`; `hθ` is the one
compatibility they are asked for — the regrouping `𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d + 1)` upstairs is carried
to the one downstairs, through the comparison of [Stacks, Tag 01CD] — and `hst` says that `t` is
the restriction of `s` along `(g, θ1)`. Nothing is assumed about `g` beyond its being a morphism
of schemes.

Both hypotheses are discharged in
`Stacks.AlgebraicGeometry.PullbackTwistSectionMul.exists_pullback_twistSectionMul`.

The ringed-space statement is named by `have` and only then given to `exact`. Every argument of
`pullbackTensorComparison_twistMul` is supplied, so naming it determines its type outright and
the crossing from `Stacks.RelativeVeryAmple.tensorModules` to the tensor product of
[Stacks, Tag 01CA] is then one defeq check between two closed terms. Handing the application
straight to `exact` instead makes the expected type drive the elaboration of the arguments, and
the unifier meets that crossing inside terms that are still half-unknown, and it exhausts
the 200000 heartbeats at `whnf`. -/
theorem pullback_twistSectionMul (F : (projectiveSpaceOver n S).Modules) (d : ℤ)
    (θd : (Scheme.Modules.pullback g).obj (twistOver n S d) ≅ twistOver m S d)
    (θ1 : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (θd1 : (Scheme.Modules.pullback g).obj (twistOver n S (d + 1)) ≅
      twistOver m S (d + 1))
    (hθ : (Scheme.Modules.pullback g).map (twistOverMulIso n S d 1).hom ≫ θd1.hom =
      (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1)).hom ≫
        (θd.hom ⊗ₘ θ1.hom) ≫ (twistOverMulIso m S d 1).hom)
    (s : (twistOver n S 1).sections) (t : (twistOver m S 1).sections)
    (hst : sectionHom (twistOver m S 1) t =
      inv (pullbackUnitComparison g.toLRSHom.toShHom) ≫
        (Scheme.Modules.pullback g).map (sectionHom (twistOver n S 1) s) ≫ θ1.hom) :
    (Scheme.Modules.pullback g).map (twistSectionMul n S F s d) ≫
        (pullbackTensorModulesIso g F (twistOver n S (d + 1))).hom ≫
        (tensorModulesMapIso (projectiveSpaceOver m S)
          (Iso.refl ((Scheme.Modules.pullback g).obj F)) θd1).hom =
      ((pullbackTensorModulesIso g F (twistOver n S d)).hom ≫
          (tensorModulesMapIso (projectiveSpaceOver m S)
            (Iso.refl ((Scheme.Modules.pullback g).obj F)) θd).hom) ≫
        twistSectionMul m S ((Scheme.Modules.pullback g).obj F) t d := by
  rw [Stacks.AlgebraicGeometry.PullbackSectionMul.tensorModulesMapIso_refl_hom,
    Stacks.AlgebraicGeometry.PullbackSectionMul.tensorModulesMapIso_refl_hom,
    twistSectionMul_eq, twistSectionMul_eq]
  have h := pullbackTensorComparison_twistMul g.toLRSHom.toShHom F (twistOver n S d)
    (twistOver n S 1) (twistOver n S (d + 1)) (twistOverMulIso n S d 1).hom
    (twistOverMulIso m S d 1).hom (sectionHom (twistOver n S 1) s)
    (sectionHom (twistOver m S 1) t) θd.hom θ1.hom θd1.hom hst hθ
  exact h

/-- **Every global section of `𝒪_{ℙⁿ}(1)` has a restriction along `g`, and restriction
intertwines the two multiplications uniformly in the module and in the degree.**

The input is a family `θ` of identifications of the twists over all of `ℤ` satisfying the
regrouping square in every degree; `Stacks.AlgebraicGeometry.PullbackTwistSectionMul`'s
`exists_pullbackTwistIso_succ` constructs such a family upwards from any one degree. The
restriction `t` depends only on `g`, `θ 1` and `s`, so one `t` serves every `ℱ` and every `d` —
which is what the square of sheaves of [Stacks, Tag 08A7], quantified over all the twists `ℱ(d)`,
needs. -/
theorem exists_pullback_twistSectionMul
    (θ : ∀ d : ℤ, (Scheme.Modules.pullback g).obj (twistOver n S d) ≅ twistOver m S d)
    (hθ : ∀ d : ℤ,
      (Scheme.Modules.pullback g).map (twistOverMulIso n S d 1).hom ≫ (θ (d + 1)).hom =
        (pullbackTensorModulesIso g (twistOver n S d) (twistOver n S 1)).hom ≫
          ((θ d).hom ⊗ₘ (θ 1).hom) ≫ (twistOverMulIso m S d 1).hom)
    (s : (twistOver n S 1).sections) :
    ∃ t : (twistOver m S 1).sections,
      ∀ (F : (projectiveSpaceOver n S).Modules) (d : ℤ),
        (Scheme.Modules.pullback g).map (twistSectionMul n S F s d) ≫
            (pullbackTensorModulesIso g F (twistOver n S (d + 1))).hom ≫
            (tensorModulesMapIso (projectiveSpaceOver m S)
              (Iso.refl ((Scheme.Modules.pullback g).obj F)) (θ (d + 1))).hom =
          ((pullbackTensorModulesIso g F (twistOver n S d)).hom ≫
              (tensorModulesMapIso (projectiveSpaceOver m S)
                (Iso.refl ((Scheme.Modules.pullback g).obj F)) (θ d)).hom) ≫
            twistSectionMul m S ((Scheme.Modules.pullback g).obj F) t d := by
  obtain ⟨t, ht⟩ := exists_sectionHom_eq_restrict n m S g (θ 1) s
  exact ⟨t, fun F d ↦ pullback_twistSectionMul n m S g F d (θ d) (θ 1) (θ (d + 1)) (hθ d) s t ht⟩

/-- **The square in a single degree, with no compatibility hypothesis at all.** Given
identifications `θ_d` and `θ_1` of the twists in degrees `d` and one — nothing more — there are an
identification `θ_{d+1}` in degree `d + 1` and a restriction `t` of `s` such that the square
commutes for every module `ℱ`.

This is `Stacks.AlgebraicGeometry.PullbackTwistSectionMul.exists_pullbackTwistIso_succ` feeding
`…pullback_twistSectionMul`: the regrouping square is not assumed but solved, which is legitimate
because every arrow in it is an isomorphism. At `d = -1` the two inputs are
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso` in degrees `-1` and one,
the latter being the hypothesis of [Stacks, Tag 089Z]; the `θ_0` produced here need not be
`pullbackTwistOverIso` in degree zero, and nothing asks it to be — post-composing an
identification of twists with an automorphism changes neither `comp_res` nor either exactness
clause of the restriction package. -/
theorem exists_pullback_twistSectionMul_succ (d : ℤ)
    (θd : (Scheme.Modules.pullback g).obj (twistOver n S d) ≅ twistOver m S d)
    (θ1 : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (s : (twistOver n S 1).sections) :
    ∃ (θd1 : (Scheme.Modules.pullback g).obj (twistOver n S (d + 1)) ≅
        twistOver m S (d + 1)) (t : (twistOver m S 1).sections),
      ∀ F : (projectiveSpaceOver n S).Modules,
        (Scheme.Modules.pullback g).map (twistSectionMul n S F s d) ≫
            (pullbackTensorModulesIso g F (twistOver n S (d + 1))).hom ≫
            (tensorModulesMapIso (projectiveSpaceOver m S)
              (Iso.refl ((Scheme.Modules.pullback g).obj F)) θd1).hom =
          ((pullbackTensorModulesIso g F (twistOver n S d)).hom ≫
              (tensorModulesMapIso (projectiveSpaceOver m S)
                (Iso.refl ((Scheme.Modules.pullback g).obj F)) θd).hom) ≫
            twistSectionMul m S ((Scheme.Modules.pullback g).obj F) t d := by
  obtain ⟨θd1, hθ⟩ := exists_pullbackTwistIso_succ n m S g d θd θ1
  obtain ⟨t, ht⟩ := exists_sectionHom_eq_restrict n m S g θ1 s
  exact ⟨θd1, t, fun F ↦ pullback_twistSectionMul n m S g F d θd θ1 θd1 hθ s t ht⟩

end Projective

end Stacks.AlgebraicGeometry.PullbackTwistSectionMul

end
