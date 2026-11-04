module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism

/-!
# Untwisting the source of the conormal map over an open trivialising the line bundle

Stacks Tag 0B3V clause 3 gives a canonical map out of `ker(q) ⊗ 𝓛^{⊗ -1}`, built in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap`. Over an open `U` on which
`𝓛` is trivial the source is just `ker(q)|_U`, which is why the clause's local computation reads
`k ⊗ s^{-1} ↦ f mod 𝓘²` and says nothing about the twist. This file carries out that reduction.

## Main definitions

* `Stacks.ProjectiveBundleConormal.restrictTensorIso`: **Tag 01CD along an open immersion**,
  `(A ⊗ B)|_U ≅ A|_U ⊗ B|_U`.
* `Stacks.ProjectiveBundleConormal.restrictUnitMonoidalIso`: `(𝒪_X)|_U ≅ 𝒪_U`, at the monoidal
  unit.
* `Stacks.ProjectiveBundleConormal.restrictTrivialTensorIso`: a tensor factor that becomes
  trivial on `U` may be dropped from the restriction, `(K ⊗ T)|_U ≅ K|_U`.
* `Stacks.ProjectiveBundleConormal.restrictInverseTwistIso`: **over an open trivialising `L`, the
  inverse twist `L^{⊗ -1}` is trivial too.**
* `Stacks.ProjectiveBundleConormal.restrictSourceIso`: **over an open trivialising `L`, the source
  `K ⊗ L^{⊗ -1}` of the conormal map restricts to `K` itself.**

## Main results

* `Stacks.ProjectiveBundleConormal.restrictTensorIso_hom` and
  `restrictTensorIso_naturality_left`: the comparison spelled out, and its naturality in the
  first variable in whiskered form — the form the assembly needs.
* `Stacks.ProjectiveBundleConormal.restrictTrivialTensorIso_hom` and
  `restrictTrivialTensorIso_naturality_left`: the same two statements for the generic version,
  which is where they are proved.
* `Stacks.ProjectiveBundleConormal.restrictSourceIso_hom`: **the normalisation.** On sections over
  `U` the isomorphism is `k ⊗ s̄^{-1} ↦ k`: it is Tag 01CD, then the trivialisation of the twist,
  then the right unitor, and nothing else.
* `Stacks.ProjectiveBundleConormal.restrictSourceIso_naturality_left`: naturality in `K`, so that
  the reduction may be matched against
  `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_comp_ι`, whose source is read through a
  map of the first factor.

## Implementation notes

**Which tensor spelling.** The re-seated monoidal structure
`SheafOfModules.monoidalCategorySheafTensor X.toRingedSpace.sheaf` of
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor`, the one `CanonicalMap` is written over.
Under it `A ⊗ B` is `Stacks.SheafOfModules.Invertible.tensorProduct` and `𝟙_` is
`SheafOfModules.unit` definitionally, so `Scheme.Modules.restrictUnitIso` and
`Stacks.SheafOfModules.Invertible.mulNegOneIso` can be ascribed to the monoidal spelling by
`rfl`, and no unit comparison is needed anywhere below. The instance is not redeclared here: it
is `CanonicalMap`'s, switched on by `attribute [local instance]`.

**Nothing about the tensor product is reproved.** `restrictTensorIso` is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` — restriction along an open
immersion is the pullback — conjugating `Stacks.ProjectiveBundleConormal.pullbackTensorComparison`,
Tag 01CD at this monoidal spelling, whose invertibility
(`Stacks.PullbackSheafTensor.isIso_sheafTensorComparison`) is unconditional. Its naturality is
`pullbackTensorComparison_naturality_left` conjugated the same way.

**Restriction is not shown to commute with `tensorPower`,** and does not have to be: the twist is
trivialised through the evaluation pairing `L ⊗ L^{⊗ -1} ≅ 𝒪_X` instead. Restricting the pairing
and feeding it `L|_U ≅ 𝒪_U` identifies `(L^{⊗ -1})|_U` with `𝒪_U` by the unitors alone, which is
all `restrictSourceIso` consumes.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}}

/-! ### Tag 01CD along an open immersion -/

/-- **Restricting a tensor product to an open is the tensor product of the restrictions.**
Restriction along `U.ι` is the pullback along it, by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the pullback splits over the
tensor product by Tag 01CD; this is the latter conjugated by the former. -/
def restrictTensorIso (U : X.Opens) (A B : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj (A ⊗ B) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj A ⊗
        (Scheme.Modules.restrictFunctor U.ι).obj B :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (A ⊗ B) ≪≫
    pullbackTensorComparisonIso U.ι A B ≪≫
    whiskerRightIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app A).symm
      ((Scheme.Modules.pullback U.ι).obj B) ≪≫
    whiskerLeftIso ((Scheme.Modules.restrictFunctor U.ι).obj A)
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app B).symm

/-- `restrictTensorIso` spelled out: the crossing to the pullback, Tag 01CD, and the two
crossings back, one factor at a time. -/
theorem restrictTensorIso_hom (U : X.Opens) (A B : X.Modules) :
    (restrictTensorIso U A B).hom =
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app (A ⊗ B) ≫
        pullbackTensorComparison U.ι A B ≫
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app A ▷
            (Scheme.Modules.pullback U.ι).obj B) ≫
            ((Scheme.Modules.restrictFunctor U.ι).obj A ◁
              (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app B) :=
  rfl

/-- **Naturality of `restrictTensorIso` in the first variable**, in whiskered form. This is the
form the assembly needs: the source of the conormal map is read through a map of its first
factor. -/
theorem restrictTensorIso_naturality_left (U : X.Opens) {A A' : X.Modules} (v : A ⟶ A')
    (B : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (v ▷ B) ≫ (restrictTensorIso U A' B).hom =
      (restrictTensorIso U A B).hom ≫
        ((Scheme.Modules.restrictFunctor U.ι).map v ▷
          (Scheme.Modules.restrictFunctor U.ι).obj B) := by
  rw [restrictTensorIso_hom, restrictTensorIso_hom]
  slice_lhs 1 2 => rw [(Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.naturality (v ▷ B)]
  slice_lhs 2 3 => rw [← pullbackTensorComparison_naturality_left]
  slice_lhs 3 4 => rw [← comp_whiskerRight]
  slice_lhs 3 3 => rw [(Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.naturality v]
  slice_lhs 3 3 => rw [comp_whiskerRight]
  slice_lhs 4 5 => rw [← whisker_exchange]
  simp only [Category.assoc]

/-- **The restriction of the structure sheaf to an open is the structure sheaf**, with source and
target ascribed at the monoidal unit. This is `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`;
the unit of the re-seated structure is `SheafOfModules.unit` definitionally, so no comparison of
units is involved. -/
def restrictUnitMonoidalIso (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj (𝟙_ X.Modules) ≅ 𝟙_ _ :=
  Scheme.Modules.restrictUnitIso U.ι

/-! ### Dropping a trivial second factor from a restricted tensor product -/

/-- **A tensor factor that becomes trivial on `U` may be dropped from the restriction.** Given a
trivialisation `t : T|_U ≅ 𝒪_U`, the restriction of `K ⊗ T` to `U` is `K|_U`: Tag 01CD splits the
restriction, `t` turns the second factor into `𝒪_U`, and the right unitor drops it.

Stated for an arbitrary `T` rather than for the inverse twist it is used at, because the twist is
`Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)`, whose sheaf
condition argument makes a goal mentioning it fail to be type-correct at `implicit`
transparency; `rw` then refuses the naturality square below. With `T` a variable there is no such
term and the proof is the three-step slide it should be. -/
def restrictTrivialTensorIso (U : X.Opens) (K T : X.Modules)
    (t : (Scheme.Modules.restrictFunctor U.ι).obj T ≅ 𝟙_ _) :
    (Scheme.Modules.restrictFunctor U.ι).obj (K ⊗ T) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj K :=
  restrictTensorIso U K T ≪≫
    whiskerLeftIso ((Scheme.Modules.restrictFunctor U.ι).obj K) t ≪≫
    ρ_ ((Scheme.Modules.restrictFunctor U.ι).obj K)

/-- `restrictTrivialTensorIso` spelled out: Tag 01CD, the trivialisation in the second factor,
the right unitor. -/
theorem restrictTrivialTensorIso_hom (U : X.Opens) (K T : X.Modules)
    (t : (Scheme.Modules.restrictFunctor U.ι).obj T ≅ 𝟙_ _) :
    (restrictTrivialTensorIso U K T t).hom =
      (restrictTensorIso U K T).hom ≫
        ((Scheme.Modules.restrictFunctor U.ι).obj K ◁ t.hom) ≫
          (ρ_ ((Scheme.Modules.restrictFunctor U.ι).obj K)).hom :=
  rfl

/-- **Naturality of `restrictTrivialTensorIso` in the kept factor**, in whiskered form:
naturality of Tag 01CD, the interchange law, and naturality of the right unitor, in that
order. -/
theorem restrictTrivialTensorIso_naturality_left (U : X.Opens) {K K' : X.Modules} (k : K ⟶ K')
    (T : X.Modules) (t : (Scheme.Modules.restrictFunctor U.ι).obj T ≅ 𝟙_ _) :
    (Scheme.Modules.restrictFunctor U.ι).map (k ▷ T) ≫
        (restrictTrivialTensorIso U K' T t).hom =
      (restrictTrivialTensorIso U K T t).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map k := by
  rw [restrictTrivialTensorIso_hom, restrictTrivialTensorIso_hom]
  slice_lhs 1 2 => rw [restrictTensorIso_naturality_left]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  simp only [Category.assoc]

/-! ### The inverse twist over an open trivialising the line bundle -/

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- **Over an open trivialising `L`, the inverse twist `L^{⊗ -1}` is trivial too.** Restricting
the evaluation pairing `L ⊗ L^{⊗ -1} ≅ 𝒪_X` and splitting it by Tag 01CD exhibits
`L|_U ⊗ (L^{⊗ -1})|_U ≅ 𝒪_U`; feeding the trivialisation `τ : L|_U ≅ 𝒪_U` into the first factor
and cancelling it with the left unitor leaves `(L^{⊗ -1})|_U ≅ 𝒪_U`. No commutation of
restriction with `tensorPower` is needed. -/
def restrictInverseTwistIso (U : X.Opens)
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ _) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) ≅
      𝟙_ _ :=
  (λ_ ((Scheme.Modules.restrictFunctor U.ι).obj
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)))).symm ≪≫
    whiskerRightIso τ.symm _ ≪≫
    (restrictTensorIso U L
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1))).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (invertibleEvaluation L) ≪≫
    restrictUnitMonoidalIso U

/-! ### The source of the conormal map over an open trivialising the line bundle -/

/-- **Over an open trivialising `L`, the source of the conormal map is just `Ker(q)`.** For
`K : X.Modules` — in Tag 0B3V clause 3, `K = ker(q)` — the restriction of `K ⊗ L^{⊗ -1}` to `U`
is `K|_U`: Tag 01CD splits the restriction, the trivialisation of the inverse twist turns the
second factor into `𝒪_U`, and the right unitor drops it. `restrictSourceIso_hom` is the `rfl`
decomposition into those three steps; the statement that on sections this is `k ⊗ s̄^{-1} ↦ k` is
`Stacks.ProjectiveBundleConormal.restrictSourceIso_inv_tensorSectionsAt`. -/
def restrictSourceIso (U : X.Opens) (K : X.Modules)
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ _) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (K ⊗ Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj K :=
  restrictTrivialTensorIso U K
    (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
    (restrictInverseTwistIso L U τ)

/-- **The normalisation of `restrictSourceIso`**: it is Tag 01CD along `U.ι`, then the
trivialisation of the inverse twist in the second factor, then the right unitor — nothing else.
This is what pins the reduction down well enough to be matched against
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_comp_ι`. -/
theorem restrictSourceIso_hom (U : X.Opens) (K : X.Modules)
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ _) :
    (restrictSourceIso L U K τ).hom =
      (restrictTensorIso U K
            (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
              L (-1))).hom ≫
        ((Scheme.Modules.restrictFunctor U.ι).obj K ◁
            (restrictInverseTwistIso L U τ).hom) ≫
          (ρ_ ((Scheme.Modules.restrictFunctor U.ι).obj K)).hom :=
  rfl

/-- **Naturality of `restrictSourceIso` in `K`**, in whiskered form: a map of the first factor of
the source commutes with the reduction. -/
theorem restrictSourceIso_naturality_left (U : X.Opens) {K K' : X.Modules} (k : K ⟶ K')
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj L ≅ 𝟙_ _) :
    (Scheme.Modules.restrictFunctor U.ι).map
          (k ▷ Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)) ≫
        (restrictSourceIso L U K' τ).hom =
      (restrictSourceIso L U K τ).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map k :=
  restrictTrivialTensorIso_naturality_left U k
    (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
    (restrictInverseTwistIso L U τ)

end Stacks.ProjectiveBundleConormal

end
