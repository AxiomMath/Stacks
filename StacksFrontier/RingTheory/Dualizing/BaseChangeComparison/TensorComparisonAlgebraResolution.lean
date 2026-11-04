module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonBaseChangeMor

/-!
# The comparison identity moved onto a K-flat resolution of the algebra

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonBaseChangeMor` splits
`Dualizing.TensorComparisonCompatibility` — the one remaining input of
`Dualizing.KFlatAlgebraActionEq` — into

* the **identification** `μ' = μ` of the [stacks 068I] morphism `Dualizing.tensorBaseChangeMor`
  with the lax monoidal structure map of derived base change, at pairs of K-flat complexes; and
* the **comparison identity** `μ'_{X, A} ≫ tensorComparisonOfIso X = 𝟙 ⊗ θ`, in which no
  component of [stacks 0E1W], no morphism of [stacks 0E1X], no transpose, neither `μ` nor `ν` and
  no unit of [stacks 0GMT] occurs.

Its docstring records what the split does *not* remove: the comparison identity reads `μ'` at
`(X, A[0])`, and `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates `μ'` at a pair of
localizations of **K-flat** complexes, while the algebra is not K-flat over `R`.  So a value for
`μ'` there asks for a K-flat resolution of `A` over `R`.

This file performs that transport.  There is no new resolution API: `Dualizing.exists_kFlat_iso`
already produces, for any object of `D(R)`, a K-flat complex and an isomorphism onto its
localization, from the resolution of [stacks 06Y4]
(`CochainComplex.KFlat.exists_kFlat_resolution`); and
`Dualizing.tensorBaseChangeMor_app_of_iso` already transports `μ'` along an isomorphism of its
second variable.  What is done here is to carry the *whole comparison identity* across such an
isomorphism, so that its `μ'` is read at a pair of localizations of K-flat complexes, and to
assemble the result with the split.

Carrying it across is not just substituting `Q P` for `A[0]`: the transport of `μ'` leaves a
factor `baseChangeR (𝟙 ⊗ b⁻¹)` between `μ'_{X, Q P}` and the comparison, and a factor
`𝟙 ⊗ baseChangeR b` in front, and the second has to be cancelled into the right-hand side —
which turns `𝟙 ⊗ θ` into `𝟙 ⊗ (baseChangeR b⁻¹ ≫ θ)`.  Both of those are tensorings of the
identity with a morphism, so the cancellation happens in the second variable of the bifunctor of
[stacks 0A63] alone.

**What is not done here.** `Dualizing.TensorComparisonCompatibility` is not proved and no tag
loses its conditional caveat.  What changes is that the keystone's second half is now an equation
whose factors are read at a K-flat complex: `μ'` by
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj`, the comparison across the square by
`Dualizing.tensorComparisonOfIso_app_q_obj`, and the base change of the algebra by
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single`.  One factor that is *not* a component
formula is `baseChangeR (𝟙 ⊗ b⁻¹)`, the image under base change of the resolution map tensored
into `X`; that is the price of the transport and it is named explicitly in the hypothesis of
`Dualizing.tensorComparisonCompatibility_of_kFlat_resolution`.

It is not the only one.  The first
factor of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is the projection formula over
`R` read in the *inverse* direction, and `Dualizing.tensorComparisonOfIso_app_q_obj` leaves it
alone precisely because nothing evaluates it there:
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` evaluates only `pf.hom`.
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonProjectionTail` moves that
factor across the equation, by cancelling the invertible prefix of the identity, and
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail` is the resulting form of the split — the
one in which every factor is read in a direction a component formula evaluates.

## Main results

* `Dualizing.tensorBaseChangeMor_comp_tensorComparison_eq_iff_of_iso` — **the comparison identity
  transported along an isomorphism of the algebra's class.**  Stated for an arbitrary
  isomorphism out of `Dualizing.derivedAlgebraSingle`, so that the K-flat resolution is only one
  instance of it.
* `Dualizing.tensorComparisonCompatibility_of_iso_resolution` — the split with the algebra's
  class replaced by any chosen isomorphic object, which is the form a consumer who picks the
  representative wants.
* `Dualizing.tensorComparisonCompatibility_of_kFlat_resolution` — **the split with the algebra
  resolved**: the obligation at every object of `D(R)` from the [stacks 068I] identification at
  pairs of K-flat complexes and the transported comparison identity, in which both variables of
  `μ'` are localizations of K-flat complexes.

## Implementation notes

`Dualizing.comp_eq_iff_eq_comp` is stated over a variable category and instantiated, following
`Stacks.CategoryTheory.BaseChange.eq_of_comp_tensorComparisonOfIso`: `CategoryTheory.cancel_mono`
is unusable here, since `IsIso` of a comparison across this square does not yield the `Mono`
instance that instance resolution asks for, and a cancellation written at the square makes the
unifier match two spellings of a long composite instead of computing the type from the arguments.

The reassociation of the transported composite is `Category.assoc` applied by hand rather than
`simp only [Category.assoc]`, which does not reassociate the composite that
`Dualizing.tensorBaseChangeMor_app_of_iso` produces.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

namespace Dualizing

universe uR uA uRp v w₁ w₂

/-- A morphism may be cancelled on the left against a two-sided inverse.  Stated over a variable
category and used at the derived category of `R'`-modules, following
`Stacks.CategoryTheory.BaseChange.eq_of_comp_tensorComparisonOfIso`: instantiating a generic
cancellation computes the type from the arguments, while stating it at the base-change square
makes the unifier match two spellings of a long composite. -/
private theorem comp_eq_iff_eq_comp {𝒞 : Type w₁} [Category.{w₂} 𝒞] {W W' Z : 𝒞}
    {t : W ⟶ W'} {t' : W' ⟶ W} (h1 : t' ≫ t = 𝟙 W') (h2 : t ≫ t' = 𝟙 W)
    {a : W' ⟶ Z} {u : W ⟶ Z} :
    t ≫ a = u ↔ a = t' ≫ u := by
  constructor
  · intro h
    rw [← h, ← Category.assoc, h1, Category.id_comp]
  · intro h
    rw [h, ← Category.assoc, h2, Category.id_comp]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hf hA hR hi in
/-- **The comparison identity transported along an isomorphism of the algebra's class.**  The
second half of the keystone's split — `μ'_{X, A[0]} ≫ tensorComparisonOfIso X = 𝟙 ⊗ θ`, the
equation `Dualizing.tensorComparisonCompatibility_iff_tensorBaseChangeMor` reduces the obligation
to — holds exactly when the same equation with `A[0]` replaced by any isomorphic object `P` holds,
the [stacks 068I] morphism being transported by `Dualizing.tensorBaseChangeMor_app_of_iso` and the
leftover factor `𝟙 ⊗ baseChangeR b` cancelled into the right-hand side.

Taking `P` to be the localization of a K-flat complex puts both variables of `μ'` in the range
where `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates it; that is
`Dualizing.tensorComparisonCompatibility_of_kFlat_resolution`.  Nothing is assumed of `P` here
beyond the isomorphism, so the same statement serves any other choice of representative. -/
theorem tensorBaseChangeMor_comp_tensorComparison_eq_iff_of_iso
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    {P : DerivedCategory (ModuleCat.{max v uR uA uRp} R)}
    (b : derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A) ≅ P) :
    (tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
            (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai)
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA) X =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj X),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom) :
            (baseChangeR.obj X,
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj X,
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom))) ↔
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X P ≫
          baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
                max v uR uA uRp + 1} R).tensor.map
              ((𝟙 X, b.inv) :
                (X, P) ⟶ (X, derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
            Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
              (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
                (algebraMap R A) Ff alphaf)
              (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
              (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                comparisonR Fi alphai)
              (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA) X =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj X),
              baseChangeR.map b.inv ≫
                (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom) :
            (baseChangeR.obj X, baseChangeR.obj P) ⟶
              (baseChangeR.obj X,
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) := by
  have ht := tensorBaseChangeMor_app_of_iso.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
    comparisonR D X b
  have hcomp : ∀ {Y B C E : DerivedCategory (ModuleCat.{max v uR uA uRp} R')}
      (f : B ⟶ C) (g : C ⟶ E),
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor.map ((𝟙 Y, f) : (Y, B) ⟶ (Y, C)) ≫
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor.map ((𝟙 Y, g) : (Y, C) ⟶ (Y, E)) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor.map ((𝟙 Y, f ≫ g) : (Y, B) ⟶ (Y, E)) := fun f g =>
    Eq.trans ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').tensor_map_comp _ _ _ _)
      (congrArg _ (Prod.ext (Category.comp_id _) rfl))
  have hid : ∀ {Y B C : DerivedCategory (ModuleCat.{max v uR uA uRp} R')}
      (f : B ⟶ C) (g : C ⟶ B), f ≫ g = 𝟙 B →
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor.map ((𝟙 Y, f) : (Y, B) ⟶ (Y, C)) ≫
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
          max v uR uA uRp + 1} R').tensor.map ((𝟙 Y, g) : (Y, C) ⟶ (Y, B)) = 𝟙 _ := by
    intro Y B C f g h
    rw [hcomp, h]
    exact (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').tensor_map_id _ _
  rw [ht]
  erw [Category.assoc, Category.assoc]
  have h1 : baseChangeR.map b.inv ≫ baseChangeR.map b.hom = 𝟙 _ := by
    rw [← baseChangeR.map_comp, b.inv_hom_id, baseChangeR.map_id]
  have h2 : baseChangeR.map b.hom ≫ baseChangeR.map b.inv = 𝟙 _ := by
    rw [← baseChangeR.map_comp, b.hom_inv_id, baseChangeR.map_id]
  refine (comp_eq_iff_eq_comp (hid _ _ h1) (hid _ _ h2)).trans ?_
  exact Iff.of_eq (congrArg _ (hcomp _ _))

include hf hA hR hi in
/-- **The split with the algebra's class replaced by a chosen isomorphic object.**  The obligation
holds at every object of `D(R)` as soon as the [stacks 068I] morphism is the lax monoidal structure
map at every pair of localizations of K-flat complexes, and the comparison identity transported
along one isomorphism `b : A[0] ≅ P` holds at the localization of every K-flat complex.

Nothing is assumed of `P`: this is
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` with its second hypothesis
replaced through `Dualizing.tensorBaseChangeMor_comp_tensorComparison_eq_iff_of_iso`, and the
K-flat resolution is the instance of it that matters
(`Dualizing.tensorComparisonCompatibility_of_kFlat_resolution`).  Stated with `b` given rather
than quantified, since a consumer proving the hypothesis chooses the representative. -/
theorem tensorComparisonCompatibility_of_iso_resolution
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    {P : DerivedCategory (ModuleCat.{max v uR uA uRp} R)}
    (b : derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A) ≅ P)
    (hmu : ∀ K L : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K → CochainComplex.KFlat.{uR, max v uA uRp} L →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (h : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D
            (DerivedCategory.Q.obj K) P ≫
          baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
                max v uR uA uRp + 1} R).tensor.map
              ((𝟙 (DerivedCategory.Q.obj K), b.inv) :
                (DerivedCategory.Q.obj K, P) ⟶
                  (DerivedCategory.Q.obj K,
                    derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
            Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
              (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
                (algebraMap R A) Ff alphaf)
              (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
              (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                comparisonR Fi alphai)
              (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA) (DerivedCategory.Q.obj K) =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj (DerivedCategory.Q.obj K)),
              baseChangeR.map b.inv ≫
                (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom) :
            (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj P) ⟶
              (baseChangeR.obj (DerivedCategory.Q.obj K),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X :=
  tensorComparisonCompatibility_of_tensorBaseChangeMor hTor baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai D hmu
    (fun K hK => (tensorBaseChangeMor_comp_tensorComparison_eq_iff_of_iso hTor baseChangeR
      comparisonR baseChangeA comparisonA Ff alphaf Fi alphai D
      (DerivedCategory.Q.obj K) b).mpr (h K hK)) X

include hf hA hR hi in
/-- **The split with the algebra resolved.**  `Dualizing.TensorComparisonCompatibility` holds at
every object of `D(R)` as soon as

* the [stacks 068I] morphism is the lax monoidal structure map at every pair of localizations of
  K-flat complexes of `R`-modules, and
* the transported comparison identity holds at the localization of every K-flat complex, for
  every K-flat complex `P` and isomorphism `A[0] ≅ Q P`.

This is `Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` with its second
hypothesis replaced through
`Dualizing.tensorBaseChangeMor_comp_tensorComparison_eq_iff_of_iso` at the resolution supplied by
`Dualizing.exists_kFlat_iso`.  The resolution is quantified over rather than fixed, since the
existence statement does not name one; a consumer proving the hypothesis has `P` K-flat and `b`
arbitrary, which is exactly the generality the chain-level evaluations need.

The factors of the second hypothesis are now read at K-flat complexes: the [stacks 068I] morphism
at `(Q K, Q P)` by `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`, the comparison across the square
at `Q K` by `Dualizing.tensorComparisonOfIso_app_q_obj`, and the base change of the algebra by
`Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single`.  The factor `baseChangeR (𝟙 ⊗ b⁻¹)` is the
base change of the resolution map tensored into `Q K`; it is the one thing the transport adds, and
it is the reason the hypothesis is not simply the comparison identity at a pair of K-flat classes.

The inverse projection formula over `R`, which the comparison across the square reads first, has
no component formula in that direction; `Dualizing.tensorComparisonCompatibility_of_kFlat_tail` is
this statement with that factor moved across the equation, and is the form in which a consumer
should discharge the hypothesis. -/
theorem tensorComparisonCompatibility_of_kFlat_resolution
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    (hmu : ∀ K L : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K → CochainComplex.KFlat.{uR, max v uA uRp} L →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (h : ∀ P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} P →
      ∀ b : derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A) ≅
          DerivedCategory.Q.obj P,
      ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D
            (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P) ≫
          baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
                max v uR uA uRp + 1} R).tensor.map
              ((𝟙 (DerivedCategory.Q.obj K), b.inv) :
                (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
                  (DerivedCategory.Q.obj K,
                    derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
            Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
              (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
                (algebraMap R A) Ff alphaf)
              (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
              (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
                comparisonR Fi alphai)
              (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA) (DerivedCategory.Q.obj K) =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj (DerivedCategory.Q.obj K)),
              baseChangeR.map b.inv ≫
                (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                  comparisonA hA).hom) :
            (baseChangeR.obj (DerivedCategory.Q.obj K),
                baseChangeR.obj (DerivedCategory.Q.obj P)) ⟶
              (baseChangeR.obj (DerivedCategory.Q.obj K),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X := by
  obtain ⟨P, hP, ⟨b⟩⟩ := exists_kFlat_iso.{uR, max v uA uRp}
    (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))
  exact tensorComparisonCompatibility_of_iso_resolution hTor baseChangeR comparisonR baseChangeA
    comparisonA Ff alphaf Fi alphai D b hmu (h P hP b) X

end Dualizing

end
