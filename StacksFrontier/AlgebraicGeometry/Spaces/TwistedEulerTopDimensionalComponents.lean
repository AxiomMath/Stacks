module

public import StacksFrontier.AlgebraicGeometry.Spaces.EulerCharacteristicAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseObjectNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.TopDimensionalComponentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerNumericalPolynomialProper

/-!
# Twisted Euler characteristics and the top-dimensional components of the support

Let `X` be a proper algebraic space over a field `k`, `F` a coherent `𝒪_X`-module and
`L₁, …, L_r` invertible `𝒪_X`-modules.  Let `d = dim Supp(F)`, let `Z_C` be the reduced closed
subspaces on the irreducible components `C` of `Supp(F)` of dimension `d` and `m_C` the length of
`F` at a geometric generic point of `C`.  Stacks 0EDE says that

`χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}) - ∑_C m_C χ(Z_C, (L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})|_{Z_C})`

is a numerical polynomial in `n₁, …, n_r` of total degree `< d`.

## The route

The dévissage is `AlgebraicGeometry.Space.exists_polynomial_sub_finsum_toNat_geometricLength_mul`
(`StacksFrontier/AlgebraicGeometry/Spaces/TopDimensionalComponentDevissage.lean`), which runs
Stacks 07UR and 07US for any function `χ` of modules that is additive on short exact sequences of
coherent modules and polynomial of total degree at most the dimension of the support on each
coherent module.  Here `χ` is the twisted Euler characteristic:

* additivity is Stacks 0DN2 at the twisted sequences,
  `AlgebraicGeometry.Space.hasAdditiveTwistedEulerOnCoherent_of_isProper`;
* the polynomial bound is Stacks 0DN4 on the scheme-theoretic support,
  `AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport`,
  whose bound, the dimension of the scheme-theoretic support, is at most `dim Supp(F)`
  (`AlgebraicGeometry.Space.dimension_coherentSchemeTheoreticSupport_le`: Stacks 0A4J on the
  decent closed subspace, and part (4) of Stacks 07U0).

This gives the statement with `χ(X, i_{C,*}𝒪_{Z_C} ⊗ L^{⊗ n})` in place of
`χ(Z_C, L^{⊗ n}|_{Z_C})`, for any closed set `T ⊇ Supp(F)` in place of `Supp(F)`
(`AlgebraicGeometry.Space.exists_twistedEuler_sub_finsum_mul_componentStructureSheaf`).  The two
Euler characteristics agree along the closed immersion `Z_C → X`, by
`eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion` in the namespace
`AlgebraicGeometry.Space`.

## Main results

* `AlgebraicGeometry.Space.exists_representsTwistedEuler_of_isCoherent`: Stacks 0DN4 with the
  bound `dim Supp(F)`.
* `AlgebraicGeometry.Space.exists_twistedEuler_sub_finsum_mul_componentStructureSheaf`: the
  statement over any closed set of points containing the support, with the direct images
  `i_{C,*}𝒪_{Z_C}` on `X`.
* `exists_twistedEuler_sub_finsum_mul_twistedEuler_topDimensionalComponent`, in the namespace
  `AlgebraicGeometry.Space`: **Stacks 0EDE.**

## Implementation notes

"Numerical polynomial of total degree `< d`" is read as a rational polynomial in `n₁, …, n_r`
which takes the given values at all integral tuples and is zero or of total degree `< d`; a
rational polynomial with integral values at the integral tuples is numerical.  The geometric
generic points `x̄_C` are arbitrary: the statement holds for every choice.  The restriction
`(L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})|_{Z_C}` is the twist of `𝒪_{Z_C}` by the inverse images of the
`L_j`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk) {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]

include hf in
/-- The direct image of the structure sheaf of the reduced closed subspace on an irreducible
component of a closed set of points of a proper algebraic space over a field is coherent. -/
theorem isCoherent_componentStructureSheaf {T : Set (points B (Spec (.of k)) hk X.1)}
    (hT : IsClosed T) (C : irreducibleComponents T) :
    IsCoherent B (Spec (.of k)) hk X.1 X.2 (componentStructureSheaf B (Spec (.of k)) hk X hT C) :=
  isCoherent_structureSheafPushforward B (Spec (.of k)) hk
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) _
    (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
      (closedSetComponentPoints B (Spec (.of k)) hk T hT C).isClosed).2

open scoped Classical in
/-- The twisted Euler characteristics, extended by zero off the coherent modules. -/
private def twistedEulerOnCoherent (H : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (n : Fin r → ℤ) : ℚ :=
  if hH : IsCoherent B (Spec (.of k)) hk X.1 X.2 H then
    (@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 H L n)
      (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L H hH n) : ℚ)
  else 0

include hf in
/-- **The scheme-theoretic support of a coherent module on a proper algebraic space over a field
has dimension at most that of the support.**  The scheme-theoretic support `Z` is proper over `k`,
hence decent, so its dimension is the Krull dimension of `|Z|` (Stacks 0A4J); and `|Z| → |X|` is a
closed embedding with image `Supp(F)` (part (4) of Stacks 07U0). -/
theorem dimension_coherentSchemeTheoreticSupport_le (H : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [IsCoherent B (Spec (.of k)) hk X.1 X.2 H] :
    dimension B (Spec (.of k)) hk
        (closedSubspaceToSpace B (Spec (.of k)) hk X
          (coherentSchemeTheoreticSupport B (Spec (.of k)) hk X H)).1
        (closedSubspaceToSpace B (Spec (.of k)) hk X
          (coherentSchemeTheoreticSupport B (Spec (.of k)) hk X H)).2 ≤
      topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk X H) := by
  set Zc := coherentSchemeTheoreticSupport B (Spec (.of k)) hk X H
  set Z := closedSubspaceToSpace B (Spec (.of k)) hk X Zc
  let i := closedSubspaceInclusion B (Spec (.of k)) hk X Zc
  have hi : IsClosedImmersion B (Spec (.of k)) hk i.hom := Zc.2.2
  have hfZ : IsProper B (Spec (.of k)) hk (i.hom ≫ f) :=
    isProper_comp B (Spec (.of k)) hk Z.2 X.2
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
      (isProper_of_isClosedImmersion B (Spec (.of k)) hk Z.2 X.2 i.hom hi) hf
  have hdec := isDecentSpace_of_isProper_baseObject k B hk Z.1 Z.2 (i.hom ≫ f) hfZ
  rw [← topologicalKrullDim_points_eq_dimension_of_isDecentSpace B (Spec (.of k)) hk Z.2 hdec]
  have hft : SheafOfModules.IsFiniteTypeOnSite H :=
    isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of k)) hk X H
  have hpts := supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B (Spec (.of k)) hk X H
    inferInstance hft
  have hemb : IsEmbedding (pointsMap B (Spec (.of k)) hk Z.1 i.hom) :=
    (isClosedEmbedding_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 hi).isEmbedding
  have hmem : ∀ p, pointsMap B (Spec (.of k)) hk Z.1 i.hom p ∈
      moduleSupportSet B (Spec (.of k)) hk X H := fun p => by
    show _ ∈ supportOfSheaf B (Spec (.of k)) hk X.1 _
    rw [hpts]
    exact ⟨p, rfl⟩
  exact (hemb.codRestrict _ hmem).isInducing.topologicalKrullDim_le

/-- **Stacks 0DN4 with the bound `dim Supp(F)`**: the twisted Euler characteristics of a
coherent module are given by a rational polynomial which is zero or of total degree at most the
Krull dimension of the support.  This is
`AlgebraicGeometry.Space.hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport` and
`AlgebraicGeometry.Space.dimension_coherentSchemeTheoreticSupport_le`. -/
theorem exists_representsTwistedEuler_of_isCoherent (H : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hH : IsCoherent B (Spec (.of k)) hk X.1 X.2 H) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      @RepresentsTwistedEuler.{u, w} k _ B hk X r f hf H L _
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L H hH) P ∧
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk X H)) := by
  have := hH
  obtain ⟨P, hP, hdeg⟩ :=
    hasTwistedEulerPolynomialOfDegreeLE_coherentSchemeTheoreticSupport.{u, w} k B hk X f hf H L
  exact ⟨P, hP, hdeg.imp_right fun h =>
    h.trans (dimension_coherentSchemeTheoreticSupport_le k B hk X f hf H)⟩

/-- **Stacks 0EDE with the direct images of the components, over any closed set containing the
support.**  Let `T ⊆ |X|` be closed with `Supp(F) ⊆ T` and let `x̄_C` be a geometric point over
the generic point of each irreducible component `C` of `T`.  Then
`χ(X, F ⊗ L^{⊗ n}) - ∑_C length(F_{x̄_C}) χ(X, i_{C,*}𝒪_{Z_C} ⊗ L^{⊗ n})`, the sum over the
components of dimension `dim T`, is given by a rational polynomial which is zero or of total degree
`< dim T`. -/
theorem exists_twistedEuler_sub_finsum_mul_componentStructureSheaf
    {T : Set (points B (Spec (.of k)) hk X.1)} (hT : IsClosed T)
    (x : irreducibleComponents T → GeometricPoint B (Spec (.of k)) hk X.1)
    (hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)))
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (hFT : moduleSupportSet B (Spec (.of k)) hk X F ⊆ T) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) < topologicalKrullDim T) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        (@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)
          (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF n) : ℚ) -
        ∑ᶠ C ∈ {C : irreducibleComponents T |
            topologicalKrullDim (Subtype.val '' (C : Set T)) = topologicalKrullDim T},
          ((geometricLength B (Spec (.of k)) hk X (x C) F).toNat : ℚ) *
            (@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
              (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
                (componentStructureSheaf B (Spec (.of k)) hk X hT C) L n)
              (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _
                (isCoherent_componentStructureSheaf k B hk X f hf hT C) n) : ℚ) := by
  obtain ⟨P, hP, hval⟩ := exists_polynomial_sub_finsum_toNat_geometricLength_mul B (Spec (.of k)) hk
    X (isNoetherian_of_isProper_baseObject k B hk X.1 X.2 f hf) hT x hx
    (twistedEulerOnCoherent.{u, w} k B hk X f hf L)
    (fun σ hσ h₁ h₂ h₃ n => by
      simp only [twistedEulerOnCoherent, dite_eq_left h₁, dite_eq_left h₂, dite_eq_left h₃]
      exact_mod_cast hasAdditiveTwistedEulerOnCoherent_of_isProper.{u, w} k B hk X f hf L σ hσ
        h₁ h₂ h₃ n)
    (fun H hH => by
      obtain ⟨P, hP, hdeg⟩ := exists_representsTwistedEuler_of_isCoherent.{u, w} k B hk X f hf L H
          hH
      exact ⟨P, fun n => by rw [hP n, twistedEulerOnCoherent, dite_eq_left hH], hdeg⟩)
    F hF hFT
  refine ⟨P, hP, fun n => ?_⟩
  rw [hval n, twistedEulerOnCoherent, dite_eq_left hF]
  congr 1
  refine finsum_mem_congr rfl fun C _ => ?_
  rw [twistedEulerOnCoherent, dite_eq_left (isCoherent_componentStructureSheaf k B hk X f hf hT C)]

/-- **Stacks 0EDE.**  Let `X` be proper over a field `k`, `F` a coherent `𝒪_X`-module and
`L₁, …, L_r` invertible `𝒪_X`-modules.  Let `Z_C` be the reduced closed subspace on an
irreducible component `C` of `Supp(F)` of dimension `d = dim Supp(F)`, `x̄_C` a geometric generic
point of `C` and `m_C = length_{𝒪_{X, x̄_C}}(F_{x̄_C})`.  Then
`χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}) - ∑_C m_C χ(Z_C, (L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})|_{Z_C})`
is given by a rational polynomial in `n₁, …, n_r` which is zero or of total degree `< d`. -/
@[stacks 0EDE]
theorem exists_twistedEuler_sub_finsum_mul_twistedEuler_topDimensionalComponent
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    (x : irreducibleComponents (moduleSupportSet B (Spec (.of k)) hk X F) → GeometricPoint B (Spec
        (.of k)) hk X.1)
    (hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set (moduleSupportSet B (Spec
        (.of k)) hk X F)))) :
    have hT : IsClosed (moduleSupportSet B (Spec (.of k)) hk X F) := isClosed_moduleSupportSet B
        (Spec (.of k)) hk X F hF
    have hW : ∀ C : irreducibleComponents (moduleSupportSet B (Spec (.of k)) hk X F),
        IsClosedSubspace B (Spec (.of k)) hk (reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
          (closedSetComponentPoints B (Spec (.of k)) hk (moduleSupportSet B (Spec
              (.of k)) hk X F) hT C).isClosed) := fun C =>
      isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
        (closedSetComponentPoints B (Spec (.of k)) hk (moduleSupportSet B (Spec
            (.of k)) hk X F) hT C).isClosed
    have hfZ : ∀ C : irreducibleComponents (moduleSupportSet B (Spec (.of k)) hk X F),
        IsProper B (Spec (.of k)) hk ((closedSubfunctorι B (Spec (.of k)) hk (hW C)).hom ≫ f) :=
      fun C => isProper_comp B (Spec (.of k)) hk (hW C).1 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) _ f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk (hW C).1 X.2 _ (hW C).2) hf
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) < topologicalKrullDim (moduleSupportSet B (Spec
          (.of k)) hk X F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        (@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 F L n)
          (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L F hF n) : ℚ) -
        ∑ᶠ C ∈ {C : irreducibleComponents (moduleSupportSet B (Spec (.of k)) hk X F) |
            topologicalKrullDim (Subtype.val '' (C : Set (moduleSupportSet B (Spec
                (.of k)) hk X F))) = topologicalKrullDim (moduleSupportSet B (Spec
                    (.of k)) hk X F)},
          haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk
            (closedSubfunctorι B (Spec (.of k)) hk (hW C)) (L j)
          ((geometricLength B (Spec (.of k)) hk X (x C) F).toNat : ℚ) *
            (@eulerCharacteristic.{u, w} k _ B hk (closedSubfunctorSpace B (Spec (.of k)) hk
                (hW C)).1
              (closedSubfunctorSpace B (Spec (.of k)) hk (hW C)).2
              ((closedSubfunctorι B (Spec (.of k)) hk (hW C)).hom ≫ f) (hfZ C)
              (twistedModuleUlift.{u, w} B (Spec (.of k)) hk
                (closedSubfunctorSpace B (Spec (.of k)) hk (hW C)).1
                (closedSubfunctorSpace B (Spec (.of k)) hk (hW C)).2
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedSite B (Spec (.of k)) hk
                    (closedSubfunctorSpace B (Spec (.of k)) hk (hW C)).1
                    (closedSubfunctorSpace B (Spec (.of k)) hk (hW C)).2).O))
                (fun j => (modulePullback B (Spec (.of k)) hk
                  (closedSubfunctorι B (Spec (.of k)) hk (hW C))).obj (L j)) n)
              (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk
                (closedSubfunctorSpace B (Spec (.of k)) hk (hW C))
                ((closedSubfunctorι B (Spec (.of k)) hk (hW C)).hom ≫ f) (hfZ C) _ _
                (isCoherent_unit_of_isClosedImmersion k B hk X
                  (closedSubfunctorSpace B (Spec (.of k)) hk (hW C)) f hf
                  (closedSubfunctorι B (Spec (.of k)) hk (hW C)) (hW C).2) n) : ℚ) := by
  intro hT hW hfZ
  obtain ⟨P, hP, hval⟩ := exists_twistedEuler_sub_finsum_mul_componentStructureSheaf.{u, w}
    k B hk X f hf L hT x hx F hF subset_rfl
  refine ⟨P, hP, fun n => ?_⟩
  rw [hval n]
  congr 1
  refine finsum_mem_congr rfl fun C _ => ?_
  congr 1
  exact congrArg (fun z : ℤ => (z : ℚ))
    (eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion.{u, w} k B hk f
        hf
      (closedSubfunctorι B (Spec (.of k)) hk (hW C)) (hW C).2 _
      (isCoherent_unit_of_isClosedImmersion k B hk X
        (closedSubfunctorSpace B (Spec (.of k)) hk (hW C)) f hf
        (closedSubfunctorι B (Spec (.of k)) hk (hW C)) (hW C).2) L n)

end AlgebraicGeometry.Space
