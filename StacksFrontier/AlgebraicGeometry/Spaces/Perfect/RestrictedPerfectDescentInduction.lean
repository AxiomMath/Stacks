module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineStagesPerfectHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPerfectHomDescent

/-!
# The induction of Stacks 08GP in the proof of Stacks 09RJ

The proof of Stacks 09RJ considers, for every quasi-compact and quasi-separated object `U₀` of
`(X₀)_{spaces,étale}`, the condition that
`colim_{i ≥ 0} D_perf(𝒪_{U_i}) ⟶ D_perf(𝒪_U)` is an equivalence, where `U = X ×_{X₀} U₀` and
`U_i = X_i ×_{X₀} U₀`, and proves it for every `U₀` by the induction principle of Stacks 08GP.
This file runs that induction: the affine case is
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_restrictTo_of_isAffineSpace`
(essential surjectivity) and
`AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_restrictTo_of_isAffineSpace` (full
faithfulness), and the last step is
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_of_restrictTo_id`. The two halves
of the step across an elementary distinguished square are the arguments `hobj` and `hhom` of the
main result; each is stated in exactly the shape the induction principle asks for. In the form for
restrictions of the situation, the full faithfulness half is the Mayer–Vietoris step
`Space.DescentSituation.perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare`, so only
the essential surjectivity half remains an argument.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.RestrictedObjectsDescend`: perfect objects descend
  for the restriction of the situation to `U₀`.
* `AlgebraicGeometry.Space.DescentSituation.RestrictedHomsDescend`: morphisms of perfect objects
  descend for the restriction of the situation to `U₀`.

## Main results

* `Space.DescentSituation.perfectObjectsDescend_of_isElementaryDistinguishedSquare`:
  perfect objects descend in a situation with bounded charts, given the two halves of the step
  across an elementary distinguished square.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Perfect objects descend for the restriction of Situation 09RH to `U₀`**: for every
structure of a quasi-compact quasi-separated algebraic space on `U₀`, every perfect object on
`X ×_{X₀} U₀` is the derived pullback of a perfect object on some `X_i ×_{X₀} U₀`. The structure
is quantified over so that this is a property of the morphism `u : U₀ ⟶ X₀` alone, which is the
shape the induction principle of Stacks 08GP takes. -/
def RestrictedObjectsDescend {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (u : U₀ ⟶ D.system.obj (op D.base)) : Prop :=
  ∀ (hU₀ : IsAlgebraicSpace B S hS U₀) (hU₀qc : IsQuasiCompactSpace B S hS U₀)
    (hU₀qs : IsAbsolutelyQuasiSeparated B S hS hZ U₀),
    (D.restrictTo hU₀ hU₀qc hU₀qs u).PerfectObjectsDescend

/-- **Morphisms of perfect objects descend for the restriction of Situation 09RH to `U₀`**, for
every structure of a quasi-compact quasi-separated algebraic space on `U₀`
(`AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend` for the restricted situation). -/
def RestrictedHomsDescend {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (u : U₀ ⟶ D.system.obj (op D.base)) : Prop :=
  ∀ (hU₀ : IsAlgebraicSpace B S hS U₀) (hU₀qc : IsQuasiCompactSpace B S hS U₀)
    (hU₀qs : IsAbsolutelyQuasiSeparated B S hS hZ U₀),
    (D.restrictTo hU₀ hU₀qc hU₀qs u).PerfectHomsDescend

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The induction of Stacks 08GP in the proof of Stacks 09RJ.** In Situation 09RH with bounded
charts, perfect objects on the limit descend to a stage, provided the property "perfect objects
and their morphisms descend for the restriction to `U₀`" passes across every elementary
distinguished square `(U ⊆ W, V ⟶ W)` of quasi-compact quasi-separated objects of
`(X₀)_{spaces,étale}` with affine `V`: `hobj` is the essential surjectivity half of the step
(it may use full faithfulness on the intersection) and `hhom` the full faithfulness half. The
affine case is the affine case of Stacks 09RI–09RJ proved in
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_restrictTo_of_isAffineSpace` and
`AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_restrictTo_of_isAffineSpace`. -/
theorem perfectObjectsDescend_of_isElementaryDistinguishedSquare
    (hb : ChartsBounded B S hS D.system)
    (hobj : ∀ (W V : SpacesEtale B S hS ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
      (U : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      D.RestrictedObjectsDescend (U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend V.1.hom.hom →
      D.RestrictedHomsDescend (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend W.1.hom.hom)
    (hhom : ∀ (W V : SpacesEtale B S hS ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
      (U : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      D.RestrictedHomsDescend (U.ι ≫ W.1.hom.hom) →
      D.RestrictedHomsDescend V.1.hom.hom →
      D.RestrictedHomsDescend (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      D.RestrictedHomsDescend W.1.hom.hom) :
    D.PerfectObjectsDescend := by
  have h := qcqs_induction_on_self B S hS hZ
    ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩ (D.quasiCompact D.base)
    (D.quasiSeparated D.base)
    (fun _ y => D.RestrictedObjectsDescend y ∧ D.RestrictedHomsDescend y)
    (fun V hV => ⟨fun hU₀ hU₀qc hU₀qs =>
        D.perfectObjectsDescend_restrictTo_of_isAffineSpace hU₀ hU₀qc hU₀qs _ hb hV,
      fun hU₀ hU₀qc hU₀qs =>
        D.perfectHomsDescend_restrictTo_of_isAffineSpace hU₀ hU₀qc hU₀qs _ hb hV⟩)
    (fun W V U f hf hsq hWqc hWqs hUqc hVaff hU hV hP =>
      ⟨hobj W V U f hf hsq hWqc hWqs hUqc hVaff hU.1 hV.1 hP.2,
        hhom W V U f hf hsq hWqc hWqs hUqc hVaff hU.2 hV.2 hP.2⟩)
  exact D.perfectObjectsDescend_of_restrictTo_id
    (h.1 (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base))

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The induction of Stacks 08GP in the proof of Stacks 09RJ**, with the full faithfulness half
of the step across an elementary distinguished square `(U ⊆ W₀, f : V₀ ⟶ W₀)` discharged by the
Mayer–Vietoris step `perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare`: perfect
objects on the limit descend to a stage once the essential surjectivity half `hobj` of the step
holds. The side conditions that `U`, `V₀` and `U ×_{W₀} V₀` are quasi-compact quasi-separated
algebraic spaces hold in the induction: `U` is open in the quasi-separated `W₀`, `V₀` is affine,
and `U ×_{W₀} V₀` is quasi-compact by Stacks 073B. -/
theorem perfectObjectsDescend_of_restrictTo_isElementaryDistinguishedSquare
    (hb : ChartsBounded B S hS D.system)
    (hobj : ∀ (W V : SpacesEtale B S hS ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
      (U : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      D.RestrictedObjectsDescend (U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend V.1.hom.hom →
      D.RestrictedHomsDescend (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend W.1.hom.hom) :
    D.PerfectObjectsDescend := by
  refine D.perfectObjectsDescend_of_isElementaryDistinguishedSquare hb hobj ?_
  intro W V U f hf hsq hWqc hWqs hUqc hVaff hFU hFV hFP hW' hWqc' hWqs'
  have hUa : IsAlgebraicSpace B S hS U.toFunctor := hsq.isOpenSubspace.1
  have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.toFunctor :=
    isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hWqs U hUa
  have hVqc : IsQuasiCompactSpace B S hS V.1.left.1 := hVaff.isQuasiCompactSpace
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.1.left.1 :=
    isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVaff
  have hPa : IsAlgebraicSpace B S hS (pullback U.ι f) :=
    isAlgebraicSpace_pullback B S hS U.ι f hUa hsq.isAlgebraicSpace W.1.left.property
  have hPqc : IsQuasiCompactSpace B S hS (pullback U.ι f) :=
    isQuasiCompactSpace_pullback B S hS hZ U.ι f hUa W.1.left.property hUqc hVqc hWqs
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback U.ι f) :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ U.ι f hUa hsq.isAlgebraicSpace
      W.1.left.property hUqs hVqs
  have hFV' := hFV hsq.isAlgebraicSpace hVqc hVqs
  rw [← hf] at hFV'
  exact D.perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare hW' hWqc' hWqs'
    W.1.hom.hom U f hsq hUa hUqc hUqs hVqc hVqs hPa hPqc hPqs (hFU hUa hUqc hUqs) hFV'
    (hFP hPa hPqc hPqs)

end AlgebraicGeometry.Space.DescentSituation

end
