module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.Gluing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtaleCohomology

/-!
# The Mayer–Vietoris long exact sequence of a square that is an isomorphism off a closed set

Consider a cartesian square of schemes

```
E --j--> X'
|π       |b
v        v
Z --i--> X
```

with `i` a closed immersion, `c = π ≫ i = j ≫ b`, `b` an isomorphism over the open complement of
`Z`, and such that cohomology commutes with base change for `b`. For `K` bounded below in
`D(X_étale)` with torsion cohomology sheaves there is a long exact sequence

`H^p(X, K) ⟶ H^p(X', K|_{X'}) ⊕ H^p(Z, K|_Z) ⟶ H^p(E, K|_E) ⟶ H^{p+1}(X, K)`

whose first map is formed by the two restriction maps and whose second map is the difference of
the restriction maps to `E` (`K|_E = c⁻¹ K`, identified with `j⁻¹ b⁻¹ K` and with
`π⁻¹ i⁻¹ K`). For the blowup square of a quasi-coherent ideal of finite type this is Stacks Tag
0EW3.

## Main results

* `exists_longExactSequence_of_isPullback_of_cohomologyCommutesWithBaseChange`: the long exact
  sequence above.

## Implementation notes

Following the first proof of the source, the sequence is the long exact sequence of
`Hom(ℤ_X[-p], -)` applied to the Mayer–Vietoris triangle
`K ⟶ Ri_*(K|_Z) ⊕ Rb_*(K|_{X'}) ⟶ Rc_*(K|_E) ⟶ K[1]` of Stacks 0EW5
(`Stacks.EtaleCohomology.exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange`).
The identification `H^p(X, Rf_* N) ≅ H^p(Y, N)` of the source (Cohomology on Sites, Section
072X) is the adjunction `f⁻¹ ⊣ Rf_*`
(`Stacks.EtaleCohomology.etaleDerivedCohomologyDirectImageEquiv`); under it the units become the
restriction maps, and the two comparison maps into `Rc_*(K|_E)` become the restriction maps to
`E`, by the cocycle identity for the identifications `f⁻¹ ℤ_X[-p] ≅ ℤ_Y[-p]`
(`Stacks.EtaleCohomology.etaleConstantIntegersIso_comp`).

## References

* [Stacks Project, Tag 0EW3](https://stacks.math.columbia.edu/tag/0EW3)
* [Stacks Project, Tag 0EW5](https://stacks.math.columbia.edu/tag/0EW5)
* [Stacks Project, Tag 072X](https://stacks.math.columbia.edu/tag/072X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- A distinguished triangle gives an exact sequence of the groups of morphisms out of any fixed
object, at its second vertex. -/
private theorem exact_rightComp_of_distTriang {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [HasZeroObject 𝒞] [HasShift 𝒞 ℤ] [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]
    (T : Triangle 𝒞) (hT : T ∈ distTriang 𝒞) (A : 𝒞) :
    Function.Exact (Preadditive.rightComp A T.mor₁) (Preadditive.rightComp A T.mor₂) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ T hT y hy
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    simp [Preadditive.rightComp, comp_distTriang_mor_zero₁₂ T hT]

section CompDirectImageMap

variable {E Z X : Scheme.{u}} (π : E ⟶ Z) (i : Z ⟶ X) (c : E ⟶ X) (hc : c = π ≫ i)

/-- **Under `H^p(X, Rc_* N) ≅ H^p(E, N)`, the map induced by `w : π⁻¹ L ⟶ N` is restriction to
`E` followed by `w`.** For `c = π ≫ i` and a class of `H^p(X, Ri_* L) ≅ H^p(Z, L)`, composing
with `Ri_* L ⟶ Rc_* N` corresponds to restricting along `π` and composing with `w`. -/
public theorem etaleDerivedCohomologyDirectImageEquiv_comp_compDirectImageMap (p : ℤ)
    {L : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    {N : DerivedCategory (Sheaf E.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (w : etaleDerivedCohomology.{u, v} X p ((etaleAbelianDerivedDirectImage.{u, v} i).obj L))
    (t : (etaleAbelianDerivedInverseImage.{u, v} π).obj L ⟶ N) :
    etaleDerivedCohomologyDirectImageEquiv.{u, v} c p N
        (w ≫ etaleAbelianDerivedCompDirectImageMap.{u, v} π i c hc t) =
      etaleDerivedCohomologyRestriction.{u, v} π p L
        (etaleDerivedCohomologyDirectImageEquiv.{u, v} i p L w) ≫ t := by
  obtain ⟨w, rfl⟩ := ((etaleAbelianDerivedAdjunction.{u, v} i).homEquiv _ _).surjective w
  rw [homEquiv_comp_etaleAbelianDerivedCompDirectImageMap,
    etaleDerivedCohomologyDirectImageEquiv_apply, etaleDerivedCohomologyDirectImageEquiv_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, etaleDerivedCohomologyRestriction_apply,
    ← Category.assoc, etaleConstantIntegersIso_comp.{u, v} π i c hc p]
  simp

end CompDirectImageMap

section LongExactSequence

variable {X Z X' E : Scheme.{u}} (i : Z ⟶ X) (b : X' ⟶ X) (j : E ⟶ X') (π : E ⟶ Z)
  (c : E ⟶ X) (hcπ : c = π ≫ i) (hcj : c = j ≫ b)

/-- `H^p(X, Ri_* i⁻¹ K ⊕ Rb_* b⁻¹ K) ≅ H^p(X', b⁻¹ K) × H^p(Z, i⁻¹ K)`. -/
private def biprodEquiv (p : ℤ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    etaleDerivedCohomology.{u, v} X p
        ((etaleAbelianDerivedDirectImage.{u, v} i).obj
            ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) ⊞
          (etaleAbelianDerivedDirectImage.{u, v} b).obj
            ((etaleAbelianDerivedInverseImage.{u, v} b).obj K)) ≃+
      etaleDerivedCohomology.{u, v} X' p ((etaleAbelianDerivedInverseImage.{u, v} b).obj K) ×
        etaleDerivedCohomology.{u, v} Z p ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) :=
  AddEquiv.ofBijective
    (((etaleDerivedCohomologyDirectImageEquiv.{u, v} b p _).toAddMonoidHom.comp
        (Preadditive.rightComp _ biprod.snd)).prod
      ((etaleDerivedCohomologyDirectImageEquiv.{u, v} i p _).toAddMonoidHom.comp
        (Preadditive.rightComp _ biprod.fst))) (by
    refine ⟨fun w w' h ↦ ?_, fun x ↦ ?_⟩
    · simp only [AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddEquiv.coe_toAddMonoidHom, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
        Preadditive.rightComp] at h
      exact biprod.hom_ext _ _ h.2 h.1
    · refine ⟨biprod.lift ((etaleDerivedCohomologyDirectImageEquiv.{u, v} i p _).symm x.2)
        ((etaleDerivedCohomologyDirectImageEquiv.{u, v} b p _).symm x.1), ?_⟩
      simp [Preadditive.rightComp])

/-- The value of `biprodEquiv`, written out. -/
private theorem biprodEquiv_apply (p : ℤ)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (w : etaleDerivedCohomology.{u, v} X p
        ((etaleAbelianDerivedDirectImage.{u, v} i).obj
            ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) ⊞
          (etaleAbelianDerivedDirectImage.{u, v} b).obj
            ((etaleAbelianDerivedInverseImage.{u, v} b).obj K))) :
    biprodEquiv.{u, v} i b p K w =
      (etaleDerivedCohomologyDirectImageEquiv.{u, v} b p _ (w ≫ biprod.snd),
        etaleDerivedCohomologyDirectImageEquiv.{u, v} i p _ (w ≫ biprod.fst)) :=
  rfl

/-- Under `biprodEquiv`, the units become the two restriction maps. -/
private theorem biprodEquiv_units (p : ℤ)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (x : etaleDerivedCohomology.{u, v} X p K) :
    biprodEquiv.{u, v} i b p K (x ≫ etaleAbelianDerivedSquareUnits.{u, v} i b K) =
      (etaleDerivedCohomologyRestriction.{u, v} b p K x,
        etaleDerivedCohomologyRestriction.{u, v} i p K x) := by
  rw [biprodEquiv_apply, Category.assoc, Category.assoc, etaleAbelianDerivedSquareUnits,
    biprod.lift_snd, biprod.lift_fst, etaleDerivedCohomologyDirectImageEquiv_comp_unit,
    etaleDerivedCohomologyDirectImageEquiv_comp_unit]

/-- **Stacks 0EW3 for a square that is an isomorphism off a closed subscheme, granted that
cohomology commutes with base change for `b`.** Let
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
be a cartesian square of schemes with `i` a closed immersion and common composite `c`, let
`o : U ⟶ X` be an open immersion onto the complement of `Z`, with `b` an isomorphism over `U`
(the base change `bU` is invertible), and suppose cohomology commutes with base change for `b`.
For every bounded below `K` in `D(X_étale)` with torsion cohomology sheaves there is a long exact
sequence
`H^p(X, K) ⟶ H^p(X', K|_{X'}) × H^p(Z, K|_Z) ⟶ H^p(E, K|_E) ⟶ H^{p+1}(X, K) ⟶ ⋯`
whose first map is `x ↦ (x|_{X'}, x|_Z)` and whose second map is `(x', z) ↦ x'|_E - z|_E`, the
restrictions to `E` being read in `H^p(E, c⁻¹ K)` through `j⁻¹ b⁻¹ K ≅ c⁻¹ K ≅ π⁻¹ i⁻¹ K`. Here
`H^p(Y, M) = Hom(ℤ_Y[-p], M)` (`Stacks.EtaleCohomology.etaleDerivedCohomology`). -/
public theorem exists_longExactSequence_of_isPullback_of_cohomologyCommutesWithBaseChange
    [IsClosedImmersion i] {U U' : Scheme.{u}} (o : U ⟶ X) [IsOpenImmersion o]
    (hio : Set.range o.base = (Set.range i.base)ᶜ) (sq : IsPullback j π b i)
    (o' : U' ⟶ X') (bU : U' ⟶ U) (sqU : IsPullback o' bU b o) [IsIso bU]
    (hb : CohomologyCommutesWithBaseChange.{u, v} b)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (n : ℤ)
    (hK : K.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology K) :
    ∃ δ : ∀ p : ℤ, etaleDerivedCohomology.{u, v} E p
        ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) →+
      etaleDerivedCohomology.{u, v} X (p + 1) K,
    ∀ p : ℤ,
      Function.Exact
        (fun x : etaleDerivedCohomology.{u, v} X p K ↦
          (etaleDerivedCohomologyRestriction.{u, v} b p K x,
            etaleDerivedCohomologyRestriction.{u, v} i p K x))
        (fun y : etaleDerivedCohomology.{u, v} X' p
              ((etaleAbelianDerivedInverseImage.{u, v} b).obj K) ×
            etaleDerivedCohomology.{u, v} Z p ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) ↦
          etaleDerivedCohomologyRestriction.{u, v} j p _ y.1 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K -
            etaleDerivedCohomologyRestriction.{u, v} π p _ y.2 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).inv.app K) ∧
      Function.Exact
        (fun y : etaleDerivedCohomology.{u, v} X' p
              ((etaleAbelianDerivedInverseImage.{u, v} b).obj K) ×
            etaleDerivedCohomology.{u, v} Z p ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) ↦
          etaleDerivedCohomologyRestriction.{u, v} j p _ y.1 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K -
            etaleDerivedCohomologyRestriction.{u, v} π p _ y.2 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).inv.app K)
        (δ p) ∧
      Function.Exact (δ p)
        (fun x : etaleDerivedCohomology.{u, v} X (p + 1) K ↦
          (etaleDerivedCohomologyRestriction.{u, v} b (p + 1) K x,
            etaleDerivedCohomologyRestriction.{u, v} i (p + 1) K x)) := by
  obtain ⟨δT, hT'⟩ := exists_distTriang_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, v}
    i b j π c hcπ hcj o hio sq o' bU sqU hb K n hK hT
  -- the identification of the third vertex, negated so that the squares commute
  let eC : ∀ p : ℤ, etaleDerivedCohomology.{u, v} X p
      ((etaleAbelianDerivedDirectImage.{u, v} c).obj
        ((etaleAbelianDerivedInverseImage.{u, v} c).obj K)) ≃+
      etaleDerivedCohomology.{u, v} E p ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) :=
    fun p ↦ (etaleDerivedCohomologyDirectImageEquiv.{u, v} c p _).trans (AddEquiv.neg _)
  let δ : ∀ p : ℤ, etaleDerivedCohomology.{u, v} E p
      ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) →+
      etaleDerivedCohomology.{u, v} X (p + 1) K :=
    fun p ↦ (etaleDerivedCohomologyShiftEquiv.{u, v} X p K).toAddMonoidHom.comp
      ((Preadditive.rightComp _ δT).comp (eC p).symm.toAddMonoidHom)
  -- the difference of the restrictions to `E`
  let D (p : ℤ) : etaleDerivedCohomology.{u, v} X' p
          ((etaleAbelianDerivedInverseImage.{u, v} b).obj K) ×
        etaleDerivedCohomology.{u, v} Z p ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) →+
      etaleDerivedCohomology.{u, v} E p ((etaleAbelianDerivedInverseImage.{u, v} c).obj K) :=
    (Preadditive.rightComp _
          ((etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K)).comp
        ((etaleDerivedCohomologyRestriction.{u, v} j p _).comp (AddMonoidHom.fst _ _)) -
      (Preadditive.rightComp _
          ((etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).inv.app K)).comp
        ((etaleDerivedCohomologyRestriction.{u, v} π p _).comp (AddMonoidHom.snd _ _))
  have comm₂ : ∀ (p : ℤ) (w : etaleDerivedCohomology.{u, v} X p
        ((etaleAbelianDerivedDirectImage.{u, v} i).obj
            ((etaleAbelianDerivedInverseImage.{u, v} i).obj K) ⊞
          (etaleAbelianDerivedDirectImage.{u, v} b).obj
            ((etaleAbelianDerivedInverseImage.{u, v} b).obj K))),
      etaleDerivedCohomologyRestriction.{u, v} j p _ (biprodEquiv.{u, v} i b p K w).1 ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} j b c hcj).inv.app K -
        etaleDerivedCohomologyRestriction.{u, v} π p _ (biprodEquiv.{u, v} i b p K w).2 ≫
          (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hcπ).inv.app K =
      eC p (w ≫ etaleAbelianDerivedSquareDifference.{u, v} i b j π c hcπ hcj K) := by
    intro p w
    simp only [biprodEquiv_apply, eC, AddEquiv.trans_apply, AddEquiv.neg_apply,
      etaleAbelianDerivedSquareDifference, biprod.desc_eq, Preadditive.comp_add,
      Preadditive.comp_neg, map_add, map_neg, ← Category.assoc,
      etaleAbelianDerivedUnitCompMap_app_eq_compDirectImageMap]
    rw [etaleDerivedCohomologyDirectImageEquiv_comp_compDirectImageMap.{u, v} π i c hcπ,
      etaleDerivedCohomologyDirectImageEquiv_comp_compDirectImageMap.{u, v} j b c hcj]
    abel
  refine ⟨δ, fun p ↦ ⟨?_, ?_, ?_⟩⟩
  · exact (Function.Exact.iff_of_ladder_addEquiv (AddEquiv.refl _) (biprodEquiv.{u, v} i b p K)
      (eC p) (g₁₂ := (etaleDerivedCohomologyRestriction.{u, v} b p K).prod
        (etaleDerivedCohomologyRestriction.{u, v} i p K))
      (g₂₃ := D p)
      (f₁₂ := Preadditive.rightComp _ (etaleAbelianDerivedSquareUnits.{u, v} i b K))
      (f₂₃ := Preadditive.rightComp _
        (etaleAbelianDerivedSquareDifference.{u, v} i b j π c hcπ hcj K))
      (AddMonoidHom.ext fun x ↦ (biprodEquiv_units.{u, v} i b p x).symm)
      (AddMonoidHom.ext fun w ↦ comm₂ p w)).2
      (exact_rightComp_of_distTriang _ hT' _)
  · exact (Function.Exact.iff_of_ladder_addEquiv (biprodEquiv.{u, v} i b p K) (eC p)
      (etaleDerivedCohomologyShiftEquiv.{u, v} X p K)
      (g₁₂ := D p)
      (g₂₃ := δ p)
      (f₁₂ := Preadditive.rightComp _
        (etaleAbelianDerivedSquareDifference.{u, v} i b j π c hcπ hcj K))
      (f₂₃ := Preadditive.rightComp _ δT)
      (AddMonoidHom.ext fun w ↦ comm₂ p w)
      (AddMonoidHom.ext fun w ↦ by simp [δ])).2
      (exact_rightComp_of_distTriang _ (rot_of_distTriang _ hT') _)
  · exact (Function.Exact.iff_of_ladder_addEquiv (eC p)
      (etaleDerivedCohomologyShiftEquiv.{u, v} X p K)
      (((etaleDerivedCohomologyShiftEquiv.{u, v} X p _).trans
        (biprodEquiv.{u, v} i b (p + 1) K)).trans (AddEquiv.neg _))
      (g₁₂ := δ p)
      (g₂₃ := (etaleDerivedCohomologyRestriction.{u, v} b (p + 1) K).prod
        (etaleDerivedCohomologyRestriction.{u, v} i (p + 1) K))
      (f₁₂ := Preadditive.rightComp _ δT)
      (f₂₃ := Preadditive.rightComp _ (-(etaleAbelianDerivedSquareUnits.{u, v} i b K)⟦(1 : ℤ)⟧'))
      (AddMonoidHom.ext fun w ↦ by simp [δ])
      (AddMonoidHom.ext fun y ↦ by
        have h := biprodEquiv_units.{u, v} i b (p + 1)
          (etaleDerivedCohomologyShiftEquiv.{u, v} X p K y)
        rw [← etaleDerivedCohomologyShiftEquiv_comp] at h
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.trans_apply,
          AddEquiv.neg_apply, Preadditive.rightComp, AddMonoidHom.mk'_apply,
          Preadditive.comp_neg, map_neg, neg_neg, AddMonoidHom.prod_apply, AddMonoidHom.coe_coe]
        rw [h])).2
      (exact_rightComp_of_distTriang _ (rot_of_distTriang _ (rot_of_distTriang _ hT')) _)

end LongExactSequence

end Stacks.EtaleCohomology

end
