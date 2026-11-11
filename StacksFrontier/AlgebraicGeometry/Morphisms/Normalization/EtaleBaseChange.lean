module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.IrreducibleComponents

/-!
# Normalization commutes with étale base change

Let `φ : X ⟶ Y` be an étale morphism of schemes and assume every quasi-compact open of `Y` has
finitely many irreducible components. Then the same holds for `X`, and the square

```
X^ν ⟶ Y^ν
 |      |
 v      v
 X  ⟶  Y
```

formed by the normalization morphisms and the morphism of normalizations induced by `φ` is
cartesian: `X^ν` is the base change `X ×_Y Y^ν`.

## Main results

* `AlgebraicGeometry.mem_genericPoints_of_etale`: a point of the source of an étale morphism
  lying over a generic point of an irreducible component is itself such a generic point.
* `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale`: the normalization square of
  an étale morphism is cartesian, that is, `X^ν = X ×_Y Y^ν`.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 034F](https://stacks.math.columbia.edu/tag/034F)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
* [Stacks Project, Tag 0BAH](https://stacks.math.columbia.edu/tag/0BAH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of the source of an étale morphism which lies over a generic point of an irreducible
component of the target is a generic point of an irreducible component of the source. -/
theorem mem_genericPoints_of_etale {X Y : Scheme.{u}} (φ : X ⟶ Y) [Etale φ]
    {x : X} (hx : φ x ∈ genericPoints Y) : x ∈ genericPoints X := by
  have hsub : ⇑φ ⁻¹' {φ x} ⊆ genericPoints X :=
    ((quasiFiniteAt_over_genericPoint_tfae φ (φ x) hx).out 2 1).mp fun z _ ↦
      (forall_quasiFiniteAt_iff φ).2 (locallyQuasiFinite_of_etale φ) z
  exact hsub rfl

section

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) [Etale φ]
  (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)

/-- The projection of the base change of the normalization morphism of `Y` along an étale morphism
`φ : X ⟶ Y` onto the normalization of `Y` is étale. -/
private theorem etale_pullback_fst_normalization :
    Etale (pullback.fst (Y.normalization hY) φ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
    (IsPullback.of_hasPullback (Y.normalization hY) φ).flip inferInstance

/-- The base change `X ×_Y Y^ν` of the normalization morphism of `Y` along an étale morphism
`φ : X ⟶ Y` is a normal scheme. -/
private theorem isNormal_pullback_normalization :
    IsNormal (pullback (Y.normalization hY) φ) := by
  have := Scheme.isNormal_normalizationScheme Y hY
  have := etale_pullback_fst_normalization φ hY
  exact isNormal_of_etale (pullback.fst (Y.normalization hY) φ)

/-- A generic point of an irreducible component of `X ×_Y Y^ν` is carried to a generic point of
an irreducible component of `Y^ν` by the first projection. -/
private theorem mem_genericPoints_pullback_fst
    {z : ↥(pullback (Y.normalization hY) φ)}
    (hz : z ∈ genericPoints ↥(pullback (Y.normalization hY) φ)) :
    pullback.fst (Y.normalization hY) φ z ∈ genericPoints (Y.normalizationScheme hY) := by
  have := etale_pullback_fst_normalization φ hY
  exact (pullback.fst (Y.normalization hY) φ).mem_genericPoints_of_flat hz

/-- A generic point of an irreducible component of `X ×_Y Y^ν` is carried to a generic point of
an irreducible component of `Y` by the composite of the first projection with the normalization
morphism of `Y`. -/
private theorem mem_genericPoints_pullback_fst_normalization
    {z : ↥(pullback (Y.normalization hY) φ)}
    (hz : z ∈ genericPoints ↥(pullback (Y.normalization hY) φ)) :
    (pullback.fst (Y.normalization hY) φ ≫ Y.normalization hY) z ∈ genericPoints Y := by
  rw [Scheme.Hom.comp_apply]
  exact Scheme.normalization_mem_genericPoints Y hY (mem_genericPoints_pullback_fst φ hY hz)

/-- A generic point of an irreducible component of `X ×_Y Y^ν` is carried to a generic point of an
irreducible component of `X` by the second projection. -/
private theorem mem_genericPoints_pullback_snd
    {z : ↥(pullback (Y.normalization hY) φ)}
    (hz : z ∈ genericPoints ↥(pullback (Y.normalization hY) φ)) :
    pullback.snd (Y.normalization hY) φ z ∈ genericPoints X := by
  refine mem_genericPoints_of_etale φ ?_
  have h := mem_genericPoints_pullback_fst_normalization φ hY hz
  rwa [pullback.condition, Scheme.Hom.comp_apply] at h

/-- Let `φ : X ⟶ Y` be an étale morphism of schemes and assume every quasi-compact open of `Y` has
finitely many irreducible components. Then the square formed by the normalization morphisms of `X`
and `Y`, the morphism of normalizations induced by `φ` and `φ` itself is cartesian, that is,
`X^ν = X ×_Y Y^ν`. This is the case of an étale morphism of [Stacks, Tag 07TD], whose full
statement is `AlgebraicGeometry.existsUnique_normalizationScheme_iso_pullback_of_smooth`. -/
theorem isPullback_normalizationSchemeMap_of_etale :
    IsPullback
      (normalizationSchemeMap φ (finite_irreducibleComponents_of_smooth φ hY) hY)
      (X.normalization (finite_irreducibleComponents_of_smooth φ hY))
      (Y.normalization hY) φ := by
  set hX := finite_irreducibleComponents_of_smooth φ hY
  have hsq : normalizationSchemeMap φ hX hY ≫ Y.normalization hY
      = X.normalization hX ≫ φ := normalizationSchemeMap_normalization φ hX hY
  have hNnormal : IsNormal (pullback (Y.normalization hY) φ) :=
    isNormal_pullback_normalization φ hY
  have hXνnormal : IsNormal (X.normalizationScheme hX) :=
    Scheme.isNormal_normalizationScheme X hX
  set lift : X.normalizationScheme hX ⟶ pullback (Y.normalization hY) φ :=
    pullback.lift (normalizationSchemeMap φ hX hY) (X.normalization hX) hsq with hliftdef
  obtain ⟨u, hu, -⟩ := Scheme.existsUnique_lift_normalization hX
    (pullback.snd (Y.normalization hY) φ)
    (fun η ↦ mem_genericPoints_pullback_snd φ hY η.2)
  have hunique := Scheme.existsUnique_lift_normalization hX (X.normalization hX)
    (fun η ↦ Scheme.normalization_mem_genericPoints X hX η.2)
  have hliftu : lift ≫ u = 𝟙 (X.normalizationScheme hX) :=
    hunique.unique (by rw [Category.assoc, hu, hliftdef, pullback.lift_snd])
      (Category.id_comp _)
  have huniqueY := Scheme.existsUnique_lift_normalization hY
    (pullback.fst (Y.normalization hY) φ ≫ Y.normalization hY)
    (fun η ↦ mem_genericPoints_pullback_fst_normalization φ hY η.2)
  have hfst : u ≫ normalizationSchemeMap φ hX hY = pullback.fst (Y.normalization hY) φ :=
    huniqueY.unique
      (by rw [Category.assoc, hsq, ← Category.assoc, hu, pullback.condition]) rfl
  have hulift : u ≫ lift = 𝟙 (pullback (Y.normalization hY) φ) := pullback.hom_ext
    (by rw [Category.assoc, hliftdef, pullback.lift_fst, hfst, Category.id_comp])
    (by rw [Category.assoc, hliftdef, pullback.lift_snd, hu, Category.id_comp])
  have : IsIso lift := ⟨u, hliftu, hulift⟩
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso lift)
    (by rw [asIso_hom, hliftdef, pullback.lift_fst])
    (by rw [asIso_hom, hliftdef, pullback.lift_snd])

end

end AlgebraicGeometry

end
