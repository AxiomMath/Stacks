module

public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints

/-!
# Algebraic spaces smooth over a field

A scheme smooth over a field is regular (Stacks 056S), and regularity of an algebraic space is
regularity of one surjective étale scheme atlas (Stacks 03E6). An atlas of an algebraic space
smooth over a field is smooth over that field, because the morphism of schemes underlying any
commuting square of étale charts of a smooth morphism is smooth; so the space is regular.

Reading the atlas as a smooth scheme over the field also makes the finite separable points of
the space dense. The closed points of the atlas whose residue fields are finite separable over
the base field are dense in the atlas (Stacks 056U); the residue field at such a point, with
the canonical morphism from its spectrum, is a finite separable point of the space lying over
it; and the topology on the points of an algebraic space is the one detected by the
scheme-valued points, so density transfers along a surjective atlas.

## Main results

* `AlgebraicGeometry.Space.isRegular_of_isSmooth_over_field`: **Stacks 06M1**.
* `AlgebraicGeometry.Space.dense_setOf_class_finiteSeparable_of_isSmooth`: **Stacks 07W4**.

## Implementation notes

For the regularity statement the field enters as an object `T` of the big fppf site over `S`
whose underlying scheme is `Spec k`, and the smooth structure morphism of the space is a
morphism to `yoneda.obj T`. The identity of `yoneda.obj T` is the étale chart of the target
used in the chart square, and the morphism of the site underlying the square is the Yoneda
preimage of the composite of the atlas with the structure morphism.

Only the some-atlas form of Stacks 03E6 is used, so the étale locality of regularity of schemes,
which this library does not have, is not needed.

The density statement is about `|X|` for `X` an algebraic space over `Spec k` itself, so there
the base scheme is the spectrum of the field and the base object of the site is the terminal
one `Over.mk (𝟙 (B.obj hk))`, which is the situation of the source statement. A morphism
`Spec k' ⟶ X` over `Spec k` with `k'` a finite separable extension of `k` is a field-valued
point of Tag 03BU whose field of definition is `k'` and whose structure morphism to the base is
`Spec` of the inclusion `k → k'`; that last condition is the equation on
`AlgebraicGeometry.Space.FieldValuedPoint.toBase` in the statement, and the point of `|X|` it
represents is its class. The topology is
`AlgebraicGeometry.Space.pointTopology`, which is the topology of Tag 03BX.

Smoothness of the atlas over `Spec k` is read off directly from the chart square of the
structure morphism whose target chart is the identity, exactly as in the regularity statement.
So the source's composition of the étale atlas with the smooth structure morphism — Stacks
04XX and 03ZD — is not needed.

## References

* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 07W4](https://stacks.math.columbia.edu/tag/07W4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- The identity of a representable presheaf on the big fppf site is an étale chart. -/
theorem etale_presheaf_id_yoneda (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T)) :=
  AlgebraicGeometry.presheaf_id_of_iso B S hS _
    (fun {_ _} g hg ↦ by
      have := hg
      have : IsIso ((BigFppfOver.toScheme B S hS).map g) := inferInstance
      exact inferInstanceAs (Etale ((BigFppfOver.toScheme B S hS).map g))) T

/-- The scheme morphism underlying the Yoneda preimage of an étale chart followed by a smooth
morphism to a representable is smooth. -/
private theorem smooth_map_preimage_of_isSmooth (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ F) (f : F ⟶ yoneda.obj T) (hf : IsSmooth B S hS f)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Smooth ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))) :=
  hf U T a (𝟙 (yoneda.obj T)) _ ha (etale_presheaf_id_yoneda B S hS T)
    (by rw [yoneda.map_preimage]; simp)

/-- **Stacks 06M1.** An algebraic space over `S` which is smooth over the spectrum of a field
is regular. -/
@[stacks 06M1]
theorem isRegular_of_isSmooth_over_field (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (k : Type u) [Field k] (T : BigFppfOver B S hS)
    (hT : (BigFppfOver.toScheme B S hS).obj T = Spec (.of k))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ yoneda.obj T) (hf : IsSmooth B S hS f) :
    HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} ↦ IsRegular X) := by
  obtain ⟨U, a, hsurj, hetale⟩ := hF.exists_atlas
  refine ⟨U, a, hsurj, hetale, ?_⟩
  have hsmooth := smooth_map_preimage_of_isSmooth B S hS a f hf hetale
  have : Smooth (eqToHom hT) := inferInstance
  exact AlgebraicGeometry.isRegular_of_smooth_over_field (k := k)
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f)) ≫ eqToHom hT)

/-- The structure morphism of the canonical field-valued representative above a point `z` of
the scheme representing `U`, read on underlying schemes: it is the canonical morphism from the
spectrum of the residue field at `z`, followed by the structure morphism of `U`. -/
private theorem toBase_schemePointRepresentative (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj U) :
    (schemePointRepresentative B S hS U z).toBase =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField z ≫ B.inclusion.map U.hom := by
  show B.inclusion.map (B.inclusion.preimage _ ≫ U.hom) = _
  rw [B.inclusion.map_comp, B.inclusion.map_preimage]

section BaseField

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

attribute [local instance] pointTopology

/-- **Stacks 07W4.** Let `k` be a field and let `X` be an algebraic space over `Spec k` which is
smooth over `Spec k`. The points of `|X|` represented by a morphism `Spec k' ⟶ X` over `Spec k`
with `k'` a finite separable extension of `k` are dense in `|X|`. -/
@[stacks 07W4]
theorem dense_setOf_class_finiteSeparable_of_isSmooth
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : IsSmooth B (Spec (.of k)) hk f) :
    Dense {x : points B (Spec (.of k)) hk X |
      ∃ p : FieldValuedPoint B (Spec (.of k)) hk X,
        p.class B (Spec (.of k)) hk X = x ∧
          ∃ alg : Algebra k p.carrier,
            letI := alg
            Module.Finite k p.carrier ∧ Algebra.IsSeparable k p.carrier ∧
              p.toBase = Spec.map (CommRingCat.ofHom (algebraMap k p.carrier))} := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  let h : U ⟶ (Over.mk (𝟙 (B.obj hk)) : BigFppfOver B (Spec (.of k)) hk) :=
    yoneda.preimage (a ≫ f)
  let Z := (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U
  let g : Z ⟶ Spec (.of k) := (BigFppfOver.toScheme B (Spec (.of k)) hk).map h
  have hgSmooth : Smooth g := smooth_map_preimage_of_isSmooth B (Spec (.of k)) hk a f hf haEtale
  have hgBase : g = B.inclusion.map U.hom :=
    congrArg B.inclusion.map (show h.left = U.hom by simpa using Over.w h)
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨y, hyO⟩ := hOne
  obtain ⟨q, hq⟩ :=
    (surjective_iff_surjective_pointsMap B (Spec (.of k)) hk X hX U a).1 haSurj y
  have hWne : (pointsMap B (Spec (.of k)) hk (yoneda.obj U) a ⁻¹' O).Nonempty :=
    ⟨q, by rw [Set.mem_preimage, hq]; exact hyO⟩
  obtain ⟨V, hVopen, hVmem⟩ :=
    (isOpen_yoneda_iff_isSchemeOpen B (Spec (.of k)) hk U _).1
      ((continuous_pointsMap B (Spec (.of k)) hk a).isOpen_preimage O hO)
  have hVne : V.Nonempty := by
    obtain ⟨q₀, hq₀⟩ := hWne
    refine Quot.inductionOn (motive := fun w ↦
      w ∈ pointsMap B (Spec (.of k)) hk (yoneda.obj U) a ⁻¹' O → V.Nonempty) q₀ ?_ hq₀
    intro p hp
    exact ⟨schemePoint B (Spec (.of k)) hk U p, (hVmem p).1 hp⟩
  obtain ⟨z, hzV, hz⟩ := dense_iff_inter_open.1
    (dense_closedPoints_with_finite_separable_residueField_of_smooth g) V hVopen hVne
  have hpO : pointsMap B (Spec (.of k)) hk (yoneda.obj U) a
      ((schemePointRepresentative B (Spec (.of k)) hk U z).class B (Spec (.of k)) hk
        (yoneda.obj U)) ∈ O :=
    (hVmem _).2 (by rw [schemePointRepresentative_point]; exact hzV)
  refine ⟨_, hpO, FieldValuedPoint.map B (Spec (.of k)) hk (yoneda.obj U) a
    (schemePointRepresentative B (Spec (.of k)) hk U z), rfl,
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Z.Γevaluation z).hom.toAlgebra, hz.2.1, hz.2.2, ?_⟩
  show (schemePointRepresentative B (Spec (.of k)) hk U z).toBase = _
  rw [toBase_schemePointRepresentative, ← hgBase]
  exact (SpecMap_algebraMap_residueField g z).symm

end BaseField

end AlgebraicGeometry.Space

end
