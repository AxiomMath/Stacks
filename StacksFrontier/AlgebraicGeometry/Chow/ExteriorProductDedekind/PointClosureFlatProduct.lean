module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Associativity
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.DominantClosure
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.RespectsRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompositionPushPull
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.Topology.Sober.Generization
import all StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
import all StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity

/-!
# Products of point closures with a factor flat over the base

Let `(S, δ)` be as in section 42.63 of the Stacks Project. For `X`, `Y` locally of finite type
over `S`, a point `a` of `X` and a closed subscheme `K` of `Y` flat of relative dimension `r` over
`S`, the generic points of `closure {a} ×_S K` lie over `a` and have relative dimension
`δ(a) + r`. Over a component of the base which is a closed point the product of two point closures
therefore does not drop dimension: its cycle lives in delta-dimension `δ(a) + δ(b)` only.

## Main results

* `Stacks.Chow.fst_eq_and_relativeDimension_of_closedSubschemeCycleCoeff_product_ne_zero` — the
  multiplicity of `closure {a} ×_S K` is concentrated over `a`, in delta-dimension `δ(a) + r`.
* `Stacks.Chow.closedSubschemeCycleCoeff_product_eq_zero_of_isClosed_right`,
  `Stacks.Chow.closedSubschemeCycleCoeff_product_eq_zero_of_isClosed_left` — over a closed point
  of the base dominated by one factor, the cycle of the product of two point closures vanishes
  outside delta-dimension `δ(a) + δ(b)`.

## References

* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section FlatFactor

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (K : Y.IdealSheafData)

/-- The product `(X ×_S Y) ×_Y K ⟶ X` of the closed subscheme of `K` with `X` is the base change
of `K ⟶ S` along `X ⟶ S`. -/
theorem isPullback_productProjection :
    IsPullback (pullback.snd (pullback.snd f g) K.subschemeι)
      (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) (K.subschemeι ≫ g) f :=
  (IsPullback.of_hasPullback (pullback.snd f g) K.subschemeι).flip.paste_vert
    (IsPullback.of_hasPullback f g).flip

/-- The product of the closed subschemes of `I` and `K` is the inverse image of `I` along the
projection `(X ×_S Y) ×_Y K ⟶ X`, pushed into `X ×_S Y`. -/
theorem map_comap_productProjection (I : X.IdealSheafData) :
    (I.comap (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)).map
        (pullback.fst (pullback.snd f g) K.subschemeι) =
      I.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g) := by
  rw [Scheme.IdealSheafData.comap_comp, map_comap_closedImmersion]
  rfl

/-- The closed subscheme `I ×_S K` of `X ×_S Y`, presented as the fibre product of the closed
subscheme of `I` with the projection `(X ×_S Y) ×_Y K ⟶ X`. -/
def productSubschemeIso (I : X.IdealSheafData) :
    (pullback (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)
        I.subschemeι : Scheme.{u}) ≅
      ((I.comap (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)).map
        (pullback.fst (pullback.snd f g) K.subschemeι)).subscheme :=
  (I.comapIso _).symm ≪≫ imageIsoOfIsClosedImmersion _ _

/-- The presentation `Stacks.Chow.productSubschemeIso` lies over `X`. -/
theorem productSubschemeIso_hom_subschemeι_fst (I : X.IdealSheafData) :
    (productSubschemeIso f g K I).hom ≫
        ((I.comap (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)).map
          (pullback.fst (pullback.snd f g) K.subschemeι)).subschemeι ≫ pullback.fst f g =
      pullback.snd (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)
        I.subschemeι ≫ I.subschemeι := by
  simp only [productSubschemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc (imageIsoOfIsClosedImmersion _ _).hom,
    imageIsoOfIsClosedImmersion_hom_subschemeι, Category.assoc,
    Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
  exact pullback.condition

end FlatFactor

section FlatFactorDimension

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] (K : Y.IdealSheafData)

/-- **Components of a product with a flat factor.** Let `K` be an ideal sheaf on `Y` whose closed
subscheme is flat of relative dimension `r` over the base. Every generic point `ξ` of an
irreducible component of `I ×_S K` lies over the generic point of an irreducible component of
`I`, and its relative dimension is `r` more than that of its image. -/
theorem exists_genericPoint_of_mem_genericPoints_product (I : X.IdealSheafData)
    [Flat (K.subschemeι ≫ g)] (r : ℕ)
    (hK : AlgebraicGeometry.RelativeDimension (K.subschemeι ≫ g) r)
    (ξ : (I.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g)).subscheme)
    (hξ : ξ ∈ genericPoints (I.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g)).subscheme) :
    ∃ η ∈ genericPoints I.subscheme,
      I.subschemeι.base η = (pullback.fst f g).base
        ((I.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g)).subschemeι.base ξ) ∧
      relativeDimension C.dimensionFunction (pullback.fst f g ≫ f)
          ((I.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g)).subschemeι.base ξ) =
        relativeDimension C.dimensionFunction f (I.subschemeι.base η) + r := by
  have sq := isPullback_productProjection f g K
  let _ : Flat (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) :=
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  let _ : LocallyOfFiniteType
      (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hq : AlgebraicGeometry.RelativeDimension
      (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hK
  have key : ∀ (J : (pullback f g : Scheme.{u}).IdealSheafData)
      (hJ : (I.comap (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)).map
        (pullback.fst (pullback.snd f g) K.subschemeι) = J) (ξ : J.subscheme),
      ξ ∈ genericPoints J.subscheme →
      ∃ η ∈ genericPoints I.subscheme,
        I.subschemeι.base η = (pullback.fst f g).base (J.subschemeι.base ξ) ∧
        relativeDimension C.dimensionFunction (pullback.fst f g ≫ f) (J.subschemeι.base ξ) =
          relativeDimension C.dimensionFunction f (I.subschemeι.base η) + r := by
    rintro J rfl ξ hξ
    have hξ' : (productSubschemeIso f g K I).inv.base ξ ∈ genericPoints _ :=
      mem_genericPoints_of_generalizingMap
        (productSubschemeIso f g K I).inv.isOpenEmbedding.generalizingMap hξ
    have hξξ : (productSubschemeIso f g K I).hom.base
        ((productSubschemeIso f g K I).inv.base ξ) = ξ := by
      simp [← Scheme.Hom.comp_apply]
    have hsq := productSubschemeIso_hom_subschemeι_fst f g K I
    have hpt : I.subschemeι.base ((pullback.snd _ I.subschemeι).base
        ((productSubschemeIso f g K I).inv.base ξ)) =
        (pullback.fst f g).base
          (((I.comap (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)).map
            (pullback.fst (pullback.snd f g) K.subschemeι)).subschemeι.base ξ) := by
      rw [← Scheme.Hom.comp_apply, ← hsq]
      simp only [Scheme.Hom.comp_apply, hξξ]
    refine ⟨(pullback.snd _ I.subschemeι).base ((productSubschemeIso f g K I).inv.base ξ),
      mem_genericPoints_of_generalizingMap (Flat.generalizingMap _) hξ', hpt, ?_⟩
    let W : irreducibleComponents (pullback
        (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)
        I.subschemeι : Scheme.{u}) :=
      ⟨closure {(productSubschemeIso f g K I).inv.base ξ}, hξ'⟩
    have hW : W.2.1.genericPoint = (productSubschemeIso f g K I).inv.base ξ :=
      (W.2.1.isGenericPoint_genericPoint isClosed_closure).eq isGenericPoint_closure
    have htr := toNat_residueTrdeg_genericPoint (pullback.snd _ I.subschemeι) W r
      (relativeDimension_pullback_snd _ I.subschemeι r hq)
    rw [hW] at htr
    have hδ := relativeDimension_comp_eq_add_trdeg C.dimensionFunction (I.subschemeι ≫ f)
      (pullback.snd _ I.subschemeι) ((productSubschemeIso f g K I).inv.base ξ)
    rw [htr, relativeDimension_comp_closedImmersion C.dimensionFunction I.subschemeι f] at hδ
    rw [← hδ]
    have hmor : pullback.snd _ I.subschemeι ≫ I.subschemeι ≫ f =
        (productSubschemeIso f g K I).hom ≫
          ((I.comap (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)).map
            (pullback.fst (pullback.snd f g) K.subschemeι)).subschemeι ≫
          pullback.fst f g ≫ f := by
      rw [← Category.assoc, ← hsq]
      simp only [Category.assoc]
    rw [hmor, relativeDimension_comp_closedImmersion C.dimensionFunction
      (productSubschemeIso f g K I).hom, relativeDimension_comp_closedImmersion
      C.dimensionFunction _ (pullback.fst f g ≫ f), hξξ]
  exact key _ (map_comap_productProjection f g K I) ξ hξ

/-- The only generic point of the reduced closure of a point `a` is `a`. -/
theorem integralComponentAt_subschemeι_of_mem_genericPoints {T : Scheme.{u}} (a : T)
    (η : (integralComponentAt a).subscheme)
    (hη : η ∈ genericPoints (integralComponentAt a).subscheme) :
    (integralComponentAt a).subschemeι.base η = a := by
  have _ : IsIntegral (integralComponentAt a).subscheme := isIntegral_integralComponentAt a
  have hηg : η = genericPoint (integralComponentAt a).subscheme := by
    have hmem : η ∈ ({genericPoint (integralComponentAt a).subscheme} :
        Set (integralComponentAt a).subscheme) := by
      rw [← genericPoints_eq_singleton]
      exact hη
    exact hmem
  rw [hηg]
  exact genericPointOf_integralComponentAt a

/-- **The multiplicity of a product of a point closure with a flat factor is concentrated over
that point.** If the cycle of `closure {a} ×_S K`, with `K` flat of relative dimension `r` over
the base, has a nonzero coefficient at `v` in delta-dimension `k`, then `v` lies over `a` and
`k = δ(a) + r`. -/
theorem fst_eq_and_relativeDimension_of_closedSubschemeCycleCoeff_product_ne_zero (a : X)
    [Flat (K.subschemeι ≫ g)] (r : ℕ)
    (hK : AlgebraicGeometry.RelativeDimension (K.subschemeι ≫ g) r) (k : ℤ)
    (v : (pullback f g : Scheme.{u}))
    (hv : closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
      ((integralComponentAt a).comap (pullback.fst f g) ⊔
        K.comap (pullback.snd f g)).subschemeι k v ≠ 0) :
    (pullback.fst f g).base v = a ∧ relativeDimension C.dimensionFunction f a + r = k := by
  unfold closedSubschemeCycleCoeff at hv
  split_ifs at hv with hex
  · obtain ⟨ξ, hξ, hk⟩ := hex
    obtain ⟨η, hη, hηpt, hηdim⟩ := exists_genericPoint_of_mem_genericPoints_product C f g K
      (integralComponentAt a) r hK ξ.1 ξ.2
    have ha := integralComponentAt_subschemeι_of_mem_genericPoints a η hη
    rw [ha, hξ] at hηpt
    rw [ha, hξ, hk] at hηdim
    exact ⟨hηpt.symm, hηdim.symm⟩
  · exact absurd rfl hv

/-- The mirror image of
`Stacks.Chow.fst_eq_and_relativeDimension_of_closedSubschemeCycleCoeff_product_ne_zero`, with
the flat factor on the left. -/
theorem snd_eq_and_relativeDimension_of_closedSubschemeCycleCoeff_product_ne_zero
    (K : X.IdealSheafData) (a : Y) [Flat (K.subschemeι ≫ f)] (r : ℕ)
    (hK : AlgebraicGeometry.RelativeDimension (K.subschemeι ≫ f) r) (k : ℤ)
    (v : (pullback f g : Scheme.{u}))
    (hv : closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
      (K.comap (pullback.fst f g) ⊔
        (integralComponentAt a).comap (pullback.snd f g)).subschemeι k v ≠ 0) :
    (pullback.snd f g).base v = a ∧ relativeDimension C.dimensionFunction g a + r = k := by
  rw [closedSubschemeCycleCoeff_product_symm C f g K (integralComponentAt a) k v] at hv
  have H := fst_eq_and_relativeDimension_of_closedSubschemeCycleCoeff_product_ne_zero C g f K a
    r hK k _ hv
  have hfst : (pullback.fst g f).base ((pullbackSymmetry f g).hom.base v) =
      (pullback.snd f g).base v :=
    congrArg (fun φ : (pullback f g : Scheme.{u}) ⟶ Y ↦ φ.base v)
      (pullbackSymmetry_hom_comp_fst f g)
  rw [hfst] at H
  exact H

end FlatFactorDimension

/-! ### Products of point closures over the base of section 42.63 -/

section DedekindProduct

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X Y : Scheme.{u}}
  (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g]

include hC

/-- Over the base of section 42.63, the closure of a point `b` dominating a component of the base
which is a closed point is flat over the base of relative dimension `δ(b)`. -/
private theorem exists_flat_relativeDimension_pointClosure_of_isClosed {Z : Scheme.{u}}
    (p : Z ⟶ C.S) [LocallyOfFiniteType p] (b : Z) (hb : DominatesBaseComponent C p b)
    (hbc : IsClosed ({p.base b} : Set C.S)) :
    ∃ r : ℕ, (r : ℤ) = relativeDimension C.dimensionFunction p b ∧
      Flat ((integralComponentAt b).subschemeι ≫ p) ∧
      AlgebraicGeometry.RelativeDimension ((integralComponentAt b).subschemeι ≫ p) r := by
  obtain ⟨hr, hrel⟩ := pointClosure_relativeDimension_of_dominatesBaseComponent C hC p b hb _ rfl
  rw [hC.2.1 _ hbc, sub_zero] at hr hrel
  exact ⟨_, hr, flat_pointClosure_of_dominatesBaseComponent C hC p b hb, hrel⟩

/-- Over the base of section 42.63, if `b` dominates an irreducible component of the base which
is a closed point, then the cycle of `closure {a} ×_S closure {b}` lives in delta-dimension
`δ(a) + δ(b)` only: over a component of the base which is a point the product does not drop
dimension. -/
theorem closedSubschemeCycleCoeff_product_eq_zero_of_isClosed_right (a : X) (b : Y)
    (hb : DominatesBaseComponent C g b) (hbc : IsClosed ({g.base b} : Set C.S)) (k : ℤ)
    (hk : k ≠ relativeDimension C.dimensionFunction f a +
      relativeDimension C.dimensionFunction g b) (v : (pullback f g : Scheme.{u})) :
    closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
      ((integralComponentAt a).comap (pullback.fst f g) ⊔
        (integralComponentAt b).comap (pullback.snd f g)).subschemeι k v = 0 := by
  by_contra hv
  obtain ⟨r, hr, _, hrel⟩ :=
    exists_flat_relativeDimension_pointClosure_of_isClosed hC g b hb hbc
  have H := (fst_eq_and_relativeDimension_of_closedSubschemeCycleCoeff_product_ne_zero C f g
    (integralComponentAt b) a _ hrel k v hv).2
  omega

/-- The mirror image of `Stacks.Chow.closedSubschemeCycleCoeff_product_eq_zero_of_isClosed_right`,
with the dominating factor on the left. -/
theorem closedSubschemeCycleCoeff_product_eq_zero_of_isClosed_left (b : X) (a : Y)
    (hb : DominatesBaseComponent C f b) (hbc : IsClosed ({f.base b} : Set C.S)) (k : ℤ)
    (hk : k ≠ relativeDimension C.dimensionFunction f b +
      relativeDimension C.dimensionFunction g a) (v : (pullback f g : Scheme.{u})) :
    closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
      ((integralComponentAt b).comap (pullback.fst f g) ⊔
        (integralComponentAt a).comap (pullback.snd f g)).subschemeι k v = 0 := by
  by_contra hv
  obtain ⟨r, hr, _, hrel⟩ :=
    exists_flat_relativeDimension_pointClosure_of_isClosed hC f b hb hbc
  have H := (snd_eq_and_relativeDimension_of_closedSubschemeCycleCoeff_product_ne_zero C f g
    (integralComponentAt b) a _ hrel k v hv).2
  omega

end DedekindProduct

end Stacks.Chow

end
