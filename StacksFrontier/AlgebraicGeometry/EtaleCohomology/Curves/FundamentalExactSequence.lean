module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorDirectSum
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceLocalDivisor
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSectionsSupplement

/-!
# The fundamental exact sequence of Stacks 03RI

Let `X` be a smooth curve over a field, let `η = Spec k(X)` be its generic point with inclusion
`j : η ⟶ X`, and let `X_0` be the set of closed points of `X` with inclusions
`i_x : Spec κ(x) ⟶ X`. The fundamental exact sequence of Stacks 03RI,

`0 ⟶ 𝐆_{m,X} ⟶ j_* 𝐆_{m,η} ⟶ ⨁_{x ∈ X_0} (i_x)_* 𝐙 ⟶ 0`,

is proved here to be a short exact sequence of abelian sheaves on the small étale site of `X`.
Its two maps are `Stacks.EtaleCohomology.multiplicativeDirectImageComparison` along `j` and
`Stacks.EtaleCohomology.closedPointDivisorMap`; the sequence is a complex by
`Stacks.EtaleCohomology.comparison_comp_closedPointDivisorMap`.

The three exactness statements have quite different content.

* **At `𝐆_{m,X}`**: the generic fibre of an étale `X`-scheme is scheme-theoretically dense in it,
  so an invertible global function is determined by its restriction there. This is
  `Stacks.EtaleCohomology.mono_multiplicativeDirectImageComparison_genericPointInclusion`.

* **In the middle**: a section of `j_* 𝐆_{m,η}` killed by the divisor map has, over an
  irreducible quasi-compact étale `X`-scheme, vanishing family of orders of vanishing — the
  comparison from the coproduct of the underlying presheaves to the coproduct of the sheaves is
  locally injective, and the assembly of a finitely supported family into a section of the
  presheaf coproduct is injective — and algebraic Hartogs on the normal scheme then writes it as
  an invertible global function. This is `Stacks.EtaleCohomology.exact_fundamentalSequence`,
  proved by the local surjectivity of the lift into the kernel.

* **On the right**: a divisor on a nonsingular curve is locally the divisor of a rational
  function, and the pullback of that function to an étale `X`-scheme has the prescribed orders of
  vanishing. This is `Stacks.EtaleCohomology.epi_closedPointDivisorMap`.

## Main results

* `Stacks.EtaleCohomology.exists_comparison_app_eq_of_divisorPresheafMap_eq_zero`: a section with
  vanishing divisor over an irreducible quasi-compact étale `X`-scheme is the restriction of an
  invertible global function.
* `Stacks.EtaleCohomology.imageSieve_comparison_mem`: a section killed by the divisor map is
  locally the restriction of an invertible global function, over any étale `X`-scheme.
* `Stacks.EtaleCohomology.isLocallySurjective_kernelLift` and
  `Stacks.EtaleCohomology.exact_fundamentalSequence`: **exactness in the middle.**
* `Stacks.EtaleCohomology.fundamentalSequence_shortExact`: **Stacks 03RI** — the sequence is short
  exact.

## Implementation notes

The sequence is a sequence of sheaves on the whole small étale site of `X`; no irreducibility
hypothesis on the étale `X`-schemes appears anywhere in its statement. Irreducibility is used only
inside the proofs, where the order of vanishing is taken in the function field of an irreducible
object, and it is removed again by the cover-density of the irreducible quasi-compact objects,
`Stacks.EtaleCohomology.isCoverDense_isIntegralCompactEtale_ι`.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Middle

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsCurve k fX]
  [Smooth fX]

/-- **A section of `j_* 𝐆_{m,η}` over an irreducible quasi-compact étale `X`-scheme whose family
of orders of vanishing is zero is the restriction of an invertible global function.** This is
algebraic Hartogs, through
`Stacks.EtaleCohomology.exists_restrict_eq_of_genericFibreDivisorSections_eq_zero`. -/
theorem exists_comparison_app_eq_of_divisorPresheafMap_eq_zero (W : X.Etale)
    [AlgebraicGeometry.IsIntegral W.left] [IsLocallyNoetherian W.left] [NoetherianSpace W.left]
    (s : ToType (((genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj (op W)))
    (hs : genericFibreDivisorPresheafMap.{u, v} (U := W) (X := X) s = 0) :
    ∃ b : (Γ(W.left, ⊤))ˣ,
      (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom.app (op W)
        (Stacks.Kummer.ofUnit.{u, v} b) = s := by
  have : IsNormal X := isNormal_of_smooth_isCurve fX
  have : IsNormal ((Functor.fromPUnit X).obj W.right) := inferInstanceAs (IsNormal X)
  have : AlgebraicGeometry.IsNormal ((𝟭 Scheme).obj W.left) := isNormal_of_etale W.hom
  have : AlgebraicGeometry.IsNormal W.left :=
    inferInstanceAs (AlgebraicGeometry.IsNormal ((𝟭 Scheme).obj W.left))
  have hzero : genericFibreDivisorSections.{u, v} W
      (Additive.ofMul (Additive.toMul s.down)) = 0 :=
    toAddMonoid_sigmaι_eq_zero.{u, v} X (op W) _ hs
  obtain ⟨b, hb⟩ := exists_restrict_eq_of_genericFibreDivisorSections_eq_zero.{u, v} fX W
    (Additive.toMul s.down) hzero
  refine ⟨b, ?_⟩
  refine Eq.trans (multiplicativeDirectImageComparison_app_ofUnit.{u, v}
    (genericPointInclusion X) W b) ?_
  rw [hb]
  rfl

/-- **A section of `j_* 𝐆_{m,η}` over `W` whose divisor vanishes after restriction along
`h : Z ⟶ W` is, over `Z`, the restriction of an invertible global function.** -/
theorem imageSieve_comparison_of_divisor_restrict_eq_zero {W Z : X.Etale} (h : Z ⟶ W)
    [AlgebraicGeometry.IsIntegral W.left] [IsLocallyNoetherian W.left] [NoetherianSpace W.left]
    [AlgebraicGeometry.IsIntegral Z.left] [IsLocallyNoetherian Z.left] [NoetherianSpace Z.left]
    (s : ToType (((genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj (op W)))
    (hs : (∐ fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj).map h.op
      (genericFibreDivisorPresheafMap.{u, v} (U := W) (X := X) s) = 0) :
    Presheaf.imageSieve
      (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom s h := by
  have hmf : genericFibreDivisorPresheafMap.{u, v} (U := Z) (X := X)
      (((genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
        (Spec X.functionField))).obj.map h.op s) = 0 :=
    (ConcreteCategory.congr_hom
      (genericFibreDivisorPresheafMap_naturality.{u, v} h) s).trans hs
  obtain ⟨c, hc⟩ := exists_comparison_app_eq_of_divisorPresheafMap_eq_zero fX Z _ hmf
  exact ⟨Stacks.Kummer.ofUnit.{u, v} c, hc⟩

/-- **The divisor of a section killed by the second map of the fundamental exact sequence
vanishes on a covering.** The comparison from the coproduct of the underlying presheaves to the
coproduct of the sheaves is locally injective. -/
theorem equalizerSieve_divisorPresheafMap_mem (W : X.Etale)
    [AlgebraicGeometry.IsIntegral W.left] [CompactSpace W.left] [IsLocallyNoetherian W.left]
    [NoetherianSpace W.left]
    (s : ToType (((genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj (op W)))
    (hs : (closedPointDivisorMap.{u, v} fX).hom.app (op W) s = 0) :
    Presheaf.equalizerSieve
      (genericFibreDivisorPresheafMap.{u, v} (U := W) (X := X) s) 0 ∈
        X.smallEtaleTopology W := by
  have : Presheaf.IsLocallyInjective X.smallEtaleTopology
      (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X) :=
    Sheaf.isLocallyInjective_sigmaPresheafComparison (closedPointSkyscraper.{u, v} X)
  refine Presheaf.equalizerSieve_mem X.smallEtaleTopology
    (closedPointDivisorSheaf.fromPresheafCoproduct.{u, v} X) _ 0 ?_
  refine Eq.trans ?_ (map_zero _).symm
  refine Eq.trans ?_ hs
  exact (ConcreteCategory.congr_hom
    (closedPointDivisorMap_app.{u, v} fX ⟨W, ⟨inferInstance, inferInstance⟩⟩) s).symm

/-- **A section of `j_* 𝐆_{m,η}` killed by the divisor map is, over an irreducible quasi-compact
étale `X`-scheme, locally the restriction of an invertible global function.** -/
theorem imageSieve_comparison_mem_of_isIntegral (W : X.Etale)
    [AlgebraicGeometry.IsIntegral W.left] [CompactSpace W.left]
    (s : ToType (((genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj (op W)))
    (hs : (closedPointDivisorMap.{u, v} fX).hom.app (op W) s = 0) :
    Presheaf.imageSieve
      (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom s ∈
        X.smallEtaleTopology W := by
  have : IsNormal X := isNormal_of_smooth_isCurve fX
  have : IsLocallyNoetherian W.left := isLocallyNoetherian_of_etale_over_isCurve fX W
  have : NoetherianSpace W.left := noetherianSpace_of_etale_over_isCurve fX W
  refine X.smallEtaleTopology.transitive
    (equalizerSieve_divisorPresheafMap_mem fX W s hs) _ ?_
  intro V f hf
  refine X.smallEtaleTopology.superset_covering ?_
    ((isIntegralCompactEtale X).ι.is_cover_of_isCoverDense X.smallEtaleTopology V)
  rintro V' k ⟨⟨Z, lift, map, fac⟩⟩
  have : AlgebraicGeometry.IsIntegral ((isIntegralCompactEtale X).ι.obj Z).left := Z.property.1
  have : CompactSpace ((isIntegralCompactEtale X).ι.obj Z).left := Z.property.2
  have : IsLocallyNoetherian ((isIntegralCompactEtale X).ι.obj Z).left :=
    isLocallyNoetherian_of_etale_over_isCurve fX _
  have : NoetherianSpace ((isIntegralCompactEtale X).ι.obj Z).left :=
    noetherianSpace_of_etale_over_isCurve fX _
  have hvanish := ((Presheaf.equalizerSieve
    (genericFibreDivisorPresheafMap.{u, v} (U := W) (X := X) s) 0).downward_closed hf map).trans
    (map_zero _)
  have hmain := imageSieve_comparison_of_divisor_restrict_eq_zero fX (map ≫ f) s hvanish
  have hk : k ≫ f = lift ≫ (map ≫ f) := by rw [← fac, Category.assoc]
  change Presheaf.imageSieve
    (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom s (k ≫ f)
  rw [hk]
  exact (Presheaf.imageSieve _ s).downward_closed hmain lift


/-- **A section of `j_* 𝐆_{m,η}` killed by the divisor map is locally the restriction of an
invertible global function**, over an arbitrary étale `X`-scheme: the irreducible quasi-compact
objects are cover-dense. -/
theorem imageSieve_comparison_mem (U : X.Etale)
    (s : ToType (((genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj (op U)))
    (hs : (closedPointDivisorMap.{u, v} fX).hom.app (op U) s = 0) :
    Presheaf.imageSieve
      (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom s ∈
        X.smallEtaleTopology U := by
  have : IsNormal X := isNormal_of_smooth_isCurve fX
  refine X.smallEtaleTopology.transitive
    ((isIntegralCompactEtale X).ι.is_cover_of_isCoverDense X.smallEtaleTopology U) _ ?_
  rintro V f ⟨⟨Z, lift, map, fac⟩⟩
  have : AlgebraicGeometry.IsIntegral ((isIntegralCompactEtale X).ι.obj Z).left := Z.property.1
  have : CompactSpace ((isIntegralCompactEtale X).ι.obj Z).left := Z.property.2
  have hsZ : (closedPointDivisorMap.{u, v} fX).hom.app (op ((isIntegralCompactEtale X).ι.obj Z))
      (((genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
        (Spec X.functionField))).obj.map map.op s) = 0 := by
    refine Eq.trans (ConcreteCategory.congr_hom
      ((closedPointDivisorMap.{u, v} fX).hom.naturality map.op) s) ?_
    refine (congrArg _ hs).trans ?_
    simp
  have hZ := imageSieve_comparison_mem_of_isIntegral fX ((isIntegralCompactEtale X).ι.obj Z) _ hsZ
  rw [← fac, Sieve.pullback_comp]
  refine X.smallEtaleTopology.pullback_stable lift ?_
  rw [Presheaf.pullback_imageSieve]
  exact hZ

/-- The inclusion of the kernel of the divisor map is injective on sections, being a
monomorphism of sheaves. -/
theorem injective_kernel_ι_app (V : X.Etaleᵒᵖ) :
    Function.Injective ((kernel.ι (closedPointDivisorMap.{u, v} fX)).hom.app V) :=
  (AddCommGrpCat.mono_iff_injective _).1
    ((NatTrans.mono_iff_mono_app _).1
      (Functor.map_mono (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) _) V)

/-- **The comparison into the kernel of the divisor map is locally surjective.** A section of the
kernel over an étale `X`-scheme is a section of `j_* 𝐆_{m,η}` with vanishing divisor, hence
locally the restriction of an invertible global function; and the inclusion of the kernel is
injective on sections, so the lift hits the given section. -/
theorem isLocallySurjective_kernelLift :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (kernel.lift (closedPointDivisorMap.{u, v} fX)
        (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X))
        (comparison_comp_closedPointDivisorMap.{u, v} fX)).hom := by
  refine ⟨fun {U} t => ?_⟩
  have hs : (closedPointDivisorMap.{u, v} fX).hom.app (op U)
      ((kernel.ι (closedPointDivisorMap.{u, v} fX)).hom.app (op U) t) = 0 := by
    have h := congrArg (fun φ : kernel (closedPointDivisorMap.{u, v} fX) ⟶
      closedPointDivisorSheaf.{u, v} X => φ.hom.app (op U) t)
      (kernel.condition (closedPointDivisorMap.{u, v} fX))
    refine h.trans ?_
    simp
  refine X.smallEtaleTopology.superset_covering ?_ (imageSieve_comparison_mem fX U _ hs)
  intro V f hf
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, ?_⟩
  refine injective_kernel_ι_app fX (op V) ?_
  have hlift : (kernel.ι (closedPointDivisorMap.{u, v} fX)).hom.app (op V)
      ((kernel.lift (closedPointDivisorMap.{u, v} fX)
        (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X))
        (comparison_comp_closedPointDivisorMap.{u, v} fX)).hom.app (op V) c) =
      (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom.app (op V) c :=
    ConcreteCategory.congr_hom (congr_app (congrArg
      (fun φ : Stacks.Kummer.multiplicativeSheaf.{u, v} X ⟶
          (genericPointDirectImage.{u, v} X).obj (Stacks.Kummer.multiplicativeSheaf.{u, v}
            (Spec X.functionField)) => φ.hom)
      (kernel.lift_ι (closedPointDivisorMap.{u, v} fX)
        (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X))
        (comparison_comp_closedPointDivisorMap.{u, v} fX))) (op V)) c
  rw [hlift, hc]
  exact (ConcreteCategory.congr_hom
    ((kernel.ι (closedPointDivisorMap.{u, v} fX)).hom.naturality f.op) t).symm

/-- **The fundamental exact sequence of Stacks 03RI is exact in the middle**: a section of
`j_* 𝐆_{m,η}` whose divisor vanishes is étale-locally an invertible global function. -/
theorem exact_fundamentalSequence :
    (ShortComplex.mk (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X))
      (closedPointDivisorMap.{u, v} fX)
      (comparison_comp_closedPointDivisorMap.{u, v} fX)).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have := isLocallySurjective_kernelLift.{u, v} fX
  infer_instance

/-- **Stacks Project, Tag 03RI.** Let `X` be a smooth curve over a field, let `η = Spec k(X)` be
its generic point with inclusion `j : η ⟶ X`, and let `X_0` be the set of closed points of `X`
with inclusions `i_x : Spec κ(x) ⟶ X`. Then

`0 ⟶ 𝐆_{m,X} ⟶ j_* 𝐆_{m,η} ⟶ ⨁_{x ∈ X_0} (i_x)_* 𝐙 ⟶ 0`

is a short exact sequence of abelian sheaves on the small étale site of `X`. The first map is the
comparison morphism `Stacks.EtaleCohomology.multiplicativeDirectImageComparison` along `j`, which
restricts an invertible global function on an étale `X`-scheme `U` to the generic fibre
`U ×_X η`; the second is `Stacks.EtaleCohomology.closedPointDivisorMap`, the family of orders of
vanishing.

Exactness at `𝐆_{m,X}` is
`Stacks.EtaleCohomology.mono_multiplicativeDirectImageComparison_genericPointInclusion`: the
generic fibre is scheme-theoretically dense. Exactness in the middle is
`Stacks.EtaleCohomology.exact_fundamentalSequence`, which rests on algebraic Hartogs on the
normal scheme `U`. Exactness on the right is
`Stacks.EtaleCohomology.epi_closedPointDivisorMap`: a divisor on a nonsingular curve is locally
the divisor of a rational function, and the pullback of that function along an étale morphism has
the prescribed orders of vanishing. -/
@[stacks 03RI]
theorem fundamentalSequence_shortExact :
    (ShortComplex.mk (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X))
      (closedPointDivisorMap.{u, v} fX)
      (comparison_comp_closedPointDivisorMap.{u, v} fX)).ShortExact :=
  .mk' (exact_fundamentalSequence.{u, v} fX)
    (mono_multiplicativeDirectImageComparison_genericPointInclusion.{u, v} X)
    (epi_closedPointDivisorMap.{u, v} fX)

end Middle

end Stacks.EtaleCohomology

end
