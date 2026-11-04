module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GaloisBaseChangeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange

/-!
# The projection of the base change of an algebraic space along a field extension

Let `X` be an algebraic space over a field `k` and let `k'/k` be a field extension. The base
change `X_{k'}` is `AlgebraicGeometry.Space.extensionBaseChange`, the product of `X` with the
presheaf represented by `Spec k'` over `Spec k`. The projection `X_{k'} ⟶ X` is a base change of
`Spec k' ⟶ Spec k`; it is integral when `k'/k` is algebraic, surjective, and universally
injective when `k'/k` is purely inseparable.

## Main definitions

* `AlgebraicGeometry.Space.specExtensionToBase` is the structure morphism of `Spec k'` over
  `Spec k`, read as a morphism of the big fppf site of `Spec k` to the terminal object.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_yoneda_map`: a morphism of the big fppf site of
  `S` whose underlying morphism of schemes is universally injective represents a universally
  injective morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.isPullback_extensionBaseChangeProj`: the projection `X_{k'} ⟶ X` is
  a base change of the structure morphism of `Spec k'` over `Spec k`.
* `AlgebraicGeometry.Space.isIntegralHom_extensionBaseChangeProj`,
  `AlgebraicGeometry.Space.isSurjective_extensionBaseChangeProj` and
  `AlgebraicGeometry.Space.universallyInjective_extensionBaseChangeProj`: the projection
  `X_{k'} ⟶ X` is integral when `k'/k` is algebraic, is always surjective, and is universally
  injective when `k'/k` is purely inseparable.

## References

* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MW](https://stacks.math.columbia.edu/tag/03MW)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 0B83](https://stacks.math.columbia.edu/tag/0B83)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Universal injectivity of a represented morphism -/

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is universally
injective represents a universally injective morphism of algebraic spaces over `S`. -/
theorem universallyInjective_yoneda_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (hφ : _root_.AlgebraicGeometry.UniversallyInjective
      ((BigFppfOver.toScheme B S hS).map φ)) :
    UniversallyInjective B S hS (yoneda.map φ) := by
  have hfield : ∀ (K : Type u) [Field K], Function.Injective
      (fun g : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj U =>
        g ≫ (BigFppfOver.toScheme B S hS).map φ) :=
    ((_root_.AlgebraicGeometry.tfae_universallyInjective
      ((BigFppfOver.toScheme B S hS).map φ)).out 1 2).mp hφ
  refine universallyInjective_of_fieldPoints B S hS _ fun p y hy => ⟨p, 𝟙 _, by simp, ?_⟩
  have hcomp : (BigFppfOver.toScheme B S hS).map p.value ≫
        (BigFppfOver.toScheme B S hS).map φ =
      (BigFppfOver.toScheme B S hS).map y ≫ (BigFppfOver.toScheme B S hS).map φ := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (BigFppfOver.toScheme B S hS).map hy
  have heq := (BigFppfOver.toScheme B S hS).map_injective (hfield p.carrier hcomp)
  simpa using heq.symm

/-! ### The projection of a base change along a field extension -/

section FieldExtension

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (.of k))) (hk' : B.Contains (Spec (.of k')))

/-- The structure morphism of `Spec k'` over `Spec k`, read as the morphism of the big fppf
site of `Spec k` from `Spec k'` to the terminal object of that site. -/
noncomputable def specExtensionToBase :
    specExtension k k' B hk hk' ⟶ Over.mk (𝟙 (B.obj hk)) :=
  Over.homMk (specExtensionHom k k' B hk hk') (Category.comp_id _)

/-- The projection `X_{k'} ⟶ X` is a base change of the structure morphism of `Spec k'` over
`Spec k`. -/
theorem isPullback_extensionBaseChangeProj
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    IsPullback (prod.fst : extensionBaseChange k k' B hk hk' X ⟶
        yoneda.obj (specExtension k k' B hk hk'))
      (extensionBaseChangeProj k k' B hk hk' X)
      (yoneda.map (specExtensionToBase k k' B hk hk'))
      ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X) := by
  have hι : Over.mkIdTerminal.from (specExtension k k' B hk hk') =
      specExtensionToBase k k' B hk hk' := Over.mkIdTerminal.hom_ext _ _
  exact hι ▸ isPullback_prod_fst_snd_yoneda_obj (specExtension k k' B hk hk') X

/-- The projection `X_{k'} ⟶ X` is integral when the field extension `k'/k` is integral. -/
theorem isIntegralHom_extensionBaseChangeProj [Algebra.IsIntegral k k']
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    IsIntegralHom B (Spec (.of k)) hk (extensionBaseChangeProj k k' B hk hk' X) :=
  isIntegralHom_of_isPullback B (Spec (.of k)) hk
    (isPullback_extensionBaseChangeProj k k' B hk hk' X)
    (isIntegralHom_yoneda_map B (Spec (.of k)) hk _
      (_root_.AlgebraicGeometry.IsIntegralHom.SpecMap_iff.2
        (algebraMap_isIntegral_iff.mpr inferInstance)))

/-- The projection `X_{k'} ⟶ X` is surjective on points. -/
theorem isSurjective_extensionBaseChangeProj
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    IsSurjective B (Spec (.of k)) hk (extensionBaseChangeProj k k' B hk hk' X) := by
  intro x
  have hbase : IsSurjective B (Spec (.of k)) hk
      (yoneda.map (specExtensionToBase k k' B hk hk')) :=
    isSurjective_yoneda_map B (Spec (.of k)) hk _
      (show _root_.AlgebraicGeometry.Surjective
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) from
        (AlgebraicGeometry.surjective_iff _).2 (Function.surjective_to_subsingleton _))
  obtain ⟨c, hc⟩ := hbase (pointsMap B (Spec (.of k)) hk X
    ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X) x)
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B (Spec (.of k)) hk
    (isPullback_extensionBaseChangeProj k k' B hk hk' X) c x hc
  exact ⟨w, hw⟩

/-- For an algebraic space `X` over `k`, the projection `X_{k'} ⟶ X` is universally injective
when the field extension `k'/k` is purely inseparable. -/
theorem universallyInjective_extensionBaseChangeProj [IsPurelyInseparable k k']
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    UniversallyInjective B (Spec (.of k)) hk (extensionBaseChangeProj k k' B hk hk' X) :=
  universallyInjective_of_isPullback B (Spec (.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (specExtension k k' B hk hk')) hX
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (Over.mk (𝟙 (B.obj hk))))
    (yoneda.map (specExtensionToBase k k' B hk hk'))
    ((isTerminal_yoneda_obj_base B (Spec (.of k)) hk).from X)
    (universallyInjective_yoneda_map B (Spec (.of k)) hk
      (specExtensionToBase k k' B hk hk')
      (show _root_.AlgebraicGeometry.UniversallyInjective
          (Spec.map (CommRingCat.ofHom (algebraMap k k'))) from
        universallyInjective_specMap_of_isPurelyInseparable k k'))
    (isPullback_extensionBaseChangeProj k k' B hk hk' X).flip

end FieldExtension

end AlgebraicGeometry.Space

end
