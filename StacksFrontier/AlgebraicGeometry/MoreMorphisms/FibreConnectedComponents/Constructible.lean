module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.GenericConstancy
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricComponentCountConstructible
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of the number of geometric connected components

Stacks Tag 055I says that for a morphism of schemes of finite presentation, each level set of
the function counting the geometrically connected components of the fibres is locally
constructible in the target.

## Main results

* `AlgebraicGeometry.isLocallyConstructible_numGeometricConnectedComponents` is Stacks Tag 055I.

## Implementation notes

The number of components is `AlgebraicGeometry.numGeometricConnectedComponents` of Tag 055F,
valued in `ℕ∞`, so the statement also covers the level set at infinity.

The argument is local on the target, so the target may be taken affine, `Spec R`. Writing `R`
as the filtered colimit of the subalgebras generated over `ℤ` by its finite subsets, each of
which is Noetherian, `AlgebraicGeometry.exists_noetherian_model` descends the morphism to a
model over a Noetherian base; there Tag 055H gives generic constancy of the count, which by
`isConstructible_of_constant_near_genericPoints` makes each level set
constructible. Tag 055F and Tag 054I carry the conclusion back.

## References

* [Stacks Project, Tag 055I](https://stacks.math.columbia.edu/tag/055I)
-/

public section

open CategoryTheory Topology

namespace AlgebraicGeometry

universe u

open TopologicalSpace Limits

noncomputable section

private theorem numGeometricConnectedComponents_eq_of_over_iso {Y : Scheme.{u}}
    {X X' : Over Y} (e : X ≅ X') :
    numGeometricConnectedComponents X.hom = numGeometricConnectedComponents X'.hom := by
  funext y
  let K := SeparableClosure (Y.residueField y)
  let e₁ := (Over.pullback (Y.fromSpecResidueField y)).mapIso e
  let e₂ := (Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField y) K)))).mapIso e₁
  let e₃ : geometricFiber X.hom y K ≅ geometricFiber X'.hom y K :=
    (Over.forget _).mapIso e₂
  exact enatCard_connectedComponents_iso e₃

@[ega "IV 9.7.9" "special case"]
private theorem isLocallyConstructible_numGeometricConnectedComponents_spec {X : Scheme.{u}}
    (R : CommRingCat.{u}) (f : X ⟶ Spec R) (hf : AlgebraicGeometry.FinitePresentation f)
    (n : ℕ∞) :
    IsLocallyConstructible {y | numGeometricConnectedComponents f y = n} := by
  obtain ⟨Y₀, X₀, g, f₀, hY₀, hf₀, ⟨e⟩⟩ := exists_noetherian_model R f hf
  let := hY₀; let := hf₀.1; let := hf₀.2.1
  have h := (isConstructible_of_constant_near_genericPoints
    (numGeometricConnectedComponents f₀)
    (exists_open_numGeometricConnectedComponents_eq f₀) n).isLocallyConstructible
  have he := numGeometricConnectedComponents_eq_of_over_iso e
  change numGeometricConnectedComponents f =
    numGeometricConnectedComponents (pullback.snd f₀ g) at he
  have hpb := numGeometricConnectedComponents_eq_of_isPullback f₀ (pullback.snd f₀ g)
    (pullback.fst f₀ g) g (IsPullback.of_hasPullback f₀ g)
  rw [he, hpb]
  exact isLocallyConstructible_preimage g h

/-- **Stacks Project, Tag 055I.** Every level set of the number of geometrically connected
components of the fibres of a morphism of finite presentation is locally constructible. -/
@[stacks 055I, ega "IV 9.7.9" "n'(s) (connected)"]
theorem isLocallyConstructible_numGeometricConnectedComponents {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.FinitePresentation f) (n : ℕ∞) :
    IsLocallyConstructible {y : Y | numGeometricConnectedComponents f y = n} := by
  let := hf.1; let := hf.2.1; let := hf.2.2
  refine .of_isOpenCover Y.affineCover.isOpenCover_opensRange fun i => ?_
  have hp : AlgebraicGeometry.FinitePresentation (pullback.snd f (Y.affineCover.f i)) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have h₀ := isLocallyConstructible_numGeometricConnectedComponents_spec _
    (pullback.snd f (Y.affineCover.f i)) hp n
  have hfun := numGeometricConnectedComponents_eq_of_isPullback f
    (pullback.snd f (Y.affineCover.f i)) (pullback.fst f (Y.affineCover.f i))
    (Y.affineCover.f i) (IsPullback.of_hasPullback f (Y.affineCover.f i))
  have hcount : {y | numGeometricConnectedComponents
        (pullback.snd f (Y.affineCover.f i)) y = n} =
      {y | (numGeometricConnectedComponents f ∘ (Y.affineCover.f i)) y = n} := by
    ext y
    change numGeometricConnectedComponents (pullback.snd f (Y.affineCover.f i)) y = n ↔
      (numGeometricConnectedComponents f ∘ (Y.affineCover.f i)) y = n
    rw [congrFun hfun y]
  have h : IsLocallyConstructible
      {y | (numGeometricConnectedComponents f ∘ (Y.affineCover.f i)) y = n} :=
    cast (congrArg (fun s => IsLocallyConstructible s) hcount) h₀
  have h' := h.preimage_of_isOpenEmbedding (Y.affineCover.f i).isoOpensRange.inv.isOpenEmbedding
  convert! h' using 1
  ext y
  change (numGeometricConnectedComponents f y.1 = n) ↔
    (numGeometricConnectedComponents f
      ((Y.affineCover.f i) ((Y.affineCover.f i).isoOpensRange.inv y)) = n)
  have he := congrArg (fun k : (Y.affineCover.f i).opensRange.toScheme ⟶ Y => k y)
    (Scheme.Hom.isoOpensRange_inv_comp (Y.affineCover.f i))
  have hpt : (Y.affineCover.f i) ((Y.affineCover.f i).isoOpensRange.inv y) = y.1 := he
  rw [hpt]

end

end AlgebraicGeometry

end
