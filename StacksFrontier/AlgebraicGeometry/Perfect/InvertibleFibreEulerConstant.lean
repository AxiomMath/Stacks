module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree

/-!
# Euler characteristics of fibres in a proper flat family over a connected base

Let `p : F ⟶ S` be proper, flat and locally of finite presentation over a connected scheme `S`,
and let `ℋ` be an `𝒪_F`-module of finite presentation, flat over `S` (for instance an invertible
module). For two field-valued points `x₁ : Spec K₁ ⟶ S`, `x₂ : Spec K₂ ⟶ S` with fibres
`F_{x₁}`, `F_{x₂}` (given by cartesian squares), the Euler characteristics `χ(F_{xᵢ}, ℋ|_{F_{xᵢ}})`
agree. Indeed, at a field-valued point the Euler characteristic of the fibre is the derived-fibre
Euler characteristic of `Rp_*ℋ` ([Stacks, Tag 0B9T], via the base change of [Stacks, Tag 0B91]),
and that function is locally constant on `S` ([Stacks, Tag 0BDJ]), hence constant. The fields are
arbitrary (not assumed algebraically closed).

The Euler characteristic is
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum K g 𝒢 = ∑ (-1)ⁿ dim_K Hⁿ(Z, 𝒢)`.
The second half of the file collects the transport lemmas for `eulerSum`: along an isomorphism of
schemes over `Spec K`, and along a composite of pullbacks.

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum_eq_of_isPullback_of_isFlatOver`
  — constancy for a module of finite presentation, flat over the base.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum_eq_of_isPullback_of_isInvertible`
  — constancy for an invertible module.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum_pullback_iso_hom` and
  `eulerSum_pullback_comp` — transport along an isomorphism and along a composite.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.eulerSum_pullback_eq_of_iso` — two maps
  to `V` that are isomorphic over `V` and over `Spec K` give the same Euler characteristic of the
  restriction of a module on `V`.

## References

* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-! ### Constancy over a connected base -/

/-- **The Euler characteristic of the fibres of a proper family over a connected base is
constant**, for a module of finite presentation flat over the base. For `p : F ⟶ S` proper and
locally of finite presentation, `S` connected, and `ℋ` of finite presentation and flat over `S`,
the fibres over two field-valued points (given by cartesian squares) have the same
`χ(F_x, ℋ|_{F_x})`. -/
theorem eulerSum_eq_of_isPullback_of_isFlatOver {S F : Scheme.{u}} [PreconnectedSpace S]
    (p : F ⟶ S) [IsProper p] [LocallyOfFinitePresentation p]
    (H : F.Modules) (hH : H.IsFinitePresentation) (hflat : IsFlatOver p.toLRSHom.toShHom H)
    {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    (x₁ : Spec (.of K₁) ⟶ S) (x₂ : Spec (.of K₂) ⟶ S)
    {Z₁ Z₂ : Scheme.{u}} (q₁ : Z₁ ⟶ F) (g₁ : Z₁ ⟶ Spec (.of K₁)) (sq₁ : IsPullback q₁ g₁ p x₁)
    (q₂ : Z₂ ⟶ F) (g₂ : Z₂ ⟶ Spec (.of K₂)) (sq₂ : IsPullback q₂ g₂ p x₂) :
    eulerSum K₁ g₁ ((Scheme.Modules.pullback q₁).obj H) =
      eulerSum K₂ g₂ ((Scheme.Modules.pullback q₂).obj H) := by
  have hfp : FinitePresentation p := FinitePresentation.mk inferInstance inferInstance inferInstance
  have h₁ := chiDerivedFibre_eq_eulerSum p hfp H hH hflat K₁ x₁ q₁ g₁ sq₁
    (IsLocalRing.closedPoint K₁)
  have h₂ := chiDerivedFibre_eq_eulerSum p hfp H hH hflat K₂ x₂ q₂ g₂ sq₂
    (IsLocalRing.closedPoint K₂)
  have hc := DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S _
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward p hfp inferInstance H hH
      hflat)
  rw [← h₁, ← h₂]
  exact hc.apply_eq_of_preconnectedSpace _ _

/-- **The Euler characteristic of an invertible module is constant on the fibres of a proper flat
family over a connected base.** For `p : F ⟶ S` proper, flat and locally of finite presentation,
`S` connected, and `ℋ` invertible on `F`, the fibres over two field-valued points (given by
cartesian squares; the fields are arbitrary) have the same `χ(F_x, ℋ|_{F_x})`. -/
theorem eulerSum_eq_of_isPullback_of_isInvertible {S F : Scheme.{u}} [PreconnectedSpace S]
    (p : F ⟶ S) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (H : F.Modules) [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 H]
    {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    (x₁ : Spec (.of K₁) ⟶ S) (x₂ : Spec (.of K₂) ⟶ S)
    {Z₁ Z₂ : Scheme.{u}} (q₁ : Z₁ ⟶ F) (g₁ : Z₁ ⟶ Spec (.of K₁)) (sq₁ : IsPullback q₁ g₁ p x₁)
    (q₂ : Z₂ ⟶ F) (g₂ : Z₂ ⟶ Spec (.of K₂)) (sq₂ : IsPullback q₂ g₂ p x₂) :
    eulerSum K₁ g₁ ((Scheme.Modules.pullback q₁).obj H) =
      eulerSum K₂ g₂ ((Scheme.Modules.pullback q₂).obj H) := by
  have hH : Stacks.SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 H :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      F.presheaf _ _).mpr inferInstance
  obtain ⟨hfp, hflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible p H hH
  exact eulerSum_eq_of_isPullback_of_isFlatOver p H hfp hflat x₁ x₂ q₁ g₁ sq₁ q₂ g₂ sq₂

/-! ### Transport of the Euler characteristic -/

/-- The Euler characteristic is invariant under pullback along an isomorphism of schemes over
`Spec K`. -/
theorem eulerSum_pullback_of_isIso_of_comp_eq (K : Type u) [Field K] {Z Z' : Scheme.{u}}
    (f : Z ⟶ Z') [IsIso f] (g : Z ⟶ Spec (.of K)) (g' : Z' ⟶ Spec (.of K)) (hg : f ≫ g' = g)
    (G' : Z'.Modules) :
    eulerSum K g ((Scheme.Modules.pullback f).obj G') = eulerSum K g' G' := by
  subst hg
  exact finsum_congr fun n => by rw [finrank_cohomologyOverField_pullback K f g' G' n]

/-- The Euler characteristic is invariant under pullback along an isomorphism `e : Z ≅ Z'` of
schemes over `Spec K`. -/
theorem eulerSum_pullback_iso_hom (K : Type u) [Field K] {Z Z' : Scheme.{u}} (e : Z ≅ Z')
    (g : Z ⟶ Spec (.of K)) (g' : Z' ⟶ Spec (.of K)) (hg : e.hom ≫ g' = g) (G' : Z'.Modules) :
    eulerSum K g ((Scheme.Modules.pullback e.hom).obj G') = eulerSum K g' G' :=
  eulerSum_pullback_of_isIso_of_comp_eq K e.hom g g' hg G'

/-- The Euler characteristic of a pullback along a composite is that of the iterated pullback. -/
theorem eulerSum_pullback_comp (K : Type u) [Field K] {Z W V : Scheme.{u}} (a : Z ⟶ W)
    (b : W ⟶ V) (g : Z ⟶ Spec (.of K)) (H : V.Modules) :
    eulerSum K g ((Scheme.Modules.pullback (a ≫ b)).obj H) =
      eulerSum K g ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj H)) :=
  eulerSum_congr K g ((Scheme.Modules.pullbackComp a b).app H).symm

/-- **Two maps to `V` that are isomorphic over `V` and over `Spec K` restrict a module on `V` to
modules with the same Euler characteristic.** If `e : Z ≅ Z'` satisfies `e.hom ≫ q' = q` and
`e.hom ≫ g' = g`, then `χ(Z, q^*ℋ) = χ(Z', q'^*ℋ)`. -/
theorem eulerSum_pullback_eq_of_iso (K : Type u) [Field K] {Z Z' V : Scheme.{u}}
    (q : Z ⟶ V) (q' : Z' ⟶ V) (g : Z ⟶ Spec (.of K)) (g' : Z' ⟶ Spec (.of K)) (e : Z ≅ Z')
    (hq : e.hom ≫ q' = q) (hg : e.hom ≫ g' = g) (H : V.Modules) :
    eulerSum K g ((Scheme.Modules.pullback q).obj H) =
      eulerSum K g' ((Scheme.Modules.pullback q').obj H) := by
  subst hq
  rw [eulerSum_pullback_comp K e.hom q' g H, eulerSum_pullback_iso_hom K e g g' hg]

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end
