module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorNumerical
public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition

/-!
# The numerical invariants of `Hilb_{X/B}` induced from `Coh_{X/B}`

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation.  A family `Z ⊆ X_T`
classified by the Hilbert functor over a scheme `T` determines, through the identification
`Hilb_{X/B} = Quot_{𝒪_X/X/B}` of Stacks 0D00 and the morphism `Quot_{𝒪_X/X/B} ⟶ Coh_{X/B}` of
Stacks 0DP6, the object `(T, 𝒪_Z)` of `Coh_{X/B}`.  Numerical invariants of the objects of
`Coh_{X/B}`, compatible with pullback, therefore induce fibrewise invariants of the families
classified by the Hilbert functor, in the sense of `AlgebraicGeometry.Space.HilbertEulerData`,
and the subfunctor `Hilb^P_{X/B}` they cut out is the subfunctor of `Hilb_{X/B}` corresponding to
the fibre product `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`.  This is how Stacks 0DPG defines
`Hilb^P_{X/B}`.

## Main definitions

* `AlgebraicGeometry.Space.HilbertFamily.toOver`: a family over a scheme over `B`, read over the
  underlying scheme of the site.
* `AlgebraicGeometry.Space.HilbertEulerData.ofCoherent`: the fibrewise invariants of the families
  classified by `Hilb_{X/B}` induced by invariants of the objects of `Coh_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.HilbertFamily.toOver_baseChange`: base change over the schemes over
  `B` and over the schemes of the site agree.
* `AlgebraicGeometry.Space.isPrescribed_ofCoherent_iff`: the subfunctor
  `AlgebraicGeometry.Space.HilbertEulerData.numericalHilbertFunctor` of induced invariants is the
  subfunctor `AlgebraicGeometry.Space.hilbertCondition` corresponding to
  `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`.

## References

* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

/-- A family over a scheme `T` over `Y`, read over the scheme of the site underlying `T`. -/
abbrev HilbertFamily.toOver {T : SchemesOverPresheaf B S hS Y} (z : HilbertFamily f T) :
    HilbertFamilyOver f T.left :=
  ⟨T.hom, z⟩

/-- Base change of families over schemes over `Y` and over schemes of the site agree. -/
theorem HilbertFamily.toOver_baseChange {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T)
    (z : HilbertFamily f T) :
    (z.baseChange g).toOver f = (z.toOver f).baseChange g.left := by
  obtain ⟨T'l, ⟨⟨⟩⟩, T'h⟩ := T'
  obtain ⟨gl, ⟨⟨⟨⟩⟩⟩, hg⟩ := g
  change T'l ⟶ T.left at gl
  have hg' : T'h = yoneda.map gl ≫ T.hom := by simpa using hg.symm
  subst hg'
  rfl

variable (hf : IsFinitePresentation B S hS f.hom) {I : Type v}
  (χ : ∀ A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation, I →
    A.testScheme → ℤ)
  (hχ : ∀ {A' A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation}
    (φ : CoherentHom A' A) (i : I) (t : A'.testScheme), χ A' i t = χ A i (φ.baseScheme t))

include hχ in
/-- The object of `Coh_{X/B}` of the base change of a family maps to the object of the family,
over the given morphism of schemes. -/
theorem hilbertCohObject_baseChange_apply {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : HilbertFamilyOver f T) (i : I) (t : (BigFppfOver.toScheme B S hS).obj T') :
    χ (hilbertCohObject f hf (x.baseChange g)) i t =
      χ (hilbertCohObject f hf x) i ((BigFppfOver.toScheme B S hS).map g t) := by
  have key : ∀ y₁ y₂ : QuotFamilyOver (structureSheafQuotSituation f hf) T', y₁ = y₂ →
      χ y₁.cohObject i t = χ y₂.cohObject i t := by
    rintro _ _ rfl
    rfl
  exact (key _ _ (quotFamilyOfHilbertFamilyOver_baseChange f hf g x)).trans
    (hχ ((quotFamilyOfHilbertFamilyOver f hf x).cohHomBaseChange g) i t)

/-- **The fibrewise invariants of the families classified by `Hilb_{X/B}` induced by invariants
of the objects of `Coh_{X/B}`.**  A family `Z ⊆ X_T` gets the invariants of its object
`(T, 𝒪_Z)` of `Coh_{X/B}`; their compatibility with base change is the compatibility of the
invariants with pullback along the morphisms of `Coh_{X/B}`. -/
def HilbertEulerData.ofCoherent : HilbertEulerData f I where
  χ T z t i := χ (hilbertCohObject f hf (z.toOver f)) i t
  χ_baseChange g z t i := by
    rw [HilbertFamily.toOver_baseChange]
    exact hilbertCohObject_baseChange_apply f hf χ hχ g.left (z.toOver f) i t

/-- **The repository's `Hilb^P_{X/B}` is the base change of `Coh^P_{X/B}`.**  For invariants
induced from `Coh_{X/B}`, a family `Z ⊆ X_T` over a scheme `T` over `Y` lies in
`AlgebraicGeometry.Space.HilbertEulerData.numericalHilbertFunctor` exactly when, read over the
scheme of the site underlying `T`, it lies in the subfunctor of `Hilb_{X/B}` corresponding under
Stacks 0D00 to `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`. -/
theorem isPrescribed_ofCoherent_iff (P : I → ℤ) {T : SchemesOverPresheaf B S hS Y}
    (z : HilbertFamily f T) :
    (HilbertEulerData.ofCoherent f hf χ hχ).IsPrescribed P z ↔
      z.toOver f ∈ (hilbertCondition f hf (fun A => ∀ i t, χ A i t = P i)
        (CoherentSituation.numerical_of_hom χ P hχ)).obj (Opposite.op T.left) :=
  ⟨fun h i t => h t i, fun h t i => h i t⟩

section Points

attribute [local instance] pointTopology

variable {J : Type*}
  {ψ : ∀ A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation, J →
    points B S hS (yoneda.obj A.T.left) → ℤ}
  (hψ : ∀ {A' A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation}
    (φ : CoherentHom A' A) (j : J) (t : points B S hS (yoneda.obj A'.T.left)),
    ψ A' j t = ψ A j (pointsMap B S hS _ (yoneda.map φ.base.left) t))
  (hlc : ∀ A j, IsLocallyConstant (ψ A j)) (Q : J → ℤ)

include hlc in
/-- **The subfunctor of `Hilb_{X/B}` cut out by prescribed values of locally constant invariants
of `Coh_{X/B}` is a flat closed subfunctor**: its inclusion is representable by flat closed
immersions. -/
theorem relative_closedImmersion_flat_hilbertCondition_of_isLocallyConstant :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (hilbertCondition f hf (fun A => ∀ j t, ψ A j t = Q j)
          (CoherentSituation.numerical_points_of_hom Q hψ)).ι :=
  relative_closedImmersion_flat_hilbertCondition_ι f hf _
    (CoherentSituation.isCutOutOnTestSchemes_of_isLocallyConstant_points Q hψ hlc)

include hlc in
/-- **For a finite index set the subfunctor is open and closed**: its inclusion is representable
by morphisms which are open and closed immersions. -/
theorem relative_openImmersion_closedImmersion_hilbertCondition_of_isLocallyConstant [Finite J] :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (hilbertCondition f hf (fun A => ∀ j t, ψ A j t = Q j)
          (CoherentSituation.numerical_points_of_hom Q hψ)).ι :=
  relative_openImmersion_closedImmersion_hilbertCondition_ι f hf _
    (CoherentSituation.isCutOutOnTestSchemes_isClopen_of_isLocallyConstant_points Q hψ hlc)

end Points

end AlgebraicGeometry.Space

end
