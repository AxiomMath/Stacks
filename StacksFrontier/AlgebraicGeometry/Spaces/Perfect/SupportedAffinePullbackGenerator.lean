module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectClassicalGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardReflectsIsomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffineConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiCompactOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction

/-!
# Pulling back a supported perfect generator along an affine morphism

Let `g : X ⟶ X₀` be an affine morphism of algebraic spaces and `T₀ ⊆ |X₀|` a closed subset. If
`G₀` is a generator of `D_{QCoh,T₀}(𝒪_{X₀})` in the sense of Stacks 0AEC, then `Lg^*G₀` is a
generator of `D_{QCoh,g⁻¹T₀}(𝒪_X)`: for `E` in `D_QCoh(𝒪_X)` supported on `g⁻¹T₀`, the derived
direct image `Rg_*E` is supported on `T₀` (its cohomology sheaves are the direct images of those
of `E`), `Hom(Lg^*G₀[n], E) = Hom(G₀[n], Rg_*E)`, and `Rg_*` is conservative on `D_QCoh` for `g`
affine.

Combined with Stacks 0AEC on `X₀` and Stacks 0GFD on `X`, this gives the generation step of the
Noetherian approximation argument: when `X` and `X₀` are quasi-compact and quasi-separated and
`|X₀| ∖ T₀` is quasi-compact, a thick property of objects of `D(𝒪_X)` which holds for the
derived pullbacks of the perfect objects of `D(𝒪_{X₀})` supported on `T₀` holds for every perfect
object of `D(𝒪_X)` supported on `g⁻¹T₀`.

## Main results

* `AlgebraicGeometry.Space.cohomologySupportedOn_derivedModulePushforward_of_isAffineHom`
* `AlgebraicGeometry.Space.isZero_of_forall_quasicoherentDerivedModulePullback_hom_eq_zero`
* `AlgebraicGeometry.Space.prop_of_isPerfect_of_cohomologySupportedOn_preimage`

## References

* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 0GFD](https://stacks.math.columbia.edu/tag/0GFD)
* [Stacks Project, Tag 08II](https://stacks.math.columbia.edu/tag/08II)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


/-- **The derived direct image along an affine morphism preserves supports.** For an affine
`g : X ⟶ X₀`, a closed subset `T₀ ⊆ |X₀|` and `E ∈ D_QCoh(𝒪_X)` supported on `g⁻¹T₀`, the
derived direct image `Rg_*E` is supported on `T₀`. -/
theorem cohomologySupportedOn_derivedModulePushforward_of_isAffineHom
    {X X₀ : AlgebraicSpaces B S hS} (g : X ⟶ X₀) (hg : IsAffineHom B S hS g.hom)
    (T₀ : Set (points B S hS X₀.1)) (hT₀ : IsClosed T₀)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E)
    (hs : CohomologySupportedOn B S hS X.1 X.2 (pointsMap B S hS X.1 g.hom ⁻¹' T₀) E) :
    CohomologySupportedOn B S hS X₀.1 X₀.2 T₀ ((derivedModulePushforward B S hS g).obj E) := by
  intro i
  refine (supportOfSheaf_eq_of_iso B S hS X₀ (homologyDerivedModulePushforwardIsoOfIsAffineHom B S
    hS g hg (derivedModulePushforward B S hS g) (derivedModulePushforwardUnit B S hS g) E
    (fun q => hE q) i)).trans_subset ?_
  exact supportOfSheaf_modulePushforward_subset_of_isClosed B S hS g _ T₀ hT₀ (hs i)

/-- **The derived pullback of a supported generator along an affine morphism is a supported
generator.** Let `g : X ⟶ X₀` be affine, `T₀ ⊆ |X₀|` closed and `G₀ ∈ D(𝒪_{X₀})` such that an
object of `D_QCoh(𝒪_{X₀})` supported on `T₀` receiving no nonzero morphism from any shift of
`G₀` is zero. Then the same holds for `Lg^*G₀` and the objects of `D_QCoh(𝒪_X)` supported on
`g⁻¹T₀`. -/
theorem isZero_of_forall_quasicoherentDerivedModulePullback_hom_eq_zero
    {X X₀ : AlgebraicSpaces B S hS} (g : X ⟶ X₀) (hg : IsAffineHom B S hS g.hom)
    (T₀ : Set (points B S hS X₀.1)) (hT₀ : IsClosed T₀)
    (G₀ : QuasicoherentDerivedCategory.{u, u} B S hS X₀.1 X₀.2)
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X₀.1 X₀.2,
      CohomologySupportedOn B S hS X₀.1 X₀.2 T₀ E.obj →
        (∀ (n : ℤ) (h : G₀.obj⟦n⟧ ⟶ E.obj), h = 0) → IsZero E.obj)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hEs : CohomologySupportedOn B S hS X.1 X.2 (pointsMap B S hS X.1 g.hom ⁻¹' T₀) E.obj)
    (h0 : ∀ (n : ℤ) (h : ((quasicoherentDerivedModulePullback g).obj G₀).obj⟦n⟧ ⟶ E.obj),
      h = 0) :
    IsZero E.obj := by
  have hqc := isQuasiCompact_of_isAffineHom' B S hS g.hom X.2 X₀.2 hg
  have hqs := isQuasiSeparated_of_isAffineHom B S hS g.hom X.2 X₀.2 hg
  let L : DerivedCategory (Modules.{u, u} B S hS X₀.1 X₀.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) := smallEtaleDerivedModulePullback B S hS g
  let R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X₀.1 X₀.2) := derivedModulePushforward B S hS g
  let adj : L ⊣ R := smallEtaleDerivedModuleAdjunction B S hS g
  let : L.CommShift ℤ := commShift_smallEtaleDerivedModulePullback B S hS g
  refine isZero_of_isZero_derivedModulePushforward_of_isAffineHom B S hS g hg E.obj E.property ?_
  refine hgen ⟨R.obj E.obj, qcohDerived_derivedModulePushforward_obj B S hS g hqc hqs E.obj
    E.property⟩ (cohomologySupportedOn_derivedModulePushforward_of_isAffineHom g hg T₀ hT₀ E.obj
    E.property hEs) fun n h => ?_
  have key : (L.commShiftIso n).inv.app G₀.obj ≫ (adj.homEquiv _ _).symm h = 0 := h0 n _
  have key' : (adj.homEquiv _ _).symm h = 0 := by
    have := congrArg (fun k => (L.commShiftIso n).hom.app G₀.obj ≫ k) key
    simpa only [Iso.hom_inv_id_app_assoc, comp_zero] using this
  simpa only [Equiv.apply_symm_apply, Adjunction.homEquiv_apply, Functor.map_zero,
    comp_zero] using congrArg (adj.homEquiv _ _) key'

/-- The complement of the inverse image of a closed subset with quasi-compact complement along a
quasi-compact morphism into a quasi-separated space, inside a quasi-compact space, is
quasi-compact. -/
theorem isCompact_compl_preimage_of_isQuasiCompact {X X₀ : AlgebraicSpaces B S hS} (g : X ⟶ X₀)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X₀.1)
    (T₀ : Set (points B S hS X₀.1)) (hT₀ : IsClosed T₀) (hT₀c : IsCompact T₀ᶜ) :
    IsCompact (pointsMap B S hS X.1 g.hom ⁻¹' T₀)ᶜ := by
  have hT : IsClosed (pointsMap B S hS X.1 g.hom ⁻¹' T₀) :=
    hT₀.preimage (continuous_pointsMap B S hS g.hom)
  let G₀ := (openSubspacesOrderIso B S hS X₀.1 X₀.2).symm ⟨T₀ᶜ, hT₀.isOpen_compl⟩
  have hG₀qc : IsQuasiCompactSpace B S hS G₀.1.toFunctor :=
    isQuasiCompactSpace_of_isCompact_range B S hS X₀.2 G₀.2 (by
      rw [range_openSubspacesOrderIso_symm B S hS X₀.1 X₀.2 T₀ hT₀]
      exact hT₀c)
  have hι₀ : IsQuasiCompact B S hS G₀.1.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal X₀.2 hX₀qs hG₀qc G₀.1.ι
  have hι := isQuasiCompact_openSubspacesOrderIso_symm_preimage B S hS X₀.2 X.2 g.hom T₀ hT₀ hι₀
    hT
  let G := (openSubspacesOrderIso B S hS X.1 X.2).symm
    ⟨(pointsMap B S hS X.1 g.hom ⁻¹' T₀)ᶜ, hT.isOpen_compl⟩
  have hGqc : IsQuasiCompactSpace B S hS G.1.toFunctor :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc hι
  have := isCompact_range_of_isQuasiCompactSpace B S hS G.2 hGqc
  rwa [range_openSubspacesOrderIso_symm B S hS X.1 X.2 _ hT] at this

/-- **Generation of the supported perfect objects by pullbacks along an affine morphism.** Let
`g : X ⟶ X₀` be an affine morphism of quasi-compact and quasi-separated algebraic spaces and
`T₀ ⊆ |X₀|` a closed subset with `|X₀| ∖ T₀` quasi-compact. Let `Φ` be a property of objects of
`D(𝒪_X)` which is triangulated, stable under retracts and closed under isomorphisms, and which
holds for `Lg^*G₀` for every perfect `G₀ ∈ D(𝒪_{X₀})` with quasi-coherent cohomology supported
on `T₀`. Then `Φ` holds for every perfect object of `D(𝒪_X)` supported on `g⁻¹T₀`.

This is Stacks 0AEC on `X₀`, the pullback of the generator along `g`, and Stacks 0GFD on `X`. -/
theorem prop_of_isPerfect_of_cohomologySupportedOn_preimage {X X₀ : AlgebraicSpaces B S hS}
    (g : X ⟶ X₀) (hg : IsAffineHom B S hS g.hom)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀.1)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X₀.1)
    (T₀ : Set (points B S hS X₀.1)) (hT₀ : IsClosed T₀) (hT₀c : IsCompact T₀ᶜ)
    (Φ : ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)))
    [Φ.IsTriangulated] [Φ.IsStableUnderRetracts] [Φ.IsClosedUnderIsomorphisms]
    (hΦ : ∀ G₀ : DerivedCategory (Modules.{u, u} B S hS X₀.1 X₀.2),
      (smallEtaleRingedSite B S hS X₀.1 X₀.2).IsPerfect G₀ → QcohDerived B S hS X₀ G₀ →
        CohomologySupportedOn B S hS X₀.1 X₀.2 T₀ G₀ →
          Φ ((smallEtaleDerivedModulePullback B S hS g).obj G₀))
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hPs : CohomologySupportedOn B S hS X.1 X.2 (pointsMap B S hS X.1 g.hom ⁻¹' T₀) P) :
    Φ P := by
  obtain ⟨G₀, hG₀p, hG₀q, hG₀s, hG₀g⟩ :=
    exists_isPerfect_generator_of_supported B S hS X₀ hX₀qc hX₀qs T₀ hT₀ hT₀c
  let T := pointsMap B S hS X.1 g.hom ⁻¹' T₀
  have hT : IsClosed T := hT₀.preimage (continuous_pointsMap B S hS g.hom)
  have hTc := isCompact_compl_preimage_of_isQuasiCompact g hXqc hX₀qs T₀ hT₀ hT₀c
  let G := ((quasicoherentDerivedModulePullback g).obj ⟨G₀, hG₀q⟩).obj
  have hGp : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G :=
    isPerfect_smallEtaleDerivedModulePullback g G₀ hG₀p
  have hGq : QcohDerived B S hS X G :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 G
      (RingedSite.isPseudoCoherent_of_isPerfect_general
        (X := smallEtaleRingedSite B S hS X.1 X.2) (E := G) hGp)
  have hGs : CohomologySupportedOn B S hS X.1 X.2 T G :=
    cohomologySupportedOn_smallEtaleDerivedModulePullback g G₀ hG₀s
  have henv := triangEnvelope_singleton_eq_isPerfect_of_supported X hXqc hXqs T hT hTc G hGp hGq
    hGs fun E hEs h0 => isZero_of_forall_quasicoherentDerivedModulePullback_hom_eq_zero g hg T₀
      hT₀ ⟨G₀, hG₀q⟩ (fun E hEs h => (hG₀g E hEs).2 h) E hEs h0
  let ι := quasicoherentDerivedSupportedOnι X T
  let Ψ := Φ.inverseImage ι
  have : Ψ.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero _, Φ.prop_of_isZero (ι.map_isZero (isZero_zero _))⟩
      isStableUnderShiftBy := fun n => ⟨fun F hF =>
        Φ.prop_of_iso ((ι.commShiftIso n).app F).symm (Φ.le_shift n _ hF)⟩
      ext₂' := fun Tri hTri h₁ h₃ => ObjectProperty.le_isoClosure _ _
        (Φ.ext_of_isTriangulatedClosed₂ (ι.mapTriangle.obj Tri) (ι.map_distinguished Tri hTri)
          h₁ h₃) }
  have : Ψ.IsStableUnderRetracts := ⟨fun r hF => Φ.prop_of_retract (r.map ι) hF⟩
  have hle : (ObjectProperty.singleton
      (⟨⟨G, hGq⟩, hGs⟩ : (quasicoherentDerivedSupportedOn X T).FullSubcategory)).triangEnvelope ≤
      Ψ := by
    rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
    exact hΦ G₀ hG₀p hG₀q hG₀s
  have hPq : QcohDerived B S hS X P :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 P
      (RingedSite.isPseudoCoherent_of_isPerfect_general
        (X := smallEtaleRingedSite B S hS X.1 X.2) (E := P) hP)
  exact hle ⟨⟨P, hPq⟩, hPs⟩ (henv ▸ hP)

end AlgebraicGeometry.Space

end
