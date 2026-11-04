module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.AmpleNoRationalBridge
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelLocal
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierDivisorDimension
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.TricanonicalVeryAmple
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase

/-!
# Stable curves over a field through the ampleness of the dualizing sheaf (Stacks 0E74, 0E76)

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities. Then `X` has genus at least two and neither a rational tail nor a
rational bridge exactly when its dualizing sheaf `ω_X` is ample: this is the fibrewise content of
Stacks 0E74, and the equivalence of (2)(b) and (2)(c) in Stacks 0E76. The forward direction is
Stacks 0E3P. Conversely an ample `ω_X` has positive degree on every rational tail and bridge
(Stacks 0E63, 0E64), and positive total degree `2g - 2` (Stacks 0C19, 0AYW, 0B5Y), so `g ≥ 2`.

Through this characterization stability is insensitive to the ground field, as the proof of
Stacks 0E76 says ("ampleness is insensitive to base field extensions by Descent, Lemma 0D2P"):
for a field extension `K/k` the dualizing sheaf of `X_K` is the pullback of `ω_X` (Stacks 0E32),
and ampleness of an invertible module ascends and descends along the fpqc covering
`Spec K → Spec k` (Stacks 0D2P), ampleness over a field being relative ampleness (Stacks 01VK).

## Main results

* `AlgebraicGeometry.C1590Private.invertibleCurveDegree_pos_of_isAmple`: an ample invertible
  module on an equidimensional proper curve over a field has positive degree.
* `AlgebraicGeometry.C1590Private.isStableCurveOver_iff_isAmple`: a proper nodal curve of
  dimension one with `H⁰ = k` is stable exactly when its dualizing sheaf is ample.
* `AlgebraicGeometry.C1590Private.isStableCurveOver_of_iso`: stability is invariant under
  isomorphism over the field.
* `AlgebraicGeometry.C1590Private.isStableCurveOver_iff_of_isPullback`: stability is invariant
  under extension of the ground field.

## Implementation notes

These are unregistered helpers towards the openness of the stable locus (Stacks 0E76).
Everything here is unconditional.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

open Stacks.AlgebraicGeometry.ComponentDegrees in
/-- **An ample invertible module on a proper curve over a field has positive degree.** Let `X` be
nonempty, proper over `k`, equidimensional of dimension one, and `𝓛` invertible and ample. By
Stacks 0AYW `deg 𝓛` is the sum over the one-dimensional components `C` of
`length(𝒪_{X,ξ_C}) · deg(𝓛|_C)`; every multiplicity is positive, every `deg(𝓛|_C)` is positive by
Stacks 0B5Y, and there is a component, every component being one-dimensional. -/
theorem invertibleCurveDegree_pos_of_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Nonempty X] (hdim : topologicalKrullDim X = 1)
    (heq : TopologicalSpace.Equidimensional X) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k f hdim.le L := by
  classical
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  let : Fintype (genericPointsOne X) := (finite_genericPointsOne X).fintype
  -- an irreducible component, of dimension one by equidimensionality
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨Z, hZ, -⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible ({x} : Set X) isIrreducible_singleton
  have hZdim : topologicalKrullDim Z = 1 := by
    refine le_antisymm (hdim ▸ topologicalKrullDim_subspace_le X Z) ?_
    rw [← hdim, Stacks.Chow.topologicalKrullDim_eq_iSup_irreducibleComponents]
    exact iSup_le fun W => iSup_le fun hW => (heq W hW Z hZ).le
  have hcl : closure ({hZ.1.genericPoint} : Set X) = Z :=
    hZ.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  let ξ : genericPointsOne X := ⟨hZ.1.genericPoint, mem_genericPointsOne_iff.2
    ⟨show closure ({hZ.1.genericPoint} : Set X) ∈ irreducibleComponents X by rw [hcl]; exact hZ,
      by rw [hcl]; exact hZdim⟩⟩
  rw [invertibleCurveDegree_eq_curveDegree_one,
    Stacks.AlgebraicGeometry.ComponentDegreeDevissage.curveDegree_eq_finsum_componentDegree k f
      hdim.le L 1, finsum_eq_sum_of_fintype]
  refine Finset.sum_pos (fun η _ => mul_pos ?_ ?_) ⟨ξ, Finset.mem_univ _⟩
  · have hpos : 0 < Module.length (X.presheaf.stalk η.1) (X.presheaf.stalk η.1) :=
      Module.length_pos
    rw [← componentMultiplicity_cast k f η] at hpos
    exact_mod_cast hpos
  · have h := invertibleCurveDegree_reducedComponent_pos_of_isAmple k f hdim.le L hL η
    rwa [invertibleCurveDegree_eq_curveDegree_one] at h

/-- **An ample dualizing sheaf forces genus at least two.** On a proper nodal curve of dimension
one over `k` with `H⁰ = k`, which is Gorenstein and connected, `deg ω_X = 2g - 2` (Stacks 0C19),
and this degree is positive when `ω_X` is ample. -/
theorem two_le_genus_of_isAmple_dualizingSheafOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩; Stacks.Curves.HasAtWorstNodalSingularities k X)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)]
    (hL : Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField f)) :
    2 ≤ genus f := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  have heq := equidimensional_of_isIso_globalSections_of_dimension_one k f hdim
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  have : IsGorenstein X :=
    Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k X heq hdim hnodal
  have hdeg := invertibleCurveDegree_dualizingSheafOverField k f hdim
  have hpos := invertibleCurveDegree_pos_of_isAmple k f hdim heq _ hL
  rw [hdeg] at hpos
  omega

/-- **Stacks 0E74 on a curve over a field.** A proper scheme of dimension one over `k` with
`H⁰ = k` and at-worst-nodal singularities is a stable curve exactly when its dualizing sheaf is
invertible and ample: the forward direction is Stacks 0E3P, the converse excludes rational tails
(Stacks 0E63) and rational bridges (Stacks 0E64) and bounds the genus by Stacks 0C19. -/
theorem isStableCurveOver_iff_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X = 1)
    [hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩; Stacks.Curves.HasAtWorstNodalSingularities k X) :
    IsStableCurveOver k f ↔
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField f),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField f) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hH0
  constructor
  · rintro ⟨-, -, -, -, hg, htail, hp, hbridge⟩
    exact isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal htail
      hbridge hg
  · rintro ⟨hinv, hL⟩
    have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) := hinv
    have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
    exact ⟨inferInstance, hdim, hH0, hnodal,
      two_le_genus_of_isAmple_dualizingSheafOverField k f hdim hnodal hL,
      forall_not_isRationalTail_of_isAmple_dualizingSheafOverField hdim hnodal hL,
      inferInstance, not_isRationalBridge_of_isAmple_dualizingSheafOverField k X hdim hnodal hL⟩

/-- **The conditions of a prestable curve over a field are invariant under isomorphism over the
field**: properness, dimension one, `H⁰ = k` and at-worst-nodal singularities. -/
theorem prestable_properties_of_iso {k : Type u} [Field k] {W W₀ : Scheme.{u}}
    {g : W ⟶ Spec (.of k)} {g₀ : W₀ ⟶ Spec (.of k)} (e : W ≅ W₀) (he : e.hom ≫ g₀ = g)
    (h₀ : IsProper g₀ ∧ topologicalKrullDim W₀ = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g₀.appTop) ∧
      (letI : W₀.Over (Spec (.of k)) := ⟨g₀⟩; Stacks.Curves.HasAtWorstNodalSingularities k W₀)) :
    IsProper g ∧ topologicalKrullDim W = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ∧
      (letI : W.Over (Spec (.of k)) := ⟨g⟩; Stacks.Curves.HasAtWorstNodalSingularities k W) := by
  obtain ⟨hp₀, hdim₀, hH0₀, hnodal₀⟩ := h₀
  have := hp₀
  have := hH0₀
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  refine ⟨by rw [← he]; infer_instance, ?_, ?_, ?_⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph, hdim₀]
  · rw [← he, Scheme.Hom.comp_appTop, ← Category.assoc]
    infer_instance
  · exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso g₀ g hdim₀ e.hom (𝟙 _)
      (by rw [Spec.map_id, Category.comp_id, he]) hnodal₀

/-- **Stability is invariant under isomorphism over the field.** -/
theorem isStableCurveOver_of_iso {k : Type u} [Field k] {W W₀ : Scheme.{u}}
    {g : W ⟶ Spec (.of k)} {g₀ : W₀ ⟶ Spec (.of k)} (e : W ≅ W₀) (he : e.hom ≫ g₀ = g)
    (h₀ : IsStableCurveOver k g₀) : IsStableCurveOver k g := by
  obtain ⟨hp₀, hdim₀, hH0₀, hnodal₀, hst₀⟩ := h₀
  obtain ⟨hp, hdim, hH0, hnodal⟩ :=
    prestable_properties_of_iso e he ⟨hp₀, hdim₀, hH0₀, hnodal₀⟩
  have := hp₀
  have := hH0₀
  have := hp
  have := hH0
  rw [isStableCurveOver_iff_isAmple k g hdim hnodal]
  exact isAmple_dualizingSheafOverField_of_iso g g₀ hdim hnodal e he
    ((isStableCurveOver_iff_isAmple k g₀ hdim₀ hnodal₀).1 ⟨hp₀, hdim₀, hH0₀, hnodal₀, hst₀⟩)

/-- **Ampleness ascends and descends along an extension of the ground field.** For a proper
`f : X ⟶ Spec k`, an invertible `𝓛` on `X` and the base change `X' = X_K` along a field
extension `K/k`, `𝓛` is ample exactly when its pullback to `X'` is. Over the spectrum of a field
ampleness is relative ampleness (Stacks 01VK), and relative ampleness is fpqc local on the base
(Stacks 0D2P), `Spec K ⟶ Spec k` being an fpqc covering. -/
theorem isAmple_iff_isAmple_pullback_of_isPullback {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g' : X' ⟶ X)
    (f' : X' ⟶ Spec (.of K))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (L : X.Modules) [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property ((Scheme.Modules.pullback g').obj L)] :
    Scheme.Modules.IsAmple X L ↔
      Scheme.Modules.IsAmple X' ((Scheme.Modules.pullback g').obj L) := by
  let γ : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hcov : Presieve.ofArrows (fun _ : PUnit.{u + 1} => Spec (.of K)) (fun _ => γ) ∈
      Scheme.fpqcPrecoverage (Spec (.of k)) := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage γ
  let e : (Stacks.AmpleLocallyClosed.pullbackModule g' L) ≅ (Scheme.Modules.pullback g').obj L :=
    ((Stacks.ProjectiveBundleQuotients.pullbackIso g').app L).symm
  have : SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property
      (Stacks.AmpleLocallyClosed.pullbackModule g' L) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
  rw [← Scheme.Modules.isRelativelyAmple_iff_isAmple f L,
    Stacks.Descent.isRelativelyAmple_iff_forall_of_fpqcCover hcov f L
      (p := fun _ => g') (f' := fun _ => f') (fun _ => h),
    ← Scheme.Modules.isRelativelyAmple_iff_isAmple f' ((Scheme.Modules.pullback g').obj L)]
  exact ⟨fun h' => (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (h' PUnit.unit),
    fun h' _ => (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mpr h'⟩

/-- **Stability is insensitive to extension of the ground field.** Let `X` be a proper scheme of
dimension one over `k` with `H⁰ = k` and at-worst-nodal singularities, and `X'` the base change
along a field extension `K/k`, again of dimension one with `H⁰ = K` and nodal. Then `X` is stable
exactly when `X'` is: `ω_{X'}` is the pullback of `ω_X` (Stacks 0E32), and ampleness ascends and
descends along `Spec K ⟶ Spec k` (Stacks 0D2P). -/
theorem isStableCurveOver_iff_of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (g' : X' ⟶ X)
    (f' : X' ⟶ Spec (.of K))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩; Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hdim' : topologicalKrullDim X' = 1) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop)]
    (hnodal' : letI : X'.Over (Spec (.of K)) := ⟨f'⟩;
      Stacks.Curves.HasAtWorstNodalSingularities K X') :
    IsStableCurveOver k f ↔ IsStableCurveOver K f' := by
  have : IsProper f' := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
  rw [isStableCurveOver_iff_isAmple k f hdim hnodal,
    isStableCurveOver_iff_isAmple K f' hdim' hnodal']
  let : X.Over (Spec (.of k)) := ⟨f⟩
  let : X'.Over (Spec (.of K)) := ⟨f'⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : IsProper (X' ↘ Spec (.of K)) := inferInstanceAs (IsProper f')
  have := connectedSpace_of_isIso_globalSections k f
  have := connectedSpace_of_isIso_globalSections K f'
  have hω : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have hω' : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f') :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K X' hdim' hnodal'
  let e := Stacks.Duality.dualizingSheafOverFieldBaseChangeIso f g' f' h
  have : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have key := isAmple_iff_isAmple_pullback_of_isPullback f g' f' h
    (Stacks.Duality.dualizingSheafOverField f)
  exact ⟨fun ⟨_, hL⟩ => ⟨hω', Scheme.Modules.isAmple_of_iso e (key.mp hL)⟩,
    fun ⟨_, hL⟩ => ⟨hω, key.mpr (Scheme.Modules.isAmple_of_iso e.symm hL)⟩⟩

end AlgebraicGeometry.C1590Private

end
