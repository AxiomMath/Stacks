module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwist
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.C1590Private.GlobalGenerationNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SemistableFibreGeneration
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SemistableFibreLocus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpen

/-!
# The locus of fibres without rational tails is open (Stacks 0E6Y)

Let `q : Z ⟶ U` be a proper, flat, finitely presented morphism of schemes whose fibres are proper
nodal curves with `H⁰ = κ` of a fixed genus `g ≥ 1`. The points `u ∈ U` whose fibre `Z_u` has no
rational tail form an open subset of `U`. This is the content of Stacks 0E6Y used for the openness
of `Curves^{semistable}` (Stacks 0E70), and the proof is the source's: with `ω = ω_{Z/U}` the
relative dualizing sheaf and `m = 1` in genus one, `m = 2` in genus at least two,

* at a point `u₀` whose fibre has no rational tail, `ω_{Z_{u₀}}^{⊗ m}` is globally generated with
  `dim H⁰ = r` (`r = 1`, resp. `r = 3g - 3`), while `dim H⁰(Z_u, ω_{Z_u}^{⊗ m}) ≥ r` at every `u`
  (`StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SemistableFibreGeneration`);
* hence, over a reduced base, the global sections of `ω^{⊗ m}` commute with base change near
  `u₀`, and global generation spreads from the fibre over `u₀` to the fibres over a neighbourhood
  (`AlgebraicGeometry.C1590Private.exists_away_nonempty_generatingSections`);
* a fibre on which `ω^{⊗ m}` is globally generated has no rational tail.

The base is first made affine and then reduced: the reduction `U_red ⟶ U` is a homeomorphism and
does not change the fibres up to extension of the residue fields, under which the absence of
rational tails is invariant (Stacks 0E3L,
`AlgebraicGeometry.C1590Private.hasPositiveGenusNoRationalTail_iff_of_isPullback`).

The relative dualizing sheaf is the input
`AlgebraicGeometry.C1590Private.HasNodalRelativeDualizingSheaf`
(Stacks 0E6P, 0E6Q, 0E6R).

## Main results

* `AlgebraicGeometry.C1590Private.exists_isOpen_noRationalTail_of_isReduced`: the case of a
  reduced affine base `Spec A`.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry.C1590Private

/-! ### Invertible modules: finite presentation, flatness, tensor powers and pullbacks -/

section Invertible

variable {X : Scheme.{u}}

/-- The pullback of a tensor power of an invertible module, along a morphism of schemes, is the
tensor power of the pullback, for every isomorphism of the pullback with an invertible module. -/
def pullbackTensorPowerIso {Y : Scheme.{u}} (h : Y ⟶ X) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (e : (Scheme.Modules.pullback h).obj L ≅ M) (n : ℤ) :
    (Scheme.Modules.pullback h).obj (tensorPower X.presheaf X.ringCatSheaf.2 L n) ≅
      tensorPower Y.presheaf Y.ringCatSheaf.2 M n :=
  haveI : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback h).obj L) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_pullback h L
  Stacks.Algebraization.pullbackTensorPowSchemeIso h L n ≪≫
    Stacks.Algebraization.tensorPowSchemeCongr Y e n

end Invertible

/-! ### The fibrewise facts, on a module identified with `ω^{⊗ m}` -/

section FibrePackage

variable {K : Type u} [Field K] {W : Scheme.{u}} [W.Over (Spec (.of K))]
  [IsProper (W ↘ Spec (.of K))] (hdim : topologicalKrullDim W = 1)
  [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (W ↘ Spec (.of K)).appTop)]
  (hnodal : Stacks.Curves.HasAtWorstNodalSingularities K W) {g : ℕ}
  (hgW : genus (W ↘ Spec (.of K)) = g) (M : W.Modules)
  (e : haveI := connectedSpace_of_isIso_globalSections K (W ↘ Spec (.of K))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K W hdim hnodal
    M ≅ tensorPower W.presheaf W.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (W ↘ Spec (.of K))) (semistablePower g))

include hdim hnodal hgW e

/-- The lower bound `dim Γ(W, M) ≥ r` on a module identified with `ω_W^{⊗ m}`. -/
theorem semistableRank_le_finrank_sections (hg : 1 ≤ g) :
    letI := Stacks.Cech.sectionsModule (W ↘ Spec (.of K)) M ⊤
    semistableRank g ≤ Module.finrank K Γ(M, ⊤) := by
  subst hgW
  rw [finrank_sections_eq, finrank_cohomologyOverField_zero_congr _ e]
  exact semistableRank_le_finrank K hdim hnodal hg

/-- Without rational tails, `dim Γ(W, M) ≤ r` and `M` is globally generated. -/
theorem finrank_sections_le_and_isGeneratedByGlobalSections (hg : 1 ≤ g)
    (htail : ∀ C : W.IdealSheafData, ¬ IsRationalTail K W C) :
    (letI := Stacks.Cech.sectionsModule (W ↘ Spec (.of K)) M ⊤;
    Module.finrank K Γ(M, ⊤) ≤ semistableRank g) ∧
      SheafOfModules.IsGeneratedByGlobalSections M := by
  subst hgW
  refine ⟨?_, Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso e.symm
    (isGeneratedByGlobalSections_of_noRationalTail K hdim hnodal hg htail)⟩
  rw [finrank_sections_eq, finrank_cohomologyOverField_zero_congr _ e]
  exact finrank_le_semistableRank K hdim hnodal hg htail

/-- If `M` is globally generated, `W` has no rational tail. -/
theorem noRationalTail_of_isGeneratedByGlobalSections_of_iso
    (h : SheafOfModules.IsGeneratedByGlobalSections M) :
    ∀ C : W.IdealSheafData, ¬ IsRationalTail K W C := by
  subst hgW
  exact noRationalTail_of_isGeneratedByGlobalSections K hdim hnodal
    (Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso e h)

end FibrePackage

/-! ### A reduced affine base -/

/-- The fibre of a proper morphism over a point is proper over the residue field. -/
private theorem isProper_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (y : Y) : IsProper (f.fiberToSpecResidueField y) :=
  inferInstanceAs (IsProper (pullback.snd _ _))

section Reduced

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The ring map `A → κ(u)` of the residue field of a point of `Spec A`. -/
def residueRingHom (u : Spec (.of A)) : A →+* (Spec (.of A)).residueField u :=
  (Spec.preimage ((Spec (.of A)).fromSpecResidueField u)).hom

/-- `Spec` of `residueRingHom u` is the canonical morphism `Spec κ(u) ⟶ Spec A`. -/
theorem spec_map_residueRingHom (u : Spec (.of A)) :
    Spec.map (CommRingCat.ofHom (residueRingHom u)) = (Spec (.of A)).fromSpecResidueField u :=
  Spec.map_preimage _

/-- The kernel of `A → κ(u)` is the prime ideal of `A` corresponding to `u`. -/
theorem ker_residueRingHom (u : Spec (.of A)) :
    RingHom.ker (residueRingHom u) = (show PrimeSpectrum A from u).asIdeal := by
  have h := congrArg (fun x : Spec (.of A) => (show PrimeSpectrum A from x).asIdeal)
    (congrArg (fun g : Spec ((Spec (.of A)).residueField u) ⟶ Spec (.of A) =>
      g (IsLocalRing.closedPoint _)) (spec_map_residueRingHom u))
  refine Eq.trans ?_ (h.trans (congrArg (fun x : Spec (.of A) =>
    (show PrimeSpectrum A from x).asIdeal)
      (Scheme.fromSpecResidueField_apply u (IsLocalRing.closedPoint _))))
  change RingHom.ker (residueRingHom u) =
    Ideal.comap (residueRingHom u) (IsLocalRing.maximalIdeal _)
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]

/-- The fibre over a point of `Spec A`, as a base change along `A → κ(u)`. -/
theorem isPullback_fiberι_residueRingHom (u : Spec (.of A)) :
    IsPullback (f.fiberι u) (f.fiberToSpecResidueField u) f
      (Spec.map (CommRingCat.ofHom (residueRingHom u))) :=
  (spec_map_residueRingHom u).symm ▸ IsPullback.of_hasPullback _ _

/-- The fibre of `f` over `u`, as a scheme over the spectrum of `κ(u)` read as a field. -/
abbrev fiberOver (u : Spec (.of A)) :
    (f.fiber u).Over (Spec (.of ((Spec (.of A)).residueField u))) :=
  ⟨f.fiberToSpecResidueField u⟩

/-- The fibre of `f` over `u` is a proper nodal curve with `H⁰ = κ(u)`. -/
abbrev IsNodalCurveFiber (u : Spec (.of A)) : Prop :=
  letI := fiberOver f u
  topologicalKrullDim (f.fiber u) = 1 ∧
    IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of A)).residueField u))).inv ≫
      (f.fiber u ↘ Spec (.of ((Spec (.of A)).residueField u))).appTop) ∧
    Stacks.Curves.HasAtWorstNodalSingularities ((Spec (.of A)).residueField u) (f.fiber u)

/-- The fibre of `f` over `u` has no rational tail. -/
abbrev HasNoRationalTailFiber (u : Spec (.of A)) : Prop :=
  letI := fiberOver f u
  ∀ C : (f.fiber u).IdealSheafData, ¬ IsRationalTail ((Spec (.of A)).residueField u) (f.fiber u) C

/-- **Stacks 0E6Y over a reduced affine base.** Let `f : X ⟶ Spec A` be proper, flat, of finite
presentation and at-worst-nodal of relative dimension one, with `A` reduced, and let every fibre
be a curve with `H⁰ = κ` of genus `g ≥ 1`. If the fibre over `u₀` has no rational tail, neither
has the fibre over any point of a neighbourhood of `u₀`. -/
theorem exists_isOpen_noRationalTail_of_isReduced (hω : HasNodalRelativeDualizingSheaf.{u})
    [_root_.IsReduced A] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hnod : IsAtWorstNodalOfRelativeDimensionOne f) (hfib : ∀ u, IsNodalCurveFiber f u)
    {g : ℕ} (hg : 1 ≤ g) (hgen : ∀ u, genus (f.fiberToSpecResidueField u) = g)
    (u₀ : Spec (.of A)) (h₀ : HasNoRationalTailFiber f u₀) :
    ∃ N : (Spec (.of A)).Opens, u₀ ∈ N ∧ ∀ u ∈ N, HasNoRationalTailFiber f u := by
  classical
  obtain ⟨ω, hωinv, hωfib⟩ := hω f hnod
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω := hωinv
  have hLinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPower X.presheaf X.ringCatSheaf.2 ω (semistablePower g)) :=
    tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 ω (semistablePower g)
  set L := tensorPower X.presheaf X.ringCatSheaf.2 ω (semistablePower g) with hL
  have key : ∀ u : Spec (.of A),
      (let : Module ((Spec (.of A)).residueField u)
          Γ((Scheme.Modules.pullback (f.fiberι u)).obj L, ⊤) :=
        Stacks.Cech.sectionsModule (f.fiberToSpecResidueField u)
          ((Scheme.Modules.pullback (f.fiberι u)).obj L) ⊤;
      semistableRank g ≤ Module.finrank ((Spec (.of A)).residueField u)
        Γ((Scheme.Modules.pullback (f.fiberι u)).obj L, ⊤)) ∧
      (HasNoRationalTailFiber f u →
        (let : Module ((Spec (.of A)).residueField u)
            Γ((Scheme.Modules.pullback (f.fiberι u)).obj L, ⊤) :=
          Stacks.Cech.sectionsModule (f.fiberToSpecResidueField u)
            ((Scheme.Modules.pullback (f.fiberι u)).obj L) ⊤;
        Module.finrank ((Spec (.of A)).residueField u)
          Γ((Scheme.Modules.pullback (f.fiberι u)).obj L, ⊤) ≤ semistableRank g) ∧
          SheafOfModules.IsGeneratedByGlobalSections
            ((Scheme.Modules.pullback (f.fiberι u)).obj L)) ∧
      (SheafOfModules.IsGeneratedByGlobalSections
        ((Scheme.Modules.pullback (f.fiberι u)).obj L) → HasNoRationalTailFiber f u) := by
    intro u
    let := fiberOver f u
    obtain ⟨hdim, hH0, hnodal⟩ := hfib u
    have := hH0
    have : IsProper (f.fiber u ↘ Spec (.of ((Spec (.of A)).residueField u))) :=
      isProper_fiberToSpecResidueField f u
    have := connectedSpace_of_isIso_globalSections ((Spec (.of A)).residueField u)
      (f.fiber u ↘ Spec (.of ((Spec (.of A)).residueField u)))
    have hωu : SheafOfModules.IsInvertible (f.fiber u).presheaf (f.fiber u).ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField
          (f.fiber u ↘ Spec (.of ((Spec (.of A)).residueField u)))) :=
      isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities
        ((Spec (.of A)).residueField u) (f.fiber u) hdim hnodal
    have : Stacks.Ample.IsInvertibleModule (f.fiber u)
        (Stacks.Duality.dualizingSheafOverField
          (f.fiber u ↘ Spec (.of ((Spec (.of A)).residueField u)))) := hωu
    have e₀ : (Scheme.Modules.pullback (f.fiberι u)).obj ω ≅ Stacks.Duality.dualizingSheafOverField
        (f.fiber u ↘ Spec (.of ((Spec (.of A)).residueField u))) := (hωfib u).some
    have e := pullbackTensorPowerIso (f.fiberι u) ω _ e₀ (semistablePower g)
    exact ⟨semistableRank_le_finrank_sections hdim hnodal (hgen u) _ e hg,
      fun htail => finrank_sections_le_and_isGeneratedByGlobalSections hdim hnodal (hgen u) _ e
        hg htail,
      noRationalTail_of_isGeneratedByGlobalSections_of_iso hdim hnodal (hgen u) _ e⟩
  have : Stacks.Ample.IsInvertibleModule X L := hLinv
  obtain ⟨g', hg'u₀, hgen'⟩ := exists_away_nonempty_generatingSections f L
    (show PrimeSpectrum A from u₀).asIdeal
    (semistableRank g)
    ⟨_, inferInstance, residueRingHom u₀, ker_residueRingHom u₀, f.fiber u₀,
      f.fiberToSpecResidueField u₀, f.fiberι u₀, isPullback_fiberι_residueRingHom f u₀,
      ((key u₀).2.1 h₀).1, ((key u₀).2.1 h₀).2⟩
    (fun q _ => ⟨_, inferInstance, residueRingHom (show Spec (.of A) from ⟨q, inferInstance⟩),
      ker_residueRingHom _, _, _, _, isPullback_fiberι_residueRingHom f _, (key _).1⟩)
  refine ⟨PrimeSpectrum.basicOpen g', hg'u₀, fun u hu => (key u).2.2 ?_⟩
  refine hgen' (residueRingHom u) (fun h => hu ?_) (isPullback_fiberι_residueRingHom f u)
  rwa [← SetLike.mem_coe, ← ker_residueRingHom u]

end Reduced

/-! ### Fibres under a change of base -/

section FieldExtension

/-- **Prestable curves over a field stay prestable after extension of the ground field.** -/
theorem prestable_properties_of_isPullback {k K : Type u} [Field k] [Field K] (φ : k →+* K)
    {V W : Scheme.{u}} (a : W ⟶ V) (w : W ⟶ Spec (.of K)) (fV : V ⟶ Spec (.of k))
    (h : IsPullback a w fV (Spec.map (CommRingCat.ofHom φ))) [IsProper fV]
    (hdim : topologicalKrullDim V = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fV.appTop)]
    (hnodal : letI : V.Over (Spec (.of k)) := ⟨fV⟩;
      Stacks.Curves.HasAtWorstNodalSingularities k V) :
    IsProper w ∧ topologicalKrullDim W = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ w.appTop) ∧
      (letI : W.Over (Spec (.of K)) := ⟨w⟩; Stacks.Curves.HasAtWorstNodalSingularities K W) := by
  let : Algebra k K := φ.toAlgebra
  set g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have h' : IsPullback a w fV g := h
  have hpb : IsPullback (pullback.fst fV g) (pullback.snd fV g) fV g :=
    IsPullback.of_hasPullback _ _
  let : V.Over (Spec (.of k)) := ⟨fV⟩
  have : LocallyOfFiniteType (V ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType fV)
  have hequi : TopologicalSpace.Equidimensional V :=
    equidimensional_of_isIso_globalSections_of_dimension_one k fV hdim
  refine prestable_properties_of_iso h'.isoPullback h'.isoPullback_hom_snd
    ⟨inferInstance, ?_, isIso_globalSections_baseChange k K _ _ fV hpb,
      Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K V hequi hdim hnodal⟩
  rw [topologicalKrullDim_baseChange k K _ _ fV hpb, hdim]

end FieldExtension

section BaseChangeFibre

variable {Z U Z' U' : Scheme.{u}} {q : Z ⟶ U} {ι : U' ⟶ U} {q' : Z' ⟶ U'} {ι' : Z' ⟶ Z}

/-- **The fibre of a base change.** For a cartesian square `Z' = Z ×_U U'` and a point `u'` of
`U'`, the fibre of `Z'` over `u'` is the base change of the fibre of `Z` over the image of `u'`
along the extension of residue fields. -/
theorem exists_isPullback_fiber (hsq : IsPullback ι' q' q ι) (u' : U') :
    ∃ a : q'.fiber u' ⟶ q.fiber (ι u'), IsPullback a (q'.fiberToSpecResidueField u')
      (q.fiberToSpecResidueField (ι u')) (Spec.map (ι.residueFieldMap u')) := by
  have h₁ : IsPullback (q.fiberι (ι u')) (q.fiberToSpecResidueField (ι u')) q
      (U.fromSpecResidueField (ι u')) := IsPullback.of_hasPullback _ _
  have h₂ : IsPullback (q'.fiberι u' ≫ ι') (q'.fiberToSpecResidueField u') q
      (Spec.map (ι.residueFieldMap u') ≫ U.fromSpecResidueField (ι u')) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    exact (IsPullback.of_hasPullback q' (U'.fromSpecResidueField u')).paste_horiz hsq
  refine ⟨h₁.lift (q'.fiberι u' ≫ ι') (q'.fiberToSpecResidueField u' ≫
      Spec.map (ι.residueFieldMap u')) (by rw [h₂.w, Category.assoc]),
    IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rwa [h₁.lift_fst]

end BaseChangeFibre

/-! ### An arbitrary affine base -/

section Affine

/-- The reduction of the spectrum of the ring of global functions of an affine scheme, mapping to
the scheme. -/
def reductionToAffine (U : Scheme.{u}) [IsAffine U] :
    Spec (.of (Γ(U, ⊤) ⧸ nilradical Γ(U, ⊤))) ⟶ U :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical Γ(U, ⊤)))) ≫ U.isoSpec.inv

/-- The morphism `reductionToAffine U` is surjective and open. -/
theorem surjective_and_isOpenMap_reductionToAffine (U : Scheme.{u}) [IsAffine U] :
    Function.Surjective (reductionToAffine U) ∧ IsOpenMap (reductionToAffine U) := by
  set I := nilradical Γ(U, ⊤)
  have hce : Topology.IsClosedEmbedding
      (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [← Set.range_eq_univ, range_comap_of_surjective (hf := Ideal.Quotient.mk_surjective),
      Ideal.mk_ker]
    exact PrimeSpectrum.zeroLocus_nilradical
  have hι : ∀ x, reductionToAffine U x =
      (Scheme.homeoOfIso U.isoSpec.symm) (PrimeSpectrum.comap (Ideal.Quotient.mk I) x) := by
    intro x
    rw [reductionToAffine, Scheme.Hom.comp_apply, Scheme.coe_homeoOfIso_symm]
    rfl
  refine ⟨fun y => ?_, fun s hs => ?_⟩
  · obtain ⟨z, hz⟩ := (Scheme.homeoOfIso U.isoSpec.symm).surjective y
    obtain ⟨x, rfl⟩ := hsurj z
    exact ⟨x, (hι x).trans hz⟩
  · have himg : reductionToAffine U '' s = (Scheme.homeoOfIso U.isoSpec.symm) ''
        (PrimeSpectrum.comap (Ideal.Quotient.mk I) '' s) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩, (hι x).symm⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, hι x⟩
    rw [himg]
    exact (Scheme.homeoOfIso U.isoSpec.symm).isOpenMap _
      ((hce.toIsEmbedding.toHomeomorphOfSurjective hsurj).isOpenMap s hs)

/-- The quotient of `Γ(U, ⊤)` by its nilradical is reduced. -/
instance (U : Scheme.{u}) : _root_.IsReduced (Γ(U, ⊤) ⧸ nilradical Γ(U, ⊤)) :=
  (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical ⊥)

/-- **Stacks 0E6Y: the locus of fibres without rational tails is open, over an affine base.**
Let `q : Z ⟶ U` be proper, flat, of finite presentation and at-worst-nodal of relative dimension
one over an affine scheme, and let every fibre be a curve with `H⁰ = κ` of genus `g ≥ 1`. If the
fibre over `u₀` has no rational tail, neither has the fibre over any point of a neighbourhood of
`u₀`. The base is replaced by its reduction, which is homeomorphic to it and changes the fibres
only by extension of the residue fields. -/
theorem exists_isOpen_noRationalTail_of_isAffine (hω : HasNodalRelativeDualizingSheaf.{u})
    {Z U : Scheme.{u}} (q : Z ⟶ U) [IsAffine U] [IsProper q] [Flat q]
    [LocallyOfFinitePresentation q] (hnod : IsAtWorstNodalOfRelativeDimensionOne q)
    (hfib : ∀ u : U, topologicalKrullDim (q.fiber u) = 1 ∧
      IsIso ((Scheme.ΓSpecIso (U.residueField u)).inv ≫ (q.fiberToSpecResidueField u).appTop) ∧
      (letI : (q.fiber u).Over (Spec (U.residueField u)) := ⟨q.fiberToSpecResidueField u⟩;
        Stacks.Curves.HasAtWorstNodalSingularities (U.residueField u) (q.fiber u)))
    {g : ℕ} (hg : 1 ≤ g) (hgen : ∀ u, genus (q.fiberToSpecResidueField u) = g)
    (u₀ : U)
    (h₀ : HasPositiveGenusNoRationalTail (U.residueField u₀) (q.fiberToSpecResidueField u₀)) :
    ∃ N : U.Opens, u₀ ∈ N ∧ ∀ u ∈ N,
      HasPositiveGenusNoRationalTail (U.residueField u) (q.fiberToSpecResidueField u) := by
  set ι := reductionToAffine U
  obtain ⟨hιs, hιo⟩ := surjective_and_isOpenMap_reductionToAffine U
  set q' := pullback.snd q ι
  have hsq : IsPullback (pullback.fst q ι) q' q ι := IsPullback.of_hasPullback _ _
  have hnod' : IsAtWorstNodalOfRelativeDimensionOne q' :=
    IsAtWorstNodalOfRelativeDimensionOne.of_isPullback hsq hnod
  have hpr := isProper_fiberToSpecResidueField q
  have hfib' : ∀ u' : Spec (.of (Γ(U, ⊤) ⧸ nilradical Γ(U, ⊤))),
      IsNodalCurveFiber q' u' ∧ genus (q'.fiberToSpecResidueField u') = g ∧
      (HasPositiveGenusNoRationalTail ((Spec (.of (Γ(U, ⊤) ⧸ nilradical Γ(U, ⊤)))).residueField u')
          (q'.fiberToSpecResidueField u') ↔
        HasPositiveGenusNoRationalTail (U.residueField (ι u'))
          (q.fiberToSpecResidueField (ι u'))) := by
    intro u'
    obtain ⟨a, ha⟩ := exists_isPullback_fiber hsq u'
    have ha' : IsPullback a (q'.fiberToSpecResidueField u') (q.fiberToSpecResidueField (ι u'))
        (Spec.map (CommRingCat.ofHom (ι.residueFieldMap u').hom)) := ha
    obtain ⟨hdim, hH0, hnodal⟩ := hfib (ι u')
    have := hpr (ι u')
    obtain ⟨-, hdim', hH0', hnodal'⟩ := @prestable_properties_of_isPullback _ _ _ _ _ _ _ a _ _
      ha' (hpr (ι u')) hdim hH0 hnodal
    refine ⟨⟨hdim', hH0', hnodal'⟩, ?_, @hasPositiveGenusNoRationalTail_iff_of_isPullback _ _ _ _
      _ _ _ a _ _ ha' (hpr (ι u')) hdim hH0 hnodal⟩
    exact (@genus_eq_of_isPullback _ _ _ _ _ _ _ a _ _ ha' (hpr (ι u'))).trans (hgen _)
  obtain ⟨u₀', rfl⟩ := hιs u₀
  obtain ⟨N', hu₀', hN'⟩ := exists_isOpen_noRationalTail_of_isReduced q' hω hnod'
    (fun u' => (hfib' u').1) hg (fun u' => (hfib' u').2.1) u₀' ((hfib' u₀').2.2.2 h₀).2
  refine ⟨⟨ι '' N', hιo _ N'.2⟩, ⟨u₀', hu₀', rfl⟩, ?_⟩
  rintro _ ⟨u', hu', rfl⟩
  exact (hfib' u').2.2.1 ⟨hg.trans_eq (hfib' u').2.1.symm, hN' u' hu'⟩

end Affine

end AlgebraicGeometry.C1590Private

end
