module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Functorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Normalization and extension of the ground field

Let `X` be a scheme locally of finite type over a field `k` and let `K/k` be an extension of
fields.  The normalization of the base change `X_K` maps canonically to the base change of the
normalization of `X`.

The construction is the one of the source: a flat morphism carries generic points to generic
points, so it induces a morphism on the coproducts of the generic-point residue spectra, and
functoriality of relative normalization then supplies a morphism of normalizations over it.
Applying this to the projection `X_K ⟶ X`, which is flat because `Spec K ⟶ Spec k` is, and
pairing the result with the structure morphism of `X_K` gives the comparison morphism into the
fibre product.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.genericPointResidueSpectrumMap` is the morphism of generic-point
  residue spectra induced by a flat morphism.
* `AlgebraicGeometry.normalizationSchemeMap` is the morphism of normalizations induced by a flat
  morphism.
* `AlgebraicGeometry.baseChangeNormalization` is the base change to `K` of the normalization
  morphism of `X`.
* `AlgebraicGeometry.normalizationBaseChangeComparison` is the canonical comparison from the
  normalization after base change to the base change of the normalization.

## Main results

* `AlgebraicGeometry.mem_genericPoints_of_generalizingMap`: a map along which generalizations
  lift carries generic points to generic points.
* `AlgebraicGeometry.normalizationSchemeMap_normalization`: the induced morphism of
  normalizations commutes with the normalization morphisms.
* `AlgebraicGeometry.normalizationBaseChangeComparison_comp_fst` and
  `AlgebraicGeometry.normalizationBaseChangeComparison_comp_snd` identify the two projections of
  the comparison, and
  `AlgebraicGeometry.normalizationBaseChangeComparison_comp_baseChangeNormalization` identifies
  its composite with the base-changed normalization morphism.

## Implementation notes

Schemes over a field are represented as objects of the over category, and base change is the
pullback functor on that category.  Local finite type over a field implies local
Noetherianness, which supplies the finiteness of irreducible components of quasi-compact opens
required to normalize; this is
`AlgebraicGeometry.finite_irreducibleComponents_of_locallyOfFiniteType`.

The source deduces that the projection `X_K ⟶ X` carries generic points to generic points from
the fact that it is surjective, open and generizing.  Openness is not needed: lifting
generalizations alone gives the conclusion, and a flat morphism lifts generalizations by
`AlgebraicGeometry.Flat.generalizingMap`.  Flatness of the projection is base change from
`Spec K ⟶ Spec k`, which is flat because every module over a field is flat.

The two remaining assertions of Tag 0C3N — that the comparison is a universal homeomorphism in
general, and an isomorphism for a separable extension — are not proved here.

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Generic points and lifting of generalizations -/

/-- A map along which generalizations lift carries generic points of irreducible components to
generic points of irreducible components. -/
theorem mem_genericPoints_of_generalizingMap
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [T0Space S] [T0Space T]
    [QuasiSober S] [QuasiSober T] {f : S → T} (hf : GeneralizingMap f)
    {x : S} (hx : x ∈ genericPoints S) : f x ∈ genericPoints T := by
  refine (mem_genericPoints_iff_forall_specializes_eq (f x)).2 fun y hy ↦ ?_
  obtain ⟨x', hx', rfl⟩ := hf hy
  simp [(mem_genericPoints_iff_forall_specializes_eq x).1 hx x' hx']

namespace Scheme

variable {X Y : Scheme.{u}}

/-- A flat morphism of schemes carries generic points of irreducible components to generic
points of irreducible components. -/
@[ega "IV 2.3.4" "(iii), special case", sga "3 X 5.14.0" "more general"]
theorem Hom.mem_genericPoints_of_flat (f : X ⟶ Y) [Flat f]
    {x : X} (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y :=
  mem_genericPoints_of_generalizingMap (Flat.generalizingMap f) hx

/-! ### Functoriality of the generic-point residue spectrum -/

/-- The morphism of generic-point residue spectra induced by a flat morphism: on the summand at
a generic point `η` it is the residue-field morphism at `η`, landing in the summand at the
image of `η`. -/
noncomputable def Hom.genericPointResidueSpectrumMap (f : X ⟶ Y) [Flat f] :
    genericPointResidueSpectrum X ⟶ genericPointResidueSpectrum Y :=
  Sigma.desc fun η : genericPoints X ↦
    Spec.map (f.residueFieldMap η.1) ≫
      Sigma.ι (fun ξ : genericPoints Y ↦ Spec (.of (Y.residueField ξ.1)))
        ⟨f η.1, f.mem_genericPoints_of_flat η.2⟩

/-- The restriction of `AlgebraicGeometry.Scheme.Hom.genericPointResidueSpectrumMap` to the
summand at a generic point. -/
theorem Hom.ι_genericPointResidueSpectrumMap (f : X ⟶ Y) [Flat f] (η : genericPoints X) :
    Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ≫
        f.genericPointResidueSpectrumMap =
      Spec.map (f.residueFieldMap η.1) ≫
        Sigma.ι (fun ξ : genericPoints Y ↦ Spec (.of (Y.residueField ξ.1)))
          ⟨f η.1, f.mem_genericPoints_of_flat η.2⟩ :=
  Sigma.ι_comp_desc _ _

/-- The induced morphism of generic-point residue spectra lies over the given morphism. -/
theorem Hom.genericPointResidueSpectrumMap_fromGenericPointResidueFields (f : X ⟶ Y) [Flat f] :
    f.genericPointResidueSpectrumMap ≫ fromGenericPointResidueFields Y =
      fromGenericPointResidueFields X ≫ f :=
  Sigma.hom_ext _ _ fun η ↦
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ fromGenericPointResidueFields Y)
          (f.ι_genericPointResidueSpectrumMap η)).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (Spec.map (f.residueFieldMap η.1) ≫ ·)
              (genericPointResidueSpectrum_ι_fromGenericPointResidueFields Y
                ⟨f η.1, f.mem_genericPoints_of_flat η.2⟩)).trans <|
            (Hom.SpecMap_residueFieldMap_fromSpecResidueField f η.1).trans <|
              (congrArg (· ≫ f)
                  (genericPointResidueSpectrum_ι_fromGenericPointResidueFields X η)).symm.trans
                (Category.assoc _ _ _)

end Scheme

/-! ### Functoriality of the normalization of a scheme along a flat morphism -/

variable {X Y : Scheme.{u}}

/-- The morphism of normalizations induced by a flat morphism of schemes whose quasi-compact
opens have finitely many irreducible components. -/
noncomputable def normalizationSchemeMap (f : X ⟶ Y) [Flat f]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    X.normalizationScheme hX ⟶ Y.normalizationScheme hY :=
  letI := Scheme.quasiCompactFromGenericPointResidueFields X hX
  letI := Scheme.quasiSeparatedFromGenericPointResidueFields X
  letI := Scheme.quasiCompactFromGenericPointResidueFields Y hY
  letI := Scheme.quasiSeparatedFromGenericPointResidueFields Y
  Scheme.Hom.normalizationMap (Scheme.fromGenericPointResidueFields Y)
    (Scheme.fromGenericPointResidueFields X) f.genericPointResidueSpectrumMap f
    f.genericPointResidueSpectrumMap_fromGenericPointResidueFields

/-- The induced morphism of normalizations commutes with the normalization morphisms. -/
theorem normalizationSchemeMap_normalization (f : X ⟶ Y) [Flat f]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    normalizationSchemeMap f hX hY ≫ Y.normalization hY = X.normalization hX ≫ f :=
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let := Scheme.quasiCompactFromGenericPointResidueFields Y hY
  let := Scheme.quasiSeparatedFromGenericPointResidueFields Y
  Scheme.Hom.normalizationMap_fromNormalization _ _ _ _ _

/-! ### The comparison for an extension of the ground field -/

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- `Spec` of an algebra over a field is flat, because every module over a field is flat.  In
particular this applies to an extension of fields. -/
theorem flat_specMap_algebraMap (k K : Type u) [Field k] [CommRing K] [Algebra k K] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The projection of a base change along an extension of fields is flat. -/
theorem flat_pullback_fst_specMap_algebraMap (X : Over (Spec (.of k))) :
    Flat (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).flip (flat_specMap_algebraMap k K)

/-- The base change to `K` of the normalization morphism of `X`. -/
noncomputable def baseChangeNormalization
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
    ((Over.pullback σ).obj (Over.mk (X.left.normalization hX ≫ X.hom))).left ⟶
      ((Over.pullback σ).obj X).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
    (Over.homMk (X.left.normalization
      (finite_irreducibleComponents_of_locallyOfFiniteType k X.hom)))).left

/-- **Stacks Project, Tag 0C3N.** The canonical morphism from the normalization after extending
the ground field to the base change of the original normalization. -/
@[stacks 0C3N "canonical morphism"]
noncomputable def normalizationBaseChangeComparison
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (Over.pullback σ).obj X
    letI : LocallyOfFiniteType Y.hom := by
      dsimp [Y, σ]
      infer_instance
    let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
    let hY := finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom
    Y.left.normalizationScheme hY ⟶
      ((Over.pullback σ).obj
        (Over.mk (X.left.normalization hX ≫ X.hom))).left := by
  intro σ Y hX hY
  letI := flat_pullback_fst_specMap_algebraMap (K := K) X
  change Y.left.normalizationScheme hY ⟶ pullback (X.left.normalization hX ≫ X.hom) σ
  refine pullback.lift (normalizationSchemeMap (pullback.fst X.hom σ) hY hX)
    (Y.left.normalization hY ≫ Y.hom) ?_
  rw [← Category.assoc, normalizationSchemeMap_normalization, Category.assoc,
    Category.assoc, pullback.condition]
  rfl

/-- **Stacks Project, Tag 0C3N.** The projection of the comparison to the original normalization
is the canonical map induced by functoriality of relative normalization.  The map on
generic-point residue spectra is over the projection `X_K ⟶ X`. -/
@[stacks 0C3N "projection to the original normalization"]
theorem normalizationBaseChangeComparison_comp_fst
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (Over.pullback σ).obj X
    letI : LocallyOfFiniteType Y.hom := by
      dsimp [Y, σ]
      infer_instance
    let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
    let hY := finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom
    let fX := Scheme.fromGenericPointResidueFields X.left
    let fY := Scheme.fromGenericPointResidueFields Y.left
    letI : QuasiCompact fX := Scheme.quasiCompactFromGenericPointResidueFields X.left hX
    letI : QuasiSeparated fX := Scheme.quasiSeparatedFromGenericPointResidueFields X.left
    letI : QuasiCompact fY := Scheme.quasiCompactFromGenericPointResidueFields Y.left hY
    letI : QuasiSeparated fY := Scheme.quasiSeparatedFromGenericPointResidueFields Y.left
    ∃ (gY : Scheme.genericPointResidueSpectrum Y.left ⟶
        Scheme.genericPointResidueSpectrum X.left)
      (sq : gY ≫ fX = fY ≫ pullback.fst X.hom σ),
      normalizationBaseChangeComparison X ≫
          pullback.fst (X.left.normalization hX ≫ X.hom) σ =
        Scheme.Hom.normalizationMap fX fY gY (pullback.fst X.hom σ) sq := by
  intro σ Y hX hY fX fY
  have := flat_pullback_fst_specMap_algebraMap (K := K) X
  exact ⟨(pullback.fst X.hom σ).genericPointResidueSpectrumMap,
    (pullback.fst X.hom σ).genericPointResidueSpectrumMap_fromGenericPointResidueFields,
    pullback.lift_fst (f := X.left.normalization hX ≫ X.hom) (g := σ) _ _ _⟩

/-- **Stacks Project, Tag 0C3N.** The projection of the comparison to `Spec K` is the structural
morphism of the normalized base change.  Together with the preceding projection formula, this
characterizes the map into the fibre product. -/
@[stacks 0C3N "projection to the extended base field"]
theorem normalizationBaseChangeComparison_comp_snd
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (Over.pullback σ).obj X
    letI : LocallyOfFiniteType Y.hom := by
      dsimp [Y, σ]
      infer_instance
    let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
    normalizationBaseChangeComparison X ≫
        pullback.snd (X.left.normalization hX ≫ X.hom) σ =
      Y.left.normalization (finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom) ≫
        Y.hom := by
  intro σ Y hX
  have := flat_pullback_fst_specMap_algebraMap (K := K) X
  exact pullback.lift_snd (f := X.left.normalization hX ≫ X.hom) (g := σ) _ _ _

/-- **Stacks Project, Tag 0C3N.** The canonical comparison commutes with the normalization
morphisms to the base-changed scheme. -/
@[stacks 0C3N "compatibility with normalization morphisms"]
theorem normalizationBaseChangeComparison_comp_baseChangeNormalization
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    let σ := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (Over.pullback σ).obj X
    letI : LocallyOfFiniteType Y.hom := by
      dsimp [Y, σ]
      infer_instance
    normalizationBaseChangeComparison X ≫ baseChangeNormalization X =
      Y.left.normalization (finite_irreducibleComponents_of_locallyOfFiniteType K Y.hom) := by
  intro σ Y
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k X.hom
  have := flat_pullback_fst_specMap_algebraMap (K := K) X
  have hfst : baseChangeNormalization X ≫
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        pullback.fst (X.left.normalization hX ≫ X.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
          X.left.normalization hX :=
    pullback.lift_fst _ _ _
  have hsnd : baseChangeNormalization X ≫
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        pullback.snd (X.left.normalization hX ≫ X.hom)
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift_snd _ _ _
  obtain ⟨gY, sq, hcomp⟩ := normalizationBaseChangeComparison_comp_fst (K := K) X
  simp only [Y, σ]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hfst, ← Category.assoc, hcomp,
      Scheme.Hom.normalizationMap_fromNormalization]
  · rw [Category.assoc, hsnd, normalizationBaseChangeComparison_comp_snd (K := K) X]
    rfl

end AlgebraicGeometry

end
