module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.Topology.Sober.Generization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normalization commutes with base change to a local ring of the base

Let `g : L ⟶ S` be the canonical morphism from the spectrum of a local ring of `S`, and let
`f : W ⟶ S` be any morphism. Then the projection `W ×_S L ⟶ W` is flat and a preimmersion, and
along such a morphism normalization commutes with base change: the normalization of `W ×_S L` is
`W^ν ×_W (W ×_S L)`.

This is the scheme-theoretic form of the statement that integral closure commutes with
localization, [Stacks, Tag 0307]. It is the hypothesis under which the base-change functor of
[Stacks, Tag 0BFU] carries a normalized blowing up to a normalized blowing up.

## Main results

* `AlgebraicGeometry.mem_genericPoints_of_flat_preimmersion`: a point of the source of a flat
  preimmersion lying over a generic point of an irreducible component is itself such a generic
  point.
* `AlgebraicGeometry.isNormal_of_flat_preimmersion`: the source of a flat preimmersion with
  normal target is normal.
* `AlgebraicGeometry.finite_irreducibleComponents_of_mapsTo_injOn_genericPoints`: a morphism
  which is injective on generic points of irreducible components and carries them to such
  generic points inherits finiteness of the irreducible components of quasi-compact opens.
* `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_flat_preimmersion`: the normalization
  square of a flat preimmersion whose base change of the normalization morphism is normal is
  cartesian.
* `AlgebraicGeometry.isPullback_normalizationSchemeMap_pullbackFst_fromSpecStalk` is that applied
  to `W ×_S L ⟶ W`, together with
  `AlgebraicGeometry.finite_irreducibleComponents_pullbackFst_fromSpecStalk`, the finiteness
  statement which makes it meaningful.

## Implementation notes

The cartesian square is proved exactly as in the étale case,
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale`: the two mutually inverse
morphisms between `X^ν` and `X ×_Y Y^ν` both come from the universal property of the
normalization of a scheme, [Stacks, Tag 035Q] part (4), and each composite is an identity because
it is a factorization of a morphism having exactly one. Étaleness enters that proof only through
the three facts isolated here — that generic points of irreducible components descend along the
morphism, that the base change of the normalization morphism is normal, and that finiteness of
irreducible components of quasi-compact opens ascends — so the proof is repeated with those as
hypotheses rather than being derived from a common generalization, the étale file being left
untouched.

For a flat preimmersion the first of the three is formal: the morphism is injective and
generalizations lift along it, so a point with no proper generization downstairs has none
upstairs. The second is not formal and is carried as a hypothesis of the general statement; for
`W ×_S L ⟶ W` it holds because the base change of the normalization morphism along it is, after
the comparison isomorphism `pullbackRightPullbackFstIso`, the base change of `L ⟶ S` along
`W^ν ⟶ S`, whose source is therefore the source of a flat preimmersion with normal target. The
third is the generic-point counting argument of
`Stacks.Blowup.finite_irreducibleComponents_blowUp`, extracted here in the form which only uses
that the morphism maps generic points to generic points injectively; a flat preimmersion does so,
whereas `AlgebraicGeometry.finite_irreducibleComponents_of_flat_locallyOfFiniteType` does not
apply, the morphism from the spectrum of a local ring not being locally of finite type.

## References

* [Stacks Project, Tag 0307](https://stacks.math.columbia.edu/tag/0307)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Flat preimmersions -/

/-- A point of the source of a flat preimmersion which lies over a generic point of an
irreducible component of the target is a generic point of an irreducible component of the source:
the morphism is injective and generalizations lift along it, so the point has no proper
generization. -/
theorem mem_genericPoints_of_flat_preimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsPreimmersion f] {x : X} (hx : f x ∈ genericPoints Y) : x ∈ genericPoints X :=
  (TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq x).2 fun _ hbx =>
    f.isEmbedding.injective
      ((TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq (f x)).1 hx _
        (hbx.map f.continuous))

/-- The source of a flat preimmersion whose target is a normal scheme is normal: the morphism
induces isomorphisms on local rings. -/
theorem isNormal_of_flat_preimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f]
    [IsNormal Y] : IsNormal X := by
  refine (isNormal_iff_stalk_normal X).2 fun x => ?_
  have : IsIso (f.stalkMap x) := isIso_stalkMap_of_flat_preimmersion f x
  let e : Y.presheaf.stalk (f x) ≃+* X.presheaf.stalk x :=
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  have : IsIntegrallyClosed (Y.presheaf.stalk (f x)) := IsNormal.stalk_normal (f x)
  have : IsDomain (X.presheaf.stalk x) := Function.Injective.isDomain e.symm e.symm.injective
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩

/-! ### Ascent of finiteness of irreducible components -/

/-- Finiteness of the irreducible components of quasi-compact opens ascends along a morphism
which carries generic points of irreducible components to such generic points injectively: a
quasi-compact open of the source is covered by the inverse images of finitely many affine opens
of the target, and the generic points lying in each of those are finite in number. -/
theorem finite_irreducibleComponents_of_mapsTo_injOn_genericPoints {A X : Scheme.{u}} (b : A ⟶ X)
    (hmaps : Set.MapsTo b (genericPoints A) (genericPoints X))
    (hinj : Set.InjOn b (genericPoints A))
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∀ U : A.Opens, IsCompact (U : Set A) → (irreducibleComponents U).Finite := by
  classical
  let V (i : X.affineCover.I₀) : X.Opens := (X.affineCover.f i).opensRange
  have hfiniteV (i : X.affineCover.I₀) : {η : genericPoints X | η.1 ∈ V i}.Finite :=
    (genericPoints.finite (hX (V i) (isAffineOpen_opensRange (X.affineCover.f i)).isCompact))
      |>.of_injective (Scheme.genericPointsInOpenEquiv X (V i))
        (Scheme.genericPointsInOpenEquiv X (V i)).injective
  intro U hU
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i => b ⁻¹ᵁ V i)
    (fun i => (b ⁻¹ᵁ V i).isOpen) (by
      intro y _
      obtain ⟨i, hi⟩ := X.affineCover.exists_eq (b y)
      exact Set.mem_iUnion.mpr ⟨i, Scheme.Hom.mem_opensRange.mpr hi⟩)
  let S : Set (genericPoints X) :=
    ⋃ i ∈ (t : Set X.affineCover.I₀), {η : genericPoints X | η.1 ∈ V i}
  have hS : S.Finite := t.finite_toSet.biUnion fun i _ => hfiniteV i
  let g : {η : genericPoints A // η.1 ∈ U} → {ξ : genericPoints X // ξ ∈ S} :=
    fun η => ⟨⟨b η.1.1, hmaps η.1.2⟩, by
      obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (ht η.2)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hiy⟩⟩
  have hginj : Function.Injective g := fun η ξ heq =>
    Subtype.ext (Subtype.ext (hinj η.1.2 ξ.1.2
      (congrArg (fun z : {ξ : genericPoints X // ξ ∈ S} => z.1.1) heq)))
  have : Finite {ξ : genericPoints X // ξ ∈ S} := hS.to_subtype
  have : Finite {η : genericPoints A // η.1 ∈ U} := Finite.of_injective g hginj
  have : Finite (genericPoints (U : Set A)) :=
    Finite.of_equiv _ (Scheme.genericPointsInOpenEquiv A U)
  have : QuasiSober (U : Set A) := U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  have : Finite (irreducibleComponents (U : Set A)) :=
    Finite.of_equiv _ (genericPoints.equiv (α := (U : Set A)))
  rw [Set.finite_def]
  exact ⟨Fintype.ofFinite (irreducibleComponents (U : Set A))⟩

/-- Finiteness of the irreducible components of quasi-compact opens ascends along a flat
preimmersion. -/
@[ega "IV 2.3.6" "(iii), special case"]
theorem finite_irreducibleComponents_of_flat_preimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsPreimmersion f]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite :=
  finite_irreducibleComponents_of_mapsTo_injOn_genericPoints f
    (fun _ hx => mem_genericPoints_of_flat (f := f) hx)
    (fun _ _ _ _ h => f.isEmbedding.injective h) hY

/-! ### The normalization square of a flat preimmersion -/

section

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) [Flat φ] [IsPreimmersion φ]
  (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)

omit [IsPreimmersion φ] in
/-- A generic point of an irreducible component of the base change of the normalization morphism
of `Y` along a flat `φ` lies over a generic point of an irreducible component of `Y`. -/
private theorem mem_genericPoints_pullbackFst_normalization
    {z : ↥(pullback (Y.normalization hY) φ)}
    (hz : z ∈ genericPoints ↥(pullback (Y.normalization hY) φ)) :
    (pullback.fst (Y.normalization hY) φ ≫ Y.normalization hY) z ∈ genericPoints Y := by
  rw [Scheme.Hom.comp_apply]
  exact Scheme.normalization_mem_genericPoints Y hY
    (mem_genericPoints_of_flat (pullback.fst (Y.normalization hY) φ) hz)

/-- A generic point of an irreducible component of the base change of the normalization morphism
of `Y` along a flat preimmersion `φ` is carried by the second projection to a generic point of an
irreducible component of `X`. -/
private theorem mem_genericPoints_pullbackSnd {z : ↥(pullback (Y.normalization hY) φ)}
    (hz : z ∈ genericPoints ↥(pullback (Y.normalization hY) φ)) :
    pullback.snd (Y.normalization hY) φ z ∈ genericPoints X := by
  refine mem_genericPoints_of_flat_preimmersion φ ?_
  have h := mem_genericPoints_pullbackFst_normalization φ hY hz
  rwa [pullback.condition, Scheme.Hom.comp_apply] at h

/-- The normalization square of a flat preimmersion along which the base change of the
normalization morphism of the target is normal is cartesian: the normalization of the source is
the base change of the normalization of the target.

This is the conclusion of [Stacks, Tag 07TD] for a morphism which is not smooth but for which
the three facts the proof consumes are available. -/
theorem isPullback_normalizationSchemeMap_of_flat_preimmersion
    (hnormal : IsNormal (pullback (Y.normalization hY) φ)) :
    IsPullback
      (normalizationSchemeMap φ (finite_irreducibleComponents_of_flat_preimmersion φ hY) hY)
      (X.normalization (finite_irreducibleComponents_of_flat_preimmersion φ hY))
      (Y.normalization hY) φ := by
  set hX := finite_irreducibleComponents_of_flat_preimmersion φ hY
  have hsq : normalizationSchemeMap φ hX hY ≫ Y.normalization hY
      = X.normalization hX ≫ φ := normalizationSchemeMap_normalization φ hX hY
  have : IsNormal (X.normalizationScheme hX) := Scheme.isNormal_normalizationScheme X hX
  set lift : X.normalizationScheme hX ⟶ pullback (Y.normalization hY) φ :=
    pullback.lift (normalizationSchemeMap φ hX hY) (X.normalization hX) hsq with hliftdef
  obtain ⟨u, hu, -⟩ := Scheme.existsUnique_lift_normalization hX
    (pullback.snd (Y.normalization hY) φ)
    (fun η ↦ mem_genericPoints_pullbackSnd φ hY η.2)
  have hunique := Scheme.existsUnique_lift_normalization hX (X.normalization hX)
    (fun η ↦ Scheme.normalization_mem_genericPoints X hX η.2)
  have hliftu : lift ≫ u = 𝟙 (X.normalizationScheme hX) :=
    hunique.unique (by rw [Category.assoc, hu, hliftdef, pullback.lift_snd])
      (Category.id_comp _)
  have huniqueY := Scheme.existsUnique_lift_normalization hY
    (pullback.fst (Y.normalization hY) φ ≫ Y.normalization hY)
    (fun η ↦ mem_genericPoints_pullbackFst_normalization φ hY η.2)
  have hfst : u ≫ normalizationSchemeMap φ hX hY = pullback.fst (Y.normalization hY) φ :=
    huniqueY.unique
      (by rw [Category.assoc, hsq, ← Category.assoc, hu, pullback.condition]) rfl
  have hulift : u ≫ lift = 𝟙 (pullback (Y.normalization hY) φ) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hliftdef, pullback.lift_fst, hfst, Category.id_comp]
    · rw [Category.assoc, hliftdef, pullback.lift_snd, hu, Category.id_comp]
  have : IsIso lift := ⟨u, hliftu, hulift⟩
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso lift)
    (by rw [asIso_hom, hliftdef, pullback.lift_fst])
    (by rw [asIso_hom, hliftdef, pullback.lift_snd])

end

/-! ### Base change to a local ring of the base -/

section

variable {S W : Scheme.{u}} (f : W ⟶ S) (s : S)

/-- The projection of a base change to the spectrum of a local ring of the base is flat. -/
theorem flat_pullbackFst_fromSpecStalk : Flat (pullback.fst f (S.fromSpecStalk s)) := by
  have : Flat (S.fromSpecStalk s) := flat_fromSpecStalk S s
  infer_instance

/-- Finiteness of the irreducible components of quasi-compact opens passes to a base change to
the spectrum of a local ring of the base. -/
theorem finite_irreducibleComponents_pullbackFst_fromSpecStalk
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    ∀ U : (pullback f (S.fromSpecStalk s)).Opens,
      IsCompact (U : Set ↥(pullback f (S.fromSpecStalk s))) → (irreducibleComponents U).Finite :=
  have := flat_pullbackFst_fromSpecStalk f s
  finite_irreducibleComponents_of_flat_preimmersion (pullback.fst f (S.fromSpecStalk s)) hW

/-- The base change of the normalization morphism of `W` along `W ×_S L ⟶ W`, for `L` the
spectrum of a local ring of `S`, has normal source: after the comparison isomorphism it is the
base change of `L ⟶ S` along `W^ν ⟶ S`, which is a flat preimmersion with normal target. -/
theorem isNormal_pullback_normalization_pullbackFst_fromSpecStalk
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    IsNormal (pullback (W.normalization hW) (pullback.fst f (S.fromSpecStalk s))) := by
  have hflat : Flat (S.fromSpecStalk s) := flat_fromSpecStalk S s
  have hν : IsNormal (W.normalizationScheme hW) := Scheme.isNormal_normalizationScheme W hW
  have hbase : IsNormal (pullback (W.normalization hW ≫ f) (S.fromSpecStalk s)) :=
    isNormal_of_flat_preimmersion (pullback.fst (W.normalization hW ≫ f) (S.fromSpecStalk s))
  exact isNormal_of_iso
    (pullbackRightPullbackFstIso f (S.fromSpecStalk s) (W.normalization hW))

/-- Normalization commutes with base change to the spectrum of a local ring of the base: for
`f : W ⟶ S` and `s : S`, the normalization of `W ×_S Spec 𝒪_{S,s}` is the base change of the
normalization of `W`.

This is the scheme-theoretic form of [Stacks, Tag 0307]. -/
theorem isPullback_normalizationSchemeMap_pullbackFst_fromSpecStalk
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    letI := flat_pullbackFst_fromSpecStalk f s
    IsPullback
      (normalizationSchemeMap (pullback.fst f (S.fromSpecStalk s))
        (finite_irreducibleComponents_pullbackFst_fromSpecStalk f s hW) hW)
      ((pullback f (S.fromSpecStalk s)).normalization
        (finite_irreducibleComponents_pullbackFst_fromSpecStalk f s hW))
      (W.normalization hW) (pullback.fst f (S.fromSpecStalk s)) :=
  let := flat_pullbackFst_fromSpecStalk f s
  isPullback_normalizationSchemeMap_of_flat_preimmersion
    (pullback.fst f (S.fromSpecStalk s)) hW
    (isNormal_pullback_normalization_pullbackFst_fromSpecStalk f s hW)

end

end AlgebraicGeometry

end
