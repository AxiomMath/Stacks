module

public import StacksFrontier.AlgebraicGeometry.Descent.IntegralEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EtaleBaseLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent

/-!
# Effectivity of quasi-compact separated étale descent data

Let `f : X ⟶ S` be a morphism of schemes. This file defines the property that every descent
datum relative to `X/S` whose underlying `X`-scheme is quasi-compact, separated and étale is
effective, by a scheme étale over `S`. It is equivalent to étale effectivity of each such datum,
the conditions on the underlying scheme are stable under restriction of the base to an open, and,
for `f` surjective and integral, a scheme descending such a datum is quasi-compact and separated
over `S`.

## Main definitions

* `AlgebraicGeometry.QcSepEtaleEffective`: every descent datum relative to `f` with
  quasi-compact separated étale underlying scheme carries a descended scheme which is étale
  over the base.
* `AlgebraicGeometry.DescentDatum.changeDatum`: the base change of a descent datum along an
  arbitrary morphism of the base, generalising
  `AlgebraicGeometry.DescentDatum.baseDatum`.
* `AlgebraicGeometry.DescentDatum.pullbackSquareDatum`: the pullback of a descent datum along an
  arbitrary commutative square, of which both of the above are instances.

## Main results

* `AlgebraicGeometry.QcSepEtaleEffective.isEtaleEffective` and
  `AlgebraicGeometry.qcSepEtaleEffective_of_isEtaleEffective`: the property read as étale
  effectivity in the sense of `AlgebraicGeometry.DescentDatum.IsEtaleEffective`.
* `AlgebraicGeometry.DescentDatum.property_pullbackSquare_over_hom`: the underlying scheme of
  the pullback of a datum along a commutative square has every base-change stable property of
  the underlying scheme of the datum, with
  `AlgebraicGeometry.DescentDatum.baseDatum_property` and
  `AlgebraicGeometry.DescentDatum.changeDatum_property` its two instances.
* `AlgebraicGeometry.quasiCompact_of_comp_of_surjective`: quasi-compactness of `g ≫ h` and
  surjectivity of `g` give quasi-compactness of `h`.
* `AlgebraicGeometry.DescentDatum.Descended.quasiCompact_base_hom` and
  `AlgebraicGeometry.DescentDatum.Descended.isSeparated_base_hom`: along a surjective integral
  morphism a scheme descending a quasi-compact separated datum is quasi-compact and separated
  over the base.

## Implementation notes

The property is stated with an explicit descended scheme rather than with membership in an
essential image.

## References

* [Stacks Project, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe v u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}}

/-- **Quasi-compact separated étale descent along `f` is effective.** Every descent datum
relative to `f : X ⟶ S` whose underlying `X`-scheme is quasi-compact, separated and étale
carries a descended scheme whose structure morphism to `S` is étale. -/
def QcSepEtaleEffective (f : X ⟶ S) : Prop :=
  ∀ D : DescentDatum f, Etale D.over.hom → QuasiCompact D.over.hom → IsSeparated D.over.hom →
    ∃ Q : D.Descended, Etale Q.base.hom

/-- The property read as étale effectivity of a single datum. -/
theorem QcSepEtaleEffective.isEtaleEffective {f : X ⟶ S} (h : QcSepEtaleEffective f)
    (D : DescentDatum f) [Etale D.over.hom] (hqc : QuasiCompact D.over.hom)
    (hsep : IsSeparated D.over.hom) : D.IsEtaleEffective := by
  obtain ⟨Q, _⟩ := h D ‹_› hqc hsep
  exact Q.isEtaleEffective

/-- Étale effectivity of every quasi-compact separated étale datum gives the property. -/
theorem qcSepEtaleEffective_of_isEtaleEffective {f : X ⟶ S}
    (h : ∀ (D : DescentDatum f) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
      IsSeparated D.over.hom → D.IsEtaleEffective) :
    QcSepEtaleEffective f := by
  intro D hD hqc hsep
  exact ⟨DescentDatum.Descended.ofIso ((IsEtaleDescentData f).ι.mapIso (h D hD hqc hsep).getIso),
    (h D hD hqc hsep).witness.prop⟩

/-- **Quasi-compactness passes to the target of a surjective morphism.** If `g ≫ h` is
quasi-compact and `g` is surjective then `h` is quasi-compact. -/
theorem quasiCompact_of_comp_of_surjective {Y : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ S)
    [QuasiCompact (g ≫ h)] [Surjective g] : QuasiCompact h := by
  constructor
  intro W hW hWc
  have hpre : IsCompact ((g ≫ h).base ⁻¹' W) :=
    QuasiCompact.isCompact_preimage (f := g ≫ h) W hW hWc
  have himg : g.base '' ((g ≫ h).base ⁻¹' W) = h.base ⁻¹' W := by
    have : (g ≫ h).base ⁻¹' W = g.base ⁻¹' (h.base ⁻¹' W) := by
      rw [Scheme.Hom.comp_base]; rfl
    rw [this, Set.image_preimage_eq _ g.surjective]
  rw [← himg]
  exact hpre.image g.continuous

namespace DescentDatum

variable {f : X ⟶ S}

/-- **The pullback of a descent datum along a commutative square**, read as a descent datum
relative to the square's right-hand vertical arrow. -/
abbrev pullbackSquareDatum {S' X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {h : S' ⟶ S}
    {p : X' ⟶ X} {comm : p ≫ a = a' ≫ h}
    (P : DescentData.PullbackFunctor a a' h p comm) (D : DescentDatum a) : DescentDatum a' :=
  P.functor.obj D

/-- **The pullback of a datum along a commutative square inherits every base-change stable
property of the underlying scheme.** The underlying scheme of the pullback is the base change of
the underlying scheme of the datum along the square's top arrow. -/
theorem property_pullbackSquare_over_hom {S' X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'}
    {h : S' ⟶ S} {p : X' ⟶ X} {comm : p ≫ a = a' ≫ h}
    (P : DescentData.PullbackFunctor a a' h p comm) (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] (D : DescentDatum a) (hQ : Q D.over.hom) :
    Q (pullbackSquareDatum P D).over.hom := by
  have : Q.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hpb : Q ((Over.pullback p).obj D.over).hom := by
    show Q (pullback.snd D.over.hom p)
    exact MorphismProperty.pullback_snd _ _ hQ
  have hcomm : (P.objIso D).hom.left ≫ ((Over.pullback p).obj D.over).hom =
      (pullbackSquareDatum P D).over.hom := (P.objIso D).hom.w
  have : IsIso (P.objIso D).hom.left := by
    show IsIso ((Over.forget X').map (P.objIso D).hom)
    infer_instance
  rw [← hcomm]
  exact (Q.cancel_left_of_respectsIso _ _).mpr hpb

/-- **The datum restricted to an open of the base inherits every base-change stable property
of the underlying scheme.** The underlying scheme of the restricted datum is the base change of
the underlying scheme of the datum along `X ×_S T ⟶ X`. -/
theorem baseDatum_property (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (D : DescentDatum f) (T : S.Opens) (hP : P D.over.hom) :
    P (D.baseDatum T).over.hom :=
  property_pullbackSquare_over_hom (basePullbackFunctor f T) P D hP

/-- The datum restricted to an open of the base has quasi-compact underlying scheme. -/
theorem quasiCompact_baseDatum_over_hom (D : DescentDatum f) (T : S.Opens)
    (hP : QuasiCompact D.over.hom) : QuasiCompact (D.baseDatum T).over.hom :=
  baseDatum_property @QuasiCompact D T hP

/-- The datum restricted to an open of the base has separated underlying scheme. -/
theorem isSeparated_baseDatum_over_hom (D : DescentDatum f) (T : S.Opens)
    (hP : IsSeparated D.over.hom) : IsSeparated (D.baseDatum T).over.hom :=
  baseDatum_property @IsSeparated D T hP

/-! ### Base change of a datum along an arbitrary morphism of the base -/

/-- The pullback functor on descent data for the cartesian square over a morphism `g : T ⟶ S`
of the base. -/
abbrev changePullbackFunctor (f : X ⟶ S) {T : Scheme.{u}} (g : T ⟶ S) :
    DescentData.PullbackFunctor f (pullback.snd f g) g (pullback.fst f g) pullback.condition :=
  DescentData.pullbackFunctor f (pullback.snd f g) g (pullback.fst f g) pullback.condition

/-- **The base change of a descent datum along a morphism `g : T ⟶ S` of the base**, a descent
datum relative to `X ×_S T ⟶ T`. For `g` the inclusion of an open this is
`AlgebraicGeometry.DescentDatum.baseDatum`. -/
abbrev changeDatum (D : DescentDatum f) {T : Scheme.{u}} (g : T ⟶ S) :
    DescentDatum (pullback.snd f g) :=
  (changePullbackFunctor f g).functor.obj D

/-- **The base change of a datum along a morphism of the base inherits every base-change stable
property of the underlying scheme.** -/
theorem changeDatum_property (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (D : DescentDatum f) {T : Scheme.{u}} (g : T ⟶ S) (hP : P D.over.hom) :
    P (D.changeDatum g).over.hom :=
  property_pullbackSquare_over_hom (changePullbackFunctor f g) P D hP

/-- The base change of an étale datum along a morphism of the base is étale. -/
instance etale_changeDatum_over_hom (D : DescentDatum f) {T : Scheme.{u}} (g : T ⟶ S)
    [hP : Etale D.over.hom] : Etale (D.changeDatum g).over.hom :=
  changeDatum_property @Etale D g hP

/-- The base change of a quasi-compact datum along a morphism of the base is quasi-compact. -/
theorem quasiCompact_changeDatum_over_hom (D : DescentDatum f) {T : Scheme.{u}} (g : T ⟶ S)
    (hP : QuasiCompact D.over.hom) : QuasiCompact (D.changeDatum g).over.hom :=
  changeDatum_property @QuasiCompact D g hP

/-- The base change of a separated datum along a morphism of the base is separated. -/
theorem isSeparated_changeDatum_over_hom (D : DescentDatum f) {T : Scheme.{u}} (g : T ⟶ S)
    (hP : IsSeparated D.over.hom) : IsSeparated (D.changeDatum g).over.hom :=
  changeDatum_property @IsSeparated D g hP

namespace Descended

variable {D : DescentDatum f} (Q : D.Descended)

/-- The projection of a descended scheme is universally closed when `f` is. -/
theorem universallyClosed_proj [UniversallyClosed f] : UniversallyClosed Q.proj :=
  MorphismProperty.of_isPullback Q.isPullback inferInstance

/-- The structure morphism of a descended scheme, composed with the projection, is the
structure morphism of the underlying scheme of the datum over `S`. -/
theorem proj_comp_base_hom : Q.proj ≫ Q.base.hom = D.over.hom ≫ f :=
  Q.isPullback.w.symm

/-- **A scheme descending a quasi-compact datum along a surjective quasi-compact morphism is
quasi-compact over the base.** -/
theorem quasiCompact_base_hom [Surjective f] [QuasiCompact f]
    (hqc : QuasiCompact D.over.hom) : QuasiCompact Q.base.hom := by
  have : QuasiCompact (Q.proj ≫ Q.base.hom) := by rw [Q.proj_comp_base_hom]; infer_instance
  exact quasiCompact_of_comp_of_surjective Q.proj Q.base.hom

/-- **A scheme descending a separated datum along a surjective universally closed morphism is
separated over the base.** -/
theorem isSeparated_base_hom [Surjective f] [UniversallyClosed f] [IsSeparated f]
    (hsep : IsSeparated D.over.hom) : IsSeparated Q.base.hom := by
  let A : Over S := Over.mk (D.over.hom ≫ f)
  let φ : A ⟶ Q.base := Over.homMk Q.proj Q.proj_comp_base_hom
  have : Surjective φ.left := show Surjective Q.proj from inferInstance
  have : UniversallyClosed φ.left := show UniversallyClosed Q.proj from Q.universallyClosed_proj
  have : IsSeparated A.hom := show IsSeparated (D.over.hom ≫ f) from inferInstance
  exact isSeparated_of_surjective_universallyClosed φ

end Descended

end DescentDatum

end AlgebraicGeometry

end
