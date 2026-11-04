module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# A finite morphism of algebraic spaces is an affine proper morphism

For morphisms of schemes, finiteness is the conjunction of properness and affineness
(`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`). The same holds for morphisms of
algebraic spaces over a scheme `S`.

## Main results

* `AlgebraicGeometry.Space.presheaf_isProper_iff`: a representable morphism of algebraic spaces
  is proper exactly when each of its represented base changes is a proper morphism of schemes.
* `AlgebraicGeometry.Space.isProper_yoneda_map`: the Yoneda image of a proper morphism of the
  site is a proper morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isFinite_iff_isAffineHom_and_isProper`: a morphism of algebraic
  spaces is finite exactly when it is affine and proper.

## Implementation notes

Properness of a morphism of algebraic spaces, `AlgebraicGeometry.Space.IsProper`, is
separatedness together with being of finite type and universally closed, whereas Mathlib's
`AlgebraicGeometry.IsProper` asks for separatedness, universal closedness and local finite type.
The quasi-compactness half of finite type follows from universal closedness
(`AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed`), so no quasi-compactness
hypothesis appears.

## References

* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Properness on the represented base changes -/

/-- **Properness of a representable morphism of algebraic spaces, read on its represented base
changes.** A relatively representable morphism `f` of algebraic spaces over `S` is proper
exactly when, for every represented base change of `f`, the corresponding morphism of schemes is
proper. -/
theorem presheaf_isProper_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : yoneda.relativelyRepresentable f) :
    IsProper B S hS f ↔
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f := by
  have hsep := isSeparated_iff_presheaf B S hS f hX hY hf
  have hlft := holdsOnEveryEtaleChart_iff_relative B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hX hY f hf
  have huc := (presheaf_universallyClosed_iff B S hS hX hY hf).symm
  constructor
  · intro hp
    refine ⟨hf, fun U V g fst snd hpb ↦ ?_⟩
    exact (_root_.AlgebraicGeometry.isProper_iff (f := (BigFppfOver.toScheme B S hS).map snd)).mpr
      ⟨(hsep.mp hp.1).property g fst snd hpb, (huc.mp hp.2.2).property g fst snd hpb,
        (hlft.mp hp.2.1.1).property g fst snd hpb⟩
  · intro hp
    have hparts : ∀ ⦃U V : BigFppfOver B S hS⦄ (g : yoneda.obj U ⟶ Y)
        (fst : yoneda.obj V ⟶ X) (snd : V ⟶ U),
        IsPullback fst (yoneda.map snd) f g →
        _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map snd) ∧
          _root_.AlgebraicGeometry.UniversallyClosed
            ((BigFppfOver.toScheme B S hS).map snd) ∧
          _root_.AlgebraicGeometry.LocallyOfFiniteType
            ((BigFppfOver.toScheme B S hS).map snd) :=
      fun _ _ g fst snd hpb ↦ (_root_.AlgebraicGeometry.isProper_iff
        (f := (BigFppfOver.toScheme B S hS).map snd)).mp (hp.property g fst snd hpb)
    simp only [forall_and] at hparts
    have hsep' := hsep.mpr ⟨hf, hparts.1⟩
    have huc' := huc.mpr ⟨hf, hparts.2.1⟩
    have hlft' := hlft.mpr ⟨hf, hparts.2.2⟩
    exact ⟨hsep', ⟨hlft', isQuasiCompact_of_universallyClosed B S hS hX hY f huc'⟩, huc'⟩

/-- **The Yoneda image of a proper morphism of the site is a proper morphism of algebraic
spaces.** If `f : U ⟶ V` is a morphism of the site whose underlying morphism of schemes is
proper, then `yoneda.map f` is a proper morphism of algebraic spaces. -/
theorem isProper_yoneda_map {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map f)) :
    IsProper B S hS (yoneda.map f) := by
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hstab : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsProper)
      (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩
  refine (presheaf_isProper_iff B S hS (yoneda.map f)
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
    (Functor.relativelyRepresentable.map yoneda f)).mpr ?_
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).mpr hf

/-! ### Finite is affine and proper -/

/-- A morphism of algebraic spaces over `S` is finite exactly when it is affine and proper. -/
@[stacks 04NZ, ega "III 4.4.2" "a) <=> b)"]
theorem isFinite_iff_isAffineHom_and_isProper {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsFinite B S hS f ↔ IsAffineHom B S hS f ∧ IsProper B S hS f := by
  constructor
  · intro hf
    obtain ⟨hrep, hfiniteR⟩ := (isFinite_iff_representable B S hS f hX hY).mp hf
    have hsplit (U V : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y) (fst : yoneda.obj V ⟶ X)
        (snd : V ⟶ U) (hpb : IsPullback fst (yoneda.map snd) f g) :=
      (_root_.AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
        (f := (BigFppfOver.toScheme B S hS).map snd)).mp (hfiniteR.property g fst snd hpb)
    exact ⟨isAffineHom_of_presheaf
        ⟨hrep, fun _ _ g fst snd hpb ↦ (hsplit _ _ g fst snd hpb).2⟩,
      (presheaf_isProper_iff B S hS f hX hY hrep).mpr
        ⟨hrep, fun _ _ g fst snd hpb ↦ (hsplit _ _ g fst snd hpb).1⟩⟩
  · rintro ⟨hAffine, hproper⟩
    obtain ⟨hrep, haffR⟩ :=
      presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS hX hY hAffine
    have hproperR := (presheaf_isProper_iff B S hS f hX hY hrep).mp hproper
    refine (isFinite_iff_representable B S hS f hX hY).mpr ⟨hrep, hrep, ?_⟩
    intro U V g fst snd hpb
    exact (_root_.AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
      (f := (BigFppfOver.toScheme B S hS).map snd)).mpr
      ⟨hproperR.property g fst snd hpb, haffR.property g fst snd hpb⟩

end AlgebraicGeometry.Space

end
