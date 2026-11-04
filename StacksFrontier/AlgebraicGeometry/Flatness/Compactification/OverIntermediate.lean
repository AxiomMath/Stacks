module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticImage
public import StacksCore.Tactic.StacksAttribute

/-!
# Compactification over a finite-type intermediate scheme

Let `X ⟶ Y ⟶ S` be morphisms of schemes. If `S` is quasi-compact and quasi-separated, `Y` is
separated and of finite type over `S`, and `X` is compactifiable over `S`, then `X` is
compactifiable over `Y`.

## Main results

* `AlgebraicGeometry.exists_quasiCompact_compactification_over` produces a compactification of
  `X` over `Y`.

## Implementation notes

Compactifiability is expressed by the existence of a compactification whose open immersion is
quasi-compact; a compactification is `AlgebraicGeometry.CompactificationOf`, and the structure
map of `X` over `S` is the composite `X ⟶ Y ⟶ S`.

## References

* [Stacks Project, Tag 0A9Z](https://stacks.math.columbia.edu/tag/0A9Z)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A compactifiable `S`-scheme is also compactifiable over a separated finite-type `S`-scheme
through which its structure morphism factors. -/
@[stacks 0A9Z, sga "4 XVII 3.2.2" "(v)"]
theorem exists_quasiCompact_compactification_over
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (hX : ∃ j : CompactificationOf (Over.mk (f ≫ g)),
      QuasiCompact j.immersion) :
    ∃ j : CompactificationOf (Over.mk f),
      QuasiCompact j.immersion := by
  classical
  obtain ⟨j, hj⟩ := hX
  let Z := j.space
  let V : Z.Opens := Scheme.Hom.opensRange j.immersion
  have hV : IsRetrocompact (V : Set Z) := by
    have : QuasiCompact j.immersion := hj
    have hrange : IsRetrocompact (Set.range (j.immersion : X → Z)) := by
      intro U hU hUopen
      rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
      exact (QuasiCompact.isCompact_preimage U hUopen hU).image j.immersion.continuous
    simpa [V, Scheme.Hom.coe_opensRange] using hrange
  have hιqc : QuasiCompact V.ι := by
    rw [quasiCompact_iff_isSpectralMap]
    show IsSpectralMap (Subtype.val : V → Z)
    exact IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hV
  have hr : Set.range V.ι = Set.range j.immersion := by simp [V, Scheme.Hom.coe_opensRange]
  let e : V.toScheme ≅ X := IsOpenImmersion.isoOfRangeEq V.ι j.immersion hr
  have he : e.hom ≫ j.immersion = V.ι := IsOpenImmersion.isoOfRangeEq_hom_fac V.ι j.immersion hr
  have hcomm : j.immersion ≫ j.toBase = f ≫ g := by
    simp [CompactificationOf.immersion, CompactificationOf.toBase]
  let P := pullback j.toBase g
  let s : V.toScheme ⟶ P := pullback.lift (e.hom ≫ j.immersion) (e.hom ≫ f)
    (by simpa only [Category.assoc] using congrArg (e.hom ≫ ·) hcomm)
  have hs : s ≫ pullback.fst j.toBase g = V.ι := (pullback.lift_fst _ _ _).trans he
  let a : Scheme := Scheme.Hom.image s
  let q : a ⟶ Z := s.imageι ≫ pullback.fst j.toBase g
  have : IsIso (pullback.snd q V.ι) :=
    AlgebraicGeometry.isIso_pullback_snd_imageι_comp_of_section
      (pullback.fst j.toBase g) V hV s hs
  let t : V.toScheme ⟶ pullback q V.ι :=
    pullback.lift s.toImage (𝟙 V.toScheme) (by
      simpa only [q, ← Category.assoc, Scheme.Hom.toImage_imageι, Category.id_comp] using hs)
  have : IsIso (t ≫ pullback.snd q V.ι) := by
    rw [show t ≫ pullback.snd q V.ι = 𝟙 V.toScheme from pullback.lift_snd _ _ _]
    infer_instance
  have : IsIso t := IsIso.of_isIso_comp_right t (pullback.snd q V.ι)
  have htfst : t ≫ pullback.fst q V.ι = s.toImage := pullback.lift_fst _ _ _
  let k : X ⟶ a := e.inv ≫ t ≫ pullback.fst q V.ι
  have hkOpen : IsOpenImmersion k := by infer_instance
  have hkQC : QuasiCompact k := by infer_instance
  let m : a ⟶ Y := s.imageι ≫ pullback.snd j.toBase g
  have hmProper : IsProper m := by infer_instance
  have hkm : k ≫ m = f := by
    simp only [k, m, Category.assoc, htfst, Scheme.Hom.toImage_imageι_assoc]
    simp [s, pullback.lift_snd]
  exact ⟨⟨StructuredArrow.mk (Over.homMk k hkm : Over.mk f ⟶ Over.mk m), hkOpen, hmProper⟩, hkQC⟩

end AlgebraicGeometry
