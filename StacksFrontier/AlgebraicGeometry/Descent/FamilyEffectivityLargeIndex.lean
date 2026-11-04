module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcFamilyEffective
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDataReindex
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityChartRigidity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effectivity along a covering family indexed in an arbitrary universe

An fpqc covering family of a scheme in `Scheme.{u}`, indexed by a type in an arbitrary universe,
has a covering subfamily indexed in `Type u`, and a descent datum relative to the whole family is
effective as soon as its restrictions to the covering subfamilies indexed in `Type u` are. In
particular a descent datum relative to such a family all of whose structure morphisms are affine
is effective.

## Main results

* `AlgebraicGeometry.hom_ext_of_mem_fpqcPrecoverage`: an fpqc covering family is an epimorphic
  family — two morphisms out of its target agreeing on every member are equal.
* `AlgebraicGeometry.exists_small_subfamily`: an fpqc covering family has a covering subfamily
  indexed in the universe of the schemes.
* `AlgebraicGeometry.DescentData.Chart.reindex`: a chart of a descent datum restricts along a
  map of index types.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_reindex`: a descent datum relative
  to an fpqc covering family indexed in an arbitrary universe is effective as soon as each of its
  restrictions to a covering subfamily indexed in the universe of the schemes is.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex`: a descent datum
  with affine structure morphisms, relative to an fpqc covering family indexed in an arbitrary
  universe, is effective.

## Implementation notes

The small subfamily comes from Mathlib's `CategoryTheory.Precoverage.Small` instance for
`AlgebraicGeometry.Scheme.propQCPrecoverage`; `AlgebraicGeometry.Scheme.fpqcPrecoverage` is that
precoverage at flatness.

A chart of the whole datum is built directly. Its base is the base of a chart of the subfamily;
the projection at an index `i` comes from a chart of the subfamily augmented by `i`, carried to
the chosen base along `AlgebraicGeometry.DescentData.Chart.isoOfCharts`, and it is independent of
the augmentation because its compatibility with the subfamily determines it: the base change of
the subfamily to a member of the family is an fpqc covering, hence an epimorphic family.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u v w

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- Morphisms out of a scheme are determined by their restrictions along an fpqc covering. -/
theorem hom_ext_of_mem_fpqcPrecoverage {T Z : Scheme.{u}} {J : Type w} {Y : J → Scheme.{u}}
    (g : ∀ j, Y j ⟶ T) (hg : Presieve.ofArrows Y g ∈ Scheme.fpqcPrecoverage T)
    {a b : T ⟶ Z} (h : ∀ j, g j ≫ a = g j ≫ b) : a = b := by
  have hs : Presieve.IsSheafFor (yoneda.obj Z) (Presieve.ofArrows Y g) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck hg)
  refine hs.isSeparatedFor.ext ?_
  rintro W p ⟨j⟩
  exact h j

/-- A covering family for the quasi-compact precoverage attached to a property of morphisms
admits a covering subfamily indexed in the universe of the schemes. -/
theorem exists_small_subfamily_propQC {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
    {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.propQCPrecoverage P S) :
    ∃ (I' : Type u) (r : I' → I),
      Presieve.ofArrows (fun i' ↦ X (r i')) (fun i' ↦ f (r i')) ∈
        Scheme.propQCPrecoverage P S := by
  let E : (Scheme.propQCPrecoverage P).ZeroHypercover.{v} S := ⟨⟨I, X, f⟩, hf⟩
  have hES : Precoverage.ZeroHypercover.Small.{u} E := inferInstance
  exact ⟨Precoverage.ZeroHypercover.Small.Index E,
    Precoverage.ZeroHypercover.Small.restrictFun E,
    Precoverage.ZeroHypercover.Small.mem₀ E⟩

/-- An fpqc covering family admits a covering subfamily indexed in the universe of the
schemes. -/
theorem exists_small_subfamily {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S) :
    ∃ (I' : Type u) (r : I' → I),
      Presieve.ofArrows (fun i' ↦ X (r i')) (fun i' ↦ f (r i')) ∈ Scheme.fpqcPrecoverage S :=
  exists_small_subfamily_propQC f hf

namespace DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- The restriction of a chart along a map of index types. -/
def Chart.reindex {D : DescentData f} (C : D.Chart) {J : Type w} (m : J → ι) :
    (D.reindex m).Chart where
  base := C.base
  proj j := C.proj (m j)
  isPullback j := C.isPullback (m j)
  compat j j' := C.compat (m j) (m j')

/-- The base of the restriction of a chart is the base of the chart. -/
@[simp]
lemma Chart.reindex_base {D : DescentData f} (C : D.Chart) {J : Type w} (m : J → ι) :
    (C.reindex m).base = C.base := rfl

/-- The projection of the restriction of a chart at `j` is the projection of the chart at
`m j`. -/
@[simp]
lemma Chart.reindex_proj {D : DescentData f} (C : D.Chart) {J : Type w} (m : J → ι) (j : J) :
    (C.reindex m).proj j = C.proj (m j) := rfl

/-- **Effectivity along an fpqc covering family indexed in an arbitrary universe, reduced to
the subfamilies indexed in the universe of the schemes.** -/
theorem isFamilyEffective_of_forall_reindex {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f)
    (H : ∀ (J : Type u) (m : J → I),
      Presieve.ofArrows (fun j ↦ X (m j)) (fun j ↦ f (m j)) ∈ Scheme.fpqcPrecoverage S →
        (D.reindex m).IsFamilyEffective) :
    D.IsFamilyEffective := by
  classical
  obtain ⟨I', r, hr⟩ := exists_small_subfamily f hf
  have hflat : ∀ i, Flat (f i) := fun i ↦ ((Scheme.ofArrows_mem_precoverage_iff _).1 hf.2).2 i
  have hcov : ∀ {K : Type u} (k : K → I),
      Presieve.ofArrows (fun x ↦ X (Sum.elim r k x)) (fun x ↦ f (Sum.elim r k x)) ∈
        Scheme.fpqcPrecoverage S := by
    intro K k
    refine ⟨?_, ?_⟩
    · have hsub : QuasiCompactCover (⟨I', fun i' ↦ X (r i'), fun i' ↦ f (r i')⟩ :
          PreZeroHypercover.{u} S) := Scheme.presieve₀_mem_qcPrecoverage_iff.1 hr.1
      exact Scheme.presieve₀_mem_qcPrecoverage_iff.2
        (QuasiCompactCover.of_hom
          (𝒰 := (⟨I' ⊕ K, fun x ↦ X (Sum.elim r k x),
            fun x ↦ f (Sum.elim r k x)⟩ : PreZeroHypercover.{u} S))
          (𝒱 := (⟨I', fun i' ↦ X (r i'), fun i' ↦ f (r i')⟩ : PreZeroHypercover.{u} S))
          ⟨Sum.inl, fun _ ↦ 𝟙 _, by simp⟩)
    · refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x ↦ ?_, fun x ↦ hflat _⟩
      obtain ⟨i', hi'⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 hr.2).1 x
      exact ⟨Sum.inl i', hi'⟩
  obtain ⟨C₀⟩ := nonempty_chart_of_isFamilyEffective _ (H I' r hr)
  let ch : ∀ (K : Type u) (k : K → I), (D.reindex (Sum.elim r k)).Chart := fun K k ↦
    (nonempty_chart_of_isFamilyEffective _ (H _ (Sum.elim r k) (hcov k))).some
  let cmp : ∀ (K : Type u) (k : K → I), (ch K k).base ≅ C₀.base := fun K k ↦
    Chart.isoOfCharts (𝒰 := ⟨I', fun i' ↦ X (r i'), fun i' ↦ f (r i')⟩) hr
      ((ch K k).reindex Sum.inl) C₀
  have hsub : ∀ (K : Type u) (k : K → I) (i' : I'),
      (ch K k).proj (Sum.inl i') ≫ (cmp K k).hom.left = C₀.proj i' := fun K k i' ↦
    Chart.proj_comp_isoOfCharts_hom (𝒰 := ⟨I', fun i' ↦ X (r i'), fun i' ↦ f (r i')⟩) hr
      ((ch K k).reindex Sum.inl) C₀ i'
  have hcomp : ∀ (K : Type u) (k : K → I) (u v : I' ⊕ K),
      (D.gluingPullbackIso (Sum.elim r k u) (Sum.elim r k v)).hom ≫
          pullback.snd (f (Sum.elim r k u)) ((D.obj (Sum.elim r k v)).hom ≫ f (Sum.elim r k v)) ≫
            ((ch K k).proj v ≫ (cmp K k).hom.left) =
        pullback.fst ((D.obj (Sum.elim r k u)).hom ≫ f (Sum.elim r k u)) (f (Sum.elim r k v)) ≫
          ((ch K k).proj u ≫ (cmp K k).hom.left) := by
    intro K k u v
    have h1 := congrArg (fun t ↦ t ≫ (cmp K k).hom.left) ((ch K k).compat u v)
    simp only [Category.assoc] at h1
    exact h1
  have hspec : ∀ (K : Type u) (k : K → I) (x : K) (i' : I'),
      (D.gluingPullbackIso (k x) (r i')).hom ≫
          pullback.snd (f (k x)) ((D.obj (r i')).hom ≫ f (r i')) ≫ C₀.proj i' =
        pullback.fst ((D.obj (k x)).hom ≫ f (k x)) (f (r i')) ≫
          ((ch K k).proj (Sum.inr x) ≫ (cmp K k).hom.left) := by
    intro K k x i'
    have h1 := hcomp K k (Sum.inr x) (Sum.inl i')
    erw [hsub K k i'] at h1
    exact h1
  have hcovobj : ∀ i : I, Presieve.ofArrows
      (fun i' : I' ↦ pullback ((D.obj i).hom ≫ f i) (f (r i')))
      (fun i' ↦ pullback.fst ((D.obj i).hom ≫ f i) (f (r i'))) ∈
        Scheme.fpqcPrecoverage (D.obj i).left := fun i ↦
    Precoverage.mem_coverings_of_isPullback (fun i' ↦ f (r i')) hr ((D.obj i).hom ≫ f i)
      _ (fun i' ↦ pullback.snd _ _) fun i' ↦ IsPullback.of_hasPullback _ _
  let proj : ∀ i : I, (D.obj i).left ⟶ C₀.base.left := fun i ↦
    (ch PUnit.{u + 1} (fun _ ↦ i)).proj (Sum.inr PUnit.unit) ≫
      (cmp PUnit.{u + 1} (fun _ ↦ i)).hom.left
  have hprj : ∀ (K : Type u) (k : K → I) (x : K),
      (ch K k).proj (Sum.inr x) ≫ (cmp K k).hom.left = proj (k x) := fun K k x ↦
    hom_ext_of_mem_fpqcPrecoverage _ (hcovobj (k x)) fun i' ↦
      (hspec K k x i').symm.trans (hspec PUnit.{u + 1} (fun _ ↦ k x) PUnit.unit i')
  have hfin : ∀ (K : Type u) (k : K → I) (x y : K),
      (D.gluingPullbackIso (k x) (k y)).hom ≫
          pullback.snd (f (k x)) ((D.obj (k y)).hom ≫ f (k y)) ≫ proj (k y) =
        pullback.fst ((D.obj (k x)).hom ≫ f (k x)) (f (k y)) ≫ proj (k x) := by
    intro K k x y
    rw [← hprj K k x, ← hprj K k y]
    exact hcomp K k (Sum.inr x) (Sum.inr y)
  refine Chart.isFamilyEffective ⟨C₀.base, proj, fun i ↦ ?_, fun i j ↦ ?_⟩
  · have : IsIso (cmp PUnit.{u + 1} (fun _ ↦ i)).hom.left :=
      (Over.forget S).map_isIso (cmp PUnit.{u + 1} (fun _ ↦ i)).hom
    have h1 := (ch PUnit.{u + 1} (fun _ ↦ i)).isPullback (Sum.inr PUnit.unit)
    have h2 : IsPullback (cmp PUnit.{u + 1} (fun _ ↦ i)).hom.left
        (ch PUnit.{u + 1} (fun _ ↦ i)).base.hom C₀.base.hom (𝟙 S) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have h3 := h1.paste_horiz h2
    rwa [Category.comp_id] at h3
  · exact hfin (ULift.{u} Bool) (fun b ↦ cond b.down j i) ⟨false⟩ ⟨true⟩

/-- **Effective descent for affine morphisms along an fpqc covering family indexed in an arbitrary
universe.** Let `S` be a scheme, let `{X i ⟶ S}` be a covering family of `S` for the fpqc topology,
indexed by a type in an arbitrary universe, and let `D` be a descent datum relative to that family
all of whose structure morphisms `V i ⟶ X i` are affine. Then `D` is effective: it is isomorphic to
the canonical descent datum of a scheme over `S`. -/
@[stacks 0245 "for a covering family indexed in an arbitrary universe", sga "3 IX 2.3" "partial"]
theorem isFamilyEffective_of_isAffineHom_of_anyIndex {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S) (D : DescentData f)
    (hD : ∀ i, IsAffineHom (D.obj i).hom) : D.IsFamilyEffective :=
  isFamilyEffective_of_forall_reindex f hf D fun _ m hm ↦
    isFamilyEffective_of_isAffineHom (fun j ↦ f (m j)) hm (D.reindex m) fun j ↦ hD (m j)

end DescentData

end AlgebraicGeometry

end

end
