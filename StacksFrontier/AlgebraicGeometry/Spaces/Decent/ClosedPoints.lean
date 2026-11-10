module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Closed points above a closed point of the base

Let `X` be an algebraic space over a scheme `S` and let `Spec k ⟶ X ⟶ S` be a commutative
diagram, that is a field-valued point of `X` in the sense of Stacks 03BU. If `X` is decent, the
image point `s` of `Spec k ⟶ S` is closed in `S` and the residue field extension `κ(s) ⟶ k` is
algebraic, then the image of `Spec k ⟶ X` is a closed point of `|X|`. Moreover, every closed
point of a decent algebraic space is represented by a closed immersion from the spectrum of a
field.

## Main results

* `AlgebraicGeometry.Space.isClosed_singleton_class_of_isAlgebraic_residueField`: a
  field-valued point over a closed point of `S` with algebraic residue field extension has
  closed image in `|X|`.
* `AlgebraicGeometry.Space.isClosed_singleton_iff_isClosed_singleton_pointsToScheme`: a
  point of a represented presheaf is closed exactly when the corresponding point of the
  representing scheme is closed.
* `AlgebraicGeometry.Space.exists_fieldValuedPoint_isClosedImmersion`: a closed point of a
  decent algebraic space is represented by a closed immersion from the spectrum of a field.

## Implementation notes

A field-valued point of `X` is exactly the data of the diagram above: the field `k` is
`AlgebraicGeometry.Space.FieldValuedPoint.carrier`, the morphism `Spec k ⟶ S` is its
`toBase`, the morphism `Spec k ⟶ X` is its `value`, and the image point of `|X|` is its
class. The point `s` and the embedding `κ(s) ⟶ k` are the two components of
`AlgebraicGeometry.Scheme.SpecToEquivOfField` applied to `toBase`, which reads a morphism from
the spectrum of a field as a point of the target together with a residue field embedding.

The first statement is given for condition `(α)` of Stacks 03JX,
`AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint`: every étale chart of `X` by an
affine scheme has finite fibres. Every decent algebraic space satisfies it, by
`AlgebraicGeometry.Space.hasFiniteChartFibersAtEveryPoint_of_isDecentSpace`.

## References

* [Stacks Project, Tag 01TE](https://stacks.math.columbia.edu/tag/01TE)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JS](https://stacks.math.columbia.edu/tag/03JS)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 07U5](https://stacks.math.columbia.edu/tag/07U5)
* [Stacks Project, Tag 0AHB](https://stacks.math.columbia.edu/tag/0AHB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Algebraicity in a tower of fields -/

/-- In a factorization `γ = β ∘ α` of ring maps, the induced algebra structures form a scalar
tower. -/
private theorem isScalarTower_of_eq_comp {K L M : Type u} [Field K] [Field L] [Field M]
    (α : K →+* L) (β : L →+* M) (γ : K →+* M) (hγ : γ = β.comp α) :
    letI := α.toAlgebra
    letI := β.toAlgebra
    letI := γ.toAlgebra
    IsScalarTower K L M := by
  subst hγ
  let := α.toAlgebra
  let := β.toAlgebra
  let := (β.comp α).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- In a factorization `γ = β ∘ α` of extensions of fields, algebraicity of `γ` gives
algebraicity of `α`. -/
private theorem isAlgebraic_of_comp {K L M : Type u} [Field K] [Field L] [Field M]
    (α : K →+* L) (β : L →+* M) (γ : K →+* M) (hγ : γ = β.comp α)
    (halg : letI := γ.toAlgebra; Algebra.IsAlgebraic K M) :
    letI := α.toAlgebra
    Algebra.IsAlgebraic K L := by
  let := α.toAlgebra
  let := β.toAlgebra
  let := γ.toAlgebra
  have : Algebra.IsAlgebraic K M := halg
  have := isScalarTower_of_eq_comp α β γ hγ
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom K L M) β.injective

/-- In a factorization `γ = β ∘ α` of extensions of fields, algebraicity of `α` and of `β`
gives algebraicity of `γ`. -/
private theorem isAlgebraic_comp {K L M : Type u} [Field K] [Field L] [Field M]
    (α : K →+* L) (β : L →+* M) (γ : K →+* M) (hγ : γ = β.comp α)
    (hα : letI := α.toAlgebra; Algebra.IsAlgebraic K L)
    (hβ : letI := β.toAlgebra; Algebra.IsAlgebraic L M) :
    letI := γ.toAlgebra
    Algebra.IsAlgebraic K M := by
  let := α.toAlgebra
  let := β.toAlgebra
  let := γ.toAlgebra
  have : Algebra.IsAlgebraic K L := hα
  have : Algebra.IsAlgebraic L M := hβ
  have := isScalarTower_of_eq_comp α β γ hγ
  exact Algebra.IsAlgebraic.trans K L M

/-! ### Algebraicity of residue field extensions along a factorization -/

/-- Algebraicity of a residue field extension passes to an intermediate scheme: if
`g ≫ h = f` and the residue field at `z` is algebraic over the residue field of `f z`, then
the residue field at `g z` is algebraic over the residue field of `h (g z)`. -/
private theorem isAlgebraic_residueField_of_comp_eq {Z V W : Scheme.{u}}
    (f : Z ⟶ W) (g : Z ⟶ V) (h : V ⟶ W) (z : Z) (hgh : g ≫ h = f)
    (halg : letI := (f.residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField (f z)) (Z.residueField z)) :
    letI := (h.residueFieldMap (g z)).hom.toAlgebra
    Algebra.IsAlgebraic (W.residueField (h (g z))) (V.residueField (g z)) := by
  subst hgh
  exact isAlgebraic_of_comp (h.residueFieldMap (g z)).hom (g.residueFieldMap z).hom
    ((g ≫ h).residueFieldMap z).hom
    (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp g h z)) halg

/-- Algebraicity of residue field extensions composes along a factorization `g ≫ h = f`. -/
private theorem isAlgebraic_residueField_comp_of_comp_eq {Z V W : Scheme.{u}}
    (f : Z ⟶ W) (g : Z ⟶ V) (h : V ⟶ W) (z : Z) (hgh : g ≫ h = f)
    (hh : letI := (h.residueFieldMap (g z)).hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField (h (g z))) (V.residueField (g z)))
    (hg : letI := (g.residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic (V.residueField (g z)) (Z.residueField z)) :
    letI := (f.residueFieldMap z).hom.toAlgebra
    Algebra.IsAlgebraic (W.residueField (f z)) (Z.residueField z) := by
  subst hgh
  exact isAlgebraic_comp (h.residueFieldMap (g z)).hom (g.residueFieldMap z).hom
    ((g ≫ h).residueFieldMap z).hom
    (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp g h z)) hh hg

/-- A morphism `b : Spec K ⟶ W` out of the spectrum of a field is a point `s` of `W` together
with an embedding `κ(s) ⟶ K`. If that embedding is algebraic, then so is the residue field
extension `κ(s) ⟶ κ(c)` induced by `b` at the unique point `c` of `Spec K`. -/
private theorem isAlgebraic_residueField_specToEquivOfField {W : Scheme.{u}} (K : Type u)
    [Field K] (b : Spec (CommRingCat.of K) ⟶ W) (c : Spec (CommRingCat.of K))
    (halg : letI := (W.SpecToEquivOfField K b).2.hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField (W.SpecToEquivOfField K b).1) K) :
    letI := (b.residueFieldMap c).hom.toAlgebra
    Algebra.IsAlgebraic (W.residueField (b c))
      ((Spec (CommRingCat.of K)).residueField c) := by
  obtain rfl : c = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  refine isAlgebraic_of_comp (b.residueFieldMap (IsLocalRing.closedPoint K)).hom
    (Scheme.descResidueField
      (Scheme.stalkClosedPointTo (𝟙 (Spec (CommRingCat.of K))))).hom
    (W.SpecToEquivOfField K b).2.hom ?_ halg
  have hmap := congrArg CommRingCat.Hom.hom
    (Scheme.descResidueField_stalkClosedPointTo_comp (f := b)
      (g := 𝟙 (Spec (CommRingCat.of K))))
  convert hmap using 1
  rfl

/-! ### The statement for schemes -/

/-- Let `q : Z ⟶ Spec K` be étale, let `j : Z ⟶ V` and `v : V ⟶ W` be morphisms and let
`b : Spec K ⟶ W` make the resulting square commute. If the point `s` of `W` underlying `b` is
closed and the embedding `κ(s) ⟶ K` is algebraic, then the image in `V` of every point of `Z`
is a closed point. -/
private theorem isClosed_singleton_image_of_etale_over_field {W : Scheme.{u}} {K : Type u}
    [Field K] {Z V : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ W)
    (q : Z ⟶ Spec (CommRingCat.of K)) (j : Z ⟶ V) (v : V ⟶ W) (hq : Etale q)
    (hcomm : j ≫ v = q ≫ b) (z : Z)
    (hclosed : IsClosed ({(W.SpecToEquivOfField K b).1} : Set W))
    (halg : letI := (W.SpecToEquivOfField K b).2.hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField (W.SpecToEquivOfField K b).1) K) :
    IsClosed ({j z} : Set V) := by
  have := hq
  have hbase : v (j z) = (W.SpecToEquivOfField K b).1 := by
    have hpt := congrArg (fun k : Z ⟶ W ↦ k z) hcomm
    change v (j z) = b (q z) at hpt
    rw [hpt, show q z = IsLocalRing.closedPoint K from
      Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _]
    exact (Scheme.SpecToEquivOfField_apply_fst K W b).symm
  have halgZ : let := ((q ≫ b).residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField ((q ≫ b) z)) (Z.residueField z) :=
    isAlgebraic_residueField_comp_of_comp_eq (q ≫ b) q b z rfl
      (isAlgebraic_residueField_specToEquivOfField K b (q z) halg) (by infer_instance)
  have halgV : let := (v.residueFieldMap (j z)).hom.toAlgebra
      Algebra.IsAlgebraic (W.residueField (v (j z))) (V.residueField (j z)) :=
    isAlgebraic_residueField_of_comp_eq (q ≫ b) j v z hcomm halgZ
  exact isClosed_of_isAlgebraic_residueField v (j z) halgV (hbase ▸ hclosed)

/-! ### Closed points of an algebraic space -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A point of a presheaf represented by an object `U` of the big fppf site over `S` is a
closed point exactly when the corresponding point of the scheme underlying `U` is a closed
point. -/
theorem isClosed_singleton_iff_isClosed_singleton_pointsToScheme
    (U : BigFppfOver B S hS) (a : points B S hS (yoneda.obj U)) :
    IsClosed ({a} : Set (points B S hS (yoneda.obj U))) ↔
      IsClosed ({pointsToScheme B S hS U a} :
        Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  rw [← (schemePointsHomeomorph B S hS U).isClosed_image, Set.image_singleton,
    schemePointsHomeomorph_apply]

/-- A point of an étale chart of an algebraic space `X` lying above the image point of a
field-valued point `p` whose base point is closed and whose residue field extension is algebraic
is a closed point of the scheme underlying the chart. -/
private theorem isClosed_singleton_pointsToScheme_of_isAlgebraic_residueField
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (p : FieldValuedPoint B S hS X)
    (hclosed : IsClosed ({(S.SpecToEquivOfField p.carrier p.toBase).1} : Set S))
    (halg : letI := (S.SpecToEquivOfField p.carrier p.toBase).2.hom.toAlgebra
      Algebra.IsAlgebraic
        (S.residueField (S.SpecToEquivOfField p.carrier p.toBase).1) p.carrier)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (a : points B S hS (yoneda.obj U))
    (ha : pointsMap B S hS (yoneda.obj U) φ a = p.class B S hS X) :
    IsClosed ({pointsToScheme B S hS U a} :
      Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  obtain ⟨T, m, j, hmEtale, hpb⟩ :
      ∃ (T : BigFppfOver B S hS) (m : T ⟶ p.siteObject) (j : T ⟶ U),
        Etale ((BigFppfOver.toScheme B S hS).map m) ∧
        IsPullback (yoneda.map j) (yoneda.map m) φ (fieldMorphism B S hS X p) := by
    have hrep : yoneda.relativelyRepresentable φ :=
      (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).1
        hX.diagonal_representable φ
    refine ⟨hrep.pullback (fieldMorphism B S hS X p), hrep.snd (fieldMorphism B S hS X p),
      hrep.fst' (fieldMorphism B S hS X p), ?_,
      hrep.isPullback' (fieldMorphism B S hS X p)⟩
    exact hφ.property (fieldMorphism B S hS X p)
      (yoneda.map (hrep.fst' (fieldMorphism B S hS X p)))
      (hrep.snd (fieldMorphism B S hS X p))
      (hrep.isPullback' (fieldMorphism B S hS X p))
  obtain ⟨t, htj, -⟩ := exists_points_of_isPullback B S hS hpb a
    ((p.tautologicalPoint B S hS X).class B S hS (yoneda.obj p.siteObject))
    (ha.trans (pointsMap_fieldMorphism_tautologicalPoint B S hS X p).symm)
  have hinc : ∀ {A C : BigFppfOver B S hS} (f : A ⟶ C),
      (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map C.hom = B.inclusion.map A.hom := by
    intro A C f
    change B.inclusion.map f.left ≫ B.inclusion.map C.hom = B.inclusion.map A.hom
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map f.w
  have hcomm : (BigFppfOver.toScheme B S hS).map j ≫ B.inclusion.map U.hom =
      (BigFppfOver.toScheme B S hS).map m ≫ p.toBase := by
    rw [hinc j]
    exact (hinc m).symm
  rw [show pointsToScheme B S hS U a =
      (BigFppfOver.toScheme B S hS).map j (pointsToScheme B S hS T t) by
    rw [← htj]; exact pointsToScheme_pointsMap B S hS j t]
  exact isClosed_singleton_image_of_etale_over_field p.toBase
    ((BigFppfOver.toScheme B S hS).map m) ((BigFppfOver.toScheme B S hS).map j)
    (B.inclusion.map U.hom) hmEtale hcomm (pointsToScheme B S hS T t) hclosed halg

/-- Let `X` be an algebraic space over a scheme `S` above every point of which every étale
chart of `X` by an affine scheme has a finite fibre, which is condition `(α)` of Stacks 03JX —
in particular a decent one. Let `p` be a field-valued point of `X`
with field of definition `k`, so a commutative diagram `Spec k ⟶ X ⟶ S`. If the image point
`s` of `Spec k ⟶ S` is a closed point of `S` and the residue field extension `κ(s) ⟶ k` is
algebraic, then the image of `Spec k ⟶ X` is a closed point of `|X|`. -/
@[stacks 07U5 "with decency read as condition (alpha) of Stacks 03JX"]
theorem isClosed_singleton_class_of_isAlgebraic_residueField
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdecent : HasFiniteChartFibersAtEveryPoint B S hS X)
    (p : FieldValuedPoint B S hS X)
    (hclosed : IsClosed ({(S.SpecToEquivOfField p.carrier p.toBase).1} : Set S))
    (halg : letI := (S.SpecToEquivOfField p.carrier p.toBase).2.hom.toAlgebra
      Algebra.IsAlgebraic
        (S.residueField (S.SpecToEquivOfField p.carrier p.toBase).1) p.carrier) :
    IsClosed ({p.class B S hS X} : Set (points B S hS X)) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  rw [Set.mem_singleton_iff]
  rw [← specializes_iff_mem_closure] at hy
  obtain ⟨U, φ, hsurj, hφ⟩ := hX.exists_atlas
  obtain ⟨a, ha⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U φ).1 hsurj y
  obtain ⟨a', ha'spec, ha'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX hy
    (hdecent (p.class B S hS X)) U φ hφ a ha
  have hclosedPt : IsClosed ({a'} : Set (points B S hS (yoneda.obj U))) :=
    (isClosed_singleton_iff_isClosed_singleton_pointsToScheme B S hS U a').2
      (isClosed_singleton_pointsToScheme_of_isAlgebraic_residueField B S hS hX p hclosed
        halg U φ hφ a' ha')
  have haa' : a = a' := by
    simpa only [hclosedPt.closure_eq, Set.mem_singleton_iff] using ha'spec.mem_closure
  rwa [← ha, haa']

/-! ### Closed immersions out of the spectrum of a field -/

/-- A finite set of closed points of a topological space is closed. -/
private theorem isClosed_of_finite_of_isClosed_singletons {Z : Type*} [TopologicalSpace Z]
    {s : Set Z} (hs : s.Finite) (hclosed : ∀ z ∈ s, IsClosed ({z} : Set Z)) : IsClosed s := by
  simpa using hs.isClosed_biUnion hclosed

/-- A monomorphism from the spectrum of a field whose image point is closed is a closed
immersion. -/
private theorem isClosedImmersion_of_mono_of_isClosed_singleton {K : Type u} [Field K]
    {Y : Scheme.{u}} (f : Spec (CommRingCat.of K) ⟶ Y) [Mono f]
    (hclosed : IsClosed ({f (IsLocalRing.closedPoint K)} : Set Y)) :
    _root_.AlgebraicGeometry.IsClosedImmersion f := by
  let g := Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo f))
  have hfactor : f = g ≫ Y.fromSpecResidueField (f (IsLocalRing.closedPoint K)) :=
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y f).symm
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      (Y.fromSpecResidueField (f (IsLocalRing.closedPoint K))) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  have : Mono g := mono_of_mono_fac hfactor.symm
  have : Surjective g := ⟨fun _ ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have : IsIso g := Flat.isIso_of_surjective_of_mono g
  rw [hfactor]
  infer_instance

/-! ### Local rings of a scheme étale over a field -/

/-- The local rings of an affine scheme étale over the spectrum of a field are fields. -/
private theorem isField_stalk_of_isAffine_of_etale_over_field (K : Type u) [Field K]
    {W : Scheme.{u}} [IsAffine W] (t : W ⟶ Spec (CommRingCat.of K)) (ht : Etale t) (z : W) :
    IsField (W.presheaf.stalk z) := by
  have := ht
  let A := Γ(W, ⊤)
  let := globalSectionsAlgebra K t
  have : Algebra.Etale K A := algebra_etale_globalSections K t
  have : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : _root_.IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  let q : PrimeSpectrum A := W.isoSpec.hom z
  let R := Localization.AtPrime q.asIdeal
  have : IsArtinianRing R := IsArtinianRing.localization_artinian q.asIdeal.primeCompl R
  have hR : IsField R := IsArtinianRing.isField_of_isReduced_of_isLocalRing R
  let e : CommRingCat.of R ≅ CommRingCat.of (W.presheaf.stalk z) :=
    (Spec.stalkIso A q).symm ≪≫ asIso (W.isoSpec.hom.stalkMap z)
  exact e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isField hR

/-- The local rings of a scheme étale over the spectrum of a field are fields. -/
private theorem isField_stalk_of_etale_over_field (K : Type u) [Field K] {W : Scheme.{u}}
    (t : W ⟶ Spec (CommRingCat.of K)) (ht : Etale t) (z : W) :
    IsField (W.presheaf.stalk z) := by
  have := ht
  obtain ⟨i, z', rfl⟩ := W.affineCover.exists_eq z
  have hcomp : Etale (W.affineCover.f i ≫ t) := Etale.etale_comp _ _
  exact (asIso ((W.affineCover.f i).stalkMap z')).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (isField_stalk_of_isAffine_of_etale_over_field K (W.affineCover.f i ≫ t) hcomp z')

/-! ### Closed points of an étale chart above a closed point -/

/-- A point of an étale chart of a decent algebraic space lying above a closed point is a closed
point of the scheme underlying the chart. -/
private theorem isClosed_singleton_pointsToScheme_of_isClosed_singleton
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {x : points B S hS X}
    (hx : IsClosed ({x} : Set (points B S hS X))) (U : BigFppfOver B S hS)
    (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (a : points B S hS (yoneda.obj U)) (ha : pointsMap B S hS (yoneda.obj U) φ a = x) :
    IsClosed ({pointsToScheme B S hS U a} :
      Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  rw [← isClosed_singleton_iff_isClosed_singleton_pointsToScheme,
    ← closure_subset_iff_isClosed]
  intro b hb
  rw [Set.mem_singleton_iff]
  rw [← specializes_iff_mem_closure] at hb
  have hbx : pointsMap B S hS (yoneda.obj U) φ b = x :=
    (hb.map (continuous_pointsMap B S hS φ)).mem_closed hx ha
  exact eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) U φ hφ b a
    (hbx.trans ha.symm) hb

/-! ### The base change of a closed point to an étale chart -/

/-- The base change of a quasi-compact monomorphic field-valued representative of a *closed*
point of a decent algebraic space `X` along an étale chart `φ : h_U ⟶ X` with quasi-compact
source is a closed immersion into that chart. -/
private theorem isClosedImmersion_map_of_isPullback_of_compactSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {x : points B S hS X}
    (hx : IsClosed ({x} : Set (points B S hS X))) (p : FieldValuedPoint B S hS X)
    (hpx : p.class B S hS X = x) (hmono : Mono (fieldMorphism B S hS X p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS X p))
    {U W : BigFppfOver B S hS}
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (t : W ⟶ p.siteObject) (n : W ⟶ U)
    (sq : IsPullback (yoneda.map t) (yoneda.map n) (fieldMorphism B S hS X p) φ) :
    _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map n) := by
  have hetT : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map t) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq.flip hφ
  have hEtaleT : Etale ((BigFppfOver.toScheme B S hS).map t) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ t).1 hetT
  have hqcs : IsQuasiCompactSpace B S hS (pullback φ (fieldMorphism B S hS X p)) :=
    hqc (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (isQuasiCompactSpace_yoneda_obj B S hS hU) φ
  have hWcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (hqcs.of_iso B S hS
        ((IsPullback.of_hasPullback φ (fieldMorphism B S hS X p)).isoIsPullback _ _ sq.flip))
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hWfin : Finite ((BigFppfOver.toScheme B S hS).obj W) :=
    finite_of_etale_of_subsingleton ((BigFppfOver.toScheme B S hS).map t)
  have hptsSub : Subsingleton (points B S hS (yoneda.obj p.siteObject)) :=
    (pointsEquivScheme B S hS p.siteObject).subsingleton
  have hfm : ∀ y : points B S hS (yoneda.obj p.siteObject),
      pointsMap B S hS (yoneda.obj p.siteObject) (fieldMorphism B S hS X p) y =
        p.class B S hS X := by
    intro y
    rw [Subsingleton.elim y
      ((p.tautologicalPoint B S hS X).class B S hS (yoneda.obj p.siteObject))]
    exact pointsMap_fieldMorphism_tautologicalPoint B S hS X p
  have hpointClosed : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      IsClosed ({(BigFppfOver.toScheme B S hS).map n z} :
        Set ((BigFppfOver.toScheme B S hS).obj U)) := by
    intro z
    have hclass : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (yoneda.obj W) (yoneda.map n)
          ((schemePointRepresentative B S hS W z).class B S hS (yoneda.obj W))) = x := by
      rw [← pointsMap_comp_apply, ← sq.w, pointsMap_comp_apply, hfm]
      exact hpx
    have hci := isClosed_singleton_pointsToScheme_of_isClosed_singleton B S hS hX hdec hx
      U φ hφ _ hclass
    rwa [pointsToScheme_pointsMap B S hS n
        ((schemePointRepresentative B S hS W z).class B S hS (yoneda.obj W)),
      pointsToScheme_class B S hS W (schemePointRepresentative B S hS W z),
      schemePointRepresentative_point B S hS W z] at hci
  have hmonoY : Mono (yoneda.map n) := sq.mono_snd_of_mono
  have hmonoN : Mono n := yoneda.mono_of_mono_map hmonoY
  have hmonoS : Mono ((BigFppfOver.toScheme B S hS).map n) :=
    Functor.map_mono (BigFppfOver.toScheme B S hS) n
  have hclosedMap : IsClosedMap ((BigFppfOver.toScheme B S hS).map n).base := by
    intro A _
    refine isClosed_of_finite_of_isClosed_singletons (Set.toFinite _) ?_
    rintro y ⟨z, -, rfl⟩
    exact hpointClosed z
  have hemb : Topology.IsClosedEmbedding ((BigFppfOver.toScheme B S hS).map n).base :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      ((BigFppfOver.toScheme B S hS).map n).continuous
      (Scheme.Hom.injective ((BigFppfOver.toScheme B S hS).map n)) hclosedMap
  have hstalks : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      Function.Surjective (ConcreteCategory.hom
        (((BigFppfOver.toScheme B S hS).map n).stalkMap z)) := by
    intro z
    let j := ((BigFppfOver.toScheme B S hS).obj W).fromSpecResidueField z
    let z' : Spec (((BigFppfOver.toScheme B S hS).obj W).residueField z) :=
      IsLocalRing.closedPoint _
    have hz : j z' = z := Scheme.fromSpecResidueField_apply z _
    have hmonoj : Mono (j ≫ (BigFppfOver.toScheme B S hS).map n) := mono_comp j _
    have hclosedComp : IsClosed ({(j ≫ (BigFppfOver.toScheme B S hS).map n) z'} :
        Set ((BigFppfOver.toScheme B S hS).obj U)) := by
      change IsClosed {(BigFppfOver.toScheme B S hS).map n (j z')}
      rw [hz]
      exact hpointClosed z
    have hcomp : _root_.AlgebraicGeometry.IsClosedImmersion
        (j ≫ (BigFppfOver.toScheme B S hS).map n) :=
      @isClosedImmersion_of_mono_of_isClosed_singleton _ inferInstance _ _ hmonoj hclosedComp
    have hsurjComp := hcomp.stalkMap_surjective z'
    rw [Scheme.Hom.stalkMap_comp j ((BigFppfOver.toScheme B S hS).map n) z'] at hsurjComp
    have hjinj : Function.Injective (ConcreteCategory.hom (j.stalkMap z')) := by
      have hfield : IsField (((BigFppfOver.toScheme B S hS).obj W).presheaf.stalk (j z')) := by
        rw [hz]
        exact isField_stalk_of_etale_over_field p.carrier
          ((BigFppfOver.toScheme B S hS).map t) hEtaleT z
      have : IsSimpleRing (((BigFppfOver.toScheme B S hS).obj W).presheaf.stalk (j z')) :=
        (isSimpleRing_iff_isField _).mpr hfield
      exact RingHom.injective _
    have hsurjN : Function.Surjective (ConcreteCategory.hom
        (((BigFppfOver.toScheme B S hS).map n).stalkMap (j z'))) :=
      Function.Surjective.of_comp_left
        (show Function.Surjective (ConcreteCategory.hom (j.stalkMap z') ∘
          ConcreteCategory.hom (((BigFppfOver.toScheme B S hS).map n).stalkMap (j z')))
          from hsurjComp) hjinj
    rw [← hz]
    exact hsurjN
  have : IsPreimmersion ((BigFppfOver.toScheme B S hS).map n) :=
    { isEmbedding := hemb.isEmbedding
      stalkMap_surjective := hstalks }
  exact _root_.AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ hemb.isClosed_range

/-! ### Stacks 0AHB -/

/-- A closed point of a decent algebraic space `X` over a scheme `S` is represented by a closed
immersion from the spectrum of a field: there is a field-valued point of `X` whose class is the
given point and whose presenting morphism `Spec k ⟶ X` is a closed immersion. -/
@[stacks 0AHB]
theorem exists_fieldValuedPoint_isClosedImmersion
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (x : points B S hS X)
    (hx : IsClosed ({x} : Set (points B S hS X))) :
    ∃ p : FieldValuedPoint B S hS X,
      p.class B S hS X = x ∧ IsClosedImmersion B S hS (fieldMorphism B S hS X p) := by
  obtain ⟨p, hpx, hmono, hqc⟩ := hdec x
  refine ⟨p, hpx, ?_⟩
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable (fieldMorphism B S hS X p) :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).1
      hX.diagonal_representable _
  obtain ⟨U, a, hasurj, haet⟩ := hX.exists_atlas
  have := isMultiplicative_presheaf_etale B S hS
  have hq : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hrep.snd a)) := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (fun V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens ↦
        (V : ((BigFppfOver.toScheme B S hS).obj U).Opens))
      (iSup_affineOpens_eq_top _)]
    intro V
    have hVsize : B.Contains (V : ((BigFppfOver.toScheme B S hS).obj U).Opens).toScheme :=
      (Scheme.size_coe_opens_le ((BigFppfOver.toScheme B S hS).obj U) V.1).trans_lt
        U.left.property
    let v : (Over.mk ((ObjectProperty.homMk
        (V : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι :
          B.obj hVsize ⟶ U.left) ≫ U.hom) : BigFppfOver B S hS) ⟶ U :=
      Over.homMk (ObjectProperty.homMk
        (V : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι) rfl
    have hvEt : Etale ((BigFppfOver.toScheme B S hS).map v) := by
      change Etale (V : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι
      infer_instance
    have haV : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map v ≫ a) :=
      MorphismProperty.comp_mem _ _ _
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ v).2 hvEt) haet
    have sqW : IsPullback (yoneda.map (pullback.fst (hrep.snd a) v ≫ hrep.fst' a))
        (yoneda.map (pullback.snd (hrep.snd a) v)) (fieldMorphism B S hS X p)
        (yoneda.map v ≫ a) := by
      simpa only [Functor.map_comp] using
        ((IsPullback.of_hasPullback (hrep.snd a) v).map yoneda).paste_horiz
          (hrep.isPullback' a)
    have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (Over.mk ((ObjectProperty.homMk
          (V : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι :
            B.obj hVsize ⟶ U.left) ≫ U.hom) : BigFppfOver B S hS)) := V.2
    have hVcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj
        (Over.mk ((ObjectProperty.homMk
          (V : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι :
            B.obj hVsize ⟶ U.left) ≫ U.hom) : BigFppfOver B S hS)) :=
      have := hVaff
      inferInstance
    have hci := isClosedImmersion_map_of_isPullback_of_compactSpace B S hS hX hdec hx p hpx
      hmono hqc hVcpt (yoneda.map v ≫ a) haV _ _ sqW
    have sp : IsPullback
        ((BigFppfOver.toScheme B S hS).map (pullback.fst (hrep.snd a) v))
        ((BigFppfOver.toScheme B S hS).map (pullback.snd (hrep.snd a) v))
        ((BigFppfOver.toScheme B S hS).map (hrep.snd a))
        (V : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι :=
      (IsPullback.of_hasPullback (hrep.snd a) v).map (BigFppfOver.toScheme B S hS)
    let j := sp.isoIsPullback _ _
      (isPullback_morphismRestrict
        ((BigFppfOver.toScheme B S hS).map (hrep.snd a)) V.1).flip
    have hj : j.inv ≫ (BigFppfOver.toScheme B S hS).map (pullback.snd (hrep.snd a) v) =
        (BigFppfOver.toScheme B S hS).map (hrep.snd a) ∣_ V.1 := by simp [j]
    have hh := MorphismProperty.RespectsIso.precomp
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) j.inv _ hci
    rwa [hj] at hh
  have hcl : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (hrep.snd a)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (hrep.snd a)).2 hq
  have := Stacks.Descent.isClosedImmersion_descendsAlong_fppf.{u}
  exact presheaf_of_surjectiveEtaleChart_of_descendsAlong hrep hasurj haet
    (hrep.isPullback' a) hcl

end AlgebraicGeometry.Space

end
