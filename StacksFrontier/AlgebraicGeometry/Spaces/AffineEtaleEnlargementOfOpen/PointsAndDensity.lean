module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Points of representables, density and dense affine opens

Auxiliary results for the enlargement of a dense open subspace of a Noetherian algebraic space by
an affine etale chart (Stacks 0F4C): etaleness of open immersions and of composites of presheaves
on the big fppf site, the identification of the points of a represented presheaf with the points
of the representing scheme as a homeomorphism, the density statements this implies, the dense
open affine inside an open subspace of a Noetherian algebraic space (Stacks 06NH), and the points
of a binary coproduct in the big fppf site.

## Main results

* `AlgebraicGeometry.Space.exists_dense_affine_openImmersion`: a Noetherian algebraic space has a
  dense open affine inside any of its open subspaces.
* `AlgebraicGeometry.Space.binary_coproduct_points_cover`: every point of a coproduct in the big
  fppf site comes from one of the two summands.

## References

* [Stacks Project, Tag 0F4C](https://stacks.math.columbia.edu/tag/0F4C)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space


/-- An open immersion of presheaves on the big fppf site is étale, since an open immersion
of schemes is étale. -/
theorem isEtale_of_isOpenImmersion_aux
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : G ⟶ H} (hf : AlgebraicGeometry.Space.IsOpenImmersion B S hS f) :
    AlgebraicGeometry.Space.IsEtale B S hS f := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T
  let Q := MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have hPQ : P ≤ Q := by
    intro X Y g hg
    change AlgebraicGeometry.IsOpenImmersion (T.map g) at hg
    let : AlgebraicGeometry.IsOpenImmersion (T.map g) := hg
    exact (inferInstance : Etale (T.map g))
  have hfP : P.presheaf f := hf
  have hfQ : Q.presheaf f := MorphismProperty.relative_monotone hPQ f hfP
  let : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage T
  let : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  intro A g hg
  exact MorphismProperty.comp_mem Q.presheaf g f hg hfQ

/-- A composition of étale morphisms of presheaves on the big fppf site is étale. -/
theorem isEtale_comp_aux
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : AlgebraicGeometry.Space.IsEtale B S hS f)
    (hg : AlgebraicGeometry.Space.IsEtale B S hS g) :
    AlgebraicGeometry.Space.IsEtale B S hS (f ≫ g) := by
  intro A φ hφ
  simpa only [Category.assoc] using hg A (φ ≫ f) (hf A φ hφ)

/-- The underlying scheme point of a field-valued point of a represented presheaf moves
along the underlying morphism of schemes when the field-valued point is pushed along a
morphism of the site. -/
private theorem schemePoint_fieldValuedPoint_map
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (A D : AlgebraicGeometry.BigFppfOver B S hS) (f : A ⟶ D)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj A)) :
    AlgebraicGeometry.Space.schemePoint B S hS D
        (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj A) (yoneda.map f) p) =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f
        (AlgebraicGeometry.Space.schemePoint B S hS A p) := by
  change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (p.value ≫ f) (IsLocalRing.closedPoint p.carrier) =
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p.value
        (IsLocalRing.closedPoint p.carrier))
  rw [Functor.map_comp]
  rfl

/-- The point map of an identity morphism is the identity on points. -/
private theorem pointsMap_id_apply
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (x : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS F (𝟙 F) x = x := by
  induction x using Quot.inductionOn with | h p => rfl

/-- A morphism of algebraic spaces whose image on points lies in the image of an open
immersion factors through that open immersion. -/
theorem factorsThrough_isOpenImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hH : AlgebraicGeometry.IsAlgebraicSpace B S hS H)
    (i : F ⟶ G) (hi : AlgebraicGeometry.Space.IsOpenImmersion B S hS i) (f : H ⟶ G)
    (hpoints : Set.range (AlgebraicGeometry.Space.pointsMap B S hS H f) ⊆
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS F i)) :
    ∃ g : H ⟶ F, g ≫ i = f := by
  let : Mono i := mono_of_isOpenImmersion B S hS i hi
  let R := Subfunctor.range i
  let P := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  have hi' : inv (Subfunctor.toRange i) ≫ i = R.ι := by
    calc
      _ = inv (Subfunctor.toRange i) ≫ (Subfunctor.toRange i ≫ R.ι) :=
        congrArg (fun t => inv (Subfunctor.toRange i) ≫ t) (Subfunctor.toRange_ι i).symm
      _ = R.ι := by simp
  have hRopen : AlgebraicGeometry.Space.IsOpenImmersion B S hS R.ι := by
    rw [← hi']
    exact MorphismProperty.RespectsIso.precomp P (inv (Subfunctor.toRange i)) i hi
  have hR : AlgebraicGeometry.Space.IsOpenSubspace B S hS R :=
    ⟨AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS R.ι hRopen.1 hG,
      hRopen⟩
  have hsubset : Set.range (AlgebraicGeometry.Space.pointsMap B S hS H f) ⊆
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS R.toFunctor R.ι) := by
    rintro x hx
    obtain ⟨y, rfl⟩ := hpoints hx
    refine ⟨AlgebraicGeometry.Space.pointsMap B S hS F (Subfunctor.toRange i) y, ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
  obtain ⟨g, hg⟩ := (AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points
    B S hS hG hH R hR f).2 hsubset
  refine ⟨g ≫ inv (Subfunctor.toRange i), ?_⟩
  rw [Category.assoc, hi', hg]

/-- A morphism of the big fppf site whose underlying morphism of schemes is an open
immersion induces an open immersion of the represented presheaves. -/
theorem isOpenImmersion_yoneda_map_aux
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A D : AlgebraicGeometry.BigFppfOver B S hS} (j : A ⟶ D)
    (hj : AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)) :
    AlgebraicGeometry.Space.IsOpenImmersion B S hS (yoneda.map j) := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T
  let : P.IsStableUnderBaseChange := ⟨by
    intro X Y Y' R f g f' g' h hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsOpenImmersion) (h.map T) hg⟩
  exact MorphismProperty.relative_map (P := P) hj

/-- If `g` lifts `Z.ι` along `f` and the inclusion of the preimage factors through `g`, then
the preimage of `Z` along `f` is isomorphic to `Z`. -/
theorem isIso_fromPreimage_of_section {C : Type*} [Category C] {X Y : C ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X) (g : Z.toFunctor ⟶ Y) (hg : g ≫ f = Z.ι)
    (hng : Z.fromPreimage f ≫ g = (Z.preimage f).ι) : IsIso (Z.fromPreimage f) := by
  have hn := CategoryTheory.Subfunctor.isPullback_preimage f Z
  let s : Z.toFunctor ⟶ (Z.preimage f).toFunctor := hn.lift (𝟙 _) g (by simpa using hg.symm)
  have hsn : s ≫ Z.fromPreimage f = 𝟙 _ := hn.lift_fst _ _ _
  have hsi : s ≫ (Z.preimage f).ι = g := hn.lift_snd _ _ _
  refine ⟨⟨s, hn.hom_ext ?_ ?_, hsn⟩⟩
  · simp only [Category.assoc, hsn, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, hsi, hng, Category.id_comp]

/-- The field-valued point of a scheme underlying a field-valued point of the presheaf it
represents. -/
private noncomputable def absoluteFieldValuedPoint {B : AlgebraicGeometry.BigFppfSite.{u}}
    (S : Scheme.{u}) (hS : B.Contains S) (U : AlgebraicGeometry.BigFppfOver B S hS)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    AlgebraicGeometry.FieldValuedPoint ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) where
  carrier := p.carrier
  field := p.field
  map := B.inclusion.map p.value.left

/-- The field-valued point of a represented presheaf represented by a point of the
representing scheme, taken over the residue field at that point. -/
private noncomputable def schemePointRepresentative_aux
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) :
    AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U) := by
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U
  let hK : B.Contains (Spec (X.residueField x)) := B.residueField_spec_contains U.left.property x
  let kobj : B.Schemes := B.obj hK
  let f : kobj ⟶ U.left := B.inclusion.preimage (X := kobj) (Y := U.left)
    (X.fromSpecResidueField x)
  let V : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (f ≫ U.hom)
  refine ⟨X.residueField x, hK, ?_, ?_⟩
  · exact B.inclusion.map (f ≫ U.hom)
  · change V ⟶ U
    exact Over.homMk f

/-- The scheme point underlying the residue-field representative of a point of a scheme is
that point. -/
private theorem schemePointRepresentative_schemePoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) :
    AlgebraicGeometry.Space.schemePoint B S hS U
      (schemePointRepresentative_aux B S hS U x) = x := by
  let kobj : B.Schemes := B.obj (B.residueField_spec_contains U.left.property x)
  change (B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left)
    (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x))) _ = x
  rw [B.inclusion.map_preimage]
  exact Scheme.fromSpecResidueField_apply x _

/-- The residue-field representative at the underlying scheme point of a field-valued point
defines the same point of the presheaf. -/
private theorem canonical_class_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    (schemePointRepresentative_aux B S hS U
      (AlgebraicGeometry.Space.schemePoint B S hS U p)).class B S hS (yoneda.obj U) =
      p.class B S hS (yoneda.obj U) := by
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U
  let x := AlgebraicGeometry.Space.schemePoint B S hS U p
  let q := schemePointRepresentative_aux B S hS U x
  let hp := absoluteFieldValuedPoint (B := B) S hS U p
  let hq := absoluteFieldValuedPoint (B := B) S hS U q
  have hpx : hp.point = x := rfl
  have hcx : (AlgebraicGeometry.FieldValuedPoint.canonical X x).point = x :=
    Scheme.fromSpecResidueField_apply x _
  obtain ⟨φ, hφ, -⟩ :=
    (AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest x) hp (hpx.trans hcx.symm)
  have hqmap : hq.map = (AlgebraicGeometry.FieldValuedPoint.canonical X x).map := by
    let kobj : B.Schemes := B.obj (B.residueField_spec_contains U.left.property x)
    change B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left)
      (X.fromSpecResidueField x)) = X.fromSpecResidueField x
    rw [B.inclusion.map_preimage]
  let φ' : B.inclusion.obj (p.siteObject B S hS (yoneda.obj U)).left ⟶
      B.inclusion.obj (q.siteObject B S hS (yoneda.obj U)).left := by
    change Spec (.of p.carrier) ⟶ Spec (.of q.carrier)
    exact φ
  let fbase := B.inclusion.preimage φ'
  have hleft : fbase ≫ q.value.left = p.value.left := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    change φ ≫ hq.map = hp.map
    rw [hqmap]
    exact hφ
  have hbase : fbase ≫ (AlgebraicGeometry.Space.FieldValuedPoint.siteObject B S hS
      (yoneda.obj U) q).hom = (AlgebraicGeometry.Space.FieldValuedPoint.siteObject B S hS
      (yoneda.obj U) p).hom := by
    calc
      fbase ≫ (AlgebraicGeometry.Space.FieldValuedPoint.siteObject B S hS
          (yoneda.obj U) q).hom = fbase ≫ (q.value.left ≫ U.hom) := by
            rw [q.value.w]
            rfl
      _ = (fbase ≫ q.value.left) ≫ U.hom := by simp [Category.assoc]
      _ = p.value.left ≫ U.hom := by rw [hleft]
      _ = (AlgebraicGeometry.Space.FieldValuedPoint.siteObject B S hS
          (yoneda.obj U) p).hom := by
            rw [p.value.w]
            rfl
  let f : p.siteObject B S hS (yoneda.obj U) ⟶
      q.siteObject B S hS (yoneda.obj U) := Over.homMk fbase hbase
  have hdom : AlgebraicGeometry.Space.FieldValuedPoint.Dominates B S hS (yoneda.obj U) p q := by
    refine ⟨f, ?_⟩
    change f ≫ q.value = p.value
    exact Over.OverMorphism.ext hleft
  have hrel : AlgebraicGeometry.Space.FieldValuedPoint.HasCommonExtension B S hS
      (yoneda.obj U) p q :=
    ⟨p, AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) p, hdom⟩
  exact (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension
    B S hS (yoneda.obj U) hrel).symm

/-- The points of a represented presheaf on the big fppf site are the points of the
representing scheme. -/
private noncomputable def schemePointEquiv
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U ≃
      AlgebraicGeometry.Space.points B S hS (yoneda.obj U) := by
  classical
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U
  let pt := fun x => (schemePointRepresentative_aux B S hS U x).class B S hS (yoneda.obj U)
  let inv : AlgebraicGeometry.Space.points B S hS (yoneda.obj U) → X := fun q =>
    Quot.lift
      (fun p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U) =>
        (absoluteFieldValuedPoint (B := B) S hS U p).point)
      (by
        intro p q hpq
        obtain ⟨r, hpr, hqr⟩ := hpq
        obtain ⟨f, hf⟩ := hpr
        obtain ⟨g, hg⟩ := hqr
        have hf' : f ≫ p.value = r.value := hf
        have hg' : g ≫ q.value = r.value := hg
        have hdom (s : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U))
            (k : r.siteObject B S hS (yoneda.obj U) ⟶
              s.siteObject B S hS (yoneda.obj U)) (hk : k ≫ s.value = r.value) :
            (absoluteFieldValuedPoint (B := B) S hS U r).Dominates
              (absoluteFieldValuedPoint (B := B) S hS U s) := by
          refine ⟨B.inclusion.map k.left, ?_⟩
          exact congrArg (fun t => B.inclusion.map t.left) hk
        have hpq' : (absoluteFieldValuedPoint (B := B) S hS U p).HasCommonExtension
            (absoluteFieldValuedPoint (B := B) S hS U q) :=
          ⟨absoluteFieldValuedPoint (B := B) S hS U r, hdom p f hf', hdom q g hg'⟩
        exact (AlgebraicGeometry.FieldValuedPoint.hasCommonExtension_iff_point_eq _ _).mp hpq') q
  have hinv (x : X) : inv (pt x) = x := schemePointRepresentative_schemePoint B S hS U x
  refine Equiv.ofBijective pt ⟨?_, ?_⟩
  · intro x y h
    rw [← hinv x, ← hinv y, h]
  · intro q
    refine Quot.inductionOn q ?_
    intro p
    refine ⟨AlgebraicGeometry.Space.schemePoint B S hS U p, ?_⟩
    exact canonical_class_eq B S hS U p

/-- The bijection between the points of a scheme of the site and the points of the presheaf
it represents is a homeomorphism for the point topology. -/
private noncomputable def schemePointHomeomorph
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS (yoneda.obj U)) :=
      AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj U)
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U ≃ₜ
      AlgebraicGeometry.Space.points B S hS (yoneda.obj U) := by
  classical
  letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS (yoneda.obj U)) :=
    AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj U)
  let e := schemePointEquiv B S hS U
  let fam := AlgebraicGeometry.Space.pointTopologyFamily B S hS
  have hsymm (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U)) :
      e.symm (p.class B S hS (yoneda.obj U)) = AlgebraicGeometry.Space.schemePoint B S hS U p :=
    e.symm_apply_eq.mpr (canonical_class_eq B S hS U p).symm
  have hecont : Continuous e := by
    rw [continuous_def]
    intro W hW
    obtain ⟨V, hV, hmem⟩ := (fam.scheme U W).mp hW
    have hpre : e ⁻¹' W = V := by
      ext x
      change e x ∈ W ↔ x ∈ V
      have hx := hmem (schemePointRepresentative_aux B S hS U x)
      rw [schemePointRepresentative_schemePoint] at hx
      change (schemePointRepresentative_aux B S hS U x).class B S hS (yoneda.obj U) ∈ W ↔
        x ∈ V
      exact hx
    rw [hpre]
    exact hV
  have hesymm : Continuous e.symm := by
    rw [continuous_def]
    intro V hV
    apply (fam.scheme U (e.symm ⁻¹' V)).mpr
    refine ⟨V, hV, ?_⟩
    intro p
    change e.symm (p.class B S hS (yoneda.obj U)) ∈ V ↔
      AlgebraicGeometry.Space.schemePoint B S hS U p ∈ V
    rw [hsymm]
  exact ⟨e, hecont, hesymm⟩

/-- The homeomorphism identifying the points of a representable with the points of its
representing scheme is natural in the site object. -/
private theorem schemePointHomeomorph_naturality
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A D : AlgebraicGeometry.BigFppfOver B S hS} (j : A ⟶ D)
    (x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A) :
    schemePointHomeomorph B S hS D ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j x) =
      AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (yoneda.map j)
        (schemePointHomeomorph B S hS A x) := by
  have h := canonical_class_eq B S hS D
    (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj A) (yoneda.map j)
      (schemePointRepresentative_aux B S hS A x))
  rwa [schemePoint_fieldValuedPoint_map, schemePointRepresentative_schemePoint] at h

/-- A morphism of the site whose underlying morphism of schemes has dense image induces a
map with dense image on the points of the represented presheaves. -/
private theorem denseRange_pointsMap_of_denseRange
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A D : AlgebraicGeometry.BigFppfOver B S hS} (j : A ⟶ D)
    (hj : DenseRange ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)) :
    letI := AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj D)
    DenseRange (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (yoneda.map j)) := by
  let := AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj D)
  have hd := (schemePointHomeomorph B S hS D).surjective.denseRange.comp hj
    (schemePointHomeomorph B S hS D).continuous
  have he : (schemePointHomeomorph B S hS D) ∘
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j =
      (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (yoneda.map j)) ∘
        schemePointHomeomorph B S hS A :=
    funext (schemePointHomeomorph_naturality B S hS j)
  rw [he] at hd
  exact hd.of_comp

/-- An open immersion of algebraic spaces is an open embedding on points. -/
private theorem isOpenEmbedding_pointsMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (i : F ⟶ G) (hi : AlgebraicGeometry.Space.IsOpenImmersion B S hS i) :
    @Topology.IsOpenEmbedding _ _ (AlgebraicGeometry.Space.pointTopology B S hS F)
      (AlgebraicGeometry.Space.pointTopology B S hS G)
      (AlgebraicGeometry.Space.pointsMap B S hS F i) := by
  let : Mono i := mono_of_isOpenImmersion B S hS i hi
  let := AlgebraicGeometry.Space.pointTopology B S hS F
  let := AlgebraicGeometry.Space.pointTopology B S hS G
  exact .of_continuous_injective_isOpenMap
    ((AlgebraicGeometry.Space.pointTopologyFamily B S hS).continuous hF hG i)
    (AlgebraicGeometry.Space.pointsMap_injective_of_mono B S hS i)
    (AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isEtale B S hS i hF hG
      (isEtale_of_isOpenImmersion_aux hi))

/-- A quasi-separated scheme with finitely many irreducible components has a dense affine
open: an affine open containing the generic point of every irreducible component. -/
@[sga "3 VIA 3.2.1" "more general"]
private theorem exists_dense_affineOpen (X : Scheme.{u})
    [QuasiSeparatedSpace X] (hfinite : (irreducibleComponents X).Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ Dense (U : Set X) := by
  classical
  let : Finite (irreducibleComponents X) := hfinite.to_subtype
  let η : irreducibleComponents X → X := fun Z => Z.2.1.genericPoint
  have hη (Z : irreducibleComponents X) : IsGenericPoint (η Z) Z.1 :=
    Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  obtain ⟨U, hU, hηU⟩ := AlgebraicGeometry.exists_affine_open_containing_generic_points
    (fun Z : irreducibleComponents X => Z.1) (fun Z => Z.2) Subtype.val_injective η hη
  refine ⟨U, hU, ?_⟩
  intro x
  have hx : x ∈ irreducibleComponent x := mem_irreducibleComponent
  let Z : irreducibleComponents X := ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x⟩
  have hZ : Z.1 ⊆ closure (U : Set X) := by
    rw [← (hη Z).def]
    exact closure_mono (Set.singleton_subset_iff.mpr (hηU Z))
  exact hZ hx

/-- Density is inherited by the first projection of a pullback along an open immersion: if
the other leg has dense image, so does the projection to the open part. -/
private theorem denseRange_fst_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P A D X : AlgebraicGeometry.AlgebraicSpaces B S hS}
    {p : P ⟶ A} {q : P ⟶ D} {i : A ⟶ X} {j : D ⟶ X}
    (sq : IsPullback p q i j)
    (hi : AlgebraicGeometry.Space.IsOpenImmersion B S hS i.hom)
    (hj : letI := AlgebraicGeometry.Space.pointTopology B S hS X.1
      DenseRange (AlgebraicGeometry.Space.pointsMap B S hS D.1 j.hom)) :
    letI := AlgebraicGeometry.Space.pointTopology B S hS A.1
    DenseRange (AlgebraicGeometry.Space.pointsMap B S hS P.1 p.hom) := by
  let := AlgebraicGeometry.Space.pointTopology B S hS X.1
  let := AlgebraicGeometry.Space.pointTopology B S hS A.1
  have hpre := hj.preimage
    (isOpenEmbedding_pointsMap B S hS A.property X.property i.hom hi).isOpenMap
  have heq : (AlgebraicGeometry.Space.pointsMap B S hS A.1 i.hom) ⁻¹'
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS D.1 j.hom) =
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS P.1 p.hom) := by
    ext a
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨z, hz, -⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS sq a d hd.symm
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      refine ⟨AlgebraicGeometry.Space.pointsMap B S hS P.1 q.hom z, ?_⟩
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]
      exact congrArg (fun t => AlgebraicGeometry.Space.pointsMap B S hS P.1 t z)
        (congrArg (fun t => t.hom) sq.w.symm)
  rwa [heq] at hpre

/-- A Noetherian algebraic space has a dense open affine inside any of its open subspaces:
the schematic locus is dense by Stacks 06NH, and a Noetherian scheme has a dense affine
open. -/
theorem exists_dense_affine_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hN : AlgebraicGeometry.Space.IsNoetherian B S hS hZ X)
    (U : Subfunctor X) (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U) :
    ∃ (D : AlgebraicGeometry.BigFppfOver B S hS) (j : yoneda.obj D ⟶ U.toFunctor),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D) ∧
      AlgebraicGeometry.Space.IsOpenImmersion B S hS j ∧
      (letI := AlgebraicGeometry.Space.pointTopology B S hS U.toFunctor
       DenseRange (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj D) j)) := by
  classical
  let L := AlgebraicGeometry.Space.schematicLocus B S hS X
  have hLdata :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX
  have hL := hLdata.1
  let := hLdata.2
  let R := L.toFunctor.reprX
  let e : yoneda.obj R ≅ L.toFunctor := L.toFunctor.reprW
  let l : yoneda.obj R ⟶ X := e.hom ≫ L.ι
  let P := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  have hl : AlgebraicGeometry.Space.IsOpenImmersion B S hS l :=
    MorphismProperty.RespectsIso.precomp P e.hom L.ι hL.2
  have hLd := denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ X hX
    (isZariskiLocallyQuasiSeparatedOver_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ hX
      (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated
        B S hS X hZ hX hN.2.1))
  let := AlgebraicGeometry.Space.pointTopology B S hS X
  let := AlgebraicGeometry.Space.pointTopology B S hS L.toFunctor
  have hld : DenseRange (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj R) l) := by
    have hd := hLd.comp (pointsMap_surjective_of_isIso B S hS e.hom).denseRange
      ((AlgebraicGeometry.Space.pointTopologyFamily B S hS).continuous hL.1 hX L.ι)
    convert hd using 1
    funext x
    exact pointsMap_comp_apply _ _ _ e.hom L.ι x
  obtain ⟨Q, k, a, hsq⟩ := hU.2.rep l
  let QQ : AlgebraicGeometry.AlgebraicSpaces B S hS :=
    ⟨yoneda.obj Q, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Q⟩
  let RR : AlgebraicGeometry.AlgebraicSpaces B S hS :=
    ⟨yoneda.obj R, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R⟩
  let UU : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨U.toFunctor, hU.1⟩
  let XX : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨X, hX⟩
  have sq : IsPullback (ObjectProperty.homMk a : QQ ⟶ UU)
      (ObjectProperty.homMk (yoneda.map k) : QQ ⟶ RR)
      (ObjectProperty.homMk U.ι : UU ⟶ XX) (ObjectProperty.homMk l : RR ⟶ XX) := by
    apply IsPullback.of_map_of_faithful (F := ObjectProperty.ι
      (AlgebraicGeometry.IsAlgebraicSpace B S hS))
    exact hsq
  have ha : AlgebraicGeometry.Space.IsOpenImmersion B S hS a :=
    AlgebraicGeometry.Space.isOpenImmersion_of_isPullback B S hS sq.flip hl
  have had := denseRange_fst_of_isPullback B S hS sq hU.2 hld
  let := AlgebraicGeometry.Space.pointTopology B S hS U.toFunctor
  let := AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj Q)
  let : TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Space.points B S hS X) :=
    AlgebraicGeometry.Space.noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian
      B S hS X hX hN.1 hN.2.2
  have haX : AlgebraicGeometry.Space.IsOpenImmersion B S hS (a ≫ U.ι) :=
    AlgebraicGeometry.Space.isOpenImmersion_comp B S hS _ _ ha hU.2
  let : TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Space.points B S hS (yoneda.obj Q)) :=
    (isOpenEmbedding_pointsMap B S hS QQ.property hX (a ≫ U.ι)
      haX).isEmbedding.isInducing.noetherianSpace
  let Qs := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Q
  let : TopologicalSpace.NoetherianSpace Qs :=
    (schemePointHomeomorph B S hS Q).isEmbedding.isInducing.noetherianSpace
  let : QuasiSeparatedSpace Qs := ⟨fun _ _ _ _ _ _ =>
    TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨O, hO, hd⟩ := exists_dense_affineOpen Qs
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let Osite : B.Schemes := ⟨O.toScheme, (Scheme.size_coe_opens_le _ O).trans_lt Q.left.2⟩
  let jleft : Osite ⟶ Q.left := ObjectProperty.homMk O.ι
  let D : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (jleft ≫ Q.hom)
  let j : D ⟶ Q := Over.homMk jleft
  have hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS (yoneda.map j) :=
    isOpenImmersion_yoneda_map_aux B S hS j
      (by change AlgebraicGeometry.IsOpenImmersion O.ι; infer_instance)
  have hjdense : DenseRange
      (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj D) (yoneda.map j)) :=
    denseRange_pointsMap_of_denseRange B S hS j (by
      change Dense (Set.range O.ι)
      simpa only [Scheme.Opens.range_ι] using hd)
  refine ⟨D, yoneda.map j ≫ a, hO, ?_, ?_⟩
  · exact AlgebraicGeometry.Space.isOpenImmersion_comp B S hS _ _ hjOpen ha
  · have hd := had.comp hjdense
      ((AlgebraicGeometry.Space.pointTopologyFamily B S hS).continuous QQ.property hU.1 a)
    convert hd using 1
    funext x
    exact pointsMap_comp_apply _ _ _ (yoneda.map j) a x

/-- Every point of a coproduct in the big fppf site comes from one of the two summands. -/
theorem binary_coproduct_points_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A D E : AlgebraicGeometry.BigFppfOver B S hS} (i : A ⟶ E) (j : D ⟶ E)
    (e : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A ⨿
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D) ≅
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj E)
    (hi : coprod.inl ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i)
    (hj : coprod.inr ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)
    (x : AlgebraicGeometry.Space.points B S hS (yoneda.obj E)) :
    x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj A) (yoneda.map i)) ∨
    x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj D) (yoneda.map j)) := by
  let := AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj E)
  let := AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj A)
  let := AlgebraicGeometry.Space.pointTopology B S hS (yoneda.obj D)
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨x, rfl⟩ := (schemePointHomeomorph B S hS E).surjective x
  obtain ⟨x, rfl⟩ := e.hom.homeomorph.surjective x
  obtain ⟨x, rfl⟩ := (coprodMk (T.obj A) (T.obj D)).surjective x
  cases x with
  | inl a =>
    left
    refine ⟨schemePointHomeomorph B S hS A a, ?_⟩
    rw [← schemePointHomeomorph_naturality, ← hi]
    simp only [coprodMk_inl, Scheme.Hom.comp_apply]
    rfl
  | inr d =>
    right
    refine ⟨schemePointHomeomorph B S hS D d, ?_⟩
    rw [← schemePointHomeomorph_naturality, ← hj]
    simp only [coprodMk_inr, Scheme.Hom.comp_apply]
    rfl

end AlgebraicGeometry.Space

end
