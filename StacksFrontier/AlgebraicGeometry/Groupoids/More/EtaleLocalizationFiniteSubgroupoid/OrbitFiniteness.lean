module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.CardForm
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CommonField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.Decomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# Finiteness of orbits for étale localization of a groupoid

Preliminaries for `AlgebraicGeometry.GroupoidScheme.exists_finite_openClosed_subgroupoid`
(Stacks Project, Tag 03FL): finiteness of fibres over residue fields, shrinking and refining
elementary étale neighbourhoods so that finitely many finite morphisms stay finite, and the
finiteness and quasi-finiteness of the source, target and arrows over the orbit of a point
with finite source fibre, and the finiteness and ranges of morphisms out of finite
coproducts.

## Main definitions

No new public definitions are introduced.

## References

* [Stacks Project, Tag 03FL](https://stacks.math.columbia.edu/tag/03FL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The comparison morphism between two pullbacks, followed by the first projection, is the
first projection followed by the map of first factors. -/
@[reassoc]
lemma pullbackMap_fst {C : Type*} [Category C] {X Y Z X' Y' Z' : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [HasPullback f g] [HasPullback f' g'] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst f' g' =
      pullback.fst f g ≫ i₁ :=
  pullback.lift_fst _ _ _

/-- The comparison morphism between two pullbacks, followed by the second projection, is the
second projection followed by the map of second factors. -/
@[reassoc]
lemma pullbackMap_snd {C : Type*} [Category C] {X Y Z X' Y' Z' : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [HasPullback f g] [HasPullback f' g'] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd f' g' =
      pullback.snd f g ≫ i₂ :=
  pullback.lift_snd _ _ _

/-- The pasting isomorphism identifies the pullback of `h` along the first projection of
`pullback g w` with the pullback of `h ≫ g` along `w`, compatibly with the first projections. -/
private lemma pullbackPaste_inv_fst {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : X ⟶ Y) (hh : h ≫ g = f) (w : T ⟶ S) :
    (pullbackRightPullbackFstIso g w h ≪≫ pullback.congrHom hh rfl).inv ≫
        pullback.fst h (pullback.fst g w) = pullback.fst f w := by
  rw [Iso.trans_inv, Category.assoc, pullbackRightPullbackFstIso_inv_fst,
    pullback.congrHom_inv, pullbackMap_fst, Category.comp_id]

/-- The commuting square of a pullback square of schemes, read on points. -/
lemma isPullback_w_apply {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {c : X ⟶ Z} {d : Y ⟶ Z} (h : IsPullback a b c d) (z : P) : c (a z) = d (b z) := by
  rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]

private lemma finite_fiber_over_residue_field_of_finite_points
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hfin : (f ⁻¹' {y}).Finite) : IsFinite (f.fiberToSpecResidueField y) := by
  let := hfin.fintype
  let : Finite (f.fiber y) :=
    Finite.of_equiv (↥(f ⁻¹' {y})) (f.fiberHomeo y).symm.toEquiv
  let : JacobsonSpace (f.fiber y) := inferInstance
  let : DiscreteTopology (f.fiber y) :=
    JacobsonSpace.discreteTopology (Set.toFinite (closedPoints (f.fiber y)))
  let g := f.fiberToSpecResidueField y
  have : LocallyOfFiniteType g := by
    show LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  have : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
    intro z
    exact isDiscrete_iff_discreteTopology.mpr inferInstance
  have : QuasiCompact g := by
    constructor
    intro U hU hcompact
    exact (Set.toFinite (g ⁻¹' U)).isCompact
  exact IsFinite.of_locallyQuasiFinite g

private lemma finite_points_of_finite_map_to_spec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    (Set.univ : Set X).Finite := by
  classical
  by_cases hn : Nonempty X
  · let x := Classical.choice hn
    let z := f x
    have hf : (f ⁻¹' {z}).Finite := f.finite_preimage_singleton z
    have hz : f ⁻¹' {z} = Set.univ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim (f y) z
    simpa [hz] using hf
  · have hE : IsEmpty X := not_nonempty_iff.mp hn
    exact Set.finite_empty.subset (by simp)

private alias isFinite_respects_arrow_iso := Stacks.Morphisms.isFinite_respectsIso

private lemma finite_set_fiber_of_finite_residue_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (hf : IsFinite (f.fiberToSpecResidueField y)) : (f ⁻¹' {y}).Finite := by
  have : IsFinite (f.fiberToSpecResidueField y) := hf
  have hpts : (Set.univ : Set (f.fiber y)).Finite :=
    finite_points_of_finite_map_to_spec_field
      (K := Y.residueField y) (f.fiberToSpecResidueField y)
  let : Finite (f.fiber y) := Set.finite_univ_iff.mp hpts
  let : Finite (f ⁻¹' {y}) :=
    Finite.of_equiv (f.fiber y) (f.fiberHomeo y).toEquiv
  exact Set.toFinite (f ⁻¹' {y})

private lemma finite_pullback_snd_of_factorization
    {X Y Z T : Scheme.{u}} (f : Y ⟶ X) (q : Z ⟶ X) (k : T ⟶ Z)
    (hf : IsFinite (pullback.snd f q)) : IsFinite (pullback.snd f (k ≫ q)) := by
  let e := pullbackLeftPullbackSndIso f q k
  have : IsFinite (pullback.snd (pullback.snd f q) k) := by
    let : IsFinite (pullback.snd f q) := hf
    infer_instance
  let e' : Arrow.mk (pullback.snd f (k ≫ q)) ≅
      Arrow.mk (pullback.snd (pullback.snd f q) k) :=
    Arrow.isoMk e.symm (Iso.refl _) (by simp [e])
  let : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    isFinite_respects_arrow_iso
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e').mpr inferInstance

private lemma isIso_residueFieldMap_fromSpecResidueField
    {X : Scheme.{u}} (x : X) (z : Spec (X.residueField x)) :
    IsIso ((X.fromSpecResidueField x).residueFieldMap z) := by
  let f := X.fromSpecResidueField x
  have hf : IsPreimmersion f := inferInstance
  exact isIso_residueFieldMap_of_stalkMap_surjective f z (hf.stalkMap_surjective z)

private lemma isSeparated_coprod_desc
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated f] [IsSeparated g] :
    IsSeparated (coprod.desc f g) := by
  let d : S ⨿ S ⟶ S := coprod.desc (𝟙 S) (𝟙 S)
  have hmap : IsSeparated (coprod.map f g) :=
    IsZariskiLocalAtTarget.coprodMap f g inferInstance inferInstance
  have hd : IsSeparated d := by
    let : IsFinite d := inferInstance
    infer_instance
  have heq : coprod.desc f g = coprod.map f g ≫ d := by
    apply coprod.hom_ext <;> simp [d]
  rw [heq]
  infer_instance

private lemma isFinite_of_fpqc_base_change
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (q : Z ⟶ Y)
    [Flat q] [Surjective q] [QuasiCompact q]
    (hf : IsFinite (pullback.snd f q)) : IsFinite f := by
  let : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    isFinite_respects_arrow_iso
  let : MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (q.singleton_mem_fpqcPrecoverage)
  rintro _ _ _ ⟨⟩
  exact hf

lemma exists_open_neighborhood_preimage_le_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Y)
    (U : X.Opens) (hfiber : ∀ x, f x = y → x ∈ U) :
    ∃ V : Y.Opens, y ∈ V ∧ f ⁻¹ᵁ V ≤ U := by
  let B : Set Y := f '' (Uᶜ : Set X)
  have hB : IsClosed B := f.isClosedMap _ U.2.isClosed_compl
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, ?_, ?_⟩
  · show y ∉ B
    rintro ⟨x, hx, hxy⟩
    exact hx (hfiber x hxy)
  · intro x hx
    change f x ∉ B at hx
    show x ∈ U
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩

noncomputable def shrinkEtaleNeighborhood
    {S : Scheme.{u}} {p : S} (N : AlgebraicGeometry.EtaleNeighborhood S p)
    (V : N.scheme.Opens) (hp : N.point ∈ V) : AlgebraicGeometry.EtaleNeighborhood S p := by
  let : Etale V.ι := inferInstance
  let c : V.toScheme := ⟨N.point, hp⟩
  exact
    { scheme := V.toScheme
      point := c
      toBase := V.ι ≫ N.toBase
      map_point := N.map_point }

lemma shrinkEtaleNeighborhood_elementary
    {S : Scheme.{u}} {p : S} (N : AlgebraicGeometry.EtaleNeighborhood S p)
    (hN : N.IsElementary) (V : N.scheme.Opens) (hp : N.point ∈ V) :
    (shrinkEtaleNeighborhood N V hp).IsElementary := by
  let c : V.toScheme := ⟨N.point, hp⟩
  let : IsIso N.residueFieldMap := hN
  show IsIso ((S.residueFieldCongr (shrinkEtaleNeighborhood N V hp).map_point).inv ≫
    (V.ι ≫ N.toBase).residueFieldMap c)
  rw [Scheme.residueFieldMap_comp]
  show IsIso (N.residueFieldMap ≫ V.ι.residueFieldMap c)
  have hopen : IsIso (V.ι.residueFieldMap c) := by
    infer_instance
  exact IsIso.comp_isIso' hN hopen

private lemma exists_elementary_shrink_for_finite_map
    {S : Scheme.{u}} {p : S} (N : AlgebraicGeometry.EtaleNeighborhood S p)
    (hN : N.IsElementary) {X : Scheme.{u}} (f : X ⟶ N.scheme) [IsFinite f]
    (U : X.Opens) (hfiber : ∀ x, f x = N.point → x ∈ U) :
    ∃ (V : N.scheme.Opens) (hp : N.point ∈ V),
      f ⁻¹ᵁ V ≤ U ∧ (shrinkEtaleNeighborhood N V hp).IsElementary := by
  obtain ⟨V, hp, hpre⟩ := exists_open_neighborhood_preimage_le_of_isFinite f N.point U hfiber
  exact ⟨V, hp, hpre, shrinkEtaleNeighborhood_elementary N hN V hp⟩

private lemma exists_elementary_shrink_for_two_finite_maps
    {S : Scheme.{u}} {p : S} (N : AlgebraicGeometry.EtaleNeighborhood S p)
    (hN : N.IsElementary) {X Y : Scheme.{u}}
    (f : X ⟶ N.scheme) (g : Y ⟶ N.scheme) [IsFinite f] [IsFinite g]
    (U : X.Opens) (hfiber : ∀ x, f x = N.point → x ∈ U)
    (V : Y.Opens) (hgiber : ∀ y, g y = N.point → y ∈ V) :
    ∃ (W : N.scheme.Opens) (hp : N.point ∈ W),
      f ⁻¹ᵁ W ≤ U ∧ g ⁻¹ᵁ W ≤ V ∧
        (shrinkEtaleNeighborhood N W hp).IsElementary := by
  obtain ⟨W₁, hp₁, hf₁, _⟩ :=
    exists_elementary_shrink_for_finite_map N hN f U hfiber
  obtain ⟨W₂, hp₂, hg₂, _⟩ :=
    exists_elementary_shrink_for_finite_map N hN g V hgiber
  let W := W₁ ⊓ W₂
  have hp : N.point ∈ W := ⟨hp₁, hp₂⟩
  refine ⟨W, hp, ?_, ?_, shrinkEtaleNeighborhood_elementary N hN W hp⟩
  · intro x hx
    exact hf₁ hx.1
  · intro y hy
    exact hg₂ hy.2

private lemma exists_elementary_shrink_for_finite_family
    {S : Scheme.{u}} {p : S} (N : AlgebraicGeometry.EtaleNeighborhood S p)
    (hN : N.IsElementary) {ι : Type u} [Finite ι]
    (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ N.scheme)
    (hfinite : ∀ i, IsFinite (f i)) (U : ∀ i, (X i).Opens)
    (hfiber : ∀ i x, f i x = N.point → x ∈ U i) :
    ∃ (V : N.scheme.Opens) (hp : N.point ∈ V),
      (∀ i, (f i) ⁻¹ᵁ V ≤ U i) ∧
      (shrinkEtaleNeighborhood N V hp).IsElementary := by
  classical
  have hchoose : ∀ i, ∃ (V : N.scheme.Opens) (hp : N.point ∈ V),
      (f i) ⁻¹ᵁ V ≤ U i := by
    intro i
    let : IsFinite (f i) := hfinite i
    obtain ⟨V, hp, hV, _⟩ :=
      exists_elementary_shrink_for_finite_map N hN (f i) (U i) (hfiber i)
    exact ⟨V, hp, hV⟩
  choose V hp hpre using hchoose
  let W : N.scheme.Opens := ⨅ i, V i
  have hpoint : N.point ∈ W := by
    show N.point ∈ (((⨅ i, V i) : TopologicalSpace.Opens N.scheme) : Set N.scheme)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hp
  refine ⟨W, hpoint, ?_, shrinkEtaleNeighborhood_elementary N hN W hpoint⟩
  intro i x hx
  apply hpre i
  change f i x ∈ (((⨅ j, V j) : TopologicalSpace.Opens N.scheme) : Set N.scheme) at hx
  rw [TopologicalSpace.Opens.coe_iInf] at hx
  exact Set.mem_iInter.mp hx i

lemma pullback_fst_residueFieldMap_isIso_of_elementary
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary)
    (y : (pullback f U.toBase : Scheme).carrier)
    (hy : pullback.snd f U.toBase y = U.point) :
    IsIso ((pullback.fst f U.toBase).residueFieldMap y) := by
  have : IsIso (U.toBase.residueFieldMap U.point) := U.isElementary_iff.mp hU
  let z := (pullbackSymmetry f U.toBase).hom y
  have hz : pullback.fst U.toBase f z = U.point := by
    show pullback.fst U.toBase f ((pullbackSymmetry f U.toBase).hom y) = U.point
    rw [← Scheme.Hom.comp_apply, CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst]
    exact hy
  have hfx : IsIso (U.toBase.residueFieldMap (pullback.fst U.toBase f z)) := by
    rw [hz]
    infer_instance
  have hsecond := pullback_snd_residueFieldMap_isIso U.toBase f z hfx
  have hsymm : IsIso (((pullbackSymmetry f U.toBase).hom).residueFieldMap y) := by infer_instance
  let : IsIso ((pullbackSymmetry f U.toBase).hom.residueFieldMap y) := hsymm
  let : IsIso ((pullback.snd U.toBase f).residueFieldMap z) := hsecond
  have hcomp : IsIso (((pullbackSymmetry f U.toBase).hom ≫
      pullback.snd U.toBase f).residueFieldMap y) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' hsecond hsymm
  rw [pullbackSymmetry_hom_comp_snd] at hcomp
  exact hcomp

structure CommonEtaleNeighborhood
    {S : Scheme.{u}} {p : S} (N₁ N₂ : AlgebraicGeometry.EtaleNeighborhood S p)
    (hN₁ : N₁.IsElementary) (hN₂ : N₂.IsElementary) where
  neighborhood : AlgebraicGeometry.EtaleNeighborhood S p
  elementary : neighborhood.IsElementary
  toFirst : neighborhood.scheme ⟶ N₁.scheme
  toSecond : neighborhood.scheme ⟶ N₂.scheme
  toFirst_over : toFirst ≫ N₁.toBase = neighborhood.toBase
  toSecond_over : toSecond ≫ N₂.toBase = neighborhood.toBase
  toFirst_point : toFirst neighborhood.point = N₁.point
  toSecond_point : toSecond neighborhood.point = N₂.point

noncomputable def pullbackMapOfEtaleRefinement
    {S : Scheme.{u}} {p : S} {X : Scheme.{u}} (f : X ⟶ S)
    (N M : AlgebraicGeometry.EtaleNeighborhood S p) (q : N.scheme ⟶ M.scheme)
    (hq : q ≫ M.toBase = N.toBase) :
    pullback f N.toBase ⟶ pullback f M.toBase :=
  pullback.map f N.toBase f M.toBase (𝟙 X) q (𝟙 S) (by simp) hq.symm

/-- The refinement map over the first projection is the first projection. -/
lemma pullbackMapOfEtaleRefinement_fst
    {S : Scheme.{u}} {p : S} {X : Scheme.{u}} (f : X ⟶ S)
    (N M : AlgebraicGeometry.EtaleNeighborhood S p) (q : N.scheme ⟶ M.scheme)
    (hq : q ≫ M.toBase = N.toBase) :
    pullbackMapOfEtaleRefinement f N M q hq ≫ pullback.fst f M.toBase =
      pullback.fst f N.toBase := by
  simp only [pullbackMapOfEtaleRefinement, pullback.map, pullback.lift_fst,
    Category.comp_id]

noncomputable def commonEtaleNeighborhood
    {S : Scheme.{u}} {p : S} (N₁ N₂ : AlgebraicGeometry.EtaleNeighborhood S p)
    (hN₁ : N₁.IsElementary) (hN₂ : N₂.IsElementary) :
    CommonEtaleNeighborhood N₁ N₂ hN₁ hN₂ := by
  let P := pullback N₁.toBase N₂.toBase
  have hex : ∃ q : P,
      pullback.fst N₁.toBase N₂.toBase q = N₁.point ∧
      pullback.snd N₁.toBase N₂.toBase q = N₂.point :=
    Scheme.Pullback.exists_preimage_pullback (f := N₁.toBase) (g := N₂.toBase)
      N₁.point N₂.point (N₁.map_point.trans N₂.map_point.symm)
  let q : P := Classical.choose hex
  obtain ⟨hq₁, hq₂⟩ := Classical.choose_spec hex
  let : Etale (pullback.fst N₁.toBase N₂.toBase) := inferInstance
  let N : AlgebraicGeometry.EtaleNeighborhood S p :=
    { scheme := P
      point := q
      toBase := pullback.fst N₁.toBase N₂.toBase ≫ N₁.toBase
      map_point := by
        change (pullback.fst N₁.toBase N₂.toBase ≫ N₁.toBase) q = p
        rw [Scheme.Hom.comp_apply, hq₁]
        exact N₁.map_point }
  have hfst : IsIso ((pullback.fst N₁.toBase N₂.toBase).residueFieldMap q) :=
    pullback_fst_residueFieldMap_isIso_of_elementary N₁.toBase p N₂ hN₂ q hq₂
  have hElem : N.IsElementary := by
    have hbase : IsIso (N₁.toBase.residueFieldMap N₁.point) := by
      let : IsIso N₁.residueFieldMap := hN₁
      let : IsIso ((S.residueFieldCongr N₁.map_point).inv) := inferInstance
      change IsIso ((S.residueFieldCongr N₁.map_point).inv ≫
        N₁.toBase.residueFieldMap N₁.point) at hN₁
      exact IsIso.of_isIso_comp_left
        ((S.residueFieldCongr N₁.map_point).inv) (N₁.toBase.residueFieldMap N₁.point)
    have hbase' : IsIso (N₁.toBase.residueFieldMap
        (pullback.fst N₁.toBase N₂.toBase q)) := by
      have hcongr : IsIso
          ((N₁.scheme.residueFieldCongr hq₁).hom) :=
        (N₁.scheme.residueFieldCongr hq₁).isIso_hom
      have hcomp : IsIso (N₁.toBase.residueFieldMap
          (pullback.fst N₁.toBase N₂.toBase q) ≫
            (N₁.scheme.residueFieldCongr hq₁).hom) := by
        rw [N₁.toBase.residueFieldMap_congr' hq₁]
        let : IsIso ((N₁.scheme.residueFieldCongr hq₁).hom) := hcongr
        let : IsIso (N₁.toBase.residueFieldMap N₁.point) := hbase
        infer_instance
      let : IsIso (N₁.toBase.residueFieldMap
          (pullback.fst N₁.toBase N₂.toBase q) ≫
            (N₁.scheme.residueFieldCongr hq₁).hom) := hcomp
      let : IsIso ((N₁.scheme.residueFieldCongr hq₁).hom) := hcongr
      exact IsIso.of_isIso_comp_right
        (N₁.toBase.residueFieldMap (pullback.fst N₁.toBase N₂.toBase q))
        ((N₁.scheme.residueFieldCongr hq₁).hom)
    have hmap : IsIso ((pullback.fst N₁.toBase N₂.toBase ≫ N₁.toBase).residueFieldMap q) := by
      rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' hbase' hfst
    change IsIso ((S.residueFieldCongr N.map_point).inv ≫
      (pullback.fst N₁.toBase N₂.toBase ≫ N₁.toBase).residueFieldMap q)
    have hcongr : IsIso ((S.residueFieldCongr N.map_point).inv) := by infer_instance
    exact IsIso.comp_isIso' hcongr hmap
  exact
    { neighborhood := N
      elementary := hElem
      toFirst := pullback.fst N₁.toBase N₂.toBase
      toSecond := pullback.snd N₁.toBase N₂.toBase
      toFirst_over := rfl
      toSecond_over := pullback.condition.symm
      toFirst_point := hq₁
      toSecond_point := hq₂ }

/-- The source map sends the identity section at a point back to that point. -/
private lemma source_left_identity_left_apply {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (v : G.objects.left) :
    G.source.left (G.identity.left v) = v := by
  rw [← Scheme.Hom.comp_apply, Stacks.Groupoids.identity_left_comp_source_left]
  rfl

/-- The target map sends the identity section at a point back to that point. -/
private lemma target_left_identity_left_apply {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (v : G.objects.left) :
    G.target.left (G.identity.left v) = v := by
  rw [← Scheme.Hom.comp_apply, Stacks.Groupoids.identity_left_comp_target_left]
  rfl

private lemma finite_residue_fiber_over_target_of_arrow
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    (hfinite : (G.source.left ⁻¹' {u}).Finite) (r : G.arrows.left)
    (v : G.objects.left) (hrs : G.source.left r = u) (hrt : G.target.left r = v)
    [LocallyOfFinitePresentation G.source.left] :
    IsFinite (G.source.left.fiberToSpecResidueField v) := by
  let : LocallyOfFiniteType G.source.left := inferInstance
  have hu : IsFinite (G.source.left.fiberToSpecResidueField u) :=
    finite_fiber_over_residue_field_of_finite_points G.source.left u hfinite
  have hsid := source_left_identity_left_apply G v
  have htargets : G.target.left r = G.target.left (G.identity.left v) :=
    hrt.trans (target_left_identity_left_apply G v).symm
  obtain ⟨K, hK, hU, hV, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_common_field_fiber_iso G r (G.identity.left v) htargets
  let : Field K := hK
  let a := G.source.left r
  let b := G.source.left (G.identity.left v)
  let : Algebra (G.objects.left.residueField a) K := hU
  let : Algebra (G.objects.left.residueField b) K := hV
  let qU := Spec.map (CommRingCat.ofHom
    (algebraMap (G.objects.left.residueField a) K))
  let qV := Spec.map (CommRingCat.ofHom
    (algebraMap (G.objects.left.residueField b) K))
  have hua : IsFinite (G.source.left.fiberToSpecResidueField a) := by
    show IsFinite (G.source.left.fiberToSpecResidueField (G.source.left r))
    rw [hrs]
    exact hu
  have hUext : IsFinite (pullback.snd
      (G.source.left.fiberToSpecResidueField a) qU) := by
    let : IsFinite (G.source.left.fiberToSpecResidueField a) := hua
    infer_instance
  let eDom := (Over.forget (Spec (CommRingCat.of K))).mapIso e
  let e' : Arrow.mk (pullback.snd (G.source.left.fiberToSpecResidueField a) qU) ≅
      Arrow.mk (pullback.snd (G.source.left.fiberToSpecResidueField b) qV) :=
    Arrow.isoMk eDom (Iso.refl _) e.hom.w
  let : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    isFinite_respects_arrow_iso
  have hVext : IsFinite (pullback.snd
      (G.source.left.fiberToSpecResidueField b) qV) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e').mp hUext
  have : Flat qV := inferInstance
  have : Surjective qV := inferInstance
  have : QuasiCompact qV := inferInstance
  have hb : IsFinite (G.source.left.fiberToSpecResidueField b) :=
    isFinite_of_fpqc_base_change (G.source.left.fiberToSpecResidueField b) qV hVext
  show IsFinite (G.source.left.fiberToSpecResidueField v)
  rw [← hsid]
  exact hb

private lemma source_point_fiber_finite_of_arrow
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    (hfinite : (G.source.left ⁻¹' {u}).Finite) (r : G.arrows.left)
    (v : G.objects.left) (hrs : G.source.left r = u) (hrt : G.target.left r = v)
    [LocallyOfFinitePresentation G.source.left] :
    (G.source.left ⁻¹' {v}).Finite :=
  finite_set_fiber_of_finite_residue_map _ _
    (finite_residue_fiber_over_target_of_arrow G u hfinite r v hrs hrt)

lemma source_over_orbit_finite
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    (hfinite : (G.source.left ⁻¹' {u}).Finite)
    [LocallyOfFinitePresentation G.source.left] :
    (G.source.left ⁻¹' (G.target.left '' (G.source.left ⁻¹' {u}))).Finite :=
  (hfinite.image G.target.left).preimage' fun v ⟨r, hrs, hrt⟩ =>
    source_point_fiber_finite_of_arrow G u hfinite r v hrs hrt

lemma source_target_orbit_finite
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    (hfinite : (G.source.left ⁻¹' {u}).Finite) :
    (G.target.left '' (G.source.left ⁻¹' {u})).Finite :=
  hfinite.image G.target.left

noncomputable def finitePointList {α : Type u} (s : Set α) [Fintype s] :
    Fin (Fintype.card s) → α := fun i => ((Fintype.equivFin s).symm i).1

lemma finitePointList_injective {α : Type u} (s : Set α) [Fintype s] :
    Function.Injective (finitePointList s) :=
  fun _ _ hij => (Fintype.equivFin s).symm.injective (Subtype.ext hij)

lemma finitePointList_mem {α : Type u} (s : Set α) [Fintype s]
    (i : Fin (Fintype.card s)) : finitePointList s i ∈ s :=
  ((Fintype.equivFin s).symm i).2

/-- A morphism in `Over S` commutes with the structure maps, on points. -/
private lemma hom_apply_left {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (x : X.left) :
    Y.hom (f.left x) = X.hom x := by
  rw [← Scheme.Hom.comp_apply, Over.w]

lemma object_point_over_orbit
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (p : S) (u : G.objects.left)
    (hu : G.objects.hom u = p)
    {v : G.objects.left} (hv : v ∈ G.target.left '' (G.source.left ⁻¹' {u})) :
    G.objects.hom v = p := by
  rcases hv with ⟨r, hrs, hrt⟩
  rw [← hu, ← hrt, ← hrs, hom_apply_left G.target, hom_apply_left G.source]

lemma object_lies_in_source_target_orbit
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left) :
    u ∈ G.target.left '' (G.source.left ⁻¹' {u}) := by
  exact ⟨G.identity.left u, source_left_identity_left_apply G u,
    target_left_identity_left_apply G u⟩

lemma card_quasiFiniteAt_of_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hqf : f.QuasiFiniteAt x) : AlgebraicGeometry.quasiFiniteAt f x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hyU (f ⁻¹ᵁ U).2
  let U' : Y.affineOpens := ⟨U, hU⟩
  let V' : X.affineOpens := ⟨V, hV⟩
  refine (AlgebraicGeometry.quasiFiniteAt_iff_exists_affineOpens f x).2
    ⟨U', V', hxV, hVU, f.finiteType_appLE U'.2 V'.2 hVU, ?_⟩
  exact hqf.quasiFiniteAt V'.2 U'.2 hVU hxV

private lemma quasiFiniteAt_of_finite_set_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (hfin : (f ⁻¹' {y}).Finite) (x : X) (hxy : f x = y) :
    AlgebraicGeometry.quasiFiniteAt f x := by
  classical
  have hfin' : (f ⁻¹' {f x}).Finite := by simpa [hxy] using hfin
  let := hfin'.fintype
  let : Finite (f.fiber (f x)) :=
    Finite.of_equiv (↥(f ⁻¹' {f x})) (f.fiberHomeo (f x)).symm.toEquiv
  let : JacobsonSpace (f.fiber (f x)) := inferInstance
  let : DiscreteTopology (f.fiber (f x)) :=
    JacobsonSpace.discreteTopology (Set.toFinite (closedPoints (f.fiber (f x))))
  have hqf : f.QuasiFiniteAt x :=
    (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber).2 (isOpen_discrete _)
  exact card_quasiFiniteAt_of_quasiFiniteAt f x hqf

/-- The structure map of the arrows of a groupoid scheme is locally of finite type when the
source map and the structure map of the objects are. -/
private lemma locallyOfFiniteType_arrows_hom {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.objects.hom] :
    LocallyOfFiniteType G.arrows.hom := by
  rw [← G.source.w]
  infer_instance

private lemma arrow_quasiFiniteAt_of_source_and_object
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (r : G.arrows.left)
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.objects.hom]
    (hs : AlgebraicGeometry.quasiFiniteAt G.source.left r)
    (ht : AlgebraicGeometry.quasiFiniteAt G.objects.hom (G.source.left r)) :
    AlgebraicGeometry.quasiFiniteAt G.arrows.hom r := by
  have := locallyOfFiniteType_arrows_hom G
  have hqf : G.arrows.hom.QuasiFiniteAt r := by
    show (G.arrows.hom.stalkMap r).hom.QuasiFinite
    rw [← G.source.w, Scheme.Hom.stalkMap_comp]
    exact RingHom.QuasiFinite.comp hs.2 ht.2
  exact card_quasiFiniteAt_of_quasiFiniteAt G.arrows.hom r hqf

private lemma arrow_isolated_in_special_fiber
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [LocallyOfFiniteType G.arrows.hom] (r : G.arrows.left)
    (hqf : AlgebraicGeometry.quasiFiniteAt G.arrows.hom r) :
    IsOpen {G.arrows.hom.asFiber r} :=
  ((AlgebraicGeometry.quasiFiniteAt_tfae G.arrows.hom r).out 1 2).mp hqf

private lemma quasiFiniteAt_target_of_quasiFiniteAt_source
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : X ⟶ Y)
    (hh : h ≫ g = f) [Flat h] [LocallyOfFinitePresentation h]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (hqf : AlgebraicGeometry.quasiFiniteAt f x) :
    AlgebraicGeometry.quasiFiniteAt g (h x) := by
  have hqf' : f.QuasiFiniteAt x := hqf.2
  have hopen : IsOpen {f.asFiber x} :=
    ((AlgebraicGeometry.quasiFiniteAt_tfae f x).out 1 2).mp hqf
  have hxy : g (h x) = f x := by
    calc
      g (h x) = (h ≫ g) x := by rw [Scheme.Hom.comp_apply]
      _ = f x := congrArg (fun q : X ⟶ S => q x) hh
  let e : pullback h (g.fiberι (f x)) ≅ f.fiber (f x) :=
    pullbackRightPullbackFstIso g (S.fromSpecResidueField (f x)) h ≪≫
      pullback.congrHom hh rfl
  let m : f.fiber (f x) ⟶ g.fiber (f x) :=
    e.inv ≫ pullback.snd h (g.fiberι (f x))
  have : UniversallyOpen h := UniversallyOpen.of_flat h
  have : UniversallyOpen (pullback.snd h
      (g.fiberι (f x))) := by
    infer_instance
  have : UniversallyOpen m := by
    show UniversallyOpen (e.inv ≫
      pullback.snd h (g.fiberι (f x)))
    infer_instance
  have himage : IsOpen (m '' ({f.asFiber x} : Set (f.fiber (f x)))) :=
    (show IsOpenMap m from Scheme.Hom.isOpenMap m) _ hopen
  have hmap_point :
      m (f.asFiber x) = (g.fiberHomeo (f x)).symm ⟨h x, by simpa using hxy⟩ := by
    apply (g.fiberHomeo (f x)).injective
    apply Subtype.ext
    rw [Scheme.Hom.fiberHomeo_apply, Homeomorph.apply_symm_apply]
    have he : e.inv ≫ pullback.fst h (g.fiberι (f x)) = f.fiberι (f x) :=
      pullbackPaste_inv_fst f g h hh (S.fromSpecResidueField (f x))
    have hm : m ≫ g.fiberι (f x) = f.fiberι (f x) ≫ h := by
      calc
        m ≫ g.fiberι (f x) = e.inv ≫
            (pullback.snd h (g.fiberι (f x)) ≫ g.fiberι (f x)) := by
              dsimp [m]
              rw [Category.assoc]
        _ = e.inv ≫ (pullback.fst h (g.fiberι (f x)) ≫ h) := by
              rw [← pullback.condition]
        _ = (e.inv ≫ pullback.fst h (g.fiberι (f x))) ≫ h := by
              rw [Category.assoc]
        _ = f.fiberι (f x) ≫ h := by rw [he]
    rw [← Scheme.Hom.comp_apply, hm]
    simp [Scheme.Hom.asFiber, Scheme.Hom.fiberι_fiberHomeo_symm]
  have hs : m '' ({f.asFiber x} : Set (f.fiber (f x))) =
      ({(g.fiberHomeo (f x)).symm ⟨h x, by simpa using hxy⟩} : Set (g.fiber (f x))) := by
    rw [Set.image_singleton, hmap_point]
  rw [hs] at himage
  have hpre : IsOpen ({⟨h x, hxy⟩} : Set (g ⁻¹' {f x})) := by
    have h := (g.fiberHomeo (f x)).isOpen_image.mpr himage
    simpa [Set.image_singleton] using h
  have hpreEq : g ⁻¹' {f x} = g ⁻¹' {g (h x)} := by
    ext z
    simp [hxy]
  have hpre' : IsOpen ({⟨h x, rfl⟩} : Set (g ⁻¹' {g (h x)})) := by
    let eSet := Homeomorph.setCongr hpreEq
    have heSet : eSet ⟨h x, by simpa using hxy⟩ = ⟨h x, rfl⟩ := by
      apply Subtype.ext
      rfl
    have himageSet : eSet '' {⟨h x, by simpa using hxy⟩} =
        ({⟨h x, rfl⟩} : Set (g ⁻¹' {g (h x)})) := by
      rw [Set.image_singleton, heSet]
    have hOpenImage := eSet.isOpenMap _ hpre
    rw [himageSet] at hOpenImage
    exact hOpenImage
  have hopen' : IsOpen {g.asFiber (h x)} := by
    have hset :
        (g.fiberHomeo (g (h x))) '' {g.asFiber (h x)} =
          ({⟨h x, rfl⟩} : Set (g ⁻¹' {g (h x)})) := by
      ext z
      simp [Scheme.Hom.asFiber]
    have h := (g.fiberHomeo (g (h x))).isOpen_image.mp (hset ▸ hpre')
    exact h
  have hqfg : g.QuasiFiniteAt (h x) :=
    (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber).2 hopen'
  exact card_quasiFiniteAt_of_quasiFiniteAt g (h x) hqfg

private lemma arrows_over_finite_source_fiber_are_isolated
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    [LocallyOfFiniteType G.objects.hom] [LocallyOfFiniteType G.source.left]
    [LocallyOfFiniteType G.arrows.hom]
    (hqu : AlgebraicGeometry.quasiFiniteAt G.objects.hom u)
    (hfinite : (G.source.left ⁻¹' {u}).Finite)
    (r : G.arrows.left) (hrs : G.source.left r = u) :
    IsOpen {G.arrows.hom.asFiber r} := by
  have hs := quasiFiniteAt_of_finite_set_fiber G.source.left u hfinite r hrs
  have hr := arrow_quasiFiniteAt_of_source_and_object G r hs (by simpa [hrs] using hqu)
  exact arrow_isolated_in_special_fiber G r hr

lemma quasiFiniteAt_on_source_target_orbit
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    [LocallyOfFiniteType G.objects.hom]
    [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    (hqu : AlgebraicGeometry.quasiFiniteAt G.objects.hom u)
    (hfinite : (G.source.left ⁻¹' {u}).Finite) :
    ∀ v ∈ G.target.left '' (G.source.left ⁻¹' {u}),
      AlgebraicGeometry.quasiFiniteAt G.objects.hom v := by
  intro v hv
  rcases hv with ⟨r, hrs, hrt⟩
  have := locallyOfFiniteType_arrows_hom G
  have hs := quasiFiniteAt_of_finite_set_fiber G.source.left u hfinite r hrs
  have htSource : AlgebraicGeometry.quasiFiniteAt G.objects.hom (G.source.left r) := by
    rwa [hrs]
  have harrow := arrow_quasiFiniteAt_of_source_and_object G r hs htSource
  have ht := quasiFiniteAt_target_of_quasiFiniteAt_source
    G.arrows.hom G.objects.hom G.target.left G.target.w r harrow
  simpa [hrt] using ht

lemma arrows_over_orbit_are_isolated
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    [LocallyOfFiniteType G.objects.hom]
    [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    (hqu : AlgebraicGeometry.quasiFiniteAt G.objects.hom u)
    (hfinite : (G.source.left ⁻¹' {u}).Finite) :
    ∀ r ∈ G.source.left ⁻¹' (G.target.left '' (G.source.left ⁻¹' {u})),
      IsOpen {G.arrows.hom.asFiber r} := by
  intro r hr
  change G.source.left r ∈ G.target.left '' (G.source.left ⁻¹' {u}) at hr
  rcases hr with ⟨q, hquSrc, hqv⟩
  let v := G.source.left r
  have hvOrbit : v ∈ G.target.left '' (G.source.left ⁻¹' {u}) := ⟨q, hquSrc, hqv⟩
  have hvqf := quasiFiniteAt_on_source_target_orbit G u hqu hfinite v hvOrbit
  have hvfin := source_point_fiber_finite_of_arrow G u hfinite q v hquSrc hqv
  have := locallyOfFiniteType_arrows_hom G
  exact arrows_over_finite_source_fiber_are_isolated G v hvqf hvfin r rfl

lemma arrow_point_over_source_target_orbit
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) (p : S) (u : G.objects.left)
    (hu : G.objects.hom u = p) {r : G.arrows.left}
    (hr : G.source.left r ∈ G.target.left '' (G.source.left ⁻¹' {u})) :
    G.arrows.hom r = p := by
  rw [← hom_apply_left G.source]
  exact object_point_over_orbit G p u hu hr

/-- A morphism out of a coproduct of a finite family of schemes is finite when each of its
restrictions to a component is. -/
lemma finite_sigma_desc {Y : Scheme.{u}} (n : ℕ)
    (X : Fin n → Scheme.{u}) (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsFinite (f i)) :
    IsFinite (Sigma.desc f) :=
  @isFinite_sigmaDesc (Fin n) _ Y X f hf

/-- The range of a morphism out of a coproduct of a finite family is the union of the ranges
of its restrictions to the components. -/
lemma range_sigma_desc {ι : Type*} [Finite ι]
    {X : ι → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y) :
    Set.range (Sigma.desc f) = ⋃ i, Set.range (f i) :=
  Stacks.AffineClosedUnion.range_sigmaDesc f

lemma disjoint_ranges_of_sigma_desc_iso {ι : Type*} [Small.{u} ι]
    {X : ι → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    [IsIso (Sigma.desc f)] {i j : ι} (hij : i ≠ j) :
    Disjoint (Set.range (f i)) (Set.range (f j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have he : Sigma.ι X i x = Sigma.ι X j y := by
    apply (Sigma.desc f).isOpenEmbedding.injective
    simpa [← Scheme.Hom.comp_apply] using hy.symm
  have hh := (sigmaι_eq_iff X i j x y).mp he
  exact hij (congrArg Sigma.fst hh)

lemma isIso_coprod_desc_sigma_option {ι : Type*} [Small.{u} ι] [Small.{u} (Option ι)]
    {X : Option ι → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    [IsIso (Sigma.desc f)] :
    IsIso (coprod.desc (Sigma.desc fun i => f (some i)) (f none)) := by
  let X' := fun i => X (some i)
  let a : ∐ X' ⨿ X none ⟶ ∐ X := coprod.desc
    (Sigma.desc fun i => Sigma.ι X (some i)) (Sigma.ι X none)
  let b : ∐ X ⟶ ∐ X' ⨿ X none := Sigma.desc
    (fun i => Option.casesOn i coprod.inr (fun i => Sigma.ι X' i ≫ coprod.inl))
  have hab : a ≫ b = 𝟙 _ := by
    apply coprod.hom_ext
    · apply Sigma.hom_ext
      intro i
      simp only [a, b, coprod.desc_comp, coprod.inl_desc, Sigma.ι_desc,
        Sigma.ι_desc_assoc, Category.comp_id]
    · simp only [a, b, coprod.desc_comp, coprod.inr_desc, Sigma.ι_desc, Category.comp_id]
  have hba : b ≫ a = 𝟙 _ := by
    apply Sigma.hom_ext
    intro i
    cases i with
    | none => simp only [a, b, Sigma.ι_desc_assoc, Category.comp_id, coprod.inr_desc]
    | some j => simp only [a, b, Sigma.ι_desc_assoc, Category.assoc, coprod.inl_desc,
        Sigma.ι_desc, Category.comp_id]
  have : IsIso a := ⟨⟨b, hab, hba⟩⟩
  have he : coprod.desc (Sigma.desc fun i => f (some i)) (f none) =
      a ≫ Sigma.desc f := by
    apply coprod.hom_ext
    · apply Sigma.hom_ext
      intro i
      simp only [a, coprod.inl_desc,
        coprod.inl_desc_assoc, Sigma.ι_desc, Sigma.ι_desc_assoc]
    · simp only [a, coprod.inr_desc,
        coprod.inr_desc_assoc, Sigma.ι_desc]
  rw [he]
  infer_instance

end AlgebraicGeometry.GroupoidScheme
