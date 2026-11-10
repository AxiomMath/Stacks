module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.PurelyInseparableDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.FppfSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Étale decompositions and purely inseparable fibres

Auxiliary results for the étale chart of the finite part (Stacks 04QG), assembled in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover`: finite sets of the
fibre containing a finite open, the étale localization of a separated locally quasi-finite
morphism of schemes (Stacks 04HJ) in the form used for the chart, and the fact that over a
point whose fibre is a single purely inseparable point every open finite over the base is a
union of the pieces of such a decomposition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePartChart

attribute [local instance] Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  Stacks.Morphisms.isFinite_respectsIso

attribute [local instance] schemeSizeBelow_isClosedUnderIsomorphisms
  schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan
  BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- The two composites of `g` through the pullback square agree after mapping to the base. -/
private theorem comp_snd_comp_eq_comp_fst_comp {X Y S T : Scheme.{u}} (f : X ⟶ Y) (b : T ⟶ Y)
    (g : S ⟶ pullback b f) : (g ≫ pullback.snd b f) ≫ f = (g ≫ pullback.fst b f) ≫ b := by
  rw [Category.assoc, Category.assoc, pullback.condition]

private theorem exists_finset_fiber_containing_image
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    {A : Type u} [Finite A] (g : A → X) (hg : ∀ a, f (g a) = y) :
    ∃ s : Finset (f.fiber y), ∀ a, ∃ x ∈ s, g a = f.fiberι y x := by
  classical
  let := Fintype.ofFinite A
  let l : A → f.fiber y := fun a ↦ (f.fiberHomeo y).symm ⟨g a, hg a⟩
  refine ⟨Finset.univ.image l, fun a ↦ ⟨l a, Finset.mem_image.mpr ⟨a, by simp, rfl⟩, ?_⟩⟩
  exact (congrArg Subtype.val ((f.fiberHomeo y).apply_symm_apply ⟨g a, hg a⟩)).symm

theorem exists_finset_fiber_containing_finite_open
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (b : T ⟶ Y) [Subsingleton T]
    (t : T) (Z : (pullback b f).Opens)
    (hfinite : IsFinite (Z.ι ≫ pullback.fst b f)) :
    ∃ s : Finset (f.fiber (b t)), ∀ z : Z, ∃ x ∈ s,
      (Z.ι ≫ pullback.snd b f) z = f.fiberι (b t) x := by
  let g := Z.ι ≫ pullback.fst b f
  have : IsFinite g := hfinite
  have hZ : Finite Z.toScheme := by
    have h : Set.Finite (g ⁻¹' {t}) := g.finite_preimage_singleton t
    have heq : g ⁻¹' {t} = Set.univ := by
      ext z
      simp [Subsingleton.elim (g z) t]
    rw [heq] at h
    exact Set.finite_univ_iff.mp h
  have hg (z : Z) : f ((Z.ι ≫ pullback.snd b f) z) = b t :=
    (congrArg (fun h : Z.toScheme ⟶ Y ↦ h z) (comp_snd_comp_eq_comp_fst_comp f b Z.ι)).trans
      (congrArg b (Subsingleton.elim _ _))
  exact exists_finset_fiber_containing_image (A := Z.toScheme) f (b t)
    (fun z : Z ↦ (Z.ι ≫ pullback.snd b f) z) hg

theorem exists_etale_decomposition_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsSeparated f] [LocallyQuasiFinite f] (y : Y) (s : Finset (f.fiber y)) :
    ∃ (U : EtaleNeighborhood Y y) (I : Type u) (_ : Finite I)
      (W : (pullback f U.toBase).Opens) (D : I → (pullback f U.toBase).Opens),
      Pairwise (fun i j ↦ Disjoint (D i) (D j)) ∧
      ((W : Set (pullback f U.toBase : Scheme.{u})) ∪
        ⋃ i, (D i : Set (pullback f U.toBase : Scheme.{u}))) = Set.univ ∧
      (∀ i, ∃ v : D i, IsFinite ((D i).ι ≫ pullback.snd f U.toBase) ∧
        ((D i).ι ≫ pullback.snd f U.toBase) ⁻¹' {U.point} = {v} ∧
        ∃ hv : ((D i).ι ≫ pullback.snd f U.toBase) v = U.point,
          ((U.scheme.residueFieldCongr hv).inv ≫
            ((D i).ι ≫ pullback.snd f U.toBase).residueFieldMap v).hom.IsPurelyInseparable) ∧
      (∀ w : W, (W.ι ≫ pullback.snd f U.toBase) w = U.point →
        ∀ x ∈ s, (W.ι ≫ pullback.fst f U.toBase) w ≠ f.fiberι y x) := by
  classical
  let e := (Fintype.equivFin s).symm
  let x : Fin (Fintype.card s) → f.fiber y := fun i ↦ (e i).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.injective
  have hloc : IsLocallyArtinian (f.fiber y) := inferInstance
  have hxi : ∀ i, IsIsolatedPoint (x i) := fun _ ↦ isOpen_discrete _
  obtain ⟨U, m, D, v, hdisj, hcover, _, hfin, hW⟩ :=
    AlgebraicGeometry.exists_etaleNeighborhood_purelyInseparable_decomposition
      f (Fintype.card s) y x hx hxi
  let I := ULift.{u} (Σ i, Fin (m i))
  refine ⟨U, I, inferInstance, D none, (fun i ↦ D (some i.down)), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hne : some i.down ≠ some j.down := fun h ↦ hij (ULift.ext (Option.some.inj h))
    exact (TopologicalSpace.Opens.coe_disjoint).mp
      (hdisj (Set.mem_univ _) (Set.mem_univ _) hne)
  · refine Set.eq_univ_of_forall fun p ↦ ?_
    have hp : p ∈ ⋃ k, (D k).1 := by rw [hcover]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    cases k with
    | none => exact Or.inl hk
    | some ij => exact Or.inr (Set.mem_iUnion.mpr ⟨⟨ij⟩, hk⟩)
  · intro i
    obtain ⟨hi, hv, _, hfield⟩ := hfin i.down.1 i.down.2
    exact ⟨v i.down.1 i.down.2, hi, hv, hfield⟩
  · intro w hw x' hx'
    obtain ⟨i, hi⟩ := e.surjective ⟨x', hx'⟩
    have hix : x i = x' := congrArg Subtype.val hi
    simpa [hix] using hW w hw i

private theorem exists_subset_eq_union_of_subsingleton
    {A I : Type*} (D : I → Set A) (hD : ∀ i, (D i).Subsingleton)
    (Z : Set A) (hZ : Z ⊆ ⋃ i, D i) :
    ∃ J : Set I, Z = ⋃ i ∈ J, D i := by
  refine ⟨{i | (Z ∩ D i).Nonempty}, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hZ hx)
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨⟨x, hx, hi⟩, hi⟩⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨⟨y, hy, hyD⟩, hxD⟩ := Set.mem_iUnion.mp hi
    exact (hD i hxD hyD) ▸ hy

private theorem spec_hom_ext_of_purelyInseparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : (f.residueFieldMap x).hom.IsPurelyInseparable)
    {K : Type u} [Field K] (g₁ g₂ : Spec (.of K) ⟶ X)
    (h₁ : g₁ (IsLocalRing.closedPoint K) = x)
    (h₂ : g₂ (IsLocalRing.closedPoint K) = x)
    (hg : g₁ ≫ f = g₂ ≫ f) : g₁ = g₂ := by
  obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    congr((Y.SpecToEquivOfField K) $(hg))
  apply (X.SpecToEquivOfField K).injective
  dsimp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_mk] at e h
  have he : g₁ (IsLocalRing.closedPoint K) = g₂ (IsLocalRing.closedPoint K) :=
    h₁.trans h₂.symm
  -- The two sides of `h` are cut down to maps out of `κ(f (g₁ u))` and the comparison of the
  -- residue fields of `g₁ u` and `g₂ u` is moved across `f`, so that the common factor
  -- `f.residueFieldMap (g₁ u)` can be cancelled. Every step is a term, because the point
  -- `IsLocalRing.closedPoint K` of `Spec K` is only a point of the scheme after unfolding
  -- `AlgebraicGeometry.Spec`, which `rw` and `simp` will not do.
  have hsplit₁ : f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo g₁) =
      Scheme.descResidueField (Scheme.stalkClosedPointTo (g₁ ≫ f)) :=
    (Scheme.descResidueField_stalkClosedPointTo_comp f g₁).symm
  have hsplit₂ : (Y.residueFieldCongr e).hom ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo (g₂ ≫ f)) =
      (Y.residueFieldCongr e).hom ≫
        f.residueFieldMap (g₂ (IsLocalRing.closedPoint K)) ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo g₂) :=
    congrArg (fun t ↦ (Y.residueFieldCongr e).hom ≫ t)
      (Scheme.descResidueField_stalkClosedPointTo_comp f g₂)
  have hmove : (Y.residueFieldCongr e).hom ≫
      f.residueFieldMap (g₂ (IsLocalRing.closedPoint K)) ≫
        Scheme.descResidueField (Scheme.stalkClosedPointTo g₂) =
      f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
        (X.residueFieldCongr he).hom ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo g₂) :=
    (Scheme.Hom.residueFieldMap_congr'_assoc he _).symm
  have hkey : f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo g₁) =
      f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)) ≫
        (X.residueFieldCongr he).hom ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo g₂) :=
    hsplit₁.trans (h.trans (hsplit₂.trans hmove))
  rw [Scheme.SpecToEquivOfField_eq_iff]
  have hfx : (f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom.IsPurelyInseparable :=
    h₁.symm ▸ hf
  algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
  refine ⟨he, CommRingCat.hom_ext ?_⟩
  exact IsPurelyInseparable.injective_comp_algebraMap
    (Y.residueField (f (g₁ (IsLocalRing.closedPoint K))))
    (X.residueField (g₁ (IsLocalRing.closedPoint K))) _
    (CommRingCat.hom_ext_iff.mp hkey)

private theorem subsingleton_pullback_of_singleton_purelyInseparable_fiber
    {X T Y : Scheme.{u}} (f : X ⟶ Y) (a : T ⟶ Y) [Subsingleton T]
    (y : Y) (x : X) (ha : ∀ t, a t = y) (hf : f ⁻¹' {y} = {x})
    (hpure : (f.residueFieldMap x).hom.IsPurelyInseparable) :
    Subsingleton (pullback a f : Scheme.{u}) := by
  have hinj : ∀ (K : Type u) [Field K], Function.Injective
      (fun g : Spec (.of K) ⟶ pullback a f ↦ g ≫ pullback.fst a f) := by
    intro K hK g₁ g₂ he
    have hx (g : Spec (.of K) ⟶ pullback a f) :
        (g ≫ pullback.snd a f) (IsLocalRing.closedPoint K) = x := by
      apply Set.mem_singleton_iff.mp
      rw [← hf]
      change f ((g ≫ pullback.snd a f) (IsLocalRing.closedPoint K)) = y
      exact (congrArg (fun k : Spec (.of K) ⟶ Y ↦ k (IsLocalRing.closedPoint K))
        (comp_snd_comp_eq_comp_fst_comp f a g)).trans (ha _)
    apply pullback.hom_ext
    · exact he
    · apply spec_hom_ext_of_purelyInseparable f x hpure _ _ (hx g₁) (hx g₂)
      rw [comp_snd_comp_eq_comp_fst_comp, comp_snd_comp_eq_comp_fst_comp]
      exact congrArg (· ≫ a) he
  have : UniversallyInjective (pullback.fst a f) :=
    ((tfae_universallyInjective (pullback.fst a f)).out 2 1).mp hinj
  exact ⟨fun p q ↦ (pullback.fst a f).injective (Subsingleton.elim _ _)⟩

private theorem subsingleton_pullback_of_singleton_fiber_residueFieldCongr
    {X T Y : Scheme.{u}} (f : X ⟶ Y) (a : T ⟶ Y) [Subsingleton T]
    (y : Y) (x : X) (ha : ∀ t, a t = y) (hf : f ⁻¹' {y} = {x})
    (hpure : ∃ hxy : f x = y,
      ((Y.residueFieldCongr hxy).inv ≫ f.residueFieldMap x).hom.IsPurelyInseparable) :
    Subsingleton (pullback a f : Scheme.{u}) := by
  obtain ⟨rfl, hpure⟩ := hpure
  apply subsingleton_pullback_of_singleton_purelyInseparable_fiber f a (f x) x ha hf
  simpa using hpure

theorem isFinite_preimage_open_of_isPullback
    {P A T U : Scheme.{u}} (k : P ⟶ A) (a : P ⟶ T) (b : A ⟶ U) (c : T ⟶ U)
    (sq : IsPullback k a b c) (D : A.Opens) (hD : IsFinite (D.ι ≫ b)) :
    IsFinite ((k ⁻¹ᵁ D).ι ≫ a) :=
  MorphismProperty.of_isPullback
    ((isPullback_morphismRestrict k D).paste_vert sq) hD

private theorem preimage_subsingleton_of_singleton_purelyInseparable_fiber
    {P A T U : Scheme.{u}} (k : P ⟶ A) (a : P ⟶ T) (b : A ⟶ U) (c : T ⟶ U)
    (sq : IsPullback k a b c) [Subsingleton T]
    (u : U) (hc : ∀ t, c t = u) (D : A.Opens) (v : D)
    (hv : (D.ι ≫ b) ⁻¹' {u} = {v})
    (hpure : ∃ hvu : (D.ι ≫ b) v = u,
      ((U.residueFieldCongr hvu).inv ≫ (D.ι ≫ b).residueFieldMap v).hom.IsPurelyInseparable) :
    ((k ⁻¹ᵁ D : P.Opens) : Set P).Subsingleton := by
  have hsq := ((IsPullback.of_hasPullback k D.ι).flip.paste_vert sq).flip
  have hsub := subsingleton_pullback_of_singleton_fiber_residueFieldCongr
    (D.ι ≫ b) c u v hc hv hpure
  have : Subsingleton (pullback k D.ι : Scheme.{u}) :=
    ⟨fun x y ↦ hsq.isoPullback.hom.injective (Subsingleton.elim _ _)⟩
  have hr := Set.subsingleton_range (pullback.fst k D.ι)
  change ((pullback.fst k D.ι).opensRange : Set P).Subsingleton at hr
  rw [Scheme.Hom.opensRange_pullbackFst, D.opensRange_ι] at hr
  exact hr

private theorem exists_subset_preimage_eq_of_singleton_purelyInseparable_fibers
    {P A T U : Scheme.{u}} (k : P ⟶ A) (a : P ⟶ T) (b : A ⟶ U) (c : T ⟶ U)
    (sq : IsPullback k a b c) [Subsingleton T]
    (u : U) (hc : ∀ t, c t = u)
    {I : Type*} (D : I → A.Opens)
    (hD : ∀ i, ∃ v : D i, ((D i).ι ≫ b) ⁻¹' {u} = {v} ∧
      ∃ hvu : ((D i).ι ≫ b) v = u,
        ((U.residueFieldCongr hvu).inv ≫
          ((D i).ι ≫ b).residueFieldMap v).hom.IsPurelyInseparable)
    (Z : P.Opens) (hZ : (Z : Set P) ⊆ ⋃ i, ((k ⁻¹ᵁ D i : P.Opens) : Set P)) :
    ∃ J : Set I, Z = ⨆ i ∈ J, k ⁻¹ᵁ D i := by
  have hsub (i : I) : ((k ⁻¹ᵁ D i : P.Opens) : Set P).Subsingleton := by
    obtain ⟨v, hv, hpure⟩ := hD i
    exact preimage_subsingleton_of_singleton_purelyInseparable_fiber
      k a b c sq u hc (D i) v hv hpure
  obtain ⟨J, hJ⟩ := exists_subset_eq_union_of_subsingleton
    (fun i ↦ ((k ⁻¹ᵁ D i : P.Opens) : Set P)) hsub Z hZ
  exact ⟨J, SetLike.coe_injective (by simpa using hJ)⟩

theorem exists_subset_of_etale_decomposition
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (s : Finset (f.fiber y))
    (U : EtaleNeighborhood Y y) {I : Type u}
    (W : (pullback f U.toBase).Opens) (D : I → (pullback f U.toBase).Opens)
    (hcover : ((W : Set (pullback f U.toBase : Scheme.{u})) ∪
      ⋃ i, (D i : Set (pullback f U.toBase : Scheme.{u}))) = Set.univ)
    (hD : ∀ i, ∃ v : D i,
      ((D i).ι ≫ pullback.snd f U.toBase) ⁻¹' {U.point} = {v} ∧
      ∃ hvu : ((D i).ι ≫ pullback.snd f U.toBase) v = U.point,
        ((U.scheme.residueFieldCongr hvu).inv ≫
          ((D i).ι ≫ pullback.snd f U.toBase).residueFieldMap v).hom.IsPurelyInseparable)
    (hW : ∀ w : W, (W.ι ≫ pullback.snd f U.toBase) w = U.point →
      ∀ x ∈ s, (W.ι ≫ pullback.fst f U.toBase) w ≠ f.fiberι y x)
    {K : Type u} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ Y)
    (hb : b default = y) (Z : (pullback b f).Opens)
    (hZ : ∀ z : Z, ∃ x ∈ s,
      (Z.ι ≫ pullback.snd b f) z = f.fiberι y x) :
    ∃ (l : Spec (.of K) ⟶ U.scheme)
      (k : pullback b f ⟶ pullback f U.toBase) (J : Set I),
      l ≫ U.toBase = b ∧ l default = U.point ∧
      k ≫ pullback.fst f U.toBase = pullback.snd b f ∧
      k ≫ pullback.snd f U.toBase = pullback.fst b f ≫ l ∧
      Z = ⨆ i ∈ J, k ⁻¹ᵁ D i := by
  obtain ⟨l, hl, hlu⟩ := Scheme.exists_fac_of_etale_of_isSepClosed U.toBase b
    U.point (U.map_point.trans hb.symm)
  let k : pullback b f ⟶ pullback f U.toBase :=
    pullback.lift (pullback.snd b f) (pullback.fst b f ≫ l) (by
      rw [Category.assoc, hl, pullback.condition])
  have hkfst : k ≫ pullback.fst f U.toBase = pullback.snd b f :=
    pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd f U.toBase = pullback.fst b f ≫ l :=
    pullback.lift_snd _ _ _
  have sq : IsPullback k (pullback.fst b f) (pullback.snd f U.toBase) l := by
    apply IsPullback.of_right _ hksnd (IsPullback.of_hasPullback f U.toBase)
    rw [hkfst, hl]
    exact (IsPullback.of_hasPullback b f).flip
  have hlpoint (t : Spec (.of K)) : l t = U.point :=
    (congrArg l (Subsingleton.elim t default)).trans hlu
  have hZcover : (Z : Set (pullback b f : Scheme.{u})) ⊆
      ⋃ i, ((k ⁻¹ᵁ D i : (pullback b f).Opens) : Set (pullback b f : Scheme.{u})) := by
    intro z hz
    have hmem : k z ∈ (W : Set (pullback f U.toBase : Scheme.{u})) ∪
        ⋃ i, (D i : Set (pullback f U.toBase : Scheme.{u})) := by rw [hcover]; trivial
    rcases hmem with hw | hd
    · obtain ⟨x, hx, hzx⟩ := hZ ⟨z, hz⟩
      have hwpoint : (W.ι ≫ pullback.snd f U.toBase) ⟨k z, hw⟩ = U.point := by
        change (k ≫ pullback.snd f U.toBase) z = U.point
        rw [hksnd]
        exact hlpoint _
      refine (hW ⟨k z, hw⟩ hwpoint x hx ?_).elim
      change (k ≫ pullback.fst f U.toBase) z = f.fiberι y x
      rw [hkfst]
      exact hzx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hd
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨J, hJ⟩ := exists_subset_preimage_eq_of_singleton_purelyInseparable_fibers
    k (pullback.fst b f) (pullback.snd f U.toBase) l sq U.point hlpoint D hD Z hZcover
  exact ⟨l, k, J, hl, hlu, hkfst, hksnd, hJ⟩

end AlgebraicGeometry.FinitePartChart

end
