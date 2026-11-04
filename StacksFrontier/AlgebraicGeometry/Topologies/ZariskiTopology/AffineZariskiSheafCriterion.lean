module

public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.SheafOnBasis
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallZariskiOpens
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.StandardOpenCoverSquares

/-!
# Detecting Zariski sheaves on the affine opens of a scheme

The small affine Zariski site of a scheme `X` is the category of affine opens of `X`. A presheaf
of sets on it is a sheaf as soon as it has a single section over the empty affine open and glues
compatible pairs of sections across the covers of an affine open by two standard opens; the
gluing theory of presheaves on the affine-open basis reduces an arbitrary covering family to
such a pair.

## Main definitions

* `AlgebraicGeometry.affineBasisToSmallAffineZariski`: an affine open of `X`, viewed as an
  object of the small affine Zariski site.
* `AlgebraicGeometry.smallAffineZariskiEquivAffineBasis`: the equivalence between the small
  affine Zariski site of `X` and the affine-open basis category of `X`.

## Main results

* `AlgebraicGeometry.isSheaf_smallAffineZariski_of_isSheafFor_affineBasis`: a presheaf on the
  small affine Zariski site is a sheaf once it satisfies the sheaf condition for the covers of
  an affine open by affine opens.
* `AlgebraicGeometry.isSheaf_smallAffineZariski_of_isPullback_standardOpenCoverSquare`: a sheaf
  for a topology under which the empty affine opens are covered by the empty sieve is a sheaf
  for the Zariski topology as soon as it turns standard open cover squares into pullbacks.
* `AlgebraicGeometry.isSheaf_smallAffineZariski_of_almostChaotic`: the same criterion for a
  sheaf for the almost chaotic topology.

## References

* [Stacks Project, Tag 0F1A](https://stacks.math.columbia.edu/tag/0F1A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.OpensBasis

universe w v u

namespace AlgebraicGeometry

/-! ### Gluing sections over the affine-open basis -/

section Basis

variable (X : Scheme.{u})

/-- The standard open cut out by a product of two sections of an affine open is contained in the
standard open cut out by the first of them. -/
private lemma affineBasisOpen_mul_le_left (U : X.affineOpens) (f g : Γ(X, U.val)) :
    (Scheme.affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
      (Scheme.affineBasisOpen X (X.affineBasicOpen f)).obj := by
  show X.basicOpen (f * g) ≤ X.basicOpen f
  rw [X.basicOpen_mul]
  exact inf_le_left

/-- The standard open cut out by a product of two sections of an affine open is contained in the
standard open cut out by the second of them. -/
private lemma affineBasisOpen_mul_le_right (U : X.affineOpens) (f g : Γ(X, U.val)) :
    (Scheme.affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
      (Scheme.affineBasisOpen X (X.affineBasicOpen g)).obj := by
  show X.basicOpen (f * g) ≤ X.basicOpen g
  rw [X.basicOpen_mul]
  exact inf_le_right

/-- The standard open cut out by a section of an affine open is contained in that affine
open. -/
private lemma affineBasisOpen_affineBasicOpen_le (U : X.affineOpens) (f : Γ(X, U.val)) :
    (Scheme.affineBasisOpen X (X.affineBasicOpen f)).obj ≤
      (Scheme.affineBasisOpen X U).obj :=
  X.affineBasicOpen_le f

/-- The standard-pair gluing condition for a presheaf on the affine-open basis: over an affine
open presented as the union of the two standard opens cut out by `f` and `g`, a pair of sections
agreeing on the standard open cut out by `f * g` glues to a unique section. -/
private def StandardPairGluing (G : (BasisCat X.affineOpens)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ (U : X.affineOpens) (f g : Γ(X, U.val))
    (_hcov : U.val = X.basicOpen f ⊔ X.basicOpen g)
    (s : G.obj (op (Scheme.affineBasisOpen X (X.affineBasicOpen f))))
    (t : G.obj (op (Scheme.affineBasisOpen X (X.affineBasicOpen g)))),
    basisRestrictMap X.affineOpens G (affineBasisOpen_mul_le_left X U f g) s =
      basisRestrictMap X.affineOpens G (affineBasisOpen_mul_le_right X U f g) t →
    ∃! r : G.obj (op (Scheme.affineBasisOpen X U)),
      (basisRestrictMap X.affineOpens G (affineBasisOpen_affineBasicOpen_le X U f) r = s) ∧
      (basisRestrictMap X.affineOpens G (affineBasisOpen_affineBasicOpen_le X U g) r = t)

variable (G : (BasisCat X.affineOpens)ᵒᵖ ⥤ Type v)

/-- A cover of an affine open by affine opens is refined by finitely many standard opens that
cover it. -/
private lemma exists_basicOpen_refinement_affineBasis (affine : X.affineOpens) {ι : Type*}
    (cover : ι → BasisCat X.affineOpens) (hcover : (⨆ index, (cover index).obj) = affine.val) :
    ∃ (count : ℕ) (functions : Fin count → Γ(X, affine.val)) (indices : Fin count → ι),
      (⨆ index, X.basicOpen (functions index)) = affine.val ∧ ∀ index,
        (Scheme.affineBasisOpen X (X.affineBasicOpen (functions index))).obj ≤
          (cover (indices index)).obj :=
  Scheme.exists_finite_basicOpen_refinement_affine affine.property
    (fun index => (cover index).obj) hcover.ge

/-- Restrictions of two sections to the standard opens cut out by `f` and `g` agree on the
standard open cut out by `f * g` as soon as the sections agree there. -/
private lemma basisRestrictMap_mul_eq (affine : X.affineOpens) (f g : Γ(X, affine.val))
    {V W : BasisCat X.affineOpens} (v : G.obj (op V)) (w : G.obj (op W))
    (hf : (Scheme.affineBasisOpen X (X.affineBasicOpen f)).obj ≤ V.obj)
    (hg : (Scheme.affineBasisOpen X (X.affineBasicOpen g)).obj ≤ W.obj)
    (h : ∀ (hv : (Scheme.affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤ V.obj)
      (hw : (Scheme.affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤ W.obj),
      basisRestrictMap X.affineOpens G hv v = basisRestrictMap X.affineOpens G hw w) :
    basisRestrictMap X.affineOpens G (affineBasisOpen_mul_le_left X affine f g)
        (basisRestrictMap X.affineOpens G hf v) =
      basisRestrictMap X.affineOpens G (affineBasisOpen_mul_le_right X affine f g)
        (basisRestrictMap X.affineOpens G hg w) := by
  rw [Scheme.basisRestrictMap_comp, Scheme.basisRestrictMap_comp]
  exact h _ _

/-- A section of a presheaf on the affine-open basis satisfying the empty-open and standard-pair
gluing conditions is determined by its restrictions to any cover of an affine open by affine
opens. -/
private lemma affineBasis_sections_ext
    (hempty : ∃! _s : G.obj (op (Scheme.affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)), True)
    (hpair : StandardPairGluing X G)
    {U : BasisCat X.affineOpens} {ι : Type*} (cover : ι → BasisCat X.affineOpens)
    (hcover : (⨆ index, (cover index).obj) = U.obj)
    {first second : G.obj (op U)}
    (agreement : ∀ index, basisRestrictMap X.affineOpens G
      ((le_iSup (fun index => (cover index).obj) index).trans_eq hcover) first =
        basisRestrictMap X.affineOpens G
          ((le_iSup (fun index => (cover index).obj) index).trans_eq hcover) second) :
    first = second := by
  classical
  let affine : X.affineOpens := ⟨U.obj, U.property⟩
  obtain ⟨count, functions, indices, refinementCover, refinementLe'⟩ :=
    exists_basicOpen_refinement_affineBasis X affine cover hcover
  let sections : ∀ index : Fin count,
      G.obj (op (Scheme.affineBasisOpen X (X.affineBasicOpen (functions index)))) :=
    fun index => basisRestrictMap X.affineOpens G
      (affineBasisOpen_affineBasicOpen_le X affine (functions index)) first
  have compatibility : ∀ firstIndex secondIndex,
      basisRestrictMap X.affineOpens G
          (affineBasisOpen_mul_le_left X affine (functions firstIndex)
            (functions secondIndex)) (sections firstIndex) =
        basisRestrictMap X.affineOpens G
          (affineBasisOpen_mul_le_right X affine (functions firstIndex)
            (functions secondIndex)) (sections secondIndex) := fun _ _ =>
    basisRestrictMap_mul_eq X G affine _ _ first first _ _ fun _ _ => rfl
  obtain ⟨glued, gluing, unique⟩ := Scheme.finite_basicOpen_glue X G hempty hpair
    affine count functions refinementCover sections compatibility
  refine (unique first fun _ => rfl).trans (unique second fun index => ?_).symm
  dsimp only [sections]
  simpa only [Scheme.basisRestrictMap_comp] using (congrArg
    (basisRestrictMap X.affineOpens G
      (V := Scheme.affineBasisOpen X (X.affineBasicOpen (functions index)))
      (refinementLe' index))
    (agreement (indices index))).symm

/-- A presheaf on the affine-open basis satisfying the empty-open and standard-pair gluing
conditions glues a compatible family of sections over any cover of an affine open by affine
opens, uniquely. -/
private lemma affineBasis_sections_glue
    (hempty : ∃! _s : G.obj (op (Scheme.affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)), True)
    (hpair : StandardPairGluing X G)
    {U : BasisCat X.affineOpens} {ι : Type*} (cover : ι → BasisCat X.affineOpens)
    (hcover : (⨆ index, (cover index).obj) = U.obj)
    (sections : ∀ index, G.obj (op (cover index)))
    (compatibility : ∀ firstIndex secondIndex (V : BasisCat X.affineOpens)
      (firstLe : V.obj ≤ (cover firstIndex).obj)
      (secondLe : V.obj ≤ (cover secondIndex).obj),
      basisRestrictMap X.affineOpens G firstLe (sections firstIndex) =
        basisRestrictMap X.affineOpens G secondLe (sections secondIndex)) :
    ∃! value : G.obj (op U), ∀ index,
      basisRestrictMap X.affineOpens G
        ((le_iSup (fun index => (cover index).obj) index).trans_eq hcover) value =
          sections index := by
  classical
  let affine : X.affineOpens := ⟨U.obj, U.property⟩
  obtain ⟨count, functions, indices, refinementCover, refinementLe'⟩ :=
    exists_basicOpen_refinement_affineBasis X affine cover hcover
  let refinedSections : ∀ index : Fin count,
      G.obj (op (Scheme.affineBasisOpen X (X.affineBasicOpen (functions index)))) :=
    fun index =>
      basisRestrictMap X.affineOpens G (refinementLe' index) (sections (indices index))
  have refinedCompatibility : ∀ firstIndex secondIndex,
      basisRestrictMap X.affineOpens G
          (affineBasisOpen_mul_le_left X affine (functions firstIndex)
            (functions secondIndex)) (refinedSections firstIndex) =
        basisRestrictMap X.affineOpens G
          (affineBasisOpen_mul_le_right X affine (functions firstIndex)
            (functions secondIndex)) (refinedSections secondIndex) := fun _ _ =>
    basisRestrictMap_mul_eq X G affine _ _ _ _ _ _ fun _ _ =>
      compatibility _ _ _ _ _
  obtain ⟨glued, gluing, unique⟩ := Scheme.finite_basicOpen_glue X G hempty hpair
    affine count functions refinementCover refinedSections refinedCompatibility
  have gluedRestriction : ∀ index,
      basisRestrictMap X.affineOpens G
        ((le_iSup (fun index => (cover index).obj) index).trans_eq hcover) glued =
          sections index := by
    intro index
    let localAffine : X.affineOpens := ⟨(cover index).obj, (cover index).property⟩
    have localLe : (cover index).obj ≤ U.obj :=
      (le_iSup (fun index => (cover index).obj) index).trans_eq hcover
    let localFunctions : Fin count → Γ(X, localAffine.val) := fun refinedIndex =>
      X.presheaf.map (homOfLE localLe).op (functions refinedIndex)
    have localBasic : ∀ refinedIndex,
        X.basicOpen (localFunctions refinedIndex) =
          localAffine.val ⊓ X.basicOpen (functions refinedIndex) :=
      fun _ => X.basicOpen_res _ _
    have localCover : (⨆ refinedIndex, X.basicOpen (localFunctions refinedIndex)) =
        localAffine.val := by
      show (⨆ refinedIndex, X.basicOpen (localFunctions refinedIndex)) = (cover index).obj
      simp only [localBasic, ← inf_iSup_eq, refinementCover]
      exact inf_eq_left.mpr localLe
    apply affineBasis_sections_ext X G hempty hpair
      (fun refinedIndex => Scheme.affineBasisOpen X
        (X.affineBasicOpen (localFunctions refinedIndex))) localCover
    intro refinedIndex
    let localOpen := Scheme.affineBasisOpen X (X.affineBasicOpen (localFunctions refinedIndex))
    have localRefinementLe : localOpen.obj ≤
        (Scheme.affineBasisOpen X (X.affineBasicOpen (functions refinedIndex))).obj := by
      show X.basicOpen (localFunctions refinedIndex) ≤ X.basicOpen (functions refinedIndex)
      rw [localBasic]
      exact inf_le_right
    have localCoverLe : localOpen.obj ≤ (cover index).obj := by
      show X.basicOpen (localFunctions refinedIndex) ≤ (cover index).obj
      rw [localBasic]
      exact inf_le_left
    calc
      _ = basisRestrictMap X.affineOpens G localRefinementLe
          (basisRestrictMap X.affineOpens G
            (affineBasisOpen_affineBasicOpen_le X affine (functions refinedIndex)) glued) := by
        rw [Scheme.basisRestrictMap_comp, Scheme.basisRestrictMap_comp]
      _ = basisRestrictMap X.affineOpens G localRefinementLe
          (refinedSections refinedIndex) := congrArg _ (gluing refinedIndex)
      _ = basisRestrictMap X.affineOpens G
          (localRefinementLe.trans (refinementLe' refinedIndex))
          (sections (indices refinedIndex)) := by
        dsimp only [refinedSections]
        rw [Scheme.basisRestrictMap_comp]
      _ = basisRestrictMap X.affineOpens G localCoverLe (sections index) :=
        compatibility (indices refinedIndex) index localOpen _ _
  exact ⟨glued, gluedRestriction, fun other otherRestriction =>
    affineBasis_sections_ext X G hempty hpair cover hcover
      fun index => (otherRestriction index).trans (gluedRestriction index).symm⟩

/-- A presheaf on the affine-open basis satisfying the empty-open and standard-pair gluing
conditions satisfies the sheaf condition for every cover of an affine open by affine opens. -/
private lemma isSheafFor_affineBasis_cover
    (hempty : ∃! _s : G.obj (op (Scheme.affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)), True)
    (hpair : StandardPairGluing X G)
    {U : BasisCat X.affineOpens} {ι : Type w} (cover : ι → BasisCat X.affineOpens)
    (arrows : ∀ index, cover index ⟶ U)
    (hcover : (⨆ index, (cover index).obj) = U.obj) :
    Presieve.IsSheafFor G (Presieve.ofArrows cover arrows) := by
  have hom_eq : ∀ {A B : BasisCat X.affineOpens} (f g : A ⟶ B), f = g := fun _ _ => by
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _
  rw [Presieve.isSheafFor_arrows_iff]
  intro sections compatibility
  obtain ⟨value, gluing, unique⟩ := affineBasis_sections_glue X G hempty hpair
    cover hcover sections (fun firstIndex secondIndex V firstLe secondLe =>
      compatibility firstIndex secondIndex V (basisHom X.affineOpens firstLe)
        (basisHom X.affineOpens secondLe) (hom_eq _ _))
  have arrow_eq : ∀ index, arrows index = basisHom X.affineOpens
      ((le_iSup (fun index => (cover index).obj) index).trans_eq hcover) := fun _ =>
    hom_eq _ _
  exact ⟨value, fun index => by simpa only [basisRestrictMap, arrow_eq] using gluing index,
    fun other restrictions => unique other fun index => by
      simpa only [basisRestrictMap, arrow_eq] using restrictions index⟩

end Basis

variable (B : BigZariskiSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-! ### The small affine Zariski site as the affine-open basis -/

/-- The small affine Zariski site of `X` is the category of affine opens of `X`: an object is
sent to the open image of its structure morphism. -/
noncomputable def smallAffineZariskiEquivAffineBasis :
    SmallAffineZariski B X hX ≌ BasisCat X.affineOpens := by
  letI : (basisProp X.affineOpens).IsClosedUnderIsomorphisms := ⟨by
    intro source target iso hsource
    have heq : source = target := le_antisymm (leOfHom iso.hom) (leOfHom iso.inv)
    simpa only [← heq] using hsource⟩
  exact (smallZariskiSiteEquiv B X hX).congrFullSubcategory
    (P := SmallZariski.IsAffine B X hX) (Q := basisProp X.affineOpens) (by
      ext object
      change IsAffineOpen (smallZariskiOpenImmersion B X hX object).opensRange ↔
        IsAffine ((SmallZariski.toScheme B X hX).obj object)
      let immersion := smallZariskiOpenImmersion B X hX object
      constructor
      · intro hopen
        exact (IsAffine.iff_of_isIso immersion.isoOpensRange.hom).2 hopen
      · intro haffine
        have := haffine
        exact isAffineOpen_opensRange immersion)

/-- An affine open of `X`, viewed as an object of the small affine Zariski site of `X`. -/
noncomputable def affineBasisToSmallAffineZariski :
    BasisCat X.affineOpens ⥤ SmallAffineZariski B X hX where
  obj U :=
    ⟨⟨Over.mk (ObjectProperty.homMk
      (X := ⟨Scheme.Opens.toScheme (X := X) U.obj,
        Scheme.size_lt_of_isOpenImmersion (Scheme.Opens.ι (X := X) U.obj) hX⟩)
      (Y := ⟨X, hX⟩) (Scheme.Opens.ι (X := X) U.obj)), by
        change IsOpenImmersion (Scheme.Opens.ι (X := X) U.obj)
        infer_instance⟩,
      U.property⟩
  map {U V} arrow := ObjectProperty.homMk
    (ObjectProperty.homMk (Over.homMk
      (ObjectProperty.homMk (X.homOfLE arrow.hom.le)) (by
        apply ObjectProperty.hom_ext
        simp)))
  map_id U := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp [Scheme.homOfLE_rfl]
  map_comp first second := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp [Scheme.homOfLE_homOfLE]

/-- The scheme of an affine open viewed in the small affine Zariski site is the open subscheme
it cuts out. -/
lemma affineBasisToSmallAffineZariski_toScheme_obj (U : BasisCat X.affineOpens) :
    (SmallAffineZariski.toScheme B X hX).obj
      ((affineBasisToSmallAffineZariski B X hX).obj U) =
        Scheme.Opens.toScheme (X := X) U.obj := rfl

/-- An inclusion of affine opens viewed in the small affine Zariski site is the inclusion of the
corresponding open subschemes. -/
lemma affineBasisToSmallAffineZariski_toScheme_map
    {U V : BasisCat X.affineOpens} (arrow : U ⟶ V) :
    (SmallAffineZariski.toScheme B X hX).map
      ((affineBasisToSmallAffineZariski B X hX).map arrow) = X.homOfLE arrow.hom.le :=
  rfl

/-- A morphism in the small affine Zariski site is determined by its source and target: its
scheme map is cut out by the structure morphism of the target, which is a monomorphism. -/
lemma smallAffineZariski_hom_ext {U V : SmallAffineZariski B X hX} (first second : U ⟶ V) :
    first = second := by
  apply (SmallAffineZariski.toScheme B X hX).map_injective
  apply (cancel_mono (smallZariskiOpenImmersion B X hX V.obj)).mp
  exact (smallZariskiOpenImmersion_comp B X hX first.hom).trans
    (smallZariskiOpenImmersion_comp B X hX second.hom).symm

/-- The affine open attached to an object of the small affine Zariski site is the open image of
its structure morphism. -/
lemma smallAffineZariskiEquivAffineBasis_obj (U : SmallAffineZariski B X hX) :
    ((smallAffineZariskiEquivAffineBasis B X hX).functor.obj U).obj =
      (smallZariskiOpenImmersion B X hX U.obj).opensRange := rfl

/-- Viewing an object of the small affine Zariski site as an affine open and back recovers the
object. -/
noncomputable def smallAffineZariskiAffineBasisCounitIso :
    (smallAffineZariskiEquivAffineBasis B X hX).functor ⋙
      affineBasisToSmallAffineZariski B X hX ≅ 𝟭 (SmallAffineZariski B X hX) := by
  let component : ∀ U : SmallAffineZariski B X hX,
      ((smallAffineZariskiEquivAffineBasis B X hX).functor ⋙
        affineBasisToSmallAffineZariski B X hX).obj U ≅ U := fun U =>
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Over.isoMk
      (ObjectProperty.isoMk _
        (smallZariskiOpenImmersion B X hX U.obj).isoOpensRange.symm)
      (by
        apply ObjectProperty.hom_ext
        change (smallZariskiOpenImmersion B X hX U.obj).isoOpensRange.inv ≫
          smallZariskiOpenImmersion B X hX U.obj = _
        exact Scheme.Hom.isoOpensRange_inv_comp _)))
  exact NatIso.ofComponents component
    (fun _ => smallAffineZariski_hom_ext B X hX _ _)

/-- Viewing affine opens of `X` as objects of the small affine Zariski site is an
equivalence. -/
instance affineBasisToSmallAffineZariski_isEquivalence :
    (affineBasisToSmallAffineZariski B X hX).IsEquivalence := by
  let equivalence := smallAffineZariskiEquivAffineBasis B X hX
  let _ : equivalence.functor.IsEquivalence := equivalence.isEquivalence_functor
  let _ : (equivalence.functor ⋙ affineBasisToSmallAffineZariski B X hX).IsEquivalence :=
    Functor.isEquivalence_of_iso (smallAffineZariskiAffineBasisCounitIso B X hX).symm
  exact Functor.isEquivalence_of_comp_left equivalence.functor _

/-- A family of maps in the small affine Zariski site whose schemes cover the target has open
images covering the affine open attached to the target. -/
lemma iSup_smallAffineZariskiEquivAffineBasis_obj
    {U : SmallAffineZariski B X hX} (E : PreZeroHypercover.{u + 1} U)
    (hE : (E.map (SmallAffineZariski.toScheme B X hX)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((SmallAffineZariski.toScheme B X hX).obj U)) :
    (⨆ index, ((smallAffineZariskiEquivAffineBasis B X hX).functor.obj (E.X index)).obj) =
      ((smallAffineZariskiEquivAffineBasis B X hX).functor.obj U).obj := by
  let immersion := smallZariskiOpenImmersion B X hX U.obj
  let cover : ((SmallAffineZariski.toScheme B X hX).obj U).OpenCover :=
    ⟨E.map (SmallAffineZariski.toScheme B X hX), hE⟩
  have : ∀ index, IsOpenImmersion
      ((SmallAffineZariski.toScheme B X hX).map (E.f index)) :=
    fun index => cover.map_prop index
  have h := congrArg (immersion ''ᵁ ·) cover.iSup_opensRange
  show (⨆ index, (smallZariskiOpenImmersion B X hX
    (E.X index).obj).opensRange) = immersion.opensRange
  change (immersion ''ᵁ ⨆ index,
    ((SmallAffineZariski.toScheme B X hX).map (E.f index)).opensRange) =
      immersion ''ᵁ ⊤ at h
  rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange] at h
  simpa only [← Scheme.Hom.opensRange_comp, immersion,
    show ∀ index, (SmallAffineZariski.toScheme B X hX).map (E.f index) ≫
      smallZariskiOpenImmersion B X hX U.obj =
        smallZariskiOpenImmersion B X hX (E.X index).obj from
      fun index => smallZariskiOpenImmersion_comp B X hX (E.f index).hom] using h

/-! ### From the affine-open basis to the small affine Zariski site -/

/-- A presheaf on the small affine Zariski site satisfying the sheaf condition for the covers of
an affine open by affine opens satisfies it for every covering family of the site. -/
lemma isSheafFor_smallAffineZariski_cover
    (F : (SmallAffineZariski B X hX)ᵒᵖ ⥤ Type v)
    (hbasis : ∀ {W : BasisCat X.affineOpens} {ι : Type (u + 1)}
      (cover : ι → BasisCat X.affineOpens) (arrows : ∀ index, cover index ⟶ W),
      (⨆ index, (cover index).obj) = W.obj →
      Presieve.IsSheafFor ((affineBasisToSmallAffineZariski B X hX).op ⋙ F)
        (Presieve.ofArrows cover arrows))
    {U : SmallAffineZariski B X hX} (E : PreZeroHypercover.{u + 1} U)
    (hE : (E.map (SmallAffineZariski.toScheme B X hX)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((SmallAffineZariski.toScheme B X hX).obj U)) :
    Presieve.IsSheafFor F E.presieve₀ := by
  let equivalence := smallAffineZariskiEquivAffineBasis B X hX
  let G := (affineBasisToSmallAffineZariski B X hX).op ⋙ F
  let comparison : equivalence.functor.op ⋙ G ≅ F :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.op (smallAffineZariskiAffineBasisCounitIso B X hX)).symm F ≪≫
        Functor.leftUnitor F
  apply Presieve.isSheafFor_iso comparison
  apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks
    equivalence.functor G E.presieve₀).mpr
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
  exact hbasis (fun index => equivalence.functor.obj (E.X index))
    (fun index => equivalence.functor.map (E.f index))
    (iSup_smallAffineZariskiEquivAffineBasis_obj B X hX E hE)

/-- A presheaf on the small affine Zariski site of `X` is a sheaf as soon as it satisfies the
sheaf condition for the covers of an affine open of `X` by affine opens. -/
lemma isSheaf_smallAffineZariski_of_isSheafFor_affineBasis
    (F : (SmallAffineZariski B X hX)ᵒᵖ ⥤ Type v)
    (hbasis : ∀ {W : BasisCat X.affineOpens} {ι : Type (u + 1)}
      (cover : ι → BasisCat X.affineOpens) (arrows : ∀ index, cover index ⟶ W),
      (⨆ index, (cover index).obj) = W.obj →
      Presieve.IsSheafFor ((affineBasisToSmallAffineZariski B X hX).op ⋙ F)
        (Presieve.ofArrows cover arrows)) :
    Presheaf.IsSheaf (SmallAffineZariski.topology B X hX) F := by
  rw [isSheaf_iff_isSheaf_of_type, Precoverage.isSheaf_toGrothendieck_iff]
  intro U V arrow presieve covering
  rw [SmallAffineZariski.mem_precoverage_iff] at covering
  obtain ⟨E, rfl, hE⟩ := covering
  let schemeFunctor := SmallAffineZariski.toScheme B X hX
  obtain ⟨-, hscheme, -⟩ := hE
  change (E.map schemeFunctor).presieve₀ ∈ Scheme.zariskiPrecoverage
    (schemeFunctor.obj U) at hscheme
  let schemeCover : (schemeFunctor.obj U).OpenCover := ⟨E.map schemeFunctor, hscheme⟩
  have : ∀ index, IsOpenImmersion (schemeFunctor.map (E.f index)) :=
    fun index => schemeCover.map_prop index
  have hpullback : ((E.pullback₂ arrow).map schemeFunctor).presieve₀ ∈
      Scheme.zariskiPrecoverage (schemeFunctor.obj V) := by
    apply Precoverage.mem_coverings_of_isPullback (E.map schemeFunctor).f hscheme
      (schemeFunctor.map arrow)
      (fun index => schemeFunctor.map (pullback.snd (E.f index) arrow))
      (fun index => schemeFunctor.map (pullback.fst (E.f index) arrow))
    intro index
    exact ((IsPullback.of_hasPullback (E.f index) arrow).map schemeFunctor).flip
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate,
    ← PreZeroHypercover.presieve₀_pullback₁]
  exact isSheafFor_smallAffineZariski_cover B X hX F hbasis (E.pullback₂ arrow) hpullback

/-! ### Standard-open cover squares -/

/-- The square of affine opens cut out by two sections of an affine open: the two standard opens
they define, their intersection, and the affine open itself. -/
noncomputable def affineBasisStandardSquare
    (U : X.affineOpens) (firstFunction secondFunction : Γ(X, U.val)) :
    Square (BasisCat X.affineOpens) where
  X₁ := Scheme.affineBasisOpen X (X.affineBasicOpen (firstFunction * secondFunction))
  X₂ := Scheme.affineBasisOpen X (X.affineBasicOpen firstFunction)
  X₃ := Scheme.affineBasisOpen X (X.affineBasicOpen secondFunction)
  X₄ := Scheme.affineBasisOpen X U
  f₁₂ := basisHom X.affineOpens (by
    change X.basicOpen (firstFunction * secondFunction) ≤ X.basicOpen firstFunction
    rw [X.basicOpen_mul]
    exact inf_le_left)
  f₁₃ := basisHom X.affineOpens (by
    change X.basicOpen (firstFunction * secondFunction) ≤ X.basicOpen secondFunction
    rw [X.basicOpen_mul]
    exact inf_le_right)
  f₂₄ := basisHom X.affineOpens (X.affineBasicOpen_le firstFunction)
  f₃₄ := basisHom X.affineOpens (X.affineBasicOpen_le secondFunction)
  fac := by
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _

/-- The open image of a standard open of `X` inside an affine open containing it is the standard
open cut out there by the restricted section. -/
lemma basicOpen_homOfLE_range (U : X.affineOpens) (function : Γ(X, U.val)) :
    (X.homOfLE (X.basicOpen_le function)).opensRange =
      U.val.toScheme.basicOpen (U.val.topIso.inv function) := by
  apply U.val.ι.image_injective
  show U.val.ι ''ᵁ (X.homOfLE (X.basicOpen_le function)).opensRange =
    U.val.ι ''ᵁ U.val.toScheme.basicOpen (U.val.topIso.inv function)
  calc
    _ = (X.homOfLE (X.basicOpen_le function) ≫ U.val.ι).opensRange :=
      (Scheme.Hom.opensRange_comp _ _).symm
    _ = X.basicOpen function := by simp only [Scheme.homOfLE_ι, Scheme.Opens.opensRange_ι]
    _ = _ := (Scheme.Opens.ι_image_basicOpen_topIso_inv U.val function).symm

/-- Two sections covering an affine open of `X` cut out a standard open cover square in the
small affine Zariski site. -/
lemma isStandardOpenCoverSquare_affineBasisStandardSquare
    (U : X.affineOpens) (firstFunction secondFunction : Γ(X, U.val))
    (covering : U.val = X.basicOpen firstFunction ⊔ X.basicOpen secondFunction) :
    SmallAffineZariski.IsStandardOpenCoverSquare B X hX
      ((affineBasisStandardSquare X U firstFunction secondFunction).map
        (affineBasisToSmallAffineZariski B X hX)) := by
  let firstArrow := X.homOfLE (X.basicOpen_le firstFunction)
  let secondArrow := X.homOfLE (X.basicOpen_le secondFunction)
  have firstRange := basicOpen_homOfLE_range X U firstFunction
  have secondRange := basicOpen_homOfLE_range X U secondFunction
  let firstIso := firstArrow.isoOpensRange ≪≫
    (U.val.toScheme.restrictFunctor ⋙ Over.forget _).mapIso (eqToIso firstRange)
  let secondIso := secondArrow.isoOpensRange ≪≫
    (U.val.toScheme.restrictFunctor ⋙ Over.forget _).mapIso (eqToIso secondRange)
  refine ⟨U.val.topIso.inv firstFunction, U.val.topIso.inv secondFunction,
    firstIso, secondIso, ?_, ?_, ?_, ?_⟩
  · show firstArrow = firstArrow.isoOpensRange.hom ≫
      U.val.toScheme.homOfLE firstRange.le ≫
        (U.val.toScheme.basicOpen (U.val.topIso.inv firstFunction)).ι
    rw [Scheme.homOfLE_ι]
    exact firstArrow.isoOpensRange_hom_ι.symm
  · show secondArrow = secondArrow.isoOpensRange.hom ≫
      U.val.toScheme.homOfLE secondRange.le ≫
        (U.val.toScheme.basicOpen (U.val.topIso.inv secondFunction)).ι
    rw [Scheme.homOfLE_ι]
    exact secondArrow.isoOpensRange_hom_ι.symm
  · apply U.val.ι.image_injective
    show U.val.ι ''ᵁ (U.val.toScheme.basicOpen (U.val.topIso.inv firstFunction) ⊔
      U.val.toScheme.basicOpen (U.val.topIso.inv secondFunction)) = U.val.ι ''ᵁ ⊤
    rw [show ∀ (first second : U.val.toScheme.Opens),
        U.val.ι ''ᵁ (first ⊔ second) = U.val.ι ''ᵁ first ⊔ U.val.ι ''ᵁ second from
      fun first second => Opens.ext (Set.image_union _ _ _),
      Scheme.Opens.ι_image_basicOpen_topIso_inv,
      Scheme.Opens.ι_image_basicOpen_topIso_inv, ← covering]
    simp
  · show CategoryTheory.IsPullback
      (X.homOfLE (show X.basicOpen (firstFunction * secondFunction) ≤
          X.basicOpen firstFunction by rw [X.basicOpen_mul]; exact inf_le_left))
      (X.homOfLE (show X.basicOpen (firstFunction * secondFunction) ≤
          X.basicOpen secondFunction by rw [X.basicOpen_mul]; exact inf_le_right))
      (X.homOfLE (X.basicOpen_le firstFunction))
      (X.homOfLE (X.basicOpen_le secondFunction))
    refine (isPullback_opens_inf_le (X.basicOpen_le firstFunction)
      (X.basicOpen_le secondFunction)).of_iso
      (X.isoOfEq (X.basicOpen_mul firstFunction secondFunction).symm)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    all_goals simp [Scheme.isoOfEq_hom, Scheme.homOfLE_homOfLE]

/-! ### The sheaf criterion -/

/-- A sheaf of sets on the affine opens of `X`, for a topology under which the empty sieve covers
every empty affine open, is a sheaf for the Zariski topology as soon as it turns every standard
open cover square into a pullback. -/
theorem isSheaf_smallAffineZariski_of_isPullback_standardOpenCoverSquare
    {J : GrothendieckTopology (SmallAffineZariski B X hX)}
    (hbot : ∀ U : SmallAffineZariski B X hX,
      IsEmpty ((SmallAffineZariski.toScheme B X hX).obj U) → (⊥ : Sieve U) ∈ J U)
    (F : Sheaf J (Type v))
    (pullbacks : ∀ sq : Square (SmallAffineZariski B X hX),
      SmallAffineZariski.IsStandardOpenCoverSquare B X hX sq → (sq.op.map F.obj).IsPullback) :
    Presheaf.IsSheaf (SmallAffineZariski.topology B X hX) F.obj := by
  have hempty : ∃! _s : ((affineBasisToSmallAffineZariski B X hX).op ⋙ F.obj).obj
      (op (Scheme.affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)), True := by
    let emptyObject := (affineBasisToSmallAffineZariski B X hX).obj
      (Scheme.affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)
    have hisEmpty : IsEmpty ((SmallAffineZariski.toScheme B X hX).obj emptyObject) := by
      show IsEmpty (Scheme.Opens.toScheme (X := X) ⊥)
      exact ⟨fun point => point.property⟩
    have terminal := F.isTerminalOfBotCover emptyObject (hbot emptyObject hisEmpty)
    let unique := (Types.isTerminalEquivUnique _).toFun terminal
    exact ⟨unique.default, trivial, fun _ _ => unique.uniq _⟩
  have hpair : StandardPairGluing X ((affineBasisToSmallAffineZariski B X hX).op ⋙ F.obj) := by
    intro U firstFunction secondFunction covering firstValue secondValue agreement
    have pullback := pullbacks
      ((affineBasisStandardSquare X U firstFunction secondFunction).map
        (affineBasisToSmallAffineZariski B X hX))
      (isStandardOpenCoverSquare_affineBasisStandardSquare B X hX U
        firstFunction secondFunction covering)
    obtain ⟨value, firstRestriction, secondRestriction⟩ :=
      Types.exists_of_isPullback pullback firstValue secondValue agreement
    refine ⟨value, ⟨firstRestriction, secondRestriction⟩, ?_⟩
    intro other restrictions
    exact Types.ext_of_isPullback pullback
      (restrictions.1.trans firstRestriction.symm)
      (restrictions.2.trans secondRestriction.symm)
  exact isSheaf_smallAffineZariski_of_isSheafFor_affineBasis B X hX F.obj
    fun cover arrows hcover => isSheafFor_affineBasis_cover X _ hempty hpair cover arrows hcover

/-- A sheaf for the almost chaotic topology on the affine opens of `X` is a sheaf for the Zariski
topology as soon as it turns every standard open cover square into a pullback. -/
theorem isSheaf_smallAffineZariski_of_almostChaotic
    (F : Sheaf (SmallAffineZariski.almostChaotic B X hX) (Type v))
    (pullbacks : ∀ sq : Square (SmallAffineZariski B X hX),
      SmallAffineZariski.IsStandardOpenCoverSquare B X hX sq →
        (sq.op.map F.obj).IsPullback) :
    Presheaf.IsSheaf (SmallAffineZariski.topology B X hX) F.obj :=
  isSheaf_smallAffineZariski_of_isPullback_standardOpenCoverSquare B X hX
    (fun _ hU => SmallAffineZariski.bot_mem_almostChaotic B X hX hU) F pullbacks

end AlgebraicGeometry

end
