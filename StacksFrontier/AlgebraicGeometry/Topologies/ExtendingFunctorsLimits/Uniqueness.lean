module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits.LimitCondition

/-!
# Extending functors from a full subcategory of schemes: restriction, existence and uniqueness

This file is the third of the three parts of
`StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits`. It identifies the
restriction of the extension `AlgebraicGeometry.ExtendingFunctors.extension` of `F` to the
subcategory `𝒞` with `F`, by covering an object of `𝒞` by its affine opens lying over affine
opens of `S` and gluing with condition (a), and deduces the existence and uniqueness of the
extension.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.affineExtensionToF`: the comparison of the colimit formula
  with `F` on an object of the subcategory.
* `AlgebraicGeometry.ExtendingFunctors.restrictionApp`,
  `AlgebraicGeometry.ExtendingFunctors.restrictionHom`: the identification of the restriction of
  the extension to the subcategory with `F`.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.existsUnique_glue_of_cover`: condition (a) for a covering
  by affine opens whose pairwise intersections are themselves covered by affine opens.
* `AlgebraicGeometry.ExtendingFunctors.nonempty_restrictionIso`: the restriction of the extension
  to the subcategory is `F`.
* `AlgebraicGeometry.ExtendingFunctors.exists_unique_extension`: the statement of Stacks 0EUW.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

/-! ### Condition (a) for a covering whose intersections are covered -/

section Glue

variable {P : ObjectProperty (Over S)}

/-- An object of `Sch/S` isomorphic to an affine object lying over an affine open of `S` is again
such an object. -/
lemma isAffineOverAffineOpen_of_iso {X Y : Over S} (e : X ≅ Y)
    (hX : IsAffineOverAffineOpen X) : IsAffineOverAffineOpen Y :=
  have : IsAffine X.left := hX.1
  isAffineOverAffineOpen_of_hom e.inv hX (IsAffine.of_isIso e.inv.left)

/-- **Condition (a) of Stacks 0EUW for a covering of an object of the subcategory by affine opens
whose pairwise intersections are themselves covered by affine opens.** The intersection of two
members of such a covering need not be affine, so the coverings `K i j` of the footnote of the
source are genuinely needed; they are the data recorded here. -/
theorem existsUnique_glue_of_cover {F : P.FullSubcategoryᵒᵖ ⥤ Type w}
    (haF : IsZariskiSheafOnSubcategory P F) {Z : Over S} (hZ : P Z) {ι : Type u}
    {V : ι → Z.left.Opens} (hV : ⨆ i, V i = ⊤) {A : ι → P.FullSubcategory}
    (e : ∀ i, overOpen Z (V i) ≅ (A i).obj) {K : ι → ι → Type u}
    {V₂ : ∀ i j, K i j → Z.left.Opens} {A₂ : ∀ i j, K i j → P.FullSubcategory}
    (e₂ : ∀ i j k, overOpen Z (V₂ i j k) ≅ (A₂ i j k).obj)
    (h₁ : ∀ i j k, V₂ i j k ≤ V i) (h₂ : ∀ i j k, V₂ i j k ≤ V j)
    (h₃ : ∀ i j, ⨆ k, (V i).ι ⁻¹ᵁ V₂ i j k = (V i).ι ⁻¹ᵁ V j)
    (s : ∀ i, F.obj (op (A i)))
    (hs : ∀ i j k, F.map (openLEHom (h₁ i j k) (e i) (e₂ i j k)).op (s i)
      = F.map (openLEHom (h₂ i j k) (e j) (e₂ i j k)).op (s j)) :
    ∃! t : F.obj (op (⟨Z, hZ⟩ : P.FullSubcategory)),
      ∀ i, F.map (openSubHom hZ (e i)).op t = s i := by
  refine haF ⟨Z, hZ⟩ ι A (fun i => openSubHom hZ (e i)) inferInstance ?_
    K (fun i j k => A₂ i j k) (fun i j k => openLEHom (h₁ i j k) (e i) (e₂ i j k))
    (fun i j k => openLEHom (h₂ i j k) (e j) (e₂ i j k)) inferInstance ?_ ?_ s ?_
  · simp only [opensRange_left_openSubHom]
    exact hV
  · intro i j k
    rw [openLEHom_comp_openSubHom, openLEHom_comp_openSubHom]
  · intro i j
    simp only [opensRange_left_openLEHom, opensRange_left_openSubHom,
      left_openSubHom hZ (e i), Scheme.Hom.comp_preimage]
    rw [← Scheme.Hom.preimage_iSup, h₃ i j]
  · intro i j k
    exact hs i j k

/-- **Separatedness of `F` on the subcategory.** Two sections over an object of the subcategory
which agree on the members of a covering as in `existsUnique_glue_of_cover` are equal. -/
theorem glue_ext {F : P.FullSubcategoryᵒᵖ ⥤ Type w} (haF : IsZariskiSheafOnSubcategory P F)
    {Z : Over S} (hZ : P Z) {ι : Type u} {V : ι → Z.left.Opens} (hV : ⨆ i, V i = ⊤)
    {A : ι → P.FullSubcategory} (e : ∀ i, overOpen Z (V i) ≅ (A i).obj) {K : ι → ι → Type u}
    {V₂ : ∀ i j, K i j → Z.left.Opens} {A₂ : ∀ i j, K i j → P.FullSubcategory}
    (e₂ : ∀ i j k, overOpen Z (V₂ i j k) ≅ (A₂ i j k).obj)
    (h₁ : ∀ i j k, V₂ i j k ≤ V i) (h₂ : ∀ i j k, V₂ i j k ≤ V j)
    (h₃ : ∀ i j, ⨆ k, (V i).ι ⁻¹ᵁ V₂ i j k = (V i).ι ⁻¹ᵁ V j)
    (t t' : F.obj (op (⟨Z, hZ⟩ : P.FullSubcategory)))
    (h : ∀ i, F.map (openSubHom hZ (e i)).op t = F.map (openSubHom hZ (e i)).op t') :
    t = t' := by
  obtain ⟨w, -, huniq⟩ := existsUnique_glue_of_cover haF hZ hV e e₂ h₁ h₂ h₃
    (fun i => F.map (openSubHom hZ (e i)).op t) (fun i j k => by
      rw [map_map_apply, map_map_apply, openLEHom_comp_openSubHom, openLEHom_comp_openSubHom])
  rw [huniq t fun i => rfl, huniq t' fun i => (h i).symm]

/-- **The covering of an object of the subcategory used to compare the extension with `F`.**
Every object `Z` of the subcategory is covered by affine opens lying over affine opens of `S`,
each isomorphic to an object of the subcategory, with all pairwise intersections again covered by
such opens; the covering may be chosen to refine any given open covering of `Z`. The covering is
indexed by the points of `Z`, so it is infinite in general: `Z` need not be quasi-compact, and
condition (a) allows arbitrary Zariski coverings. -/
theorem exists_coveringData (hP1 : HasAffineOpens P) {Z : Over S} (hZ : P Z)
    {M : Type u} (O : M → Z.left.Opens) (hO : ⨆ m, O m = ⊤) :
    ∃ (ι : Type u) (V : ι → Z.left.Opens) (A : ι → P.FullSubcategory)
      (_ : ∀ i, overOpen Z (V i) ≅ (A i).obj) (cv : ι → M) (K : ι → ι → Type u)
      (V₂ : ∀ i j, K i j → Z.left.Opens) (A₂ : ∀ i j, K i j → P.FullSubcategory)
      (_ : ∀ i j k, overOpen Z (V₂ i j k) ≅ (A₂ i j k).obj)
      (_ : ∀ i j k, V₂ i j k ≤ V i) (_ : ∀ i j k, V₂ i j k ≤ V j),
      (⨆ i, V i = ⊤) ∧ (∀ i, IsAffineOverAffineOpen (overOpen Z (V i))) ∧
        (∀ i, V i ≤ O (cv i)) ∧
        (∀ i j, ⨆ k, (V i).ι ⁻¹ᵁ V₂ i j k = (V i).ι ⁻¹ᵁ V j) ∧
        (∀ i j, ⨆ k, V₂ i j k = V i ⊓ V j) ∧
        ∀ i j k, IsAffineOverAffineOpen (overOpen Z (V₂ i j k)) := by
  classical
  have hmem : ∀ z : Z.left, ∃ m, z ∈ O m := by
    intro z
    have : z ∈ (⨆ m, O m) := by rw [hO]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp this
  choose cv hcv using hmem
  choose V hVaff hzV hVO hVover using fun z : Z.left =>
    exists_isAffineOverAffineOpen_nbhd Z z (O (cv z)) (hcv z)
  choose V₂ hV₂aff hzV₂ hV₂le hV₂over using fun (i j : Z.left) (k : ↥(V i ⊓ V j)) =>
    exists_isAffineOverAffineOpen_nbhd Z k.1 (V i ⊓ V j) k.2
  choose A hA eA using fun z : Z.left => hP1 Z hZ ⟨V z, hVaff z⟩
  choose A₂ hA₂ eA₂ using fun (i j : Z.left) (k : ↥(V i ⊓ V j)) =>
    hP1 Z hZ ⟨V₂ i j k, hV₂aff i j k⟩
  refine ⟨Z.left, V, fun z => ⟨A z, hA z⟩, fun z => (eA z).some, cv,
    fun i j => ↥(V i ⊓ V j), V₂, fun i j k => ⟨A₂ i j k, hA₂ i j k⟩,
    fun i j k => (eA₂ i j k).some, fun i j k => le_trans (hV₂le i j k) inf_le_left,
    fun i j k => le_trans (hV₂le i j k) inf_le_right, ?_, hVover, hVO, ?_, ?_, hV₂over⟩
  · refine le_antisymm le_top fun z _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzV z⟩
  · intro i j
    have hcovinf : ⨆ k : ↥(V i ⊓ V j), V₂ i j k = V i ⊓ V j := by
      refine le_antisymm (iSup_le fun k => hV₂le i j k) fun z hz => ?_
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV₂ i j ⟨z, hz⟩⟩
    rw [← Scheme.Hom.preimage_iSup, hcovinf, Scheme.Hom.preimage_inf,
      Scheme.Opens.ι_preimage_self, top_inf_eq]
  · intro i j
    refine le_antisymm (iSup_le fun k => hV₂le i j k) fun z hz => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV₂ i j ⟨z, hz⟩⟩

end Glue

/-! ### The canonical map from the colimit formula to `F` -/

section ToF

variable {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- **The canonical comparison of the colimit formula with `F` on the subcategory.** An arrow
from an object `Z` of the subcategory into an object of the subcategory which is locally of
finite presentation over `S` is a morphism of the subcategory, because the subcategory is full;
the induced maps assemble into a map `colim_{Z → V'} F(V') ⟶ F(Z)`. -/
noncomputable def affineExtensionToF (Z : P.FullSubcategory) :
    (affineExtension P F).obj (op Z.obj) ⟶ F.obj (op Z) :=
  colimit.desc _ (subcategoryCocone F Z.obj Z.property)

/-- The comparison map sends the class of a section `y` of `F` at an arrow `f` from `Z` to the
restriction of `y` along `f`, as a morphism of the subcategory. -/
@[simp]
lemma affineExtensionToF_affineExtensionι (Z : P.FullSubcategory)
    (A : (lfpPart P).FullSubcategory) (f : Z.obj ⟶ A.obj)
    (y : (lfpRestriction P F).obj (op A)) :
    affineExtensionToF F Z (affineExtensionι P F A f y)
      = F.map (ObjectProperty.homMk (X := Z) (Y := (lfpIncl P).obj A) f).op y :=
  ConcreteCategory.congr_hom (colimit.ι_desc (subcategoryCocone F Z.obj Z.property)
    (CostructuredArrow.mk (Y := op A) f.op)) y

/-- The comparison map is natural in the object of the subcategory. -/
lemma affineExtensionToF_naturality {Z Z' : P.FullSubcategory} (g : Z' ⟶ Z)
    (x : (affineExtension P F).obj (op Z.obj)) :
    affineExtensionToF F Z' ((affineExtension P F).map (P.ι.map g).op x)
      = F.map g.op (affineExtensionToF F Z x) := by
  obtain ⟨A, f, y, rfl⟩ := exists_affineExtensionι_eq_of_arrow F Z.obj x
  rw [affineExtensionι_naturality, affineExtensionToF_affineExtensionι,
    affineExtensionToF_affineExtensionι]
  refine Eq.trans (congrArg (fun h : Z' ⟶ (lfpIncl P).obj A => F.map (Quiver.Hom.op h) y)
    (P.ι.map_injective rfl :
      (ObjectProperty.homMk (X := Z') (Y := (lfpIncl P).obj A) (P.ι.map g ≫ f))
        = g ≫ ObjectProperty.homMk (X := Z) (Y := (lfpIncl P).obj A) f)) ?_
  exact (map_map_apply F g (ObjectProperty.homMk (X := Z) (Y := (lfpIncl P).obj A) f) y).symm

/-- **The colimit formula agrees with `F` on the affine objects of the subcategory lying over an
affine open of `S`.** -/
lemma isIso_affineExtensionToF (hP2 : HasFinitePresentationAffines P)
    (hbF : PreservesAffineLimitsOnSubcategory P F) (Z : P.FullSubcategory)
    (hZaff : IsAffineOverAffineOpen Z.obj) :
    IsIso (affineExtensionToF F Z) := by
  obtain ⟨h⟩ := nonempty_isColimit_subcategoryCocone F hP2 hbF Z.obj Z.property hZaff
  refine ⟨⟨h.desc (colimit.cocone _), colimit.hom_ext fun d => ?_, h.hom_ext fun d => ?_⟩⟩
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ h.desc (colimit.cocone _))
      (colimit.ι_desc (subcategoryCocone F Z.obj Z.property) d)) ?_
    refine Eq.trans (h.fac (colimit.cocone _) d) ?_
    exact (Category.comp_id _).symm
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ affineExtensionToF F Z)
      (h.fac (colimit.cocone _) d)) ?_
    refine Eq.trans (colimit.ι_desc (subcategoryCocone F Z.obj Z.property) d) ?_
    exact (Category.comp_id _).symm

/-- The comparison map is bijective on the affine objects of the subcategory lying over an affine
open of `S`. -/
lemma bijective_affineExtensionToF (hP2 : HasFinitePresentationAffines P)
    (hbF : PreservesAffineLimitsOnSubcategory P F) (Z : P.FullSubcategory)
    (hZaff : IsAffineOverAffineOpen Z.obj) :
    Function.Bijective (affineExtensionToF F Z) :=
  have := isIso_affineExtensionToF F hP2 hbF Z hZaff
  ConcreteCategory.bijective_of_isIso _

end ToF

/-! ### The restriction of the extension to the subcategory -/

section Restriction

variable {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- Restricting the comparison of the colimit formula with `F` along a morphism of the
subcategory. -/
lemma affineExtensionToF_extensionπ_comp {Z B B' : P.FullSubcategory}
    (hB : IsAffineOverAffineOpen B.obj) (hB' : IsAffineOverAffineOpen B'.obj) (k : B' ⟶ B)
    (g : B ⟶ Z) (t : (extension P F).obj (op Z.obj)) :
    F.map k.op (affineExtensionToF F B (extensionπ P F hB (P.ι.map g) t))
      = affineExtensionToF F B' (extensionπ P F hB' (P.ι.map (k ≫ g)) t) := by
  refine Eq.trans (affineExtensionToF_naturality F k (extensionπ P F hB (P.ι.map g) t)).symm ?_
  refine congrArg (fun z => affineExtensionToF F B' z) ?_
  refine Eq.trans (extensionπ_map P F hB hB' (P.ι.map k) (P.ι.map g) t) ?_
  exact congrArg (fun f => extensionπ P F hB' f t) (P.ι.map_comp k g).symm

/-- A morphism of the subcategory whose image lies in an open subobject identified with an object
of the subcategory factors through that object. -/
lemma exists_comp_openSubHom {Z : Over S} (hZ : P Z) {V : Z.left.Opens}
    {A : P.FullSubcategory} (e : overOpen Z V ≅ A.obj) {B : P.FullSubcategory}
    (h : B ⟶ (⟨Z, hZ⟩ : P.FullSubcategory))
    (hr : Set.range (⇑(P.ι.map h).left) ⊆ (V : Set Z.left)) :
    ∃ k : B ⟶ A, k ≫ openSubHom hZ e = h := by
  refine ⟨ObjectProperty.homMk (X := B) (Y := A)
    (liftOverOpen (P.ι.map h) V hr ≫ e.hom), P.ι.map_injective ?_⟩
  rw [Functor.map_comp]
  show (liftOverOpen (P.ι.map h) V hr ≫ e.hom) ≫ e.inv ≫ overOpenι Z V = P.ι.map h
  rw [Category.assoc, Iso.hom_inv_id_assoc, liftOverOpen_comp_overOpenι]

/-- **A section of `F` compatible with a section of the extension on a covering is compatible
with it everywhere.** If `s` and `t` correspond on the members of a covering of `Z` by affine
opens lying over affine opens of `S`, then they correspond along every morphism into `Z` out of
an affine object of the subcategory lying over an affine open of `S`: refine the covering of such
an object by the inverse images of the members of the given covering. -/
lemma restriction_spec_of_cover (hP1 : HasAffineOpens P)
    (haF : IsZariskiSheafOnSubcategory P F) {Z : P.FullSubcategory}
    (t : (extension P F).obj (op Z.obj)) (s : F.obj (op Z)) {ι : Type u}
    {V : ι → Z.obj.left.Opens} (hVcov : ⨆ i, V i = ⊤) {A : ι → P.FullSubcategory}
    (e : ∀ i, overOpen Z.obj (V i) ≅ (A i).obj)
    (hAover : ∀ i, IsAffineOverAffineOpen (A i).obj)
    (hs : ∀ i, F.map (openSubHom Z.property (e i)).op s
      = affineExtensionToF F (A i) (extensionπ P F (hAover i)
          (P.ι.map (openSubHom Z.property (e i))) t))
    (B : P.FullSubcategory) (hB : IsAffineOverAffineOpen B.obj) (g : B ⟶ Z) :
    F.map g.op s = affineExtensionToF F B (extensionπ P F hB (P.ι.map g) t) := by
  classical
  have hcov : ⨆ i, (P.ι.map g).left ⁻¹ᵁ V i = (⊤ : B.obj.left.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, hVcov]
    simp
  obtain ⟨ι', V', A', e', cv', K', V₂', A₂', e₂', h₁', h₂', hV'cov, hV'over, hV'le, h₃', -, -⟩ :=
    exists_coveringData hP1 B.property (fun i => (P.ι.map g).left ⁻¹ᵁ V i) hcov
  have hA'over : ∀ i', IsAffineOverAffineOpen (A' i').obj :=
    fun i' => isAffineOverAffineOpen_of_iso (e' i') (hV'over i')
  refine glue_ext haF B.property hV'cov e' e₂' h₁' h₂' h₃' _ _ fun i' => ?_
  have hrange : Set.range (⇑(P.ι.map (openSubHom B.property (e' i') ≫ g)).left)
      ⊆ ((V (cv' i') : Z.obj.left.Opens) : Set Z.obj.left) := by
    rintro _ ⟨y, rfl⟩
    have hz : ((e' i').inv.left ≫ (V' i').ι).base y ∈ V' i' := by
      have h : ((V' i').ι).base ((e' i').inv.left.base y) ∈ Set.range (⇑(V' i').ι) :=
        Set.mem_range_self _
      rwa [Scheme.Opens.range_ι] at h
    have h2 : (P.ι.map (openSubHom B.property (e' i') ≫ g)).left.base y
        = (P.ι.map g).left.base (((e' i').inv.left ≫ (V' i').ι).base y) := by
      rw [Functor.map_comp]
      rfl
    rw [h2]
    exact hV'le i' hz
  obtain ⟨k, hk⟩ := exists_comp_openSubHom Z.property (e (cv' i'))
    (openSubHom B.property (e' i') ≫ g) hrange
  refine Eq.trans (map_map_apply F (openSubHom B.property (e' i')) g s) ?_
  refine Eq.trans (congrArg (fun h : A' i' ⟶ Z => F.map (Quiver.Hom.op h) s) hk.symm) ?_
  refine Eq.trans (map_map_apply F k (openSubHom Z.property (e (cv' i'))) s).symm ?_
  refine Eq.trans (congrArg (fun z => F.map k.op z) (hs (cv' i'))) ?_
  refine Eq.trans (affineExtensionToF_extensionπ_comp F (hAover (cv' i')) (hA'over i') k
    (openSubHom Z.property (e (cv' i'))) t) ?_
  refine Eq.trans (congrArg (fun h : A' i' ⟶ Z => affineExtensionToF F (A' i')
    (extensionπ P F (hA'over i') (P.ι.map h) t)) hk) ?_
  exact (affineExtensionToF_extensionπ_comp F hB (hA'over i') (openSubHom B.property (e' i'))
    g t).symm

/-- **The restriction of the extension to the subcategory is `F`, pointwise.** A section of the
extension over an object `Z` of the subcategory determines a unique section of `F` over `Z` whose
restriction along every morphism into `Z` out of an affine object of the subcategory lying over
an affine open of `S` is computed by the colimit formula. Existence is the gluing of condition
(a) over the covering of `Z` by the affine opens lying over affine opens of `S`. -/
theorem existsUnique_restriction (hP1 : HasAffineOpens P)
    (haF : IsZariskiSheafOnSubcategory P F) (Z : P.FullSubcategory)
    (t : (extension P F).obj (op Z.obj)) :
    ∃! s : F.obj (op Z), ∀ (B : P.FullSubcategory) (hB : IsAffineOverAffineOpen B.obj)
      (g : B ⟶ Z), F.map g.op s
        = affineExtensionToF F B (extensionπ P F hB (P.ι.map g) t) := by
  classical
  obtain ⟨κ, V, A, e, -, K, V₂, A₂, e₂, h₁, h₂, hVcov, hVover, -, h₃, -, hV₂over⟩ :=
    exists_coveringData hP1 Z.property (fun _ : PUnit.{u + 1} => (⊤ : Z.obj.left.Opens)) (by simp)
  have hAover : ∀ i, IsAffineOverAffineOpen (A i).obj :=
    fun i => isAffineOverAffineOpen_of_iso (e i) (hVover i)
  have hA₂over : ∀ i j k, IsAffineOverAffineOpen (A₂ i j k).obj :=
    fun i j k => isAffineOverAffineOpen_of_iso (e₂ i j k) (hV₂over i j k)
  have hcompat : ∀ i j k,
      F.map (openLEHom (h₁ i j k) (e i) (e₂ i j k)).op
          (affineExtensionToF F (A i) (extensionπ P F (hAover i)
            (P.ι.map (openSubHom Z.property (e i))) t))
        = F.map (openLEHom (h₂ i j k) (e j) (e₂ i j k)).op
          (affineExtensionToF F (A j) (extensionπ P F (hAover j)
            (P.ι.map (openSubHom Z.property (e j))) t)) := by
    intro i j k
    refine Eq.trans (affineExtensionToF_extensionπ_comp F (hAover i) (hA₂over i j k)
      (openLEHom (h₁ i j k) (e i) (e₂ i j k)) (openSubHom Z.property (e i)) t) ?_
    refine Eq.trans (congrArg (fun h : A₂ i j k ⟶ Z => affineExtensionToF F (A₂ i j k)
      (extensionπ P F (hA₂over i j k) (P.ι.map h) t))
      (openLEHom_comp_openSubHom Z.property (h₁ i j k) (e i) (e₂ i j k))) ?_
    refine Eq.trans ?_ (affineExtensionToF_extensionπ_comp F (hAover j) (hA₂over i j k)
      (openLEHom (h₂ i j k) (e j) (e₂ i j k)) (openSubHom Z.property (e j)) t).symm
    exact congrArg (fun h : A₂ i j k ⟶ Z => affineExtensionToF F (A₂ i j k)
      (extensionπ P F (hA₂over i j k) (P.ι.map h) t))
      (openLEHom_comp_openSubHom Z.property (h₂ i j k) (e j) (e₂ i j k)).symm
  obtain ⟨s, hs, -⟩ := existsUnique_glue_of_cover haF Z.property hVcov e e₂ h₁ h₂ h₃
    (fun i => affineExtensionToF F (A i) (extensionπ P F (hAover i)
      (P.ι.map (openSubHom Z.property (e i))) t)) hcompat
  refine ⟨s, restriction_spec_of_cover F hP1 haF t s hVcov e hAover hs, fun s' hs' => ?_⟩
  refine glue_ext haF Z.property hVcov e e₂ h₁ h₂ h₃ s' s fun i => ?_
  rw [hs' (A i) (hAover i) (openSubHom Z.property (e i)), hs i]

/-- The section of `F` over an object of the subcategory attached to a section of the extension
there. -/
noncomputable def restrictionApp (hP1 : HasAffineOpens P)
    (haF : IsZariskiSheafOnSubcategory P F) (Z : P.FullSubcategory)
    (t : (extension P F).obj (op Z.obj)) : F.obj (op Z) :=
  (existsUnique_restriction F hP1 haF Z t).choose

/-- On every affine object of the subcategory lying over an affine open of `S`,
`restrictionApp F hP1 haF Z t` restricts to the section the colimit formula attaches to `t`. -/
lemma restrictionApp_spec (hP1 : HasAffineOpens P) (haF : IsZariskiSheafOnSubcategory P F)
    (Z : P.FullSubcategory) (t : (extension P F).obj (op Z.obj)) (B : P.FullSubcategory)
    (hB : IsAffineOverAffineOpen B.obj) (g : B ⟶ Z) :
    F.map g.op (restrictionApp F hP1 haF Z t)
      = affineExtensionToF F B (extensionπ P F hB (P.ι.map g) t) :=
  (existsUnique_restriction F hP1 haF Z t).choose_spec.1 B hB g

/-- `restrictionApp F hP1 haF Z t` is the only section of `F` over `Z` with the restrictions of
`restrictionApp_spec`. -/
lemma restrictionApp_unique (hP1 : HasAffineOpens P) (haF : IsZariskiSheafOnSubcategory P F)
    (Z : P.FullSubcategory) (t : (extension P F).obj (op Z.obj)) (s : F.obj (op Z))
    (hs : ∀ (B : P.FullSubcategory) (hB : IsAffineOverAffineOpen B.obj) (g : B ⟶ Z),
      F.map g.op s = affineExtensionToF F B (extensionπ P F hB (P.ι.map g) t)) :
    s = restrictionApp F hP1 haF Z t :=
  (existsUnique_restriction F hP1 haF Z t).choose_spec.2 s hs

/-- `restrictionApp` is natural in the object of the subcategory. -/
lemma restrictionApp_naturality (hP1 : HasAffineOpens P)
    (haF : IsZariskiSheafOnSubcategory P F) {Z Z' : P.FullSubcategory} (g : Z' ⟶ Z)
    (t : (extension P F).obj (op Z.obj)) :
    restrictionApp F hP1 haF Z' ((extension P F).map (P.ι.map g).op t)
      = F.map g.op (restrictionApp F hP1 haF Z t) := by
  refine (restrictionApp_unique F hP1 haF Z' _ _ fun B hB h => ?_).symm
  refine Eq.trans (map_map_apply F h g (restrictionApp F hP1 haF Z t)) ?_
  refine Eq.trans (restrictionApp_spec F hP1 haF Z t B hB (h ≫ g)) ?_
  refine congrArg (fun z => affineExtensionToF F B z) ?_
  refine Eq.trans (congrArg (fun f => extensionπ P F hB f t) (P.ι.map_comp h g)) ?_
  exact (extensionπ_naturality P F (P.ι.map g) hB (P.ι.map h) t).symm

/-- **The restriction of the extension to the subcategory maps to `F`.** -/
noncomputable def restrictionHom (hP1 : HasAffineOpens P)
    (haF : IsZariskiSheafOnSubcategory P F) : P.ι.op ⋙ extension P F ⟶ F where
  app Z := TypeCat.ofHom (restrictionApp F hP1 haF Z.unop)
  naturality Z Z' g := by
    ext t
    change restrictionApp F hP1 haF Z'.unop ((extension P F).map (P.ι.map g.unop).op t)
      = F.map g (restrictionApp F hP1 haF Z.unop t)
    exact restrictionApp_naturality F hP1 haF g.unop t

/-- Transporting the `𝟙`-component of the extension on an open subobject along an isomorphism
with an object of the subcategory gives the component along the induced morphism. -/
private lemma map_inv_extensionπ_id_map (Z : P.FullSubcategory) {V : Z.obj.left.Opens}
    {A : P.FullSubcategory} (e : overOpen Z.obj V ≅ A.obj)
    (hV : IsAffineOverAffineOpen (overOpen Z.obj V)) (hA : IsAffineOverAffineOpen A.obj)
    (u : (extension P F).obj (op Z.obj)) :
    (affineExtension P F).map e.inv.op
        (extensionπ P F hV (𝟙 _) ((extension P F).map (overOpenι Z.obj V).op u))
      = extensionπ P F hA (P.ι.map (openSubHom Z.property e)) u :=
  Eq.trans (congrArg (fun z => (affineExtension P F).map e.inv.op z)
    (extensionπ_id_map P F hV (overOpenι Z.obj V) u))
    (extensionπ_map P F hV hA e.inv (overOpenι Z.obj V) u)

/-- `restrictionApp` is injective. -/
lemma restrictionApp_injective (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) (Z : P.FullSubcategory) :
    Function.Injective (restrictionApp F hP1 haF Z) := by
  classical
  intro t t' htt'
  obtain ⟨κ, V, A, e, -, K, V₂, A₂, e₂, h₁, h₂, hVcov, hVover, -, h₃, -, -⟩ :=
    exists_coveringData hP1 Z.property (fun _ : PUnit.{u + 1} => (⊤ : Z.obj.left.Opens)) (by simp)
  have hAover : ∀ i, IsAffineOverAffineOpen (A i).obj :=
    fun i => isAffineOverAffineOpen_of_iso (e i) (hVover i)
  have hpieces : ∀ i, extensionπ P F (hAover i) (P.ι.map (openSubHom Z.property (e i))) t
      = extensionπ P F (hAover i) (P.ι.map (openSubHom Z.property (e i))) t' := by
    intro i
    refine (bijective_affineExtensionToF F hP2 hbF (A i) (hAover i)).1 ?_
    rw [← restrictionApp_spec F hP1 haF Z t (A i) (hAover i) (openSubHom Z.property (e i)),
      ← restrictionApp_spec F hP1 haF Z t' (A i) (hAover i) (openSubHom Z.property (e i)), htt']
  refine extension_ext_of_cover P F hP1 hP2 haF V hVcov t t' fun i => ?_
  refine extension_ext_of_affine P F (hVover i) _ _ ?_
  have hmono : ∀ z : (affineExtension P F).obj (op (overOpen Z.obj (V i))),
      (affineExtension P F).map (e i).hom.op
        ((affineExtension P F).map (e i).inv.op z) = z := by
    intro z
    refine Eq.trans (map_map_apply (affineExtension P F) (e i).hom (e i).inv z) ?_
    simp
  have hgoal : (affineExtension P F).map (e i).inv.op
        (extensionπ P F (hVover i) (𝟙 _) ((extension P F).map (overOpenι Z.obj (V i)).op t))
      = (affineExtension P F).map (e i).inv.op
        (extensionπ P F (hVover i) (𝟙 _)
          ((extension P F).map (overOpenι Z.obj (V i)).op t')) := by
    rw [map_inv_extensionπ_id_map F Z (e i) (hVover i) (hAover i) t,
      map_inv_extensionπ_id_map F Z (e i) (hVover i) (hAover i) t', hpieces i]
  refine Eq.trans (hmono _).symm (Eq.trans ?_ (hmono _))
  exact congrArg (fun z => (affineExtension P F).map (e i).hom.op z) hgoal

/-- `restrictionApp` is surjective. -/
lemma restrictionApp_surjective (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) (Z : P.FullSubcategory) :
    Function.Surjective (restrictionApp F hP1 haF Z) := by
  classical
  intro s
  obtain ⟨κ, V, A, e, -, K, V₂, A₂, e₂, h₁, h₂, hVcov, hVover, -, h₃, hV₂cov, hV₂over⟩ :=
    exists_coveringData hP1 Z.property (fun _ : PUnit.{u + 1} => (⊤ : Z.obj.left.Opens)) (by simp)
  have hAover : ∀ i, IsAffineOverAffineOpen (A i).obj :=
    fun i => isAffineOverAffineOpen_of_iso (e i) (hVover i)
  have hA₂over : ∀ i j k, IsAffineOverAffineOpen (A₂ i j k).obj :=
    fun i j k => isAffineOverAffineOpen_of_iso (e₂ i j k) (hV₂over i j k)
  obtain ⟨x, hx⟩ : ∃ x : ∀ i, (affineExtension P F).obj (op (A i).obj),
      ∀ i, affineExtensionToF F (A i) (x i) = F.map (openSubHom Z.property (e i)).op s := by
    choose x hx using fun i => (bijective_affineExtensionToF F hP2 hbF (A i) (hAover i)).2
      (F.map (openSubHom Z.property (e i)).op s)
    exact ⟨x, hx⟩
  have hxx : ∀ i j k, (affineExtension P F).map
        (P.ι.map (openLEHom (h₁ i j k) (e i) (e₂ i j k))).op (x i)
      = (affineExtension P F).map
        (P.ι.map (openLEHom (h₂ i j k) (e j) (e₂ i j k))).op (x j) := by
    intro i j k
    refine (bijective_affineExtensionToF F hP2 hbF (A₂ i j k) (hA₂over i j k)).1 ?_
    refine Eq.trans (affineExtensionToF_naturality F
      (openLEHom (h₁ i j k) (e i) (e₂ i j k)) (x i)) ?_
    refine Eq.trans ?_ (affineExtensionToF_naturality F
      (openLEHom (h₂ i j k) (e j) (e₂ i j k)) (x j)).symm
    rw [hx i, hx j, map_map_apply, map_map_apply, openLEHom_comp_openSubHom,
      openLEHom_comp_openSubHom]
  obtain ⟨tt, htt⟩ : ∃ tt : ∀ i, (extension P F).obj (op (overOpen Z.obj (V i))),
      ∀ i, extensionπ P F (hVover i) (𝟙 _) (tt i)
        = (affineExtension P F).map (e i).hom.op (x i) :=
    ⟨fun i => toExtension P F (hVover i) ((affineExtension P F).map (e i).hom.op (x i)),
      fun i => extensionπ_id_toExtension P F (hVover i) _⟩
  have hrestr : ∀ (i : κ) (W : Over S) (hW : IsAffineOverAffineOpen W)
      (f : W ⟶ overOpen Z.obj (V i)),
      extensionπ P F hW f (tt i)
        = (affineExtension P F).map (f ≫ (e i).hom).op (x i) := by
    intro i W hW f
    refine Eq.trans (congrArg (fun k => extensionπ P F hW k (tt i))
      (Category.comp_id f).symm) ?_
    refine Eq.trans (extensionπ_map P F (hVover i) hW f (𝟙 _) (tt i)).symm ?_
    refine Eq.trans (congrArg (fun z => (affineExtension P F).map f.op z) (htt i)) ?_
    exact map_map_apply (affineExtension P F) f (e i).hom (x i)
  have hcompat : ∀ i j : κ, (extension P F).map
        (overOpenLE Z.obj (inf_le_left : V i ⊓ V j ≤ V i)).op (tt i)
      = (extension P F).map
        (overOpenLE Z.obj (inf_le_right : V i ⊓ V j ≤ V j)).op (tt j) := by
    intro i j
    refine extension_ext P F _ _ fun W hW f => ?_
    have hWaff : IsAffine W.left := hW.1
    have hcovW : ⨆ k, (f ≫ overOpenι Z.obj (V i ⊓ V j)).left ⁻¹ᵁ V₂ i j k
        = (⊤ : W.left.Opens) := by
      rw [← Scheme.Hom.preimage_iSup, hV₂cov i j]
      simp
    obtain ⟨κ', hκ', U, cc, hUaff, hUle, hUcov⟩ := exists_finite_affine_refinement
      (fun k => (f ≫ overOpenι Z.obj (V i ⊓ V j)).left ⁻¹ᵁ V₂ i j k) hcovW
    refine Eq.trans (extensionπ_naturality P F
      (overOpenLE Z.obj (inf_le_left : V i ⊓ V j ≤ V i)) hW f (tt i)) ?_
    refine Eq.trans ?_ (extensionπ_naturality P F
      (overOpenLE Z.obj (inf_le_right : V i ⊓ V j ≤ V j)) hW f (tt j)).symm
    refine Eq.trans (hrestr i W hW
      (f ≫ overOpenLE Z.obj (inf_le_left : V i ⊓ V j ≤ V i))) ?_
    refine Eq.trans ?_ (hrestr j W hW
      (f ≫ overOpenLE Z.obj (inf_le_right : V i ⊓ V j ≤ V j))).symm
    refine affineExtension_ext P F hP1 hP2 haF hW U hUcov hUaff _ _ fun a => ?_
    have hr : Set.range (⇑(overOpenι W (U a) ≫ f ≫ overOpenι Z.obj (V i ⊓ V j)).left)
        ⊆ ((V₂ i j (cc a) : Z.obj.left.Opens) : Set Z.obj.left) := by
      rintro _ ⟨y, rfl⟩
      have hy : (U a).ι.base y ∈ U a := by
        have h : (U a).ι.base y ∈ Set.range (⇑(U a).ι) := Set.mem_range_self y
        rwa [Scheme.Opens.range_ι] at h
      exact hUle a hy
    have hfac : ∀ (i' : κ) (hle : V₂ i j (cc a) ≤ V i')
        (hle₂ : V i ⊓ V j ≤ V i'),
        overOpenι W (U a) ≫ (f ≫ overOpenLE Z.obj hle₂) ≫ (e i').hom
          = (liftOverOpen (overOpenι W (U a) ≫ f ≫ overOpenι Z.obj (V i ⊓ V j))
                (V₂ i j (cc a)) hr ≫ (e₂ i j (cc a)).hom)
            ≫ P.ι.map (openLEHom hle (e i') (e₂ i j (cc a))) := by
      intro i' hle hle₂
      refine eq_of_comp_openSub_eq (e i') ?_
      simp only [ι_map_openLEHom, Category.assoc, Iso.hom_inv_id_assoc,
        overOpenLE_comp_overOpenι, liftOverOpen_comp_overOpenι]
    refine Eq.trans (map_map_apply (affineExtension P F) (overOpenι W (U a))
      ((f ≫ overOpenLE Z.obj (inf_le_left : V i ⊓ V j ≤ V i)) ≫ (e i).hom) (x i)) ?_
    refine Eq.trans ?_ (map_map_apply (affineExtension P F) (overOpenι W (U a))
      ((f ≫ overOpenLE Z.obj (inf_le_right : V i ⊓ V j ≤ V j)) ≫ (e j).hom) (x j)).symm
    refine Eq.trans (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k) (x i))
      (hfac i (h₁ i j (cc a)) inf_le_left)) ?_
    refine Eq.trans ?_ (congrArg (fun k => (affineExtension P F).map (Quiver.Hom.op k) (x j))
      (hfac j (h₂ i j (cc a)) inf_le_right)).symm
    refine Eq.trans (map_map_apply (affineExtension P F) _
      (P.ι.map (openLEHom (h₁ i j (cc a)) (e i) (e₂ i j (cc a)))) (x i)).symm ?_
    refine Eq.trans ?_ (map_map_apply (affineExtension P F) _
      (P.ι.map (openLEHom (h₂ i j (cc a)) (e j) (e₂ i j (cc a)))) (x j)).symm.symm
    exact congrArg (fun z => (affineExtension P F).map
      (liftOverOpen (overOpenι W (U a) ≫ f ≫ overOpenι Z.obj (V i ⊓ V j))
        (V₂ i j (cc a)) hr ≫ (e₂ i j (cc a)).hom).op z) (hxx i j (cc a))
  obtain ⟨t, ht, -⟩ := isZariskiSheaf_extension P F hP1 hP2 haF Z.obj κ V hVcov tt hcompat
  refine ⟨t, ?_⟩
  refine (restrictionApp_unique F hP1 haF Z t s
    (restriction_spec_of_cover F hP1 haF t s hVcov e hAover fun i => ?_)).symm
  have hxi : extensionπ P F (hAover i) (P.ι.map (openSubHom Z.property (e i))) t = x i := by
    rw [← map_inv_extensionπ_id_map F Z (e i) (hVover i) (hAover i) t, ht i, htt i,
      map_map_apply (affineExtension P F) (e i).inv (e i).hom (x i)]
    simp
  rw [hxi, hx i]

/-- **The restriction of the extension to the subcategory is `F`.** This is the identification of
`F'` with `F` on `𝒞` asserted by Stacks 0EUW. There is no canonical map in either direction: the
object of `𝒞` is covered by its affine opens lying over affine opens of `S`, the extension is
computed there by the colimit formula, and the resulting sections of `F` are glued by condition
(a). The coverings of the pairwise intersections required by the footnote of the source are
genuinely needed, because an intersection of two members of the covering need not be affine. -/
theorem nonempty_restrictionIso (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) :
    Nonempty (P.ι.op ⋙ extension P F ≅ F) := by
  have hiso : ∀ Z : P.FullSubcategoryᵒᵖ, IsIso ((restrictionHom F hP1 haF).app Z) := by
    intro Z
    rw [isIso_iff_bijective]
    exact ⟨restrictionApp_injective F hP1 hP2 haF hbF Z.unop,
      restrictionApp_surjective F hP1 hP2 haF hbF Z.unop⟩
  exact ⟨NatIso.ofComponents (fun Z => @asIso _ _ _ _ _ (hiso Z))
    fun g => (restrictionHom F hP1 haF).naturality g⟩

end Restriction

/-! ### Existence and uniqueness of the extension -/

section Uniqueness

variable {P : ObjectProperty (Over S)}

/-- **Separatedness of a Zariski sheaf.** Two sections over an object of `Sch/S` which agree on
the members of an open covering are equal. -/
theorem zariskiSheaf_ext {G : (Over S)ᵒᵖ ⥤ Type w} (haG : IsZariskiSheaf G) {X : Over S}
    {ι : Type u} (V : ι → X.left.Opens) (hcov : ⨆ i, V i = ⊤) (t t' : G.obj (op X))
    (h : ∀ i, G.map (overOpenι X (V i)).op t = G.map (overOpenι X (V i)).op t') : t = t' := by
  obtain ⟨w, -, huniq⟩ := haG X ι V hcov
    (fun i => G.map (overOpenι X (V i)).op t) (fun i j => by
      rw [map_map_apply, map_map_apply, overOpenLE_comp_overOpenι, overOpenLE_comp_overOpenι])
  rw [huniq t fun i => rfl, huniq t' fun i => (h i).symm]

/-- Every object of `Sch/S` is covered by its affine opens lying over affine opens of `S`. -/
lemma exists_isAffineOverAffineOpen_cover (X : Over S) :
    ∃ (ι : Type u) (V : ι → X.left.Opens), (⨆ i, V i = ⊤) ∧
      ∀ i, IsAffineOverAffineOpen (overOpen X (V i)) := by
  classical
  choose V hVaff hzV hVle hVover using fun z : X.left =>
    exists_isAffineOverAffineOpen_nbhd X z ⊤ (Set.mem_univ z)
  refine ⟨X.left, V, ?_, hVover⟩
  refine le_antisymm le_top fun z _ => ?_
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzV z⟩

/-- **Stacks 0EUW.** For a scheme `S` and a full subcategory `𝒞` of `Sch/S` which contains, up to
isomorphism, the affine opens of its objects and the affine schemes of finite presentation over
the affine opens of `S`, a functor `F : 𝒞ᵒᵖ ⥤ Set` which is a Zariski sheaf and takes directed
inverse limits of affine objects to filtered colimits extends to `Sch/S` in a unique way: there
is a functor `F'` on `Sch/S` which is a Zariski sheaf, takes directed inverse limits of affine
schemes over `S` to filtered colimits, restricts to `F` on `𝒞`, and is isomorphic to any other
functor with these three properties. -/
@[stacks 0EUW]
theorem exists_unique_extension (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P)
    {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
    (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))) (_ : IsZariskiSheaf F')
      (_ : PreservesAffineLimits F') (_ : P.ι.op ⋙ F' ≅ F),
      ∀ (F'' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))), IsZariskiSheaf F'' →
        PreservesAffineLimits F'' → (P.ι.op ⋙ F'' ≅ F) → Nonempty (F' ≅ F'') := by
  classical
  refine ⟨extension P F, isZariskiSheaf_extension P F hP1 hP2 haF,
    preservesAffineLimits_extension F hP1 hP2 haF,
    (nonempty_restrictionIso F hP1 hP2 haF hbF).some, fun F'' ha₂ hb₂ β => ?_⟩
  -- the Kan extension properties of the two halves of the construction
  have hLan : (affineExtension P F).IsLeftKanExtension (affineExtensionUnit P F) :=
    inferInstanceAs ((Functor.pointwiseLeftKanExtension (lfpPart P).ι.op
      (lfpRestriction P F)).IsLeftKanExtension (Functor.pointwiseLeftKanExtensionUnit _ _))
  have hRan : (extension P F).IsRightKanExtension (extensionCounit P F) :=
    inferInstanceAs ((Functor.pointwiseRightKanExtension
      (IsAffineOverAffineOpen (S := S)).ι.op
      ((IsAffineOverAffineOpen (S := S)).ι.op ⋙ affineExtension P F)).IsRightKanExtension
      (Functor.pointwiseRightKanExtensionCounit _ _))
  set β' : lfpRestriction P F ⟶ (lfpPart P).ι.op ⋙ F'' :=
    Functor.whiskerLeft (lfpIncl P).op β.inv with hβ'
  have hβ'iso : ∀ A : (lfpPart P).FullSubcategory, IsIso (β'.app (op A)) := by
    intro A
    rw [hβ']
    exact NatIso.isIso_app_of_isIso β.inv _
  -- the comparison of the colimit formula with `F''`
  set α : affineExtension P F ⟶ F'' :=
    (affineExtension P F).descOfIsLeftKanExtension (affineExtensionUnit P F) F'' β' with hα'
  have hα : ∀ (Y : Over S) (A : (lfpPart P).FullSubcategory) (f : Y ⟶ A.obj)
      (y : (lfpRestriction P F).obj (op A)),
      α.app (op Y) (affineExtensionι P F A f y) = F''.map f.op (β'.app (op A) y) := by
    intro Y A f y
    have hfac : α.app (op A.obj) (affineExtensionι P F A (𝟙 A.obj) y) = β'.app (op A) y := by
      have h := ConcreteCategory.congr_hom (Functor.descOfIsLeftKanExtension_fac_app
        (affineExtension P F) (affineExtensionUnit P F) F'' β' (op A)) y
      show α.app (op A.obj) ((affineExtensionUnit P F).app (op A) y) = β'.app (op A) y
      simpa [hα'] using h
    have h1 : affineExtensionι P F A f y
        = (affineExtension P F).map f.op (affineExtensionι P F A (𝟙 A.obj) y) := by
      rw [affineExtensionι_naturality, Category.comp_id]
    rw [h1]
    refine Eq.trans ?_ (congrArg (fun z => F''.map f.op z) hfac)
    simp
  -- it is bijective on the affine objects lying over affine opens of `S`
  have hαbij : ∀ V : Over S, IsAffineOverAffineOpen V →
      Function.Bijective (α.app (op V)) := by
    intro V hV
    obtain ⟨Λ, _, _, _, D, c, hc, ci, haff⟩ := exists_lfpPresentation hP2 V hV
    have hcV : IsLimit (c.extend ci.inv) :=
      hc.ofIsoLimit (Cone.ext ci fun j => (Iso.hom_inv_id_assoc ci (c.π.app j)).symm)
    have hπ : ∀ l, (c.extend ci.inv).π.app l = ci.inv ≫ c.π.app l := fun l => rfl
    obtain ⟨hcol⟩ := hb₂ Λ (D ⋙ (lfpPart P).ι) (fun l => haff l) (c.extend ci.inv) hcV
    constructor
    · intro u u' huu'
      obtain ⟨l₁, y₁, hy₁⟩ := exists_affineExtensionι_eq c hc ci haff u
      obtain ⟨l₂, y₂, hy₂⟩ := exists_affineExtensionι_eq c hc ci haff u'
      obtain ⟨l, hl₁, hl₂⟩ := exists_ge_ge l₁ l₂
      set z₁ := (lfpRestriction P F).map (D.map (homOfLE hl₁).op).op y₁ with hz₁
      set z₂ := (lfpRestriction P F).map (D.map (homOfLE hl₂).op).op y₂ with hz₂
      have hu : affineExtensionι P F (D.obj (op l)) ((c.extend ci.inv).π.app (op l)) z₁ = u := by
        rw [hz₁, affineExtensionι_cone_map (c.extend ci.inv).π (homOfLE hl₁) y₁]
        exact hy₁
      have hu' : affineExtensionι P F (D.obj (op l)) ((c.extend ci.inv).π.app (op l)) z₂ = u' := by
        rw [hz₂, affineExtensionι_cone_map (c.extend ci.inv).π (homOfLE hl₂) y₂]
        exact hy₂
      have hkey : F''.map ((c.extend ci.inv).π.app (op l)).op (β'.app (op (D.obj (op l))) z₁)
          = F''.map ((c.extend ci.inv).π.app (op l)).op (β'.app (op (D.obj (op l))) z₂) := by
        rw [← hα V (D.obj (op l)) ((c.extend ci.inv).π.app (op l)) z₁,
          ← hα V (D.obj (op l)) ((c.extend ci.inv).π.app (op l)) z₂, hu, hu', huu']
      obtain ⟨m, hm, hmeq⟩ := exists_le_map_eq_of_isColimit_op F'' (D ⋙ (lfpPart P).ι)
        (c.extend ci.inv) hcol _ _ hkey
      have hnat : ∀ z : (lfpRestriction P F).obj (op (D.obj (op l))),
          F''.map ((D ⋙ (lfpPart P).ι).map (homOfLE hm).op).op
              (β'.app (op (D.obj (op l))) z)
            = β'.app (op (D.obj (op m)))
              ((lfpRestriction P F).map (D.map (homOfLE hm).op).op z) := by
        intro z
        simp
      rw [hnat, hnat] at hmeq
      have hz : (lfpRestriction P F).map (D.map (homOfLE hm).op).op z₁
          = (lfpRestriction P F).map (D.map (homOfLE hm).op).op z₂ :=
        (ConcreteCategory.bijective_of_isIso (β'.app (op (D.obj (op m))))).1 hmeq
      rw [← hu, ← hu', ← affineExtensionι_cone_map (c.extend ci.inv).π (homOfLE hm) z₁,
        ← affineExtensionι_cone_map (c.extend ci.inv).π (homOfLE hm) z₂, hz]
    · intro x
      obtain ⟨l, y, hy⟩ := exists_map_eq_of_isColimit_op F'' (D ⋙ (lfpPart P).ι)
        (c.extend ci.inv) hcol x
      obtain ⟨z, hz⟩ :=
        (ConcreteCategory.bijective_of_isIso (β'.app (op (D.obj (op l))))).2 y
      refine ⟨affineExtensionι P F (D.obj (op l)) ((c.extend ci.inv).π.app (op l)) z, ?_⟩
      rw [hα V (D.obj (op l)) ((c.extend ci.inv).π.app (op l)) z, hz]
      exact hy
  -- hence it is an isomorphism on the affine objects lying over affine opens of `S`
  have hαiso : ∀ V : (IsAffineOverAffineOpen (S := S)).FullSubcategoryᵒᵖ,
      IsIso (α.app (op V.unop.obj)) :=
    fun V => (isIso_iff_bijective _).2 (hαbij V.unop.obj V.unop.property)
  set γ : (IsAffineOverAffineOpen (S := S)).ι.op ⋙ affineExtension P F
      ≅ (IsAffineOverAffineOpen (S := S)).ι.op ⋙ F'' :=
    NatIso.ofComponents (fun V => @asIso _ _ _ _ _ (hαiso V))
      (fun g => α.naturality ((IsAffineOverAffineOpen (S := S)).ι.op.map g)) with hγ
  -- the comparison morphism into the extension
  set θ : F'' ⟶ extension P F :=
    (extension P F).liftOfIsRightKanExtension (extensionCounit P F) F'' γ.inv with hθ'
  have hθiso : ∀ (V : Over S) (hV : IsAffineOverAffineOpen V), IsIso (θ.app (op V)) := by
    intro V hV
    have h1 : θ.app (op V) ≫ (extensionCounit P F).app
          (op (⟨V, hV⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory))
        = γ.inv.app (op (⟨V, hV⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory)) :=
      Functor.liftOfIsRightKanExtension_fac_app (extension P F) (extensionCounit P F) F'' γ.inv
        (op (⟨V, hV⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory))
    have := isIso_extensionCounit P F
    have : IsIso (θ.app (op V) ≫ (extensionCounit P F).app
        (op (⟨V, hV⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory))) := by
      rw [h1]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((extensionCounit P F).app
      (op (⟨V, hV⟩ : (IsAffineOverAffineOpen (S := S)).FullSubcategory)))
  -- the comparison morphism is bijective everywhere, by the sheaf condition
  have hn : ∀ (Y Y' : Over S) (k : Y ⟶ Y') (u : F''.obj (op Y')),
      θ.app (op Y) (F''.map k.op u) = (extension P F).map k.op (θ.app (op Y') u) := by
    intro Y Y' k u
    simp
  have hθinj : ∀ X : Over S, Function.Injective (θ.app (op X)) := by
    intro X t t' htt'
    obtain ⟨ι, V, hVcov, hVover⟩ := exists_isAffineOverAffineOpen_cover X
    refine zariskiSheaf_ext ha₂ V hVcov t t' fun i => ?_
    have hi := hθiso (overOpen X (V i)) (hVover i)
    refine (ConcreteCategory.bijective_of_isIso (θ.app (op (overOpen X (V i))))).1 ?_
    rw [hn, hn, htt']
  have hθsurj : ∀ X : Over S, Function.Surjective (θ.app (op X)) := by
    intro X v
    obtain ⟨ι, V, hVcov, hVover⟩ := exists_isAffineOverAffineOpen_cover X
    have hbij : ∀ i, Function.Surjective (θ.app (op (overOpen X (V i)))) := fun i =>
      have := hθiso (overOpen X (V i)) (hVover i)
      (ConcreteCategory.bijective_of_isIso _).2
    choose s hs using fun i => hbij i ((extension P F).map (overOpenι X (V i)).op v)
    have hcompat : ∀ i j, F''.map (overOpenLE X (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)
        = F''.map (overOpenLE X (inf_le_right : V i ⊓ V j ≤ V j)).op (s j) := by
      intro i j
      refine hθinj (overOpen X (V i ⊓ V j)) ?_
      rw [hn, hn, hs i, hs j, map_map_apply, map_map_apply, overOpenLE_comp_overOpenι,
        overOpenLE_comp_overOpenι]
    obtain ⟨t, ht, -⟩ := ha₂ X ι V hVcov s hcompat
    refine ⟨t, ?_⟩
    refine zariskiSheaf_ext (isZariskiSheaf_extension P F hP1 hP2 haF) V hVcov _ _ fun i => ?_
    rw [← hn, ht i, hs i]
  have hθall : ∀ X : (Over S)ᵒᵖ, IsIso (θ.app X) :=
    fun X => (isIso_iff_bijective _).2 ⟨hθinj X.unop, hθsurj X.unop⟩
  exact ⟨(NatIso.ofComponents (fun X => @asIso _ _ _ _ _ (hθall X))
    fun g => θ.naturality g).symm⟩

end Uniqueness

end AlgebraicGeometry.ExtendingFunctors

end
