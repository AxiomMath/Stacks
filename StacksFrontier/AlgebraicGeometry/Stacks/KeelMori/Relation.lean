module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.MonoCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization

/-!
# The étale relation `∐ N i j ⇉ ∐ M i` of a Keel–Mori cover (Stacks 0DUT)

Let `C` be a Keel–Mori cover of an algebraic stack (`AlgebraicGeometry.Stack.KeelMoriCover`)
which is *small*: its index type and the charts of its members are bounded by one cardinal below
the cutoff of the site. This file shows that `N i j ⟶ M i ×_S M j` is a monomorphism, bounds the
sizes of the `M i` and `N i j`, and forms the disjoint unions `U = ∐ M i` and `R = ∐ N i j`
inside the site, with the étale morphisms `sR, tR : R ⟶ U` assembled from the `s i j` and
`t i j`.

## Main definitions

* `AlgebraicGeometry.Stack.KeelMoriCover.IsSmall`
* `AlgebraicGeometry.Stack.KeelMoriCover.U`, `.R`, `.ιU`, `.ιR`, `.sR`, `.tR`

## Main results

* `AlgebraicGeometry.Stack.KeelMoriCover.mono_jPair`
* `AlgebraicGeometry.Stack.KeelMoriCover.etale_sR`, `etale_tR`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

namespace AlgebraicGeometry

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Morphisms out of a disjoint open cover, and points of a field spectrum -/

/-- **A family of morphisms out of the members of a disjoint open cover glues.** -/
theorem BigFppfOver.exists_desc_of_disjoint_openCover {K : Type*} {T X : BigFppfOver B S hS}
    {W : K → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hoi : ∀ k, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p k)))
    (hdisj : ∀ k k', k ≠ k' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (W k))
      (y' : (BigFppfOver.toScheme B S hS).obj (W k')),
      (BigFppfOver.toScheme B S hS).map (p k) y ≠ (BigFppfOver.toScheme B S hS).map (p k') y')
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (φ : ∀ k, W k ⟶ X) : ∃ d : T ⟶ X, ∀ k, p k ≫ d = φ k := by
  have hsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS X)
  obtain ⟨τ, hτ⟩ := BigFppfOver.exists_section_of_disjoint_openCover hsheaf p hoi hdisj hcov φ
  exact ⟨τ, hτ⟩

/-- **Two points of an object of the site with values in a small field spectrum, agreeing over
`S`, come from morphisms of the site** out of one object whose underlying scheme is the field
spectrum. -/
theorem BigFppfOver.exists_homs_of_spec {X : BigFppfOver B S hS} {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k)))
    (a b : Spec (.of k) ⟶ (BigFppfOver.toScheme B S hS).obj X)
    (hab : a ≫ B.inclusion.map X.hom = b ≫ B.inclusion.map X.hom) :
    ∃ (V : BigFppfOver B S hS) (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
      (ah bh : V ⟶ X), (BigFppfOver.toScheme B S hS).map ah = e.hom ≫ a ∧
        (BigFppfOver.toScheme B S hS).map bh = e.hom ≫ b := by
  let V : BigFppfOver B S hS :=
    Space.schemeSiteObject B hS (X := Over.mk (a ≫ B.inclusion.map X.hom)) hk
  obtain ⟨ah, hah⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := V) (Y := X) a rfl
  obtain ⟨bh, hbh⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := V) (Y := X) b hab.symm
  exact ⟨V, Iso.refl _, ah, bh, by rw [hah]; exact (Category.id_comp a).symm,
    by rw [hbh]; exact (Category.id_comp b).symm⟩

namespace Stack.KeelMoriCover

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (C : KeelMoriCover B S hS 𝒳)

/-! ### Smallness -/

/-- A Keel–Mori cover is **small** when its index type and the charts of its members are bounded
by one cardinal below the cutoff of the site. -/
def IsSmall : Prop :=
  ∃ μ : Cardinal.{u}, ℵ₀ ≤ μ ∧ μ < B.cutoff ∧ #C.ι ≤ μ ∧
    ∀ i, ((BigFppfOver.toScheme B S hS).obj (C.chart i).U).size ≤ μ

/-- The moduli space of a member is no larger than its chart. -/
theorem size_M_le (i : C.ι) :
    ((BigFppfOver.toScheme B S hS).obj (C.M i)).size ≤
      ((BigFppfOver.toScheme B S hS).obj (C.chart i).U).size := by
  change (Spec (.of (invariantRing (C.chart i).groupoidScheme))).size ≤ _
  rw [Scheme.size_Spec]
  have : IsAffine (C.chart i).groupoidScheme.objects.left := inferInstance
  change _ ≤ Scheme.size (C.chart i).groupoidScheme.objects.left
  rw [Scheme.size_of_isAffine (C.chart i).groupoidScheme.objects.left]
  exact max_le_max le_rfl (Cardinal.mk_le_of_injective Subtype.val_injective)

/-! ### `N i j ⟶ M i ×_S M j` is a monomorphism -/

/-- The morphism of schemes `N i j ⟶ M i ×_S M j` given by `s i j` and `t i j`. -/
noncomputable def jPair (i j : C.ι) :
    (BigFppfOver.toScheme B S hS).obj (C.N i j) ⟶
      pullback (B.inclusion.map (C.M i).hom) (B.inclusion.map (C.M j).hom) :=
  pullback.lift ((BigFppfOver.toScheme B S hS).map (C.s i j))
    ((BigFppfOver.toScheme B S hS).map (C.t i j))
    ((BigFppfOver.toScheme_map_comp_hom _).trans (BigFppfOver.toScheme_map_comp_hom _).symm)

/-- The morphism `N i j ⟶ M i ×_S M j` is unramified. -/
instance unramified_jPair (i j : C.ι) : Unramified (C.jPair i j) := by
  have : Unramified (C.jPair i j ≫ pullback.fst _ _) := by
    rw [jPair, pullback.lift_fst]
    exact unramified_of_etale _
  exact unramified_of_comp (C.jPair i j) (pullback.fst _ _)

/-- **`N i j ⟶ M i ×_S M j` is a monomorphism**: it is unramified and injective on geometric
points (`AlgebraicGeometry.Stack.KeelMoriCover.eq_of_comp_s_eq_of_comp_t_eq`). -/
instance mono_jPair (i j : C.ι) : Mono (C.jPair i j) := by
  refine mono_of_unramified_of_injective_geometricPoints (C.jPair i j) B.aleph0_lt_cutoff
    (Scheme.size_pullback_lt _ _ (C.N i j).left.2 (C.N i j).left.2) ?_
  intro k _ _ hk a b hab
  have hs : a ≫ (BigFppfOver.toScheme B S hS).map (C.s i j) =
      b ≫ (BigFppfOver.toScheme B S hS).map (C.s i j) := by
    have := congrArg (· ≫ pullback.fst _ _) hab
    simp only [Category.assoc, jPair, pullback.lift_fst] at this
    exact this
  have ht : a ≫ (BigFppfOver.toScheme B S hS).map (C.t i j) =
      b ≫ (BigFppfOver.toScheme B S hS).map (C.t i j) := by
    have := congrArg (· ≫ pullback.snd _ _) hab
    simp only [Category.assoc, jPair, pullback.lift_snd] at this
    exact this
  obtain ⟨V, e, ah, bh, hah, hbh⟩ := BigFppfOver.exists_homs_of_spec hk a b (by
    rw [← BigFppfOver.toScheme_map_comp_hom (C.s i j), ← Category.assoc, hs, Category.assoc])
  have key := C.eq_of_comp_s_eq_of_comp_t_eq k V e ah bh
    ((BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hah, hbh, Category.assoc, Category.assoc, hs]))
    ((BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hah, hbh, Category.assoc, Category.assoc, ht]))
  have : e.hom ≫ a = e.hom ≫ b := by rw [← hah, ← hbh, key]
  simpa using this

/-- A cardinal is at most its double power set. -/
private theorem le_two_pow_two_pow (μ : Cardinal.{u}) :
    μ ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ μ :=
  (cantor μ).le.trans (cantor _).le

/-- **A bound on `N i j`** in terms of bounds on `M i` and `M j`. -/
theorem size_N_le {i j : C.ι} {μ : Cardinal.{u}} (_hℵ : ℵ₀ ≤ μ)
    (hi : ((BigFppfOver.toScheme B S hS).obj (C.M i)).size ≤ μ)
    (hj : ((BigFppfOver.toScheme B S hS).obj (C.M j)).size ≤ μ) :
    ((BigFppfOver.toScheme B S hS).obj (C.N i j)).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ μ := by
  have hY := (Scheme.size_pullback_le (B.inclusion.map (C.M i).hom)
    (B.inclusion.map (C.M j).hom)).trans (max_le hi hj)
  refine (Scheme.size_le_of_mono (C.jPair i j)).trans (max_le ?_ ?_)
  · exact power_le_power_left two_ne_zero ((Scheme.mk_le_two_pow_size _).trans
      (power_le_power_left two_ne_zero hY))
  · exact hY.trans (le_two_pow_two_pow μ)

/-! ### The disjoint unions `U = ∐ M i` and `R = ∐ N i j` -/

/-- The family `(i, j) ↦ N i j`. -/
noncomputable abbrev Nfam (p : C.ι × C.ι) : BigFppfOver B S hS := C.N p.1 p.2

variable {C} (hC : C.IsSmall)

/-- The bound of a small Keel–Mori cover. -/
noncomputable def bound : Cardinal.{u} := hC.choose

/-- The bound of a small Keel–Mori cover is infinite. -/
theorem aleph0_le_bound : ℵ₀ ≤ bound hC := hC.choose_spec.1

/-- The bound of a small Keel–Mori cover is below the cutoff of the site. -/
theorem bound_lt : bound hC < B.cutoff := hC.choose_spec.2.1

/-- The index type of a small Keel–Mori cover has cardinality at most its bound. -/
theorem mk_ι_le_bound : #C.ι ≤ bound hC := hC.choose_spec.2.2.1

/-- Each `M i` of a small Keel–Mori cover has size at most the bound. -/
theorem size_M_le_bound (i : C.ι) :
    ((BigFppfOver.toScheme B S hS).obj (C.M i)).size ≤ bound hC :=
  (C.size_M_le i).trans (hC.choose_spec.2.2.2 i)

/-- The bound on the pieces of the relation. -/
noncomputable def bound₂ : Cardinal.{u} := (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ bound hC

/-- The cardinal `bound₂` is infinite. -/
theorem aleph0_le_bound₂ : ℵ₀ ≤ bound₂ hC :=
  (aleph0_le_bound hC).trans (le_two_pow_two_pow _)

/-- The cardinal `bound₂` is below the cutoff of the site. -/
theorem bound₂_lt : bound₂ hC < B.cutoff :=
  B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (bound_lt hC))

/-- The index type `ι × ι` of the pieces `N i j` has cardinality at most `bound₂`. -/
theorem mk_ι_prod_le_bound₂ : #(C.ι × C.ι) ≤ bound₂ hC := by
  rw [mk_prod, lift_id]
  exact (mul_le_mul' (mk_ι_le_bound hC) (mk_ι_le_bound hC)).trans
    ((mul_eq_self (aleph0_le_bound hC)).le.trans (le_two_pow_two_pow _))

/-- Each `N i j` of a small Keel–Mori cover has size at most `bound₂`. -/
theorem size_N_le_bound₂ (p : C.ι × C.ι) :
    ((BigFppfOver.toScheme B S hS).obj (C.Nfam p)).size ≤ bound₂ hC :=
  C.size_N_le (aleph0_le_bound hC) (size_M_le_bound hC p.1) (size_M_le_bound hC p.2)

include hC in
/-- There is an object `Z` of the site with morphisms `M i ⟶ Z` that are open immersions with
pairwise disjoint images covering `Z`. -/
theorem exists_U :
    ∃ (Z : BigFppfOver B S hS) (c : ∀ k, C.M k ⟶ Z),
      (∀ k, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (c k))) ∧
      (∀ k k', k ≠ k' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (C.M k))
        (y' : (BigFppfOver.toScheme B S hS).obj (C.M k')),
        (BigFppfOver.toScheme B S hS).map (c k) y ≠ (BigFppfOver.toScheme B S hS).map (c k') y') ∧
      (∀ z : (BigFppfOver.toScheme B S hS).obj Z,
        ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (c k))) :=
  BigFppfOver.exists_coproduct_of_size_le B S hS C.M (aleph0_le_bound hC) (bound_lt hC)
    (mk_ι_le_bound hC) (size_M_le_bound hC)

include hC in
/-- **`U = ∐ M i`**, inside the site. -/
noncomputable def U : BigFppfOver B S hS := (exists_U hC).choose

/-- The inclusion `M i ⟶ U`. -/
noncomputable def ιU (i : C.ι) : C.M i ⟶ U hC := (exists_U hC).choose_spec.choose i

/-- The inclusion `M i ⟶ U` is an open immersion. -/
instance isOpenImmersion_ιU (i : C.ι) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ιU hC i)) :=
  (exists_U hC).choose_spec.choose_spec.1 i

/-- For `i ≠ i'`, the images of `M i` and `M i'` in `U` are disjoint. -/
theorem disjoint_ιU {i i' : C.ι} (h : i ≠ i') (y : (BigFppfOver.toScheme B S hS).obj (C.M i))
    (y' : (BigFppfOver.toScheme B S hS).obj (C.M i')) :
    (BigFppfOver.toScheme B S hS).map (ιU hC i) y ≠
      (BigFppfOver.toScheme B S hS).map (ιU hC i') y' :=
  (exists_U hC).choose_spec.choose_spec.2.1 i i' h y y'

/-- Every point of `U` lies in the image of some `M i`. -/
theorem cover_ιU (z : (BigFppfOver.toScheme B S hS).obj (U hC)) :
    ∃ i, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ιU hC i)) :=
  (exists_U hC).choose_spec.choose_spec.2.2 z

include hC in
/-- There is an object `Z` of the site with morphisms `N i j ⟶ Z` that are open immersions with
pairwise disjoint images covering `Z`. -/
theorem exists_R :
    ∃ (Z : BigFppfOver B S hS) (c : ∀ k : C.ι × C.ι, C.Nfam k ⟶ Z),
      (∀ k, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (c k))) ∧
      (∀ k k', k ≠ k' → ∀ (y : (BigFppfOver.toScheme B S hS).obj (C.Nfam k))
        (y' : (BigFppfOver.toScheme B S hS).obj (C.Nfam k')),
        (BigFppfOver.toScheme B S hS).map (c k) y ≠ (BigFppfOver.toScheme B S hS).map (c k') y') ∧
      (∀ z : (BigFppfOver.toScheme B S hS).obj Z,
        ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (c k))) :=
  BigFppfOver.exists_coproduct_of_size_le B S hS C.Nfam
    (aleph0_le_bound₂ hC) (bound₂_lt hC) (mk_ι_prod_le_bound₂ hC) (size_N_le_bound₂ hC)

include hC in
/-- **`R = ∐ N i j`**, inside the site. -/
noncomputable def R : BigFppfOver B S hS := (exists_R hC).choose

/-- The inclusion `N i j ⟶ R`. -/
noncomputable def ιR (p : C.ι × C.ι) : C.N p.1 p.2 ⟶ R hC := (exists_R hC).choose_spec.choose p

/-- The inclusion `N i j ⟶ R` is an open immersion. -/
instance isOpenImmersion_ιR (p : C.ι × C.ι) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ιR hC p)) :=
  (exists_R hC).choose_spec.choose_spec.1 p

/-- For distinct index pairs `p ≠ p'`, the images of the corresponding pieces in `R` are
disjoint. -/
theorem disjoint_ιR {p p' : C.ι × C.ι} (h : p ≠ p')
    (y : (BigFppfOver.toScheme B S hS).obj (C.N p.1 p.2))
    (y' : (BigFppfOver.toScheme B S hS).obj (C.N p'.1 p'.2)) :
    (BigFppfOver.toScheme B S hS).map (ιR hC p) y ≠
      (BigFppfOver.toScheme B S hS).map (ιR hC p') y' :=
  (exists_R hC).choose_spec.choose_spec.2.1 p p' h y y'

/-- Every point of `R` lies in the image of some `N i j`. -/
theorem cover_ιR (z : (BigFppfOver.toScheme B S hS).obj (R hC)) :
    ∃ p, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ιR hC p)) :=
  (exists_R hC).choose_spec.choose_spec.2.2 z

/-- Two morphisms out of `U` agreeing on every `M i` are equal. -/
theorem hom_ext_U {X : BigFppfOver B S hS} {h₁ h₂ : U hC ⟶ X}
    (h : ∀ i, ιU hC i ≫ h₁ = ιU hC i ≫ h₂) : h₁ = h₂ :=
  BigFppfOver.hom_ext_of_openCover (ιU hC) (isOpenImmersion_ιU hC) (cover_ιU hC) h

/-- Two morphisms out of `R` agreeing on every `N i j` are equal. -/
theorem hom_ext_R {X : BigFppfOver B S hS} {h₁ h₂ : R hC ⟶ X}
    (h : ∀ p, ιR hC p ≫ h₁ = ιR hC p ≫ h₂) : h₁ = h₂ :=
  BigFppfOver.hom_ext_of_openCover (ιR hC) (isOpenImmersion_ιR hC) (cover_ιR hC) h

/-- A family of morphisms `M i ⟶ X` extends to a morphism `U ⟶ X`. -/
theorem exists_desc_U {X : BigFppfOver B S hS} (φ : ∀ i, C.M i ⟶ X) :
    ∃ d : U hC ⟶ X, ∀ i, ιU hC i ≫ d = φ i :=
  BigFppfOver.exists_desc_of_disjoint_openCover (ιU hC) (isOpenImmersion_ιU hC)
    (fun _ _ h => disjoint_ιU hC h) (cover_ιU hC) φ

/-- A family of morphisms `N i j ⟶ X` extends to a morphism `R ⟶ X`. -/
theorem exists_desc_R {X : BigFppfOver B S hS} (φ : ∀ p : C.ι × C.ι, C.N p.1 p.2 ⟶ X) :
    ∃ d : R hC ⟶ X, ∀ p, ιR hC p ≫ d = φ p :=
  BigFppfOver.exists_desc_of_disjoint_openCover (ιR hC) (isOpenImmersion_ιR hC)
    (fun _ _ h => disjoint_ιR hC h) (cover_ιR hC) φ

/-- **The source map `sR : R ⟶ U`**, equal to `s i j` on `N i j`. -/
noncomputable def sR : R hC ⟶ U hC :=
  (exists_desc_R hC fun p => C.s p.1 p.2 ≫ ιU hC p.1).choose

/-- The restriction of `sR` to `N i j` is `s i j` followed by the inclusion `M i ⟶ U`. -/
theorem ιR_sR (p : C.ι × C.ι) : ιR hC p ≫ sR hC = C.s p.1 p.2 ≫ ιU hC p.1 :=
  (exists_desc_R hC fun p => C.s p.1 p.2 ≫ ιU hC p.1).choose_spec p

/-- **The target map `tR : R ⟶ U`**, equal to `t i j` on `N i j`. -/
noncomputable def tR : R hC ⟶ U hC :=
  (exists_desc_R hC fun p => C.t p.1 p.2 ≫ ιU hC p.2).choose

/-- The restriction of `tR` to `N i j` is `t i j` followed by the inclusion `M j ⟶ U`. -/
theorem ιR_tR (p : C.ι × C.ι) : ιR hC p ≫ tR hC = C.t p.1 p.2 ≫ ιU hC p.2 :=
  (exists_desc_R hC fun p => C.t p.1 p.2 ≫ ιU hC p.2).choose_spec p

/-- The open cover of `R` by the `N i j`, on underlying schemes. -/
noncomputable def openCoverR : ((BigFppfOver.toScheme B S hS).obj (R hC)).OpenCover :=
  Scheme.Cover.mkOfCovers (C.ι × C.ι) (fun p => (BigFppfOver.toScheme B S hS).obj (C.N p.1 p.2))
    (fun p => (BigFppfOver.toScheme B S hS).map (ιR hC p)) (fun z => by
      obtain ⟨p, y, hy⟩ := cover_ιR hC z
      exact ⟨p, y, hy⟩)

/-- The source map `sR : R ⟶ U` is étale. -/
instance etale_sR : Etale ((BigFppfOver.toScheme B S hS).map (sR hC)) := by
  refine IsZariskiLocalAtSource.of_openCover (openCoverR hC) fun (p : C.ι × C.ι) => ?_
  change Etale ((BigFppfOver.toScheme B S hS).map (ιR hC p) ≫
    (BigFppfOver.toScheme B S hS).map (sR hC))
  rw [← Functor.map_comp, ιR_sR, Functor.map_comp]
  infer_instance

/-- The target map `tR : R ⟶ U` is étale. -/
instance etale_tR : Etale ((BigFppfOver.toScheme B S hS).map (tR hC)) := by
  refine IsZariskiLocalAtSource.of_openCover (openCoverR hC) fun (p : C.ι × C.ι) => ?_
  change Etale ((BigFppfOver.toScheme B S hS).map (ιR hC p) ≫
    (BigFppfOver.toScheme B S hS).map (tR hC))
  rw [← Functor.map_comp, ιR_tR, Functor.map_comp]
  infer_instance

end Stack.KeelMoriCover

end AlgebraicGeometry

end
