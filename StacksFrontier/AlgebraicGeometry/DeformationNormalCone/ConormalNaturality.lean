module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNestedZeroSection
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf

/-!
# The canonical map of conormal algebras on pulled-back Rees sections

Let `i : Z ⟶ X` be an immersion with closed-immersion part `g : Z ⟶ U` and ideal `ℐ`. A local
section `x` of `ℐⁿ` pulls back to a section `g^*x` of the conormal algebra `𝒞_{Z/X,n}`. On an
affine chart this pulled-back section is the class of `x` in `ℐⁿ/ℐⁿ⁺¹`
(`Stacks.Deformation.restrict_pullbackSection_eq_localMap`).

For a commutative square of closed immersions `f ≫ i' = i ≫ g` the canonical morphism of
conormal algebras of [Stacks, Tag 0634] sends the class of a section to the class of its image
under `g^♯`. Read on pulled-back Rees sections: it sends `g'^*x` to `g^*(h^♯ x)`, where `h` is the
map of the coborders (`Stacks.Deformation.conormalAlgebraHom_map_pullbackSection`).

The closed immersion `κ : C_ZX ⟶ D(Z ⊆ X)` of the normal cone into the deformation space is
natural for such squares (`Stacks.Deformation.normalConeToDeformation_comp_deformationMap`), with
no affineness assumption on the map of coborders: `κ` is read on homogeneous sections over an
arbitrary open (`Stacks.Deformation.normalConeToDeformation_appLE_chartIncl_of_opens`), through
the sections of the morphism attached to a relative-spectrum pair over every open of the base
(`Stacks.RelativeSpec.pairToHom_appLE_of_opens`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.Blowup Stacks.Conormal
  Stacks.SymAlgSheaf

universe u

namespace Stacks.Deformation

/-- Restriction along two inclusions into one open whose sources are equal opens differ by the
transport along that equality. -/
theorem map_homOfLE_eq_cast {T : Scheme.{u}} (M : T.Modules) {A B C : T.Opens} (hAB : A = B)
    (hA : A ≤ C) (hB : B ≤ C) (x : M.val.obj (op C)) :
    M.val.map (homOfLE hB).op x =
      AddEquiv.cast (M := fun S : T.Opens => M.val.obj (op S)) hAB
        (M.val.map (homOfLE hA).op x) := by
  subst hAB
  rfl

section Bridge

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **On an affine chart, the pullback of a section of `ℐⁿ` to the conormal algebra is its
class in `ℐⁿ/ℐⁿ⁺¹`**, i.e. the local presentation `localMap` of the conormal algebra. -/
theorem restrict_pullbackSection_eq_localMap (n : ℕ) (W : i.coborderRange.toScheme.Opens)
    (x : (reesPiece (coborderIdeal i) (n : ℤ)).val.obj (op W)) (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hUW : i.coborderRange.ι ⁻¹ᵁ U.1 ≤ W)
    (hle : i ⁻¹ᵁ U.1 ≤ i.liftCoborder ⁻¹ᵁ W)
    (a : ↥(chartIdeal i U ^ n))
    (ha : (i.coborderRange.ι.app U.1).hom a = reesPieceAmbient (coborderIdeal i) (n : ℤ)
      (i.coborderRange.ι ⁻¹ᵁ U.1)
      ((reesPiece (coborderIdeal i) (n : ℤ)).val.map (homOfLE hUW).op x)) :
    ((conormalAlgebra i).algebra.piece (n : ℤ)).val.map (homOfLE hle).op
        (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ)) W
          (i.liftCoborder ⁻¹ᵁ W) le_rfl x) =
      (conormalAlgebra i).localMap U hU n a := by
  have hUW' : (coborderAffineChart i U hU).1 ≤ W := by
    rwa [coborderAffineChart_coe]
  have hZ : i.liftCoborder ⁻¹ᵁ (coborderAffineChart i U hU).1 ≤ i.liftCoborder ⁻¹ᵁ W :=
    Scheme.Hom.preimage_mono _ hUW'
  have hcast := map_homOfLE_eq_cast ((conormalAlgebra i).algebra.piece (n : ℤ))
    (coborderAffineChart_preimage i U hU) hZ hle
    (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ)) W
      (i.liftCoborder ⁻¹ᵁ W) le_rfl x)
  refine hcast.trans ?_
  have hres := pullbackSection_restrict i.liftCoborder (reesModule (coborderIdeal i) (n : ℤ))
    hUW' hZ x
  have hsec : (reesPiece (coborderIdeal i) (n : ℤ)).val.map (homOfLE hUW').op x =
      reesSection (coborderIdeal i) n (coborderAffineChart i U hU)
        (coborderPowerEquiv i U hU n a) := by
    refine (reesPieceAffineEquiv (coborderIdeal i) (n : ℤ) (Int.natCast_nonneg n)
      (coborderAffineChart i U hU)).injective (Subtype.ext ?_)
    refine (reesPieceAffineEquiv_coe _ _ _ _ _).trans ?_
    have ha' : coborderSectionEquiv i U hU a = reesPieceAmbient (coborderIdeal i) (n : ℤ)
        (coborderAffineChart i U hU).1
        ((reesPiece (coborderIdeal i) (n : ℤ)).val.map (homOfLE hUW').op x) := ha
    refine ha'.symm.trans ?_
    exact (reesSection_coe (coborderIdeal i) n (coborderAffineChart i U hU)
      (coborderPowerEquiv i U hU n a)).symm
  show _ = AddEquiv.cast (M := fun W : Z.Opens =>
      ((conormalGradedAlgebra i).piece (n : ℤ)).val.obj (op W))
    (coborderAffineChart_preimage i U hU)
    (reesPullbackMap (coborderIdeal i) i.liftCoborder n (coborderAffineChart i U hU)
      (coborderPowerEquiv i U hU n a))
  exact congrArg (AddEquiv.cast (M := fun W : Z.Opens =>
      ((conormalGradedAlgebra i).piece (n : ℤ)).val.obj (op W))
    (coborderAffineChart_preimage i U hU)) (hres.trans (congrArg _ hsec))

/-- On an affine chart, a section of `ℐⁿ` is represented by an element of the `n`-th power of the
ideal of the chart. -/
private theorem exists_chartIdeal_pow_app_eq (n : ℕ) (W : i.coborderRange.toScheme.Opens)
    (x : (reesPiece (coborderIdeal i) (n : ℤ)).val.obj (op W)) (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hUW : i.coborderRange.ι ⁻¹ᵁ U.1 ≤ W) :
    ∃ a : ↥(chartIdeal i U ^ n), (i.coborderRange.ι.app U.1).hom a =
      reesPieceAmbient (coborderIdeal i) (n : ℤ) (i.coborderRange.ι ⁻¹ᵁ U.1)
        ((reesPiece (coborderIdeal i) (n : ℤ)).val.map (homOfLE hUW).op x) := by
  have hmem : reesPieceAmbient (coborderIdeal i) (n : ℤ) (i.coborderRange.ι ⁻¹ᵁ U.1)
      ((reesPiece (coborderIdeal i) (n : ℤ)).val.map (homOfLE hUW).op x) ∈
      (coborderIdeal i).ideal (coborderAffineChart i U hU) ^ n :=
    reesPieceAmbient_mem_affine (coborderIdeal i) (n : ℤ) (Int.natCast_nonneg n)
      (coborderAffineChart i U hU) _
  exact ⟨_, congrArg Subtype.val ((coborderPowerEquiv i U hU n).apply_symm_apply ⟨_, hmem⟩)⟩

/-- An open of `X` whose inverse image in the coborder lies in `W` has inverse image in `Z`
inside the inverse image of `W`. -/
private theorem preimage_le_preimage_liftCoborder {U : X.Opens}
    {W : i.coborderRange.toScheme.Opens} (h : i.coborderRange.ι ⁻¹ᵁ U ≤ W) :
    i ⁻¹ᵁ U ≤ i.liftCoborder ⁻¹ᵁ W := by
  intro y hy
  apply h
  show i.coborderRange.ι (i.liftCoborder y) ∈ U
  have h2 := congrArg (fun q : Z ⟶ X => q y) i.liftCoborder_ι
  simp only [Scheme.Hom.comp_apply] at h2
  rw [h2]
  exact hy

end Bridge

section Square

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
  [IsClosedImmersion i] [IsClosedImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X')
  (comm : f ≫ i' = i ≫ g)
  (gU : i.coborderRange.toScheme ⟶ i'.coborderRange.toScheme)
  (hgU : gU ≫ i'.coborderRange.ι = i.coborderRange.ι ≫ g)
  (hJ : (coborderIdeal i').comap gU ≤ coborderIdeal i)

/-- An open of a closed subscheme is cut out by an open of the ambient scheme. -/
theorem exists_opens_preimage_eq {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : Z.Opens) : ∃ O : X.Opens, i ⁻¹ᵁ O = V := by
  obtain ⟨T, hT, hTV⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V.2
  exact ⟨⟨T, hT⟩, Opens.ext hTV⟩

include comm hgU in
/-- The two composites `Z ⟶ U'` agree. -/
theorem liftCoborder_comp_gU :
    i.liftCoborder ≫ gU = f ≫ i'.liftCoborder := by
  rw [← cancel_mono i'.coborderRange.ι, Category.assoc, hgU, ← Category.assoc,
    i.liftCoborder_ι, Category.assoc, i'.liftCoborder_ι, comm]

include comm in
/-- **Compatible affine charts around a point.** A point of an open `V ⊆ Z` whose image under `f`
lies in the open cut out by `W'` has an affine chart `U ⊆ X` with `i⁻¹(U) ≤ V`, lying over an
affine chart `U' ⊆ X'` whose inverse image in the coborder of `i'` is inside `W'`. -/
private theorem exists_affineOpens_chart (W' : i'.coborderRange.toScheme.Opens) (V : Z.Opens)
    (hV : V ≤ f ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W')) (z : V) :
    ∃ (U : X.affineOpens) (U' : X'.affineOpens),
      i z.1 ∈ U.1 ∧ i ⁻¹ᵁ U.1 ≤ V ∧ U.1 ≤ g ⁻¹ᵁ U'.1 ∧
        i'.coborderRange.ι ⁻¹ᵁ U'.1 ≤ W' := by
  have hz' : i'.liftCoborder (f z.1) ∈ W' := hV z.2
  have hx' : g (i z.1) ∈ i'.coborderRange.ι ''ᵁ W' := by
    refine ⟨i'.liftCoborder (f z.1), hz', ?_⟩
    have h1 := congrArg (fun q : Z ⟶ X' => q z.1) comm
    have h2 := congrArg (fun q : Z' ⟶ X' => q (f z.1)) i'.liftCoborder_ι
    simp only [Scheme.Hom.comp_apply] at h1 h2
    exact h2.trans (h1.trans rfl)
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'le⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    hx' (i'.coborderRange.ι ''ᵁ W').isOpen
  obtain ⟨O, hO⟩ := exists_opens_preimage_eq i V
  have hxO : i z.1 ∈ O ⊓ g ⁻¹ᵁ U' := by
    refine ⟨?_, hxU'⟩
    show z.1 ∈ i ⁻¹ᵁ O
    rw [hO]
    exact z.2
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxO (O ⊓ g ⁻¹ᵁ U').isOpen
  refine ⟨⟨U, hU⟩, ⟨U', hU'⟩, hxU, ?_, fun y hy => (hUle hy).2, ?_⟩
  · intro y hy
    have : y ∈ i ⁻¹ᵁ O := (hUle hy).1
    rwa [hO] at this
  · intro y hy
    obtain ⟨w, hw, hwy⟩ := hU'le hy
    exact i'.coborderRange.ι.isOpenEmbedding.injective hwy ▸ hw

include hgU in
/-- **The ambient section of the pulled-back class on a chart.** On compatible affine charts
`U ≤ g⁻¹(U')`, let `a'` be a section of `ℐ'ⁿ` on `U'` representing the class of `x`, and let `b`
be its image under `g^♯`. Then `b` represents the class of the pullback of `x` to the coborder
of `i`. -/
private theorem app_coborderRange_extReesPullback (n : ℕ)
    (W' : i'.coborderRange.toScheme.Opens)
    (x : (reesPiece (coborderIdeal i') (n : ℤ)).val.obj (op W'))
    (U : X.affineOpens) (U' : X'.affineOpens) (hUU' : U.1 ≤ g ⁻¹ᵁ U'.1)
    (hU'W' : i'.coborderRange.ι ⁻¹ᵁ U'.1 ≤ W')
    (hchart : i.coborderRange.ι ⁻¹ᵁ U.1 ≤ gU ⁻¹ᵁ W')
    (hchart2 : i.coborderRange.ι ⁻¹ᵁ U.1 ≤ gU ⁻¹ᵁ (i'.coborderRange.ι ⁻¹ᵁ U'.1))
    (a' : ↥(chartIdeal i' U' ^ n))
    (ha'eq : (i'.coborderRange.ι.app U'.1).hom a' = reesPieceAmbient (coborderIdeal i') (n : ℤ)
      (i'.coborderRange.ι ⁻¹ᵁ U'.1)
      ((reesPiece (coborderIdeal i') (n : ℤ)).val.map (homOfLE hU'W').op x))
    (b : ↥(chartIdeal i U ^ n))
    (hb : (b : Γ(X, U.1)) =
      X.presheaf.map (homOfLE hUU').op ((g.app U'.1).hom (a' : Γ(X', U'.1)))) :
    (i.coborderRange.ι.app U.1).hom b = reesPieceAmbient (coborderIdeal i) (n : ℤ)
      (i.coborderRange.ι ⁻¹ᵁ U.1)
      ((reesPiece (coborderIdeal i) (n : ℤ)).val.map (homOfLE hchart).op
        (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ (n : ℤ) W' x)) := by
  have hring : g.appLE U'.1 U.1 hUU' ≫
      i.coborderRange.ι.appLE U.1 (i.coborderRange.ι ⁻¹ᵁ U.1) le_rfl =
      i'.coborderRange.ι.appLE U'.1 (i'.coborderRange.ι ⁻¹ᵁ U'.1) le_rfl ≫
        gU.appLE (i'.coborderRange.ι ⁻¹ᵁ U'.1) (i.coborderRange.ι ⁻¹ᵁ U.1) hchart2 := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (φ ψ : i.coborderRange.toScheme ⟶ X') (_ : φ = ψ) (e e'),
        φ.appLE U'.1 (i.coborderRange.ι ⁻¹ᵁ U.1) e =
          ψ.appLE U'.1 (i.coborderRange.ι ⁻¹ᵁ U.1) e' := by
      rintro φ _ rfl e e'
      rfl
    exact key _ _ hgU.symm _ _
  refine Eq.trans ?_ (reesPieceAmbient_restrict _ _ _ _ hchart _).symm
  refine Eq.trans ?_ (congrArg _ (extReesAmbient_extReesPullback gU (coborderIdeal i')
    (coborderIdeal i) hJ (n : ℤ) W' x).symm)
  have hnat : (gU.appLE W' (i.coborderRange.ι ⁻¹ᵁ U.1) hchart).hom
      (extReesAmbient (coborderIdeal i') (n : ℤ) W' x) =
      (gU.appLE (i'.coborderRange.ι ⁻¹ᵁ U'.1) (i.coborderRange.ι ⁻¹ᵁ U.1)
        hchart2).hom ((i'.coborderRange.ι.app U'.1).hom a') := by
    rw [ha'eq, reesPieceAmbient_restrict]
    exact (congrArg (fun q => q.hom (extReesAmbient (coborderIdeal i') (n : ℤ) W' x))
      (Scheme.Hom.map_appLE gU hchart2 (homOfLE hU'W').op)).symm
  refine Eq.trans ?_ hnat.symm
  rw [Scheme.Hom.app_eq_appLE (f := i'.coborderRange.ι)]
  refine Eq.trans ?_ (congrArg (fun q => q.hom (a' : Γ(X', U'.1))) hring)
  exact (congrArg (fun q : Γ(X, U.1) ⟶ Γ(i.coborderRange.toScheme,
      i.coborderRange.ι ⁻¹ᵁ U.1) => q.hom (b : Γ(X, U.1)))
    (Scheme.Hom.app_eq_appLE i.coborderRange.ι)).trans (by rw [hb]; rfl)

include comm hgU in
/-- **The canonical map of conormal algebras on pulled-back Rees sections**: it sends the
pullback `g'^*x` of a section `x` of `ℐ'ⁿ` to the pullback `g^*(h^♯x)`. -/
theorem conormalAlgebraHom_map_pullbackSection (n : ℕ) (W' : i'.coborderRange.toScheme.Opens)
    (x : (reesPiece (coborderIdeal i') (n : ℤ)).val.obj (op W')) (V : Z.Opens)
    (hV : V ≤ f ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W'))
    (hV2 : V ≤ i.liftCoborder ⁻¹ᵁ (gU ⁻¹ᵁ W')) :
    (conormalAlgebraHom i i' f g comm).hom.map (n : ℤ) V (i'.liftCoborder ⁻¹ᵁ W') hV
        (Scheme.Modules.pullbackSection i'.liftCoborder (reesPiece (coborderIdeal i') (n : ℤ))
          W' (i'.liftCoborder ⁻¹ᵁ W') le_rfl x) =
      ((conormalAlgebra i).algebra.piece (n : ℤ)).val.map (homOfLE hV2).op
        (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ))
          (gU ⁻¹ᵁ W') (i.liftCoborder ⁻¹ᵁ (gU ⁻¹ᵁ W')) le_rfl
          (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ (n : ℤ) W' x)) := by
  classical
  set H := conormalAlgebraHom i i' f g comm
  set M := (conormalAlgebra i).algebra.piece (n : ℤ)
  choose U U' hzU hUV hUU' hU'W' using exists_affineOpens_chart i i' f g comm W' V hV
  refine (TopCat.Sheaf.eq_of_locally_eq' ⟨M.val.presheaf, M.isSheaf⟩ (fun z : V => i ⁻¹ᵁ (U z).1)
    V (fun z => homOfLE (hUV z)) (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩) _ _
    fun z => ?_)
  have hZU := isClosedImmersion_resLE_of_le_coborderRange i (U z).1
    (by rw [Stacks.Divisors.coborderRange_eq_top]; exact le_top)
  have hZ'U' := isClosedImmersion_resLE_of_le_coborderRange i' (U' z).1
    (by rw [Stacks.Divisors.coborderRange_eq_top]; exact le_top)
  have hFU : i ⁻¹ᵁ (U z).1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ (U' z).1) := by
    rw [← Scheme.Hom.comp_preimage, comm, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ (hUU' z)
  have hchart2 : i.coborderRange.ι ⁻¹ᵁ (U z).1 ≤ gU ⁻¹ᵁ (i'.coborderRange.ι ⁻¹ᵁ (U' z).1) := by
    rw [← Scheme.Hom.comp_preimage, hgU, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ (hUU' z)
  have hchart : i.coborderRange.ι ⁻¹ᵁ (U z).1 ≤ gU ⁻¹ᵁ W' :=
    hchart2.trans (Scheme.Hom.preimage_mono _ (hU'W' z))
  obtain ⟨a', ha'eq⟩ := exists_chartIdeal_pow_app_eq i' n W' x (U' z) hZ'U' (hU'W' z)
  have hbmem := H.map_ideal_pow (U z) (U' z) (hUU' z) hZU hZ'U' n a'
  set b : ↥(chartIdeal i (U z) ^ n) := ⟨_, hbmem⟩ with hb
  have hcan := H.chart (U z) (U' z) (hUU' z) hZU hZ'U' hFU n a' b rfl
  have hle' := preimage_le_preimage_liftCoborder i' (hU'W' z)
  have hL := restrict_pullbackSection_eq_localMap i' n W' x (U' z) hZ'U' (hU'W' z) hle' a' ha'eq
  have hlhs : M.val.map (homOfLE (hUV z)).op (H.hom.map (n : ℤ) V (i'.liftCoborder ⁻¹ᵁ W') hV
      (Scheme.Modules.pullbackSection i'.liftCoborder (reesPiece (coborderIdeal i') (n : ℤ))
        W' (i'.liftCoborder ⁻¹ᵁ W') le_rfl x)) = (conormalAlgebra i).localMap (U z) hZU n b := by
    refine (H.hom.map_restrict_target (n : ℤ) V (i ⁻¹ᵁ (U z).1) (hUV z) _ hV _).trans ?_
    refine (H.hom.map_restrict_source (n : ℤ) (i ⁻¹ᵁ (U z).1) _ (i' ⁻¹ᵁ (U' z).1) hle' hFU _
      _).symm.trans ?_
    exact (congrArg _ hL).trans hcan
  have hbeq := app_coborderRange_extReesPullback i i' g gU hgU hJ n W' x (U z) (U' z)
    (hUU' z) (hU'W' z) hchart hchart2 a' ha'eq b rfl
  have hR := restrict_pullbackSection_eq_localMap i n (gU ⁻¹ᵁ W')
    (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ (n : ℤ) W' x) (U z) hZU hchart
    ((hUV z).trans hV2) b hbeq
  exact hlhs.trans (hR.symm.trans
    (ConcreteCategory.congr_hom (M.val.map_comp (homOfLE hV2).op (homOfLE (hUV z)).op) _))

include hgU in
/-- **Both composites of the naturality square lie over the same morphism to the base.** -/
private theorem normalConeToDeformation_comp_deformationMap_toBase :
    (normalConeToDeformation i ≫ deformationMap gU (coborderIdeal i') (coborderIdeal i) hJ) ≫
        deformationSpaceToBase (coborderIdeal i') =
      (normalConeMapOfSquare i i' f g comm ≫ normalConeToDeformation i') ≫
        deformationSpaceToBase (coborderIdeal i') := by
  calc (normalConeToDeformation i ≫ deformationMap gU (coborderIdeal i') (coborderIdeal i) hJ)
        ≫ deformationSpaceToBase (coborderIdeal i')
      = normalConeToDeformation i ≫ deformationSpaceToBase (coborderIdeal i) ≫ gU := by
        rw [Category.assoc, deformationMap_toBase]
    _ = (normalConeToBase i ≫ i.liftCoborder) ≫ gU := by
        rw [← Category.assoc, normalConeToDeformation_toBase]
    _ = normalConeToBase i ≫ f ≫ i'.liftCoborder := by
        rw [Category.assoc, liftCoborder_comp_gU i i' f g comm gU hgU]
    _ = (normalConeMapOfSquare i i' f g comm ≫ normalConeToBase i') ≫ i'.liftCoborder := by
        rw [normalConeMapOfSquare_toBase, Category.assoc]
    _ = (normalConeMapOfSquare i i' f g comm ≫ normalConeToDeformation i') ≫
        deformationSpaceToBase (coborderIdeal i') := by
        rw [Category.assoc, Category.assoc, normalConeToDeformation_toBase]

/-- **`κ` followed by the map of deformation spaces, on a homogeneous section.** The section it
produces is the restriction of the one computed on the chart `g_U⁻¹(W')` of `D(Z ⊆ X)`. -/
private theorem appLE_chartIncl_comp_deformationMap
    (W' : i'.coborderRange.toScheme.affineOpens) (k : ℤ)
    (x : ((extReesGradedAlgebra (coborderIdeal i')).piece k).val.obj (op W'.1))
    (T : (normalCone i).Opens)
    (hT0 : T ≤ (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ (gU ⁻¹ᵁ W'.1))
    (h₁ : T ≤ (normalConeToDeformation i ≫
      deformationMap gU (coborderIdeal i') (coborderIdeal i) hJ) ⁻¹ᵁ
        (deformationSpaceToBase (coborderIdeal i') ⁻¹ᵁ W'.1))
    (hκ : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ (gU ⁻¹ᵁ W'.1) ≤
      normalConeToDeformation i ⁻¹ᵁ
        (deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ (gU ⁻¹ᵁ W'.1))) :
    ((normalConeToDeformation i ≫ deformationMap gU (coborderIdeal i') (coborderIdeal i)
        hJ).appLE _ _ h₁).hom (chartIncl (coborderIdeal i') k W'.1 x) =
      (normalCone i).presheaf.map (homOfLE hT0).op
        (((normalConeToDeformation i).appLE _ _ hκ).hom
          (chartIncl (coborderIdeal i) k (gU ⁻¹ᵁ W'.1)
            (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ k W'.1 x))) := by
  have hΦ : (deformationSpaceToBase (coborderIdeal i) ≫ gU) ⁻¹ᵁ W'.1 ≤
      deformationMap gU (coborderIdeal i') (coborderIdeal i) hJ ⁻¹ᵁ
        (deformationSpaceToBase (coborderIdeal i') ⁻¹ᵁ W'.1) := by
    rw [← Scheme.Hom.comp_preimage (deformationMap gU (coborderIdeal i') (coborderIdeal i) hJ),
      deformationMap_toBase]
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ hΦ (hT0.trans hκ)]
  refine (congrArg (fun q => ((normalConeToDeformation i).appLE _ _ (hT0.trans hκ)).hom q)
    (deformationMap_appLE_chartIncl gU (coborderIdeal i') (coborderIdeal i) hJ W' k x
      hΦ)).trans ?_
  exact (congrArg (fun q => q.hom (chartIncl (coborderIdeal i) k (gU ⁻¹ᵁ W'.1)
    (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ k W'.1 x)))
    (Scheme.Hom.appLE_map (normalConeToDeformation i) hκ (homOfLE hT0).op)).symm

end Square

end Stacks.Deformation

namespace Stacks.RelativeSpec

variable {s : RelativeSpecSituation.{u}} {T : Scheme.{u}}

/-- The sections of a morphism into a relative spectrum which pulls the universal pair back to
`q`, over the preimage of an arbitrary open of the base, are the algebra map of `q`. -/
theorem appLE_of_pullback_universalRelativeSpecPair (m : T ⟶ (gluedSpectrum s).scheme)
    (q : RelativeSpecPair s T)
    (hq : RelativeSpecPair.pullback m (universalRelativeSpecPair s) = q) (U : s.base.Opens)
    (h : q.1 ⁻¹ᵁ U ≤ m ⁻¹ᵁ ((gluedSpectrum s).toBase ⁻¹ᵁ U)) :
    (universalAlgebraMap s).right.app (op U) ≫
        m.appLE ((gluedSpectrum s).toBase ⁻¹ᵁ U) (q.1 ⁻¹ᵁ U) h =
      q.2.right.app (op U) := by
  subst hq
  exact congrArg (fun k => (universalAlgebraMap s).right.app (op U) ≫ k) m.appLE_eq_app

/-- **The sections of the morphism attached to a relative-spectrum pair, over the preimage of any
open of the base**, are the algebra map of the pair. Over an affine open this is
`Stacks.RelativeSpec.pairToHom_appLE`. -/
theorem pairToHom_appLE_of_opens (p : RelativeSpecPair s T) (U : s.base.Opens)
    (h : p.1 ⁻¹ᵁ U ≤ pairToHom p ⁻¹ᵁ ((gluedSpectrum s).toBase ⁻¹ᵁ U)) :
    (universalAlgebraMap s).right.app (op U) ≫
        (pairToHom p).appLE ((gluedSpectrum s).toBase ⁻¹ᵁ U) (p.1 ⁻¹ᵁ U) h =
      p.2.right.app (op U) :=
  appLE_of_pullback_universalRelativeSpecPair (pairToHom p) p
    (pullback_universalRelativeSpecPair_pairToHom p) U h

end Stacks.RelativeSpec

namespace Stacks.Deformation

/-! ### Morphisms into the deformation space -/

section HomExt

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Every function on an affine chart `π⁻¹(W)` of the deformation space is a finite sum of images
of homogeneous sections. -/
theorem chartIncl_induction (W : X.affineOpens)
    {P : Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1) → Prop}
    (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hincl : ∀ k x, P (chartIncl I k W.1 x)) (y) : P y := by
  have := isIso_universalAlgebraMap_app (extReesSituation I) W
  let F : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W.1) →+*
      Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1) :=
    ((universalAlgebraMap (extReesSituation I)).right.app (op W.1)).hom.comp
      ((((ungradedAlgebraSheafIsoGradedAlgebraSheaf X (extReesGradedAlgebra I)
        (extReesGradedAlgebra_mul_comm I)).hom.right.hom.app (op W.1)).hom).comp
        (ungradedCommUnit X (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) W.1).hom)
  have hF : Function.Surjective F :=
    (ConcreteCategory.bijective_of_isIso
      ((universalAlgebraMap (extReesSituation I)).right.app (op W.1))).2.comp
      ((bijective_algebraSheafIso_app (ungradedAlgebraSheafIsoGradedAlgebraSheaf X
        (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I)) W.1).2.comp
        (bijective_ungradedCommUnit_of_isAffineOpen X (extReesGradedAlgebra I)
          (extReesGradedAlgebra_mul_comm I) W.2).2)
  obtain ⟨t, rfl⟩ := hF y
  induction t using Stacks.GradedAlgebra.incl_induction with
  | zero => rwa [map_zero]
  | incl k x => exact hincl k x
  | add t t' ht ht' =>
    rw [map_add]
    exact hadd _ _ ht ht'

/-- **Two morphisms into the deformation space agree as soon as they lie over the same morphism
to the base and agree on the images of homogeneous sections over the affine opens.** -/
theorem hom_ext_deformationSpace {T : Scheme.{u}} (m m' : T ⟶ deformationSpace I)
    (hb : m ≫ deformationSpaceToBase I = m' ≫ deformationSpaceToBase I)
    (h : ∀ (W : X.affineOpens) (k : ℤ) (x : ((extReesGradedAlgebra I).piece k).val.obj (op W.1))
      (h₁ : (m ≫ deformationSpaceToBase I) ⁻¹ᵁ W.1 ≤ m ⁻¹ᵁ (deformationSpaceToBase I ⁻¹ᵁ W.1))
      (h₂ : (m ≫ deformationSpaceToBase I) ⁻¹ᵁ W.1 ≤ m' ⁻¹ᵁ (deformationSpaceToBase I ⁻¹ᵁ W.1)),
      (m.appLE _ _ h₁).hom (chartIncl I k W.1 x) = (m'.appLE _ _ h₂).hom (chartIncl I k W.1 x)) :
    m = m' := by
  refine Scheme.hom_ext_of_affinePreimages (m ≫ deformationSpaceToBase I) fun W => ?_
  have hV := Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation I) W
  have h₁ : (m ≫ deformationSpaceToBase I) ⁻¹ᵁ W.1 ≤
      m ⁻¹ᵁ (deformationSpaceToBase I ⁻¹ᵁ W.1) := (Scheme.Hom.comp_preimage _ _ _).le
  have h₂ : (m ≫ deformationSpaceToBase I) ⁻¹ᵁ W.1 ≤
      m' ⁻¹ᵁ (deformationSpaceToBase I ⁻¹ᵁ W.1) := by
    rw [hb]
    exact (Scheme.Hom.comp_preimage _ _ _).le
  have happ : m.appLE _ _ h₁ = m'.appLE _ _ h₂ := by
    refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
    induction y using chartIncl_induction I W with
    | h0 => exact (map_zero _).trans (map_zero _).symm
    | hadd a b ha hb' => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ha hb').trans
        (map_add _ _ _).symm)
    | hincl k x => exact h W k x h₁ h₂
  have : IsAffine (deformationSpaceToBase I ⁻¹ᵁ W.1).toScheme := hV
  have hres : m.resLE _ _ h₁ = m'.resLE _ _ h₂ := ext_of_isAffine (by
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happ])
  rw [← Scheme.Hom.resLE_comp_ι m h₁, ← Scheme.Hom.resLE_comp_ι m' h₂, hres]

end HomExt

/-! ### The normal cone inside the deformation space, on homogeneous sections -/

section Cone

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The image in `Γ(C_ZX, π⁻¹V)` of a homogeneous section of the conormal algebra. -/
def coneIncl (n : ℤ) (V : Z.Opens) (y : ((conormalAlgebra i).algebra.piece n).val.obj (op V)) :
    Γ(normalCone i, normalConeToBase i ⁻¹ᵁ V) :=
  ((universalAlgebraMap (normalConeSituation i)).right.app (op V)).hom
    (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op V)).hom
      (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int
        n V y))

/-- `coneIncl` commutes with restriction: restricting the image of a homogeneous section `y` over
`V` to `π⁻¹V'` gives the image of the restriction of `y` to `V'`. -/
theorem coneIncl_restrict (n : ℤ) {V V' : Z.Opens} (h : V' ≤ V)
    (y : ((conormalAlgebra i).algebra.piece n).val.obj (op V)) :
    (normalCone i).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op (coneIncl i n V y) =
      coneIncl i n V' (((conormalAlgebra i).algebra.piece n).val.map (homOfLE h).op y) := by
  have h1 := ConcreteCategory.congr_hom
    ((universalAlgebraMap (normalConeSituation i)).right.naturality (homOfLE h).op)
    (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op V)).hom
      (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int
        n V y))
  have h2 := ConcreteCategory.congr_hom
    ((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int).hom.right.hom.naturality (homOfLE h).op)
    (ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int n V y)
  refine h1.symm.trans ?_
  refine (congrArg _ h2.symm).trans ?_
  exact congrArg (fun z => ((universalAlgebraMap (normalConeSituation i)).right.app (op V')).hom
    (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op V')).hom z))
    (ungradedAlgebraSheafIncl_restrict Z (conormalAlgebra i).algebra
      (conormalAlgebra i).mul_comm_int n h y)

/-- `κ` on a homogeneous section over any open of the coborder. -/
private theorem appLE_chartIncl_of_opens_aux (W : i.coborderRange.toScheme.Opens)
    (k : ℤ) (x : ((extReesGradedAlgebra (coborderIdeal i)).piece k).val.obj (op W))
    (hle : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W ≤
      normalConeToDeformation i ⁻¹ᵁ (deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ W)) :
    ((normalConeToDeformation i).appLE _ _ hle).hom (chartIncl (coborderIdeal i) k W x) =
      ((universalAlgebraMap (normalConeSituation i)).right.app
        (op (i.liftCoborder ⁻¹ᵁ W))).hom
        (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op (i.liftCoborder ⁻¹ᵁ W))).hom
          (toConormalExtAdd i k (op W) x)) := by
  have happLE := pairToHom_appLE_of_opens (s := deformationSituation i)
    ⟨normalConeToBase i ≫ i.liftCoborder,
      (extReesAlgebraSheaf (coborderIdeal i)).pairHomEquiv (normalConeToBase i ≫ i.liftCoborder)
        (normalConeToDeformationAlgebraHom i)⟩ W hle
  refine (congrArg (fun φ => φ.hom (((ungradedAlgebraSheafIsoGradedAlgebraSheaf
    i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
    (extReesGradedAlgebra_mul_comm _)).hom.right.hom.app (op W)).hom
      (ungradedAlgebraSheafIncl i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _) k W x))) happLE).trans ?_
  have hinv : ((ungradedAlgebraSheafIsoGradedAlgebraSheaf i.coborderRange.toScheme
      (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _)).inv.right.hom.app
        (op W)).hom
      (((ungradedAlgebraSheafIsoGradedAlgebraSheaf i.coborderRange.toScheme
        (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _)).hom.right.hom.app
          (op W)).hom
        (ungradedAlgebraSheafIncl i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
          (extReesGradedAlgebra_mul_comm _) k W x)) =
      ungradedAlgebraSheafIncl i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
        (extReesGradedAlgebra_mul_comm _) k W x :=
    congrArg (fun k' : ungradedAlgebraSheaf i.coborderRange.toScheme
        (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _) ⟶
        ungradedAlgebraSheaf i.coborderRange.toScheme (extReesGradedAlgebra (coborderIdeal i))
          (extReesGradedAlgebra_mul_comm _) => (k'.right.hom.app (op W)).hom
          (ungradedAlgebraSheafIncl i.coborderRange.toScheme
            (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _) k W x))
      (ungradedAlgebraSheafIsoGradedAlgebraSheaf i.coborderRange.toScheme
        (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _)).hom_inv_id
  show ((universalAlgebraMap (normalConeSituation i)).right.app
        (op (i.liftCoborder ⁻¹ᵁ W))).hom
        (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op (i.liftCoborder ⁻¹ᵁ W))).hom
          (((toConormalUngradedHom i).right.hom.app (op W)).hom
            (((ungradedAlgebraSheafIsoGradedAlgebraSheaf i.coborderRange.toScheme
              (extReesGradedAlgebra (coborderIdeal i))
              (extReesGradedAlgebra_mul_comm _)).inv.right.hom.app
                (op W)).hom
              (((ungradedAlgebraSheafIsoGradedAlgebraSheaf i.coborderRange.toScheme
                (extReesGradedAlgebra (coborderIdeal i))
                (extReesGradedAlgebra_mul_comm _)).hom.right.hom.app
                  (op W)).hom
                (ungradedAlgebraSheafIncl i.coborderRange.toScheme
                  (extReesGradedAlgebra (coborderIdeal i)) (extReesGradedAlgebra_mul_comm _) k W
                  x))))) = _
  rw [hinv, toConormalUngradedHom_app_incl]

/-- **`κ` on a homogeneous section**: the section `x t^k` of the deformation space restricts on
`C_ZX` to the image of `Ψ(x)`. -/
theorem normalConeToDeformation_appLE_chartIncl (W : i.coborderRange.toScheme.affineOpens) (k : ℤ)
    (x : ((extReesGradedAlgebra (coborderIdeal i)).piece k).val.obj (op W.1))
    (hle : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W.1 ≤
      normalConeToDeformation i ⁻¹ᵁ (deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ W.1)) :
    ((normalConeToDeformation i).appLE _ _ hle).hom (chartIncl (coborderIdeal i) k W.1 x) =
      ((universalAlgebraMap (normalConeSituation i)).right.app
        (op (i.liftCoborder ⁻¹ᵁ W.1))).hom
        (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op (i.liftCoborder ⁻¹ᵁ W.1))).hom
          (toConormalExtAdd i k (op W.1) x)) :=
  appLE_chartIncl_of_opens_aux i W.1 k x hle

/-- **`κ` on a homogeneous section over any open**: the section `x t^k` of the deformation space
restricts on `C_ZX` to the image of `Ψ(x)`. Over an affine open this is
`Stacks.Deformation.normalConeToDeformation_appLE_chartIncl`. -/
theorem normalConeToDeformation_appLE_chartIncl_of_opens (W : i.coborderRange.toScheme.Opens)
    (k : ℤ) (x : ((extReesGradedAlgebra (coborderIdeal i)).piece k).val.obj (op W))
    (hle : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W ≤
      normalConeToDeformation i ⁻¹ᵁ (deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ W)) :
    ((normalConeToDeformation i).appLE _ _ hle).hom (chartIncl (coborderIdeal i) k W x) =
      ((universalAlgebraMap (normalConeSituation i)).right.app
        (op (i.liftCoborder ⁻¹ᵁ W))).hom
        (((ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
          (conormalAlgebra i).mul_comm_int).hom.right.hom.app (op (i.liftCoborder ⁻¹ᵁ W))).hom
          (toConormalExtAdd i k (op W) x)) :=
  appLE_chartIncl_of_opens_aux i W k x hle

end Cone

/-! ### Naturality of the normal cone inside the deformation space -/

section Naturality

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
  [IsClosedImmersion i] [IsClosedImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X')
  (comm : f ≫ i' = i ≫ g)
  (gU : i.coborderRange.toScheme ⟶ i'.coborderRange.toScheme)
  (hgU : gU ≫ i'.coborderRange.ι = i.coborderRange.ι ≫ g)
  (hJ : (coborderIdeal i').comap gU ≤ coborderIdeal i) [IsAffineHom gU]

/-- The ungraded spelling of a homogeneous section of the conormal algebra. -/
theorem coneIncl_eq (n : ℤ) (V : Z.Opens)
    (y : ((conormalAlgebra i).algebra.piece n).val.obj (op V)) :
    coneIncl i n V y = ((universalAlgebraMap (normalConeSituation i)).right.app (op V)).hom
      ((conormalAlgebra i).algebra.ungradedIncl n y) :=
  congrArg _ (ungradedToGradedRight_ungradedAlgebraSheafIncl Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int n V y)

include comm in
/-- **The canonical morphism of normal cones on a homogeneous section.** -/
theorem normalConeMapOfSquare_appLE_coneIncl (V : Z'.affineOpens) (n : ℤ)
    (y : ((conormalAlgebra i').algebra.piece n).val.obj (op V.1))
    (hle : (normalConeToBase i ≫ f) ⁻¹ᵁ V.1 ≤
      normalConeMapOfSquare i i' f g comm ⁻¹ᵁ (normalConeToBase i' ⁻¹ᵁ V.1)) :
    ((normalConeMapOfSquare i i' f g comm).appLE _ _ hle).hom (coneIncl i' n V.1 y) =
      coneIncl i n (f ⁻¹ᵁ V.1)
        ((conormalAlgebraHom i i' f g comm).hom.map n (f ⁻¹ᵁ V.1) V.1 le_rfl y) := by
  rw [coneIncl_eq, coneIncl_eq]
  have happLE := pairToHom_appLE (normalConeMapPair i i' f
    (conormalAlgebraHom i i' f g comm).hom) V hle
  exact (congrArg (fun φ => φ.hom ((conormalAlgebra i').algebra.ungradedIncl n y)) happLE).trans
    (normalConeMapPair_snd_right_app_ungradedIncl i i' f _ n V.1 y)

/-- **The two sections of the naturality square agree on a chart.** The section of `κ` computed
over the chart `g_U⁻¹(W')` of `D(Z ⊆ X)` and the section of `C(g)` followed by `κ'` computed over
`W'` have the same restriction to `T`. In negative degrees both sides vanish; in degree `n ≥ 0`
this is the canonical map of conormal algebras on pulled-back Rees sections. -/
private theorem map_appLE_chartIncl_eq_map_normalConeMapOfSquare {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i'] (f : Z ⟶ Z')
    (g : X ⟶ X') (comm : f ≫ i' = i ≫ g)
    (gU : i.coborderRange.toScheme ⟶ i'.coborderRange.toScheme)
    (hgU : gU ≫ i'.coborderRange.ι = i.coborderRange.ι ≫ g)
    (hJ : (coborderIdeal i').comap gU ≤ coborderIdeal i)
    (W' : i'.coborderRange.toScheme.affineOpens) (k : ℤ)
    (x : ((extReesGradedAlgebra (coborderIdeal i')).piece k).val.obj (op W'.1))
    (T : (normalCone i).Opens)
    (hT0 : T ≤ (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ (gU ⁻¹ᵁ W'.1))
    (hT1 : T ≤ (normalConeToBase i ≫ f) ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W'.1))
    (hκ : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ (gU ⁻¹ᵁ W'.1) ≤
      normalConeToDeformation i ⁻¹ᵁ
        (deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ (gU ⁻¹ᵁ W'.1)))
    (hκ' : (normalConeToBase i' ≫ i'.liftCoborder) ⁻¹ᵁ W'.1 ≤
      normalConeToDeformation i' ⁻¹ᵁ (deformationSpaceToBase (coborderIdeal i') ⁻¹ᵁ W'.1))
    (hC : (normalConeToBase i ≫ f) ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W'.1) ≤
      normalConeMapOfSquare i i' f g comm ⁻¹ᵁ
        (normalConeToBase i' ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W'.1))) :
    (normalCone i).presheaf.map (homOfLE hT0).op
        (((normalConeToDeformation i).appLE _ _ hκ).hom
          (chartIncl (coborderIdeal i) k (gU ⁻¹ᵁ W'.1)
            (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ k W'.1 x))) =
      (normalCone i).presheaf.map (homOfLE hT1).op
        (((normalConeMapOfSquare i i' f g comm).appLE _ _ hC).hom
          (((normalConeToDeformation i').appLE _ _ hκ').hom
            (chartIncl (coborderIdeal i') k W'.1 x))) := by
  have e1 := normalConeToDeformation_appLE_chartIncl_of_opens i (gU ⁻¹ᵁ W'.1) k
    (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ k W'.1 x) hκ
  have e2 := normalConeToDeformation_appLE_chartIncl i' W' k x hκ'
  refine (congrArg ((normalCone i).presheaf.map (homOfLE hT0).op).hom e1).trans ?_
  refine Eq.trans ?_ (congrArg (fun q => ((normalCone i).presheaf.map (homOfLE hT1).op).hom
    (((normalConeMapOfSquare i i' f g comm).appLE _ _ hC).hom q)) e2).symm
  rcases lt_or_ge k 0 with hk | hk
  · rw [toConormalExtAdd_of_neg i hk, toConormalExtAdd_of_neg i' hk]
    have z1 : (0 : ((extReesPiece (coborderIdeal i) k).val.obj (op (gU ⁻¹ᵁ W'.1)) : Type u) →+
        algSections (conormalPushforwardAlgebra i i.liftCoborder) (op (gU ⁻¹ᵁ W'.1)))
        (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ k W'.1 x) = 0 := rfl
    have z2 : (0 : ((extReesPiece (coborderIdeal i') k).val.obj (op W'.1) : Type u) →+
        algSections (conormalPushforwardAlgebra i' i'.liftCoborder) (op W'.1)) x = 0 := rfl
    rw [z1, z2]
    exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (map_zero _)).trans
      ((congrArg _ ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans
        (map_zero _))).trans (map_zero _)).symm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [toConormalExtAdd_of_nonneg i hk, toConormalExtAdd_of_nonneg i' hk]
  show (normalCone i).presheaf.map (homOfLE hT0).op
      (coneIncl i (n : ℤ) (i.liftCoborder ⁻¹ᵁ (gU ⁻¹ᵁ W'.1)) _) =
    (normalCone i).presheaf.map (homOfLE hT1).op
      (((normalConeMapOfSquare i i' f g comm).appLE _ _ hC).hom
        (coneIncl i' (n : ℤ) (i'.liftCoborder ⁻¹ᵁ W'.1) _))
  have hV2 : f ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W'.1) ≤ i.liftCoborder ⁻¹ᵁ (gU ⁻¹ᵁ W'.1) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      liftCoborder_comp_gU i i' f g comm gU hgU])
  have hR' := normalConeMapOfSquare_appLE_coneIncl i i' f g comm
    ⟨i'.liftCoborder ⁻¹ᵁ W'.1, W'.2.preimage i'.liftCoborder⟩ (n : ℤ)
    (Scheme.Modules.pullbackSection i'.liftCoborder (reesPiece (coborderIdeal i') (n : ℤ)) W'.1
      (i'.liftCoborder ⁻¹ᵁ W'.1) le_rfl x) hC
  have hM := conormalAlgebraHom_map_pullbackSection i i' f g comm gU hgU hJ n W'.1 x
    (f ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W'.1)) le_rfl hV2
  have hres := coneIncl_restrict i (n : ℤ) hV2
    (Scheme.Modules.pullbackSection i.liftCoborder (reesPiece (coborderIdeal i) (n : ℤ))
      (gU ⁻¹ᵁ W'.1) (i.liftCoborder ⁻¹ᵁ (gU ⁻¹ᵁ W'.1)) le_rfl
      (extReesPullback gU (coborderIdeal i') (coborderIdeal i) hJ (n : ℤ) W'.1 x))
  refine Eq.trans ?_ (congrArg ((normalCone i).presheaf.map (homOfLE hT1).op).hom hR').symm
  refine Eq.trans ?_ (congrArg (fun q => ((normalCone i).presheaf.map (homOfLE hT1).op).hom
    (coneIncl i (n : ℤ) (f ⁻¹ᵁ (i'.liftCoborder ⁻¹ᵁ W'.1)) q)) hM).symm
  refine Eq.trans ?_ (congrArg ((normalCone i).presheaf.map (homOfLE hT1).op).hom hres)
  exact ConcreteCategory.congr_hom ((normalCone i).presheaf.map_comp _ _) _

omit [IsAffineHom gU] in
include comm hgU in
/-- **The normal cone sits naturally inside the deformation space**: for a commutative square
of closed immersions, `κ` followed by the morphism of deformation spaces is the canonical
morphism of normal cones followed by `κ`. The morphism of coborders need not be affine. -/
theorem normalConeToDeformation_comp_deformationMap :
    normalConeToDeformation i ≫ deformationMap gU (coborderIdeal i') (coborderIdeal i) hJ =
      normalConeMapOfSquare i i' f g comm ≫ normalConeToDeformation i' := by
  refine hom_ext_deformationSpace (coborderIdeal i') _ _
    (normalConeToDeformation_comp_deformationMap_toBase i i' f g comm gU hgU hJ)
    fun W' k x h₁ h₂ => ?_
  set W : i.coborderRange.toScheme.Opens := gU ⁻¹ᵁ W'.1
  set V' : Z'.affineOpens := ⟨i'.liftCoborder ⁻¹ᵁ W'.1, W'.2.preimage i'.liftCoborder⟩
  set T := ((normalConeToDeformation i ≫ deformationMap gU (coborderIdeal i') (coborderIdeal i) hJ)
    ≫ deformationSpaceToBase (coborderIdeal i')) ⁻¹ᵁ W'.1
  have hT0 : T ≤ (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W := by
    intro y hy
    change ((normalConeToDeformation i ≫ deformationMap gU (coborderIdeal i')
      (coborderIdeal i) hJ) ≫ deformationSpaceToBase (coborderIdeal i')) y ∈ W'.1 at hy
    rwa [Category.assoc, deformationMap_toBase, ← Category.assoc,
      normalConeToDeformation_toBase] at hy
  have hT1 : T ≤ (normalConeToBase i ≫ f) ⁻¹ᵁ V'.1 := by
    intro y hy
    change ((normalConeToDeformation i ≫ deformationMap gU (coborderIdeal i')
      (coborderIdeal i) hJ) ≫ deformationSpaceToBase (coborderIdeal i')) y ∈ W'.1 at hy
    rwa [Category.assoc, deformationMap_toBase, ← Category.assoc,
      normalConeToDeformation_toBase, Category.assoc,
      liftCoborder_comp_gU i i' f g comm gU hgU] at hy
  have hκ : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W ≤
      normalConeToDeformation i ⁻¹ᵁ (deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage (normalConeToDeformation i), normalConeToDeformation_toBase]
  have hL := appLE_chartIncl_comp_deformationMap i i' gU hJ W' k x T hT0 h₁ hκ
  have hκ' : (normalConeToBase i' ≫ i'.liftCoborder) ⁻¹ᵁ W'.1 ≤
      normalConeToDeformation i' ⁻¹ᵁ (deformationSpaceToBase (coborderIdeal i') ⁻¹ᵁ W'.1) := by
    rw [← Scheme.Hom.comp_preimage (normalConeToDeformation i'), normalConeToDeformation_toBase]
  have hC : (normalConeToBase i ≫ f) ⁻¹ᵁ V'.1 ≤
      normalConeMapOfSquare i i' f g comm ⁻¹ᵁ (normalConeToBase i' ⁻¹ᵁ V'.1) := by
    rw [← Scheme.Hom.comp_preimage (normalConeMapOfSquare i i' f g comm),
      normalConeMapOfSquare_toBase]
  have hR : ((normalConeMapOfSquare i i' f g comm ≫ normalConeToDeformation i').appLE _ _
      h₂).hom (chartIncl (coborderIdeal i') k W'.1 x) =
      (normalCone i).presheaf.map (homOfLE hT1).op
        (((normalConeMapOfSquare i i' f g comm).appLE _ _ hC).hom
          (((normalConeToDeformation i').appLE _ _ hκ').hom
            (chartIncl (coborderIdeal i') k W'.1 x))) := by
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ hκ' (hT1.trans hC)]
    exact (congrArg (fun q => q.hom (((normalConeToDeformation i').appLE _ _ hκ').hom
      (chartIncl (coborderIdeal i') k W'.1 x)))
      (Scheme.Hom.appLE_map (normalConeMapOfSquare i i' f g comm) hC (homOfLE hT1).op)).symm
  exact hL.trans ((map_appLE_chartIncl_eq_map_normalConeMapOfSquare i i' f g comm gU hgU hJ
    W' k x T hT0 hT1 hκ hκ' hC).trans hR.symm)

end Naturality

end Stacks.Deformation

end
