module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorGluing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorRestrictOpenImmersion

/-!
# The order of a differential operator across an open immersion

Let `j : Z ⟶ W` be an open immersion of schemes and `p : W ⟶ Y` a morphism. An operator on the
local sections of modules on `W`, defined over the opens contained in the image of `j`, is a
differential operator of order at most `k` on `W/Y` exactly when the corresponding global operator
on the restrictions to `Z` is a differential operator of order at most `k` on `Z/Y`.

The comparison rests on a reformulation of linearity over the inverse image of the structure sheaf
of `Y`: an operator compatible with restriction of sections is linear over that sheaf of rings
exactly when it commutes with multiplication by every section of the structure sheaf of `Y`
restricted to an open of `W`. In that form the condition refers only to the maps
`Scheme.Hom.appLE` of `p`, which transform across the open immersion by a single identity.

## Main definitions

* `DiffOp.RawOp.IsBaseLinear`: an operator commutes with multiplication by the sections of the
  structure sheaf of the relative base.

## Main results

* `AlgebraicGeometry.appLE_mem_range_sectionRingHom`: a section of the structure sheaf of the base,
  restricted to an open of the source, comes from a section of the inverse image of that structure
  sheaf.
* `DiffOp.RawOp.isO1Linear_iff_isBaseLinear`: for an operator compatible with restriction of
  sections, linearity over the inverse image of the structure sheaf of the base is linearity over
  the sections of that structure sheaf.
* `AlgebraicGeometry.isDiffOpOfOrder_iff_sections`: an operator is a differential operator of order
  at most `k` on `X/Y` exactly when it is compatible with restriction of sections, linear over the
  sections of the structure sheaf of `Y`, and a differential operator of order at most `k` on each
  module of sections.
* `AlgebraicGeometry.appIso_inv_comp_appLE`: the identification of the sections across an open
  immersion carries the restriction of a section of the base along `j ≫ p` to its restriction
  along `p`.
* `AlgebraicGeometry.isDiffOpOfOrder_iff_isGlobalDiffOpOfOrder_restrict`: the order predicates on
  the two sides of an open immersion correspond.
* `AlgebraicGeometry.diffOpEquivGlobalDiffOpRestrict`: the resulting equivalence of the
  differential operators of order at most `k` on the two sides.

## Implementation notes

The order predicate is decomposed, rather than transported by induction, into a part that does not
mention the sheaf of rings of scalars at all — compatibility with restriction together with the
order of the operator on each module of sections, which transports across the immersion because
the modules of sections are literally the same — and the linearity clause, which does mention it
and is handled through `DiffOp.RawOp.IsBaseLinear`. The modules of sections carry the two rings of
scalars of the two sides, related by the ring isomorphism `Scheme.Hom.appIso`, and the order of an
operator between modules is unchanged under such a change of scalars.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace LinearMap

/-- The order of a differential operator is unchanged when the ring of scalars is replaced by one
acting through a surjective ring homomorphism. -/
theorem isDifferentialOperatorOfOrderLE_iff_of_surjective {S T M N : Type*}
    [Ring S] [Ring T] [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module T M] [Module S N] [Module T N]
    (σ : S →+* T) (hσ : Function.Surjective σ)
    (hM : ∀ (s : S) (m : M), s • m = σ s • m) (hN : ∀ (s : S) (n : N), s • n = σ s • n)
    (k : ℕ) (D : M →ₗ[ℤ] N) :
    D.IsDifferentialOperatorOfOrderLE S k ↔ D.IsDifferentialOperatorOfOrderLE T k := by
  induction k generalizing D with
  | zero =>
    constructor
    · intro hD t m
      obtain ⟨s, rfl⟩ := hσ t
      rw [← hM, ← hN]
      exact hD s m
    · intro hD s m
      rw [hM, hN]
      exact hD (σ s) m
  | succ k ih =>
    have key (s : S) : (D ∘ₗ Algebra.lsmul ℤ ℤ M s - Algebra.lsmul ℤ ℤ N s ∘ₗ D) =
        D ∘ₗ Algebra.lsmul ℤ ℤ M (σ s) - Algebra.lsmul ℤ ℤ N (σ s) ∘ₗ D := by
      ext m
      show D (s • m) - s • D m = D (σ s • m) - σ s • D m
      rw [hM, hN]
    constructor
    · intro hD t
      obtain ⟨s, rfl⟩ := hσ t
      rw [← key s]
      exact (ih _).1 (hD s)
    · intro hD s
      rw [key s]
      exact (ih _).2 (hD (σ s))

end LinearMap

namespace AlgebraicGeometry

open Scheme

/-- A section of the structure sheaf of the target of a morphism of schemes, restricted to an open
of the source, is the image of a section of the inverse image of that structure sheaf. -/
theorem appLE_mem_range_sectionRingHom {W Y : Scheme.{u}} (p : W ⟶ Y) (V : Y.Opens)
    (U : W.Opens) (h : U ≤ p ⁻¹ᵁ V) (b : Γ(Y, V)) :
    ∃ a, DiffOp.sectionRingHom p.relativeStructureSheafMap (op U) a = p.appLE V U h b := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} p.base
  let P := (TopCat.Sheaf.pullback RingCat.{u} p.base).obj Y.ringCatSheaf
  let φ := p.relativeStructureSheafMap
  let η := adj.unit.app Y.ringCatSheaf
  refine ⟨P.obj.map (homOfLE h).op (η.hom.app (op V) b), ?_⟩
  have he : η ≫ (TopCat.Sheaf.pushforward RingCat.{u} p.base).map φ = p.toRingCatSheafHom :=
    adj.homEquiv _ _ |>.apply_symm_apply _
  show φ.hom.app (op U) (P.obj.map (homOfLE h).op (η.hom.app (op V) b)) = _
  rw [show φ.hom.app (op U) (P.presheaf.map (homOfLE h).op (η.hom.app (op V) b)) =
      W.presheaf.map (homOfLE h).op (φ.hom.app (op (p ⁻¹ᵁ V)) (η.hom.app (op V) b)) from
    ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE h).op) _]
  have hb := congrArg (fun m => m.hom.app (op V) b) he
  change φ.hom.app (op (p ⁻¹ᵁ V)) (η.hom.app (op V) b) = p.app V b at hb
  rw [hb]
  rfl

end AlgebraicGeometry

namespace DiffOp.RawOp

open AlgebraicGeometry

/-- An operator on the local sections of modules on `W` is *linear over the base* `p : W ⟶ Y` if it
commutes with multiplication by every section of the structure sheaf of `Y` restricted to an open
of `W`. -/
def IsBaseLinear {W Y : Scheme.{u}} (p : W ⟶ Y) {M M' : W.Modules} {U : W.Opens}
    (D : DiffOp.RawOp M M' U) : Prop :=
  ∀ (T : Over U) (V : Y.Opens) (h : T.left ≤ p ⁻¹ᵁ V) (b : Γ(Y, V)) (s : Γ(M, T.left)),
    D T (p.appLE V T.left h b • s) =
      @SMul.smul Γ(W, T.left) Γ(M', T.left) inferInstance (p.appLE V T.left h b) (D T s)

/-- An operator compatible with restriction of sections and linear over the base is linear over the
inverse image of the structure sheaf of the base: every section of that inverse image is locally
the image of a section of the structure sheaf of the base. -/
theorem isO1Linear_of_isBaseLinear {W Y : Scheme.{u}} (p : W ⟶ Y) {M M' : W.Modules}
    {U : W.Opens} (D : DiffOp.RawOp M M' U) (hnat : D.IsNatural) (hD : D.IsBaseLinear p) :
    D.IsO1Linear p.relativeStructureSheafMap := by
  intro T a s
  apply TopCat.Presheaf.IsSheaf.section_ext M'.isSheaf
  intro x hx
  obtain ⟨W₀, hW₀, V, hV, b, hxW, hb⟩ := AffineDiffOp.pullback_image_locally p.base
    Y.ringCatSheaf W.ringCatSheaf p.toRingCatSheafHom T.left a x hx
  refine ⟨W₀, hW₀, hxW, ?_⟩
  change W.presheaf.map (homOfLE hW₀).op
      (DiffOp.sectionRingHom p.relativeStructureSheafMap (op T.left) a) =
    p.appLE V W₀ hV b at hb
  have hn (z : Γ(M, T.left)) :
      D (Over.mk (homOfLE (hW₀.trans T.hom.le))) (M.presheaf.map (homOfLE hW₀).op z) =
        M'.presheaf.map (homOfLE hW₀).op (D T z) :=
    hnat (Over.mk (homOfLE (hW₀.trans T.hom.le))) T
      (Over.homMk (homOfLE hW₀) (Subsingleton.elim _ _)) z
  have e (N : W.Modules) (z : Γ(N, T.left)) :
      N.presheaf.map (homOfLE hW₀).op
          (@SMul.smul Γ(W, T.left) Γ(N, T.left) inferInstance
            (DiffOp.sectionRingHom p.relativeStructureSheafMap (op T.left) a) z) =
        p.appLE V W₀ hV b • N.presheaf.map (homOfLE hW₀).op z :=
    (AffineDiffOp.modules_presheaf_map_smul N hW₀ _ z).trans
      (congrArg (fun r => r • N.presheaf.map (homOfLE hW₀).op z) hb)
  refine (hn _).symm.trans (Eq.trans ?_ (e M' _).symm)
  refine (congrArg (fun z => D (Over.mk (homOfLE (hW₀.trans T.hom.le))) z) (e M s)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => p.appLE V W₀ hV b • z) (hn s))
  exact hD (Over.mk (homOfLE (hW₀.trans T.hom.le))) V hV b _

/-- An operator linear over the inverse image of the structure sheaf of the base is linear over the
base. -/
theorem isBaseLinear_of_isO1Linear {W Y : Scheme.{u}} (p : W ⟶ Y) {M M' : W.Modules}
    {U : W.Opens} (D : DiffOp.RawOp M M' U)
    (hD : D.IsO1Linear p.relativeStructureSheafMap) : D.IsBaseLinear p := by
  intro T V h b s
  obtain ⟨a, ha⟩ := appLE_mem_range_sectionRingHom p V T.left h b
  rw [← ha]
  exact hD T a s

/-- For an operator compatible with restriction of sections, linearity over the inverse image of
the structure sheaf of the base is the same as linearity over the base. -/
theorem isO1Linear_iff_isBaseLinear {W Y : Scheme.{u}} (p : W ⟶ Y) {M M' : W.Modules}
    {U : W.Opens} (D : DiffOp.RawOp M M' U) (hnat : D.IsNatural) :
    D.IsO1Linear p.relativeStructureSheafMap ↔ D.IsBaseLinear p :=
  ⟨isBaseLinear_of_isO1Linear p D, isO1Linear_of_isBaseLinear p D hnat⟩

end DiffOp.RawOp

namespace AlgebraicGeometry

open Scheme

/-- **The order of a differential operator, sectionwise.** An operator on the local sections of
modules on `X` is a differential operator of order at most `k` on `X/Y` exactly when it is
compatible with restriction of sections, is linear over the base, and is a differential operator of
order at most `k` between the modules of sections over each open. -/
theorem isDiffOpOfOrder_iff_sections {X Y : Scheme.{u}} (p : X ⟶ Y) {M M' : X.Modules}
    {U : X.Opens} (k : ℕ) (D : DiffOp.RawOp M M' U) :
    DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D ↔
      D.IsNatural ∧ D.IsBaseLinear p ∧
        ∀ T : Over U, (D T).toIntLinearMap.IsDifferentialOperatorOfOrderLE
          (X.ringCatSheaf.obj.obj (op T.left)) k :=
  ⟨fun h ↦ ⟨DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k D h,
      DiffOp.RawOp.isBaseLinear_of_isO1Linear p D
        (DiffOp.RawOp.isO1Linear_of_isDiffOpOfOrder _ k D h),
      fun T ↦ AffineDiffOp.rawOrder_section _ D h T⟩,
    fun h ↦ AffineDiffOp.rawOrder_of_sections _
      (fun V r s ↦ mul_comm (G := Γ(X, V.unop)) r s) D h.1
      (DiffOp.RawOp.isO1Linear_of_isBaseLinear p D h.1 h.2.1) h.2.2⟩

section OpenImmersion

variable {Z W Y : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j] (p : W ⟶ Y)

/-- An open of the source of an open immersion lies over an open of the base exactly when its image
does. -/
theorem image_le_preimage_iff {V : Y.Opens} {U : Z.Opens} :
    j ''ᵁ U ≤ p ⁻¹ᵁ V ↔ U ≤ (j ≫ p) ⁻¹ᵁ V := by
  rw [Scheme.Hom.comp_preimage]
  exact ⟨fun h ↦ (j.preimage_image_eq U).ge.trans (j.preimage_mono h),
    fun h ↦ (j.image_mono h).trans (j.image_preimage_le _)⟩

/-- Restricting a section of the structure sheaf of the base along `j ≫ p` and transporting it
across the identification of the sections over an open with the sections over its image gives its
restriction along `p`. -/
theorem appIso_inv_comp_appLE (V : Y.Opens) (U : Z.Opens) (h : U ≤ (j ≫ p) ⁻¹ᵁ V)
    (h' : j ''ᵁ U ≤ p ⁻¹ᵁ V) :
    (j ≫ p).appLE V U h ≫ (j.appIso U).inv = p.appLE V (j ''ᵁ U) h' := by
  have e2 : U ≤ j ⁻¹ᵁ (j ''ᵁ U) := (j.preimage_image_eq U).ge
  calc (j ≫ p).appLE V U h ≫ (j.appIso U).inv
      = (p.appLE V (j ''ᵁ U) h' ≫ j.appLE (j ''ᵁ U) U e2) ≫ (j.appIso U).inv := by
        rw [Scheme.Hom.appLE_comp_appLE]
    _ = p.appLE V (j ''ᵁ U) h' ≫ (j.appLE (j ''ᵁ U) U e2 ≫ (j.appIso U).inv) :=
        Category.assoc _ _ _
    _ = p.appLE V (j ''ᵁ U) h' := by
        rw [Scheme.Hom.appLE_appIso_inv,
          show (homOfLE ((j.image_mono e2).trans
              (j.image_preimage_eq_opensRange_inf (j ''ᵁ U) ▸ inf_le_right))
                : j ''ᵁ U ⟶ j ''ᵁ U) = 𝟙 _ from Subsingleton.elim _ _]
        simp

/-- Multiplication on the sections of the restriction of `M` along an open immersion is
multiplication on the sections of `M` over the image, along the identification of the structure
sheaves. -/
theorem Scheme.Modules.restrict_smul (M : W.Modules) (U : Z.Opens) (r : Γ(Z, U))
    (x : Γ(M, j ''ᵁ U)) :
    @SMul.smul Γ(Z, U) Γ(M.restrict j, U) inferInstance r x =
      @SMul.smul Γ(W, j ''ᵁ U) Γ(M, j ''ᵁ U) inferInstance ((j.appIso U).inv r) x := rfl

/-- Multiplication by a section of the structure sheaf of the base restricted along `j ≫ p` is
multiplication by its restriction along `p`. -/
theorem appLE_smul_eq (M : W.Modules) (V : Y.Opens) (U : Z.Opens)
    (h : U ≤ (j ≫ p) ⁻¹ᵁ V) (h' : j ''ᵁ U ≤ p ⁻¹ᵁ V) (b : Γ(Y, V)) (x : Γ(M, j ''ᵁ U)) :
    @SMul.smul Γ(Z, U) Γ(M.restrict j, U) inferInstance ((j ≫ p).appLE V U h b) x =
      @SMul.smul Γ(W, j ''ᵁ U) Γ(M, j ''ᵁ U) inferInstance (p.appLE V (j ''ᵁ U) h' b) x := by
  have key : (j.appIso U).inv ((j ≫ p).appLE V U h b) = p.appLE V (j ''ᵁ U) h' b := by
    simpa using ConcreteCategory.congr_hom (appIso_inv_comp_appLE j p V U h h') b
  exact congrArg
    (fun r ↦ @SMul.smul Γ(W, j ''ᵁ U) Γ(M, j ''ᵁ U) inferInstance r x) key

/-- The identification of the sections of the structure sheaf of `Z` over `U` with the sections
over the image of `U`, as a homomorphism of the rings of sections of the underlying sheaves of
rings. -/
noncomputable def ringCatAppIsoInv (U : Z.Opens) :
    Z.ringCatSheaf.obj.obj (op U) →+* W.ringCatSheaf.obj.obj (op (j ''ᵁ U)) :=
  (j.appIso U).inv.hom

/-- The sections of `M` over the image of an open `U` of `Z`, as a module over the sections of the
sheaf of rings underlying the structure sheaf of `Z` over `U`. -/
@[instance_reducible]
noncomputable def moduleImageSections (M : W.Modules) (U : Z.Opens) :
    Module (Z.ringCatSheaf.obj.obj (op U)) (M.val.obj (op (j ''ᵁ U))) :=
  inferInstanceAs (Module (Z.ringCatSheaf.obj.obj (op U)) ((M.restrict j).val.obj (op U)))

attribute [local instance] moduleImageSections

/-- Multiplication on the sections of the restriction of `M` along an open immersion is
multiplication on the sections of `M` over the image, along the identification of the sheaves of
rings underlying the structure sheaves. -/
theorem Scheme.Modules.ringCat_restrict_smul (M : W.Modules) (U : Z.Opens)
    (r : Z.ringCatSheaf.obj.obj (op U)) (x : M.val.obj (op (j ''ᵁ U))) :
    r • x = ringCatAppIsoInv j U r • x := rfl

/-- The identification of the sections of the structure sheaves across an open immersion is
surjective. -/
theorem ringCatAppIsoInv_surjective (U : Z.Opens) :
    Function.Surjective (ringCatAppIsoInv j U) := fun y ↦
  ⟨(j.appIso U).hom y, ConcreteCategory.congr_hom (j.appIso U).hom_inv_id y⟩

/-- The order of an operator between the modules of sections over an open of the source of an open
immersion does not depend on which of the two structure sheaves provides the scalars. -/
theorem sectionOrder_restrict_iff (M M' : W.Modules) (U : Z.Opens) (k : ℕ)
    (D : M.val.obj (op (j ''ᵁ U)) →+ M'.val.obj (op (j ''ᵁ U))) :
    D.toIntLinearMap.IsDifferentialOperatorOfOrderLE (Z.ringCatSheaf.obj.obj (op U)) k ↔
      D.toIntLinearMap.IsDifferentialOperatorOfOrderLE
        (W.ringCatSheaf.obj.obj (op (j ''ᵁ U))) k :=
  LinearMap.isDifferentialOperatorOfOrderLE_iff_of_surjective (ringCatAppIsoInv j U)
    (ringCatAppIsoInv_surjective j U) (Scheme.Modules.ringCat_restrict_smul j M U)
    (Scheme.Modules.ringCat_restrict_smul j M' U) k _

/-- Compatibility with restriction of sections corresponds across an open immersion. -/
theorem isNatural_restrict_iff (M M' : W.Modules) (D : DiffOp.RawOp M M' j.opensRange) :
    D.IsNatural ↔ ∀ U : Z.Opens,
      ((rawOpEquivGlobalOpRestrict j M M' D).restrict U).IsNatural := by
  refine ⟨fun hD U T T' hh s ↦ hD (imageOver j T.left) (imageOver j T'.left)
    (Over.homMk (j.opensFunctor.map hh.left) (Subsingleton.elim _ _)) s, fun hE T T' hh s ↦ ?_⟩
  obtain ⟨V, rfl⟩ := exists_imageOver j T
  obtain ⟨V', rfl⟩ := exists_imageOver j T'
  have hVV' : V ≤ V' := (j.image_le_image_iff V V').1 hh.left.le
  exact hE V' (Over.mk (homOfLE hVV')) (Over.mk (𝟙 V'))
    (Over.homMk (homOfLE hVV') (Subsingleton.elim _ _)) s

/-- Linearity over the base corresponds across an open immersion. -/
theorem isBaseLinear_restrict_iff (M M' : W.Modules) (D : DiffOp.RawOp M M' j.opensRange) :
    D.IsBaseLinear p ↔ ∀ U : Z.Opens,
      ((rawOpEquivGlobalOpRestrict j M M' D).restrict U).IsBaseLinear (j ≫ p) := by
  constructor
  · intro hD U T V h b s
    have h' : j ''ᵁ T.left ≤ p ⁻¹ᵁ V := (image_le_preimage_iff j p).2 h
    exact (congrArg (fun z ↦ D (imageOver j T.left) z)
        (appLE_smul_eq j p M V T.left h h' b s)).trans
      ((hD (imageOver j T.left) V h' b s).trans
        (appLE_smul_eq j p M' V T.left h h' b (D (imageOver j T.left) s)).symm)
  · intro hE T V h b s
    obtain ⟨U, rfl⟩ := exists_imageOver j T
    have hZ : U ≤ (j ≫ p) ⁻¹ᵁ V := (image_le_preimage_iff j p).1 h
    exact (congrArg (fun z ↦ D (imageOver j U) z)
        (appLE_smul_eq j p M V U hZ h b s).symm).trans
      ((hE U (Over.mk (𝟙 U)) V hZ b s).trans
        (appLE_smul_eq j p M' V U hZ h b (D (imageOver j U) s)))

/-- **The order of a differential operator across an open immersion.** An operator on the local
sections of modules on `W`, defined over the opens contained in the image of an open immersion
`j : Z ⟶ W`, is a differential operator of order at most `k` on `W/Y` exactly when the
corresponding global operator on the restrictions to `Z` is a differential operator of order at
most `k` on `Z/Y`. -/
theorem isDiffOpOfOrder_iff_isGlobalDiffOpOfOrder_restrict (M M' : W.Modules) (k : ℕ)
    (D : DiffOp.RawOp M M' j.opensRange) :
    DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D ↔
      DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k
        (rawOpEquivGlobalOpRestrict j M M' D) := by
  rw [isDiffOpOfOrder_iff_sections]
  constructor
  · rintro ⟨hnat, hlin, hsec⟩ U
    refine (isDiffOpOfOrder_iff_sections (j ≫ p) k _).2
      ⟨(isNatural_restrict_iff j M M' D).1 hnat U,
        (isBaseLinear_restrict_iff j p M M' D).1 hlin U, fun T ↦ ?_⟩
    exact (sectionOrder_restrict_iff j M M' T.left k _).2 (hsec (imageOver j T.left))
  · intro hE
    have hcomp : ∀ U : Z.Opens, _ ∧ _ ∧ _ := fun U ↦
      (isDiffOpOfOrder_iff_sections (j ≫ p) k _).1 (hE U)
    refine ⟨(isNatural_restrict_iff j M M' D).2 (fun U ↦ (hcomp U).1),
      (isBaseLinear_restrict_iff j p M M' D).2 (fun U ↦ (hcomp U).2.1), fun T ↦ ?_⟩
    obtain ⟨U, rfl⟩ := exists_imageOver j T
    exact (sectionOrder_restrict_iff j M M' U k _).1 ((hcomp U).2.2 (Over.mk (𝟙 U)))

/-- **Differential operators across an open immersion.** The differential operators of order at
most `k` on `W/Y` between modules on `W`, defined over the opens contained in the image of an open
immersion `j : Z ⟶ W`, are the differential operators of order at most `k` on `Z/Y` between the
restrictions of those modules to `Z`. -/
noncomputable def diffOpEquivGlobalDiffOpRestrict (M M' : W.Modules) (k : ℕ) :
    {D : DiffOp.RawOp M M' j.opensRange //
        DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D} ≃
      {E : DiffOp.GlobalOp (M.restrict j) (M'.restrict j) //
        DiffOp.IsGlobalDiffOpOfOrder (j ≫ p).relativeStructureSheafMap k E} :=
  Equiv.subtypeEquiv (rawOpEquivGlobalOpRestrict j M M')
    (isDiffOpOfOrder_iff_isGlobalDiffOpOfOrder_restrict j p M M' k)

/-- The differential operator on `Z/Y` corresponding to one on `W/Y` is its value at the image of
the open. -/
theorem diffOpEquivGlobalDiffOpRestrict_coe_apply (M M' : W.Modules) (k : ℕ)
    (D : {D : DiffOp.RawOp M M' j.opensRange //
      DiffOp.IsDiffOpOfOrder p.relativeStructureSheafMap k D}) (V : Z.Opens) :
    (diffOpEquivGlobalDiffOpRestrict j p M M' k D).1 (op V) = D.1 (imageOver j V) := rfl

end OpenImmersion

end AlgebraicGeometry

end
