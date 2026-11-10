module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Stalk
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# The universal property of the zero scheme of a section of a finite locally free module

Let `ℰ` be finite locally free of rank `r` on a scheme `X` and `s ∈ Γ(X, ℰ)`. A morphism
`f : Y ⟶ X` factors through the zero scheme `Z(s)` exactly when the pulled-back section `f^* s`
vanishes. Consequently the zero scheme of `f^* s` is the scheme-theoretic inverse image of `Z(s)`:

  `Z(f^* s) = f⁻¹(Z(s))`.

These are [Stacks, Tag 02OR] (the factorization clause) and [Stacks, Tag 0B6Y] for a module of
any rank; for an invertible module they are
`Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme` and
`Stacks.Divisors.zeroScheme_pullback`.

## Main results

* `Stacks.Chow.SectionZeroScheme.pullbackGlobalSections_eq_zero_iff_factorsThrough` — the
  universal property.
* `Stacks.Chow.SectionZeroScheme.zeroSchemeOfSection_pullback` — the pulled-back zero scheme.

## Implementation notes

The proof is the one for an invertible module, with a frame `ℰ|_U ≅ 𝒪_U^{⊕ r}` in place of a
trivialization: over the frame the pulled-back section vanishes exactly when the pullbacks of its
`r` coordinates do, because the coordinate forms and the frame vectors of a frame decompose the
identity of `ℰ|_U` and the pullback functor is additive.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.SectionZeroScheme

open Stacks.SheafOfModules Stacks.Divisors

/-- The coordinate forms and frame vectors of a frame decompose the identity. -/
theorem id_eq_sum_frame {X : Scheme.{u}} {M : X.Modules} {r : ℕ}
    (e : M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    𝟙 M = ∑ i, (e.hom ≫ freeProj i) ≫ (SheafOfModules.ιFree i ≫ e.inv) := by
  classical
  refine (e.hom_inv_id.symm.trans
    ((congrArg (fun φ => e.hom ≫ φ) (Category.id_comp e.inv).symm).trans
      (congrArg (fun φ => e.hom ≫ φ ≫ e.inv) id_free_eq_sum))).trans ?_
  exact (congrArg (fun φ => e.hom ≫ φ) (Preadditive.sum_comp _ _ _)).trans
    ((Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun i _ =>
      (congrArg (fun φ => e.hom ≫ φ) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm))

/-- Pulling back sections is natural in the module. -/
theorem pullback_map_app_pullbackGlobalSections {X Y : Scheme.{u}} (g : Y ⟶ X) {M N : X.Modules}
    (φ : M ⟶ N) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ (pullbackGlobalSections g M m) =
      pullbackGlobalSections g N (φ.app ⊤ m) :=
  (congrArg (fun z => ((Scheme.Modules.pullback g).map φ).app ⊤ z)
      (congrArg (fun ψ : Γ(M, ⊤) ⟶ Γ((Scheme.Modules.pullback g).obj M, ⊤) => ψ m)
        (pullbackGlobalSections_eq_unit g M))).trans
    ((pullbackGlobalSections_naturality g φ m).trans
      (congrArg (fun ψ : Γ(N, ⊤) ⟶ Γ((Scheme.Modules.pullback g).obj N, ⊤) =>
          ψ (φ.app ⊤ m)) (pullbackGlobalSections_eq_unit g N)).symm)

/-- Pulling back a composite acts on sections as the composite of the pullbacks. -/
theorem pullback_map_comp_app_apply {X Y : Scheme.{u}} (g : Y ⟶ X) {M N P : X.Modules}
    (a : M ⟶ N) (b : N ⟶ P) (x : Γ((Scheme.Modules.pullback g).obj M, ⊤)) :
    ((Scheme.Modules.pullback g).map (a ≫ b)).app ⊤ x =
      ((Scheme.Modules.pullback g).map b).app ⊤ (((Scheme.Modules.pullback g).map a).app ⊤ x) := by
  rw [Functor.map_comp]
  rfl

/-- A finite sum of morphisms of modules acts on sections as the sum of the actions. -/
theorem sum_app_apply {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} (t : Finset ι)
    (φ : ι → (M ⟶ N)) (U : X.Opens) (m : Γ(M, U)) :
    (∑ i ∈ t, φ i).app U m = ∑ i ∈ t, (φ i).app U m :=
  Stacks.SheafOfModules.app_sum t φ (Opposite.op U) m

/-- **Over a frame, a pulled-back section vanishes exactly when the pullbacks of its coordinates
do.** -/
theorem pullbackGlobalSections_eq_zero_iff_frame {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    {r : ℕ} (e : M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) (m : Γ(M, ⊤))
    [(SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint]
    [(TopologicalSpace.Opens.map g.base).Final]
    [IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)] :
    pullbackGlobalSections g M m = 0 ↔
      ∀ i, g.app ⊤ ((e.hom ≫ freeProj i).app ⊤ m) = 0 := by
  have hunit : ∀ a : Γ(SheafOfModules.unit X.ringCatSheaf, ⊤),
      pullbackGlobalSections g (SheafOfModules.unit X.ringCatSheaf) a = 0 ↔ g.app ⊤ a = 0 :=
    fun a => pullbackGlobalSections_eq_zero_iff_frame_appTop g _ (Iso.refl _) a
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · exact (hunit _).mp ((pullback_map_app_pullbackGlobalSections g _ m).symm.trans
      ((congrArg (fun z => ((Scheme.Modules.pullback g).map (e.hom ≫ freeProj i)).app ⊤ z) h).trans
        (map_zero _)))
  · have hi : ∀ i, ((Scheme.Modules.pullback g).map (e.hom ≫ freeProj i)).app ⊤
        (pullbackGlobalSections g M m) = 0 := fun i =>
      (pullback_map_app_pullbackGlobalSections g _ m).trans ((hunit _).mpr (h i))
    have hid : pullbackGlobalSections g M m =
        ((Scheme.Modules.pullback g).map (𝟙 M)).app ⊤ (pullbackGlobalSections g M m) := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hid, id_eq_sum_frame e, Functor.map_sum, sum_app_apply]
    exact Finset.sum_eq_zero fun i _ => (pullback_map_comp_app_apply g _ _ _).trans
      ((congrArg (fun z => ((Scheme.Modules.pullback g).map
        (SheafOfModules.ιFree i ≫ e.inv)).app ⊤ z) (hi i)).trans (map_zero _))

/-- Over a frame `(U, e)`, the pulled-back section vanishes on `f⁻¹(U)` exactly when the
pullbacks of the coordinates of `s|_U` vanish. -/
theorem pullbackGlobalSections_local_frame_iff {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    (s : Γ(F, ⊤)) (U : X.Opens) {r : ℕ}
    (e : F.restrict U.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map
        (homOfLE (show (f ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
        (pullbackGlobalSections f F s) = 0 ↔
      ∀ i, f.app (U.ι ''ᵁ ⊤) (frameCoord F U e i (F.presheaf.map (homOfLE le_top).op s)) = 0 := by
  let g := f ∣_ U
  have hcomp : g ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  rw [← pullbackGlobalSections_open_eq_zero_iff,
    ← pullbackGlobalSections_comp_eq_zero_iff, ← hcomp,
    pullbackGlobalSections_comp_eq_zero_iff, ← pullbackGlobalSections_open U.ι F s]
  have : (TopologicalSpace.Opens.map g.base).Final := opensMap_final g
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal g.toRingCatSheafHom
  refine Iff.trans (pullbackGlobalSections_hom_eq_zero_iff g
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app F)
    (F.presheaf.map (homOfLE le_top).op s)) ?_
  refine Iff.trans (pullbackGlobalSections_eq_zero_iff_frame g (F.restrict U.ι) e
    (F.presheaf.map (homOfLE le_top).op s)) ?_
  refine forall_congr' fun i => ?_
  change g.app ⊤ ((e.hom ≫ freeProj i).app ⊤ (F.presheaf.map (homOfLE le_top).op s)) = 0 ↔
    f.app (U.ι ''ᵁ ⊤) ((e.hom ≫ freeProj i).app ⊤ (F.presheaf.map (homOfLE le_top).op s)) = 0
  dsimp only [g]
  rw [morphismRestrict_app]
  exact map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).injective

/-- Over an affine open carrying a frame, the pulled-back section vanishes on `f⁻¹(U)` exactly
when the ideal of the zero scheme on `U` is carried to zero by `f`. -/
theorem pullbackGlobalSections_local_ideal_iff {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    (s : Γ(F, ⊤)) (U : X.affineOpens) {r : ℕ}
    (e : F.restrict U.1.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map
        (homOfLE (show f ⁻¹ᵁ U.1 ≤ ⊤ from le_top)).op
        (pullbackGlobalSections f F s) = 0 ↔
      (zeroSchemeOfSection X F s).ideal U ≤ RingHom.ker (f.app U.1).hom := by
  let W : X.affineOpens := ⟨U.1.ι ''ᵁ ⊤, isAffineOpen_image_top U.2⟩
  have hW : W = U := Subtype.ext (by simp [W])
  have h := pullbackGlobalSections_local_frame_iff f F s U.1 e
  have hspan : (zeroSchemeOfSection X F s).ideal W ≤ RingHom.ker (f.app W.1).hom ↔
      ∀ i, f.app W.1 (frameCoord F U.1 e i (F.presheaf.map (homOfLE le_top).op s)) = 0 := by
    rw [zeroSchemeOfSection_ideal_frame F U.1 e s W.2, Ideal.span_le, Set.range_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker]
  rw [← hspan, hW] at h
  exact (restriction_eq_zero_congr ((Scheme.Modules.pullback f).obj F)
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U.1)).symm (pullbackGlobalSections f F s)).trans h

/-- **The universal property of the zero scheme, [Stacks, Tag 02OR] for a module of any rank.**
A global section `s` of a finite locally free module `ℰ` on `X` vanishes after pullback along
`f : Y ⟶ X` if and only if `f` factors through the zero scheme of `s`. -/
theorem pullbackGlobalSections_eq_zero_iff_factorsThrough {X : Scheme.{u}} (F : X.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (s : Γ(F, ⊤)) {Y : Scheme.{u}} (f : Y ⟶ X) :
    pullbackGlobalSections f F s = 0 ↔
      ∃ g : Y ⟶ (zeroSchemeOfSection X F s).subscheme,
        g ≫ (zeroSchemeOfSection X F s).subschemeι = f := by
  classical
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  rw [_root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker]
  refine ⟨fun hs => ?_, fun hI => ?_⟩
  · apply ideal_le_ker_of_locally f (zeroSchemeOfSection X F s)
    intro W x hx
    obtain ⟨U, hU, hxU, hUW, ⟨e⟩⟩ := exists_frame F r (W := W.1) hx
    refine ⟨⟨U, hU⟩, hxU, hUW, ?_⟩
    apply (pullbackGlobalSections_local_ideal_iff f F s ⟨U, hU⟩ e).mp
    simp [hs]
  · choose U hU hy _ e using fun y : Y => exists_frame F r (W := ⊤) (x := f y) trivial
    let V (y : Y) : Y.Opens := f ⁻¹ᵁ (U y)
    let G : TopCat.Sheaf AddCommGrpCat Y :=
      ⟨((Scheme.Modules.pullback f).obj F).presheaf,
        ((Scheme.Modules.pullback f).obj F).isSheaf⟩
    have hcover : (⊤ : Y.Opens) ≤ ⨆ y, V y := fun y _ =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
    apply G.eq_of_locally_eq' V ⊤ (fun _ => homOfLE le_top) hcover
    intro y
    simpa only [map_zero] using (pullbackGlobalSections_local_ideal_iff f F s ⟨U y, hU y⟩
      (e y).some).mpr ((hI ⟨U y, hU y⟩).trans (f.ideal_ker_le ⟨U y, hU y⟩))

/-- The section `s` vanishes on its zero scheme. -/
theorem pullbackGlobalSections_subschemeι_eq_zero {X : Scheme.{u}} (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (s : Γ(F, ⊤)) :
    pullbackGlobalSections (zeroSchemeOfSection X F s).subschemeι F s = 0 :=
  (pullbackGlobalSections_eq_zero_iff_factorsThrough F r s
    (zeroSchemeOfSection X F s).subschemeι).2 ⟨𝟙 _, by simp⟩

/-- **[Stacks, Tag 0B6Y] for a module of any rank.** The zero scheme of the pulled-back section
is the scheme-theoretic inverse image of the zero scheme: `Z(f^* s) = f⁻¹(Z(s))`. -/
theorem zeroSchemeOfSection_pullback {X X' : Scheme.{u}} (f : X' ⟶ X) (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (s : Γ(F, ⊤)) :
    zeroSchemeOfSection X' ((Scheme.Modules.pullback f).obj F) (pullbackGlobalSections f F s) =
      (zeroSchemeOfSection X F s).comap f := by
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f F r
  let D' := zeroSchemeOfSection X' ((Scheme.Modules.pullback f).obj F)
    (pullbackGlobalSections f F s)
  let D := zeroSchemeOfSection X F s
  let i' := D'.subschemeι
  let i := D.subschemeι
  have hiff {T : Scheme.{u}} (t : T ⟶ X') :
      pullbackGlobalSections t ((Scheme.Modules.pullback f).obj F) (pullbackGlobalSections f F s) =
        0 ↔ pullbackGlobalSections (t ≫ f) F s = 0 := by
    rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp t f F s]
    exact (map_eq_zero_iff _ (pullbackGlobalSections_injective_pullbackComp t f F)).symm
  obtain ⟨g, hg⟩ :=
    (pullbackGlobalSections_eq_zero_iff_factorsThrough F r s (i' ≫ f)).mp ((hiff i').mp
      (pullbackGlobalSections_subschemeι_eq_zero _ r (pullbackGlobalSections f F s)))
  have hpb : IsPullback i' g f i := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk i' g hg.symm) ?_
    choose lift lift_fst using fun c : PullbackCone f i =>
      show ∃ l : c.pt ⟶ D'.subscheme, l ≫ i' = c.fst from
        (pullbackGlobalSections_eq_zero_iff_factorsThrough ((Scheme.Modules.pullback f).obj F) r
          (pullbackGlobalSections f F s) c.fst).mp <| (hiff c.fst).mpr <| by
          rw [c.condition,
            ← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp c.snd i F s,
            pullbackGlobalSections_subschemeι_eq_zero F r s]
          simp
    have lift_snd (c : PullbackCone f i) : lift c ≫ g = c.snd := by
      refine (cancel_mono i).1 ?_
      rw [Category.assoc, hg, ← Category.assoc, lift_fst, c.condition]
    exact PullbackCone.IsLimit.mk hg.symm lift lift_fst lift_snd
      fun c m hleft _ => (cancel_mono i').1 (hleft.trans (lift_fst c).symm)
  calc
    D' = Scheme.Hom.ker i' := (Scheme.IdealSheafData.ker_subschemeι D').symm
    _ = Scheme.Hom.ker (pullback.fst f i) :=
        (congrArg Scheme.Hom.ker hpb.isoPullback_hom_fst).symm.trans
          (Scheme.Hom.ker_comp_of_isIso _ _)
    _ = D.comap f := rfl

end Stacks.Chow.SectionZeroScheme

end
