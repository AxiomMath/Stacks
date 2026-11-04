module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.ExtensionByZero
public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic

/-!
# Restricting a system of schemes to an open of the base, and the reduction to affine opens

For a directed system `j ↦ T_j` of schemes over a base `B` with a cone `T`, and an open `U` of
`B`, the preimages `k_j⁻¹U ⊆ T_j` and `k⁻¹U ⊆ T` form a system over `U`. This file proves the
induction step of the proof of Stacks 09RE: the statement that `Hom(Lk^*X, Lk^*Y)` is the
filtered colimit of the `Hom(Lk_j^*X, Lk_j^*Y)`, read on the restriction to an open and for all
shifts of `X`, passes from two opens and their intersection to their union, by the
Mayer--Vietoris triangle of Stacks 08BU and the five lemma; by the induction principle of
Stacks 08DR it then holds on a quasi-compact quasi-separated base as soon as it holds on the
restrictions to the affine opens.

## Main definitions

* `Stacks.LimitHomDescent.SchemeSystem.restrict`: the restriction of a system to an open of the
  base.
* `Stacks.LimitHomDescent.SchemeSystem.restrictInclusion`: the inclusion of the restriction to a
  smaller open.

## Main results

* `Stacks.LimitHomDescent.SchemeSystem.isColim_restrict_extensionRestriction_iff`: at an
  extension by zero from a smaller open, the statement on the restriction to the larger open is
  the statement on the restriction to the smaller one.
* `Stacks.LimitHomDescent.SchemeSystem.restrictIsColim_sup`: the union step.
* `Stacks.LimitHomDescent.SchemeSystem.isColim_of_isAffineOpen`: the reduction to affine opens.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.ExtensionByZero (derivedRestriction derivedExtensionRestriction)
open Stacks.DerivedPullback (schemeFactorIso schemeFactorHom)

attribute [local instance 10000] HasDerivedCategory.standard

universe v u

namespace Stacks.LimitHomDescent

namespace SchemeSystem

variable {B : Scheme.{u}} {J : Type v} [Preorder J] (S : SchemeSystem.{v, u} B J)

/-! ### Morphisms of systems inducing bijections -/

/-- The map of morphism sets induced by a factorisation `f ≫ g = k` is bijective as soon as the
derived pullback along `f` is bijective on morphisms. -/
private theorem bijective_schemeFactorHom {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ B)
    (k : X ⟶ B) (h : f ≫ g = k) (M N : DMod B)
    (hf : Function.Bijective (fun φ : (pb g).obj M ⟶ (pb g).obj N => (pb f).map φ)) :
    Function.Bijective (schemeFactorHom f g k h M N) :=
  (Equiv.bijective (Iso.homCongr ((schemeFactorIso f g k h).app M)
    ((schemeFactorIso f g k h).app N))).comp hf

/-- A morphism of systems whose components are isomorphisms induces bijections on the morphism
sets. -/
theorem Hom.isColim_iff_of_isIso {S' : SchemeSystem.{v, u} B J} (α : Hom S' S)
    [∀ j, IsIso (α.app j)] [IsIso α.limitApp] (X Y : DMod B) :
    S.IsColim X Y ↔ S'.IsColim X Y := by
  refine α.isColim_iff X Y (fun j => ?_) ?_
  · exact bijective_schemeFactorHom _ _ _ _ _ _
      (Stacks.DerivedPullback.bijective_derivedPullback_map
      (α.app j).toLRSHom.toShHom (inv (α.app j)).toLRSHom.toShHom
      (congrArg (fun m => m.toLRSHom.toShHom) (IsIso.hom_inv_id (α.app j)))
      (congrArg (fun m => m.toLRSHom.toShHom) (IsIso.inv_hom_id (α.app j))) _ _)
  · exact bijective_schemeFactorHom _ _ _ _ _ _
      (Stacks.DerivedPullback.bijective_derivedPullback_map
      α.limitApp.toLRSHom.toShHom (inv α.limitApp).toLRSHom.toShHom
      (congrArg (fun m => m.toLRSHom.toShHom) (IsIso.hom_inv_id α.limitApp))
      (congrArg (fun m => m.toLRSHom.toShHom) (IsIso.inv_hom_id α.limitApp)) _ _)

/-- **A morphism of systems by open immersions onto the preimages of an open `V` of the base
induces bijections on morphism sets out of an extension by zero from `V`.** -/
theorem Hom.isColim_iff_of_extensionRestriction {S' : SchemeSystem.{v, u} B J} (α : Hom S' S)
    [∀ j, IsOpenImmersion (α.app j)] [IsOpenImmersion α.limitApp] (V : B.Opens)
    (hα : ∀ j, (α.app j).opensRange = S.toBase j ⁻¹ᵁ V)
    (hαL : α.limitApp.opensRange = S.limitToBase ⁻¹ᵁ V) {X X' : DMod B}
    (e : X ≅ (derivedExtensionRestriction (structureSheafRing B.toRingedSpace) V).obj X')
    (Y : DMod B) : S.IsColim X Y ↔ S'.IsColim X Y := by
  refine α.isColim_iff X Y (fun j => ?_) ?_
  · exact bijective_schemeFactorHom _ _ _ _ _ _ (bijective_pb_map_of_iso_extensionRestriction
      (α.app j) ((pb (S.toBase j)).mapIso e ≪≫ pbExtensionRestrictionIso (S.toBase j) V X' ≪≫
        eqToIso (by rw [hα j])) _)
  · exact bijective_schemeFactorHom _ _ _ _ _ _ (bijective_pb_map_of_iso_extensionRestriction
      α.limitApp ((pb S.limitToBase).mapIso e ≪≫ pbExtensionRestrictionIso S.limitToBase V X' ≪≫
        eqToIso (by rw [hαL])) _)

/-! ### The restriction to an open of the base -/

/-- Two morphisms into an open subscheme agree as soon as their composites with the inclusion
agree. -/
theorem ext_ι {X Y : Scheme.{u}} {U : Y.Opens} {a b : X ⟶ U.toScheme}
    (h : a ≫ U.ι = b ≫ U.ι) : a = b :=
  (cancel_mono U.ι).1 h

/-- **The restriction of a system to an open `U` of the base**: the preimages of `U` in the
stages and in the vertex, as a system over `U`. -/
def restrict (U : B.Opens) : SchemeSystem.{v, u} U.toScheme J where
  stage j := (S.toBase j ⁻¹ᵁ U).toScheme
  toBase j := (S.toBase j).resLE U _ le_rfl
  transition {i j} h := (S.transition h).resLE (S.toBase i ⁻¹ᵁ U) (S.toBase j ⁻¹ᵁ U)
    (le_of_eq (by rw [← Scheme.Hom.comp_preimage, S.transition_toBase]))
  transition_toBase h := by
    rw [← cancel_mono U.ι]
    simp [S.transition_toBase]
  transition_comp h h' := by
    apply ext_ι
    simp [← S.transition_comp h h']
  transition_refl i := by
    apply ext_ι
    simp [S.transition_refl i]
  limit := (S.limitToBase ⁻¹ᵁ U).toScheme
  limitToBase := S.limitToBase.resLE U _ le_rfl
  proj j := (S.proj j).resLE (S.toBase j ⁻¹ᵁ U) (S.limitToBase ⁻¹ᵁ U)
    (le_of_eq (by rw [← Scheme.Hom.comp_preimage, S.proj_toBase]))
  proj_toBase j := by
    rw [← cancel_mono U.ι]
    simp [S.proj_toBase]
  proj_transition h := by
    apply ext_ι
    simp [S.proj_transition h]

/-- The inclusion of the restriction to an open `V` of the base, read over `B`, into the
system. -/
def restrictι (V : B.Opens) : Hom ((S.restrict V).comp V.ι) S where
  app j := (S.toBase j ⁻¹ᵁ V).ι
  app_toBase j := by simp [comp, restrict]
  app_transition h := by simp [comp, restrict]
  limitApp := (S.limitToBase ⁻¹ᵁ V).ι
  limitApp_toBase := by simp [comp, restrict]
  limitApp_proj j := by simp [comp, restrict]

/-- The components of the inclusion of the restriction to `V` are open immersions. -/
instance (V : B.Opens) (j : J) : IsOpenImmersion ((S.restrictι V).app j) :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

/-- The vertex component of the inclusion of the restriction to `V` is an open immersion. -/
instance (V : B.Opens) : IsOpenImmersion (S.restrictι V).limitApp :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

/-- The inclusion of the restriction to `V` into the restriction to `W ≥ V`, over `W`. -/
def restrictInclusion {V W : B.Opens} (hVW : V ≤ W) :
    Hom ((S.restrict V).comp (B.homOfLE hVW)) (S.restrict W) where
  app j := (S.stage j).homOfLE (Scheme.Hom.preimage_mono (S.toBase j) hVW)
  app_toBase j := by
    apply ext_ι
    simp [comp, restrict]
  app_transition h := by
    apply ext_ι
    simp [comp, restrict]
  limitApp := S.limit.homOfLE (Scheme.Hom.preimage_mono S.limitToBase hVW)
  limitApp_toBase := by
    apply ext_ι
    simp [comp, restrict]
  limitApp_proj j := by
    apply ext_ι
    simp [comp, restrict]

/-- The components of the inclusion of the restriction to `V` into the restriction to `W` are
open immersions. -/
instance {V W : B.Opens} (hVW : V ≤ W) (j : J) :
    IsOpenImmersion ((S.restrictInclusion hVW).app j) :=
  inferInstanceAs (IsOpenImmersion
    ((S.stage j).homOfLE (Scheme.Hom.preimage_mono (S.toBase j) hVW)))

/-- The vertex component of the inclusion of the restriction to `V` into the restriction to `W`
is an open immersion. -/
instance {V W : B.Opens} (hVW : V ≤ W) : IsOpenImmersion (S.restrictInclusion hVW).limitApp :=
  inferInstanceAs (IsOpenImmersion
    (S.limit.homOfLE (Scheme.Hom.preimage_mono S.limitToBase hVW)))

/-- The image of the `j`-th component of `restrictInclusion hVW` is the preimage of `V`, read
in `W`, in the `j`-th stage of the restriction to `W`. -/
theorem restrictInclusion_opensRange {V W : B.Opens} (hVW : V ≤ W) (j : J) :
    ((S.restrictInclusion hVW).app j).opensRange = (S.restrict W).toBase j ⁻¹ᵁ (W.ι ⁻¹ᵁ V) :=
  (Scheme.opensRange_homOfLE (Scheme.Hom.preimage_mono (S.toBase j) hVW)).trans
    (congrArg (fun f => f ⁻¹ᵁ V) (Scheme.Hom.resLE_comp_ι (S.toBase j) le_rfl).symm)

/-- The image of the vertex component of `restrictInclusion hVW` is the preimage of `V`, read
in `W`, in the vertex of the restriction to `W`. -/
theorem restrictInclusion_limit_opensRange {V W : B.Opens} (hVW : V ≤ W) :
    (S.restrictInclusion hVW).limitApp.opensRange =
      (S.restrict W).limitToBase ⁻¹ᵁ (W.ι ⁻¹ᵁ V) :=
  (Scheme.opensRange_homOfLE (Scheme.Hom.preimage_mono S.limitToBase hVW)).trans
    (congrArg (fun f => f ⁻¹ᵁ V) (Scheme.Hom.resLE_comp_ι S.limitToBase le_rfl).symm)

/-- Each component of the inclusion of the restriction to `⊤` into the system is an
isomorphism. -/
instance (j : J) : IsIso ((S.restrictι ⊤).app j) :=
  inferInstanceAs (IsIso (S.stage j).topIso.hom)

/-- The vertex component of the inclusion of the restriction to `⊤` into the system is an
isomorphism. -/
instance : IsIso (S.restrictι ⊤).limitApp :=
  inferInstanceAs (IsIso S.limit.topIso.hom)

/-! ### The union step -/

variable [IsDirected J (· ≤ ·)]

/-- **The statement at an extension by zero from a smaller open.** On the restriction to `W`, at
`j_{V'!}(E|_{V'})` with `V' = W ∩ V` read in `W`, the statement is the statement on the
restriction to `V` at the pullbacks to `V`. -/
theorem isColim_restrict_extensionRestriction_iff {V W : B.Opens} (hVW : V ≤ W)
    (E Y : DMod W.toScheme) :
    (S.restrict W).IsColim ((derivedExtensionRestriction
        (structureSheafRing W.toScheme.toRingedSpace) (W.ι ⁻¹ᵁ V)).obj E) Y ↔
      (S.restrict V).IsColim ((pb (B.homOfLE hVW)).obj E) ((pb (B.homOfLE hVW)).obj Y) := by
  rw [Hom.isColim_iff_of_extensionRestriction (S.restrict W) (S.restrictInclusion hVW)
      (W.ι ⁻¹ᵁ V)
      (S.restrictInclusion_opensRange hVW) (S.restrictInclusion_limit_opensRange hVW)
      (Iso.refl _) Y,
    isColim_comp_iff]
  have hr : (B.homOfLE hVW).opensRange = W.ι ⁻¹ᵁ V := Scheme.opensRange_homOfLE hVW
  exact ⟨fun h => h.of_iso_fst (eqToIso (by rw [hr]) ≪≫
      pbOpenImmersionExtensionRestrictionIso (B.homOfLE hVW) E),
    fun h => h.of_iso_fst (eqToIso (by rw [hr]) ≪≫
      pbOpenImmersionExtensionRestrictionIso (B.homOfLE hVW) E).symm⟩

/-- The predicate of the induction: the statement on the restriction to `U`, at every shift of
the first argument. -/
def RestrictIsColim (X Y : DMod B) (U : B.Opens) : Prop :=
  ∀ m : ℤ, (S.restrict U).IsColim ((pb U.ι).obj (X⟦m⟧)) ((pb U.ι).obj Y)

/-- The pullbacks to a smaller open, through the larger one, are the pullbacks to the smaller
one. -/
def pbHomOfLEIso {V W : B.Opens} (hVW : V ≤ W) (M : DMod B) :
    (pb (B.homOfLE hVW)).obj ((pb W.ι).obj M) ≅ (pb V.ι).obj M :=
  (schemeFactorIso (B.homOfLE hVW) W.ι V.ι (Scheme.homOfLE_ι _ _)).app M

/-- The induction predicate on `V ≤ W` gives the statement on `W` at an extension by zero from
`V`, for every shift. -/
theorem isColim_restrict_extensionRestriction {V W : B.Opens} (hVW : V ≤ W) (X Y : DMod B)
    (hV : S.RestrictIsColim X Y V) (m : ℤ) :
    (S.restrict W).IsColim ((derivedExtensionRestriction
        (structureSheafRing W.toScheme.toRingedSpace) (W.ι ⁻¹ᵁ V)).obj ((pb W.ι).obj (X⟦m⟧)))
      ((pb W.ι).obj Y) :=
  (S.isColim_restrict_extensionRestriction_iff hVW _ _).2
    (((hV m).of_iso_fst (pbHomOfLEIso hVW (X⟦m⟧)).symm).of_iso_snd _
      (pbHomOfLEIso hVW Y).symm)

/-- **The union step of the induction.** If the statement holds, for every shift of the first
argument, on the restrictions to `V`, to `W` and to `V ∩ W`, then it holds on the restriction to
`V ∪ W`. -/
theorem restrictIsColim_sup (X Y : DMod B) (V W : B.Opens) (hV : S.RestrictIsColim X Y V)
    (hW : S.RestrictIsColim X Y W) (hVW : S.RestrictIsColim X Y (V ⊓ W)) :
    S.RestrictIsColim X Y (V ⊔ W) := by
  intro m
  let U := V ⊔ W
  let O := structureSheafRing U.toScheme.toRingedSpace
  have hcover : U.ι ⁻¹ᵁ V ⊔ U.ι ⁻¹ᵁ W = ⊤ := by
    rw [← Scheme.Hom.preimage_sup]
    exact Scheme.Opens.ι_preimage_self U
  let G : B.Opens → ℤ → DMod U.toScheme := fun A n =>
    (derivedExtensionRestriction O (U.ι ⁻¹ᵁ A)).obj ((pb U.ι).obj (X⟦n⟧))
  have hG : ∀ (A : B.Opens) (hA : A ≤ U), S.RestrictIsColim X Y A → ∀ n,
      (S.restrict U).IsColim (G A n) ((pb U.ι).obj Y) :=
    fun A hA h n => S.isColim_restrict_extensionRestriction hA X Y h n
  have hshift : ∀ (A : B.Opens) (n : ℤ), G A (n + 1) ≅ (G A n)⟦(1 : ℤ)⟧ := fun A n =>
    (derivedExtensionRestriction O (U.ι ⁻¹ᵁ A)).mapIso
        ((pb U.ι).mapIso ((shiftFunctorAdd' (DMod B) n 1 (n + 1) rfl).app X) ≪≫
          ((pb U.ι).commShiftIso (1 : ℤ)).app (X⟦n⟧)) ≪≫
      ((derivedExtensionRestriction O (U.ι ⁻¹ᵁ A)).commShiftIso (1 : ℤ)).app _
  have hG' : ∀ (A : B.Opens) (hA : A ≤ U), S.RestrictIsColim X Y A →
      (S.restrict U).IsColim ((G A m)⟦(1 : ℤ)⟧) ((pb U.ι).obj Y) :=
    fun A hA h => (hG A hA h (m + 1)).of_iso_fst (hshift A m)
  obtain ⟨f, g, h, hT⟩ := exists_distTriang_extensionRestriction O (U.ι ⁻¹ᵁ V) (U.ι ⁻¹ᵁ W)
    hcover ((pb U.ι).obj (X⟦m⟧))
  have : PreservesBinaryBiproducts (shiftFunctor (DMod U.toScheme) (1 : ℤ)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact IsColim.obj₃ hT (hG (V ⊓ W) (inf_le_left.trans le_sup_left) hVW m)
    ((hG V le_sup_left hV m).biprod (hG W le_sup_right hW m))
    (hG' (V ⊓ W) (inf_le_left.trans le_sup_left) hVW)
    (((hG' V le_sup_left hV).biprod (hG' W le_sup_right hW)).of_iso_fst
      ((shiftFunctor (DMod U.toScheme) (1 : ℤ)).mapBiprod _ _).symm)

/-- **The reduction to affine opens.** On a quasi-compact quasi-separated base, if the statement
holds, for every shift of the first argument, on the restriction to every affine open, then it
holds. This is the induction principle of Stacks 08DR, with the union step
`restrictIsColim_sup`. -/
theorem isColim_of_isAffineOpen [QuasiSeparatedSpace B] [CompactSpace B] (X Y : DMod B)
    (haff : ∀ U : B.Opens, IsAffineOpen U → S.RestrictIsColim X Y U) : S.IsColim X Y := by
  have htop : S.RestrictIsColim X Y ⊤ :=
    Stacks.AlgebraicGeometry.CompactOpenInduction.top (P := S.RestrictIsColim X Y) haff
      (fun V W _ _ hV hW hVW => S.restrictIsColim_sup X Y V W hV hW hVW)
  have h0 := (htop 0).of_iso_fst ((pb (⊤ : B.Opens).ι).mapIso ((shiftFunctorZero _ ℤ).app X))
  rw [← isColim_comp_iff] at h0
  exact (Hom.isColim_iff_of_isIso S (S.restrictι ⊤) X Y).2 h0

end SchemeSystem

end Stacks.LimitHomDescent

end
