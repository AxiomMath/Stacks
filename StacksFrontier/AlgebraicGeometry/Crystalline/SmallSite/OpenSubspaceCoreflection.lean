module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.MayerVietorisCover
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubspaceGlobalSections

/-!
# The inclusion of `Cris(V/S)` into `Cris(X/S)` has a right adjoint

Let `V` be an open of `X` and let `u : Cris(V/S) ⥤ Cris(X/S)` be the inclusion, change of divided
power base along the identity of `S` and the open immersion `V ⟶ X`
(`Crystalline.GlobalCrystallineSituation.openSubspace`).  An object `(U, T, δ)` of `Cris(X/S)`
restricts to `V`: the open `T_V` of `T` cut out by `V`
(`...SmallSite.CrystallineThickening.ambientOpen`) carries the object `(U ∩ V, T_V, δ|_{T_V})`,
which lies over `V` and so comes from `Cris(V/S)`.  This file shows that this restriction is right
adjoint to `u`: a morphism `u(B) ⟶ (U, T, δ)` has its ambient image inside `T_V`, so it factors
through the restriction, uniquely because the restriction morphism is a monomorphism.

This is the site-level form of the statement that `Cris(V/S)` is the localization of `Cris(X/S)`
at the open subobject `h_V` of the final sheaf, which is how [Stacks, Tag 07ML] uses it: the
endofunctor `A ↦ u(A|_V)` of `Cris(X/S)` and its counit `A|_V ⟶ A` are what the Mayer--Vietoris
sequence of `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/MayerVietorisSequence.lean` is
built from.  On sheaves of modules the adjunction gives restriction `F ↦ F|_V` a right adjoint
`j_{V, *}`, computed by `(j_{V, *}G)(A) = G(A|_V)`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `openSubspaceInclusion` — the inclusion `u : Cris(V/S) ⥤ Cris(X/S)`.
* `CrystallineThickening.openSubspaceRestrict` — the restriction `A|_V` of an object of
  `Cris(X/S)`, read as an object of `Cris(V/S)`.
* `CrystallineThickening.openSubspaceCounit` — the morphism `u(A|_V) ⟶ A`.
* `openSubspaceRetraction` — the restriction `Cris(X/S) ⥤ Cris(V/S)` as a functor.
* `openSubspaceAdjunction` — `u ⊣ openSubspaceRetraction`.
* `openSubspaceDirectImage` — `j_{V, *} : Mod(𝒪_{V/S}) ⥤ Mod(𝒪_{X/S})`, restriction along the
  right adjoint.
* `openSubspaceRestrictionAdjunction` — restriction of modules to `Cris(V/S)` is left adjoint to
  `j_{V, *}`.

## Main results

* `CrystallineThickening.exists_unique_lift_openSubspaceCounit` — the universal property of
  `u(A|_V) ⟶ A`.
* `openSubspaceAdjunction_counit_app` — the counit of the adjunction is
  `CrystallineThickening.openSubspaceCounit`.
* `mono_openSubspaceAdjunction_counit_app` — the counit is a monomorphism.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (V : S.X.Opens)

variable (S) in
/-- **The inclusion `u : Cris(V/S) ⥤ Cris(X/S)` of the small crystalline site of an open `V` of
`X`**, change of divided power base along the identity of `S` and the open immersion `V ⟶ X`. -/
abbrev openSubspaceInclusion :
    CrystallineThickening (openSubspace S V) ⥤ CrystallineThickening S :=
  smallChangeBase (openSubspace S V) S (𝟙 S.S) V.ι (openSubspace_changeBase_condition S V)

namespace CrystallineThickening

/-- The thickened scheme of the restriction of an object of `Cris(X/S)` to the open of its
ambient scheme cut out by `V` maps into `V`. -/
theorem range_toX_restrictOpen_ambientOpen_subset (A : CrystallineThickening S) :
    Set.range ⇑(A.restrictOpen (ambientOpen A V)).obj.toX.base ⊆ Set.range ⇑V.ι.base := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hx : (A.obj.thickening.immersion ⁻¹ᵁ ambientOpen A V).ι.base x ∈
      ((A.obj.thickening.immersion ⁻¹ᵁ ambientOpen A V : A.obj.thickening.source.Opens) :
        Set A.obj.thickening.source) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  exact (SetLike.ext_iff.mp (immersion_preimage_ambientOpen A V) _).mp hx

/-- **The restriction `A|_V` of an object `A = (U, T, δ)` of `Cris(X/S)` to an open `V` of `X`,
read as an object of `Cris(V/S)`**: the restriction of `A` to the open `T_V` of `T` cut out by `V`,
whose thickened scheme `U ∩ V` maps into `V`. -/
def openSubspaceRestrict (A : CrystallineThickening S) :
    CrystallineThickening (openSubspace S V) :=
  smallChangeBaseDescend (h := openSubspace_changeBase_condition S V)
    (DividedPowerScheme.isInducedOpen_of_isIso (𝟙 S.S)) (A.restrictOpen (ambientOpen A V))
    (range_toX_restrictOpen_ambientOpen_subset V A)

/-- Including `A|_V` back into `Cris(X/S)` gives the restriction of `A` to `T_V`. -/
def openSubspaceRestrictIso (A : CrystallineThickening S) :
    (openSubspaceInclusion S V).obj (openSubspaceRestrict V A) ≅
      A.restrictOpen (ambientOpen A V) :=
  (Thickening.IsCrystalline (S := S)).fullyFaithfulι.preimageIso
    (changeBaseDescendIso (h := openSubspace_changeBase_condition S V)
      (DividedPowerScheme.isInducedOpen_of_isIso (𝟙 S.S)) (A.restrictOpen (ambientOpen A V)).obj
      (range_toX_restrictOpen_ambientOpen_subset V A))

/-- **The morphism `u(A|_V) ⟶ A`**: the restriction morphism of `A` to `T_V`. -/
def openSubspaceCounit (A : CrystallineThickening S) :
    (openSubspaceInclusion S V).obj (openSubspaceRestrict V A) ⟶ A :=
  (openSubspaceRestrictIso V A).hom ≫ A.restrictOpenHom (ambientOpen A V)

/-- The morphism `u(A|_V) ⟶ A` is a monomorphism. -/
instance mono_openSubspaceCounit (A : CrystallineThickening S) :
    Mono (openSubspaceCounit V A) :=
  inferInstanceAs (Mono ((openSubspaceRestrictIso V A).hom ≫ A.restrictOpenHom (ambientOpen A V)))

/-- **A morphism of `Cris(X/S)` whose source lies over `V` has its ambient image inside the open
cut out by `V`.**  Every point of the ambient scheme of the source comes from its thickened scheme,
which maps into `V`. -/
theorem targetHom_base_mem_ambientOpen {B A : CrystallineThickening S} (g : B ⟶ A)
    (hB : Set.range ⇑B.obj.toX.base ⊆ Set.range ⇑V.ι.base)
    (x : B.obj.thickening.target.scheme) : g.hom.targetHom.hom.base x ∈ ambientOpen A V := by
  obtain ⟨s, rfl⟩ := B.obj.thickening.isThickening.2 x
  have h1 : g.hom.targetHom.hom.base (B.obj.thickening.immersion.base s) =
      A.obj.thickening.immersion.base (g.hom.sourceHom.base s) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, g.hom.immersion_naturality]
  rw [h1]
  change g.hom.sourceHom.base s ∈ A.obj.thickening.immersion ⁻¹ᵁ ambientOpen A V
  rw [immersion_preimage_ambientOpen]
  change A.obj.toX.base (g.hom.sourceHom.base s) ∈ V
  have h2 : A.obj.toX.base (g.hom.sourceHom.base s) = B.obj.toX.base s := by
    rw [← Scheme.Hom.comp_apply, g.hom.toX_naturality]
  rw [h2]
  have h3 := hB ⟨s, rfl⟩
  rwa [Scheme.Opens.range_ι] at h3

/-- An object in the image of the inclusion lies over `V`. -/
theorem range_toX_openSubspaceInclusion_obj_subset (B : CrystallineThickening (openSubspace S V)) :
    Set.range ⇑((openSubspaceInclusion S V).obj B).obj.toX.base ⊆ Set.range ⇑V.ι.base := by
  rintro _ ⟨x, rfl⟩
  exact ⟨B.obj.toX.base x, (Scheme.Hom.comp_apply B.obj.toX V.ι x).symm⟩

/-- **The universal property of `u(A|_V) ⟶ A`**: every morphism `u(B) ⟶ A` factors uniquely
through it, as `u` of a morphism `B ⟶ A|_V` of `Cris(V/S)`. -/
theorem exists_unique_lift_openSubspaceCounit (A : CrystallineThickening S)
    {B : CrystallineThickening (openSubspace S V)}
    (g : (openSubspaceInclusion S V).obj B ⟶ A) :
    ∃! p : B ⟶ openSubspaceRestrict V A,
      (openSubspaceInclusion S V).map p ≫ openSubspaceCounit V A = g := by
  obtain ⟨q, hq⟩ := exists_comp_restrictOpenHom_eq (ambientOpen A V) g
    (targetHom_base_mem_ambientOpen V g (range_toX_openSubspaceInclusion_obj_subset V B))
  refine ⟨(openSubspaceInclusion S V).preimage (q ≫ (openSubspaceRestrictIso V A).inv), ?_, ?_⟩
  · beta_reduce
    rw [Functor.map_preimage, openSubspaceCounit, Category.assoc, Iso.inv_hom_id_assoc, hq]
  · intro p hp
    apply (openSubspaceInclusion S V).map_injective
    rw [Functor.map_preimage, ← cancel_mono (openSubspaceCounit V A), hp, openSubspaceCounit,
      Category.assoc, Iso.inv_hom_id_assoc, hq]

end CrystallineThickening

open _root_.Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

/-- The hom bijection of the adjunction `u ⊣ (-)|_V`. -/
def openSubspaceHomEquiv (B : CrystallineThickening (openSubspace S V))
    (A : CrystallineThickening S) :
    ((openSubspaceInclusion S V).obj B ⟶ A) ≃ (B ⟶ openSubspaceRestrict V A) where
  toFun g := (exists_unique_lift_openSubspaceCounit V A g).choose
  invFun p := (openSubspaceInclusion S V).map p ≫ openSubspaceCounit V A
  left_inv g := (exists_unique_lift_openSubspaceCounit V A g).choose_spec.1
  right_inv p :=
    ((exists_unique_lift_openSubspaceCounit V A _).choose_spec.2 p rfl).symm

/-- The hom bijection `openSubspaceHomEquiv` is natural in the object of `Cris(V/S)`. -/
theorem openSubspaceHomEquiv_naturality (B' B : CrystallineThickening (openSubspace S V))
    (A : CrystallineThickening S) (f : B' ⟶ B)
    (g : (openSubspaceInclusion S V).obj B ⟶ A) :
    openSubspaceHomEquiv V B' A ((openSubspaceInclusion S V).map f ≫ g) =
      f ≫ openSubspaceHomEquiv V B A g := by
  rw [← Equiv.eq_symm_apply]
  change _ = (openSubspaceInclusion S V).map (f ≫ openSubspaceHomEquiv V B A g) ≫
    openSubspaceCounit V A
  rw [Functor.map_comp, Category.assoc]
  congr 1
  exact ((openSubspaceHomEquiv V B A).left_inv g).symm

/-- **The restriction `Cris(X/S) ⥤ Cris(V/S)`**, `A ↦ A|_V`, the right adjoint of the inclusion. -/
def openSubspaceRetraction : CrystallineThickening S ⥤ CrystallineThickening (openSubspace S V) :=
  Adjunction.rightAdjointOfEquiv (openSubspaceHomEquiv V) (openSubspaceHomEquiv_naturality V)

/-- The restriction functor sends `A` to `A|_V`. -/
@[simp]
theorem openSubspaceRetraction_obj (A : CrystallineThickening S) :
    (openSubspaceRetraction V).obj A = openSubspaceRestrict V A :=
  rfl

/-- **The inclusion `u : Cris(V/S) ⥤ Cris(X/S)` is left adjoint to restriction to `V`.** -/
def openSubspaceAdjunction : openSubspaceInclusion S V ⊣ openSubspaceRetraction V :=
  Adjunction.adjunctionOfEquivRight (openSubspaceHomEquiv V) (openSubspaceHomEquiv_naturality V)

/-- The counit of `u ⊣ (-)|_V` at `A` is the restriction morphism `u(A|_V) ⟶ A`. -/
theorem openSubspaceAdjunction_counit_app (A : CrystallineThickening S) :
    (openSubspaceAdjunction V).counit.app A = openSubspaceCounit V A := by
  simp [openSubspaceAdjunction, Adjunction.adjunctionOfEquivRight, openSubspaceHomEquiv]

/-- The counit of `u ⊣ (-)|_V` is a monomorphism at every object. -/
instance mono_openSubspaceAdjunction_counit_app (A : CrystallineThickening S) :
    Mono ((openSubspaceAdjunction V).counit.app A) := by
  rw [openSubspaceAdjunction_counit_app]
  exact CrystallineThickening.mono_openSubspaceCounit V A

/-- Restriction to `V` is continuous, being right adjoint to the cocontinuous inclusion. -/
instance isContinuous_openSubspaceRetraction :
    (openSubspaceRetraction V).IsContinuous (smallTopology S) (smallTopology (openSubspace S V)) :=
  (openSubspaceAdjunction V).isContinuous_of_isCocontinuous _ _

/-! ### The direct image of modules along the inclusion of `Cris(V/S)` -/

/-- **The ring map `𝒪_{X/S} ⟶ (-)|_V^{-1}𝒪_{V/S}`**: on an object `A` of `Cris(X/S)`, restriction of
functions along the morphism `u(A|_V) ⟶ A`.  The ambient scheme of `A|_V` is the open `T_V` of the
ambient scheme `T` of `A`, so this is the restriction `Γ(T, 𝒪_T) ⟶ Γ(T_V, 𝒪_T)`. -/
def openSubspaceDirectImageRingHom :
    structureSheaf S ⟶ ((openSubspaceRetraction V).sheafPushforwardContinuous RingCat.{u}
      (smallTopology S) (smallTopology (openSubspace S V))).obj
        (structureSheaf (openSubspace S V)) :=
  ⟨Functor.whiskerRight (NatTrans.op (openSubspaceAdjunction V).counit) (structureSheaf S).obj⟩

/-- **The direct image `j_{V, *} : Mod(𝒪_{V/S}) ⥤ Mod(𝒪_{X/S})` along the inclusion of `Cris(V/S)`
into `Cris(X/S)`**: restriction along the right adjoint `A ↦ A|_V` of the inclusion, so that its
sections over `A` are the sections over `A|_V`. -/
def openSubspaceDirectImage : ModuleSheaf (openSubspace S V) ⥤ ModuleSheaf S :=
  SheafOfModules.pushforward.{u + 1} (openSubspaceDirectImageRingHom V)

/-- **Restriction of modules to `Cris(V/S)` is left adjoint to the direct image `j_{V, *}`.**  The
adjunction of sites `u ⊣ (-)|_V` induces it on restrictions, with the identity structure map on the
left and `openSubspaceDirectImageRingHom` on the right. -/
def openSubspaceRestrictionAdjunction :
    openSubspaceModuleRestriction S V ⊣ openSubspaceDirectImage V :=
  SheafOfModules.pushforwardPushforwardAdj.{u + 1} (openSubspaceAdjunction V)
    (smallChangeBaseStructureHom (openSubspace S V) S (𝟙 S.S) V.ι
      (openSubspace_changeBase_condition S V))
    (openSubspaceDirectImageRingHom V)
    (by exact (Category.comp_id _).symm)
    (by
      refine NatTrans.ext (funext fun B ↦ ?_)
      change 𝟙 _ ≫ (structureSheaf S).obj.map ((openSubspaceAdjunction V).counit.app
          ((openSubspaceInclusion S V).obj B.unop)).op ≫
        (structureSheaf S).obj.map ((openSubspaceInclusion S V).map
          ((openSubspaceAdjunction V).unit.app B.unop)).op = 𝟙 _
      rw [Category.id_comp, ← Functor.map_comp, ← op_comp,
        (openSubspaceAdjunction V).left_triangle_components B.unop]
      exact (structureSheaf S).obj.map_id _)

/-- The unit of `openSubspaceRestrictionAdjunction` at a module `M` is, on the sections over an
object `A` of `Cris(X/S)`, restriction along `u(A|_V) ⟶ A`. -/
theorem openSubspaceRestrictionAdjunction_unit_app_val_app (M : ModuleSheaf S)
    (A : (CrystallineThickening S)ᵒᵖ) (x : M.val.obj A) :
    ((openSubspaceRestrictionAdjunction V).unit.app M).val.app A x =
      M.val.map ((openSubspaceAdjunction V).counit.app A.unop).op x :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
