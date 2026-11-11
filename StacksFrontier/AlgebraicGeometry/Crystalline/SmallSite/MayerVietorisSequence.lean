module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Homology.Square
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubspaceRestrictionInjective

/-!
# The Mayer--Vietoris sequence of sheaves of modules for an open covering of `X`

Let `X = X' ∪ X''` be an open covering, `X''' = X' ∩ X''`.  For a sheaf `F` of
`𝒪_{X/S}`-modules on `Cris(X/S)` write `j_{V, *}(F|_V)` for its restriction to `Cris(V/S)` pushed
back to `Cris(X/S)` (`...SmallSite.openSubspaceRestrictionAdjunction`); its sections over an object
`A` are the sections of `F` over `A|_V`.  This file proves that the Mayer--Vietoris sequence

`0 ⟶ F ⟶ j_{X', *}(F|_{X'}) ⊕ j_{X'', *}(F|_{X''}) ⟶ j_{X''', *}(F|_{X'''}) ⟶ 0`

is a short exact sequence of sheaves of `𝒪_{X/S}`-modules.  This is the sheaf-level form of the
fact recorded in the hints of [Stacks, Tag 07ML], that `Cris(X'/S)`, `Cris(X''/S)` and
`Cris(X'''/S)` are the localizations of `Cris(X/S)` at open subobjects of the final sheaf, the last
the intersection of the first two.

Exactness on the left and in the middle is the sheaf condition: on the sections over `A` the
sequence is the Mayer--Vietoris sequence of the square of restrictions of `A`, which is
`...SmallSite.CrystallineThickening.isPullback_op_map_of_cover`.  Surjectivity on the right is
local: over `A|_{X'}` the restriction from `X''` to `X'''` is an isomorphism, because there the
two opens cut out the same part of the ambient scheme.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `openSubspaceRestrictEndo` — the endofunctor `A ↦ A|_V` of `Cris(X/S)`.
* `openSubspaceRestrictEndoLE` — for `W ≤ V`, the inclusion `A|_W ⟶ A|_V`.
* `openSubspaceRestrictModule` — the endofunctor `F ↦ j_{V, *}(F|_V)` of `Mod(𝒪_{X/S})`, with
  `openSubspaceRestrictModuleUnit : F ⟶ j_{V, *}(F|_V)` and, for `W ≤ V`,
  `openSubspaceRestrictModuleLE : j_{V, *}(F|_V) ⟶ j_{W, *}(F|_W)`.
* `mayerVietorisShortComplex` — the Mayer--Vietoris short complex of a module.

## Main results

* `mayerVietorisShortComplex_shortExact` — the Mayer--Vietoris sequence is short exact.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The endofunctor `A ↦ A|_V` -/

/-- **The endofunctor `A ↦ A|_V` of `Cris(X/S)`**, restriction to `V` followed by the inclusion. -/
abbrev openSubspaceRestrictEndo (V : S.X.Opens) :
    CrystallineThickening S ⥤ CrystallineThickening S :=
  openSubspaceRetraction V ⋙ openSubspaceInclusion S V

namespace CrystallineThickening

/-- **A morphism of `Cris(X/S)` out of an object lying over `V` factors through `A|_V ⟶ A`.** -/
theorem exists_factor_openSubspaceCounit (V : S.X.Opens) (A : CrystallineThickening S)
    {C : CrystallineThickening S} (g : C ⟶ A)
    (hC : Set.range ⇑C.obj.toX.base ⊆ Set.range ⇑V.ι.base) :
    ∃ p : C ⟶ (openSubspaceRestrictEndo V).obj A,
      p ≫ (openSubspaceAdjunction V).counit.app A = g := by
  obtain ⟨B, ⟨e⟩⟩ := smallChangeBase_essImage_of_range_toX_subset
    (h := openSubspace_changeBase_condition S V)
    (DividedPowerScheme.isInducedOpen_of_isIso (𝟙 S.S)) C hC
  refine ⟨e.inv ≫ (openSubspaceInclusion S V).map
    ((openSubspaceAdjunction V).homEquiv B A (e.hom ≫ g)), ?_⟩
  have key := (openSubspaceAdjunction V).homEquiv_counit
    (g := (openSubspaceAdjunction V).homEquiv B A (e.hom ≫ g))
  rw [Equiv.symm_apply_apply] at key
  rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]

/-- `A|_W` lies over `V` when `W ≤ V`. -/
theorem range_toX_openSubspaceRestrictEndo_subset {V W : S.X.Opens} (h : W ≤ V)
    (A : CrystallineThickening S) :
    Set.range ⇑((openSubspaceRestrictEndo W).obj A).obj.toX.base ⊆ Set.range ⇑V.ι.base := by
  refine (range_toX_openSubspaceInclusion_obj_subset W _).trans ?_
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  exact h

end CrystallineThickening

open _root_.Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

/-- **The inclusion `A|_W ⟶ A|_V` for `W ≤ V`**, the unique morphism over `A`. -/
def openSubspaceRestrictEndoLE {V W : S.X.Opens} (h : W ≤ V) :
    openSubspaceRestrictEndo W ⟶ openSubspaceRestrictEndo V where
  app A := (exists_factor_openSubspaceCounit V A ((openSubspaceAdjunction W).counit.app A)
    (range_toX_openSubspaceRestrictEndo_subset h A)).choose
  naturality A A' a := by
    have hA := (exists_factor_openSubspaceCounit V A ((openSubspaceAdjunction W).counit.app A)
      (range_toX_openSubspaceRestrictEndo_subset h A)).choose_spec
    have hA' := (exists_factor_openSubspaceCounit V A' ((openSubspaceAdjunction W).counit.app A')
      (range_toX_openSubspaceRestrictEndo_subset h A')).choose_spec
    rw [← cancel_mono ((openSubspaceAdjunction V).counit.app A'), Category.assoc, hA',
      Category.assoc, (openSubspaceAdjunction V).counit.naturality, ← Category.assoc, hA]
    exact (openSubspaceAdjunction W).counit.naturality a

/-- The inclusion `A|_W ⟶ A|_V` lies over `A`. -/
@[reassoc (attr := simp)]
theorem openSubspaceRestrictEndoLE_app_counit {V W : S.X.Opens} (h : W ≤ V)
    (A : CrystallineThickening S) :
    (openSubspaceRestrictEndoLE h).app A ≫ (openSubspaceAdjunction V).counit.app A =
      (openSubspaceAdjunction W).counit.app A :=
  (exists_factor_openSubspaceCounit V A ((openSubspaceAdjunction W).counit.app A)
    (range_toX_openSubspaceRestrictEndo_subset h A)).choose_spec

/-! ### The endofunctor `F ↦ j_{V, *}(F|_V)` of modules -/

/-- The endofunctor `A ↦ A|_V` is continuous. -/
instance isContinuous_openSubspaceRestrictEndo (V : S.X.Opens) :
    (openSubspaceRestrictEndo V).IsContinuous (smallTopology S) (smallTopology S) :=
  Functor.isContinuous_comp _ _ _ (smallTopology (openSubspace S V)) _

/-- The ring map of `F ↦ j_{V, *}(F|_V)`: restriction of functions along `A|_V ⟶ A`. -/
def openSubspaceRestrictModuleRingHom (V : S.X.Opens) :
    structureSheaf S ⟶ ((openSubspaceRestrictEndo V).sheafPushforwardContinuous RingCat.{u}
      (smallTopology S) (smallTopology S)).obj (structureSheaf S) :=
  openSubspaceDirectImageRingHom V ≫
    ((openSubspaceRetraction V).sheafPushforwardContinuous RingCat.{u} (smallTopology S)
      (smallTopology (openSubspace S V))).map
      (smallChangeBaseStructureHom (openSubspace S V) S (𝟙 S.S) V.ι
        (openSubspace_changeBase_condition S V))

/-- **The endofunctor `F ↦ j_{V, *}(F|_V)` of sheaves of `𝒪_{X/S}`-modules**: sections over `A`
are the sections over `A|_V`. -/
def openSubspaceRestrictModule (V : S.X.Opens) : ModuleSheaf S ⥤ ModuleSheaf S :=
  SheafOfModules.pushforward.{u + 1} (openSubspaceRestrictModuleRingHom V)

/-- `F ↦ j_{V, *}(F|_V)` is restriction to `Cris(V/S)` followed by `j_{V, *}`. -/
def openSubspaceRestrictModuleIso (V : S.X.Opens) :
    openSubspaceModuleRestriction S V ⋙ openSubspaceDirectImage V ≅ openSubspaceRestrictModule V :=
  SheafOfModules.pushforwardComp _ _

/-- **The map `F ⟶ j_{V, *}(F|_V)`**, restriction of sections along `A|_V ⟶ A`. -/
def openSubspaceRestrictModuleUnit (V : S.X.Opens) :
    𝟭 (ModuleSheaf S) ⟶ openSubspaceRestrictModule V :=
  (openSubspaceRestrictionAdjunction V).unit ≫ (openSubspaceRestrictModuleIso V).hom

/-- The map `F ⟶ j_{V, *}(F|_V)` on sections over `A` is restriction along `A|_V ⟶ A`. -/
theorem openSubspaceRestrictModuleUnit_app_val_app (V : S.X.Opens) (M : ModuleSheaf S)
    (A : (CrystallineThickening S)ᵒᵖ) (x : M.val.obj A) :
    ((openSubspaceRestrictModuleUnit V).app M).val.app A x =
      M.val.map ((openSubspaceAdjunction V).counit.app A.unop).op x :=
  rfl

/-- The ring maps of `j_{V, *}(F|_V)` and `j_{W, *}(F|_W)` are compatible with `A|_W ⟶ A|_V`. -/
theorem openSubspaceRestrictModuleRingHom_comp {V W : S.X.Opens} (h : W ≤ V) :
    openSubspaceRestrictModuleRingHom V ≫
        (Functor.sheafPushforwardContinuousNatTrans (openSubspaceRestrictEndoLE h) RingCat.{u}
          (smallTopology S) (smallTopology S)).app (structureSheaf S) =
      openSubspaceRestrictModuleRingHom W := by
  ext A : 3
  change (structureSheaf S).obj.map ((openSubspaceAdjunction V).counit.app A.unop).op ≫
      𝟙 _ ≫ (structureSheaf S).obj.map ((openSubspaceRestrictEndoLE h).app A.unop).op =
    (structureSheaf S).obj.map ((openSubspaceAdjunction W).counit.app A.unop).op ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← op_comp,
    openSubspaceRestrictEndoLE_app_counit]

/-- **The restriction `j_{V, *}(F|_V) ⟶ j_{W, *}(F|_W)` for `W ≤ V`**, restriction of sections
along `A|_W ⟶ A|_V`. -/
def openSubspaceRestrictModuleLE {V W : S.X.Opens} (h : W ≤ V) :
    openSubspaceRestrictModule V ⟶ openSubspaceRestrictModule W :=
  SheafOfModules.pushforwardNatTrans (openSubspaceRestrictModuleRingHom V)
      (openSubspaceRestrictEndoLE h) ≫
    (SheafOfModules.pushforwardCongr (openSubspaceRestrictModuleRingHom_comp h)).hom

/-- The restriction `j_{V, *}(F|_V) ⟶ j_{W, *}(F|_W)` on sections over `A` is restriction along
`A|_W ⟶ A|_V`. -/
theorem openSubspaceRestrictModuleLE_app_val_app {V W : S.X.Opens} (h : W ≤ V)
    (M : ModuleSheaf S) (A : (CrystallineThickening S)ᵒᵖ)
    (x : M.val.obj (op ((openSubspaceRestrictEndo V).obj A.unop))) :
    ((openSubspaceRestrictModuleLE h).app M).val.app A x =
      M.val.map ((openSubspaceRestrictEndoLE h).app A.unop).op x :=
  rfl

/-- Restricting to `V` and then to `W ≤ V` is restricting to `W`. -/
@[reassoc (attr := simp)]
theorem openSubspaceRestrictModuleUnit_comp_LE {V W : S.X.Opens} (h : W ≤ V) :
    openSubspaceRestrictModuleUnit V ≫ openSubspaceRestrictModuleLE h =
      openSubspaceRestrictModuleUnit W := by
  ext M A x
  change M.val.map ((openSubspaceRestrictEndoLE h).app A.unop).op
      (M.val.map ((openSubspaceAdjunction V).counit.app A.unop).op x) =
    M.val.map ((openSubspaceAdjunction W).counit.app A.unop).op x
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, openSubspaceRestrictEndoLE_app_counit]

/-! ### The Mayer--Vietoris square of an object of `Cris(X/S)` -/

namespace CrystallineThickening

/-- `A|_V` is the restriction of `A` to the open `T_V` of its ambient scheme. -/
def openSubspaceRestrictEndoIso (V : S.X.Opens) (A : CrystallineThickening S) :
    (openSubspaceRestrictEndo V).obj A ≅ A.restrictOpen (ambientOpen A V) :=
  openSubspaceRestrictIso V A

/-- `u(A|_V) ⟶ A` is the restriction morphism of `A` to `T_V`, through
`openSubspaceRestrictEndoIso`. -/
theorem openSubspaceRestrictIso_hom_restrictOpenHom (V : S.X.Opens) (A : CrystallineThickening S) :
    (openSubspaceRestrictEndoIso V A).hom ≫ A.restrictOpenHom (ambientOpen A V) =
      (openSubspaceAdjunction V).counit.app A := by
  rw [openSubspaceAdjunction_counit_app]
  rfl

/-- **For `U ⊓ V ≤ W ≤ V` and `B` lying over `U`, the inclusion `B|_W ⟶ B|_V` is an
isomorphism**: `B|_V` lies over `U ⊓ V`, hence over `W`, so `B|_V ⟶ B` factors through `B|_W`. -/
theorem isIso_openSubspaceRestrictEndoLE_app {U V W : S.X.Opens} (h : W ≤ V) (hW : U ⊓ V ≤ W)
    (B : CrystallineThickening S) (hB : Set.range ⇑B.obj.toX.base ⊆ Set.range ⇑U.ι.base) :
    IsIso ((openSubspaceRestrictEndoLE h).app B) := by
  have hU := range_toX_subset_of_hom U ((openSubspaceAdjunction V).counit.app B) hB
  have hV := range_toX_openSubspaceInclusion_obj_subset V ((openSubspaceRetraction V).obj B)
  have hR : Set.range ⇑((openSubspaceRestrictEndo V).obj B).obj.toX.base ⊆
      Set.range ⇑W.ι.base := by
    intro x hx
    have h1 := hU hx
    have h2 := hV hx
    rw [Scheme.Opens.range_ι] at h1 h2 ⊢
    exact hW ⟨h1, h2⟩
  obtain ⟨p, hp⟩ := exists_factor_openSubspaceCounit W B
    ((openSubspaceAdjunction V).counit.app B) hR
  refine ⟨p, ?_, ?_⟩
  · rw [← cancel_mono ((openSubspaceAdjunction W).counit.app B), Category.assoc, hp,
      openSubspaceRestrictEndoLE_app_counit, Category.id_comp]
  · rw [← cancel_mono ((openSubspaceAdjunction V).counit.app B), Category.assoc,
      openSubspaceRestrictEndoLE_app_counit, hp, Category.id_comp]

variable (V₁ V₂ : S.X.Opens)

/-- **The Mayer--Vietoris square of an object `A` of `Cris(X/S)`** for a pair of opens of `X`:
the restrictions `A|_{V₁ ⊓ V₂}`, `A|_{V₁}`, `A|_{V₂}` over `A`. -/
def openSubspaceCoverSquare (A : CrystallineThickening S) : Square (CrystallineThickening S) where
  X₁ := (openSubspaceRestrictEndo (V₁ ⊓ V₂)).obj A
  X₂ := (openSubspaceRestrictEndo V₁).obj A
  X₃ := (openSubspaceRestrictEndo V₂).obj A
  X₄ := A
  f₁₂ := (openSubspaceRestrictEndoLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).app A
  f₁₃ := (openSubspaceRestrictEndoLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).app A
  f₂₄ := (openSubspaceAdjunction V₁).counit.app A
  f₃₄ := (openSubspaceAdjunction V₂).counit.app A
  fac := by rw [openSubspaceRestrictEndoLE_app_counit, openSubspaceRestrictEndoLE_app_counit]

/-- The right edge of the Mayer--Vietoris square of an object is a monomorphism. -/
instance mono_openSubspaceCoverSquare_f₂₄ (A : CrystallineThickening S) :
    Mono (openSubspaceCoverSquare V₁ V₂ A).f₂₄ :=
  mono_openSubspaceAdjunction_counit_app V₁ A

/-- The lower edge of the Mayer--Vietoris square of an object is a monomorphism. -/
instance mono_openSubspaceCoverSquare_f₃₄ (A : CrystallineThickening S) :
    Mono (openSubspaceCoverSquare V₁ V₂ A).f₃₄ :=
  mono_openSubspaceAdjunction_counit_app V₂ A

/-- **The Mayer--Vietoris square of an object is cartesian**: it is isomorphic, over `A`, to the
square of restrictions of `A` to the opens of its ambient scheme cut out by `V₁ ⊓ V₂`, `V₁`, `V₂`,
which is `isPullback_openCoverSquare`. -/
theorem isPullback_openSubspaceCoverSquare (A : CrystallineThickening S) :
    (openSubspaceCoverSquare V₁ V₂ A).IsPullback := by
  have h : IsPullback (restrictOpenLE A (ambientOpen_le_ambientOpen A (inf_le_left : V₁ ⊓ V₂ ≤ V₁)))
      (restrictOpenLE A (ambientOpen_le_ambientOpen A (inf_le_right : V₁ ⊓ V₂ ≤ V₂)))
      (A.restrictOpenHom (ambientOpen A V₁)) (A.restrictOpenHom (ambientOpen A V₂)) :=
    isPullback_openCoverSquare A V₁ V₂
  have e₁ := openSubspaceRestrictIso_hom_restrictOpenHom (V₁ ⊓ V₂) A
  have e₂ := openSubspaceRestrictIso_hom_restrictOpenHom V₁ A
  have e₃ := openSubspaceRestrictIso_hom_restrictOpenHom V₂ A
  have c₁ : restrictOpenLE A (ambientOpen_le_ambientOpen A (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) ≫
      (openSubspaceRestrictEndoIso V₁ A).inv = (openSubspaceRestrictEndoIso (V₁ ⊓ V₂) A).inv ≫
        (openSubspaceRestrictEndoLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).app A := by
    refine (cancel_mono ((openSubspaceAdjunction V₁).counit.app A)).1 ?_
    rw [Category.assoc, Category.assoc, openSubspaceRestrictEndoLE_app_counit, ← e₂,
      Iso.inv_hom_id_assoc, ← e₁, Iso.inv_hom_id_assoc]
    exact restrictOpenLE_restrictOpenHom A _
  have c₂ : restrictOpenLE A (ambientOpen_le_ambientOpen A (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) ≫
      (openSubspaceRestrictEndoIso V₂ A).inv = (openSubspaceRestrictEndoIso (V₁ ⊓ V₂) A).inv ≫
        (openSubspaceRestrictEndoLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).app A := by
    refine (cancel_mono ((openSubspaceAdjunction V₂).counit.app A)).1 ?_
    rw [Category.assoc, Category.assoc, openSubspaceRestrictEndoLE_app_counit, ← e₃,
      Iso.inv_hom_id_assoc, ← e₁, Iso.inv_hom_id_assoc]
    exact restrictOpenLE_restrictOpenHom A _
  have c₃ : A.restrictOpenHom (ambientOpen A V₁) ≫ 𝟙 A =
      (openSubspaceRestrictEndoIso V₁ A).inv ≫ (openSubspaceAdjunction V₁).counit.app A := by
    rw [← e₂, Iso.inv_hom_id_assoc, Category.comp_id]
  have c₄ : A.restrictOpenHom (ambientOpen A V₂) ≫ 𝟙 A =
      (openSubspaceRestrictEndoIso V₂ A).inv ≫ (openSubspaceAdjunction V₂).counit.app A := by
    rw [← e₃, Iso.inv_hom_id_assoc, Category.comp_id]
  exact IsPullback.of_iso h (openSubspaceRestrictEndoIso (V₁ ⊓ V₂) A).symm
    (openSubspaceRestrictEndoIso V₁ A).symm (openSubspaceRestrictEndoIso V₂ A).symm (Iso.refl A)
    c₁ c₂ c₃ c₄

/-- **The two lower edges of the Mayer--Vietoris square of an object generate a covering sieve**
when `X = V₁ ∪ V₂`: they differ by isomorphisms from the restrictions to the two opens of the
ambient scheme, which cover by `ofTwoArrows_openCoverSquare_mem_smallTopology`. -/
theorem ofTwoArrows_openSubspaceCoverSquare_mem_smallTopology {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) (A : CrystallineThickening S) :
    Sieve.ofTwoArrows (openSubspaceCoverSquare V₁ V₂ A).f₂₄ (openSubspaceCoverSquare V₁ V₂ A).f₃₄ ∈
      smallTopology S A := by
  refine (smallTopology S).superset_covering ?_ (ofTwoArrows_openCoverSquare_mem_smallTopology A hV)
  change Sieve.ofTwoArrows (A.restrictOpenHom (ambientOpen A V₁))
      (A.restrictOpenHom (ambientOpen A V₂)) ≤
    Sieve.ofTwoArrows ((openSubspaceAdjunction V₁).counit.app A)
      ((openSubspaceAdjunction V₂).counit.app A)
  rw [Sieve.generate_le_iff]
  rintro Z k ⟨(_ | _)⟩
  · change (Sieve.ofTwoArrows ((openSubspaceAdjunction V₁).counit.app A)
      ((openSubspaceAdjunction V₂).counit.app A)).arrows (A.restrictOpenHom (ambientOpen A V₁))
    rw [← Iso.inv_hom_id_assoc (openSubspaceRestrictEndoIso V₁ A) (A.restrictOpenHom _),
      openSubspaceRestrictIso_hom_restrictOpenHom]
    exact Sieve.downward_closed _
      (Sieve.ofArrows_mk (Y := _) (f := _) WalkingPair.left) _
  · change (Sieve.ofTwoArrows ((openSubspaceAdjunction V₁).counit.app A)
      ((openSubspaceAdjunction V₂).counit.app A)).arrows (A.restrictOpenHom (ambientOpen A V₂))
    rw [← Iso.inv_hom_id_assoc (openSubspaceRestrictEndoIso V₂ A) (A.restrictOpenHom _),
      openSubspaceRestrictIso_hom_restrictOpenHom]
    exact Sieve.downward_closed _
      (Sieve.ofArrows_mk (Y := _) (f := _) WalkingPair.right) _

end CrystallineThickening

open _root_.Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

/-! ### The Mayer--Vietoris sequence of a module -/

variable (V₁ V₂ : S.X.Opens)

/-- **The Mayer--Vietoris square of a sheaf of modules** `M` for a pair of opens of `X`: `M` and
its restrictions `j_{V, *}(M|_V)` to `V₁`, `V₂` and `V₁ ⊓ V₂`. -/
def mayerVietorisSquare (M : ModuleSheaf S) : Square (ModuleSheaf S) where
  X₁ := M
  X₂ := (openSubspaceRestrictModule V₁).obj M
  X₃ := (openSubspaceRestrictModule V₂).obj M
  X₄ := (openSubspaceRestrictModule (V₁ ⊓ V₂)).obj M
  f₁₂ := (openSubspaceRestrictModuleUnit V₁).app M
  f₁₃ := (openSubspaceRestrictModuleUnit V₂).app M
  f₂₄ := (openSubspaceRestrictModuleLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).app M
  f₃₄ := (openSubspaceRestrictModuleLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).app M
  fac := by
    rw [← NatTrans.comp_app, openSubspaceRestrictModuleUnit_comp_LE, ← NatTrans.comp_app,
      openSubspaceRestrictModuleUnit_comp_LE]

/-- **The Mayer--Vietoris short complex of a sheaf of modules**
`M ⟶ j_{V₁, *}(M|_{V₁}) ⊕ j_{V₂, *}(M|_{V₂}) ⟶ j_{V₁ ⊓ V₂, *}(M|_{V₁ ⊓ V₂})`, the second map
the difference of the two restrictions. -/
def mayerVietorisShortComplex (M : ModuleSheaf S) : ShortComplex (ModuleSheaf S) :=
  ShortComplex.mk (biprod.lift (mayerVietorisSquare V₁ V₂ M).f₁₂ (mayerVietorisSquare V₁ V₂ M).f₁₃)
    (biprod.desc (mayerVietorisSquare V₁ V₂ M).f₂₄ (-(mayerVietorisSquare V₁ V₂ M).f₃₄))
    (by simp [(mayerVietorisSquare V₁ V₂ M).fac])

/-! ### Exactness -/

/-- A square of presheaves is cartesian as soon as it is cartesian at every object. -/
theorem isPullback_of_evaluation {C D : Type*} [Category C] [Category D] {P X Y Z : C ⥤ D}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : ∀ c : C, IsPullback (fst.app c) (snd.app c) (f.app c) (g.app c)) :
    IsPullback fst snd f g :=
  IsPullback.of_isLimit (evaluationJointlyReflectsLimits _ fun c ↦
    (isLimitMapConePullbackConeEquiv ((evaluation C D).obj c) w).symm (h c).isLimit)

/-- **The Mayer--Vietoris square of a sheaf of modules is cartesian** for an open covering
`X = V₁ ∪ V₂`.  On the sections over an object `A` it is the square of sections of `M` over the
Mayer--Vietoris square of `A`, which is cartesian by the sheaf condition,
`isPullback_op_map_of_cover`; limits of sheaves of modules are computed on sections. -/
theorem isPullback_mayerVietorisSquare {V₁ V₂ : S.X.Opens} (hV : V₁ ⊔ V₂ = ⊤)
    (M : ModuleSheaf S) : (mayerVietorisSquare V₁ V₂ M).IsPullback := by
  have : ReflectsLimitsOfShape WalkingCospan (toAbelianSheaf S) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let Φ := toAbelianSheaf S ⋙ sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}
  refine IsPullback.of_map_of_faithful Φ (isPullback_of_evaluation
    (by rw [← Functor.map_comp, ← Functor.map_comp, (mayerVietorisSquare V₁ V₂ M).fac])
    fun A ↦ ?_)
  exact isPullback_op_map_of_cover (openSubspaceCoverSquare V₁ V₂ A.unop)
    (isPullback_openSubspaceCoverSquare V₁ V₂ A.unop)
    (ofTwoArrows_openSubspaceCoverSquare_mem_smallTopology hV A.unop) ((toAbelianSheaf S).obj M)

/-- **The difference of the two restrictions to `V₁ ⊓ V₂` is an epimorphism** for an open covering
`X = V₁ ∪ V₂`.  It is locally surjective: over `A|_{V₁}` the restriction from `V₂` to `V₁ ⊓ V₂` is
an isomorphism, and symmetrically over `A|_{V₂}`, and these two cover `A`. -/
theorem epi_mayerVietorisShortComplex_g {V₁ V₂ : S.X.Opens} (hV : V₁ ⊔ V₂ = ⊤)
    (M : ModuleSheaf S) : Epi (mayerVietorisShortComplex V₁ V₂ M).g := by
  apply (toAbelianSheaf S).epi_of_epi_map
  have hls : Sheaf.IsLocallySurjective ((toAbelianSheaf S).map
      (mayerVietorisShortComplex V₁ V₂ M).g) := by
    refine ⟨fun {A} s ↦ (smallTopology S).superset_covering ?_
      (ofTwoArrows_openSubspaceCoverSquare_mem_smallTopology hV A)⟩
    change Sieve.ofTwoArrows ((openSubspaceAdjunction V₁).counit.app A)
      ((openSubspaceAdjunction V₂).counit.app A) ≤ _
    rw [Sieve.generate_le_iff]
    rintro Z k ⟨(_ | _)⟩
    · have := isIso_openSubspaceRestrictEndoLE_app (U := V₁) (inf_le_right : V₁ ⊓ V₂ ≤ V₂) le_rfl
        ((openSubspaceRestrictEndo V₁).obj A)
        (range_toX_openSubspaceInclusion_obj_subset V₁ _)
      let B := (openSubspaceRestrictEndo V₁).obj A
      let α := (openSubspaceRestrictEndoLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).app B
      let s' : M.val.obj (op ((openSubspaceRestrictEndo (V₁ ⊓ V₂)).obj B)) :=
        ((toAbelianSheaf S).obj (mayerVietorisShortComplex V₁ V₂ M).X₃).obj.map
          ((openSubspaceAdjunction V₁).counit.app A).op s
      let t' : M.val.obj (op ((openSubspaceRestrictEndo V₂).obj B)) := M.val.map (inv α).op s'
      let x : ToType (((toAbelianSheaf S).obj
          ((mayerVietorisSquare V₁ V₂ M).X₂ ⊞ (mayerVietorisSquare V₁ V₂ M).X₃)).obj.obj (op B)) :=
        ((toAbelianSheaf S).map (biprod.inr : (mayerVietorisSquare V₁ V₂ M).X₃ ⟶
          (mayerVietorisSquare V₁ V₂ M).X₂ ⊞ (mayerVietorisSquare V₁ V₂ M).X₃)).hom.app (op B) t'
      refine ⟨-x, ?_⟩
      have e := ConcreteCategory.congr_hom
        (congrArg (fun φ ↦ ((toAbelianSheaf S).map φ).hom.app (op B))
        (biprod.inr_desc (mayerVietorisSquare V₁ V₂ M).f₂₄ (-(mayerVietorisSquare V₁ V₂ M).f₃₄))) t'
      rw [Functor.map_comp, Functor.map_neg] at e
      have hneg : ∀ y,
          ((-(toAbelianSheaf S).map (mayerVietorisSquare V₁ V₂ M).f₃₄).hom.app (op B)) y =
          -(((toAbelianSheaf S).map (mayerVietorisSquare V₁ V₂ M).f₃₄).hom.app (op B) y) :=
        fun _ ↦ rfl
      refine (map_neg (ConcreteCategory.hom (((toAbelianSheaf S).map
        (mayerVietorisShortComplex V₁ V₂ M).g).hom.app (op B))) x).trans ?_
      refine (congrArg Neg.neg (e.trans (hneg t'))).trans ?_
      refine (neg_neg _).trans ?_
      change M.val.map α.op (M.val.map (inv α).op s') = s'
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, IsIso.hom_inv_id, op_id]
      simp only [PresheafOfModules.map_id]
      rfl
    · have := isIso_openSubspaceRestrictEndoLE_app (U := V₂) (inf_le_left : V₁ ⊓ V₂ ≤ V₁)
        (inf_comm V₂ V₁).le ((openSubspaceRestrictEndo V₂).obj A)
        (range_toX_openSubspaceInclusion_obj_subset V₂ _)
      let B := (openSubspaceRestrictEndo V₂).obj A
      let α := (openSubspaceRestrictEndoLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).app B
      let s' : M.val.obj (op ((openSubspaceRestrictEndo (V₁ ⊓ V₂)).obj B)) :=
        ((toAbelianSheaf S).obj (mayerVietorisShortComplex V₁ V₂ M).X₃).obj.map
          ((openSubspaceAdjunction V₂).counit.app A).op s
      let t' : M.val.obj (op ((openSubspaceRestrictEndo V₁).obj B)) := M.val.map (inv α).op s'
      let x : ToType (((toAbelianSheaf S).obj
          ((mayerVietorisSquare V₁ V₂ M).X₂ ⊞ (mayerVietorisSquare V₁ V₂ M).X₃)).obj.obj (op B)) :=
        ((toAbelianSheaf S).map (biprod.inl : (mayerVietorisSquare V₁ V₂ M).X₂ ⟶
          (mayerVietorisSquare V₁ V₂ M).X₂ ⊞ (mayerVietorisSquare V₁ V₂ M).X₃)).hom.app (op B) t'
      refine ⟨x, ?_⟩
      have e := ConcreteCategory.congr_hom
        (congrArg (fun φ ↦ ((toAbelianSheaf S).map φ).hom.app (op B))
          (biprod.inl_desc (mayerVietorisSquare V₁ V₂ M).f₂₄ (-(mayerVietorisSquare V₁ V₂ M).f₃₄)))
        t'
      rw [Functor.map_comp] at e
      refine e.trans ?_
      change M.val.map α.op (M.val.map (inv α).op s') = s'
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, IsIso.hom_inv_id, op_id]
      simp only [PresheafOfModules.map_id]
      rfl
  infer_instance

/-- **The Mayer--Vietoris sequence of a sheaf of modules is short exact** for an open covering
`X = V₁ ∪ V₂`:

`0 ⟶ M ⟶ j_{V₁, *}(M|_{V₁}) ⊕ j_{V₂, *}(M|_{V₂}) ⟶ j_{V₁ ⊓ V₂, *}(M|_{V₁ ⊓ V₂}) ⟶ 0`. -/
theorem mayerVietorisShortComplex_shortExact {V₁ V₂ : S.X.Opens} (hV : V₁ ⊔ V₂ = ⊤)
    (M : ModuleSheaf S) : (mayerVietorisShortComplex V₁ V₂ M).ShortExact := by
  have hme := (mayerVietorisShortComplex V₁ V₂ M).exact_and_mono_f_iff_f_is_kernel.mpr
    ⟨(isPullback_mayerVietorisSquare hV M).isLimitKernelFork⟩
  have := epi_mayerVietorisShortComplex_g hV M
  exact { exact := hme.1, mono_f := hme.2 }

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
