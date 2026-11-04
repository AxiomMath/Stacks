module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealAffine

/-!
# The comparison map of [Stacks, Tag 07IQ] along an arbitrary morphism, on global sections

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `g : (U', T', δ') ⟶ (U, T, δ)` be a
morphism of `CRIS(X/S)`.  This module isolates, for an **arbitrary** `g`, the part of the affine
computation of the base change of sections that does not mention a tensor product: the comparison
map

`c_g : g^* F_T ⟶ F_{T'}`

of [Stacks, Tag 07IQ] read along the morphism `g : T' ⟶ T` of ambient schemes, its bijectivity on
sections for a crystal, and the resulting identification of `Γ(T', g^* F_T)` with `F(U', T', δ')`.

`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` carries out the same
construction for the first projection `p₀ : T' ⟶ T` of the first-order universal thickening of
[Stacks, Tag 07J2], where the names are specialised to that morphism; the development here is
word for word that one with `p₀` replaced by `g`, and is what the degree-two analogue at the
second projection `q₀ : T'' ⟶ T` of [Stacks, Tag 07J3] consumes in
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderIdealAffine.lean`.

Nothing here is about tensor products, and that is the reason it can be stated for an arbitrary
`g`: the two tensor products of the affine computation carry scalar actions built from `g`, so
they cannot be found by instance search from the two objects alone and the tensor-level glue has
to be written out at each morphism separately.  Everything below is free of that constraint.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.affineComparisonAlong` — the comparison map
  `g^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ], read along the morphism `g : T' ⟶ T` of ambient
  schemes.
* `Crystalline.GlobalCrystallineSituation.ambientComparisonAlong` — the same map with both sides
  read over the structure sheaf of the ambient scheme.
* `Crystalline.GlobalCrystallineSituation.affineChainTailAlong` — the tail of the affine chain:
  the sections of `g^* F_T` over the whole of `T'` carried to the sections of `F` over
  `(U', T', δ')`.

## Main results

* `Crystalline.GlobalCrystallineSituation.isIso_affineComparisonAlong` — the comparison map of a
  crystal is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.bijective_affineChainTailAlong` — the tail of the chain
  is bijective for a crystal.
* `Crystalline.GlobalCrystallineSituation.affineChainTailAlong_smul_ambientPullbackSectionTopAlong`
  — the tail on a scalar multiple of a pullback of a section, which is the whole of the
  computation that follows the affine base-change comparison.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A A' : Thickening S} (g : A' ⟶ A)

/-! ### Two normalisations of the morphism of ambient schemes -/

/-- The whole of the ambient scheme of the source is contained in the preimage of the whole of the
ambient scheme of the target, the two being equal.  Named because the proof term has to carry this
type and not the type of `le_top`, which is only definitionally equal to it and which `rw`
therefore refuses. -/
theorem top_le_preimage_ambient :
    (⊤ : A'.thickening.target.scheme.Opens) ≤ g.targetHom.hom ⁻¹ᵁ ⊤ := le_top

/-- **The restriction map of `𝒪_{X/S}` along `g` is the map on global sections of the morphism of
ambient schemes.**  Both are the comorphism of `g : T' ⟶ T` read over `⊤`; the restriction map of
the structure sheaf of the site is that comorphism by definition, and
`AlgebraicGeometry.Scheme.Hom.appLE` at `⊤, ⊤` is it followed by a restriction map between two
spellings of `⊤`, which is the identity.

Stated pointwise rather than as an equation of ring homomorphisms: `crysSheafRingMap` carries the
ring structure of `Γ(T, 𝒪_T)` through `RingCat` and
`AlgebraicGeometry.Scheme.Hom.appLE` carries it through `CommRingCat`, so the two `RingHom` types
have different instance arguments and the equation of the two maps is not accepted at the
`instances` transparency level, the carriers being definitionally equal but the instance paths
not syntactically so. -/
theorem appLE_top_eq_crysSheafRingMap
    (hVU : (⊤ : A'.thickening.target.scheme.Opens) ≤ g.targetHom.hom ⁻¹ᵁ ⊤)
    (b : crysSheafRing S A) :
    (g.targetHom.hom.appLE ⊤ ⊤ hVU).hom b = crysSheafRingMap g b := by
  have hid : (A'.thickening.target.scheme.presheaf.map (homOfLE hVU).op :
      Γ(A'.thickening.target.scheme, ⊤) ⟶ Γ(A'.thickening.target.scheme, ⊤)) =
      𝟙 Γ(A'.thickening.target.scheme, ⊤) :=
    A'.thickening.target.scheme.presheaf.map_id _
  show (A'.thickening.target.scheme.presheaf.map (homOfLE hVU).op).hom
      ((g.targetHom.hom.app ⊤).hom b) = _
  exact congrArg (fun k ↦ CommRingCat.Hom.hom k ((g.targetHom.hom.app ⊤).hom b)) hid

/-! ### The two adjunctions behind the comparison of the two pullbacks -/

/-- **The pullback along the crystalline `f`-map of `g`, as a left adjoint on modules over the
structure sheaf of the ambient scheme.**  It is the restriction of scalars along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso` followed by
the pullback of sheaves of modules along the `f`-map of [Stacks, Tag 07IQ]. -/
def crysPullbackAdjunctionAlong :
    SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).hom ⋙
        SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g) ⊣
      SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g) ⋙
        SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv :=
  (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).comp
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (Thickening.ringRestrictionSheafFMap g))

/-- **The pullback along the morphism `g : T' ⟶ T` of ambient schemes, as a left adjoint of the
same functor.**  Mathlib's pullback–pushforward adjunction of a morphism of schemes, composed
with the restriction of scalars over `T'` and transported along
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePushforwardIso`. -/
def ambientPullbackAdjunctionAlong :
    Scheme.Modules.pullback g.targetHom.hom ⋙
        SheafOfModules.restrictScalars
          (Thickening.ringRestrictionSheafStructureIso A').hom ⊣
      SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g) ⋙
        SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g.targetHom.hom).comp
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso A'))).ofNatIsoRight
    (Thickening.ambientSchemePushforwardIso g).symm

/-- **The unit of
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong` is the unit of Mathlib's
pullback–pushforward adjunction of the morphism `g : T' ⟶ T` of ambient schemes, on sections.**
The two extra factors are the unit of a restriction of scalars along an isomorphism and the
comparison of the two pushforwards, and both are the identity on sections. -/
theorem ambientPullbackAdjunctionAlong_unit_app_val_app
    (N : SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf)
    (W : (A.thickening.target.scheme.Opens)ᵒᵖ) (a : N.val.obj W) :
    ((ambientPullbackAdjunctionAlong g).unit.app N).val.app W a =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.targetHom.hom).unit.app N).val.app W a := by
  show ((Scheme.Modules.pullback g.targetHom.hom).obj N).val.map
      (𝟙 (op (g.targetHom.hom ⁻¹ᵁ W.unop)))
      (((Scheme.Modules.pullbackPushforwardAdjunction g.targetHom.hom).unit.app N).val.app W a) = _
  rw [((Scheme.Modules.pullback g.targetHom.hom).obj N).val.map_id]
  rfl

/-- **The comparison of the two pullbacks of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` is the uniqueness of
left adjoints applied to the two adjunctions above.**  True by definition; the point of the
statement is that the two adjunctions are available as named objects, so that Mathlib's
compatibilities of `CategoryTheory.Adjunction.leftAdjointUniq` with the unit and with the adjoint
transposes can be used. -/
theorem ambientSchemePullbackIso_eq_leftAdjointUniq :
    Thickening.ambientSchemePullbackIso g =
      Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
        (ambientPullbackAdjunctionAlong g) := rfl

/-! ### The comparison of the pullback along the morphism of ambient schemes with `F_{T'}` -/

/-- **The comparison map `g^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ], read along the morphism
`g : T' ⟶ T` of ambient schemes.**  It is the adjoint transpose of the `f`-map of
[Stacks, Tag 07IQ] through
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong`, that is, the comparison
map of the crystalline `f`-map read through
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso`. -/
def affineComparisonAlong :
    (SheafOfModules.restrictScalars
          (Thickening.ringRestrictionSheafStructureIso A').hom).obj
        ((Scheme.Modules.pullback g.targetHom.hom).obj
          (Thickening.ambientModuleRestriction M A)) ⟶
      Thickening.moduleRestrictionSheaf M A' :=
  ((ambientPullbackAdjunctionAlong g).homEquiv _ _).symm
    ((SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv).map
      (Thickening.moduleFMapSheaf M g))

/-- **The normalisation of the comparison map: it carries the pullback of a section to the
restriction of that section along `g`.**  The adjoint transpose of a morphism is the unit followed
by the pushforward of the transpose, the unit of
`Crystalline.GlobalCrystallineSituation.ambientPullbackAdjunctionAlong` is on sections the unit of
Mathlib's pullback–pushforward adjunction of `g : T' ⟶ T`, and that unit on sections over the
whole space is `AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
theorem affineComparisonAlong_pullbackSection
    (h : (⊤ : A'.thickening.target.scheme.Opens) ≤ g.targetHom.hom ⁻¹ᵁ ⊤)
    (a : (Thickening.ambientModuleRestriction M A).val.obj (op ⊤)) :
    (affineComparisonAlong M g).val.app (op (g.targetHom.hom ⁻¹ᵁ ⊤))
        (Scheme.Modules.pullbackSection g.targetHom.hom
          (Thickening.ambientModuleRestriction M A) ⊤ ⊤ h a) =
      M.val.map (Thickening.restrictOpenMap g ⊤).op a := by
  have hθ : (ambientPullbackAdjunctionAlong g).unit.app
          (Thickening.ambientModuleRestriction M A) ≫
        (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g) ⋙
          SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map
          (affineComparisonAlong M g) =
      (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv).map
        (Thickening.moduleFMapSheaf M g) := by
    show (ambientPullbackAdjunctionAlong g).homEquiv _ _ (affineComparisonAlong M g) = _
    exact Equiv.apply_symm_apply _ _
  refine (congrArg (fun y ↦ (affineComparisonAlong M g).val.app
      (op (g.targetHom.hom ⁻¹ᵁ ⊤)) y) ?_).trans (congrArg (fun k ↦ k.val.app (op ⊤) a) hθ)
  exact (Scheme.Modules.pullbackSection_top _ _ h a).trans
    (ambientPullbackAdjunctionAlong_unit_app_val_app g
      (Thickening.ambientModuleRestriction M A) (op ⊤) a).symm

/-- **The same adjoint transpose, taken through the crystalline `f`-map, is the comparison map
`c_g` of [Stacks, Tag 07IQ].**  The transpose through
`Crystalline.GlobalCrystallineSituation.crysPullbackAdjunctionAlong` is taken in two steps:
through the restriction of scalars, where the counit and its naturality turn the restriction of
scalars of the `f`-map back into the `f`-map, and then through the pullback–pushforward
adjunction, where by definition the transpose of the `f`-map is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf`. -/
theorem crysPullbackAdjunctionAlong_homEquiv_symm_moduleFMapSheaf :
    ((crysPullbackAdjunctionAlong g).homEquiv
        (Thickening.ambientModuleRestriction M A)
        (Thickening.moduleRestrictionSheaf M A')).symm
      ((SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).inv).map
        (Thickening.moduleFMapSheaf M g)) =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
            (Thickening.moduleRestrictionSheaf M A)) ≫
        Thickening.moduleComparisonSheaf M g := by
  have hinner : (SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map
            (Thickening.moduleFMapSheaf M g)) ≫
        (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
          ((SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj
            (Thickening.moduleRestrictionSheaf M A')) =
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
          (Thickening.moduleRestrictionSheaf M A) ≫
        Thickening.moduleFMapSheaf M g :=
    (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).counit.naturality
        (Thickening.moduleFMapSheaf M g)
  have hcounit : (crysPullbackAdjunctionAlong g).counit.app
        (Thickening.moduleRestrictionSheaf M A') =
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
            (Thickening.ringRestrictionSheafStructureIso A)).counit.app
            ((SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj
              (Thickening.moduleRestrictionSheaf M A'))) ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (Thickening.ringRestrictionSheafFMap g)).counit.app
          (Thickening.moduleRestrictionSheaf M A') :=
    Adjunction.comp_counit_app
      (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
        (Thickening.ringRestrictionSheafStructureIso A))
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (Thickening.ringRestrictionSheafFMap g))
      (Thickening.moduleRestrictionSheaf M A')
  show (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
        ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).hom).map
          ((SheafOfModules.restrictScalars
            (Thickening.ringRestrictionSheafStructureIso A).inv).map
            (Thickening.moduleFMapSheaf M g))) ≫
      (crysPullbackAdjunctionAlong g).counit.app (Thickening.moduleRestrictionSheaf M A') =
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
        ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
          (Thickening.ringRestrictionSheafStructureIso A)).counit.app
          (Thickening.moduleRestrictionSheaf M A)) ≫
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).map
          (Thickening.moduleFMapSheaf M g) ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g)).counit.app
          (Thickening.moduleRestrictionSheaf M A')
  rw [hcounit, ← Category.assoc, ← Functor.map_comp, hinner, Functor.map_comp, Category.assoc]

/-- **The comparison map `g^* F_T ⟶ F_{T'}` of a crystal is an isomorphism.**  Through
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` it is the comparison
map of [Stacks, Tag 07IQ] along the crystalline `f`-map of `g`, precomposed with the pullback of
the counit of a restriction of scalars along an isomorphism; the first is an isomorphism by the
crystal condition and the second is one because the counit is. -/
theorem isIso_affineComparisonAlong (hM : IsSheafCrystal M) :
    IsIso (affineComparisonAlong M g) := by
  have : IsIso (Thickening.moduleComparisonSheaf M g) := hM _ _ _
  have : IsIso ((Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
      (Thickening.ringRestrictionSheafStructureIso A)).counit.app
      (Thickening.moduleRestrictionSheaf M A)) :=
    Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app _ _
  have : IsIso ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
      (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientModuleRestriction M A)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) _
  have : IsIso ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
      (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientModuleRestriction M A) ≫
      affineComparisonAlong M g) := by
    refine (congrArg IsIso ((Adjunction.leftAdjointUniq_hom_app_homEquiv_symm _ _ _).trans
      (crysPullbackAdjunctionAlong_homEquiv_symm_moduleFMapSheaf M g))).mpr
      (IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance)
  exact IsIso.of_isIso_comp_left ((Adjunction.leftAdjointUniq (crysPullbackAdjunctionAlong g)
    (ambientPullbackAdjunctionAlong g)).hom.app (Thickening.ambientModuleRestriction M A))
    (affineComparisonAlong M g)

/-- **The comparison map of a crystal is bijective on sections over every open of `T'`.**  This is
the form in which the comparison enters the affine computation of the base change: composed with
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` over `⊤` it identifies the base change of
the global sections with `F(U', T', δ')`. -/
theorem bijective_affineComparisonAlong_val_app (hM : IsSheafCrystal M)
    (W : (A'.thickening.target.scheme.Opens)ᵒᵖ) :
    Function.Bijective fun x ↦ (affineComparisonAlong M g).val.app W x := by
  have := isIso_affineComparisonAlong M g hM
  have := Stacks.SheafOfModules.isIso_val_app_of_isIso (affineComparisonAlong M g) W
  exact ConcreteCategory.bijective_of_isIso ((affineComparisonAlong M g).val.app W)

/-! ### The comparison map read over the structure sheaf of the ambient scheme -/

/-- **The comparison map `g^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ] with both sides read over the
structure sheaf of the ambient scheme.**  It is the adjoint transpose of
`Crystalline.GlobalCrystallineSituation.affineComparisonAlong` through the adjunction of
restrictions of scalars along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`; by
`Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_homEquiv_val_app` it is the same map on
sections.  This is the spelling in which the comparison can be composed with
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`. -/
def ambientComparisonAlong :
    (Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A) ⟶
      ambientSchemeModules M A' :=
  (Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso
    (Thickening.ringRestrictionSheafStructureIso A')).homEquiv _ _ (affineComparisonAlong M g)

/-- **The change of spelling does not move sections.** -/
theorem ambientComparisonAlong_val_app (W : (A'.thickening.target.scheme.Opens)ᵒᵖ)
    (y : ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A)).val.obj W) :
    (ambientComparisonAlong M g).val.app W y = (affineComparisonAlong M g).val.app W y :=
  Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_homEquiv_val_app _ _ W y

/-- The comparison map on sections over the whole of `T'`, as an additive map. -/
def ambientComparisonAlongTop :
    Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A), ⊤) →+
      Γ(ambientSchemeModules M A', ⊤) :=
  AddMonoidHom.mk' (fun y ↦ (ambientComparisonAlong M g).app ⊤ y) (fun y y' ↦ map_add _ y y')

/-- **For a crystal that map is bijective**, being
`Crystalline.GlobalCrystallineSituation.affineComparisonAlong` on sections. -/
theorem bijective_ambientComparisonAlongTop (hM : IsSheafCrystal M) :
    Function.Bijective (ambientComparisonAlongTop M g) := by
  have h : (ambientComparisonAlongTop M g : _ → _) =
      fun y ↦ (affineComparisonAlong M g).val.app (op ⊤) y :=
    funext fun y ↦ ambientComparisonAlong_val_app M g (op ⊤) y
  rw [h]
  exact bijective_affineComparisonAlong_val_app M g hM (op ⊤)

/-- The pullback along `g` of a section of `F_T` over the whole of `T`, as a section of `g^* F_T`
over the whole of `T'`, with its type named at the sections notation. -/
def ambientPullbackSectionTopAlong (x : Γ(ambientSchemeModules M A, ⊤)) :
    Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A), ⊤) :=
  Scheme.Modules.pullbackSection g.targetHom.hom (ambientSchemeModules M A) ⊤ ⊤
    (top_le_preimage_ambient g) x

/-- **The normalisation of the comparison map in the ambient spelling**: it carries the pullback
of a section to the restriction of that section along `g`.  This is
`Crystalline.GlobalCrystallineSituation.affineComparisonAlong_pullbackSection` moved across the
change of spelling. -/
theorem ambientComparisonAlong_pullbackSection
    (h : (⊤ : A'.thickening.target.scheme.Opens) ≤ g.targetHom.hom ⁻¹ᵁ ⊤)
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    (ambientComparisonAlong M g).app ⊤
        (Scheme.Modules.pullbackSection g.targetHom.hom (ambientSchemeModules M A) ⊤ ⊤ h x) =
      ambientModuleSection M A'
        (moduleSiteRestrict M (restrictOpenMapTop g) (siteModuleSection M A x)) :=
  (ambientComparisonAlong_val_app M g (op ⊤) _).trans
    (affineComparisonAlong_pullbackSection M g h (siteModuleSection M A x))

/-- The same normalisation, with the pullback of the section named. -/
theorem ambientComparisonAlong_ambientPullbackSectionTopAlong
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    (ambientComparisonAlong M g).app ⊤ (ambientPullbackSectionTopAlong M g x) =
      ambientModuleSection M A'
        (moduleSiteRestrict M (restrictOpenMapTop g) (siteModuleSection M A x)) :=
  ambientComparisonAlong_pullbackSection M g (top_le_preimage_ambient g) x

/-- **The tail of the affine chain**, after the base-change comparison: the sections of `g^* F_T`
over the whole of `T'` are carried to the sections of `F` over `(U', T', δ')`, by the comparison
map followed by the two changes of spelling. -/
def affineChainTailAlong :
    Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A), ⊤) →+
      M.val.obj (op A') :=
  ((restrictOpenTopEquiv M A').symm.toAddMonoidHom.comp (siteModuleSectionHom M A')).comp
    (ambientComparisonAlongTop M g)

/-- The tail of the chain, written out. -/
theorem affineChainTailAlong_apply
    (y : Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeModules M A), ⊤)) :
    affineChainTailAlong M g y =
      (restrictOpenTopEquiv M A').symm
        (siteModuleSection M A' ((ambientComparisonAlong M g).app ⊤ y)) := rfl

/-- **The tail of the chain is bijective for a crystal**: each of its three factors is. -/
theorem bijective_affineChainTailAlong (hM : IsSheafCrystal M) :
    Function.Bijective (affineChainTailAlong M g) :=
  ((restrictOpenTopEquiv M A').symm.bijective.comp (bijective_siteModuleSectionHom M A')).comp
    (bijective_ambientComparisonAlongTop M g hM)

/-- **The tail of the chain on a scalar multiple of a pullback of a section.**  This is the whole
of the computation that follows the base-change comparison: the comparison map is semilinear, its
normalisation applies to the pullback, and the two changes of spelling are semilinear. -/
theorem affineChainTailAlong_smul_ambientPullbackSectionTopAlong (t : crysSheafRing S A')
    (x : Γ(ambientSchemeModules M A, ⊤)) :
    affineChainTailAlong M g (ambientRingSection A' t • ambientPullbackSectionTopAlong M g x) =
      t • (restrictOpenTopEquiv M A').symm
        (moduleSiteRestrict M (restrictOpenMapTop g) (siteModuleSection M A x)) := by
  rw [affineChainTailAlong_apply, Scheme.Modules.Hom.app_smul,
    ambientComparisonAlong_ambientPullbackSectionTopAlong, ambientModuleSection_smul,
    siteModuleSection_ambientModuleSection, restrictOpenTopEquiv_symm_smul_site]

end Crystalline.GlobalCrystallineSituation

end

end
