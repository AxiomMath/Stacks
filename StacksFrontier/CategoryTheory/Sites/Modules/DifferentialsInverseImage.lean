module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsRepresentable
import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image of the sheaf of relative differentials

Let `f : Sh(D) ⟶ Sh(C)` be a morphism of topoi, presented by a continuous functor `F : C ⥤ D`
of the underlying sites, and let `φ : O₁ ⟶ O₂` be a homomorphism of sheaves of commutative
rings on `C`. The inverse image of the sheaf of relative differentials `Ω_{O₂/O₁}` is
canonically the sheaf of relative differentials of `f⁻¹O₁ ⟶ f⁻¹O₂`, compatibly with the
universal derivations.

## Main definitions

* `sqZeroExtSheaf` is the square-zero extension `O ⋉ N` of a sheaf of commutative rings by a
  sheaf of modules, with projection `sqZeroExtSheafProj` and zero section `sqZeroExtSheafInl`.
* `inverseImageRing`, `inverseImageRingHom` and `inverseImageModule` are the inverse image of
  a sheaf of commutative rings, the unit `O ⟶ f_* f⁻¹O` read on sheaves of rings, and the
  inverse image of a sheaf of modules taken along that unit.
* `pushforwardInverseImageDerivation` reads a relative derivation for `f⁻¹φ` along the unit as
  a relative derivation for `φ` with values in the direct image.
* `inverseImageDerivation` is the inverse image of a relative derivation.
* `pullbackDifferentialsIso` is the canonical identification
  `f⁻¹Ω_{O₂/O₁} ≅ Ω_{f⁻¹O₂/f⁻¹O₁}`.

## Main results

* `directImageDerivationEquiv`: relative derivations for `f⁻¹φ` with values in `N` are exactly
  the relative derivations for `φ` with values in `f_* N`.
* `pullbackDifferentialsIso_compatible` and `pullbackDifferentialsIso_unique`: the canonical
  identification carries the inverse image of the universal derivation to the universal
  derivation, and is the only isomorphism that does so.

## Implementation notes

A relative derivation with values in `N` is a splitting of the square-zero extension
`f⁻¹O₂ ⋉ N` which is trivial on the base, so `directImageDerivationEquiv` is obtained from the
inverse-image/direct-image adjunction on sheaves of commutative rings alone: the splitting
clause corresponds to the transpose being the unit, and the two triviality clauses correspond
by naturality of the unit. Nothing about the inverse image of a sheaf of modules, and no
commutation of `f⁻¹` with a forgetful functor, is needed. The identification of the two sheaves
of differentials is then the comparison of two objects corepresenting one functor.

Both sites are small in the single universe of the sections of the sheaves of rings and of the
modules, and the inverse image of sheaves of commutative rings is assumed to exist; this is the
generality in which the representing sheaf of differentials is available.

## References

* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ)
-/

@[expose] public section

open CategoryTheory PresheafOfModules
open CategoryTheory.Functor

universe u

namespace Stacks.Sheaves.Differentials
section SqZero

/-- Morphisms of sheaves of commutative rings agreeing on all sections are equal. -/
private theorem sheaf_hom_ext_apply {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {A B : Sheaf K CommRingCat.{u}} {f g : A ⟶ B}
    (h : ∀ U b, (f.hom.app U).hom b = (g.hom.app U).hom b) : f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ CommRingCat.hom_ext (RingHom.ext (h U))))

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The square-zero extension of a sheaf of commutative rings by a sheaf of modules satisfies
the sheaf condition, since its two components do. -/
theorem isSheaf_sqZeroExtPresheaf (O : Sheaf K CommRingCat.{u})
    (N : SheafOfModules.{u} (underlyingRingSheaf O)) :
    Presheaf.IsSheaf K (PresheafOfModules.sqZeroExtPresheaf N.val) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget K _ (forget CommRingCat.{u}),
    isSheaf_iff_isSheaf_of_type]
  have hO : Presieve.IsSheaf K (O.obj ⋙ forget CommRingCat.{u}) := by
    rw [← isSheaf_iff_isSheaf_of_type,
      ← Presheaf.isSheaf_iff_isSheaf_forget K _ (forget CommRingCat.{u})]
    exact O.property
  have hN : Presieve.IsSheaf K (N.val.presheaf ⋙ forget AddCommGrpCat.{u}) := by
    rw [← isSheaf_iff_isSheaf_of_type,
      ← Presheaf.isSheaf_iff_isSheaf_forget K _ (forget AddCommGrpCat.{u})]
    exact N.isSheaf
  intro X S hS x hx
  obtain ⟨t₁, ht₁, ht₁'⟩ := hO S hS (fun _ f h => sqZeroExtFst (M := N.val) (x f h))
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hg => congrArg (sqZeroExtFst (M := N.val)) (hx g₁ g₂ h₁ h₂ hg))
  obtain ⟨t₂, ht₂, ht₂'⟩ := hN S hS (fun _ f h => sqZeroExtSnd (M := N.val) (x f h))
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hg => congrArg (sqZeroExtSnd (M := N.val)) (hx g₁ g₂ h₁ h₂ hg))
  refine ⟨sqZeroExtMk t₁ t₂, fun Y f h => ?_, fun y hy => ?_⟩
  · exact sqZeroExt_ext (ht₁ f h) (ht₂ f h)
  · exact sqZeroExt_ext (ht₁' _ fun _ f h => congrArg (sqZeroExtFst (M := N.val)) (hy f h))
      (ht₂' _ fun _ f h => congrArg (sqZeroExtSnd (M := N.val)) (hy f h))

/-- The square-zero extension of a sheaf of commutative rings by a sheaf of modules. -/
noncomputable def sqZeroExtSheaf (O : Sheaf K CommRingCat.{u})
    (N : SheafOfModules.{u} (underlyingRingSheaf O)) : Sheaf K CommRingCat.{u} where
  obj := PresheafOfModules.sqZeroExtPresheaf N.val
  property := isSheaf_sqZeroExtPresheaf O N

/-- The projection from the square-zero extension onto the sheaf of commutative rings. -/
noncomputable def sqZeroExtSheafProj (O : Sheaf K CommRingCat.{u})
    (N : SheafOfModules.{u} (underlyingRingSheaf O)) : sqZeroExtSheaf O N ⟶ O :=
  ObjectProperty.homMk (PresheafOfModules.sqZeroExtProj N.val)

/-- The inclusion of the sheaf of commutative rings into its square-zero extension. -/
noncomputable def sqZeroExtSheafInl (O : Sheaf K CommRingCat.{u})
    (N : SheafOfModules.{u} (underlyingRingSheaf O)) : O ⟶ sqZeroExtSheaf O N :=
  ObjectProperty.homMk (PresheafOfModules.sqZeroExtInl N.val)

/-- The splitting of the projection determined by a relative derivation. -/
noncomputable def sqZeroExtSheafOfDerivation {O₀ O : Sheaf K CommRingCat.{u}} (ψ : O₀ ⟶ O)
    {N : SheafOfModules.{u} (underlyingRingSheaf O)} (δ : SheafDerivation O₀ O ψ N) :
    O ⟶ sqZeroExtSheaf O N :=
  ObjectProperty.homMk (PresheafOfModules.sqZeroExtOfDerivation N.val δ)

end SqZero

section OneSite

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)

/-- Morphisms out of the sheaf of relative differentials are the relative derivations. -/
noncomputable def differentialsHomEquiv (G : SheafOfModules.{u} (underlyingRingSheaf O₂)) :
    (moduleOfDifferentials O₁ O₂ φ ⟶ G) ≃ SheafDerivation O₁ O₂ φ G :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (underlyingRingSheaf O₂).obj)
      (P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)
      (F := G)).trans
    (presheafDifferentialsEquiv φ.hom G.val)

/-- Under the identification of morphisms with derivations, a morphism corresponds to its
postcomposition with the universal derivation. -/
theorem differentialsHomEquiv_apply (G : SheafOfModules.{u} (underlyingRingSheaf O₂))
    (h : moduleOfDifferentials O₁ O₂ φ ⟶ G) :
    differentialsHomEquiv φ G h = (universalDerivation O₁ O₂ φ).postcomp h.val := by
  ext U x
  rfl

end OneSite

section InverseImage

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Functor.IsContinuous F J K]
  [(F.sheafPushforwardContinuous CommRingCat.{u} J K).IsRightAdjoint]

/-- The inverse image of a sheaf of commutative rings. -/
noncomputable abbrev inverseImageRing (O : Sheaf J CommRingCat.{u}) : Sheaf K CommRingCat.{u} :=
  (F.sheafPullback CommRingCat.{u} J K).obj O

/-- The unit `O ⟶ f_* f⁻¹O`, after forgetting commutativity. -/
noncomputable def inverseImageRingHom (O : Sheaf J CommRingCat.{u}) :
    underlyingRingSheaf O ⟶
      (F.sheafPushforwardContinuous RingCat.{u} J K).obj
        (underlyingRingSheaf (inverseImageRing J K F O)) :=
  ObjectProperty.homMk (Functor.whiskerRight
    ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.app O).hom
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The direct image of presheaves of modules along the inverse-image unit has a left adjoint. -/
instance isRightAdjoint_presheafPushforward (O : Sheaf J CommRingCat.{u}) :
    (PresheafOfModules.pushforward.{u} (inverseImageRingHom J K F O).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- The direct image of sheaves of modules along the inverse-image unit has a left adjoint. -/
instance isRightAdjoint_pushforward (O : Sheaf J CommRingCat.{u}) :
    (SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O)).IsRightAdjoint :=
  SheafOfModules.instIsRightAdjointPushforward _

/-- The inverse image of a sheaf of `O`-modules. -/
noncomputable def inverseImageModule (O : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (underlyingRingSheaf O)) :
    SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O)) :=
  (SheafOfModules.pullback.{u} (inverseImageRingHom J K F O)).obj M

/-- The inverse-image/pushforward adjunction on sheaves of modules. -/
noncomputable def inverseImageAdjunction (O : Sheaf J CommRingCat.{u}) :
    SheafOfModules.pullback.{u} (inverseImageRingHom J K F O) ⊣
      SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O) :=
  SheafOfModules.pullbackPushforwardAdjunction _

/-- The unit sending a local section of a module to its inverse-image section. -/
noncomputable def inverseImageModuleUnit (O : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (underlyingRingSheaf O)) :
    M ⟶ (SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O)).obj
      (inverseImageModule J K F O M) :=
  (inverseImageAdjunction J K F O).unit.app M

variable {O₁ O₂ : Sheaf J CommRingCat.{u}}

/-- Naturality of the inverse-image unit on sheaves of rings, on sections. -/
theorem inverseImageRingHom_naturality_apply (ψ : O₁ ⟶ O₂) (U : Cᵒᵖ) (x : O₁.obj.obj U) :
    ((inverseImageRingHom J K F O₂).hom.app U).hom ((ψ.hom.app U).hom x) =
      (((F.sheafPullback CommRingCat.{u} J K).map ψ).hom.app (F.op.obj U)).hom
        (((inverseImageRingHom J K F O₁).hom.app U).hom x) := by
  have h := (F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.naturality ψ
  replace h := congrArg (fun m : O₁ ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
      (inverseImageRing J K F O₂) => (m.hom.app U).hom x) h
  simp only [Functor.id_map, Functor.comp_map] at h
  show (((F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.app O₂).hom.app U).hom
      ((ψ.hom.app U).hom x) = _
  refine h.trans ?_
  rfl


variable (φ : O₁ ⟶ O₂)

/-- A relative derivation for the inverse-image morphism of rings, read along the unit
`O ⟶ f_* f⁻¹O`, is a relative derivation for the original morphism with values in the
direct image. -/
noncomputable def pushforwardInverseImageDerivation
    (N : SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O₂)))
    (δ : SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
      ((F.sheafPullback CommRingCat.{u} J K).map φ) N) :
    SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N) where
  d {U} := (δ.d (X := F.op.obj U)).comp
      ((inverseImageRingHom J K F O₂).hom.app U).hom.toAddMonoidHom
  d_mul b b' :=
    (congrArg δ.d (map_mul ((inverseImageRingHom J K F O₂).hom.app _).hom b b')).trans
      (δ.d_mul _ _)
  d_map {U} {V} i x := by
    refine (congrArg δ.d ?_).trans (δ.d_map (F.op.map i) _)
    exact congrArg (fun m : (underlyingRingSheaf O₂).obj.obj U ⟶
      (underlyingRingSheaf (inverseImageRing J K F O₂)).obj.obj (F.op.obj V) => m.hom x)
      ((inverseImageRingHom J K F O₂).hom.naturality i)
  d_app b :=
    (congrArg δ.d (inverseImageRingHom_naturality_apply J K F φ _ b)).trans (δ.d_app _)

/-- The comparison derivation is the original one evaluated at inverse-image sections. -/
@[simp]
theorem pushforwardInverseImageDerivation_d
    (N : SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O₂)))
    (δ : SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
      ((F.sheafPullback CommRingCat.{u} J K).map φ) N) (U : Cᵒᵖ) (b : O₂.obj.obj U) :
    (pushforwardInverseImageDerivation J K F φ N δ).d b =
      δ.d (((inverseImageRingHom J K F O₂).hom.app U).hom b) :=
  rfl

/-- The comparison map commutes with postcomposition by a morphism of sheaves of modules. -/
theorem pushforwardInverseImageDerivation_postcomp
    {N N' : SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O₂))}
    (δ : SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
      ((F.sheafPullback CommRingCat.{u} J K).map φ) N) (m : N ⟶ N') :
    pushforwardInverseImageDerivation J K F φ N' (δ.postcomp m.val) =
      (pushforwardInverseImageDerivation J K F φ N δ).postcomp
        ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).map m).val :=
  rfl

section SquareZero

variable (N : SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O₂)))

/-- The unit of the inverse-image/direct-image adjunction on sheaves of commutative rings,
on sections. -/
noncomputable abbrev unitCommApp (U : Cᵒᵖ) :
    O₂.obj.obj U ⟶ (inverseImageRing J K F O₂).obj.obj (F.op.obj U) :=
  ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.app O₂).hom.app U

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Transposing a morphism of sheaves of commutative rings out of the inverse image, on
sections. -/
theorem sheafAdjunction_homEquiv_app_apply (T : Sheaf K CommRingCat.{u})
    (s : inverseImageRing J K F O₂ ⟶ T) (U : Cᵒᵖ) (b : O₂.obj.obj U) :
    ((((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₂ T) s).hom.app U).hom b
      = (s.hom.app (F.op.obj U)).hom ((unitCommApp J K F U).hom b) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The derivation underlying a relative derivation with values in a direct image, written as
an additive map into the plain sections of `N`. -/
noncomputable def pushforwardDerivationApp
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N))
    (U : Cᵒᵖ) : ↥(O₂.obj.obj U) →+ ↥(N.val.obj (F.op.obj U)) :=
  D.d

/-- The component at an object of the site of `pushforwardSqZeroHom`. -/
noncomputable def pushforwardSqZeroApp
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N))
    (U : Cᵒᵖ) :
    O₂.obj.obj U ⟶ (PresheafOfModules.sqZeroExtPresheaf N.val).obj (F.op.obj U) :=
  PresheafOfModules.sqZeroExtLift N.val (unitCommApp J K F U)
    (pushforwardDerivationApp J K F φ N D U) (fun b b' ↦ D.d_mul b b')

/-- A relative derivation of `φ` with values in the direct image of `N`, read as a morphism of
sheaves of commutative rings into the direct image of the square-zero extension. -/
noncomputable def pushforwardSqZeroHom
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N)) :
    O₂ ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
      (sqZeroExtSheaf (inverseImageRing J K F O₂) N) :=
  ObjectProperty.homMk
    { app := pushforwardSqZeroApp J K F φ N D
      naturality := fun U U' h ↦ CommRingCat.hom_ext (RingHom.ext fun b ↦ by
        refine sqZeroExt_ext ?_ ?_
        · change (unitCommApp J K F U').hom ((O₂.obj.map h).hom b)
            = ((inverseImageRing J K F O₂).obj.map (F.op.map h)).hom
                ((unitCommApp J K F U).hom b)
          exact congrArg (fun m : O₂.obj.obj U ⟶
            (inverseImageRing J K F O₂).obj.obj (F.op.obj U') => m.hom b)
            (((F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.app O₂).hom.naturality h)
        · exact D.d_map h b) }

end SquareZero

section DerivationBijection

variable (N : SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O₂)))

/-- The splitting of the square-zero extension transposed from a relative derivation with
values in the direct image. -/
noncomputable def sqZeroSection
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N)) :
    inverseImageRing J K F O₂ ⟶ sqZeroExtSheaf (inverseImageRing J K F O₂) N :=
  ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₂
    (sqZeroExtSheaf (inverseImageRing J K F O₂) N)).symm (pushforwardSqZeroHom J K F φ N D)

/-- The transposition of the splitting is the morphism into the direct image of the square-zero
extension that the derivation defines. -/
theorem sqZeroSection_homEquiv
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N)) :
    (F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₂
        (sqZeroExtSheaf (inverseImageRing J K F O₂) N) (sqZeroSection J K F φ N D)
      = pushforwardSqZeroHom J K F φ N D :=
  Equiv.apply_symm_apply _ _

/-- The splitting, evaluated at an inverse-image section, is the pair consisting of that
section and the value of the derivation. -/
theorem sqZeroSection_apply
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N))
    (U : Cᵒᵖ) (b : O₂.obj.obj U) :
    ((sqZeroSection J K F φ N D).hom.app (F.op.obj U)).hom ((unitCommApp J K F U).hom b)
      = (pushforwardSqZeroApp J K F φ N D U).hom b := by
  refine (sheafAdjunction_homEquiv_app_apply J K F _ (sqZeroSection J K F φ N D) U b).symm.trans ?_
  exact congrArg (fun m : O₂ ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
      (sqZeroExtSheaf (inverseImageRing J K F O₂) N) ↦ (m.hom.app U).hom b)
    (Equiv.apply_symm_apply _ _)

/-- The transposed morphism splits the projection from the square-zero extension. -/
theorem sqZeroSection_split
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N)) :
    sqZeroSection J K F φ N D ≫ sqZeroExtSheafProj (inverseImageRing J K F O₂) N
      = 𝟙 (inverseImageRing J K F O₂) := by
  have hid : (F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₂
      (inverseImageRing J K F O₂) (𝟙 (inverseImageRing J K F O₂))
      = (F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.app O₂ := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  refine ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₂ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, sqZeroSection_homEquiv, hid]
  refine sheaf_hom_ext_apply fun U b ↦ ?_
  show ((sqZeroExtSheafProj (inverseImageRing J K F O₂) N).hom.app (F.op.obj U)).hom
      ((pushforwardSqZeroApp J K F φ N D U).hom b) = (unitCommApp J K F U).hom b
  rfl

/-- The transposed morphism agrees with the trivial splitting on the base ring. -/
theorem sqZeroSection_triv
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N)) :
    (F.sheafPullback CommRingCat.{u} J K).map φ ≫ sqZeroSection J K F φ N D =
      (F.sheafPullback CommRingCat.{u} J K).map φ
        ≫ sqZeroExtSheafInl (inverseImageRing J K F O₂) N := by
  refine ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₁ _).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    sqZeroSection_homEquiv, Adjunction.homEquiv_unit]
  refine sheaf_hom_ext_apply fun U x ↦ ?_
  show (pushforwardSqZeroApp J K F φ N D U).hom ((φ.hom.app U).hom x)
      = ((sqZeroExtSheafInl (inverseImageRing J K F O₂) N).hom.app (F.op.obj U)).hom
          ((unitCommApp J K F U).hom ((φ.hom.app U).hom x))
  exact sqZeroExt_ext rfl (D.d_app x)

/-- The relative derivation for the inverse-image morphism of rings determined by a relative
derivation with values in the direct image. -/
noncomputable def inverseImageDerivationOfDirectImage
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N)) :
    SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
      ((F.sheafPullback CommRingCat.{u} J K).map φ) N :=
  PresheafOfModules.sqZeroExtDerivation N.val (sqZeroSection J K F φ N D).hom
    ((F.sheafPullback CommRingCat.{u} J K).map φ).hom
    (Sheaf.hom_ext_iff.mp (sqZeroSection_split J K F φ N D))
    (Sheaf.hom_ext_iff.mp (sqZeroSection_triv J K F φ N D))

/-- Reading the derivation obtained from a splitting along the inverse-image unit recovers the
original derivation with values in the direct image. -/
theorem pushforwardInverseImageDerivation_ofDirectImage
    (D : SheafDerivation O₁ O₂ φ
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N)) :
    pushforwardInverseImageDerivation J K F φ N
        (inverseImageDerivationOfDirectImage J K F φ N D) = D :=
  PresheafOfModules.derivation_ext _ fun U b ↦
    congrArg (sqZeroExtSnd (M := N.val)) (sqZeroSection_apply J K F φ N D U b)

/-- A relative derivation for the inverse-image morphism of rings is determined by its values
on inverse-image sections. -/
theorem pushforwardInverseImageDerivation_injective :
    Function.Injective (pushforwardInverseImageDerivation J K F φ N) := by
  intro δ₁ δ₂ hδ
  have hcomp : ∀ (δ : SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) N) (U : Cᵒᵖ) (b : O₂.obj.obj U),
      (((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₂
          (sqZeroExtSheaf (inverseImageRing J K F O₂) N)
          (sqZeroExtSheafOfDerivation ((F.sheafPullback CommRingCat.{u} J K).map φ) δ)).hom.app
            U).hom b
        = sqZeroExtMk (M := N.val) ((unitCommApp J K F U).hom b)
            (δ.d (((inverseImageRingHom J K F O₂).hom.app U).hom b)) := fun δ U b ↦
    (sheafAdjunction_homEquiv_app_apply J K F _
      (sqZeroExtSheafOfDerivation ((F.sheafPullback CommRingCat.{u} J K).map φ) δ) U b).trans rfl
  have hsec : sqZeroExtSheafOfDerivation ((F.sheafPullback CommRingCat.{u} J K).map φ) δ₁
      = sqZeroExtSheafOfDerivation ((F.sheafPullback CommRingCat.{u} J K).map φ) δ₂ := by
    refine ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv O₂ _).injective
      (sheaf_hom_ext_apply fun U b ↦ ?_)
    refine (hcomp δ₁ U b).trans (Eq.trans ?_ (hcomp δ₂ U b).symm)
    refine congrArg (fun z : ↥(N.val.obj (F.op.obj U)) ↦
      sqZeroExtMk (M := N.val) ((unitCommApp J K F U).hom b) z) ?_
    exact congrArg (fun m : SheafDerivation O₁ O₂ φ
        ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N) ↦ m.d b) hδ
  refine PresheafOfModules.derivation_ext N.val fun V x ↦ ?_
  exact congrArg (fun m : inverseImageRing J K F O₂ ⟶ sqZeroExtSheaf
    (inverseImageRing J K F O₂) N ↦ sqZeroExtSnd (M := N.val) ((m.hom.app V).hom x)) hsec

/-- Reading a relative derivation for the inverse-image morphism of rings along the unit
`O₂ ⟶ f_* f⁻¹O₂` is a bijection onto the relative derivations of `φ` with values in the
direct image. Both sides are morphisms of sheaves of commutative rings into the square-zero
extension `f⁻¹O₂ ⋉ N`, matched by the inverse-image/direct-image adjunction. -/
noncomputable def directImageDerivationEquiv :
    SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) N
      ≃ SheafDerivation O₁ O₂ φ
        ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj N) where
  toFun := pushforwardInverseImageDerivation J K F φ N
  invFun := inverseImageDerivationOfDirectImage J K F φ N
  left_inv _ := pushforwardInverseImageDerivation_injective J K F φ N
    (pushforwardInverseImageDerivation_ofDirectImage J K F φ N _)
  right_inv := pushforwardInverseImageDerivation_ofDirectImage J K F φ N

/-- The bijection is given by reading a derivation along the inverse-image unit. -/
@[simp]
theorem directImageDerivationEquiv_apply
    (δ : SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
      ((F.sheafPullback CommRingCat.{u} J K).map φ) N) :
    directImageDerivationEquiv J K F φ N δ = pushforwardInverseImageDerivation J K F φ N δ :=
  rfl

end DerivationBijection

section Comparison

variable (M : SheafOfModules.{u} (underlyingRingSheaf O₂))

/-- Morphisms out of the inverse image of the sheaf of relative differentials are the relative
derivations for the inverse-image morphism of rings. -/
noncomputable def inverseImageDifferentialsHomEquiv
    (G : SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O₂))) :
    (inverseImageModule J K F O₂ (moduleOfDifferentials O₁ O₂ φ) ⟶ G) ≃
      SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) G :=
  ((inverseImageAdjunction J K F O₂).homEquiv (moduleOfDifferentials O₁ O₂ φ) G).trans
    ((differentialsHomEquiv φ _).trans (directImageDerivationEquiv J K F φ G).symm)

/-- The inverse image of a relative derivation, characterised by its action on the images of
local sections under the inverse-image units. -/
noncomputable def inverseImageDerivation (d : SheafDerivation O₁ O₂ φ M) :
    SheafDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
      ((F.sheafPullback CommRingCat.{u} J K).map φ) (inverseImageModule J K F O₂ M) :=
  (directImageDerivationEquiv J K F φ (inverseImageModule J K F O₂ M)).symm
    (d.postcomp (inverseImageModuleUnit J K F O₂ M).val)

/-- The inverse image of a relative derivation, read along the inverse-image unit, is the
original derivation followed by the unit of the module adjunction. -/
theorem pushforwardInverseImageDerivation_inverseImageDerivation (d : SheafDerivation O₁ O₂ φ M) :
    pushforwardInverseImageDerivation J K F φ (inverseImageModule J K F O₂ M)
        (inverseImageDerivation J K F φ M d)
      = d.postcomp (inverseImageModuleUnit J K F O₂ M).val :=
  Equiv.apply_symm_apply (directImageDerivationEquiv J K F φ (inverseImageModule J K F O₂ M)) _

/-- The inverse image of a relative derivation sends an inverse-image section to the
inverse-image section of its value. -/
theorem inverseImageDerivation_d (d : SheafDerivation O₁ O₂ φ M) (U : Cᵒᵖ)
    (b : O₂.obj.obj U) :
    (inverseImageDerivation J K F φ M d).d
        (((inverseImageRingHom J K F O₂).hom.app U).hom b)
      = ((inverseImageModuleUnit J K F O₂ M).val.app U).hom (d.d b) :=
  PresheafOfModules.Derivation.congr_d
    (pushforwardInverseImageDerivation_inverseImageDerivation J K F φ M d) b

/-- The hom-equivalence out of the inverse image of the differentials is postcomposition with
the inverse image of the universal derivation. -/
theorem inverseImageDifferentialsHomEquiv_apply
    (G : SheafOfModules.{u} (underlyingRingSheaf (inverseImageRing J K F O₂)))
    (h : inverseImageModule J K F O₂ (moduleOfDifferentials O₁ O₂ φ) ⟶ G) :
    inverseImageDifferentialsHomEquiv J K F φ G h =
      (inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
        (universalDerivation O₁ O₂ φ)).postcomp h.val := by
  have h1 : inverseImageDifferentialsHomEquiv J K F φ G h
      = (directImageDerivationEquiv J K F φ G).symm
        ((universalDerivation O₁ O₂ φ).postcomp
          (((inverseImageAdjunction J K F O₂).homEquiv (moduleOfDifferentials O₁ O₂ φ) G) h).val)
        := by
    show (directImageDerivationEquiv J K F φ G).symm
      ((differentialsHomEquiv φ _)
        (((inverseImageAdjunction J K F O₂).homEquiv (moduleOfDifferentials O₁ O₂ φ) G) h)) = _
    rw [differentialsHomEquiv_apply]
  rw [h1]
  refine (directImageDerivationEquiv J K F φ G).injective ?_
  rw [Equiv.apply_symm_apply, directImageDerivationEquiv_apply,
    pushforwardInverseImageDerivation_postcomp J K F φ
      (inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
        (universalDerivation O₁ O₂ φ)) h,
    pushforwardInverseImageDerivation_inverseImageDerivation]
  have h2 : ((universalDerivation O₁ O₂ φ).postcomp
        (inverseImageModuleUnit J K F O₂ (moduleOfDifferentials O₁ O₂ φ)).val).postcomp
        ((SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).map h).val
      = (universalDerivation O₁ O₂ φ).postcomp
        ((inverseImageModuleUnit J K F O₂ (moduleOfDifferentials O₁ O₂ φ) ≫
          (SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).map h).val) := rfl
  rw [h2]
  exact congrArg (fun m : moduleOfDifferentials O₁ O₂ φ ⟶
      (SheafOfModules.pushforward.{u} (inverseImageRingHom J K F O₂)).obj G ↦
    (universalDerivation O₁ O₂ φ).postcomp m.val)
    (Adjunction.homEquiv_unit (inverseImageAdjunction J K F O₂) _ _ h)

/-- The canonical morphism from the inverse image of the differentials, determined by carrying
the inverse image of the universal derivation to the universal derivation. -/
noncomputable def pullbackDifferentialsHom :
    inverseImageModule J K F O₂ (moduleOfDifferentials O₁ O₂ φ) ⟶
      moduleOfDifferentials (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) :=
  (inverseImageDifferentialsHomEquiv J K F φ _).symm
    (universalDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
      ((F.sheafPullback CommRingCat.{u} J K).map φ))

/-- The canonical morphism carries the inverse image of the universal derivation to the
universal derivation. -/
theorem pullbackDifferentialsHom_spec :
    (inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
          (universalDerivation O₁ O₂ φ)).postcomp (pullbackDifferentialsHom J K F φ).val =
      universalDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) := by
  rw [← inverseImageDifferentialsHomEquiv_apply]
  exact Equiv.apply_symm_apply _ _

/-- The canonical morphism to the inverse image of the differentials, determined by carrying the
universal derivation to the inverse image of the universal derivation. -/
noncomputable def pullbackDifferentialsInv :
    moduleOfDifferentials (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) ⟶
      inverseImageModule J K F O₂ (moduleOfDifferentials O₁ O₂ φ) :=
  (differentialsHomEquiv ((F.sheafPullback CommRingCat.{u} J K).map φ) _).symm
    (inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
      (universalDerivation O₁ O₂ φ))

/-- The canonical morphism in the other direction carries the universal derivation to the
inverse image of the universal derivation. -/
theorem pullbackDifferentialsInv_spec :
    (universalDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
          ((F.sheafPullback CommRingCat.{u} J K).map φ)).postcomp
        (pullbackDifferentialsInv J K F φ).val =
      inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
        (universalDerivation O₁ O₂ φ) := by
  rw [← differentialsHomEquiv_apply]
  exact Equiv.apply_symm_apply _ _

/-- **Stacks Project, Tag 08TQ.** For a morphism of topoi presented by a continuous functor of
the underlying sites, the inverse image of the sheaf of relative differentials is canonically
the sheaf of relative differentials of the inverse-image morphism of sheaves of rings. -/
@[stacks 08TQ "the canonical identification, with the morphism of topoi presented by a
continuous functor of the underlying sites, both sites small in the single universe of the
sections of the sheaves of rings and of the modules, and the inverse image of sheaves of
commutative rings assumed to exist"]
noncomputable def pullbackDifferentialsIso :
    inverseImageModule J K F O₂ (moduleOfDifferentials O₁ O₂ φ) ≅
      moduleOfDifferentials (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) where
  hom := pullbackDifferentialsHom J K F φ
  inv := pullbackDifferentialsInv J K F φ
  hom_inv_id := by
    refine (inverseImageDifferentialsHomEquiv J K F φ _).injective ?_
    rw [inverseImageDifferentialsHomEquiv_apply, inverseImageDifferentialsHomEquiv_apply]
    have h1 : (inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
          (universalDerivation O₁ O₂ φ)).postcomp
          (pullbackDifferentialsHom J K F φ ≫ pullbackDifferentialsInv J K F φ).val
        = ((inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
            (universalDerivation O₁ O₂ φ)).postcomp
            (pullbackDifferentialsHom J K F φ).val).postcomp
          (pullbackDifferentialsInv J K F φ).val := rfl
    rw [h1, pullbackDifferentialsHom_spec, pullbackDifferentialsInv_spec]
    rfl
  inv_hom_id := by
    refine (differentialsHomEquiv ((F.sheafPullback CommRingCat.{u} J K).map φ) _).injective ?_
    rw [differentialsHomEquiv_apply, differentialsHomEquiv_apply]
    have h1 : (universalDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
          ((F.sheafPullback CommRingCat.{u} J K).map φ)).postcomp
          (pullbackDifferentialsInv J K F φ ≫ pullbackDifferentialsHom J K F φ).val
        = ((universalDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
            ((F.sheafPullback CommRingCat.{u} J K).map φ)).postcomp
            (pullbackDifferentialsInv J K F φ).val).postcomp
          (pullbackDifferentialsHom J K F φ).val := rfl
    rw [h1, pullbackDifferentialsInv_spec, pullbackDifferentialsHom_spec]
    rfl

/-- **Stacks Project, Tag 08TQ.** The canonical identification carries the inverse image of the
universal derivation to the universal derivation. -/
@[stacks 08TQ "compatibility with universal derivations"]
theorem pullbackDifferentialsIso_compatible :
    (inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
          (universalDerivation O₁ O₂ φ)).postcomp
        (pullbackDifferentialsIso J K F φ).hom.val =
      universalDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ) :=
  pullbackDifferentialsHom_spec J K F φ

/-- **Stacks Project, Tag 08TQ.** Compatibility with universal derivations characterises the
canonical identification. -/
@[stacks 08TQ "canonicity"]
theorem pullbackDifferentialsIso_unique
    (e : inverseImageModule J K F O₂ (moduleOfDifferentials O₁ O₂ φ) ≅
      moduleOfDifferentials (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ))
    (he : (inverseImageDerivation J K F φ (moduleOfDifferentials O₁ O₂ φ)
        (universalDerivation O₁ O₂ φ)).postcomp e.hom.val =
      universalDerivation (inverseImageRing J K F O₁) (inverseImageRing J K F O₂)
        ((F.sheafPullback CommRingCat.{u} J K).map φ)) :
    e = pullbackDifferentialsIso J K F φ := by
  refine Iso.ext ((inverseImageDifferentialsHomEquiv J K F φ _).injective ?_)
  rw [inverseImageDifferentialsHomEquiv_apply, inverseImageDifferentialsHomEquiv_apply, he,
    pullbackDifferentialsIso_compatible]

end Comparison

end InverseImage

end Stacks.Sheaves.Differentials

end
