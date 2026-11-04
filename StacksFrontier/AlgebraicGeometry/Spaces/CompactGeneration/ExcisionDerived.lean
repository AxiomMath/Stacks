module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.CategoryTheory.Triangulated.ExcisionGluing

/-!
# Derived excision for an elementary distinguished square

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces with
intersection `P = U ×_W V`, and let `K` be an object of `D(𝒪_V)` restricting to zero on `P`.
Then:

* `Rj_* K` restricts to zero on `U`, by étale base change ([Stacks, Tag 08GE]);
* the counit `(Rj_* K)|_V ⟶ K` is an isomorphism ([Stacks, Tag 08GG], clause (2)(b), derived
  from the excision isomorphism for `j_!`);
* the extension by zero `j_! K` is isomorphic to `Rj_* K`: both restrict to zero on `U` and to
  `K` on `V`, and vanishing is local for the square.

## Main results

* `AlgebraicGeometry.Space.isZero_restrictOpen_derivedPushforwardEtale`
* `AlgebraicGeometry.Space.isIso_etaleDerivedModuleAdjunction_counit_edsEtale`
* `AlgebraicGeometry.Space.isZero_restrictOpen_derivedShriekEtale`
* `AlgebraicGeometry.Space.isIso_derivedShriekToPushforwardEtale`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- Restriction to the intersection, on the derived category of the étale space. -/
abbrev edsDerivedRestrictSnd :
    DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2) :=
  (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
    (isEtale_edsSnd B S hS hsq)).mapDerivedCategory

/-- Extension by zero along the étale morphism, on derived categories. -/
abbrev edsDerivedShriekEtale :
    DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2) :=
  (etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory

/-- **`Rj_*K` restricts to zero on `U` when `K` restricts to zero on `P`**: by étale base change
along `U ⟶ W`, `(Rj_* K)|_U` is the direct image of `K|_P`. -/
theorem isZero_restrictOpen_derivedPushforwardEtale
    (K : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hK : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj K)) :
    IsZero ((edsDerivedRestrictOpen B S hS hsq).obj
      ((derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).obj K)) :=
  have := (smallEtaleDerivedModuleAdjunction B S hS (edsFst B S hS hsq)).isRightAdjoint
  ((derivedModulePushforward B S hS (edsFst B S hS hsq)).map_isZero hK).of_iso
    ((derivedPushforwardEtaleBaseChangeIso B S hS (isPullback_edsInter B S hS hsq).flip
      (isEtale_edsOpenHom B S hS hsq)).app K)

/-- Restricting to the étale space and then to the intersection is restricting to the open
subspace and then to the intersection, on derived categories. -/
def edsDerivedRestrictInterIso :
    edsDerivedRestrictEtale B S hS hsq ⋙ edsDerivedRestrictSnd B S hS hsq ≅
      edsDerivedRestrictOpen B S hS hsq ⋙
        (etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq)
          (isEtale_edsFst B S hS hsq)).mapDerivedCategory :=
  Dualizing.mapDerivedCategoryCompNatIso _ _ _ (edsFactorIsoEtale B S hS hsq) ≪≫
    (Dualizing.mapDerivedCategoryCompNatIso _ _ _ (edsFactorIsoOpen B S hS hsq)).symm

/-- **Derived excision for the direct image**, clause (2)(b) of [Stacks, Tag 08GG]: for `K` in
`D(𝒪_V)` restricting to zero on `P`, the counit `(Rj_* K)|_V ⟶ K` is an isomorphism. -/
theorem isIso_etaleDerivedModuleAdjunction_counit_edsEtale
    (K : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hK : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj K)) :
    IsIso ((etaleDerivedModuleAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).counit.app K) := by
  refine isIso_counit_of_isIso_unit
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
    (etaleDerivedModuleAdjunction B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
    (fun N => IsZero ((edsDerivedRestrictSnd B S hS hsq).obj N))
    (fun M hM => isIso_derivedUnit_edsEtale_of_isZero_restrict B S hS hsq M
      ((forall_isZero_restrict_homology_iff B S hS hsq M).2 hM))
    (fun N hN => ?_) K hK
  exact (Functor.map_isZero _
    (isZero_restrictOpen_derivedPushforwardEtale B S hS hsq N hN)).of_iso
    ((edsDerivedRestrictInterIso B S hS hsq).app _)

/-- **The extension by zero of `K` restricts to zero on `U` when `K` restricts to zero on `P`**,
on derived categories: by base change of extension by zero ([Stacks, Tag 08HA]) on each
cohomology sheaf. -/
theorem isZero_restrictOpen_derivedShriekEtale
    (K : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hK : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj K)) :
    IsZero ((edsDerivedRestrictOpen B S hS hsq).obj
      ((edsDerivedShriekEtale B S hS hsq).obj K)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  exact (isZero_restrict_edsOpen_edsEtale_shriek B S hS hsq _
    ((forall_isZero_restrict_homology_iff B S hS hsq K).2 hK n)).of_iso <|
    ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategoryHomologyIso n).app _ ≪≫
    (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapIso
      (((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryHomologyIso n).app K)

/-- The comparison `j_! K ⟶ Rj_* K` for `K` restricting to zero on `P`: the transpose, under
`j_! ⊣ (-)|_V`, of the inverse of the invertible counit `(Rj_* K)|_V ⟶ K`. -/
def derivedShriekToPushforwardEtale
    (K : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hK : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj K)) :
    (edsDerivedShriekEtale B S hS hsq).obj K ⟶
      (derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).obj K :=
  haveI := isIso_etaleDerivedModuleAdjunction_counit_edsEtale B S hS hsq K hK
  (((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.homEquiv _ _).symm
      (inv ((etaleDerivedModuleAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).counit.app K)))

/-- **Extension by zero agrees with the direct image away from `P`**: for `K` in `D(𝒪_V)`
restricting to zero on `P`, the comparison `j_! K ⟶ Rj_* K` is an isomorphism. Both sides
restrict to zero on `U`, the comparison restricts to an isomorphism on `V`, and vanishing is
local for the square. -/
theorem isIso_derivedShriekToPushforwardEtale
    (K : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hK : IsZero ((edsDerivedRestrictSnd B S hS hsq).obj K)) :
    IsIso (derivedShriekToPushforwardEtale B S hS hsq K hK) := by
  let adjS := (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
  let φ := derivedShriekToPushforwardEtale B S hS hsq K hK
  have := isIso_etaleDerivedModuleAdjunction_counit_edsEtale B S hS hsq K hK
  have : IsIso (adjS.unit.app K) := isIso_derivedUnit_edsEtale_of_isZero_restrict B S hS hsq K
    ((forall_isZero_restrict_homology_iff B S hS hsq K).2 hK)
  have hφV : IsIso ((edsDerivedRestrictEtale B S hS hsq).map φ) := by
    have h : adjS.unit.app K ≫ (edsDerivedRestrictEtale B S hS hsq).map φ =
        inv ((etaleDerivedModuleAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).counit.app K) :=
      (adjS.homEquiv_unit (f := φ)).symm.trans ((adjS.homEquiv _ _).apply_symm_apply _)
    have : IsIso (adjS.unit.app K ≫ (edsDerivedRestrictEtale B S hS hsq).map φ) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (adjS.unit.app K) _
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle φ
  have hZV : IsZero ((edsDerivedRestrictEtale B S hS hsq).obj Z) :=
    Triangle.isZero₃_of_isIso₁ _ ((edsDerivedRestrictEtale B S hS hsq).map_distinguished _ hT) hφV
  have hZU : IsZero ((edsDerivedRestrictOpen B S hS hsq).obj Z) := by
    have h1 := isZero_restrictOpen_derivedShriekEtale B S hS hsq K hK
    have h2 := isZero_restrictOpen_derivedPushforwardEtale B S hS hsq K hK
    exact Triangle.isZero₃_of_isIso₁ _
      ((edsDerivedRestrictOpen B S hS hsq).map_distinguished _ hT)
      ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_derivedRestrict_eds B S hS hsq Z hZU hZV)

end AlgebraicGeometry.Space

end
