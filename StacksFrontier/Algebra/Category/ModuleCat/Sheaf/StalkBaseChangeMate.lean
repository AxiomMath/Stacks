module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare

/-!
# The base-change interchange on stalks is the mate of the restriction-of-scalars square

Let `(C, J)` be a site, `Φ` a point of it and `θ : A₁ ⟶ A₂` a morphism of presheaves of
commutative rings whose underlying presheaves of rings are sheaves.  There are two adjunctions
in play:

* `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` (Stacks 03CZ), extension
  of scalars along `θ` left adjoint to restriction of scalars, between sheaves of modules; and
* `ModuleCat.extendRestrictScalarsAdj`, the same for modules over the stalk of `θ`.

Taking stalks at `Φ` relates them in two ways.  On the left adjoints it gives
`Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso`, the interchange
`(A₂ ⊗_{A₁} F)_Φ ≅ A₂,Φ ⊗_{A₁,Φ} F_Φ`.  On the right adjoints it gives
`Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso`, which is the identity on
carriers: restriction of scalars does not change the underlying sheaf of abelian groups.

The two are mates of each other
(`Stacks.Sheaves.StalkPullback.mateEquiv_symm_restrictScalarsSheafStalkNatIso`). Consequently the
stalk of the counit of Stacks 03CZ is the multiplication map `A₂,Φ ⊗_{A₁,Φ} M_Φ → M_Φ`, read
through the interchange (`Stacks.Sheaves.StalkPullback.sheafStalk_map_counit_eq`).

## Main definitions

* `Stacks.Sheaves.StalkPullback.restrictScalarsStalkHom` and
  `restrictScalarsStalkNatIso`: the stalk of a restriction of scalars of *presheaves* of modules
  is the restriction of scalars of the stalk, naturally in the presheaf.
* `Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso`: the same for sheaves of
  modules — the square of right adjoints whose mate is the interchange.

## Main results

* `Stacks.Sheaves.StalkPullback.unit_square`: **the unit square.**  The interchange, read
  backwards, carries `1 ⊗ m` to the stalk of the unit of Stacks 03CZ applied to `m`.
* `Stacks.Sheaves.StalkPullback.mateEquiv_symm_restrictScalarsSheafStalkNatIso`: **the
  interchange is the mate of the restriction-of-scalars square.**
* `Stacks.Sheaves.StalkPullback.map_restrictScalarsSheafStalk_comp_counit` and
  `sheafStalk_map_counit_eq`: **the stalk of the counit of Stacks 03CZ.**  Read through the
  interchange and the restriction-of-scalars square it is the counit of
  `ModuleCat.extendRestrictScalarsAdj`, which is the multiplication map
  `a ⊗ m ↦ a • m` (`ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul`).

## Implementation notes

The mate is identified through `CategoryTheory.mateEquiv_symm_eq_of_unit`, from the unit square:
the unit of `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` is described on
sections (`Stacks.Sheaves.RingedToposModules.forget_map_extendRestrictScalarsAdjunction_unit_app`),
while its counit is characterised only by the universal property of sheafification.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open scoped TensorProduct ChangeOfRings

universe w v u

noncomputable section

namespace Stacks.Sheaves.StalkPullback

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-! ### The stalk of a restriction of scalars -/

omit [LocallySmall.{w} C] in
/-- The stalk of `θ` carries the germ of a section `r` of `A₁` to the germ of `θ(r)`. -/
theorem stalkRingHom_ringGerm (U : C) (x : Φ.fiber.obj U) (r : A₁.obj (op U)) :
    SitePointBaseChange.stalkRingHom θ Φ (Stacks.ringGerm Φ A₁ U x r) =
      Stacks.ringGerm Φ A₂ U x ((θ.app (op U)).hom r) :=
  Φ.toPresheafFiber_naturality_apply θ U x r

/-- Restriction of scalars does not change germs: a section of a presheaf of `A₂`-modules has
the same germ read over `A₁` as over `A₂`. -/
theorem germ_restrictScalars (M : PresheafOfModules.{w} (ringPresheaf A₂)) (U : C)
    (x : Φ.fiber.obj U) (s : M.obj (op U)) :
    Stacks.germ Φ A₁ ((restrictScalars θ).obj M) U x s = Stacks.germ Φ A₂ M U x s :=
  rfl

/-- **The two scalar actions on the stalk correspond.**  The germ of `r • s` computed in the
restriction of scalars along `θ` is the stalk of `θ` applied to the germ of `r`, acting on the
germ of `s`. -/
theorem germ_restrictScalars_smul (M : PresheafOfModules.{w} (ringPresheaf A₂)) (U : C)
    (x : Φ.fiber.obj U) (r : A₁.obj (op U)) (s : ((restrictScalars θ).obj M).obj (op U)) :
    Stacks.germ Φ A₁ ((restrictScalars θ).obj M) U x (r • s) =
      SitePointBaseChange.stalkRingHom θ Φ (Stacks.ringGerm Φ A₁ U x r) •
        Stacks.germ Φ A₂ M U x s := by
  refine Eq.trans ?_ (congrArg (fun t : Stacks.ringFiber Φ A₂ => t • Stacks.germ Φ A₂ M U x s)
    (stalkRingHom_ringGerm Φ θ U x r).symm)
  exact Stacks.germ_smul U x ((θ.app (op U)).hom r) s

/-- **The comparison map from the stalk of a restriction of scalars to the restriction of
scalars of the stalk.**  It is the identity on carriers. -/
def restrictScalarsStalkHom (M : PresheafOfModules.{w} (ringPresheaf A₂)) :
    (Stacks.presheafModuleFiberOfCommRing Φ A₁).obj ((restrictScalars θ).obj M) ⟶
      (ModuleCat.restrictScalars.{w} (SitePointBaseChange.stalkRingHom θ Φ)).obj
        ((Stacks.presheafModuleFiberOfCommRing Φ A₂).obj M) :=
  ConcreteCategory.ofHom (C := ModuleCat.{w} (Stacks.ringFiber Φ A₁))
    { toFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        obtain ⟨U, x, s, hs⟩ := Stacks.germ_jointly_surjective (O := A₁)
          (M := (restrictScalars θ).obj M) m
        obtain ⟨V, y, ρ, hρ⟩ := Stacks.ringGerm_jointly_surjective (O := A₁) r
        obtain ⟨W, z, a, b, ha, hb⟩ := Stacks.exists_common_nbhd (Φ := Φ) x y
        have hs' : Stacks.germ Φ A₁ ((restrictScalars θ).obj M) W z
            (((restrictScalars θ).obj M).restrictₛₗ a.op s) = m := by
          rw [← Stacks.germ_w a z s, ha, hs]
        have hρ' : Stacks.ringGerm Φ A₁ W z (A₁.map b.op ρ) = r := by
          rw [← Stacks.ringGerm_w b z ρ, hb, hρ]
        rw [← hs', ← hρ', ← Stacks.germ_smul W z]
        exact germ_restrictScalars_smul Φ θ M W z (A₁.map b.op ρ) _ }

/-- On underlying abelian groups the comparison map is the identity. -/
theorem forget₂_map_restrictScalarsStalkHom (M : PresheafOfModules.{w} (ringPresheaf A₂)) :
    (forget₂ (ModuleCat.{w} (Stacks.ringFiber Φ A₁)) AddCommGrpCat.{w}).map
        (restrictScalarsStalkHom Φ θ M) = 𝟙 _ := by
  ext m
  rfl

/-- The comparison map is an isomorphism. -/
instance isIso_restrictScalarsStalkHom (M : PresheafOfModules.{w} (ringPresheaf A₂)) :
    IsIso (restrictScalarsStalkHom Φ θ M) := by
  rw [← isIso_iff_of_reflects_iso _
      (forget₂ (ModuleCat.{w} (Stacks.ringFiber Φ A₁)) AddCommGrpCat.{w}),
    forget₂_map_restrictScalarsStalkHom]
  exact IsIso.id _

/-- The comparison map is natural in the presheaf of modules. -/
theorem restrictScalarsStalkHom_naturality
    {M N : PresheafOfModules.{w} (ringPresheaf A₂)} (f : M ⟶ N) :
    (Stacks.presheafModuleFiberOfCommRing Φ A₁).map ((restrictScalars θ).map f) ≫
        restrictScalarsStalkHom Φ θ N =
      restrictScalarsStalkHom Φ θ M ≫
        (ModuleCat.restrictScalars.{w} (SitePointBaseChange.stalkRingHom θ Φ)).map
          ((Stacks.presheafModuleFiberOfCommRing Φ A₂).map f) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  obtain ⟨U, x, s, rfl⟩ := Stacks.germ_jointly_surjective (O := A₁)
    (M := (restrictScalars θ).obj M) m
  exact (Stacks.germ_naturality Φ A₁ ((restrictScalars θ).obj M)
      ((restrictScalars θ).map f) U x s).trans
    (Stacks.germ_naturality Φ A₂ M f U x s).symm

/-- **The stalk of a restriction of scalars of presheaves of modules is the restriction of
scalars of the stalk**, at a point of a site, naturally in the presheaf. -/
def restrictScalarsStalkNatIso :
    restrictScalars θ ⋙ Stacks.presheafModuleFiberOfCommRing Φ A₁ ≅
      Stacks.presheafModuleFiberOfCommRing Φ A₂ ⋙
        ModuleCat.restrictScalars.{w} (SitePointBaseChange.stalkRingHom θ Φ) :=
  NatIso.ofComponents (fun M => asIso (restrictScalarsStalkHom Φ θ M))
    fun f => restrictScalarsStalkHom_naturality Φ θ f

/-! ### The interchange as a mate -/

section Mate

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The stalk of a restriction of scalars of sheaves of modules is the restriction of scalars
of the stalk**, at a point of a site: the square of right adjoints whose mate is the
interchange `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso`. -/
def restrictScalarsSheafStalkNatIso :
    SheafOfModules.restrictScalars.{w} (commRingSheafMap J θ h₁ h₂) ⋙ sheafStalk Φ A₁ h₁ ≅
      sheafStalk Φ A₂ h₂ ⋙
        ModuleCat.restrictScalars.{w} (SitePointBaseChange.stalkRingHom θ Φ) :=
  NatIso.ofComponents (fun M => @asIso _ _ _ _ (restrictScalarsStalkHom Φ θ M.val)
      (isIso_restrictScalarsStalkHom Φ θ M.val))
    fun f => restrictScalarsStalkHom_naturality Φ θ f.val

/-- The interchange, read backwards, is the stalkwise comparison for the sectionwise tensor
product followed by the stalk of the sheafification unit. -/
theorem extendScalarsSheafStalkNatIso_inv_app
    (N : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalarsSheafStalkNatIso Φ θ h₁ h₂).inv.app N =
      (SitePointBaseChange.extendScalarsStalkObjIso θ N.val Φ).hom ≫
        (Stacks.presheafModuleFiberOfCommRing Φ A₂).map
          ((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
            ((changeOfRings θ).obj N.val)) :=
  rfl

/-- The interchange, read backwards, carries `1 ⊗ m` to the image of `m` under the canonical map
`N_Φ → (A₂ ⊗_{A₁} N)_Φ` followed by the stalk of the sheafification unit. -/
theorem extendScalarsSheafStalkNatIso_inv_app_one_tmul
    (N : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (m : Stacks.moduleFiber Φ A₁ N.val) :
    (extendScalarsSheafStalkNatIso Φ θ h₁ h₂).inv.app N
        ((1 : Stacks.ringFiber Φ A₂) ⊗ₜ[Stacks.ringFiber Φ A₁,
            SitePointBaseChange.stalkRingHom θ Φ] m) =
      (Stacks.presheafModuleFiberOfCommRing Φ A₂).map
        ((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj N.val))
        (SitePointBaseChange.toStalkAdd θ N.val Φ m) :=
  congrArg (fun t => (Stacks.presheafModuleFiberOfCommRing Φ A₂).map
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj N.val)) t)
    (SitePointBaseChange.extendScalarsStalkObjIso_hom_one_tmul θ N.val Φ m)

omit [LocallySmall.{w} C] in
/-- **The unit of Stacks 03CZ on sections**: a section `s` of `N` over `U` goes to the image of
`1 ⊗ s` under the sheafification unit. -/
theorem forget_map_unit_app_apply (N : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (U : C)
    (s : N.val.obj (op U)) :
    ((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map
        ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app N)).app (op U) s =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
        ((changeOfRings θ).obj N.val)).app (op U)
        (SitePointBaseChange.cofTmul θ N.val U 1 s) := by
  rw [forget_map_extendRestrictScalarsAdjunction_unit_app]
  rfl

/-- The stalk of the unit of Stacks 03CZ carries the germ of a section `s` to the germ of the
image of `1 ⊗ s` under the sheafification unit. -/
theorem sheafStalk_map_unit_app_germ (N : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (U : C)
    (x : Φ.fiber.obj U) (s : N.val.obj (op U)) :
    (sheafStalk Φ A₁ h₁).map ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app N)
        (Stacks.germ Φ A₁ N.val U x s) =
      Stacks.germ Φ A₂ ((extendScalars J θ h₁ h₂).obj N).val U x
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app
          ((changeOfRings θ).obj N.val)).app (op U)
          (SitePointBaseChange.cofTmul θ N.val U 1 s)) :=
  (Stacks.germ_naturality Φ A₁ N.val
      ((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map
        ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app N)) U x s).trans
    (congrArg (Stacks.germ Φ A₂ ((extendScalars J θ h₁ h₂).obj N).val U x)
      (forget_map_unit_app_apply θ h₁ h₂ N U s))

/-- **The unit square, on an element of the stalk.**  The interchange, read backwards, carries
`1 ⊗ m` to the stalk of the unit of Stacks 03CZ applied to `m`. -/
theorem unit_square_app (N : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    (m : Stacks.moduleFiber Φ A₁ N.val) :
    (extendScalarsSheafStalkNatIso Φ θ h₁ h₂).inv.app N
        ((1 : Stacks.ringFiber Φ A₂) ⊗ₜ[Stacks.ringFiber Φ A₁,
            SitePointBaseChange.stalkRingHom θ Φ] m) =
      restrictScalarsStalkHom Φ θ ((extendScalars J θ h₁ h₂).obj N).val
        ((sheafStalk Φ A₁ h₁).map
          ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app N) m) := by
  obtain ⟨U, x, s, rfl⟩ := Stacks.germ_jointly_surjective (O := A₁) (M := N.val) m
  rw [extendScalarsSheafStalkNatIso_inv_app_one_tmul, SitePointBaseChange.toStalkAdd_germ,
    Stacks.germ_naturality Φ A₂ (SitePointBaseChange.cof θ N.val) _ U x _,
    sheafStalk_map_unit_app_germ]
  rfl

/-- **The unit square.**  The unit of `ModuleCat.extendRestrictScalarsAdj` followed by the
interchange read backwards is the stalk of the unit of Stacks 03CZ followed by the
restriction-of-scalars square. -/
theorem unit_square (N : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (ModuleCat.extendRestrictScalarsAdj (SitePointBaseChange.stalkRingHom θ Φ)).unit.app
          ((sheafStalk Φ A₁ h₁).obj N) ≫
        (ModuleCat.restrictScalars.{w} (SitePointBaseChange.stalkRingHom θ Φ)).map
          ((extendScalarsSheafStalkNatIso Φ θ h₁ h₂).inv.app N) =
      (sheafStalk Φ A₁ h₁).map ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app N) ≫
        (restrictScalarsSheafStalkNatIso Φ θ h₁ h₂).hom.app
          ((extendScalars J θ h₁ h₂).obj N) :=
  ModuleCat.hom_ext (LinearMap.ext fun m => unit_square_app Φ θ h₁ h₂ N m)

/-- **The base-change interchange on stalks is the mate of the restriction-of-scalars square.**
The inverse mate, under the adjunctions of Stacks 03CZ for sheaves of modules and for modules
over the stalk, of
`Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso` is
`Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso` read backwards. -/
theorem mateEquiv_symm_restrictScalarsSheafStalkNatIso :
    (mateEquiv (extendRestrictScalarsAdjunction J θ h₁ h₂)
          (ModuleCat.extendRestrictScalarsAdj
            (SitePointBaseChange.stalkRingHom θ Φ))).symm
        (restrictScalarsSheafStalkNatIso Φ θ h₁ h₂).hom =
      (extendScalarsSheafStalkNatIso Φ θ h₁ h₂).inv :=
  mateEquiv_symm_eq_of_unit _ _ _ _ (unit_square Φ θ h₁ h₂)

/-- **The counit square.**  The restriction-of-scalars square, extended along the stalk of `θ`
and followed by the multiplication map, is the interchange read backwards followed by the stalk
of the counit of Stacks 03CZ. -/
theorem map_restrictScalarsSheafStalk_comp_counit
    (M : SheafOfModules.{w} (commRingSheaf J A₂ h₂)) :
    (ModuleCat.extendScalars (SitePointBaseChange.stalkRingHom θ Φ)).map
          ((restrictScalarsSheafStalkNatIso Φ θ h₁ h₂).hom.app M) ≫
        (ModuleCat.extendRestrictScalarsAdj
            (SitePointBaseChange.stalkRingHom θ Φ)).counit.app
          ((sheafStalk Φ A₂ h₂).obj M) =
      (extendScalarsSheafStalkNatIso Φ θ h₁ h₂).inv.app
          ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj M) ≫
        (sheafStalk Φ A₂ h₂).map
          ((extendRestrictScalarsAdjunction J θ h₁ h₂).counit.app M) :=
  map_counit_comp_of_unit _ _ _ _ (unit_square Φ θ h₁ h₂) M

/-- **The stalk of the counit of Stacks 03CZ is the multiplication map.**  Read through the
interchange `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso` and the
restriction-of-scalars square, the stalk at `Φ` of the counit
`A₂ ⊗_{A₁} M_{A₁} ⟶ M` is the counit of `ModuleCat.extendRestrictScalarsAdj`, which sends
`a ⊗ m` to `a • m` (`ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul`). -/
theorem sheafStalk_map_counit_eq (M : SheafOfModules.{w} (commRingSheaf J A₂ h₂)) :
    (sheafStalk Φ A₂ h₂).map
        ((extendRestrictScalarsAdjunction J θ h₁ h₂).counit.app M) =
      ((extendScalarsSheafStalkNatIso Φ θ h₁ h₂).hom.app
            ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj M) ≫
          (ModuleCat.extendScalars (SitePointBaseChange.stalkRingHom θ Φ)).map
            ((restrictScalarsSheafStalkNatIso Φ θ h₁ h₂).hom.app M)) ≫
        (ModuleCat.extendRestrictScalarsAdj
            (SitePointBaseChange.stalkRingHom θ Φ)).counit.app
          ((sheafStalk Φ A₂ h₂).obj M) := by
  rw [Category.assoc, map_restrictScalarsSheafStalk_comp_counit, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp]

end Mate

end Stacks.Sheaves.StalkPullback

end

end
