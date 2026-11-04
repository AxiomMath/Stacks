module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocalSliceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedExtensionByZero

/-!
# The derived direct image of a supported perfect object is perfect

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S` and set `T = |X| \ |U|`.  This file proves, unconditionally:

* Stacks 08GG, clause (2)(b): for `F` in `D(𝒪_V)` supported on `j⁻¹T` the counit
  `(Rj_*F)|_V ⟶ F` is an isomorphism;
* **Stacks 08HK**: for `E` a perfect object of `D(𝒪_V)` supported on `j⁻¹T`, `Rj_*E` is a perfect
  object of `D(𝒪_X)`.

As in `AlgebraicGeometry.Space.isPerfect_derivedPushforward_of_cohomologySupportedOn`, the derived
direct image enters as a right adjoint `Rj_*` of derived restriction together with its
adjunction, which determines it up to a unique compatible isomorphism.

## The argument

The source obtains clause (2)(b) by base changing the square to `V`, where `j` acquires a
section.  The argument here uses only adjunctions and the two clauses of Stacks 08GG about
extension by zero, which are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SupportedExtensionByZero.lean`.

* `Rj_*F` vanishes on `U`.  Restriction to `U` is right adjoint to `j_{U!}`, and
  `(j_{U!}G)|_V = j_{U×V→V,!}(G|_{U×V})` by Stacks 08HA, so
  `Hom(G, (Rj_*F)|_U) = Hom(G|_{U×V}, F|_{U×V}) = 0` because `F` vanishes on `U ×_X V`.
  Hence `Rj_*F` is supported on `T` and its restriction to `V` on `j⁻¹T`.
* With `η` and `c` the unit and counit of `j_! ⊣ (-)|_V`, both invertible on supported objects,
  and `ψ : j_!F ⟶ Rj_*F` the adjunct of `η_F⁻¹`, the counit `ε_F` of `(-)|_V ⊣ Rj_*` satisfies
  `ψ|_V ≫ ε_F = η_F⁻¹` and `j_!ε_F ≫ ψ = c_{Rj_*F}`.  The first makes `ψ|_V` a split
  monomorphism, the second (restricted to `V`, where `c|_V` is `η⁻¹`) a split epimorphism; so
  `ψ|_V` is invertible, and with it `ε_F`.  This is
  `CategoryTheory.Adjunction.isIso_counit_of_isIso_unit_of_isIso_counit`.

Stacks 08HK then follows the source: perfectness is local on `X_étale`
(`AlgebraicGeometry.Space.isPerfect_of_isPerfect_eds`), `(Rj_*E)|_U = 0` is perfect and
`(Rj_*E)|_V ≅ E` is perfect.

## Main results

* `CategoryTheory.Adjunction.isIso_counit_of_isIso_unit_of_isIso_counit`: the abstract step.
* `AlgebraicGeometry.Space.isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn`:
  `(Rj_*F)|_U = 0`.
* `AlgebraicGeometry.Space.isIso_counit_edsEtale_rightAdjoint_of_cohomologySupportedOn`:
  Stacks 08GG, clause (2)(b).
* `AlgebraicGeometry.Space.isIso_unit_edsEtale_rightAdjoint_of_cohomologySupportedOn` and
  `AlgebraicGeometry.Space.isIso_supportedShriekToPushforward_of_cohomologySupportedOn`:
  Stacks 08GG, clauses (1)(a) and (2)(c).
* `AlgebraicGeometry.Space.isPerfect_edsEtale_shriek_of_cohomologySupportedOn`,
  `AlgebraicGeometry.Space.shiftedShriekHomEquiv` and
  `AlgebraicGeometry.Space.isZero_of_isZero_edsDerivedRestrict`: the extension by zero of a
  supported perfect object is perfect, morphisms out of its shifts, and the detection of zero
  objects on the two members of the square.
* `Space.isPerfect_rightAdjoint_edsDerivedRestrictEtale_of_cohomologySupportedOn`:
  **Stacks 08HK**.

## References

* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08HA](https://stacks.math.columbia.edu/tag/08HA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : D ⥤ C} {res : C ⥤ D} {R : D ⥤ C}

/-- **A counit invertibility from a left adjoint.**  Let `L ⊣ res ⊣ R`.  If, at an object `E` of
`D`, the unit `η_E : E ⟶ res(L E)` of `L ⊣ res` is invertible, and the counit `c` of `L ⊣ res` at
`R E` and the unit of `L ⊣ res` at `res(R E)` are invertible, then the counit
`res(R E) ⟶ E` of `res ⊣ R` is invertible. -/
theorem isIso_counit_of_isIso_unit_of_isIso_counit (adjL : L ⊣ res) (adjR : res ⊣ R) (E : D)
    [hη : IsIso (adjL.unit.app E)] [IsIso (adjL.counit.app (R.obj E))]
    [hη' : IsIso (adjL.unit.app (res.obj (R.obj E)))] :
    IsIso (adjR.counit.app E) := by
  let ψ : L.obj E ⟶ R.obj E := adjR.homEquiv _ _ (inv (adjL.unit.app E))
  have h1 : res.map ψ ≫ adjR.counit.app E = inv (adjL.unit.app E) := by
    have := (adjR.homEquiv _ _).symm_apply_apply (inv (adjL.unit.app E))
    rwa [Adjunction.homEquiv_counit] at this
  have hrc : res.map (adjL.counit.app (R.obj E)) = inv (adjL.unit.app (res.obj (R.obj E))) := by
    rw [← cancel_epi (adjL.unit.app (res.obj (R.obj E))), IsIso.hom_inv_id]
    exact adjL.right_triangle_components _
  have hnat : adjL.unit.app (res.obj (R.obj E)) ≫ res.map (L.map (adjR.counit.app E)) =
      adjR.counit.app E ≫ adjL.unit.app E := (adjL.unit.naturality (adjR.counit.app E)).symm
  have h2 : L.map (adjR.counit.app E) ≫ ψ = adjL.counit.app (R.obj E) := by
    apply (adjR.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc, h1, hrc, IsIso.eq_inv_comp, ← Category.assoc, hnat, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  -- `res ψ` has a left and a right inverse.
  have hmono : res.map ψ ≫ (adjR.counit.app E ≫ adjL.unit.app E) = 𝟙 _ := by
    rw [← Category.assoc, h1, IsIso.inv_hom_id]
  have hepi : (adjL.unit.app (res.obj (R.obj E)) ≫ res.map (L.map (adjR.counit.app E))) ≫
      res.map ψ = 𝟙 _ := by
    rw [Category.assoc, ← Functor.map_comp, h2, hrc, IsIso.hom_inv_id]
  have hlr : adjR.counit.app E ≫ adjL.unit.app E =
      adjL.unit.app (res.obj (R.obj E)) ≫ res.map (L.map (adjR.counit.app E)) := by
    calc adjR.counit.app E ≫ adjL.unit.app E
        = ((adjL.unit.app (res.obj (R.obj E)) ≫ res.map (L.map (adjR.counit.app E))) ≫
            res.map ψ) ≫ (adjR.counit.app E ≫ adjL.unit.app E) := by
          rw [hepi, Category.id_comp]
      _ = adjL.unit.app (res.obj (R.obj E)) ≫ res.map (L.map (adjR.counit.app E)) := by
          rw [Category.assoc, hmono]
          exact Category.comp_id _
  have hψ : IsIso (res.map ψ) :=
    ⟨⟨adjR.counit.app E ≫ adjL.unit.app E, hmono, by rw [hlr]; exact hepi⟩⟩
  have : adjR.counit.app E = inv (res.map ψ) ≫ inv (adjL.unit.app E) := by
    rw [← h1, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If the restriction of `M` along an étale morphism `f` vanishes, the support of each cohomology
sheaf of `M` misses the image of `f`. -/
private theorem preimage_supportOfSheaf_homology_eq_empty {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (M : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (n : ℤ) (hM : IsZero ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj M)) :
    pointsMap B S hS X.1 f.hom ⁻¹' supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj M)) = ∅ := by
  have hH : IsZero ((etaleModulePullback.{u, u} B S hS f hf).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj M)) :=
    IsZero.of_iso ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) n).map_isZero hM)
      (((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryHomologyIso n).app _).symm
  rw [← supportOfSheaf_toSheaf_etaleModulePullback B S hS f hf,
    supportOfSheaf_eq_empty_iff_isZero]
  exact hH

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- An object of `D(𝒪_X)` whose restriction to the open subspace `U` of an elementary
distinguished square vanishes is supported on `T = |X| \ |U|`: each cohomology sheaf restricts
to zero on `U`, and the support of a restriction is the inverse image of the support. -/
theorem cohomologySupportedOn_of_isZero_edsDerivedRestrictOpen
    (M : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hM : IsZero ((edsDerivedRestrictOpen B S hS hsq).obj M)) :
    CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) M := by
  intro n x hx hxU
  obtain ⟨p, rfl⟩ := hxU
  exact Set.eq_empty_iff_forall_notMem.1 (preimage_supportOfSheaf_homology_eq_empty B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) M n hM) p hx

/-- The restriction to `V` of an object of `D(𝒪_X)` supported on `T` is supported on `j⁻¹T`. -/
theorem cohomologySupportedOn_edsDerivedRestrictEtale
    (M : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hM : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) M) :
    CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq)
      ((edsDerivedRestrictEtale B S hS hsq).obj M) := by
  intro n
  have hj := isEtale_edsEtaleHom B S hS hsq
  have e : (DerivedCategory.homologyFunctor _ n).obj ((edsDerivedRestrictEtale B S hS hsq).obj M) ≅
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq) hj).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) n).obj M) :=
    ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq) hj).mapDerivedCategoryHomologyIso
      n).app M
  have hsupp := supportOfSheaf_toSheaf_etaleModulePullback B S hS (edsEtaleHom B S hS hsq) hj
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) n).obj M)
  intro x hx
  have hx' := (supportOfSheaf_eq_of_iso B S hS (edsEtale B S hS hsq) e).subset hx
  rw [hsupp] at hx'
  exact hM n hx'

/-- The counit of the derived `j_! ⊣ (-)|_V` is invertible on objects supported on `T`. -/
private theorem isIso_derivedCounit_edsEtale_app
    (Z : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hZ : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) Z) :
    IsIso ((Adjunction.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq)).counit.app Z) := by
  have hc := isIso_derivedCounit_edsEtale_of_cohomologySupportedOn B S hS hsq Z hZ
  rw [← Adjunction.mapDerivedCategory_counit_eq (edsEtaleShriekAdjunction B S hS hsq)]
  simp only [NatTrans.comp_app]
  infer_instance

variable {RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
  (adjPush : edsDerivedRestrictEtale B S hS hsq ⊣ RpushD)

include adjPush

/-- **`Rj_*F` vanishes on `U` for `F` supported on `j⁻¹T`.**  Restriction to `U` is right adjoint
to `j_{U!}`, `(j_{U!}G)|_V` is `j_{U×V→V,!}(G|_{U×V})` by Stacks 08HA, and `F|_{U×V} = 0`; so
every morphism into `(Rj_*F)|_U` is zero. -/
theorem isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsZero ((edsDerivedRestrictOpen B S hS hsq).obj (RpushD.obj F)) := by
  have sq := (isPullback_edsInter B S hS hsq).flip
  have hj := isEtale_edsOpenHom B S hS hsq
  have hjV := isEtale_edsEtaleHom B S hS hsq
  let hjW := isEtale_of_isPullback B S hS (edsFst B S hS hsq) (edsSnd B S hS hsq)
    (edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq) sq.flip hj
  let adjU := etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq) hj
  let adjW := etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq) hjW
  let adjUD := Adjunction.mapDerivedCategory adjU
  let adjWD := Adjunction.mapDerivedCategory adjW
  -- `F` vanishes on `U ×_X V`.
  have hFW : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      hjW).mapDerivedCategory.obj F) := by
    refine isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS
      (edsSnd B S hS hsq) hjW _ F hF ?_
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨q, rfl⟩ hq
    have h1 : pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom
        (pointsMap B S hS (edsInter B S hS hsq).1 (edsSnd B S hS hsq).hom q) ∈
          Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := by
      rw [← pointsMap_comp_apply]
      have : (edsSnd B S hS hsq).hom ≫ (edsEtaleHom B S hS hsq).hom =
          (edsInterHom B S hS hsq).hom :=
        congrArg (fun m => m.hom) (edsSnd_comp_edsEtaleHom B S hS hsq)
      rw [this]
      exact range_pointsMap_edsInterHom_subset B S hS hsq ⟨q, rfl⟩
    exact hq h1
  have hmap := isIso_derivedRestrictExtensionByZeroMap B S hS sq hj hjV adjU adjW
  have hsub : ∀ G, Subsingleton (G ⟶ (edsDerivedRestrictOpen B S hS hsq).obj (RpushD.obj F)) := by
    intro G
    let e3 := asIso ((derivedRestrictExtensionByZeroMap B S hS sq hj hjV adjU adjW).app G)
    have : Subsingleton ((etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq)
        (isEtale_of_isPullback B S hS (edsSnd B S hS hsq) (edsFst B S hS hsq)
          (edsEtaleHom B S hS hsq) (edsOpenHom B S hS hsq) sq hjV)).mapDerivedCategory.obj G ⟶
        (etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) hjW).mapDerivedCategory.obj F) :=
      ⟨fun a b => hFW.eq_of_tgt a b⟩
    exact ((adjUD.homEquiv _ _).symm.trans ((adjPush.homEquiv _ _).symm.trans
      ((e3.homCongr (Iso.refl F)).symm.trans (adjWD.homEquiv _ _)))).subsingleton
  rw [IsZero.iff_id_eq_zero]
  exact Subsingleton.elim _ _

/-- **Stacks 08GG, clause (2)(b).**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished
square of algebraic spaces over a scheme `S` and set `T = |X| \ |U|`.  For `F` in `D(𝒪_V)`
supported on `j⁻¹T`, the counit `(Rj_*F)|_V ⟶ F` is an isomorphism.

`Rj_*` is a right adjoint of derived restriction, given with its adjunction.  The proof is
`CategoryTheory.Adjunction.isIso_counit_of_isIso_unit_of_isIso_counit` applied to
`j_! ⊣ (-)|_V ⊣ Rj_*`; its three inputs are clause (2)(a) at `F` and at `(Rj_*F)|_V`, and
clause (1)(b) at `Rj_*F`, which is supported on `T` because it vanishes on `U`
(`isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn`). -/
@[stacks 08GG "clause (2)(b): the counit (Rj_*F)|_V ⟶ F is an isomorphism for F in D(O_V)
supported on j^{-1}T, unconditionally; Rj_* is a right adjoint of derived restriction, given
with its adjunction"]
theorem isIso_counit_edsEtale_rightAdjoint_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (adjPush.counit.app F) := by
  let adjL := Adjunction.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq)
  have hN := cohomologySupportedOn_of_isZero_edsDerivedRestrictOpen B S hS hsq (RpushD.obj F)
    (isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush F hF)
  have : IsIso (adjL.unit.app F) :=
    isIso_derivedUnit_edsEtale_of_cohomologySupportedOn B S hS hsq F hF
  have : IsIso (adjL.unit.app ((edsDerivedRestrictEtale B S hS hsq).obj (RpushD.obj F))) :=
    isIso_derivedUnit_edsEtale_of_cohomologySupportedOn B S hS hsq _
      (cohomologySupportedOn_edsDerivedRestrictEtale B S hS hsq _ hN)
  have : IsIso (adjL.counit.app (RpushD.obj F)) :=
    isIso_derivedCounit_edsEtale_app B S hS hsq _ hN
  exact Adjunction.isIso_counit_of_isIso_unit_of_isIso_counit adjL adjPush F

omit adjPush in
/-- **A map of objects supported on `T` whose restriction to `V` is invertible is invertible**:
both are the extensions by zero of their restrictions (Stacks 08GG (1)(b)), naturally. -/
theorem isIso_of_isIso_edsDerivedRestrictEtale_map
    {M N : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)} (φ : M ⟶ N)
    (hM : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) M)
    (hN : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) N)
    (hφ : IsIso ((edsDerivedRestrictEtale B S hS hsq).map φ)) : IsIso φ := by
  let adjL := Adjunction.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq)
  have := isIso_derivedCounit_edsEtale_app B S hS hsq M hM
  have := isIso_derivedCounit_edsEtale_app B S hS hsq N hN
  have hnat := adjL.counit.naturality φ
  simp only [Functor.comp_map, Functor.id_map] at hnat
  have : φ = inv (adjL.counit.app M) ≫
      (etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.map
        ((edsDerivedRestrictEtale B S hS hsq).map φ) ≫ adjL.counit.app N := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

/-- **Stacks 08GG, clause (1)(a).**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished
square of algebraic spaces over a scheme `S` and set `T = |X| \ |U|`.  For `E` in `D(𝒪_X)`
supported on `T`, the unit `E ⟶ Rj_*(E|_V)` is an isomorphism.

Its restriction to `V` is a section of the counit at `E|_V`, which is invertible by clause
(2)(b); both `E` and `Rj_*(E|_V)` are supported on `T`, and a map between such objects which is
invertible on `V` is invertible (`isIso_of_isIso_edsDerivedRestrictEtale_map`). -/
@[stacks 08GG "clause (1)(a): the unit E ⟶ Rj_*(E|_V) is an isomorphism for E in D(O_X)
supported on T = |X| \\ |U|, unconditionally; Rj_* is a right adjoint of derived restriction,
given with its adjunction"]
theorem isIso_unit_edsEtale_rightAdjoint_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    IsIso (adjPush.unit.app E) := by
  have hEV := cohomologySupportedOn_edsDerivedRestrictEtale B S hS hsq E hE
  have hN := cohomologySupportedOn_of_isZero_edsDerivedRestrictOpen B S hS hsq _
    (isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush _ hEV)
  have := isIso_counit_edsEtale_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush _ hEV
  refine isIso_of_isIso_edsDerivedRestrictEtale_map B S hS hsq _ hE hN ?_
  have htri := adjPush.left_triangle_components E
  have : (edsDerivedRestrictEtale B S hS hsq).map (adjPush.unit.app E) =
      inv (adjPush.counit.app ((edsDerivedRestrictEtale B S hS hsq).obj E)) := by
    rw [← cancel_mono (adjPush.counit.app ((edsDerivedRestrictEtale B S hS hsq).obj E)),
      IsIso.inv_hom_id]
    exact htri
  rw [this]
  infer_instance

/-- **Stacks 08GG, clause (2)(c).**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished
square of algebraic spaces over a scheme `S` and set `T = |X| \ |U|`.  For `F` in `D(𝒪_V)`
supported on `j⁻¹T`, the comparison `j_!F ⟶ Rj_*F` is an isomorphism.

The comparison is the library's `AlgebraicGeometry.Space.supportedShriekToPushforward`, the
adjunct of the inverse of the unit of clause (2)(a); its invertibility is
`AlgebraicGeometry.Space.isIso_supportedShriekToPushforward` with all four of its inputs, clauses
(2)(a), (2)(b) and (1)(a) at `j_!F` and at `Rj_*F`, now theorems. -/
@[stacks 08GG "clause (2)(c): the comparison j_!F ⟶ Rj_*F is an isomorphism for F in D(O_V)
supported on j^{-1}T, unconditionally; j_! and Rj_* are the left and right adjoints of derived
restriction, given with their adjunctions"]
theorem isIso_supportedShriekToPushforward_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (supportedShriekToPushforward B S hS hsq
      (Adjunction.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq)) adjPush F
      (isIso_derivedUnit_edsEtale_of_cohomologySupportedOn B S hS hsq F hF)) :=
  isIso_supportedShriekToPushforward B S hS hsq
    (Adjunction.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq)) adjPush F
    (isIso_derivedUnit_edsEtale_of_cohomologySupportedOn B S hS hsq F)
    (isIso_counit_edsEtale_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush F)
    (fun hF' => isIso_unit_edsEtale_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush _
      (cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn B S hS hsq F hF'))
    (fun hF' => isIso_unit_edsEtale_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush _
      (cohomologySupportedOn_of_isZero_edsDerivedRestrictOpen B S hS hsq _
        (isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush F
          hF')))
    hF

omit adjPush in
/-- **The extension by zero of a perfect object supported on `j⁻¹T` is perfect**: it vanishes on
`U` (Stacks 08HA) and restricts to the object itself on `V` (Stacks 08GG (2)(a)), and
perfectness is local on `X_étale`. -/
theorem isPerfect_edsEtale_shriek_of_cohomologySupportedOn
    (K : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hperf : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect K)
    (hK : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) K) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj K) := by
  have := isIso_derivedUnit_edsEtale_of_cohomologySupportedOn B S hS hsq K hK
  refine isPerfect_of_isPerfect_eds B S hS hsq _ (RingedSite.isPerfect_of_isZero _ ?_)
    (RingedSite.IsPerfect.of_iso _ hperf (asIso ((Adjunction.mapDerivedCategory
      (edsEtaleShriekAdjunction B S hS hsq)).unit.app K)))
  exact isZero_etaleModulePullback_mapDerivedCategory_of_range_subset B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) _
    (cohomologySupportedOn_lowerShriek_of_cohomologySupportedOn B S hS hsq K hK)
    (range_pointsMap_edsOpenHom B S hS hsq).subset

omit adjPush in
/-- **Morphisms out of a shifted extension by zero** are morphisms out of the shifted object
into the restriction: `Hom(j_!K[n], E) = Hom(K[n], E|_V)`, by the derived adjunction
`j_! ⊣ (-)|_V` and the compatibility of `j_!` with shifts. -/
def shiftedShriekHomEquiv
    (K : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (n : ℤ) :
    (((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj K)⟦n⟧ ⟶ E) ≃
      (K⟦n⟧ ⟶ (edsDerivedRestrictEtale B S hS hsq).obj E) :=
  (((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.commShiftIso n).app K).homCongr
      (Iso.refl E) |>.symm.trans
    ((Adjunction.mapDerivedCategory (edsEtaleShriekAdjunction B S hS hsq)).homEquiv _ _)

omit adjPush in
/-- **An object of `D(𝒪_X)` vanishing on both members of an elementary distinguished square
vanishes**: every cohomology sheaf restricts to zero on both, so its support misses the images
of both, which cover `|X|`. -/
theorem isZero_of_isZero_edsDerivedRestrict
    (M : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : IsZero ((edsDerivedRestrictOpen B S hS hsq).obj M))
    (hV : IsZero ((edsDerivedRestrictEtale B S hS hsq).obj M)) : IsZero M := by
  have hT := cohomologySupportedOn_of_isZero_edsDerivedRestrictOpen B S hS hsq M hU
  refine (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun n => ?_
  refine (supportOfSheaf_eq_empty_iff_isZero B S hS W _).1 ?_
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have hxT := hT n hx
  have hcov := (isEtaleCovering_edsCoveringMember B S hS hsq).jointly_surjective
  have hxU : x ∈ (⋃ b, Set.range (pointsMap B S hS (edsCoveringMember B S hS hsq b).1
      (edsCoveringMemberHom B S hS hsq b).hom)) := by rw [hcov]; trivial
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hxU
  cases b
  · exact hxT hb
  · obtain ⟨y, rfl⟩ := hb
    exact Set.eq_empty_iff_forall_notMem.1 (preimage_supportOfSheaf_homology_eq_empty B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) M n hV) y hx

/-- **Stacks 08HK.**  Let `S` be a scheme, let `(U ⊆ X, j : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`, and set `T = |X| \ |U|`.  Let `E` be a
perfect object of `D(𝒪_V)` supported on `j⁻¹(T)`.  Then `Rj_*E` is a perfect object of
`D(𝒪_X)`.

`Rj_*` is a right adjoint of derived restriction `(-)|_V`, given together with its adjunction,
as in `AlgebraicGeometry.Space.isPerfect_derivedPushforward_of_cohomologySupportedOn`; this
determines it up to a unique compatible isomorphism.  The proof is the source's: perfectness is
local on `X_étale` (`AlgebraicGeometry.Space.isPerfect_of_isPerfect_eds`), the restriction of
`Rj_*E` to `U` vanishes and its restriction to `V` is `E` (Stacks 08GG (2)(b)). -/
@[stacks 08HK]
theorem isPerfect_rightAdjoint_edsDerivedRestrictEtale_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hperf : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect E)
    (hE : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) E) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect (RpushD.obj E) := by
  have := isIso_counit_edsEtale_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush E hE
  exact isPerfect_of_isPerfect_eds B S hS hsq (RpushD.obj E)
    (RingedSite.isPerfect_of_isZero _
      (isZero_edsDerivedRestrictOpen_rightAdjoint_of_cohomologySupportedOn B S hS hsq adjPush E hE))
    (RingedSite.IsPerfect.of_iso _ hperf (asIso (adjPush.counit.app E)).symm)

end Square

end AlgebraicGeometry.Space

end
