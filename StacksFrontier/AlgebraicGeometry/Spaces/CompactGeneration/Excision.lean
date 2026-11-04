module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.RingTheory.Dualizing.Ext
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Excision for an elementary distinguished square

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces with
intersection `P = U ×_W V`. For a sheaf of `𝒪_V`-modules `M` whose restriction to `P` vanishes,
the unit `M ⟶ (j_! M)|_V` of extension by zero is an isomorphism: such a module is recovered from
its extension by zero to `W`.

## Main results

* `AlgebraicGeometry.Space.isIso_edsEtale_unit_of_isZero_restrict`: the excision isomorphism.
* `AlgebraicGeometry.Space.isIso_derivedUnit_edsEtale_of_isZero_restrict`: the same on the
  unbounded derived category.

## References

* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The extension by zero along the étale morphism of an elementary distinguished square of a
module vanishing on the intersection restricts to zero on the open subspace. -/
theorem isZero_restrict_edsOpen_edsEtale_shriek (M : Modules.{u, u} B S hS
      (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)
    (hM : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).obj M)) :
    IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj
        ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj M)) := by
  have h := isIso_restrictExtensionByZeroMap B S hS (isPullback_edsInter B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq))
  exact (((etaleModuleLowerShriek B S hS (edsFst B S hS hsq)
    (isEtale_edsFst B S hS hsq)).map_isZero hM)).of_iso
      (asIso ((restrictExtensionByZeroMap B S hS (isPullback_edsInter B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
        (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq))
        (etaleModuleLowerShriekAdjunction B S hS (edsFst B S hS hsq)
          (isEtale_edsFst B S hS hsq))).app M)).symm

/-- For a sheaf of `𝒪_W`-modules `F` restricting to zero on the open subspace of an elementary
distinguished square, the counit `j_!(F|_V) ⟶ F` along the étale morphism is an isomorphism. -/
theorem isIso_edsEtale_counit_of_isZero_restrict_edsOpen (F : Modules.{u, u} B S hS W.1 W.2)
    (hF : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj F)) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).counit.app F) := by
  have hSE := (mayerVietoris_shortExact_and_mem_distTriang B S hS hsq).1 F
  have hU : IsZero ((etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj ((etaleModulePullback.{u, u} B S hS
        (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).obj F)) :=
    Functor.map_isZero _ hF
  have hP : IsZero ((etaleModuleLowerShriek B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).obj ((etaleModulePullback.{u, u} B S hS
        (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)).obj F)) :=
    Functor.map_isZero _ (((etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq)
      (isEtale_edsFst B S hS hsq)).map_isZero hF).of_iso ((edsFactorIsoOpen B S hS hsq).app F).symm)
  set εU := (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)).counit.app F
  set εV := (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).counit.app F
  have hg : IsIso (biprod.desc εU εV) := by
    have : Epi (biprod.desc εU εV) := hSE.epi_g
    have : Mono (biprod.desc εU εV) := hSE.exact.mono_g (hP.eq_of_src _ _)
    exact isIso_of_mono_of_epi _
  rw [← biprod.inr_desc εU εV]
  exact IsIso.comp_isIso' (isoZeroBiprod hU).isIso_hom hg

/-- **Excision for an elementary distinguished square.** For a sheaf of `𝒪_V`-modules `M`
vanishing on the intersection `P`, the unit `M ⟶ (j_! M)|_V` of extension by zero along the étale
morphism `j : V ⟶ W` is an isomorphism. -/
theorem isIso_edsEtale_unit_of_isZero_restrict (M : Modules.{u, u} B S hS
      (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)
    (hM : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).obj M)) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).unit.app M) := by
  let j := edsEtaleHom B S hS hsq
  let hj := isEtale_edsEtaleHom B S hS hsq
  let adj := etaleModuleLowerShriekAdjunction B S hS j hj
  let η := adj.unit.app M
  have hε := isIso_edsEtale_counit_of_isZero_restrict_edsOpen B S hS hsq _
    (isZero_restrict_edsOpen_edsEtale_shriek B S hS hsq M hM)
  have : IsIso ((etaleModuleLowerShriek B S hS j hj).map η ≫
      adj.counit.app ((etaleModuleLowerShriek B S hS j hj).obj M)) := by
    rw [adj.left_triangle_components M]; infer_instance
  have := IsIso.of_isIso_comp_right ((etaleModuleLowerShriek B S hS j hj).map η)
    (adj.counit.app ((etaleModuleLowerShriek B S hS j hj).obj M))
  have : Mono η := Preadditive.mono_of_isZero_kernel _ <|
    isZero_of_isZero_etaleModuleLowerShriek B S hS j hj _ <|
      (isZero_kernel_of_mono ((etaleModuleLowerShriek B S hS j hj).map η)).of_iso
        (PreservesKernel.iso (etaleModuleLowerShriek B S hS j hj) η)
  have : Epi η := Preadditive.epi_of_isZero_cokernel _ <|
    isZero_of_isZero_etaleModuleLowerShriek B S hS j hj _ <|
      (isZero_cokernel_of_epi ((etaleModuleLowerShriek B S hS j hj).map η)).of_iso
        (PreservesCokernel.iso (etaleModuleLowerShriek B S hS j hj) η)
  exact isIso_of_mono_of_epi η

section Derived

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **Excision on the unbounded derived category.** For an object `E` of `D(𝒪_V)` whose
cohomology sheaves vanish on the intersection `P`, the unit `E ⟶ (j_! E)|_V` of the derived
extension-by-zero adjunction along `j : V ⟶ W` is an isomorphism. -/
theorem isIso_derivedUnit_edsEtale_of_isZero_restrict
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hE : ∀ i : ℤ, IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).obj ((DerivedCategory.homologyFunctor _ i).obj E))) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.unit.app E) :=
  Dualizing.PowerTorsionBaseChange.mapDerivedAdjunction_unit_isIso _ E
    fun i => isIso_edsEtale_unit_of_isZero_restrict B S hS hsq _ (hE i)

/-- The cohomology sheaves of an object of `D(𝒪_V)` vanish on the intersection exactly when the
object itself restricts to zero there. -/
theorem forall_isZero_restrict_homology_iff
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)) :
    (∀ i : ℤ, IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).obj ((DerivedCategory.homologyFunctor _ i).obj E))) ↔
      IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj E) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  exact forall_congr' fun i => Iso.isZero_iff
    (((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategoryHomologyIso i).app E).symm

end Derived

end Square

end AlgebraicGeometry.Space

end
