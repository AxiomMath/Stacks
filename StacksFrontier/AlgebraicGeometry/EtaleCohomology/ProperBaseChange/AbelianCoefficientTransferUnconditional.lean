module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralBaseChangeReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# AbelianCoefficientTransferUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer`,
stated as separate declarations beside the ones there: over more general coefficient universes,
or with inputs that are carried there as hypotheses discharged, together with the new results
built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

section Abstract

end Abstract

section Unit

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A : Type*} [Category* A]

variable [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P]

end Unit

section Coefficients

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A B : Type*} [Category* A] [Category* B] (Gf : A ⥤ B)
  [HasWeakSheafify K A] [HasWeakSheafify K B]
  [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P] [∀ P : Cᵒᵖ ⥤ B, uf.op.HasLeftKanExtension P]
  [Gf.PreservesLeftKanExtensions uf.op]
  [J.HasSheafCompose Gf] [K.HasSheafCompose Gf] [K.PreservesSheafification Gf]

end Coefficients

/-- **The forgetful functor of abelian groups preserves left Kan extensions along the opposite of
base change of étale schemes**, at every coefficient universe `max (u + 1) v`. Base change
`Stacks.EtaleCohomology.smallEtaleBaseChange` is
representably flat, so each costructured-arrow category indexing the pointwise left Kan extension
is filtered — it is opposite to a structured-arrow category, by
`CategoryTheory.structuredArrowOpEquivalence` — and the forgetful functor preserves filtered
colimits of that size. This is the argument of
`Stacks.EtaleCohomology.etaleAbelianInverseImage_preservesFiniteLimits` aimed at
`CategoryTheory.CostructuredArrow.proj` instead of at the evaluation of the Kan extension. -/
@[sga "4 I 5.8.3" "special case"]
public theorem preservesLeftKanExtensions_forget_smallEtaleBaseChange_univ {X Y : Scheme.{u}}
    (i : Y ⟶ X) :
    (forget AddCommGrpCat.{max (u + 1) v}).PreservesLeftKanExtensions
      (smallEtaleBaseChange i).op := by
  intro P
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange i).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange i) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  infer_instance

/-- The case `v = 0` of
`Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange_univ`, as an
instance: the universe-polymorphic statement cannot be an instance, its coefficient universe
`max (u + 1) v` not unifying with `u + 1`. -/
public instance preservesLeftKanExtensions_forget_smallEtaleBaseChange_succ {X Y : Scheme.{u}}
    (i : Y ⟶ X) :
    (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions (smallEtaleBaseChange i).op :=
  preservesLeftKanExtensions_forget_smallEtaleBaseChange_univ.{u, 0} i

section BaseChange

variable (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)

/-- Composition with the forgetful functor, on abelian sheaves of Mathlib's small étale site of
a scheme of a big étale site. -/
private abbrev coefficientForgetSheafGeneral (S : B.Scheme) :
    Sheaf (Scheme.smallEtaleTopology S.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.smallEtaleTopology S.obj) (Type (max (u + 1) v)) :=
  sheafCompose (Scheme.smallEtaleTopology S.obj) (forget AddCommGrpCat.{max (u + 1) v})

/-- Inverse image of abelian sheaves on Mathlib's small étale site, along a morphism of the
underlying category of a big étale site. -/
private abbrev bigSiteAbelianPullbackGeneral {S T : B.Scheme} (k : T ⟶ S) :
    Sheaf (Scheme.smallEtaleTopology S.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.smallEtaleTopology T.obj) AddCommGrpCat.{max (u + 1) v} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtaleBaseChange (B.inclusion.map k)) AddCommGrpCat.{max (u + 1) v}
    (Scheme.smallEtaleTopology S.obj) (Scheme.smallEtaleTopology T.obj)

/-- The inverse-image/direct-image adjunction for abelian sheaves on Mathlib's small étale
site. -/
private abbrev abelianAdjGeneral {S T : B.Scheme} (k : T ⟶ S) :
    bigSiteAbelianPullbackGeneral.{u, v} B k ⊣
      AlgebraicGeometry.SmallEtale.unboundedPushforward B AddCommGrpCat.{max (u + 1) v} k :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- Inverse image of sheaves of sets on Mathlib's small étale site, along a morphism of the
underlying category of a big étale site. -/
private abbrev unboundedPullbackGeneral {S T : B.Scheme} (k : T ⟶ S) :
    Sheaf (Scheme.smallEtaleTopology S.obj) (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.smallEtaleTopology T.obj) (Type (max (u + 1) v)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtaleBaseChange (B.inclusion.map k)) (Type (max (u + 1) v))
    (Scheme.smallEtaleTopology S.obj) (Scheme.smallEtaleTopology T.obj)

/-- The inverse-image/direct-image adjunction for sheaves of sets on Mathlib's small étale
site. -/
private abbrev unboundedAdjGeneral {S T : B.Scheme} (k : T ⟶ S) :
    unboundedPullbackGeneral.{u, v} B k ⊣
      AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (max (u + 1) v)) k :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The comparison of the two composites of an inverse image with the change of coefficients,
for a morphism of the underlying category of a big étale site. -/
private abbrev bigSitePullbackForgetGeneral {S T : B.Scheme} (k : T ⟶ S) :
    TwoSquare (coefficientForgetSheafGeneral.{u, v} B S) (bigSiteAbelianPullbackGeneral.{u, v} B
      k) (unboundedPullbackGeneral.{u, v} B k)
      (coefficientForgetSheafGeneral.{u, v} B T) :=
  coefficientPullbackTwoSquare (smallEtaleBaseChange (B.inclusion.map k))
    (Scheme.smallEtaleTopology S.obj) (Scheme.smallEtaleTopology T.obj)
    (forget AddCommGrpCat.{max (u + 1) v})

/-- **Direct image commutes with the change of coefficients on the nose**: both composites
restrict sections along base change and then forget the group structure. -/
private abbrev pushforwardForgetGeneral {S T : B.Scheme} (k : T ⟶ S) :
    AlgebraicGeometry.SmallEtale.unboundedPushforward B AddCommGrpCat.{max (u + 1) v} k ⋙
        coefficientForgetSheafGeneral.{u, v} B S ⟶
      coefficientForgetSheafGeneral.{u, v} B T ⋙
        AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (max (u + 1) v)) k :=
  𝟙 _

private instance isIso_pushforwardForget {S T : B.Scheme} (k : T ⟶ S) :
    IsIso (pushforwardForgetGeneral.{u, v} B k) := by
  change IsIso (𝟙 _)
  infer_instance

/-- The comparison of `Stacks.EtaleCohomology.pushforwardForget` read in the other direction. -/
private abbrev pushforwardForget'General {S T : B.Scheme} (k : T ⟶ S) :
    coefficientForgetSheafGeneral.{u, v} B T ⋙
        AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (max (u + 1) v)) k ⟶
      AlgebraicGeometry.SmallEtale.unboundedPushforward B AddCommGrpCat.{max (u + 1) v} k ⋙
        coefficientForgetSheafGeneral.{u, v} B S :=
  𝟙 _

private instance isIso_pushforwardForget' {S T : B.Scheme} (k : T ⟶ S) :
    IsIso (pushforwardForget'General.{u, v} B k) := by
  change IsIso (𝟙 _)
  infer_instance

/-- **The comparison of composite direct images around the square is compatible with the change
of coefficients.** Both sides restrict sections along the same composite of comparisons of base
changes of sites, so the statement is the compatibility of that restriction with the forgetful
functor. -/
private lemma unboundedBaseChangeMate_forget_general
    (F : Sheaf (Scheme.smallEtaleTopology X'.obj) AddCommGrpCat.{max (u + 1) v}) :
    (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f'
          P hP₁ hP₂).app ((coefficientForgetSheafGeneral.{u, v} B X').obj F) =
      (coefficientForgetSheafGeneral.{u, v} B Y).map
        ((AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{max (u + 1) v} f g
          g' f' P hP₁ hP₂).app F) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun UU => ?_))
  obtain ⟨U⟩ := UU
  rw [AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate_app_hom_app, sheafCompose_map_hom,
    Functor.whiskerRight_app, AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate_app_hom_app]
  rfl

/-- **The cube identity for the change of coefficients.** The comparison of the two composite
direct images around the square at set coefficients, pasted with the comparisons of the two
coefficient categories, is the comparison at abelian coefficients. Every side comparison through
a direct image is an identity, so this is
`Stacks.EtaleCohomology.unboundedBaseChangeMate_forget` padded with identities. -/
private lemma coefficient_cube_eq_general :
    ((mateEquiv (abelianAdjGeneral.{u, v} B g') (unboundedAdjGeneral.{u, v} B g')
            (bigSitePullbackForgetGeneral.{u, v} B g') ≫ᵥ
          AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f'
            P hP₁ hP₂).whiskerRight (pushforwardForgetGeneral.{u, v} B f)).whiskerLeft
        (pushforwardForget'General.{u, v} B f') =
      AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{max (u + 1) v} f g g' f'
          P hP₁ hP₂ ≫ᵥ
        mateEquiv (abelianAdjGeneral.{u, v} B g) (unboundedAdjGeneral.{u, v} B g)
          (bigSitePullbackForgetGeneral.{u, v} B g) := by
  rw [mateEquiv_coefficientPullbackTwoSquare, mateEquiv_coefficientPullbackTwoSquare]
  refine NatTrans.ext (funext fun F => ?_)
  rw [AlgebraicGeometry.SmallEtale.ts_whiskerLeft_app,
    AlgebraicGeometry.SmallEtale.ts_whiskerRight_app, AlgebraicGeometry.SmallEtale.ts_vComp_app,
    AlgebraicGeometry.SmallEtale.ts_vComp_app]
  exact pad_identities _ _ _ _ _ _
    (unboundedBaseChangeMate_forget_general.{u, v} B f g g' f' P hP₁ hP₂ F)
    rfl (CategoryTheory.Functor.map_id _ _) (CategoryTheory.Functor.map_id _ _) rfl

/-- **The mate of the comparison of composite direct images is invertible at abelian
coefficients.** This is the transport of Stacks 0959 from sheaves of sets to sheaves of abelian
groups: the cube identity `Stacks.EtaleCohomology.coefficient_cube_eq` feeds
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, whose hypothesis at the
lower right corner is only that composition with the forgetful functor reflects isomorphisms. -/
private lemma isIso_mateEquiv_symm_abelianBaseChangeMate_general
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (hcomm : g' ≫ f = f' ≫ g) :
    IsIso ((mateEquiv (abelianAdjGeneral.{u, v} B g') (abelianAdjGeneral.{u, v} B g)).symm
      (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{max (u + 1) v} f g g'
        f' P hP₁ hP₂)) := by
  have := preservesLeftKanExtensions_forget_smallEtaleBaseChange_univ.{u, v} (B.inclusion.map g')
  have := preservesLeftKanExtensions_forget_smallEtaleBaseChange_univ.{u, v} (B.inclusion.map g)
  have hback :=
    AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate_univ.{u, v}
      B f g g' f' sq hcomm P hP₁ hP₂ (unboundedAdjGeneral.{u, v} B g)
      (unboundedAdjGeneral.{u, v} B g')
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (abelianAdjGeneral.{u, v} B g') (abelianAdjGeneral.{u, v} B g)
    (unboundedAdjGeneral.{u, v} B g') (unboundedAdjGeneral.{u, v} B g)
    (bigSitePullbackForgetGeneral.{u, v} B g') (bigSitePullbackForgetGeneral.{u, v} B g)
    (pushforwardForgetGeneral.{u, v} B f) (pushforwardForget'General.{u, v} B f')
    (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{max (u + 1) v} f g g' f'
      P hP₁ hP₂)
    (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f'
      P hP₁ hP₂)
    (coefficient_cube_eq_general.{u, v} B f g g' f' P hP₁ hP₂)

end BaseChange

section BigSite

variable (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- The underived base change comparison of abelian sheaves is invertible for a cartesian square
of the underlying category of a big étale site with `f` finite: Stacks 0959 transported from
sheaves of sets on the size-bounded small étale site of Stacks 021B to abelian sheaves on the
presentation of the small étale site used here. The containment in `B` is removed in
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_unconditional`. -/
private theorem isIso_etaleAbelianBaseChange_of_isFinite_of_bigEtaleSite
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g)) [IsFinite (B.inclusion.map f)] :
    IsIso (etaleAbelianBaseChange.{u, v} (B.inclusion.map f) (B.inclusion.map g)
      (B.inclusion.map g') (B.inclusion.map f') sq.w) := by
  have hcomm : g' ≫ f = f' ≫ g :=
    B.inclusion.map_injective (by rw [B.inclusion.map_comp, B.inclusion.map_comp]; exact sq.w)
  have hkey := isIso_mateEquiv_symm_abelianBaseChangeMate_general.{u, v} B f g g' f' (g' ≫ f) rfl
    hcomm.symm sq hcomm
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v}
    (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') sq.w
    (B.inclusion.map (g' ≫ f)) (B.inclusion.map_comp g' f)
    ((congrArg B.inclusion.map hcomm).trans (B.inclusion.map_comp f' g))]
  exact hkey

end BigSite

section Main

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **The underived base change comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian sheaves on
the small étale sites is invertible**, for a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of schemes with `f` finite. This is Stacks 0959 at abelian coefficients and at the presentation
of the small étale site used here. The statement proved in the library,
`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_univ`, is for sheaves of sets on the
size-bounded small étale site of Stacks 021B of a big étale site; the four schemes of the square
are placed in one such site by `AlgebraicGeometry.BigEtaleSite.ofSet`, which is Stacks 000J and
000X, so no containment is assumed. -/
public theorem isIso_etaleAbelianBaseChange_of_isFinite_unconditional (sq : IsPullback g' f' f g)
    [IsFinite f] : IsIso (etaleAbelianBaseChange.{u, v} f g g' f' sq.w) := by
  let S₀ : Set Scheme.{u} := {X, X', Y, Y'}
  let B := BigEtaleSite.ofSet S₀
  let o (Z : Scheme.{u}) (hZ : Z ∈ S₀ := by simp [S₀]) : B.Scheme :=
    ⟨Z, BigEtaleSite.contains_ofSet S₀ hZ⟩
  let oX := o X
  let oX' := o X'
  let oY := o Y
  let oY' := o Y'
  have : IsFinite (B.inclusion.map (X := oX) (Y := oY) (ObjectProperty.homMk f)) := ‹IsFinite f›
  exact isIso_etaleAbelianBaseChange_of_isFinite_of_bigEtaleSite.{u, v} B (X := oX) (Y := oY)
    (X' := oX') (Y' := oY') (ObjectProperty.homMk f) (ObjectProperty.homMk g)
    (ObjectProperty.homMk g') (ObjectProperty.homMk f') sq

/-- **The base change map of a finite morphism is invertible at every abelian sheaf.** For a
cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of schemes with `f` finite, and every abelian sheaf `F` on the small étale site of `X`, the base
change map `g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` on unbounded derived categories is an
isomorphism. No torsion condition is imposed, and finiteness of `f'` is obtained from the
square.

The two inputs are
`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso`, which
reduces the derived statement to the underived comparison using the vanishing of the positive
higher direct images of a finite morphism (Stacks 03QP), and
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_unconditional`, which is
Stacks 0959 at abelian coefficients. -/
@[sga "4 XII 5.1" "(iii)", sga "4½ Th_finitude 5.1.3" "1.3.1, special case"]
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_univ (sq : IsPullback g' f' f g)
    [IsFinite f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' sq.w F) :=
  isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso.{u, v} f g g' f' sq
    (isIso_etaleAbelianBaseChange_of_isFinite_unconditional f g g' f' sq) F

/-- **[Stacks, Tag 0A4E]: proper base change for finite morphisms.** Cohomology commutes with
base change for a finite morphism of schemes `f : X ⟶ Y`: for every cartesian square with
`X' = Y' ×_Y X` and every torsion abelian sheaf `F` on `X_étale`, the base change map
`g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` is an isomorphism.

The torsion hypothesis of the predicate is not used:
`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_univ` gives the
isomorphism at every abelian sheaf. Coefficients are `AddCommGrpCat.{max (u + 1) v}` for every
universe `v`: abelian groups at least as large as the small étale site of a scheme in
`Scheme.{u}`. -/
@[sga "4 XII 5.2" "(iii), special case", sga "4½ Th_finitude 5.1.3" "1.3.1, special case"]
public theorem cohomologyCommutesWithBaseChange_of_isFinite_general (f : X ⟶ Y) [IsFinite f] :
    CohomologyCommutesWithBaseChange.{u, v} f :=
  fun _ _ g g' f' sq F _ ↦ isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_univ f g g' f' sq F

end Main

end Stacks.EtaleCohomology

end
