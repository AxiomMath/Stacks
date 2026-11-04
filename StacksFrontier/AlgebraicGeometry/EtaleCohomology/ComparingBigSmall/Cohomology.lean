module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Restriction
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianSheaves
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Étale cohomology on the big and the small site agree

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of `B`. Cohomology over the
object `T ⟶ S` on the big étale site of `S` agrees with cohomology on the small étale site of
`T` after restriction: the derived sections functor at `T ⟶ S` is the composite of restriction
with derived global sections on the small étale site.

## Main definitions

* `AlgebraicGeometry.bigEtaleSections` is the sections functor at the object `T ⟶ S` of the
  big étale site of `S`.
* `AlgebraicGeometry.smallEtaleRestriction` is the inverse image to the small étale site of `T`.

## Main results

* `AlgebraicGeometry.bigSmallEtaleCohomologyIso` is the natural comparison of the two derived
  section functors. Taking degree-`n` homology gives the asserted equality of cohomology
  groups in every degree.

## Implementation notes

The value of sections on the big site is taken at the object `T ⟶ S`; on the small site it is
global sections after the inverse-image functor
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor`. The two agree because `T / T` is the final
object of the small étale site of `T` and is carried to `T ⟶ S`.

The comparison is stated between unbounded derived section functors, so it is natural in the
derived coefficient object rather than only in each degree. The identification of the composite
as a right-derived functor uses that restriction preserves K-injectivity
(`AlgebraicGeometry.isKInjective_smallEtaleRestrictionAlong`), which is what makes the
composite's unit an isomorphism on K-injective complexes; the criteria for recognizing a
right-derived functor from its values on K-injective complexes are in
`Stacks.Injectives.rightDerived_of_kInjective_units` and
`Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective`. Both sheaf categories are
Grothendieck abelian because the sites are essentially small, by
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify`.

## References

* [Stacks Project, Tag 0DDH](https://stacks.math.columbia.edu/tag/0DDH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

attribute [local instance] HasDerivedCategory.standard

/-- Sections on the big étale site of `S` over the object `T ⟶ S`. -/
public abbrev bigEtaleSections :
    Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (sheafSections (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}).obj
    (op (Over.mk f))

/-- Restriction from the big étale site of `S` to the small étale site of `T`. -/
public abbrev smallEtaleRestriction :
    Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1} ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1} :=
  (smallEtaleToBigEtaleFunctor B T S f).sheafPushforwardContinuous
      Ab.{u + 1} (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)

public instance bigEtaleSections_additive : (bigEtaleSections B T S f).Additive := ⟨rfl⟩

public instance smallEtaleGlobalSections_additive
    [HasSheafify (SmallEtale.topology B T.obj T.property) Ab.{u + 1}] :
    (Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

public instance smallEtaleRestriction_additive
    [HasSheafify (SmallEtale.topology B T.obj T.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}] :
    (smallEtaleRestriction B T S f).Additive := ⟨rfl⟩

/-- Sections at `T ⟶ S` on the big site are global sections of the restriction to the small
étale site of `T`, naturally in the sheaf. -/
public noncomputable def bigSmallEtaleSectionsIso
    [HasSheafify (SmallEtale.topology B T.obj T.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}] :
    bigEtaleSections B T S f ≅
      smallEtaleRestriction B T S f ⋙
        Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1} := by
  let U := SmallEtale.final B T.obj T.property
  have hU : IsTerminal U := SmallEtale.finalIsTerminal B T.obj T.property
  have hobj : (smallEtaleToBigEtaleFunctor B T S f).obj U =
      Over.mk f := by
    change (Over.map f).obj ((SmallEtale.inclusion B T.obj T.property).obj U) = _
    change Over.mk (𝟙 (B.obj T.obj T.property) ≫ f) = Over.mk f
    simp
  let γ := Sheaf.ΓNatIsoSheafSections
    (SmallEtale.topology B T.obj T.property) Ab.{u + 1} hU
  let eF (F : Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :
      F.obj.obj (op (Over.mk f)) ≅
        ((smallEtaleRestriction B T S f).obj F).obj.obj (op U) :=
    (eqToIso (congrArg (fun X : BigEtaleOver B S.obj S.property =>
      F.obj.obj (op X)) hobj)).symm
  have eF_hom (F : Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :
      (eF F).hom = F.obj.map (eqToHom hobj).op := by
    dsimp [eF]
    rw [eqToHom_op, eqToHom_map]
  refine NatIso.ofComponents (fun F => eF F ≪≫
    (γ.app ((smallEtaleRestriction B T S f).obj F)).symm) ?_
  · intro F G φ
    have hEval : φ.hom.app (op (Over.mk f)) ≫ (eF G).hom =
        (eF F).hom ≫ ((smallEtaleRestriction B T S f).map φ).hom.app (op U) := by
      have hR : ((smallEtaleRestriction B T S f).map φ).hom.app (op U) =
          φ.hom.app (op ((smallEtaleToBigEtaleFunctor B T S f).obj U)) := by
        rfl
      rw [eF_hom G, eF_hom F, hR]
      exact (φ.hom.naturality (eqToHom hobj).op).symm
    change φ.hom.app (op (Over.mk f)) ≫
        ((eF G).hom ≫ (γ.symm).hom.app ((smallEtaleRestriction B T S f).obj G)) =
      ((eF F).hom ≫ (γ.symm).hom.app ((smallEtaleRestriction B T S f).obj F)) ≫
        (Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).map
          ((smallEtaleRestriction B T S f).map φ)
    calc
      _ = (eF F).hom ≫
          (((smallEtaleRestriction B T S f).map φ).hom.app (op U) ≫
            (γ.symm).hom.app ((smallEtaleRestriction B T S f).obj G)) := by
              rw [← Category.assoc, hEval, ← Category.assoc]
      _ = (eF F).hom ≫
          ((γ.symm).hom.app ((smallEtaleRestriction B T S f).obj F) ≫
            (Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).map
              ((smallEtaleRestriction B T S f).map φ)) := by
                rw [← Category.assoc]
                change (eF F).hom ≫
                  ((sheafSections (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).obj
                    (op U)).map ((smallEtaleRestriction B T S f).map φ) ≫
                    (γ.symm).hom.app ((smallEtaleRestriction B T S f).obj G) = _
                exact congrArg ((eF F).hom ≫ ·)
                  ((γ.symm).hom.naturality ((smallEtaleRestriction B T S f).map φ))
      _ = _ := by rw [Category.assoc]

/-- Abelian sheaves on the big étale site over `S` form a Grothendieck abelian category. -/
public lemma bigEtaleSheaf_isGrothendieckAbelian
    (B : BigEtaleSite.{u}) (S : B.Scheme)
    [HasSheafify (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}] :
    IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify.{u + 1, u + 1, u, u + 2, u + 1}
    (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}

/-- Abelian sheaves on the small étale site of `T` form a Grothendieck abelian category. -/
public lemma smallEtaleSheaf_isGrothendieckAbelian
    (B : BigEtaleSite.{u}) (T : B.Scheme)
    [HasSheafify (SmallEtale.topology B T.obj T.property) Ab.{u + 1}] :
    IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify.{u + 1, u + 1, u, u + 2, u + 1}
    (SmallEtale.topology B T.obj T.property) Ab.{u + 1}

/-- The canonical comparison of big-site cohomology over `T` with small-site
cohomology of the restricted complex, natural in the unbounded derived object.
Applying degree-`n` homology gives the equality of groups in Stacks 0DDH. -/
@[stacks 0DDH "big_small_abelian"]
public noncomputable def bigSmallEtaleCohomologyIso
    [HasSheafify (SmallEtale.topology B T.obj T.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}]
    [((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ))]
    [((smallEtaleRestriction B T S f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ))]
    [((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
          (ComplexShape.up ℤ))] :
    (((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ))) ≅
    ((((smallEtaleRestriction B T S f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ))) ⋙
    (((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
          (ComplexShape.up ℤ)))) := by
  let Cb := Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}
  let Cs := Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2} Cb :=
    bigEtaleSheaf_isGrothendieckAbelian B S
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2} Cs :=
    smallEtaleSheaf_isGrothendieckAbelian B T
  let c := ComplexShape.up ℤ
  let Qb := DerivedCategory.Qh (C := Cb)
  let Qs := DerivedCategory.Qh (C := Cs)
  let Qa := DerivedCategory.Qh (C := Ab.{u + 1})
  let Wb := HomotopyCategory.quasiIso Cb c
  let Ws := HomotopyCategory.quasiIso Cs c
  let F := bigEtaleSections B T S f
  let R := smallEtaleRestriction B T S f
  let G := Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}
  let Fh := F.mapHomotopyCategory c ⋙ Qa
  let Rh := R.mapHomotopyCategory c
  let Gc := G.mapHomotopyCategory c
  let Gh := Gc ⋙ Qa
  let RF := Fh.totalRightDerived Qb Wb
  let αF := Fh.totalRightDerivedUnit Qb Wb
  let RR := (Rh ⋙ Qs).totalRightDerived Qb Wb
  let αR := (Rh ⋙ Qs).totalRightDerivedUnit Qb Wb
  let RG := Gh.totalRightDerived Qs Ws
  let αG := Gh.totalRightDerivedUnit Qs Ws
  let e₀ := bigSmallEtaleSectionsIso B T S f
  let e₁ := Functor.mapHomotopyCategoryCompIso e₀.symm c
  let τ : Fh ≅ Rh ⋙ Gh :=
    Functor.isoWhiskerRight e₁.symm Qa ≪≫ Functor.associator Rh Gc Qa
  let α : Fh ⟶ Qb ⋙ (RR ⋙ RG) :=
    τ.hom ≫ Functor.whiskerLeft Rh αG ≫
      (Functor.associator Rh Qs RG).inv ≫ Functor.whiskerRight αR RG ≫
      (Functor.associator Qb RR RG).hom
  have hα : ∀ (I : CochainComplex Cb ℤ) [I.IsKInjective],
      IsIso (α.app ((HomotopyCategory.quotient Cb c).obj I)) := by
    intro I hI
    have hR : IsIso (αR.app ((HomotopyCategory.quotient Cb c).obj I)) := by
      exact Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective (Rh ⋙ Qs) RR αR I
    have hRI : CochainComplex.IsKInjective
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
      exact isKInjective_smallEtaleRestrictionAlong B T S f I
    have hG : IsIso (αG.app
        (Rh.obj ((HomotopyCategory.quotient Cb c).obj I))) := by
      let := hRI
      exact Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective Gh RG αG
        ((R.mapHomologicalComplex c).obj I)
    have hτ : IsIso (τ.hom.app ((HomotopyCategory.quotient Cb c).obj I)) :=
      NatIso.isIso_app_of_isIso τ.hom ((HomotopyCategory.quotient Cb c).obj I)
    let := hR
    let := hG
    let := hτ
    dsimp [α]
    infer_instance
  have hcomp : (RR ⋙ RG).IsRightDerivedFunctor α Wb :=
    Stacks.Injectives.rightDerived_of_kInjective_units Fh (RR ⋙ RG) α hα
  let : RR.IsRightDerivedFunctor αR Wb := inferInstance
  let : RG.IsRightDerivedFunctor αG Ws := inferInstance
  let : (RR ⋙ RG).IsRightDerivedFunctor α Wb := hcomp
  exact Functor.rightDerivedNatIso RF (RR ⋙ RG) αF α Wb (Iso.refl Fh)

/-! ### The two derived section functors exist -/

/-- **`RΓ(T → S, −)` on the big étale site exists.**  Sections at the object `T ⟶ S` are only
left exact, so — unlike for the exact `i_f^{-1}` of
`AlgebraicGeometry.hasRightDerivedFunctor_smallEtaleRestriction` — the right derived functor is
not the functor induced on derived categories.  It exists all the same: abelian sheaves on the
big étale site over `S` are Grothendieck abelian
(`AlgebraicGeometry.bigEtaleSheaf_isGrothendieckAbelian`), so every cochain complex of them
admits a quasi-isomorphism into a K-injective complex ([Stacks, Tag 079P], here
`Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`), and such a resolution is a
terminal index of the colimit computing the left Kan extension along
`DerivedCategory.Qh` ([Stacks, Tag 070K]).  Neither boundedness nor exactness of countable
products enters, and nothing about the functor beyond its being a functor. -/
public instance hasRightDerivedFunctor_bigEtaleSections :
    ((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ)) :=
  let _ : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :=
    bigEtaleSheaf_isGrothendieckAbelian B S
  have : ((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u + 1,
      u + 2, 0, u + 2, u + 2, 0} _
      Stacks.Injectives.exists_kInjective_resolution_of_grothendieck).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **`RΓ(T_étale, −)` on the small étale site exists.**  Global sections are only left exact;
abelian sheaves on the small étale site of `T` are Grothendieck abelian
(`AlgebraicGeometry.smallEtaleSheaf_isGrothendieckAbelian`), so the same K-injective resolution
argument as for `AlgebraicGeometry.hasRightDerivedFunctor_bigEtaleSections` applies. -/
public instance hasRightDerivedFunctor_smallEtaleGlobalSections :
    ((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
          (ComplexShape.up ℤ)) :=
  let _ : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) :=
    smallEtaleSheaf_isGrothendieckAbelian B T
  have : ((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
          (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u + 1,
      u + 2, 0, u + 2, u + 2, 0} _
      Stacks.Injectives.exists_kInjective_resolution_of_grothendieck).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

end AlgebraicGeometry
