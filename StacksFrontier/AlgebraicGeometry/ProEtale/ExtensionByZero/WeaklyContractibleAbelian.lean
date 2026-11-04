module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompactGeneration
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.WeaklyContractible
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image of an abelian sheaf at a weakly contractible affine pro-étale object

This is the abelian-coefficient form of
`StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.WeaklyContractible`: for a closed
immersion `i : Z ⟶ X` of affine objects of a chosen big pro-étale site and a weakly contractible
object `V` of the affine ind-étale site of `Z`, the inverse image of an *abelian* pro-étale sheaf
on `X` has the same sections over `V` as the sheaf has over the lift of `V`.

The argument is the one for sheaves of sets, which
`StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.WeaklyContractible` carries out for an
arbitrary coefficient category once the sheafification step is granted. Only two things have to
be added for abelian coefficients: the identification of the two topoi of Stacks 098X, and the
fact that the unit of sheafification is invertible on sections over a weakly contractible
object. The second is deduced from the statement for sheaves of sets, because local injectivity
and local surjectivity of a morphism of abelian presheaves are properties of the underlying
morphism of presheaves of sets, and a morphism of abelian groups which is bijective is
invertible.

## Main results

* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.hasSheafify_addCommGrp`,
  `AffineIndEtaleProetale.wEqualsLocallyBijective_addCommGrp`: abelian presheaves on the affine
  ind-étale site admit sheafification, which inverts exactly the locally bijective morphisms.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isEquivalence_restriction_addCommGrp`:
  **Stacks 098X** for abelian sheaves.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.sheaf_preservesProduct_addCommGrp`: an
  abelian sheaf on the affine ind-étale site turns the finite coproducts of the site into
  products.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isIso_toSheafify_app_addCommGrp`: at a
  weakly contractible object sheafification is invertible on sections, for abelian presheaves.
* `AlgebraicGeometry.ProEtale.affineIndEtaleSheafificationEvaluationIsoAddCommGrp`: the
  sheafification in the description of the inverse image may therefore be dropped.
* `AlgebraicGeometry.ProEtale.proetaleInverseImage_sections_iso_affineIndEtaleLiftAddCommGrp`:
  **Stacks 09BL (2) for abelian sheaves.**

## Implementation notes

Abelian sheaves are taken in `AddCommGrpCat.{u + 1}`, the universe of the objects of the sites,
which is the choice the rest of the library makes for abelian sheaves on these sites; the
sheaves of sets of the set-valued statements are correspondingly in `Type (u + 1)`.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProEtale

namespace AffineIndEtaleProetale

variable (B : BigProetaleSite.{u}) (S : B.Scheme)

/-- Abelian presheaves on the affine ind-étale site admit sheafification. -/
instance hasSheafify_addCommGrp :
    HasSheafify (topology B S) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0}

/-- Sheafification of abelian presheaves on the affine ind-étale site inverts exactly the
locally bijective morphisms. -/
instance wEqualsLocallyBijective_addCommGrp :
    (topology B S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0}

/-- **Stacks 098X for abelian sheaves.** Restriction from the small pro-étale site to the affine
ind-étale subsite is an equivalence of categories of abelian sheaves. -/
@[stacks 098X "restriction is an equivalence of topoi, for abelian sheaves"]
instance isEquivalence_restriction_addCommGrp [IsAffine S.obj] :
    ((inclusion B S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (topology B S) (SmallProetale.topology B S.obj S.property)).IsEquivalence := by
  have _ : (inclusion B S).IsCoverDense (SmallProetale.topology B S.obj S.property) :=
    inclusion_isCoverDense B S
  have _ : (inclusion B S).IsDenseSubsite (topology B S)
      (SmallProetale.topology B S.obj S.property) := by
    rw [topology_eq_restricted B S]
    infer_instance
  have _ : ∀ X : (SmallProetale B S.obj S.property)ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X (inclusion B S).op) AddCommGrpCat.{u + 1} := by
    intro X
    have _ : EssentiallySmall.{u + 1} (AffineIndEtaleProetale B S) :=
      essentiallySmall.{u, u + 1} B S
    exact CategoryTheory.Limits.HasLimitsOfShape.of_essentiallySmall.{u + 1, u + 1, u,
      u + 1, u + 1, u + 2}
      (C := AddCommGrpCat.{u + 1}) (J := StructuredArrow X (inclusion B S).op)
  infer_instance

/-- An abelian sheaf on the affine ind-étale site turns a finite coproduct of the site, of index
set below the covering bound, into a product: its underlying presheaf of sets does, and the
forgetful functor reflects limits. -/
theorem sheaf_preservesProduct_addCommGrp [IsAffine S.obj]
    (F : Sheaf (topology B S) AddCommGrpCat.{u + 1})
    {I : Type (u + 1)} [Finite I] (A : I → AffineIndEtaleProetale B S)
    (hI : Cardinal.mk I ≤ B.coveringBound) :
    PreservesLimit (Discrete.functor (fun j ↦ op (A j))) F.obj := by
  have hforget : Presheaf.IsSheaf (topology B S)
      (F.obj ⋙ forget AddCommGrpCat.{u + 1}) :=
    (Presheaf.isSheaf_iff_isSheaf_forget (topology B S) F.obj
      (forget AddCommGrpCat.{u + 1})).mp F.property
  have _ := sheaf_preservesProduct.{u, u} B S ⟨F.obj ⋙ forget AddCommGrpCat.{u + 1}, hforget⟩
    A hI
  exact preservesLimit_of_reflects_of_preserves F.obj (forget AddCommGrpCat.{u + 1})

/-- At a weakly contractible object of the affine ind-étale site, sheafification of an abelian
presheaf which already takes the finite coproducts of the site to products is invertible on
sections.

A morphism of abelian groups is invertible as soon as it is bijective, and the underlying map of
the unit of sheafification is locally bijective with sheaf target, so the statement for sheaves
of sets applies to it. -/
theorem isIso_toSheafify_app_addCommGrp [IsAffine S.obj]
    (V : AffineIndEtaleProetale B S) (hV : (topology B S).IsWeaklyContractible V)
    (P : (AffineIndEtaleProetale B S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hP : ∀ {I : Type (u + 1)} [Finite I] (A : I → AffineIndEtaleProetale B S),
      Cardinal.mk I ≤ B.coveringBound →
      PreservesLimit (Discrete.functor (fun j ↦ op (A j))) P) :
    IsIso ((toSheafify (topology B S) P).app (op V)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hQ : Presheaf.IsSheaf (topology B S)
      (sheafify (topology B S) P ⋙ forget AddCommGrpCat.{u + 1}) :=
    (Presheaf.isSheaf_iff_isSheaf_forget (topology B S) (sheafify (topology B S) P)
      (forget AddCommGrpCat.{u + 1})).mp
      ((presheafToSheaf (topology B S) AddCommGrpCat.{u + 1}).obj P).property
  exact bijective_app_of_isLocallyBijective.{u, u} B S V hV
    (Functor.whiskerRight (toSheafify (topology B S) P) (forget AddCommGrpCat.{u + 1}))
    hQ inferInstance inferInstance (fun {I} _ A hbound ↦ by
      have _ := hP A hbound
      infer_instance)

end AffineIndEtaleProetale

section

variable (B : BigProetaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsAffine Z.obj] [IsAffine X.obj] [IsClosedImmersion (B.inclusion.map i)]

/-- At a weakly contractible object of the affine ind-étale site of `Z`, the sheafification in
the description of inverse image of abelian sheaves is invisible: sections of the sheafified
restriction at `V` are sections of the original sheaf at the lift of `V`, naturally in the
sheaf. -/
def affineIndEtaleSheafificationEvaluationIsoAddCommGrp (V : AffineIndEtaleProetale B Z)
    (hV : (AffineIndEtaleProetale.topology B Z).IsWeaklyContractible V) :
    (sheafToPresheaf (AffineIndEtaleProetale.topology B X) AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (affineIndEtaleLift B i).op ⋙
      presheafToSheaf (AffineIndEtaleProetale.topology B Z) AddCommGrpCat.{u + 1} ⋙
      sheafToPresheaf (AffineIndEtaleProetale.topology B Z) AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op V)) ≅
    (sheafToPresheaf (AffineIndEtaleProetale.topology B X) AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op ((affineIndEtaleLift B i).obj V))) := by
  let a := affineIndEtaleLift B i
  haveI : a.IsLeftAdjoint :=
    (Classical.choice (affineIndEtaleLift_adj_baseChange B i)).isLeftAdjoint
  refine affineIndEtaleSheafificationEvaluationIsoOfIsIso B i AddCommGrpCat.{u + 1} V
    (fun F ↦ ?_)
  refine AffineIndEtaleProetale.isIso_toSheafify_app_addCommGrp B Z V hV _ (fun Aj hbound ↦ ?_)
  have : PreservesLimit
      (Discrete.functor (((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op).obj ∘ Discrete.mk))
      F.obj :=
    AffineIndEtaleProetale.sheaf_preservesProduct_addCommGrp B X F (fun j ↦ a.obj (Aj j)) hbound
  have : PreservesLimit ((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op) F.obj :=
    preservesLimit_of_iso_diagram F.obj Discrete.natIsoFunctor.symm
  infer_instance

/-- **Stacks 09BL (2) for abelian sheaves.** At a weakly contractible affine ind-étale object of
the closed fibre, the inverse image of an abelian pro-étale sheaf is evaluation at the lift of
that object, naturally in the sheaf. -/
@[stacks 09BL "(2) for abelian sheaves: at a weakly contractible object V of Z_app the inverse \
image of an abelian sheaf is F(v(V)), for the morphism of topoi of a closed immersion of affine \
objects of a chosen big pro-etale site"]
def proetaleInverseImage_sections_iso_affineIndEtaleLiftAddCommGrp
    (V : AffineIndEtaleProetale B Z)
    (hV : (AffineIndEtaleProetale.topology B Z).IsWeaklyContractible V) :
    Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        AddCommGrpCat.{u + 1} (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property) ⋙
      sheafToPresheaf (SmallProetale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (Opposite.op ((AffineIndEtaleProetale.inclusion B Z).obj V)) ≅
    sheafToPresheaf (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj
        (Opposite.op ((AffineIndEtaleProetale.inclusion B X).obj
          ((affineIndEtaleLift B i).obj V))) := by
  let a := affineIndEtaleLift B i
  haveI : a.IsLeftAdjoint :=
    (Classical.choice (affineIndEtaleLift_adj_baseChange B i)).isLeftAdjoint
  refine proetaleInverseImage_sections_iso_affineIndEtaleLiftOfIsIso B i
    AddCommGrpCat.{u + 1} V (fun F ↦ ?_)
  refine AffineIndEtaleProetale.isIso_toSheafify_app_addCommGrp B Z V hV _ (fun Aj hbound ↦ ?_)
  have : PreservesLimit
      (Discrete.functor (((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op).obj ∘ Discrete.mk))
      F.obj :=
    AffineIndEtaleProetale.sheaf_preservesProduct_addCommGrp B X F (fun j ↦ a.obj (Aj j)) hbound
  have : PreservesLimit ((Discrete.functor (fun j ↦ op (Aj j))) ⋙ a.op) F.obj :=
    preservesLimit_of_iso_diagram F.obj Discrete.natIsoFunctor.symm
  infer_instance

end

end AlgebraicGeometry.ProEtale

end
