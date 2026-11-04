module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactRepresentables
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.LowerShriek
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.WeaklyContractibleAbelian
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.PushforwardFullyFaithful
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# A left adjoint of the pro-étale inverse image of abelian sheaves

Let `i : Z ⟶ X` be a closed immersion of affine objects of a chosen big pro-étale site. On
abelian sheaves on the small pro-étale sites the direct image `i_*` is fully faithful, the counit
`i^{-1}i_* ⟶ id` is an isomorphism, the inverse image `i^{-1}` has a left adjoint `i_!`, the unit
`id ⟶ i^{-1}i_!` is an isomorphism and `i_!` is fully faithful. These are clauses (4), (5) and
(6) of [Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL) for abelian sheaves.

The source's route is followed. Full faithfulness of the direct image needs no coefficients at
all: on the affine ind-étale sites the direct image is restriction along base change, whose left
adjoint is restriction along the fully faithful lift `v` of Stacks 09BK, and the restriction
equivalences of Stacks 098X carry this to the small pro-étale sites. The left adjoint `i_!` is
obtained from Stacks 0793: the free abelian sheaves `Z_V^#` on weakly contractible objects `V` of
`Z_app` satisfy `Mor(Z_V^#, i^{-1}F) = (i^{-1}F)(V) = F(v(V)) = Mor(Z_{v(V)}^#, F)` — the middle
equality being clause (2) for abelian sheaves — and every abelian sheaf is a quotient of a
coproduct of such `Z_V^#`, at which the partial left adjoint is therefore defined. Clause (5) for
the unit and clause (6) for `i_!` are then formal consequences in the adjoint triple
`i_! ⊣ i^{-1} ⊣ i_*`.

## Main results

* `CategoryTheory.Sheaf.freeAbelianSheaf` and
  `CategoryTheory.Sheaf.coyonedaFreeAbelianSheafIso`: the free abelian sheaf `Z_V^#` on an object
  of a site and `Mor(Z_V^#, G) = G(V)`.
* `AlgebraicGeometry.ProEtale.abelianSmallProetalePushforward_fullyFaithful` and
  `AlgebraicGeometry.ProEtale.abelianSmallProetale_isIso_counit`: **Stacks 09BL (6)** and
  **(5)** for the direct image on abelian sheaves.
* `AlgebraicGeometry.ProEtale.isRightAdjoint_abelianAffineIndEtaleSheafPullback` and
  `AlgebraicGeometry.ProEtale.isRightAdjoint_abelianSmallProetaleSheafPullback`:
  **Stacks 09BL (4)**, the existence of `i_!`.
* `AlgebraicGeometry.ProEtale.abelianSmallProetaleLowerShriek` and
  `AlgebraicGeometry.ProEtale.abelianSmallProetaleLowerShriekAdjunction`: the functor `i_!` and
  its adjunction to `i^{-1}`.
* `AlgebraicGeometry.ProEtale.abelianSmallProetaleLowerShriek_unit_isIso`: **Stacks 09BL (5)**
  for `id ⟶ i^{-1}i_!`.
* `AlgebraicGeometry.ProEtale.abelianSmallProetaleLowerShriek_fullyFaithful`:
  **Stacks 09BL (6)** for `i_!`.

## Implementation notes

The free abelian sheaf on an object is `CategoryTheory.Sheaf.composeAndSheafify` of the free
abelian group functor applied to the sheafified representable of Stacks 09YX, so that
`Mor(Z_V^#, G) = Mor(h_V^#, G)` as sets by the adjunction between the free and forgetful functors
on sheaves, and the latter is Yoneda for sheaves.

The coproduct of the free abelian sheaves indexed by the pairs `(V, s)` of a weakly contractible
object and a section of the sheaf over it is formed as the image of a coproduct of presheaves of
sets under two left adjoints, which is enough to produce the colimit cocone that
`Functor.leftAdjointObjIsDefined_of_isColimit` consumes. Its canonical map to the sheaf is
surjective on sections over every weakly contractible object — the pair `(V, s)` produces a
preimage of `s` — hence locally surjective, hence an epimorphism.

Abelian sheaves are taken in `AddCommGrpCat.{u + 1}`, the universe of the objects of the sites,
as elsewhere in this directory. The sheafification, the Stacks 098X restriction equivalence and
clause (2) at these coefficients are imported from
`StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.WeaklyContractibleAbelian`.

Everything here is for a closed immersion of **affine** objects of a chosen big pro-étale site,
which is the hypothesis of the tag. In particular it does not discharge the full-faithfulness
hypothesis of
`AlgebraicGeometry.ProEtale.shortExact_map_proetaleInverseImage`, whose direct image is that of
the unrestricted site `AlgebraicGeometry.Scheme.ProEt`: the comparison of that site with the
affine ind-étale site is not available, as set out in
`StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.BaseChange`.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 0793](https://stacks.math.columbia.edu/tag/0793)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace CategoryTheory.Sheaf

section FreeAbelianSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

/-- The free abelian sheaf `Z_V^#` on an object `V` of a site: the sheafification of the free
abelian presheaf on the representable presheaf of `V`. -/
def freeAbelianSheaf (V : C) : Sheaf J AddCommGrpCat.{max u v} :=
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ((sheafifiedYoneda J).obj V)

/-- **Yoneda for abelian sheaves.** `Mor(Z_V^#, G) = G(V)`, naturally in the abelian sheaf `G`:
the free abelian sheaf on `V` is left adjoint to the forgetful functor applied to Yoneda for
sheaves of sets. -/
def coyonedaFreeAbelianSheafIso (V : C) :
    coyoneda.obj (op (freeAbelianSheaf J V)) ≅
      (sheafSections J AddCommGrpCat.{max u v}).obj (op V) ⋙
        forget AddCommGrpCat.{max u v} :=
  (Adjunction.compCoyonedaIso (Sheaf.adjunction J AddCommGrpCat.adj)).app
      (op ((sheafifiedYoneda J).obj V)) ≪≫
    Functor.isoWhiskerLeft (sheafCompose J (forget AddCommGrpCat.{max u v}))
      (coyonedaSheafifiedYonedaIso J V)

end FreeAbelianSheaf

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]

/-- The direct image on the affine ind-étale sites of a closed immersion of affine schemes is
fully faithful, for sheaves with values in an arbitrary category: it is restriction along base
change, whose left adjoint is restriction along the fully faithful lift of Stacks 09BK. -/
def affineIndEtaleBaseChangePushforward_fullyFaithful (A : Type w) [Category.{w'} A] :
    ((affineIndEtaleBaseChange B i).sheafPushforwardContinuous A
      (AffineIndEtaleProetale.topology B X)
      (AffineIndEtaleProetale.topology B Z)).FullyFaithful := by
  haveI : (affineIndEtaleBaseChange B i).IsContinuous
      (AffineIndEtaleProetale.topology B X) (AffineIndEtaleProetale.topology B Z) :=
    affineIndEtaleBaseChange_isContinuous B i
  have hl := Classical.choice (affineIndEtaleLift_fullyFaithful B i)
  haveI : (affineIndEtaleLift B i).Full := hl.full
  haveI : (affineIndEtaleLift B i).Faithful := hl.faithful
  exact Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint A (affineIndEtaleBaseChange B i)
    (Classical.choice (affineIndEtaleLift_adj_baseChange B i))
    (AffineIndEtaleProetale.topology B X) (AffineIndEtaleProetale.topology B Z)

/-- **Stacks 09BL (4), the generators.** At a weakly contractible object `V` of the affine
ind-étale site of `Z`, the partial left adjoint of the inverse image of abelian sheaves is
defined at the free abelian sheaf `Z_V^#`, with value `Z_{v(V)}^#`:
`Mor(Z_V^#, i^{-1}F) = (i^{-1}F)(V) = F(v(V)) = Mor(Z_{v(V)}^#, F)`, the middle equality being
Stacks 09BL (2) for abelian sheaves. -/
theorem leftAdjointObjIsDefined_freeAbelianSheaf (V : AffineIndEtaleProetale B Z)
    (hV : (AffineIndEtaleProetale.topology B Z).IsWeaklyContractible V) :
    (Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        AddCommGrpCat.{u + 1} (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z)).leftAdjointObjIsDefined
      (Sheaf.freeAbelianSheaf (AffineIndEtaleProetale.topology B Z) V) := by
  have e₂ : Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        AddCommGrpCat.{u + 1} (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) ⋙
      (sheafSections (AffineIndEtaleProetale.topology B Z) AddCommGrpCat.{u + 1}).obj (op V) ≅
      (sheafSections (AffineIndEtaleProetale.topology B X) AddCommGrpCat.{u + 1}).obj
        (op ((affineIndEtaleLift B i).obj V)) :=
    Functor.isoWhiskerRight
        (affineIndEtaleSheafPullbackIsoLiftOfCategory B i AddCommGrpCat.{u + 1}) _ ≪≫
      affineIndEtaleSheafificationEvaluationIsoAddCommGrp B i V hV
  have e : Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        AddCommGrpCat.{u + 1} (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) ⋙
      coyoneda.obj (op (Sheaf.freeAbelianSheaf (AffineIndEtaleProetale.topology B Z) V)) ≅
      coyoneda.obj (op (Sheaf.freeAbelianSheaf (AffineIndEtaleProetale.topology B X)
        ((affineIndEtaleLift B i).obj V))) :=
    Functor.isoWhiskerLeft _
        (Sheaf.coyonedaFreeAbelianSheafIso (AffineIndEtaleProetale.topology B Z) V) ≪≫
      Functor.isoWhiskerRight e₂ (forget AddCommGrpCat.{u + 1}) ≪≫
      (Sheaf.coyonedaFreeAbelianSheafIso (AffineIndEtaleProetale.topology B X)
        ((affineIndEtaleLift B i).obj V)).symm
  rw [Functor.leftAdjointObjIsDefined_iff]
  exact corepresentable_of_natIso _ e.symm

/-! ### Every abelian sheaf is a quotient of free abelian sheaves on weakly contractible objects -/

/-- The index type of the canonical presentation of an abelian sheaf `Y` on the affine ind-étale
site of `Z`: pairs `(V, s)` of a weakly contractible object `V` and a section of `Y` over `V`. -/
abbrev abelianPresentationIndex
    (Y : Sheaf (AffineIndEtaleProetale.topology B Z) AddCommGrpCat.{u + 1}) :=
  Σ V : ObjectProperty.FullSubcategory
      ((AffineIndEtaleProetale.topology B Z).IsWeaklyContractible :
        ObjectProperty (AffineIndEtaleProetale B Z)),
    ToType (Y.obj.obj (op V.obj))

/-- Every abelian sheaf on the affine ind-étale site of `Z` is a quotient of a coproduct of free
abelian sheaves on weakly contractible objects, at each of which the partial left adjoint of the
inverse image is defined by `leftAdjointObjIsDefined_freeAbelianSheaf`.

The coproduct is over the pairs `(V, s)` of a weakly contractible object and a section over it,
and the canonical map is surjective on sections over every weakly contractible object — the pair
`(V, s)` itself produces a preimage of `s` — hence locally surjective, hence an epimorphism. -/
theorem exists_epi_leftAdjointObjIsDefined_abelian
    (Y : Sheaf (AffineIndEtaleProetale.topology B Z) AddCommGrpCat.{u + 1}) :
    ∃ (P : Sheaf (AffineIndEtaleProetale.topology B Z) AddCommGrpCat.{u + 1}) (p : P ⟶ Y),
      Epi p ∧ (Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        AddCommGrpCat.{u + 1} (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z)).leftAdjointObjIsDefined P := by
  classical
  have : HasColimitsOfShape (Discrete (abelianPresentationIndex B Y))
      (Sheaf (AffineIndEtaleProetale.topology B X) AddCommGrpCat.{u + 1}) :=
    ⟨fun _ ↦ HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
  let Dpsh : Discrete (abelianPresentationIndex B Y) ⥤
      ((AffineIndEtaleProetale B Z)ᵒᵖ ⥤ Type (u + 1)) :=
    Discrete.functor (fun j ↦ uliftYoneda.{u + 1}.obj j.1.obj)
  let F₁ := presheafToSheaf (AffineIndEtaleProetale.topology B Z) (Type (u + 1))
  let F₂ := Sheaf.composeAndSheafify (AffineIndEtaleProetale.topology B Z)
    AddCommGrpCat.free.{u + 1}
  have : PreservesColimits F₁ :=
    (sheafificationAdjunction (AffineIndEtaleProetale.topology B Z)
      (Type (u + 1))).leftAdjoint_preservesColimits
  have : PreservesColimits F₂ :=
    (Sheaf.adjunction (AffineIndEtaleProetale.topology B Z)
      AddCommGrpCat.adj.{u + 1}).leftAdjoint_preservesColimits
  let c₂ := (F₁ ⋙ F₂).mapCocone (colimit.cocone Dpsh)
  have hc₂ : IsColimit c₂ := isColimitOfPreserves (F₁ ⋙ F₂) (colimit.isColimit Dpsh)
  let e : ∀ W : AffineIndEtaleProetale B Z,
      coyoneda.obj (op (Sheaf.freeAbelianSheaf (AffineIndEtaleProetale.topology B Z) W)) ≅
        (sheafSections (AffineIndEtaleProetale.topology B Z) AddCommGrpCat.{u + 1}).obj (op W) ⋙
          forget AddCommGrpCat.{u + 1} :=
    fun W ↦ Sheaf.coyonedaFreeAbelianSheafIso (AffineIndEtaleProetale.topology B Z) W
  let π : c₂.pt ⟶ Y :=
    hc₂.desc ⟨Y, Discrete.natTrans (fun j ↦ (e j.as.1.obj).inv.app Y j.as.2)⟩
  refine ⟨c₂.pt, π, ?_, ?_⟩
  · have hsurj : ∀ ⦃W : AffineIndEtaleProetale B Z⦄,
        (AffineIndEtaleProetale.topology B Z).IsWeaklyContractible W →
        Function.Surjective (π.hom.app (op W)) := by
      intro W hW t
      let α : Sheaf.freeAbelianSheaf (AffineIndEtaleProetale.topology B Z) W ⟶ c₂.pt :=
        c₂.ι.app (Discrete.mk ⟨⟨W, hW⟩, t⟩)
      refine ⟨(e W).hom.app c₂.pt α, ?_⟩
      have hfac : (coyoneda.obj (op (Sheaf.freeAbelianSheaf
          (AffineIndEtaleProetale.topology B Z) W))).map π α = (e W).inv.app Y t :=
        hc₂.fac _ (Discrete.mk ⟨⟨W, hW⟩, t⟩)
      have hnat := (e W).hom.naturality_apply π α
      rw [hfac] at hnat
      simpa using hnat.symm
    have h₁ : Presheaf.IsLocallySurjective (AffineIndEtaleProetale.topology B Z) π.hom :=
      Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective
        (AffineIndEtaleProetale.topology B Z) π.hom
        (affineIndEtaleProetale_hasEnough_weaklyContractible B Z) hsurj
    have : Sheaf.IsLocallySurjective π :=
      ⟨fun s ↦ h₁.imageSieve_mem s⟩
    exact (Sheaf.isLocallySurjective_iff_epi' (φ := π)).mp inferInstance
  · exact Functor.leftAdjointObjIsDefined_of_isColimit hc₂
      (fun j ↦ leftAdjointObjIsDefined_freeAbelianSheaf B i j.as.1.obj j.as.1.property)

/-- **Stacks 09BL (6) for the direct image on abelian sheaves.** For a closed immersion of
affine schemes the direct image `i_*` on abelian sheaves on the small pro-étale sites is fully
faithful. -/
@[stacks 09BL "(6), full faithfulness of the direct image i_* on abelian sheaves, for the small \
pro-etale sites of a closed immersion of affine objects of a chosen big pro-etale site"]
def abelianSmallProetalePushforward_fullyFaithful :
    ((smallProetaleBaseChange B Z X i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property)).FullyFaithful := by
  haveI : (smallProetaleBaseChange B Z X i).IsContinuous
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B Z X i).toIsContinuous
  haveI : (affineIndEtaleBaseChange B i).IsContinuous
      (AffineIndEtaleProetale.topology B X) (AffineIndEtaleProetale.topology B Z) :=
    affineIndEtaleBaseChange_isContinuous B i
  exact Functor.fullyFaithful_rightAdjoint_of_isoCompEquivalence
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallProetaleBaseChange B Z X i) AddCommGrpCat.{u + 1}
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (affineIndEtaleBaseChange B i) AddCommGrpCat.{u + 1}
      (AffineIndEtaleProetale.topology B X)
      (AffineIndEtaleProetale.topology B Z))
    _ _ (affineIndEtaleSheafPullbackRestrictionIsoOfCategory B i AddCommGrpCat.{u + 1})
    (affineIndEtaleBaseChangePushforward_fullyFaithful B i AddCommGrpCat.{u + 1})

/-- **Stacks 09BL (5) for the direct image on abelian sheaves.** For a closed immersion of
affine schemes the counit `i^{-1} i_* ⟶ id` on abelian sheaves on the small pro-étale sites is
an isomorphism, its right adjoint `i_*` being fully faithful. -/
@[stacks 09BL "(5), the map i^{-1} i_* -> id is an isomorphism on abelian sheaves, for the small \
pro-etale sites of a closed immersion of affine objects of a chosen big pro-etale site"]
theorem abelianSmallProetale_isIso_counit :
    IsIso (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallProetaleBaseChange B Z X i) AddCommGrpCat.{u + 1}
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property)).counit := by
  have : (smallProetaleBaseChange B Z X i).IsContinuous
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B Z X i).toIsContinuous
  have hff := abelianSmallProetalePushforward_fullyFaithful B i
  have := hff.full
  have := hff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

/-! ### The left adjoint `i_!` on abelian sheaves -/

/-- **Stacks 09BL (4) on the affine ind-étale sites.** The inverse image of abelian sheaves along
base change of the affine ind-étale pro-étale sites has a left adjoint.

This is Stacks 0793 applied to the family of free abelian sheaves on weakly contractible
objects: every abelian sheaf is a quotient of a coproduct of those
(`exists_epi_leftAdjointObjIsDefined_abelian`) and the partial left adjoint is defined at each
such coproduct. -/
instance isRightAdjoint_abelianAffineIndEtaleSheafPullback :
    (Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
      AddCommGrpCat.{u + 1} (AffineIndEtaleProetale.topology B X)
      (AffineIndEtaleProetale.topology B Z)).IsRightAdjoint := by
  refine isRightAdjoint_of_partialAdjointData _
    {P | ((Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
      AddCommGrpCat.{u + 1} (AffineIndEtaleProetale.topology B X)
      (AffineIndEtaleProetale.topology B Z)) ⋙ coyoneda.obj (op P)).IsCorepresentable} ?_ ?_
  · intro Y
    obtain ⟨P, p, hp, hP⟩ := exists_epi_leftAdjointObjIsDefined_abelian B i Y
    exact ⟨P, hP, p, hp⟩
  · intro P hP
    obtain ⟨Q, ⟨ee⟩⟩ := hP.has_corepresentation
    exact ⟨Q, ⟨ee.toIso⟩⟩

/-- **Stacks 09BL (4).** The inverse image `i^{-1}` on abelian sheaves on the small pro-étale
sites of a closed immersion of affine schemes has a left adjoint `i_!`. -/
@[stacks 09BL "(4), the inverse image i^{-1} : Ab(X_proetale) -> Ab(Z_proetale) of a closed \
immersion of affine objects of a chosen big pro-etale site has a left adjoint i_!"]
instance isRightAdjoint_abelianSmallProetaleSheafPullback :
    (Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
      AddCommGrpCat.{u + 1} (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_isoCompEquivalence _ _ _ _
    (affineIndEtaleSheafPullbackRestrictionIsoOfCategory B i AddCommGrpCat.{u + 1})

/-- **Stacks 09BL (4), the functor.** The left adjoint `i_!` of the inverse image on abelian
sheaves on the small pro-étale sites of a closed immersion of affine schemes. -/
def abelianSmallProetaleLowerShriek :
    Sheaf (SmallProetale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  (Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
    AddCommGrpCat.{u + 1} (SmallProetale.topology B X.obj X.property)
    (SmallProetale.topology B Z.obj Z.property)).leftAdjoint

/-- The adjunction `i_! ⊣ i^{-1}` of Stacks 09BL (4). -/
def abelianSmallProetaleLowerShriekAdjunction :
    abelianSmallProetaleLowerShriek B i ⊣
      Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        AddCommGrpCat.{u + 1} (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property) :=
  Adjunction.ofIsRightAdjoint _

/-- The adjoint triple `i_! ⊣ i^{-1} ⊣ i_*` on abelian sheaves on the small pro-étale sites. -/
def abelianSmallProetaleLowerShriekTriple :
    Adjunction.Triple (abelianSmallProetaleLowerShriek B i)
      (Functor.sheafPullbackConstruction.sheafPullback (smallProetaleBaseChange B Z X i)
        AddCommGrpCat.{u + 1} (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property))
      ((smallProetaleBaseChange B Z X i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property)) where
  adj₁ := abelianSmallProetaleLowerShriekAdjunction B i
  adj₂ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallProetaleBaseChange B Z X i) AddCommGrpCat.{u + 1}
    (SmallProetale.topology B X.obj X.property)
    (SmallProetale.topology B Z.obj Z.property)

/-- **Stacks 09BL (5), the unit of lower shriek on abelian sheaves.** For a closed immersion of
affine schemes the unit `id ⟶ i^{-1} i_!` of the adjunction `i_! ⊣ i^{-1}` on abelian sheaves on
the small pro-étale sites is an isomorphism.

In the adjoint triple `i_! ⊣ i^{-1} ⊣ i_*` the unit of the left adjunction is invertible exactly
when the counit of the right one is, and the latter is
`abelianSmallProetale_isIso_counit`. -/
@[stacks 09BL "(5), the map id -> i^{-1} i_! is an isomorphism, for abelian sheaves on the small \
pro-etale sites of a closed immersion of affine objects of a chosen big pro-etale site"]
theorem abelianSmallProetaleLowerShriek_unit_isIso :
    IsIso (abelianSmallProetaleLowerShriekAdjunction B i).unit :=
  (abelianSmallProetaleLowerShriekTriple B i).isIso_unit_iff_isIso_counit.mpr
    (abelianSmallProetale_isIso_counit B i)

/-- **Stacks 09BL (6) for lower shriek on abelian sheaves.** For a closed immersion of affine
schemes the left adjoint `i_!` of the inverse image on abelian sheaves on the small pro-étale
sites is fully faithful. -/
@[stacks 09BL "(6), full faithfulness of i_!, for abelian sheaves on the small pro-etale sites \
of a closed immersion of affine objects of a chosen big pro-etale site"]
def abelianSmallProetaleLowerShriek_fullyFaithful :
    (abelianSmallProetaleLowerShriek B i).FullyFaithful :=
  (abelianSmallProetaleLowerShriekTriple B i).fullyFaithfulEquiv.symm
    (abelianSmallProetalePushforward_fullyFaithful B i)

end AlgebraicGeometry.ProEtale

end
