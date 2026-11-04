module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekAbelianExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekExact

/-!
# The comparison of global sections along `f_cris`

Let `f : X' ⟶ X` be a morphism of the global crystalline situations of [Stacks, Tag 07I5], so
that `f_{cris, *} : Ab(Cris(X'/S)) ⥤ Ab(Cris(X/S))` is the abelian direct image of
[Stacks, Tag 07IK].  This file proves

`Γ(Cris(X/S), f_{cris, *} -) ≅ Γ(Cris(X'/S), -)`,

the comparison of underlying global sections along `f_cris`.  It is the one input the Leray
factorization `Crystalline.GlobalCrystallineSituation.SmallSite.derivedCrisGlobalSectionsIso` of
`SmallSite/AlphaPCoverTriangle.lean` still carried as a datum, there named
`...SmallSite.CrisGlobalSectionsComparison`; `crisGlobalSectionsIso` below is a term of that
type, proved unconditionally for every morphism of global crystalline situations.

As in `SmallSite/CrisDirectImage.lean`, the orientation of the variables is that `S` is the
*source* situation `X'/S` and `S'` the *target* situation `X/S`, so `fX : S.X ⟶ S'.X` is the
morphism `f : X' ⟶ X` and `crisDirectImage S S' fS fX hf` is `f_{cris, *}`.

## The three factors

`f_{cris, *}` is the composite `π_{X', *} ∘ f_{CRIS, *} ∘ i_{X, *}` of
`Crystalline.GlobalCrystallineSituation.SmallSite.crisDirectImage`, and the comparison splits
accordingly into three isomorphisms.

Two of the three are the argument of
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiGlobalSectionsDirectImageIso`, carried
over verbatim.  The direct image along a cocontinuous functor of sites is, on underlying
presheaves, the right Kan extension of [Stacks, Tag 00XK]; global sections are the limit of the
underlying presheaf, `CategoryTheory.Sheaf.ΓNatIsoLim`; and the limit of a right Kan extension
is the limit of the functor extended, `CategoryTheory.Functor.ranCompLimIso`.  That gives
`bigDirectImageGlobalSectionsIso` for the inclusion `i_X : Cris(X'/S) ⥤ CRIS(X'/S)` and
`changeBaseDirectImageGlobalSectionsIso` for change of divided power base.

The third factor is restriction `π_{X', *} = i_{X'}^{-1}` to the small crystalline site, which is
*not* a Kan extension, so that argument says nothing about it.  What has to be proved is
`smallRestrictionGlobalSectionsIso`:

`Γ(Cris(X/S), i_X^{-1} -) ≅ Γ(CRIS(X/S), -)`.

## The restriction factor

Read through `CategoryTheory.Sheaf.ΓNatIsoLim` on both sides, the comparison is the canonical
`CategoryTheory.Limits.limit.pre` along `i_X^{op}`: the assertion is that the limit of (the
presheaf underlying) a sheaf on `CRIS(X/S)` is already computed over the full subcategory
`Cris(X/S)`.  For *presheaves* this is false — it would say that `i_X` is cofinal, and there is
in general no morphism at all from an object of `Cris(X/S)` to a given object of `CRIS(X/S)`.
For sheaves it holds, and the two halves of `isIso_limitPre_ι` are exactly the two things the
small site contributes.

*Separatedness.*  Two maps into `Γ(CRIS(X/S), ℱ)` agreeing on every object of `Cris(X/S)` agree,
because those objects cover the final object of the topos of `CRIS(X/S)`.  That covering is the
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.coversTop_ι`, the step
[Stacks, Tag 07IJ] omits in general, and the implication is Mathlib's
`CategoryTheory.GrothendieckTopology.CoversTop.ext`.

*Gluing.*  A point of `Γ(Cris(X/S), i_X^{-1}ℱ)` — concretely, the cone of projections out of the
limit over `Cris(X/S)` — is a compatible family of elements of the sheaf of types
`B ↦ Hom(L, ℱ(B))` on the objects of `Cris(X/S)`, in the sense of
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`.  Compatibility is
`restrictionFamily_isCompatible`: two morphisms `B ⟶ i_X(A)` and `B ⟶ i_X(A')` out of an object
of `CRIS(X/S)` factor through a common object of `Cris(X/S)`, because `Cris(X/S)` has products
of pairs and equalizers which `i_X` preserves — [Stacks, Tag 07I9], in the form
`Stacks.Sites.LowerShriek.isCofilteredOrEmpty_of_products_equalizers` applied to the
structured-arrow category.  The same covering then amalgamates the family to a cone on all of
`CRIS(X/S)`, by `...FamilyOfElementsOnObjects.IsCompatible.section_`, and that cone is the
inverse.

So the restriction factor needs no statement about the abelian lower shriek `i_{X, !}` and no
constant-sheaf computation: the covering statement is applied to the sheaf itself rather than to
`ℤ`, and the filteredness of [Stacks, Tag 00X6] enters only through the elementary
`isCofilteredOrEmpty_of_products_equalizers`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bigGlobalSections` — the global sections functor `Γ(CRIS(X/S), -)` of abelian sheaves on the
  big crystalline site.
* `smallRestrictionGlobalSectionsIso` — **`Γ(Cris(X/S), i_X^{-1}ℱ) ≅ Γ(CRIS(X/S), ℱ)`.**
* `bigDirectImageGlobalSectionsIso` — `Γ(CRIS(X/S), i_{X, *}ℱ) ≅ Γ(Cris(X/S), ℱ)`.
* `changeBaseDirectImageGlobalSectionsIso` — `Γ(CRIS(X'/S'), f_{CRIS, *}ℱ) ≅ Γ(CRIS(X/S), ℱ)`.
* `crisGlobalSectionsIso` — **`Γ(Cris(X/S), f_{cris, *}ℱ) ≅ Γ(Cris(X'/S), ℱ)`**, the composite
  of the three, and a term of the type
  `Crystalline.GlobalCrystallineSituation.SmallSite.CrisGlobalSectionsComparison`.

## Main results

* `isIso_limitPre_ι` — **the limit of an abelian sheaf on `CRIS(X/S)` is computed over
  `Cris(X/S)`**: the canonical map `limit ℱ ⟶ limit (i_X^{op} ⋙ ℱ)` is invertible.
* `restrictionFamily_isCompatible` — the projections out of the limit over `Cris(X/S)` form a
  compatible family of elements on the objects of `Cris(X/S)`.
* `isCofilteredOrEmpty_structuredArrow_ι` — the objects of `Cris(X/S)` under a fixed object of
  `CRIS(X/S)` form a cofiltered-or-empty category.

## What is and is not proved

The comparison is proved unconditionally, for every morphism of global crystalline situations,
with no affineness hypothesis and no appeal to [Stacks, Tag 07HP]; the only geometric input is
`coversTop_ι`.  Each of the three factors is the canonical comparison — the Kan extension
counit for the two cocontinuous ones, `limit.pre` for the restriction — so the composite is the
canonical map and not merely some isomorphism between the two functors.

The coefficients are abelian groups at the universe `u + 1` throughout, as everywhere in this
chapter; see the module documentation of `SmallSite/CrisDirectImage.lean` for why a
module-valued `f_{cris, *}` does not exist here, and `SmallSite/Cohomology.lean` for why `u + 1`
is the smallest coefficient universe available.  Nothing here is a statement about cohomology in
positive degree: the consequence for `RΓ` is `derivedCrisGlobalSectionsIso` of
`SmallSite/AlphaPCoverTriangle.lean`, which consumes this comparison together with the
preservation of injectives proved there.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Global sections on the big crystalline site -/

section Big

variable (S : GlobalCrystallineSituation.{u})

/-- **The global sections functor `Γ(CRIS(X/S), -)` of abelian sheaves on the big crystalline
site**, Mathlib's right adjoint of the constant sheaf functor, at the coefficient universe of the
small crystalline side.  This is the companion of
`Crystalline.GlobalCrystallineSituation.SmallSite.globalSections`; it exists because
`AddCommGrpCat.{u + 1}` has limits indexed by `CRIS(X/S)ᵒᵖ`, whose objects form a `Type (u + 1)`
and whose morphisms form a `Type u`. -/
abbrev bigGlobalSections :
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.Γ (topology S) AddCommGrpCat.{u + 1}

end Big

/-! ### Global sections and restriction to the small site -/

section Restriction

variable (S : GlobalCrystallineSituation.{u})

/-- **Two morphisms out of an object of `CRIS(X/S)` into objects of `Cris(X/S)` factor through a
common object of `Cris(X/S)`**: the category of objects of the small crystalline site under a
fixed object of the big one is cofiltered-or-empty.

This is [Stacks, Tag 07I9] for the small site in the form [Stacks, Tag 00X6] uses it:
`Cris(X/S)` has products of pairs and equalizers, which the inclusion preserves, so the
structured-arrow category has them too and
`Stacks.Sites.LowerShriek.isCofilteredOrEmpty_of_products_equalizers` applies.  It is the same
filteredness that makes the abelian `i_{X, !}` exact in
`SmallSite/LowerShriekAbelianExact.lean`, used here on the sheaf itself instead. -/
theorem isCofilteredOrEmpty_structuredArrow_ι (A : Thickening S) :
    IsCofilteredOrEmpty (StructuredArrow A (CrystallineThickening.ι S)) :=
  have : HasBinaryProducts (CrystallineThickening S) := inferInstance
  have : HasEqualizers (CrystallineThickening S) :=
    CrystallineThickening.hasEqualizers_crystallineThickening S
  have : PreservesLimitsOfShape (Discrete WalkingPair) (CrystallineThickening.ι S) :=
    inferInstance
  have : PreservesLimitsOfShape WalkingParallelPair (CrystallineThickening.ι S) :=
    CrystallineThickening.ι_preservesEqualizers S
  Stacks.Sites.LowerShriek.isCofilteredOrEmpty_of_products_equalizers _

variable {S}

/-- **The projections out of the limit of an abelian sheaf over the small crystalline site**, read
as a family of elements indexed by the objects of `Cris(X/S)` of the sheaf of *types*
`B ↦ Hom(Γ(Cris(X/S), i_X^{-1}ℱ), ℱ(B))` on `CRIS(X/S)`.  Amalgamating this family is what
produces the inverse of the comparison of global sections. -/
def restrictionFamily (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    Presheaf.FamilyOfElementsOnObjects
      (sheafOver G (limit ((CrystallineThickening.ι S).op ⋙ G.obj))).obj
      (CrystallineThickening.ι S).obj :=
  fun A ↦ limit.π ((CrystallineThickening.ι S).op ⋙ G.obj) (op A)

/-- **The family of projections is compatible.**  Given an object `Z` of `CRIS(X/S)` and two
morphisms from it to objects of `Cris(X/S)`, both factor through a single object of `Cris(X/S)`
by `isCofilteredOrEmpty_structuredArrow_ι`, and the two restrictions then agree because both are
the projection at that object followed by the same map. -/
theorem restrictionFamily_isCompatible (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    (restrictionFamily G).IsCompatible := by
  intro Z i j f g
  obtain ⟨W, a, b, -⟩ := (isCofilteredOrEmpty_structuredArrow_ι S Z).cone_objs
    (StructuredArrow.mk f) (StructuredArrow.mk g)
  have hf' : W.hom ≫ (CrystallineThickening.ι S).map a.right = f := StructuredArrow.w a
  have hg' : W.hom ≫ (CrystallineThickening.ι S).map b.right = g := StructuredArrow.w b
  have key : ∀ {k : CrystallineThickening S} (c : W.right ⟶ k),
      limit.π ((CrystallineThickening.ι S).op ⋙ G.obj) (op k) ≫
        G.obj.map ((CrystallineThickening.ι S).map c).op =
      limit.π ((CrystallineThickening.ι S).op ⋙ G.obj) (op W.right) := fun c ↦
    limit.w ((CrystallineThickening.ι S).op ⋙ G.obj) c.op
  show limit.π ((CrystallineThickening.ι S).op ⋙ G.obj) (op i) ≫ G.obj.map f.op =
    limit.π ((CrystallineThickening.ι S).op ⋙ G.obj) (op j) ≫ G.obj.map g.op
  rw [← hf', ← hg', op_comp, op_comp, G.obj.map_comp, G.obj.map_comp,
    ← Category.assoc, ← Category.assoc, key (k := i) a.right, key (k := j) b.right]

/-- **The compatible family of projections extends to all of `CRIS(X/S)`.**  The objects of
`Cris(X/S)` cover the final object of the topos of `CRIS(X/S)`, so
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.section_` glues the family to a
global section of the sheaf of types `B ↦ Hom(Γ(Cris(X/S), i_X^{-1}ℱ), ℱ(B))`. -/
def restrictionSection (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    (sheafOver G (limit ((CrystallineThickening.ι S).op ⋙ G.obj))).obj.sections :=
  (restrictionFamily_isCompatible G).section_ (CrystallineThickening.coversTop_ι S)
    (sheafOver G _).property

/-- The value of `restrictionSection` at an object `B` of `CRIS(X/S)`, as a morphism from the
limit over `Cris(X/S)` to the sections of the sheaf over `B`. -/
def restrictionConeπ (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (B : (Thickening S)ᵒᵖ) :
    limit ((CrystallineThickening.ι S).op ⋙ G.obj) ⟶ G.obj.obj B :=
  (restrictionSection G).1 B

/-- The values of `restrictionSection` are compatible with restriction in `CRIS(X/S)`, being the
components of a section of a presheaf. -/
theorem restrictionConeπ_naturality (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    {B B' : (Thickening S)ᵒᵖ} (h : B ⟶ B') :
    restrictionConeπ G B ≫ G.obj.map h = restrictionConeπ G B' :=
  (restrictionSection G).2 h

/-- At an object of `Cris(X/S)` the glued section is the projection it was glued from. -/
theorem restrictionConeπ_ι (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (A : CrystallineThickening S) :
    restrictionConeπ G (op ((CrystallineThickening.ι S).obj A)) =
      limit.π ((CrystallineThickening.ι S).op ⋙ G.obj) (op A) :=
  (restrictionFamily_isCompatible G).section_apply (CrystallineThickening.coversTop_ι S)
    (sheafOver G _).property A

/-- **The limit over `Cris(X/S)` of an abelian sheaf on `CRIS(X/S)`, as a cone over the whole big
crystalline site.**  Its legs are the glued sections of `restrictionSection`. -/
def restrictionCone (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) : Cone G.obj where
  pt := limit ((CrystallineThickening.ι S).op ⋙ G.obj)
  π :=
    { app := fun B ↦ restrictionConeπ G B
      naturality := fun _ _ h ↦
        (Category.id_comp _).trans (restrictionConeπ_naturality G h).symm }

/-- **The inverse of the comparison of limits**, the map from the limit of an abelian sheaf over
`Cris(X/S)` to its limit over `CRIS(X/S)` induced by `restrictionCone`. -/
def restrictionInv (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    limit ((CrystallineThickening.ι S).op ⋙ G.obj) ⟶ limit G.obj :=
  limit.lift G.obj (restrictionCone G)

/-- Composing `restrictionInv` with the projection of the limit over `CRIS(X/S)` at an object of
`Cris(X/S)` gives the projection of the limit over `Cris(X/S)` at that object. -/
@[reassoc (attr := simp)]
theorem restrictionInv_π (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (A : CrystallineThickening S) :
    restrictionInv G ≫ limit.π G.obj (op ((CrystallineThickening.ι S).obj A)) =
      limit.π ((CrystallineThickening.ι S).op ⋙ G.obj) (op A) :=
  (limit.lift_π (restrictionCone G) (op ((CrystallineThickening.ι S).obj A))).trans
    (restrictionConeπ_ι G A)

/-- **The limit of an abelian sheaf on `CRIS(X/S)` is already computed over `Cris(X/S)`:** the
canonical comparison `limit ℱ ⟶ limit (i_X^{op} ⋙ ℱ)` is invertible.

Its inverse is `restrictionInv`.  One composite is the identity because the projections of the
limit over `Cris(X/S)` characterize a map into it, the other because the objects of `Cris(X/S)`
cover the final object of the topos of `CRIS(X/S)` — `coversTop_ι` through
`CategoryTheory.GrothendieckTopology.CoversTop.ext`.  The statement fails for presheaves: it
would say that the inclusion is cofinal, and in general no object of `Cris(X/S)` receives a
morphism from a given object of `CRIS(X/S)` at all. -/
instance isIso_limitPre_ι (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) :
    IsIso (limit.pre G.obj (CrystallineThickening.ι S).op) := by
  refine ⟨restrictionInv G, ?_, ?_⟩
  · refine (CrystallineThickening.coversTop_ι S).ext G (limit.isLimit G.obj) fun A ↦ ?_
    show (limit.pre G.obj (CrystallineThickening.ι S).op ≫ restrictionInv G) ≫
      limit.π G.obj (op ((CrystallineThickening.ι S).obj A)) = _
    rw [Category.assoc, restrictionInv_π, limit.pre_π, Category.id_comp]
    rfl
  · refine limit.hom_ext fun A ↦ ?_
    rw [Category.assoc, limit.pre_π, Category.id_comp]
    exact restrictionInv_π G A.unop

/-- The isomorphism of `isIso_limitPre_ι`, naturally in the abelian sheaf: taking the limit of
the underlying presheaf over `CRIS(X/S)` is taking it over `Cris(X/S)` after restriction. -/
def restrictionLimIso :
    sheafToPresheaf (topology S) AddCommGrpCat.{u + 1} ⋙ lim ≅
      smallRestriction S ⋙ sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙ lim :=
  NatIso.ofComponents (fun G ↦ @asIso _ _ _ _ _ (isIso_limitPre_ι G)) (by
    intro G H φ
    refine limit.hom_ext fun A ↦ ?_
    show (limMap φ.hom ≫ limit.pre H.obj (CrystallineThickening.ι S).op) ≫
        limit.π ((CrystallineThickening.ι S).op ⋙ H.obj) A =
      (limit.pre G.obj (CrystallineThickening.ι S).op ≫
        limMap (Functor.whiskerLeft (CrystallineThickening.ι S).op φ.hom)) ≫
        limit.π ((CrystallineThickening.ι S).op ⋙ H.obj) A
    simp)

/-- **`Γ(Cris(X/S), i_X^{-1}ℱ) ≅ Γ(CRIS(X/S), ℱ)`**, naturally in the abelian sheaf `ℱ` on the big
crystalline site: restricting to the small crystalline site loses no global section.

Both sides are limits of the underlying presheaf, by `CategoryTheory.Sheaf.ΓNatIsoLim`, and the
comparison between the two limits is invertible by `isIso_limitPre_ι`.  This is the factor of the
comparison along `f_cris` that the Kan extension argument of
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiGlobalSectionsDirectImageIso` does not
reach, restriction along the inclusion being a right adjoint for the *other* adjunction. -/
def smallRestrictionGlobalSectionsIso :
    smallRestriction S ⋙ globalSections S ≅ bigGlobalSections S :=
  Functor.isoWhiskerLeft (smallRestriction S)
      (Sheaf.ΓNatIsoLim (smallTopology S) AddCommGrpCat.{u + 1}) ≪≫
    (restrictionLimIso (S := S)).symm ≪≫
    (Sheaf.ΓNatIsoLim (topology S) AddCommGrpCat.{u + 1}).symm

end Restriction

/-! ### Global sections and the two cocontinuous direct images -/

section Cocontinuous

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **`Γ(CRIS(X/S), i_{X, *}ℱ) ≅ Γ(Cris(X/S), ℱ)`**, naturally in the abelian sheaf `ℱ` on the
small crystalline site.

The inclusion `Cris(X/S) ⥤ CRIS(X/S)` is cocontinuous, so the presheaf underlying `i_{X, *}ℱ` is
the right Kan extension of that of `ℱ` along it, [Stacks, Tag 00XK]; the limit of a right Kan
extension is the limit of the functor extended, `CategoryTheory.Functor.ranCompLimIso`; and
global sections are that limit, `CategoryTheory.Sheaf.ΓNatIsoLim`.  This is the argument of
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiGlobalSectionsDirectImageIso` with the
forgetful functor of [Stacks, Tag 07IH] replaced by the inclusion. -/
def bigDirectImageGlobalSectionsIso :
    bigDirectImage S ⋙ bigGlobalSections S ≅ globalSections S :=
  Functor.isoWhiskerLeft (bigDirectImage S)
      (Sheaf.ΓNatIsoLim (topology S) AddCommGrpCat.{u + 1}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((CrystallineThickening.ι S).sheafPushforwardCocontinuousCompSheafToPresheafIso
        AddCommGrpCat.{u + 1} (smallTopology S) (topology S)) lim ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
      (Functor.ranCompLimIso (H := AddCommGrpCat.{u + 1}) (CrystallineThickening.ι S).op) ≪≫
    (Sheaf.ΓNatIsoLim (smallTopology S) AddCommGrpCat.{u + 1}).symm

include hf in
/-- **`Γ(CRIS(X'/S'), f_{CRIS, *}ℱ) ≅ Γ(CRIS(X/S), ℱ)`**, naturally in the abelian sheaf `ℱ` on
the big crystalline site of the source.

Change of divided power base is cocontinuous, so this is `bigDirectImageGlobalSectionsIso` for
`Crystalline.GlobalCrystallineSituation.changeBase` in place of the inclusion: the direct image
of [Stacks, Tag 07IC] is again the right Kan extension of [Stacks, Tag 00XK], and the limit of a
right Kan extension is the limit of the functor extended. -/
def changeBaseDirectImageGlobalSectionsIso :
    changeBaseDirectImage S S' fS fX hf ⋙ bigGlobalSections S' ≅ bigGlobalSections S :=
  Functor.isoWhiskerLeft (changeBaseDirectImage S S' fS fX hf)
      (Sheaf.ΓNatIsoLim (topology S') AddCommGrpCat.{u + 1}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((changeBase S S' fS fX hf).sheafPushforwardCocontinuousCompSheafToPresheafIso
        AddCommGrpCat.{u + 1} (topology S) (topology S')) lim ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (topology S) AddCommGrpCat.{u + 1})
      (Functor.ranCompLimIso (H := AddCommGrpCat.{u + 1}) (changeBase S S' fS fX hf).op) ≪≫
    (Sheaf.ΓNatIsoLim (topology S) AddCommGrpCat.{u + 1}).symm

include hf in
/-- **The comparison of underived global sections along `f_cris`,
`Γ(Cris(X/S), f_{cris, *}ℱ) ≅ Γ(Cris(X'/S), ℱ)`.**

This is a term of the type
`Crystalline.GlobalCrystallineSituation.SmallSite.CrisGlobalSectionsComparison`, which
`SmallSite/AlphaPCoverTriangle.lean` states and carries as an open datum: the Leray factorization
`derivedCrisGlobalSectionsIso` of [Stacks, Tag 015M] for `f_cris`, and with it the map
`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')` of [Stacks, Tag 07QA], carry this datum and
nothing else.  It is proved here unconditionally.

`f_{cris, *}` is the composite `π_{X', *} ∘ f_{CRIS, *} ∘ i_{X, *}` of [Stacks, Tag 07IK], and
the comparison is the composite of the three factors: `smallRestrictionGlobalSectionsIso` for the
restriction, which is the part needing the covering statement `coversTop_ι`, and
`changeBaseDirectImageGlobalSectionsIso` and `bigDirectImageGlobalSectionsIso` for the two
cocontinuous direct images, which are the Kan extension argument. -/
def crisGlobalSectionsIso :
    crisDirectImage S S' fS fX hf ⋙ globalSections S' ≅ globalSections S :=
  Functor.isoWhiskerLeft (bigDirectImage S ⋙ changeBaseDirectImage S S' fS fX hf)
      (smallRestrictionGlobalSectionsIso (S := S')) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (bigDirectImage S)
      (changeBaseDirectImageGlobalSectionsIso S S' fS fX hf) ≪≫
    bigDirectImageGlobalSectionsIso S

end Cocontinuous

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
