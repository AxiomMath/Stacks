module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProduct

/-!
# Restricting the small crystalline site to a pair of opens

Fix a global crystalline situation `(p, (S, I, γ), X)`, an open `W ⊆ S` and an open `V ⊆ X` whose
image in `S` lies in `W`.  `Crystalline.GlobalCrystallineSituation.restrict` is the restricted
situation `(p, S|_W, V)` and `...extend` is change of divided power base, [Stacks, Tag 07IC],
along the two open immersions `S|_W ⟶ S` and `V ⟶ X`, from `CRIS(V/S|_W)` to `CRIS(X/S)`.  Both
structure morphisms being open immersions, change of base carries `Cris(V/S|_W)` into
`Cris(X/S)`: that is `smallExtend`, the instance of
`Crystalline.GlobalCrystallineSituation.smallChangeBase`, [Stacks, Tag 07KL], at this pair.  This
file identifies its essential image.

An object of `Cris(X/S)` lies in that essential image exactly when its structure morphism to `X`
factors through `V`.  No condition on the ambient divided power scheme is needed: the immersion
of a divided power thickening is surjective on points, so an object whose thickened scheme maps
into `V` has its ambient scheme mapping into `W` automatically (`range_toBase_subset_restrict`).
The object of `Cris(V/S|_W)` it comes from is `CrystallineThickening.localObject`, and
`CrystallineThickening.extendLocalObjectIso` says that extending it gives the object back.
Change of base along the two open immersions being fully faithful, the two together exhibit
`Cris(V/S|_W)` as the full subcategory of `Cris(X/S)` on the objects lying in `V`: that is
`smallExtendEquivalence`.

## The types of the two open immersions

The thickened space of the restricted situation is `V` and its divided power base is `S|_W`, but
`Crystalline.GlobalCrystallineSituation.restrict` is a plain `def`, so `(restrict S W V hVW).X`
does not reduce to `V.toScheme` at `instances` transparency and `IsOpenImmersion V.ι` is not
found at the type change of base wants.  `restrictXι` and `restrictSι` are the two morphisms
named at those types, with their open-immersion instances attached to the names; every statement
below is phrased with them.  Compare the `@[reducible]` on
`Crystalline.GlobalCrystallineSituation.openSubspace`, which solves the same problem for the
situation that restricts only the thickened space.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `restrictXι` and `restrictSι` — the open immersions `V ⟶ X` and `S|_W ⟶ S`, at the types they
  have out of the restricted situation.
* `smallExtend` — change of divided power base `Cris(V/S|_W) ⥤ Cris(X/S)` along those two.
* `CrystallineThickening.localObject` — an object of `Cris(X/S)` whose structure morphism to `X`
  factors through `V`, read as an object of `Cris(V/S|_W)`.
* `smallExtendEquivalence` — `Cris(V/S|_W)` is equivalent to the full subcategory of `Cris(X/S)`
  on the objects lying in `V`.

## Main results

* `range_toBase_subset_restrict` — an object of `CRIS(X/S)` whose thickened scheme maps into `V`
  has its ambient divided power scheme mapping into `W`.
* `CrystallineThickening.extendLocalObjectIso` — extending the local reading of an object gives
  back the object.
* `smallExtend_essImage_iff` and `smallExtend_essImage_eq` — **the essential image of
  `smallExtend`**: an object of `Cris(X/S)` comes from `Cris(V/S|_W)` exactly when its structure
  morphism to `X` factors through `V`.
* `smallExtendFullyFaithful` — change of base along the two open immersions is fully faithful on
  the small crystalline sites.

## What is and is not proved

No tag attribute is placed in this file.  It is the instance of
`Crystalline.GlobalCrystallineSituation.smallChangeBase_essImage_iff` at the pair of open
immersions coming from a restricted situation, and the [Stacks, Tag 07KL] attribute for change of
base along open immersions already sits on the general statements in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Functoriality.lean`.

Nothing here asserts that the opens `W` and `V` may be chosen, nor that the resulting local
descriptions glue.  The big crystalline analogues of `CrystallineThickening.localObject` and
`CrystallineThickening.extendLocalObjectIso` are
`Crystalline.GlobalCrystallineSituation.localObject` and `...extendLocalObjectIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductLocal.lean`; the local reading
here is that one, cut down to the small site.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The open immersion `V ⟶ X`, at the type it has as a morphism of thickened spaces out of the
restricted situation.**  The thickened space of `(p, S|_W, V)` is `V`, but
`Crystalline.GlobalCrystallineSituation.restrict` does not reduce at `instances` transparency, so
the open-immersion instance has to be attached to a name carrying this type. -/
def restrictXι : (restrict S W V hVW).X ⟶ S.X := V.ι

/-- The morphism of thickened spaces out of the restricted situation is the open immersion of
`V`. -/
@[simp]
theorem restrictXι_eq : restrictXι S W V hVW = V.ι := rfl

/-- The morphism `restrictXι` of thickened spaces out of the restricted situation is an open
immersion. -/
instance isOpenImmersion_restrictXι : IsOpenImmersion (restrictXι S W V hVW) :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- **The restriction morphism `S|_W ⟶ S` of divided power schemes, at the type it has as the
morphism of divided power bases out of the restricted situation.** -/
def restrictSι : (restrict S W V hVW).S ⟶ S.S := S.S.restrictι W

/-- The morphism of divided power bases out of the restricted situation is the restriction
morphism of `S`. -/
@[simp]
theorem restrictSι_eq : restrictSι S W V hVW = S.S.restrictι W := rfl

/-- The morphism of schemes underlying `restrictSι` is an open immersion. -/
instance isOpenImmersion_restrictSι_hom : IsOpenImmersion (restrictSι S W V hVW).hom :=
  inferInstanceAs (IsOpenImmersion (S.S.restrictι W).hom)

/-- `S|_W ⟶ S` exhibits `S|_W` as an open divided power subscheme of `S`. -/
theorem isInducedOpen_restrictSι :
    DividedPowerScheme.IsInducedOpen (restrictSι S W V hVW) :=
  DividedPowerScheme.isInducedOpen_restrictι S.S W

/-- **The compatibility datum of [Stacks, Tag 07IC] for the restricted situation**, at the types
of `restrictSι` and `restrictXι`. -/
theorem restrict_changeBase_condition' :
    (restrict S W V hVW).toClosedFiber ≫
        DividedPowerScheme.closedFiberMap (restrictSι S W V hVW) =
      restrictXι S W V hVW ≫ S.toClosedFiber :=
  restrict_changeBase_condition S W V hVW

/-- The range of the morphism of thickened spaces out of the restricted situation is `V`. -/
theorem range_restrictXι :
    Set.range (restrictXι S W V hVW).base = (V : Set S.X) :=
  V.range_ι

/-- The range of the morphism of divided power bases out of the restricted situation is `W`. -/
theorem range_restrictSι_hom :
    Set.range (restrictSι S W V hVW).hom.base = (W : Set S.S.scheme) :=
  W.range_ι

include hVW in
/-- **An object of `CRIS(X/S)` whose thickened scheme maps into `V` has its ambient divided power
scheme mapping into `W`.**  This is
`Crystalline.GlobalCrystallineSituation.range_toBase_subset_of_range_toX_subset` for the pair of
open immersions `S|_W ⟶ S` and `V ⟶ X`: the immersion of a divided power thickening is surjective
on points, so the image of `T ⟶ S` is the image of `U ↪ T ⟶ S`, which is the image of
`U ⟶ X ⟶ S`, and that lies in `W` because `V ⟶ X ⟶ S` does. -/
theorem range_toBase_subset_restrict (A : Thickening S)
    (hV : Set.range A.toX.base ⊆ (V : Set S.X)) :
    Set.range A.toBase.hom.base ⊆ (W : Set S.S.scheme) :=
  (range_restrictSι_hom S W V hVW) ▸
    range_toBase_subset_of_range_toX_subset (f := restrictSι S W V hVW)
      (g := restrictXι S W V hVW) (h := restrict_changeBase_condition' S W V hVW) A
      ((range_restrictXι S W V hVW) ▸ hV)

/-- **Change of divided power base from the restricted situation back to `S`, on the small
crystalline sites.**  This is `Crystalline.GlobalCrystallineSituation.smallChangeBase`,
[Stacks, Tag 07KL], for the two open immersions `S|_W ⟶ S` and `V ⟶ X`: an object of
`Cris(V/S|_W)` is read as an object of `Cris(X/S)` with the same thickening, by composing its two
structure morphisms with the open immersions.  Its structure morphism to `X` is again an open
immersion, being a composite of two. -/
def smallExtend : CrystallineThickening (restrict S W V hVW) ⥤ CrystallineThickening S :=
  smallChangeBase (restrict S W V hVW) S (restrictSι S W V hVW) (restrictXι S W V hVW)
    (restrict_changeBase_condition' S W V hVW)

/-- The underlying object of `CRIS(X/S)` of an extended object is its extension in the big
crystalline category. -/
@[simp]
theorem smallExtend_obj_obj (A : CrystallineThickening (restrict S W V hVW)) :
    ((smallExtend S W V hVW).obj A).obj = (extend S W V hVW).obj A.obj := rfl

/-- Change of base along the two open immersions is faithful on the small sites, change of base
being faithful and the inclusion of a full subcategory being faithful. -/
instance smallExtend_faithful : (smallExtend S W V hVW).Faithful :=
  inferInstanceAs ((smallChangeBase (restrict S W V hVW) S (restrictSι S W V hVW)
    (restrictXι S W V hVW) (restrict_changeBase_condition' S W V hVW)).Faithful)

/-- Change of base along the two open immersions is full on the small sites, both structure
morphisms being open immersions and hence monomorphisms. -/
instance smallExtend_full : (smallExtend S W V hVW).Full :=
  inferInstanceAs ((smallChangeBase (restrict S W V hVW) S (restrictSι S W V hVW)
    (restrictXι S W V hVW) (restrict_changeBase_condition' S W V hVW)).Full)

/-- **Change of base along the two open immersions is fully faithful on the small crystalline
sites.** -/
def smallExtendFullyFaithful : (smallExtend S W V hVW).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

namespace CrystallineThickening

variable (A : CrystallineThickening S) (hV : Set.range A.obj.toX.base ⊆ (V : Set S.X))

/-- The local reading of an object of `Cris(X/S)` is again an object of the small crystalline
category: its structure morphism to `V` composed with the open immersion of `V` is the original
open immersion to `X`, and a morphism whose composite with an open immersion is an open immersion
is one. -/
theorem isCrystalline_localObject :
    Thickening.IsCrystalline (GlobalCrystallineSituation.localObject S W V hVW A.obj
      (range_toBase_subset_restrict S W V hVW A.obj hV) hV) := by
  have : IsOpenImmersion A.obj.toX := A.property
  change IsOpenImmersion (localObjectToX S V A.obj hV)
  have : IsOpenImmersion (localObjectToX S V A.obj hV ≫ V.ι) := by
    rw [localObjectToX_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ V.ι

/-- **An object of `Cris(X/S)` whose structure morphism to `X` factors through `V`, read as an
object of `Cris(V/S|_W)`.**  The underlying object of `CRIS(V/S|_W)` is the local reading
`Crystalline.GlobalCrystallineSituation.localObject` of the big crystalline category: the divided
power thickening is unchanged and the two structure morphisms are factored through the two open
immersions.  The condition on the ambient divided power scheme is automatic, by
`Crystalline.GlobalCrystallineSituation.range_toBase_subset_restrict`. -/
def localObject : CrystallineThickening (restrict S W V hVW) :=
  ⟨GlobalCrystallineSituation.localObject S W V hVW A.obj
      (range_toBase_subset_restrict S W V hVW A.obj hV) hV,
    isCrystalline_localObject S W V hVW A hV⟩

/-- The underlying object of `CRIS(V/S|_W)` of the local reading of an object of `Cris(X/S)`, by
definition. -/
@[simp]
theorem localObject_obj :
    (localObject S W V hVW A hV).obj =
      GlobalCrystallineSituation.localObject S W V hVW A.obj
        (range_toBase_subset_restrict S W V hVW A.obj hV) hV := rfl

/-- **Extending the local reading of an object of `Cris(X/S)` gives back the object.**  Both
objects have the same underlying divided power thickening, and the two pairs of structure
morphisms agree because factoring through an open immersion and composing back is the identity.
The isomorphism is the big crystalline one,
`Crystalline.GlobalCrystallineSituation.extendLocalObjectIso`, read in the full subcategory. -/
def extendLocalObjectIso :
    (smallExtend S W V hVW).obj (localObject S W V hVW A hV) ≅ A :=
  (Thickening.IsCrystalline (S := S)).fullyFaithfulι.preimageIso
    (GlobalCrystallineSituation.extendLocalObjectIso S W V hVW A.obj
      (range_toBase_subset_restrict S W V hVW A.obj hV) hV)

end CrystallineThickening

/-- **The essential image of change of base along the two open immersions.**  An object of
`Cris(X/S)` comes from `Cris(V/S|_W)` exactly when its structure morphism to `X` factors through
the open `V`.  This is
`Crystalline.GlobalCrystallineSituation.smallChangeBase_essImage_iff`, [Stacks, Tag 07KL], at the
restriction morphism `S|_W ⟶ S`, which exhibits `S|_W` as an open divided power subscheme of `S`
by `Crystalline.DividedPowerScheme.isInducedOpen_restrictι`. -/
theorem smallExtend_essImage_iff (A : CrystallineThickening S) :
    (smallExtend S W V hVW).essImage A ↔ Set.range A.obj.toX.base ⊆ (V : Set S.X) :=
  (range_restrictXι S W V hVW) ▸
    smallChangeBase_essImage_iff (f := restrictSι S W V hVW) (g := restrictXι S W V hVW)
      (h := restrict_changeBase_condition' S W V hVW) (isInducedOpen_restrictSι S W V hVW) A

/-- The essential image of change of base along the two open immersions, as a property of the
objects of `Cris(X/S)`. -/
theorem smallExtend_essImage_eq :
    (smallExtend S W V hVW).essImage =
      fun A : CrystallineThickening S ↦ Set.range A.obj.toX.base ⊆ (V : Set S.X) :=
  funext fun A ↦ propext (smallExtend_essImage_iff S W V hVW A)

/-- **`Cris(V/S|_W)` is equivalent to the full subcategory of `Cris(X/S)` on the objects whose
structure morphism to `X` factors through `V`.**  Change of base along the two open immersions is
fully faithful, so it is an equivalence onto its essential image, which
`Crystalline.GlobalCrystallineSituation.smallExtend_essImage_eq` identifies with that full
subcategory. -/
def smallExtendEquivalence :
    CrystallineThickening (restrict S W V hVW) ≌ (smallExtend S W V hVW).EssImageSubcategory :=
  (smallExtend S W V hVW).toEssImage.asEquivalence

/-- Change of base along the two open immersions, followed by the inclusion of the essential
image, is change of base. -/
def smallExtendEquivalenceCompι :
    (smallExtendEquivalence S W V hVW).functor ⋙ (smallExtend S W V hVW).essImage.ι ≅
      smallExtend S W V hVW :=
  (smallExtend S W V hVW).toEssImageCompι

end GlobalCrystallineSituation

end Crystalline

end
