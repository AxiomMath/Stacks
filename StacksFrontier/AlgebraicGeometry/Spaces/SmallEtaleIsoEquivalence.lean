module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# The small étale sites of isomorphic algebraic spaces

An isomorphism `e : X ≅ Y` of algebraic spaces over `S` induces an equivalence of their small
étale sites, `AlgebraicGeometry.Space.smallEtaleIsoEquivalence`: postcomposition of étale charts
with `e` and with its inverse.  Postcomposition does not change the underlying scheme of a chart,
so the two structure sheaves of global regular functions correspond along it on the nose: the
comparison maps `smallEtaleIsoStructureMap` and `smallEtaleIsoStructureMapInverse` are
identities, and they satisfy the two compatibilities that make the two pushforwards of modules
mutually inverse.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleIsoEquivalence`: the equivalence of small étale sites.
* `AlgebraicGeometry.Space.smallEtaleIsoStructureMap` and
  `AlgebraicGeometry.Space.smallEtaleIsoStructureMapInverse`: the two comparisons of structure
  sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)

/-- The underlying morphism of presheaves of an isomorphism of algebraic spaces is invertible. -/
instance isIso_hom_hom_of_iso : IsIso e.hom.hom :=
  Iso.isIso_hom ((ObjectProperty.ι _).mapIso e)

/-- The underlying morphism of presheaves of an isomorphism of algebraic spaces is étale. -/
theorem isEtale_hom_hom_of_iso : IsEtale B S hS e.hom.hom :=
  isEtale_of_isIso B S hS e.hom.hom

/-- **The small étale sites of isomorphic algebraic spaces are equivalent**, by postcomposition
of étale charts with the isomorphism and with its inverse. -/
def smallEtaleIsoEquivalence : SmallEtale B S hS X.1 ≌ SmallEtale B S hS Y.1 :=
  Equivalence.mk'
    (smallEtalePostcomp B S hS e.hom (isEtale_hom_hom_of_iso B S hS e))
    (smallEtalePostcomp B S hS e.inv (isEtale_hom_hom_of_iso B S hS e.symm))
    (NatIso.ofComponents
      (fun V => ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
        simp [smallEtalePostcomp])))
      (fun f => by
        apply ObjectProperty.hom_ext
        ext
        simp [smallEtalePostcomp]))
    (NatIso.ofComponents
      (fun V => ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
        simp [smallEtalePostcomp])))
      (fun f => by
        apply ObjectProperty.hom_ext
        ext
        simp [smallEtalePostcomp]))
    (fun V => by
      apply ObjectProperty.hom_ext
      ext
      simp [smallEtalePostcomp])

/-- The functor of `smallEtaleIsoEquivalence` is postcomposition of étale charts with `e.hom`. -/
@[simp]
theorem smallEtaleIsoEquivalence_functor :
    (smallEtaleIsoEquivalence B S hS e).functor =
      smallEtalePostcomp B S hS e.hom (isEtale_hom_hom_of_iso B S hS e) :=
  rfl

/-- The inverse of `smallEtaleIsoEquivalence` is postcomposition of étale charts with `e.inv`. -/
@[simp]
theorem smallEtaleIsoEquivalence_inverse :
    (smallEtaleIsoEquivalence B S hS e).inverse =
      smallEtalePostcomp B S hS e.inv (isEtale_hom_hom_of_iso B S hS e.symm) :=
  rfl

/-- The equivalence of small étale sites is continuous. -/
instance isContinuous_smallEtaleIsoEquivalence_functor :
    (smallEtaleIsoEquivalence B S hS e).functor.IsContinuous
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  smallEtalePostcomp_isContinuous B S hS e.hom (isEtale_hom_hom_of_iso B S hS e)

/-- The inverse of the equivalence of small étale sites is continuous. -/
instance isContinuous_smallEtaleIsoEquivalence_inverse :
    (smallEtaleIsoEquivalence B S hS e).inverse.IsContinuous
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  smallEtalePostcomp_isContinuous B S hS e.inv (isEtale_hom_hom_of_iso B S hS e.symm)

/-- The equivalence of small étale sites is continuous, at the spelling of the ringed sites. -/
instance isContinuous_smallEtaleIsoEquivalence_functor_ringedSite :
    (smallEtaleIsoEquivalence B S hS e).functor.IsContinuous
      (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  smallEtalePostcomp_isContinuous B S hS e.hom (isEtale_hom_hom_of_iso B S hS e)

/-- The inverse of the equivalence of small étale sites is continuous, at the spelling of the
ringed sites. -/
instance isContinuous_smallEtaleIsoEquivalence_inverse_ringedSite :
    (smallEtaleIsoEquivalence B S hS e).inverse.IsContinuous
      (smallEtaleRingedSite B S hS Y.1 Y.2).J (smallEtaleRingedSite B S hS X.1 X.2).J :=
  smallEtalePostcomp_isContinuous B S hS e.inv (isEtale_hom_hom_of_iso B S hS e.symm)

/-- The structure sheaf of `X` is the pushforward of the structure sheaf of `Y` along the
equivalence of small étale sites: postcomposition does not change the underlying scheme of a
chart, so the comparison is the identity. -/
def smallEtaleIsoStructureMap :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O ⟶
      ((smallEtaleIsoEquivalence B S hS e).functor.sheafPushforwardContinuous RingCat.{u}
        (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS Y.1 Y.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) where
  hom := 𝟙 _

/-- The structure sheaf of `Y` is the pushforward of the structure sheaf of `X` along the
inverse equivalence of small étale sites; the comparison is the identity. -/
def smallEtaleIsoStructureMapInverse :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O ⟶
      ((smallEtaleIsoEquivalence B S hS e).inverse.sheafPushforwardContinuous RingCat.{u}
        (smallEtaleRingedSite B S hS Y.1 Y.2).J (smallEtaleRingedSite B S hS X.1 X.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) where
  hom := 𝟙 _

/-- The comparison of structure sheaves is invertible, being the identity. -/
instance isIso_smallEtaleIsoStructureMap : IsIso (smallEtaleIsoStructureMap B S hS e) :=
  ⟨⟨⟨𝟙 _⟩, rfl, rfl⟩⟩

/-- The inverse comparison of structure sheaves is invertible, being the identity. -/
instance isIso_smallEtaleIsoStructureMapInverse :
    IsIso (smallEtaleIsoStructureMapInverse B S hS e) :=
  ⟨⟨⟨𝟙 _⟩, rfl, rfl⟩⟩

/-- The first compatibility of the two comparisons of structure sheaves: the counit of the
equivalence of small étale sites does not move the underlying scheme of a chart. -/
theorem smallEtaleIsoStructureMap_counit :
    Functor.whiskerRight (NatTrans.op (smallEtaleIsoEquivalence B S hS e).counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj =
      (smallEtaleIsoStructureMapInverse B S hS e).hom ≫
        (smallEtaleIsoEquivalence B S hS e).inverse.op.whiskerLeft
          (smallEtaleIsoStructureMap B S hS e).hom := by
  ext : 2
  exact rfl

/-- The second compatibility of the two comparisons of structure sheaves. -/
theorem smallEtaleIsoStructureMap_unit :
    (smallEtaleIsoStructureMap B S hS e).hom ≫
        (smallEtaleIsoEquivalence B S hS e).functor.op.whiskerLeft
          (smallEtaleIsoStructureMapInverse B S hS e).hom ≫
        Functor.whiskerRight (NatTrans.op (smallEtaleIsoEquivalence B S hS e).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj := by
  ext : 2
  exact rfl

end AlgebraicGeometry.Space

end
