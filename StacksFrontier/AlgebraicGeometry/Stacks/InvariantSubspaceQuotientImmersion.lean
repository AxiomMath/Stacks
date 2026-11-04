module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRestrictionImmersion
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliarySpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantClosedSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantRestrictionCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackSquareFibred
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpacesOfFppfCover
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# Stacks 04YN: the quotient of an invariant subspace immerses in the quotient stack

Let `G = (U, R, s, t, c)` be a smooth groupoid in algebraic spaces over an algebraic space `B`
over a scheme `S` of a big fppf site, and let `Z ⊆ U` be an invariant subspace of its object
space in the sense of Stacks 044F. Stacks 04YN asserts that

```
[Z/R_Z] ⟶ [U/R]
```

is an immersion of algebraic stacks, and an open — respectively closed — immersion when `Z` is
an open — respectively closed — subspace of `U`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackMapHom_restrict`: the
  1-morphism `[Z/R_Z] ⟶ [U/R]` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isImmersion_quotientStackMap_of_invariantRestrictionBaseChange`,
* `AlgebraicGeometry.Stack.isOpenImmersion_quotientStackMap_of_invariantRestrictionBaseChange`,
* `AlgebraicGeometry.Stack.isClosedImmersion_quotientStackMap_of_invariantRestrictionBaseChange`:
  **Stacks 04YN**, for an invariant locally closed, respectively open, respectively closed
  subspace.

## Implementation notes

The source's proof cites Stacks 04ZP and Stacks 04ZN. Stacks 04ZN for the restriction is
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquareFibred`, whose hypothesis — the
source square of the restriction is cartesian — is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_restrictionSource_of_preimage_le`: the
base change of `[Z/R_Z] ⟶ [U/R]` along the projection `S_U ⟶ [U/R]` is `S_Z ⟶ S_U`.

Stacks 04ZP is stated in this library for the 2-category of algebraic stacks of Stacks 03YP, which
is formed at the universes of the site, whereas a quotient stack has its morphisms one universe
up. So the representability is obtained as the source's proof of Stacks 04ZP obtains it, through
faithfulness. The 1-morphism is faithful by Stacks 06DV, `S_Z ⟶ S_U` being faithful and the
projection `S_U ⟶ [U/R]` locally essentially surjective; the two quotient stacks are algebraic by
Stacks 04TK, the restriction of a smooth groupoid along an invariant subspace being smooth; their
small models (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`) are objects of that
2-category, where the induced 1-morphism is faithful, hence representable by algebraic spaces by
Stacks 04Y5; and representability passes back along the two equivalences by Stacks 0457.

An immersion of algebraic stacks (Stacks 04YL) is a 1-morphism representable by algebraic spaces
whose base changes are immersions (Stacks 04XB); since a quotient stack is not literally an object
of `AlgebraicGeometry.Stack.AlgebraicStacks` the two conjuncts are stated separately, with
`AlgebraicGeometry.Stack.IsImmersion` and its two companions for the second. Their descent along
`S_U ⟶ [U/R]` is `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackMapHom_restrict`; the
locality of the three properties at the target for the fppf precoverage is Stacks 042U, 041X and
0420.

## References

* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YN](https://stacks.math.columbia.edu/tag/04YN)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The swapped square of Stacks 04ZN for the restriction to an invariant subspace is a 2-fibre
product. -/
private noncomputable def isTwoFibreProduct_swap_functorialitySquareFibred_restrict
    (G : GroupoidInAlgebraicSpaces C S hS B) (Z : Subfunctor G.objects.obj)
    (hZ : IsAlgebraicSpace C S hS Z.toFunctor)
    (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    Bicategory.IsTwoFibreProduct
      (functorialitySquareFibred (G.restrict (subspaceInclusion G Z hZ)).hom).swap :=
  Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_functorialitySquareFibred _
    (AlgebraicSpaces.isPullback_hom C S hS
      (isPullback_restrictionSource_of_preimage_le G Z hZ hinv)))

/-- **The 1-morphism `[Z/R_Z] ⟶ [U/R]` is faithful.** For a subspace `Z` of the object space of a
groupoid in algebraic spaces with `s⁻¹(Z) ≤ t⁻¹(Z)`, the base change of `[Z/R_Z] ⟶ [U/R]` along
the projection `S_U ⟶ [U/R]` is `S_Z ⟶ S_U` (Stacks 04ZN), which is faithful, and the projection
is locally essentially surjective on fibres, so Stacks 06DV applies. -/
theorem faithful_homFunctor_quotientStackMapHom_restrict
    (G : GroupoidInAlgebraicSpaces C S hS B) (Z : Subfunctor G.objects.obj)
    (hZ : IsAlgebraicSpace C S hS Z.toFunctor)
    (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    (CatFiberedInGroupoids.homFunctor
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ)).hom)).Faithful := by
  let R := G.restrict (subspaceInclusion G Z hZ)
  let Q := (functorialitySquareFibred R.hom).swap
  have : Q.pt.val.p.Faithful := liftedFibredCategory_faithful R.groupoid.objects
  exact faithful_homFunctor_of_isTwoFibreProduct_of_locallyEssSurjOnFibers.{u, u + 1, u + 1}
    C S hS (quotientStackMapHom R.hom) (quotientStackProjectionHom G)
    (isStack_quotientStack R.groupoid)
    (locallyEssSurjOnFibers_of_localEssSurj C S hS _ (localEssSurj_quotientStackProjectionHom G))
    Q (isTwoFibreProduct_swap_functorialitySquareFibred_restrict G Z hZ hinv)
    (Functor.Faithful.of_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p Q.fst))

/-- **The 1-morphism `[Z/R_Z] ⟶ [U/R]` is representable by algebraic spaces** for a smooth
groupoid `G` in algebraic spaces and an invariant subspace `Z` of its object space: this is the
Stacks 04ZP step of the proof of Stacks 04YN.

Both quotient stacks are algebraic stacks (Stacks 04TK), the restriction being smooth. Their small
models are objects of the 2-category of algebraic stacks, the 1-morphism between them induced by
`[Z/R_Z] ⟶ [U/R]` is faithful with it, and so is representable by algebraic spaces by Stacks 04Y5;
Stacks 0457 carries this back along the two equivalences. -/
theorem isRepresentableByAlgebraicSpaces_quotientStackMapHom_restrict
    {G : GroupoidInAlgebraicSpaces C S hS B} (hG : IsSmooth C S hS G)
    (Z : Subfunctor G.objects.obj) (hZ : IsAlgebraicSpace C S hS Z.toFunctor)
    (heq : Z.preimage G.source.hom = Z.preimage G.target.hom) :
    IsRepresentableByAlgebraicSpaces C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ)).hom).hom := by
  let R := G.restrict (subspaceInclusion G Z hZ)
  let m := quotientStackMap R.hom
  have : m.toFunctor.Faithful :=
    faithful_homFunctor_quotientStackMapHom_restrict G Z hZ heq.le
  have h𝒳 : IsAlgebraicStack.{u, u} C S hS (quotientStack R.groupoid) :=
    isAlgebraicStack_quotientStack_of_isSmooth (isSmooth_restriction G Z hZ hG heq R)
  have h𝒴 : IsAlgebraicStack.{u, u} C S hS (quotientStack G) :=
    isAlgebraicStack_quotientStack_of_isSmooth hG
  let eX := AlgebraicStacks.smallModelEquivalenceOver C S hS _ h𝒳
  let eY := AlgebraicStacks.smallModelEquivalenceOver C S hS _ h𝒴
  -- the induced 1-morphism of small models
  let fs : AlgebraicStacks.smallModel C S hS _ h𝒳 ⟶ AlgebraicStacks.smallModel C S hS _ h𝒴 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := eX.inv.functor ⋙ m.toFunctor ⋙ eY.hom.functor
        w := by rw [Functor.assoc, Functor.assoc, eY.hom.w, m.w, eX.inv.w] })
  have := eX.isEquivalence_inv_functor
  have := eY.isEquivalence_hom_functor
  have hfs : (CatFiberedInGroupoids.homFunctor fs.hom).Faithful :=
    inferInstanceAs (eX.inv.functor ⋙ m.toFunctor ⋙ eY.hom.functor).Faithful
  -- Stacks 04Y5 for the small models, and Stacks 0457 back
  let a : (AlgebraicStacks.smallModel C S hS _ h𝒳).val.val ⥤ᵇ
      (quotientStackCFG C S hS R.groupoid).val := ⟨eX.inv.functor, eX.inv.w⟩
  let b : (AlgebraicStacks.smallModel C S hS _ h𝒴).val.val ⥤ᵇ
      (quotientStackCFG C S hS G).val := ⟨eY.inv.functor, eY.inv.w⟩
  have : a.toFunctor.IsEquivalence := eX.isEquivalence_inv_functor
  have : b.toFunctor.IsEquivalence := eY.isEquivalence_inv_functor
  refine (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (𝒳' := (AlgebraicStacks.smallModel C S hS _ h𝒳).val)
    (𝒳 := quotientStackCFG C S hS R.groupoid)
    (𝒴' := (AlgebraicStacks.smallModel C S hS _ h𝒴).val) (𝒴 := quotientStackCFG C S hS G)
    fs.hom.hom m a b ?_).2
    (AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful C S hS fs hfs)
  refine BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft (eX.inv.functor ⋙ m.toFunctor) eY.unitIso) fun a => ?_
  have h := eY.isHomLift_unitIso_hom_app ((eX.inv.functor ⋙ m.toFunctor).obj a)
  have hobj : (quotientStack G).p.obj ((eX.inv.functor ⋙ m.toFunctor).obj a) =
      (AlgebraicStacks.smallModel C S hS _ h𝒳).val.val.p.obj a :=
    Functor.congr_obj (F := (eX.inv.functor ⋙ m.toFunctor) ⋙ (quotientStack G).p)
      (by rw [Functor.assoc, m.w, eX.inv.w]) a
  rwa [hobj] at h

/-- The morphism of representing presheaves induced by `S_Z ⟶ S_U`, the first leg of the square
of Stacks 04ZN for the restriction, is the inclusion of `Z`. -/
theorem representingMap_associatedMap_restrict
    (G : GroupoidInAlgebraicSpaces C S hS B) (Z : Subfunctor G.objects.obj)
    (hZ : IsAlgebraicSpace C S hS Z.toFunctor) :
    representingMap C S hS
        (fibredCategory C S hS (G.restrict (subspaceInclusion G Z hZ)).groupoid.objects.obj)
        (fibredCategory C S hS G.objects.obj) Z.toFunctor G.objects.obj
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (associatedMap C S hS (G.restrict (subspaceInclusion G Z hZ)).hom.objectsMap.hom).1 =
      Z.ι :=
  (representingMap_associatedMap C S hS _ _ _).trans
    ((G.restrict (subspaceInclusion G Z hZ)).mapObjects_eq.trans (Category.id_comp _))

/-- **A relative property of `[Z/R_Z] ⟶ [U/R]` from the same property of `Z ⟶ U`.** Let `P` be a
property of morphisms of algebraic spaces over `S`, stable under base change and local on the
target for the fppf precoverage, and let `Z` be a subspace of the object space of a groupoid `G`
in algebraic spaces with `s⁻¹(Z) ≤ t⁻¹(Z)` whose inclusion has `P`. Then the 1-morphism
`[Z/R_Z] ⟶ [U/R]`, if representable by algebraic spaces, has `P` relatively (Stacks 03YK).

The base change along the projection `S_U ⟶ [U/R]` is `S_Z ⟶ S_U` by Stacks 04ZN
(`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquareFibred`), whose representing
morphism is the inclusion of `Z`, and the descent step is
`AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackMapHom_of_representingMap`. -/
theorem hasRelativeProperty_quotientStackMapHom_restrict
    (G : GroupoidInAlgebraicSpaces C S hS B) (Z : Subfunctor G.objects.obj)
    (hZ : IsAlgebraicSpace C S hS Z.toFunctor)
    (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} C S hS)]
    (hf : IsRepresentableByAlgebraicSpaces C S hS
      (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ)).hom).hom)
    (hP : P (subspaceInclusion G Z hZ)) :
    HasRelativeProperty C S hS P (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ)).hom)
      hf := by
  let R := G.restrict (subspaceInclusion G Z hZ)
  exact @hasRelativeProperty_quotientStackMapHom_of_representingMap.{u, u + 1} C S hS B _ _ R.hom
    P _ _ hf (functorialitySquareFibred R.hom).swap
    (isTwoFibreProduct_swap_functorialitySquareFibred_restrict G Z hZ hinv)
    (isRepresentableByAlgebraicSpaces_liftedSpaceStackMap R.hom.objectsMap.hom) _ _
    (associatedMap C S hS R.hom.objectsMap.hom).1
    (isRepresentableByAlgebraicSpaces_associatedMap R.hom.objectsMap.hom)
    (liftedFibredCategoryDown R.groupoid.objects) (liftedFibredCategoryDown G.objects)
    (isEquivalence_liftedFibredCategoryDown _) (isEquivalence_liftedFibredCategoryDown _)
    (liftedSpaceStackMapSquareIso R.hom.objectsMap.hom) Z.toFunctor G.objects.obj hZ
    G.objects.property (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (by rwa [representingMap_associatedMap_restrict G Z hZ])

/-- **Stacks 04YN**, the immersion. For a smooth groupoid `G` in algebraic spaces and an invariant
locally closed subspace `Z` of its object space, the 1-morphism `[Z/R_Z] ⟶ [U/R]` of Stacks 044B
is an immersion of algebraic stacks: it is representable by algebraic spaces and an immersion in
the sense of Stacks 04XB. -/
@[stacks 04YN "the immersion [Z/R_Z] ⟶ [U/R] for an invariant locally closed subspace"]
theorem isImmersion_quotientStackMap_of_invariantRestrictionBaseChange
    {G : GroupoidInAlgebraicSpaces C S hS B} (hG : IsSmooth C S hS G)
    {Z : Subfunctor G.objects.obj} (hZ : IsInvariantLocallyClosed G Z) :
    IsRepresentableByAlgebraicSpaces C S hS
        (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom).hom ∧
      Stack.IsImmersion C S hS
        (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom) :=
  have hf := isRepresentableByAlgebraicSpaces_quotientStackMapHom_restrict hG Z hZ.1.1 hZ.2.symm
  have := Space.isImmersion_isLocalAtTarget_fppf.{u, u + 1} C S hS
  ⟨hf, (isImmersion_iff_hasRelativeProperty C S hS _ hf).mpr
    (hasRelativeProperty_quotientStackMapHom_restrict G Z hZ.1.1 hZ.2.ge _ hf hZ.1.2)⟩

/-- **Stacks 04YN**, the open immersion. For a smooth groupoid `G` in algebraic spaces and an
invariant open subspace `Z` of its object space, the 1-morphism `[Z/R_Z] ⟶ [U/R]` of Stacks 044B
is an open immersion of algebraic stacks: it is representable by algebraic spaces and an open
immersion in the sense of Stacks 04XB. -/
@[stacks 04YN "the open immersion [Z/R_Z] ⟶ [U/R] for an invariant open subspace"]
theorem isOpenImmersion_quotientStackMap_of_invariantRestrictionBaseChange
    {G : GroupoidInAlgebraicSpaces C S hS B} (hG : IsSmooth C S hS G)
    {Z : Subfunctor G.objects.obj} (hZ : IsInvariantOpen G Z) :
    IsRepresentableByAlgebraicSpaces C S hS
        (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom).hom ∧
      Stack.IsOpenImmersion C S hS
        (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom) :=
  have hf := isRepresentableByAlgebraicSpaces_quotientStackMapHom_restrict hG Z hZ.1.1
    (preimage_source_eq_preimage_target G Z hZ.2)
  have := Space.openImmersion_isLocalAtTarget_fppf.{u, u + 1} C S hS
  ⟨hf, (isOpenImmersion_iff_hasRelativeProperty C S hS _ hf).mpr
    (hasRelativeProperty_quotientStackMapHom_restrict G Z hZ.1.1 hZ.2 _ hf hZ.1.2)⟩

/-- **Stacks 04YN**, the closed immersion. For a smooth groupoid `G` in algebraic spaces and an
invariant closed subspace `Z` of its object space, the 1-morphism `[Z/R_Z] ⟶ [U/R]` of
Stacks 044B is a closed immersion of algebraic stacks: it is representable by algebraic spaces and
a closed immersion in the sense of Stacks 04XB. -/
@[stacks 04YN "the closed immersion [Z/R_Z] ⟶ [U/R] for an invariant closed subspace"]
theorem isClosedImmersion_quotientStackMap_of_invariantRestrictionBaseChange
    {G : GroupoidInAlgebraicSpaces C S hS B} (hG : IsSmooth C S hS G)
    {Z : Subfunctor G.objects.obj} (hZ : IsInvariantClosed G Z) :
    IsRepresentableByAlgebraicSpaces C S hS
        (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom).hom ∧
      Stack.IsClosedImmersion C S hS
        (quotientStackMapHom (G.restrict (subspaceInclusion G Z hZ.1.1)).hom) :=
  have hf := isRepresentableByAlgebraicSpaces_quotientStackMapHom_restrict hG Z hZ.1.1 hZ.2.symm
  have := Space.isClosedImmersion_isLocalAtTarget_fppf.{u, u + 1} C S hS
  ⟨hf, (isClosedImmersion_iff_hasRelativeProperty C S hS _ hf).mpr
    (hasRelativeProperty_quotientStackMapHom_restrict G Z hZ.1.1 hZ.2.ge _ hf hZ.1.2)⟩

end AlgebraicGeometry.Stack

end
