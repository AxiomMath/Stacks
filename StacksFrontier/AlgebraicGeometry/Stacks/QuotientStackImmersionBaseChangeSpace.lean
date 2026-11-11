module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceSections
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# The base change of a relatively-`P` 1-morphism along the atlas of a quotient stack

Let `S` be a scheme contained in a big fppf site, let `P` be a property of morphisms of algebraic
spaces over `S` stable under base change and local on the target for the fppf precoverage, and let
`i : 𝒵 ⟶ [U/R]` be a 1-morphism into a quotient stack which is representable by algebraic spaces
and has the relative property `P`. The 2-fibre product `U' = 𝒵 ×_{[U/R]} U` is represented by an
algebraic space, its projection `m : U' ⟶ U` has `P`, and the range of `m` is the locus of `U`
whose image in `[U/R]` lies in the essential image of `i`.

## Main results

* `AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty_of_equivalences`: a
  1-morphism with the relative property `P`, carried by a pair of equivalences onto a 1-morphism
  between represented categories fibred in groupoids, induces a morphism of representing
  presheaves with `P`; the first 1-morphism lives in arbitrary morphism and object universes.
* `AlgebraicGeometry.Stack.mem_range_representingMap_iff_exists_sectionOfObj`: a section of the
  target over `W` is in the range of the morphism of representing presheaves induced by a
  1-morphism exactly when it is the one named by the image of some object lying over `W`.
* `AlgebraicGeometry.Stack.exists_prop_representingMap_of_hasRelativeProperty_quotientStack`: for
  `i : 𝒵 ⟶ [U/R]` representable by algebraic spaces with the relative property `P`, there is a
  morphism of algebraic spaces `m : U' ⟶ U` with `P` whose range is, pointwise, the locus of `U`
  whose image in `[U/R]` lies in the essential image of `i`.
* `AlgebraicGeometry.Stack.exists_isImmersion_representingMap_of_isImmersion_quotientStack` and
  its open and closed companions: that statement at the three immersion properties.
* `AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_range_of_isImmersion_quotientStack`
  and its open and closed companions: for `i : 𝒵 ⟶ [U/R]` an immersion (respectively open,
  respectively closed immersion) of algebraic stacks, the locus of `U` whose image in `[U/R]` is
  in the essential image of `i` is an `R`-invariant locally closed (respectively open,
  respectively closed) subspace of `U`. These are the subspace steps of Stacks 0505, which is
  `AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_groupoidPresentation_of_isImmersion`
  of `StacksFrontier.AlgebraicGeometry.Stacks.ImmersionQuotientStackPresentation`.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0505](https://stacks.math.columbia.edu/tag/0505)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u t v₁ w₁

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f' : 𝒳' ⟶ 𝒴'` be a 1-morphism of categories fibred in groupoids over the big fppf site
of `S`, in arbitrary morphism and object universes, which is representable by algebraic spaces and
has the relative property `P`, and suppose it is carried by a pair of equivalences `p`, `q` onto a
1-morphism `a : 𝒜 ⟶ 𝒞` whose source and target are represented by algebraic spaces `F` and `G`.
Then the induced morphism `F ⟶ G` of representing presheaves has `P`. -/
theorem prop_representingMap_of_hasRelativeProperty_of_equivalences
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    (f' : 𝒳' ⟶ 𝒴') (hf' : IsRepresentableByAlgebraicSpaces B S hS f'.hom)
    (hP : HasRelativeProperty.{u, v₁, w₁} B S hS P f' hf')
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (p : 𝒳'.val ⥤ᵇ 𝒜.val) (q : 𝒴'.val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp f'.hom q)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F G eF eG a) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) :=
  (hasRelativeProperty_iff_prop_representingMap.{u, t} B S hS P a ha F G hF hG eF eG).mp
    ((hasRelativeProperty_iff_of_equivalences' B S hS P f' a p q α ha hf').mpr hP)

/-- Let `𝒜` and `𝒞` be categories fibred in groupoids over the big fppf site of `S` represented
by presheaves `F` and `G` through chosen equivalences over the site, and let `a : 𝒜 ⟶ 𝒞` be a
1-morphism. A section `u` of `G` over `W` is in the range of the induced morphism `F ⟶ G` exactly
when it is the section named by `a z` for some object `z` of `𝒜` lying over `W`. -/
theorem mem_range_representingMap_iff_exists_sectionOfObj
    (𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (a : 𝒜 ⟶ 𝒞) (W : (BigFppfOver B S hS)ᵒᵖ) (u : G.obj W) :
    u ∈ (Subfunctor.range (representingMap B S hS 𝒜 𝒞 F G eF eG a)).obj W ↔
      ∃ (z : 𝒜.val.obj) (h : 𝒜.val.p.obj z = W.unop),
        PresheafOfCategories.sectionOfObj eG ((CatFiberedInGroupoids.homFunctor a).obj z)
          ((Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) z).trans h) = u := by
  have key (z : 𝒜.val.obj) (h : 𝒜.val.p.obj z = W.unop) :=
    morphismSpaceEquiv_app_sectionOfObj B S hS 𝒜 𝒞 F G eF eG
      ⟨CatFiberedInGroupoids.homFunctor a, CatFiberedInGroupoids.homFunctor_comp_p a⟩ z h
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨z, h, hz⟩ := PresheafOfCategories.exists_sectionOfObj eF (W := W.unop) s
    exact ⟨z, h, by rwa [← key z h, hz]⟩
  · rintro ⟨z, h, hz⟩
    exact ⟨PresheafOfCategories.sectionOfObj eF z h, (key z h).trans hz⟩

section Quotient

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, let `P` be a property of morphisms of algebraic spaces over `S`
stable under base change and local on the target for the fppf precoverage, and let
`i : 𝒵 ⟶ [U/R]` be a 1-morphism over the big fppf site which is representable by algebraic spaces
and has the relative property `P`. Then there is an algebraic space `U'` over `S` and a morphism
`m : U' ⟶ U` of algebraic spaces with `P` whose range is, pointwise, the locus of `U` whose image
in `[U/R]` lies in the essential image of `i`. -/
theorem exists_prop_representingMap_of_hasRelativeProperty_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} C S hS)]
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (hP : HasRelativeProperty.{u, u + 1, u + 1, t} C S hS P i hi) :
    ∃ (U' : AlgebraicSpaces C S hS) (m : U' ⟶ G.objects), P m ∧
      ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
        u ∈ (Subfunctor.range m.hom).obj W ↔
          i.hom.toFunctor.essImage
            ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩) := by
  set Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
    (quotientStackProjectionHom G) i with hQdef
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
      (quotientStackProjectionHom G) i
  have hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} C S hS _ _ _
      i (quotientStackProjectionHom G) Q hQ hi
  have hObj : IsRepresentableByAlgebraicSpace C S hS (liftedObjectSpace G) :=
    isRepresentableByAlgebraicSpace_liftedObjectSpace G
  have hApex : IsRepresentableByAlgebraicSpace C S hS Q.pt :=
    isRepresentableByAlgebraicSpace_of_representable C S hS Q.pt (liftedObjectSpace G)
      Q.fst hQfst hObj
  obtain ⟨F, hF, ⟨eF⟩⟩ := hApex
  let 𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS) :=
    fibredCategory C S hS F
  let 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS) :=
    fibredCategory C S hS G.objects.obj
  let p : Q.pt.val ⥤ᵇ 𝒜.val := ⟨eF.hom.functor, eF.hom.w⟩
  let pinv : 𝒜.val ⥤ᵇ Q.pt.val := ⟨eF.inv.functor, eF.inv.w⟩
  let q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val := objectSpaceLiftDown G
  have : Functor.IsEquivalence p.toFunctor := eF.isEquivalence_hom_functor
  have : Functor.IsEquivalence q.toFunctor :=
    (ULiftHom.equiv (C := (fibredCategory C S hS G.objects.obj).val.obj)).isEquivalence_inverse
  let a : 𝒜 ⟶ 𝒞 :=
    Bicategory.InducedBicategory.mkHom (BasedFunctor.comp pinv
      (BasedFunctor.comp Q.fst.hom q))
  have ha : IsRepresentableByAlgebraicSpaces C S hS a.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace C S hS a
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS F hF)
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS G.objects.obj G.objects.property)
  let α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight eF.unitIso.symm (Q.fst.hom.toFunctor ⋙ q.toFunctor))
      (fun x => by
        have := eF.isHomLift_unitIso_inv_app x
        exact Functor.isHomLift_map_of_comp_eq (BasedFunctor.comp Q.fst.hom q).w
          (𝟙 (Q.pt.val.p.obj x)) (eF.unitIso.inv.app x))
  let e𝒜 : StacksRepresentableCFG.EquivalenceOver
    𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p := .refl _
  let e𝒞 : StacksRepresentableCFG.EquivalenceOver
    𝒞.val.p (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p := .refl _
  refine ⟨⟨F, hF⟩, ObjectProperty.homMk (representingMap C S hS 𝒜 𝒞 F G.objects.obj
    e𝒜 e𝒞 a), ?_, ?_⟩
  · exact prop_representingMap_of_hasRelativeProperty_of_equivalences.{u, t} C S hS P Q.fst hQfst
      (hasRelativeProperty_baseChange.{u, u + 1, u} C S hS P _ _ _ i
        (quotientStackProjectionHom G) Q hQ hi hP)
      a ha p q α F G.objects.obj hF G.objects.property e𝒜 e𝒞
  intro W u
  refine (mem_range_representingMap_iff_exists_sectionOfObj C S hS 𝒜 𝒞 F G.objects.obj
    e𝒜 e𝒞 a W u).trans ⟨?_, ?_⟩
  · rintro ⟨z, h, hz⟩
    have hb : 𝒞.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj z) = W.unop :=
      (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) z).trans h
    have efib := PresheafOfCategories.fiberIsoOfSectionOfObj_eq e𝒞
      (z' := (⟨W.unop, Discrete.mk u⟩ :
        (presheafOfCategories (G.objects.obj ⋙ typeToCat)).obj)) hb rfl hz
    exact ⟨(pinv.toFunctor.obj z).y, ⟨(pinv.toFunctor.obj z).iso.symm ≪≫
      (quotientStackProjection G).toFunctor.mapIso
        (Functor.Fiber.fiberInclusion.mapIso efib)⟩⟩
  · intro hess
    obtain ⟨P, hP⟩ :=
      (essImage_quotientStackProjection_iff_exists_twoFibreProductSquare.{u, u + 1}
        𝒵 i W u).mp hess
    have hPbase : Q.pt.val.p.obj P = W.unop := (hP ▸ P.hx).symm
    have hb : 𝒞.val.p.obj ((BasedFunctor.comp Q.fst.hom q).toFunctor.obj P) = W.unop :=
      (BasedFunctor.w_obj (BasedFunctor.comp Q.fst.hom q) P).trans hPbase
    have hname : PresheafOfCategories.sectionOfObj e𝒞
        ((BasedFunctor.comp Q.fst.hom q).toFunctor.obj P) hb = u :=
      (PresheafOfCategories.sectionOfObj_eq_of_obj_eq e𝒞 e𝒞 _
        (⟨W.unop, Discrete.mk u⟩ : (presheafOfCategories (G.objects.obj ⋙ typeToCat)).obj)
        hb rfl (congrArg (ULiftHom.objDown.{u + 1, u + 1}) hP)).trans
        (PresheafOfCategories.sectionOfObj_refl _)
    have := eF.isHomLift_unitIso_hom_app P
    have hlift : 𝒞.val.p.IsHomLift (𝟙 (Q.pt.val.p.obj P))
        ((BasedFunctor.comp Q.fst.hom q).toFunctor.map (eF.unitIso.hom.app P)) :=
      BasedFunctor.preserves_isHomLift (BasedFunctor.comp Q.fst.hom q)
        (𝟙 (Q.pt.val.p.obj P)) (eF.unitIso.hom.app P)
    rw [hPbase] at hlift
    exact ⟨p.toFunctor.obj P, (BasedFunctor.w_obj p P).trans hPbase,
      (PresheafOfCategories.sectionOfObj_eq_of_hom e𝒞 hb _
        ((BasedFunctor.comp Q.fst.hom q).toFunctor.map (eF.unitIso.hom.app P))
        hlift).symm.trans hname⟩

/-- Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `i : 𝒵 ⟶ [U/R]` be an
immersion which is representable by algebraic spaces. Then there is an algebraic space `U'` over
`S` and an immersion of algebraic spaces `m : U' ⟶ U` whose range is the locus of `U` whose image
in `[U/R]` is in the essential image of `i`. -/
theorem exists_isImmersion_representingMap_of_isImmersion_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (himm : IsImmersion C S hS i) :
    ∃ (U' : AlgebraicSpaces C S hS) (m : U' ⟶ G.objects),
      Space.IsImmersion C S hS m.hom ∧
        ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
          u ∈ (Subfunctor.range m.hom).obj W ↔
            i.hom.toFunctor.essImage
              ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩) := by
  have : (Space.immersionProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} C S hS) :=
    Space.isImmersion_isLocalAtTarget_fppf C S hS
  exact exists_prop_representingMap_of_hasRelativeProperty_quotientStack.{u, u} G
    (Space.immersionProperty C S hS) i hi himm

/-- The open-immersion case of
`AlgebraicGeometry.Stack.exists_isImmersion_representingMap_of_isImmersion_quotientStack`: for an
open immersion `i : 𝒵 ⟶ [U/R]` the morphism `m : U' ⟶ U` is an open immersion. -/
theorem exists_isOpenImmersion_representingMap_of_isOpenImmersion_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (hopen : IsOpenImmersion C S hS i) :
    ∃ (U' : AlgebraicSpaces C S hS) (m : U' ⟶ G.objects),
      Space.IsOpenImmersion C S hS m.hom ∧
        ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
          u ∈ (Subfunctor.range m.hom).obj W ↔
            i.hom.toFunctor.essImage
              ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩) := by
  have : (Space.openImmersionProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} C S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage C S hS)
  exact exists_prop_representingMap_of_hasRelativeProperty_quotientStack.{u, u} G
    (Space.openImmersionProperty C S hS) i hi hopen

/-- The closed-immersion case of
`AlgebraicGeometry.Stack.exists_isImmersion_representingMap_of_isImmersion_quotientStack`: for a
closed immersion `i : 𝒵 ⟶ [U/R]` the morphism `m : U' ⟶ U` is a closed immersion. -/
theorem exists_isClosedImmersion_representingMap_of_isClosedImmersion_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (hclosed : IsClosedImmersion C S hS i) :
    ∃ (U' : AlgebraicSpaces C S hS) (m : U' ⟶ G.objects),
      Space.IsClosedImmersion C S hS m.hom ∧
        ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
          u ∈ (Subfunctor.range m.hom).obj W ↔
            i.hom.toFunctor.essImage
              ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩) := by
  have : (Space.closedImmersionProperty C S hS).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u} C S hS) :=
    Space.isClosedImmersion_isLocalAtTarget_fpqc C S hS
  have : (Space.closedImmersionProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} C S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage C S hS)
  exact exists_prop_representingMap_of_hasRelativeProperty_quotientStack.{u, u} G
    (Space.closedImmersionProperty C S hS) i hi hclosed

/-- Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, and let `i : 𝒵 ⟶ [U/R]` be an immersion which is representable by
algebraic spaces. Then the locus of `U` whose image in `[U/R]` lies in the essential image of `i`
is an `R`-invariant locally closed subspace `Z ⊆ U`; it is the range of an immersion of algebraic
spaces `m : U' ⟶ U`.

This is the subspace step of Stacks 0505. The full statement, with the presentation
`[Z/R_Z] ⟶ 𝒵` and the 2-commutative triangle, is
`AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_groupoidPresentation_of_isImmersion`. -/
theorem exists_isInvariantLocallyClosed_range_of_isImmersion_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (himm : IsImmersion C S hS i) :
    ∃ (U' : AlgebraicSpaces C S hS) (m : U' ⟶ G.objects),
      Space.IsImmersion C S hS m.hom ∧
        IsInvariantLocallyClosed G (Subfunctor.range m.hom) ∧
        ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
          u ∈ (Subfunctor.range m.hom).obj W ↔
            i.hom.toFunctor.essImage
              ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩) := by
  obtain ⟨U', m, hm, hmem⟩ :=
    exists_isImmersion_representingMap_of_isImmersion_quotientStack G i hi himm
  exact ⟨U', m, hm,
    isInvariantLocallyClosed_range_of_isImmersion_essImage i.hom m hm hmem, hmem⟩

/-- The open-immersion case of
`AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_range_of_isImmersion_quotientStack`: the
locus is an `R`-invariant open subspace of `U`. -/
theorem exists_isInvariantOpen_range_of_isOpenImmersion_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (hopen : IsOpenImmersion C S hS i) :
    ∃ (U' : AlgebraicSpaces C S hS) (m : U' ⟶ G.objects),
      Space.IsOpenImmersion C S hS m.hom ∧
        IsInvariantOpen G (Subfunctor.range m.hom) ∧
        ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
          u ∈ (Subfunctor.range m.hom).obj W ↔
            i.hom.toFunctor.essImage
              ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩) := by
  obtain ⟨U', m, hm, hmem⟩ :=
    exists_isOpenImmersion_representingMap_of_isOpenImmersion_quotientStack G i hi hopen
  exact ⟨U', m, hm,
    isInvariantOpen_range_of_isOpenImmersion_essImage i.hom m hm hmem, hmem⟩

/-- The closed-immersion case of
`AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_range_of_isImmersion_quotientStack`: the
locus is an `R`-invariant closed subspace of `U`. -/
theorem exists_isInvariantClosed_range_of_isClosedImmersion_quotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A)
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (hclosed : IsClosedImmersion C S hS i) :
    ∃ (U' : AlgebraicSpaces C S hS) (m : U' ⟶ G.objects),
      Space.IsClosedImmersion C S hS m.hom ∧
        IsInvariantClosed G (Subfunctor.range m.hom) ∧
        ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
          u ∈ (Subfunctor.range m.hom).obj W ↔
            i.hom.toFunctor.essImage
              ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩) := by
  obtain ⟨U', m, hm, hmem⟩ :=
    exists_isClosedImmersion_representingMap_of_isClosedImmersion_quotientStack G i hi hclosed
  exact ⟨U', m, hm,
    isInvariantClosed_range_of_isClosedImmersion_essImage i.hom m hm hmem, hmem⟩

end Quotient

end AlgebraicGeometry.Stack

end
