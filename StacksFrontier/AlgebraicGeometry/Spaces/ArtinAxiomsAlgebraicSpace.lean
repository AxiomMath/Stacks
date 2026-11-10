module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafArtinAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace
import all StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion

/-!
# Artin's axioms for algebraic spaces (Stacks 07Y1)

**Stacks 07Y1.** Let `S` be a locally Noetherian scheme and `F : (Sch/S)_{fppf}ᵒᵖ ⥤ Sets` a
functor such that `Δ : F ⟶ F × F` is representable by algebraic spaces, `F` satisfies Artin's
axioms [-1], [0], [1], [2], [3], [4], [5] of Section 07XZ, and the local rings of `S` at its finite
type points are G-rings. Then `F` is an algebraic space.

The proof is the source's direct atlas argument. Stacks 07XY, applied to the category fibred in
sets `𝒮_F` attached to `F`, gives for every finite type field-valued point of `F` a smooth
neighbourhood of finite type; the coproduct `U = ⨿ U_{k, x₀}` of these neighbourhoods, indexed by
a set thanks to axiom [-1] (Stacks 000R), maps to `F` by a morphism which is smooth and, by
Stacks 07WI and Stacks 02J4, surjective. Bootstrap, Lemma 07WF — whose input is that `F` is a
sheaf for the *étale* topology, axiom [0] — then makes `F` an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.exists_smooth_surjective_atlas_of_isStackInGroupoids_etale`: a
  category fibred in groupoids which is an étale stack, with representable diagonal, which
  satisfies axioms [-1] and [1] and in which every finite type field-valued object has a smooth
  neighbourhood of finite type (the conclusion of Stacks 07XY) has a surjective smooth 1-morphism
  from a scheme. This is the atlas half of the proof of Stacks 07Y4, with the stack condition
  taken for the étale topology, as in the source's axiom [0].
* `AlgebraicGeometry.Space.exists_locallyOfFiniteType_smooth_surjective_atlas_of_artinAxioms`:
  the smooth surjective atlas, from a scheme locally of finite type over `S`, of a category
  fibred in setoids satisfying Artin's axioms.
* `AlgebraicGeometry.Space.isAlgebraicSpace_isoClassPresheafModel_of_artinAxioms`: the core of
  the proof, for a category fibred in setoids, concluding that the model of its presheaf of
  isomorphism classes is an algebraic space.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_artinAxioms`: **Stacks 07Y1**.

## Implementation notes

*The axioms.* Following Section 07XZ, axioms [2], [3], [4] and [5] for `F` are the
Rim–Schlessinger condition, the finite dimensionality of the tangent spaces, the effectivity of
formal objects and openness of versality for the category fibred in sets `𝒮_F`
(`AlgebraicGeometry.Stack.fibredCategory`): the source does not distinguish a category cofibred
in sets over `𝒞_Λ` from the functor it defines (Remarks 06GK, 06GP), so these are stated exactly
as the fibred-in-groupoids criterion Stacks 07Y4 states them. For a functor axiom [3] is the
tangent-space condition alone, a category fibred in sets having no infinitesimal automorphisms.
Axioms [-1], [0] and [1] are conditions on `F` itself: [-1] bounds the cardinalities `|F(Spec k)|`
for the finite type fields `k` over `S` by the size of one object of the site, [0] is the étale
sheaf condition and [1] is limit preservation in the sense of Limits of Spaces, Definition 049J,
for index categories in the universe of the site (the size the source's directed sets have).
`StacksFrontier.AlgebraicGeometry.Stacks.PresheafArtinAxioms` translates these three, and the
diagonal condition, into the corresponding conditions on `𝒮_F`.

*Openness of versality.* Axiom [5] is written out — for every scheme `U` locally of finite type
over `S`, every object of `𝒮_F` over `U` and every finite type point at which it is versal, there
is an open neighbourhood at whose finite type points it is versal — rather than through
`AlgebraicGeometry.IsOpenVersality`. That predicate asks its fibred category to be fibred in
groupoids over all schemes over `S`, which a category over the bounded big fppf site of `S`
cannot be; the written-out form is the source's definition over the site, and is the form in
which Stacks 07Y4 and Stacks 07Y5 take it.

*Why not Stacks 07Y4 followed by Stacks 04SZ.* Axiom [0] for `F` is the étale sheaf condition,
and an étale sheaf is an fppf sheaf here only once it is known to be an algebraic space. The proof
therefore runs through the atlas directly and closes with Stacks 07WF, which takes the étale
condition, as the source's proof does.
Its bootstrap input, Stacks 04S6 part (1), is the library's
`AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`.

## References

* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 07XY](https://stacks.math.columbia.edu/tag/07XY)
* [Stacks Project, Tag 07WF](https://stacks.math.columbia.edu/tag/07WF)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a representative of every isomorphism class of the fibre of `p` over `T` has a morphism to
`x` lying over some `a : T ⟶ W`, then so does every object of that fibre. -/
theorem exists_isHomLift_of_exists_isHomLift_out {𝒮 𝒳 : Type*} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮) {T W : 𝒮} {x : 𝒳}
    (h : ∀ q : Quotient (isIsomorphicSetoid (p.Fiber T)),
      ∃ (a : T ⟶ W) (r : q.out.1 ⟶ x), p.IsHomLift a r)
    (y : p.Fiber T) : ∃ (a : T ⟶ W) (r : y.1 ⟶ x), p.IsHomLift a r := by
  have hiso : IsIsomorphic (Quotient.out (Quotient.mk (isIsomorphicSetoid _) y)) y :=
    Quotient.mk_out (s := isIsomorphicSetoid _) y
  obtain ⟨a, r, hr⟩ := h (Quotient.mk _ y)
  have hψ : p.IsHomLift (𝟙 T) hiso.some.inv.1 := hiso.some.inv.2
  exact ⟨a, hiso.some.inv.1 ≫ r, IsHomLift.comp_lift_id_left' p T _ a r⟩

private theorem locallyOfFiniteType_finiteTypeCoproduct {ι : Type u}
    (U : ι → BigFppfOver B S hS) (hι : Cardinal.mk ι < B.cutoff)
    (hU : ∀ i, Deformation.Artin.IsFiniteTypeOver B S hS (U i)) :
    LocallyOfFiniteType (B.inclusion.map (finiteTypeCoproduct B S hS U hι hU).hom) := by
  change LocallyOfFiniteType (Sigma.desc fun i => B.inclusion.map (U i).hom)
  let : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) fun i => (hU i).1

private theorem hasRelativeProperty_smooth_of_open_cover
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {W : BigFppfOver B S hS} (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g)
    {I : Type u} (U : I → BigFppfOver B S hS) (j : ∀ i, U i ⟶ W)
    (hj : ∀ i, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcover : ∀ w : W.left.1, ∃ i u, ((BigFppfOver.toScheme B S hS).map (j i)) u = w)
    (f : ∀ i, (schemeFibredCategory B S hS (U i)).val ⥤ᵇ 𝒳.val)
    (hrestr : ∀ i, Nonempty (precomposeSchemePoint 𝒳.val.p (j i) g ≅ f i))
    (hf : ∀ i, ∃ _hrep : IsRepresentableByAlgebraicSpaces B S hS (f i),
      ∀ (V : BigFppfOver B S hS) (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
        (_hy : y ⋙ 𝒳.val.p = Over.map V.hom)
        (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory B S hS (U i)).val.p 𝒳.val.p y (f i).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsSmooth B S hS
          (algebraicSpaceMap B S hS V
            ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom) :
    HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.smoothMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒳) hrep := by
  intro V y hy F hF eF
  apply (isSmooth_algebraicSpaceMap_iff_relocalized B S hS V F hF).mpr
  apply isSmooth_relocalized_of_open_cover B S hS 𝒳.val.p 𝒳.property W
    g.toFunctor g.w U j hj hcover V y hy F hF eF.some
  intro i
  obtain ⟨hfi, hsmi⟩ := hf i
  obtain ⟨G, hG, ⟨eG⟩⟩ := hfi V y hy
  let ε := (hrestr i).some
  let e : (Over.map (j i) ⋙ g.toFunctor) ≅ (f i).toFunctor :=
    (BasedNatTrans.forgetful _ _).mapIso ε
  have he : ∀ t, 𝒳.val.p.IsHomLift (𝟙 ((Over.forget (U i)).obj t)) (e.hom.app t) :=
    fun t => ε.hom.isHomLift' t
  refine ⟨G, hG, ⟨reindexSndRepresentingEquivalence (Over.map V.hom)
    (Over.forget (U i)) 𝒳.val.p y e he _ eG⟩, ?_⟩
  exact (isSmooth_algebraicSpaceMap_iff_relocalized B S hS V G hG).mp
    (hsmi V y hy G hG ⟨eG⟩)

private theorem hasRelativeProperty_surjective_of_field_models [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    {W : BigFppfOver B S hS} (z : 𝒳.val.p.Fiber W)
    (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g)
    (heval : Nonempty ((Functor.twoYonedaEvaluation 𝒳.val.p W).obj g ≅ z))
    (hmodels : ∀ (d : finiteTypeFieldBaseData S)
      (q : Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1)))),
      ∃ (a : fieldBaseOver B S hS d.1 ⟶ W) (r : q.out.1 ⟶ z.1), 𝒳.val.p.IsHomLift a r)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒳) hrep) :
    HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.surjectiveMorphismProperty B S hS)
      (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒳) hrep :=
  hasRelativeProperty_of_affine_locallyOfFinitePresentation_univ
    B S hS (Space.surjectiveMorphismProperty B S hS) (𝒳 := schemeFibredCategory B S hS W)
    (𝒴 := 𝒳) g hrep
    (isLimitPreservingOverTerminal_of_isLimitPreserving.{u, u, u} B S hS 𝒳 hlimit)
    fun V _ hlfp y hy F hF e => by
      let : LocallyOfFinitePresentation (B.inclusion.map V.hom) := hlfp
      exact isSurjective_of_field_models B S hS 𝒳 W z g heval
        (fun d => exists_isHomLift_of_exists_isHomLift_out 𝒳.val.p (hmodels d))
        V y hy F hF e.some (hsmooth V y hy F hF e)

/-- **The atlas of Artin's criterion, for an étale stack, with its scheme locally of finite
type over `S`.** Under the hypotheses of
`AlgebraicGeometry.Stack.exists_smooth_surjective_atlas_of_isStackInGroupoids_etale`, the scheme
`W` of the atlas can be taken locally of finite type over `S`: it is a coproduct of schemes of
finite type over `S`. -/
theorem exists_locallyOfFiniteType_smooth_surjective_atlas_of_isStackInGroupoids_etale
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hsize : IsSizeBounded B S hS 𝒳)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hnbhd : HasSmoothFiniteTypeNeighborhoods B S hS 𝒳) :
    ∃ (W : BigFppfOver B S hS), LocallyOfFiniteType (B.inclusion.map W.hom) ∧
      ∃ (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val)
      (hrep : IsRepresentableByAlgebraicSpaces B S hS g),
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.surjectiveMorphismProperty B S hS)
          (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒳) hrep ∧
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.smoothMorphismProperty B S hS)
          (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒳) hrep := by
  classical
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_bounded_fieldFiber_index B S hS 𝒳 hsize
  let d (i : I) := (eI i).1
  let k (i : I) := FreeCommRing S.size.out ⧸ (d i).1.2.1.1
  let (i : I) : Field (k i) := fieldBaseField S (d i).1
  choose U x hx u₀ e r f hU using fun i : I =>
    hnbhd (k i) (fieldBaseMap S (d i).1) (eI i).2.out.1
      (congrArg (Over.post B.inclusion).obj (eI i).2.out.2)
      (d i).2.1 (d i).2.2
      ((fieldBaseMap S (d i).1) (IsLocalRing.closedPoint (k i))) rfl
  have hfiniteU (i : I) : Deformation.Artin.IsFiniteTypeOver B S hS (U i) :=
    ⟨(hU i).1, (hU i).2.1⟩
  let W := finiteTypeCoproduct B S hS U hI hfiniteU
  let j := finiteTypeCoproductι B S hS U hI hfiniteU
  obtain ⟨xW, hxW⟩ := exists_fiber_of_coproduct B S hS 𝒳.val.p hstack U W j
    (Iso.refl _) (fun i => Category.comp_id _) (fun i => ⟨x i, hx i⟩)
  let ev := Functor.twoYonedaEvaluation 𝒳.val.p W
  let : ev.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence 𝒳.val.p 𝒳.property W
  let g := ev.objPreimage xW
  have hrestr (i : I) : Nonempty (precomposeSchemePoint 𝒳.val.p (j i) g ≅ f i) := by
    apply schemePoint_iso_of_evaluation_iso 𝒳.val.p 𝒳.property (U i)
    exact ⟨precomposeSchemePoint_evaluationIso 𝒳.val.p 𝒳.property (j i) g ≪≫
      Functor.pullbackFiberIso (ev.objObjPreimageIso xW) (j i) ≪≫
      (hxW i).some ≪≫ (hU i).2.2.2.2.2.1.some.symm⟩
  have hmodels₀ (q : Σ d : finiteTypeFieldBaseData S,
      Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber (fieldBaseOver B S hS d.1)))) :
      ∃ (a : fieldBaseOver B S hS q.1.1 ⟶ W) (r : q.2.out.1 ⟶ xW.1),
        𝒳.val.p.IsHomLift a r := by
    obtain ⟨i, rfl⟩ := eI.surjective q
    let a := eqToHom (eI i).2.out.2.symm ≫ 𝒳.val.p.map (r i) ≫ eqToHom (hx i)
    obtain ⟨s, hs⟩ := exists_hom_to_glued_object 𝒳.val.p (j i) xW
      ⟨x i, hx i⟩ (hxW i).some (eI i).2.out a (r i)
      (IsHomLift.of_fac 𝒳.val.p a (r i) (eI i).2.out.2 (hx i) rfl)
    exact ⟨a ≫ j i, s, hs⟩
  have hrep : IsRepresentableByAlgebraicSpaces B S hS g :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp hdiag) W g
  have hsmooth := hasRelativeProperty_smooth_of_open_cover B S hS 𝒳 g hrep U j
      (finiteTypeCoproductι_isOpenImmersion B S hS U hI hfiniteU)
      (finiteTypeCoproductι_jointly_surjective B S hS U hI hfiniteU) f hrestr
      fun i => (hU i).2.2.2.2.2.2
  exact ⟨W, locallyOfFiniteType_finiteTypeCoproduct B S hS U hI hfiniteU, g, hrep,
    hasRelativeProperty_surjective_of_field_models B S hS 𝒳 hlimit xW g hrep
      ⟨ev.objObjPreimageIso xW⟩ (fun _ q => hmodels₀ ⟨_, q⟩) hsmooth, hsmooth⟩

/-- **The atlas of Artin's criterion, for an étale stack.** A category fibred in groupoids over a
locally Noetherian scheme `S` which is a stack in groupoids for the étale topology, whose diagonal
is representable by algebraic spaces, which satisfies axioms [-1] and [1], and every finite type
field-valued object of which has a smooth neighbourhood of finite type (the conclusion of
Stacks 07XY), receives a 1-morphism from the category of a scheme which is representable by
algebraic spaces, surjective and smooth.

This is the atlas half of
`AlgebraicGeometry.Stack.isAlgebraicStack_of_hasSmoothFiniteTypeNeighborhoods`, whose proof uses
the stack condition only through the étale topology. -/
theorem exists_smooth_surjective_atlas_of_isStackInGroupoids_etale [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hsize : IsSizeBounded B S hS 𝒳)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hnbhd : HasSmoothFiniteTypeNeighborhoods B S hS 𝒳) :
    ∃ (W : BigFppfOver B S hS) (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val)
      (hrep : IsRepresentableByAlgebraicSpaces B S hS g),
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.surjectiveMorphismProperty B S hS)
          (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒳) hrep ∧
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (Space.smoothMorphismProperty B S hS)
          (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒳) hrep := by
  obtain ⟨W, -, g, hrep, hsurj, hsmooth⟩ :=
    exists_locallyOfFiniteType_smooth_surjective_atlas_of_isStackInGroupoids_etale B S hS 𝒳 hdiag
      hsize hstack hlimit hnbhd
  exact ⟨W, g, hrep, hsurj, hsmooth⟩

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Axiom [-1] of Section 07XZ.** If the cardinalities of the values of `F` on the finite type
fields over `S` are bounded by the size of one object of the site, then so are the cardinalities
of the sets of isomorphism classes of the fibres of `𝒮_F` over them: those sets are the values
of `F`. -/
theorem isSizeBounded_fibredCategory (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hsize : ∃ T : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
          Cardinal.mk (F.obj (op U)) ≤ T.left.1.size) :
    IsSizeBounded B S hS (fibredCategory B S hS F) := by
  obtain ⟨T, hT⟩ := hsize
  refine ⟨T, fun U k _ hk hU => ?_⟩
  let : (fibredCategory B S hS F).val.p.IsFibered :=
    (fibredCategory B S hS F).isFiberedInGroupoids.isFibered
  have e : (fibredCategory B S hS F).val.p.isoClassPresheaf.obj (op U) ≃ F.obj (op U) :=
    PresheafOfCategories.elementsIsoClassEquiv F
      (StacksRepresentableCFG.EquivalenceOver.refl _) U
  exact (Cardinal.lift_mk_eq'.2 ⟨e⟩).trans_le (Cardinal.lift_le.2 (hT U k hk hU))

/-- **The atlas of Artin's axioms for a category fibred in setoids.** Under the hypotheses of
`AlgebraicGeometry.Space.isAlgebraicSpace_isoClassPresheafModel_of_artinAxioms`, `𝒵` receives a
1-morphism from the category of a scheme `W` locally of finite type over `S` which is
representable by algebraic spaces, surjective and smooth: the atlas of the proof of Stacks 07Y1.
-/
theorem exists_locallyOfFiniteType_smooth_surjective_atlas_of_artinAxioms [IsLocallyNoetherian S]
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    [𝒵.val.p.IsFibered] [𝒵.val.p.IsFiberedInSetoids]
    [CategoryTheory.FunctorToTypes.Small.{u} 𝒵.val.p.isoClassPresheaf]
    (hdiag : HasRepresentableDiagonal B S hS 𝒵)
    (hsize : IsSizeBounded B S hS 𝒵)
    (hsheaf : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS))
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵.val.p))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒵)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒵.val.p 𝒵.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒵)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒵.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒵.val.p 𝒵.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒵.val.obj) (hy : (𝒵.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒵.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒵.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ (W : BigFppfOver B S hS), LocallyOfFiniteType (B.inclusion.map W.hom) ∧
      ∃ (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒵.val)
        (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS g),
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (surjectiveMorphismProperty B S hS)
            (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒵) hrep ∧
          HasRelativeProperty.{u, u, u + 1, u + 1} B S hS (smoothMorphismProperty B S hS)
            (Bicategory.InducedBicategory.mkHom g : schemeFibredCategory B S hS W ⟶ 𝒵) hrep :=
  exists_locallyOfFiniteType_smooth_surjective_atlas_of_isStackInGroupoids_etale B S hS 𝒵 hdiag
    hsize
    ((PresheafOfCategories.isStackInSetoids_of_equivalenceOver_discreteProjection (𝒳 := 𝒵.val)
      _ _ hsheaf (isoClassEquivalenceOverModel B S hS 𝒵.val.p)).isStack.isStackInGroupoids
      𝒵.isFiberedInGroupoids)
    hlimit
    (hasSmoothFiniteTypeNeighborhoods_of_artinAxioms.{u, u, u} B S hS 𝒵 hdiag hlimit hRS
      htangent heffective hopen hG)

/-- **Artin's axioms for a category fibred in setoids (the core of Stacks 07Y1).** Let `S` be a
locally Noetherian scheme and `𝒵` a category fibred in setoids over the big fppf site of `S`,
with presheaf of isomorphism classes modelled in `Type u`. Assume that the diagonal of `𝒵` is
representable by algebraic spaces, that `𝒵` satisfies axiom [-1], that the model of its presheaf
of isomorphism classes is a sheaf for the étale topology (axiom [0]), that `𝒵` is limit preserving
(axiom [1]), satisfies the Rim–Schlessinger condition (axiom [2]), has finite dimensional tangent
spaces (axiom [3]), effective formal objects (axiom [4]) and open versality (axiom [5], written
out as in Stacks 07Y4), and that the local rings of `S` at its finite type points are G-rings.
Then the model of its presheaf of isomorphism classes is an algebraic space. -/
theorem isAlgebraicSpace_isoClassPresheafModel_of_artinAxioms [IsLocallyNoetherian S]
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    [𝒵.val.p.IsFibered] [𝒵.val.p.IsFiberedInSetoids]
    [CategoryTheory.FunctorToTypes.Small.{u} 𝒵.val.p.isoClassPresheaf]
    (hdiag : HasRepresentableDiagonal B S hS 𝒵)
    (hsize : IsSizeBounded B S hS 𝒵)
    (hsheaf : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS))
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵.val.p))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒵)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒵.val.p 𝒵.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒵)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒵.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒵.val.p 𝒵.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒵.val.obj) (hy : (𝒵.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒵.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒵.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace B S hS (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵.val.p) := by
  classical
  obtain ⟨W, -, g, hrep, hsurj, hsmooth⟩ :=
    exists_locallyOfFiniteType_smooth_surjective_atlas_of_artinAxioms B S hS 𝒵 hdiag hsize
      hsheaf hlimit hRS htangent heffective hopen hG
  -- the atlas as a morphism of the `Type u` models of the presheaves of isomorphism classes
  let 𝒰 := schemeFibredCategory B S hS W
  obtain ⟨h𝒰set, h𝒰iso⟩ := (isRepresentableByAlgebraicSpace_iff B S hS 𝒰).1
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  let : 𝒰.val.p.IsFibered := 𝒰.isFiberedInGroupoids.isFibered
  have : CategoryTheory.FunctorToTypes.Small.{u} 𝒰.val.p.isoClassPresheaf :=
    small_isoClassPresheaf_of_isAlgebraicSpaceIsoClassPresheaf B S hS _ h𝒰iso
  have h𝒰model : IsAlgebraicSpace B S hS
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰.val.p) :=
    (isAlgebraicSpaceIsoClassPresheaf_iff_isAlgebraicSpace_isoClassPresheafModel B S hS _).1
      h𝒰iso
  let 𝒵s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒵.val inferInstance
  let 𝒰s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒰.val h𝒰set
  let fs : 𝒰s ⟶ 𝒵s := Bicategory.InducedBicategory.mkHom g
  let a := CategoryTheory.Functor.isoClassPresheafModelMap.{u} 𝒰s.val.p 𝒵s.val.p
    (CatFiberedInGroupoids.homFunctor_comp_p fs)
  have ha : IsoClassCompatible B S hS fs
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒵s.val.p) a := fun V z =>
    CategoryTheory.Functor.isoClassPresheafModelMap_app_isoClassMk.{u} 𝒰s.val.p 𝒵s.val.p _ z
  have hfrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map fs).hom := hrep
  have harep := (isoClassMap_isRepresentableByAlgebraicSpaces_iff_model.{u, u, u + 1}
    B S hS fs a ha).2 hfrep
  -- Stacks 07WF, in its form for a smooth surjective chart from an algebraic space
  exact coreCriterion B S hS hsheaf h𝒰model a harep
    ((isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS fs
      (surjectiveMorphismProperty B S hS) a ha hfrep).2 hsurj)
    ((isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS fs
      (smoothMorphismProperty B S hS) a ha hfrep).2 hsmooth)
    (bootstrap04S6QuotientSheaf B S hS)

/-- **Stacks 07Y1 (Artin's axioms for algebraic spaces).** Let `S` be a locally Noetherian scheme
and `F` a set-valued functor on the big fppf site of `S`. Assume that

1. the diagonal `Δ : F ⟶ F × F` is representable by algebraic spaces,
2. `F` satisfies Artin's axioms of Section 07XZ: [-1] the cardinalities `|F(Spec k)|`, for `k`
   running over the finite type fields over `S`, are bounded by the size of one object of the
   site; [0] `F` is a sheaf for the étale topology; [1] `F` is limit preserving (Stacks 049J);
   [2] `F` satisfies the Rim–Schlessinger condition; [3] every tangent space of `F` at a finite
   type field-valued point is finite dimensional; [4] every formal object of `F` is effective;
   [5] `F` satisfies openness of versality — axioms [2]–[5] read, as in Section 07XZ, on the
   category fibred in sets `𝒮_F`, and
3. the local rings `𝒪_{S,s}` at the finite type points `s` of `S` are G-rings.

Then `F` is an algebraic space.

Axiom [5] is written out rather than through `AlgebraicGeometry.IsOpenVersality`, which asks its
fibred category to be fibred in groupoids over all schemes over `S` and so cannot hold for a
category over the bounded big fppf site; the written-out form is the source's definition.

The proof is `AlgebraicGeometry.Space.isAlgebraicSpace_isoClassPresheafModel_of_artinAxioms` for
`𝒮_F`, whose presheaf of isomorphism classes is `F`, after the translations of Section 07XZ. -/
@[stacks 07Y1]
theorem isAlgebraicSpace_of_artinAxioms [IsLocallyNoetherian S]
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hsize : ∃ T : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
          Cardinal.mk (F.obj (op U)) ≤ T.left.1.size)
    (hF : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) F)
    (hlimit : AlgebraicGeometry.LimitPreserving.{u, u, u, u} (BigFppfOver.toScheme B S hS) F)
    (hRS : Deformation.Artin.SatisfiesRS B S hS (fibredCategory B S hS F).val.p
      (fibredCategory B S hS F).property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS (fibredCategory B S hS F))
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS (fibredCategory B S hS F).val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS (fibredCategory B S hS F).val.p
        (fibredCategory B S hS F).property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : (fibredCategory B S hS F).val.obj)
        (hy : ((fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U ((fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion)
          u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U
              ((fibredCategory B S hS F).val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace B S hS F := by
  classical
  let 𝒳 := fibredCategory B S hS F
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒳.val.p.IsFiberedInSetoids :=
    PresheafOfCategories.isFiberedInSetoids_discreteProjection F
  let eF (U : (BigFppfOver B S hS)ᵒᵖ) : 𝒳.val.p.isoClassPresheaf.obj U ≃ F.obj U :=
    PresheafOfCategories.elementsIsoClassEquiv F
      (StacksRepresentableCFG.EquivalenceOver.refl _) U.unop
  have hnatF : ∀ ⦃U V : (BigFppfOver B S hS)ᵒᵖ⦄ (f : U ⟶ V)
      (z : 𝒳.val.p.isoClassPresheaf.obj U),
      eF V (𝒳.val.p.isoClassPresheaf.map f z) = F.map f (eF U z) := fun _ _ f z =>
    PresheafOfCategories.elementsIsoClassEquiv_naturality 𝒳.isFiberedInGroupoids F
      (StacksRepresentableCFG.EquivalenceOver.refl _) f.unop z
  have : CategoryTheory.FunctorToTypes.Small.{u} 𝒳.val.p.isoClassPresheaf :=
    Functor.small_isoClassPresheaf_of_equiv 𝒳.val.p eF
  -- the model of the presheaf of isomorphism classes of `𝒮_F` is `F`
  let eModel : CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p ≅ F :=
    CategoryTheory.Functor.isoClassPresheafModelIso.{u} 𝒳.val.p eF hnatF
  exact isAlgebraicSpace_of_iso B S hS eModel
    (isAlgebraicSpace_isoClassPresheafModel_of_artinAxioms B S hS 𝒳
      (hasRepresentableDiagonal_fibredCategory B S hS hdiag)
      (isSizeBounded_fibredCategory B S hS F hsize)
      ((Presheaf.isSheaf_of_iso_iff eModel).2 hF)
      (isLimitPreserving_fibredCategory B S hS hlimit) hRS htangent heffective hopen hG)

end AlgebraicGeometry.Space

end
