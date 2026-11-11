module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChangePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.RingTheory.Henselian.HenselizationCompletion

/-!
# Henselian local rings under base change to the completion of the base ring

Let `(A, 𝔪)` be a local ring whose maximal ideal is finitely generated, let `X` be a decent
algebraic space over `Spec A` and let `Y = X ×_{Spec A} Spec A^` be its base change to the
`𝔪`-adic completion of `A`. At a point `q` of `Y` whose image `p` in `X` lies over the closed
point of `Spec A`, the canonical homomorphism `𝒪^h_{X,p} ⟶ 𝒪^h_{Y,q}` of henselian local rings
induces an isomorphism on `𝔪`-adic completions.

An elementary étale neighborhood `(U, u)` of `p` base-changes to the chart
`U ×_{Spec A} Spec A^` of `Y`, which is an elementary étale neighborhood of `q` once pointed at
the scheme point underlying the monomorphic field-valued representative of `q`. The underlying
scheme of that chart is the scheme-theoretic fibre product, so the case of schemes applies to
its local ring; the two henselian local rings are henselizations of the two local rings, and
the uniqueness of henselizations transports the isomorphism of completions through them.

## Main results

* `AlgebraicGeometry.Space.isLocalRing_henselianLocalRing`: the henselian local ring of a
  decent algebraic space at a point is a local ring.
* `AlgebraicGeometry.Space.exists_adicCompletion_ringEquiv_henselianLocalRing_of_neighborhood`:
  an isomorphism of the completions of the local rings of a pair of corresponding elementary
  étale neighborhoods induces one of the completions of the henselian local rings.
* `AlgebraicGeometry.Space.exists_adicCompletion_ringEquiv_henselianLocalRing_completionSpace`:
  the isomorphism of completions for the base change to the completion.

## References

* [Stacks Project, Tag 0BHP](https://stacks.math.columbia.edu/tag/0BHP)
* [Stacks Project, Tag 0BG5](https://stacks.math.columbia.edu/tag/0BG5)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The map on stalks induced by a morphism of schemes carrying one point to another, read
through the identification of the stalks at the two points, is a local homomorphism. -/
theorem isLocalHom_stalkCongr_comp_stalkMap {T W : Scheme.{u}} (g : T ⟶ W) {t : T} {w : W}
    (hw : g.base t = w) :
    IsLocalHom ((W.presheaf.stalkCongr (Inseparable.of_eq hw.symm)).hom ≫ g.stalkMap t).hom :=
  CommRingCat.isLocalHom_comp _ _

namespace Space

/-! ### The henselian local ring of a decent algebraic space is local -/

section Local

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (hXdec : IsDecentSpace B S hS X) (x : points B S hS X)

include hXdec in
/-- The category of elementary étale neighborhoods of a point of a decent algebraic space is
cofiltered. -/
@[stacks 0BGV "the category of elementary étale neighbourhoods of a point of a decent \
  space is cofiltered; nonemptiness by Tag 0BBP"]
theorem isCofiltered_elementaryEtaleNeighborhood :
    IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX x) :=
  ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X hX x
    ⟨(exists_affine_elementaryEtaleNeighborhood' B S hS hX hXdec x).choose⟩

/-- The henselian local ring of a decent algebraic space at a point is a local ring. -/
@[stacks 0EMY "O^h is a local ring for a decent space"]
theorem isLocalRing_henselianLocalRing :
    IsLocalRing (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)) :=
  henselianLocalRing_isLocalRing B S hS X hX x hXdec

end Local

/-! ### Transport through a pair of corresponding elementary étale neighborhoods -/

section Neighborhood

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Transport of an isomorphism of completed local rings to the henselian local rings.** Let
`E` be an elementary étale neighborhood of a point `x` of a decent algebraic space `X`, let `N`
be one of a point `y` of a decent algebraic space `Y`, and let `j : N.scheme ⟶ E.scheme` carry
the distinguished point to the distinguished point. An isomorphism of the completions of the
two local rings compatible with the map on stalks induces a local homomorphism
`𝒪^h_{X,x} ⟶ 𝒪^h_{Y,y}`, compatible with the two local rings, which induces an isomorphism on
completions. -/
theorem exists_adicCompletion_ringEquiv_henselianLocalRing_of_neighborhood
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    (x : points B S hS X) (y : points B S hS Y)
    (E : ElementaryEtaleNeighborhood B S hS X hX x)
    (N : ElementaryEtaleNeighborhood B S hS Y hY y)
    (j : N.scheme ⟶ E.scheme) (hj : j.left.1 N.point = E.point)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (E.scheme.left.1.presheaf.stalk E.point))
          (E.scheme.left.1.presheaf.stalk E.point) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (N.scheme.left.1.presheaf.stalk N.point))
          (N.scheme.left.1.presheaf.stalk N.point))
    (he : e.toRingHom.comp
        (algebraMap (E.scheme.left.1.presheaf.stalk E.point)
          (AdicCompletion (IsLocalRing.maximalIdeal (E.scheme.left.1.presheaf.stalk E.point))
            (E.scheme.left.1.presheaf.stalk E.point))) =
      (algebraMap (N.scheme.left.1.presheaf.stalk N.point)
        (AdicCompletion (IsLocalRing.maximalIdeal (N.scheme.left.1.presheaf.stalk N.point))
          (N.scheme.left.1.presheaf.stalk N.point))).comp
        ((E.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
          j.left.1.stalkMap N.point).hom) :
    letI := isLocalRing_henselianLocalRing B S hS hX hXdec x
    letI := isLocalRing_henselianLocalRing B S hS hY hYdec y
    ∃ φ : (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)) →+*
        (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)),
      IsLocalHom φ ∧
      φ.comp (stalkToHenselianLocalRing B S hS X hX x hXdec E) =
        (stalkToHenselianLocalRing B S hS Y hY y hYdec N).comp
          ((E.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
            j.left.1.stalkMap N.point).hom ∧
      ∃ E' : AdicCompletion (IsLocalRing.maximalIdeal
            (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)))
            (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal
            (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)))
            (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)),
        E'.toRingHom.comp (algebraMap _ _) = (algebraMap _ _).comp φ := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hXdec
  let := henselianLocalRing_isLocalRing B S hS Y hY y hYdec
  let := stalkAlgebra B S hS X hX x hXdec E
  let := stalkAlgebra B S hS Y hY y hYdec N
  let := henselianLocalRing_isHenselization B S hS X hX x hXdec E
  let := henselianLocalRing_isHenselization B S hS Y hY y hYdec N
  let : IsLocalHom (algebraMap (E.scheme.left.1.presheaf.stalk E.point)
      (henselianLocalRing B S hS X hX x hXdec : Type (u + 1))) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := E.scheme.left.1.presheaf.stalk E.point)
      (L := IsLocalRing.ResidueField (E.scheme.left.1.presheaf.stalk E.point))
  let : IsLocalHom (algebraMap (N.scheme.left.1.presheaf.stalk N.point)
      (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1))) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := N.scheme.left.1.presheaf.stalk N.point)
      (L := IsLocalRing.ResidueField (N.scheme.left.1.presheaf.stalk N.point))
  let : IsLocalHom
      ((E.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
        j.left.1.stalkMap N.point).hom :=
    isLocalHom_stalkCongr_comp_stalkMap j.left.1 hj
  let : Algebra (E.scheme.left.1.presheaf.stalk E.point)
      (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)) :=
    ((stalkToHenselianLocalRing B S hS Y hY y hYdec N).comp
      ((E.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
        j.left.1.stalkMap N.point).hom).toAlgebra
  let : IsLocalHom (algebraMap (E.scheme.left.1.presheaf.stalk E.point)
      (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1))) :=
    RingHom.isLocalHom_comp _ _
  let : HenselianLocalRing (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)) :=
    IsLocalRing.IsHenselization.henselian (N.scheme.left.1.presheaf.stalk N.point)
      (IsLocalRing.ResidueField (N.scheme.left.1.presheaf.stalk N.point))
  obtain ⟨ψ, hψ, -⟩ := StacksDraft.existsUnique_isLocalHom_of_indEtale
    (A := E.scheme.left.1.presheaf.stalk E.point)
    (B := (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)))
    (C := (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)))
    (StacksDraft.indEtale_of_isHenselization
      (IsLocalRing.ResidueField (E.scheme.left.1.presheaf.stalk E.point)))
    (IsLocalRing.IsHenselization.residueField_map_bijective
      (R := E.scheme.left.1.presheaf.stalk E.point)
      (Rh := (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)))).2
  have hcomp : ψ.toRingHom.comp (stalkToHenselianLocalRing B S hS X hX x hXdec E) =
      (stalkToHenselianLocalRing B S hS Y hY y hYdec N).comp
        ((E.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
          j.left.1.stalkMap N.point).hom :=
    RingHom.ext fun a ↦ ψ.commutes a
  have hψ' : IsLocalHom ψ.toRingHom := ⟨hψ.map_nonunit⟩
  obtain ⟨eTot, heTot⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_isHenselization_square
    ((E.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
      j.left.1.stalkMap N.point).hom ψ.toRingHom hcomp e
    (fun a ↦ RingHom.congr_fun he a)
  exact ⟨ψ.toRingHom, hψ', hcomp, eTot, heTot⟩

end Neighborhood

/-! ### Base change to the completion -/

noncomputable section Completion

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable (hAc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))

/-- Let `(A, 𝔪)` be a local ring with finitely generated maximal ideal, let `X` be a decent
algebraic space over `Spec A` and let `Y = X ×_{Spec A} Spec A^` be its base change to the
`𝔪`-adic completion of `A`. For a point `q` of `Y` whose image `p` in `X` lies over the closed
point of `Spec A`, the canonical local homomorphism `𝒪^h_{X,p} ⟶ 𝒪^h_{Y,q}` — the one compatible
with the local rings of a pair of corresponding elementary étale neighborhoods — induces an
isomorphism on `𝔪`-adic completions. -/
@[stacks 0BHP]
theorem exists_adicCompletion_ringEquiv_henselianLocalRing_completionSpace
    (hfg : (IsLocalRing.maximalIdeal A).FG)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (hXdec : IsDecentSpace B (Spec (.of A)) hA X)
    (q : points B (Spec (.of A)) hA (completionSpace A B hA hAc f))
    (p : points B (Spec (.of A)) hA X)
    (hp : pointsMap B (Spec (.of A)) hA (completionSpace A B hA hAc f)
      (completionProjection A B hA hAc f) q = p)
    (hclosed : pointsToScheme B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))
        (pointsMap B (Spec (.of A)) hA X f p) =
      (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A)) :
    letI hY := isAlgebraicSpace_completionSpace A B hA hAc f hX
    letI hYdec := isDecentSpace_completionSpace A B hA hAc f hX hXdec
    letI := isLocalRing_henselianLocalRing B (Spec (.of A)) hA hX hXdec p
    letI := isLocalRing_henselianLocalRing B (Spec (.of A)) hA hY hYdec q
    ∃ φ : (henselianLocalRing B (Spec (.of A)) hA X hX p hXdec : Type (u + 1)) →+*
        (henselianLocalRing B (Spec (.of A)) hA (completionSpace A B hA hAc f) hY q hYdec :
          Type (u + 1)),
      IsLocalHom φ ∧
      (∃ (E : ElementaryEtaleNeighborhood B (Spec (.of A)) hA X hX p)
          (N : ElementaryEtaleNeighborhood B (Spec (.of A)) hA
            (completionSpace A B hA hAc f) hY q)
          (j : N.scheme ⟶ E.scheme) (hj : j.left.1 N.point = E.point),
        yoneda.map j ≫ E.toSpace = N.toSpace ≫ completionProjection A B hA hAc f ∧
          φ.comp (stalkToHenselianLocalRing B (Spec (.of A)) hA X hX p hXdec E) =
            (stalkToHenselianLocalRing B (Spec (.of A)) hA (completionSpace A B hA hAc f) hY q
                hYdec N).comp
              ((E.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
                j.left.1.stalkMap N.point).hom) ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal
            (henselianLocalRing B (Spec (.of A)) hA X hX p hXdec : Type (u + 1)))
            (henselianLocalRing B (Spec (.of A)) hA X hX p hXdec : Type (u + 1)) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal
            (henselianLocalRing B (Spec (.of A)) hA (completionSpace A B hA hAc f) hY q hYdec :
              Type (u + 1)))
            (henselianLocalRing B (Spec (.of A)) hA (completionSpace A B hA hAc f) hY q hYdec :
              Type (u + 1)),
        e.toRingHom.comp (algebraMap _ _) = (algebraMap _ _).comp φ := by
  classical
  let hY := isAlgebraicSpace_completionSpace A B hA hAc f hX
  let hYdec := isDecentSpace_completionSpace A B hA hAc f hX hXdec
  let := isLocalRing_henselianLocalRing B (Spec (.of A)) hA hX hXdec p
  let := isLocalRing_henselianLocalRing B (Spec (.of A)) hA hY hYdec q
  obtain ⟨E, -, -, -⟩ :=
    exists_affine_elementaryEtaleNeighborhood' B (Spec (.of A)) hA hX hXdec p
  obtain ⟨qRep, hqClass, hqMono⟩ := IsDecentSpace.hasMonomorphicFieldRepresentative
    B (Spec (.of A)) hA (completionSpace A B hA hAc f) hYdec q
  have hqMono' : Mono (yonedaEquiv.symm qRep.value) := hqMono
  let eRep : FieldValuedPoint B (Spec (.of A)) hA (yoneda.obj E.scheme) :=
    ⟨E.scheme.left.1.residueField E.point, E.residueField_contained,
      E.scheme.left.1.fromSpecResidueField E.point ≫ E.scheme.hom.1,
      residueFieldMap B (Spec (.of A)) hA E.scheme E.point E.residueField_contained⟩
  let eX : FieldValuedPoint B (Spec (.of A)) hA X :=
    FieldValuedPoint.map B (Spec (.of A)) hA (yoneda.obj E.scheme) E.toSpace eRep
  have heXmor : fieldMorphism B (Spec (.of A)) hA X eX =
      yoneda.map (residueFieldMap B (Spec (.of A)) hA E.scheme E.point
        E.residueField_contained) ≫ E.toSpace :=
    fieldMorphism_map_yoneda B (Spec (.of A)) hA X E.toSpace eRep
  have heXmono : Mono (fieldMorphism B (Spec (.of A)) hA X eX) := by
    rw [heXmor]; exact E.mono_residueField
  have heXmono' : Mono (yonedaEquiv.symm eX.value) := heXmono
  have heXclass : eX.class B (Spec (.of A)) hA X = p := E.map_point
  let qX : FieldValuedPoint B (Spec (.of A)) hA X :=
    FieldValuedPoint.map B (Spec (.of A)) hA (completionSpace A B hA hAc f)
      (completionProjection A B hA hAc f) qRep
  have hqXmor : fieldMorphism B (Spec (.of A)) hA X qX =
      fieldMorphism B (Spec (.of A)) hA (completionSpace A B hA hAc f) qRep ≫
        completionProjection A B hA hAc f :=
    fieldMorphism_map B (Spec (.of A)) hA (completionSpace A B hA hAc f)
      (completionProjection A B hA hAc f) qRep
  have hqXclass : qX.class B (Spec (.of A)) hA X = p := by
    rw [← hp, ← hqClass]; rfl
  obtain ⟨c, hc, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
    B (Spec (.of A)) hA X hX eX qX (heXclass.trans hqXclass.symm)
  have hcArrow : yoneda.map c ≫ fieldMorphism B (Spec (.of A)) hA X eX =
      fieldMorphism B (Spec (.of A)) hA X qX := by
    change yoneda.map c ≫ yonedaEquiv.symm eX.value = yonedaEquiv.symm qX.value
    rw [yonedaEquiv_symm_naturality_left c X eX.value, hc]
  have hcompat : yoneda.map (c ≫ residueFieldMap B (Spec (.of A)) hA E.scheme E.point
        E.residueField_contained) ≫ E.toSpace =
      fieldMorphism B (Spec (.of A)) hA (completionSpace A B hA hAc f) qRep ≫
        completionProjection A B hA hAc f :=
    ((congrArg (fun k ↦ k ≫ E.toSpace) (yoneda.map_comp c
          (residueFieldMap B (Spec (.of A)) hA E.scheme E.point
            E.residueField_contained))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k ↦ yoneda.map c ≫ k) heXmor.symm))).trans (hcArrow.trans hqXmor)
  let j := pullback.fst (Over.homMk E.scheme.hom : E.scheme ⟶ Over.mk (𝟙 (B.obj hA)))
    (yoneda.preimage (completionBaseMap A B hA hAc))
  have hpb : IsPullback (yoneda.map j) (completionChartMap A B hA hAc f E.toSpace) E.toSpace
      (completionProjection A B hA hAc f) :=
    isPullback_completionChart A B hA hAc f E.toSpace
  let l := hpb.lift (yoneda.map (c ≫ residueFieldMap B (Spec (.of A)) hA E.scheme E.point
    E.residueField_contained))
    (fieldMorphism B (Spec (.of A)) hA (completionSpace A B hA hAc f) qRep) hcompat
  have hlfst : l ≫ yoneda.map j =
      yoneda.map (c ≫ residueFieldMap B (Spec (.of A)) hA E.scheme E.point
        E.residueField_contained) := hpb.lift_fst _ _ _
  have hlsnd : l ≫ completionChartMap A B hA hAc f E.toSpace =
      fieldMorphism B (Spec (.of A)) hA (completionSpace A B hA hAc f) qRep :=
    hpb.lift_snd _ _ _
  let t : FieldValuedPoint B (Spec (.of A)) hA
      (yoneda.obj (completionChart A B hA hAc E.scheme)) :=
    { carrier := qRep.carrier
      field := qRep.field
      contained := qRep.contained
      toBase := qRep.toBase
      value := yonedaEquiv l }
  have htmor : fieldMorphism B (Spec (.of A)) hA
      (yoneda.obj (completionChart A B hA hAc E.scheme)) t = l :=
    Equiv.symm_apply_apply yonedaEquiv l
  have htmono : Mono (fieldMorphism B (Spec (.of A)) hA
      (yoneda.obj (completionChart A B hA hAc E.scheme)) t ≫
      completionChartMap A B hA hAc f E.toSpace) :=
    mono_of_eq_of_mono ((congrArg (fun k ↦ k ≫ completionChartMap A B hA hAc f E.toSpace)
      htmor).trans hlsnd) hqMono
  have htval : (FieldValuedPoint.map B (Spec (.of A)) hA
      (yoneda.obj (completionChart A B hA hAc E.scheme))
      (completionChartMap A B hA hAc f E.toSpace) t).value = qRep.value :=
    (yonedaEquiv_comp l (completionChartMap A B hA hAc f E.toSpace)).symm.trans
      ((congrArg yonedaEquiv hlsnd).trans
        (yonedaEquiv_fieldMorphism B (Spec (.of A)) hA (completionSpace A B hA hAc f) qRep))
  have htq : pointsMap B (Spec (.of A)) hA
      (yoneda.obj (completionChart A B hA hAc E.scheme))
      (completionChartMap A B hA hAc f E.toSpace)
      (t.class B (Spec (.of A)) hA (yoneda.obj (completionChart A B hA hAc E.scheme))) = q := by
    rw [pointsMap_class]
    refine Eq.trans ?_ hqClass
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of A)) hA
      (completionSpace A B hA hAc f)
      ⟨qRep, ⟨𝟙 (qRep.siteObject B (Spec (.of A)) hA (completionSpace A B hA hAc f)), ?_⟩,
        FieldValuedPoint.dominates_refl B (Spec (.of A)) hA
          (completionSpace A B hA hAc f) qRep⟩
    rw [htval]
    exact Functor.map_id_apply (completionSpace A B hA hAc f)
      (Opposite.op (qRep.siteObject B (Spec (.of A)) hA (completionSpace A B hA hAc f)))
      qRep.value
  let N := elementaryEtaleNeighborhoodOfMono B (Spec (.of A)) hA hY
    (completionChart A B hA hAc E.scheme) (completionChartMap A B hA hAc f E.toSpace)
    (isEtale_completionChartMap A B hA hAc f E.toSpace E.etale_toSpace) t htmono q htq
  have hsq : yoneda.map j ≫ E.toSpace = N.toSpace ≫ completionProjection A B hA hAc f := hpb.w
  have hsite : t.value ≫ j =
      c ≫ residueFieldMap B (Spec (.of A)) hA E.scheme E.point E.residueField_contained :=
    (yonedaEquiv_comp l (yoneda.map j)).symm.trans
      ((congrArg yonedaEquiv hlfst).trans (yonedaEquiv_yoneda_map _))
  have hj : j.left.1 N.point = E.point := by
    have h3 : (BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (c ≫ residueFieldMap B (Spec (.of A)) hA E.scheme E.point E.residueField_contained)
        (IsLocalRing.closedPoint qRep.carrier) = E.point := by
      rw [(BigFppfOver.toScheme B (Spec (.of A)) hA).map_comp c
        (residueFieldMap B (Spec (.of A)) hA E.scheme E.point E.residueField_contained)]
      exact (Scheme.Hom.comp_apply _ _ _).trans
        (E.scheme.left.1.fromSpecResidueField_apply E.point _)
    calc j.left.1 N.point
        = (BigFppfOver.toScheme B (Spec (.of A)) hA).map j
            (schemePoint B (Spec (.of A)) hA (completionChart A B hA hAc E.scheme) t) := rfl
      _ = schemePoint B (Spec (.of A)) hA E.scheme
            (FieldValuedPoint.map B (Spec (.of A)) hA
              (yoneda.obj (completionChart A B hA hAc E.scheme)) (yoneda.map j) t) :=
          (schemePoint_map_yoneda B (Spec (.of A)) hA j t).symm
      _ = (BigFppfOver.toScheme B (Spec (.of A)) hA).map
            (t.value ≫ j) (IsLocalRing.closedPoint qRep.carrier) := rfl
      _ = (BigFppfOver.toScheme B (Spec (.of A)) hA).map
            (c ≫ residueFieldMap B (Spec (.of A)) hA E.scheme E.point
              E.residueField_contained) (IsLocalRing.closedPoint qRep.carrier) := by
          rw [hsite]
          rfl
      _ = E.point := h3
  have hstruct : E.toSpace ≫ f =
      yoneda.map (Over.homMk E.scheme.hom : E.scheme ⟶ Over.mk (𝟙 (B.obj hA))) := by
    rw [← yoneda.map_preimage (E.toSpace ≫ f),
      Over.mkIdTerminal.hom_ext (yoneda.preimage (E.toSpace ≫ f))
        (Over.homMk E.scheme.hom : E.scheme ⟶ Over.mk (𝟙 (B.obj hA)))]
  have hclosedE : ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
      (Over.homMk E.scheme.hom : E.scheme ⟶ Over.mk (𝟙 (B.obj hA)))) E.point =
      (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) := by
    have h1 := pointsToScheme_pointsMap_yoneda B (Spec (.of A)) hA
      (Over.homMk E.scheme.hom : E.scheme ⟶ Over.mk (𝟙 (B.obj hA)))
      (presheafPoint B (Spec (.of A)) hA E.scheme E.point E.residueField_contained)
    rw [pointsToScheme_presheafPoint] at h1
    rw [← h1, ← hstruct, pointsMap_comp_apply, E.map_point]
    exact hclosed
  obtain ⟨eStalk, heStalk⟩ := exists_adicCompletion_ringEquiv_stalkMap_of_isPullback A hfg
    ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
      (Over.homMk E.scheme.hom : E.scheme ⟶ Over.mk (𝟙 (B.obj hA))))
    ((BigFppfOver.toScheme B (Spec (.of A)) hA).map j)
    ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
      (pullback.snd (Over.homMk E.scheme.hom : E.scheme ⟶ Over.mk (𝟙 (B.obj hA)))
        (yoneda.preimage (completionBaseMap A B hA hAc))))
    (isPullback_toScheme_completionChart A B hA hAc E.scheme) N.point E.point hj hclosedE
  obtain ⟨φ, hφ, hφcomp, eTot, heTot⟩ :=
    exists_adicCompletion_ringEquiv_henselianLocalRing_of_neighborhood B (Spec (.of A)) hA
      hX hY hXdec hYdec p q E N j hj eStalk heStalk
  exact ⟨φ, hφ, ⟨E, N, j, hj, hsq, hφcomp⟩, eTot, heTot⟩

end Completion

end Space

end AlgebraicGeometry

end
