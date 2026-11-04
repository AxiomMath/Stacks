module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment.FibrePair

/-!
# The arrow containment of Stacks 03FM: the strong splitting

This file defines the point `u'` of `|U'|` (`AlgebraicGeometry.Space.fibreValuedPoint`), proves
the arrow containment `AlgebraicGeometry.Space.contains_arrows_fibreValuedPoint`, builds
`Z_univ` as a strong splitting of `R|_{U'}` at `u'`
(`AlgebraicGeometry.Space.restrictedStrongSplitting`), and concludes Stacks 03FM,
`AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`.
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

section Fibre

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  (hP : C.Contains (pullback G.source G.target).left)
  (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))
  (W : (G.source.left.fiber u).Opens)
  (hW : ∀ x : G.source.left.fiber u,
    x ∈ W ↔ G.target.left (G.source.left.fiberι u x) = u)
  (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u))

/-! ### The point `u'` of `|U'|` and the strong splitting -/

/-- The field-valued point of an algebraic space determined by a section of it over the
spectrum of the residue field at `u`. -/
def residueSectionValuedPoint (X : AlgebraicSpaces C S hS)
    (v : X.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))) :
    FieldValuedPoint C S hS X.obj where
  carrier := G.objects.left.residueField u
  contained := hK
  toBase := G.objects.left.fromSpecResidueField u ≫ G.objects.hom
  value := v

include hW in
/-- **The point `u'` of `|U'|`**: the field-valued point of the object space of the finite part
given by the pair `(u, Z_u)` over the spectrum of the residue field at `u`. -/
def fibreValuedPoint : FieldValuedPoint C S hS F.objects.obj where
  carrier := G.objects.left.residueField u
  contained := hK
  toBase := G.objects.left.fromSpecResidueField u ≫ G.objects.hom
  value := etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin

include hW in
/-- The object of the site underlying the point `u'` is the spectrum of the residue field
at `u`. -/
theorem fibreValuedPoint_siteObject :
    (fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin).siteObject =
      schemeSiteObject C hS (X := residueOver G u) hK := rfl

include hW in
/-- The point `u'` of `|U'|` is the point determined by the section `u'` of `U'`. -/
theorem fibreValuedPoint_eq :
    fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin =
      residueSectionValuedPoint G C hS u hK F.objects
        (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) := rfl

include hW in
/-- **The arrow containment of Stacks 03FM.**  Every point of the arrow space of the
restriction `R|_{U'}` whose source and target are both the point `u'` lies in the image of
`Z_univ`.

A representative of such a point is a field-valued point `z'` of `R'`; the two hypotheses give
field-valued extensions on which the source lift and the target lift of `z'` become
restrictions of `u'`, and amalgamating the two extensions makes both happen at once.  Over that
extension `AlgebraicGeometry.Space.exists_toRestriction_eq` produces the section of `Z_univ`
of the Stacks proof, and restricting a representative does not change the point it
defines. -/
theorem contains_arrows_fibreValuedPoint
    (r : Space.points C S hS
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj)
    (hr : Space.pointsMap C S hS
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid.arrows.obj
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid.source.hom r =
        (fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin).class C S hS F.objects.obj ∧
      Space.pointsMap C S hS
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid.arrows.obj
          (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid.target.hom r =
        (fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin).class C S hS F.objects.obj) :
    ∃ p : Space.points C S hS (Subfunctor.range F.toRestriction.hom).toFunctor,
      Space.pointsMap C S hS (Subfunctor.range F.toRestriction.hom).toFunctor
        (Subfunctor.range F.toRestriction.hom).ι p = r := by
  obtain ⟨ζ, hζ⟩ := Quot.exists_rep r
  subst hζ
  obtain ⟨hsrc, htgt⟩ := hr
  obtain ⟨ρ₁, ⟨f₁, hf₁⟩, ⟨g₁, hg₁⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff C S hS F.objects.obj _ _).1 hsrc
  obtain ⟨ρ₂, ⟨f₂, hf₂⟩, ⟨g₂, hg₂⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff C S hS F.objects.obj _ _).1 htgt
  obtain ⟨Ω, instΩ, hΩ, toB, σ, τ, hcomm⟩ :
      ∃ (Ω : Type u) (_ : Field Ω) (hΩ : C.Contains (Spec (.of Ω)))
        (toB : Spec (.of Ω) ⟶ S)
        (σ : (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS) : BigFppfOver C S hS) ⟶ ρ₁.siteObject)
        (τ : (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS) : BigFppfOver C S hS) ⟶ ρ₂.siteObject),
        σ ≫ f₁ = τ ≫ f₂ := by
    have hw₁ : f₁.left.hom ≫ ζ.toBase = ρ₁.toBase := congrArg (fun k => k.hom) (Over.w f₁)
    have hw₂ : f₂.left.hom ≫ ζ.toBase = ρ₂.toBase := congrArg (fun k => k.hom) (Over.w f₂)
    obtain ⟨Ω, instΩ, hΩ, ca, cb, key⟩ :=
      exists_fieldSpec_common C (K := ρ₁.carrier) (L := ρ₂.carrier) (M := ζ.carrier)
        ρ₁.contained ρ₂.contained f₁.left.hom f₂.left.hom
    have hbase : cb ≫ ρ₂.toBase = ca ≫ ρ₁.toBase :=
      (congrArg (fun z => cb ≫ z) hw₂.symm).trans
        ((Category.assoc cb f₂.left.hom ζ.toBase).symm.trans
          ((congrArg (fun z => z ≫ ζ.toBase) key.symm).trans
            ((Category.assoc ca f₁.left.hom ζ.toBase).trans
              (congrArg (fun z => ca ≫ z) hw₁))))
    exact ⟨Ω, instΩ, hΩ, ca ≫ ρ₁.toBase,
      Over.homMk (⟨ca⟩ : C.obj hΩ ⟶ C.obj ρ₁.contained) (by ext; rfl),
      Over.homMk (⟨cb⟩ : C.obj hΩ ⟶ C.obj ρ₂.contained) (by ext; exact hbase),
      by ext; exact key⟩
  have hcompmap : ∀ {X Y Z : BigFppfOver C S hS} (k : X ⟶ Y) (l : Y ⟶ Z)
      (x : F.objects.obj.obj (Opposite.op Z)),
      F.objects.obj.map (k ≫ l).op x =
        F.objects.obj.map k.op (F.objects.obj.map l.op x) := by
    intro X Y Z k l x
    rw [op_comp]
    exact F.objects.obj.map_comp_apply l.op k.op x
  have hsrclift : (GroupoidInAlgebraicSpaces.restrictionSource
        (G.realization C hS hU hR hP) F.objectProjection).hom.app
        (Opposite.op (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS)))
        ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
          F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value) =
      F.objects.obj.map (σ ≫ g₁).op (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) := by
    refine (NatTrans.naturality_apply
      (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
        F.objectProjection).hom (σ ≫ f₁).op ζ.value).trans ?_
    refine (hcompmap σ f₁ _).trans (Eq.trans ?_ (hcompmap σ g₁ _).symm)
    exact congrArg (F.objects.obj.map σ.op) (hf₁.trans hg₁.symm)
  have htgtlift : (GroupoidInAlgebraicSpaces.restrictionTarget
        (G.realization C hS hU hR hP) F.objectProjection).hom.app
        (Opposite.op (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS)))
        ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
          F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value) =
      F.objects.obj.map (τ ≫ g₂).op (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) := by
    refine (NatTrans.naturality_apply
      (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
        F.objectProjection).hom (σ ≫ f₁).op ζ.value).trans ?_
    refine Eq.trans (congrArg (fun z => F.objects.obj.map z.op
      ((GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
        F.objectProjection).hom.app (Opposite.op ζ.siteObject) ζ.value)) hcomm) ?_
    refine (hcompmap τ f₂ _).trans (Eq.trans ?_ (hcompmap τ g₂ _).symm)
    exact congrArg (F.objects.obj.map τ.op) (hf₂.trans hg₂.symm)
  have hs' : yonedaEquiv.symm
        ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
          F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value) ≫
        (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP)
          F.objectProjection).hom =
      yoneda.map (σ ≫ g₁) ≫
        yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) :=
    (yonedaEquiv_symm_naturality_right _ _ _).trans
      ((congrArg yonedaEquiv.symm hsrclift).trans (yonedaEquiv_symm_map _ _))
  have ht' : yonedaEquiv.symm
        ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
          F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value) ≫
        (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
          F.objectProjection).hom =
      yoneda.map (τ ≫ g₂) ≫
        yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) :=
    (yonedaEquiv_symm_naturality_right _ _ _).trans
      ((congrArg yonedaEquiv.symm htgtlift).trans (yonedaEquiv_symm_map _ _))
  have hrt : (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
        (G.realization C hS hU hR hP) F.objectProjection).hom ≫
        (G.realization C hS hU hR hP).target.hom =
      (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP)
        F.objectProjection).hom ≫ F.objectProjection.hom :=
    congrArg
      (fun z : GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP)
        F.objectProjection ⟶ (G.realization C hS hU hR hP).objects => z.hom)
      (GroupoidInAlgebraicSpaces.restriction_condition' (G.realization C hS hU hR hP)
        F.objectProjection)
  have hψt : (yonedaEquiv.symm
          ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value) ≫
        (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
          F.objectProjection).hom) ≫ (G.realization C hS hU hR hP).target.hom =
      (𝟙 (yoneda.obj (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS) : BigFppfOver C S hS)) ≫
        (yoneda.map (τ ≫ g₂) ≫
          yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))) ≫
        F.universalOpen.toBase.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => yonedaEquiv.symm
          ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value) ≫ z) hrt).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ F.objectProjection.hom) ht').trans
            ((congrArg (fun z => (yoneda.map (τ ≫ g₂) ≫
                yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin)) ≫ z)
              F.universalOpen_toBase_hom.symm).trans
              (congrArg (fun z => z ≫ F.universalOpen.toBase.hom)
                (Category.id_comp _).symm)))))
  obtain ⟨b, hb⟩ := F.exists_toRestriction_eq (ArrowToPoint G C hS hU hR u hP)
    (targetInvariant_arrowToPoint G C hS hU hR u hP)
    (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS))
    (yoneda.map (σ ≫ g₁) ≫
      yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))
    (yoneda.map (τ ≫ g₂) ≫
      yonedaEquiv.symm (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))
    (cutsOut_fibrePoint G C hS hU hR u hK hP F W hW hWfin _ (σ ≫ g₁))
    (cutsOut_fibrePoint G C hS hU hR u hK hP F W hW hWfin _ (τ ≫ g₂))
    (yonedaEquiv.symm
      ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value))
    hs' ht'
    (arrowToPoint_of_target G C hS hU hR u hK hP F W hW hWfin _ (τ ≫ g₂) _
      (𝟙 (yoneda.obj (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS) : BigFppfOver C S hS))) _ hψt)
  have hval : F.toRestriction.hom.app
      (Opposite.op (Over.mk (⟨toB⟩ : C.obj hΩ ⟶ C.obj hS) : BigFppfOver C S hS))
      (yonedaEquiv b) =
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value := by
    have hb' := congrArg yonedaEquiv hb
    rw [yonedaEquiv_comp] at hb'
    exact hb'.trans (Equiv.apply_symm_apply yonedaEquiv _)
  refine ⟨Quot.mk _
    { carrier := Ω
      contained := hΩ
      toBase := toB
      value := ⟨(GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid.arrows.obj.map (σ ≫ f₁).op ζ.value,
        ⟨yonedaEquiv b, hval⟩⟩ }, ?_⟩
  refine Quot.sound ⟨_, FieldValuedPoint.dominates_refl C S hS _ _, ⟨σ ≫ f₁, rfl⟩⟩

include hW in
/-- **`Z_univ` as a strong splitting of `R|_{U'}` at `u'`.**  Together with the open finite
subgroupoid of
`AlgebraicGeometry.Space.FinitePartUniversalOpen.restrictedSubgroupoid` — conditions (a) and
(b) of Stacks 04RK — and the arrow containment
`AlgebraicGeometry.Space.contains_arrows_fibreValuedPoint`, this is condition (1) of Stacks
04RK for the restriction of the realization of a groupoid scheme to the object space of its
finite part, at the point `u' = (u, Z_u)`.

This is the conclusion of **Stacks 03FM** for the realization. -/
def restrictedStrongSplitting :
    GroupoidInAlgebraicSpaces.StrongSplitting
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid
      ((fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin).class C S hS F.objects.obj) where
  toOpenFiniteSubgroupoid := F.restrictedSubgroupoid
  contains_arrows r hr :=
    contains_arrows_fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin r hr

include hW in
/-- **The restriction `R|_{U'}` is strongly split at `u'`** in the sense of Stacks 04RK (1). -/
theorem isStronglySplitAt_fibreValuedPoint :
    GroupoidInAlgebraicSpaces.IsStronglySplitAt
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        F.objectProjection).groupoid
      ((fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin).class C S hS F.objects.obj) :=
  ⟨restrictedStrongSplitting G C hS hU hR u hK hP F W hW hWfin⟩

/-- The canonical point of `|U|` at `u`: the field-valued point of the object space of the
realization given by the canonical morphism `u : Spec κ(u) ⟶ U`. -/
def residueValuedPoint :
    FieldValuedPoint C S hS (G.realization C hS hU hR hP).objects.obj where
  carrier := G.objects.left.residueField u
  contained := hK
  toBase := G.objects.left.fromSpecResidueField u ≫ G.objects.hom
  value := residueSiteMap G C hS hU u hK

include hW in
/-- **The point `u'` lies over `u`**: the étale projection `g : U' ⟶ U` carries the point `u'`
of `|U'|` to the point `u` of `|U|`. -/
theorem pointsMap_fibreValuedPoint :
    Space.pointsMap C S hS F.objects.obj F.objectProjection.hom
        ((fibreValuedPoint G C hS hU hR u hK hP F W hW hWfin).class C S hS F.objects.obj) =
      (residueValuedPoint G C hS hU hR u hK hP).class C S hS
        (G.realization C hS hU hR hP).objects.obj := by
  refine Quot.sound ⟨_, FieldValuedPoint.dominates_refl C S hS _ _,
    ⟨𝟙 (schemeSiteObject C hS (X := residueOver G u) hK), ?_⟩⟩
  exact (Category.id_comp (residueSiteMap G C hS hU u hK)).trans
    (objectProjection_fibrePoint G C hS hU hR u hK hP F W hW hWfin).symm

end Fibre

/-! ### Stacks 03FM -/

/-- **Stacks Project, Tag 03FM.**  In the strong splitting situation of Stacks 04RL there are
an algebraic space `U'`, an étale morphism `g : U' ⟶ U` of algebraic spaces and a point
`u' : Spec κ(u) ⟶ U'` lying over `u : Spec κ(u) ⟶ U` such that the restriction `R' = R|_{U'}`
of `R` to `U'` is strongly split over `u'`.

`U'` is the object space of the finite part `(R_s/U, e)_fin` of Stacks 04RU, `g` its étale
projection, `u'` the pair `(u, Z_u)` where `Z_u` is the open and closed piece of the fibre
`F_u = R ×_{s, U} Spec κ(u)` supported on the arrows from `u` to itself, and the strong
splitting is the universal open `Z_univ` read inside `R|_{U'}`.  Being strongly split is a
condition on a point of `|U'|`, so it is asserted at the point of `|U'|` which the morphism
`u' : Spec κ(u) ⟶ U'` determines. -/
@[stacks 03FM "all four assertions, in Situation 04RL: the algebraic space U', the \
étale g : U' ⟶ U and the point u' : Spec κ(u) ⟶ U' over u are PRODUCED, and R|_{U'} is \
strongly split over u'. Beyond Situation 04RL the only hypotheses are that the big fppf site \
contains the base, object, arrow and composable-pair schemes and Spec κ(u), which is this \
library's standing ambient requirement"]
theorem exists_stronglySplit_of_strongSplittingSituation
    (D : StrongSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK)),
        (yonedaSchemePointEquiv C hS hU (Opposite.op
            (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK))
            (g.hom.app _ v)).left =
          D.groupoid.objects.left.fromSpecResidueField D.u ∧
        GroupoidInAlgebraicSpaces.IsStronglySplitAt
          (GroupoidInAlgebraicSpaces.restrict (D.groupoid.realization C hS hU hR hP)
            g).groupoid
          ((residueSectionValuedPoint D.groupoid C hS D.u hK U' v).class C D.S hS U'.obj) := by
  obtain ⟨W, hW, _, hWfin⟩ := D.exists_fiberOpens_stabilizer
  exact ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale,
    etaleLocalFibrePoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin,
    lies_over_fibrePoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin,
    isStronglySplitAt_fibreValuedPoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin⟩

end AlgebraicGeometry.Space

end
