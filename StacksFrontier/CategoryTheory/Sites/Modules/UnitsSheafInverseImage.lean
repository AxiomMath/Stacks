module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.RingedTopos

/-!
# The units subsheaf of an inverse-image ringed topos

Let `f : Sh(C, J) ⟶ Sh(D, K)` be a morphism of topoi and `Y = (Sh(D, K), O_Y)` a ringed topos.
The source topos carries the inverse-image structure sheaf `f⁻¹O_Y`, and
`AlgebraicGeometry.inverseImageRingedToposHom` is the resulting canonical morphism of ringed
topoi. Stacks 04KR asserts that this morphism is a morphism of *locally* ringed topoi, which by
Stacks 04HA means that its square of units subsheaves is cartesian.

The units subsheaf of a ringed topos is defined sectionwise, as the sheaf of units of the
structure sheaf, and the sections of an inverse image are not describable; so the assertion
cannot be proved from that description. What this file supplies instead is the *categorical*
description: the units subsheaf, paired with the inverse, is the fibre product of the
multiplication of the structure sheaf over its unit section
(`AlgebraicGeometry.RingedTopos.unitsPair_isPullback`). An inverse image is left exact, so it
carries that cartesian square to a cartesian square, which the comparison of products and of
terminal objects identifies with the corresponding square of the inverse-image structure sheaf.
Two cartesian squares over one cospan have canonically isomorphic apexes, and that isomorphism
is the comparison of units subsheaves.

## Main definitions

* `AlgebraicGeometry.RingedTopos.unitsIncl`, `.unitsInv` and `.unitsPair`: the inclusion of the
  units subsheaf into the underlying sheaf of sets of the structure sheaf, the inversion of
  units, and the pairing of a unit with its inverse.
* `AlgebraicGeometry.inverseImageUnitsIso`: the comparison of the inverse image of the units
  subsheaf with the units subsheaf of the inverse-image ringed topos.

## Main results

* `AlgebraicGeometry.RingedTopos.unitsPair_isPullback`: the units subsheaf is the fibre product
  of multiplication over the unit section.
* `Stacks.Sheaves.LocalRingedness.pullbackRingSqIso_hom_comp_ringMulHom` and
  `.terminalFrom_comp_ringOneHom_pullback`: the multiplication and the unit section of an
  inverse-image sheaf of rings are the inverse images of the multiplication and the unit
  section.
* `AlgebraicGeometry.inverseImage_units_iso`: **Stacks 04KR**, the inverse image of the units
  subsheaf is the units subsheaf of the inverse image, by a unique isomorphism compatible with
  the inclusions.
* `AlgebraicGeometry.inverseImageRingedToposHom_isLocallyRinged`: **Stacks 04KR**, the canonical
  morphism is a morphism of locally ringed topoi.

## Implementation notes

The underlying sheaf of sets of the structure sheaf has two definitionally equal spellings —
`CategoryTheory.Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)`, in which the ring
operations are
stated, and `AlgebraicGeometry.RingedTopos.forgetRing.obj O`, in which the units subsheaf is
stated — and likewise the underlying sheaf of sets of an inverse-image structure sheaf is the
inverse image of the underlying sheaf of sets on the nose. Rewriting across such a spelling
makes the target ill-typed at the `implicit` transparency level that `rw` uses, after which no
further rewrite fires, so each statement here names its endpoints: `unitsIncl`,
`inverseImageForgetIso` and `inverseImageUnitsInclComparison` are morphisms carrying the
identification in their result type, and the remaining identifications are discharged by
`exact`, which works at the default transparency level.

`CategoryTheory.IsPullback.compIso` is the transport of a cartesian square along isomorphisms of
the two objects over the base corner; it is what identifies the inverse image of the units
square of `Y` with the units square of the inverse-image structure sheaf.

## References

* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.LocalRingedness

namespace AlgebraicGeometry.RingedTopos

universe w v u

variable (X : RingedTopos.{v, u, w}) [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying sheaf of rings of the structure sheaf. -/
noncomputable abbrev ringStructureSheaf : Sheaf X.J RingCat.{w} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O

/-- The inclusion of the units subsheaf, with its codomain spelled as the underlying sheaf of
sets of the underlying sheaf of rings of the structure sheaf. -/
noncomputable def unitsIncl : units X ⟶ Sheaf.ringSheaf (ringStructureSheaf X) := unitsι X

/-- Inversion on the units subsheaf. -/
noncomputable def unitsInv : units X ⟶ units X :=
  Sheaf.unaryOpHom (A := units X) (E := units X)
    (fun Z x ↦ (((x : (X.O.obj.obj Z)ˣ)⁻¹ : (X.O.obj.obj Z)ˣ))) (fun _ _ ↦ rfl)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A section of the units subsheaf and its inverse multiply to one. -/
theorem unitsIncl_mul_unitsInv (Z : X.Cᵒᵖ)
    (s : (Sheaf.sectionsFunctor X.J Z).obj (units X)) :
    (Sheaf.sectionsFunctor X.J Z).map (unitsIncl X) s *
        (Sheaf.sectionsFunctor X.J Z).map (unitsIncl X)
          ((Sheaf.sectionsFunctor X.J Z).map (unitsInv X) s) = 1 :=
  Units.mul_inv _

/-- Two sections of the units subsheaf agreeing in the structure sheaf are equal. -/
theorem units_section_ext {Z : X.Cᵒᵖ} {u v : (Sheaf.sectionsFunctor X.J Z).obj (units X)}
    (h : (Sheaf.sectionsFunctor X.J Z).map (unitsIncl X) u =
      (Sheaf.sectionsFunctor X.J Z).map (unitsIncl X) v) : u = v :=
  Units.ext h

/-- Restriction of a section of the units subsheaf is the restriction of its value. -/
theorem sectionsFunctor_map_unitsIncl_obj_map {Z W : X.Cᵒᵖ} (g : Z ⟶ W)
    (u : (Sheaf.sectionsFunctor X.J Z).obj (units X)) :
    (Sheaf.sectionsFunctor X.J W).map (unitsIncl X) ((units X).obj.map g u) =
      (Sheaf.ringSheaf (ringStructureSheaf X)).obj.map g
        ((Sheaf.sectionsFunctor X.J Z).map (unitsIncl X) u) := rfl

/-- A pair of sections multiplying to one is a section of the units subsheaf. -/
noncomputable def unitsMk (Z : X.Cᵒᵖ)
    (a b : (Sheaf.sectionsFunctor X.J Z).obj (Sheaf.ringSheaf (ringStructureSheaf X)))
    (h : a * b = 1) : (Sheaf.sectionsFunctor X.J Z).obj (units X) :=
  Units.mkOfMulEqOne a b h

/-- The section of the structure sheaf underlying such a unit is the first of the pair. -/
@[simp]
theorem sectionsFunctor_map_unitsIncl_unitsMk (Z : X.Cᵒᵖ)
    (a b : (Sheaf.sectionsFunctor X.J Z).obj (Sheaf.ringSheaf (ringStructureSheaf X)))
    (h : a * b = 1) :
    (Sheaf.sectionsFunctor X.J Z).map (unitsIncl X) (unitsMk X Z a b h) = a := rfl

/-- A section of the units subsheaf, paired with its inverse. -/
noncomputable def unitsPair :
    units X ⟶ Sheaf.ringSheaf (ringStructureSheaf X) ⨯ Sheaf.ringSheaf (ringStructureSheaf X) :=
  prod.lift (unitsIncl X) (unitsInv X ≫ unitsIncl X)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The first component of the pair is the inclusion. -/
theorem unitsPair_comp_fst : unitsPair X ≫ prod.fst = unitsIncl X := by
  rw [unitsPair, prod.lift_fst]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The square of the units subsheaf over multiplication and the unit section commutes. -/
theorem unitsPair_comp_ringMulHom :
    unitsPair X ≫ Sheaf.ringMulHom (ringStructureSheaf X) =
      terminal.from (units X) ≫ Sheaf.ringOneHom (ringStructureSheaf X) := by
  refine Sheaf.hom_ext_sections (fun Z s ↦ ?_)
  rw [Functor.map_comp, types_comp_apply, Functor.map_comp, types_comp_apply, unitsPair,
    Functor.map_lift_apply, Sheaf.sectionsFunctor_map_ringMulHom,
    Sheaf.sectionsFunctor_map_ringOneHom, Functor.map_comp, types_comp_apply]
  exact unitsIncl_mul_unitsInv X Z s


section Pullback

variable (s : PullbackCone (Sheaf.ringMulHom (ringStructureSheaf X))
  (Sheaf.ringOneHom (ringStructureSheaf X)))

/-- The first component of the pair of sections given by a cone. -/
noncomputable def coneFst : s.pt ⟶ Sheaf.ringSheaf (ringStructureSheaf X) := s.fst ≫ prod.fst

/-- The second component of the pair of sections given by a cone. -/
noncomputable def coneSnd : s.pt ⟶ Sheaf.ringSheaf (ringStructureSheaf X) := s.fst ≫ prod.snd

/-- The two components of a cone over multiplication and the unit section multiply to one. -/
theorem coneFst_mul_coneSnd (Z : X.Cᵒᵖ) (z : (Sheaf.sectionsFunctor X.J Z).obj s.pt) :
    (Sheaf.sectionsFunctor X.J Z).map (coneFst X s) z *
        (Sheaf.sectionsFunctor X.J Z).map (coneSnd X s) z = 1 := by
  have h := congrArg (fun m ↦ (Sheaf.sectionsFunctor X.J Z).map m z) s.condition
  simp only [Functor.map_comp, types_comp_apply] at h
  rw [coneFst, coneSnd, Functor.map_comp, types_comp_apply, Functor.map_comp, types_comp_apply,
    ← Sheaf.sectionsFunctor_map_ringMulHom, Functor.prodObjMk_map_fst_map_snd, h,
    Sheaf.sectionsFunctor_map_ringOneHom]

/-- The lift of a cone through the units subsheaf: a pair of sections multiplying to one is a
unit. -/
noncomputable def coneLift : s.pt ⟶ units X :=
  Sheaf.unaryOpHom (A := s.pt) (E := units X)
    (fun Z z ↦ unitsMk X Z _ _ (coneFst_mul_coneSnd X s Z z))
    (fun g z ↦ by
      refine units_section_ext X ?_
      rw [sectionsFunctor_map_unitsIncl_obj_map, sectionsFunctor_map_unitsIncl_unitsMk,
        sectionsFunctor_map_unitsIncl_unitsMk]
      exact (NatTrans.naturality_apply (coneFst X s).hom g z).symm)

/-- The lift followed by the inclusion is the first component of the cone. -/
theorem coneLift_comp_unitsIncl : coneLift X s ≫ unitsIncl X = coneFst X s :=
  Sheaf.hom_ext_sections (fun _ _ ↦ rfl)

/-- The lift followed by inversion and the inclusion is the second component of the cone. -/
theorem coneLift_comp_unitsInv_comp_unitsIncl :
    coneLift X s ≫ unitsInv X ≫ unitsIncl X = coneSnd X s :=
  Sheaf.hom_ext_sections (fun _ _ ↦ rfl)

/-- The lift factors the cone through the units subsheaf. -/
theorem coneLift_comp_unitsPair : coneLift X s ≫ unitsPair X = s.fst := by
  refine prod.hom_ext ?_ ?_
  · rw [unitsPair, Category.assoc, prod.lift_fst, coneLift_comp_unitsIncl, coneFst]
  · rw [unitsPair, Category.assoc, prod.lift_snd,
      coneLift_comp_unitsInv_comp_unitsIncl, coneSnd]

end Pullback

/-- **The units subsheaf is the fibre product of multiplication over the unit section.** A
section of the structure sheaf is a unit exactly when it admits a right inverse, and the pair
`(a, a⁻¹)` determines the unit; so the units subsheaf, paired with the inverse, is the fibre
product of the multiplication of the structure sheaf over its unit section. -/
theorem unitsPair_isPullback :
    IsPullback (unitsPair X) (terminal.from (units X))
      (Sheaf.ringMulHom (ringStructureSheaf X)) (Sheaf.ringOneHom (ringStructureSheaf X)) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (unitsPair_comp_ringMulHom X)
    (fun s ↦ coneLift X s) (fun s ↦ coneLift_comp_unitsPair X s)
    (fun s ↦ terminal.hom_ext _ _) (fun s m h₁ _ ↦ ?_))
  have : Mono (unitsIncl X) := unitsι_mono X
  refine (cancel_mono (unitsIncl X)).1 ?_
  rw [coneLift_comp_unitsIncl, coneFst, ← h₁, unitsPair, Category.assoc, prod.lift_fst]

end AlgebraicGeometry.RingedTopos

/-! ### Transport of a cartesian square along isomorphisms of the two upper corners -/

namespace CategoryTheory.IsPullback

universe v u

variable {C : Type u} [Category.{v} C]

/-- A cartesian square stays cartesian when the two objects over the base corner are replaced by
isomorphic ones. -/
theorem compIso {P A B Z A' B' : C} {fst : P ⟶ A} {snd : P ⟶ B} {g : A ⟶ Z} {i : B ⟶ Z}
    (h : IsPullback fst snd g i) (α : A ≅ A') (β : B ≅ B') {g' : A' ⟶ Z} {i' : B' ⟶ Z}
    (hg : α.hom ≫ g' = g) (hi : β.hom ≫ i' = i) :
    IsPullback (fst ≫ α.hom) (snd ≫ β.hom) g' i' := by
  have hcone : ∀ s : PullbackCone g' i', (s.fst ≫ α.inv) ≫ g = (s.snd ≫ β.inv) ≫ i := by
    intro s
    rw [← hg, ← hi, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact s.condition
  refine of_isLimit (Limits.PullbackCone.IsLimit.mk ?_
    (fun s ↦ h.lift (s.fst ≫ α.inv) (s.snd ≫ β.inv) (hcone s)) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_))
  · rw [Category.assoc, hg, Category.assoc, hi]; exact h.w
  · simp
  · simp
  · refine h.hom_ext ?_ ?_
    · simp [h.lift_fst, ← hm₁]
    · simp [h.lift_snd, ← hm₂]

end CategoryTheory.IsPullback

/-! ### The ring operations of an inverse-image sheaf of rings -/

namespace Stacks.Sheaves.LocalRingedness

universe w w' v u v' u'

section Pullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  (R : Sheaf K RingCat.{w'})

/-- **The inverse image of multiplication.** Under the product comparison of `Φ`, the
multiplication of an inverse-image sheaf of rings is the inverse image of the multiplication. -/
theorem pullbackRingSqIso_hom_comp_ringMulHom :
    (pullbackRingSqIso J Φ R).hom ≫ Sheaf.ringMulHom (pullbackRingSheaf J Φ R) =
      Φ.map (Sheaf.ringMulHom R) := by
  refine Sheaf.hom_ext_sections fun Z z ↦ ?_
  rw [Functor.map_comp_apply, sectionsFunctor_map_pullbackRingSqIso_hom]
  refine (ringMulObj_pullback J Φ R Z _ _).trans ?_
  exact congrArg ((Φ ⋙ Sheaf.sectionsFunctor J Z).map (Sheaf.ringMulHom R))
    (Functor.prodObjMk_map_fst_map_snd (P := Φ ⋙ Sheaf.sectionsFunctor J Z) z)

/-- **The inverse image of the unit section.** The unit section of an inverse-image sheaf of
rings is the inverse image of the unit section, read through the comparison of terminal
objects. -/
theorem terminalFrom_comp_ringOneHom_pullback :
    terminal.from (Φ.obj (⊤_ (Sheaf K (Type w')))) ≫
        Sheaf.ringOneHom (pullbackRingSheaf J Φ R) =
      Φ.map (Sheaf.ringOneHom R) := by
  refine Sheaf.hom_ext_sections fun Z t ↦ ?_
  rw [Functor.map_comp_apply, Functor.map_terminalFrom_apply]
  refine (ringOneObj_pullback J Φ R Z).trans ?_
  exact congrArg ((Φ ⋙ Sheaf.sectionsFunctor J Z).map (Sheaf.ringOneHom R))
    (Subsingleton.elim (α := (Φ ⋙ Sheaf.sectionsFunctor J Z).obj
      (⊤_ (Sheaf K (Type w')))) default t)

end Pullback

end Stacks.Sheaves.LocalRingedness

/-! ### The units subsheaf of an inverse-image ringed topos -/

namespace AlgebraicGeometry

universe ww vv uu ww' vv' uu'

section InverseImage

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  (Y : RingedTopos.{vv', uu', ww'})
  (f : MorphismOfTopoi (Sheaf J (Type ww)) Y.Topos)
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [Y.J.HasSheafCompose (forget RingCat.{ww'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]

/-- The underlying sheaf of sets of an inverse-image structure sheaf is the inverse image of the
underlying sheaf of sets of the structure sheaf, on the nose; the identification is carried by
the result type. -/
noncomputable def inverseImageForgetIso :
    f.inverseImage.obj (Y.forgetRing.obj Y.O) ≅
      (inverseImageRingedTopos C J Y f).forgetRing.obj (inverseImageRingedTopos C J Y f).O :=
  Iso.refl _

/-- The inverse image of the terminal sheaf of sets is terminal, the inverse image of a morphism
of topoi being left exact. -/
noncomputable def inverseImageTerminalIso :
    f.inverseImage.obj (⊤_ Y.Topos) ≅ ⊤_ (Sheaf J (Type ww)) :=
  have := f.preservesFiniteLimits
  (IsTerminal.isTerminalObj f.inverseImage _ terminalIsTerminal).uniqueUpToIso terminalIsTerminal

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [Y.J.HasSheafCompose (forget RingCat.{ww'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})] in
/-- The comparison of terminal objects is the canonical map to the terminal object. -/
theorem inverseImageTerminalIso_hom :
    (inverseImageTerminalIso J Y f).hom = terminal.from _ :=
  terminal.hom_ext _ _

/-- **The units square of an inverse-image ringed topos is cartesian.** The inverse image is
left exact, so it carries the cartesian square of the units subsheaf of `Y` to a cartesian
square, which the comparison of products and of terminal objects identifies with the square of
multiplication and the unit section of the inverse-image structure sheaf. -/
theorem inverseImage_unitsPair_isPullback :
    IsPullback
      (f.inverseImage.map (RingedTopos.unitsPair Y) ≫
        (pullbackRingSqIso J f.inverseImage
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).hom)
      (f.inverseImage.map (terminal.from (RingedTopos.units Y)) ≫
        (inverseImageTerminalIso J Y f).hom)
      (Sheaf.ringMulHom (RingedTopos.ringStructureSheaf (inverseImageRingedTopos C J Y f)))
      (Sheaf.ringOneHom (RingedTopos.ringStructureSheaf (inverseImageRingedTopos C J Y f))) := by
  have := f.preservesFiniteLimits
  refine ((RingedTopos.unitsPair_isPullback Y).map f.inverseImage).compIso _ _ ?_ ?_
  · exact pullbackRingSqIso_hom_comp_ringMulHom J f.inverseImage
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
  · rw [inverseImageTerminalIso_hom]
    exact terminalFrom_comp_ringOneHom_pullback J f.inverseImage
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)

/-- **The inverse image of the units subsheaf is the units subsheaf of the inverse image.** -/
noncomputable def inverseImageUnitsIso :
    f.inverseImage.obj (RingedTopos.units Y) ≅
      RingedTopos.units (inverseImageRingedTopos C J Y f) :=
  (inverseImage_unitsPair_isPullback J Y f).isoIsPullback _ _
    (RingedTopos.unitsPair_isPullback (inverseImageRingedTopos C J Y f))

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})] in
/-- The product comparison, followed by the first projection, is the inverse image of the first
projection. -/
theorem pullbackRingSqIso_hom_comp_fst :
    (pullbackRingSqIso J f.inverseImage
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).hom ≫ prod.fst =
      f.inverseImage.map prod.fst := by
  have := f.preservesFiniteLimits
  exact prodComparison_fst (F := f.inverseImage) _ _

/-- The inverse image of the inclusion of the units subsheaf, with its codomain spelled as the
underlying sheaf of sets of the structure sheaf of the inverse-image ringed topos. -/
noncomputable def inverseImageUnitsInclComparison :
    f.inverseImage.obj (RingedTopos.units Y) ⟶
      Sheaf.ringSheaf (RingedTopos.ringStructureSheaf (inverseImageRingedTopos C J Y f)) :=
  f.inverseImage.map (RingedTopos.unitsIncl Y)

/-- The comparison of units subsheaves is compatible with their inclusions into the structure
sheaves. -/
theorem inverseImageUnitsIso_hom_comp_unitsIncl :
    (inverseImageUnitsIso J Y f).hom ≫
        RingedTopos.unitsIncl (inverseImageRingedTopos C J Y f) =
      inverseImageUnitsInclComparison J Y f := by
  have h : (inverseImageUnitsIso J Y f).hom ≫
      RingedTopos.unitsPair (inverseImageRingedTopos C J Y f) =
      f.inverseImage.map (RingedTopos.unitsPair Y) ≫
        (pullbackRingSqIso J f.inverseImage
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).hom :=
    (inverseImage_unitsPair_isPullback J Y f).isoIsPullback_hom_fst _ _
      (RingedTopos.unitsPair_isPullback (inverseImageRingedTopos C J Y f))
  rw [← RingedTopos.unitsPair_comp_fst (inverseImageRingedTopos C J Y f), ← Category.assoc, h]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m ↦ f.inverseImage.map (RingedTopos.unitsPair Y) ≫ m)
    (pullbackRingSqIso_hom_comp_fst J Y f)).trans ?_
  refine (f.inverseImage.map_comp _ _).symm.trans ?_
  exact congrArg f.inverseImage.map (RingedTopos.unitsPair_comp_fst Y)

/-- **The comparison of units subsheaves is compatible with the inclusions into the structure
sheaves**, read through the identification of the underlying sheaves of sets. -/
theorem inverseImageUnitsIso_hom_comp_unitsι :
    (inverseImageUnitsIso J Y f).hom ≫
        RingedTopos.unitsι (inverseImageRingedTopos C J Y f) =
      f.inverseImage.map (RingedTopos.unitsι Y) ≫ (inverseImageForgetIso J Y f).hom :=
  (inverseImageUnitsIso_hom_comp_unitsIncl J Y f).trans (Category.comp_id _).symm


/-- **Stacks 04KR: the inverse image of the units subsheaf.** There is exactly one isomorphism
of the inverse image of the units subsheaf of `Y` with the units subsheaf of the inverse-image
ringed topos compatible with the inclusions into the structure sheaves; it is therefore the
canonical one. -/
@[stacks 04KR "inverse image of the units subsheaf"]
theorem inverseImage_units_iso :
    ∃! e : f.inverseImage.obj (RingedTopos.units Y) ≅
        RingedTopos.units (inverseImageRingedTopos C J Y f),
      e.hom ≫ RingedTopos.unitsι (inverseImageRingedTopos C J Y f) =
        f.inverseImage.map (RingedTopos.unitsι Y) ≫ (inverseImageForgetIso J Y f).hom := by
  refine ⟨inverseImageUnitsIso J Y f, inverseImageUnitsIso_hom_comp_unitsι J Y f, fun e' he' ↦ ?_⟩
  have : Mono (RingedTopos.unitsι (inverseImageRingedTopos C J Y f)) :=
    RingedTopos.unitsι_mono _
  exact Iso.ext ((cancel_mono (RingedTopos.unitsι (inverseImageRingedTopos C J Y f))).1
    (he'.trans (inverseImageUnitsIso_hom_comp_unitsι J Y f).symm))

/-- The structure map of the canonical morphism is, on underlying sheaves of sets, the
identification of the inverse image of the structure sheaf with the inverse-image structure
sheaf. -/
theorem inverseImageRingedToposHom_fSharpSet :
    RingedToposHom.fSharpSet (inverseImageRingedToposHom C J Y f) =
      (inverseImageForgetIso J Y f).hom := by
  refine (RingedToposHom.fSharpInverseImage_forget_homEquiv
    (inverseImageRingedToposHom C J Y f)).symm.trans ?_
  rw [inverseImageRingedToposHom_fSharpInverseImage]
  exact CategoryTheory.Functor.map_id _ _

/-- **Stacks 04KR: the canonical morphism is a morphism of locally ringed topoi.** Its structure
map on underlying sheaves of sets is an isomorphism, so its square of units subsheaves is
cartesian as soon as the comparison of units subsheaves exists. -/
@[stacks 04KR "canonical morphism of locally ringed topoi"]
theorem inverseImageRingedToposHom_isLocallyRinged :
    RingedToposHom.IsLocallyRinged (inverseImageRingedToposHom C J Y f) := by
  have hsharp := inverseImageRingedToposHom_fSharpSet J Y f
  refine ⟨(inverseImageUnitsIso J Y f).hom, ?_⟩
  have hcomm : CommSq ((inverseImageUnitsIso J Y f).hom)
      (f.inverseImage.map (RingedTopos.unitsι Y))
      (RingedTopos.unitsι (inverseImageRingedTopos C J Y f))
      (RingedToposHom.fSharpSet (inverseImageRingedToposHom C J Y f)) := by
    refine ⟨?_⟩
    rw [hsharp]
    exact inverseImageUnitsIso_hom_comp_unitsι J Y f
  have h₁ : IsIso ((inverseImageUnitsIso J Y f).hom) :=
    Iso.isIso_hom (inverseImageUnitsIso J Y f)
  have h₂ : IsIso (RingedToposHom.fSharpSet (inverseImageRingedToposHom C J Y f)) := by
    rw [hsharp]
    exact Iso.isIso_hom (inverseImageForgetIso J Y f)
  exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ h₁ h₂ hcomm

end InverseImage

end AlgebraicGeometry

add_to_stacks 04KR "canonical ringed-topos morphism"
  AlgebraicGeometry.inverseImageRingedToposHom

end
