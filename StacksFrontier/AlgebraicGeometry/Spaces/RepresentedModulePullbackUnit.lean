module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleHomEquivTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureModulePullbackChart
public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekObjectNaturality

/-!
# The canonical map `f^*𝒪 ⟶ 𝒪` across the transport of the inverse image along a represented
morphism

Let `g : T' ⟶ T` be a morphism of the big fppf category over a scheme `S` and let `φ` be the
morphism of representable algebraic spaces it represents.
`AlgebraicGeometry.Space.representedModulePullbackIso` identifies the inverse image of modules
`φ^*` of [Stacks Project, Tag 03LU] with pullback along the morphism of small étale ringed sites
of [Stacks Project, Tag 070R] (2) of the underlying morphism of schemes, across the
identification of the small étale site of a representable algebraic space with the small étale
site of the representing scheme.  **This file proves that that identification carries the
canonical map `f^*𝒪 ⟶ 𝒪` of one to the canonical map of the other.**

Both maps are morphisms out of an inverse image of the unit module, so each is determined by its
transpose and the comparison — which is a `CategoryTheory.Adjunction.leftAdjointUniq` and
describes none of its own values — enters only through
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp`.  What has to be proved is that the
two transposes agree, and that is the square of
`AlgebraicGeometry.Space.representedStructureMapRing_square` read at the unit module: both
routes carry the unit section to pullback of regular functions along the cartesian projection.

## Main results

* `Stacks.CategoryTheory.comp_homEquiv_map` and
  `Stacks.CategoryTheory.ofNatIsoRight_comp_homEquiv_apply`: the hom-set bijection of a
  composite adjunction, applied to a morphism — the first at the image under the second left
  adjoint of a morphism, which is where the second unit appears.  Both rest on
  `Stacks.CategoryTheory.comp_homEquiv_apply` of
  `StacksFrontier/CategoryTheory/Sites/Glueing/LowerShriekObjectNaturality.lean`, which states that
  bijection in unit form.
* `SheafOfModules.unitToPushforwardObjUnit_square_comp`: **the two structure comparisons of a
  square of ringed sites agree at the unit module**, one of the four direct images being read
  through a comparison with another functor.  This is the intermediate statement inside
  `SheafOfModules.pullbackSquareIso_hom_app_unit` of
  `StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModulePullbackUnit.lean`, in the generality a
  square one of whose four pullbacks is *not* a `SheafOfModules.pullback` needs.
* `AlgebraicGeometry.Space.unitToPushforwardObjUnit_comp_representedModulePushforwardSquareIso`:
  the comparison of the two composite **direct** images of a represented morphism carries the
  structure comparison of one route to the structure comparison of the other.
* `AlgebraicGeometry.Space.homEquiv_structureModulePullbackMap_comp_eq`: the two transposes
  agree, which is what
  `CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` consumes.
* `AlgebraicGeometry.Space.structureModulePullbackMap_representedModulePullbackIso`: **the
  identification of the two inverse images carries
  `AlgebraicGeometry.Space.structureModulePullbackMap` to
  `SheafOfModules.pullbackObjUnitToUnit` of
  `AlgebraicGeometry.Space.representedSchemeStructureMapRing`.**

## Implementation notes

**Why there are twenty declarations where two would be natural.**  The goal of the geometric
half is not type-correct at `implicit` transparency:
`AlgebraicGeometry.Space.modulePushforward` of a represented morphism is typed at
`AlgebraicGeometry.Space.Modules B S hS X.obj _` while the composite it sits in wants
`SheafOfModules (AlgebraicGeometry.Space.representedStructureRingSheaf …)`, and the two agree
only by `AlgebraicGeometry.Space.modules_eq_sheafOfModules_representedStructureRingSheaf`.  So
`rw [Iso.trans_hom]` reports a missing pattern on a goal that visibly contains
`(α ≪≫ β).hom`, and `simp only` makes no progress; every step is a `congrArg` in term position,
where elaboration runs at default transparency.  Each such step costs a sizeable fraction of the
heartbeat budget, which is why there is one step per declaration.

For the same reason the generic statements are stated **generically** and instantiated once:
substituting the concrete comparison of index functors into the chain of equalities costs more
than the budget, while with the structure maps and the comparison left as variables every step
is cheap — the measurement recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareComparison.lean`.  The
instantiation is kept to one unification by stating each geometric step in the spelling the
previous one produces.

The two `SheafOfModules.pushforwardComp` factors of the comparison of the two composite direct
images are identity morphisms — the direct image along a composite *is* the direct image along
the composite comparison, by `Stacks.SheafOfModules.pushforward_pushforward_obj` — but the two
spellings of their common value are not syntactically equal, so neither
`CategoryTheory.Category.id_comp` nor a `simp` set reaches them.  They are absorbed by
statements whose proofs are `CategoryTheory.Category.id_comp` and
`CategoryTheory.Category.comp_id` applied to an explicit morphism.

## What is not proved

The compatibility proved here is at the **functor** level, for
`AlgebraicGeometry.Space.representedModulePullbackIso`.  What part (2) of
[Stacks Project, Tag 04G2] consumes at the ideal-sheaf level is the same statement for
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, and two steps sit between the
two.

The first, the obj-form bookkeeping of
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` — this comparison corrected by the
unit and the counit of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, the unit
at the unit module being `CategoryTheory.Iso.refl` by `rfl` and the counit not — **is now
proved**, as
`AlgebraicGeometry.Space.structureModulePullbackMap_representedModuleObjPullbackIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleObjPullbackUnit.lean`; the counit
correction cancels by its naturality together with the fact that the counit *at the unit module*
is the identity.

The second, the composition with the second factor
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`, whose own unit-module
compatibility is
`AlgebraicGeometry.SmallEtale.pullbackObjUnitToUnit_associatedModuleBaseChangeIso`, is still
owed, and so is the naturality in the module of
`AlgebraicGeometry.Space.representedModuleObjPullbackIso`.  The "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean` records what the
ideal-sheaf level then still needs.

## References

* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}

/-- The transpose along a composite adjunction of the image under the second left adjoint of a
morphism is the transpose along the first adjunction, followed by the second unit. -/
theorem comp_homEquiv_map (a : L ⊣ R) (b : L' ⊣ R') (x : C) (y : D) (θ : L.obj x ⟶ y) :
    (a.comp b).homEquiv x (L'.obj y) (L'.map θ) =
      a.homEquiv x y θ ≫ R.map (b.unit.app y) := by
  have h : b.homEquiv (L.obj x) (L'.obj y) (L'.map θ) = θ ≫ b.unit.app y :=
    (Adjunction.homEquiv_unit b (L.obj x) (L'.obj y) (L'.map θ)).trans
      (b.unit.naturality θ).symm
  rw [comp_homEquiv_apply a b x (L'.obj y) (L'.map θ), h]
  exact (Adjunction.homEquiv_unit a x (R'.obj (L'.obj y)) (θ ≫ b.unit.app y)).symm.trans
    (a.homEquiv_naturality_right θ (b.unit.app y))

/-- The hom-set bijection of a composite adjunction whose right adjoint has been transported
along an isomorphism, applied to a morphism. -/
theorem ofNatIsoRight_comp_homEquiv_apply (a : L ⊣ R) (b : L' ⊣ R') {G : E ⥤ C}
    (ε : R' ⋙ R ≅ G) (x : C) (z : E) (u : L'.obj (L.obj x) ⟶ z) :
    ((a.comp b).ofNatIsoRight ε).homEquiv x z u =
      a.homEquiv x (R'.obj z) (b.homEquiv (L.obj x) z u) ≫ ε.hom.app z := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, comp_homEquiv_apply,
    Adjunction.homEquiv_unit a x (R'.obj z) (b.homEquiv (L.obj x) z u)]

/-- Naturality with a morphism in front, reassociated: the component of a natural
transformation at the source, followed by the image of a morphism, is the image of that morphism
followed by the component at the target. -/
theorem comp_app_comp_map {F G : C ⥤ D} (α : F ⟶ G) {x y : C} (f : x ⟶ y) {w : D}
    (h : w ⟶ F.obj x) :
    h ≫ (α.app x ≫ G.map f) = (h ≫ F.map f) ≫ α.app y :=
  (congrArg (fun z ↦ h ≫ z) (α.naturality f).symm).trans
    (Category.assoc h (F.map f) (α.app y)).symm

end Stacks.CategoryTheory

namespace SheafOfModules

section UnitSquare

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {a : C ⥤ C'} {b : C' ⥤ D'} {c : C ⥤ D} {d : D ⥤ D'}
  [a.IsContinuous J J'] [b.IsContinuous J' K'] [c.IsContinuous J K] [d.IsContinuous K K']
  [(a ⋙ b).IsContinuous J K'] [(c ⋙ d).IsContinuous J K']
  {RC : Sheaf J RingCat.{u}} {RC' : Sheaf J' RingCat.{u}}
  {RD : Sheaf K RingCat.{u}} {RD' : Sheaf K' RingCat.{u}}
  (φa : RC ⟶ (a.sheafPushforwardContinuous RingCat.{u} J J').obj RC')
  (φb : RC' ⟶ (b.sheafPushforwardContinuous RingCat.{u} J' K').obj RD')
  (φc : RC ⟶ (c.sheafPushforwardContinuous RingCat.{u} J K).obj RD)
  (φd : RD ⟶ (d.sheafPushforwardContinuous RingCat.{u} K K').obj RD')

/-- The comparison of the direct image along a composite with the composite of the direct images
is an identity morphism, so it is absorbed by whatever follows it.  The two spellings of its
common value are not syntactically equal, which is why the statement is needed. -/
theorem pushforwardComp_inv_app_comp
    {E₂ : Type u₃} [Category.{v₃} E₂] {L : GrothendieckTopology E₂} {F₂ : C ⥤ C'}
    {G₂ : C' ⥤ E₂} [F₂.IsContinuous J J'] [G₂.IsContinuous J' L]
    [(F₂ ⋙ G₂).IsContinuous J L] {R : Sheaf J RingCat.{u}} {R' : Sheaf J' RingCat.{u}}
    {R'' : Sheaf L RingCat.{u}}
    (φ : R ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J J').obj R')
    (ψ : R' ⟶ (G₂.sheafPushforwardContinuous RingCat.{u} J' L).obj R'')
    (M : SheafOfModules.{u} R'') {X : SheafOfModules.{u} R}
    (f : X ⟶ (pushforward.{u} (comparisonComp φ ψ)).obj M) {Z : SheafOfModules.{u} R}
    (h : (pushforward.{u} ψ ⋙ pushforward.{u} φ).obj M ⟶ Z) :
    f ≫ ((pushforwardComp.{u} φ ψ).inv.app M ≫ h) = f ≫ h :=
  congrArg (fun z ↦ f ≫ z) (Category.id_comp h)

/-- The comparison of the direct image along a composite with the composite of the direct images
is an identity morphism, so it is absorbed by whatever follows it. -/
private theorem pushforwardComp_hom_app_comp
    {E₂ : Type u₃} [Category.{v₃} E₂] {L : GrothendieckTopology E₂} {F₂ : C ⥤ C'}
    {G₂ : C' ⥤ E₂} [F₂.IsContinuous J J'] [G₂.IsContinuous J' L]
    [(F₂ ⋙ G₂).IsContinuous J L] {R : Sheaf J RingCat.{u}} {R' : Sheaf J' RingCat.{u}}
    {R'' : Sheaf L RingCat.{u}}
    (φ : R ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J J').obj R')
    (ψ : R' ⟶ (G₂.sheafPushforwardContinuous RingCat.{u} J' L).obj R'')
    (M : SheafOfModules.{u} R'') {Z : SheafOfModules.{u} R}
    (h : (pushforward.{u} (comparisonComp φ ψ)).obj M ⟶ Z) :
    (pushforwardComp.{u} φ ψ).hom.app M ≫ h = h :=
  Category.id_comp h

/-- **The two structure comparisons of a square of ringed sites agree at the unit module, read
through a comparison `χ` of one of the four direct images with another functor.**

Both sides are read in that other functor: on the left a morphism `t` which `χ` carries to the
structure comparison of `a`, followed by `P` of the structure comparison of `b`; on the right
the structure comparisons of `c` and of `d`, followed by the comparison of the two composite
direct images that the square provides.  Only `χ` and the square's own data enter. -/
theorem unitToPushforwardObjUnit_square_comp (e : a ⋙ b ≅ c ⋙ d)
    (he : comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      comparisonComp φa φb)
    {P : SheafOfModules.{u} RC' ⥤ SheafOfModules.{u} RC} (χ : P ≅ pushforward.{u} φa)
    (t : unit RC ⟶ P.obj (unit RC'))
    (ht : t = unitToPushforwardObjUnit φa ≫ χ.inv.app (unit RC')) :
    t ≫ P.map (unitToPushforwardObjUnit φb) =
      (unitToPushforwardObjUnit φc ≫
          (pushforward.{u} φc).map (unitToPushforwardObjUnit φd)) ≫
        (pushforwardComp.{u} φc φd ≪≫ pushforwardCongr₂.{u} _ e he ≪≫
            (pushforwardComp.{u} φa φb).symm ≪≫
            Functor.isoWhiskerLeft (pushforward.{u} φb) χ.symm).hom.app (unit RD') := by
  have hleft : t ≫ P.map (unitToPushforwardObjUnit φb) =
      unitToPushforwardObjUnit (comparisonComp φa φb) ≫
        χ.inv.app ((pushforward.{u} φb).obj (unit RD')) := by
    rw [ht, Category.assoc, ← χ.inv.naturality (unitToPushforwardObjUnit φb),
      ← Category.assoc, ← unitToPushforwardObjUnit_comparisonComp_eq_comp_map φa φb]
    rfl
  have hright : (unitToPushforwardObjUnit φc ≫
          (pushforward.{u} φc).map (unitToPushforwardObjUnit φd)) ≫
        (pushforwardComp.{u} φc φd ≪≫ pushforwardCongr₂.{u} _ e he ≪≫
            (pushforwardComp.{u} φa φb).symm ≪≫
            Functor.isoWhiskerLeft (pushforward.{u} φb) χ.symm).hom.app (unit RD') =
      unitToPushforwardObjUnit (comparisonComp φa φb) ≫
        χ.inv.app ((pushforward.{u} φb).obj (unit RD')) := by
    have h3 : ∀ {Z : SheafOfModules.{u} RC}
        (X : Z ⟶ (pushforward.{u} (comparisonComp φa φb)).obj (unit RD')),
        X ≫ (pushforwardComp.{u} φa φb).inv.app (unit RD') = X := fun X ↦ Category.comp_id X
    have hsplit : (pushforwardComp.{u} φc φd ≪≫ pushforwardCongr₂.{u} _ e he ≪≫
          (pushforwardComp.{u} φa φb).symm ≪≫
          Functor.isoWhiskerLeft (pushforward.{u} φb) χ.symm).hom.app (unit RD') =
        (pushforwardComp.{u} φc φd).hom.app (unit RD') ≫
          ((pushforwardNatTrans (comparisonComp φc φd) e.hom).app (unit RD') ≫
              (pushforwardCongr he).hom.app (unit RD')) ≫
            (pushforwardComp.{u} φa φb).inv.app (unit RD') ≫
              χ.inv.app ((pushforward.{u} φb).obj (unit RD')) := rfl
    refine Eq.trans (congrArg (fun z ↦ (unitToPushforwardObjUnit φc ≫
        (pushforward.{u} φc).map (unitToPushforwardObjUnit φd)) ≫ z) hsplit) ?_
    refine Eq.trans (congrArg (fun z ↦ (unitToPushforwardObjUnit φc ≫
        (pushforward.{u} φc).map (unitToPushforwardObjUnit φd)) ≫ z)
      (pushforwardComp_hom_app_comp φc φd (unit RD') _)) ?_
    refine Eq.trans (congrArg (fun z ↦ z ≫
        ((pushforwardNatTrans (comparisonComp φc φd) e.hom).app (unit RD') ≫
            (pushforwardCongr he).hom.app (unit RD')) ≫
          (pushforwardComp.{u} φa φb).inv.app (unit RD') ≫
            χ.inv.app ((pushforward.{u} φb).obj (unit RD')))
      (unitToPushforwardObjUnit_comparisonComp_eq_comp_map φc φd).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z ↦ z ≫ ((pushforwardComp.{u} φa φb).inv.app (unit RD') ≫
        χ.inv.app ((pushforward.{u} φb).obj (unit RD'))))
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ (pushforwardCongr he).hom.app (unit RD'))
          (unitToPushforwardObjUnit_comp_natTrans e.hom
            (comparisonComp φc φd)).symm))) ?_
    refine Eq.trans (congrArg (fun z ↦ z ≫ ((pushforwardComp.{u} φa φb).inv.app (unit RD') ≫
        χ.inv.app ((pushforward.{u} φb).obj (unit RD'))))
      (unitToPushforwardObjUnit_comp_pushforwardCongr he)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun z ↦ z ≫ χ.inv.app ((pushforward.{u} φb).obj (unit RD')))
      (h3 (unitToPushforwardObjUnit (comparisonComp φa φb)))
  exact hleft.trans hright.symm

end UnitSquare

end SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- The transpose of `AlgebraicGeometry.Space.structureModulePullbackMap` of a represented
morphism is the structure comparison of base change of étale scheme charts, read back through
`AlgebraicGeometry.Space.modulePushforwardChartIso`.

This is `AlgebraicGeometry.Space.modulePushforwardChartIso_structureModuleFMap` with the
comparison moved to the other side, and
`AlgebraicGeometry.Space.structureModulePullbackMap_transpose` for the transpose. -/
theorem homEquiv_structureModulePullbackMap_eq :
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
        (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)) =
      SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)) :=
  (structureModulePullbackMap_transpose B S hS (representedSpaceMap B S hS g)).trans
    ((Iso.comp_inv_eq ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).app
      (SheafOfModules.unit (structureRingSheaf B S hS
        ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)))).2
      (modulePushforwardChartIso_structureModuleFMap B S hS
        (representedSpaceMap B S hS g) hg).symm).symm

/-- The component at the unit module of the comparison
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` of the two composite direct images
is the composite of the comparison of iterated direct images, the transport along
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` and
`AlgebraicGeometry.Space.representedStructureMapRing_square`, the inverse comparison of iterated
direct images, and the inverse of `AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
theorem representedModulePushforwardSquareIso_hom_app_unit :
    (representedModulePushforwardSquareIso B S hS g hg).hom.app
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      (SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
            (representedSchemeStructureMapRing B S hS g)).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
        (((SheafOfModules.pushforwardNatTrans _
                  (representedSmallEtaleBaseChangeIso B S hS g hg).hom).app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
            (SheafOfModules.pushforwardCongr
                (representedStructureMapRing_square B S hS g hg)).hom.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) ≫
          ((SheafOfModules.pushforwardComp.{u}
                (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
                (representedEquivSharp B S hS T')).inv.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
            (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
              ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
                (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))))) :=
  rfl

/-- The middle two factors of the comparison of the two composite direct images, read at the unit
module: the structure comparison of the route through the base change of schemes, followed by the
transport along the identification of the two base changes, is the structure comparison of the
route through base change of étale scheme charts.

This is `SheafOfModules.unitToPushforwardObjUnit_comp_natTrans` followed by
`SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr` at
`AlgebraicGeometry.Space.representedStructureMapRing_square`. -/
theorem unitToPushforwardObjUnit_representedSquareMiddle :
    SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        ((SheafOfModules.pushforwardNatTrans _
              (representedSmallEtaleBaseChangeIso B S hS g hg).hom).app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
          (SheafOfModules.pushforwardCongr
              (representedStructureMapRing_square B S hS g hg)).hom.app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
        (representedEquivSharp B S hS T')) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ (SheafOfModules.pushforwardCongr
        (representedStructureMapRing_square B S hS g hg)).hom.app
      (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))
    (SheafOfModules.unitToPushforwardObjUnit_comp_natTrans
      (representedSmallEtaleBaseChangeIso B S hS g hg).hom
      (SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
        (representedSchemeStructureMapRing B S hS g))).symm) ?_
  exact SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr
    (representedStructureMapRing_square B S hS g hg)

/-- The outer two factors of the comparison of the two composite direct images are identity
morphisms, the direct image along a composite being the direct image along the composite
comparison; so at the unit module the comparison is its middle two factors followed by the
identification of the two direct images of modules. -/
theorem unitToPushforwardObjUnit_comp_representedModulePushforwardSquareIso_middle :
    SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        (representedModulePushforwardSquareIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        (((SheafOfModules.pushforwardNatTrans _
                  (representedSmallEtaleBaseChangeIso B S hS g hg).hom).app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
            (SheafOfModules.pushforwardCongr
                (representedStructureMapRing_square B S hS g hg)).hom.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) ≫
          ((SheafOfModules.pushforwardComp.{u}
                (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
                (representedEquivSharp B S hS T')).inv.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
            (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
              ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
                (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))))) := by
  refine Eq.trans (congrArg (fun z ↦ SheafOfModules.unitToPushforwardObjUnit
      (SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
        (representedSchemeStructureMapRing B S hS g)) ≫ z)
    (representedModulePushforwardSquareIso_hom_app_unit B S hS g hg)) ?_
  exact congrArg (fun z ↦ SheafOfModules.unitToPushforwardObjUnit
      (SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
        (representedSchemeStructureMapRing B S hS g)) ≫ z)
    (SheafOfModules.pushforwardComp_hom_app_comp (representedEquivSharp B S hS T)
      (representedSchemeStructureMapRing B S hS g)
      (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) _)

/-- The first half of the reassociation: the middle two factors absorb the structure comparison
of the route through the base change of schemes, by
`AlgebraicGeometry.Space.unitToPushforwardObjUnit_representedSquareMiddle`. -/
theorem unitToPushforwardObjUnit_representedSquare_reassoc :
    SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        (((SheafOfModules.pushforwardNatTrans _
                  (representedSmallEtaleBaseChangeIso B S hS g hg).hom).app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
            (SheafOfModules.pushforwardCongr
                (representedStructureMapRing_square B S hS g hg)).hom.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) ≫
          ((SheafOfModules.pushforwardComp.{u}
                (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
                (representedEquivSharp B S hS T')).inv.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
            (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
              ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
                (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))))) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
          (representedEquivSharp B S hS T')) ≫
        ((SheafOfModules.pushforwardComp.{u}
              (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
              (representedEquivSharp B S hS T')).inv.app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
          (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
            ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z ↦ z ≫
      ((SheafOfModules.pushforwardComp.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
            (representedEquivSharp B S hS T')).inv.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))))
    (unitToPushforwardObjUnit_representedSquareMiddle B S hS g hg)

/-- **The comparison of the two composite direct images of a represented morphism carries the
structure comparison of one route to the structure comparison of the other**, at the unit module.
On the left the structure comparison of the route through the morphism of small étale ringed
sites of the underlying morphism of schemes; on the right the one of the route through base
change of étale scheme charts, read in the direct image of [Stacks Project, Tag 03LU] through
`AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
theorem unitToPushforwardObjUnit_comp_representedModulePushforwardSquareIso :
    SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        (representedModulePushforwardSquareIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
          (representedEquivSharp B S hS T')) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) :=
  ((unitToPushforwardObjUnit_comp_representedModulePushforwardSquareIso_middle B S hS g
          hg).trans
        (unitToPushforwardObjUnit_representedSquare_reassoc B S hS g hg)).trans
    (SheafOfModules.pushforwardComp_inv_app_comp
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
      (representedEquivSharp B S hS T')
      (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))
      (SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
        (representedEquivSharp B S hS T')))
      ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
        ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))))

/-- The transpose of the canonical map `f^*𝒪 ⟶ 𝒪`, followed by the direct image of the structure
comparison of the identification of the two small étale sites of `T'`, read through
`AlgebraicGeometry.Space.modulePushforwardChartIso`: the first half, which is
`AlgebraicGeometry.Space.homEquiv_structureModulePullbackMap_eq` reassociated. -/
theorem homEquiv_structureModulePullbackMap_comp_unitToPushforwardObjUnit :
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)) ≫
        (modulePushforward B S hS (representedSpaceMap B S hS g)).map
          (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≫
        ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
            (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)) ≫
          (modulePushforward B S hS (representedSpaceMap B S hS g)).map
            (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T'))) :=
  (congrArg (fun z ↦ z ≫ (modulePushforward B S hS (representedSpaceMap B S hS g)).map
        (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T')))
      (homEquiv_structureModulePullbackMap_eq B S hS g hg)).trans
    (Category.assoc _ _ _)

/-- The identification of the two direct images of modules is natural, so the structure
comparison of the identification of the two small étale sites of `T'` passes across it. -/
theorem unitToPushforwardObjUnit_smallBaseChangeSharp_naturality :
    SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≫
        ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
            (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)) ≫
          (modulePushforward B S hS (representedSpaceMap B S hS g)).map
            (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T'))) =
      (SheafOfModules.unitToPushforwardObjUnit
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≫
          (SheafOfModules.pushforward.{u}
              (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).map
            (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T'))) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
          ((SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T')).obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) :=
  Stacks.CategoryTheory.comp_app_comp_map
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv
    (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T'))
    (SheafOfModules.unitToPushforwardObjUnit
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg))

/-- The two structure comparisons of the route through base change of étale scheme charts
compose to the structure comparison of the composite. -/
theorem unitToPushforwardObjUnit_smallBaseChangeSharp_fold :
    (SheafOfModules.unitToPushforwardObjUnit
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≫
          (SheafOfModules.pushforward.{u}
              (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).map
            (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T'))) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
          ((SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T')).obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
          (representedEquivSharp B S hS T')) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
          ((SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T')).obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) :=
  congrArg (fun z ↦ z ≫
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
        ((SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T')).obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))))
    (SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp_map
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
      (representedEquivSharp B S hS T')).symm

/-- The two spellings of the module the identification of the two direct images is read at: the
direct image along the structure comparison of the identification of the two small étale sites,
and the functor of that identification.  They are the same functor. -/
theorem modulePushforwardChartIso_inv_app_pushforward_eq :
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
        ((SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T')).obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
        ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) :=
  rfl

/-- The transpose along the identification of the two small étale sites of `T` of the structure
comparison of the morphism of small étale ringed sites of the underlying morphism of schemes is
the structure comparison of the composite route. -/
theorem homEquiv_unitToPushforwardObjUnit_representedSchemeStructureMapRing :
    (representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
        ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))
        (SheafOfModules.unitToPushforwardObjUnit
          (representedSchemeStructureMapRing B S hS g)) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
        (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) :=
  (SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp_map
    (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)).symm

/-- **The two routes round the square of a represented morphism agree at the unit module.**  The
transpose along [Stacks Project, Tag 03D7] of the canonical map `f^*𝒪 ⟶ 𝒪` of
[Stacks Project, Tag 03LU], followed by the direct image of the structure comparison of the
identification of the two small étale sites of `T'`, is the structure comparison of the route
through the morphism of small étale ringed sites of the underlying morphism of schemes, followed
by the comparison of the two composite direct images. -/
theorem homEquiv_structureModulePullbackMap_comp_eq :
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)) ≫
        (modulePushforward B S hS (representedSpaceMap B S hS g)).map
          (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        (representedModulePushforwardSquareIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) :=
  (((homEquiv_structureModulePullbackMap_comp_unitToPushforwardObjUnit B S hS g hg).trans
          ((unitToPushforwardObjUnit_smallBaseChangeSharp_naturality B S hS g hg).trans
            (unitToPushforwardObjUnit_smallBaseChangeSharp_fold B S hS g hg))).trans
        (congrArg (fun z ↦ SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
              (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
              (representedEquivSharp B S hS T')) ≫ z)
          (modulePushforwardChartIso_inv_app_pushforward_eq B S hS g hg))).trans
    (unitToPushforwardObjUnit_comp_representedModulePushforwardSquareIso B S hS g hg).symm

/-- The transpose along the composite adjunction of the reading of the canonical map
`f^*𝒪 ⟶ 𝒪` on the small étale site of the representing scheme is the structure comparison of the
other route round the square, followed by the comparison of the two composite direct images.

The transpose along a composite is `Stacks.CategoryTheory.comp_homEquiv_map`, and the unit of
the identification of the two small étale sites of `T'`, read at the unit module, is the
structure comparison of that identification. -/
theorem homEquiv_comp_structureModulePullbackMap_eq :
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
          (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction).homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        (representedModulePushforwardSquareIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) := by
  have hP4 : (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction.unit.app
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)) =
      SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T') := rfl
  refine Eq.trans (Stacks.CategoryTheory.comp_homEquiv_map
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction
    (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
    (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
    (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) ?_
  refine Eq.trans (congrArg (fun z ↦ (modulePullbackAdjunction B S hS
            (representedSpaceMap B S hS g)).homEquiv
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)) ≫
        (modulePushforward B S hS (representedSpaceMap B S hS g)).map z) hP4) ?_
  exact homEquiv_structureModulePullbackMap_comp_eq B S hS g hg

/-- The transpose along the other composite adjunction of the canonical map `ε^*𝒪 ⟶ 𝒪` of the
morphism of small étale ringed sites of the underlying morphism of schemes is the structure
comparison of that route, followed by the comparison of the two composite direct images. -/
theorem homEquiv_ofNatIsoRight_pullbackObjUnitToUnit_eq :
    (((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.comp
            (SheafOfModules.pullbackPushforwardAdjunction.{u}
              (representedSchemeStructureMapRing B S hS g))).ofNatIsoRight
          (representedModulePushforwardSquareIso B S hS g hg)).homEquiv
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))
        (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g)) =
      SheafOfModules.unitToPushforwardObjUnit (SheafOfModules.comparisonComp
          (representedEquivSharp B S hS T) (representedSchemeStructureMapRing B S hS g)) ≫
        (representedModulePushforwardSquareIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) := by
  refine Eq.trans (Stacks.CategoryTheory.ofNatIsoRight_comp_homEquiv_apply
    (representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))
    (representedModulePushforwardSquareIso B S hS g hg)
    (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
    (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))
    (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g))) ?_
  refine Eq.trans (congrArg (fun z ↦
      (representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.homEquiv
            (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
            ((SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).obj
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) z ≫
        (representedModulePushforwardSquareIso B S hS g hg).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (representedSchemeStructureMapRing B S hS g))) ?_
  exact congrArg (fun z ↦ z ≫ (representedModulePushforwardSquareIso B S hS g hg).hom.app
      (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))
    (homEquiv_unitToPushforwardObjUnit_representedSchemeStructureMapRing B S hS g)

/-- `AlgebraicGeometry.Space.representedModulePullbackIso` is the comparison of the two left
adjoints, written out.  The identity is definitional and is recorded so that
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` can be applied to a goal naming the
isomorphism without unfolding it during unification. -/
theorem representedModulePullbackIso_eq :
    representedModulePullbackIso B S hS g hg =
      Adjunction.leftAdjointUniq
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
          (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction)
        (((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g))).ofNatIsoRight
          (representedModulePushforwardSquareIso B S hS g hg)) :=
  rfl

/-- **The identification of the inverse image of modules along a represented morphism with the
small étale pullback of the underlying morphism of schemes carries the canonical map
`f^*𝒪 ⟶ 𝒪` of [Stacks Project, Tag 03LU] to the one of the morphism of small étale ringed sites
of the underlying morphism of schemes.**

Both sides are morphisms out of an inverse image of the unit module, hence determined by their
transposes along the respective adjunction; the two transposes agree by
`AlgebraicGeometry.Space.homEquiv_comp_structureModulePullbackMap_eq` and
`AlgebraicGeometry.Space.homEquiv_ofNatIsoRight_pullbackObjUnitToUnit_eq`, and
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` turns that into the statement.  No
value of the comparison is computed. -/
theorem structureModulePullbackMap_representedModulePullbackIso :
    (representedSmallEtaleModuleEquivalence B S hS T').inverse.map
        (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)) =
      (representedModulePullbackIso B S hS g hg).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)) ≫
        SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g) := by
  rw [representedModulePullbackIso_eq B S hS g hg]
  exact Adjunction.eq_leftAdjointUniq_hom_app_comp
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
      (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction)
    (((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (representedSchemeStructureMapRing B S hS g))).ofNatIsoRight
      (representedModulePushforwardSquareIso B S hS g hg))
    (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
    ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
      (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)))
    (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g))
    ((homEquiv_comp_structureModulePullbackMap_eq B S hS g hg).trans
      (homEquiv_ofNatIsoRight_pullbackObjUnitToUnit_eq B S hS g hg).symm)

end AlgebraicGeometry.Space

end
