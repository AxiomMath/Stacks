module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraPullbackFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp

/-!
# The unit and the counit of Stacks 03D4 at the structure sheaf

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi, `O` a sheaf of rings on `C` and `𝒜 = f_*O` the
direct-image sheaf of rings. The adjunction
`Stacks.Sheaves.RingedToposModules.tensorInverseImageAdjPushforwardModuleFunctor` is Stacks 03D4,

`𝒢 ↦ O ⊗_{f⁻¹𝒜} f⁻¹𝒢  ⊣  F ↦ f_*F`,

and this file proves that its **unit is invertible at `𝒜` regarded as a module over itself**, for
an arbitrary morphism of topoi: no hypothesis of any kind is placed on `f` or on `O`.  The
specialisation to the small étale sites of a morphism of algebraic spaces is the unit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` at `𝒜 = f_*𝒪_Y`; the counit at
`𝒪_Y` follows from it by the triangle identity.

These are the analogues of the scheme-level
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_unit_app_unit` and `...isIso_counit_app_unit`,
which `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_unit_app_free` and
`...isIso_counit_app_free` upgrade from the structure sheaf to a free module by the colimit
argument.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.tensorInverseImageObjUnitIso` — the left adjoint of
  Stacks 03D4 carries the unit `𝒜`-module to the unit `O`-module: `O ⊗_{f⁻¹𝒜} f⁻¹𝒜 ≅ O`.

## Main results

* `Stacks.Sheaves.RingedToposModules.homEquiv_tensorInverseImageObjUnitIso` — **the triangle
  computing the unit of Stacks 03D4 at the structure sheaf**: the transpose of that isomorphism
  is the identity of `𝒜`.
* `isIso_tensorInverseImageAdjPushforwardModuleFunctor_unit_app_unit` — **the unit of Stacks 03D4
  is invertible at the structure sheaf.**
* `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_unit` — the same
  for the adjunction of Stacks 03D4 on the small étale sites of a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_pullback` —
  invertibility of the unit at `𝒢` gives invertibility of the counit at `𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢`;
  this is the triangle identity and uses nothing about `f` or `𝒢`.
* `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_unit` — the
  counit is invertible at `𝒪_Y`.

## Implementation notes

The unit of Stacks 03D4 has no component formula — the adjunction is the composite of Stacks 03D3
with the change-of-rings adjunction of Stacks 03CZ, transported along
`Stacks.Sheaves.RingedToposModules.restrictScalarsRingCounitCompDirectImageIso` — so the route is
the formal one, through the hom-set bijection.  The transpose of
`tensorInverseImageObjUnitIso` is computed in three steps, in the order in which the adjunction
is assembled:

* the change-of-rings half is `Stacks.SheafOfModules.ChangeOfRings.homEquiv_unitComparison`: the
  transpose of the base-change unitor `R' ⊗_R R ≅ R'` is the canonical map
  `R ⟶ (R')_R`, for **any** left adjoint of restriction of scalars;
* the inverse-image half is the unit of Stacks 03D3, whose underlying map of sheaves of sets is
  the unit of `f⁻¹ ⊣ f_*` (`moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app`);
* the comparison of the two readings of the direct image is the identity on sections.

So on underlying sheaves of sets the whole composite is
`𝒜 ⟶ f_*f⁻¹𝒜 ⟶ f_*O`, the unit of `f⁻¹ ⊣ f_*` followed by the direct image of its counit, which
is the identity by the triangle identity; and
`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor` promotes that to an equality of
morphisms of sheaves of modules.

Two spellings of one object are kept apart deliberately.  The inverse image carries the unit
`𝒜`-module to the unit `f⁻¹𝒜`-module on the nose
(`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` is `CategoryTheory.Iso.refl`), but the two
spellings are *not* interchangeable by rewriting: the module they name sits under extension of
scalars, which goes through sheafification, so deciding the two spellings equal there exhausts
the heartbeat budget.  `tensorInverseImageObjUnitIso` therefore carries that comparison as an
explicit factor rather than relying on the identification, and the proof of
`homEquiv_tensorInverseImageObjUnitIso` generalises the morphism whose transpose is computed to a
variable, so that every rewrite inside is type-correct without unfolding extension of scalars.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Sheaves.RingedToposModules

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf J RingCat.{w})

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Composing with the underlying map of sheaves of sets of the identification of the inverse
image of a unit module with a unit module does nothing: that identification is the identity on
sections. -/
lemma moduleSheafFunctor_map_pullbackModuleUnitIso_symm_hom_comp
    (O' : Sheaf K RingCat.{w'}) {T : Sheaf J (Type w)}
    (m : (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O')).obj
        (SheafOfModules.unit (inverseImageRingSheaf f O')) ⟶ T) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O')).map
        (pullbackModuleUnitIso J f.inverseImage O').symm.hom ≫ m = m :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison of the right-hand functor of Stacks 03D4 with the direct image of
Stacks 03D1 is the identity on underlying sheaves of sets: both sides apply `f_*` to the sheaf of
sets underlying the module, and only the two scalar actions differ. -/
lemma moduleSheafFunctor_map_restrictScalarsRingCounitCompDirectImageIso_hom_app
    (M : SheafOfModules.{w} O) :
    (Sheaf.moduleSheafFunctor (pushforwardRingSheaf f O)).map
        ((restrictScalarsRingCounitCompDirectImageIso f O).hom.app M) = 𝟙 _ :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **The left adjoint of Stacks 03D4 at the unit module**: `O ⊗_{f⁻¹𝒜} f⁻¹𝒜 ≅ O`, for
`𝒜 = f_*O`.

The inverse image carries the unit `𝒜`-module to the unit `f⁻¹𝒜`-module, and the base-change
unitor of Stacks 03CZ carries that to the unit `O`-module. -/
noncomputable def tensorInverseImageObjUnitIso :
    (inverseImageModules f (pushforwardRingSheaf f O) ⋙
          Stacks.NoncommChangeOfRings.Sheaf.extendScalars.{w} (ringCounit f O)).obj
        (SheafOfModules.unit (pushforwardRingSheaf f O)) ≅ SheafOfModules.unit O :=
  (Stacks.NoncommChangeOfRings.Sheaf.extendScalars.{w} (ringCounit f O)).mapIso
      (pullbackModuleUnitIso J f.inverseImage (pushforwardRingSheaf f O)).symm ≪≫
    Stacks.SheafOfModules.ChangeOfRings.baseChangeUnitor (ringCounit f O)
      (Stacks.NoncommChangeOfRings.Sheaf.extendRestrictScalarsAdjunction.{w} (ringCounit f O))

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse-image half of `homEquiv_tensorInverseImageObjUnitIso`: a map out of the inverse
image of the unit `𝒜`-module whose underlying map of sheaves of sets is the counit of
`f⁻¹ ⊣ f_*` at `O` transposes, under Stacks 03D3 followed by the comparison
`restrictScalarsRingCounitCompDirectImageIso`, to the identity of `𝒜 = f_*O`. -/
private lemma homEquiv_comp_restrictScalarsRingCounitCompDirectImageIso_hom_app_unit
    (m : (inverseImageModules f (pushforwardRingSheaf f O)).obj
        (SheafOfModules.unit (pushforwardRingSheaf f O)) ⟶
      (SheafOfModules.restrictScalars.{w} (ringCounit f O)).obj (SheafOfModules.unit O))
    (hm : (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f (pushforwardRingSheaf f O))).map m =
        f.adj.counit.app (Sheaf.ringSheaf O)) :
    (inverseImageAdjDirectImageModules f (pushforwardRingSheaf f O)).homEquiv
          (SheafOfModules.unit (pushforwardRingSheaf f O))
          ((SheafOfModules.restrictScalars.{w} (ringCounit f O)).obj
            (SheafOfModules.unit O)) m ≫
        (restrictScalarsRingCounitCompDirectImageIso f O).hom.app (SheafOfModules.unit O) =
      𝟙 (SheafOfModules.unit (pushforwardRingSheaf f O)) := by
  rw [Adjunction.homEquiv_unit]
  refine hom_ext_moduleSheafFunctor ?_
  simp only [CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_restrictScalarsRingCounitCompDirectImageIso_hom_app,
    moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app,
    moduleSheafFunctor_map_directImageModules_map, hm]
  exact (f.adj.right_triangle_components (Sheaf.ringSheaf O)).trans
    ((Sheaf.moduleSheafFunctor (pushforwardRingSheaf f O)).map_id
      (SheafOfModules.unit (pushforwardRingSheaf f O))).symm

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The change-of-rings half of `homEquiv_tensorInverseImageObjUnitIso`: the transpose of
`tensorInverseImageObjUnitIso` under the adjunction of Stacks 03CZ is the comparison
`pullbackModuleUnitIso` followed by the canonical map to the restriction of scalars. -/
private lemma extendRestrictScalarsAdjunction_homEquiv_tensorInverseImageObjUnitIso_hom :
    (Stacks.NoncommChangeOfRings.Sheaf.extendRestrictScalarsAdjunction.{w}
          (ringCounit f O)).homEquiv
        ((inverseImageModules f (pushforwardRingSheaf f O)).obj
          (SheafOfModules.unit (pushforwardRingSheaf f O)))
        (SheafOfModules.unit O) (tensorInverseImageObjUnitIso f O).hom =
      (pullbackModuleUnitIso J f.inverseImage (pushforwardRingSheaf f O)).symm.hom ≫
        Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringCounit f O) :=
  ((Stacks.NoncommChangeOfRings.Sheaf.extendRestrictScalarsAdjunction.{w}
      (ringCounit f O)).homEquiv_naturality_left _ _).trans
    (congrArg
      (fun z ↦ (pullbackModuleUnitIso J f.inverseImage
          (pushforwardRingSheaf f O)).symm.hom ≫ z)
      (Stacks.SheafOfModules.ChangeOfRings.homEquiv_unitComparison _ _))

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- On underlying sheaves of sets, the comparison `pullbackModuleUnitIso` followed by the
canonical map to the restriction of scalars along the counit is the counit of `f⁻¹ ⊣ f_*`
at `O`. -/
private lemma moduleSheafFunctor_map_pullbackModuleUnitIso_unitToRestrictScalarsUnit :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f (pushforwardRingSheaf f O))).map
        ((pullbackModuleUnitIso J f.inverseImage (pushforwardRingSheaf f O)).symm.hom ≫
          Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringCounit f O)) =
      f.adj.counit.app (Sheaf.ringSheaf O) := by
  refine (CategoryTheory.Functor.map_comp _ _ _).trans ?_
  rw [moduleSheafFunctor_map_pullbackModuleUnitIso_symm_hom_comp]
  exact (Stacks.SheafOfModules.ChangeOfRings.moduleSheafFunctor_map_unitToRestrictScalarsUnit
    (ringCounit f O)).trans
    (Stacks.Sheaves.ToposPushforward.ringSheafMap_ringCounit f O)

/-- **The triangle computing the unit of Stacks 03D4 at the structure sheaf.**  The transpose of
`Stacks.Sheaves.RingedToposModules.tensorInverseImageObjUnitIso` under the adjunction of
Stacks 03D4 is the identity of `𝒜 = f_*O`.

On underlying sheaves of sets the transpose is `𝒜 ⟶ f_*f⁻¹𝒜 ⟶ f_*O`, the unit of `f⁻¹ ⊣ f_*`
followed by the direct image of its counit, and that composite is the identity. -/
theorem homEquiv_tensorInverseImageObjUnitIso :
    (tensorInverseImageAdjPushforwardModuleFunctor f O).homEquiv
        (SheafOfModules.unit (pushforwardRingSheaf f O)) (SheafOfModules.unit O)
        (tensorInverseImageObjUnitIso f O).hom =
      𝟙 (SheafOfModules.unit (pushforwardRingSheaf f O)) := by
  rw [tensorInverseImageAdjPushforwardModuleFunctor, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv, Equiv.trans_apply,
    extendRestrictScalarsAdjunction_homEquiv_tensorInverseImageObjUnitIso_hom f O]
  exact homEquiv_comp_restrictScalarsRingCounitCompDirectImageIso_hom_app_unit f O _
    (moduleSheafFunctor_map_pullbackModuleUnitIso_unitToRestrictScalarsUnit f O)

/-- **The unit of Stacks 03D4 is invertible at the structure sheaf.**  For an arbitrary morphism
of topoi `f` and an arbitrary sheaf of rings `O` on its source, the unit of

`𝒢 ↦ O ⊗_{f⁻¹𝒜} f⁻¹𝒢  ⊣  F ↦ f_*F`

is invertible at `𝒜 = f_*O` regarded as a module over itself: the triangle
`Stacks.Sheaves.RingedToposModules.homEquiv_tensorInverseImageObjUnitIso` factors the identity
through it, and the other factor is the direct image of an isomorphism. -/
theorem isIso_tensorInverseImageAdjPushforwardModuleFunctor_unit_app_unit :
    IsIso ((tensorInverseImageAdjPushforwardModuleFunctor f O).unit.app
      (SheafOfModules.unit (pushforwardRingSheaf f O))) := by
  have key := homEquiv_tensorInverseImageObjUnitIso f O
  rw [Adjunction.homEquiv_unit] at key
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    (Functor.map_isIso (pushforwardModuleFunctor f O) (tensorInverseImageObjUnitIso f O).hom)
    (IsIso.id _) key

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **The unit of the adjunction of Stacks 03D4 for algebraic spaces is invertible at the
direct-image algebra.**  For an arbitrary morphism `f : Y ⟶ X` of algebraic spaces and
`𝒜 = f_*𝒪_Y`, the unit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` is invertible at `𝒜` regarded as a
module over itself.  No hypothesis is placed on `f`.

This is `isIso_tensorInverseImageAdjPushforwardModuleFunctor_unit_app_unit` at the morphism of
small étale ringed topoi of Stacks 03G8, and the space-level analogue of
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_unit_app_unit`.  Since `𝒜` is quasi-coherent as an
`𝒜`-module — the second assertion of Stacks 08AI applied to the first assertion of Stacks 07U8 —
it is a genuine instance of the hypothesis `hunit` of
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_unit_counit`. -/
theorem isIso_directImageAlgebraPullbackAdjunction_unit_app_unit (f : Y ⟶ X) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app
      (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))) :=
  isIso_tensorInverseImageAdjPushforwardModuleFunctor_unit_app_unit
    (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureRingSheaf B S hS Y)

/-- **Invertibility of the unit at `𝒢` gives invertibility of the counit at
`𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢`.**  This is the triangle identity of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` and uses nothing about `f` or
`𝒢`. -/
theorem isIso_directImageAlgebraPullbackAdjunction_counit_app_pullback (f : Y ⟶ X)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))
    (h : IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G)) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app
      ((directImageAlgebraPullback B S hS f).obj G)) :=
  @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ (directImageAlgebraPullback B S hS f)
      ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G) h)
    (IsIso.id _)
    ((directImageAlgebraPullbackAdjunction B S hS f).left_triangle_components G)

/-- **The counit of the adjunction of Stacks 03D4 for algebraic spaces is invertible at the
structure sheaf.**  For an arbitrary morphism `f : Y ⟶ X` of algebraic spaces, the counit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` is invertible at `𝒪_Y`.

The counit is invertible at `𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒜` by
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_pullback` and
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_unit`, and
`AlgebraicGeometry.Space.directImageAlgebraPullbackObjUnitIso` identifies that module with
`𝒪_Y`; naturality of the counit transports the conclusion.  This is the space-level analogue of
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_counit_app_unit`. -/
theorem isIso_directImageAlgebraPullbackAdjunction_counit_app_unit (f : Y ⟶ X) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app
      (SheafOfModules.unit (structureRingSheaf B S hS Y))) := by
  have : IsIso (directImageAlgebraPullbackObjUnitIso B S hS f).hom :=
    (directImageAlgebraPullbackObjUnitIso B S hS f).isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (Functor.map_isIso (moduleDirectImage B S hS f ⋙ directImageAlgebraPullback B S hS f)
      (directImageAlgebraPullbackObjUnitIso B S hS f).hom)
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_directImageAlgebraPullbackAdjunction_counit_app_pullback B S hS f _
        (isIso_directImageAlgebraPullbackAdjunction_unit_app_unit B S hS f))
      (Functor.map_isIso (𝟭 (Modules.{u, u} B S hS Y.1 Y.2))
        (directImageAlgebraPullbackObjUnitIso B S hS f).hom))
    ((directImageAlgebraPullbackAdjunction B S hS f).counit.naturality
      (directImageAlgebraPullbackObjUnitIso B S hS f).hom)

end AlgebraicGeometry.Space

end
