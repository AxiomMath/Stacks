module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Deformation.ToposThickening.FlatLiftBaseRingComparison

/-!
# Relative flat representatives under étale base change of the target

Let

```
X' --i--> X
|f'       |f
v         v
Y' --g--> Y
```

be a cartesian square of algebraic spaces with `g` étale, so that `i` is étale too.  If an
object `E` of `D(𝒪_X)` read in `D(f⁻¹𝒪_Y)` is represented by a complex of flat
`f⁻¹𝒪_Y`-modules concentrated in degrees `[a, b]`, then its étale restriction `E|_{X'}` read in
`D(f'⁻¹𝒪_{Y'})` is represented by a complex of flat `f'⁻¹𝒪_{Y'}`-modules concentrated in the same
degrees.

The representative is the inverse image `i⁻¹K` of the given one, read over `f'⁻¹𝒪_{Y'}` through
the canonical isomorphism `f'⁻¹𝒪_{Y'} ≅ i⁻¹f⁻¹𝒪_Y` of Stacks 03G8 (the composition law
`i⁻¹f⁻¹ = (f ∘ i)⁻¹ = (g ∘ f')⁻¹ = f'⁻¹g⁻¹` and `g⁻¹𝒪_Y = 𝒪_{Y'}` for étale `g`).  The inverse
image of a flat module is flat (Stacks 05VD), restriction of scalars along an isomorphism keeps
flatness, and the identification with `E|_{X'}` is the commutation of inverse images with
restriction of scalars together with Stacks' Equation 03LW.

This is how the finite Tor dimension hypothesis of Stacks 08IS reaches the affine étale charts
of the base.

## Main definitions

* `AlgebraicGeometry.Space.relativeBaseChangeRingIso`: `f'⁻¹𝒪_{Y'} ≅ i⁻¹f⁻¹𝒪_Y`.
* `AlgebraicGeometry.Space.relativeBaseChangeModules`: the inverse image of `f⁻¹𝒪_Y`-modules,
  read over `f'⁻¹𝒪_{Y'}`.

## Main results

* `AlgebraicGeometry.Space.relativeBaseChangeRingIso_structureMap`: the ring isomorphism is
  compatible with the structure maps.
* `AlgebraicGeometry.Space.exists_flatRepresentative_etaleModulePullback`: the flat
  representative under base change.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Sheaves.RingedPoint

variable {T : Type*} [Category T] {J : GrothendieckTopology T}

/-- **Restriction of scalars along the two sides of a commutative square of sheaves of rings**:
`(β ⋙ α)^* ≅ (β' ⋙ α')^*` when `α ≫ β = α' ≫ β'`. -/
def sheafRestrictScalarsSquareIso {R₁ R₂ R₂' R₃ : Sheaf J RingCat.{u}} (α : R₁ ⟶ R₂)
    (β : R₂ ⟶ R₃) (α' : R₁ ⟶ R₂') (β' : R₂' ⟶ R₃) (h : α ≫ β = α' ≫ β') :
    SheafOfModules.restrictScalars.{u} β ⋙ SheafOfModules.restrictScalars.{u} α ≅
      SheafOfModules.restrictScalars.{u} β' ⋙ SheafOfModules.restrictScalars.{u} α' :=
  NatIso.ofComponents (fun M => (SheafOfModules.fullyFaithfulForget R₁).preimageIso
      (PresheafOfModules.isoMk (fun Z =>
        (ModuleCat.restrictScalarsComp'App (α.hom.app Z).hom (β.hom.app Z).hom
          ((β.hom.app Z).hom.comp (α.hom.app Z).hom) rfl (M.val.obj Z)).symm ≪≫
        ModuleCat.restrictScalarsComp'App (α'.hom.app Z).hom (β'.hom.app Z).hom
          ((β.hom.app Z).hom.comp (α.hom.app Z).hom) (by
            have := congrArg (fun φ : R₁ ⟶ R₃ => (φ.hom.app Z).hom) h
            simpa using this) (M.val.obj Z))
        (fun _ _ _ => rfl)))
    (fun _ => rfl)

end Stacks.Sheaves.RingedPoint

namespace Stacks.Sheaves.ToposPullback

universe w w' v v' u₁ u₂

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w'}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify J (Type w)] [HasSheafify K (Type w')]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [Φ.IsLeftAdjoint] [PreservesFiniteLimits Φ]

/-- A ring isomorphism onto the inverse-image sheaf of commutative rings, read as a morphism of
sheaves of rings to the inverse image of the underlying sheaf of rings. -/
abbrev pullbackRingIsoMap (O : Sheaf K CommRingCat.{w'}) {O₁ : Sheaf J CommRingCat.{w}}
    (e : O₁ ≅ (pullbackCommRingSheafFunctor J Φ).obj O) :
    Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶
      pullbackRingSheaf J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map e.hom

/-- **The inverse image of a flat module, read over a ring isomorphic to the inverse-image ring,
is flat.** -/
theorem isFlat_restrictScalars_pullbackModuleObj (O : Sheaf K CommRingCat.{w'})
    {O₁ : Sheaf J CommRingCat.{w}} (e : O₁ ≅ (pullbackCommRingSheafFunctor J Φ).obj O)
    (G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := O) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := O₁)
      ((SheafOfModules.restrictScalars (pullbackRingIsoMap Φ O e)).obj
        ((pullbackModuleFunctor J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj G)) := by
  have : Φ.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_isLeftAdjoint _
  exact Deformation.ToposThickening.isFlat_restrictScalars_of_iso e _
    (isFlat_pullbackModuleObj_of_isFlat Φ O G hG)

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Equal morphisms have equal inverse-image structure sheaves, with the structure maps
corresponding. -/
lemma eqToHom_structureSharpInverseImage {h₁ h₂ : X ⟶ Y} (h : h₁ = h₂) :
    eqToHom (congrArg (inverseImageStructureSheaf B S hS) h) ≫
        structureSharpInverseImage B S hS h₂ =
      structureSharpInverseImage B S hS h₁ := by
  subst h
  exact Category.id_comp _

variable (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom)

/-- **The canonical isomorphism `f'⁻¹𝒪_{Y'} ≅ i⁻¹f⁻¹𝒪_Y`** of sheaves of commutative rings on the
small étale site of `X'`, for a cartesian square with `g` étale. -/
def relativeBaseChangeRingIso :
    inverseImageStructureSheaf B S hS f' ≅
      (smallEtaleInverseImageRing B S hS i).obj (inverseImageStructureSheaf B S hS f) :=
  (etaleBaseInverseImageStructureSheafIso B S hS f' g hg).symm ≪≫
    eqToIso (congrArg (inverseImageStructureSheaf B S hS) sq.w).symm ≪≫
    (inverseImageStructureSheafCompIso B S hS i f).symm

include sq in
/-- **The ring isomorphism is compatible with the structure maps**: followed by the inverse
image of `f♯` and the identification `i⁻¹𝒪_X = 𝒪_{X'}`, it is `f'♯`. -/
theorem relativeBaseChangeRingIso_structureMap (hi : IsEtale B S hS i.hom) :
    (relativeBaseChangeRingIso B S hS sq hg).hom ≫
        (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS f) ≫
        (etaleInverseImageStructureSheafIso B S hS i hi).hom =
      structureSharpInverseImage B S hS f' := by
  rw [inverseImageStructureSharp_square B S hS i hi f]
  simp only [relativeBaseChangeRingIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [eqToHom_structureSharpInverseImage B S hS sq.w.symm,
    ← etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS f' g hg,
    Iso.inv_hom_id_assoc]

/-- The ring-level form of a compatibility of a ring isomorphism `f'⁻¹𝒪_{Y'} ≅ i⁻¹f⁻¹𝒪_Y` with
the structure maps. -/
theorem relativeRingIso_ring_structureMap (hi : IsEtale B S hS i.hom)
    (e : inverseImageStructureSheaf B S hS f' ≅
      (smallEtaleInverseImageRing B S hS i).obj (inverseImageStructureSheaf B S hS f))
    (he : e.hom ≫ (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS f) ≫
        (etaleInverseImageStructureSheafIso B S hS i hi).hom =
          structureSharpInverseImage B S hS f') :
    Stacks.Sheaves.ToposPullback.pullbackRingIsoMap
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
      (inverseImageStructureSheaf B S hS f) e ≫
        Stacks.Sheaves.ToposPullback.pullbackRingSheafMap (SmallEtale.topology B S hS X'.1)
          (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
          (inverseImageStructureMap B S hS f) =
      inverseImageStructureMap B S hS f' ≫
        (etaleStructureRingSheafIso B S hS i hi).inv := by
  have h₂ : e.hom ≫
      (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS f) =
        structureSharpInverseImage B S hS f' ≫
          (etaleInverseImageStructureSheafIso B S hS i hi).inv := by
    rw [← he, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h' := congrArg
    (fun φ => (sheafCompose (SmallEtale.topology B S hS X'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map φ) h₂
  simp only [Functor.map_comp] at h'
  have e₁ : Stacks.Sheaves.ToposPullback.pullbackRingSheafMap (SmallEtale.topology B S hS X'.1)
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
      (inverseImageStructureMap B S hS f) =
        (sheafCompose (SmallEtale.topology B S hS X'.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          ((smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS f)) :=
    (Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap
      (SmallEtale.topology B S hS X'.1) (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
      (structureSharpInverseImage B S hS f)).symm
  exact (congrArg (fun φ => (sheafCompose (SmallEtale.topology B S hS X'.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map e.hom ≫ φ) e₁).trans h'

variable (e : inverseImageStructureSheaf B S hS f' ≅
  (smallEtaleInverseImageRing B S hS i).obj (inverseImageStructureSheaf B S hS f))

/-- **The inverse image of `f⁻¹𝒪_Y`-modules along `i`, read over `f'⁻¹𝒪_{Y'}`** through a ring
isomorphism `f'⁻¹𝒪_{Y'} ≅ i⁻¹f⁻¹𝒪_Y`. -/
abbrev relativeRingIsoModules :
    RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f) ⥤
      RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f') :=
  Stacks.Sheaves.ToposPullback.pullbackModuleFunctor (SmallEtale.topology B S hS X'.1)
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageStructureSheaf B S hS f)) ⋙
    SheafOfModules.restrictScalars (Stacks.Sheaves.ToposPullback.pullbackRingIsoMap
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
      (inverseImageStructureSheaf B S hS f) e)

/-- **Restricting scalars to `f⁻¹𝒪_Y` and then pulling back along `i` is pulling back along `i`
and then restricting scalars to `f'⁻¹𝒪_{Y'}`.** -/
def relativeRingIsoModulesIso (hi : IsEtale B S hS i.hom) (he : e.hom ≫
      (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS f) ≫
        (etaleInverseImageStructureSheafIso B S hS i hi).hom =
          structureSharpInverseImage B S hS f') :
    scalarRestriction B S hS f ⋙ relativeRingIsoModules B S hS e ≅
      etaleModulePullback.{u, u} B S hS i hi ⋙ scalarRestriction B S hS f' :=
  let α : (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O :
      Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) ⟶ structureRingSheaf B S hS X :=
    inverseImageStructureMap B S hS f
  let t := Stacks.Sheaves.ToposPullback.pullbackModuleFunctorRestrictScalarsIso
    (SmallEtale.topology B S hS X'.1) (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage α
  let r₁ := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        e.hom)
  let α' : (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f').O :
      Sheaf (SmallEtale.topology B S hS X'.1) RingCat.{u}) ⟶ structureRingSheaf B S hS X' :=
    inverseImageStructureMap B S hS f'
  let q := Stacks.Sheaves.RingedPoint.sheafRestrictScalarsSquareIso
    ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        e.hom)
    (Stacks.Sheaves.ToposPullback.pullbackRingSheafMap (SmallEtale.topology B S hS X'.1)
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage α)
    α' (etaleStructureRingSheafIso B S hS i hi).inv
    (relativeRingIso_ring_structureMap B S hS hi e he)
  let e := etaleModuleInverseImageIsoEtaleModulePullback B S hS i hi
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight t r₁ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ q ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e (scalarRestriction B S hS f')

/-- **The base change of a flat `f⁻¹𝒪_Y`-module is flat over `f'⁻¹𝒪_{Y'}`.** -/
theorem isFlat_relativeRingIsoModules
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (inverseImageStructureSheaf B S hS f)))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat (O := inverseImageStructureSheaf B S hS f) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := inverseImageStructureSheaf B S hS f')
      ((SheafOfModules.restrictScalars (Stacks.Sheaves.ToposPullback.pullbackRingIsoMap
        (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
        (inverseImageStructureSheaf B S hS f) e)).obj
        ((Stacks.Sheaves.ToposPullback.pullbackModuleFunctor (SmallEtale.topology B S hS X'.1)
          (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (inverseImageStructureSheaf B S hS f))).obj G)) := by
  have : (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.IsLeftAdjoint :=
    ⟨_, ⟨(smallEtaleRingedToposHom B S hS i).toToposHom.adj⟩⟩
  have : PreservesFiniteLimits (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage :=
    (smallEtaleRingedToposHom B S hS i).toToposHom.preservesFiniteLimits
  exact Stacks.Sheaves.ToposPullback.isFlat_restrictScalars_pullbackModuleObj
    (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
    (inverseImageStructureSheaf B S hS f) e G hG

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Relative flat representatives under étale restriction.**  Let `i : X' ⟶ X` be étale and
let `f'⁻¹𝒪_{Y'} ≅ i⁻¹f⁻¹𝒪_Y` be compatible with the structure maps.  If `E` read in `D(f⁻¹𝒪_Y)`
is represented by a complex of flat modules concentrated in `[a, b]`, then `E|_{X'}` read in
`D(f'⁻¹𝒪_{Y'})` is represented by a complex of flat modules concentrated in `[a, b]`. -/
theorem exists_flatRepresentative_of_relativeRingIso (hi : IsEtale B S hS i.hom)
    (he : e.hom ≫
      (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS f) ≫
        (etaleInverseImageStructureSheafIso B S hS i hi).hom = structureSharpInverseImage B S hS f')
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ)
    (hK : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) (K.X n))
    (a b : ℤ) (hKab : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K.X n))
    (eK : DerivedCategory.Q.obj K ≅ (derivedScalarRestriction B S hS f).obj E) :
    ∃ K' : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f')) ℤ,
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
        (O := (inverseImageRingedSite B S hS f').O) (K'.X n)) ∧
      (∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K'.X n)) ∧
      Nonempty (DerivedCategory.Q.obj K' ≅ (derivedScalarRestriction B S hS f').obj
        ((etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory.obj E)) := by
  let P₁ := Stacks.Sheaves.ToposPullback.pullbackModuleFunctor (SmallEtale.topology B S hS X'.1)
      (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageStructureSheaf B S hS f))
  let P₂ := SheafOfModules.restrictScalars (Stacks.Sheaves.ToposPullback.pullbackRingIsoMap
        (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage
        (inverseImageStructureSheaf B S hS f) e)
  refine ⟨(P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
    fun n => isFlat_relativeRingIsoModules B S hS e _ (hK n),
    fun n hn => P₂.map_isZero (P₁.map_isZero (hKab n hn)), ⟨?_⟩⟩
  have : P₁.Additive := inferInstanceAs (Stacks.Sheaves.RingedToposModules.inverseImageModules
    (smallEtaleRingedToposHom B S hS i).toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageStructureSheaf B S hS f))).Additive
  have : PreservesFiniteLimits P₁ := inferInstanceAs (PreservesFiniteLimits
    (Stacks.Sheaves.RingedToposModules.inverseImageModules
    (smallEtaleRingedToposHom B S hS i).toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageStructureSheaf B S hS f))))
  have : PreservesFiniteColimits P₁ := inferInstanceAs (PreservesFiniteColimits
    (Stacks.Sheaves.RingedToposModules.inverseImageModules
    (smallEtaleRingedToposHom B S hS i).toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageStructureSheaf B S hS f))))
  have : (relativeRingIsoModules B S hS e).Additive := inferInstanceAs (P₁ ⋙ P₂).Additive
  have : PreservesFiniteLimits (relativeRingIsoModules B S hS e) :=
    inferInstanceAs (PreservesFiniteLimits (P₁ ⋙ P₂))
  have : PreservesFiniteColimits (relativeRingIsoModules B S hS e) :=
    inferInstanceAs (PreservesFiniteColimits (P₁ ⋙ P₂))
  let Ei := etaleModulePullback.{u, u} B S hS i hi
  let F₀ := scalarRestriction B S hS f
  let G₀ := scalarRestriction B S hS f'
  exact (P₂.mapDerivedCategoryFactors.app _).symm ≪≫
    P₂.mapDerivedCategory.mapIso ((P₁.mapDerivedCategoryFactors.app K).symm ≪≫
      P₁.mapDerivedCategory.mapIso eK) ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso P₁ P₂).symm.app _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F₀
      (relativeRingIsoModules B S hS e)).symm.app E ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (relativeRingIsoModulesIso B S hS e hi he)).app E ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso Ei G₀).app E

include sq hg in
/-- **Relative flat representatives under étale base change of the target.**  For a cartesian
square with `g` étale, if `E` read in `D(f⁻¹𝒪_Y)` is represented by a complex of flat modules
concentrated in `[a, b]`, then so is `E|_{X'}` read in `D(f'⁻¹𝒪_{Y'})`. -/
theorem exists_flatRepresentative_etaleModulePullback (hi : IsEtale B S hS i.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ)
    (hK : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) (K.X n))
    (a b : ℤ) (hKab : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K.X n))
    (eK : DerivedCategory.Q.obj K ≅ (derivedScalarRestriction B S hS f).obj E) :
    ∃ K' : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f')) ℤ,
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
        (O := (inverseImageRingedSite B S hS f').O) (K'.X n)) ∧
      (∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K'.X n)) ∧
      Nonempty (DerivedCategory.Q.obj K' ≅ (derivedScalarRestriction B S hS f').obj
        ((etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory.obj E)) :=
  exists_flatRepresentative_of_relativeRingIso B S hS (relativeBaseChangeRingIso B S hS sq hg) hi
    (relativeBaseChangeRingIso_structureMap B S hS sq hg hi) E K hK a b hKab eK

/-- **Relative flat representatives under restriction to an étale source.**  For `i : X' ⟶ X`
étale and `f : X ⟶ Y`, if `E` read in `D(f⁻¹𝒪_Y)` is represented by a complex of flat modules
concentrated in `[a, b]`, then so is `E|_{X'}` read in `D((i ≫ f)⁻¹𝒪_Y)`. -/
theorem exists_flatRepresentative_etaleModulePullback_comp {X Y X' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f : X ⟶ Y) (hi : IsEtale B S hS i.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) ℤ)
    (hK : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) (K.X n))
    (a b : ℤ) (hKab : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K.X n))
    (eK : DerivedCategory.Q.obj K ≅ (derivedScalarRestriction B S hS f).obj E) :
    ∃ K' : CochainComplex
        (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS (i ≫ f))) ℤ,
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
        (O := (inverseImageRingedSite B S hS (i ≫ f)).O) (K'.X n)) ∧
      (∀ n : ℤ, n ∉ Set.Icc a b → IsZero (K'.X n)) ∧
      Nonempty (DerivedCategory.Q.obj K' ≅ (derivedScalarRestriction B S hS (i ≫ f)).obj
        ((etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory.obj E)) :=
  exists_flatRepresentative_of_relativeRingIso B S hS
    (inverseImageStructureSheafCompIso B S hS i f).symm hi (by
      rw [inverseImageStructureSharp_square B S hS i hi f, Iso.symm_hom, Iso.inv_hom_id_assoc])
    E K hK a b hKab eK

end AlgebraicGeometry.Space

end
