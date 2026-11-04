module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatThickeningAutomorphisms
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.BaseRing
public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionNaiveExt
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposCoefficientChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangle
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquareIso

/-!
# The deformation problem of a flat morphism over a first order thickening

Let `t : S ⟶ S'` be a first order thickening and `f : X ⟶ S` a morphism of schemes. This file
writes down the square-zero extension problem of [Stacks Project, Tag 08UF] on the Zariski
ringed topos `(X_Zar, 𝒪_X)` over `(X_Zar, f⁻¹𝒪_S)` (`structureHom f`, a change of coefficients
along the identity topos), with bottom row `(t ∘ f)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` and kernel module
`f^*𝒞_{S/S'}` (`problem`), and identifies `Ext` of its naive cotangent complex with
`Ext_{𝒪_X}(NL_{X/S}, -)` of the morphism of schemes `f` (`extIso`).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap baseStructureMap_comp)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u

namespace Stacks.Thickenings.FlatDeformation

variable {X S S' : Scheme.{u}}

/-- The ringed topos `(X_Zar, 𝒪_X)`. -/
abbrev sourceTopos (X : Scheme.{u}) : RingedTopos.{u, u, u} :=
  ⟨X.Opens, Opens.grothendieckTopology X, X.sheaf⟩

/-- The reduced base `(X_Zar, f⁻¹𝒪_S)`. -/
abbrev reducedBase (f : X ⟶ S) : RingedTopos.{u, u, u} :=
  ⟨X.Opens, Opens.grothendieckTopology X,
    Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f.toLRSHom.toShHom⟩

/-- `f` read as a change of coefficients `(X_Zar, 𝒪_X) ⟶ (X_Zar, f⁻¹𝒪_S)`. -/
abbrev structureHom (f : X ⟶ S) : RingedToposHom (sourceTopos X) (reducedBase f) :=
  RingedToposHom.coefficientMorphism (Opens.grothendieckTopology X)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f.toLRSHom.toShHom)

/-- The comorphism of `structureHom f` is the structure map `f⁻¹𝒪_S ⟶ 𝒪_X`, read through the
inverse image along the identity. -/
theorem structureHom_fSharpInverseImage (f : X ⟶ S) : (structureHom f).fSharpInverseImage =
    (Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId
      (Opens.grothendieckTopology X)).hom.app
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f.toLRSHom.toShHom) ≫
      Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f.toLRSHom.toShHom :=
  RingedToposHom.coefficientMorphism_fSharpInverseImage.{u, u, u} _ _

/-- The commutative square comparing the comorphism of `structureHom f` with the structure map
`f⁻¹𝒪_S ⟶ 𝒪_X`. -/
theorem structureHom_square (f : X ⟶ S) :
    (structureHom f).fSharpInverseImage ≫ 𝟙 X.sheaf =
      ((Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId
        (Opens.grothendieckTopology X)).app _).hom ≫
        Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f.toLRSHom.toShHom :=
  (Category.comp_id _).trans (structureHom_fSharpInverseImage f)

/-- The naive cotangent complex of the topos-level structure map is that of `f`, up to
restriction of scalars along the identity. -/
def naiveCotangentComplexIso' (f : X ⟶ S) :=
  Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare.{u, u, u, u}
    (Opens.grothendieckTopology X) _ X.sheaf (structureHom f).fSharpInverseImage _ X.sheaf
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f.toLRSHom.toShHom)
    ((Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId
      (Opens.grothendieckTopology X)).app _) (Iso.refl _) (structureHom_square f)

/-- Restriction of scalars along the identity does nothing. -/
def restrictScalarsIdIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) :
    (SheafOfModules.restrictScalars (𝟙 R)).obj M ≅ M where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) (fun _ _ _ => rfl)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun _ _ _ => rfl)⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- The naive cotangent complex of the topos-level structure map is that of `f`. -/
def naiveCotangentComplexIso (f : X ⟶ S) :
    Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X)
        _ X.sheaf (structureHom f).fSharpInverseImage ≅
      Scheme.naiveCotangentComplex f :=
  naiveCotangentComplexIso' f ≪≫
    HomologicalComplex.Hom.isoOfComponents (fun n => restrictScalarsIdIso _)
      (fun _ _ _ => by ext; rfl)

/-- Precomposition with an isomorphism, as an additive equivalence of hom groups. -/
def precompAddEquiv {D : Type*} [Category D] [Preadditive D] {A B : D} (e : A ≅ B) (T : D) :
    (B ⟶ T) ≃+ (A ⟶ T) where
  toFun ξ := e.hom ≫ ξ
  invFun ξ := e.inv ≫ ξ
  left_inv ξ := by simp
  right_inv ξ := by simp
  map_add' ξ η := Preadditive.comp_add _ _ _ _ _ _

/-- **The two readings of `Ext^n_{𝒪_X}(NL_{X/S}, 𝒢)` agree**: the one of the morphism of schemes
`f` and the one of the topos-level structure map `f⁻¹𝒪_S ⟶ 𝒪_X` on the Zariski site of `X`. -/
def extIso (f : X ⟶ S) (G : X.Modules) (n : ℤ) :
    Scheme.naiveCotangentExt f G n ≃+
      Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, u} (Opens.grothendieckTopology X)
        ((inverseImageCommRingFunctor (structureHom f).toToposHom).obj (reducedBase f).O)
        X.sheaf (structureHom f).fSharpInverseImage G n :=
  precompAddEquiv (DerivedCategory.Q.mapIso (naiveCotangentComplexIso f)) _

/-! ### The extension problem -/

section Problem

variable (t : S ⟶ S') (f : X ⟶ S)

/-- `(t ∘ f)⁻¹𝒪_{S'}`, the inverse image on `X` of the structure sheaf of the thickened base. -/
abbrev thickenedBaseRing : TopCat.Sheaf CommRingCat.{u} X :=
  Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf
    (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)

/-- `f⁻¹𝒪_S`. -/
abbrev reducedBaseRing : TopCat.Sheaf CommRingCat.{u} X :=
  Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f.toLRSHom.toShHom

/-- The inverse image along the identity of the Zariski topos of `X`, through which the extension
problem of ringed topoi reads the base rings. -/
abbrev rebuilt (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (inverseImageCommRingFunctor (structureHom f).toToposHom).obj O

/-- The reduction of the thickened base, read through the inverse image along the identity. -/
abbrev rebuiltReduction : rebuilt f (thickenedBaseRing t f) ⟶ rebuilt f (reducedBaseRing f) :=
  (inverseImageCommRingFunctor (structureHom f).toToposHom).map
    (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom t.toLRSHom.toShHom)

/-- The same, as a morphism of sheaves of rings. -/
abbrev rebuiltReductionRing :
    Stacks.SheafOfModules.Tensor.ringSheaf (rebuilt f (thickenedBaseRing t f)) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (rebuilt f (reducedBaseRing f)) :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (rebuiltReduction t f)

/-- The inverse image along the identity is isomorphic to the identity, compatibly with the
reduction. -/
theorem rebuiltReduction_comp_hom :
    rebuiltReduction t f ≫
        ((Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId
          (Opens.grothendieckTopology X)).app (reducedBaseRing f)).hom =
      ((Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId
          (Opens.grothendieckTopology X)).app (thickenedBaseRing t f)).hom ≫
        Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom
          t.toLRSHom.toShHom :=
  (Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId
    (Opens.grothendieckTopology X)).hom.naturality _

/-- A locally surjective morphism of sheaves of commutative rings is locally surjective as a
morphism of sheaves of rings. -/
theorem isLocallySurjective_forget₂_map
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (φ : O₁ ⟶ O₂) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        φ).hom := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  exact (Presheaf.isLocallySurjective_iff_whisker_forget _ φ.hom).mp inferInstance

/-- For a closed immersion `t`, the reduction `(t ∘ f)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S` is locally
surjective. -/
instance isLocallySurjective_baseStructureMap' [IsClosedImmersion t] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom
        t.toLRSHom.toShHom).hom :=
  isLocallySurjective_baseStructureMap (t := t.toLRSHom.toShHom) f.toLRSHom.toShHom
    (fun N r y hy => exists_comorphism_eq_of_isClosedImmersion t N r y hy)

/-- On underlying sheaves of sets, the reduction read through the inverse image along the
identity is the reduction. -/
theorem forget_map_rebuiltReduction :
    (sheafCompose (Opens.grothendieckTopology X) (forget CommRingCat.{u})).map
        (rebuiltReduction t f) =
      (sheafCompose (Opens.grothendieckTopology X) (forget CommRingCat.{u})).map
        (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom
          t.toLRSHom.toShHom) :=
  Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
    (Opens.grothendieckTopology X) (𝟭 _)
    (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom t.toLRSHom.toShHom)

/-- For a closed immersion `t`, `rebuiltReduction t f` is locally surjective. -/
instance isLocallySurjective_rebuiltReduction [IsClosedImmersion t] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (rebuiltReduction t f).hom := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  have h := (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mp
    (isLocallySurjective_baseStructureMap' t f)
  exact (congrArg (fun φ => Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    φ.hom) (forget_map_rebuiltReduction t f)).mpr h

/-- For a closed immersion `t`, `rebuiltReductionRing t f` is locally surjective. -/
instance isLocallySurjective_rebuiltReductionRing [IsClosedImmersion t] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (rebuiltReductionRing t f).hom :=
  isLocallySurjective_forget₂_map _

/-- The kernel of the reduction of the thickened base, as a sheaf of modules over the thickened
base ring (read through the inverse image along the identity). -/
abbrev idealKernel :
    SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (rebuilt f (thickenedBaseRing t f))) :=
  Stacks.Sites.Conormal.idealSheaf.{u, u, u} (Opens.grothendieckTopology X)
    (Stacks.Sites.Conormal.presentationRingHom.{u, u, u} (Opens.grothendieckTopology X)
      (rebuiltReduction t f))

/-- The inverse image along the identity is the identity. -/
def idIso (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) : rebuilt f O ≅ O :=
  (Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId
    (Opens.grothendieckTopology X)).app O

/-- The identification of the sections of the inverse image along the identity with the original
sections is a ring homomorphism whose underlying map is the identity. -/
theorem idIso_hom_app_apply (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : X.Opensᵒᵖ) (a : (rebuilt f O).obj.obj U) :
    ((idIso f O).hom.hom.app U) a = a :=
  congr($((Stacks.Sheaves.ToposPullback.forget_map_pullbackCommRingSheafFunctorId_hom_app
    (Opens.grothendieckTopology X) O)).hom.app U a)

/-- The inverse of `idIso f O` is the identity on sections. -/
theorem idIso_inv_app_apply (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : X.Opensᵒᵖ) (a : O.obj.obj U) :
    ((idIso f O).inv.hom.app U) a = a := by
  have h : ((idIso f O).hom.hom.app U) (((idIso f O).inv.hom.app U) a) = a :=
    congr($((idIso f O).inv_hom_id).hom.app U a)
  exact (idIso_hom_app_apply f O U _).symm.trans h

/-- On sections, `rebuiltReduction t f` is the reduction `(t ∘ f)⁻¹𝒪_{S'} ⟶ f⁻¹𝒪_S`. -/
theorem rebuiltReduction_app_apply (U : X.Opensᵒᵖ)
    (a : (rebuilt f (thickenedBaseRing t f)).obj.obj U) :
    (rebuiltReduction t f).hom.app U a =
      (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom
        t.toLRSHom.toShHom).hom.app U a :=
  congr($((forget_map_rebuiltReduction t f)).hom.app U a)

/-- `rebuiltReduction t f` followed by the comorphism of `structureHom f` is the structure map
`(t ∘ f)⁻¹𝒪_{S'} ⟶ 𝒪_X`, read through the inverse image along the identity. -/
theorem rebuiltReduction_comp_fSharpInverseImage :
    rebuiltReduction t f ≫ (structureHom f).fSharpInverseImage =
      (idIso f (thickenedBaseRing t f)).hom ≫
        Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap
          (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom) := by
  refine (congrArg (rebuiltReduction t f ≫ ·) (structureHom_fSharpInverseImage f)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (rebuiltReduction_comp_hom t f)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg ((idIso f (thickenedBaseRing t f)).hom ≫ ·)
    (Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp _ _)

variable [IsClosedImmersion t] (hst : t.ker ^ 2 = ⊥)
include hst

/-- The kernel of the reduction of the thickened base has square zero. -/
theorem mul_eq_zero_of_rebuiltReduction (U : X.Opensᵒᵖ)
    (a b : (rebuilt f (thickenedBaseRing t f)).obj.obj U)
    (ha : (rebuiltReduction t f).hom.app U a = 0) (hb : (rebuiltReduction t f).hom.app U b = 0) :
    a * b = 0 := by
  have hinj : Function.Injective ((idIso f (thickenedBaseRing t f)).hom.hom.app U) :=
    fun x y h => (idIso_hom_app_apply f _ U x).symm.trans (h.trans (idIso_hom_app_apply f _ U y))
  rw [rebuiltReduction_app_apply] at ha hb
  refine hinj ((map_mul _ a b).trans ((congrArg₂ (· * ·) (idIso_hom_app_apply f _ U a)
    (idIso_hom_app_apply f _ U b)).trans (Eq.trans ?_ (map_zero _).symm)))
  exact mul_eq_zero_of_baseStructureMap_eq_zero f.toLRSHom.toShHom
    (t.isEmbedding.isInducing)
    (fun W j j' hj hj' => mul_eq_zero_of_comorphism t hst W j j' hj hj')
    U.unop a b ha hb

/-- The kernel of the reduction of the thickened base is annihilated by that kernel. -/
theorem smul_idealKernel_eq_zero (U : X.Opensᵒᵖ)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf (rebuilt f (thickenedBaseRing t f))).obj.obj U)
    (hb : b ∈ RingHom.ker ((rebuiltReductionRing t f).hom.app U).hom)
    (m : (idealKernel t f).val.obj U) : b • m = 0 :=
  Subtype.ext (mul_eq_zero_of_rebuiltReduction t f hst U b m.1 hb m.2)

/-- **The ideal of the thickened base, as a module over the reduced base.** -/
abbrev ideal :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (rebuilt f (reducedBaseRing f))) :=
  Stacks.SheafOfModules.ChangeOfRings.liftedSheaf (rebuiltReductionRing t f) (idealKernel t f)
    (smul_idealKernel_eq_zero t f hst)

/-- The inclusion of the ideal of the thickened base. -/
abbrev idealInclusion :
    (SheafOfModules.restrictScalars (rebuiltReductionRing t f)).obj (ideal t f hst) ⟶
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (rebuilt f (thickenedBaseRing t f))) :=
  (Stacks.SheafOfModules.ChangeOfRings.restrictScalarsLiftedSheafIso (rebuiltReductionRing t f)
    (idealKernel t f) (smul_idealKernel_eq_zero t f hst)).hom ≫ SheafOfModules.kerIota _

/-- On sections, `idealInclusion` is the inclusion of the kernel. -/
theorem idealInclusion_app (U : X.Opensᵒᵖ) (a : (ideal t f hst).val.obj U) :
    (idealInclusion t f hst).val.app U a = (show (idealKernel t f).val.obj U from a).1 :=
  rfl

/-- The module `f^*𝒞_{S/S'}` of the deformation problem. -/
abbrev conormalModule : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
      X.sheaf) :=
  pullbackConormalModule f t

/-- **The deformation problem of `f` over the thickening `S ⊂ S'`**, for a prescribed map `c` from
the ideal of the thickened base to `f^*𝒞_{S/S'}`. -/
def problem (c : ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f)) :
    Deformation.ToposThickening.RingedToposExtensionProblem (sourceTopos X) (reducedBase f) where
  f := structureHom f
  baseExtension := thickenedBaseRing t f
  baseReduction := Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f.toLRSHom.toShHom
    t.toLRSHom.toShHom
  baseLocallySurjective := isLocallySurjective_baseStructureMap' t f
  baseSquareZero U := by
    rw [pow_two]
    refine le_antisymm (Ideal.mul_le.mpr fun a ha b hb => ?_) bot_le
    exact mul_eq_zero_of_baseStructureMap_eq_zero f.toLRSHom.toShHom
      (t.isEmbedding.isInducing)
      (fun W j j' hj hj' => mul_eq_zero_of_comorphism t hst W j j' hj hj') U.unop a b ha hb
  I := ideal t f hst
  G := conormalModule t f
  idealInclusion := idealInclusion t f hst
  c := c
  idealZero U a := (show (idealKernel t f).val.obj U from a).2
  idealUniversal U a ha := ⟨⟨a, ha⟩, rfl, fun y hy => Subtype.ext hy⟩

end Problem



end Stacks.Thickenings.FlatDeformation
