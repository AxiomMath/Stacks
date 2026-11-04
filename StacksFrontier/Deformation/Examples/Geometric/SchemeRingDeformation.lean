module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecProduct
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.Rings

/-!
# Deformations of an affine scheme and of its coordinate ring

For a `k`-algebra `P` the deformation category of the scheme `Spec P` is equivalent, over the
category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field `k`, to the deformation
category of the algebra `P`. The equivalence sends a deformation `(A, Y)` of `Spec P` to the
`A`-algebra `Γ(Y, 𝒪_Y)`; it is well defined because a deformation of an affine scheme is a
thickening of it and is therefore affine.

## Main definitions

* `Deformation.Examples.SchemeRingDeformation.sectionsFunctor`: the global-sections functor
  from deformations of `Spec P` to deformations of `P`.
* `Deformation.Examples.SchemeRingDeformation.specFunctor`: the functor back, taking spectra.

## Main results

* `Deformation.Examples.SchemeRingDeformation.isAffine_scheme`: a deformation of an affine
  scheme is affine.
* `Deformation.Examples.SchemeRingDeformation.equivalenceOver`: the two functors form an
  equivalence over `𝒞_Λ`.

## Implementation notes

Affineness of a deformation is unconditional here. The special-fibre immersion of a deformation
is a thickening of `Spec P`, by `deformationSpecialMap_isClosedImmersion` and
`deformationSpecialMap_surjective`, and [Stacks Project, Tag 06AD] is available for thickenings
of arbitrary order as `Stacks.Thickenings.isAffine_of_isThickening`, proved from affineness of
the target of a finite surjective morphism with affine source. So `isAffine_scheme` and
everything built on it take no hypothesis.

Both functors preserve the Artinian base on the nose, so the two commutation squares with the
projections to `𝒞_Λ` hold by `rfl` and the equivalence is recorded as a
`StacksRepresentableCFG.EquivalenceOver`, whose unit and counit are 2-cells over `𝒞_Λ`.

## References

* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DYX](https://stacks.math.columbia.edu/tag/0DYX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples.SchemeRingDeformation

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The spectrum of an algebra as a scheme over the residue field -/

/-- The total space of `specOver k P` is the affine scheme `Spec P`. -/
instance isAffine_specOver_left (P : Type u) [CommRing P] [Algebra k P] :
    IsAffine (specOver k P).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of P)))

/-! ### The morphism to the residue field object -/

/-- Every morphism of `𝒞_Λ` into the residue-field object is the residue map. -/
theorem hom_apply_eq_residueMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) (a : A) : f.hom a = Deformation.Artin.residueMap A a :=
  (residueFieldBase_residueEquiv_residue Λ k (f.hom a)).symm.trans (f.residue_comm a)

/-- The morphism of `𝒞_Λ` from an object to the residue-field object. -/
def residueBase (A : ArtinianLocalAlgCat.{u, u, u} Λ k) : A ⟶ residueFieldBase Λ k :=
  (isTerminal_residueFieldBase (Λ := Λ) (k := k)).from A

/-- The residue-field object is terminal, so there is no other morphism into it. -/
theorem eq_residueBase {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) : f = residueBase A :=
  (isTerminal_residueFieldBase (Λ := Λ) (k := k)).hom_ext f _

/-- The underlying map of commutative rings of a morphism into the residue-field object is the
residue map of the source. -/
theorem ofHom_eq_residueMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) :
    CommRingCat.ofHom f.hom.toRingHom = CommRingCat.ofHom (Deformation.Artin.residueMap A) := by
  ext a
  exact hom_apply_eq_residueMap f a

/-- The underlying map of commutative rings of the structural morphism of a deformation of an
algebra is the residue map of its Artinian base. -/
theorem baseMap_eq_residueMap {X : FlatAlgebraCategory.{u, u} Λ k} {Q : Type u} [CommRing Q]
    [Algebra k Q] (f : X ⟶ residueFieldAlgebra (Λ := Λ) (k := k) Q) :
    FlatAlgebraCategory.baseMap f.base =
      CommRingCat.ofHom (Deformation.Artin.residueMap X.base) :=
  ofHom_eq_residueMap f.base

/-! ### Affineness of a deformation of an affine scheme -/

variable (P : Type u) [CommRing P] [Algebra k P]

/-- A deformation of an affine scheme is affine: its special-fibre immersion is a thickening of
`Spec P`, so [Stacks Project, Tag 06AD] applies. -/
@[sga "7 VI 4.1(b)"]
theorem isAffine_scheme (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    IsAffine Y.scheme :=
  Stacks.Thickenings.isAffine_of_isThickening (i := Y.specialMap)
    ⟨deformationSpecialMap_isClosedImmersion Y, deformationSpecialMap_surjective Y⟩

/-! ### Spectra and global sections turn pushouts into pullbacks and back -/

/-- Global sections send a cartesian square of affine schemes to a cocartesian square of
rings. -/
@[sga "3 V 4.1" "more general"]
theorem gammaIsPushout {T X Y S : Scheme.{u}} {fst : T ⟶ X} {snd : T ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback fst snd f g)
    [IsAffine T] [IsAffine X] [IsAffine Y] [IsAffine S] :
    IsPushout (Scheme.Γ.map g.op) (Scheme.Γ.map f.op)
      (Scheme.Γ.map snd.op) (Scheme.Γ.map fst.op) := by
  have : ∀ i, IsAffine ((span g.op f.op).obj i).unop := by
    intro i
    cases i with
    | none => exact ‹IsAffine S›
    | some j =>
      cases j with
      | left => exact ‹IsAffine Y›
      | right => exact ‹IsAffine X›
  have : PreservesColimit (span g.op f.op) Scheme.Γ := by infer_instance
  let hp : IsPushout g.op f.op snd.op fst.op := h.op
  exact IsPushout.of_isColimit_cocone (isColimitOfPreserves Scheme.Γ hp.isColimit)

/-- The spectrum sends a cocartesian square of rings to a cartesian square of schemes. -/
theorem specIsPullback {A B C D : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ D} {j : C ⟶ D} (h : IsPushout f g i j) :
    IsPullback (Spec.map i) (Spec.map j) (Spec.map f) (Spec.map g) := by
  have : PreservesLimit (cospan f.op g.op) Scheme.Spec := by infer_instance
  exact (h.flip.op).map Scheme.Spec

/-! ### The global-sections functor -/

/-- The structure map making the global sections of a deformation an algebra over its Artinian
base. -/
def sectionsStructureMap (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    CommRingCat.of Y.base ⟶ CommRingCat.of (Scheme.Γ.obj (Opposite.op Y.scheme)) :=
  (Scheme.ΓSpecIso (.of Y.base)).inv ≫ Y.toBase.appTop

/-- The global sections of a deformation of `Spec P`, as a flat algebra over the Artinian base
of the deformation. -/
def sectionsFlatAlgebra
    (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    FlatAlgebraCategory.{u, u} Λ k := by
  have : IsAffine Y.scheme := isAffine_scheme P Y
  have : Flat Y.toBase := Y.flat
  have hflat : (Y.toBase.appTop).hom.Flat := Scheme.Hom.flat_appTop Y.toBase
  have hstructure : (sectionsStructureMap P Y).hom.Flat :=
    RingHom.Flat.comp
      (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of Y.base)).inv))
      hflat
  letI : Algebra Y.base (Scheme.Γ.obj (Opposite.op Y.scheme)) :=
    (sectionsStructureMap P Y).hom.toAlgebra
  have hmodule : Module.Flat Y.base (Scheme.Γ.obj (Opposite.op Y.scheme)) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact hstructure
  exact
    { base := Y.base
      fiber := Scheme.Γ.obj (Opposite.op Y.scheme)
      algebra := inferInstance
      flat := hmodule }

/-- The structure map of the flat algebra of global sections is the one it was built from. -/
theorem structureMap_sectionsFlatAlgebra
    (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    FlatAlgebraCategory.structureMap (sectionsFlatAlgebra P Y) =
      sectionsStructureMap P Y := by
  ext a
  rfl

/-- The map from the global sections of a deformation of `Spec P` to `P`, induced by the
special-fibre immersion. -/
def sectionsSpecialRingMap (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    CommRingCat.of (Scheme.Γ.obj (Opposite.op Y.scheme)) ⟶ CommRingCat.of P :=
  Y.specialMap.appTop ≫ (Scheme.ΓSpecIso (.of P)).hom

/-- The special-fibre square of a deformation of `Spec P` becomes, on global sections, the
cocartesian square exhibiting `P` as the reduction of the global sections. -/
theorem sectionsPushout
    (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    IsPushout (sectionsStructureMap P Y)
      (CommRingCat.ofHom (residueBase Y.base).hom.toRingHom)
      (sectionsSpecialRingMap P Y)
      (FlatAlgebraCategory.structureMap (residueFieldAlgebra (Λ := Λ) (k := k) P)) := by
  have : IsAffine Y.scheme := isAffine_scheme P Y
  have h := (gammaIsPushout Y.specialCartesian).flip
  apply h.of_iso (Scheme.ΓSpecIso (.of Y.base)) (Iso.refl _)
    (Scheme.ΓSpecIso (.of k)) (Scheme.ΓSpecIso (.of P))
  · simp [sectionsStructureMap]
  · change Scheme.Γ.map (Opposite.op (residueSpecMap Y.base)) ≫ (Scheme.ΓSpecIso (.of k)).hom =
      (Scheme.ΓSpecIso (.of Y.base)).hom ≫
        CommRingCat.ofHom (residueBase Y.base).hom.toRingHom
    rw [ofHom_eq_residueMap, ← Scheme.ΓSpecIso_naturality]
    rfl
  · exact (Category.id_comp _).symm
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k P))

/-- The global sections of a deformation of `Spec P`, as a deformation of `P`. -/
def sectionsObj
    (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    ringDeformationCategory (Λ := Λ) (k := k) P :=
  Over.mk
    (show sectionsFlatAlgebra P Y ⟶ residueFieldAlgebra (Λ := Λ) (k := k) P from
      { base := residueBase Y.base
        map := sectionsSpecialRingMap P Y
        cartesian := by
          rw [structureMap_sectionsFlatAlgebra]
          exact sectionsPushout P Y })

/-- The map on global sections induced by a morphism of deformations of `Spec P`. -/
def sectionsMap
    {Y Z : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)} (f : Y ⟶ Z) :
    sectionsObj P Y ⟶ sectionsObj P Z := by
  have hY : IsAffine Y.scheme := isAffine_scheme P Y
  have hZ : IsAffine Z.scheme := isAffine_scheme P Z
  refine Over.homMk
    (show sectionsFlatAlgebra P Y ⟶ sectionsFlatAlgebra P Z from
      { base := f.base
        map := Scheme.Γ.map f.map.op
        cartesian := ?_ }) ?_
  · rw [structureMap_sectionsFlatAlgebra, structureMap_sectionsFlatAlgebra]
    refine (gammaIsPushout f.cartesian).flip.of_iso (Scheme.ΓSpecIso (.of Y.base))
      (Iso.refl _) (Scheme.ΓSpecIso (.of Z.base)) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans
        ((Scheme.ΓSpecIso (.of Y.base)).hom_inv_id_assoc _).symm
    · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.base.hom.toRingHom)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans
        ((Scheme.ΓSpecIso (.of Z.base)).hom_inv_id_assoc _).symm
  · refine FlatAlgebraCategory.Hom.ext ?_ ?_
    · exact (eq_residueBase (f.base ≫ residueBase Z.base)).trans rfl
    · change Scheme.Γ.map f.map.op ≫ sectionsSpecialRingMap P Z =
        sectionsSpecialRingMap P Y
      have hc : f.map.appTop ≫ Z.specialMap.appTop = Y.specialMap.appTop := by
        have h := congrArg Scheme.Hom.appTop f.special_compat
        rwa [Scheme.Hom.comp_appTop] at h
      change f.map.appTop ≫ Z.specialMap.appTop ≫ (Scheme.ΓSpecIso (.of P)).hom =
        Y.specialMap.appTop ≫ (Scheme.ΓSpecIso (.of P)).hom
      rw [← Category.assoc, hc]

/-- **Stacks 0DYX.** Global sections as a functor from deformations of `Spec P` to
deformations of `P`. -/
@[stacks 0DYX "the functor sending (A, Y) to the global sections of Y"]
def sectionsFunctor :
    SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P) ⥤
      ringDeformationCategory (Λ := Λ) (k := k) P where
  obj := sectionsObj P
  map := sectionsMap P
  map_id Y := by
    refine Over.OverMorphism.ext ?_
    refine FlatAlgebraCategory.Hom.ext rfl ?_
    change Scheme.Γ.map (𝟙 Y.scheme).op = 𝟙 _
    rw [op_id, Scheme.Γ.map_id]
  map_comp f g := by
    refine Over.OverMorphism.ext ?_
    refine FlatAlgebraCategory.Hom.ext rfl ?_
    change Scheme.Γ.map (g.map ≫ f.map).op = Scheme.Γ.map f.map.op ≫ Scheme.Γ.map g.map.op
    rw [op_comp, Scheme.Γ.map_comp]

/-! ### The functor back -/

/-- The spectrum of a deformation of `P`, as a deformation of `Spec P`. -/
def specObj (D : ringDeformationCategory (Λ := Λ) (k := k) P) :
    SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P) where
  base := D.left.base
  scheme := Spec (.of D.left.fiber)
  toBase := Spec.map (FlatAlgebraCategory.structureMap D.left)
  flat := by
    refine Flat.SpecMap_iff.mpr ?_
    change (algebraMap D.left.base D.left.fiber).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact D.left.flat
  specialMap := Spec.map D.hom.map
  specialCartesian := by
    have h := specIsPullback D.hom.cartesian
    rwa [baseMap_eq_residueMap D.hom] at h

/-- The map of spectra induced by a morphism of deformations of `P`. -/
def specMap {D E : ringDeformationCategory (Λ := Λ) (k := k) P} (f : D ⟶ E) :
    specObj P D ⟶ specObj P E where
  base := f.left.base
  map := Spec.map f.left.map
  cartesian := specIsPullback f.left.cartesian
  special_compat := by
    change Spec.map E.hom.map ≫ Spec.map f.left.map = Spec.map D.hom.map
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg (fun a : D.left ⟶ _ => a.map) f.w)

/-- Taking spectra as a functor from deformations of `P` to deformations of `Spec P`. -/
def specFunctor :
    ringDeformationCategory (Λ := Λ) (k := k) P ⥤
      SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P) where
  obj := specObj P
  map := specMap P
  map_id D := by
    refine SchemeDeformationCategory.Hom.ext rfl ?_
    change Spec.map (𝟙 (CommRingCat.of D.left.fiber)) = 𝟙 _
    rw [Spec.map_id]
  map_comp f g := by
    refine SchemeDeformationCategory.Hom.ext rfl ?_
    change Spec.map (f.left.map ≫ g.left.map) = Spec.map g.left.map ≫ Spec.map f.left.map
    rw [Spec.map_comp]

/-! ### The unit -/

/-- The structure morphism of the spectrum of the global sections of a deformation is the
structure morphism of the deformation, read through the canonical isomorphism. -/
theorem specMap_sectionsStructureMap
    (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) [IsAffine Y.scheme] :
    Spec.map (sectionsStructureMap P Y) = Y.scheme.isoSpec.inv ≫ Y.toBase := by
  have h₁ : Spec.map (sectionsStructureMap P Y) =
      Spec.map Y.toBase.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of Y.base)).inv :=
    Spec.map_comp _ _
  rw [h₁, ← Scheme.isoSpec_Spec_inv]
  exact Scheme.isoSpec_inv_naturality Y.toBase

/-- The special-fibre immersion of the spectrum of the global sections of a deformation is the
one of the deformation, read through the canonical isomorphism. -/
theorem specMap_sectionsSpecialRingMap
    (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    Spec.map (sectionsSpecialRingMap P Y) =
      (Spec (CommRingCat.of P)).isoSpec.hom ≫ Spec.map Y.specialMap.appTop := by
  have h₁ : Spec.map (sectionsSpecialRingMap P Y) =
      Spec.map (Scheme.ΓSpecIso (.of P)).hom ≫ Spec.map Y.specialMap.appTop :=
    Spec.map_comp _ _
  rw [h₁, Scheme.isoSpec_Spec_hom]

/-- Composing with the map of spectra induced by an identity of `𝒞_Λ` changes nothing. -/
theorem comp_baseSpecMap_id {A : ArtinianLocalAlgCat.{u, u, u} Λ k} {W : Scheme.{u}}
    (f : W ⟶ baseSpec A) : f ≫ baseSpecMap (𝟙 A) = f :=
  (congrArg (fun m => f ≫ m) (baseSpecMap_id A)).trans (Category.comp_id _)

/-- A deformation of `Spec P` is isomorphic to the spectrum of its global sections. -/
def unitIsoApp
    (Y : SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) :
    Y ≅ specObj P (sectionsObj P Y) := by
  have hY : IsAffine Y.scheme := isAffine_scheme P Y
  have hbase : baseSpecMap (𝟙 Y.base) = 𝟙 (baseSpec Y.base) := baseSpecMap_id Y.base
  have hbaseIso : IsIso (baseSpecMap (𝟙 Y.base)) := by rw [hbase]; infer_instance
  have htb : Spec.map (sectionsStructureMap P Y) = Y.scheme.isoSpec.inv ≫ Y.toBase :=
    specMap_sectionsStructureMap P Y
  have hcartHom : Y.scheme.isoSpec.inv ≫ Y.toBase =
      Spec.map (sectionsStructureMap P Y) ≫ baseSpecMap (𝟙 Y.base) :=
    htb.symm.trans (comp_baseSpecMap_id _).symm
  have hcartInv : Y.scheme.isoSpec.hom ≫ Spec.map (sectionsStructureMap P Y) =
      Y.toBase ≫ baseSpecMap (𝟙 Y.base) :=
    ((congrArg (fun m => Y.scheme.isoSpec.hom ≫ m) htb).trans
      (Y.scheme.isoSpec.hom_inv_id_assoc Y.toBase)).trans (comp_baseSpecMap_id Y.toBase).symm
  have hspecInv : Y.specialMap ≫ Y.scheme.isoSpec.hom = Spec.map (sectionsSpecialRingMap P Y) := by
    rw [specMap_sectionsSpecialRingMap]
    exact (Scheme.isoSpec_hom_naturality Y.specialMap).symm
  have hspecHom : Spec.map (sectionsSpecialRingMap P Y) ≫ Y.scheme.isoSpec.inv = Y.specialMap :=
    (congrArg (fun m => m ≫ Y.scheme.isoSpec.inv) hspecInv.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => Y.specialMap ≫ m) Y.scheme.isoSpec.hom_inv_id).trans
          (Category.comp_id _)))
  exact
    { hom :=
        { base := 𝟙 Y.base
          map := Y.scheme.isoSpec.inv
          cartesian := @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _
            Y.scheme.isoSpec.isIso_inv hbaseIso ⟨hcartHom⟩
          special_compat := hspecHom }
      inv :=
        { base := 𝟙 Y.base
          map := Y.scheme.isoSpec.hom
          cartesian := @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _
            Y.scheme.isoSpec.isIso_hom hbaseIso ⟨hcartInv⟩
          special_compat := hspecInv }
      hom_inv_id :=
        SchemeDeformationCategory.Hom.ext (Category.comp_id _) Y.scheme.isoSpec.hom_inv_id
      inv_hom_id :=
        SchemeDeformationCategory.Hom.ext (Category.comp_id _) Y.scheme.isoSpec.inv_hom_id }

/-- Every deformation of `Spec P` is the spectrum of its global sections, naturally. -/
def unitIso :
    𝟭 (SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P)) ≅
      sectionsFunctor P ⋙ specFunctor P :=
  NatIso.ofComponents (unitIsoApp P) (by
    intro Y Z f
    have hY : IsAffine Y.scheme := isAffine_scheme P Y
    have hZ : IsAffine Z.scheme := isAffine_scheme P Z
    exact SchemeDeformationCategory.Hom.ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (Scheme.isoSpec_inv_naturality f.map).symm)

/-! ### The counit -/

/-- A deformation of `P` is isomorphic to the global sections of its spectrum. -/
def counitIsoApp
    (D : ringDeformationCategory (Λ := Λ) (k := k) P) :
    (specFunctor P ⋙ sectionsFunctor P).obj D ≅ D := by
  have hbase : FlatAlgebraCategory.baseMap (𝟙 D.left.base) =
      𝟙 (CommRingCat.of D.left.base) := by
    simp [FlatAlgebraCategory.baseMap, ArtinianLocalAlgCat.id_hom, ← CommRingCat.ofHom_id]
  have hbaseIso : IsIso (FlatAlgebraCategory.baseMap (𝟙 D.left.base)) := by
    rw [hbase]; infer_instance
  have hsec : sectionsStructureMap P (specObj P D) ≫
      (Scheme.ΓSpecIso (.of D.left.fiber)).hom = FlatAlgebraCategory.structureMap D.left := by
    change (Scheme.ΓSpecIso (.of D.left.base)).inv ≫
      (Spec.map (FlatAlgebraCategory.structureMap D.left)).appTop ≫
        (Scheme.ΓSpecIso (.of D.left.fiber)).hom = _
    rw [Scheme.ΓSpecIso_naturality, ← Category.assoc,
      (Scheme.ΓSpecIso (.of D.left.base)).inv_hom_id, Category.id_comp]
  have hcartHom : sectionsStructureMap P (specObj P D) ≫
      (Scheme.ΓSpecIso (.of D.left.fiber)).hom =
        FlatAlgebraCategory.baseMap (𝟙 D.left.base) ≫
          FlatAlgebraCategory.structureMap D.left := by
    rw [hbase, Category.id_comp]; exact hsec
  have hsecInv : FlatAlgebraCategory.structureMap D.left ≫
      (Scheme.ΓSpecIso (.of D.left.fiber)).inv = sectionsStructureMap P (specObj P D) :=
    (congrArg (fun m => m ≫ (Scheme.ΓSpecIso (.of D.left.fiber)).inv) hsec.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => sectionsStructureMap P (specObj P D) ≫ m)
          (Scheme.ΓSpecIso (.of D.left.fiber)).hom_inv_id).trans (Category.comp_id _)))
  have hcartInv : FlatAlgebraCategory.structureMap D.left ≫
      (Scheme.ΓSpecIso (.of D.left.fiber)).inv =
        FlatAlgebraCategory.baseMap (𝟙 D.left.base) ≫ sectionsStructureMap P (specObj P D) :=
    hsecInv.trans
      (((congrArg (fun m => m ≫ sectionsStructureMap P (specObj P D)) hbase).trans
        (Category.id_comp _)).symm)
  have hmapHom : (Scheme.ΓSpecIso (.of D.left.fiber)).hom ≫ D.hom.map =
      sectionsSpecialRingMap P (specObj P D) :=
    (Scheme.ΓSpecIso_naturality D.hom.map).symm
  have hmapInv : (Scheme.ΓSpecIso (.of D.left.fiber)).inv ≫
      sectionsSpecialRingMap P (specObj P D) = D.hom.map :=
    (congrArg (fun m => (Scheme.ΓSpecIso (.of D.left.fiber)).inv ≫ m) hmapHom.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ D.hom.map)
          (Scheme.ΓSpecIso (.of D.left.fiber)).inv_hom_id).trans (Category.id_comp _)))
  exact
    { hom := Over.homMk
        (show sectionsFlatAlgebra P (specObj P D) ⟶ D.left from
          { base := 𝟙 D.left.base
            map := (Scheme.ΓSpecIso (.of D.left.fiber)).hom
            cartesian := @IsPushout.of_vert_isIso _ _ _ _ _ _ _ _ _ _ hbaseIso
              (Scheme.ΓSpecIso (.of D.left.fiber)).isIso_hom ⟨hcartHom⟩ })
        (FlatAlgebraCategory.Hom.ext
          ((Category.id_comp _).trans (eq_residueBase D.hom.base)) hmapHom)
      inv := Over.homMk
        (show D.left ⟶ sectionsFlatAlgebra P (specObj P D) from
          { base := 𝟙 D.left.base
            map := (Scheme.ΓSpecIso (.of D.left.fiber)).inv
            cartesian := @IsPushout.of_vert_isIso _ _ _ _ _ _ _ _ _ _ hbaseIso
              (Scheme.ΓSpecIso (.of D.left.fiber)).isIso_inv ⟨hcartInv⟩ })
        (FlatAlgebraCategory.Hom.ext
          ((Category.id_comp _).trans (eq_residueBase D.hom.base).symm) hmapInv)
      hom_inv_id := Over.OverMorphism.ext (FlatAlgebraCategory.Hom.ext (Category.comp_id _)
        (Scheme.ΓSpecIso (.of D.left.fiber)).hom_inv_id)
      inv_hom_id := Over.OverMorphism.ext (FlatAlgebraCategory.Hom.ext (Category.comp_id _)
        (Scheme.ΓSpecIso (.of D.left.fiber)).inv_hom_id) }

/-- Every deformation of `P` is the global sections of its spectrum, naturally. -/
def counitIso :
    specFunctor P ⋙ sectionsFunctor P ≅
      𝟭 (ringDeformationCategory (Λ := Λ) (k := k) P) :=
  NatIso.ofComponents (counitIsoApp P) (by
    intro D E f
    exact Over.OverMorphism.ext (FlatAlgebraCategory.Hom.ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (Scheme.ΓSpecIso_naturality f.left.map)))

/-! ### The equivalence -/

/-- **Stacks 0DYX.** For a `k`-algebra `P`, global sections are an equivalence from the
deformation category of the affine scheme `Spec P` to the deformation category of `P`, over the
category of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 0DYX "the equivalence Def_(Spec P) = Def_P; 06AD is isAffine_of_isThickening",
  sga "7 VI 4.1(b)"]
def equivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (specOver k P))
      (Over.forget (residueFieldAlgebra (Λ := Λ) (k := k) P) ⋙
        FlatAlgebraCategory.projection (Λ := Λ) (k := k)) where
  hom := ⟨sectionsFunctor P, rfl⟩
  inv := ⟨specFunctor P, rfl⟩
  unitIso := unitIso P
  counitIso := counitIso P
  unit_over := rfl
  counit_over := rfl

/-- **Stacks 0DYX.** The underlying equivalence of categories. -/
def equivalence :
    SchemeDeformationCategory (Λ := Λ) (k := k) (specOver k P) ≌
      ringDeformationCategory (Λ := Λ) (k := k) P :=
  (equivalenceOver P).toEquivalence

end Deformation.Examples.SchemeRingDeformation

end
