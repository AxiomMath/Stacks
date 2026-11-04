module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsSchemes
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.SheafGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion
public import StacksFrontier.Deformation.Examples.Spaces
public import StacksFrontier.Deformation.Examples.Geometric.SpacesRimSchlessinger
public import StacksFrontier.Deformation.Examples.Geometric.SpacesSpecialFibreThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.ThickeningProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NoetherianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange

/-!
# Deformations in `Spaces'_{fp, flat, proper}` are deformations of an algebraic space

Let `x₀ = (X ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over the spectrum of a
field `k`, the stack being formed over the big fppf site of `Spec ℤ`. This file compares the
predeformation category `𝓕_{𝒳,k,x₀}` over `𝒞_ℤ` (Stacks 07T2) with the deformation category
`𝓓_X` of the algebraic space `X` over `k` (Stacks 0E3Z): a deformation of `x₀` over `A` is a
finitely presented, flat and proper algebraic space over `Spec A` with a cartesian arrow from
`X`, and forgetting finite presentation and properness gives a deformation of `X`.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceDeformation.toSpaceDeformationFunctor`: the functor
  `𝓕_{𝒳,k,x₀} ⥤ 𝓓_X`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
* [Stacks Project, Tag 07T2](https://stacks.math.columbia.edu/tag/07T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Examples

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The stack `Spaces'_{fp, flat, proper}` over the big fppf site of `Spec ℤ`, read in schemes over
`Spec ℤ`: the functor along which its predeformation categories are formed. -/
abbrev projection : CartesianProperFlatSpaces B integerBase hZ ⥤ Over integerBase :=
  cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion

variable {B hZ} {k : Type u} [Field k] [Algebra (ULift.{u} ℤ) k]
  (x₀ : CartesianProperFlatSpaces B integerBase hZ)
  (hx₀ : (projection B hZ).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k)) ≫ 𝟙 integerBase))

include hx₀ in
/-- The spectrum of the residue field lies in the site. -/
theorem contains_spec_residueField : B.Contains (Spec (.of k)) := by
  have h : ((projection B hZ).obj x₀).left = Spec (.of k) :=
    congrArg Over.left hx₀
  exact h ▸ ((cartesianProperFlatProjection B integerBase hZ).obj x₀).left.property

include hx₀ in
/-- The spectra of the objects of `𝒞_ℤ` lie in the site. -/
theorem contains_spec (A : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k) :
    B.Contains (Spec (.of A)) :=
  contains_spec_of_artinianLocalAlgCat A (contains_spec_residueField x₀ hx₀)

/-- The image in schemes over `Spec ℤ` of the spectrum of an object of `𝒞_ℤ`. -/
theorem post_spaceBaseOver (A : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k) :
    (Over.post B.inclusion).obj (spaceBaseOver B hZ (contains_spec x₀ hx₀) A) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) ≫ 𝟙 integerBase) := by
  rw [Category.comp_id]
  show Over.mk (B.inclusion.map (B.inclusion.preimage _)) = _
  rw [Functor.map_preimage]

/-- The objects of `𝓕_{𝒳,k,x₀}`. -/
abbrev Obj := Deformation.Artin.DeformationObject (𝟙 integerBase) (projection B hZ) x₀ hx₀

/-- The morphisms of `𝓕_{𝒳,k,x₀}`. -/
abbrev Hom (a b : Obj x₀ hx₀) :=
  Deformation.Artin.DeformationMorphism (𝟙 integerBase) (projection B hZ) x₀ hx₀ a b

/-- An object of `𝒳` lying over the spectrum of an object `A` of `𝒞_ℤ`, read in schemes over
`Spec ℤ`, lies over the spectrum of `A` as an object of the site. -/
theorem base_eq_spaceBaseOver {y : CartesianProperFlatSpaces B integerBase hZ}
    {A : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k}
    (hy : (projection B hZ).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) ≫ 𝟙 integerBase)) :
    (cartesianProperFlatProjection B integerBase hZ).obj y =
      spaceBaseOver B hZ (contains_spec x₀ hx₀) A :=
  BigFppfOver.obj_injective_post_inclusion B integerBase hZ
    (hy.trans (post_spaceBaseOver x₀ hx₀ A).symm)

/-- The base of `x₀` is the spectrum of the residue field. -/
theorem base_eq_residueFieldBase :
    (cartesianProperFlatProjection B integerBase hZ).obj x₀ =
      spaceBaseOver B hZ (contains_spec x₀ hx₀) (residueFieldBase (ULift.{u} ℤ) k) :=
  base_eq_spaceBaseOver x₀ hx₀ hx₀

/-- A morphism of `𝒳` lying over the spectrum of a morphism `φ` of `𝒞_ℤ`, read in schemes over
`Spec ℤ`, is the spectrum of `φ` as a morphism of the site. -/
theorem map_eq_spaceBaseOverMap {y y' : CartesianProperFlatSpaces B integerBase hZ}
    {A A' : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k} (φ : A ⟶ A') (f : y' ⟶ y)
    (hy : (projection B hZ).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) ≫ 𝟙 integerBase))
    (hy' : (projection B hZ).obj y' =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A')) ≫ 𝟙 integerBase))
    (hf : eqToHom (congrArg Over.left hy').symm ≫ ((projection B hZ).map f).left ≫
        eqToHom (congrArg Over.left hy) = Spec.map (CommRingCat.ofHom φ.hom.toRingHom)) :
    eqToHom (base_eq_spaceBaseOver x₀ hx₀ hy').symm ≫
        (cartesianProperFlatProjection B integerBase hZ).map f ≫
          eqToHom (base_eq_spaceBaseOver x₀ hx₀ hy) =
      spaceBaseOverMap B hZ (contains_spec x₀ hx₀) φ := by
  apply BigFppfOver.map_injective_post_inclusion B integerBase hZ
  apply Over.OverMorphism.ext
  simp only [Functor.map_comp, eqToHom_map, Over.comp_left, Over.eqToHom_left]
  refine Eq.trans ?_ (hf.trans ?_)
  · rfl
  · simp only [Over.post_map, Over.homMk_left, spaceBaseOverMap, BigFppfSite.homOfContains,
      Functor.map_preimage]

/-- A morphism of `𝒞_ℤ` to the residue field is the residue map. -/
theorem hom_toRingHom_eq_residueMap {A : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k}
    (φ : A ⟶ residueFieldBase (ULift.{u} ℤ) k) :
    φ.hom.toRingHom = Deformation.Artin.residueMap A := by
  rw [← Deformation.Artin.residueMap_comp φ]
  ext a
  exact (residueFieldBase_residueEquiv_residue (ULift.{u} ℤ) k _).symm

/-! ### The algebraic space `X` -/

/-- The algebraic space `X` underlying `x₀`. -/
abbrev space : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u := x₀.obj.obj.left.obj

/-- The structure morphism `X ⟶ Spec k`. -/
abbrev toResidueField :
    space x₀ ⟶ yoneda.obj (spaceBaseOver B hZ (contains_spec x₀ hx₀)
      (residueFieldBase (ULift.{u} ℤ) k)) :=
  x₀.obj.obj.hom ≫ yoneda.map (eqToHom (base_eq_residueFieldBase x₀ hx₀))

/-- The deformation category `𝓓_X` of the algebraic space `X` over `k` (Stacks 0E3Z), over
`𝒞_ℤ`. -/
abbrev spaceProjection :=
  spaceDeformationProjection B hZ (contains_spec x₀ hx₀) (space x₀) x₀.obj.obj.left.property
    (toResidueField x₀ hx₀)

/-! ### Transport along identifications of bases -/

/-- Composing with the identification of two equal objects of the site preserves flatness. -/
theorem isFlat_comp_yoneda_eqToHom {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {U U' : BigFppfOver B integerBase hZ} (f : X ⟶ yoneda.obj U) (h : U = U')
    (hf : Space.IsFlat B integerBase hZ f) :
    Space.IsFlat B integerBase hZ (f ≫ yoneda.map (eqToHom h)) := by
  subst h
  simpa using hf

/-- Transporting a cartesian square of algebraic spaces over two objects of the site along
identifications of those objects. -/
theorem isPullback_comp_yoneda_eqToHom {X X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {U U' V V' : BigFppfOver B integerBase hZ} (top : X ⟶ X') (l : X ⟶ yoneda.obj U)
    (r : X' ⟶ yoneda.obj V) (b : U ⟶ V) (hU : U = U') (hV : V = V')
    (h : IsPullback l top (yoneda.map b) r) (b' : U' ⟶ V')
    (hb : eqToHom hU.symm ≫ b ≫ eqToHom hV = b') :
    IsPullback top (l ≫ yoneda.map (eqToHom hU)) (r ≫ yoneda.map (eqToHom hV)) (yoneda.map b') := by
  subst hU hV hb
  simpa using h.flip

/-- The converse transport. -/
theorem isPullback_of_comp_yoneda_eqToHom {X X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {U U' V V' : BigFppfOver B integerBase hZ} (top : X ⟶ X') (l : X ⟶ yoneda.obj U)
    (r : X' ⟶ yoneda.obj V) (b : U ⟶ V) (hU : U = U') (hV : V = V') (b' : U' ⟶ V')
    (hb : eqToHom hU.symm ≫ b ≫ eqToHom hV = b')
    (h : IsPullback top (l ≫ yoneda.map (eqToHom hU)) (r ≫ yoneda.map (eqToHom hV))
      (yoneda.map b')) :
    IsPullback l top (yoneda.map b) r := by
  subst hU hV hb
  simpa using h.flip

/-! ### The functor on objects -/

/-- The flat family of algebraic spaces underlying a deformation of `x₀`. -/
def family (a : Obj x₀ hx₀) : FlatAlgebraicSpaceFamily B hZ (contains_spec x₀ hx₀) where
  base := a.algebra
  space := a.point.obj.obj.left.obj
  algebraic := a.point.obj.obj.left.property
  toBase := a.point.obj.obj.hom ≫ yoneda.map (eqToHom (base_eq_spaceBaseOver x₀ hx₀ a.base))
  flat := isFlat_comp_yoneda_eqToHom _ _ a.point.obj.property.2.1

/-- The arrow of a deformation, as a morphism of flat families to the special fibre `(k, X)`. -/
def familyToSpecialFiber (a : Obj x₀ hx₀) :
    family x₀ hx₀ a ⟶ spaceSpecialFiber B hZ (contains_spec x₀ hx₀) (space x₀)
      x₀.obj.obj.left.property (toResidueField x₀ hx₀) where
  base := isTerminal_residueFieldBase.from a.algebra
  map := a.arrow.hom.hom.left.hom
  cartesian := by
    have hsq := isPullback_hom_of_isStronglyCartesian B integerBase hZ a.arrow.hom.hom
      a.arrow.property
    refine isPullback_comp_yoneda_eqToHom _ _ _ _ _ _ hsq _ ?_
    refine map_eq_spaceBaseOverMap x₀ hx₀ _ a.arrow a.base hx₀ ?_
    rw [hom_toRingHom_eq_residueMap]
    exact a.arrow_base

/-- The deformation of `X` attached to a deformation of `x₀`. -/
def toSpaceDeformation (a : Obj x₀ hx₀) :
    Over (spaceSpecialFiber B hZ (contains_spec x₀ hx₀) (space x₀) x₀.obj.obj.left.property
      (toResidueField x₀ hx₀)) :=
  Over.mk (familyToSpecialFiber x₀ hx₀ a)

/-- The morphism of flat families underlying a morphism of deformations of `x₀`. -/
def familyHom {a b : Obj x₀ hx₀} (m : Hom x₀ hx₀ a b) : family x₀ hx₀ a ⟶ family x₀ hx₀ b where
  base := m.ringHom
  map := m.arrow.hom.hom.left.hom
  cartesian :=
    isPullback_comp_yoneda_eqToHom _ _ _ _ _ _
      (isPullback_hom_of_isStronglyCartesian B integerBase hZ m.arrow.hom.hom m.arrow.property) _
      (map_eq_spaceBaseOverMap x₀ hx₀ m.ringHom m.arrow a.base b.base m.arrow_base)

/-- The morphism of deformations of `X` attached to a morphism of deformations of `x₀`. -/
def toSpaceDeformationHom {a b : Obj x₀ hx₀} (m : Hom x₀ hx₀ a b) :
    toSpaceDeformation x₀ hx₀ a ⟶ toSpaceDeformation x₀ hx₀ b :=
  Over.homMk (familyHom x₀ hx₀ m) (FlatAlgebraicSpaceFamily.Hom.ext
    (isTerminal_residueFieldBase.hom_ext _ _) (congrArg (fun f => f.hom.hom.left.hom) m.triangle))

/-- The predeformation category `𝓕_{𝒳,k,x₀}` over `𝒞_ℤ`. -/
abbrev predeformation :=
  Deformation.Artin.predeformationCategory (𝟙 integerBase) (projection B hZ) x₀ hx₀

/-- **Deformations of `x₀` are deformations of the algebraic space `X`.** The functor from
`𝓕_{𝒳,k,x₀}` to the deformation category `𝓓_X` of Stacks 0E3Z, forgetting finite presentation and
properness. -/
def toSpaceDeformationFunctor :
    letI := (predeformation x₀ hx₀).category
    (predeformation x₀ hx₀).carrier ⥤
      Over (spaceSpecialFiber B hZ (contains_spec x₀ hx₀) (space x₀) x₀.obj.obj.left.property
        (toResidueField x₀ hx₀)) :=
  letI := (predeformation x₀ hx₀).category
  { obj := fun a => toSpaceDeformation x₀ hx₀ a
    map := fun {a b} m => toSpaceDeformationHom x₀ hx₀ m
    map_id := fun a => by
      apply Over.OverMorphism.ext
      apply FlatAlgebraicSpaceFamily.Hom.ext <;> rfl
    map_comp := fun {a b c} f g => by
      apply Over.OverMorphism.ext
      apply FlatAlgebraicSpaceFamily.Hom.ext <;> rfl }

/-- The functor `𝓕_{𝒳,k,x₀} ⥤ 𝓓_X` commutes with the projections to `𝒞_ℤ`. -/
theorem toSpaceDeformationFunctor_comp_projection :
    letI := (predeformation x₀ hx₀).category
    toSpaceDeformationFunctor x₀ hx₀ ⋙ spaceProjection x₀ hx₀ =
      (predeformation x₀ hx₀).projection :=
  rfl

/-! ### Full faithfulness -/

/-- Solving an identity of the form `eqToHom h₁.symm ≫ r ≫ eqToHom h₂ = s` for `r`. -/
theorem eq_eqToHom_comp_of_eqToHom_comp {U U' V V' : BigFppfOver B integerBase hZ} {r : U ⟶ V}
    {s : U' ⟶ V'} (h₁ : U = U') (h₂ : V = V') (h : eqToHom h₁.symm ≫ r ≫ eqToHom h₂ = s) :
    r = eqToHom h₁ ≫ s ≫ eqToHom h₂.symm := by
  subst h
  simp

/-- The base morphism of a morphism of deformations of `x₀` is the spectrum of its arrow of
`𝒞_ℤ`. -/
theorem hom_arrow_right_eq {a b : Obj x₀ hx₀} (m : Hom x₀ hx₀ a b) :
    (cartesianProperFlatProjection B integerBase hZ).map m.arrow =
      eqToHom (base_eq_spaceBaseOver x₀ hx₀ b.base) ≫
      spaceBaseOverMap B hZ (contains_spec x₀ hx₀) m.ringHom ≫
        eqToHom (base_eq_spaceBaseOver x₀ hx₀ a.base).symm :=
  eq_eqToHom_comp_of_eqToHom_comp _ _
    (map_eq_spaceBaseOverMap x₀ hx₀ m.ringHom m.arrow a.base b.base m.arrow_base)

/-- The base morphism of the arrow of a deformation of `x₀` is the spectrum of the residue map. -/
theorem arrow_right_eq (a : Obj x₀ hx₀) :
    (cartesianProperFlatProjection B integerBase hZ).map a.arrow =
      eqToHom (base_eq_residueFieldBase x₀ hx₀) ≫
      spaceBaseOverMap B hZ (contains_spec x₀ hx₀)
        (isTerminal_residueFieldBase.from a.algebra) ≫
        eqToHom (base_eq_spaceBaseOver x₀ hx₀ a.base).symm := by
  refine eq_eqToHom_comp_of_eqToHom_comp _ _
    (map_eq_spaceBaseOverMap x₀ hx₀ _ a.arrow a.base hx₀ ?_)
  rw [hom_toRingHom_eq_residueMap]
  exact a.arrow_base

/-- Two morphisms of deformations of `x₀` with the same image in `𝓓_X` are equal. -/
theorem toSpaceDeformationHom_injective {a b : Obj x₀ hx₀} {m m' : Hom x₀ hx₀ a b}
    (h : toSpaceDeformationHom x₀ hx₀ m = toSpaceDeformationHom x₀ hx₀ m') : m = m' := by
  have hr : m.ringHom = m'.ringHom := congrArg (fun g => g.left.base) h
  refine Deformation.Artin.DeformationMorphism.ext_of_components _ _ _ _ hr ?_
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · exact ObjectProperty.hom_ext _ (congrArg (fun g => g.left.map) h)
  · show (cartesianProperFlatProjection B integerBase hZ).map m.arrow =
      (cartesianProperFlatProjection B integerBase hZ).map m'.arrow
    rw [hom_arrow_right_eq, hom_arrow_right_eq, hr]

section Preimage

/-- Cancelling the identifications around a conjugated morphism. -/
theorem eqToHom_conj_cancel {U U' V V' : BigFppfOver B integerBase hZ} (h₁ : U = U')
    (h₂ : V = V') (r : U' ⟶ V') :
    eqToHom h₁.symm ≫ (eqToHom h₁ ≫ r ≫ eqToHom h₂.symm) ≫ eqToHom h₂ = r := by
  subst h₁ h₂
  simp

/-- The commutativity of a square over transported bases. -/
theorem comp_eq_comp_of_comp_yoneda_eqToHom {X X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {U U' V V' : BigFppfOver B integerBase hZ} (h₁ : U = U') (h₂ : V = V') (g : X ⟶ X')
    (ra : X' ⟶ yoneda.obj U) (rb : X ⟶ yoneda.obj V) (r : V' ⟶ U')
    (hw : g ≫ ra ≫ yoneda.map (eqToHom h₁) = (rb ≫ yoneda.map (eqToHom h₂)) ≫ yoneda.map r) :
    g ≫ ra = rb ≫ yoneda.map (eqToHom h₂ ≫ r ≫ eqToHom h₁.symm) := by
  subst h₁ h₂
  simpa using hw

/-- A morphism of the site between spectra of objects of `𝒞_ℤ` which is the spectrum of a
morphism `φ` of `𝒞_ℤ` is `Spec φ` in schemes. -/
theorem spec_eq_of_eq_spaceBaseOverMap {U U' : BigFppfOver B integerBase hZ} (r : U' ⟶ U)
    {A A' : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k} (φ : A ⟶ A')
    (hU : U = spaceBaseOver B hZ (contains_spec x₀ hx₀) A)
    (hU' : U' = spaceBaseOver B hZ (contains_spec x₀ hx₀) A')
    (hr : r = eqToHom hU' ≫ spaceBaseOverMap B hZ (contains_spec x₀ hx₀) φ ≫ eqToHom hU.symm)
    (h₁ : Spec (.of A') = B.inclusion.obj U'.left) (h₂ : B.inclusion.obj U.left = Spec (.of A)) :
    eqToHom h₁ ≫ B.inclusion.map r.left ≫ eqToHom h₂ =
      Spec.map (CommRingCat.ofHom φ.hom.toRingHom) := by
  subst hU hU' hr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [spaceBaseOverMap, Over.homMk_left, BigFppfSite.homOfContains, Functor.map_preimage]

/-- A morphism of `𝒳` whose base is the spectrum of a morphism `φ` of `𝒞_ℤ`, as a morphism of the
site, lies over `Spec φ` in schemes over `Spec ℤ`. -/
theorem spec_eq_of_map_eq {y y' : CartesianProperFlatSpaces B integerBase hZ}
    {A A' : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k} (φ : A ⟶ A') (f : y' ⟶ y)
    (hy : (projection B hZ).obj y =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A)) ≫ 𝟙 integerBase))
    (hy' : (projection B hZ).obj y' =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A')) ≫ 𝟙 integerBase))
    (h : (cartesianProperFlatProjection B integerBase hZ).map f =
      eqToHom (base_eq_spaceBaseOver x₀ hx₀ hy') ≫
        spaceBaseOverMap B hZ (contains_spec x₀ hx₀) φ ≫
          eqToHom (base_eq_spaceBaseOver x₀ hx₀ hy).symm) :
    eqToHom (congrArg Over.left hy').symm ≫ ((projection B hZ).map f).left ≫
        eqToHom (congrArg Over.left hy) = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) :=
  spec_eq_of_eq_spaceBaseOverMap x₀ hx₀ _ φ (base_eq_spaceBaseOver x₀ hx₀ hy)
    (base_eq_spaceBaseOver x₀ hx₀ hy') h _ _

variable {a b : Obj x₀ hx₀} (g : toSpaceDeformation x₀ hx₀ a ⟶ toSpaceDeformation x₀ hx₀ b)

/-- The morphism of `𝒞_ℤ` of a morphism of deformations of `X`. -/
abbrev preimageBase : a.algebra ⟶ b.algebra := g.left.base

/-- The base morphism of the preimage of a morphism of deformations of `X`. -/
abbrev preimageRight :
    (cartesianProperFlatProjection B integerBase hZ).obj b.point ⟶
      (cartesianProperFlatProjection B integerBase hZ).obj a.point :=
  eqToHom (base_eq_spaceBaseOver x₀ hx₀ b.base) ≫
    spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (preimageBase x₀ hx₀ g) ≫
      eqToHom (base_eq_spaceBaseOver x₀ hx₀ a.base).symm

/-- The reversed arrow of `𝒳` of the preimage of a morphism of deformations of `X`. -/
def preimageArrow : b.point ⟶ a.point where
  hom := ObjectProperty.homMk
    { left := ObjectProperty.homMk g.left.map
      right := preimageRight x₀ hx₀ g
      w := comp_eq_comp_of_comp_yoneda_eqToHom _ _ _ _ _ _ g.left.cartesian.w }
  property := by
    refine SpacesDescent.isStronglyCartesian_of_isPullback
      (U := ((isProperFlatSpace B integerBase hZ).ι.obj a.point.obj).right)
      (V := ((isProperFlatSpace B integerBase hZ).ι.obj b.point.obj).right)
      (preimageRight x₀ hx₀ g) _ rfl rfl
      (by simp only [eqToHom_refl, Category.id_comp]; exact (Category.comp_id _).symm)
      (by simp only [eqToHom_refl]; exact Category.comp_id _)
      (by simp only [eqToHom_refl]; exact Category.comp_id _) ?_
    exact (isPullback_of_comp_yoneda_eqToHom _ _ _ _ _ _ _
      (eqToHom_conj_cancel _ _ _) g.left.cartesian).flip

/-- The preimage of a morphism of deformations of `X`. -/
def preimageHom : Hom x₀ hx₀ a b where
  ringHom := preimageBase x₀ hx₀ g
  arrow := preimageArrow x₀ hx₀ g
  triangle := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact ObjectProperty.hom_ext _ (congrArg (fun f => f.map) (Over.w g))
    · change (cartesianProperFlatProjection B integerBase hZ).map b.arrow ≫
        preimageRight x₀ hx₀ g = (cartesianProperFlatProjection B integerBase hZ).map a.arrow
      rw [arrow_right_eq, arrow_right_eq]
      simp only [preimageRight, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [← Category.assoc (spaceBaseOverMap B hZ _ _), ← spaceBaseOverMap_comp]
      congr 3
      exact isTerminal_residueFieldBase.hom_ext _ _
  arrow_base := spec_eq_of_map_eq x₀ hx₀ _ _ a.base b.base rfl

/-- The image in `𝓓_X` of `preimageHom x₀ hx₀ g` is `g`. -/
theorem toSpaceDeformationHom_preimageHom :
    toSpaceDeformationHom x₀ hx₀ (preimageHom x₀ hx₀ g) = g := by
  apply Over.OverMorphism.ext
  apply FlatAlgebraicSpaceFamily.Hom.ext <;> rfl

end Preimage

/-- The functor `𝓕_{𝒳,k,x₀} ⥤ 𝓓_X` is faithful. -/
theorem toSpaceDeformationFunctor_faithful :
    letI := (predeformation x₀ hx₀).category
    (toSpaceDeformationFunctor x₀ hx₀).Faithful :=
  let := (predeformation x₀ hx₀).category
  ⟨fun h => toSpaceDeformationHom_injective x₀ hx₀ h⟩

/-- The functor `𝓕_{𝒳,k,x₀} ⥤ 𝓓_X` is full. -/
theorem toSpaceDeformationFunctor_full :
    letI := (predeformation x₀ hx₀).category
    (toSpaceDeformationFunctor x₀ hx₀).Full :=
  let := (predeformation x₀ hx₀).category
  ⟨fun g => ⟨preimageHom x₀ hx₀ g, toSpaceDeformationHom_preimageHom x₀ hx₀ g⟩⟩

/-! ### Essential surjectivity -/

section EssSurj

open Space in
/-- A property of morphisms of algebraic spaces stable under base change passes to the left side
of a cartesian square of presheaves between algebraic spaces. -/
theorem prop_of_isPullback {Q : MorphismProperty (AlgebraicSpaces B integerBase hZ)}
    [Q.IsStableUnderBaseChange] {A₁ A₂ A₃ A₄ : AlgebraicSpaces B integerBase hZ}
    (f' : A₁ ⟶ A₂) (g' : A₁ ⟶ A₃) (g : A₂ ⟶ A₄) (f : A₃ ⟶ A₄)
    (h : IsPullback f'.hom g'.hom g.hom f.hom) (hg : Q g) : Q g' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_map_of_faithful (ObjectProperty.ι _) h) hg

/-- Composing with the identification of two equal objects of the site preserves finite
presentation and properness. -/
theorem prop_comp_yoneda_eqToHom {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {U U' : BigFppfOver B integerBase hZ} (f : X ⟶ yoneda.obj U) (h : U = U')
    (hf : Space.IsFinitePresentation B integerBase hZ f ∧ Space.IsProper B integerBase hZ f) :
    Space.IsFinitePresentation B integerBase hZ (f ≫ yoneda.map (eqToHom h)) ∧
      Space.IsProper B integerBase hZ (f ≫ yoneda.map (eqToHom h)) := by
  subst h
  simpa using hf

variable (P : Over (spaceSpecialFiber B hZ (contains_spec x₀ hx₀) (space x₀)
  x₀.obj.obj.left.property (toResidueField x₀ hx₀)))

/-- The morphism `A ⟶ k` of `𝒞_ℤ` of a deformation of `X` over `A`. -/
abbrev specialBase : P.left.base ⟶ residueFieldBase (ULift.{u} ℤ) k := P.hom.base

/-- The closed subspace `Spec k ⊂ Spec A` of the base of a deformation of `X` over `A`. -/
abbrev baseSpecial :
    Subfunctor (yoneda.obj (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base)) :=
  Subfunctor.range
    (yoneda.map (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P)))

/-- The morphism `Spec k ⟶ Spec A` of a deformation of `X` over `A` is a thickening. -/
theorem isThickeningHom_baseSpecial :
    Space.IsThickeningHom B integerBase hZ
      (schemeSpaceMap (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P))) :=
  isThickeningHom_schemeSpaceMap_spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P)
    (surjective_of_hom_residueFieldBase (specialBase x₀ hx₀ P))

/-- `Spec k ⊂ Spec A` is a thickening of algebraic spaces. -/
theorem isThickening_baseSpecial :
    Space.IsThickening B integerBase hZ
      (schemeSpace (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base))
      (baseSpecial x₀ hx₀ P) :=
  (isThickeningHom_baseSpecial x₀ hx₀ P).2

/-- `Spec k ⊂ Spec A` is a thickening of finite order. -/
theorem isFiniteOrderThickening_baseSpecial :
    Space.IsFiniteOrderThickening B integerBase hZ
      (schemeSpace (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base))
      (baseSpecial x₀ hx₀ P) := by
  have : IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj
      (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base)) := by
    show IsNoetherian (Spec (.of P.left.base))
    infer_instance
  refine Space.isFiniteOrderThickening_of_atlas B integerBase hZ (isThickening_baseSpecial x₀ hx₀ P)
    (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base) (yoneda.map (𝟙 _)) ?_ ?_
  · exact (Space.presheaf_yoneda_map_iff B integerBase hZ
      (P := @AlgebraicGeometry.Surjective.{u}) inferInstance _).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  · exact (Space.presheaf_yoneda_map_iff B integerBase hZ
      (P := @AlgebraicGeometry.Etale.{u}) inferInstance _).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)

/-- The total space of a deformation of `X`, as an algebraic space. -/
abbrev totalSpace : AlgebraicSpaces B integerBase hZ := ⟨P.left.space, P.left.algebraic⟩

/-- **The cartesian finite-order deformation of a deformation of `X`** over the thickening
`Spec k ⊂ Spec A`: the morphism under study is the total space over its base. -/
def specialDeformation : Space.CartesianFiniteOrderDeformation B integerBase hZ where
  X' := totalSpace x₀ hx₀ P
  Y' := schemeSpace (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base)
  B' := schemeSpace (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base)
  X := (baseSpecial x₀ hx₀ P).preimage P.left.toBase
  Y := baseSpecial x₀ hx₀ P
  B := baseSpecial x₀ hx₀ P
  base_finiteOrder := isFiniteOrderThickening_baseSpecial x₀ hx₀ P
  source_thickening := Space.isThickening_preimage B integerBase hZ (baseSpecial x₀ hx₀ P)
    (ObjectProperty.homMk P.left.toBase :
      totalSpace x₀ hx₀ P ⟶ schemeSpace (spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base))
    (isThickening_baseSpecial x₀ hx₀ P)
  target_thickening := isThickening_baseSpecial x₀ hx₀ P
  f := (baseSpecial x₀ hx₀ P).fromPreimage P.left.toBase
  f' := P.left.toBase
  g := 𝟙 _
  g' := 𝟙 _
  comm_f := Subfunctor.fromPreimage_ι _ _
  comm_g := by simp
  isPullback_X := by
    have h := (Subfunctor.isPullback_preimage P.left.toBase (baseSpecial x₀ hx₀ P)).flip
    rwa [← Category.comp_id ((baseSpecial x₀ hx₀ P).fromPreimage P.left.toBase),
      ← Category.comp_id P.left.toBase] at h
  isPullback_Y := IsPullback.id_vert _
  flat_X' := by
    have h := P.left.flat
    rwa [← Category.comp_id P.left.toBase] at h

/-- The special fibre `X` maps to the inverse image of `Spec k` in the total space. -/
def specialLift : space x₀ ⟶ ((baseSpecial x₀ hx₀ P).preimage P.left.toBase).toFunctor :=
  (Subfunctor.isPullback_preimage P.left.toBase (baseSpecial x₀ hx₀ P)).lift
    (toResidueField x₀ hx₀ ≫ Subfunctor.toRange (yoneda.map
      (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P))))
    P.hom.map (by
      rw [Category.assoc, Subfunctor.toRange_ι]
      exact P.hom.cartesian.w.symm)

/-- The composite of `specialLift x₀ hx₀ P` with the inclusion of the inverse image of `Spec k`
is the map `X ⟶ P.left.space` of the deformation. -/
@[reassoc]
theorem specialLift_ι : specialLift x₀ hx₀ P ≫ ((baseSpecial x₀ hx₀ P).preimage P.left.toBase).ι =
    P.hom.map :=
  (Subfunctor.isPullback_preimage P.left.toBase (baseSpecial x₀ hx₀ P)).lift_snd _ _ _

/-- The composite of `specialLift x₀ hx₀ P` with the projection of the inverse image of `Spec k`
to `Spec k` is the structure morphism `X ⟶ Spec k`. -/
theorem specialLift_fromPreimage :
    specialLift x₀ hx₀ P ≫ (baseSpecial x₀ hx₀ P).fromPreimage P.left.toBase =
      toResidueField x₀ hx₀ ≫ Subfunctor.toRange (yoneda.map
        (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P))) :=
  (Subfunctor.isPullback_preimage P.left.toBase (baseSpecial x₀ hx₀ P)).lift_fst _ _ _

/-- The square formed by `specialLift x₀ hx₀ P`, the structure morphism `X ⟶ Spec k`, the
projection of the inverse image of `Spec k` and the identification of `Spec k` with its image in
`Spec A` is cartesian. -/
theorem isPullback_specialLift :
    IsPullback (specialLift x₀ hx₀ P) (toResidueField x₀ hx₀)
      ((baseSpecial x₀ hx₀ P).fromPreimage P.left.toBase) (Subfunctor.toRange (yoneda.map
        (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P)))) := by
  refine IsPullback.of_right ?_ (specialLift_fromPreimage x₀ hx₀ P)
    (Subfunctor.isPullback_preimage P.left.toBase (baseSpecial x₀ hx₀ P)).flip
  rw [specialLift_ι, Subfunctor.toRange_ι]
  exact P.hom.cartesian

include hx₀ in
/-- The structure morphism `X ⟶ Spec k` is of finite presentation and proper. -/
theorem isFinitePresentation_and_isProper_toResidueField :
    Space.IsFinitePresentation B integerBase hZ (toResidueField x₀ hx₀) ∧
      Space.IsProper B integerBase hZ (toResidueField x₀ hx₀) :=
  prop_comp_yoneda_eqToHom _ _ ⟨x₀.obj.property.1, x₀.obj.property.2.2⟩

/-- The special fibre of the cartesian finite-order deformation is of finite presentation and
proper over `Spec k`: it is `X ⟶ Spec k`, up to isomorphism. -/
theorem isFinitePresentation_and_isProper_specialDeformation_f :
    Space.IsFinitePresentation B integerBase hZ (specialDeformation x₀ hx₀ P).f ∧
      Space.IsProper B integerBase hZ (specialDeformation x₀ hx₀ P).f := by
  have : IsIso (Subfunctor.toRange (yoneda.map
      (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P)))) :=
    (isThickeningHom_baseSpecial x₀ hx₀ P).1
  have : IsIso (specialLift x₀ hx₀ P) := (isPullback_specialLift x₀ hx₀ P).isIso_fst_of_isIso
  let ie := (asIso (Subfunctor.toRange (yoneda.map
    (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P))))).inv
  let il := (asIso (specialLift x₀ hx₀ P)).inv
  have hsq : IsPullback il ((baseSpecial x₀ hx₀ P).fromPreimage P.left.toBase)
      (toResidueField x₀ hx₀) ie := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    simp only [il, ie, asIso_inv, IsIso.eq_comp_inv, Category.assoc,
      ← (isPullback_specialLift x₀ hx₀ P).w, IsIso.inv_hom_id_assoc]
  let sX : AlgebraicSpaces B integerBase hZ :=
    ⟨_, (specialDeformation x₀ hx₀ P).source_thickening.1.1⟩
  let sY : AlgebraicSpaces B integerBase hZ := ⟨_, (isThickening_baseSpecial x₀ hx₀ P).1.1⟩
  let s₀ : AlgebraicSpaces B integerBase hZ := ⟨space x₀, x₀.obj.obj.left.property⟩
  let sk : AlgebraicSpaces B integerBase hZ := schemeSpace (spaceBaseOver B hZ
    (contains_spec x₀ hx₀) (residueFieldBase (ULift.{u} ℤ) k))
  have h := isFinitePresentation_and_isProper_toResidueField x₀ hx₀
  have key (Q : MorphismProperty (AlgebraicSpaces B integerBase hZ)) [Q.IsStableUnderBaseChange]
      (hQ : Q (ObjectProperty.homMk (toResidueField x₀ hx₀) : s₀ ⟶ sk)) :
      Q (ObjectProperty.homMk ((baseSpecial x₀ hx₀ P).fromPreimage P.left.toBase) : sX ⟶ sY) :=
    prop_of_isPullback (ObjectProperty.homMk il : sX ⟶ s₀) _ _ (ObjectProperty.homMk ie : sY ⟶ sk)
      hsq hQ
  exact ⟨key (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (f : F ⟶ G) =>
      Space.IsFinitePresentation B integerBase hZ f.hom) h.1,
    key (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (f : F ⟶ G) =>
      Space.IsProper B integerBase hZ f.hom) h.2⟩

/-- **A deformation of `X` over `A` is of finite presentation and proper over `Spec A`**:
finite presentation and properness pass from the special fibre to the total space of a cartesian
finite-order deformation (Stacks 0CG6, parts 0CGK, 0CGB, 0CGD and 0CGS). -/
theorem isProperFlatSpace_family :
    Space.IsFinitePresentation B integerBase hZ P.left.toBase ∧
      Space.IsFlat B integerBase hZ P.left.toBase ∧
        Space.IsProper B integerBase hZ P.left.toBase := by
  obtain ⟨⟨hlfp, hqc, hqs⟩, hpr⟩ := isFinitePresentation_and_isProper_specialDeformation_f x₀ hx₀ P
  let D := specialDeformation x₀ hx₀ P
  exact ⟨⟨D.isLocallyOfFinitePresentation_iff.1 hlfp, D.isQuasiCompact_iff.1 hqc,
      D.isSeparated_iff_and_isQuasiSeparated_iff.2.1 hqs⟩, P.left.flat, D.isProper_iff.1 hpr⟩

/-- Transporting a cartesian square along an identification of the base of its left side. -/
theorem isPullback_comp_eqToHom_left {X X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {U U' V : BigFppfOver B integerBase hZ} (top : X ⟶ X') (l : X ⟶ yoneda.obj U)
    (r : X' ⟶ yoneda.obj V) (hU : U = U') (b : U' ⟶ V)
    (h : IsPullback top (l ≫ yoneda.map (eqToHom hU)) r (yoneda.map b)) :
    IsPullback top l r (yoneda.map (eqToHom hU ≫ b)) := by
  subst hU
  simpa using h

/-- The commutativity of a square over a transported base. -/
theorem comp_eq_comp_eqToHom_comp {X X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {U U' V : BigFppfOver B integerBase hZ} (m : X ⟶ X') (l : X ⟶ yoneda.obj U)
    (r : X' ⟶ yoneda.obj V) (hU : U = U') (b : U' ⟶ V)
    (hw : m ≫ r = (l ≫ yoneda.map (eqToHom hU)) ≫ yoneda.map b) :
    m ≫ r = l ≫ yoneda.map (eqToHom hU ≫ b) := by
  subst hU
  simpa using hw

/-- The deformation of `x₀` attached to a deformation of `X`: its total space, which is of finite
presentation, flat and proper over its base. -/
def toPoint : CartesianProperFlatSpaces B integerBase hZ :=
  ⟨⟨⟨⟨P.left.space, P.left.algebraic⟩, spaceBaseOver B hZ (contains_spec x₀ hx₀) P.left.base,
    P.left.toBase⟩, isProperFlatSpace_family x₀ hx₀ P⟩⟩

/-- The base morphism of the arrow of the deformation of `x₀` attached to a deformation of `X`. -/
abbrev toArrowRight :
    (cartesianProperFlatProjection B integerBase hZ).obj x₀ ⟶
      (cartesianProperFlatProjection B integerBase hZ).obj (toPoint x₀ hx₀ P) :=
  eqToHom (base_eq_residueFieldBase x₀ hx₀) ≫
    spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P)

/-- The arrow `x₀ ⟶ x` of the deformation of `x₀` attached to a deformation of `X`. -/
def toArrow : x₀ ⟶ toPoint x₀ hx₀ P where
  hom := ObjectProperty.homMk
    { left := ObjectProperty.homMk P.hom.map
      right := toArrowRight x₀ hx₀ P
      w := comp_eq_comp_eqToHom_comp _ _ _ _ _ P.hom.cartesian.w }
  property := by
    refine SpacesDescent.isStronglyCartesian_of_isPullback
      (U := ((isProperFlatSpace B integerBase hZ).ι.obj (toPoint x₀ hx₀ P).obj).right)
      (V := ((isProperFlatSpace B integerBase hZ).ι.obj x₀.obj).right)
      (toArrowRight x₀ hx₀ P) _ rfl rfl
      (by simp only [eqToHom_refl, Category.id_comp]; exact (Category.comp_id _).symm)
      (by simp only [eqToHom_refl]; exact Category.comp_id _)
      (by simp only [eqToHom_refl]; exact Category.comp_id _) ?_
    exact isPullback_comp_eqToHom_left _ _ _ _ _ P.hom.cartesian

/-- `toPoint x₀ hx₀ P` lies over the spectrum of the base of `P`. -/
theorem toPoint_base : (projection B hZ).obj (toPoint x₀ hx₀ P) =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) P.left.base)) ≫
      𝟙 integerBase) :=
  post_spaceBaseOver x₀ hx₀ P.left.base

/-- The base morphism of `toArrow x₀ hx₀ P` is the spectrum of the morphism `A ⟶ k` of `P`. -/
theorem toArrow_map :
    (cartesianProperFlatProjection B integerBase hZ).map (toArrow x₀ hx₀ P) =
      eqToHom (base_eq_spaceBaseOver x₀ hx₀ hx₀) ≫
        spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (specialBase x₀ hx₀ P) ≫
          eqToHom (base_eq_spaceBaseOver x₀ hx₀ (toPoint_base x₀ hx₀ P)).symm := by
  show toArrowRight x₀ hx₀ P = _
  simp only [toArrowRight]
  rfl

/-- In schemes over `Spec ℤ`, `toArrow x₀ hx₀ P` lies over the spectrum of the residue map of the
base of `P`. -/
theorem toArrow_base :
    eqToHom (congrArg Over.left hx₀).symm ≫ ((projection B hZ).map (toArrow x₀ hx₀ P)).left ≫
        eqToHom (congrArg Over.left (toPoint_base x₀ hx₀ P)) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap P.left.base)) := by
  have h := spec_eq_of_map_eq x₀ hx₀ (specialBase x₀ hx₀ P) (toArrow x₀ hx₀ P)
    (toPoint_base x₀ hx₀ P) hx₀ (toArrow_map x₀ hx₀ P)
  rwa [hom_toRingHom_eq_residueMap] at h

/-- The deformation of `x₀` attached to a deformation of `X`. -/
def toObj : Obj x₀ hx₀ where
  algebra := P.left.base
  point := toPoint x₀ hx₀ P
  arrow := toArrow x₀ hx₀ P
  base := toPoint_base x₀ hx₀ P
  arrow_base := toArrow_base x₀ hx₀ P

/-- The identity is cartesian over the identity of a spectrum, up to an identification of the
spectrum with itself. -/
theorem isPullback_id_comp_eqToHom {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (A : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k)
    (r : X ⟶ yoneda.obj (spaceBaseOver B hZ (contains_spec x₀ hx₀) A))
    (h : spaceBaseOver B hZ (contains_spec x₀ hx₀) A =
      spaceBaseOver B hZ (contains_spec x₀ hx₀) A) :
    IsPullback (𝟙 X) r (r ≫ yoneda.map (eqToHom h))
      (yoneda.map (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (𝟙 A))) := by
  rw [spaceBaseOverMap_id]
  simpa using IsPullback.id_horiz r

/-- The identity is cartesian over the identity of a spectrum, up to an identification of the
spectrum with itself, the other way round. -/
theorem isPullback_id_comp_eqToHom' {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (A : ArtinianLocalAlgCat.{u, u, u} (ULift.{u} ℤ) k)
    (r : X ⟶ yoneda.obj (spaceBaseOver B hZ (contains_spec x₀ hx₀) A))
    (h : spaceBaseOver B hZ (contains_spec x₀ hx₀) A =
      spaceBaseOver B hZ (contains_spec x₀ hx₀) A) :
    IsPullback (𝟙 X) (r ≫ yoneda.map (eqToHom h)) r
      (yoneda.map (spaceBaseOverMap B hZ (contains_spec x₀ hx₀) (𝟙 A))) := by
  rw [spaceBaseOverMap_id]
  simpa using IsPullback.id_horiz r

/-- The family of the deformation of `x₀` attached to a deformation `P` of `X` is the family of
`P`. -/
def familyToObjIso : family x₀ hx₀ (toObj x₀ hx₀ P) ≅ P.left where
  hom :=
    { base := 𝟙 P.left.base
      map := 𝟙 P.left.space
      cartesian := isPullback_id_comp_eqToHom x₀ hx₀ P.left.base P.left.toBase _ }
  inv :=
    { base := 𝟙 P.left.base
      map := 𝟙 P.left.space
      cartesian := isPullback_id_comp_eqToHom' x₀ hx₀ P.left.base P.left.toBase _ }
  hom_inv_id := FlatAlgebraicSpaceFamily.Hom.ext (Category.id_comp _) (Category.id_comp _)
  inv_hom_id := FlatAlgebraicSpaceFamily.Hom.ext (Category.id_comp _) (Category.id_comp _)

/-- **Every deformation of `X` comes from a deformation of `x₀`.** -/
def toSpaceDeformationToObjIso : toSpaceDeformation x₀ hx₀ (toObj x₀ hx₀ P) ≅ P :=
  Over.isoMk (familyToObjIso x₀ hx₀ P) (FlatAlgebraicSpaceFamily.Hom.ext
    (isTerminal_residueFieldBase.hom_ext _ _) (Category.comp_id _))

/-- The functor `𝓕_{𝒳,k,x₀} ⥤ 𝓓_X` is essentially surjective. -/
theorem toSpaceDeformationFunctor_essSurj :
    letI := (predeformation x₀ hx₀).category
    (toSpaceDeformationFunctor x₀ hx₀).EssSurj :=
  let := (predeformation x₀ hx₀).category
  ⟨fun P => ⟨toObj x₀ hx₀ P, ⟨toSpaceDeformationToObjIso x₀ hx₀ P⟩⟩⟩

end EssSurj

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
