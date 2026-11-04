module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction
public import StacksFrontier.Deformation.Artin.Versality.SliceSmoothness
public import StacksFrontier.Deformation.Artin.Versality.RepresentablySmoothPredeformation

/-!
# Smoothness on a neighbourhood gives versality (Stacks 0DQZ, (4) ⟹ (1))

Let `x` be an object of a category fibred in groupoids `𝒳` over the big fppf site of a locally
Noetherian scheme `S`, lying over a scheme `U`, and let `u₀ ∈ U` be a point with
`Spec κ(u₀) ⟶ S` locally of finite type. This file proves the implication (4) ⟹ (1) of
**Stacks 0DQZ**: if `x|_{U'} : U' → U → 𝒳` is smooth for some open neighbourhood `U' ⊆ U` of
`u₀`, then `x` is versal at `u₀`. The source's argument is that Artin's Axioms, **Stacks 07WK**,
makes `x̂` smooth; here that is case (3) of 07WK,
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'`, read at the residue
point of `u₀` in `U'`, followed by the invariance of versality under restriction to an open
subscheme, `Deformation.Artin.isVersalAt_iff_restrict`.

## Main results

* `AlgebraicGeometry.Stack.isVersalAt_of_isRelativelySmooth_objectMorphism`: a smooth
  `x : (Sch/U) ⟶ 𝒳` is versal at every point whose residue point is locally of finite type over
  `S`.
* `AlgebraicGeometry.Stack.isVersalAt_of_isRelativelySmooth_of_isOpenImmersion`: the same for a
  restriction of `x` along an open immersion.
* `AlgebraicGeometry.Stack.isVersalAt_of_exists_isRelativelySmooth_restrict`: **Stacks 0DQZ**,
  (4) ⟹ (1), with `x|_{U'}` the composite of the inclusion of an open subscheme
  (`AlgebraicGeometry.BigFppfOver.openSubObj`) with `x`.

## Implementation notes

The 2-Yoneda 1-morphism `AlgebraicGeometry.Stack.objectMorphism` of `x` is built from the lifts
`CategoryTheory.Functor.TwoYoneda.chosenLift`, and these form a choice of pullbacks,
`CategoryTheory.Functor.TwoYoneda.choiceOfPullbacks`, whose slice functor is, on the nose, the
functor underlying `objectMorphism`. So the smoothness of predeformation categories that
Stacks 07WK produces for `objectMorphism` is literally the smoothness of `x̂` that
`Deformation.Artin.isVersalAt_iff_isSmooth_mapPredeformationCategory` reads versality off.

The equivalence of (1) and (4), with the converse implication, is
`AlgebraicGeometry.Stack.isVersalAt_iff_exists_isRelativelySmooth_restrict` in
`StacksFrontier/AlgebraicGeometry/Stacks/VersalChartSmoothBaseChange.lean`.

## References

* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Functor.TwoYoneda

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- The choice of pullbacks underlying the 2-Yoneda 1-morphisms
`CategoryTheory.Functor.TwoYoneda.liftBased` of a category fibred in groupoids: the pullback of
`x` along `f : V ⟶ U` is the chosen lift of `x` at the object `f` of `Over U`. -/
def choiceOfPullbacks (p : 𝒮 ⥤ C) (hp : p.IsFiberedInGroupoids) : p.ChoiceOfPullbacks where
  obj {_ U} f x :=
    haveI : p.IsHomLift f (chosenLift p hp U x (Over.mk f)).φ :=
      (chosenLift p hp U x (Over.mk f)).isStronglyCartesian.toIsHomLift
    ⟨(chosenLift p hp U x (Over.mk f)).y,
      IsHomLift.domain_eq p f (chosenLift p hp U x (Over.mk f)).φ⟩
  map {_ U} f x := (chosenLift p hp U x (Over.mk f)).φ
  isStronglyCartesian {_ U} f x := (chosenLift p hp U x (Over.mk f)).isStronglyCartesian

/-- The 1-morphism attached to an object of a fibre by `choiceOfPullbacks` is, on the nose, the
functor underlying the 2-Yoneda 1-morphism `CategoryTheory.Functor.TwoYoneda.liftBased`. -/
theorem sliceFunctor_choiceOfPullbacks (p : 𝒮 ⥤ C) (hp : p.IsFiberedInGroupoids) {U : C}
    (x : p.Fiber U) :
    (choiceOfPullbacks p hp).sliceFunctor x = liftFunctor p hp U x :=
  rfl

end CategoryTheory.Functor.TwoYoneda

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The spectrum of a field is quasi-compact over any scheme: it has a single point. -/
private theorem quasiCompact_of_spec_field {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Spec (.of k) ⟶ Y) : QuasiCompact f :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun V _ => (Set.toFinite (f ⁻¹' (V : Set Y))).isCompact

/-- The residue point of a point of an open subscheme `U'` of `U` is locally of finite type over
the base exactly when the residue point of its image in `U` is: the two residue fields are
identified by the open immersion. -/
private theorem locallyOfFiniteType_residue_of_isOpenImmersion {T : Scheme.{u}} {U U' : Over T}
    (j : U'.left ⟶ U.left) (hj : _root_.AlgebraicGeometry.IsOpenImmersion j)
    (hjU : j ≫ U.hom = U'.hom) (u : U'.left)
    (h : LocallyOfFiniteType (U.left.fromSpecResidueField (j.base u) ≫ U.hom)) :
    LocallyOfFiniteType (U'.left.fromSpecResidueField u ≫ U'.hom) := by
  rw [← hjU, ← Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j u,
    Category.assoc]
  have := hj
  infer_instance

/-- **Smoothness of `x : U → 𝒳` gives versality at every point whose residue field is of finite
type over `S`.** Let `x` be an object of a category fibred in groupoids over the big fppf site of
a locally Noetherian scheme `S`, lying over `U`, and suppose the 1-morphism
`x : (Sch/U)_{fppf} ⟶ 𝒳` is smooth (Stacks 04XB). Then `x` is versal at every point `u₀ ∈ U` for
which `Spec κ(u₀) ⟶ S` is locally of finite type.

This is the implication (4) ⟹ (2) of Stacks 0DQZ before shrinking: Stacks 07WK, case (3), makes
the map of predeformation categories `x̂` smooth at the residue point of `u₀`, and that is
versality at `u₀` by `Deformation.Artin.isVersalAt_iff_isSmooth_mapPredeformationCategory`, the
2-Yoneda morphism of `x` being the slice functor of the choice of pullbacks
`CategoryTheory.Functor.TwoYoneda.choiceOfPullbacks`. -/
theorem isVersalAt_of_isRelativelySmooth_objectMorphism [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (x : 𝒳.val.obj)
    (hsm : IsRelativelySmooth B S hS
      (objectMorphism B S hS 𝒳 (Functor.Fiber.mk (a := x) rfl)))
    (u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left)
    (hft : LocallyOfFiniteType
      (((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom)) :
    Deformation.Artin.IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl := by
  let U := (𝒳.val.p ⋙ Over.post B.inclusion).obj x
  -- an affine open `Spec Λ ⊆ S` through which the residue point of `u₀` factors
  let i := S.affineOpenCover.idx (Deformation.Artin.basePoint U u₀)
  let Λ := (S.affineOpenCover.X i : Type u)
  let iΛ : Spec (.of Λ) ⟶ S := S.affineOpenCover.f i
  have hcov : Deformation.Artin.basePoint U u₀ ∈ Set.range iΛ.base :=
    S.affineOpenCover.covers _
  have H : Set.range (U.left.fromSpecResidueField u₀ ≫ U.hom).base ⊆ Set.range iΛ.base := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint (U.left.residueField u₀) :=
      Subsingleton.elim (α := Spec (U.left.residueField u₀)) _ _
    rw [hs]
    exact hcov
  let : Algebra Λ (U.left.residueField u₀) := Deformation.Artin.chartResidueAlgebra iΛ U u₀ H
  have hcompat := Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U u₀ H
  obtain ⟨t, ht⟩ := hcov
  let c := Functor.TwoYoneda.choiceOfPullbacks 𝒳.val.p 𝒳.isFiberedInGroupoids
  have hκ := Deformation.Artin.residueFieldPoint_site_contains B S hS 𝒳.val.p x u₀
  rw [Deformation.Artin.isVersalAt_iff_isSmooth_mapPredeformationCategory B S hS 𝒳.val.p x iΛ
    𝒳.isFiberedInGroupoids c u₀ t ht hcompat
    (Deformation.Artin.residueFieldSlicePoint B S hS 𝒳.val.p x u₀ hκ)
    (Deformation.Artin.residueFieldSlicePoint_base B S hS 𝒳.val.p x iΛ u₀ hκ hcompat)
    (Deformation.Artin.residueFieldSlicePoint_fieldPointMap B S hS 𝒳.val.p x iΛ u₀ hκ _)]
  exact Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth' B S hS _ hsm iΛ
    (Deformation.Artin.residueFieldSlicePoint B S hS 𝒳.val.p x u₀ hκ)
    (Deformation.Artin.residueFieldSlicePoint_base B S hS 𝒳.val.p x iΛ u₀ hκ hcompat)
    (by rwa [hcompat]) (quasiCompact_of_spec_field _) inferInstance

/-- **Versality at a point from smoothness on an open neighbourhood.** Let `x` be an object of a
category fibred in groupoids over the big fppf site of a locally Noetherian scheme `S`, lying
over `U`, let `x' ⟶ x` be an arrow lying over a morphism `j : U' ⟶ U` of the site which is an
open immersion of schemes, and suppose `x' : (Sch/U')_{fppf} ⟶ 𝒳` is smooth. Then `x` is versal
at every point `u₀` of the image of `j` for which `Spec κ(u₀) ⟶ S` is locally of finite type.

The point `u₀ = j u₀'` is a point of `U'` at which `x'` is versal by
`AlgebraicGeometry.Stack.isVersalAt_of_isRelativelySmooth_objectMorphism`, and versality is
unchanged by restriction to an open subscheme (`Deformation.Artin.isVersalAt_iff_restrict`). -/
theorem isVersalAt_of_isRelativelySmooth_of_isOpenImmersion [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (x : 𝒳.val.obj)
    {U' : BigFppfOver B S hS} (x' : 𝒳.val.p.Fiber U') (ρ : x'.1 ⟶ x)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (𝒳.val.p.map ρ).left))
    (hsm : IsRelativelySmooth B S hS (objectMorphism B S hS 𝒳 x'))
    (u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left)
    (hu : u₀ ∈ Set.range (B.inclusion.map (𝒳.val.p.map ρ).left).base)
    (hft : LocallyOfFiniteType
      (((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom)) :
    Deformation.Artin.IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl := by
  obtain ⟨y, rfl⟩ := x'
  obtain ⟨u₀', rfl⟩ := hu
  let q := 𝒳.val.p ⋙ Over.post B.inclusion
  let U := q.obj x
  let U' := q.obj y
  let j : U'.left ⟶ U.left := B.inclusion.map (𝒳.val.p.map ρ).left
  have hρ : Deformation.Artin.schemeMap q rfl rfl ρ = j := by
    simp only [Deformation.Artin.schemeMap, eqToHom_refl, Category.id_comp]
    exact Category.comp_id _
  have hjU : j ≫ U.hom = U'.hom :=
    Deformation.Artin.comp_hom_eq_of_schemeMap_eq B S hS 𝒳.val.p rfl rfl ρ j hρ
  -- an affine open `Spec Λ ⊆ S` through which the residue point of `j u₀'` factors
  let i := S.affineOpenCover.idx (Deformation.Artin.basePoint U (j.base u₀'))
  let Λ := (S.affineOpenCover.X i : Type u)
  let iΛ : Spec (.of Λ) ⟶ S := S.affineOpenCover.f i
  have hcov : Deformation.Artin.basePoint U (j.base u₀') ∈ Set.range iΛ.base :=
    S.affineOpenCover.covers _
  have hcomp : U'.left.fromSpecResidueField u₀' ≫ U'.hom =
      Spec.map (j.residueFieldMap u₀') ≫ (U.left.fromSpecResidueField (j.base u₀') ≫ U.hom) := by
    rw [← hjU, ← Category.assoc,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j u₀', Category.assoc]
  have H : Set.range (U.left.fromSpecResidueField (j.base u₀') ≫ U.hom).base ⊆
      Set.range iΛ.base := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint (U.left.residueField (j.base u₀')) :=
      Subsingleton.elim (α := Spec (U.left.residueField (j.base u₀'))) _ _
    rw [hs]
    exact hcov
  have H' : Set.range (U'.left.fromSpecResidueField u₀' ≫ U'.hom).base ⊆ Set.range iΛ.base := by
    rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (Set.range_comp_subset_range _ _).trans H
  exact (Deformation.Artin.isVersalAt_iff_restrict B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids iΛ
    rfl rfl ρ j hj hρ u₀' H H').mp <|
    isVersalAt_of_isRelativelySmooth_objectMorphism B S hS 𝒳 y hsm u₀'
      (locallyOfFiniteType_residue_of_isOpenImmersion j hj hjU u₀' hft)

/-- **Stacks 0DQZ, (4) ⟹ (1), before the finite type hypotheses are spelled out.** Let `x` be an
object of a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`, lying over `U`, and let `U' ⊆ U` be an open subscheme containing `u₀`, read as an object of
the site by `AlgebraicGeometry.BigFppfOver.openSubObj`. If some restriction `x|_{U'}` of `x` to
`U'` — an object over `U'` with an arrow to `x` lying over the inclusion `U' ⟶ U` — is such that
`x|_{U'} : (Sch/U')_{fppf} ⟶ 𝒳` is smooth, and `Spec κ(u₀) ⟶ S` is locally of finite type, then
`x` is versal at `u₀`. -/
theorem isVersalAt_of_isRelativelySmooth_openSubObj [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (x : 𝒳.val.obj)
    (V : (𝒳.val.p.obj x).left.obj.Opens)
    (x' : 𝒳.val.p.Fiber (BigFppfOver.openSubObj B S hS (𝒳.val.p.obj x) V)) (ρ : x'.1 ⟶ x)
    (hρ : 𝒳.val.p.IsHomLift (BigFppfOver.openSubHom B S hS (𝒳.val.p.obj x) V) ρ)
    (hsm : IsRelativelySmooth B S hS (objectMorphism B S hS 𝒳 x'))
    (u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left) (hu₀ : u₀ ∈ V)
    (hft : LocallyOfFiniteType
      (((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom)) :
    Deformation.Artin.IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl := by
  have hy : (B.inclusion.obj (𝒳.val.p.obj x'.1).left) =
      (B.inclusion.obj (BigFppfOver.openSubObj B S hS (𝒳.val.p.obj x) V).left) :=
    congrArg (fun T : BigFppfOver B S hS => B.inclusion.obj T.left) x'.2
  have hmap : B.inclusion.map (𝒳.val.p.map ρ).left = eqToHom hy ≫ V.ι := by
    rw [IsHomLift.fac' 𝒳.val.p (BigFppfOver.openSubHom B S hS (𝒳.val.p.obj x) V) ρ]
    simp [Over.comp_left, Over.eqToHom_left]
  refine isVersalAt_of_isRelativelySmooth_of_isOpenImmersion B S hS 𝒳 x x' ρ ?_ hsm u₀ ?_ hft
  · rw [hmap]
    infer_instance
  · refine ⟨(eqToHom hy.symm).base ⟨u₀, hu₀⟩, ?_⟩
    have h2 : eqToHom hy.symm ≫ B.inclusion.map (𝒳.val.p.map ρ).left = V.ι := by
      rw [hmap, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg (fun f => f.base ⟨u₀, hu₀⟩) h2

/-- **The 1-morphism of a restriction is the restriction of the 1-morphism.** An arrow `x' ⟶ x`
of a category fibred in groupoids over the big fppf site of `S`, lying over `g : U' ⟶ U`, makes
`x' : (Sch/U')_{fppf} ⟶ 𝒳` 2-isomorphic to the composite `U' → U → 𝒳` of `g` with `x`. This is
`AlgebraicGeometry.Stack.objectMorphismFactorIso` with `x'` read in the fibre over a given `U'`. -/
theorem nonempty_objectMorphism_iso_of_isHomLift
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U U' : BigFppfOver B S hS} (x : 𝒳.val.p.Fiber U) (x' : 𝒳.val.p.Fiber U')
    (g : U' ⟶ U) (ρ : x'.1 ⟶ x.1) (hρ : 𝒳.val.p.IsHomLift g ρ) :
    Nonempty (objectMorphism B S hS 𝒳 x' ≅
      schemeFibredCategoryMap B S hS g ≫ objectMorphism B S hS 𝒳 x) := by
  obtain ⟨y, rfl⟩ := x'
  obtain ⟨z, rfl⟩ := x
  obtain rfl : 𝒳.val.p.map ρ = g := (IsHomLift.eq_of_isHomLift 𝒳.val.p g ρ).symm
  exact ⟨objectMorphismFactorIso B S hS 𝒳 ρ⟩

/-- **Stacks 0DQZ, (4) ⟹ (1).** Let `x` be an object of a category fibred in groupoids over the
big fppf site of a locally Noetherian scheme `S`, lying over `U`, and let `u₀ ∈ U` be a point
with `Spec κ(u₀) ⟶ S` locally of finite type. If there is an open neighbourhood `U' ⊆ U` of
`u₀` such that `x|_{U'} : U' → U → 𝒳` is smooth, then `x` is versal at `u₀`. -/
theorem isVersalAt_of_exists_isRelativelySmooth_restrict [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (x : 𝒳.val.obj)
    (u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left)
    (hft : LocallyOfFiniteType
      (((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom))
    (h : ∃ V : (𝒳.val.p.obj x).left.obj.Opens, u₀ ∈ V ∧
      IsRelativelySmooth B S hS
        (schemeFibredCategoryMap B S hS (BigFppfOver.openSubHom B S hS (𝒳.val.p.obj x) V) ≫
          objectMorphism B S hS 𝒳 (Functor.Fiber.mk (a := x) rfl))) :
    Deformation.Artin.IsVersalAt ((𝒳.val.p ⋙ Over.post B.inclusion).obj x)
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x rfl := by
  obtain ⟨V, hu₀, hsm⟩ := h
  let g := BigFppfOver.openSubHom B S hS (𝒳.val.p.obj x) V
  let c := Functor.TwoYoneda.choiceOfPullbacks 𝒳.val.p 𝒳.isFiberedInGroupoids
  let xf : 𝒳.val.p.Fiber (𝒳.val.p.obj x) := Functor.Fiber.mk (a := x) rfl
  have hρ : 𝒳.val.p.IsHomLift g (c.map g xf) := (c.isStronglyCartesian g xf).toIsHomLift
  obtain ⟨e⟩ := nonempty_objectMorphism_iso_of_isHomLift B S hS 𝒳 xf (c.obj g xf) g
    (c.map g xf) hρ
  exact isVersalAt_of_isRelativelySmooth_openSubObj B S hS 𝒳 x V (c.obj g xf) (c.map g xf) hρ
    (isRelativelySmooth_congr_twoIso B S hS e.symm hsm) u₀ hu₀ hft

end AlgebraicGeometry.Stack

end
