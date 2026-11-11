module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesEffectiveRebase
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyCartesian
public import StacksFrontier.Deformation.Artin.FormalObject.OfPredeformation
public import StacksFrontier.Deformation.Smooth.VersalLevelHom

/-!
# The levels of an effective formal object of `Spaces'_{fp, flat, proper}` map to its algebraization

Let `ξ = (R, ξ_n, f_n)` be an effective formal object of the stack `p'_{fp, flat, proper}` of
Stacks 0D1D over the big fppf site of `S`, realized (Stacks 07X7) by an algebraic space `Y` over
`Spec R` with identifications `e_n : Λ(Y_n) ≅ ξ_n` of the lower-shriek extensions of its adic
fibres with the levels
(`AlgebraicGeometry.exists_relocalizeSpace_adicFibreSpaceOf_iso_of_isEffective`).
The composites `ξ_n ≅ Λ(Y_n) ⟶ Λ(Y)` are compatible with the transitions of `ξ`.

When `ξ` is the image of a formal object `η` of the predeformation category `𝓕_{𝒳,k,x₀}` of a point
`x₀` (Stacks 07T4, 0CXH), the arrows `x₀ ⟶ ξ_n` composed with these maps all agree, and if `η` is
versal (Stacks 06HR) every deformation `x₀ ⟶ x` over an Artinian base factors this common map
`x₀ ⟶ Λ(Y)` through `x`. This is the form in which the proof of Stacks 0D1R restricts an invertible
module on the algebraization `Y` to every infinitesimal deformation of `x₀`.

## Main definitions

* `AlgebraicGeometry.levelToAlgebraization`: the map `ξ_n ≅ Λ(Y_n) ⟶ Λ(Y)`.

## Main results

* `AlgebraicGeometry.transition_comp_levelToAlgebraization`: compatibility with the transitions.
* `AlgebraicGeometry.isIso_hom_left_of_isIso_hom_right`: a morphism of `Spaces'_{fp, flat, proper}`
  over an isomorphism of bases is an isomorphism of total spaces.
* `AlgebraicGeometry.exists_comp_eq_of_isVersal`: every deformation of `x₀` factors the map from
  `x₀` to the algebraization.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 06HR](https://stacks.math.columbia.edu/tag/06HR)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

open Space Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Isomorphisms of total spaces -/

/-- **A morphism of `Spaces'_{fp, flat, proper}` lying over an isomorphism of bases is an
isomorphism of total spaces**: the square of a morphism of families is cartesian (Stacks 04U9). -/
theorem isIso_hom_left_of_isIso_hom_right {x y : CartesianProperFlatSpaces B S hS} (φ : x ⟶ y)
    [IsIso φ.hom.hom.right] : IsIso φ.hom.hom.left := by
  have h := CartesianProperFlatSpaces.isPullback_hom φ
  have : IsIso φ.hom.hom.left.hom := h.isIso_fst_of_isIso
  have : IsIso ((ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
    IsAlgebraicSpace B S hS F).map φ.hom.hom.left) := this
  exact isIso_of_reflects_iso φ.hom.hom.left
    (ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)

/-! ### The maps from the levels to the algebraization -/

/-- The lower-shriek extension of a composite is the composite of the extensions. -/
theorem relocalizeHom_comp_eq (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T)
    (hS : B.Contains S) (g : B.obj hT ⟶ B.obj hS) {X Y Z : AlgebraicSpaces B T hT} (φ : X ⟶ Y)
    (ψ : Y ⟶ Z) :
    Space.relocalizeHom B hT hS g (φ ≫ ψ) =
      Space.relocalizeHom B hT hS g φ ≫ Space.relocalizeHom B hT hS g ψ :=
  ObjectProperty.hom_ext _ ((OverShriek.relocalizePresheafFunctor g).map_comp φ.hom ψ.hom)

section Levels

variable {ξ : FormalObject B S hS (cartesianProperFlatProjection B S hS)}
  {hA : B.Contains (Spec (.of ξ.base.R))} {Y : AlgebraicSpaces B (Spec (.of ξ.base.R)) hA}
  {fY : Y ⟶ schemeSpace (baseObject ξ.base.R B hA)}
  (e : ∀ n, Space.relocalizeSpace B hA hS (formalBaseHom hS ξ.base hA)
      (adicFibreSpaceOf ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY n) ≅ (ξ.level n).obj.obj.left)

/-- The map `ξ_n ≅ Λ(Y_n) ⟶ Λ(Y)` from the `n`-th level of an effective formal object to the
lower-shriek extension of its algebraization `Y`. -/
def levelToAlgebraization (n : ℕ) :
    (ξ.level n).obj.obj.left ⟶ Space.relocalizeSpace B hA hS (formalBaseHom hS ξ.base hA) Y :=
  (e n).inv ≫ Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
    (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY n)

/-- **The maps from the levels to the algebraization are compatible with the transitions.** -/
theorem transition_comp_levelToAlgebraization
    (he : ∀ n, Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
        (adicFibreSuccMap (maximalIdeal ξ.base.R) Y fY n) ≫ (e (n + 1)).hom =
      (e n).hom ≫ (ξ.transition n).hom.hom.left) (n : ℕ) :
    (ξ.transition n).hom.hom.left ≫ levelToAlgebraization e (n + 1) =
      levelToAlgebraization e n := by
  have h1 : (ξ.transition n).hom.hom.left ≫ (e (n + 1)).inv =
      (e n).inv ≫ Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
        (adicFibreSuccMap (maximalIdeal ξ.base.R) Y fY n) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← he n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
        (adicFibreSuccMap (maximalIdeal ξ.base.R) Y fY n) ≫
      Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
        (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY (n + 1)) =
      Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
        (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY n) := by
    rw [← adicFibreSuccMap_adicFibreInclusion (maximalIdeal ξ.base.R) Y fY n]
    exact (relocalizeHom_comp_eq B hA hS (formalBaseHom hS ξ.base hA) _ _).symm
  calc (ξ.transition n).hom.hom.left ≫ levelToAlgebraization e (n + 1)
      = ((ξ.transition n).hom.hom.left ≫ (e (n + 1)).inv) ≫
          Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
            (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY (n + 1)) :=
        (Category.assoc _ _ _).symm
    _ = ((e n).inv ≫ Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
          (adicFibreSuccMap (maximalIdeal ξ.base.R) Y fY n)) ≫
          Space.relocalizeHom B hA hS (formalBaseHom hS ξ.base hA)
            (adicFibreInclusion ξ.base.R (maximalIdeal ξ.base.R) B hA Y fY (n + 1)) := by
        rw [h1]
    _ = levelToAlgebraization e n := by
        rw [Category.assoc, h2]
        rfl

end Levels

/-! ### Formal objects of a predeformation category -/

section Predeformation

attribute [local instance] PredeformationConstruction.category

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CartesianProperFlatSpaces B S hS)
  (hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (η : Deformation.FormalObject (predeformationCategory iΛ
    (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀).projection)

/-- The arrows `x₀ ⟶ ξ_n` of the levels of a formal object of the predeformation category,
followed by any family of maps out of the levels compatible with the transitions, all agree. -/
theorem arrow_comp_eq_arrow_zero_comp {T : AlgebraicSpaces B S hS}
    (G : ∀ n, ((FormalObject.ofPredeformation B S hS iΛ (cartesianProperFlatProjection B S hS) x₀
      hx₀ hfinite η).level n).obj.obj.left ⟶ T)
    (hG : ∀ n, ((FormalObject.ofPredeformation B S hS iΛ (cartesianProperFlatProjection B S hS)
      x₀ hx₀ hfinite η).transition n).hom.hom.left ≫ G (n + 1) = G n) (n : ℕ) :
    ((predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
        x₀ hx₀).objects (η.level n)).arrow.hom.hom.left ≫ G n =
      ((predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
        x₀ hx₀).objects (η.level 0)).arrow.hom.hom.left ≫ G 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, ← hG n]
    have htri := ((predeformationCategory iΛ
      (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀).morphisms _ _
        (η.transition n)).triangle
    exact (congrArg (fun φ => φ.hom.hom.left ≫ G (n + 1)) htri.symm).trans (Category.assoc _ _ _)

/-- The residue map of the first adic truncation `R / 𝔪` of a complete local algebra is
bijective. -/
theorem _root_.Deformation.Artin.residueMap_obj_zero_bijective
    (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) :
    Function.Bijective (residueMap (Deformation.AdicTruncation.obj R 0)) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h : R.residueEquiv (residue R r) = R.residueEquiv (residue R s) := by
      have h1 := Deformation.AdicTruncation.residueEquiv_residue_mk R 0 r
      have h2 := Deformation.AdicTruncation.residueEquiv_residue_mk R 0 s
      exact h1.symm.trans (hxy.trans h2)
    have h' : r - s ∈ maximalIdeal R := Ideal.Quotient.eq.1 (R.residueEquiv.injective h)
    refine Ideal.Quotient.eq.2 ?_
    simpa [Deformation.AdicTruncation.ideal] using h'
  · obtain ⟨y, rfl⟩ := R.residueEquiv.surjective z
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk _ r, Deformation.AdicTruncation.residueEquiv_residue_mk R 0 r⟩

/-- **The arrow from `x₀` to the level `0` of a formal object of the predeformation category lies
over an isomorphism of bases**: its image in schemes is `Spec` of the residue map of `R / 𝔪`,
which is bijective. -/
theorem isIso_arrow_hom_right_level_zero :
    IsIso ((predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion) x₀ hx₀).objects (η.level 0)).arrow.hom.hom.right := by
  set a := (predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙
    Over.post B.inclusion) x₀ hx₀).objects (η.level 0)
  have halg : a.algebra = Deformation.AdicTruncation.obj η.base 0 :=
    ((predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion) x₀ hx₀).object_projection (η.level 0)).symm.trans (η.level_eq 0)
  have hbij : Function.Bijective (residueMap a.algebra) := by
    rw [halg]
    exact Deformation.Artin.residueMap_obj_zero_bijective η.base
  have : IsIso (CommRingCat.ofHom (residueMap a.algebra)) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  have hb := a.arrow_base
  have hX : IsIso ((cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).map
      a.arrow).left := by
    have h3 : IsIso (eqToHom (congrArg Over.left hx₀).symm ≫
        ((cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).map a.arrow).left ≫
          eqToHom (congrArg Over.left a.base)) := by
      rw [hb]
      infer_instance
    have h4 : IsIso (((cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).map
        a.arrow).left ≫ eqToHom (congrArg Over.left a.base)) :=
      IsIso.of_isIso_comp_left (eqToHom (congrArg Over.left hx₀).symm) _
    exact IsIso.of_isIso_comp_right _ (eqToHom (congrArg Over.left a.base))
  have hL : IsIso (B.inclusion.map a.arrow.hom.hom.right.left) := hX
  have : IsIso a.arrow.hom.hom.right.left := isIso_of_reflects_iso _ B.inclusion
  have : IsIso ((Over.forget _).map a.arrow.hom.hom.right) := this
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- **Every deformation of `x₀` factors the common map out of `x₀`**, when `η` is versal: for a
family of maps out of the levels compatible with the transitions, and a deformation `x₀ ⟶ x`
over an Artinian base, there is a map out of the total space of `x` whose composite with
`x₀ ⟶ x` is the map `x₀ ⟶ ξ_0 ⟶ T`. -/
theorem exists_comp_eq_of_isVersal
    (hdef : Deformation.IsPredeformationCategory (predeformationCategory iΛ
      (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (hη : Deformation.IsVersal hdef.cofibered η) {T : AlgebraicSpaces B S hS}
    (G : ∀ n, ((FormalObject.ofPredeformation B S hS iΛ (cartesianProperFlatProjection B S hS) x₀
      hx₀ hfinite η).level n).obj.obj.left ⟶ T)
    (hG : ∀ n, ((FormalObject.ofPredeformation B S hS iΛ (cartesianProperFlatProjection B S hS)
      x₀ hx₀ hfinite η).transition n).hom.hom.left ≫ G (n + 1) = G n)
    (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
      x₀ hx₀) :
    ∃ g : a.point.obj.obj.left ⟶ T, a.arrow.hom.hom.left ≫ g =
      ((predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
        x₀ hx₀).objects (η.level 0)).arrow.hom.hom.left ≫ G 0 := by
  obtain ⟨n, ⟨m⟩⟩ := Deformation.FormalObject.exists_level_hom_of_isVersal hdef η hη
    (show (predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
      x₀ hx₀).carrier from a)
  let mor := (predeformationCategory iΛ
    (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀).morphisms _ _ m
  refine ⟨mor.arrow.hom.hom.left ≫ G n, ?_⟩
  rw [← arrow_comp_eq_arrow_zero_comp iΛ x₀ hx₀ hfinite η G hG n]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ.hom.hom.left ≫ G n) mor.triangle)

end Predeformation

end AlgebraicGeometry

end
