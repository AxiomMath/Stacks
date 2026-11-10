module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FpqcDescent

/-!
# The four flattening functors are fpqc sheaves

In the situation of a homomorphism `u : F ⟶ G` of quasi-coherent modules on a scheme `X` over
`S`, the four subterminal functors recording whether the base change `u_T` is an isomorphism, a
monomorphism, an epimorphism, or zero satisfy the sheaf condition for the fpqc topology.

Each is a subterminal functor, so the sheaf condition reduces to the reflection statements of
`StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FpqcDescent`: a compatible family of
sections over an fpqc covering is exactly the assertion that the condition holds over every
member of the covering, and amalgamation is the reflection.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor_isSheaf_fpqc`,
  `surjectivityFunctor_isSheaf_fpqc`, `zeroFunctor_isSheaf_fpqc` and
  `injectivityFunctor_isSheaf_fpqc`.

## Implementation notes

The first three functors are defined on all of `Over S` and the topology is
`AlgebraicGeometry.Scheme.fpqcTopology.over S`.  The injectivity functor is defined only on the
subcategory with flat morphisms, so the topology there is the comap of
`AlgebraicGeometry.Scheme.fpqcPrecoverage` along the inclusion followed by the forgetful functor
to schemes.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- A subterminal functor on schemes over `S`, given by a predicate that is fpqc local on the base,
satisfies the sheaf condition for the fpqc topology. -/
private theorem isSheaf_fpqc_of_forall_iff {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type)
    (P : Over S → Prop) (toProp : ∀ T, F.obj (op T) → P T)
    (ofProp : ∀ T, P T → F.obj (op T))
    (h : ∀ (T : Over S) (𝒰 : Precoverage.ZeroHypercover.{u + 1} Scheme.fpqcPrecoverage T.left),
      P T ↔ ∀ i, P (Over.mk (𝒰.f i ≫ T.hom)))
    (subsingleton : ∀ (T : Over S) (a b : F.obj (op T)), a = b) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F := by
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf ((Scheme.fpqcPrecoverage.toGrothendieck).over S) F
  rw [CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget
    Scheme.fpqcPrecoverage S,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨ι, Y, g, rfl⟩ := R.exists_eq_ofArrows
  let 𝒰 : Scheme.fpqcPrecoverage.ZeroHypercover T.left :=
    ⟨⟨ι, fun i ↦ (Y i).left, fun i ↦ (g i).left⟩, by
      simpa [Precoverage.mem_comap_iff] using hR⟩
  rw [Presieve.isSheafFor_arrows_iff]
  intro x _
  have hlocal (i : ι) : P (Over.mk (𝒰.f i ≫ T.hom)) := by
    have : Over.mk ((g i).left ≫ T.hom) = Y i :=
      CostructuredArrow.obj_ext _ _ rfl (CostructuredArrow.w (g i)).symm
    exact this ▸ toProp _ (x i)
  exact ⟨ofProp T ((h T 𝒰).2 hlocal), fun _ ↦ subsingleton _ _ _,
    fun _ _ ↦ subsingleton _ _ _⟩

/-- The isomorphism functor of a homomorphism of quasi-coherent modules satisfies the sheaf
condition for the fpqc topology on schemes over the base. -/
@[stacks 05MJ "iso_fpqc"]
theorem isomorphismFunctor_isSheaf_fpqc (D : ModuleMapBaseChangeSituation.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) D.isomorphismFunctor :=
  isSheaf_fpqc_of_forall_iff _ _ (fun _ ↦ PLift.down) (fun _ ↦ PLift.up)
    D.isIsomorphismAfterBaseChange_iff_fpqcCover
    (fun _ ⟨_⟩ ⟨_⟩ ↦ rfl)

/-- The surjectivity functor of a homomorphism of quasi-coherent modules satisfies the sheaf
condition for the fpqc topology on schemes over the base. -/
@[stacks 05MJ "surj_fpqc"]
theorem surjectivityFunctor_isSheaf_fpqc (D : ModuleMapBaseChangeSituation.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) D.surjectivityFunctor :=
  isSheaf_fpqc_of_forall_iff _ _ (fun _ ↦ PLift.down) (fun _ ↦ PLift.up)
    D.isSurjectiveAfterBaseChange_iff_fpqcCover
    (fun _ ⟨_⟩ ⟨_⟩ ↦ rfl)

/-- The zero functor of a homomorphism of quasi-coherent modules satisfies the sheaf condition
for the fpqc topology on schemes over the base. -/
@[stacks 05MJ "zero_fpqc"]
theorem zeroFunctor_isSheaf_fpqc (D : ModuleMapBaseChangeSituation.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) D.zeroFunctor :=
  isSheaf_fpqc_of_forall_iff _ _ (fun _ ↦ PLift.down) (fun _ ↦ PLift.up)
    D.isZeroAfterBaseChange_iff_fpqcCover
    (fun _ ⟨_⟩ ⟨_⟩ ↦ rfl)

/-- The injectivity functor of a homomorphism of quasi-coherent modules satisfies the sheaf
condition for the fpqc topology on the category of schemes over the base with flat morphisms. -/
@[stacks 05MJ "inj_fpqc"]
theorem injectivityFunctor_isSheaf_fpqc (D : ModuleMapBaseChangeSituation.{u}) :
    Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap
        (wideSubcategoryInclusion (FlatMorphismOver D.S) ⋙ Over.forget D.S)).toGrothendieck
      D.injectivityFunctor := by
  rw [isSheaf_iff_isSheaf_of_type, Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  let F := wideSubcategoryInclusion (FlatMorphismOver D.S) ⋙ Over.forget D.S
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  let 𝒰 : Precoverage.ZeroHypercover.{u + 1} Scheme.fpqcPrecoverage (F.obj X) :=
    ⟨⟨ι, fun i ↦ F.obj (Z i), fun i ↦ F.map (g i)⟩, by
      simpa [F, Precoverage.mem_comap_iff] using hR⟩
  let P (i : ι) := pullback (F.map (g i)) (F.map f)
  let p₁ (i : ι) : P i ⟶ F.obj (Z i) := pullback.fst (F.map (g i)) (F.map f)
  let p₂ (i : ι) : P i ⟶ F.obj Y := pullback.snd (F.map (g i)) (F.map f)
  let V : Precoverage.ZeroHypercover.{u + 1} Scheme.fpqcPrecoverage (F.obj Y) :=
    ⟨⟨ι, P, p₂⟩, Precoverage.mem_coverings_of_isPullback (fun i ↦ F.map (g i)) 𝒰.mem₀ (F.map f)
      p₂ p₁ (fun i ↦ (IsPullback.of_hasPullback (F.map (g i)) (F.map f)).flip)⟩
  let W (i : ι) : FlatOver D.S := ⟨Over.mk (p₂ i ≫ Y.obj.hom)⟩
  let a (i : ι) : W i ⟶ Y := ⟨Over.homMk (p₂ i), by
    change Flat (p₂ i)
    dsimp [p₂]
    have hg : Flat (F.map (g i)) := (g i).property
    infer_instance⟩
  let b (i : ι) : W i ⟶ Z i := ⟨Over.homMk (p₁ i) (by
    dsimp [W, F]
    have hg : F.map (g i) ≫ X.obj.hom = (Z i).obj.hom := CostructuredArrow.w ((g i).hom)
    have hf : F.map f ≫ X.obj.hom = Y.obj.hom := CostructuredArrow.w f.hom
    rw [← hg, ← hf]
    exact pullback.condition_assoc X.obj.hom), by
    change Flat (p₁ i)
    dsimp [p₁]
    have hf : Flat (F.map f) := f.property
    infer_instance⟩
  have hmem (i : ι) : ((Sieve.generate (Presieve.ofArrows Z g)).pullback f) (a i) := by
    have hcomp : a i ≫ f = b i ≫ g i := by
      apply WideSubcategory.hom_ext
      apply CostructuredArrow.hom_ext
      exact pullback.condition.symm
    rw [Sieve.pullback_apply, hcomp]
    exact Sieve.downward_closed _ (Sieve.le_generate _ _ _ ⟨i⟩) (b i)
  intro x _
  exact ⟨PLift.up ((D.isInjectiveAfterBaseChange_iff_fpqcCover Y.obj V).2
    fun i ↦ (x (a i) (hmem i)).down), fun _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end Stacks.Flatness.ModuleMapBaseChangeSituation

end
