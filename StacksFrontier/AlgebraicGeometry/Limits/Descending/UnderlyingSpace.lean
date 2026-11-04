module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.Topology.Limits.RecognizeCone
public import StacksCore.Tactic.StacksAttribute

/-!
# Underlying spaces of inverse limits of schemes

The underlying topological space of the limit of a cofiltered diagram of schemes with affine
transition morphisms is the limit of the underlying topological spaces, and likewise for the
underlying sets.

A directed inverse system is represented by a diagram on a cofiltered category. Both assertions
are phrased as preservation of limits by the forgetful functors `AlgebraicGeometry.Scheme.forget`
and `AlgebraicGeometry.Scheme.forgetToTop`, which retains the canonical projections of any
chosen limit cone together with their naturality.

## Main results

* `AlgebraicGeometry.preservesLimit_forgetToTop_of_isCofiltered_of_isAffineHom`: passing to
  underlying topological spaces preserves such a limit.
* `AlgebraicGeometry.preservesLimit_forget_of_isCofiltered_of_isAffineHom`: passing to underlying
  sets preserves such a limit.

## Implementation notes

The topological statement is proved by exhibiting the preimages of opens of the stages as a
topological basis of the limit and recognising the cone with
`TopCat.isLimit_of_basis_of_preimages`. The set-level statement then follows because
`Scheme.forget` factors as `Scheme.forgetToTop` followed by the forgetful functor on `TopCat`.

Surjectivity of the limit onto compatible families of points is obtained by forming the inverse
system of the spectra of the residue fields at the given points: that system is affine, so its
limit is nonempty, and any point of it maps to the required point of the limit.

## References

* [EGA IV, Proposition 8.2.9]
* [Stacks Project, Tag 0CUE](https://stacks.math.columbia.edu/tag/0CUE)
* [Stacks Project, Tag 0CUF](https://stacks.math.columbia.edu/tag/0CUF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A family of points of the stages of a cofiltered diagram of schemes that is compatible with
the transition morphisms is the family of images of a point of the limit. -/
private theorem exists_point_of_compatible_family
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c)
    (x : ∀ i, D.obj i)
    (hx : ∀ {i j : I} (f : i ⟶ j), D.map f (x i) = x j) :
    ∃ z : c.pt, ∀ i, c.π.app i z = x i := by
  let map' {i j : I} (f : i ⟶ j) : Spec ((D.obj i).residueField (x i)) ⟶
      Spec ((D.obj j).residueField (x j)) :=
    Spec.map ((D.map f).residueFieldMap (x i)) ≫
      Spec.map ((D.obj j).residueFieldCongr (hx f)).inv
  have hr (i j : I) (f : i ⟶ j) :
      map' f ≫ (D.obj j).fromSpecResidueField (x j) =
        (D.obj i).fromSpecResidueField (x i) ≫ D.map f := by
    dsimp [map']
    rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField (hx f).symm]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ _
  let E : I ⥤ Scheme.{u} :=
    { obj i := Spec ((D.obj i).residueField (x i))
      map f := map' f
      map_id i := by
        rw [← cancel_mono ((D.obj i).fromSpecResidueField (x i))]
        simpa using hr i i (𝟙 i)
      map_comp {i} {j} {k} f g := by
        rw [← cancel_mono ((D.obj _).fromSpecResidueField (x _)), hr i k (f ≫ g), D.map_comp]
        rw [Category.assoc, hr j k g, reassoc_of% hr i j f] }
  let α : E ⟶ D :=
    { app i := (D.obj i).fromSpecResidueField (x i)
      naturality {i j} f := by
        dsimp only [E, Functor.const_obj_obj]
        exact hr i j f }
  obtain ⟨p⟩ := Scheme.nonempty_of_isLimit E _ (limit.isLimit E)
  let e : Cone D := (Cone.postcompose α).obj (limit.cone E)
  refine ⟨hc.lift e p, fun i ↦ ?_⟩
  calc
    c.π.app i (hc.lift e p) = e.π.app i p :=
      congrArg (fun f : (limit.cone E).pt ⟶ D.obj i ↦ f p) (hc.fac e i)
    _ = x i := Scheme.fromSpecResidueField_apply (x i) ((limit.cone E).π.app i p)

/-- Passing to underlying topological spaces preserves the limit of a cofiltered diagram of
schemes with affine transition morphisms. -/
@[stacks 0CUF, instance, ega "IV 8.2.9"]
theorem preservesLimit_forgetToTop_of_isCofiltered_of_isAffineHom
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] :
    PreservesLimit D Scheme.forgetToTop := by
  let c : Cone (D ⋙ Scheme.forgetToTop) := Scheme.forgetToTop.mapCone (limit.cone D)
  have hBasis : TopologicalSpace.IsTopologicalBasis
      {U : Set c.pt | ∃ (i : I) (V : Set (D.obj i)), IsOpen V ∧ U = (c.π.app i) ⁻¹' V} := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro W ⟨i, V, hV, rfl⟩
      exact (c.π.app i).hom.continuous.isOpen_preimage V hV
    · intro x U hx hU
      have hAff := isBasis_preimage_isAffineOpen D (limit.cone D) (limit.isLimit D)
      rw [TopologicalSpace.Opens.isBasis_iff_nbhd] at hAff
      obtain ⟨_, ⟨i, V, hV, rfl⟩, hxW, hWU⟩ := hAff (U := ⟨U, hU⟩) hx
      refine ⟨c.π.app i ⁻¹' (V : Set (D.obj i)), ⟨i, (V : Set (D.obj i)), V.2, rfl⟩,
        (Scheme.Hom.mem_preimage (f := (limit.cone D).π.app i)).mp hxW, fun y hy ↦ ?_⟩
      exact hWU ((Scheme.Hom.mem_preimage (f := (limit.cone D).π.app i)).mpr hy)
  have hSet : IsLimit (Scheme.forget.mapCone (limit.cone D)) := by
    have : T0Space c.pt := T0Space.of_open_cover fun x ↦ by
      let f := (limit D).affineCover.f ((limit D).affineCover.idx x)
      exact ⟨_, (limit D).affineCover.covers x, f.opensRange.2,
        Topology.IsEmbedding.t0Space (Y := PrimeSpectrum _)
          ((isAffineOpen_opensRange f).isoSpec.schemeIsoToHomeo.isEmbedding)⟩
    choose liftPoint liftPoint_spec using fun (s : Cone (D ⋙ Scheme.forget)) (p : s.pt) ↦
      exists_point_of_compatible_family D (limit.cone D) (limit.isLimit D)
        (fun i ↦ s.π.app i p) fun f ↦ by simpa using congrArg (fun q ↦ q p) (s.w f)
    refine IsLimit.mk (fun s ↦ TypeCat.ofHom (liftPoint s))
      (fun s i ↦ by ext p; exact liftPoint_spec s p i) fun s m hm ↦ ?_
    ext p
    apply hBasis.eq_iff.mpr
    rintro _ ⟨i, V, hV, rfl⟩
    have hcoords : c.π.app i (m p) = s.π.app i p := congrArg (fun f => f p) (hm i)
    have hlift : c.π.app i (liftPoint s p) = s.π.app i p := liftPoint_spec s p i
    show c.π.app i (m p) ∈ V ↔ c.π.app i (liftPoint s p) ∈ V
    rw [hcoords, hlift]
  rw [← Scheme.forgetToTop_comp_forget] at hSet
  exact preservesLimit_of_preserves_limit_cone (limit.isLimit D)
    (TopCat.isLimit_of_basis_of_preimages c
      (IsLimit.ofIsoLimit hSet (Functor.mapConeMapCone (limit.cone D)).symm) hBasis).some

/-- Passing to underlying sets preserves the limit of a cofiltered diagram of schemes with
affine transition morphisms. -/
@[stacks 0CUE, instance]
theorem preservesLimit_forget_of_isCofiltered_of_isAffineHom
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] :
    PreservesLimit D Scheme.forget := by
  have := preservesLimit_forgetToTop_of_isCofiltered_of_isAffineHom D
  show PreservesLimit D (Scheme.forgetToTop ⋙ forget TopCat)
  infer_instance

end AlgebraicGeometry

end
