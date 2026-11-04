module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFamilyDatum
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFamilyOverlaps

/-!
# The rings of global functions on the objects of a slice, and the maps between them

Let `p : 𝒳 ⥤ BigFppfOver B S hS` be a category fibred in groupoids and `x` an object of `𝒳`. This
file studies the rings of global functions on the schemes underlying the objects of the slice
`Over x`, the maps between them induced by morphisms of the slice, and the restriction maps of a
sheaf of modules on the slice along those morphisms.

* The induced maps compose contravariantly: the map induced by a composite `f ≫ h` is the map
  induced by `h` followed by the map induced by `f`.
* For a pullback square of objects of the slice over an affine object with affine factors, the
  ring of global functions on the fibre product is the tensor product of the rings of the two
  factors over the ring of the base, with `b ⊗ₜ 1` and `1 ⊗ₜ c` sent to the images of `b` and
  `c` along the two projections.
* Restriction of sections along a morphism of the slice is semilinear over the induced map of
  global functions.

## Main results

* `AlgebraicGeometry.FibredSite.appTopGamma_comp_apply`,
  `AlgebraicGeometry.FibredSite.appTopGamma_id_apply` and
  `AlgebraicGeometry.FibredSite.appTopGamma_comp_apply_of_eq`: the global functions on the schemes
  underlying the objects of a slice are a contravariant functor of the slice.
* `AlgebraicGeometry.FibredSite.restrictₛₗ_smul_appTopGamma`: restriction of sections along a
  morphism of the slice is semilinear along the induced map of global functions.
* `AlgebraicGeometry.FibredSite.isScalarTower_appTopGamma`: a factorisation `f ≫ h = k` of a
  morphism of the slice makes a scalar tower on the sections at its source.
* `AlgebraicGeometry.FibredSite.exists_ringEquivTensorGamma_of_isPullback`: the ring of global
  functions on a fibre product of two affine objects over an affine object is the tensor product
  of the rings of the two factors, with its values on the two kinds of pure tensor.
* `AlgebraicGeometry.FibredSite.exists_piRestrictₛₗ_linear`: the restrictions of sections to the
  members of a family assemble into one linear map to the product of the modules of sections.

## Implementation notes

The module structures over the rings of global functions are instance arguments, together with
hypotheses identifying their action with that of the ring of sections of the coefficient sheaf of
rings, which is the same ring by
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_over_obj_obj`. For the structures
`inferInstanceAs` at an object and `Module.compHom` along an induced map, these hypotheses are
`fun _ _ => rfl`. No instance is created.

`AlgebraicGeometry.FibredSite.exists_ringEquivTensorGamma_of_isPullback` returns a ring
equivalence rather than the algebra equivalence
`AlgebraicGeometry.FibredSite.algEquivTensorGammaOfIsPullback` it is built from: the two factors
may be the same object, so the two maps into the ring of the fibre product cannot both be algebra
structures.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v w u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The map of global functions induced by a composite `f ≫ h` of morphisms of the slice is the
map induced by `h` followed by the map induced by `f`. -/
theorem appTopGamma_comp_apply {x : 𝒳} {U V W : Over x} (f : U ⟶ V) (h : V ⟶ W)
    (b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (p.map f.left)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map (p.map h.left)).appTop.hom b) =
      ((BigFppfOver.toScheme B S hS).map (p.map (f ≫ h).left)).appTop.hom b := by
  rw [Over.comp_left, p.map_comp, CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- The map of global functions induced by an identity of the slice is the identity. -/
theorem appTopGamma_id_apply {x : 𝒳} {U : Over x}
    (b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj U.left), ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (p.map (𝟙 U : U ⟶ U).left)).appTop.hom b = b := by
  simp

/-- If `f ≫ h = k` in the slice, the map of global functions induced by `k` is the map induced by
`h` followed by the map induced by `f`. -/
theorem appTopGamma_comp_apply_of_eq {x : 𝒳} {U V W : Over x} (f : U ⟶ V) (h : V ⟶ W)
    (k : U ⟶ W) (hk : f ≫ h = k)
    (b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (p.map f.left)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map (p.map h.left)).appTop.hom b) =
      ((BigFppfOver.toScheme B S hS).map (p.map k.left)).appTop.hom b := by
  rw [appTopGamma_comp_apply, hk]

/-- Restriction of sections of a sheaf of modules along a morphism `f : U ⟶ V` of the slice is
semilinear along the map of global functions induced by `f`, for module structures over the rings
of global functions whose actions agree with those of the rings of sections by `hV` and `hU`. -/
theorem restrictₛₗ_smul_appTopGamma (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    (N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    {U V : Over x} (f : U ⟶ V)
    [Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤) (N.val.obj (op V))]
    [Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj U.left), ⊤) (N.val.obj (op U))]
    (hV : ∀ (c : Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤))
      (n : N.val.obj (op V)), c • n = (sectionRingEquivGamma B S hS p hp .fppf V).symm c • n)
    (hU : ∀ (c : Γ((BigFppfOver.toScheme B S hS).obj (p.obj U.left), ⊤))
      (n : N.val.obj (op U)), c • n = (sectionRingEquivGamma B S hS p hp .fppf U).symm c • n)
    (b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤)) (n : N.val.obj (op V)) :
    N.val.restrictₛₗ f.op (b • n) =
      ((BigFppfOver.toScheme B S hS).map (p.map f.left)).appTop.hom b •
        N.val.restrictₛₗ f.op n := by
  rw [hV, hU]
  exact N.val.map_smul f.op _ n

/-- Let `f : U ⟶ V` and `h : V ⟶ W` be morphisms of the slice with `f ≫ h = k`. If the sections of
a sheaf of modules over `U` are a module over the global functions on `V` through `f` and over
those on `W` through `k`, and the algebra structure of the global functions on `V` over those on
`W` is the map induced by `h`, then these structures form a scalar tower. -/
theorem isScalarTower_appTopGamma (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    (N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    {U V W : Over x} (f : U ⟶ V) (h : V ⟶ W) (k : U ⟶ W) (hk : f ≫ h = k)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤)]
    [Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj U.left), ⊤) (N.val.obj (op U))]
    [Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤) (N.val.obj (op U))]
    [Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) (N.val.obj (op U))]
    (halg : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map h.left)).appTop.hom)
    (hV : ∀ (b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤))
      (n : N.val.obj (op U)), b • n =
        ((BigFppfOver.toScheme B S hS).map (p.map f.left)).appTop.hom b • n)
    (hW : ∀ (a : Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤))
      (n : N.val.obj (op U)), a • n =
        ((BigFppfOver.toScheme B S hS).map (p.map k.left)).appTop.hom a • n) :
    IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj V.left), ⊤) (N.val.obj (op U)) :=
  IsScalarTower.of_algebraMap_smul fun a n ↦ by
    rw [halg, hV, appTopGamma_comp_apply, hk, hW]

include hS in
/-- For a pullback square of objects of the slice whose base `T` and factors `Yi`, `Yj` are
affine, there is a ring isomorphism from the tensor product of the rings of global functions on
`Yi` and `Yj` over that on `T` to the ring of global functions on the fibre product, taking
`b ⊗ₜ 1` to the image of `b` along the first projection and `1 ⊗ₜ c` to the image of `c` under
the algebra structure given by the second projection. -/
theorem exists_ringEquivTensorGamma_of_isPullback (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    {T Yi Yj Pb : Over x} {fst : Pb ⟶ Yi} {snd : Pb ⟶ Yj} {gi : Yi ⟶ T} {gj : Yj ⟶ T}
    (h : IsPullback fst snd gi gj)
    (hT : IsAffineOver B S hS (p.obj T.left)) (hYi : IsAffineOver B S hS (p.obj Yi.left))
    (hYj : IsAffineOver B S hS (p.obj Yj.left))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yi.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤)]
    (hgi : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yi.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map gi.left)).appTop.hom)
    (hgj : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map gj.left)).appTop.hom)
    (hPb : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map (fst ≫ gi).left)).appTop.hom)
    (hsnd : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map snd.left)).appTop.hom) :
    ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yi.left), ⊤)
        ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)]
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤) ≃+*
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤),
      (∀ b : Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yi.left), ⊤),
        ψ (b ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)]
            (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤))) =
          ((BigFppfOver.toScheme B S hS).map (p.map fst.left)).appTop.hom b) ∧
      (∀ c : Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤),
        ψ ((1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yi.left), ⊤))
            ⊗ₜ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)] c) =
          algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) c) := by
  have hu : ∀ a, ((BigFppfOver.toScheme B S hS).map (p.map fst.left)).appTop.hom
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yi.left), ⊤) a) =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) a := fun a ↦ by
    rw [hgi, hPb, appTopGamma_comp_apply]
  have hv : ∀ a, ((BigFppfOver.toScheme B S hS).map (p.map snd.left)).appTop.hom
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Yj.left), ⊤) a) =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) a := fun a ↦ by
    rw [hgj, hPb, h.w, appTopGamma_comp_apply]
  have key := algEquivTensorAppTopOfIsPullback_tmul
    (isPullback_toScheme_of_isPullback B S hS p hp h) hgi hgj hu hv
  refine ⟨(algEquivTensorGammaOfIsPullback B S hS p hp h hT hYi hYj hgi hgj hu hv).toRingEquiv,
    fun b => (key b 1).trans ?_, fun c => (key 1 c).trans ?_⟩
  · simp
  · rw [hsnd]
    simp

/-- The restrictions of sections along morphisms `g i : Y i ⟶ T` of the slice assemble into one
linear map, over the ring of global functions on `T`, from the sections over `T` to the product of
the sections over the `Y i`, where the sections over `Y i` are a module over that ring through
the map induced by `g i` as `hY` says. -/
theorem exists_piRestrictₛₗ_linear (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    (N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x))
    {T : Over x} {ι : Type*} (Y : ι → Over x) (g : ∀ i, Y i ⟶ T)
    [Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤) (N.val.obj (op T))]
    [∀ i, Module Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤) (N.val.obj (op (Y i)))]
    (hT : ∀ (c : Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤))
      (n : N.val.obj (op T)), c • n = (sectionRingEquivGamma B S hS p hp .fppf T).symm c • n)
    (hY : ∀ (i : ι) (c : Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤))
      (n : N.val.obj (op (Y i))), c • n =
        (sectionRingEquivGamma B S hS p hp .fppf (Y i)).symm
          (((BigFppfOver.toScheme B S hS).map (p.map (g i).left)).appTop.hom c) • n) :
    ∃ ρ : N.val.obj (op T) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj T.left), ⊤)]
        ∀ i, N.val.obj (op (Y i)),
      ∀ (n : N.val.obj (op T)) (i : ι), ρ n i = N.val.restrictₛₗ (g i).op n := by
  refine ⟨{ toFun := fun n i ↦ N.val.restrictₛₗ (g i).op n
            map_add' := fun n n' ↦ funext fun i ↦ map_add (N.val.restrictₛₗ (g i).op) n n'
            map_smul' := fun c n ↦ funext fun i ↦ ?_ }, fun _ _ ↦ rfl⟩
  simp only [RingHom.id_apply, Pi.smul_apply]
  rw [hT, hY i]
  exact N.val.map_smul (g i).op _ n

end AlgebraicGeometry.FibredSite

end
