module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleQuasicoherentChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartEtale
public import StacksFrontier.RingTheory.TensorProduct.BaseChangeAlongSquareZeroQuotient

/-!
# The kernel ideals of a square-zero extension are a base change, and the charts are étale

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` over `Y`, in the sense of `AlgebraicGeometry.Space.SquareZeroExtension`, and let
`h : U ⟶ V` be a morphism of the small étale site of `X` between objects with affine underlying
scheme.  This file proves that

```
ker(𝒜(U) ⟶ 𝒪_X(U)) = ker(𝒜(V) ⟶ 𝒪_X(V)) ⊗_{𝒜(V)} 𝒜(U)
```

and deduces that `𝒜(V) ⟶ 𝒜(U)` is étale with no hypothesis beyond the affineness of the two
charts.  That is the step which makes the assignment `U ↦ Spec(𝒜(U))` of
[Stacks Project, Tag 05ZT] an étale diagram.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.π_app_map_apply`: the naturality square of the
  reduction `𝒜 ⟶ 𝒪_X`, read on sections.
* `AlgebraicGeometry.Space.SquareZeroExtension.isBaseChange_ker_app_of_isAffine`: **the kernel
  ideal of the reduction over an affine object of the small étale site is the base change, along
  the restriction map of `𝒜`, of the kernel ideal over any affine object it maps to.**
* `AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isAffine`: **the sections of
  the extension sheaf over an affine object of the small étale site are an étale algebra over its
  sections over any affine object it maps to**, with no further hypothesis.

## Implementation notes

**Two steps, and where each is spent.**  Quasi-coherence of `ℐ` describes `ℐ(U)` as a base change
of `ℐ(V)` along `𝒪_X(V) ⟶ 𝒪_X(U)`, by
`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_isQuasicoherentOnSite`; the
conclusion asks for a base change of the *kernel ideals* along `𝒜(V) ⟶ 𝒜(U)`.  The change of
base ring is `Module.BaseChange.bijective_liftBaseChange_of_ker_le_map_ker`, whose one
non-formal hypothesis is `ker(𝒜(V) ⟶ 𝒪_X(V)) · 𝒜(U) = ker(𝒜(U) ⟶ 𝒪_X(U))`, and that identity is
proved here out of the *surjectivity* of the comparison for `ℐ`: a section of `𝒜(U)` killed by
the reduction is a section of `ℐ(U)` (`AlgebraicGeometry.Space.SquareZeroExtension.mem_ker_iff`),
hence a combination of restrictions of sections of `ℐ(V)` with coefficients in `𝒪_X(U)`, and
lifting those coefficients to `𝒜(U)` — which is where the surjectivity of the reduction over an
affine object is used — exhibits it inside the extended ideal.  The passage between `ℐ` and the
kernel ideals is
`AlgebraicGeometry.Space.SquareZeroExtension.idealAddEquivKer` together with
`AlgebraicGeometry.Space.SquareZeroExtension.idealToKer_naturality` and
`AlgebraicGeometry.Space.SquareZeroExtension.idealToKer_smul`.

**Why the action of `𝒜` on `ℐ` is built here and not assumed.**  `ℐ` carries its scalars over
`𝒪_X`, because the action of `𝒜` on it factors through the reduction — that is the field
`smul_lift`, and it is exactly the hypothesis `hpM` of
`Module.BaseChange.bijective_liftBaseChange_of_ker_le_map_ker`.  The `𝒜`-actions on `ℐ(V)` and
`ℐ(U)` are therefore `Module.compHom` along the reduction, built inside the proofs, and the
identity `hpM` holds by definition for them.

**The comparison is taken as data.**  `isBaseChange_ker_app_of_isAffine` asks for the comparison
`g` on the kernel ideals together with the identity describing it, so that the conclusion is
about a given map; in that form it is the last hypothesis of
`AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isBaseChange`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YT](https://stacks.math.columbia.edu/tag/05YT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The naturality square of the reduction of a square-zero extension, read on sections**:
restricting a section of `𝒜` along `h` and then reducing is reducing and then restricting. -/
theorem SquareZeroExtension.π_app_map_apply {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (a : E.A.obj.obj (op V)) :
    (E.π.hom.app (op U)).hom (E.A.obj.map h.op a) =
      ((smallEtaleRingedTopos B S hS X).O.obj.map h.op).hom
        ((E.π.hom.app (op V)).hom a) :=
  congrArg (fun k => k.hom a) (E.π.hom.naturality h.op)

/-- Reducing the image of a section under `algebraMap` is reducing and then restricting. -/
private theorem π_app_algebraMap_apply {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    [Algebra (E.A.obj.obj (op V)) (E.A.obj.obj (op U))]
    (halg : algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) = (E.A.obj.map h.op).hom)
    (a : E.A.obj.obj (op V)) :
    (E.π.hom.app (op U)).hom (algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) a) =
      ((smallEtaleRingedTopos B S hS X).O.obj.map h.op).hom
        ((E.π.hom.app (op V)).hom a) := by
  rw [halg]
  exact SquareZeroExtension.π_app_map_apply B S hS E h a

/-- **The kernel ideal of the reduction over an affine object of the small étale site is the base
change of the kernel ideal over any affine object it maps to**, along the restriction map of the
extension sheaf.

This is the identification `ℐ(U) = ℐ(V) ⊗_{𝒜(V)} 𝒜(U)` of [Stacks Project, Tag 05ZT], read on the
kernel ideals of the reduction, and it is the last hypothesis of
`AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isBaseChange`.

Quasi-coherence of `ℐ` gives the base change along `𝒪_X(V) ⟶ 𝒪_X(U)`
(`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_isQuasicoherentOnSite`), and
`Module.BaseChange.bijective_liftBaseChange_of_ker_le_map_ker` changes the base ring to
`𝒜(V) ⟶ 𝒜(U)`; its hypothesis `ker π_V · 𝒜(U) = ker π_U` is proved from the surjectivity of that
comparison together with the surjectivity of the reduction on an affine object
(`AlgebraicGeometry.Space.SquareZeroExtension.surjective_π_app_of_isAffine`). -/
theorem SquareZeroExtension.isBaseChange_ker_app_of_isAffine
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
    {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)))
    [Algebra (E.A.obj.obj (op V)) (E.A.obj.obj (op U))]
    (halg : algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) = (E.A.obj.map h.op).hom)
    (g : RingHom.ker (E.π.hom.app (op V)).hom →ₗ[E.A.obj.obj (op V)]
      RingHom.ker (E.π.hom.app (op U)).hom)
    (hg : ∀ x, ((g x : E.A.obj.obj (op U)) : E.A.obj.obj (op U)) =
      algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) (x : E.A.obj.obj (op V))) :
    IsBaseChange (E.A.obj.obj (op U)) g := by
  have hqsurj := SquareZeroExtension.surjective_π_app_of_isAffine B S hS E U hU
  have hcomm := π_app_algebraMap_apply B S hS E h halg
  -- The structure-sheaf side: quasi-coherence of `ℐ` over the two affine charts.
  let algO : Algebra ((smallEtaleRingedTopos B S hS X).O.obj.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U)) :=
    ((smallEtaleRingedTopos B S hS X).O.obj.map h.op).hom.toAlgebra
  let mIV : Module ((smallEtaleRingedTopos B S hS X).O.obj.obj (op V))
      (E.I.val.obj (op V)) := inferInstanceAs (Module
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op V))
    (E.I.val.obj (op V)))
  let mIU : Module ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U))
      (E.I.val.obj (op U)) := inferInstanceAs (Module
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op U))
    (E.I.val.obj (op U)))
  let mIUV : Module ((smallEtaleRingedTopos B S hS X).O.obj.obj (op V))
      (E.I.val.obj (op U)) := Module.compHom _
    (algebraMap ((smallEtaleRingedTopos B S hS X).O.obj.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U)))
  have twI : IsScalarTower ((smallEtaleRingedTopos B S hS X).O.obj.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U)) (E.I.val.obj (op U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let rI : E.I.val.obj (op V) →ₗ[(smallEtaleRingedTopos B S hS X).O.obj.obj (op V)]
      E.I.val.obj (op U) :=
    { toFun := fun n => E.I.val.map h.op n
      map_add' := map_add (E.I.val.map h.op).hom
      map_smul' := fun c n => E.I.val.map_smul h.op c n }
  have hbc : Function.Bijective (rI.liftBaseChange
      ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U))) :=
    SmallEtale.bijective_liftBaseChange_of_isQuasicoherentOnSite B S hS X.1 X.2 E.I
      E.quasicoherent h hV hU ((smallEtaleRingedTopos B S hS X).O.obj.obj (op V))
      ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U)) (algAB := algO)
      (RingEquiv.refl _) (fun _ _ => rfl) (RingEquiv.refl _)
      (fun _ _ => rfl) (fun _ => rfl) rI fun _ => rfl
  -- The extension-sheaf side: the action of `𝒜` on `ℐ` through the reduction.
  let mAV : Module (E.A.obj.obj (op V)) (E.I.val.obj (op V)) :=
    Module.compHom _ (E.π.hom.app (op V)).hom
  let mAU : Module (E.A.obj.obj (op U)) (E.I.val.obj (op U)) :=
    Module.compHom _ (E.π.hom.app (op U)).hom
  let mAVU : Module (E.A.obj.obj (op V)) (E.I.val.obj (op U)) :=
    Module.compHom _ (algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)))
  have twA : IsScalarTower (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) (E.I.val.obj (op U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let gI : E.I.val.obj (op V) →ₗ[E.A.obj.obj (op V)] E.I.val.obj (op U) :=
    { toFun := rI
      map_add' := map_add rI
      map_smul' := fun a x => by
        change rI ((E.π.hom.app (op V)).hom a • x) =
          (E.π.hom.app (op U)).hom
            (algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) a) • rI x
        rw [hcomm a]
        exact map_smul rI _ x }
  -- The kernel ideal over `U` is generated by the kernel ideal over `V`.
  have hker : RingHom.ker (E.π.hom.app (op U)).hom ≤
      Ideal.map (algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)))
        (RingHom.ker (E.π.hom.app (op V)).hom) := by
    intro b hb
    obtain ⟨y, rfl⟩ := (SquareZeroExtension.mem_ker_iff B S hS E (op U) b).mp hb
    obtain ⟨z, rfl⟩ := hbc.2 y
    clear hb
    induction z with
    | zero =>
      rw [map_zero]
      exact (congrArg (· ∈ _) (map_zero (E.ι (op U)))).mpr (zero_mem _)
    | tmul c x =>
      obtain ⟨b, rfl⟩ := hqsurj c
      have key : E.ι (op U) ((rI.liftBaseChange
          ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U)))
            ((E.π.hom.app (op U)).hom b ⊗ₜ x)) =
          b * algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) (E.ι (op V) x) := by
        rw [LinearMap.liftBaseChange_tmul]
        refine (E.smul_lift (op U) b (rI x)).trans ?_
        rw [halg]
        exact congrArg (b * ·) (E.naturality h.op x)
      rw [key]
      exact Ideal.mul_mem_left _ _
        (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr (E.mem_kernel (op V) x)))
    | add z z' hz hz' =>
      rw [map_add]
      exact (congrArg (· ∈ _) (map_add (E.ι (op U)) _ _)).mpr (add_mem hz hz')
  -- The change of base ring, and the identification of `ℐ` with the kernel ideals.
  have hbcA : Function.Bijective (gI.liftBaseChange (E.A.obj.obj (op U))) :=
    Module.BaseChange.bijective_liftBaseChange_of_ker_le_map_ker
      (E.π.hom.app (op V)).hom (E.π.hom.app (op U)).hom
      (SquareZeroExtension.surjective_π_app_of_isAffine B S hS E V hV) hqsurj hcomm
      (fun _ _ => rfl) (fun _ _ => rfl) hker rI gI (fun _ => rfl) hbc
  let eV : E.I.val.obj (op V) ≃ₗ[E.A.obj.obj (op V)]
      RingHom.ker (E.π.hom.app (op V)).hom :=
    { SquareZeroExtension.idealAddEquivKer B S hS E (op V) with
      map_smul' := fun a x => SquareZeroExtension.idealToKer_smul B S hS E (op V) a x }
  let eU : E.I.val.obj (op U) ≃ₗ[E.A.obj.obj (op U)]
      RingHom.ker (E.π.hom.app (op U)).hom :=
    { SquareZeroExtension.idealAddEquivKer B S hS E (op U) with
      map_smul' := fun a x => SquareZeroExtension.idealToKer_smul B S hS E (op U) a x }
  have htr : ∀ n : RingHom.ker (E.π.hom.app (op V)).hom,
      eU.symm (g n) = gI (eV.symm n) := fun n => by
    rw [eU.symm_apply_eq]
    apply Subtype.ext
    rw [hg n]
    change algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) (n : E.A.obj.obj (op V)) =
      E.ι (op U) (E.I.val.map h.op (eV.symm n))
    rw [E.naturality h.op (eV.symm n), halg]
    exact congrArg (fun t : E.A.obj.obj (op V) => E.A.obj.map h.op t)
      (congrArg Subtype.val (eV.apply_symm_apply n)).symm
  exact Stacks.FlatSectionsDescent.isBaseChange_of_bijective_liftBaseChange g
    (Module.BaseChange.bijective_liftBaseChange_of_comm g gI eV.symm eU.symm htr hbcA)

/-- **The sections of a square-zero extension of the structure sheaf over an affine object of the
small étale site are an étale algebra over its sections over any affine object it maps to**, with
no hypothesis beyond the affineness of the two charts.

This is the étaleness of `Spec(𝒜(U)) ⟶ Spec(𝒜(V))` that makes the chart diagram
`U ↦ Spec(𝒜(U))` of [Stacks Project, Tag 05ZT] an étale diagram, with every hypothesis of
`AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isBaseChange` discharged: its
base-change hypothesis is
`AlgebraicGeometry.Space.SquareZeroExtension.isBaseChange_ker_app_of_isAffine`, applied to the
comparison carrying a section of the kernel ideal over `V` to its image in `𝒜(U)`. -/
theorem SquareZeroExtension.algebraEtale_app_of_isAffine
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
    {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)))
    [Algebra (E.A.obj.obj (op V)) (E.A.obj.obj (op U))]
    (halg : algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) = (E.A.obj.map h.op).hom) :
    Algebra.Etale (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) := by
  have hcomm := π_app_algebraMap_apply B S hS E h halg
  let g : RingHom.ker (E.π.hom.app (op V)).hom →ₗ[E.A.obj.obj (op V)]
      RingHom.ker (E.π.hom.app (op U)).hom :=
    { toFun := fun x => ⟨algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U))
        (x : E.A.obj.obj (op V)), by
          rw [RingHom.mem_ker, hcomm, RingHom.mem_ker.mp x.2, map_zero]⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun a x => Subtype.ext (by
        change algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U))
            (a * (x : E.A.obj.obj (op V))) =
          a • algebraMap (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) (x : E.A.obj.obj (op V))
        rw [Algebra.smul_def, map_mul]) }
  exact SquareZeroExtension.algebraEtale_app_of_isBaseChange B S hS E h hU hV halg g
    (fun _ => rfl)
    (SquareZeroExtension.isBaseChange_ker_app_of_isAffine B S hS E h hU hV halg g fun _ => rfl)

end AlgebraicGeometry.Space

end
