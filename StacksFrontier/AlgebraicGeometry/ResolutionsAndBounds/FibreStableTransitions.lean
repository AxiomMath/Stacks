module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.PerfectFibreBands

/-!
# Stability of the kernels under a transition map

Let `S` be affine and Jacobson, let `X` and `Y` be locally of finite type over `S` with `X` and
`X ×_S Y` locally Noetherian, and let `τ : K ⟶ K'` be a morphism of perfect objects of
`D(𝒪_{X ×_S Y})` whose cohomology vanishes above a degree `m ≥ 0`. Suppose that for every
coherent `𝒪_X`-module `𝓕` with zero-dimensional support the cohomology of the integral transform
`R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 K)` is concentrated in `[-m, m] ∪ [-m-n, m-n]`, that the same holds for
`K'` with the band `[-m-n-1, m-n-1]` in place of `[-m-n, m-n]`, and that `τ` is an isomorphism on
the cohomology of these transforms throughout `[-m, m]`. Part (2) of [Stacks, Tag 0FZ9] asserts
that for `n > 2m` the map `τ` is then an isomorphism on the cohomology sheaves of the kernels
themselves throughout `[-m, m]`.

## Main results

* `AlgebraicGeometry.isIso_homologyMap_of_fibreStable`: part (2) of [Stacks, Tag 0FZ9].
* `AlgebraicGeometry.isZero_homology_fibreTransform_obj₃`: the transform of the third vertex of a
  distinguished triangle has vanishing cohomology in `[-m-1, m]` when the first map is invertible
  on the transforms throughout `[-m, m]` and the transforms of the first two vertices vanish in
  the degrees `m+1` and `-m-1`.
* `AlgebraicGeometry.isZero_homology_obj₃_of_epi_of_mono`: the third vertex of a distinguished
  triangle has vanishing cohomology in a degree where the first morphism is onto and is injective
  one degree up.

## Implementation notes

*The model of the derived categories.* Everything is read at
`CategoryTheory.HasDerivedCategory.standard`, the model at which `AlgebraicGeometry.fourierMukai`
is defined.

*Exactness of the transform in the kernel.* The integral transform of a fixed module, read as a
functor of the kernel, is `AlgebraicGeometry.fibreTransformFunctor`, a composite of the derived
tensor product of [Stacks, Tag 06YU] in one variable with the derived direct image of
[Stacks, Tag 079W]. Both factors commute with the shift and are exact, so the composite is, and
the cone triangle of `τ` therefore transforms to a distinguished triangle.

*The two spellings of [Stacks, Tag 08CM].* Perfectness of the cone comes from
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished`, stated for
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, while the reflection step reads
`AlgebraicGeometry.RingedSpace.IsPerfect`; the two definitions agree, and
`AlgebraicGeometry.isPerfect_obj₃_scheme` performs the identification once.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Stacks Set
open TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Cancellation against a zero object -/

/-- A morphism into a zero object is an epimorphism. -/
public theorem epi_of_isZero_target {A : Type*} [Category A] {Z W : A} (hW : IsZero W)
    (a : Z ⟶ W) : Epi a :=
  ⟨fun _ _ _ => hW.eq_of_src _ _⟩

/-- A morphism out of a zero object is a monomorphism. -/
public theorem mono_of_isZero_source {A : Type*} [Category A] {Z W : A} (hZ : IsZero Z)
    (a : Z ⟶ W) : Mono a :=
  ⟨fun _ _ _ => hZ.eq_of_tgt _ _⟩

/-! ### A vanishing criterion on the third vertex of a distinguished triangle -/

section Triangles

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A)) (n₀ n₁ : ℤ)
  (h : n₀ + 1 = n₁)

include hT h

/-- **The third vertex of a distinguished triangle has vanishing cohomology in a degree where the
first morphism is onto and is injective one degree up.** -/
public theorem isZero_homology_obj₃_of_epi_of_mono
    (he : Epi ((DerivedCategory.homologyFunctor A n₀).map T.mor₁))
    (hm : Mono ((DerivedCategory.homologyFunctor A n₁).map T.mor₁)) :
    IsZero ((DerivedCategory.homologyFunctor A n₀).obj T.obj₃) :=
  have : Epi ((DerivedCategory.homologyFunctor A n₀).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT n₀ n₁ h).2
      ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT n₀ n₁ h).1 hm)
  IsZero.of_epi_eq_zero _
    ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT n₀).1 he)

end Triangles

/-! ### Perfectness of the third vertex, in the scheme spelling -/

/-- **[Stacks, Tag 08CR] for the third vertex**, read for the category of modules on a scheme:
the third vertex of a distinguished triangle is perfect if the first two are. -/
public theorem isPerfect_obj₃_scheme {W : Scheme.{u}}
    (T : Triangle (DerivedCategory W.Modules))
    (hT : T ∈ distTriang (DerivedCategory W.Modules))
    (h₁ : RingedSpace.IsPerfect (X := W.toRingedSpace) T.obj₁)
    (h₂ : RingedSpace.IsPerfect (X := W.toRingedSpace) T.obj₂) :
    RingedSpace.IsPerfect (X := W.toRingedSpace) T.obj₃ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    (X := W.toRingedSpace) T hT h₁ h₂

/-! ### The transform of a fixed module as an exact functor of the kernel -/

section Transform

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct derivedTensorProductFunctor)

attribute [local instance] AlgebraicGeometry.commShift_pushforward
  AlgebraicGeometry.isTriangulated_pushforward

/-- `pr_1^*𝓕 ⊗^𝐋 -`, the derived tensor product with the pullback along `pr₁` of a fixed
`𝒪_X`-module, as an endofunctor of `D(𝒪_{X ×_S Y})`. This is the first factor of
`AlgebraicGeometry.fibreTransformFunctor`. -/
public abbrev fibreTensorFunctor (F : X.Modules) :
    DerivedCategory (Limits.pullback f g).Modules ⥤
      DerivedCategory (Limits.pullback f g).Modules :=
  (derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).obj
    ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F))

/-- `pr_1^*𝓕 ⊗^𝐋 -` commutes with the shift, by [Stacks, Tag 06YU]. -/
local instance commShift_fibreTensor (F : X.Modules) :
    (fibreTensorFunctor f g F).CommShift ℤ :=
  (canonicalDerivedTensorProduct (Limits.pullback f g).toRingedSpace.sheaf).commShift_right _

/-- `pr_1^*𝓕 ⊗^𝐋 -` is exact, by [Stacks, Tag 06YU]. -/
local instance isTriangulated_fibreTensor (F : X.Modules) :
    (fibreTensorFunctor f g F).IsTriangulated :=
  (canonicalDerivedTensorProduct (Limits.pullback f g).toRingedSpace.sheaf).exact_right _

/-- The integral transform read as a functor of the kernel is the derived tensor product with
`pr_1^*𝓕` followed by the derived direct image along `pr₂`. -/
public theorem fibreTransformFunctor_eq (F : X.Modules) :
    fibreTransformFunctor f g F = fibreTensorFunctor f g F ⋙ fourierMukaiPushforward f g :=
  rfl

/-- The integral transform read as a functor of the kernel takes at a kernel the value the
integral transform by that kernel has. -/
public theorem fibreTransformFunctor_obj (K : DerivedCategory (Limits.pullback f g).Modules)
    (F : X.Modules) : (fibreTransformFunctor f g F).obj K = fibreTransform f g K F :=
  rfl

/-- **The transform of the third vertex of a distinguished triangle vanishes throughout
`[-m-1, m]`** as soon as the first morphism is invertible on the transforms throughout `[-m, m]`
and the transforms of the first two vertices vanish in the degrees `m+1` and `-m-1`. -/
public theorem isZero_homology_fibreTransform_obj₃
    (T : Triangle (DerivedCategory (Limits.pullback f g).Modules))
    (hT : T ∈ distTriang (DerivedCategory (Limits.pullback f g).Modules))
    (F : X.Modules) (m : ℕ)
    (hhigh : IsZero ((DerivedCategory.homologyFunctor Y.Modules ((m : ℤ) + 1)).obj
      (fibreTransform f g T.obj₁ F)))
    (hlow : IsZero ((DerivedCategory.homologyFunctor Y.Modules (-(m : ℤ) - 1)).obj
      (fibreTransform f g T.obj₂ F)))
    (hstable : ∀ j : ℤ, -(m : ℤ) ≤ j → j ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor Y.Modules j).map
        ((fibreTransformFunctor f g F).map T.mor₁)))
    (j : ℤ) (hj₁ : -(m : ℤ) - 1 ≤ j) (hj₂ : j ≤ (m : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj
      (fibreTransform f g T.obj₃ F)) := by
  have he : Epi ((DerivedCategory.homologyFunctor Y.Modules j).map
      ((fibreTransformFunctor f g F).map T.mor₁)) := by
    obtain rfl | hlt := hj₁.eq_or_lt
    · exact epi_of_isZero_target hlow _
    · have := hstable j (by omega) hj₂
      infer_instance
  have hm : Mono ((DerivedCategory.homologyFunctor Y.Modules (j + 1)).map
      ((fibreTransformFunctor f g F).map T.mor₁)) := by
    obtain rfl | hlt := hj₂.eq_or_lt
    · exact mono_of_isZero_source hhigh _
    · have := hstable (j + 1) (by omega) (by omega)
      infer_instance
  exact isZero_homology_obj₃_of_epi_of_mono _
    ((fibreTensorFunctor f g F ⋙ fourierMukaiPushforward f g).map_distinguished T hT)
    j (j + 1) rfl he hm

/-! ### Part (2) of the tag -/

variable [IsAffine S] [JacobsonSpace ↥S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
  [IsLocallyNoetherian X] [IsLocallyNoetherian (Limits.pullback f g)]

/-- Let `τ : K ⟶ K'` be a morphism of perfect objects of `D(𝒪_{X ×_S Y})` with cohomology
vanishing above `m`, let the cohomology of the integral transforms of the coherent modules with
zero-dimensional support be concentrated in `[-m, m] ∪ [-m-n, m-n]` for `K` and in
`[-m, m] ∪ [-m-n-1, m-n-1]` for `K'`, and let `τ` be an isomorphism on the cohomology of those
transforms throughout `[-m, m]`. If `n > 2m` then `τ` is an isomorphism on the cohomology sheaves
of the kernels throughout `[-m, m]`. -/
@[stacks 0FZ9 "part (2), the transition map is invertible on the cohomology of the kernels in \
[-m, m] once n > 2m, with the general derived-tensor comparisons carried as \
FibreTensorComparisons"]
public theorem isIso_homologyMap_of_fibreStable (cmp : FibreTensorComparisons f g)
    (K K' : DerivedCategory (Limits.pullback f g).Modules) (τ : K ⟶ K')
    (hK : RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (hK' : RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) K') (m n : ℕ)
    (hupper : ∀ j : ℤ, (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K))
    (hupper' : ∀ j : ℤ, (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K'))
    (hband : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ j : ℤ, ¬ InBands m n j →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj (fibreTransform f g K F)))
    (hband' : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ j : ℤ, ¬ InBands m (n + 1) j →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj (fibreTransform f g K' F)))
    (hstable : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ j : ℤ, -(m : ℤ) ≤ j → j ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor Y.Modules j).map
        ((fibreTransformFunctor f g F).map τ)))
    (hn : 2 * m < n) (i : ℤ) (hi₁ : -(m : ℤ) ≤ i) (hi₂ : i ≤ (m : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).map τ) := by
  obtain ⟨C, ι, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle τ
  set T : Triangle (DerivedCategory (Limits.pullback f g).Modules) :=
    Pretriangulated.Triangle.mk τ ι δ
  have hhigh : ¬ InBands m n ((m : ℤ) + 1) := by
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> omega
  have hlow : ¬ InBands m (n + 1) (-(m : ℤ) - 1) := by
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> omega
  have hC : RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) C :=
    isPerfect_obj₃_scheme T hT hK hK'
  have hupperC : ∀ j : ℤ, (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj C) :=
    fun j hj => isZero_homology_obj₃_of_isZero T hT j (j + 1) rfl (hupper' j hj)
      (hupper (j + 1) (by omega))
  have hCvan : ∀ j : ℤ, -(m : ℤ) - 1 ≤ j → j ≤ (m : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj C) := by
    intro j hj₁ hj₂
    refine isZero_homology_of_isZero_homology_fibreTransform f g cmp C hC (m : ℤ) hupperC j ?_
    intro F hF hdim
    exact isZero_homology_fibreTransform_obj₃ f g T hT F m
      (hband F hF hdim ((m : ℤ) + 1) hhigh) (hband' F hF hdim (-(m : ℤ) - 1) hlow)
      (fun l hl₁ hl₂ => hstable F hF hdim l hl₁ hl₂) j hj₁ hj₂
  exact isIso_homologyMap_mor₁_of_isZero T hT (i - 1) i (by omega)
    (hCvan (i - 1) (by omega) (by omega)) (hCvan i (by omega) (by omega))

end Transform

end AlgebraicGeometry

end
