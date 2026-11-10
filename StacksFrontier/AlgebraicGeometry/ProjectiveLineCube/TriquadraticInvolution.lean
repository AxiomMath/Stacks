module

public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.ThirdFactor
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.TriquadraticSurface
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.OtherRootInvolution

/-!
# The covering involution of a triquadratic surface

Let `X = Z(F) ⊂ S × ℙ¹ × ℙ¹ × ℙ¹` be the triquadratic surface of an integer array `coef`
(`AlgebraicGeometry.projectiveLineCube.triquadraticSurface`), cut out by
`F = A₀ z₀² + A₁ z₀ z₁ + A₂ z₁²` with `A₀, A₁, A₂` biquadratic forms in the first two factors and
`z₀, z₁` the coordinates of the third. If `A₀, A₁, A₂` have no common zero, the projection of `X`
to `S × ℙ¹ × ℙ¹` is a family of binary quadrics and `X` carries the covering involution `σ`
exchanging the two roots over each point: it is the identity on the first two factors and the
other root `(-(A₁ z₁ + A₀ z₀) : A₀ z₁) = (A₂ z₀ : -(A₁ z₀ + A₂ z₁))` on the third. It satisfies
`σ ∘ σ = id`, `σ^*𝓗₀ ≅ 𝓗₀`, `σ^*𝓗₁ ≅ 𝓗₁` and `σ^*𝓗₂ ⊗ 𝓗₂² ≅ M ⊗ 𝓗₂` for `M = 𝓗₀² ⊗ 𝓗₁²`, so
numerically `σ^*𝓗₂ + 𝓗₂ ≡ 2𝓗₀ + 2𝓗₁`.

The involution is `Stacks.BinaryQuadric.quadricInvolution` for the decomposition
`S × ℙ¹ × ℙ¹ × ℙ¹ = (S × ℙ¹ × ℙ¹) × ℙ¹`.

## Main definitions

* `AlgebraicGeometry.projectiveLineCube.triquadraticCoefficientTuple`: `(M, (A₀, A₁, A₂))`.
* `AlgebraicGeometry.projectiveLineCube.thirdCoordinateTuple`: `(𝓗₂, (z₀, z₁))`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticSurfaceInvolution`: the covering involution,
  and `triquadraticSurfaceInvolutionIso` the automorphism it defines.
* `AlgebraicGeometry.projectiveLineCube.triquadraticSurfaceInvolutionLineBundleIso`:
  `σ^*(𝓗ᵢ|_X) ≅ 𝓗ᵢ|_X` for `i = 0, 1`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticSurfaceInvolutionTwistIso`:
  `σ^*𝓗₂ ⊗ 𝓗₂² ≅ M ⊗ 𝓗₂`.

## Main results

* `AlgebraicGeometry.projectiveLineCube.isDeterminedBy_triquadraticCoefficientTuple`: the
  coefficients only depend on the first two factors.
* `AlgebraicGeometry.projectiveLineCube.quadric_triquadraticCoefficientTuple`: the triquadratic
  surface is the quadric of `Stacks.BinaryQuadric.quadric`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticSurfaceInvolution_comp_self`: `σ ∘ σ = id`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticSurfaceInvolution_ι_proj`,
  `triquadraticSurfaceInvolution_toBase`: `σ` is the identity on the first two factors and a
  morphism over `S`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticSurfaceInvolution_ι_proj_two`: on the third
  factor `σ` is the other root.

## References

* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.ProjectiveSpaceModuli Stacks.InvertibleStalk Stacks.BinaryQuadric

universe u

namespace AlgebraicGeometry

namespace projectiveLineCube

attribute [local instance] MvPolynomial.gradedAlgebra

variable (S : Scheme.{u})

/-! ### Coordinates of biquadratic forms -/

/-- A homogeneous coordinate of `ℙ¹_ℤ` not vanishing at the image of `x` under `h`. -/
def lineFrameIndex {T : Scheme.{u}} (h : T ⟶ projectiveSpaceAtUniverse.{u} 1) (x : T) : Fin 2 :=
  (exists_mem_nonvanishingLocus_coordGlobalSection (h x)).choose

/-- The chosen homogeneous coordinate does not vanish at the image of `x`. -/
theorem mem_nonvanishingLocus_lineFrameIndex {T : Scheme.{u}}
    (h : T ⟶ projectiveSpaceAtUniverse.{u} 1) (x : T) :
    h x ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 1)
      (Stacks.TwistPullbackPinned.coordGlobalSection.{u} 1 (lineFrameIndex h x)) :=
  (exists_mem_nonvanishingLocus_coordGlobalSection (h x)).choose_spec

/-- The coordinates at `x` of the pair attached to `h : T ⟶ ℙ¹_ℤ`, relative to the member
`lineFrameIndex h x`. -/
def lineCoord {T : Scheme.{u}} (h : T ⟶ projectiveSpaceAtUniverse.{u} 1) (x : T) :
    Fin 2 → T.presheaf.stalk x :=
  tupleCoord (tautological h)
    (mem_nonvanishingLocus_pullbackGlobalSections h (mem_nonvanishingLocus_lineFrameIndex h x))

/-- The biquadratic form `∑ a i j · mᵢ(l₀) mⱼ(l₁)` evaluated at two pairs `l₀, l₁`, with
`m₀, m₁, m₂` the quadratic monomials. -/
def biquadraticPoly {R : Type*} [CommRing R] (a : Fin 3 → Fin 3 → ℤ) (l₀ l₁ : Fin 2 → R) : R :=
  ∑ i, ∑ j, (a i j : R) * ((l₀ (quadraticFirst i) * l₀ (quadraticSecond i)) *
    (l₁ (quadraticFirst j) * l₁ (quadraticSecond j)))

/-- The biquadratic form commutes with ring homomorphisms. -/
theorem map_biquadraticPoly {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (a : Fin 3 → Fin 3 → ℤ) (l₀ l₁ : Fin 2 → R) :
    φ (biquadraticPoly a l₀ l₁) = biquadraticPoly a (fun i => φ (l₀ i)) (fun i => φ (l₁ i)) := by
  simp only [biquadraticPoly, map_sum, map_mul, map_intCast]

/-- The coordinate sections of the pencils are those of the tautological pairs of the projections,
as elements of `Γ(𝓗ᵢ, ⊤)`. -/
theorem quadraticMonomial_eval_top (i k : Fin 3) :
    (quadraticMonomial S i k).eval (op ⊤) =
      Stacks.SheafOfModules.tensorSectionsAt (projectiveLineCube S).sheaf.obj
        (projectiveLineCube S).ringCatSheaf.property (op ⊤) (lineBundle S i) (lineBundle S i)
        ((tautological (cubeProduct.proj S _ i)).coord (quadraticFirst k))
        ((tautological (cubeProduct.proj S _ i)).coord (quadraticSecond k)) := by
  change Stacks.SheafOfModules.tensorSectionsAt _ _ (op ⊤) _ _ ((coordinate S i _).eval (op ⊤))
    ((coordinate S i _).eval (op ⊤)) = _
  rw [coordinate_eval_top, coordinate_eval_top]
  rfl

variable {S} {T : Scheme.{u}} (f : T ⟶ projectiveLineCube S) (x : T)

/-- The member of the coordinates of the `K`-th pencil chosen not to vanish at `f x`. -/
theorem mem_nonvanishingLocus_pencilFrame (K : Fin 3) :
    f x ∈ Stacks.Ample.nonvanishingLocus (lineBundle S K)
      ((tautological (cubeProduct.proj S _ K)).coord
        (lineFrameIndex (f ≫ cubeProduct.proj S _ K) x)) :=
  mem_nonvanishingLocus_pullbackGlobalSections _
    (mem_nonvanishingLocus_lineFrameIndex (f ≫ cubeProduct.proj S _ K) x)

/-- The coordinates at `f x` of the coordinate sections of the `K`-th pencil, relative to the
chosen member, are the coordinates of the pair attached to `f ≫ prₖ` after `f^♯`. -/
theorem map_stalkCoord_pencil (K : Fin 3) (a : Fin 2) :
    (f.stalkMap x).hom (stalkCoord _ (mem_nonvanishingLocus_pencilFrame f x K)
        ((tautological (cubeProduct.proj S _ K)).coord a)) =
      lineCoord (f ≫ cubeProduct.proj S _ K) x a := by
  refine (congrArg _ (stalkCoord_tautological_coord (cubeProduct.proj S _ K)
    (mem_nonvanishingLocus_lineFrameIndex (f ≫ cubeProduct.proj S _ K) x) a)).trans ?_
  refine Eq.trans ?_ (stalkCoord_tautological_coord (f ≫ cubeProduct.proj S _ K)
    (mem_nonvanishingLocus_lineFrameIndex (f ≫ cubeProduct.proj S _ K) x) a).symm
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- The frame of `𝓗ₖ ⊗ 𝓗ₖ` at `f x` built from the chosen coordinates. -/
theorem mem_nonvanishingLocus_quadraticFrame (K : Fin 3) :
    f x ∈ Stacks.Ample.nonvanishingLocus (lineBundleSq S K)
      (Stacks.SheafOfModules.tensorSectionsAt (projectiveLineCube S).sheaf.obj
        (projectiveLineCube S).ringCatSheaf.property (op ⊤) (lineBundle S K) (lineBundle S K)
        ((tautological (cubeProduct.proj S _ K)).coord
          (lineFrameIndex (f ≫ cubeProduct.proj S _ K) x))
        ((tautological (cubeProduct.proj S _ K)).coord
          (lineFrameIndex (f ≫ cubeProduct.proj S _ K) x))) :=
  mem_nonvanishingLocus_tensorSectionsAt (mem_nonvanishingLocus_pencilFrame f x K)
    (mem_nonvanishingLocus_pencilFrame f x K)

/-- The frame of `M = 𝓗₀² ⊗ 𝓗₁²` at `f x` built from the chosen coordinates. -/
theorem mem_nonvanishingLocus_biquadraticFrame :
    f x ∈ Stacks.Ample.nonvanishingLocus (biquadraticModule S)
      (Stacks.SheafOfModules.tensorSectionsAt (projectiveLineCube S).sheaf.obj
        (projectiveLineCube S).ringCatSheaf.property (op ⊤) (lineBundleSq S 0) (lineBundleSq S 1)
        (Stacks.SheafOfModules.tensorSectionsAt (projectiveLineCube S).sheaf.obj
          (projectiveLineCube S).ringCatSheaf.property (op ⊤) (lineBundle S 0) (lineBundle S 0)
          ((tautological (cubeProduct.proj S _ 0)).coord
            (lineFrameIndex (f ≫ cubeProduct.proj S _ 0) x))
          ((tautological (cubeProduct.proj S _ 0)).coord
            (lineFrameIndex (f ≫ cubeProduct.proj S _ 0) x)))
        (Stacks.SheafOfModules.tensorSectionsAt (projectiveLineCube S).sheaf.obj
          (projectiveLineCube S).ringCatSheaf.property (op ⊤) (lineBundle S 1) (lineBundle S 1)
          ((tautological (cubeProduct.proj S _ 1)).coord
            (lineFrameIndex (f ≫ cubeProduct.proj S _ 1) x))
          ((tautological (cubeProduct.proj S _ 1)).coord
            (lineFrameIndex (f ≫ cubeProduct.proj S _ 1) x)))) :=
  mem_nonvanishingLocus_tensorSectionsAt (mem_nonvanishingLocus_quadraticFrame f x 0)
    (mem_nonvanishingLocus_quadraticFrame f x 1)

/-- The coordinate of a quadratic monomial. -/
theorem stalkCoord_quadraticMonomial (K k : Fin 3) :
    stalkCoord _ (mem_nonvanishingLocus_quadraticFrame f x K)
        ((quadraticMonomial S K k).eval (op ⊤)) =
      stalkCoord _ (mem_nonvanishingLocus_pencilFrame f x K)
          ((tautological (cubeProduct.proj S _ K)).coord (quadraticFirst k)) *
        stalkCoord _ (mem_nonvanishingLocus_pencilFrame f x K)
          ((tautological (cubeProduct.proj S _ K)).coord (quadraticSecond k)) :=
  (congrArg (stalkCoord _ (mem_nonvanishingLocus_quadraticFrame f x K))
    (quadraticMonomial_eval_top S K k)).trans (stalkCoord_tensorSectionsAt _ _ _ _)

/-- **The coordinate of the pullback of a biquadratic form** is the biquadratic form evaluated at
the coordinates of the pairs attached to the first two components of `f`. -/
theorem stalkCoord_pullbackGlobalSections_biquadraticSection (a : Fin 3 → Fin 3 → ℤ) :
    stalkCoord _ (mem_nonvanishingLocus_pullbackGlobalSections f
        (mem_nonvanishingLocus_biquadraticFrame f x))
      (pullbackGlobalSections f _ (biquadraticSection S a)) =
      biquadraticPoly a (lineCoord (f ≫ cubeProduct.proj S _ 0) x)
        (lineCoord (f ≫ cubeProduct.proj S _ 1) x) := by
  refine (stalkCoord_pullbackGlobalSections f (mem_nonvanishingLocus_biquadraticFrame f x)
    _).trans ?_
  have hb : stalkCoord _ (mem_nonvanishingLocus_biquadraticFrame f x) (biquadraticSection S a) =
      ∑ i, ∑ j, (a i j : (projectiveLineCube S).presheaf.stalk (f x)) *
        ((stalkCoord _ (mem_nonvanishingLocus_pencilFrame f x 0)
            ((tautological (cubeProduct.proj S _ 0)).coord (quadraticFirst i)) *
          stalkCoord _ (mem_nonvanishingLocus_pencilFrame f x 0)
            ((tautological (cubeProduct.proj S _ 0)).coord (quadraticSecond i))) *
         (stalkCoord _ (mem_nonvanishingLocus_pencilFrame f x 1)
            ((tautological (cubeProduct.proj S _ 1)).coord (quadraticFirst j)) *
          stalkCoord _ (mem_nonvanishingLocus_pencilFrame f x 1)
            ((tautological (cubeProduct.proj S _ 1)).coord (quadraticSecond j)))) := by
    refine (stalkCoord_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (stalkCoord_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    refine (stalkCoord_zsmul _ _ _).trans ?_
    rw [zsmul_eq_mul]
    congr 1
    exact (stalkCoord_tensorSectionsAt _ _ _ _).trans (congrArg₂ (· * ·)
      (stalkCoord_quadraticMonomial f x 0 i) (stalkCoord_quadraticMonomial f x 1 j))
  rw [hb]
  simp only [map_sum, map_mul, map_intCast, map_stalkCoord_pencil, biquadraticPoly]

/-! ### The covering involution -/

variable (S)

/-- The coordinates `(z₀, z₁)` of the third factor, as an invertible module with two generating
sections: the pair attached to the third projection. -/
def thirdCoordinateTuple : GeneratingTuple (projectiveLineCube S) 1 where
  bundle := lineBundle S 2
  isInvertible := inferInstance
  coord := thirdCoordinate S
  generates := by
    have h : thirdCoordinate S = (tautological (cubeProduct.proj S _ 2)).coord :=
      funext (coordinate_eval_top S 2)
    exact h ▸ (tautological (cubeProduct.proj S _ 2)).generates

/-- The coordinate pair of the third factor is the tautological pair of the third projection. -/
theorem isomorphic_thirdCoordinateTuple :
    Isomorphic (thirdCoordinateTuple S) (tautological (cubeProduct.proj S _ 2)) :=
  ⟨Iso.refl _, coordinate_eval_top S 2⟩

variable (coef : Fin 3 → Fin 3 → Fin 3 → ℤ)
  (hgen : Stacks.ProjectiveFromSections.GeneratesStalks (triquadraticCoefficient coef S))

/-- The three biquadratic coefficients `A₀, A₁, A₂` of the triquadratic form of `coef`, as an
invertible module with three generating sections (the hypothesis `hgen` that they have no common
zero). -/
def triquadraticCoefficientTuple : GeneratingTuple (projectiveLineCube S) 2 where
  bundle := biquadraticModule S
  isInvertible := inferInstance
  coord := triquadraticCoefficient coef S
  generates := hgen

/-- **The coefficients of a triquadratic form do not depend on the third factor**: they are
determined by the projection `S × ℙ¹ × ℙ¹ × ℙ¹ ⟶ S × ℙ¹ × ℙ¹`. At every point the coordinates of
their pullback along `f` only depend on the first two components of `f`. -/
theorem isDeterminedBy_triquadraticCoefficientTuple :
    (triquadraticCoefficientTuple S coef hgen).IsDeterminedBy
      (cubeProduct.forgetThird S (projectiveSpaceAtUniverse.{u} 1)) := by
  intro T f g e
  have h₀ : f ≫ cubeProduct.proj S _ 0 = g ≫ cubeProduct.proj S _ 0 := by
    rw [← cubeProduct.forgetThird_snd_fst, reassoc_of% e]
  have h₁ : f ≫ cubeProduct.proj S _ 1 = g ≫ cubeProduct.proj S _ 1 := by
    rw [← cubeProduct.forgetThird_snd_snd, reassoc_of% e]
  refine isomorphic_of_crossMultiplies fun x => ?_
  have hf := mem_nonvanishingLocus_pullbackGlobalSections f
    (mem_nonvanishingLocus_biquadraticFrame f x)
  have hg := mem_nonvanishingLocus_pullbackGlobalSections g
    (mem_nonvanishingLocus_biquadraticFrame g x)
  have e : ∀ k : T ⟶ projectiveLineCube S, k ≫ cubeProduct.proj S _ 0 = g ≫ cubeProduct.proj S _ 0 →
      k ≫ cubeProduct.proj S _ 1 = g ≫ cubeProduct.proj S _ 1 → ∀ l,
      stalkCoord _ (mem_nonvanishingLocus_pullbackGlobalSections k
          (mem_nonvanishingLocus_biquadraticFrame k x))
          ((pullbackTuple k (triquadraticCoefficientTuple S coef hgen)).coord l) =
        biquadraticPoly (fun i j => coef i j l) (lineCoord (g ≫ cubeProduct.proj S _ 0) x)
          (lineCoord (g ≫ cubeProduct.proj S _ 1) x) := fun k hk₀ hk₁ l => by
    rw [← hk₀, ← hk₁]
    exact stalkCoord_pullbackGlobalSections_biquadraticSection k x (fun i j => coef i j l)
  refine (crossMultiplies_at_iff_stalkCoord hf hg _ _).2 fun i j => ?_
  rw [e f h₀ h₁, e f h₀ h₁, e g rfl rfl, e g rfl rfl, mul_comm]

/-- **The triquadratic surface is the quadric of its coefficients at the third coordinates.** -/
theorem quadric_triquadraticCoefficientTuple :
    quadric (triquadraticCoefficientTuple S coef hgen) (thirdCoordinateTuple S) =
      triquadraticIdeal coef S :=
  rfl

/-- **The covering involution of a triquadratic surface** `X = Z(A₀ z₀² + A₁ z₀ z₁ + A₂ z₁²)`
over `S × ℙ¹ × ℙ¹`, for coefficients `A₀, A₁, A₂` without common zero: it is the identity on the
first two factors and exchanges the two roots `(z₀ : z₁)` of the binary quadratic form on the
third. -/
def triquadraticSurfaceInvolution : triquadraticSurface coef S ⟶ triquadraticSurface coef S :=
  quadricInvolution (triquadraticCoefficientTuple S coef hgen) (thirdCoordinateTuple S)
    (cubeProduct.isPullback_forgetThird_proj S _)
    (isDeterminedBy_triquadraticCoefficientTuple S coef hgen) (isomorphic_thirdCoordinateTuple S)

/-- **The covering involution is an involution.** -/
@[reassoc (attr := simp)]
theorem triquadraticSurfaceInvolution_comp_self :
    triquadraticSurfaceInvolution S coef hgen ≫ triquadraticSurfaceInvolution S coef hgen = 𝟙 _ :=
  quadricInvolution_comp_self _ _ _ _ _

/-- The covering involution as an automorphism of the triquadratic surface. -/
@[simps]
def triquadraticSurfaceInvolutionIso : triquadraticSurface coef S ≅ triquadraticSurface coef S where
  hom := triquadraticSurfaceInvolution S coef hgen
  inv := triquadraticSurfaceInvolution S coef hgen
  hom_inv_id := triquadraticSurfaceInvolution_comp_self S coef hgen
  inv_hom_id := triquadraticSurfaceInvolution_comp_self S coef hgen

/-- **The covering involution is a morphism over `S × ℙ¹ × ℙ¹`.** -/
@[reassoc]
theorem triquadraticSurfaceInvolution_ι_forgetThird :
    triquadraticSurfaceInvolution S coef hgen ≫ triquadraticSurfaceι coef S ≫
        cubeProduct.forgetThird S _ =
      triquadraticSurfaceι coef S ≫ cubeProduct.forgetThird S _ :=
  quadricInvolution_subschemeι_π _ _ _ _ _

/-- **The covering involution is the identity on the first two factors.** -/
@[reassoc]
theorem triquadraticSurfaceInvolution_ι_proj (i : Fin 3) (hi : i ≠ 2) :
    triquadraticSurfaceInvolution S coef hgen ≫ triquadraticSurfaceι coef S ≫
        cubeProduct.proj S _ i =
      triquadraticSurfaceι coef S ≫ cubeProduct.proj S _ i :=
  quadricInvolution_subschemeι_comp_of_factors _ _ _ _ _
    (cubeProduct.exists_forgetThird_comp_eq_proj S _ i hi)

/-- **The covering involution is a morphism over `S`.** -/
@[reassoc]
theorem triquadraticSurfaceInvolution_toBase :
    triquadraticSurfaceInvolution S coef hgen ≫ triquadraticSurfaceToBase coef S =
      triquadraticSurfaceToBase coef S :=
  quadricInvolution_subschemeι_comp_of_factors _ _ _ _ _
    ⟨pullback.fst _ _, cubeProduct.forgetThird_fst S _⟩

/-- **On the third factor the covering involution is the other root** of the binary quadratic
form. -/
@[reassoc]
theorem triquadraticSurfaceInvolution_ι_proj_two :
    triquadraticSurfaceInvolution S coef hgen ≫ triquadraticSurfaceι coef S ≫
        cubeProduct.proj S _ 2 =
      quadricOtherRoot (triquadraticCoefficientTuple S coef hgen) (thirdCoordinateTuple S) :=
  quadricInvolution_subschemeι_τ _ _ _ _ _

/-- **The covering involution fixes the pencils of the first two factors**:
`σ^*(𝓗ᵢ|_X) ≅ 𝓗ᵢ|_X` for `i = 0, 1`. -/
def triquadraticSurfaceInvolutionLineBundleIso (i : Fin 3) (hi : i ≠ 2) :
    (Scheme.Modules.pullback (triquadraticSurfaceInvolution S coef hgen)).obj
        ((Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (lineBundle S i)) ≅
      (Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (lineBundle S i) :=
  quadricInvolutionPullbackIso _ _ _ _ _ (cubeProduct.proj S _ i)
    (cubeProduct.exists_forgetThird_comp_eq_proj S _ i hi) _

/-- **The line-bundle identity of the covering involution**: `σ^*𝓗₂ ⊗ 𝓗₂² ≅ M ⊗ 𝓗₂` on `X`, with
`M = 𝓗₀² ⊗ 𝓗₁²` the module of the coefficients. -/
def triquadraticSurfaceInvolutionTwistIso :
    Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback (triquadraticSurfaceInvolution S coef hgen)).obj
          ((Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (lineBundle S 2)))
        (Scheme.Modules.tensorObj
          ((Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (lineBundle S 2))
          ((Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (lineBundle S 2))) ≅
      Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (biquadraticModule S))
        ((Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (lineBundle S 2)) :=
  quadricInvolutionTwistIso _ _ _ _ _

end projectiveLineCube

end AlgebraicGeometry

end
