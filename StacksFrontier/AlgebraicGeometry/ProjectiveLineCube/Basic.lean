module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.AlgebraicGeometry.ProjAmple.Basic
public import StacksFrontier.AlgebraicGeometry.Segre.ChartAffine

/-!
# Products of three projective lines

For schemes `S` and `X`, the product `S × X × X × X` over `Spec ℤ` is a scheme over `S` whose
morphisms from a scheme `T` are the quadruples `(T → S, T → X, T → X, T → X)`. The symmetric group
on the three factors acts on it by automorphisms over `S`, and when `X` is proper over `Spec ℤ`
the product is proper over `S`.

For `X = ℙ¹` this is `ℙ¹_S ×_S ℙ¹_S ×_S ℙ¹_S`. It carries the three pencils `𝓗ᵢ = prᵢ^*𝒪(1)`
and, more generally, the invertible modules `𝒪(a, b, c) = pr₀^*𝒪(a) ⊗ pr₁^*𝒪(b) ⊗ pr₂^*𝒪(c)`;
the cyclic permutation `ρ` of the factors satisfies `ρ^*𝓗ᵢ ≅ 𝓗ᵢ₊₁`. When `S` is affine,
`𝒪(1, 1, 1)` is ample: the sections `pr₀^*Tₐ ⊗ pr₁^*T_b ⊗ pr₂^*T_c` have the affine opens
`S × D₊(Tₐ) × D₊(T_b) × D₊(T_c)` as nonvanishing loci, and these cover.

This is the ambient space of the cyclically symmetric `(2, 2, 2)`-surfaces of
[Stacks, Tag 0DSR].

## Main definitions

* `AlgebraicGeometry.cubeProduct S X`: the product `S × X × X × X` over `Spec ℤ`, with its
  projections `AlgebraicGeometry.cubeProduct.toBase` and `AlgebraicGeometry.cubeProduct.proj`
  and the morphisms `AlgebraicGeometry.cubeProduct.lift` into it.
* `AlgebraicGeometry.cubeProduct.permutationIso`: the automorphism permuting the three factors,
  and `AlgebraicGeometry.cubeProduct.rotation`, the cyclic one.
* `AlgebraicGeometry.projectiveLineCube S`: the product `S × ℙ¹ × ℙ¹ × ℙ¹`.
* `AlgebraicGeometry.projectiveLineCube.lineBundle`: the pencils `𝓗ᵢ = prᵢ^*𝒪(1)`.
* `AlgebraicGeometry.projectiveLineCube.twist`: the invertible modules `𝒪(a, b, c)`.
* `AlgebraicGeometry.projectiveLineCube.coordinate`: the sections `prᵢ^*T₀`, `prᵢ^*T₁` of `𝓗ᵢ`.

## Main results

* `AlgebraicGeometry.cubeProduct.isProper_toBase`: `S × X × X × X` is proper over `S` when `X` is
  proper over `Spec ℤ`; in particular `S × ℙ¹ × ℙ¹ × ℙ¹` is proper over `S`.
* `AlgebraicGeometry.cubeProduct.isAffineOpen_toBase_preimage_inf`: products of affine opens are
  affine opens.
* `AlgebraicGeometry.projectiveLineCube.rotationPullbackLineBundleIso`: `ρ^*𝓗ᵢ ≅ 𝓗ᵢ₊₁`.
* `AlgebraicGeometry.projectiveLineCube.isAmple_twist_one_one_one`: `𝒪(1, 1, 1)` is ample over an
  affine base.

## Implementation notes

The product is the iterated fibre product `S ×_{Spec ℤ} (X ×_{Spec ℤ} (X ×_{Spec ℤ} X))`, with
`Spec ℤ` realised as the terminal scheme, as for `AlgebraicGeometry.projectiveSpaceOver`. Over the
terminal scheme every pair of morphisms is compatible, so a morphism into the product is just a
quadruple of morphisms, and the permutations of the factors are defined through
`AlgebraicGeometry.cubeProduct.lift` rather than through the associativity and symmetry
isomorphisms of fibre products.

Ampleness of `𝒪(1, 1, 1)` is proved directly at exponent one rather than through the Segre
embedding: every point lies in the nonvanishing locus of one of the eight monomials
`pr₀^*Tₐ ⊗ pr₁^*T_b ⊗ pr₂^*T_c`, and that locus is a product of affine opens.

## References

* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable (S X : Scheme.{u})

/-- The product `S × X × X × X` of schemes over `Spec ℤ`. -/
abbrev cubeProduct : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from
    (pullback (terminal.from X) (terminal.from (pullback (terminal.from X) (terminal.from X)))))

namespace cubeProduct

/-- The projection of `S × X × X × X` to the base `S`. -/
def toBase : cubeProduct S X ⟶ S := pullback.fst _ _

/-- The three projections of `S × X × X × X` to `X`. -/
def proj : Fin 3 → (cubeProduct S X ⟶ X) :=
  ![pullback.snd _ _ ≫ pullback.fst _ _, pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.fst _ _,
    pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _]

variable {S X}

/-- The morphism to `S × X × X × X` with given components. -/
def lift {T : Scheme.{u}} (f : T ⟶ S) (g : Fin 3 → (T ⟶ X)) : T ⟶ cubeProduct S X :=
  pullback.lift f (pullback.lift (g 0) (pullback.lift (g 1) (g 2) (terminal.hom_ext _ _))
    (terminal.hom_ext _ _)) (terminal.hom_ext _ _)

/-- The base component of `AlgebraicGeometry.cubeProduct.lift`. -/
@[reassoc (attr := simp)]
theorem lift_toBase {T : Scheme.{u}} (f : T ⟶ S) (g : Fin 3 → (T ⟶ X)) :
    lift f g ≫ toBase S X = f :=
  pullback.lift_fst _ _ _

/-- The `i`-th component of `AlgebraicGeometry.cubeProduct.lift`. -/
@[reassoc (attr := simp)]
theorem lift_proj {T : Scheme.{u}} (f : T ⟶ S) (g : Fin 3 → (T ⟶ X)) (i : Fin 3) :
    lift f g ≫ proj S X i = g i := by
  fin_cases i <;>
    simp only [lift, proj, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      pullback.lift_snd_assoc, pullback.lift_fst, pullback.lift_snd]

/-- Two morphisms into `S × X × X × X` agreeing on all four components are equal. -/
theorem hom_ext {T : Scheme.{u}} {a b : T ⟶ cubeProduct S X}
    (h : a ≫ toBase S X = b ≫ toBase S X) (h' : ∀ i, a ≫ proj S X i = b ≫ proj S X i) :
    a = b := by
  refine pullback.hom_ext h (pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_))
  · simpa [proj] using h' 0
  · simpa [proj] using h' 1
  · simpa [proj] using h' 2

variable (S X)

/-- The automorphism of `S × X × X × X` over `S` permuting the three factors by `e`: its
composite with the `i`-th projection is the `e i`-th projection. -/
def permutation (e : Equiv.Perm (Fin 3)) : cubeProduct S X ⟶ cubeProduct S X :=
  lift (toBase S X) fun i => proj S X (e i)

/-- The permutations of the factors are morphisms over `S`. -/
@[reassoc (attr := simp)]
theorem permutation_toBase (e : Equiv.Perm (Fin 3)) :
    permutation S X e ≫ toBase S X = toBase S X :=
  lift_toBase _ _

/-- The `i`-th component of the permutation by `e` is the `e i`-th projection. -/
@[reassoc (attr := simp)]
theorem permutation_proj (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    permutation S X e ≫ proj S X i = proj S X (e i) :=
  lift_proj _ _ i

/-- The trivial permutation is the identity. -/
@[simp]
theorem permutation_one : permutation S X 1 = 𝟙 _ :=
  hom_ext (by simp) fun i => by simp

/-- The permutations of the factors compose as the permutations do. -/
@[reassoc]
theorem permutation_comp (e e' : Equiv.Perm (Fin 3)) :
    permutation S X e ≫ permutation S X e' = permutation S X (e * e') :=
  hom_ext (by simp) fun i => by simp

/-- The permutation of the factors of `S × X × X × X` as an automorphism. -/
@[simps]
def permutationIso (e : Equiv.Perm (Fin 3)) : cubeProduct S X ≅ cubeProduct S X where
  hom := permutation S X e
  inv := permutation S X e⁻¹
  hom_inv_id := by rw [permutation_comp, mul_inv_cancel, permutation_one]
  inv_hom_id := by rw [permutation_comp, inv_mul_cancel, permutation_one]

/-- The cyclic permutation of the factors of `S × X × X × X`, sending `(s, x₀, x₁, x₂)` to
`(s, x₁, x₂, x₀)`: its composite with the `i`-th projection is the `(i + 1)`-th projection. -/
abbrev rotation : cubeProduct S X ≅ cubeProduct S X :=
  permutationIso S X (finRotate 3)

/-- The `i`-th component of the cyclic permutation is the `(i + 1)`-th projection. -/
@[reassoc (attr := simp)]
theorem rotation_hom_proj (i : Fin 3) :
    (rotation S X).hom ≫ proj S X i = proj S X (i + 1) := by
  rw [permutationIso_hom, permutation_proj, finRotate_apply]

/-- A product `S × X × X × X` with `X` proper over `Spec ℤ` is proper over `S`. -/
instance isProper_toBase [IsProper (terminal.from X)] : IsProper (toBase S X) := by
  have h₁ : IsProper (terminal.from (pullback (terminal.from X) (terminal.from X))) := by
    rw [show terminal.from (pullback (terminal.from X) (terminal.from X)) =
      pullback.snd _ _ ≫ terminal.from X from terminal.hom_ext _ _]
    infer_instance
  have h₂ : IsProper (terminal.from (pullback (terminal.from X)
      (terminal.from (pullback (terminal.from X) (terminal.from X))))) := by
    rw [show terminal.from (pullback (terminal.from X)
        (terminal.from (pullback (terminal.from X) (terminal.from X)))) =
      pullback.snd _ _ ≫ terminal.from (pullback (terminal.from X) (terminal.from X)) from
        terminal.hom_ext _ _]
    infer_instance
  change IsProper (pullback.fst _ _)
  infer_instance

/-- **Products of affine opens are affine.** For an affine open `V` of `S` and affine opens
`U₀, U₁, U₂` of `X`, the open `V × U₀ × U₁ × U₂` of `S × X × X × X` is affine. -/
theorem isAffineOpen_toBase_preimage_inf {V : S.Opens} (hV : IsAffineOpen V) {U : Fin 3 → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsAffineOpen (toBase S X ⁻¹ᵁ V ⊓ proj S X 0 ⁻¹ᵁ U 0 ⊓ proj S X 1 ⁻¹ᵁ U 1 ⊓
      proj S X 2 ⁻¹ᵁ U 2) := by
  have h₁ := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf (terminal.from X)
    (terminal.from X) (hU 1) (hU 2)
  have h₂ := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf (terminal.from X)
    (terminal.from (pullback (terminal.from X) (terminal.from X))) (hU 0) h₁
  have h₃ := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf (terminal.from S)
    (terminal.from (pullback (terminal.from X)
      (terminal.from (pullback (terminal.from X) (terminal.from X))))) hV h₂
  simp only [inf_assoc]
  exact h₃

/-- For an affine base `S` and affine opens `U₀, U₁, U₂` of `X`, the open `S × U₀ × U₁ × U₂` of
`S × X × X × X` is affine. -/
theorem isAffineOpen_proj_preimage_inf [IsAffine S] {U : Fin 3 → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsAffineOpen (proj S X 0 ⁻¹ᵁ U 0 ⊓ proj S X 1 ⁻¹ᵁ U 1 ⊓ proj S X 2 ⁻¹ᵁ U 2) := by
  simpa using isAffineOpen_toBase_preimage_inf S X (isAffineOpen_top S) hU

end cubeProduct

/-! ### Products of three projective lines -/

/-- The product `S × ℙ¹ × ℙ¹ × ℙ¹` over `Spec ℤ`, that is, the fibre product
`ℙ¹_S ×_S ℙ¹_S ×_S ℙ¹_S` of three copies of the projective line over `S`. -/
abbrev projectiveLineCube (S : Scheme.{u}) : Scheme.{u} :=
  cubeProduct S (projectiveSpaceAtUniverse.{u} 1)

namespace projectiveLineCube

variable (S : Scheme.{u})

open cubeProduct

/-- **`S × ℙ¹ × ℙ¹ × ℙ¹` is proper over `S`.** -/
instance isProper_toBase : IsProper (toBase S (projectiveSpaceAtUniverse.{u} 1)) :=
  have := isProper_terminalFrom_projectiveSpaceAtUniverse.{u} 1
  inferInstance

/-- The invertible module `𝒪(a, b, c) = pr₀^*𝒪(a) ⊗ pr₁^*𝒪(b) ⊗ pr₂^*𝒪(c)` on
`S × ℙ¹ × ℙ¹ × ℙ¹`. -/
def twist (a b c : ℤ) : (projectiveLineCube S).Modules :=
  Scheme.Modules.tensorObj
    (Scheme.Modules.tensorObj
      ((Scheme.Modules.pullback (proj S _ 0)).obj (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 a))
      ((Scheme.Modules.pullback (proj S _ 1)).obj (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 b)))
    ((Scheme.Modules.pullback (proj S _ 2)).obj (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 c))

/-- The invertible module `𝓗ᵢ = prᵢ^*𝒪(1)` on `S × ℙ¹ × ℙ¹ × ℙ¹`. -/
def lineBundle (i : Fin 3) : (projectiveLineCube S).Modules :=
  (Scheme.Modules.pullback (proj S _ i)).obj (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1)

/-- `𝒪(1, 1, 1) = 𝓗₀ ⊗ 𝓗₁ ⊗ 𝓗₂`. -/
theorem twist_one_one_one : twist S 1 1 1 = Scheme.Modules.tensorObj
    (Scheme.Modules.tensorObj (lineBundle S 0) (lineBundle S 1)) (lineBundle S 2) :=
  rfl

/-- **Permuting the factors permutes the pencils**: `e^*𝓗ᵢ ≅ 𝓗_{e i}`. -/
def permutationPullbackLineBundleIso (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (Scheme.Modules.pullback (permutation S (projectiveSpaceAtUniverse.{u} 1) e)).obj
      (lineBundle S i) ≅ lineBundle S (e i) :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (permutation_proj S _ e i)).app _

/-- **The cyclic permutation of the factors moves the pencils**: `ρ^*𝓗ᵢ ≅ 𝓗ᵢ₊₁`. -/
def rotationPullbackLineBundleIso (i : Fin 3) :
    (Scheme.Modules.pullback (rotation S (projectiveSpaceAtUniverse.{u} 1)).hom).obj
      (lineBundle S i) ≅ lineBundle S (i + 1) :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (rotation_hom_proj S _ i)).app _

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `𝒪(d)` on `ℙ¹_ℤ` is invertible. -/
theorem isInvertible_twistingSheaf (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (projectiveSpaceAtUniverse.{u} 1).toRingedSpace.presheaf
      (structureSheafRing (projectiveSpaceAtUniverse.{u} 1).toRingedSpace).property
      (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 d) :=
  ProjectiveSpectrum.Proj.projectiveSpace_isInvertible_twistingSheaf (ULift.{u} ℤ) 2 d

/-- `𝓗ᵢ` is invertible. -/
instance isInvertible_lineBundle (i : Fin 3) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property (lineBundle S i) :=
  have := isInvertible_twistingSheaf.{u} 1
  inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible
    (projectiveLineCube S).toRingedSpace.presheaf
    (structureSheafRing (projectiveLineCube S).toRingedSpace).property
    ((Scheme.Modules.pullback (proj S _ i)).obj (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1)))

/-- `𝓗ᵢ` is invertible, in the form the nonvanishing loci of its sections ask for. -/
instance isInvertible_lineBundle_stacks (i : Fin 3) :
    Stacks.SheafOfModules.IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property (lineBundle S i) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr inferInstance

/-- `𝒪(a, b, c)` is invertible, in the form the nonvanishing loci of its sections ask for. -/
instance isInvertible_twist_stacks (a b c : ℤ) :
    Stacks.SheafOfModules.IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property (twist S a b c) := by
  have h : ∀ (i : Fin 3) (d : ℤ), Stacks.SheafOfModules.IsInvertible
      (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property
      ((Scheme.Modules.pullback (proj S _ i)).obj
        (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 d)) := fun i d =>
    have := isInvertible_twistingSheaf.{u} d
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr inferInstance
  have h₁ := h 0 a
  have h₂ := h 1 b
  have h₃ := h 2 c
  have h₁₂ : Stacks.SheafOfModules.IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property
      (Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback (proj S _ 0)).obj
          (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 a))
        ((Scheme.Modules.pullback (proj S _ 1)).obj
          (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 b))) :=
    Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ _
  exact Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ _

/-- `𝒪(a, b, c)` is invertible. -/
instance isInvertible_twist (a b c : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineCube S).toRingedSpace.presheaf
      (structureSheafRing (projectiveLineCube S).toRingedSpace).property (twist S a b c) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp inferInstance

/-- The global section `prᵢ^* Tₐ` of `𝓗ᵢ`, the pullback of the `a`-th homogeneous coordinate of
`ℙ¹` along the `i`-th projection. -/
def coordinate (i : Fin 3) (a : Fin 2) : (lineBundle S i).sections :=
  Stacks.SheafOfModules.modulePullbackSection (proj S _ i).toLRSHom
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a)

/-- The nonvanishing locus of `prᵢ^* Tₐ` is `prᵢ⁻¹ D₊(Tₐ)`. -/
theorem nonvanishingOpen_coordinate (i : Fin 3) (a : Fin 2) :
    Stacks.SheafOfModules.nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
        (lineBundle S i) (coordinate S i a) =
      proj S _ i ⁻¹ᵁ Proj.basicOpen (Segre.coordinateGrading.{u} 1) (MvPolynomial.X a) := by
  rw [← Segre.nonvanishingOpen_coordinateSection_eq_basicOpen.{u} 1 a]
  exact (Stacks.SheafOfModules.preimage_nonvanishingOpen (proj S _ i)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} 1 1) (Segre.coordinateSection.{u} 1 a)).symm

/-- The nonvanishing loci of the two sections `prᵢ^* T₀` and `prᵢ^* T₁` of `𝓗ᵢ` cover. -/
theorem iSup_nonvanishingOpen_coordinate (i : Fin 3) :
    (⨆ a : Fin 2, Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveLineCube S).toRingedSpace) (lineBundle S i) (coordinate S i a)) = ⊤ := by
  simp_rw [nonvanishingOpen_coordinate, ← Segre.nonvanishingOpen_coordinateSection_eq_basicOpen]
  exact Scheme.Hom.iSup_preimage_eq_top _ (Segre.iSup_nonvanishingOpen_coordinateSection_eq_top 1)

/-- The global section `pr₀^* Tₐ ⊗ pr₁^* T_b ⊗ pr₂^* T_c` of `𝒪(1, 1, 1)`. -/
def coordinateMonomial (a b c : Fin 2) : (twist S 1 1 1).sections :=
  Stacks.SheafOfModules.tensorSections _ _
    (Stacks.SheafOfModules.tensorSections _ _ (coordinate S 0 a) (coordinate S 1 b))
    (coordinate S 2 c)

/-- The nonvanishing locus of `pr₀^* Tₐ ⊗ pr₁^* T_b ⊗ pr₂^* T_c` is
`pr₀⁻¹ D₊(Tₐ) ∩ pr₁⁻¹ D₊(T_b) ∩ pr₂⁻¹ D₊(T_c)`. -/
theorem nonvanishingOpen_coordinateMonomial (a b c : Fin 2) :
    Stacks.SheafOfModules.nonvanishingOpen (X := (projectiveLineCube S).toRingedSpace)
        (twist S 1 1 1) (coordinateMonomial S a b c) =
      proj S _ 0 ⁻¹ᵁ Proj.basicOpen (Segre.coordinateGrading.{u} 1) (MvPolynomial.X a) ⊓
        proj S _ 1 ⁻¹ᵁ Proj.basicOpen (Segre.coordinateGrading.{u} 1) (MvPolynomial.X b) ⊓
        proj S _ 2 ⁻¹ᵁ Proj.basicOpen (Segre.coordinateGrading.{u} 1) (MvPolynomial.X c) := by
  rw [← nonvanishingOpen_coordinate, ← nonvanishingOpen_coordinate,
    ← nonvanishingOpen_coordinate]
  refine TopologicalSpace.Opens.ext ?_
  refine (Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _).trans ?_
  exact congrArg (· ∩ _) (Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _)

/-- **`𝒪(1, 1, 1)` is ample on `S × ℙ¹ × ℙ¹ × ℙ¹` for an affine base `S`.** The nonvanishing loci
of the sections `pr₀^* Tₐ ⊗ pr₁^* T_b ⊗ pr₂^* T_c` are the products of standard opens
`S × D₊(Tₐ) × D₊(T_b) × D₊(T_c)`, which are affine and cover. -/
theorem isAmple_twist_one_one_one [IsAffine S] :
    Scheme.Modules.IsAmple (projectiveLineCube S) (twist S 1 1 1) := by
  refine Scheme.Modules.isAmple_of_forall_exists_affine_nonvanishingOpen _ _
    (QuasiCompact.compactSpace_of_compactSpace (toBase S _)) fun x => ?_
  have hcov : ∀ i : Fin 3, ∃ a : Fin 2,
      proj S _ i x ∈ Proj.basicOpen (Segre.coordinateGrading.{u} 1) (MvPolynomial.X a) := by
    intro i
    have h : x ∈ ⨆ a : Fin 2, Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveLineCube S).toRingedSpace) (lineBundle S i) (coordinate S i a) := by
      rw [iSup_nonvanishingOpen_coordinate]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    exact ⟨a, by rwa [nonvanishingOpen_coordinate] at ha⟩
  obtain ⟨a, ha⟩ := hcov 0
  obtain ⟨b, hb⟩ := hcov 1
  obtain ⟨c, hc⟩ := hcov 2
  refine ⟨coordinateMonomial S a b c, ?_, ?_⟩
  · rw [nonvanishingOpen_coordinateMonomial]
    exact ⟨⟨ha, hb⟩, hc⟩
  · rw [nonvanishingOpen_coordinateMonomial]
    exact isAffineOpen_proj_preimage_inf S _ (U := ![_, _, _]) fun i => by
      fin_cases i <;> exact Segre.isAffineOpen_basicOpen_X.{u} 1 _

end projectiveLineCube

end AlgebraicGeometry
