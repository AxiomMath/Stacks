module

public import StacksFrontier.AlgebraicGeometry.Constructions.Cone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme

/-!
# Vector bundles over a scheme

A *vector bundle* over a scheme `S` is a cone `π : V ⟶ S` — an affine morphism of schemes whose
direct image `π_* 𝒪_V = ⨁_{n ≥ 0} ℰ_n` carries a nonnegative grading as a sheaf of
`𝒪_S`-algebras with `ℰ_0 = 𝒪_S` — whose canonical maps `Sym^n(ℰ_1) ⟶ ℰ_n` are isomorphisms. A
morphism of vector bundles over `S` is a morphism of the total spaces over `S` whose pullback on
functions preserves the grading, which is exactly a morphism of the underlying cones; vector
bundles over `S` therefore form a category. Neither `ℰ_1` nor the bundle is required to be of
finite type or locally free.

## Main definitions

* `AlgebraicGeometry.AbstractCone.symmetricAlgebraDesc` is the canonical homomorphism
  `Sym(ℰ_1) ⟶ π_* 𝒪_C` of sheaves of graded `𝒪_S`-algebras, and
  `AlgebraicGeometry.AbstractCone.symmetricPowerComparison` its degree-`n` component
  `Sym^n(ℰ_1) ⟶ ℰ_n`.
* `AlgebraicGeometry.AbstractCone.Hom.id` and `AlgebraicGeometry.AbstractCone.Hom.comp` are the
  identity morphism of a cone and the composition of morphisms of cones.
* `AlgebraicGeometry.VectorBundle` is a vector bundle over a scheme and
  `AlgebraicGeometry.VectorBundle.category` is the category of vector bundles over a fixed base,
  whose morphisms are the morphisms of the underlying cones.
* `AlgebraicGeometry.VectorBundle.ofIsSymmetricAlgebra` and
  `AlgebraicGeometry.VectorBundle.ofNonneg` build a vector bundle from the universal property of
  the symmetric algebra, respectively from the comparison maps in nonnegative degrees only.

## Main results

* `AlgebraicGeometry.AbstractCone.pairwiseCommutes`: the degree-one local sections of the
  direct-image algebra of a cone commute.
* `AlgebraicGeometry.VectorBundle.isSymmetricAlgebra` and
  `AlgebraicGeometry.VectorBundle.ofIsSymmetricAlgebra`: a cone is a vector bundle if and only if
  its direct-image algebra is the symmetric algebra on its own degree-one piece.
* `AlgebraicGeometry.AbstractCone.isIso_symmetricPowerComparison_of_neg`: in negative degrees
  both `Sym^n(ℰ_1)` and `ℰ_n` vanish, so the comparison is automatically an isomorphism there.
* `AlgebraicGeometry.VectorBundle.symmetricPowerComparison_one_comp_symmetricAlgebraGen`: in
  degree one the comparison is inverse to the generator of the symmetric algebra, and
  `AlgebraicGeometry.VectorBundle.isIso_symmetricPowerComparison_zero_comp_degreeZero` reads the
  degree-zero comparison, composed with `ℰ_0 ≅ 𝒪_S`, as an isomorphism `Sym^0(ℰ_1) ≅ 𝒪_S`.

## Implementation notes

`AlgebraicGeometry.VectorBundle` extends `AlgebraicGeometry.AbstractCone` by the single condition
that the comparison maps are isomorphisms, so its morphisms are the morphisms of the underlying
cones. The condition quantifies over all integers rather than over `n ≥ 0`; the two agree by
`AlgebraicGeometry.AbstractCone.isIso_symmetricPowerComparison_of_neg` and
`AlgebraicGeometry.VectorBundle.ofNonneg`. It is stated as `IsIso` of
`AlgebraicGeometry.AbstractCone.symmetricPowerComparison` rather than as a bundled isomorphism.

## References

* [Stacks Project, Tag 062M](https://stacks.math.columbia.edu/tag/062M)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

namespace AbstractCone

variable {S : Scheme.{u}}

/-! ### The comparison of a cone with the symmetric algebra on its degree-one piece -/

/-- Every homogeneous piece of a cone injects into the direct image on sections: a homogeneous
local section is determined by the function it is. -/
theorem ι_app_injective (X : AbstractCone S) (n : ℤ) (U : S.Opens) :
    Function.Injective fun a : (X.grading.piece n).val.obj (op U) =>
      ((X.ι n).val.app (op U) a : X.C.presheaf.obj (op (X.π ⁻¹ᵁ U))) := by
  intro a b hab
  have h : pushforwardHomogeneousSum X.π X.grading X.ι U (DFinsupp.single n a) =
      pushforwardHomogeneousSum X.π X.grading X.ι U (DFinsupp.single n b) := by
    simpa [pushforwardHomogeneousSum] using hab
  simpa using congrArg
    (fun s : Π₀ m : ℤ, (X.grading.piece m).val.obj (op U) => s n) (X.decomposition_unique U h)

/-- Degree-one local sections of the direct-image algebra of a cone commute. -/
theorem pairwiseCommutes (X : AbstractCone S) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (𝟙 (X.grading.piece 1)) := by
  intro U s t
  induction U with
  | op U =>
    refine X.ι_app_injective (1 + 1) U ?_
    dsimp only
    rw [X.ι_mul, X.ι_mul, mul_comm]

/-- The canonical homomorphism `Sym(ℰ_1) ⟶ π_* 𝒪_C` of sheaves of graded `𝒪_S`-algebras: the
unique unital homomorphism which is the identity on the degree-one piece. -/
def symmetricAlgebraDesc (X : AbstractCone S) :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Scheme.Modules.symmetricAlgebra S (X.grading.piece 1)) X.grading :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S
    (X.grading.piece 1)).isUniversal.desc X.grading (𝟙 (X.grading.piece 1)) X.pairwiseCommutes

/-- The canonical map `Sym^n(ℰ_1) ⟶ ℰ_n` from the `n`-th symmetric power of the degree-one piece
of a cone to its degree-`n` piece. -/
def symmetricPowerComparison (X : AbstractCone S) (n : ℤ) :
    (Scheme.Modules.symmetricAlgebra S (X.grading.piece 1)).piece n ⟶ X.grading.piece n :=
  X.symmetricAlgebraDesc.app n

/-- The canonical map is the identity on the degree-one piece: it carries the generator of
`Sym(ℰ_1)` to the identity of `ℰ_1`. -/
theorem symmetricAlgebraGen_comp_symmetricPowerComparison (X : AbstractCone S) :
    Scheme.Modules.symmetricAlgebraGen S (X.grading.piece 1) ≫ X.symmetricPowerComparison 1 =
      𝟙 (X.grading.piece 1) :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S
    (X.grading.piece 1)).isUniversal.desc_extends X.grading (𝟙 (X.grading.piece 1))
      X.pairwiseCommutes

/-- In a negative degree the canonical map `Sym^n(ℰ_1) ⟶ ℰ_n` is an isomorphism. -/
theorem isIso_symmetricPowerComparison_of_neg (X : AbstractCone S) (n : ℤ) (hn : n < 0) :
    IsIso (X.symmetricPowerComparison n) :=
  have h₀ : IsZero ((Scheme.Modules.symmetricAlgebra S (X.grading.piece 1)).piece n) :=
    Scheme.Modules.isZero_symmetricAlgebra_piece S (X.grading.piece 1) n hn
  have h₁ : IsZero (X.grading.piece n) := X.negative_isZero n hn
  ⟨⟨(h₀.iso h₁).inv, h₀.eq_of_src _ _, h₁.eq_of_src _ _⟩⟩

/-! ### The category of cones -/

namespace Hom

variable {X Y Z : AbstractCone S}

/-- Two morphisms of cones with the same morphism of total spaces, the same map on direct images
and the same graded map are equal. -/
theorem ext {φ ψ : Hom X Y} (hf : φ.f = ψ.f) (hp : φ.pullback = ψ.pullback)
    (hg : φ.graded = ψ.graded) : φ = ψ := by
  obtain ⟨f₁, c₁, p₁, pa₁, g₁, n₁⟩ := φ
  obtain ⟨f₂, c₂, p₂, pa₂, g₂, n₂⟩ := ψ
  subst hf hp hg
  rfl

/-- The identity morphism of a cone: the identity of the total space, which induces the identity
on functions and on every homogeneous piece. -/
def id (X : AbstractCone S) : Hom X X where
  f := 𝟙 X.C
  comm := Category.id_comp X.π
  pullback := 𝟙 _
  pullback_app _ _ := rfl
  graded := SheafOfModules.GradedAlgebra.Hom.id X.grading
  ι_naturality _ := (Category.comp_id _).trans (Category.id_comp _).symm

/-- On sections, the composite of two maps on direct images that realize the pullback of
functions along two morphisms over `S` realizes the pullback along their composite. -/
theorem comp_pullback_app {CX CY CZ : Scheme.{u}} {pX : CX ⟶ S} {pY : CY ⟶ S}
    {pZ : CZ ⟶ S} {k : CX ⟶ CY} {l : CY ⟶ CZ} (hk : k ≫ pY = pX) (hl : l ≫ pZ = pY)
    {Pk : Stacks.Morphisms.pushforwardStructureSheaf pY ⟶
      Stacks.Morphisms.pushforwardStructureSheaf pX}
    {Pl : Stacks.Morphisms.pushforwardStructureSheaf pZ ⟶
      Stacks.Morphisms.pushforwardStructureSheaf pY}
    (hPk : ∀ (U : S.Opens) (a : CY.presheaf.obj (op (pY ⁻¹ᵁ U))),
      Pk.val.app (op U) a = hk ▸ k.c.app (op (pY ⁻¹ᵁ U)) a)
    (hPl : ∀ (U : S.Opens) (a : CZ.presheaf.obj (op (pZ ⁻¹ᵁ U))),
      Pl.val.app (op U) a = hl ▸ l.c.app (op (pZ ⁻¹ᵁ U)) a)
    (comm : (k ≫ l) ≫ pZ = pX) (U : S.Opens)
    (a : CZ.presheaf.obj (op (pZ ⁻¹ᵁ U))) :
    (Pl ≫ Pk).val.app (op U) a = comm ▸ (k ≫ l).c.app (op (pZ ⁻¹ᵁ U)) a := by
  subst hk hl
  exact (hPk U _).trans (congrArg _ (hPl U a))

/-- The composition of two morphisms of cones: the composite of the morphisms of total spaces,
with the composite pullback on functions and the composite graded map. -/
def comp (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  f := φ.f ≫ ψ.f
  comm := by rw [Category.assoc, ψ.comm, φ.comm]
  pullback := ψ.pullback ≫ φ.pullback
  pullback_app := comp_pullback_app φ.comm ψ.comm φ.pullback_app ψ.pullback_app _
  graded := ψ.graded.comp φ.graded
  ι_naturality n :=
    (Category.assoc (Z.ι n) ψ.pullback φ.pullback).symm.trans <|
      (congrArg (fun x : Z.grading.piece n ⟶
          Stacks.Morphisms.pushforwardStructureSheaf Y.π => x ≫ φ.pullback)
        (ψ.ι_naturality n)).trans <|
        (Category.assoc (ψ.graded.app n) (Y.ι n) φ.pullback).trans <|
          (congrArg (fun x : Y.grading.piece n ⟶
              Stacks.Morphisms.pushforwardStructureSheaf X.π => ψ.graded.app n ≫ x)
            (φ.ι_naturality n)).trans
            (Category.assoc (ψ.graded.app n) (φ.graded.app n) (X.ι n)).symm

/-- The identity morphism of a cone is the identity on total spaces. -/
@[simp] theorem id_f (X : AbstractCone S) : (id X).f = 𝟙 X.C := rfl

/-- A composite of morphisms of cones is the composite on total spaces. -/
@[simp] theorem comp_f (φ : Hom X Y) (ψ : Hom Y Z) : (φ.comp ψ).f = φ.f ≫ ψ.f := rfl

/-- The identity morphism is a left unit for composition. -/
theorem id_comp (φ : Hom X Y) : (id X).comp φ = φ :=
  ext (Category.id_comp _) (Category.comp_id _)
    (SheafOfModules.GradedAlgebra.Hom.ext fun _ => Category.comp_id _)

/-- The identity morphism is a right unit for composition. -/
theorem comp_id (φ : Hom X Y) : φ.comp (id Y) = φ :=
  ext (Category.comp_id _) (Category.id_comp _)
    (SheafOfModules.GradedAlgebra.Hom.ext fun _ => Category.id_comp _)

/-- Composition of morphisms of cones is associative. -/
theorem assoc {W : AbstractCone S} (φ : Hom W X) (ψ : Hom X Y) (χ : Hom Y Z) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) :=
  ext (Category.assoc _ _ _) (Category.assoc _ _ _).symm
    (SheafOfModules.GradedAlgebra.Hom.ext fun _ => (Category.assoc _ _ _).symm)

end Hom

end AbstractCone

/-! ### Vector bundles -/

/-- A vector bundle over `S`: a cone whose direct-image algebra is generated in degree one in the
strongest sense, namely that every canonical map `Sym^n(ℰ_1) ⟶ ℰ_n` is an isomorphism. -/
@[stacks 062M "vector bundles"]
structure VectorBundle (S : Scheme.{u}) extends AbstractCone S where
  /-- The canonical maps from the symmetric powers of the degree-one piece to the homogeneous
  pieces are isomorphisms. -/
  isIso_symmetricPowerComparison (n : ℤ) :
    IsIso (toAbstractCone.symmetricPowerComparison n)

namespace VectorBundle

variable {S : Scheme.{u}}

/-- Vector bundles over a fixed base form a category, with the morphisms of the underlying
cones as its morphisms. -/
@[stacks 062M "morphisms of vector bundles"]
instance category : Category (VectorBundle S) where
  Hom X Y := AbstractCone.Hom X.toAbstractCone Y.toAbstractCone
  id X := AbstractCone.Hom.id X.toAbstractCone
  comp := AbstractCone.Hom.comp
  id_comp := AbstractCone.Hom.id_comp
  comp_id := AbstractCone.Hom.comp_id
  assoc := AbstractCone.Hom.assoc

/-- The identity morphism of a vector bundle is the identity on total spaces. -/
@[simp] theorem id_f (X : VectorBundle S) : (𝟙 X : X ⟶ X).f = 𝟙 X.C := rfl

/-- A composite of morphisms of vector bundles is the composite on total spaces. -/
@[simp] theorem comp_f {X Y Z : VectorBundle S} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

/-- A cone whose direct-image algebra is the symmetric algebra on its own degree-one piece is a
vector bundle. -/
def ofIsSymmetricAlgebra (X : AbstractCone S)
    (h : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra X.grading (𝟙 (X.grading.piece 1))) :
    VectorBundle S where
  toAbstractCone := X
  isIso_symmetricPowerComparison n :=
    ((Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S
      (X.grading.piece 1)).isUniversal.pieceIso h.isUniversal n).isIso_hom

/-- A cone whose canonical maps `Sym^n(ℰ_1) ⟶ ℰ_n` are isomorphisms in nonnegative degrees is a
vector bundle. -/
def ofNonneg (X : AbstractCone S)
    (h : ∀ n : ℤ, 0 ≤ n → IsIso (X.symmetricPowerComparison n)) : VectorBundle S where
  toAbstractCone := X
  isIso_symmetricPowerComparison n :=
    (lt_or_ge n 0).elim (X.isIso_symmetricPowerComparison_of_neg n) (h n)

/-- In degree one the canonical map is inverse to the generator of the symmetric algebra:
`Sym^1(ℰ_1) = ℰ_1`. -/
theorem symmetricPowerComparison_one_comp_symmetricAlgebraGen (V : VectorBundle S) :
    V.symmetricPowerComparison 1 ≫ Scheme.Modules.symmetricAlgebraGen S (V.grading.piece 1) =
      𝟙 ((Scheme.Modules.symmetricAlgebra S (V.grading.piece 1)).piece 1) := by
  have := V.isIso_symmetricPowerComparison 1
  rw [← IsIso.inv_eq_of_inv_hom_id V.symmetricAlgebraGen_comp_symmetricPowerComparison,
    IsIso.hom_inv_id]

/-- In degree zero the canonical map, followed by the identification `ℰ_0 ≅ 𝒪_S` of the
underlying cone, is an isomorphism `Sym^0(ℰ_1) ≅ 𝒪_S`. -/
theorem isIso_symmetricPowerComparison_zero_comp_degreeZero (V : VectorBundle S) :
    IsIso (V.symmetricPowerComparison 0 ≫ V.degreeZero.hom) := by
  have := V.isIso_symmetricPowerComparison 0
  infer_instance

/-- The direct-image algebra of a vector bundle is the symmetric algebra on its degree-one piece,
with the identity of `ℰ_1` as the degree-one generator. -/
theorem isSymmetricAlgebra (V : VectorBundle S) :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra V.grading (𝟙 (V.grading.piece 1)) := by
  have inst : ∀ n, IsIso (V.symmetricAlgebraDesc.app n) := V.isIso_symmetricPowerComparison
  have hgen : Scheme.Modules.symmetricAlgebraGen S (V.grading.piece 1) ≫
      V.symmetricAlgebraDesc.app 1 = 𝟙 (V.grading.piece 1) :=
    V.symmetricAlgebraGen_comp_symmetricPowerComparison
  have hP : SheafOfModules.GradedAlgebra.PairwiseCommutes
      (Scheme.Modules.symmetricAlgebraGen S (V.grading.piece 1) ≫
        V.symmetricAlgebraDesc.app 1) :=
    hgen ▸ V.pairwiseCommutes
  have h := (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S
    (V.grading.piece 1)).isUniversal.ofDegreewiseIso V.symmetricAlgebraDesc hP
  rwa [hgen] at h

end VectorBundle

end AlgebraicGeometry
