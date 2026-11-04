module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxTransform
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Linear
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.SituationBoxPairing
public import StacksFrontier.CategoryTheory.Linear.BoxPairingTransport

/-!
# The derived box pairing

For schemes `X`, `Y` over a scheme `S`, the derived external product of morphisms
`a : E ⟶ E'` in `D(𝒪_X)` and `b : B ⟶ B'` in `D(𝒪_Y)` is a morphism in `D(𝒪_{X ×_S Y})`
compatible with composition. When `S = Spec k` for a field `k`, it is `k`-bilinear, so for
`k`-linear families `θ` into `D(𝒪_X)` and `ψ` into `D(𝒪_Y)` compatible with composition, the
pairing `(a, b) ↦ θ(a) ⊠ ψ(b)` is a box pairing in the sense of
`CategoryTheory.Linear.BoxPairing`.

## Main definitions

* `AlgebraicGeometry.derivedBoxMap`: the derived external product of two morphisms.
* `AlgebraicGeometry.derivedBoxPairing`: the derived box pairing `(a, b) ↦ θ(a) ⊠ ψ(b)`.

## Main results

* `AlgebraicGeometry.derivedBoxMap_comp`: the derived external product of morphisms is
  compatible with composition.
* `AlgebraicGeometry.derivedBoxMapLeft_smul`, `AlgebraicGeometry.derivedBoxMapRight_smul`: the
  derived external product of morphisms is `k`-linear in each factor.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Derived

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The derived external product of two morphisms. -/
def derivedBoxMap {E E' : DerivedCategory X.Modules} {B B' : DerivedCategory Y.Modules}
    (a : E ⟶ E') (b : B ⟶ B') : derivedBox f g E B ⟶ derivedBox f g E' B' :=
  derivedBoxMapLeft f g a B ≫ derivedBoxMapRight f g E' b

/-- The two composites `E ⊠ B ⟶ E' ⊠ B'` of the one-sided derived external products agree:
`(E ⊠ b) ≫ (a ⊠ B') = (a ⊠ B) ≫ (E' ⊠ b)`. -/
theorem derivedBoxMapLeft_comp_derivedBoxMapRight {E E' : DerivedCategory X.Modules}
    {B B' : DerivedCategory Y.Modules} (a : E ⟶ E') (b : B ⟶ B') :
    derivedBoxMapRight f g E b ≫ derivedBoxMapLeft f g a B' =
      derivedBoxMapLeft f g a B ≫ derivedBoxMapRight f g E' b :=
  (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).map
    ((fourierMukaiPullback f g).map a)).naturality ((dpull (pullback.snd f g)).map b))

/-- The derived external product of morphisms is compatible with composition:
`(a ⊠ b) ≫ (a' ⊠ b') = (a ≫ a') ⊠ (b ≫ b')`. -/
theorem derivedBoxMap_comp {E E' E'' : DerivedCategory X.Modules}
    {B B' B'' : DerivedCategory Y.Modules} (a : E ⟶ E') (b : B ⟶ B') (a' : E' ⟶ E'')
    (b' : B' ⟶ B'') :
    derivedBoxMap f g a b ≫ derivedBoxMap f g a' b' = derivedBoxMap f g (a ≫ a') (b ≫ b') := by
  have hl : derivedBoxMapLeft f g (a ≫ a') B =
      derivedBoxMapLeft f g a B ≫ derivedBoxMapLeft f g a' B := by
    unfold derivedBoxMapLeft
    rw [CategoryTheory.Functor.map_comp (fourierMukaiPullback f g)]
    exact NatTrans.congr_app (CategoryTheory.Functor.map_comp _ _ _) _
  have hr : derivedBoxMapRight f g E'' (b ≫ b') =
      derivedBoxMapRight f g E'' b ≫ derivedBoxMapRight f g E'' b' := by
    unfold derivedBoxMapRight
    rw [CategoryTheory.Functor.map_comp (dpull (pullback.snd f g))]
    exact CategoryTheory.Functor.map_comp _ _ _
  simp only [derivedBoxMap, hl, hr, Category.assoc]
  rw [← Category.assoc (derivedBoxMapRight f g E' b),
    derivedBoxMapLeft_comp_derivedBoxMapRight f g a' b]
  simp only [Category.assoc]

end Derived

section Linear

variable (k : Type u) [Field k] (A B : Over (Spec (.of k)))

/-- The braiding of the derived tensor product, as an isomorphism between tensoring on the left
and on the right with a fixed object. -/
def derivedTensorFlipIso (W : Scheme.{u}) (C : DerivedCategory W.Modules) :
    (derivedTensorProductFunctor W.toRingedSpace.sheaf).flip.obj C ≅
      (derivedTensorProductFunctor W.toRingedSpace.sheaf).obj C :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal W.toRingedSpace.sheaf
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric W.toRingedSpace.sheaf
  NatIso.ofComponents (fun D => β_ D C) (fun d => BraidedCategory.braiding_naturality_left d C)

/-- Tensoring on the left with a fixed object of `D(𝒪_Z)` is `k`-linear. -/
theorem derivedTensor_obj_linear (Z : Over (Spec (.of k))) (C : DerivedCategory Z.left.Modules) :
    letI : Linear k (Stacks.DerivedTensor.RingedSite.Modules Z.left.toRingedSpace.sheaf) :=
      modulesLinear k Z
    ((derivedTensorProductFunctor Z.left.toRingedSpace.sheaf).obj C).Linear k :=
  let : Linear k (Stacks.DerivedTensor.RingedSite.Modules Z.left.toRingedSpace.sheaf) :=
    modulesLinear k Z
  have := derivedTensor_flip_obj_linear k Z C
  Functor.linear_of_iso _ (derivedTensorFlipIso Z.left C)

variable {k A B}

/-- **The derived external product of morphisms is `k`-linear in the first factor.** -/
theorem derivedBoxMapLeft_smul (r : k) {E E' : DerivedCategory A.left.Modules} (a : E ⟶ E')
    (C : DerivedCategory B.left.Modules) :
    letI : Linear k A.left.Modules := modulesLinear k A
    letI : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
    letI : Linear k (Stacks.DerivedTensor.RingedSite.Modules
      (pullback A.hom B.hom).toRingedSpace.sheaf) := modulesLinear k (overPullback k A B)
    derivedBoxMapLeft A.hom B.hom (r • a) C = r • derivedBoxMapLeft A.hom B.hom a C := by
  let : Linear k A.left.Modules := modulesLinear k A
  let : Linear k (SheafOfModules (structureSheafRing A.left.toRingedSpace)) := modulesLinear k A
  let : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
  let : Linear k (SheafOfModules (structureSheafRing (pullback A.hom B.hom).toRingedSpace)) :=
    modulesLinear k (overPullback k A B)
  let : Linear k (Stacks.DerivedTensor.RingedSite.Modules
    (pullback A.hom B.hom).toRingedSpace.sheaf) := modulesLinear k (overPullback k A B)
  have : (fourierMukaiPullback A.hom B.hom).Linear k := derivedPullback_linear k
    (Over.homMk (pullback.fst A.hom B.hom) rfl : overPullback k A B ⟶ A)
  have hT := derivedTensor_flip_obj_linear k (overPullback k A B)
    ((dpull (pullback.snd A.hom B.hom)).obj C)
  show ((derivedTensorProductFunctor (pullback A.hom B.hom).toRingedSpace.sheaf).flip.obj
      ((dpull (pullback.snd A.hom B.hom)).obj C)).map ((fourierMukaiPullback A.hom B.hom).map
        (r • a)) =
    r • ((derivedTensorProductFunctor (pullback A.hom B.hom).toRingedSpace.sheaf).flip.obj
      ((dpull (pullback.snd A.hom B.hom)).obj C)).map ((fourierMukaiPullback A.hom B.hom).map a)
  rw [Functor.map_smul]
  exact hT.map_smul _ _

/-- **The derived external product of morphisms is `k`-linear in the second factor.** -/
theorem derivedBoxMapRight_smul (r : k) (E : DerivedCategory A.left.Modules)
    {C C' : DerivedCategory B.left.Modules} (b : C ⟶ C') :
    letI : Linear k B.left.Modules := modulesLinear k B
    letI : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
    letI : Linear k (Stacks.DerivedTensor.RingedSite.Modules
      (pullback A.hom B.hom).toRingedSpace.sheaf) := modulesLinear k (overPullback k A B)
    derivedBoxMapRight A.hom B.hom E (r • b) = r • derivedBoxMapRight A.hom B.hom E b := by
  let : Linear k B.left.Modules := modulesLinear k B
  let : Linear k (SheafOfModules (structureSheafRing B.left.toRingedSpace)) := modulesLinear k B
  let : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
  let : Linear k (SheafOfModules (structureSheafRing (pullback A.hom B.hom).toRingedSpace)) :=
    modulesLinear k (overPullback k A B)
  let : Linear k (Stacks.DerivedTensor.RingedSite.Modules
    (pullback A.hom B.hom).toRingedSpace.sheaf) := modulesLinear k (overPullback k A B)
  have : (dpull (pullback.snd A.hom B.hom)).Linear k := derivedPullback_linear k
    (Over.homMk (pullback.snd A.hom B.hom) pullback.condition.symm : overPullback k A B ⟶ B)
  have hT := derivedTensor_obj_linear k (overPullback k A B)
    ((fourierMukaiPullback A.hom B.hom).obj E)
  show ((derivedTensorProductFunctor (pullback A.hom B.hom).toRingedSpace.sheaf).obj
      ((fourierMukaiPullback A.hom B.hom).obj E)).map ((dpull (pullback.snd A.hom B.hom)).map
        (r • b)) = r • ((derivedTensorProductFunctor (pullback A.hom B.hom).toRingedSpace.sheaf).obj
      ((fourierMukaiPullback A.hom B.hom).obj E)).map ((dpull (pullback.snd A.hom B.hom)).map b)
  rw [Functor.map_smul]
  exact hT.map_smul _ _

/-- Tensoring on the right with a fixed object is additive. -/
theorem derivedTensorFlipAdditive (W : Scheme.{u}) (C : DerivedCategory W.Modules) :
    ((derivedTensorProductFunctor W.toRingedSpace.sheaf).flip.obj C).Additive := by
  let := (canonicalDerivedTensorProduct W.toRingedSpace.sheaf).commShift_left C
  have := (canonicalDerivedTensorProduct W.toRingedSpace.sheaf).exact_left C
  infer_instance

/-- Tensoring on the left with a fixed object is additive. -/
theorem derivedTensorObjAdditive (W : Scheme.{u}) (C : DerivedCategory W.Modules) :
    ((derivedTensorProductFunctor W.toRingedSpace.sheaf).obj C).Additive :=
  have := derivedTensorFlipAdditive W C
  Functor.additive_of_iso (derivedTensorFlipIso W C)

/-- The derived pullback along a morphism of schemes is additive. -/
instance dpull_additive {V W : Scheme.{u}} (p : V ⟶ W) : (dpull p).Additive := by
  let h₁ : (dpull p).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift (f := p.toLRSHom.toShHom)
  have h₂ : (dpull p).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated
      (f := p.toLRSHom.toShHom)
  infer_instance

/-- The derived external product of morphisms is additive in the first factor. -/
theorem derivedBoxMapLeft_add {E E' : DerivedCategory A.left.Modules} (a a' : E ⟶ E')
    (C : DerivedCategory B.left.Modules) :
    derivedBoxMapLeft A.hom B.hom (a + a') C =
      derivedBoxMapLeft A.hom B.hom a C + derivedBoxMapLeft A.hom B.hom a' C := by
  show ((derivedTensorProductFunctor (pullback A.hom B.hom).toRingedSpace.sheaf).flip.obj
      ((dpull (pullback.snd A.hom B.hom)).obj C)).map ((fourierMukaiPullback A.hom B.hom).map
        (a + a')) = _
  rw [Functor.map_add]
  exact (derivedTensorFlipAdditive _ _).map_add

/-- The derived external product of morphisms is additive in the second factor. -/
theorem derivedBoxMapRight_add (E : DerivedCategory A.left.Modules)
    {C C' : DerivedCategory B.left.Modules} (b b' : C ⟶ C') :
    derivedBoxMapRight A.hom B.hom E (b + b') =
      derivedBoxMapRight A.hom B.hom E b + derivedBoxMapRight A.hom B.hom E b' := by
  show ((derivedTensorProductFunctor (pullback A.hom B.hom).toRingedSpace.sheaf).obj
      ((fourierMukaiPullback A.hom B.hom).obj E)).map ((dpull (pullback.snd A.hom B.hom)).map
        (b + b')) = _
  rw [Functor.map_add]
  exact (derivedTensorObjAdditive _ _).map_add

variable (k)
variable {𝒳 𝒢 : Type*} [Category* 𝒳] [Category* 𝒢] [Preadditive 𝒳] [Preadditive 𝒢]
  [Linear k 𝒳] [Linear k 𝒢] (E : ℕ → 𝒳) (G : ℕ → 𝒢)

/-- **The derived box pairing**: for families of `k`-linear maps `θ`, `ψ` carrying morphisms
between the `Eᵢ` and the `Gᵢ` to morphisms in `D(𝒪_X)` and `D(𝒪_Y)` compatibly with
composition, the pairing `(a, b) ↦ θ(a) ⊠ ψ(b)` on `X ×_k Y`. -/
def derivedBoxPairing (Eo : ℕ → DerivedCategory A.left.Modules)
    (Go : ℕ → DerivedCategory B.left.Modules)
    (θ : ∀ i j, letI : Linear k A.left.Modules := modulesLinear k A
      (E i ⟶ E j) →ₗ[k] (Eo i ⟶ Eo j))
    (θ_comp : ∀ i j l (a : E i ⟶ E j) (a' : E j ⟶ E l), θ i l (a ≫ a') = θ i j a ≫ θ j l a')
    (ψ : ∀ i j, letI : Linear k B.left.Modules := modulesLinear k B
      (G i ⟶ G j) →ₗ[k] (Go i ⟶ Go j))
    (ψ_comp : ∀ i j l (b : G i ⟶ G j) (b' : G j ⟶ G l), ψ i l (b ≫ b') = ψ i j b ≫ ψ j l b') :
    letI : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
    Linear.BoxPairing (k := k) E G (fun i => derivedBox A.hom B.hom (Eo i) (Go i)) :=
  letI : Linear k A.left.Modules := modulesLinear k A
  letI : Linear k B.left.Modules := modulesLinear k B
  letI : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
  { box := fun i j => LinearMap.mk₂ k (fun a b => derivedBoxMap A.hom B.hom (θ i j a) (ψ i j b))
      (fun a a' b => by
        simp only [derivedBoxMap, map_add, derivedBoxMapLeft_add, Preadditive.add_comp])
      (fun r a b => by
        simp only [derivedBoxMap, map_smul, derivedBoxMapLeft_smul, Linear.smul_comp])
      (fun a b b' => by
        simp only [derivedBoxMap, map_add, derivedBoxMapRight_add, Preadditive.comp_add])
      (fun r a b => by
        simp only [derivedBoxMap, map_smul, derivedBoxMapRight_smul, Linear.comp_smul])
    box_comp := fun i j l a b a' b' => by
      simp only [LinearMap.mk₂_apply, derivedBoxMap_comp, θ_comp, ψ_comp] }

end Linear

end AlgebraicGeometry
