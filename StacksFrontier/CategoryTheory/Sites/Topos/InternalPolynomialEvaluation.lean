module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial evaluation as an internal operation of a ring object

Let `R` be a commutative ring object in a cartesian monoidal category `C` (Mathlib's
`CategoryTheory.CommRingObj`). A polynomial `P` in variables indexed by `κ` whose coefficients
are read into the global sections `𝟙_ C ⟶ R` of `R` defines an *evaluation morphism*: for any
object `A` and any family of coordinates `x : κ → (A ⟶ R)` there is a generalized element
`evalRingHom R c x P : A ⟶ R`, and `P ↦ evalRingHom R c x P` is a ring homomorphism. Taking
`A = ∏ᶜ fun _ : κ => R` and `x` the projections gives the evaluation morphism `Rᵟ ⟶ R` of the
`κ`-fold power of `R` (`evalPowRingHom`).

The point of building evaluation this way — out of the internal structure maps of `R`, through
the ring structure that Mathlib's `CommRingObj.Hom.commRing` puts on each hom-set `A ⟶ R` — is
that it is then *automatically* preserved by every finite-product-preserving functor
(`CommRingObj.map_evalRingHom`): such a functor carries `R` to a commutative ring object
`F.obj R`, acts on generalized elements by ring homomorphisms, and therefore carries the
evaluation of `P` to the evaluation of the very same `P` with its coefficients pushed forward.

This is the content localized in step (2) and step (3) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6). There an affine scheme
`V = Spec(C)` étale over `Y = Spec(B)` is presented as `C = B[x_1, …, x_n]/(P_1, …, P_n)`, the
sheaf `h_V` is cut out of the `n`-fold power of `𝒪_Y` by the vanishing of the `P_i`, and the
comparison morphism `g^{-1} h_V ⟶ h_{X ×_Y V}` is produced by applying the exact functor
`g^{-1}` to that presentation. What makes the second presentation the presentation of
`X ×_Y V = Spec(A ⊗_B C)` is exactly that `g^{-1}` carries the evaluation of `P_i` to the
evaluation of `φ(P_i)`, where `φ : B ⟶ A` is the map on global sections; that is
`CommRingObj.map_evalRingHom`, with the coefficient homomorphism moved by
`Functor.mapGlobalRingHom`.

## Main definitions

* `CategoryTheory.CommRingObj.compRingHom`: precomposition `(B ⟶ R) →+* (A ⟶ R)` along
  `f : A ⟶ B`, the unbundled form of Mathlib's `yonedaCommRingObj`.
* `CategoryTheory.CommRingObj.constRingHom`: the constants `(𝟙_ C ⟶ R) →+* (A ⟶ R)`.
* `CategoryTheory.CommRingObj.evalRingHom`: evaluation of a polynomial at a family of
  coordinates, as a ring homomorphism out of `MvPolynomial κ Γ`.
* `CategoryTheory.CommRingObj.evalPowRingHom`: the same with `A` the `κ`-fold power of `R` and
  the coordinates the projections — the evaluation morphism of the power object.
* `CategoryTheory.CommRingObj.evalSystemHom` and `CategoryTheory.CommRingObj.zeroSystemHom`: the
  two arrows `∏ᵏ R ⟶ ∏ᵛ R` whose equalizer is the object of solutions of a system of polynomial
  equations.
* `CategoryTheory.Functor.commRingObjObj`: the image of a commutative ring object under a
  finite-product-preserving functor.
* `CategoryTheory.Functor.mapRingHom`: a finite-product-preserving functor acts on generalized
  elements of a ring object by a ring homomorphism.
* `CategoryTheory.Functor.mapGlobalRingHom`: the induced map on global sections.

## Main results

* `CategoryTheory.CommRingObj.comp_evalRingHom`: evaluation is natural in `A`, i.e. compatible
  with change of coordinates by precomposition.
* `CategoryTheory.CommRingObj.map_evalRingHom`: **evaluation is preserved by every
  finite-product-preserving functor**, with the coefficients pushed forward along
  `Functor.mapGlobalRingHom`.
* `CategoryTheory.CommRingObj.map_evalPowRingHom`: the same for the evaluation morphism of the
  power object, the two powers being compared by `Limits.piComparison`.
* `CategoryTheory.CommRingObj.map_evalSystemHom` and
  `CategoryTheory.CommRingObj.map_zeroSystemHom`: the two legs of the equalizer presentation of
  the solutions of a system of polynomial equations are each carried, by a
  finite-product-preserving functor, to the corresponding leg for the pushed-forward
  coefficients.

## Implementation notes

The coefficients are carried by an arbitrary ring homomorphism `c : Γ →+* (𝟙_ C ⟶ R)` rather
than being global sections of `R` on the nose. This costs nothing — `RingHom.id` recovers the
global-sections case — and it is what makes the preservation statement sharp: the polynomial `P`
is literally unchanged on both sides of `map_evalRingHom`, only its coefficient homomorphism
moves. In the application `Γ` is the coordinate ring `B` of the base affine scheme, which is the
global sections of `𝒪_Y` only after an identification one does not want to carry around.

`Functor.mapRingHom` is not an instance of `Functor.homMonoidHom`/`Functor.homAddMonoidHom`: it
is the two of them at once, which is the content needed to transport a polynomial.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public section

universe v u v' u'

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory Limits
open scoped MonObj AddMonObj RingObj CommRingObj Obj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

namespace CommRingObj

/-- Precomposition with `f : A ⟶ B` is a ring homomorphism on generalized elements of a
commutative ring object. This is Mathlib's `yonedaCommRingObj R |>.map f.op` with the
`CommRingCat` wrapper removed, so that it composes with `MvPolynomial.eval₂Hom`. -/
def compRingHom (R : C) [CommRingObj R] {A B : C} (f : A ⟶ B) : (B ⟶ R) →+* (A ⟶ R) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' g₁ g₂ := MonObj.comp_mul f g₁ g₂
  map_zero' := AddMonObj.comp_zero f
  map_add' g₁ g₂ := AddMonObj.comp_add f g₁ g₂

/-- `compRingHom R f` sends a generalized element `g : B ⟶ R` to `f ≫ g`. -/
@[simp]
lemma compRingHom_apply (R : C) [CommRingObj R] {A B : C} (f : A ⟶ B) (g : B ⟶ R) :
    compRingHom R f g = f ≫ g :=
  rfl

/-- A global section of a commutative ring object `R` is a generalized element of `R` of every
shape, constant in that shape; this is a ring homomorphism. -/
def constRingHom (R : C) [CommRingObj R] (A : C) : (𝟙_ C ⟶ R) →+* (A ⟶ R) :=
  compRingHom R (toUnit A)

/-- `constRingHom R A` sends a global section `g : 𝟙_ C ⟶ R` to the constant generalized element
`toUnit A ≫ g`. -/
@[simp]
lemma constRingHom_apply (R : C) [CommRingObj R] (A : C) (g : 𝟙_ C ⟶ R) :
    constRingHom R A g = toUnit A ≫ g :=
  rfl

variable (R : C) [CommRingObj R] {Γ : Type*} [CommRing Γ] (c : Γ →+* (𝟙_ C ⟶ R))

/-- **Polynomial evaluation as an internal operation of a ring object.** Given a commutative
ring object `R` in a cartesian monoidal category, a ring homomorphism `c : Γ →+* (𝟙_ C ⟶ R)`
reading the coefficients as global sections of `R`, and a family of coordinates
`x : κ → (A ⟶ R)`, every polynomial `P : MvPolynomial κ Γ` has a value `A ⟶ R`, and taking that
value is a ring homomorphism.

Everything is built from the internal structure maps of `R`: the ring structure on `A ⟶ R` is
Mathlib's `CommRingObj.Hom.commRing`, whose addition and multiplication are `lift` followed by
the internal `σ` and `μ` of `R`. That is what makes evaluation preserved by any
finite-product-preserving functor (`CommRingObj.map_evalRingHom`). -/
noncomputable def evalRingHom {A : C} {κ : Type*} (x : κ → (A ⟶ R)) :
    MvPolynomial κ Γ →+* (A ⟶ R) :=
  MvPolynomial.eval₂Hom ((constRingHom R A).comp c) x

/-- The value of a constant polynomial `MvPolynomial.C r` is the constant generalized element of
the global section `c r`. -/
@[simp]
lemma evalRingHom_C {A : C} {κ : Type*} (x : κ → (A ⟶ R)) (r : Γ) :
    evalRingHom R c x (MvPolynomial.C r) = toUnit A ≫ c r :=
  MvPolynomial.eval₂Hom_C _ _ r

/-- The value of the variable `MvPolynomial.X i` is the `i`-th coordinate `x i`. -/
@[simp]
lemma evalRingHom_X {A : C} {κ : Type*} (x : κ → (A ⟶ R)) (i : κ) :
    evalRingHom R c x (MvPolynomial.X i) = x i :=
  MvPolynomial.eval₂Hom_X' _ _ i

/-- A ring homomorphism out of `A ⟶ R` carries the value of `P` to the image of `P` under a ring
homomorphism `g` out of the polynomial ring, once they agree on constants and variables. -/
private theorem map_evalRingHom_eq {A : C} {κ : Type*} (x : κ → (A ⟶ R)) {T : Type*} [CommRing T]
    (f : (A ⟶ R) →+* T) (g : MvPolynomial κ Γ →+* T)
    (hC : ∀ r, f (toUnit A ≫ c r) = g (MvPolynomial.C r)) (hX : ∀ i, f (x i) = g (MvPolynomial.X i))
    (P : MvPolynomial κ Γ) : f (evalRingHom R c x P) = g P :=
  RingHom.congr_fun (g := g) (MvPolynomial.ringHom_ext (f := f.comp (evalRingHom R c x))
    (fun r => by simpa using hC r) (by simpa using hX)) P

/-- Evaluation is natural in the object of coordinates: precomposing the coordinates with
`f : A ⟶ B` precomposes the value with `f`. -/
lemma comp_evalRingHom {A B : C} (f : A ⟶ B) {κ : Type*} (x : κ → (B ⟶ R))
    (P : MvPolynomial κ Γ) :
    f ≫ evalRingHom R c x P = evalRingHom R c (fun i => f ≫ x i) P := by
  exact map_evalRingHom_eq R c x (compRingHom R f) _ (fun r => by simp [comp_toUnit_assoc])
    (fun i => by simp) P

/-- The evaluation morphism of the `κ`-fold power of a commutative ring object: a polynomial in
`κ` variables is evaluated at the `κ` coordinate projections of `∏ᶜ fun _ : κ => R`. -/
noncomputable def evalPowRingHom (κ : Type*) [HasProduct fun _ : κ => R] :
    MvPolynomial κ Γ →+* ((∏ᶜ fun _ : κ => R) ⟶ R) :=
  evalRingHom R c (Pi.π (fun _ : κ => R))

/-- The value of the variable `MvPolynomial.X i` on the `κ`-fold power of `R` is the `i`-th
projection. -/
@[simp]
lemma evalPowRingHom_X (κ : Type*) [HasProduct fun _ : κ => R] (i : κ) :
    evalPowRingHom R c κ (MvPolynomial.X i) = Pi.π (fun _ : κ => R) i :=
  evalRingHom_X R c _ i

/-- The morphism of a *system* of polynomials: the `ν`-tuple of the evaluation morphisms of a
family `P : ν → MvPolynomial κ Γ` on the `κ`-fold power of `R`. Together with
`CommRingObj.zeroSystemHom` this is the pair of arrows whose equalizer is the object of solutions
of the system `P j = 0`. -/
noncomputable def evalSystemHom (κ : Type*) [HasProduct fun _ : κ => R] {ν : Type*}
    [HasProduct fun _ : ν => R] (P : ν → MvPolynomial κ Γ) :
    (∏ᶜ fun _ : κ => R) ⟶ ∏ᶜ fun _ : ν => R :=
  Pi.lift fun j => evalPowRingHom R c κ (P j)

/-- The `j`-th component of `evalSystemHom R c κ P` is the evaluation morphism of the polynomial
`P j`. -/
@[reassoc (attr := simp)]
lemma evalSystemHom_comp_π (κ : Type*) [HasProduct fun _ : κ => R] {ν : Type*}
    [HasProduct fun _ : ν => R] (P : ν → MvPolynomial κ Γ) (j : ν) :
    evalSystemHom R c κ P ≫ Pi.π (fun _ : ν => R) j = evalPowRingHom R c κ (P j) :=
  Pi.lift_comp_π _ j

/-- The zero arrow from the `κ`-fold power of `R` to its `ν`-fold power, written as the tuple of
the zero generalized elements. The ambient category need not have zero morphisms: the zero here is
the additive unit of the internal addition of `R`, i.e. of `CommRingObj.Hom.commRing`. -/
noncomputable def zeroSystemHom (κ : Type*) [HasProduct fun _ : κ => R] (ν : Type*)
    [HasProduct fun _ : ν => R] : (∏ᶜ fun _ : κ => R) ⟶ ∏ᶜ fun _ : ν => R :=
  Pi.lift fun _ : ν => (0 : (∏ᶜ fun _ : κ => R) ⟶ R)

/-- Every component of `zeroSystemHom R κ ν` is the zero generalized element of `R`. -/
@[reassoc (attr := simp)]
lemma zeroSystemHom_comp_π (κ : Type*) [HasProduct fun _ : κ => R] (ν : Type*)
    [HasProduct fun _ : ν => R] (j : ν) :
    zeroSystemHom R κ ν ≫ Pi.π (fun _ : ν => R) j = 0 :=
  Pi.lift_comp_π _ j

end CommRingObj

namespace Functor

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided]

/-- The image of a commutative ring object under a finite-product-preserving functor. The ring
object structure is `CategoryTheory.Functor.ringObjObj`; commutativity of the multiplication is
transported exactly as the commutativity of the addition is there. -/
noncomputable abbrev commRingObjObj (R : C) [CommRingObj R] : CommRingObj (F.obj R) :=
  letI := F.ringObjObj R
  { toIsCommMonObj :=
      { mul_comm := by
          dsimp
          rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm] } }

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.commRingObjObj

/-- A finite-product-preserving functor acts on the generalized elements of a ring object by a
ring homomorphism: it is simultaneously multiplicative (`Functor.map_mul`, `Functor.map_one`)
and additive (`Functor.map_add'`, `Functor.map_zero'`). -/
noncomputable def mapRingHom (R : C) [RingObj R] (A : C) : (A ⟶ R) →+* (F.obj A ⟶ F.obj R) where
  toFun g := F.map g
  map_one' := F.map_one
  map_mul' _ _ := F.map_mul _ _
  map_zero' := F.map_zero'
  map_add' _ _ := F.map_add' _ _

/-- `F.mapRingHom R A` sends a generalized element `g : A ⟶ R` to `F.map g`. -/
@[simp]
lemma mapRingHom_apply (R : C) [RingObj R] (A : C) (g : A ⟶ R) :
    F.mapRingHom R A g = F.map g :=
  rfl

/-- The global sections of a commutative ring object map along a finite-product-preserving
functor: a global section `𝟙_ C ⟶ R` is carried to `𝟙_ D ⟶ F.obj R` by applying `F` and
precomposing with the unit comparison `ε F`, and this is a ring homomorphism. -/
noncomputable def mapGlobalRingHom (R : C) [CommRingObj R] :
    letI := F.commRingObjObj R
    (𝟙_ C ⟶ R) →+* (𝟙_ D ⟶ F.obj R) :=
  letI := F.commRingObjObj R
  (CommRingObj.compRingHom (F.obj R) (Functor.LaxMonoidal.ε F)).comp (F.mapRingHom R (𝟙_ C))

/-- `F.mapGlobalRingHom R` sends a global section `g : 𝟙_ C ⟶ R` to the global section
`Functor.LaxMonoidal.ε F ≫ F.map g` of `F.obj R`. -/
@[simp]
lemma mapGlobalRingHom_apply (R : C) [CommRingObj R] (g : 𝟙_ C ⟶ R) :
    F.mapGlobalRingHom R g = Functor.LaxMonoidal.ε F ≫ F.map g :=
  rfl

end Functor

namespace CommRingObj

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided] (R : C) [CommRingObj R] {Γ : Type*} [CommRing Γ]
  (c : Γ →+* (𝟙_ C ⟶ R))

open scoped Obj

/-- **Polynomial evaluation is preserved by every finite-product-preserving functor.**

A finite-product-preserving functor `F` carries the commutative ring object `R` to a commutative
ring object `F.obj R` (`Functor.commRingObjObj`) and the coordinates `x i : A ⟶ R` to
coordinates `F.map (x i) : F.obj A ⟶ F.obj R`. The value of a polynomial `P` is then carried to
the value of the *same* `P`, its coefficients read into `F.obj R` through
`Functor.mapGlobalRingHom`.

This is the step localized in the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6): `g^{-1}` carries the evaluation of a
polynomial with coefficients in `Γ(Y, 𝒪_Y)` to the evaluation of that polynomial with its
coefficients pushed into `Γ(X, 𝒪_X)`. -/
theorem map_evalRingHom {A : C} {κ : Type*} (x : κ → (A ⟶ R)) (P : MvPolynomial κ Γ) :
    F.map (evalRingHom R c x P) =
      evalRingHom (F.obj R) ((F.mapGlobalRingHom R).comp c) (fun i => F.map (x i)) P := by
  exact map_evalRingHom_eq R c x (F.mapRingHom R A) _ (fun r => by simp) (fun i => by simp) P

/-- **The evaluation morphism of a power object is preserved by every finite-product-preserving
functor.** The two power objects are compared by `Limits.piComparison`, which is an isomorphism
precisely because `F` preserves the product. -/
theorem map_evalPowRingHom (κ : Type*) [HasProduct fun _ : κ => R]
    [HasProduct fun _ : κ => F.obj R] (P : MvPolynomial κ Γ) :
    F.map (evalPowRingHom R c κ P) =
      piComparison F (fun _ : κ => R) ≫
        evalPowRingHom (F.obj R) ((F.mapGlobalRingHom R).comp c) κ P := by
  have hx : (fun i => F.map (Pi.π (fun _ : κ => R) i)) =
      fun i => piComparison F (fun _ : κ => R) ≫ Pi.π (fun _ : κ => F.obj R) i :=
    funext fun i => (piComparison_comp_π F (fun _ : κ => R) i).symm
  simp only [evalPowRingHom]
  rw [map_evalRingHom, hx, ← comp_evalRingHom]

/-- **The row of a system of polynomial equations is preserved by every finite-product-preserving
functor.** Applying `F` to the arrow `∏ᵏ R ⟶ ∏ᵛ R` given by a family of polynomials and
comparing both powers with `Limits.piComparison` yields the arrow given by the same family, its
coefficients read into `F.obj R`.

This is the commuting square that step (3) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6) applies the exact functor `g^{-1}` to:
the row presenting `h_V` is carried to the row presenting `h_{X ×_Y V}`. -/
theorem map_evalSystemHom (κ : Type*) [HasProduct fun _ : κ => R]
    [HasProduct fun _ : κ => F.obj R] {ν : Type*} [HasProduct fun _ : ν => R]
    [HasProduct fun _ : ν => F.obj R] (P : ν → MvPolynomial κ Γ) :
    F.map (evalSystemHom R c κ P) ≫ piComparison F (fun _ : ν => R) =
      piComparison F (fun _ : κ => R) ≫
        evalSystemHom (F.obj R) ((F.mapGlobalRingHom R).comp c) κ P := by
  refine Pi.hom_ext _ _ fun j => ?_
  rw [Category.assoc, piComparison_comp_π, ← F.map_comp, evalSystemHom_comp_π,
    map_evalPowRingHom, Category.assoc, evalSystemHom_comp_π]

/-- **The zero row is preserved by every finite-product-preserving functor.** The companion of
`CommRingObj.map_evalSystemHom` for the other leg of the equalizer presentation. -/
theorem map_zeroSystemHom (κ : Type*) [HasProduct fun _ : κ => R]
    [HasProduct fun _ : κ => F.obj R] (ν : Type*) [HasProduct fun _ : ν => R]
    [HasProduct fun _ : ν => F.obj R] :
    F.map (zeroSystemHom R κ ν) ≫ piComparison F (fun _ : ν => R) =
      piComparison F (fun _ : κ => R) ≫ zeroSystemHom (F.obj R) κ ν := by
  refine Pi.hom_ext _ _ fun j => ?_
  rw [Category.assoc, piComparison_comp_π, ← F.map_comp, zeroSystemHom_comp_π,
    Category.assoc, zeroSystemHom_comp_π, F.map_zero', AddMonObj.comp_zero]

end CommRingObj

end CategoryTheory
