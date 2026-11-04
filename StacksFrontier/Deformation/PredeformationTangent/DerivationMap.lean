module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.RingTheory.Derivation.Basic
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# The derivation map and its action on first-order deformations

For a predeformation category and a finite-dimensional `k`-vector space `V`, a `Λ`-derivation
`D : k → V` determines two morphisms of `𝒞_Λ`: the map `a ↦ a + D a` from `k` to the
square-zero extension `k[V]`, and the automorphism `a + v ↦ a + (v + D a)` of `k[V]`. Pushing
an object of the special fibre forward along the first gives the derivation map `γ_V`, and
pushing an arbitrary object over `k[V]` forward along the second gives the action `a_V` on
isomorphism classes of objects over `k[V]`.

## Main definitions

* `Deformation.derivationAlgHom`: the algebra map `a ↦ a + D a`.
* `Deformation.derivationTwistAlgHom`: the algebra automorphism `a + v ↦ a + (v + D a)`.
* `Deformation.ArtinianLocalAlgCat.homOfAlgHom`: an algebra map respecting the prescribed
  residue coordinates, read as a morphism of `𝒞_Λ`.
* `Deformation.derivationHom` and `Deformation.derivationTwistHom`: the two morphisms
  transported to a chosen square-zero presentation.
* `Deformation.DerivationMapAndAction`: the two morphisms together with the derivation map and
  the action they induce, including their coordinate and pushforward specifications.
* `Deformation.derivationMapAndAction`: the construction of that data.

## Implementation notes

The square-zero extension is presented by an object of `𝒞_Λ` with chosen coordinates
compatible with the prescribed residue-field identifications. Isomorphism classes are
represented by the skeleton of the corresponding fibre category. The pushforward
specifications state the existence of a lift over the indicated algebra map; the resulting
class is independent of the lift because the category is cofibered in groupoids. Clients use
`gamma` and `action` directly.

The vector space is taken to be an object of `FGModuleCat k`, so that the `Λ`-module and
scalar-tower instances on it which make `TrivSqZeroExt k V` a `Λ`-algebra have `k` determined
by the type of `V`. They are supplied as named definitions and registered only locally,
because for `Λ = k` the resulting `Module Λ V` is not the ambient one.

## References

* [Stacks Project, Section 90.12](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe u v w z u₁ v₁

/-! ### Scalar structures on a finite-dimensional vector space -/

/-- The right action of `k` on a `k`-vector space, used to view a square-zero extension as a
commutative ring. -/
local instance derivationMapModuleMulOpposite (k : Type w) [Field k] (V : FGModuleCat.{z} k) :
    Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The left and right `k`-actions on a `k`-vector space agree. -/
local instance derivationMapIsCentralScalar (k : Type w) [Field k] (V : FGModuleCat.{z} k) :
    IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- A `k`-vector space as a `Λ`-module through the structure map of `k`. -/
local instance derivationMapModuleOfAlgebra (Λ : Type u) (k : Type w) [CommRing Λ]
    [Field k] [Algebra Λ k] (V : FGModuleCat.{z} k) : Module Λ V :=
  Module.compHom V (algebraMap Λ k)

/-- The scalar tower `Λ → k → V`. -/
local instance derivationMapIsScalarTower (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] (V : FGModuleCat.{z} k) : IsScalarTower Λ k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The scalar tower `Λ → kᵐᵒᵖ → V`. -/
local instance derivationMapIsScalarTowerMulOpposite (Λ : Type u) (k : Type w) [CommRing Λ]
    [Field k] [Algebra Λ k] (V : FGModuleCat.{z} k) : IsScalarTower Λ kᵐᵒᵖ V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-! ### The two maps attached to a derivation -/

section Maps

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : FGModuleCat.{z} k}

/-- The algebra map `a ↦ a + D a` from `k` to the trivial square-zero extension by `V`
determined by a derivation `D : k → V`. -/
def derivationAlgHom (D : Derivation Λ k V) : k →ₐ[Λ] TrivSqZeroExt k V where
  toFun a := TrivSqZeroExt.inl a + TrivSqZeroExt.inr (D a)
  map_one' := by simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext <;>
      simp [TrivSqZeroExt.snd_mul, Derivation.leibniz]
  map_zero' := by simp
  map_add' a b := by apply TrivSqZeroExt.ext <;> simp [Derivation.map_add]
  commutes' r := by
    simp only [TrivSqZeroExt.algebraMap_eq_inl']
    simp [Derivation.map_algebraMap]

/-- The automorphism `a + v ↦ a + (v + D a)` of the trivial square-zero extension by `V`
determined by a derivation `D : k → V`. -/
def derivationTwistAlgHom (D : Derivation Λ k V) :
    TrivSqZeroExt k V →ₐ[Λ] TrivSqZeroExt k V where
  toFun x := TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr (x.snd + D x.fst)
  map_one' := by simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext <;>
      simp [TrivSqZeroExt.snd_mul, Derivation.leibniz, smul_add, add_assoc,
        add_comm, add_left_comm]
  map_zero' := by simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [Derivation.map_add]
      abel
  commutes' r := by
    simp only [TrivSqZeroExt.algebraMap_eq_inl']
    simp [Derivation.map_algebraMap]

/-- The coordinate formula for the derivation map. -/
lemma derivationAlgHom_apply (D : Derivation Λ k V) (a : k) :
    derivationAlgHom D a = TrivSqZeroExt.inl a + TrivSqZeroExt.inr (D a) :=
  rfl

/-- The coordinate formula for the twisting automorphism. -/
lemma derivationTwistAlgHom_apply (D : Derivation Λ k V) (a : k) (m : V) :
    derivationTwistAlgHom D (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (m + D a) := by
  simp [derivationTwistAlgHom]

/-- A derivation of `k` into itself, read as a derivation into `V` along a `k`-linear map. -/
noncomputable def derivationOfLinearMap (V : FGModuleCat.{z} k) (e : k →ₗ[k] V)
    (D : Derivation Λ k k) : Derivation Λ k V :=
  e.compDer D

@[simp]
lemma derivationOfLinearMap_apply (V : FGModuleCat.{z} k) (e : k →ₗ[k] V)
    (D : Derivation Λ k k) (a : k) : derivationOfLinearMap V e D a = e (D a) :=
  rfl

end Maps

/-! ### Coordinates on a square-zero object of `𝒞_Λ` -/

section Coordinates
open CategoryTheory

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The underlying algebra of the square-zero object attached to `V` is the trivial
square-zero extension of `k` by `V`, with the scalar structures registered above. -/
noncomputable def squareZeroCoordinates (V : FGModuleCat.{max v w} k) :
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V ≃ₐ[Λ] TrivSqZeroExt k V :=
  AlgEquiv.refl

/-- In those coordinates the prescribed residue-field identification is the first
projection. -/
theorem squareZeroCoordinates_residue (V : FGModuleCat.{max v w} k)
    (a : (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V) :
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V).residueEquiv
        (IsLocalRing.residue ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V) a) =
      (TrivSqZeroExt.fstHom Λ k V) (squareZeroCoordinates V a) :=
  squareZeroExtensionArtinian_residue Λ k V a

end Coordinates

/-! ### Morphisms of `𝒞_Λ` from algebra maps -/

namespace ArtinianLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An algebra map between objects of `𝒞_Λ` which respects the prescribed residue
coordinates is automatically local, hence a morphism of `𝒞_Λ`. -/
def homOfAlgHom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A →ₐ[Λ] B)
    (hres : ∀ a : A, B.residueEquiv (IsLocalRing.residue B (f a)) =
      A.residueEquiv (IsLocalRing.residue A a)) : A ⟶ B := by
  refine ⟨f, ?_, hres⟩
  refine ⟨fun a hunit ↦ ?_⟩
  have hnonzero : IsLocalRing.residue B (f a) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (f a)).2 hunit
  have hnonzero' : IsLocalRing.residue A a ≠ 0 := by
    intro hz
    apply hnonzero
    apply B.residueEquiv.injective
    rw [hres a, hz]
    simp
  exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mp hnonzero'

@[simp]
lemma homOfAlgHom_hom {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A →ₐ[Λ] B)
    (hres : ∀ a : A, B.residueEquiv (IsLocalRing.residue B (f a)) =
      A.residueEquiv (IsLocalRing.residue A a)) :
    (homOfAlgHom f hres).hom = f :=
  rfl

end ArtinianLocalAlgCat

/-! ### The two morphisms in a chosen square-zero presentation -/

section Presentation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : FGModuleCat.{max v w} k}

/-- The derivation map `a ↦ a + D a`, transported to a chosen presentation of the residue
field and of the square-zero extension. -/
def derivationHom {A₀ AV : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (i₀ : A₀ ≃ₐ[Λ] k) (iV : AV ≃ₐ[Λ] TrivSqZeroExt k V)
    (hi₀ : ∀ a : A₀, A₀.residueEquiv (IsLocalRing.residue A₀ a) = i₀ a)
    (hiV : ∀ a : AV, AV.residueEquiv (IsLocalRing.residue AV a) =
      (TrivSqZeroExt.fstHom Λ k V) (iV a))
    (D : Derivation Λ k V) : A₀ ⟶ AV :=
  ArtinianLocalAlgCat.homOfAlgHom
    (iV.symm.toAlgHom.comp ((derivationAlgHom D).comp i₀.toAlgHom))
    (by
      intro a
      calc
        AV.residueEquiv (IsLocalRing.residue AV
            ((iV.symm.toAlgHom.comp ((derivationAlgHom D).comp i₀.toAlgHom)) a))
            = (TrivSqZeroExt.fstHom Λ k V)
                (iV ((iV.symm.toAlgHom.comp
                  ((derivationAlgHom D).comp i₀.toAlgHom)) a)) := hiV _
        _ = (TrivSqZeroExt.fstHom Λ k V) (derivationAlgHom D (i₀ a)) := by simp
        _ = i₀ a := by simp [derivationAlgHom_apply]
        _ = A₀.residueEquiv (IsLocalRing.residue A₀ a) := (hi₀ a).symm)

/-- The twisting automorphism `a + v ↦ a + (v + D a)`, transported to a chosen presentation of
the square-zero extension. -/
def derivationTwistHom {AV : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (iV : AV ≃ₐ[Λ] TrivSqZeroExt k V)
    (hiV : ∀ a : AV, AV.residueEquiv (IsLocalRing.residue AV a) =
      (TrivSqZeroExt.fstHom Λ k V) (iV a))
    (D : Derivation Λ k V) : AV ⟶ AV :=
  ArtinianLocalAlgCat.homOfAlgHom
    (iV.symm.toAlgHom.comp ((derivationTwistAlgHom D).comp iV.toAlgHom))
    (by
      intro a
      calc
        AV.residueEquiv (IsLocalRing.residue AV
            ((iV.symm.toAlgHom.comp
              ((derivationTwistAlgHom D).comp iV.toAlgHom)) a)) =
              (TrivSqZeroExt.fstHom Λ k V)
                (iV ((iV.symm.toAlgHom.comp
                  ((derivationTwistAlgHom D).comp iV.toAlgHom)) a)) := hiV _
        _ = (TrivSqZeroExt.fstHom Λ k V) (derivationTwistAlgHom D (iV a)) := by simp
        _ = (TrivSqZeroExt.fstHom Λ k V) (iV a) := by
              rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (iV a)]
              rw [derivationTwistAlgHom_apply]
              simp
        _ = AV.residueEquiv (IsLocalRing.residue AV a) := (hiV a).symm)

end Presentation

/-! ### Chosen pushforwards -/

section Pushforward

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]

/-- A cofibered category supplies a pushforward of an object of one fibre into another. -/
lemma exists_fiber_pushforward (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x : p.Fiber A) (f : A ⟶ B) :
    ∃ (y : p.Fiber B) (φ : x.1 ⟶ y.1),
      p.map φ = eqToHom x.2 ≫ f ≫ eqToHom y.2.symm := by
  obtain ⟨yraw, φ, hφ⟩ := exists_pushforward hp f x.1 x.2
  let := hφ
  refine ⟨⟨yraw, IsHomLift.codomain_eq p f φ⟩, φ, ?_⟩
  exact IsHomLift.fac' p f φ

/-- A choice of target object and arrow for a pushforward. -/
noncomputable def fiberPushforward (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x : p.Fiber A) (f : A ⟶ B) : Σ y : p.Fiber B, x.1 ⟶ y.1 :=
  let h := exists_fiber_pushforward p hp x f
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

/-- The chosen pushforward arrow lies over the prescribed base map. -/
lemma fiberPushforward_fac (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (x : p.Fiber A) (f : A ⟶ B) :
    p.map (fiberPushforward p hp x f).2 =
      eqToHom x.2 ≫ f ≫ eqToHom (fiberPushforward p hp x f).1.2.symm :=
  Classical.choose_spec (Classical.choose_spec (exists_fiber_pushforward p hp x f))

end Pushforward

/-! ### The derivation map and the action on isomorphism classes -/

section Action

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : FGModuleCat.{max v w} k}
    {F : Type u₁} [Category.{v₁} F]

/-- The maps `f_D` and `f_{1,D}` attached to the derivations `D : k → V`, together with the
derivation map and the action they induce on isomorphism classes of objects over `k[V]`. The
equations specify the actual square-zero maps, and the lift clauses specify pushforward rather
than arbitrary set maps. -/
structure DerivationMapAndAction
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (A₀ AV : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (i₀ : A₀ ≃ₐ[Λ] k) (iV : AV ≃ₐ[Λ] TrivSqZeroExt k V)
    (hi₀ : ∀ a : A₀, A₀.residueEquiv (IsLocalRing.residue A₀ a) = i₀ a)
    (hiV : ∀ a : AV, AV.residueEquiv (IsLocalRing.residue AV a) =
      (TrivSqZeroExt.fstHom Λ k V) (iV a))
    (x₀ : F) (hx₀ : p.obj x₀ = A₀) where
  /-- The morphism `a ↦ a + D a`. -/
  baseMap : Derivation Λ k V → (A₀ ⟶ AV)
  /-- The coordinates of `baseMap`. -/
  baseMap_eq : ∀ (D : Derivation Λ k V) (a : k),
    iV ((baseMap D).hom (i₀.symm a)) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (D a)
  /-- The morphism `a + v ↦ a + (v + D a)`. -/
  twistMap : Derivation Λ k V → (AV ⟶ AV)
  /-- The coordinates of `twistMap`. -/
  twistMap_eq : ∀ (D : Derivation Λ k V) (a : k) (m : V),
    iV ((twistMap D).hom (iV.symm
      (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m))) =
        TrivSqZeroExt.inl a + TrivSqZeroExt.inr (m + D a)
  /-- The derivation map `γ_V`. -/
  gamma : Derivation Λ k V → Skeleton (p.Fiber AV)
  /-- `gamma D` is the class of a pushforward of `x₀` along `baseMap D`. -/
  gamma_pushforward : ∀ D : Derivation Λ k V,
    ∃ (y : p.Fiber AV) (φ : x₀ ⟶ y.1),
      (p.map φ = eqToHom hx₀ ≫ baseMap D ≫ eqToHom y.2.symm) ∧
        (toSkeleton y = gamma D)
  /-- The action `a_V` on isomorphism classes. -/
  action : Derivation Λ k V → Skeleton (p.Fiber AV) → Skeleton (p.Fiber AV)
  /-- `action D x` is the class of a pushforward of a representative of `x` along
  `twistMap D`. -/
  action_pushforward : ∀ (D : Derivation Λ k V) (x : Skeleton (p.Fiber AV)),
    ∃ (x' y : p.Fiber AV) (φ : x'.1 ⟶ y.1),
      (toSkeleton x' = x) ∧
        (p.map φ = eqToHom x'.2 ≫ twistMap D ≫ eqToHom y.2.symm) ∧
          (toSkeleton y = action D x)

/-- **Stacks Project, Section 90.12.** Derivations of the residue field determine the
canonical map to, and the action on, the isomorphism classes of first-order deformations over
`k[V]`. -/
noncomputable def derivationMapAndAction
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (A₀ AV : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (i₀ : A₀ ≃ₐ[Λ] k) (iV : AV ≃ₐ[Λ] TrivSqZeroExt k V)
    (hi₀ : ∀ a : A₀, A₀.residueEquiv (IsLocalRing.residue A₀ a) = i₀ a)
    (hiV : ∀ a : AV, AV.residueEquiv (IsLocalRing.residue AV a) =
      (TrivSqZeroExt.fstHom Λ k V) (iV a))
    (x₀ : F) (hx₀ : p.obj x₀ = A₀) :
    DerivationMapAndAction p A₀ AV i₀ iV hi₀ hiV x₀ hx₀ := by
  let base : Derivation Λ k V → (A₀ ⟶ AV) := fun D => derivationHom i₀ iV hi₀ hiV D
  let twist : Derivation Λ k V → (AV ⟶ AV) := fun D => derivationTwistHom iV hiV D
  let xbase : p.Fiber A₀ := ⟨x₀, hx₀⟩
  let gammaFiber : Derivation Λ k V → p.Fiber AV := fun D =>
    (fiberPushforward p hp.cofibered xbase (base D)).1
  let gammaArrow : (D : Derivation Λ k V) → x₀ ⟶ (gammaFiber D).1 := fun D =>
    (fiberPushforward p hp.cofibered xbase (base D)).2
  let xrep : Skeleton (p.Fiber AV) → p.Fiber AV := fun x =>
    (fromSkeleton (p.Fiber AV)).obj x
  let actionFiber : Derivation Λ k V → Skeleton (p.Fiber AV) → p.Fiber AV :=
    fun D x => (fiberPushforward p hp.cofibered (xrep x) (twist D)).1
  let actionArrow : (D : Derivation Λ k V) → (x : Skeleton (p.Fiber AV)) →
      (xrep x).1 ⟶ (actionFiber D x).1 :=
    fun D x => (fiberPushforward p hp.cofibered (xrep x) (twist D)).2
  refine {
    baseMap := base
    baseMap_eq := ?_
    twistMap := twist
    twistMap_eq := ?_
    gamma := fun D => toSkeleton (gammaFiber D)
    gamma_pushforward := ?_
    action := fun D x => toSkeleton (actionFiber D x)
    action_pushforward := ?_ }
  · intro D a
    change iV (iV.symm (derivationAlgHom D (i₀ (i₀.symm a)))) = _
    simp only [AlgEquiv.apply_symm_apply]
    exact derivationAlgHom_apply D a
  · intro D a m
    change iV (iV.symm (derivationTwistAlgHom D
      (iV (iV.symm (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m))))) = _
    simp only [AlgEquiv.apply_symm_apply]
    exact derivationTwistAlgHom_apply D a m
  · intro D
    exact ⟨gammaFiber D, gammaArrow D,
      fiberPushforward_fac p hp.cofibered xbase (base D), rfl⟩
  · intro D x
    exact ⟨xrep x, actionFiber D x, actionArrow D x,
      toSkeleton_fromSkeleton_obj x,
      fiberPushforward_fac p hp.cofibered (xrep x) (twist D), rfl⟩

/-! ### The canonical square-zero presentation -/

section SquareZeroPresentation

variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {A₀ : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {i₀ : A₀ ≃ₐ[Λ] k}
    {hi₀ : ∀ a : A₀, A₀.residueEquiv (IsLocalRing.residue A₀ a) = i₀ a}
    {x₀ : F} {hx₀ : p.obj x₀ = A₀}

/-- In the canonical coordinates on the square-zero object attached to `V`, the derivation
map is `a ↦ a + D a`. -/
theorem DerivationMapAndAction.baseMap_apply
    (d : DerivationMapAndAction p A₀ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V)
      i₀ (squareZeroCoordinates V) hi₀ (squareZeroCoordinates_residue V) x₀ hx₀)
    (D : Derivation Λ k V) (a : k) :
    (d.baseMap D).hom (i₀.symm a) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (D a) :=
  d.baseMap_eq D a

/-- In the canonical coordinates on the square-zero object attached to `V`, the twisting
automorphism is `a + v ↦ a + (v + D a)`. -/
theorem DerivationMapAndAction.twistMap_apply
    (d : DerivationMapAndAction p A₀ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V)
      i₀ (squareZeroCoordinates V) hi₀ (squareZeroCoordinates_residue V) x₀ hx₀)
    (D : Derivation Λ k V) (a : k) (m : V) :
    (d.twistMap D).hom (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (m + D a) :=
  d.twistMap_eq D a m

/-- The sum `inl a + inr m` in the trivial square-zero extension is the pair `(a, m)`. -/
private theorem inl_add_inr_eq_mk {k : Type w} [Field k] {V : FGModuleCat.{z} k}
    (a : k) (m : V) :
    (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m : TrivSqZeroExt k V) = (a, m) :=
  TrivSqZeroExt.inl_fst_add_inr_snd_eq ((a, m) : TrivSqZeroExt k V)

/-- In the canonical coordinates on the square-zero object attached to `V`, the twisting
automorphism is `(a, v) ↦ (a, v + D a)` in pair coordinates. -/
theorem DerivationMapAndAction.twistMap_apply_pair
    (d : DerivationMapAndAction p A₀ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V)
      i₀ (squareZeroCoordinates V) hi₀ (squareZeroCoordinates_residue V) x₀ hx₀)
    (D : Derivation Λ k V) (a : k) (m : V) :
    (d.twistMap D).hom ((a, m) : TrivSqZeroExt k V) =
      ((a, m + D a) : TrivSqZeroExt k V) := by
  rw [← inl_add_inr_eq_mk, ← inl_add_inr_eq_mk]
  exact d.twistMap_apply D a m

/-- In the canonical coordinates on the square-zero object attached to `V`, the derivation
map is `a ↦ (a, D a)` in pair coordinates. -/
theorem DerivationMapAndAction.baseMap_apply_pair
    (d : DerivationMapAndAction p A₀ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V)
      i₀ (squareZeroCoordinates V) hi₀ (squareZeroCoordinates_residue V) x₀ hx₀)
    (D : Derivation Λ k V) (a : k) :
    (d.baseMap D).hom (i₀.symm a) = ((a, D a) : TrivSqZeroExt k V) := by
  rw [← inl_add_inr_eq_mk]
  exact d.baseMap_apply D a

/-- The canonical choice of derivation map and action in the square-zero presentation. -/
noncomputable def squareZeroDerivationMapAndAction
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (A₀ : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (i₀ : A₀ ≃ₐ[Λ] k)
    (hi₀ : ∀ a : A₀, A₀.residueEquiv (IsLocalRing.residue A₀ a) = i₀ a)
    (V : FGModuleCat.{max v w} k) (x₀ : F) (hx₀ : p.obj x₀ = A₀) :
    DerivationMapAndAction p A₀ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V)
      i₀ (squareZeroCoordinates V) hi₀ (squareZeroCoordinates_residue V) x₀ hx₀ :=
  derivationMapAndAction p hp A₀
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj V) i₀
    (squareZeroCoordinates V) hi₀ (squareZeroCoordinates_residue V) x₀ hx₀

end SquareZeroPresentation

end Action

end

end Deformation
