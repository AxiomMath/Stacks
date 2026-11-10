module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.TangentSpace.LinearFunctor

/-!
# Tangent spaces of functors on algebras

The tangent space of a set-valued functor on algebras is its value on the
dual numbers. This file constructs the module structure on tangent spaces, the linear map induced
by a morphism of functors, and the behaviour under tensor products.

## Main definitions

* `trivSqZeroExtFunctor` sends `M` to the augmentation
  `R ⊕ M → R`.
* `squareZeroExtensionRestriction` restricts the square-zero extension
  functor to the given full subcategory.
* `tangentSpaceSetFunctor` is the functor `M ↦ F(R[M])`.
* `TangentSpaceFunctorConditions` records the singleton and binary
  product hypotheses.
* `dualNumbersOver` is the dual numbers over `R`, regarded as an `S`-algebra over `R`.
* `TangentSpace` is the value of a functor on that object.
* `artinianLocalOverToArtinian` converts the strictly full subcategory of
  augmented Artinian local algebras to the residue-field presentation of `𝒞_Λ`.
* `squareZeroExtensionArtinian` constructs finite-dimensional square-zero
  extensions in `𝒞_Λ`, allowing independent universes for the field and the vector space.
* `tangentSpaceArtinian` evaluates a functor on `𝒞_Λ` at the dual numbers.

## Main results

* `trivSqZeroExtFunctor_preservesFiniteProducts` states that this
  functor preserves finite products.
* `tangentSpaceModuleStructure` equips `M ↦ F(R[M])` with its
  natural `R`-linear, module-valued lift.
* `naturalTransformation_linearMapOnSquareZeroExtensions` states that
  every component on a square-zero extension is linear for the natural module
  structures.
* `tangentSpaceFunctor_iso_tensorLeft` identifies the
  module-valued tangent-space functor with tensoring by its value on the
  one-dimensional vector space.

## Implementation notes

### Trivial square-zero extensions preserve products

The category `S-Alg/R` is represented by
`Over (CommAlgCat.of S R)`, and `R[M]` by Mathlib's `TrivSqZeroExt R M`.
The augmentation is `TrivSqZeroExt.fstHom` and functoriality in `M` is
`TrivSqZeroExt.map`.

### Natural module structures on tangent-space functors

The strictly full subcategory is represented by an isomorphism-closed object
property and its full subcategory. The square-zero extension functor is the
restriction to finitely generated modules of the functor from Tag 06I9. The
conclusion uses `LinearFunctorLift`; in particular, it records both
naturality and the canonical `R`-linearity of the lift, not merely a choice of
module structure on each value.

The source writes `R` and `R[M] ×_R R[N]` where the statement below uses the
canonical models `R[0]` and `R[M × N]` supplied by the product-preserving
square-zero extension functor.

### Tangent spaces of functors on algebras

An `S`-algebra equipped with a map to `R` is represented by an object of
`Over (CommAlgCat.of S R)`. A full subcategory is represented by an `ObjectProperty` and its
`FullSubcategory`. Only membership of the dual numbers is needed to define the tangent space;
the stronger closure assumptions on the category and the singleton condition at `R` are needed
to construct the natural module structure, not for this definition.

The base ring and residue algebra have independent universes. The chosen dual-number object
is exactly the value of `squareZeroExtensionFunctor` on the free rank-one module `R`.
Thus, for a membership hypothesis `hP` as in Tag 06IA,
`TangentSpace S R P (hP (FGModuleCat.of R R)) F` is definitionally the corresponding value of
`tangentSpaceSetFunctor`. Both definitions are abbreviations so clients can use this
interface without transport.

The Over-model API uses the same carrier universe for the field and its modules; the
coefficient ring has an independent universe. The direct Artinian model also allows an
independent module universe. Its dual-number object uses `ULift k` as the rank-one module,
so it exists in any carrier universe containing `k`.

### Morphisms induce linear maps on tangent spaces

The module structures supplied by Tag 06IA are packaged as module-valued
functors whose underlying set-valued functors are propositionally equal to the
original functors.  The displayed casts are precisely these identifications.
Thus the equation below says that the underlying function of the linear map is
the given component of the natural transformation.  Taking `M = R` gives the
map on the tangent spaces of Tag 06IB.

### Tangent spaces and tensor products

The natural module structure supplied by Tag 06IA is used throughout. Its
value on the one-dimensional vector space has underlying set
`TangentSpace`, by the common square-zero-extension model. The
conclusion is stated as an isomorphism of functors, so it includes both the
isomorphism for every finite-dimensional vector space and its naturality in
that vector space.

## References

* [Stacks Project, Tag 06I9](https://stacks.math.columbia.edu/tag/06I9)
* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
* [Stacks Project, Tag 06IB](https://stacks.math.columbia.edu/tag/06IB)
* [Stacks Project, Tag 06ID](https://stacks.math.columbia.edu/tag/06ID)
* [Stacks Project, Tag 06IE](https://stacks.math.columbia.edu/tag/06IE)
-/

@[expose] public section

namespace Deformation

/-! ### Trivial square-zero extensions preserve products -/

section
open CategoryTheory CategoryTheory.Limits
open scoped RightActions
universe s u

variable (S : Type s) (R : Type u) [CommRing S] [CommRing R] [Algebra S R]

local instance (M : ModuleCat.{u} R) : Module Rᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring R M

local instance (M : ModuleCat.{u} R) : Module S M :=
  Module.compHom M (algebraMap S R)

local instance (M : ModuleCat.{u} R) : IsCentralScalar R M :=
  Module.isCentralScalar_oppositeOfCommSemiring R M

local instance (M : ModuleCat.{u} R) : IsScalarTower S R M :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

local instance (M : ModuleCat.{u} R) : IsScalarTower S Rᵐᵒᵖ M :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The functor taking an `R`-module `M` to the trivial square-zero extension
`R ⊕ M`, regarded via its augmentation as an `S`-algebra over `R`. -/
@[ega "0 18.2.3" "special case",
  ega "0 18.4.1" "special case",
  ega "0 22.1.3",
  sga "3 II 2.1" "special case",
  sga "3 XI 1.9",
  sga "7 VI 1.15",
  sga "7 VI 1.3(c)" "partial"]
public def trivSqZeroExtFunctor :
    ModuleCat.{u} R ⥤ Over (CommAlgCat.of S R) where
  obj M := Over.mk
    (CommAlgCat.ofHom ((TrivSqZeroExt.fstHom R R M).restrictScalars S))
  map {M N} f := Over.homMk
    (CommAlgCat.ofHom ((TrivSqZeroExt.map f.hom).restrictScalars S)) (by
      ext x
      simp)
  map_id M := by
    ext x; simp
  map_comp f g := by
    ext x
    apply TrivSqZeroExt.ext
    · simp
    · simp

/-- The trivial square-zero extension functor from `R`-modules to
`S`-algebras over `R` preserves finite products. -/
@[stacks 06I9, sga "7 VI 1.3(c)" "more general"]
theorem trivSqZeroExtFunctor_preservesFiniteProducts :
    PreservesFiniteProducts (trivSqZeroExtFunctor S R) := by
  refine ⟨fun n ↦ ⟨fun {K} ↦ ?_⟩⟩
  let Z : Fin n → ModuleCat.{u} R := fun i ↦ K.obj ⟨i⟩
  let e : K ≅ Discrete.functor Z := Discrete.natIso fun ⟨i⟩ ↦ Iso.refl _
  have hZ : PreservesLimit (Discrete.functor Z) (trivSqZeroExtFunctor S R) := by
    let t := ModuleCat.productCone Z
    apply preservesLimit_of_preserves_limit_cone (ModuleCat.productConeIsLimit Z)
    refine ⟨?_, ?_, ?_⟩
    · intro s
      let f : (i : Fin n) → s.pt.left → TrivSqZeroExt R (Z i) :=
        fun i x ↦ (s.π.app ⟨i⟩).left.hom x
      exact Over.homMk (CommAlgCat.ofHom {
      toFun := fun x ↦ (s.pt.hom.hom x, fun i ↦ (f i x).snd)
      map_one' := by
        apply Prod.ext
        · exact s.pt.hom.hom.map_one
        · funext i
          change TrivSqZeroExt.snd (f i 1) = (0 : Z i)
          have h := (s.π.app ⟨i⟩).left.hom.map_one
          change f i 1 = (1 : TrivSqZeroExt R (Z i)) at h
          simpa only [TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_zero] using congrArg
            (TrivSqZeroExt.snd (R := R) (M := Z i)) h
      map_mul' := by
        intro x y; apply Prod.ext
        · exact (s.pt.hom.hom.map_mul x y)
        · funext i
          have h := (s.π.app ⟨i⟩).left.hom.map_mul x y
          change f i (x * y) = f i x * f i y at h
          have hx : (f i x).fst = s.pt.hom.hom x := congrArg (fun q ↦ q x) (s.π.app ⟨i⟩).w
          have hy : (f i y).fst = s.pt.hom.hom y := congrArg (fun q ↦ q y) (s.π.app ⟨i⟩).w
          convert congrArg (TrivSqZeroExt.snd (R := R) (M := Z i)) h using 1
          simp only [TrivSqZeroExt.snd, Functor.const_obj_obj, Functor.comp_obj,
            Discrete.functor_obj_eq_as, Z, f]
          try { rw [← hx, ← hy]; rfl }
      map_zero' := by
        apply Prod.ext
        · exact s.pt.hom.hom.map_zero
        · funext i
          change TrivSqZeroExt.snd (f i 0) = (0 : Z i)
          have h := (s.π.app ⟨i⟩).left.hom.map_zero
          change f i 0 = (0 : TrivSqZeroExt R (Z i)) at h
          simpa only [TrivSqZeroExt.snd_zero] using congrArg (TrivSqZeroExt.snd (R := R) (M := Z i))
            h
      map_add' := by
        intro x y; apply Prod.ext
        · exact (s.pt.hom.hom.map_add x y)
        · funext i
          change TrivSqZeroExt.snd (f i (x + y)) =
            TrivSqZeroExt.snd (f i x + f i y)
          have h := (s.π.app ⟨i⟩).left.hom.map_add x y
          change f i (x + y) = f i x + f i y at h
          simpa only [TrivSqZeroExt.snd_add] using congrArg (TrivSqZeroExt.snd (R := R) (M := Z i))
            h
      commutes' := by
        intro r; apply Prod.ext
        · exact s.pt.hom.hom.commutes r
        · funext i
          change TrivSqZeroExt.snd (f i ((algebraMap S s.pt.left) r)) = 0
          exact (congrArg (TrivSqZeroExt.snd (R := R) (M := Z i)) ((s.π.app ⟨i⟩).left.hom.commutes
            r)).trans (by rfl) }) (by ext x; rfl)
    · intro s j
      rcases j with ⟨j⟩
      dsimp [t]
      apply Over.OverMorphism.ext
      ext x
      dsimp [trivSqZeroExtFunctor]
      have h := congrArg (fun q ↦ q x) (s.π.app ⟨j⟩).w
      dsimp [t, ModuleCat.productCone, trivSqZeroExtFunctor] at h
      apply TrivSqZeroExt.ext
      · change TrivSqZeroExt.fst (TrivSqZeroExt.map (LinearMap.proj j) _) = _
        simp only [ModuleCat.productCone, Fan.mk_pt, Over.homMk_left, TrivSqZeroExt.fst_map]
        exact h.symm
      · change (TrivSqZeroExt.map (LinearMap.proj j) _).snd = _
        exact (TrivSqZeroExt.snd_map (LinearMap.proj j) _).trans rfl
    · intro s m w
      apply Over.OverMorphism.ext
      ext x
      apply TrivSqZeroExt.ext
      · exact congrArg (fun g ↦ g x) m.w
      · funext i
        dsimp [trivSqZeroExtFunctor]
        change ((m.left.hom x).snd i) = ((s.π.app ⟨i⟩).left.hom x).snd
        have hi := congrArg (fun g ↦ (g x).snd) (congrArg (fun q ↦ q.left.hom) (w ⟨i⟩))
        dsimp [t, ModuleCat.productCone, trivSqZeroExtFunctor] at hi
        simp only at hi
        exact (TrivSqZeroExt.snd_map (LinearMap.proj i) _).symm.trans hi
  let := hZ
  exact preservesLimit_of_iso_diagram (trivSqZeroExtFunctor S R) e.symm

end

/-! ### Natural module structures on tangent-space functors -/

section
open CategoryTheory
universe s u v

variable (S : Type s) (R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- The trivial square-zero extension functor, restricted to finitely generated
`R`-modules. -/
abbrev squareZeroExtensionFunctor :
    FGModuleCat.{u} R ⥤ Over (CommAlgCat.of S R) :=
  forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
    trivSqZeroExtFunctor S R

/-- The zero finitely generated `R`-module, in the concrete model used in the
singleton hypothesis. -/
abbrev zeroFGModule : FGModuleCat.{u} R := FGModuleCat.of R PUnit

/-- The product of two finitely generated `R`-modules. -/
abbrev prodFGModule (M N : FGModuleCat.{u} R) : FGModuleCat.{u} R :=
  FGModuleCat.of R (M × N)

/-- The first projection from the product of two finitely generated modules. -/
abbrev prodFst (M N : FGModuleCat.{u} R) : prodFGModule R M N ⟶ M :=
  FGModuleCat.ofHom (LinearMap.fst R M N)

/-- The second projection from the product of two finitely generated modules. -/
abbrev prodSnd (M N : FGModuleCat.{u} R) : prodFGModule R M N ⟶ N :=
  FGModuleCat.ofHom (LinearMap.snd R M N)

/-- Restriction of `M ↦ R[M]` to a full subcategory containing every
square-zero extension. -/
def squareZeroExtensionRestriction
    (P : ObjectProperty (Over (CommAlgCat.of S R)))
    (hP : ∀ M : FGModuleCat.{u} R, P ((squareZeroExtensionFunctor S R).obj M)) :
    FGModuleCat.{u} R ⥤ P.FullSubcategory where
  obj M := ⟨(squareZeroExtensionFunctor S R).obj M, hP M⟩
  map f := ObjectProperty.homMk ((squareZeroExtensionFunctor S R).map f)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- The set-valued functor `M ↦ F(R[M])`. -/
abbrev tangentSpaceSetFunctor
    (P : ObjectProperty (Over (CommAlgCat.of S R)))
    (hP : ∀ M : FGModuleCat.{u} R, P ((squareZeroExtensionFunctor S R).obj M))
    (F : P.FullSubcategory ⥤ Type v) : FGModuleCat.{u} R ⥤ Type v :=
  squareZeroExtensionRestriction S R P hP ⋙ F

/-- The hypotheses that `F(R[0])` is a singleton and that the maps induced by
the projections `R[M × N] → R[M]` and `R[M × N] → R[N]` identify
`F(R[M × N])` with `F(R[M]) × F(R[N])`. -/
structure TangentSpaceFunctorConditions
    (P : ObjectProperty (Over (CommAlgCat.of S R)))
    (hP : ∀ M : FGModuleCat.{u} R, P ((squareZeroExtensionFunctor S R).obj M))
    (F : P.FullSubcategory ⥤ Type v) : Prop where
  /-- The value at the zero module is inhabited. -/
  zero_nonempty :
    Nonempty ((tangentSpaceSetFunctor S R P hP F).obj (zeroFGModule R))
  /-- The value at the zero module has at most one element. -/
  zero_subsingleton :
    Subsingleton ((tangentSpaceSetFunctor S R P hP F).obj (zeroFGModule R))
  /-- Evaluation on the two product projections gives a bijection. -/
  prod_bijective : ∀ M N, Function.Bijective
    (fun x : (tangentSpaceSetFunctor S R P hP F).obj (prodFGModule R M N) ↦
      ((tangentSpaceSetFunctor S R P hP F).map (prodFst R M N) x,
        (tangentSpaceSetFunctor S R P hP F).map (prodSnd R M N) x))

/-- **Stacks Project, Tag 06IA.** A set-valued functor on a strictly full
subcategory of `S`-algebras over `R` which takes the zero square-zero extension
and products of square-zero extensions to the corresponding products of sets
has a natural `R`-linear module-valued lift on all finitely generated
`R`-modules. -/
@[stacks 06IA, sga "3 XI 1.9" "partial"]
noncomputable def tangentSpaceModuleStructure
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M : FGModuleCat.{u} R, P ((squareZeroExtensionFunctor S R).obj M))
    (F : P.FullSubcategory ⥤ Type v)
    (hF : TangentSpaceFunctorConditions S R P hP F) :
    LinearFunctorLift R (tangentSpaceSetFunctor S R P hP F) :=
  let L := tangentSpaceSetFunctor S R P hP F
  let prodIsLimit := fun M N : FGModuleCat.{u} R ↦ Limits.BinaryFan.isLimitMk
    (fun s ↦ FGModuleCat.ofHom (LinearMap.prod s.fst.hom.hom s.snd.hom.hom))
    (fun _ ↦ by ext; rfl) (fun _ ↦ by ext; rfl)
    (fun _ f hf hg ↦ by
      ext x
      · exact congrArg (fun q ↦ q.hom.hom x) hf
      · exact congrArg (fun q ↦ q.hom.hom x) hg)
  letI : Unique (L.obj (zeroFGModule R)) :=
    { default := Classical.choice hF.zero_nonempty, uniq := fun _ ↦ hF.zero_subsingleton.elim _ _ }
  letI : ∀ X : FGModuleCat.{u} R, Nonempty (X ⟶ zeroFGModule R) := fun _ ↦ ⟨FGModuleCat.ofHom 0⟩
  letI : ∀ X : FGModuleCat.{u} R, Subsingleton (X ⟶ zeroFGModule R) := fun _ ↦ ⟨fun _ _ ↦ by ext⟩
  letI : Limits.HasTerminal (FGModuleCat.{u} R) := Limits.hasTerminal_of_unique (zeroFGModule R)
  letI : ∀ M N : FGModuleCat.{u} R, Limits.HasLimit (Limits.pair M N) :=
    fun M N ↦ ⟨⟨Limits.BinaryFan.mk (prodFst R M N) (prodSnd R M N), prodIsLimit M N⟩⟩
  letI : Limits.HasBinaryProducts (FGModuleCat.{u} R) := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasFiniteProducts (FGModuleCat.{u} R) :=
    CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal
  letI : ∀ M N : FGModuleCat.{u} R, Limits.PreservesLimit (Limits.pair M N) L :=
    fun M N ↦ Limits.preservesLimit_of_preserves_limit_cone (prodIsLimit M N)
      ((Limits.isLimitMapConeBinaryFanEquiv L (prodFst R M N) (prodSnd R M N)).symm
        (let e := Equiv.ofBijective _ (hF.prod_bijective M N)
         Limits.BinaryFan.isLimitMk
          (fun s ↦ ↾fun x ↦ e.symm (s.fst x, s.snd x))
          (fun s ↦ by ext x; exact congrArg Prod.fst (e.apply_symm_apply (s.fst x, s.snd x)))
          (fun s ↦ by ext x; exact congrArg Prod.snd (e.apply_symm_apply (s.fst x, s.snd x)))
          (fun s f hf hg ↦ by
            ext x
            apply e.injective
            change e (f x) = e (e.symm (s.fst x, s.snd x))
            rw [e.apply_symm_apply]
            dsimp [e]
            apply Prod.ext
            · simpa [L] using congrArg (fun q ↦ (ConcreteCategory.hom q) x) hf
            · simpa [L] using congrArg (fun q ↦ (ConcreteCategory.hom q) x) hg)))
  letI : Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L := {
    preservesLimit := by
      intro K
      exact Limits.preservesLimit_of_iso_diagram L (Limits.diagramIsoPair K).symm }
  letI : Limits.PreservesLimitsOfShape (Discrete PEmpty) L := {
    preservesLimit := by
      intro K
      let c : Limits.Cone K := Limits.Cone.mk (zeroFGModule R)
        { app := fun j ↦ nomatch j.as
          naturality := fun X _ _ ↦ PEmpty.elim X.as }
      let hc : Limits.IsLimit c :=
        { lift := fun _ ↦ FGModuleCat.ofHom 0
          fac := fun _ j ↦ nomatch j.as
          uniq := fun _ _ _ ↦ Subsingleton.elim _ _ }
      apply Limits.preservesLimit_of_preserves_limit_cone hc
      letI : Unique (L.mapCone c).pt :=
        { default := (default : L.obj (zeroFGModule R))
          uniq := fun a ↦ hF.zero_subsingleton.elim a _ }
      exact (Limits.Types.isLimit_iff_bijective_sectionOfCone _).mpr
        ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
          fun y ↦ ⟨default, Subsingleton.elim _ _⟩⟩ |>.some }
  letI : Limits.PreservesFiniteProducts L :=
    Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal L
  fgModuleCatLinearFunctorLift R L

end

/-! ### Tangent spaces of functors on algebras -/

section
open CategoryTheory
universe s u v w

variable (S : Type s) (R : Type u) [CommRing S] [CommRing R] [Algebra S R]

/-- The dual numbers over `R`, as an `S`-algebra over `R` via their canonical projection. -/
@[sga "3 III 4.38" "partial"]
abbrev dualNumbersOver : Over (CommAlgCat.of S R) :=
  (trivSqZeroExtFunctor S R).obj (ModuleCat.of R R)

/-- **Stacks Project, Tag 06IB.** The tangent space of a set-valued functor is its value on the
dual numbers. -/
@[stacks 06IB, sga "7 VI 1.15" "special case"]
abbrev TangentSpace
    (P : ObjectProperty (Over (CommAlgCat.of S R)))
    (hε : P (dualNumbersOver S R))
    (F : P.FullSubcategory ⥤ Type w) : Type w :=
  F.obj ⟨dualNumbersOver S R, hε⟩

/-- A surjective augmentation of a local algebra identifies its residue field with the target. -/
noncomputable def residueEquivOfAugmentation
    {Λ : Type s} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A : Type v} [CommRing A] [Algebra Λ A] [IsLocalRing A]
    (f : A →ₐ[Λ] k) (hf : Function.Surjective f) : IsLocalRing.ResidueField A ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
    (IsLocalRing.ker_eq_maximalIdeal f.toRingHom hf).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hf)

/-- The residue-field comparison recovers the augmentation on representatives. -/
@[simp] theorem residueEquivOfAugmentation_residue
    {Λ : Type s} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A : Type v} [CommRing A] [Algebra Λ A] [IsLocalRing A]
    (f : A →ₐ[Λ] k) (hf : Function.Surjective f) (a : A) :
    residueEquivOfAugmentation f hf (IsLocalRing.residue A a) = f a := rfl

section ArtinianLocal

variable (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k]

/-- The presentation of Artinian local algebras as algebras augmented onto `k`. -/
def artinianLocalOver : ObjectProperty (Over (CommAlgCat.of Λ k)) :=
  fun A ↦ IsArtinianRing A.left ∧ IsLocalRing A.left ∧ Function.Surjective A.hom.hom

/-- The residue-field identification determined by a surjective augmentation. -/
noncomputable def augmentationResidueEquiv
    (A : Over (CommAlgCat.of Λ k)) (h : artinianLocalOver Λ k A) :
    let := h.2.1
    IsLocalRing.ResidueField A.left ≃ₐ[Λ] k := by
  letI := h.2.1
  exact residueEquivOfAugmentation A.hom.hom h.2.2

/-- The residue-field identification recovers the prescribed augmentation. -/
@[simp] theorem augmentationResidueEquiv_residue
    (A : Over (CommAlgCat.of Λ k)) (h : artinianLocalOver Λ k A) (a : A.left) :
    let := h.2.1
    augmentationResidueEquiv Λ k A h (IsLocalRing.residue A.left a) = A.hom.hom a := by
  let := h.2.1
  rfl

/-- An augmented Artinian local algebra, regarded as an object of `𝒞_Λ`. -/
noncomputable def artinianLocalOverToArtinian :
    (artinianLocalOver Λ k).FullSubcategory ⥤ ArtinianLocalAlgCat Λ k where
  obj A :=
    { carrier := A.obj.left
      isArtinianRing := A.property.1
      isLocalRing := A.property.2.1
      residueEquiv := augmentationResidueEquiv Λ k A.obj A.property }
  map {A B} f :=
    { hom := f.hom.left.hom
      isLocal := by
        let := A.property.2.1
        let := B.property.2.1
        let := IsLocalHom.of_surjective A.obj.hom.hom.toRingHom A.property.2.2
        refine ⟨fun a ha ↦ ?_⟩
        apply isUnit_of_map_unit A.obj.hom.hom.toRingHom a
        have he := congrArg (fun g ↦ g.hom a) f.hom.w
        exact he ▸ ha.map B.obj.hom.hom.toRingHom
      residue_comm := by
        let := A.property.2.1
        let := B.property.2.1
        intro a
        change augmentationResidueEquiv Λ k B.obj B.property
          (IsLocalRing.residue B.obj.left (f.hom.left.hom a)) =
          augmentationResidueEquiv Λ k A.obj A.property (IsLocalRing.residue A.obj.left a)
        simpa only [augmentationResidueEquiv_residue, CommAlgCat.hom_comp, AlgHom.comp_apply] using
          congrArg (fun g ↦ g.hom a) f.hom.w }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The augmented Artinian local algebras form a strictly full subcategory. -/
instance : (artinianLocalOver Λ k).IsClosedUnderIsomorphisms where
  of_iso {A B} e h := by
    let := h.1
    let := h.2.1
    let i : A.left ≃ₐ[Λ] B.left := CommAlgCat.algEquivOfIso ((Over.forget _).mapIso e)
    refine ⟨i.toRingEquiv.isArtinianRing, i.toRingEquiv.isLocalRing, ?_⟩
    intro x
    obtain ⟨a, ha⟩ := h.2.2 x
    refine ⟨e.hom.left.hom a, ?_⟩
    exact (congrArg (fun g ↦ g.hom a) e.hom.w).trans ha

end ArtinianLocal

section GeneralSquareZero

variable (Λ : Type s) (k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]

local instance (V : FGModuleCat.{v} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance (V : FGModuleCat.{v} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

local instance (V : FGModuleCat.{v} k) : Module Λ V :=
  Module.compHom V (algebraMap Λ k)

local instance (V : FGModuleCat.{v} k) : IsScalarTower Λ k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

local instance (V : FGModuleCat.{v} k) : IsScalarTower Λ kᵐᵒᵖ V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

local instance (V : FGModuleCat.{v} k) : IsLocalRing (TrivSqZeroExt k V) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    have hab : a.fst + b.fst = 1 := congrArg TrivSqZeroExt.fst h
    exact (IsLocalRing.isUnit_or_isUnit_of_add_one hab).imp
      TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr

local instance (V : FGModuleCat.{v} k) : IsArtinianRing (TrivSqZeroExt k V) := by
  let : Module.Finite k (TrivSqZeroExt k V) :=
    inferInstanceAs (Module.Finite k (k × V))
  exact IsArtinianRing.of_finite k _

/-- Square-zero extensions in `𝒞_Λ`, with independent universes for the field and vector spaces. -/
noncomputable def squareZeroExtensionArtinian :
    FGModuleCat.{v} k ⥤ ArtinianLocalAlgCat.{s, max u v, u} Λ k where
  obj V :=
    { carrier := TrivSqZeroExt k V
      residueEquiv := residueEquivOfAugmentation
        ((TrivSqZeroExt.fstHom k k V).restrictScalars Λ) TrivSqZeroExt.fst_surjective }
  map {V W} f :=
    { hom := (TrivSqZeroExt.map f.hom.hom).restrictScalars Λ
      isLocal := by
        refine ⟨fun a ha ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ?_⟩
        simpa only [TrivSqZeroExt.fst_map] using
          (TrivSqZeroExt.isUnit_iff_isUnit_fst
            (x := (TrivSqZeroExt.map f.hom.hom) a)).mp ha
      residue_comm := by
        intro a
        change (TrivSqZeroExt.map f.hom.hom a).fst = a.fst
        simp }
  map_id _ := by ext x <;> simp
  map_comp _ _ := by ext x <;> simp

/-- The augmentation of the square-zero object is the first projection. -/
theorem squareZeroExtensionArtinian_residue (V : FGModuleCat.{v} k)
    (x : TrivSqZeroExt k V) :
    ((squareZeroExtensionArtinian Λ k).obj V).residueEquiv
      (IsLocalRing.residue ((squareZeroExtensionArtinian Λ k).obj V) x) = x.fst := rfl

/-- Dual numbers in any carrier universe containing `k`. -/
@[sga "3 III 4.38" "partial"]
noncomputable abbrev artinianDualNumbers :
    ArtinianLocalAlgCat.{s, max u v, u} Λ k :=
  (squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k (ULift.{v} k))

/-- Evaluation on the dual numbers for a functor on Artinian local algebras. -/
noncomputable abbrev tangentSpaceArtinian
    (F : ArtinianLocalAlgCat.{s, max u v, u} Λ k ⥤ Type w) : Type w :=
  F.obj (artinianDualNumbers Λ k)

end GeneralSquareZero

section SquareZero

-- The existing Over-model square-zero functor uses the carrier universe of the field.
variable (Λ : Type s) (k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]

local instance (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- Every finite-dimensional square-zero extension is an augmented Artinian local algebra. -/
theorem squareZeroExtension_mem_artinianLocalOver (V : FGModuleCat.{u} k) :
    artinianLocalOver Λ k ((squareZeroExtensionFunctor Λ k).obj V) := by
  change IsArtinianRing (TrivSqZeroExt k V) ∧ IsLocalRing (TrivSqZeroExt k V) ∧ _
  let : Module.Finite k (TrivSqZeroExt k V) :=
    inferInstanceAs (Module.Finite k (k × V))
  refine ⟨IsArtinianRing.of_finite k _, ?_, TrivSqZeroExt.fst_surjective⟩
  refine ⟨fun {a b} h ↦ ?_⟩
  have hab : a.fst + b.fst = 1 := congrArg TrivSqZeroExt.fst h
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with ha | hb
  · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha)
  · exact Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hb)

/-- The finite-dimensional square-zero-extension functor with values in `𝒞_Λ`. -/
noncomputable abbrev artinianSquareZeroExtensionFunctor :
    FGModuleCat.{u} k ⥤ ArtinianLocalAlgCat.{s, u, u} Λ k :=
  squareZeroExtensionRestriction Λ k (artinianLocalOver Λ k)
    (squareZeroExtension_mem_artinianLocalOver Λ k) ⋙ artinianLocalOverToArtinian Λ k

/-- In the universe supported by the Over model, the two square-zero functors agree. -/
theorem squareZeroExtensionArtinian_eq :
    squareZeroExtensionArtinian Λ k = artinianSquareZeroExtensionFunctor Λ k := rfl

/-- The tangent space of a functor on `𝒞_Λ`, through its canonical augmented-algebra model. -/
@[stacks 06SR "Definition 06IB applied to the category of augmented Artinian local algebras"]
noncomputable abbrev artinianTangentSpace
    (F : ArtinianLocalAlgCat.{s, u, u} Λ k ⥤ Type w) : Type w :=
  TangentSpace Λ k (artinianLocalOver Λ k)
    (squareZeroExtension_mem_artinianLocalOver Λ k (FGModuleCat.of k k))
    (artinianLocalOverToArtinian Λ k ⋙ F)

/-- Evaluation on the Artinian square-zero object agrees with the Over-model tangent space. -/
@[stacks 06SR "Definition 06IB applied to the category of augmented Artinian local algebras"]
theorem artinianTangentSpace_eq
    (F : ArtinianLocalAlgCat.{s, u, u} Λ k ⥤ Type w) :
    artinianTangentSpace Λ k F =
      F.obj ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)) := rfl

end SquareZero

end

/-! ### Morphisms induce linear maps on tangent spaces -/

section
open CategoryTheory CategoryTheory.Limits
universe u v uR uM vM

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]


private lemma cast_eqToHom_symm_app_apply (R : Type uR) [CommRing R]
    {H K : FGModuleCat.{vM} R ⥤ Type uM} (e : H = K) (M : FGModuleCat.{vM} R)
    (x : K.obj M) :
    cast (congrArg (fun L ↦ L.obj M) e) ((eqToHom e.symm).app M x) = x := by
  subst e
  rfl

/-- The module structure of Tag 06IA is the canonical lift of the underlying set-valued
functor, which preserves finite products and is a singleton at the zero module. -/
private theorem tangentSpaceModuleStructure_eq_lift
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M : FGModuleCat.{u} R, P ((squareZeroExtensionFunctor S R).obj M))
    (F : P.FullSubcategory ⥤ Type v) (hF : TangentSpaceFunctorConditions S R P hP F) :
    ∃ (_ : PreservesFiniteProducts (tangentSpaceSetFunctor S R P hP F))
      (_ : Unique ((tangentSpaceSetFunctor S R P hP F).obj (FGModuleCat.of R PUnit))),
      tangentSpaceModuleStructure S R P hP F hF =
        fgModuleCatLinearFunctorLift R (tangentSpaceSetFunctor S R P hP F) := by
  let LF := tangentSpaceModuleStructure S R P hP F hF
  let : LF.functor.Additive := LF.additive
  let : PreservesFiniteProducts LF.functor := Functor.preservesFiniteProductsOfAdditive LF.functor
  let : PreservesFiniteProducts (tangentSpaceSetFunctor S R P hP F) := by
    rw [← LF.forget_comp]
    infer_instance
  let : Unique ((tangentSpaceSetFunctor S R P hP F).obj (FGModuleCat.of R PUnit)) :=
    { default := hF.zero_nonempty.some
      uniq := fun _ ↦ hF.zero_subsingleton.elim _ _ }
  let : Unique (LinearFunctorLift R (tangentSpaceSetFunctor S R P hP F)) :=
    Classical.choice (fgModuleCat_linearFunctorLift_unique R _)
  exact ⟨inferInstance, inferInstance, Subsingleton.elim _ _⟩

/-- **Stacks Project, Tag 06ID.** A natural transformation between functors
satisfying the tangent-space hypotheses is `R`-linear on every trivial
square-zero extension `R[M]`, with respect to the natural module structures of
Tag 06IA.  The case `M = R` is the induced linear map on tangent spaces. -/
@[stacks 06ID]
theorem naturalTransformation_linearMapOnSquareZeroExtensions
    (P : ObjectProperty (Over (CommAlgCat.of S R))) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M : FGModuleCat.{u} R,
      P ((squareZeroExtensionFunctor S R).obj M))
    (F G : P.FullSubcategory ⥤ Type v)
    (hF : TangentSpaceFunctorConditions S R P hP F)
    (hG : TangentSpaceFunctorConditions S R P hP G)
    (t : F ⟶ G) (M : FGModuleCat.{u} R) :
    let LF := tangentSpaceModuleStructure S R P hP F hF
    let LG := tangentSpaceModuleStructure S R P hP G hG
    let eF := congrArg (fun H : FGModuleCat.{u} R ⥤ Type v ↦ H.obj M) LF.forget_comp
    let eG := congrArg (fun H : FGModuleCat.{u} R ⥤ Type v ↦ H.obj M) LG.forget_comp
    ∃ l : LF.functor.obj M ⟶ LG.functor.obj M, ∀ x : LF.functor.obj M,
      cast eG (l x) =
        t.app ((squareZeroExtensionRestriction S R P hP).obj M) (cast eF x) :=
  by
    dsimp only
    obtain ⟨_, _, hLF⟩ := tangentSpaceModuleStructure_eq_lift S R P hP F hF
    obtain ⟨_, _, hLG⟩ := tangentSpaceModuleStructure_eq_lift S R P hP G hG
    let TF := tangentSpaceSetFunctor S R P hP F
    let TG := tangentSpaceSetFunctor S R P hP G
    let t' : TF ⟶ TG :=
      Functor.whiskerLeft (squareZeroExtensionRestriction S R P hP) t
    obtain ⟨τ, hτ, -⟩ := fgModuleCat_linearFunctorLift_natTrans R TF TG t'
    rw [hLF, hLG]
    refine ⟨τ.app M, ?_⟩
    intro x
    have hx := congrFun (
      congrArg (fun η ↦ η.app M) hτ) x
    change τ.app M x =
      (eqToHom (fgModuleCatLinearFunctorLift R TG).forget_comp.symm).app M
        (t.app ((squareZeroExtensionRestriction S R P hP).obj M)
          ((eqToHom (fgModuleCatLinearFunctorLift R TF).forget_comp).app M x)) at hx
    rw [eqToHom_app_apply_cast
      (fgModuleCatLinearFunctorLift R TF).forget_comp M x] at hx
    have hx' := congrArg
      (cast (congrArg (fun H ↦ H.obj M)
        (fgModuleCatLinearFunctorLift R TG).forget_comp)) hx
    rw [cast_eqToHom_symm_app_apply R
      (fgModuleCatLinearFunctorLift R TG).forget_comp M] at hx'
    exact hx'

end

/-! ### Tangent spaces and tensor products -/

section
open CategoryTheory
universe s u

/-- **Stacks Project, Tag 06IE.** Over a field, the functor
`V ↦ F(K[V])`, with its natural linear structure, is naturally isomorphic
to tensoring `V` with the tangent space `F(K[ε])`. -/
@[stacks 06IE]
theorem tangentSpaceFunctor_iso_tensorLeft
    (S : Type s) (K : Type u) [CommRing S] [Field K] [Algebra S K]
    (P : ObjectProperty (Over (CommAlgCat.of S K)))
    [P.IsClosedUnderIsomorphisms]
    (hP : ∀ V : FGModuleCat.{u} K,
      P ((squareZeroExtensionFunctor S K).obj V))
    (F : P.FullSubcategory ⥤ Type u)
    (hF : TangentSpaceFunctorConditions S K P hP F) :
    let L := (tangentSpaceModuleStructure S K P hP F hF).functor
    Nonempty
      (L ≅
        (forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K) ⋙
          MonoidalCategory.tensorLeft (L.obj (FGModuleCat.of K K)))) := by
  dsimp only
  exact Nonempty.map Iso.symm
    (linearFunctor_iso_tensorLeft K
      (tangentSpaceModuleStructure S K P hP F hF).functor)

end

end Deformation
