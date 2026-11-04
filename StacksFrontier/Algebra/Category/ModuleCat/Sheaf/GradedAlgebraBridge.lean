module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Homomorphisms of sheaves of graded algebras, and universal graded algebras

Let `R` be a sheaf of rings on a site. A sheaf of `ℤ`-graded `R`-algebras is a
`SheafOfModules.GradedAlgebra R`: a family of homogeneous pieces with a sectionwise bilinear,
restriction-compatible multiplication and a global degree-zero unit. This file adds two layers
on top of that structure.

The first is the category of such algebras. A homomorphism acts degreewise and preserves
products of homogeneous local sections; it is *not* required to preserve the distinguished
unit, matching the source. The unital homomorphisms of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback` are the subclass that
does, and `UnitalHom.toHom` is the forgetful map.

The second is the tensor and symmetric instances of the universal property `IsUniversal` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback`. All three universal
properties of Section 17.21 have the same shape: fix a property `P` of a degree-one generator
`M ⟶ B.piece 1`, and ask for an algebra which has `P` and is initial among those that do.
`IsUniversal P` is that shape, with the `desc`/`desc_unique`/`pieceIso` API proved once; the
instances are `P = fun _ _ => True` (tensor), `P = SquareZero` (exterior, which is
`IsExteriorAlgebra`) and `P = PairwiseCommutes` (symmetric), and the first and third are
defined here.

That second layer is what makes a statement about *the* exterior or symmetric algebra of `M`
expressible without constructing one. A consumer takes `(A, ι, hA : IsUniversal P A ι)` as
hypotheses instead of a term, which is strictly stronger than a statement about one chosen
algebra, and `IsUniversal.pieceIso` and `IsUniversal.descIsIso` say the hypotheses pin the
algebra down up to a unique isomorphism, so nothing is lost by not naming it.

## Main definitions

* `SheafOfModules.GradedAlgebra.Hom` is a homomorphism of sheaves of graded algebras, with
  `Hom.id`, `Hom.comp` and the resulting `Category` instance.
* `SheafOfModules.GradedAlgebra.homOfPieceIso`, `invOfPieceIso` and `isoOfPieceIso` assemble a
  degreewise family of isomorphisms of the homogeneous pieces into an isomorphism of sheaves of
  graded algebras.
* `SheafOfModules.GradedAlgebra.UnitalHom.toHom` forgets preservation of the unit, and
  `UnitalHom.ofHom` recovers it from the global form of the unit law.
* `SheafOfModules.GradedAlgebra.UnitalHom.inverse` is the inverse of a unital homomorphism which
  is an isomorphism in every degree: the degreewise inverses are again multiplicative and
  unital, so a degreewise isomorphism of sheaves of graded algebras is an isomorphism.
* `SheafOfModules.GradedAlgebra.PairwiseCommutes` says any two degree-one local sections in the
  image of a generator commute.
* `SheafOfModules.GradedAlgebra.IsTensorAlgebra` and `IsSymmetricAlgebra` are the tensor and
  symmetric instances of `IsUniversal`.

## Main results

* `SheafOfModules.GradedAlgebra.UnitalHom.sectionsMap_one` and `UnitalHom.map_one_iff` identify
  the sectionwise unit law with the single global equation
  `sectionsMap (g.app 0) A.one = B.one`.
* `SheafOfModules.GradedAlgebra.IsTensorAlgebra.isUniversal`,
  `IsExteriorAlgebra.isUniversal` and `IsSymmetricAlgebra.isUniversal` exhibit the three
  universal properties as instances of `IsUniversal`, so the `desc`/`desc_unique`/`pieceIso`
  API of `ExteriorAlgebraPullback` applies to each of them.
* `SheafOfModules.GradedAlgebra.UnitalHom.comp_inverse` and `UnitalHom.inverse_comp`: the
  degreewise inverse is a two-sided inverse, and
  `SheafOfModules.GradedAlgebra.UnitalHom.isIso_comp_app` says a composite is invertible in a
  degree in which both factors are.
* `SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso`: a universal property of a sheaf of
  graded algebras transports along a unital homomorphism that is invertible in every degree, and
  `SheafOfModules.GradedAlgebra.SquareZero.compUnitalHom` supplies the square-zero hypothesis
  that transport needs for the exterior case.
* `SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit`: if degree zero of `A` is isomorphic to
  the structure sheaf by an isomorphism carrying the algebra unit to `1`, then every degree-zero
  local section is its own image times the unit.

## Implementation notes

The base is an arbitrary sheaf of rings on an arbitrary site, with the universes of the site,
the ring and the homogeneous pieces independent, exactly as in `GradedAlgebra` itself. The sole
exception is `eq_smul_one_of_isoUnit`, where the target `SheafOfModules.unit R` has its sections
in the ring universe and so forces the piece universe to equal the ring universe. That is not a
restriction of the statement being formalized: the source's degree-zero identification is with
the structure sheaf, whose sections are the ring's.

`IsTensorAlgebra` and `IsSymmetricAlgebra` are defined as instances of `IsUniversal` rather
than spelled out, so that the universal-property API applies to them without a bridge; the
`isUniversal` theorems of their namespaces are the identity, and exist only to let dot
notation find that API.

`isoOfPieceIso` asks multiplicativity only of the forward maps: the inverse family is
multiplicative automatically, which is `invOfPieceIso`. Without it every consumer that has a
degreewise comparison has to prove the same equation twice, once in each direction.

`Hom` does not require preservation of the unit, so `Hom` and `UnitalHom` are genuinely
different notions and neither is a sub-bundle of the other as a structure; `UnitalHom.toHom`
and `UnitalHom.ofHom` relate them. The category instance is on `Hom`, because that is the
category the source forms.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Homomorphisms and the category of sheaves of graded algebras -/

/-- A homomorphism of sheaves of graded algebras: a morphism of sheaves of modules in each
degree, preserving products of homogeneous local sections. The distinguished degree-zero unit
need not be preserved; the homomorphisms that preserve it are `UnitalHom`. -/
@[stacks 0FQW "homomorphisms of sheaves of graded algebras, and the category they form"]
structure Hom (A B : GradedAlgebra.{t, a} R) where
  /-- The morphism of sheaves of modules in each degree. -/
  app (n : ℤ) : A.piece n ⟶ B.piece n
  /-- The degreewise morphisms preserve multiplication. -/
  map_mul (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (app (i + j)).val.app U ((A.mul i j).app U x y) =
      (B.mul i j).app U ((app i).val.app U x) ((app j).val.app U y)

namespace Hom

variable {A B D : GradedAlgebra.{t, a} R}

/-- Two homomorphisms of sheaves of graded algebras agree as soon as all their homogeneous
components do. -/
@[ext]
theorem ext {f g : Hom A B} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; congr; funext n; exact h n

/-- The identity homomorphism of a sheaf of graded algebras. -/
def id (A : GradedAlgebra.{t, a} R) : Hom A A where
  app _ := 𝟙 _
  map_mul _ _ _ _ _ := rfl

/-- Composition of homomorphisms of sheaves of graded algebras. -/
def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  app n := f.app n ≫ g.app n
  map_mul i j U x y := by
    change (g.app (i + j)).val.app U ((f.app (i + j)).val.app U ((A.mul i j).app U x y)) = _
    rw [f.map_mul, g.map_mul]
    rfl

/-- Each homogeneous component of the identity homomorphism is the identity. -/
@[simp] theorem id_app (A : GradedAlgebra.{t, a} R) (n : ℤ) : (id A).app n = 𝟙 _ := rfl

/-- Each homogeneous component of a composite is the composite of the components. -/
@[simp] theorem comp_app (f : Hom A B) (g : Hom B D) (n : ℤ) :
    (f.comp g).app n = f.app n ≫ g.app n := rfl

end Hom

/-- Sheaves of graded algebras over a fixed sheaf of rings form a category.

The `Hom.congr_app`/`isoOfPieceIso` assembly below is stated after this instance because an
isomorphism is a datum of this category. -/
instance : Category (GradedAlgebra.{t, a} R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := by ext n; simp
  comp_id _ := by ext n; simp
  assoc _ _ _ := by ext n; simp

/-- Each homogeneous component of the categorical identity is the identity. -/
@[simp] theorem categoryStruct_id_app (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    (CategoryStruct.id A : Hom A A).app n = 𝟙 _ := rfl

/-- Each homogeneous component of a categorical composite is the composite of the
components. -/
@[simp] theorem categoryStruct_comp_app {A B D : GradedAlgebra.{t, a} R} (f : A ⟶ B) (g : B ⟶ D)
    (n : ℤ) : (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- Local sections are returned by `f` followed by `g` when `f ≫ g` is the identity. -/
private theorem app_comp_apply_of_comp_eq_id {X Y : SheafOfModules.{a} R} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : f ≫ g = 𝟙 X) (U : Cᵒᵖ) (z : X.val.obj U) : g.val.app U (f.val.app U z) = z :=
  congrArg (fun k : X ⟶ X => k.val.app U z) h

/-! ### Assembling an isomorphism out of degreewise isomorphisms

An isomorphism of sheaves of graded algebras is no more than a family of isomorphisms of the
homogeneous pieces which is multiplicative on homogeneous local sections: the inverse family is
multiplicative for free. `isoOfPieceIso` is that assembly. -/

section PieceIso

variable {A B : GradedAlgebra.{t, a} R} (e : ∀ n : ℤ, A.piece n ≅ B.piece n)

/-- The degreewise family of a multiplicative family of isomorphisms, as a homomorphism. -/
def homOfPieceIso
    (he : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y)) :
    Hom A B where
  app n := (e n).hom
  map_mul := he

/-- The inverses of a multiplicative family of isomorphisms are again multiplicative. -/
def invOfPieceIso
    (he : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y)) :
    Hom B A where
  app n := (e n).inv
  map_mul i j U x y := by
    have hhi (n : ℤ) (z : (A.piece n).val.obj U) :
        (e n).inv.val.app U ((e n).hom.val.app U z) = z :=
      congrArg (fun f : A.piece n ⟶ A.piece n => f.val.app U z) (e n).hom_inv_id
    have hih (n : ℤ) (z : (B.piece n).val.obj U) :
        (e n).hom.val.app U ((e n).inv.val.app U z) = z :=
      congrArg (fun f : B.piece n ⟶ B.piece n => f.val.app U z) (e n).inv_hom_id
    have hkey := he i j U ((e i).inv.val.app U x) ((e j).inv.val.app U y)
    rw [hih i x, hih j y] at hkey
    rw [← hkey, hhi (i + j)]

/-- **A multiplicative family of degreewise isomorphisms is an isomorphism of sheaves of graded
algebras.** The multiplicativity is required only of the forward maps. -/
def isoOfPieceIso
    (he : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y)) :
    A ≅ B where
  hom := homOfPieceIso e he
  inv := invOfPieceIso e he
  hom_inv_id := by
    refine Hom.ext fun n => ?_
    change (e n).hom ≫ (e n).inv = 𝟙 _
    exact (e n).hom_inv_id
  inv_hom_id := by
    refine Hom.ext fun n => ?_
    change (e n).inv ≫ (e n).hom = 𝟙 _
    exact (e n).inv_hom_id

/-- The forward map of `isoOfPieceIso` is the given family in each degree. -/
@[simp] theorem isoOfPieceIso_hom_app
    (he : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y)) (n : ℤ) :
    (isoOfPieceIso e he).hom.app n = (e n).hom := rfl

/-- The inverse of `isoOfPieceIso` is the family of inverses in each degree. -/
@[simp] theorem isoOfPieceIso_inv_app
    (he : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      (e (i + j)).hom.val.app U ((A.mul i j).app U x y) =
        (B.mul i j).app U ((e i).hom.val.app U x) ((e j).hom.val.app U y)) (n : ℤ) :
    (isoOfPieceIso e he).inv.app n = (e n).inv := rfl

end PieceIso

/-! ### Unital homomorphisms, and the global form of the unit law -/

namespace UnitalHom

variable {A B : GradedAlgebra.{t, a} R}

/-- A unital homomorphism of sheaves of graded algebras is in particular a homomorphism. -/
def toHom (g : UnitalHom A B) : Hom A B where
  app := g.app
  map_mul := g.map_mul

/-- Forgetting the unit law does not change the homogeneous components. -/
@[simp] theorem toHom_app (g : UnitalHom A B) (n : ℤ) : g.toHom.app n = g.app n := rfl

/-- The identity unital homomorphism forgets to the identity homomorphism. -/
@[simp] theorem toHom_id (A : GradedAlgebra.{t, a} R) : (UnitalHom.id A).toHom = Hom.id A := rfl

/-- Forgetting the unit law commutes with composition. -/
@[simp] theorem toHom_comp (g : UnitalHom A B) {D : GradedAlgebra.{t, a} R}
    (h : UnitalHom B D) : (g.comp h).toHom = g.toHom.comp h.toHom := rfl

/-- The sectionwise unit law of a unital homomorphism, as a single equation between global
sections of the degree-zero pieces. This is the form in which the condition is stated when the
unit is regarded as a global section rather than sectionwise. -/
theorem sectionsMap_one (g : UnitalHom A B) :
    SheafOfModules.sectionsMap (g.app 0) A.one = B.one :=
  PresheafOfModules.sections_ext _ _ fun U => g.map_one U

/-- The two forms of the unit law for a degreewise multiplicative family are equivalent: the
sectionwise equations and the single equation between global sections. -/
theorem map_one_iff (f : Hom A B) :
    (∀ U : Cᵒᵖ, (f.app 0).val.app U (A.one.eval U) = B.one.eval U) ↔
      SheafOfModules.sectionsMap (f.app 0) A.one = B.one :=
  ⟨fun h => PresheafOfModules.sections_ext _ _ h,
    fun h U => congrArg (fun s : (B.piece 0).sections => s.eval U) h⟩

/-- A homomorphism of sheaves of graded algebras which carries the global unit to the global
unit is a unital homomorphism. -/
def ofHom (f : Hom A B) (hf : SheafOfModules.sectionsMap (f.app 0) A.one = B.one) :
    UnitalHom A B where
  app := f.app
  map_mul := f.map_mul
  map_one := (map_one_iff f).2 hf

/-- `ofHom` does not change the homogeneous components. -/
@[simp] theorem ofHom_app (f : Hom A B)
    (hf : SheafOfModules.sectionsMap (f.app 0) A.one = B.one) (n : ℤ) :
    (ofHom f hf).app n = f.app n := rfl

/-- Forgetting the unit law of `ofHom f hf` gives back `f`. -/
@[simp] theorem toHom_ofHom (f : Hom A B)
    (hf : SheafOfModules.sectionsMap (f.app 0) A.one = B.one) : (ofHom f hf).toHom = f := rfl

/-- A unital homomorphism is recovered from its underlying homomorphism and its unit law. -/
@[simp] theorem ofHom_toHom (g : UnitalHom A B) :
    ofHom g.toHom g.sectionsMap_one = g := rfl

end UnitalHom

/-! ### Degreewise invertible homomorphisms of sheaves of graded algebras -/

section DegreewiseIso

variable {A B D : GradedAlgebra.{t, a} R}

/-- A composite of unital homomorphisms is an isomorphism in a degree in which both factors
are. -/
instance UnitalHom.isIso_comp_app (f : UnitalHom A B) (g : UnitalHom B D) (n : ℤ)
    [IsIso (f.app n)] [IsIso (g.app n)] : IsIso ((f.comp g).app n) := by
  rw [UnitalHom.comp_app]
  infer_instance

/-- A homogeneous component of a homomorphism of sheaves of graded algebras which is an
isomorphism undoes its inverse on local sections. -/
theorem app_inv_app_apply (φ : UnitalHom A B) (n : ℤ) [IsIso (φ.app n)] (U : Cᵒᵖ)
    (x : (B.piece n).val.obj U) :
    (φ.app n).val.app U ((inv (φ.app n)).val.app U x) = x :=
  app_comp_apply_of_comp_eq_id _ _ (IsIso.inv_hom_id (φ.app n)) U x

/-- The inverse of an invertible homogeneous component of a homomorphism of sheaves of graded
algebras undoes it on local sections. -/
theorem inv_app_app_apply (φ : UnitalHom A B) (n : ℤ) [IsIso (φ.app n)] (U : Cᵒᵖ)
    (x : (A.piece n).val.obj U) :
    (inv (φ.app n)).val.app U ((φ.app n).val.app U x) = x :=
  app_comp_apply_of_comp_eq_id _ _ (IsIso.hom_inv_id (φ.app n)) U x

/-- An invertible homogeneous component of a homomorphism of sheaves of graded algebras is
injective on local sections. -/
theorem app_apply_injective (φ : UnitalHom A B) (n : ℤ) [IsIso (φ.app n)] (U : Cᵒᵖ) :
    Function.Injective fun x : (A.piece n).val.obj U => (φ.app n).val.app U x :=
  Function.LeftInverse.injective (g := fun y => (inv (φ.app n)).val.app U y)
    (inv_app_app_apply φ n U)

/-- The inverse of a homomorphism of sheaves of graded algebras which is an isomorphism in every
degree: the degreewise inverses are again multiplicative and unital. -/
noncomputable def UnitalHom.inverse (φ : UnitalHom A B) [inst : ∀ n, IsIso (φ.app n)] :
    UnitalHom B A where
  app n := inv (φ.app n)
  map_mul i j U x y := by
    refine app_apply_injective φ (i + j) U ?_
    dsimp only
    rw [app_inv_app_apply, φ.map_mul, app_inv_app_apply, app_inv_app_apply]
  map_one U := by
    refine app_apply_injective φ 0 U ?_
    dsimp only
    rw [app_inv_app_apply, φ.map_one]

/-- Each homogeneous component of the inverse is the inverse of the corresponding component. -/
@[simp] theorem UnitalHom.inverse_app (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)] (n : ℤ) :
    φ.inverse.app n = inv (φ.app n) := rfl

/-- The inverse of a degreewise invertible homomorphism is a right inverse. -/
theorem UnitalHom.comp_inverse (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)] :
    φ.comp φ.inverse = UnitalHom.id A :=
  UnitalHom.ext fun n => IsIso.hom_inv_id (φ.app n)

/-- The inverse of a degreewise invertible homomorphism is a left inverse. -/
theorem UnitalHom.inverse_comp (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)] :
    φ.inverse.comp φ = UnitalHom.id B :=
  UnitalHom.ext fun n => IsIso.inv_hom_id (φ.app n)

variable {M : SheafOfModules.{a} R}

/-- Postcomposing a square-zero degree-one generator with a unital homomorphism of sheaves of
graded algebras leaves it square-zero: the square of the image is the image of the square. -/
theorem SquareZero.compUnitalHom {κ : M ⟶ A.piece 1} (hκ : SquareZero κ) (Φ : UnitalHom A B) :
    SquareZero (κ ≫ Φ.app 1) := fun U s =>
  ((Φ.map_mul 1 1 U (κ.val.app U s) (κ.val.app U s)).symm.trans
      (congrArg (fun z => (Φ.app (1 + 1)).val.app U z) (hκ U s))).trans (map_zero _)

/-- **A universal property transports along a degreewise invertible homomorphism.** If `A` with
the degree-one generator `ι` is universal for `P` and `φ : A ⟶ B` is a unital homomorphism which
is an isomorphism in every degree, then `B` with the generator `ι ≫ φ` is universal for `P` as
soon as that generator has `P`. -/
theorem IsUniversal.ofDegreewiseIso
    {P : ∀ D : GradedAlgebra.{t, a} R, (M ⟶ D.piece 1) → Prop} {ι : M ⟶ A.piece 1}
    (hA : IsUniversal P A ι) (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)]
    (hP : P B (ι ≫ φ.app 1)) : IsUniversal P B (ι ≫ φ.app 1) := by
  refine ⟨hP, fun D κ hκ => ?_⟩
  refine ⟨φ.inverse.comp (hA.desc D κ hκ), ?_, fun g hg => ?_⟩
  · dsimp only
    have h : (ι ≫ φ.app 1) ≫ (φ.inverse.comp (hA.desc D κ hκ)).app 1 =
        ι ≫ (φ.app 1 ≫ φ.inverse.app 1) ≫ (hA.desc D κ hκ).app 1 := by
      simp only [UnitalHom.comp_app, Category.assoc]
    rw [h, UnitalHom.inverse_app, IsIso.hom_inv_id, Category.id_comp, hA.desc_extends]
  · dsimp only at hg
    have hdesc : φ.comp g = hA.desc D κ hκ :=
      hA.desc_unique D κ hκ (by rw [UnitalHom.comp_app, ← Category.assoc]; exact hg)
    refine (UnitalHom.ext fun n => ?_).symm
    rw [UnitalHom.comp_app, ← hdesc, UnitalHom.comp_app, ← Category.assoc,
      UnitalHom.inverse_app, IsIso.inv_hom_id, Category.id_comp]

end DegreewiseIso

/-! ### The universal properties of the tensor, exterior and symmetric algebras -/

variable {M : SheafOfModules.{a} R}

/-- A degree-one generator has pairwise commuting image if any two local sections of `M` have
commuting products in the algebra. -/
def PairwiseCommutes {A : GradedAlgebra.{t, a} R} (ι : M ⟶ A.piece 1) : Prop :=
  ∀ (U : Cᵒᵖ) (s u : M.val.obj U),
    (A.mul 1 1).app U (ι.val.app U s) (ι.val.app U u) =
      (A.mul 1 1).app U (ι.val.app U u) (ι.val.app U s)

/-- The universal property of the tensor algebra on `M`: every degree-one generator of every
sheaf of graded algebras is obtained by a unique unital homomorphism. -/
def IsTensorAlgebra (A : GradedAlgebra.{t, a} R) (ι : M ⟶ A.piece 1) : Prop :=
  IsUniversal (fun _ _ => True) A ι

/-- The universal property of the symmetric algebra on `M`: the quotient of the tensor algebra
by the commutators of degree-one local sections, presented by its universal property. -/
@[sga "6 VI 2.2"]
def IsSymmetricAlgebra (A : GradedAlgebra.{t, a} R) (ι : M ⟶ A.piece 1) : Prop :=
  IsUniversal (fun _ κ => PairwiseCommutes κ) A ι

/-- The tensor-algebra universal property, in the form that quantifies over generators with no
side condition. -/
theorem isTensorAlgebra_iff {A : GradedAlgebra.{t, a} R} (ι : M ⟶ A.piece 1) :
    IsTensorAlgebra A ι ↔
      ∀ (B : GradedAlgebra.{t, a} R) (κ : M ⟶ B.piece 1),
        ∃! g : UnitalHom A B, ι ≫ g.app 1 = κ :=
  ⟨fun h B κ => h.2 B κ trivial, fun h => ⟨trivial, fun B κ _ => h B κ⟩⟩

namespace IsExteriorAlgebra

variable {A : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}

/-- An exterior algebra is universal for `SquareZero`: `IsExteriorAlgebra` is by definition the
`P = SquareZero` instance of `IsUniversal`, and this is that identification as a term. -/
theorem isUniversal (hA : IsExteriorAlgebra A ι) :
    IsUniversal (fun _ κ => SquareZero κ) A ι := hA

end IsExteriorAlgebra

namespace IsSymmetricAlgebra

variable {A B : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1} {κ : M ⟶ B.piece 1}

/-- A symmetric algebra is universal for `PairwiseCommutes`. -/
theorem isUniversal (hA : IsSymmetricAlgebra A ι) :
    IsUniversal (fun _ κ => PairwiseCommutes κ) A ι := hA

/-- Two symmetric algebras of the same sheaf of modules are canonically isomorphic in every
degree: the symmetric powers of `M` are well defined up to canonical isomorphism. -/
noncomputable def pieceIso (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ) (n : ℤ) :
    A.piece n ≅ B.piece n :=
  hA.isUniversal.pieceIso hB.isUniversal n

end IsSymmetricAlgebra

namespace IsTensorAlgebra

variable {A B : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1} {κ : M ⟶ B.piece 1}

/-- A tensor algebra is universal for the empty condition. -/
theorem isUniversal (hA : IsTensorAlgebra A ι) : IsUniversal (fun _ _ => True) A ι := hA

/-- Two tensor algebras of the same sheaf of modules are canonically isomorphic in every
degree: the tensor powers of `M` are well defined up to canonical isomorphism. -/
noncomputable def pieceIso (hA : IsTensorAlgebra A ι) (hB : IsTensorAlgebra B κ) (n : ℤ) :
    A.piece n ≅ B.piece n :=
  hA.isUniversal.pieceIso hB.isUniversal n

/-- A tensor algebra maps to any graded algebra with a chosen degree-one generator. -/
noncomputable def descAny (hA : IsTensorAlgebra A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) : UnitalHom A B :=
  hA.isUniversal.desc B κ trivial

/-- The map `descAny` out of a tensor algebra extends the given degree-one generator. -/
theorem descAny_extends (hA : IsTensorAlgebra A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) : ι ≫ (hA.descAny B κ).app 1 = κ :=
  hA.isUniversal.desc_extends B κ trivial

/-- A unital homomorphism out of a tensor algebra extending a degree-one generator is
`descAny`. -/
theorem descAny_unique (hA : IsTensorAlgebra A ι) (B : GradedAlgebra.{t, a} R)
    (κ : M ⟶ B.piece 1) {g : UnitalHom A B} (hg : ι ≫ g.app 1 = κ) : g = hA.descAny B κ :=
  hA.isUniversal.desc_unique B κ trivial hg

end IsTensorAlgebra

/-! ### Degree zero -/

/-- If degree zero of a sheaf of graded algebras is isomorphic to the structure sheaf by an
isomorphism carrying the algebra unit to `1`, then every degree-zero local section is its own
image times the unit: degree zero is free of rank one on the unit.

The scalar is taken as a separate argument `r` together with `hr`, rather than written as
`e.hom.val.app U x` in the conclusion, so that the scalar action is the one of
`R.obj.obj U` on `(A.piece 0).val.obj U` as stated. Written the other way the left-hand
factor has type `(unit R).val.obj U`, which is the ring of sections only up to unfolding
`SheafOfModules.unit`, and instance search for the action does not unfold it. -/
theorem eq_smul_one_of_isoUnit (A : GradedAlgebra.{t, t} R)
    (e : A.piece 0 ≅ SheafOfModules.unit R)
    (he : ∀ U : Cᵒᵖ, e.hom.val.app U (A.one.eval U) = (1 : R.obj.obj U))
    (U : Cᵒᵖ) (x : (A.piece 0).val.obj U) (r : R.obj.obj U)
    (hr : e.hom.val.app U x = r) :
    r • A.one.eval U = x := by
  refine Function.LeftInverse.injective
    (fun y => app_comp_apply_of_comp_eq_id _ _ e.hom_inv_id U y) ?_
  rw [map_smul, he, hr]
  exact _root_.mul_one r

/-- Degree zero of a sheaf of graded algebras whose degree-zero piece is isomorphic to the
structure sheaf, by an isomorphism carrying the unit to `1`, is generated by the unit. -/
theorem exists_smul_one_of_isoUnit (A : GradedAlgebra.{t, t} R)
    (e : A.piece 0 ≅ SheafOfModules.unit R)
    (he : ∀ U : Cᵒᵖ, e.hom.val.app U (A.one.eval U) = (1 : R.obj.obj U))
    (U : Cᵒᵖ) (x : (A.piece 0).val.obj U) :
    ∃ r : R.obj.obj U, r • A.one.eval U = x :=
  ⟨_, eq_smul_one_of_isoUnit A e he U x _ rfl⟩

end SheafOfModules.GradedAlgebra
