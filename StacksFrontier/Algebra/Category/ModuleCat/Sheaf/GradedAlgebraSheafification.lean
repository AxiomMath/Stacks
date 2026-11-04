module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of a graded algebra of presheaves of modules

Let `α : R₀ ⟶ R.obj` be a locally bijective morphism from a presheaf of rings to the sections
of a sheaf of rings on a site `(C, J)`, so that `PresheafOfModules.sheafification α` is the
associated-sheaf functor `PresheafOfModules R₀ ⥤ SheafOfModules R`. Let `A` be a
`ℤ`-graded algebra structure (`Stacks.GradedAlgebra`) on a family
`P : ℤ → PresheafOfModules R₀`. This file makes the degreewise sheafification of `P` into a
sheaf of graded algebras, `SheafOfModules.GradedAlgebra R`, and records its universal property
relative to the sheafification units.

This is the step that turns a *sectionwise* graded algebra — a tensor, exterior or symmetric
algebra formed on sections, as in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras`
and `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification` — into the
sheaf of graded algebras that Section 17.21 attaches to a sheaf of modules.

## Main definitions

* `Stacks.GradedAlgebra.sheafify`: **the sheafification of a graded algebra of presheaves of
  modules**, as a `SheafOfModules.GradedAlgebra`. Its degree-`n` piece is the sheafification of
  `P n`; its multiplication is `Stacks.GradedAlgebra.sheafifyMul` and its unit is
  `Stacks.GradedAlgebra.sheafifyOne`.
* `Stacks.GradedAlgebra.sheafifyMul`: the multiplication, obtained by extending the given
  multiplication along the sheafification units in each variable
  (`Stacks.BilinearMap.extend`, through `compLeftEquiv`/`compRightEquiv`) and then upgrading
  it from `R₀`-bilinear to `R`-bilinear with `Stacks.BilinearMap.ofRestrictScalars`.
* `Stacks.GradedAlgebra.sheafifyGradedHom`: **the morphism action of the sheafification.** A
  family of morphisms of the presheaf pieces which preserves products of homogeneous local
  sections sheafifies to a homomorphism of the sheafified graded algebras. `Stacks.GradedAlgebra`
  carries no type of homomorphisms, so that datum is given as the family together with its
  multiplicativity.
* `Stacks.GradedAlgebra.sheafifyGen`: the sheafification of a degree-one generator
  `F ⟶ P 1`, a degree-one generator of `sheafify`.
* `Stacks.GradedAlgebra.descApp`: the degreewise morphism out of `sheafify` determined by a
  degreewise morphism out of `P` into (the restriction of scalars of) a sheaf of graded
  algebras.
* `PresheafOfModules.sheafifyRestrict` and `PresheafOfModules.sheafifyUnit`: the codomain of
  the sheafification unit of a presheaf of modules, and that unit.
* `Stacks.liftSieve`: the covering sieve of local lifts of a section along a sheafification
  unit, and `Stacks.eq_of_isSeparated`, `Stacks.heq_of_isSeparated`, `Stacks.heq_apply`: the
  three elementary tools every proof below is assembled from.

## Main results

* `Stacks.GradedAlgebra.sheafifyMul_unit` and `sheafify_mul_unit`: the sheafified
  multiplication extends the given one — on the unit-images of two homogeneous local sections
  it is the unit-image of their product. This is what pins `sheafifyMul` down, by
  `Stacks.BilinearMap.existsUnique_extend`.
* `Stacks.GradedAlgebra.sheafifyMul_restrict` and `sheafify_mul_restrict`: the sheafified
  multiplication read on local lifts. Every law of `sheafify` is proved from this plus
  separatedness of the target.
* `Stacks.GradedAlgebra.pairwiseCommutes_sheafifyGen` and `squareZero_sheafifyGen`: the two
  side conditions that cut out the symmetric and exterior algebras transfer from a generator
  to its sheafification.
* `Stacks.GradedAlgebra.existsUnique_desc`: **the universal property of the sheafification.** A
  degreewise morphism `P n ⟶ (B.piece n)|_{R₀}` into a sheaf of graded algebras `B` which is
  multiplicative on homogeneous local sections and carries the unit to the unit extends
  uniquely to a `SheafOfModules.GradedAlgebra.UnitalHom (A.sheafify α) B`.

## Implementation notes

**Why the multiplication cannot simply be transported.** The pieces of `sheafify` are sheaves,
so a multiplication on them is a `Stacks.BilinearMap` over the *sheaf* of rings `R.obj`,
whereas the given multiplication is bilinear over the *presheaf* `R₀` and takes as arguments
sections of the presheaf pieces. Both gaps are closed by results already in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor`, in this order: the
sheafification unit is locally bijective and the target is a sheaf, so
`Stacks.BilinearMap.compLeftEquiv` and `compRightEquiv` extend the bilinear map in each
variable uniquely (`mulUnit`, `mulExtendLeft`, `mulExtend`); and the ring map `α` is locally
surjective with separated target, so `Stacks.BilinearMap.ofRestrictScalars` upgrades the
result to `R`-bilinearity (`sheafifyMul`). Neither step is available for a bilinear map into a
presheaf.

**The heterogeneous equalities.** `Stacks.GradedAlgebra` and
`SheafOfModules.GradedAlgebra` both state associativity and the unit laws with `HEq`, because
`(i + j) + k` and `i + (j + k)` are propositionally but not definitionally equal in `ℤ`, so the
two sides of each law live in different homogeneous pieces. Those degree equalities cannot be
`subst`ed where the laws are used — the degrees are not local variables there — so they are
discharged by two helpers which take the degree equality as a hypothesis and `subst` it
internally: `Stacks.heq_of_isSeparated`, which reduces a heterogeneous equality to agreement on
a covering sieve, and `Stacks.heq_apply`, degreewise congruence. Writing the transport out by
hand instead means manipulating `cast`s through restriction maps, which no separatedness
argument can be run through.

**No `@[stacks]` tag.** Tag 0FQW is the *definition* of a sheaf of graded algebras, already
carried by `SheafOfModules.GradedAlgebra` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits`; the sheafification
construction here is infrastructure used by Section 17.21 and Tag 01CG rather than the content
of a tag, so nothing below is tagged.

**What is here and what is not.** This file produces the sheaf of graded algebras and the
descent of degreewise morphisms out of it. It does **not** prove that `sheafify` has
`SheafOfModules.GradedAlgebra.IsUniversal` for any of the three properties of Section 17.21.
`existsUnique_desc` is the sheafification half of that: the remaining half is a *presheaf-level*
universal property of `A` itself, stated against the restriction of scalars of a sheaf of graded
algebras along `α` — and neither a `Hom` type for `Stacks.GradedAlgebra` nor that restriction of
scalars exists yet. `pairwiseCommutes_sheafifyGen` and `squareZero_sheafifyGen` discharge the
*first* component of `IsUniversal` (`IsSymmetricAlgebra.1`, `IsExteriorAlgebra.1`) outright.

**Universes.** The site universes `u`, `v`, the ring universe `t` and the module universe `a`
are independent, exactly as in `Stacks.GradedAlgebra` and `SheafOfModules.GradedAlgebra`; the
index of the grading is `ℤ`, as `SheafOfModules.GradedAlgebra` fixes it. Nothing here relates or
specializes a universe.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory Opposite PresheafOfModules

universe v u t a

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- The sheafification of a presheaf of modules, read again as a presheaf of `R₀`-modules by
restriction of scalars: the codomain of the sheafification unit. -/
noncomputable abbrev sheafifyRestrict (M : PresheafOfModules.{a} R₀) :
    PresheafOfModules.{a} R₀ :=
  (SheafOfModules.forget R ⋙ restrictScalars α).obj ((sheafification α).obj M)

/-- The unit of the sheafification adjunction for presheaves of modules. -/
noncomputable abbrev sheafifyUnit (M : PresheafOfModules.{a} R₀) : M ⟶ sheafifyRestrict α M :=
  (sheafificationAdjunction α).unit.app M

end PresheafOfModules

namespace Stacks

section Heq

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Degreewise congruence along an equality of degrees. -/
theorem heq_apply {ι : Type*} (F G : ι → Type a) (g : ∀ i, F i → G i) {i j : ι} (hij : i = j)
    {x : F i} {y : F j} (hxy : HEq x y) : HEq (g i x) (g j y) := by
  subst hij
  exact heq_of_eq (congrArg (g i) (eq_of_heq hxy))

/-- Two local sections of a sheaf of modules agree as soon as their restrictions along a
covering sieve do. This is `Presheaf.IsSeparated` with the sections written in the module of
sections of the sheaf of modules itself. -/
theorem eq_of_isSeparated (M : SheafOfModules.{a} R) {X : Cᵒᵖ} {u v : M.val.obj X}
    {S : Sieve X.unop} (hS : S ∈ J X.unop)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → M.val.map f.op u = M.val.map f.op v) : u = v :=
  M.isSheaf.isSeparated _ _ hS u v fun _ f hf => h f hf

/-- Two local sections of two *equal* sheaves of modules are heterogeneously equal as soon as
their restrictions along a covering sieve are. -/
theorem heq_of_isSeparated {M N : SheafOfModules.{a} R} (hMN : M = N) {X : Cᵒᵖ}
    {u : M.val.obj X} {v : N.val.obj X} {S : Sieve X.unop} (hS : S ∈ J X.unop)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → HEq (M.val.map f.op u) (N.val.map f.op v)) :
    HEq u v := by
  subst hMN
  exact heq_of_eq (M.isSheaf.isSeparated _ _ hS u v fun _ f hf => eq_of_heq (h f hf))

end Heq

section Lift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- The sieve of local lifts of a section of a sheafified presheaf of modules along the
sheafification unit. -/
noncomputable abbrev liftSieve (M : PresheafOfModules.{a} R₀) {X : Cᵒᵖ}
    (s : (sheafifyRestrict α M).obj X) : Sieve X.unop :=
  Presheaf.imageSieve ((toPresheaf R₀).map (sheafifyUnit α M)) s

/-- A section of a sheafified presheaf of modules lifts along the sheafification unit on a
covering sieve: the unit is locally surjective. -/
theorem liftSieve_mem (M : PresheafOfModules.{a} R₀) {X : Cᵒᵖ}
    (s : (sheafifyRestrict α M).obj X) : liftSieve α M s ∈ J X.unop :=
  Presheaf.imageSieve_mem J ((toPresheaf R₀).map (sheafifyUnit α M)) s

/-- Membership in `Stacks.liftSieve` is the existence of a local lift along the unit. -/
theorem exists_lift_of_liftSieve (M : PresheafOfModules.{a} R₀) {X : Cᵒᵖ}
    (s : (sheafifyRestrict α M).obj X) {Y : C} (f : Y ⟶ X.unop) (hf : liftSieve α M s f) :
    ∃ m : M.obj (op Y), Hom.app (sheafifyUnit α M) (op Y) m =
      (sheafifyRestrict α M).map f.op s := hf

/-- `Stacks.exists_lift_of_liftSieve`, with the section and restriction written in the
sheafified presheaf of modules. -/
private theorem exists_unit_eq_map_of_liftSieve {M : PresheafOfModules.{a} R₀} {X : Cᵒᵖ}
    {s : ((sheafification α).obj M).val.obj X} {Y : C} {f : Y ⟶ X.unop}
    (hf : liftSieve α M s f) :
    ∃ m : M.obj (op Y), Hom.app (sheafifyUnit α M) (op Y) m =
      ((sheafification α).obj M).val.map f.op s :=
  hf

end Lift

namespace GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {P : ℤ → PresheafOfModules.{a} R₀} (A : GradedAlgebra P)

/-- The multiplication of a graded algebra of presheaves of modules, followed by the
sheafification unit of the target. -/
noncomputable def mulUnit (i j : ℤ) :
    BilinearMap (P i) (P j) (sheafifyRestrict α (P (i + j))) :=
  (A.mul i j).postcomp (sheafifyUnit α (P (i + j)))

/-- `Stacks.GradedAlgebra.mulUnit` extended along the sheafification unit in the first
variable. -/
noncomputable def mulExtendLeft (i j : ℤ) :
    BilinearMap (sheafifyRestrict α (P i)) (P j) (sheafifyRestrict α (P (i + j))) :=
  (BilinearMap.compLeftEquiv (N := P j)
    ((sheafification α).obj (P (i + j))).isSheaf (sheafifyUnit α (P i))).symm (A.mulUnit α i j)

/-- `Stacks.GradedAlgebra.mulUnit` extended along the sheafification unit in both variables.
It is bilinear over the presheaf of rings `R₀`. -/
noncomputable def mulExtend (i j : ℤ) :
    BilinearMap (sheafifyRestrict α (P i)) (sheafifyRestrict α (P j))
      (sheafifyRestrict α (P (i + j))) :=
  (BilinearMap.compRightEquiv (M := sheafifyRestrict α (P i))
    ((sheafification α).obj (P (i + j))).isSheaf
    (sheafifyUnit α (P j))).symm (A.mulExtendLeft α i j)

/-- The multiplication of the sheafified graded algebra. -/
noncomputable def sheafifyMul (i j : ℤ) :
    SheafOfModules.BilinearMap ((sheafification α).obj (P i)) ((sheafification α).obj (P j))
      ((sheafification α).obj (P (i + j))) :=
  BilinearMap.ofRestrictScalars α (A.mulExtend α i j)
    ((sheafification α).obj (P (i + j))).isSheaf.isSeparated

/-- The sheafified multiplication extends the given one: on the unit-images of two homogeneous
local sections it is the unit-image of their product. -/
theorem sheafifyMul_unit (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X) :
    (A.sheafifyMul α i j).app X (Hom.app (sheafifyUnit α (P i)) X x)
        (Hom.app (sheafifyUnit α (P j)) X y) =
      Hom.app (sheafifyUnit α (P (i + j))) X ((A.mul i j).app X x y) :=
  (BilinearMap.congr_app
      ((BilinearMap.compRightEquiv (M := sheafifyRestrict α (P i))
        ((sheafification α).obj (P (i + j))).isSheaf
        (sheafifyUnit α (P j))).apply_symm_apply (A.mulExtendLeft α i j)) X
      (Hom.app (sheafifyUnit α (P i)) X x) y).trans
    (BilinearMap.congr_app
      ((BilinearMap.compLeftEquiv (N := P j)
        ((sheafification α).obj (P (i + j))).isSheaf
        (sheafifyUnit α (P i))).apply_symm_apply (A.mulUnit α i j)) X x y)

/-- **The sheafified multiplication, read on local lifts.** If two local sections of the
sheafified pieces lift, after restriction, to local sections `x` and `y` of the presheaf
pieces, then their product restricts to the unit-image of `(A.mul i j) x y`. Together with
separatedness of the target this is what every law of the sheafified algebra is proved by. -/
theorem sheafifyMul_restrict (i j : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b₁ : ((sheafification α).obj (P i)).val.obj X)
    (b₂ : ((sheafification α).obj (P j)).val.obj X)
    (x : (P i).obj Y) (y : (P j).obj Y)
    (hx : Hom.app (sheafifyUnit α (P i)) Y x =
      ((sheafification α).obj (P i)).val.map f b₁)
    (hy : Hom.app (sheafifyUnit α (P j)) Y y =
      ((sheafification α).obj (P j)).val.map f b₂) :
    ((sheafification α).obj (P (i + j))).val.map f ((A.sheafifyMul α i j).app X b₁ b₂) =
      Hom.app (sheafifyUnit α (P (i + j))) Y ((A.mul i j).app Y x y) := by
  refine ((A.sheafifyMul α i j).naturality f b₁ b₂).trans ?_
  rw [← hx, ← hy]
  exact A.sheafifyMul_unit α i j Y x y

/-- The unit of the sheafified graded algebra: the unit-image of the given unit. -/
noncomputable def sheafifyOne : ((sheafification α).obj (P 0)).sections :=
  PresheafOfModules.sectionsMk (fun X => Hom.app (sheafifyUnit α (P 0)) X (A.one.eval X))
    fun {X _} f => ((naturality_apply (sheafifyUnit α (P 0)) f (A.one.eval X)).symm).trans
      (congrArg (fun s => Hom.app (sheafifyUnit α (P 0)) _ s)
        (PresheafOfModules.sections_property A.one f))

/-- The unit of the sheafified algebra, evaluated at `X`, is the unit-image of the unit of `A` at
`X`. -/
@[simp]
theorem sheafifyOne_eval (X : Cᵒᵖ) :
    (A.sheafifyOne α).eval X = Hom.app (sheafifyUnit α (P 0)) X (A.one.eval X) := rfl

/-- **The sheafification of a graded algebra of presheaves of modules.** -/
noncomputable def sheafify : SheafOfModules.GradedAlgebra.{t, a} R where
  piece n := (sheafification α).obj (P n)
  mul i j := A.sheafifyMul α i j
  one := A.sheafifyOne α
  mul_assoc i j k X x y z := by
    refine heq_of_isSeparated
      (congrArg (fun n : ℤ => (sheafification α).obj (P n)) (add_assoc i j k))
      (J.intersection_covering
        (J.intersection_covering (liftSieve_mem α (P i) x) (liftSieve_mem α (P j) y))
        (liftSieve_mem α (P k) z)) ?_
    rintro Y f ⟨⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩, ⟨z₀, hz₀⟩⟩
    have hx : Hom.app (sheafifyUnit α (P i)) (op Y) x₀ =
      ((sheafification α).obj (P i)).val.map f.op x := hx₀
    have hy : Hom.app (sheafifyUnit α (P j)) (op Y) y₀ =
      ((sheafification α).obj (P j)).val.map f.op y := hy₀
    have hz : Hom.app (sheafifyUnit α (P k)) (op Y) z₀ =
      ((sheafification α).obj (P k)).val.map f.op z := hz₀
    rw [A.sheafifyMul_restrict α (i + j) k f.op _ z ((A.mul i j).app (op Y) x₀ y₀) z₀
        (A.sheafifyMul_restrict α i j f.op x y x₀ y₀ hx hy).symm hz,
      A.sheafifyMul_restrict α i (j + k) f.op x _ x₀ ((A.mul j k).app (op Y) y₀ z₀) hx
        (A.sheafifyMul_restrict α j k f.op y z y₀ z₀ hy hz).symm]
    exact heq_apply _ _ (fun n s => Hom.app (sheafifyUnit α (P n)) (op Y) s) (add_assoc i j k)
      (A.mul_assoc i j k (op Y) x₀ y₀ z₀)
  one_mul i X x := by
    refine heq_of_isSeparated
      (congrArg (fun n : ℤ => (sheafification α).obj (P n)) (zero_add i))
      (liftSieve_mem α (P i) x) ?_
    rintro Y f ⟨x₀, hx₀⟩
    have hx : Hom.app (sheafifyUnit α (P i)) (op Y) x₀ =
      ((sheafification α).obj (P i)).val.map f.op x := hx₀
    rw [A.sheafifyMul_restrict α 0 i f.op _ x (A.one.eval (op Y)) x₀
        (PresheafOfModules.sections_property (A.sheafifyOne α) f.op).symm hx, ← hx]
    exact heq_apply _ _ (fun n s => Hom.app (sheafifyUnit α (P n)) (op Y) s) (zero_add i)
      (A.one_mul i (op Y) x₀)
  mul_one i X x := by
    refine heq_of_isSeparated
      (congrArg (fun n : ℤ => (sheafification α).obj (P n)) (add_zero i))
      (liftSieve_mem α (P i) x) ?_
    rintro Y f ⟨x₀, hx₀⟩
    have hx : Hom.app (sheafifyUnit α (P i)) (op Y) x₀ =
      ((sheafification α).obj (P i)).val.map f.op x := hx₀
    rw [A.sheafifyMul_restrict α i 0 f.op x _ x₀ (A.one.eval (op Y)) hx
        (PresheafOfModules.sections_property (A.sheafifyOne α) f.op).symm, ← hx]
    exact heq_apply _ _ (fun n s => Hom.app (sheafifyUnit α (P n)) (op Y) s) (add_zero i)
      (A.mul_one i (op Y) x₀)

/-! ### The sheafified algebra, degreewise -/

/-- The degree-`n` piece of `sheafify` is the sheafification of the degree-`n` piece. -/
theorem sheafify_piece (n : ℤ) :
    (A.sheafify α).piece n = (sheafification α).obj (P n) := rfl

/-- The multiplication of `sheafify` is `Stacks.GradedAlgebra.sheafifyMul`. -/
theorem sheafify_mul (i j : ℤ) : (A.sheafify α).mul i j = A.sheafifyMul α i j := rfl

/-- The unit of `sheafify` is `Stacks.GradedAlgebra.sheafifyOne`. -/
theorem sheafify_one : (A.sheafify α).one = A.sheafifyOne α := rfl

/-- The unit of `sheafify`, evaluated at `X`, is the unit-image of the unit of `A` at `X`. -/
theorem sheafify_one_eval (X : Cᵒᵖ) :
    (A.sheafify α).one.eval X = Hom.app (sheafifyUnit α (P 0)) X (A.one.eval X) := rfl

/-- The multiplication of the sheafified algebra on unit-images of homogeneous local sections,
stated for `sheafify` itself. -/
theorem sheafify_mul_unit (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X) :
    ((A.sheafify α).mul i j).app X (Hom.app (sheafifyUnit α (P i)) X x)
        (Hom.app (sheafifyUnit α (P j)) X y) =
      Hom.app (sheafifyUnit α (P (i + j))) X ((A.mul i j).app X x y) :=
  A.sheafifyMul_unit α i j X x y

/-- `Stacks.GradedAlgebra.sheafifyMul_restrict`, stated for `sheafify` itself: the spelling in
which the homogeneous pieces are those of the sheafified algebra. -/
theorem sheafify_mul_restrict (i j : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b₁ : ((A.sheafify α).piece i).val.obj X) (b₂ : ((A.sheafify α).piece j).val.obj X)
    (x : (P i).obj Y) (y : (P j).obj Y)
    (hx : Hom.app (sheafifyUnit α (P i)) Y x = ((A.sheafify α).piece i).val.map f b₁)
    (hy : Hom.app (sheafifyUnit α (P j)) Y y = ((A.sheafify α).piece j).val.map f b₂) :
    ((A.sheafify α).piece (i + j)).val.map f (((A.sheafify α).mul i j).app X b₁ b₂) =
      Hom.app (sheafifyUnit α (P (i + j))) Y ((A.mul i j).app Y x y) :=
  A.sheafifyMul_restrict α i j f b₁ b₂ x y hx hy

/-! ### The morphism action of the sheafification -/

/-- The sheafification unit commutes with a morphism of presheaves and its sheafification, on
local lifts. -/
private theorem unit_map_lift {F G : PresheafOfModules.{a} R₀} (gen : F ⟶ G) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (b : ((sheafification α).obj F).val.obj X) (s : F.obj Y)
    (hs : Hom.app (sheafifyUnit α F) Y s = ((sheafification α).obj F).val.map f b) :
    Hom.app (sheafifyUnit α G) Y (Hom.app gen Y s) =
      ((sheafification α).obj G).val.map f (Hom.app ((sheafification α).map gen).val X b) := by
  rw [← unit_naturality_apply (α := α) gen Y s, hs]
  exact naturality_apply ((sheafification α).map gen).val f b

section Map

variable {Q : ℤ → PresheafOfModules.{a} R₀} (B : GradedAlgebra Q) (g : ∀ n, P n ⟶ Q n)

/-- **The sheafification of a degreewise multiplicative family of morphisms.** A family of
morphisms of the presheaf pieces which preserves products of homogeneous local sections
sheafifies to a homomorphism of the sheafified graded algebras, degreewise the sheafification of
the given morphism.

`Stacks.GradedAlgebra` carries no type of homomorphisms, so the datum of a morphism is given
here as the family together with its multiplicativity. This is the morphism action of
`Stacks.GradedAlgebra.sheafify`. -/
noncomputable def sheafifyGradedHom
    (hg : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
      Hom.app (g (i + j)) X ((A.mul i j).app X x y) =
        (B.mul i j).app X (Hom.app (g i) X x) (Hom.app (g j) X y)) :
    A.sheafify α ⟶ B.sheafify α where
  app n := (sheafification α).map (g n)
  map_mul i j X b₁ b₂ := by
    refine eq_of_isSeparated ((B.sheafify α).piece (i + j))
      (J.intersection_covering (liftSieve_mem α (P i) b₁) (liftSieve_mem α (P j) b₂)) ?_
    rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
    have hx : Hom.app (sheafifyUnit α (P i)) (op Y) x₀ =
      ((A.sheafify α).piece i).val.map f.op b₁ := hx₀
    have hy : Hom.app (sheafifyUnit α (P j)) (op Y) y₀ =
      ((A.sheafify α).piece j).val.map f.op b₂ := hy₀
    have h'x : Hom.app (sheafifyUnit α (Q i)) (op Y) (Hom.app (g i) (op Y) x₀) =
        ((B.sheafify α).piece i).val.map f.op
          (Hom.app ((sheafification α).map (g i)).val X b₁) :=
      ((unit_naturality_apply (α := α) (g i) (op Y) x₀).symm.trans
        (congrArg (fun z => Hom.app ((sheafification α).map (g i)).val (op Y) z) hx)).trans
        (naturality_apply ((sheafification α).map (g i)).val f.op b₁)
    have h'y : Hom.app (sheafifyUnit α (Q j)) (op Y) (Hom.app (g j) (op Y) y₀) =
        ((B.sheafify α).piece j).val.map f.op
          (Hom.app ((sheafification α).map (g j)).val X b₂) :=
      ((unit_naturality_apply (α := α) (g j) (op Y) y₀).symm.trans
        (congrArg (fun z => Hom.app ((sheafification α).map (g j)).val (op Y) z) hy)).trans
        (naturality_apply ((sheafification α).map (g j)).val f.op b₂)
    refine Eq.trans ?_ (B.sheafify_mul_restrict α i j f.op _ _
      (Hom.app (g i) (op Y) x₀) (Hom.app (g j) (op Y) y₀) h'x h'y).symm
    refine (naturality_apply ((sheafification α).map (g (i + j))).val f.op
      (((A.sheafify α).mul i j).app X b₁ b₂)).symm.trans ?_
    refine Eq.trans (congrArg
      (fun z => Hom.app ((sheafification α).map (g (i + j))).val (op Y) z)
      (A.sheafify_mul_restrict α i j f.op b₁ b₂ x₀ y₀ hx hy)) ?_
    exact (unit_naturality_apply (α := α) (g (i + j)) (op Y) ((A.mul i j).app (op Y) x₀ y₀)).trans
      (congrArg (fun z => Hom.app (sheafifyUnit α (Q (i + j))) (op Y) z)
        (hg i j (op Y) x₀ y₀))

/-- In degree `n`, `sheafifyGradedHom` is the sheafification of the morphism `g n`. -/
@[simp]
theorem sheafifyGradedHom_app
    (hg : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
      Hom.app (g (i + j)) X ((A.mul i j).app X x y) =
        (B.mul i j).app X (Hom.app (g i) X x) (Hom.app (g j) X y)) (n : ℤ) :
    (A.sheafifyGradedHom α B g hg).app n = (sheafification α).map (g n) := rfl

end Map

/-! ### Degree-one generators -/

section Generator

variable {F : PresheafOfModules.{a} R₀} (gen : F ⟶ P 1)

/-- The sheafification of a degree-one generator of a graded algebra of presheaves of modules:
a degree-one generator of the sheafified algebra. -/
noncomputable def sheafifyGen : (sheafification α).obj F ⟶ (A.sheafify α).piece 1 :=
  (sheafification α).map gen

/-- The sheafified generator carries the unit-image of a local section `s` of `F` to the unit-image
of `gen s`. -/
theorem sheafifyGen_unit (X : Cᵒᵖ) (s : F.obj X) :
    (A.sheafifyGen α gen).val.app X (Hom.app (sheafifyUnit α F) X s) =
      Hom.app (sheafifyUnit α (P 1)) X (Hom.app gen X s) :=
  PresheafOfModules.unit_naturality_apply gen X s

/-- A local lift of a local section of `F` along the sheafification unit gives a local lift of
its image under the sheafified generator. -/
theorem sheafifyGen_lift {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b : ((sheafification α).obj F).val.obj X) (s : F.obj Y)
    (hs : Hom.app (sheafifyUnit α F) Y s = ((sheafification α).obj F).val.map f b) :
    Hom.app (sheafifyUnit α (P 1)) Y (Hom.app gen Y s) =
      ((A.sheafify α).piece 1).val.map f ((A.sheafifyGen α gen).val.app X b) :=
  unit_map_lift α gen f b s hs

/-- **Pairwise commutation transfers to the sheafification.** If any two degree-one local
sections in the image of `gen` commute, so do any two in the image of the sheafified
generator. The hypothesis is `Stacks.GradedAlgebra.GenCommutes A gen`. -/
theorem pairwiseCommutes_sheafifyGen
    (hc : ∀ (X : Cᵒᵖ) (x y : F.obj X),
      (A.mul 1 1).app X (Hom.app gen X x) (Hom.app gen X y) =
        (A.mul 1 1).app X (Hom.app gen X y) (Hom.app gen X x)) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (A.sheafifyGen α gen) := by
  intro X s u
  refine eq_of_isSeparated ((A.sheafify α).piece (1 + 1))
    (J.intersection_covering (liftSieve_mem α F s) (liftSieve_mem α F u)) ?_
  rintro Y f ⟨hs, hu⟩
  obtain ⟨s₀, hs⟩ := exists_unit_eq_map_of_liftSieve α hs
  obtain ⟨u₀, hu⟩ := exists_unit_eq_map_of_liftSieve α hu
  rw [A.sheafify_mul_restrict α 1 1 f.op _ _ (Hom.app gen (op Y) s₀) (Hom.app gen (op Y) u₀)
      (A.sheafifyGen_lift α gen f.op s s₀ hs) (A.sheafifyGen_lift α gen f.op u u₀ hu),
    A.sheafify_mul_restrict α 1 1 f.op _ _ (Hom.app gen (op Y) u₀) (Hom.app gen (op Y) s₀)
      (A.sheafifyGen_lift α gen f.op u u₀ hu) (A.sheafifyGen_lift α gen f.op s s₀ hs)]
  exact congrArg (fun w => Hom.app (sheafifyUnit α (P (1 + 1))) (op Y) w) (hc (op Y) s₀ u₀)

/-- **Squaring to zero transfers to the sheafification.** -/
theorem squareZero_sheafifyGen
    (hc : ∀ (X : Cᵒᵖ) (x : F.obj X),
      (A.mul 1 1).app X (Hom.app gen X x) (Hom.app gen X x) = 0) :
    SheafOfModules.GradedAlgebra.SquareZero (A.sheafifyGen α gen) := by
  intro X s
  refine eq_of_isSeparated ((A.sheafify α).piece (1 + 1)) (liftSieve_mem α F s) ?_
  rintro Y f hs
  obtain ⟨s₀, hs⟩ := exists_unit_eq_map_of_liftSieve α hs
  rw [A.sheafify_mul_restrict α 1 1 f.op _ _ (Hom.app gen (op Y) s₀) (Hom.app gen (op Y) s₀)
      (A.sheafifyGen_lift α gen f.op s s₀ hs) (A.sheafifyGen_lift α gen f.op s s₀ hs),
    hc (op Y) s₀]
  exact (map_zero _).trans (map_zero _).symm

end Generator

/-! ### The universal property of the sheafified algebra -/

section Descent

variable {B : SheafOfModules.GradedAlgebra.{t, a} R}
  (g : ∀ n : ℤ, P n ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj (B.piece n))

/-- The degreewise morphism out of the sheafified algebra determined by a degreewise morphism
out of the graded algebra of presheaves. -/
noncomputable def descApp (n : ℤ) : (A.sheafify α).piece n ⟶ B.piece n :=
  ((sheafificationAdjunction α).homEquiv (P n) (B.piece n)).symm (g n)

/-- The morphism `descApp` carries the unit-image of a local section `s` of the degree-`n` piece
to `g n s`. -/
theorem descApp_unit (n : ℤ) (X : Cᵒᵖ) (s : (P n).obj X) :
    (A.descApp α g n).val.app X (Hom.app (sheafifyUnit α (P n)) X s) = Hom.app (g n) X s :=
  PresheafOfModules.hom_congr_apply'
    (sheafificationAdjunction_unit_comp_homEquiv_symm α (g n)) X s

variable
  (hmul : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
    Hom.app (g (i + j)) X ((A.mul i j).app X x y) =
      (B.mul i j).app X (Hom.app (g i) X x) (Hom.app (g j) X y))
  (hone : ∀ X : Cᵒᵖ, Hom.app (g 0) X (A.one.eval X) = B.one.eval X)

include hmul hone in
/-- **The universal property of the sheafification of a graded algebra.** A degreewise
morphism into a sheaf of graded algebras which is multiplicative on homogeneous local sections
and carries the unit to the unit extends uniquely to a unital homomorphism out of the
sheafified algebra. -/
theorem existsUnique_desc :
    ∃! h : SheafOfModules.GradedAlgebra.UnitalHom (A.sheafify α) B,
      ∀ (n : ℤ) (X : Cᵒᵖ) (s : (P n).obj X),
        (h.app n).val.app X (Hom.app (sheafifyUnit α (P n)) X s) = Hom.app (g n) X s := by
  refine ⟨{ app := A.descApp α g
            map_mul := ?_
            map_one := ?_ }, A.descApp_unit α g, ?_⟩
  · intro i j X b₁ b₂
    refine eq_of_isSeparated (B.piece (i + j))
      (J.intersection_covering (liftSieve_mem α (P i) b₁) (liftSieve_mem α (P j) b₂)) ?_
    rintro Y f ⟨hx, hy⟩
    obtain ⟨x₀, hx⟩ := exists_unit_eq_map_of_liftSieve α hx
    obtain ⟨y₀, hy⟩ := exists_unit_eq_map_of_liftSieve α hy
    rw [← naturality_apply (A.descApp α g (i + j)).val f.op,
      A.sheafify_mul_restrict α i j f.op b₁ b₂ x₀ y₀ hx hy, A.descApp_unit α g (i + j),
      hmul i j (op Y) x₀ y₀, (B.mul i j).naturality f.op,
      ← naturality_apply (A.descApp α g i).val f.op, ← naturality_apply (A.descApp α g j).val f.op]
    erw [← hx, ← hy]
    rw [A.descApp_unit α g i (op Y) x₀, A.descApp_unit α g j (op Y) y₀]
  · intro X
    exact (A.descApp_unit α g 0 X (A.one.eval X)).trans (hone X)
  · intro h hh
    refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
    refine sheafification_hom_ext (PresheafOfModules.hom_ext fun X => ?_)
    exact ModuleCat.hom_ext (LinearMap.ext fun s =>
      (hh n X s).trans (A.descApp_unit α g n X s).symm)

end Descent

end GradedAlgebra

end Stacks
