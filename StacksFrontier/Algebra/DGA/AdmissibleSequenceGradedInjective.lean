module

public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

/-
# Problem Description

We work over a fixed commutative ring `R` and a differential graded algebra
`(A, d)` over `R` (Stacks, Tag 061V). We use right differential graded modules
(the statement and proof for left modules are identical).

This file formalizes:

* Definition 1 (Stacks, Tag 09JI): a (right) differential graded `A`-module.
* Definition 2: a graded (right) `A`-module and graded `A`-module maps;
  the abelian category `Mod_A` of graded right `A`-modules.
* Definition 3 (Stacks, Tag 0FQD): a differential graded `A`-module that is
  injective as a graded `A`-module ("graded injective").
* Definition 4 (Stacks, Tag 09JT(1)): an admissible monomorphism.

The main statement (Stacks, Tag 09K2 / Lemma 22.19.1): if `f : I -> M` is an
injective homomorphism of differential graded `A`-modules and `I` is graded
injective, then `f` is an admissible monomorphism.

## Modelling choices

The grading is modelled externally: a graded object is a `Z`-indexed family of
`R`-modules `M^n`. The right `A`-action `M^n x A^m -> M^{n+m}` is encoded as a
family of `R`-bilinear maps. Differentials have degree `+1`.

ALL structural axioms (associativity and unitality of the multiplication,
`d . d = 0`, the graded Leibniz rules, and the graded right-module laws) are
PACKAGED AS FIELDS of the corresponding structures `DGAlgebra`, `GradedModule`,
and `DGModule`. Consequently EVERY term of these types is an actual differential
graded algebra / graded module / differential graded module, and the main
theorem needs no extra well-formedness hypotheses: the quantifiers in
`GradedInjective` already range only over genuine graded `A`-modules (the
objects of `Mod_A`), and the objects `I`, `M` of the theorem are genuine DG
modules. This faithfully matches the definitions of the source, where the
injective-object property is a property in the abelian category of graded
`A`-modules.

All carriers live in `Type` (universe `0`). This is a harmless simplification:
it keeps the statement free of universe bookkeeping while still ranging over a
genuine (large) class of graded/differential graded modules, and the lemma holds
for this class exactly as in the Stacks proof.

The graded sign `(-1)^n` appearing in the Leibniz rules is `signZ`.

The injective-object property in `Mod_A` (Definition 3) is stated concretely via
the lifting/extension property, matching the explicit description in the source.
-/

namespace Stacks.DifferentialGradedModule.AdmissibleMono

variable {R : Type} [CommRing R]

/-- Transport an element of `f m` to `f n` along a proof `h : m = n`. Used to
state graded laws whose two sides land in degrees that are equal but not
syntactically identical. -/
def degCast {ι : Type*} {f : ι → Type*} {m n : ι} (h : m = n) (x : f m) : f n := h ▸ x

/-- The graded sign `(-1)^n` as an element of `R`. It depends only on the parity
of `n`, so we define it through `n.natAbs`. -/
def signZ (R : Type) [CommRing R] (n : ℤ) : R := (-1 : R) ^ n.natAbs

/-- A *differential graded algebra* over `R` (Stacks, Tag 061V): a `Z`-indexed
family of `R`-modules `A^n` with a graded multiplication `A^m x A^n -> A^{m+n}`
(`R`-bilinear in each variable), a unit `1 in A^0`, and a degree `+1`
differential `d`, subject to associativity, unitality, `d . d = 0` and the
graded Leibniz rule. All these axioms are FIELDS of this structure, so every
term is a genuine differential graded algebra. -/
structure DGAlgebra (R : Type) [CommRing R] where
  /-- The graded pieces `A^n`. -/
  carrier : ℤ → Type
  [addCommGroup : ∀ n, AddCommGroup (carrier n)]
  [module : ∀ n, Module R (carrier n)]
  /-- Graded multiplication `A^m x A^n -> A^{m+n}`, `R`-bilinear in each variable. -/
  mul : ∀ {m n : ℤ}, carrier m →ₗ[R] carrier n →ₗ[R] carrier (m + n)
  /-- The unit, living in degree `0`. -/
  one : carrier 0
  /-- The degree `+1` differential. -/
  d : ∀ {n : ℤ}, carrier n →ₗ[R] carrier (n + 1)
  /-- Associativity of the graded multiplication. -/
  mul_assoc : ∀ {m n p : ℤ} (a : carrier m) (b : carrier n) (c : carrier p),
    degCast (add_assoc m n p) (mul (mul a b) c) = mul a (mul b c)
  /-- Left unitality. -/
  one_mul : ∀ {n : ℤ} (a : carrier n), degCast (zero_add n) (mul one a) = a
  /-- Right unitality. -/
  mul_one : ∀ {n : ℤ} (a : carrier n), degCast (add_zero n) (mul a one) = a
  /-- The differential squares to zero. -/
  d_d : ∀ {n : ℤ} (a : carrier n), d (d a) = 0
  /-- The graded Leibniz rule `d(a b) = d(a) b + (-1)^m a d(b)` for `a in A^m`. -/
  leibniz : ∀ {m n : ℤ} (a : carrier m) (b : carrier n),
    d (mul a b) =
      degCast (by ring) (mul (d a) b) +
        degCast (by ring) (signZ R m • mul a (d b))

attribute [instance] DGAlgebra.addCommGroup DGAlgebra.module

/-- A *graded (right) `A`-module* (the underlying structure of Definition 1, and
the objects of `Mod_A` in Definition 2): a `Z`-indexed family of `R`-modules
`M^n` together with a right `A`-action `M^n x A^m -> M^{n+m}` that is `R`-bilinear
in each variable and satisfies the right-module laws. The module axioms are
FIELDS of this structure, so every term is a genuine graded `A`-module. -/
structure GradedModule (A : DGAlgebra R) where
  /-- The graded pieces `M^n`. -/
  carrier : ℤ → Type
  [addCommGroup : ∀ n, AddCommGroup (carrier n)]
  [module : ∀ n, Module R (carrier n)]
  /-- The right action `M^n x A^m -> M^{n+m}`, `R`-bilinear in each variable. -/
  smul : ∀ {n m : ℤ}, carrier n →ₗ[R] A.carrier m →ₗ[R] carrier (n + m)
  /-- Associativity of the action with the algebra multiplication. -/
  smul_mul : ∀ {n m p : ℤ} (x : carrier n) (a : A.carrier m) (b : A.carrier p),
    degCast (add_assoc n m p) (smul (smul x a) b) = smul x (A.mul a b)
  /-- The unit acts trivially. -/
  smul_one : ∀ {n : ℤ} (x : carrier n), degCast (add_zero n) (smul x A.one) = x

attribute [instance] GradedModule.addCommGroup GradedModule.module

namespace GradedModule

variable {A : DGAlgebra R}

/-- A *graded `A`-module map* `g : M -> N` (Definition 2): a degree-preserving
family of `R`-linear maps compatible with the `A`-action. It is **not** required
to commute with any differential. -/
structure Hom (M N : GradedModule A) where
  /-- The degree-`n` component `M^n -> N^n`. -/
  app : ∀ n, M.carrier n →ₗ[R] N.carrier n
  /-- Compatibility with the right `A`-action. -/
  map_smul : ∀ {n m : ℤ} (x : M.carrier n) (a : A.carrier m),
    app (n + m) (M.smul x a) = N.smul (app n x) a

namespace Hom

variable {M N P : GradedModule A}

/-- The identity graded `A`-module map. -/
def id (M : GradedModule A) : Hom M M where
  app _ := LinearMap.id
  map_smul _ _ := rfl

/-- Composition of graded `A`-module maps. -/
def comp (g : Hom N P) (f : Hom M N) : Hom M P where
  app n := (g.app n).comp (f.app n)
  map_smul x a := by
    simp only [LinearMap.comp_apply]
    rw [f.map_smul, g.map_smul]

/-- Two graded module maps are equal when their components agree. -/
@[ext] theorem ext {f g : Hom M N} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; simp only [Hom.mk.injEq]; funext n; exact h n

/-- A graded `A`-module map is *injective* if every component is injective. -/
def Injective (f : Hom M N) : Prop := ∀ n, Function.Injective (f.app n)

end Hom

end GradedModule

/-- A *differential graded `A`-module* (Stacks, Tag 09JI): a graded `A`-module
together with a degree `+1` differential `d` satisfying `d . d = 0` and the
graded Leibniz rule. These axioms are FIELDS of this structure, so every term is
a genuine differential graded `A`-module. -/
structure DGModule (A : DGAlgebra R) extends GradedModule A where
  /-- The degree `+1` differential. -/
  d : ∀ {n : ℤ}, carrier n →ₗ[R] carrier (n + 1)
  /-- The differential squares to zero. -/
  d_d : ∀ {n : ℤ} (x : carrier n), d (d x) = 0
  /-- The graded Leibniz rule `d(x a) = d(x) a + (-1)^n x d(a)` for `x in M^n`. -/
  leibniz : ∀ {n m : ℤ} (x : carrier n) (a : A.carrier m),
    d (smul x a) =
      degCast (by ring) (smul (d x) a) +
        degCast (by ring) (signZ R n • smul x (A.d a))

namespace DGModule

variable {A : DGAlgebra R}

/-- A *homomorphism of differential graded `A`-modules* `f : M -> N`: a graded
`A`-module map between the underlying graded modules that commutes with the
differentials (`f . d_M = d_N . f`). -/
structure Hom (M N : DGModule A) extends
    GradedModule.Hom M.toGradedModule N.toGradedModule where
  /-- Compatibility with the differentials: `f . d_M = d_N . f`. -/
  map_d : ∀ {n : ℤ} (x : M.carrier n), app (n + 1) (M.d x) = N.d (app n x)

namespace Hom

variable {M N : DGModule A}

/-- The underlying graded `A`-module map of a DG-module homomorphism. -/
def toGradedHom (f : Hom M N) : GradedModule.Hom M.toGradedModule N.toGradedModule :=
  f.toHom

/-- A DG-module homomorphism is *injective* if its underlying graded map is, i.e.
if every degree component is injective. -/
def Injective (f : Hom M N) : Prop := f.toHom.Injective

end Hom

/-- Definition 3 (Stacks, Tag 0FQD). A differential graded `A`-module `I` is
*graded injective* (injective as a graded `A`-module) if its underlying graded
`A`-module is an injective object of `Mod_A`: for every injective graded
`A`-module map `j : N -> N'` and every graded `A`-module map `phi : N -> I`,
there is a graded `A`-module map `psi : N' -> I` with `psi . j = phi`. Since
`GradedModule A` already carries the graded-module axioms, the quantifiers range
exactly over the objects of the abelian category `Mod_A`. -/
def GradedInjective (I : DGModule A) : Prop :=
  ∀ (N N' : GradedModule A) (j : GradedModule.Hom N N'), j.Injective →
    ∀ φ : GradedModule.Hom N I.toGradedModule,
      ∃ ψ : GradedModule.Hom N' I.toGradedModule, ψ.comp j = φ

/-- Definition 4 (Stacks, Tag 09JT(1)). A homomorphism `f : K -> L` of
differential graded `A`-modules is an *admissible monomorphism* if there is a
**graded** `A`-module map `pi : L -> K` (not required to commute with the
differentials) with `pi . f = id_K`. -/
def IsAdmissibleMono {K L : DGModule A} (f : Hom K L) : Prop :=
  ∃ π : GradedModule.Hom L.toGradedModule K.toGradedModule,
    π.comp f.toGradedHom = GradedModule.Hom.id K.toGradedModule

end DGModule

-- Main Statement(s)

/-- **Stacks, Tag 09K2 / Lemma 22.19.1.** Let `f : I -> M` be an injective
homomorphism of differential graded `A`-modules. If `I` is graded injective
(Definition 3), then `f` is an admissible monomorphism (Definition 4): there is a
graded `A`-module map `pi : M -> I` with `pi . f = id_I`.

Because the structures `DGAlgebra`, `GradedModule`, `DGModule` bundle all their
axioms, `A`, `I`, `M` are genuine objects and no extra hypotheses are needed. -/
@[stacks 09K2]
theorem admissibleMono_of_gradedInjective {A : DGAlgebra R}
    {I M : DGModule A} (f : DGModule.Hom I M)
    (hf : f.Injective) (hI : I.GradedInjective) :
    DGModule.IsAdmissibleMono f := by
  obtain ⟨ψ, hψ⟩ :=
    hI I.toGradedModule M.toGradedModule f.toGradedHom hf
      (GradedModule.Hom.id I.toGradedModule)
  exact ⟨ψ, hψ⟩

end Stacks.DifferentialGradedModule.AdmissibleMono
