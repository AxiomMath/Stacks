module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation

/-!
# The higher codimension Gysin class of a virtual normal bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be an
immersion of schemes locally of finite type over `S` and let `𝒩` be a virtual normal bundle for
`i` in the sense of Stacks 0FBQ (2): a finite locally free `𝒪_Z`-module together with a surjection
`𝒩^∨ ⟶ 𝒞_{Z/X}` onto the conormal sheaf. Write `p : N = 𝐕(𝒩^∨) ⟶ Z` for the vector bundle of
`𝒩^∨`, the relative spectrum of `Sym(𝒩^∨)`.

Stacks 0FBK attaches to this datum a bivariant class `c(Z ⟶ X, 𝒩)`, and the way it is attached is
by *division*: the deformation space of Stacks 0FBH carries a canonical class `C` (Stacks 0F9J),
and the composite `i_* ∘ j^* ∘ C` of that class with the restriction to the normal cone and the
pushforward into `N` is a bivariant class for `N ⟶ X`. The class `c(Z ⟶ X, 𝒩)` is then *defined*
by the relation

  `i_* ∘ j^* ∘ C = p^* ∘ c(Z ⟶ X, 𝒩)`,

which pins `c(Z ⟶ X, 𝒩)` down because flat pullback along a vector bundle projection is bijective
on Chow groups (Stacks 02TY). This file proves that the relation does pin it down, for any
bivariant classes standing in the places of `p^*` and `i_* ∘ j^* ∘ C`.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.totalSpace` — the vector bundle `N = 𝐕(𝒩^∨)` of the
  construction, and `Stacks.Chow.VirtualNormalBundle.projection` its projection `p : N ⟶ Z`.
* `Stacks.Chow.BivariantClass.CapInjective` — the assertion that every cap operation of a
  bivariant class is injective. For `p^*` this is the injectivity half of Stacks 02TY.

## Main results

* `Stacks.Chow.cap_eq_of_isBivariantClassComposition_left` and
  `Stacks.Chow.eq_of_isBivariantClassComposition_left` — left cancellation for the composition of
  bivariant classes: if the outer factor has injective cap operations, then the composition
  formula of `Stacks.Chow.IsBivariantClassComposition` determines the inner factor.
* `Stacks.Chow.cap_eq_of_isVirtualNormalGysinRelation` and
  `Stacks.Chow.eq_of_isVirtualNormalGysinRelation` — the step of the proof of Stacks 0FBK that
  makes the construction legitimate, for abstract classes `p^*` and `i_* ∘ j^* ∘ C`: the relation
  `i_* ∘ j^* ∘ C = p^* ∘ c(Z ⟶ X, 𝒩)` determines
  `c(Z ⟶ X, 𝒩)`, both as a class and operation by operation.

## Implementation notes

### Relation to the construction of the class

The source proof of Stacks 0FBK begins with "`i_* ∘ j^* ∘ C = p^* ∘ c` defines `c`, since `p^*`
is bijective on Chow groups". This file proves that step in an abstract form, as
`Stacks.Chow.eq_of_isVirtualNormalGysinRelation`: the classes `p^*` and `i_* ∘ j^* ∘ C` are the
parameters `flat` and `b`, the bijectivity of `p^*` is weakened to the injectivity
`Stacks.Chow.BivariantClass.CapInjective` that the argument uses, and the relation is expressed by
the characterization `Stacks.Chow.IsBivariantClassComposition` of Stacks 0FE0, with `p^*` as the
outer factor and `c(Z ⟶ X, 𝒩)` as the inner one.

The class itself, with all of its ingredients constructed, is built elsewhere:
`Stacks.Chow.VirtualNormalBundle.virtualNormalClass` and
`Stacks.Chow.virtualNormalBundleClass` at constant rank (with the class `C` of Stacks 0F9J, the
deformation space of Stacks 0FBH, the flat pullback `p^*` of Stacks 0B78 and the bijectivity of
Stacks 02TY all supplied), and `Stacks.Chow.VirtualNormalBundle.completedClass` in
`A^*(Z ⟶ X)^∧` at arbitrary rank, with the base-change clause. The statement of Stacks 0FBK is
`StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Statement`.

### Degrees

The degrees are left general: `flat` has degree `p`, the sought class degree `q`, and
`i_* ∘ j^* ∘ C` degree `p + q`, which is the degree bookkeeping
`Stacks.Chow.IsBivariantClassComposition` imposes. Stacks 0FBK is the case `p = -r`, `q = r` with
`r` the rank of `𝒩`, where `i_* ∘ j^* ∘ C` has degree zero and `c(Z ⟶ X, 𝒩)` lies in
`A^r(Z ⟶ X)`; stating the general case is stronger and costs nothing.

### The two hypotheses the vector bundle carries

`Stacks.Chow.VirtualNormalBundle.totalSpace` is
`AlgebraicGeometry.Scheme.Modules.vectorBundle Z 𝒩^∨`, which carries quasi-coherence of
`Sym(𝒩^∨)` as an algebra sheaf exactly as `Stacks.Conormal.normalBundle` does; Stacks 01CK
asserts it, and what stands in the way of discharging it is the identification recorded in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule`. Quasi-coherence of `𝒩^∨`
itself is *not* carried: it is derived below from finite local freeness of `𝒩`.

That `p` is locally of finite type is carried as an instance hypothesis. It is not an extra
assumption on the geometry — `𝒩^∨` is of finite presentation because `𝒩` is finite locally free
(Stacks 01C6), and the projection of the vector bundle of a module of finite presentation is
locally of finite presentation — but it is needed to *write down* a bivariant class for `p`, so it
has to be available at the point where the statement is made.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The vector bundle of a virtual normal bundle -/

section TotalSpace

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]

/-- The dual `𝒩^∨` of a virtual normal bundle is quasi-coherent: `𝒩` is finite locally free,
hence of finite presentation, and the dual of a module of finite presentation is
quasi-coherent. -/
instance VirtualNormalBundle.isQuasicoherent_dualSheaf (N : VirtualNormalBundle i) :
    (dualSheaf N.bundle).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.InternalHomModules.isQuasicoherent_dualSheaf N.bundle
    (SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree N.bundle N.isFiniteLocallyFree)

/-- The vector bundle `N = 𝐕(𝒩^∨) = Spec_Z(Sym(𝒩^∨))` of a virtual normal bundle `𝒩` for an
immersion `i : Z ⟶ X`. This is the scheme over `Z` whose flat pullback the relation of Stacks
0FBK divides by. -/
def VirtualNormalBundle.totalSpace (N : VirtualNormalBundle i)
    [(Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf N.bundle)).IsQuasicoherent] :
    Scheme.{u} :=
  Scheme.Modules.vectorBundle Z (dualSheaf N.bundle)

/-- The projection `p : N = 𝐕(𝒩^∨) ⟶ Z` of the vector bundle of a virtual normal bundle. -/
def VirtualNormalBundle.projection (N : VirtualNormalBundle i)
    [(Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf N.bundle)).IsQuasicoherent] :
    N.totalSpace ⟶ Z :=
  Scheme.Modules.vectorBundleToBase Z (dualSheaf N.bundle)

/-- The projection of the vector bundle of a virtual normal bundle is an affine morphism. -/
instance VirtualNormalBundle.isAffineHom_projection (N : VirtualNormalBundle i)
    [(Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf N.bundle)).IsQuasicoherent] :
    IsAffineHom N.projection :=
  Scheme.Modules.isAffineHom_vectorBundleToBase Z (dualSheaf N.bundle)

end TotalSpace

/-! ### Injective cap operations -/

/-- A bivariant class *has injective cap operations* if every one of its cap operations
`A_k(T) ⟶ A_{k-p}(T ×_Y X)` is injective. For the flat pullback along a vector bundle projection
this is the injectivity half of Stacks 02TY. -/
def BivariantClass.CapInjective {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ} (c : BivariantClass C G sX sY f hf p) :
    Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ), Function.Injective (c.cap g k)

/-! ### Left cancellation for the composition of bivariant classes -/

section Cancellation

variable {C : ChowSituation.{u}} {G : GysinSystem C} {N Z X : Scheme.{u}} {sN : N ⟶ C.S}
  [LocallyOfFiniteType sN] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {pr : N ⟶ Z} [LocallyOfFiniteType pr] {i : Z ⟶ X}
  [LocallyOfFiniteType i] {hpr : pr ≫ sZ = sN} {hi : i ≫ sX = sZ}
  {hpp : ProperPushforwardDescends C} {p q : ℤ} {a : BivariantClass C G sN sZ pr hpr p}
  {c c' : BivariantClass C G sZ sX i hi q}
  {b : BivariantClass C G sN sX (pr ≫ i) (comp_comp_structureMorphism_eq hpr hi) (p + q)}

/-- Left cancellation for the composition formula of Stacks 0FE0, operation by operation: if the
outer factor `a` has injective cap operations, then the inner factor of a composite is determined
on every test scheme. -/
theorem cap_eq_of_isBivariantClassComposition_left (hinj : a.CapInjective)
    (h : IsBivariantClassComposition C G sN sZ sX pr i hpr hi hpp p q a c b)
    (h' : IsBivariantClassComposition C G sN sZ sX pr i hpr hi hpp p q a c' b)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    c.cap t k α = c'.cap t k α := by
  have key : bivariantCompositeCap C G sN sZ sX pr i hpr hi hpp p q a c t k α =
      bivariantCompositeCap C G sN sZ sX pr i hpr hi hpp p q a c' t k α :=
    eq_of_heq ((h t k α).symm.trans (h' t k α))
  rw [bivariantCompositeCap_apply, bivariantCompositeCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso] at key
  exact hinj (pullback.fst i t) (k - q)
    (chowPushforwardOfIso_injective C (pullback.fst pr (pullback.fst i t) ≫ sN)
      (pullback.fst (pr ≫ i) t ≫ sN) (pullbackRightPullbackFstIso i t pr).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sN pr i t) (k - q - p) key)

/-- Left cancellation for the composition formula of Stacks 0FE0: if the outer factor `a` has
injective cap operations, then two bivariant classes that both compose with `a` to `b` are
equal. -/
theorem eq_of_isBivariantClassComposition_left (hinj : a.CapInjective)
    (h : IsBivariantClassComposition C G sN sZ sX pr i hpr hi hpp p q a c b)
    (h' : IsBivariantClassComposition C G sN sZ sX pr i hpr hi hpp p q a c' b) : c = c' := by
  refine BivariantClass.ext C G sZ sX i hi q ?_
  intro T t _ k α
  exact cap_eq_of_isBivariantClassComposition_left (hpp := hpp) hinj h h' t k α

end Cancellation

/-! ### Stacks 0FBK: the defining relation determines the class -/

section GysinClass

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {i : Z ⟶ X} [IsImmersion i]
  [LocallyOfFiniteType i] (hi : i ≫ sX = sZ) (N : VirtualNormalBundle i)
  [(Scheme.Modules.symmetricAlgebraSheaf Z (dualSheaf N.bundle)).IsQuasicoherent]
  [LocallyOfFiniteType N.projection] (hpp : ProperPushforwardDescends C) (p q : ℤ)
  {flat : BivariantClass C G (N.projection ≫ sZ) sZ N.projection rfl p}
  {b : BivariantClass C G (N.projection ≫ sZ) sX (N.projection ≫ i)
    (comp_comp_structureMorphism_eq rfl hi) (p + q)}
  {c c' : BivariantClass C G sZ sX i hi q}

/-- The relation `i_* ∘ j^* ∘ C = p^* ∘ c(Z ⟶ X, 𝒩)` of Stacks 0FBK determines the cap
operations of `c(Z ⟶ X, 𝒩)`: on every test scheme and in every degree, two bivariant classes
satisfying it cap the same way. Here `p : N = 𝐕(𝒩^∨) ⟶ Z` is the projection of the vector bundle
of the virtual normal bundle, `flat` stands for its flat pullback `p^*` and `b` for
`i_* ∘ j^* ∘ C`, and the hypothesis on `flat` is the injectivity of Stacks 02TY. -/
theorem cap_eq_of_isVirtualNormalGysinRelation (hinj : flat.CapInjective)
    (h : IsBivariantClassComposition C G (N.projection ≫ sZ) sZ sX N.projection i rfl hi hpp p q
      flat c b)
    (h' : IsBivariantClassComposition C G (N.projection ≫ sZ) sZ sX N.projection i rfl hi hpp p q
      flat c' b)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    c.cap t k α = c'.cap t k α :=
  cap_eq_of_isBivariantClassComposition_left (hpp := hpp) hinj h h' t k α

/-- The class `c(Z ⟶ X, 𝒩)` of Stacks 0FBK attached to an immersion with a virtual normal
bundle is determined by the relation `i_* ∘ j^* ∘ C = p^* ∘ c(Z ⟶ X, 𝒩)`: two bivariant classes
of the same degree for `i` that both satisfy it are equal. This is the step the source calls
legitimate because `p^*` is bijective on Chow groups, and injectivity is all it uses. -/
theorem eq_of_isVirtualNormalGysinRelation (hinj : flat.CapInjective)
    (h : IsBivariantClassComposition C G (N.projection ≫ sZ) sZ sX N.projection i rfl hi hpp p q
      flat c b)
    (h' : IsBivariantClassComposition C G (N.projection ≫ sZ) sZ sX N.projection i rfl hi hpp p q
      flat c' b) :
    c = c' :=
  eq_of_isBivariantClassComposition_left (hpp := hpp) hinj h h'

end GysinClass

end Stacks.Chow

end
