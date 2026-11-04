module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalars
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# The diagonal of the stack of algebraic spaces (Stacks 0D1F)

Stacks 0D1F asserts that the diagonal of the stack `Spaces'_{fp, flat, proper}` of Stacks 0D1D
is representable by algebraic spaces.

By criterion (2) of Stacks 045G it suffices that for a scheme `U` and two algebraic spaces `Z`,
`X` over `U` of finite presentation, flat and proper, the functor `Isom_U(Z, X)` is an algebraic
space. This follows from the fibre product square

```text
  Isom_U(Z, X) -----------------------------------> U
       |                                            |
       v                                            v
  Mor_U(Z, X) × Mor_U(X, Z) -> Mor_U(Z, Z) × Mor_U(X, X)
```

whose bottom arrow sends `(φ, ψ)` to `(ψ ∘ φ, φ ∘ ψ)` and whose right arrow is the pair of
identities; the four relative morphism functors on the bottom row are algebraic spaces by
Stacks 0D1C, and the category of algebraic spaces over a scheme has fibre products
(Stacks 02X2).

The square is constructed over an arbitrary base `Q`, and `AlgebraicGeometry.Space.relativeIsom`
is defined as the fibre product of its cospan.

## Main definitions

* `AlgebraicGeometry.Space.RelativeMorphism.comp`: the composition of two relative morphisms of
  Stacks 05Y1.
* `AlgebraicGeometry.Space.relativeHomIdentitySection`: the identity section
  `Q ⟶ Mor_Q(Z, Z)`.
* `AlgebraicGeometry.Space.relativeHomCompPair`: the bottom arrow of the square,
  `Mor_Q(Z, X) ×_Q Mor_Q(X, Z) ⟶ Mor_Q(Z, Z) ×_Q Mor_Q(X, X)`.
* `AlgebraicGeometry.Space.relativeIsom`: the functor `Isom_Q(Z, X)`, as the fibre product of
  the source's square, with `AlgebraicGeometry.Space.relativeIsomProjection` its projection
  to `Q`.
* `AlgebraicGeometry.Space.HasAlgebraicIsomFunctors`: the statement that `Isom_U(Z, X)` is an
  algebraic space for every scheme `U` of the site and all finitely presented, flat and proper
  `Z`, `X` over `U`. This is the concrete form of criterion (2) of Stacks 045G for the stack of
  Stacks 0D1D.
* `AlgebraicGeometry.Space.HasHilbertModels`: the statement of Stacks 0D01 over every algebraic
  space base.

## Main results

* `AlgebraicGeometry.Space.relativeIsom_forward_comp_backward` and
  `AlgebraicGeometry.Space.relativeIsom_backward_comp_forward`: a section of `Isom_Q(Z, X)` is a
  pair of relative morphisms, in the two directions, whose two composites are the identities.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeIsom`: `Isom_Q(Z, X)` is an algebraic space
  when the four relative morphism functors of the square are.
* `AlgebraicGeometry.Space.hasAlgebraicIsomFunctors`: **Stacks 0D1F**, criterion (2) of
  Stacks 045G for the stack of Stacks 0D1D, from Stacks 0D1C.
* `AlgebraicGeometry.Space.hasRepresentableDiagonal_properFlatSpacesStack`: **Stacks 0D1F**, the
  diagonal is representable by algebraic spaces.

## Implementation notes

Composition of relative morphisms is clean in the source's second description of the pair
`(a, b)`, the one `AlgebraicGeometry.Space.RelativeMorphism` uses: with `b : T ×_{a, Q} Z ⟶ X`
lying over `Q`, the pair `(a, b)` and a pair `(a, b')` with `b' : T ×_{a, Q} X ⟶ Y` compose to
`(a, c ≫ b')` where `c : T ×_{a, Q} Z ⟶ T ×_{a, Q} X` is the morphism with components the
projection to `T` and `b`. No transport along an identification of base changes appears, and
compatibility with restriction of pairs is one `CategoryTheory.Limits.pullback.hom_ext`.

The two maps of the square are assembled from `CategoryTheory.Limits.pullback.lift`, so that
the only part of them defined on elements is a map *out of* the fibre product
`Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`; for that the pointwise description of a fibre product of
presheaves is not needed either, because the two components of a section are read off by the
two projections of the fibre product and the equality of their bases is
`CategoryTheory.Limits.pullback.condition` evaluated at the section.

The results are stated under Stacks 0D01, as `AlgebraicGeometry.Space.HasHilbertModels`. In
`AlgebraicGeometry.Space.hasRepresentableDiagonal_properFlatSpacesStack` the hypothesis `hcmp`
states that the fibre of the stack of Stacks 0D1D over a scheme `U` is given by two finitely
presented, flat and proper families over `U` whose isomorphism presheaf is the functor
`Isom_U(Z, X)` read over `U` by Stacks 04SG.

## References

* [Stacks Project, Tag 0D1F](https://stacks.math.columbia.edu/tag/0D1F)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

section Pairs

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Y Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q} {y : Y ⟶ Q}

attribute [local implicit_reducible] RelativeMorphism.restrict

/-- **Composition of relative morphisms.** Two pairs of Stacks 05Y1 at `T` with the same first
component `a`, one for `z` against `x` and one for `x` against `y`, compose to a pair for `z`
against `y`: the morphism `T ×_{a, Q} Z ⟶ T ×_{a, Q} X` with components the projection to `T`
and the second component of the first pair, followed by the second component of the second
pair. -/
def RelativeMorphism.comp (p : RelativeMorphism B S hS Z X Q z x T)
    (q : RelativeMorphism B S hS X Y Q x y T) (h : p.base = q.base) :
    RelativeMorphism B S hS Z Y Q z y T where
  base := p.base
  morphism :=
    pullback.lift (f := q.base) (g := x) (pullback.fst p.base z) p.morphism
      (by rw [← h, p.commutes]; exact pullback.condition) ≫ q.morphism
  commutes := by
    rw [Category.assoc, q.commutes, ← Category.assoc, pullback.lift_snd, p.commutes]

attribute [local implicit_reducible] RelativeMorphism.comp

/-- The first component of a composite of relative morphisms is the first component of the first
factor. -/
@[simp]
theorem RelativeMorphism.comp_base (p : RelativeMorphism B S hS Z X Q z x T)
    (q : RelativeMorphism B S hS X Y Q x y T) (h : p.base = q.base) :
    (RelativeMorphism.comp p q h).base = p.base := rfl

/-- Restriction of a composite of relative morphisms along a morphism of test objects is the
composite of the restrictions. -/
theorem RelativeMorphism.restrict_comp' (p : RelativeMorphism B S hS Z X Q z x T)
    (q : RelativeMorphism B S hS X Y Q x y T) (h : p.base = q.base) (t : T' ⟶ T) :
    RelativeMorphism.restrict t (RelativeMorphism.comp p q h) =
      RelativeMorphism.comp (RelativeMorphism.restrict t p) (RelativeMorphism.restrict t q)
        (by simp [h]) :=
  RelativeMorphism.ext_of_base_eq rfl (by
    simp only [RelativeMorphism.comp, RelativeMorphism.restrict_morphism, pullback.congrHom,
      asIso_hom]
    simp only [← Category.assoc]
    refine congrArg (fun m => m ≫ q.morphism) (pullback.hom_ext ?_ ?_)
    · simp [pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [pullback.lift_snd])

end Pairs

section Square

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- The projection of the relative morphism functor, read on the section corresponding to a
given pair of Stacks 05Y1, is the first component of that pair. -/
theorem relativeHomProjection_app_symm_apply (T : BigFppfOver B S hS)
    (p : RelativeMorphism B S hS Z X Q z x (yoneda.obj T)) :
    (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (op T)
        ((relativeHomSections B S hS Z X Q z x hZ hX hQ T).symm p) = yonedaEquiv p.base := by
  rw [relativeHomProjection_app, Equiv.apply_symm_apply]

/-- **The identity section of the relative morphism functor**, `Q ⟶ Mor_Q(Z, Z)`: the section
`AlgebraicGeometry.Space.relativeHomIdentity` of Stacks 05YE, read at the relative morphism
functor of Stacks 05Y2. -/
def relativeHomIdentitySection : Q ⟶ relativeHom B S hS Z Z Q z z hZ hZ hQ :=
  relativeHomIdentity (relativeHomData B S hS Z Z Q z z hZ hZ hQ)

/-- The identity section is a section of the projection of the relative morphism functor: the
first component of an identity relative morphism is the section it was built from. -/
@[reassoc (attr := simp)]
theorem relativeHomIdentitySection_comp_projection :
    relativeHomIdentitySection B S hS Z Q z hZ hQ ≫
        relativeHomProjection B S hS Z Z Q z z hZ hZ hQ = 𝟙 Q := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun a => ?_)
  show (relativeHomProjection B S hS Z Z Q z z hZ hZ hQ).app T
    ((relativeHomIdentitySection B S hS Z Q z hZ hQ).app T a) = a
  rw [relativeHomProjection_app (V := T.unop),
    show relativeHomSections B S hS Z Z Q z z hZ hZ hQ T.unop
        ((relativeHomIdentitySection B S hS Z Q z hZ hQ).app T a) =
      RelativeMorphism.identity z (yonedaEquiv.symm a) from
    sections_relativeHomIdentity (relativeHomData B S hS Z Z Q z z hZ hZ hQ) T a,
    RelativeMorphism.identity_base, Equiv.apply_symm_apply]

/-- `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`, the lower left corner of the square of Stacks 0D1F. -/
def relativeHomPair : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (relativeHomProjection B S hS Z X Q z x hZ hX hQ)
    (relativeHomProjection B S hS X Z Q x z hX hZ hQ)

/-- `Mor_Q(Z, Z) ×_Q Mor_Q(X, X)`, the lower right corner of the square of Stacks 0D1F. -/
def relativeHomEndPair : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (relativeHomProjection B S hS Z Z Q z z hZ hZ hQ)
    (relativeHomProjection B S hS X X Q x x hX hX hQ)

/-- The first projection of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`. -/
def relativeHomPairProjFst :
    relativeHomPair B S hS Z X Q z x hZ hX hQ ⟶ relativeHom B S hS Z X Q z x hZ hX hQ :=
  pullback.fst _ _

/-- The second projection of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`. -/
def relativeHomPairProjSnd :
    relativeHomPair B S hS Z X Q z x hZ hX hQ ⟶ relativeHom B S hS X Z Q x z hX hZ hQ :=
  pullback.snd _ _

/-- The first component of a section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`, as a pair of
Stacks 05Y1. -/
def relativeHomPairFst (T : BigFppfOver B S hS)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    RelativeMorphism B S hS Z X Q z x (yoneda.obj T) :=
  relativeHomSections B S hS Z X Q z x hZ hX hQ T
    ((relativeHomPairProjFst B S hS Z X Q z x hZ hX hQ).app (op T) s)

/-- The second component of a section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`, as a pair of
Stacks 05Y1. -/
def relativeHomPairSnd (T : BigFppfOver B S hS)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    RelativeMorphism B S hS X Z Q x z (yoneda.obj T) :=
  relativeHomSections B S hS X Z Q x z hX hZ hQ T
    ((relativeHomPairProjSnd B S hS Z X Q z x hZ hX hQ).app (op T) s)

/-- The two components of a section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)` have the same first
component: that is the defining condition of the fibre product over `Q`. -/
theorem relativeHomPair_base_eq (T : BigFppfOver B S hS)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeHomPairFst B S hS Z X Q z x hZ hX hQ T s).base =
      (relativeHomPairSnd B S hS Z X Q z x hZ hX hQ T s).base := by
  refine yonedaEquiv.injective ?_
  have h1 : (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (op T)
      ((relativeHomPairProjFst B S hS Z X Q z x hZ hX hQ).app (op T) s) =
      yonedaEquiv (relativeHomPairFst B S hS Z X Q z x hZ hX hQ T s).base :=
    relativeHomProjection_app B S hS Z X Q z x hZ hX hQ T _
  have h2 : (relativeHomProjection B S hS X Z Q x z hX hZ hQ).app (op T)
      ((relativeHomPairProjSnd B S hS Z X Q z x hZ hX hQ).app (op T) s) =
      yonedaEquiv (relativeHomPairSnd B S hS Z X Q z x hZ hX hQ T s).base :=
    relativeHomProjection_app B S hS X Z Q x z hX hZ hQ T _
  rw [← h1, ← h2]
  exact ConcreteCategory.congr_hom
    (congrArg (fun η : relativeHomPair B S hS Z X Q z x hZ hX hQ ⟶ Q => η.app (op T))
      (pullback.condition (f := relativeHomProjection B S hS Z X Q z x hZ hX hQ)
        (g := relativeHomProjection B S hS X Z Q x z hX hZ hQ))) s

/-- The restriction of a section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)` has as its first component the
restriction of the first component. -/
theorem relativeHomPairFst_map {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    relativeHomPairFst B S hS Z X Q z x hZ hX hQ T'
        ((relativeHomPair B S hS Z X Q z x hZ hX hQ).map f.op s) =
      RelativeMorphism.restrict (yoneda.map f)
        (relativeHomPairFst B S hS Z X Q z x hZ hX hQ T s) := by
  rw [relativeHomPairFst, relativeHomPairFst, ← relativeHomSections_map]
  exact congrArg (relativeHomSections B S hS Z X Q z x hZ hX hQ T')
    (ConcreteCategory.congr_hom
      ((relativeHomPairProjFst B S hS Z X Q z x hZ hX hQ).naturality f.op) s)

/-- The restriction of a section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)` has as its second component the
restriction of the second component. -/
theorem relativeHomPairSnd_map {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    relativeHomPairSnd B S hS Z X Q z x hZ hX hQ T'
        ((relativeHomPair B S hS Z X Q z x hZ hX hQ).map f.op s) =
      RelativeMorphism.restrict (yoneda.map f)
        (relativeHomPairSnd B S hS Z X Q z x hZ hX hQ T s) := by
  rw [relativeHomPairSnd, relativeHomPairSnd, ← relativeHomSections_map]
  exact congrArg (relativeHomSections B S hS X Z Q x z hX hZ hQ T')
    (ConcreteCategory.congr_hom
      ((relativeHomPairProjSnd B S hS Z X Q z x hZ hX hQ).naturality f.op) s)

/-- The section of `Mor_Q(Z, Z)` given by the composite `Z ⟶ X ⟶ Z` of the two components of a
section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`. -/
def relativeHomCompFstApp (T : BigFppfOver B S hS)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeHom B S hS Z Z Q z z hZ hZ hQ).obj (op T) :=
  (relativeHomSections B S hS Z Z Q z z hZ hZ hQ T).symm
    (RelativeMorphism.comp (relativeHomPairFst B S hS Z X Q z x hZ hX hQ T s)
      (relativeHomPairSnd B S hS Z X Q z x hZ hX hQ T s)
      (relativeHomPair_base_eq B S hS Z X Q z x hZ hX hQ T s))

/-- The section of `Mor_Q(X, X)` given by the composite `X ⟶ Z ⟶ X` of the two components of a
section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)`. -/
def relativeHomCompSndApp (T : BigFppfOver B S hS)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeHom B S hS X X Q x x hX hX hQ).obj (op T) :=
  (relativeHomSections B S hS X X Q x x hX hX hQ T).symm
    (RelativeMorphism.comp (relativeHomPairSnd B S hS Z X Q z x hZ hX hQ T s)
      (relativeHomPairFst B S hS Z X Q z x hZ hX hQ T s)
      (relativeHomPair_base_eq B S hS Z X Q z x hZ hX hQ T s).symm)

/-- Taking the composite `Z ⟶ X ⟶ Z` commutes with restriction along a morphism of the site. -/
theorem relativeHomCompFstApp_map {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeHom B S hS Z Z Q z z hZ hZ hQ).map f.op
        (relativeHomCompFstApp B S hS Z X Q z x hZ hX hQ T s) =
      relativeHomCompFstApp B S hS Z X Q z x hZ hX hQ T'
        ((relativeHomPair B S hS Z X Q z x hZ hX hQ).map f.op s) := by
  refine (relativeHomSections B S hS Z Z Q z z hZ hZ hQ T').injective ?_
  rw [relativeHomSections_map, relativeHomCompFstApp, Equiv.apply_symm_apply,
    relativeHomCompFstApp, Equiv.apply_symm_apply, RelativeMorphism.restrict_comp']
  congr 1
  · exact (relativeHomPairFst_map B S hS Z X Q z x hZ hX hQ f s).symm
  · exact (relativeHomPairSnd_map B S hS Z X Q z x hZ hX hQ f s).symm

/-- Taking the composite `X ⟶ Z ⟶ X` commutes with restriction along a morphism of the site. -/
theorem relativeHomCompSndApp_map {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (s : (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeHom B S hS X X Q x x hX hX hQ).map f.op
        (relativeHomCompSndApp B S hS Z X Q z x hZ hX hQ T s) =
      relativeHomCompSndApp B S hS Z X Q z x hZ hX hQ T'
        ((relativeHomPair B S hS Z X Q z x hZ hX hQ).map f.op s) := by
  refine (relativeHomSections B S hS X X Q x x hX hX hQ T').injective ?_
  rw [relativeHomSections_map, relativeHomCompSndApp, Equiv.apply_symm_apply,
    relativeHomCompSndApp, Equiv.apply_symm_apply, RelativeMorphism.restrict_comp']
  congr 1
  · exact (relativeHomPairSnd_map B S hS Z X Q z x hZ hX hQ f s).symm
  · exact (relativeHomPairFst_map B S hS Z X Q z x hZ hX hQ f s).symm

/-- **The first half of the bottom arrow of the square of Stacks 0D1F**, the map
`Mor_Q(Z, X) ×_Q Mor_Q(X, Z) ⟶ Mor_Q(Z, Z)` sending `(φ, ψ)` to `ψ ∘ φ`. -/
def relativeHomCompFst :
    relativeHomPair B S hS Z X Q z x hZ hX hQ ⟶ relativeHom B S hS Z Z Q z z hZ hZ hQ where
  app T := ↾fun s => relativeHomCompFstApp B S hS Z X Q z x hZ hX hQ T.unop s
  naturality T T' f := by
    ext s
    exact (relativeHomCompFstApp_map B S hS Z X Q z x hZ hX hQ f.unop s).symm

/-- **The second half of the bottom arrow of the square of Stacks 0D1F**, the map
`Mor_Q(Z, X) ×_Q Mor_Q(X, Z) ⟶ Mor_Q(X, X)` sending `(φ, ψ)` to `φ ∘ ψ`. -/
def relativeHomCompSnd :
    relativeHomPair B S hS Z X Q z x hZ hX hQ ⟶ relativeHom B S hS X X Q x x hX hX hQ where
  app T := ↾fun s => relativeHomCompSndApp B S hS Z X Q z x hZ hX hQ T.unop s
  naturality T T' f := by
    ext s
    exact (relativeHomCompSndApp_map B S hS Z X Q z x hZ hX hQ f.unop s).symm

/-- The two halves of the bottom arrow of the square of Stacks 0D1F agree over `Q`: both
composites read off the common first component of the two relative morphisms. -/
theorem relativeHomCompFst_comp_projection :
    relativeHomCompFst B S hS Z X Q z x hZ hX hQ ≫
        relativeHomProjection B S hS Z Z Q z z hZ hZ hQ =
      relativeHomCompSnd B S hS Z X Q z x hZ hX hQ ≫
        relativeHomProjection B S hS X X Q x x hX hX hQ := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun s => ?_)
  show (relativeHomProjection B S hS Z Z Q z z hZ hZ hQ).app T
      (relativeHomCompFstApp B S hS Z X Q z x hZ hX hQ T.unop s) =
    (relativeHomProjection B S hS X X Q x x hX hX hQ).app T
      (relativeHomCompSndApp B S hS Z X Q z x hZ hX hQ T.unop s)
  rw [relativeHomCompFstApp, relativeHomCompSndApp, relativeHomProjection_app_symm_apply,
    relativeHomProjection_app_symm_apply, RelativeMorphism.comp_base,
    RelativeMorphism.comp_base]
  exact congrArg yonedaEquiv (relativeHomPair_base_eq B S hS Z X Q z x hZ hX hQ T.unop s)

/-- **The bottom arrow of the square of Stacks 0D1F**, the map
`Mor_Q(Z, X) ×_Q Mor_Q(X, Z) ⟶ Mor_Q(Z, Z) ×_Q Mor_Q(X, X)` sending `(φ, ψ)` to
`(ψ ∘ φ, φ ∘ ψ)`. -/
def relativeHomCompPair :
    relativeHomPair B S hS Z X Q z x hZ hX hQ ⟶ relativeHomEndPair B S hS Z X Q z x hZ hX hQ :=
  pullback.lift (relativeHomCompFst B S hS Z X Q z x hZ hX hQ)
    (relativeHomCompSnd B S hS Z X Q z x hZ hX hQ)
    (relativeHomCompFst_comp_projection B S hS Z X Q z x hZ hX hQ)

/-- **The right arrow of the square of Stacks 0D1F**, the pair of identity sections
`Q ⟶ Mor_Q(Z, Z) ×_Q Mor_Q(X, X)`. -/
def relativeHomIdentityPair : Q ⟶ relativeHomEndPair B S hS Z X Q z x hZ hX hQ :=
  pullback.lift (relativeHomIdentitySection B S hS Z Q z hZ hQ)
    (relativeHomIdentitySection B S hS X Q x hX hQ)
    (by rw [relativeHomIdentitySection_comp_projection,
      relativeHomIdentitySection_comp_projection])

/-- **The isomorphism functor `Isom_Q(Z, X)` of Stacks 0D1F**: the fibre product of the square
of the source, whose sections over a test scheme are the pairs of relative morphisms, one in
each direction, whose two composites are the identities. -/
def relativeIsom : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (relativeHomCompPair B S hS Z X Q z x hZ hX hQ)
    (relativeHomIdentityPair B S hS Z X Q z x hZ hX hQ)

/-- The projection `Isom_Q(Z, X) ⟶ Q`. -/
def relativeIsomProjection : relativeIsom B S hS Z X Q z x hZ hX hQ ⟶ Q :=
  pullback.snd _ _

/-- The section of `Mor_Q(Z, X) ×_Q Mor_Q(X, Z)` underlying a section of `Isom_Q(Z, X)`. -/
def relativeIsomPair (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeHomPair B S hS Z X Q z x hZ hX hQ).obj (op T) :=
  (pullback.fst (relativeHomCompPair B S hS Z X Q z x hZ hX hQ)
    (relativeHomIdentityPair B S hS Z X Q z x hZ hX hQ)).app (op T) s

/-- The relative morphism `Z ⟶ X` underlying a section of `Isom_Q(Z, X)`. -/
def relativeIsomForward (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    RelativeMorphism B S hS Z X Q z x (yoneda.obj T) :=
  relativeHomPairFst B S hS Z X Q z x hZ hX hQ T
    (relativeIsomPair B S hS Z X Q z x hZ hX hQ T s)

/-- The relative morphism `X ⟶ Z` underlying a section of `Isom_Q(Z, X)`. -/
def relativeIsomBackward (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    RelativeMorphism B S hS X Z Q x z (yoneda.obj T) :=
  relativeHomPairSnd B S hS Z X Q z x hZ hX hQ T
    (relativeIsomPair B S hS Z X Q z x hZ hX hQ T s)

/-- The two relative morphisms underlying a section of `Isom_Q(Z, X)` have the same first
component. -/
theorem relativeIsom_base_eq (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeIsomForward B S hS Z X Q z x hZ hX hQ T s).base =
      (relativeIsomBackward B S hS Z X Q z x hZ hX hQ T s).base :=
  relativeHomPair_base_eq B S hS Z X Q z x hZ hX hQ T _

/-- The defining condition of `Isom_Q(Z, X)` at a section, evaluated at the section: the two
composites of the underlying pair of relative morphisms are the two identity relative
morphisms. -/
private theorem relativeIsom_condition (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    (relativeHomCompPair B S hS Z X Q z x hZ hX hQ).app (op T)
        (relativeIsomPair B S hS Z X Q z x hZ hX hQ T s) =
      (relativeHomIdentityPair B S hS Z X Q z x hZ hX hQ).app (op T)
        ((relativeIsomProjection B S hS Z X Q z x hZ hX hQ).app (op T) s) :=
  ConcreteCategory.congr_hom
    (congrArg (fun η : relativeIsom B S hS Z X Q z x hZ hX hQ ⟶
        relativeHomEndPair B S hS Z X Q z x hZ hX hQ => η.app (op T))
      (pullback.condition (f := relativeHomCompPair B S hS Z X Q z x hZ hX hQ)
        (g := relativeHomIdentityPair B S hS Z X Q z x hZ hX hQ))) s

/-- A functorial projection `π` of `Mor_Q(Z, Z) ×_Q Mor_Q(X, X)` read on the defining condition of
`Isom_Q(Z, X)` at a section: the pushforward by `π` of the two sides of the condition. -/
private theorem relativeIsom_apply_eq (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T))
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : relativeHomEndPair B S hS Z X Q z x hZ hX hQ ⟶ W)
    {ν : relativeHomPair B S hS Z X Q z x hZ hX hQ ⟶ W} {ι : Q ⟶ W}
    (hν : relativeHomCompPair B S hS Z X Q z x hZ hX hQ ≫ π = ν)
    (hι : relativeHomIdentityPair B S hS Z X Q z x hZ hX hQ ≫ π = ι) :
    ν.app (op T) (relativeIsomPair B S hS Z X Q z x hZ hX hQ T s) =
      ι.app (op T) ((relativeIsomProjection B S hS Z X Q z x hZ hX hQ).app (op T) s) := by
  subst hν hι
  exact congrArg (π.app (op T)) (relativeIsom_condition B S hS Z X Q z x hZ hX hQ T s)


/-- The defining condition of `Isom_Q(Z, X)` at a section, pushed into `Mor_Q(Z, Z)`: the
composite of the two underlying relative morphisms, in the order `Z ⟶ X ⟶ Z`, is the
identity. -/
theorem relativeIsom_forward_comp_backward (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    RelativeMorphism.comp (relativeIsomForward B S hS Z X Q z x hZ hX hQ T s)
        (relativeIsomBackward B S hS Z X Q z x hZ hX hQ T s)
        (relativeIsom_base_eq B S hS Z X Q z x hZ hX hQ T s) =
      RelativeMorphism.identity z
        (yonedaEquiv.symm ((relativeIsomProjection B S hS Z X Q z x hZ hX hQ).app (op T) s)) := by
  refine (relativeHomSections B S hS Z Z Q z z hZ hZ hQ T).symm.injective ?_
  exact relativeIsom_apply_eq B S hS Z X Q z x hZ hX hQ T s (pullback.fst _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)

/-- The defining condition of `Isom_Q(Z, X)` at a section, pushed into `Mor_Q(X, X)`: the
composite of the two underlying relative morphisms, in the order `X ⟶ Z ⟶ X`, is the
identity. -/
theorem relativeIsom_backward_comp_forward (T : BigFppfOver B S hS)
    (s : (relativeIsom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    RelativeMorphism.comp (relativeIsomBackward B S hS Z X Q z x hZ hX hQ T s)
        (relativeIsomForward B S hS Z X Q z x hZ hX hQ T s)
        (relativeIsom_base_eq B S hS Z X Q z x hZ hX hQ T s).symm =
      RelativeMorphism.identity x
        (yonedaEquiv.symm ((relativeIsomProjection B S hS Z X Q z x hZ hX hQ).app (op T) s)) := by
  refine (relativeHomSections B S hS X X Q x x hX hX hQ T).symm.injective ?_
  exact relativeIsom_apply_eq B S hS Z X Q z x hZ hX hQ T s (pullback.snd _ _)
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)

/-- The isomorphism functor `Isom_Q(Z, X)` is an algebraic space as soon as the four relative
morphism functors of the square of Stacks 0D1F are. -/
theorem isAlgebraicSpace_relativeIsom
    (hZX : IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ))
    (hXZ : IsAlgebraicSpace B S hS (relativeHom B S hS X Z Q x z hX hZ hQ))
    (hZZ : IsAlgebraicSpace B S hS (relativeHom B S hS Z Z Q z z hZ hZ hQ))
    (hXX : IsAlgebraicSpace B S hS (relativeHom B S hS X X Q x x hX hX hQ)) :
    IsAlgebraicSpace B S hS (relativeIsom B S hS Z X Q z x hZ hX hQ) :=
  isAlgebraicSpace_pullback B S hS _ _
    (isAlgebraicSpace_pullback B S hS _ _ hZX hXZ hQ) hQ
    (isAlgebraicSpace_pullback B S hS _ _ hZZ hXX hQ)

end Square

section Diagonal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0D01** for every base: every algebraic space over `S` has models of the Hilbert
presheaves of the finitely presented, separated morphisms to it. -/
def HasHilbertModels : Prop :=
  ∀ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hQ : IsAlgebraicSpace B S hS Q),
    HasHilbertModelsOver hQ

/-- **Criterion (2) of Stacks 045G for the stack of Stacks 0D1D, in concrete form**: for every
scheme `U` of the site and all algebraic spaces `Z`, `X` of finite presentation, flat and proper
over `U`, the isomorphism functor `Isom_U(Z, X)` is an algebraic space. -/
def HasAlgebraicIsomFunctors : Prop :=
  ∀ (U : BigFppfOver B S hS) (Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (z : Z ⟶ yoneda.obj U) (x : X ⟶ yoneda.obj U),
    IsFinitePresentation B S hS z → IsFlat B S hS z → IsProper B S hS z →
    IsFinitePresentation B S hS x → IsFlat B S hS x → IsProper B S hS x →
    IsAlgebraicSpace B S hS
      (relativeIsom B S hS Z X (yoneda.obj U) z x hZ hX (isAlgebraicSpace_yoneda B S hS U))

/-- Criterion (2) of Stacks 045G in concrete form, assuming Stacks 0D01: the isomorphism functor
of two finitely presented, flat and proper families over a scheme of the site is an algebraic
space. -/
@[stacks 0D1F "the Isom functor of two finitely presented, flat and proper families is an \
algebraic space, which is criterion (2) of Stacks 045G for the diagonal"]
theorem hasAlgebraicIsomFunctors (hilb : HasHilbertModels B S hS) :
    HasAlgebraicIsomFunctors B S hS := by
  intro U Z X hZ hX z x hz_fp hz_flat hz_proper hx_fp hx_flat hx_proper
  have hQ := isAlgebraicSpace_yoneda B S hS U
  exact isAlgebraicSpace_relativeIsom B S hS Z X (yoneda.obj U) z x hZ hX hQ
    (isAlgebraicSpace_relativeHom z x hZ hX hQ hx_fp hx_proper.1 hz_fp hz_flat hz_proper)
    (isAlgebraicSpace_relativeHom x z hX hZ hQ hz_fp hz_proper.1 hx_fp hx_flat hx_proper)
    (isAlgebraicSpace_relativeHom z z hZ hZ hQ hz_fp hz_proper.1 hz_fp hz_flat hz_proper)
    (isAlgebraicSpace_relativeHom x x hX hX hQ hx_fp hx_proper.1 hx_fp hx_flat hx_proper)

/-- The stack `Spaces'_{fp, flat, proper}` of Stacks 0D1D, as an object of the 2-category of
categories fibred in groupoids over the big fppf site of `S`. Its structure functor is the
projection `p'_{fp, flat, proper}`, which is fibred in groupoids by Stacks 0D1E. -/
abbrev properFlatSpacesStack :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (cartesianProperFlatProjection B S hS))
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)

/-- **Stacks 0D1F.** The diagonal

```text
  Spaces'_{fp, flat, proper} ⟶ Spaces'_{fp, flat, proper} × Spaces'_{fp, flat, proper}
```

is representable by algebraic spaces, assuming Stacks 0D01 (`hilb`) and that the isomorphism
presheaf of the fibre of the stack over a scheme `U` is algebraic whenever the isomorphism functors
`Isom_U(Z, X)` of finitely presented, flat and proper families over `U` are (`hcmp`). -/
@[stacks 0D1F "the diagonal is representable by algebraic spaces"]
theorem hasRepresentableDiagonal_properFlatSpacesStack (hilb : HasHilbertModels B S hS)
    (hcmp : HasAlgebraicIsomFunctors B S hS →
      Stack.IsAlgebraicSpaceIsomPresheaf B S hS (properFlatSpacesStack B S hS)) :
    Stack.HasRepresentableDiagonal B S hS (properFlatSpacesStack B S hS) :=
  (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
    (properFlatSpacesStack B S hS)).2 (hcmp (hasAlgebraicIsomFunctors B S hS hilb))

end Diagonal

end AlgebraicGeometry.Space

end
