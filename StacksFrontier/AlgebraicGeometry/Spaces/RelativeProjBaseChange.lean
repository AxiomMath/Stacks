module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruples

/-!
# Base change of the relative Proj of an algebraic space

Let `S` be a scheme, let `g : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `𝒜` be
a quasi-coherent graded `𝒪_X`-algebra.  Stacks 085C gives a canonical isomorphism
`r : Proj_{X'}(g^*𝒜) ⟶ X' ×_X Proj_X(𝒜)`, together with an isomorphism `θ` identifying the
twists of the two relative Projs.  The source proves the first assertion by exhibiting `r` on
the functor of quadruples of Tag 084A: writing `F` for that functor and `F'` for the one built
from `g^*𝒜` on `X'`, it constructs a bijection `F'(T) ⟶ X'(T) ×_{X(T)} F(T)` for every test
object `T`, sending a quadruple `(d, f' : T → X', ℒ, ψ)` for `F'` to the pair
`(f', (d, g ∘ f', ℒ, ψ))` and the pair `(f', (d, f, ℒ, ψ))` back to `(d, f', ℒ, ψ)`.

This file constructs that bijection.

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraPoints.comap` is `g^*𝒜` as a restriction datum on `X'`:
  its value at a `T`-point `f'` of `X'` is the value of `𝒜`'s datum at `g ∘ f'`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.fibre` is the fibre of `F(T)` over a `T`-point
  of `X`, the union over `d ≥ 1` of the quadruples of degree `d` over that point.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.baseChangeEquiv` is **Stacks 085C**: the
  bijection `F'(T) ≃ X'(T) ×_{X(T)} F(T)`, for every test object `T`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.baseChangeEquiv_mk` and
  `GradedAlgebraPoints.F.baseChangeEquiv_symm_mk` compute the bijection and its inverse on
  quadruples: they are the two maps the source writes down.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.baseChangeEquiv_fst` says the bijection is
  compatible with the two morphisms to `X'`, so it is a bijection over `X'`.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.laurentUnit` inhabits the restriction datum for
  every algebraic space, so none of the above is vacuous.

## Implementation notes

**The source's identification is an equality here.**  The step `(g ∘ f')^*𝒜^{(d)} =
(f')^*(g^*𝒜)^{(d)}` that makes the map of the source well defined holds definitionally: the
restriction of `𝒜` to the scheme points of `X` is a datum, as it is for Tag 084A, and the datum
attached to `g^*𝒜` is by definition the one of `𝒜` reindexed along composition with `g`.  So no
transport of a quadruple along an isomorphism of graded algebras is needed, and
`GradedAlgebraPoints.comap_algebra` is a `rfl`.  A later statement about `g^*𝒜` should take the
datum this way rather than reprove the identification as a comparison isomorphism.

**The fibre product is the fibre product of sets.**  `X'(T) ×_{X(T)} F(T)` is spelled as the
subtype of `X'(T) × F(T)` on which the morphism `F → X` of Tag 084A — which is
`GradedAlgebraPoints.F.point` — agrees with composition of the `X'`-point with `g`.  A `T`-point
of an algebraic space is a morphism `yoneda.obj T ⟶ X`, which is the library's spelling
throughout `Spaces/`, and for a sheaf `X` it is the same thing as an element of `X(T)`.

**The one cast.**  The two components of a point of `F(T)` are a `T`-point of `X` and a class of
quadruples over it, so the inverse map has to move a class of quadruples over `f` to one over
`g ∘ f'` along the equation `f = g ∘ f'` carried by a point of the fibre product.  That is
`GradedAlgebraPoints.F.mk_cast`, which says the transport changes nothing in `F(T)`.

## Not done here

* **The isomorphism `θ` of the twists is not stated.**  The source omits its proof, and the
  twists `⨁_{d ∈ ℤ} 𝒪_{Proj_X(𝒜)}(d)` of the relative Proj of an algebraic space — Tag 085A —
  are not constructed in this library.
* **The isomorphism is of the values of the functors, not of algebraic spaces.**  Tag 084A gives
  `F(T)` for each test object `T` and not the functor `F`, the pullback of a quadruple along a
  morphism of test objects being unavailable, so there is no functor to be an isomorphism of and
  no representing algebraic space to transport the bijection to.  What the source's proof
  constructs is exactly the family of bijections built here; deducing from it the isomorphism of
  algebraic spaces needs the representability of `F`, which is Tag 084B and is not proved here.

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The restriction of `g^*𝒜` to the scheme points of `X'`.**

For a morphism `g : X' ⟶ X` of algebraic spaces over `S`, the restriction datum of Tag 084A for
the pulled-back algebra: the graded algebra at a `T`-point `f'` of `X'` is the one of `𝒜` at the
`T`-point `g ∘ f'` of `X`, which is the source's `(f')^*(g^*𝒜) = (g ∘ f')^*𝒜`. -/
def GradedAlgebraPoints.comap (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X) :
    GradedAlgebraPoints B S hS X' where
  algebra T f := r.algebra T (f ≫ g)

namespace GradedAlgebraPoints

/-- **The restriction datum of Tag 084A is inhabited, for every algebraic space.** The Laurent
algebra of the structure sheaf at every scheme point of `X`, which makes nothing below vacuous:
the datum the bijection is stated for is data, not a property, and it always exists. -/
def laurentUnit (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : GradedAlgebraPoints B S hS X where
  algebra T _ :=
    letI Z := (BigFppfOver.toScheme B S hS).obj T
    letI : Stacks.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf (isSheafStruct Z)
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          Z.toRingedSpace.presheaf (isSheafStruct Z))) :=
      Stacks.SheafOfModules.isInvertible_unit _ _
    laurent (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      Z.toRingedSpace.presheaf (isSheafStruct Z)))

/-- The algebra of `g^*𝒜` at a point `f'` of `X'` is the algebra of `𝒜` at `g ∘ f'`. -/
@[simp] theorem comap_algebra (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    (r.comap g).algebra T f = r.algebra T (f ≫ g) :=
  rfl

/-- **The fibre of `F(T)` over a `T`-point of `X`.** The union over `d ≥ 1` of the quadruples of
degree `d` over that point, modulo strict equivalence inside a degree and the equivalence of Tag
01NW across degrees.  A point of `F(T)` is a `T`-point of `X` together with a point of its
fibre. -/
def F.fibre (r : GradedAlgebraPoints B S hS X) (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X) : Type (u + 1) :=
  Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (A := r.algebra T f))

/-- The fibre of `F'(T)` over a `T`-point `f'` of `X'` is the fibre of `F(T)` over `g ∘ f'`. -/
theorem F.fibre_comap (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    F.fibre (r.comap g) T f = F.fibre r T (f ≫ g) :=
  rfl

/-- Moving a point of a fibre of `F(T)` along an equality of the `T`-points of `X` it lies over
changes nothing in `F(T)`. -/
theorem F.mk_cast (r : GradedAlgebraPoints B S hS X) (T : BigFppfOver B S hS)
    {f f' : yoneda.obj T ⟶ X} (h : f = f') (q : F.fibre r T f) :
    (⟨f', cast (congrArg (F.fibre r T) h) q⟩ : r.F T) = ⟨f, q⟩ := by
  cases h
  rfl

/-- **Stacks 085C.** The canonical isomorphism `r : Proj_{X'}(g^*𝒜) ⟶ X' ×_X Proj_X(𝒜)`, on the
functor of quadruples: for every test object `T` a bijection `F'(T) ≃ X'(T) ×_{X(T)} F(T)`,
where `F` is the functor of Tag 084A of `𝒜` on `X` and `F'` the one of `g^*𝒜` on `X'`.

A quadruple `(d, f' : T → X', ℒ, ψ)` for `F'` goes to the pair `(f', (d, g ∘ f', ℒ, ψ))`, and a
pair `(f', (d, f, ℒ, ψ))` goes back to `(d, f', ℒ, ψ)`; the two are mutually inverse. -/
@[stacks 085C "the canonical isomorphism r, as the bijection F'(T) ≃ X'(T) ×_{X(T)} F(T) of the \
proof, for every test object; the isomorphism theta of the twists is not stated"]
def F.baseChangeEquiv (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) :
    (r.comap g).F T ≃ {p : (yoneda.obj T ⟶ X') × r.F T // F.point r p.2 = p.1 ≫ g} where
  toFun ξ := ⟨(ξ.1, ⟨ξ.1 ≫ g, ξ.2⟩), rfl⟩
  invFun w := ⟨w.1.1, cast (congrArg (F.fibre r T) w.2) w.1.2.2⟩
  left_inv _ := rfl
  right_inv w := Subtype.ext (Prod.ext rfl (F.mk_cast r T w.2 w.1.2.2))

/-- **Stacks 085C, the map `r` on a quadruple.** A quadruple `(d, f', ℒ, ψ)` of positive degree
for `g^*𝒜` goes to the `X'`-point `f'` together with the quadruple `(d, g ∘ f', ℒ, ψ)`
for `𝒜`. -/
@[stacks 085C "the map r sends a quadruple (d, f', L, psi) to the pair (f', (d, g f', L, psi))"]
theorem F.baseChangeEquiv_mk (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') {d : ℤ} (hd : 0 < d)
    (P : (r.comap g).Quadruples T f d) :
    F.baseChangeEquiv r g T (F.mk (r.comap g) f hd P) =
      ⟨(f, F.mk r (f ≫ g) hd P), rfl⟩ :=
  rfl

/-- **Stacks 085C, the inverse of `r`.** The `X'`-point `f'` together with a quadruple
`(d, g ∘ f', ℒ, ψ)` for `𝒜` of positive degree goes back to the quadruple `(d, f', ℒ, ψ)`
for `g^*𝒜`. -/
@[stacks 085C "the inverse of r sends (f', (d, g f', L, psi)) to the quadruple (d, f', L, psi)"]
theorem F.baseChangeEquiv_symm_mk (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') {d : ℤ} (hd : 0 < d)
    (P : (r.comap g).Quadruples T f d) :
    (F.baseChangeEquiv r g T).symm ⟨(f, F.mk r (f ≫ g) hd P), rfl⟩ =
      F.mk (r.comap g) f hd P :=
  rfl

/-- **The bijection is a bijection over `X'`.** The `X'`-point underlying the image of a point
of `F'(T)` is the `X'`-point that point lies over, so the bijection is compatible with the
morphism `F' → X'` of Tag 084A and the first projection of the fibre product. -/
theorem F.baseChangeEquiv_fst (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (ξ : (r.comap g).F T) :
    (F.baseChangeEquiv r g T ξ).1.1 = F.point (r.comap g) ξ :=
  rfl

/-- **The bijection is compatible with the morphism to `X`.** The `X`-point underlying the
second component of the image of a point of `F'(T)` is `g` after the `X'`-point it lies over. -/
theorem F.point_baseChangeEquiv (r : GradedAlgebraPoints B S hS X) (g : X' ⟶ X)
    (T : BigFppfOver B S hS) (ξ : (r.comap g).F T) :
    F.point r (F.baseChangeEquiv r g T ξ).1.2 = F.point (r.comap g) ξ ≫ g :=
  rfl

end GradedAlgebraPoints

end AlgebraicGeometry.Space

end
