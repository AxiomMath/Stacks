module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# The copower of a module by a type

For a ring `R` and an `R`-module `M`, the *copower* functor `ModuleCat.copower M` carries a type
`E` to the direct sum `⨁_{e ∈ E} M` of copies of `M`, realized as the finitely supported
functions `E →₀ M`. It is the left adjoint of the functor of morphisms out of `M`.

The point of the copower, against `ModuleCat.free R`, is the universe of the ring.
`ModuleCat.free R : Type r ⥤ ModuleCat.{r} R` carries the ring and the module in one universe,
and so a statement proved through it holds only for a ring in the module universe. The copower
`ModuleCat.copower M : Type w ⥤ ModuleCat.{w} R` for `M : ModuleCat.{w} R` leaves the universe
`r` of `R` free: `E →₀ M` is a `Type w` whenever `E` and `M` are, and the morphisms out of `M`
into a module in `ModuleCat.{w} R` form a `Type w` as well, which is what makes the adjunction
available. At `M = ModuleCat.of R (ULift.{w} R)`, the free module of rank one,
`ModuleCat.copower M` is the free module functor with the ring universe released.

## Main definitions

* `ModuleCat.copower`: the functor `E ↦ (E →₀ M)`.
* `ModuleCat.copowerAdj`: its adjunction with the functor of morphisms out of `M`.

## Main results

* `ModuleCat.moduleFinite_copower_obj`: the copower of a finite module by a finite type is a
  finite module.
* The instance `ModuleCat.moduleFree_copower_obj`: the copower of a free module by any type is
  free, hence projective by Mathlib's instance `Module.Projective.of_free`.

## Implementation notes

The adjunction is `Finsupp.lsum` over `ℕ`, not over `R`: `Finsupp.lsum S` asks for
`SMulCommClass R S N`, which for `S = R` is commutativity of `R`, while for `S = ℕ` it is
automatic. Only the underlying `R`-semilinear map matters here, and that does not depend on `S`.

This mirrors `AddCommGrpCat.copower`, the copower of an abelian group.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w r

namespace ModuleCat

variable {R : Type r} [Ring R]

/-- **The copower of a module by a type**: the functor carrying a type `E` to the direct sum
`⨁_{e ∈ E} M` of copies of `M`, realized as the finitely supported functions `E →₀ M`.

At `M = ModuleCat.of R (ULift.{w} R)` this is the free module functor, with the universe of the
ring free where `ModuleCat.free R` ties it to the module universe. -/
public def copower (M : ModuleCat.{w} R) : Type w ⥤ ModuleCat.{w} R where
  obj E := of R (E →₀ M)
  map f := ofHom (Finsupp.lmapDomain M R f)
  map_id E := by ext x; simp [Finsupp.lmapDomain]
  map_comp f g := by ext x; simp [Finsupp.lmapDomain]

/-- The inclusion of the summand of `ModuleCat.copower M` at an index `e`. -/
public def copowerMk {M : ModuleCat.{w} R} {E : Type w} (e : E) : M ⟶ (copower M).obj E :=
  ofHom (Finsupp.lsingle e)

/-- The morphism out of `ModuleCat.copower M` at `E` determined by a family, indexed by `E`, of
morphisms out of `M`. -/
public def copowerDesc {M : ModuleCat.{w} R} {E : Type w} {A : ModuleCat.{w} R}
    (f : E → (M ⟶ A)) : (copower M).obj E ⟶ A :=
  ofHom (Finsupp.lsum ℕ fun e => (f e).hom)

/-- The morphism `ModuleCat.copowerDesc f` restricts to `f e` on the summand at `e`. -/
@[simp]
public theorem copowerMk_comp_desc {M : ModuleCat.{w} R} {E : Type w} {A : ModuleCat.{w} R}
    (f : E → (M ⟶ A)) (e : E) : copowerMk e ≫ copowerDesc f = f e := by
  ext m
  change Finsupp.lsum ℕ (fun e => (f e).hom) (Finsupp.single e m) = _
  exact Finsupp.lsum_single _ _ _ _

/-- The map of `ModuleCat.copower M` along `f` carries the summand at `e` to the summand at
`f e`. -/
@[simp]
public theorem copowerMk_comp_map {M : ModuleCat.{w} R} {E E' : Type w} (f : E ⟶ E') (e : E) :
    copowerMk e ≫ (copower M).map f = copowerMk (f e) := by
  ext m
  change Finsupp.mapDomain f (Finsupp.single e m) = Finsupp.single (f e) m
  exact Finsupp.mapDomain_single

/-- Two morphisms out of `ModuleCat.copower M` at `E` agreeing on every summand agree. -/
public theorem copower_hom_ext {M : ModuleCat.{w} R} {E : Type w} {A : ModuleCat.{w} R}
    {f g : (copower M).obj E ⟶ A} (h : ∀ e : E, copowerMk e ≫ f = copowerMk e ≫ g) : f = g := by
  refine hom_ext (Finsupp.lhom_ext' fun e => ?_)
  exact congrArg Hom.hom (h e)

/-- **Morphisms out of the copower of `M` by `E` are families of morphisms out of `M` indexed by
`E`.** -/
public def copowerHomEquiv (M : ModuleCat.{w} R) (E : Type w) (A : ModuleCat.{w} R) :
    ((copower M).obj E ⟶ A) ≃ (E ⟶ (CategoryTheory.coyoneda.obj (op M)).obj A) where
  toFun φ := ↾fun e => (copowerMk e ≫ φ : M ⟶ A)
  invFun ψ := copowerDesc fun e => (ψ e : M ⟶ A)
  left_inv _ := copower_hom_ext fun e => copowerMk_comp_desc _ e
  right_inv _ := by ext e; exact copowerMk_comp_desc _ e

/-- The inverse of `ModuleCat.copowerHomEquiv` sends a family of morphisms out of `M` to the
morphism `ModuleCat.copowerDesc` it determines. -/
@[simp]
public theorem copowerHomEquiv_symm_apply (M : ModuleCat.{w} R) (E : Type w) (A : ModuleCat.{w} R)
    (ψ : E ⟶ (CategoryTheory.coyoneda.obj (op M)).obj A) :
    (copowerHomEquiv M E A).symm ψ = copowerDesc (fun e => (ψ e : M ⟶ A)) := rfl

/-- **The copower by `M` is left adjoint to the functor of morphisms out of `M`.** The universe
of the ring plays no part: both functors are between `Type w` and `ModuleCat.{w} R`. -/
public def copowerAdj (M : ModuleCat.{w} R) :
    copower M ⊣ CategoryTheory.coyoneda.obj (op M) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := copowerHomEquiv M
      homEquiv_naturality_left_symm := by
        intro E E' A f g
        refine copower_hom_ext fun e => ?_
        rw [copowerHomEquiv_symm_apply, copowerHomEquiv_symm_apply, copowerMk_comp_desc,
          ← Category.assoc, copowerMk_comp_map, copowerMk_comp_desc]
        rfl }

/-- The functor of morphisms out of a module is a right adjoint, the copower by that module
being its left adjoint. -/
public theorem coyonedaObj_isRightAdjoint (M : ModuleCat.{w} R) :
    (CategoryTheory.coyoneda.obj (op M)).IsRightAdjoint :=
  (copowerAdj M).isRightAdjoint

/-- The copower of a free module by any type is free, hence projective. -/
public instance moduleFree_copower_obj (M : ModuleCat.{w} R) [Module.Free R M] (E : Type w) :
    Module.Free R ((copower M).obj E) :=
  inferInstanceAs (Module.Free R (E →₀ (M : Type w)))

/-- The copower of a finite module by a finite type is a finite module. -/
public theorem moduleFinite_copower_obj (M : ModuleCat.{w} R) [Module.Finite R M] (E : Type w)
    [Finite E] : Module.Finite R ((copower M).obj E) :=
  inferInstanceAs (Module.Finite R (E →₀ (M : Type w)))

end ModuleCat

end
