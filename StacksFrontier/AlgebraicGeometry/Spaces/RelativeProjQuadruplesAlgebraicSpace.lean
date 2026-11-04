module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointsAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesSheafLimit

/-!
# The functor of quadruples is an algebraic space

In Situation 0849 let `X` be an algebraic space over a scheme `S`, `𝒜` a quasi-coherent graded
`𝒪_X`-algebra and `F` the functor of quadruples of Stacks 084A.  Stacks 084B asserts that `F` is
an algebraic space, that for every morphism `g : Z ⟶ X` from a scheme there is a canonical
isomorphism `Proj_Z(g^*𝒜) = Z ×_X F`, and that it is compatible with further base change.

This file deduces the three assertions from the restriction datum of the functor of quadruples,
taken as an argument: given

* the restrictions `f^*𝒜` of the graded algebra to the scheme points `f` of `X`, as graded algebra
  data `Â` of Situation 01NN on the schemes of the test objects,
* a restriction datum `ρ` over them (`AlgebraicGeometry.Space.GradedAlgebraRestriction`), and
* the statement `hc` that each relative Proj `Proj_T(f^*𝒜)` is a scheme of the site,

the functor `F` of Stacks 084A — on every test object the limit, over the quasi-compact test
objects over it, of the unions of the classes of quadruples — takes values in `u`-small sets
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.small_limPoint`), its structure morphism to `X`
is the base change of the relative Proj over every scheme point
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.relativeProjPoints`), and so it is an
algebraic space (`AlgebraicGeometry.Space.GradedAlgebraRestriction.isAlgebraicSpace`).

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleSpace`: **the functor `F` of
  quadruples of Stacks 084A**, with values in `Type u`: the shrinking of
  `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleFunctor`, whose value on a test object
  `T` is the limit over the quasi-compact test objects `W ⟶ T` of the unions
  `AlgebraicGeometry.Space.GradedAlgebraPoints.F` and on a quasi-compact `T` is `F(T)` itself
  (`AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleSpaceEquivF`); and
  `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleSpaceπ`, its morphism to `X`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.relativeProjFunctor`: the functor `F` of
  Stacks 084A, with values in `Type u`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.relativeProjπ`: its morphism to `X`, sending
  a quadruple `(d, f, ℒ, ψ)` to `f`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.relativeProjPoints`: the second assertion of
  Stacks 084B, as the datum `AlgebraicGeometry.Space.RelativeProjPoints`.

## Main results

For the functor of quadruples of Stacks 084A, with `X` a sheaf:

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.isPullback_projToQuadrupleSpace`: the second
  assertion, `Proj_Z(g^*𝒜) = Z ×_X F`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.isAlgebraicSpace_quadrupleSpace`: the first
  assertion.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.projToQuadrupleSpace_comp`, with
  `...isPullback_projComparison`: the third assertion.

For the auxiliary presentation `relativeProjFunctor`, which needs no sheaf condition on `X`:

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.isPullback_projHom`: **the second assertion**,
  `Proj_Z(g^*𝒜) = Z ×_X F`, as a cartesian square of presheaves.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.isAlgebraicSpace`: **the first assertion**.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.isPullback_projComparison`: **the third
  assertion**: for `h : Z' ⟶ Z` the square comparing `Proj_{Z'}((g ∘ h)^*𝒜)` with
  `Proj_Z(g^*𝒜)` is cartesian, i.e. `Proj_{Z'}((g ∘ h)^*𝒜) = Z' ×_Z Proj_Z(g^*𝒜)` compatibly
  with the isomorphisms of the second assertion.

## Implementation notes

The functor of quadruples takes values in `Type (u + 1)`, a quadruple carrying a sheaf of modules,
and the algebraic spaces of the site take values in `Type u`.  The second assertion makes its
values `u`-small — over a `T`-point of `X` they are the sections of `Proj_T(f^*𝒜) ⟶ T` — so it is
shrunk to `Type u` with `CategoryTheory.FunctorToTypes.shrink`.

The source's proof of the first assertion is the reduction `084B(2) ⟹ 084B(1)` of Stacks 02WY,
which is `AlgebraicGeometry.Space.RelativeProjPoints.isAlgebraicSpace`, and its third assertion is
pullback pasting, `AlgebraicGeometry.Space.RelativeProjPoints.isPullback_fibreComparison`; both
are applied here to the datum the second assertion produces.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)

/-! ### Smallness -/

/-- A point of `F(T)` over `f`, as a `T`-point of `Proj_T(f^*𝒜)`: the inverse of the bijection of
the second assertion at the identity of `T`. -/
def limPointToProj {T : BigFppfOver B S hS} (ξ : LimPoint ρ T) :
    Σ f : yoneda.obj T ⟶ X, (T ⟶ projObj Â f (hc T f)) :=
  ⟨ξ.point, (ρ.projEquiv ξ.point (hc T ξ.point) T).symm ⟨(𝟙 T, ξ), by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]⟩⟩

/-- The map `limPointToProj` from the points of `F(T)` to the `T`-points of the relative Proj is
injective. -/
theorem limPointToProj_injective (T : BigFppfOver B S hS) :
    Function.Injective (ρ.limPointToProj hc (T := T)) := by
  intro ξ η h
  have h1 : ∀ ζ : LimPoint ρ T, (ρ.projEquiv (ρ.limPointToProj hc ζ).1 (hc T _) T
      (ρ.limPointToProj hc ζ).2).1.2 = ζ := fun ζ =>
    congrArg (fun p => p.1.2) (Equiv.apply_symm_apply (ρ.projEquiv ζ.point (hc T ζ.point) T) _)
  rw [← h1 ξ, ← h1 η, h]

include hc in
/-- **The values of the functor of quadruples are `u`-small**: a point of `F(T)` over a `T`-point
`f` of `X` is a `T`-point of `Proj_T(f^*𝒜)`, by the second assertion. -/
theorem small_limPoint (T : BigFppfOver B S hS) : Small.{u} (LimPoint ρ T) := by
  have : Small.{u} (yoneda.obj T ⟶ X) := small_of_injective yonedaEquiv.injective
  exact small_of_injective (ρ.limPointToProj_injective hc T)

/-! ### The functor of quadruples as a presheaf of `u`-small sets -/

/-- **Stacks 084A: the functor of quadruples**, with values in `Type u`. -/
def relativeProjFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  haveI : FunctorToTypes.Small.{u} ρ.limFunctor := fun T => ρ.small_limPoint hc T.unop
  FunctorToTypes.shrink.{u} ρ.limFunctor

/-- The identification of the values of `relativeProjFunctor` with the points of the limit. -/
def relativeProjFunctorEquiv (T : BigFppfOver B S hS) :
    (ρ.relativeProjFunctor hc).obj (op T) ≃ LimPoint ρ T :=
  haveI := ρ.small_limPoint hc T
  (equivShrink.{u} (LimPoint ρ T)).symm

/-- The identification `relativeProjFunctorEquiv` carries restriction along `τ : T' ⟶ T` in
`relativeProjFunctor` to restriction of points of the limit. -/
theorem relativeProjFunctorEquiv_map {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (x : (ρ.relativeProjFunctor hc).obj (op T)) :
    ρ.relativeProjFunctorEquiv hc T' ((ρ.relativeProjFunctor hc).map τ.op x) =
      (ρ.relativeProjFunctorEquiv hc T x).restrict τ := by
  have := ρ.small_limPoint hc T
  have := ρ.small_limPoint hc T'
  exact (equivShrink _).symm_apply_apply _

/-- **The morphism `F ⟶ X` of Stacks 084A**, sending a quadruple `(d, f, ℒ, ψ)` to `f`. -/
def relativeProjπ : ρ.relativeProjFunctor hc ⟶ X where
  app T := TypeCat.ofHom fun x => yonedaEquiv (ρ.relativeProjFunctorEquiv hc T.unop x).point
  naturality T T' τ := by
    ext x
    change yonedaEquiv (ρ.relativeProjFunctorEquiv hc T'.unop
      ((ρ.relativeProjFunctor hc).map τ.unop.op x)).point = X.map τ (yonedaEquiv _)
    rw [relativeProjFunctorEquiv_map, LimPoint.restrict_point]
    exact (yonedaEquiv_naturality' _ τ).symm

/-- The morphism `relativeProjπ` sends a point of `F(T)` to the `T`-point of `X` it lies over. -/
theorem relativeProjπ_app {T : BigFppfOver B S hS} (x : (ρ.relativeProjFunctor hc).obj (op T)) :
    (ρ.relativeProjπ hc).app (op T) x = yonedaEquiv (ρ.relativeProjFunctorEquiv hc T x).point :=
  rfl

/-! ### The second assertion -/

/-- The morphism `Proj_Z(g^*𝒜) ⟶ F` of the second assertion: the point of `F` over
`Proj_Z(g^*𝒜)` corresponding to its identity, so that a `T`-point of the relative Proj is sent to
the corresponding point of `F(T)`. -/
def projToFunctor {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) :
    yoneda.obj (projObj Â g (hc Z g)) ⟶ ρ.relativeProjFunctor hc :=
  yonedaEquiv.symm ((ρ.relativeProjFunctorEquiv hc _).symm (ρ.projPoint g _ (𝟙 _)))

/-- The image of a `T`-point `s` of `Proj_Z(g^*𝒜)` under `projToFunctor` is the point
`projPoint g s` of `F(T)`. -/
theorem relativeProjFunctorEquiv_projToFunctor {Z T : BigFppfOver B S hS}
    (g : yoneda.obj Z ⟶ X) (s : T ⟶ projObj Â g (hc Z g)) :
    ρ.relativeProjFunctorEquiv hc T ((ρ.projToFunctor hc g).app (op T) s) =
      ρ.projPoint g _ s := by
  refine (ρ.relativeProjFunctorEquiv_map hc s _).trans ?_
  rw [Equiv.apply_symm_apply, ← projPoint_comp]
  rfl

/-- The composite `Proj_Z(g^*𝒜) ⟶ F ⟶ X` equals the composite of the structure morphism
`Proj_Z(g^*𝒜) ⟶ Z` with `g`. -/
theorem projToFunctor_comp_relativeProjπ {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) :
    ρ.projToFunctor hc g ≫ ρ.relativeProjπ hc = yoneda.map (projHom Â g (hc Z g)) ≫ g := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, projToFunctor, Equiv.apply_symm_apply, relativeProjπ_app,
    Equiv.apply_symm_apply]
  rfl

/-- **The second assertion of Stacks 084B: `Proj_Z(g^*𝒜) = Z ×_X F`.** For every scheme point
`g : Z ⟶ X` of `X` the square formed by the structure morphism `Proj_Z(g^*𝒜) ⟶ Z`, the morphism
`Proj_Z(g^*𝒜) ⟶ F`, the morphism `F ⟶ X` and `g` is cartesian. -/
theorem isPullback_projHom {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) :
    IsPullback (ρ.projToFunctor hc g) (yoneda.map (projHom Â g (hc Z g))) (ρ.relativeProjπ hc)
      g := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun α => α.app T) (ρ.projToFunctor_comp_relativeProjπ hc g), ?_, ?_⟩
  · rintro s s' ⟨h1, h2⟩
    apply (ρ.projEquiv g (hc Z g) T.unop).injective
    refine Subtype.ext (Prod.ext h2 ?_)
    have := congrArg (ρ.relativeProjFunctorEquiv hc T.unop) h1
    rwa [relativeProjFunctorEquiv_projToFunctor, relativeProjFunctorEquiv_projToFunctor] at this
  · intro x t hxt
    have hξ : (ρ.relativeProjFunctorEquiv hc T.unop x).point = yoneda.map t ≫ g :=
      yonedaEquiv.injective hxt
    refine ⟨ρ.projHomOf g (hc Z g) t _ hξ, ?_, ρ.projHomOf_comp_projHom g (hc Z g) t _ hξ⟩
    apply (ρ.relativeProjFunctorEquiv hc T.unop).injective
    rw [relativeProjFunctorEquiv_projToFunctor]
    exact ρ.projPoint_projHomOf g (hc Z g) t _ hξ

/-- **The relative Proj of the restrictions `f^*𝒜` as the datum
`AlgebraicGeometry.Space.RelativeProjPoints`**, for a morphism `π : F ⟶ X` and, over every scheme
point `f : T ⟶ X`, a morphism `Proj_T(f^*𝒜) ⟶ F` making the square with the structure morphism
`Proj_T(f^*𝒜) ⟶ T`, `π` and `f` cartesian: the fibre over `f` is `Proj_T(f^*𝒜)` itself, as the
object `projObj` of the site. -/
def relativeProjPointsOfIsPullback {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : F ⟶ X}
    (φ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      yoneda.obj (projObj Â f (hc T f)) ⟶ F)
    (hφ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      IsPullback (φ T f) (yoneda.map (projHom Â f (hc T f))) π f) :
    RelativeProjPoints B S hS π where
  algebra := Â
  fibre T f := projObj Â f (hc T f)
  fibreIso _ _ := Iso.refl _
  fibreHom T f := projHom Â f (hc T f)
  fibreHom_comp _ _ := (Category.id_comp _).symm
  fibreToSpace := φ
  isPullback := hφ

/-- **The second assertion of Stacks 084B as the datum
`AlgebraicGeometry.Space.RelativeProjPoints`**: over every scheme point `f : T ⟶ X` the relative
Proj `Proj_T(f^*𝒜)` of the restricted algebra is the base change `T ×_X F`. -/
def relativeProjPoints : RelativeProjPoints B S hS (ρ.relativeProjπ hc) :=
  relativeProjPointsOfIsPullback hc (fun _ f => ρ.projToFunctor hc f)
    (fun _ f => ρ.isPullback_projHom hc f)

/-- The graded algebra of the second assertion at a scheme point `f` is the family's `Â T f`. -/
@[simp] theorem relativeProjPoints_algebra (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (ρ.relativeProjPoints hc).algebra T f = Â T f :=
  rfl

/-! ### The first and third assertions -/

/-- **The first assertion of Stacks 084B: the functor of quadruples is an algebraic space.** -/
theorem isAlgebraicSpace (hX : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpace B S hS (ρ.relativeProjFunctor hc) :=
  (ρ.relativeProjPoints hc).isAlgebraicSpace hX

/-- The comparison morphism `Proj_{Z'}((g ∘ h)^*𝒜) ⟶ Proj_Z(g^*𝒜)` over a morphism `h : Z' ⟶ Z`
of test objects, induced by the cartesian square of the second assertion over `g`. -/
def projComparison {Z Z' : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (h : Z' ⟶ Z) :
    projObj Â (yoneda.map h ≫ g) (hc Z' _) ⟶ projObj Â g (hc Z g) :=
  (ρ.relativeProjPoints hc).fibreComparison Z g h

/-- **The third assertion of Stacks 084B: compatibility with further base change.** For a
morphism `h : Z' ⟶ Z` of test objects the comparison morphism exhibits
`Proj_{Z'}((g ∘ h)^*𝒜)` as `Z' ×_Z Proj_Z(g^*𝒜)`, and it lies over the morphisms to `F` of the
second assertion. -/
theorem isPullback_projComparison {Z Z' : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (h : Z' ⟶ Z) :
    IsPullback (ρ.projComparison hc g h) (projHom Â (yoneda.map h ≫ g) (hc Z' _))
      (projHom Â g (hc Z g)) h ∧
      yoneda.map (ρ.projComparison hc g h) ≫ ρ.projToFunctor hc g =
        ρ.projToFunctor hc (yoneda.map h ≫ g) :=
  ⟨(ρ.relativeProjPoints hc).isPullback_fibreComparison_site Z g h,
    (ρ.relativeProjPoints hc).map_fibreComparison_comp_fibreToSpace Z g h⟩

/-! ### The three assertions for the functor of quadruples of Stacks 084A -/

section Quadruple

variable (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)

include hc hX in
/-- **The values of the functor of quadruples of Stacks 084A are `u`-small.** -/
theorem small_quadrupleFunctor (T : BigFppfOver B S hS) :
    Small.{u} (SiteQcExtension ρ.functor T) := by
  have := ρ.small_limPoint hc T
  exact small_of_injective (ρ.limPointEquiv hX T).symm.injective

/-- **Stacks 084A: the functor of quadruples**, `ρ.quadrupleFunctor`, with values in `Type u`:
on every test object `T` the limit over the quasi-compact test objects `W ⟶ T` of the unions
`F(W)` of the classes of quadruples, and on a quasi-compact `T` the union `F(T)` itself
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleSpaceEquivF`). -/
def quadrupleSpace : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  haveI : FunctorToTypes.Small.{u} ρ.quadrupleFunctor := fun T =>
    ρ.small_quadrupleFunctor hc hX T.unop
  FunctorToTypes.shrink.{u} ρ.quadrupleFunctor

/-- The values of `quadrupleSpace` are the limits of the unions of the classes of quadruples. -/
def quadrupleSpaceEquiv (T : BigFppfOver B S hS) :
    (ρ.quadrupleSpace hc hX).obj (op T) ≃ SiteQcExtension ρ.functor T :=
  haveI := ρ.small_quadrupleFunctor hc hX T
  (equivShrink.{u} (SiteQcExtension ρ.functor T)).symm

/-- **On a quasi-compact test object the value of the functor of quadruples is the union `F(T)`**
of the classes of quadruples of Stacks 084A. -/
def quadrupleSpaceEquivF (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    (ρ.quadrupleSpace hc hX).obj (op T) ≃ (GradedAlgebraPoints.ofQuasicoherentFamily Â).F T :=
  (ρ.quadrupleSpaceEquiv hc hX T).trans (SiteQcExtension.equivObj T hT)

/-- The identification `quadrupleSpaceEquiv` carries restriction along `τ : T' ⟶ T` in
`quadrupleSpace` to pullback along `τ` of points of the limit. -/
theorem quadrupleSpaceEquiv_map {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (x : (ρ.quadrupleSpace hc hX).obj (op T)) :
    ρ.quadrupleSpaceEquiv hc hX T' ((ρ.quadrupleSpace hc hX).map τ.op x) =
      (ρ.quadrupleSpaceEquiv hc hX T x).pullback τ := by
  have := ρ.small_quadrupleFunctor hc hX T
  have := ρ.small_quadrupleFunctor hc hX T'
  exact (equivShrink _).symm_apply_apply _

/-- The identification of the values of `relativeProjFunctor` with those of the functor of
quadruples. -/
def relativeProjFunctorEquivQuadruple (T : BigFppfOver B S hS) :
    (ρ.relativeProjFunctor hc).obj (op T) ≃ (ρ.quadrupleSpace hc hX).obj (op T) :=
  (ρ.relativeProjFunctorEquiv hc T).trans
    ((ρ.limPointEquiv hX T).trans (ρ.quadrupleSpaceEquiv hc hX T).symm)

/-- Under `quadrupleSpaceEquiv`, the image of a point by `relativeProjFunctorEquivQuadruple` is the
image by `limPointEquiv` of the corresponding point of the limit. -/
theorem quadrupleSpaceEquiv_relativeProjFunctorEquivQuadruple (T : BigFppfOver B S hS)
    (x : (ρ.relativeProjFunctor hc).obj (op T)) :
    ρ.quadrupleSpaceEquiv hc hX T (ρ.relativeProjFunctorEquivQuadruple hc hX T x) =
      ρ.limPointEquiv hX T (ρ.relativeProjFunctorEquiv hc T x) :=
  Equiv.apply_symm_apply _ _

/-- The identification `relativeProjFunctorEquivQuadruple` commutes with restriction along
`τ : T' ⟶ T`. -/
theorem relativeProjFunctorEquivQuadruple_map {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (x : (ρ.relativeProjFunctor hc).obj (op T)) :
    ρ.relativeProjFunctorEquivQuadruple hc hX T' ((ρ.relativeProjFunctor hc).map τ.op x) =
      (ρ.quadrupleSpace hc hX).map τ.op (ρ.relativeProjFunctorEquivQuadruple hc hX T x) := by
  apply (ρ.quadrupleSpaceEquiv hc hX T').injective
  rw [quadrupleSpaceEquiv_map, quadrupleSpaceEquiv_relativeProjFunctorEquivQuadruple,
    quadrupleSpaceEquiv_relativeProjFunctorEquivQuadruple, relativeProjFunctorEquiv_map]
  rfl

/-- The functor of quadruples is isomorphic to the presheaf `relativeProjFunctor` the second
assertion was proved for. -/
def quadrupleSpaceIso : ρ.relativeProjFunctor hc ≅ ρ.quadrupleSpace hc hX :=
  NatIso.ofComponents (fun T => (ρ.relativeProjFunctorEquivQuadruple hc hX T.unop).toIso)
    (fun {_ _} τ => by
      ext x
      exact ρ.relativeProjFunctorEquivQuadruple_map hc hX τ.unop x)

/-- **The morphism `F ⟶ X` of Stacks 084A**, sending a quadruple `(d, f, ℒ, ψ)` to `f`. -/
def quadrupleSpaceπ : ρ.quadrupleSpace hc hX ⟶ X :=
  (ρ.quadrupleSpaceIso hc hX).inv ≫ ρ.relativeProjπ hc

/-- The point of `X` a point of the functor of quadruples lies over restricts, over every
quasi-compact test object `w : W ⟶ T`, to the point the quadruple class at `w` records. -/
theorem quadrupleSpaceπ_app {T : BigFppfOver B S hS} (x : (ρ.quadrupleSpace hc hX).obj (op T))
    (W : BigFppfOver B S hS) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (w : W ⟶ T) :
    X.map w.op ((ρ.quadrupleSpaceπ hc hX).app (op T) x) =
      yonedaEquiv
        (GradedAlgebraPoints.F.point _ ((ρ.quadrupleSpaceEquiv hc hX T x).val W hW w)) := by
  obtain ⟨y, rfl⟩ := (ρ.relativeProjFunctorEquivQuadruple hc hX T).surjective x
  have hy : (ρ.quadrupleSpaceIso hc hX).inv.app (op T)
      (ρ.relativeProjFunctorEquivQuadruple hc hX T y) = y :=
    (ρ.relativeProjFunctorEquivQuadruple hc hX T).symm_apply_apply y
  change X.map w.op ((ρ.relativeProjπ hc).app (op T) ((ρ.quadrupleSpaceIso hc hX).inv.app (op T)
    (ρ.relativeProjFunctorEquivQuadruple hc hX T y))) = _
  rw [hy, quadrupleSpaceEquiv_relativeProjFunctorEquivQuadruple, relativeProjπ_app,
    yonedaEquiv_naturality]
  rfl

/-- The morphism `Proj_Z(g^*𝒜) ⟶ F` of the second assertion, into the functor of quadruples. -/
def projToQuadrupleSpace {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) :
    yoneda.obj (projObj Â g (hc Z g)) ⟶ ρ.quadrupleSpace hc hX :=
  ρ.projToFunctor hc g ≫ (ρ.quadrupleSpaceIso hc hX).hom

/-- **The second assertion of Stacks 084B: `Proj_Z(g^*𝒜) = Z ×_X F`** for the functor `F` of
quadruples of Stacks 084A and every scheme point `g : Z ⟶ X`. -/
theorem isPullback_projToQuadrupleSpace {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) :
    IsPullback (ρ.projToQuadrupleSpace hc hX g) (yoneda.map (projHom Â g (hc Z g)))
      (ρ.quadrupleSpaceπ hc hX) g :=
  (ρ.isPullback_projHom hc g).of_iso (Iso.refl _) (ρ.quadrupleSpaceIso hc hX) (Iso.refl _)
    (Iso.refl _) (by simp [projToQuadrupleSpace]) (by simp) (by simp [quadrupleSpaceπ])
    (by simp)

/-- The second assertion of Stacks 084B for the functor of quadruples, as the datum
`AlgebraicGeometry.Space.RelativeProjPoints`. -/
def quadrupleRelativeProjPoints : RelativeProjPoints B S hS (ρ.quadrupleSpaceπ hc hX) :=
  relativeProjPointsOfIsPullback hc (fun _ f => ρ.projToQuadrupleSpace hc hX f)
    (fun _ f => ρ.isPullback_projToQuadrupleSpace hc hX f)

/-- The graded algebra of the second assertion for the functor of quadruples at a scheme point `f`
is the family's `Â T f`. -/
@[simp] theorem quadrupleRelativeProjPoints_algebra (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X) : (ρ.quadrupleRelativeProjPoints hc hX).algebra T f = Â T f :=
  rfl

/-- **The first assertion of Stacks 084B: the functor of quadruples of Stacks 084A is an
algebraic space**. -/
theorem isAlgebraicSpace_quadrupleSpace (hXa : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpace B S hS (ρ.quadrupleSpace hc hXa.isSheaf) :=
  (ρ.quadrupleRelativeProjPoints hc hXa.isSheaf).isAlgebraicSpace hXa

/-- For `h : Z' ⟶ Z`, composing the comparison morphism `Proj_{Z'}((g ∘ h)^*𝒜) ⟶ Proj_Z(g^*𝒜)`
with `Proj_Z(g^*𝒜) ⟶ F` gives the morphism `Proj_{Z'}((g ∘ h)^*𝒜) ⟶ F`. -/
theorem projToQuadrupleSpace_comp {Z Z' : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (h : Z' ⟶ Z) :
    yoneda.map (ρ.projComparison hc g h) ≫ ρ.projToQuadrupleSpace hc hX g =
      ρ.projToQuadrupleSpace hc hX (yoneda.map h ≫ g) := by
  rw [projToQuadrupleSpace, projToQuadrupleSpace, ← Category.assoc,
    (ρ.isPullback_projComparison hc g h).2]

end Quadruple

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
