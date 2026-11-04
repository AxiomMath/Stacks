module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor

/-!
# `F_d` and `F` as functors over the base

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN). Section 01NS attaches to a
test scheme `T` the set `F_d(T)` of strict equivalence classes of quadruples
`(d, f : T → S, L, ψ)`, and the display 01NX the union `F(T) = ⋃_{d ≥ 1} F_d(T)`. Both sets are
**fibred over the morphisms `T ⟶ S`**: the morphism `f` is part of a quadruple, and a strict
equivalence relates only quadruples over the same `f`. This file records that fibration in the
two shapes the downstream statements use.

* The projection to the functor of points of the base, as a **natural transformation**
  `F_d ⟹ h_S` and `F ⟹ h_S`. This is what "`F_d` is representable by a scheme *over* `S`"
  (Tag 01NV) compares against, and it is what has to be in place before the fibre product
  `h_{S'} ×_{h_S} F_d` of Tag 01NT can be formed at all.
* The **fibre over a fixed structure morphism**, assembled into a functor on the category of
  schemes over `S`. The value of that functor on an object `f : T ⟶ S` of `Sch/S` is the set of
  strict equivalence classes of quadruples over `f` itself, with no morphism to `S` recorded
  alongside, and its action on a morphism of `Sch/S` is the pullback of a quadruple.

Everything here is for an **arbitrary base scheme `S`**: no affineness, no chart, no cover. The
degree `d` is an arbitrary integer, as in `...RelativeProjQcohSheaf.Quadruple`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.toBase`: **the projection `F_d ⟹ h_S`**,
  the natural transformation recording the morphism to the base of a class in `F_d(T)`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.toBase`: the same for the union `F` of the
  display 01NX.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.overFunctor`: **the functor
  `F_d : (Sch/S)^{opp} ⟶ Sets`**, the fibre of `F_d` over the structure morphism.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.overFunctorObjEquiv`: **the value of
  `Fd.overFunctor` on `f : T ⟶ S` is the set of strict equivalence classes of quadruples over
  `f`**, and the equivalence is the identity on the underlying quotient.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.overFunctorObjEquiv_map`: under that
  identification the action of `Fd.overFunctor` on a morphism of `Sch/S` is the pullback of a
  quadruple, read in the fibre over the new structure morphism.

## Implementation notes

The value of `Fd.overFunctor` is written as the **subtype** of `F_d(T)` cut out by the equation
`ξ.1 = f`, rather than as `Quotient (Quadruple.setoid f 𝒜 d)` directly. The two are the same set
— `Fd.overFunctorObjEquiv` — but with the subtype the action on a morphism of `Sch/S` is the
pullback of a quadruple followed by a *proof*, so that the two functor laws are
`Fd.pullback_id` and `Fd.pullback_comp` with a `Subtype.ext` in front. Written the other way the
action has to transport a quotient along the equality `g ≫ f = f'` of morphisms of schemes that
`CategoryTheory.Over.w` supplies, and the functor laws then need the coherence of that transport
rather than the two laws already proved.

Both natural transformations land in `yoneda.obj S ⋙ CategoryTheory.uliftFunctor`, not in
`yoneda.obj S`: the sets `F_d(T)` live in `Type (u + 1)`, a quadruple recording a sheaf of
modules, while `Hom(T, S)` lives in `Type u`. The lift is the identity on elements
(`Fd.toBase_app_down`), so nothing is hidden in it.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)

/-! ### The projection to the functor of points of the base -/

/-- **Stacks Project, Section 01NS: the projection `F_d ⟹ h_S`.** A point of `F_d(T)` is the
strict equivalence class of a quadruple `(d, f : T → S, L, ψ)`, and this is the natural
transformation sending it to the morphism `f` it records.

Naturality is the computation `Fd.pullback_fst` of the morphism to the base of a pulled-back
class: it is the composite of the morphism of test schemes with the old one, which is exactly the
action of `h_S` on a morphism. -/
@[stacks 01NS "the projection of F_d to the functor of points of the base, as a natural \
transformation F_d ⟹ h_S: a class in F_d(T) records a morphism T ⟶ S and the identification is \
natural in the test scheme. This is the structure that makes `representable by a scheme over S` \
(Tag 01NV) and the fibre product h_{S'} ×_{h_S} F_d (Tag 01NT) statable; neither of those is \
proved here"]
def Fd.toBase : Fd.functor A d ⟶ yoneda.obj S ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom fun ξ => ULift.up ξ.1
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun ξ => by
    exact congrArg ULift.up (Fd.pullback_fst φ.unop ξ))

/-- The component of `Fd.toBase` at `T` sends a class in `F_d(T)` to its recorded morphism
`T ⟶ S`. -/
@[simp] theorem Fd.toBase_app_down (T : Scheme.{u}ᵒᵖ) (ξ : Fd A d T.unop) :
    ((Fd.toBase A d).app T ξ).down = ξ.1 := rfl

/-- **Stacks Project, display 01NX: the projection `F ⟹ h_S`.** A point of `F(T)` is the class of
a quadruple of positive degree, and this is the natural transformation sending it to the morphism
to the base that the quadruple records. -/
def F.toBase : F.functor A ⟶ yoneda.obj S ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom fun ξ => ULift.up ξ.1
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun ξ => by
    exact congrArg ULift.up (F.pullback_fst φ.unop ξ))

/-- The component of `F.toBase` at `T` sends a class in `F(T)` to its recorded morphism
`T ⟶ S`. -/
@[simp] theorem F.toBase_app_down (T : Scheme.{u}ᵒᵖ) (ξ : F A T.unop) :
    ((F.toBase A).app T ξ).down = ξ.1 := rfl

/-! ### The fibre over a fixed structure morphism -/

/-- The fibre of `F_d(T)` over a fixed structure morphism `f : T ⟶ S`: the classes in `F_d(T)`
whose recorded morphism to the base is `f`. -/
abbrev Fd.over (X : Over S) : Type (u + 1) :=
  {ξ : Fd A d X.left // ξ.1 = X.hom}

/-- **Stacks Project, Section 01NS: the functor `F_d : (Sch/S)^{opp} ⟶ Sets`.** On an object
`f : T ⟶ S` of the category of schemes over `S` its value is the fibre of `F_d(T)` over `f`,
that is, the set of strict equivalence classes of quadruples `(d, f, L, ψ)` with that structure
morphism; on a morphism of `Sch/S` it is the pullback of a quadruple, which lands in the fibre
over the new structure morphism because the morphism to the base of a pulled-back class is the
composite.

This is the form of `F_d` the source's phrase "a functor on schemes over `S`" refers to; the
form fibred over `Hom(-, S)` on all of `Sch` is
`...RelativeProjQcohSheaf.Fd.functor` together with the projection `Fd.toBase`. -/
@[stacks 01NS "the functor F_d on the category of schemes OVER S, for an arbitrary base scheme: \
on an object f : T ⟶ S the set of strict equivalence classes of quadruples (d, f, L, psi) with \
that structure morphism, on a morphism of Sch/S the pullback of a quadruple. The two functor \
laws are Fd.pullback_id and Fd.pullback_comp. Representability of F_d is Tag 01NV and is not \
proved here"]
def Fd.overFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj X := Fd.over A d X.unop
  map {X Y} φ := TypeCat.ofHom fun ξ =>
    (⟨Fd.pullback φ.unop.left ξ.1, by
      rw [Fd.pullback_fst, ξ.2]
      exact Over.w φ.unop⟩ : Fd.over A d Y.unop)
  map_id _ := TypeCat.homEquiv.injective (funext fun ξ =>
    Subtype.ext (Fd.pullback_id ξ.1))
  map_comp φ χ := TypeCat.homEquiv.injective (funext fun ξ =>
    Subtype.ext (Fd.pullback_comp φ.unop.left χ.unop.left ξ.1))

/-- The value of `Fd.overFunctor` on an object `f : T ⟶ S` of `Sch/S` is the fibre of `F_d(T)`
over `f`. -/
@[simp] theorem Fd.overFunctor_obj (X : (Over S)ᵒᵖ) :
    (Fd.overFunctor A d).obj X = Fd.over A d X.unop := rfl

/-- An element of a dependent sum whose index is known is the pair of that index with its own
second component, transported along the equality of indices. -/
theorem sigma_mk_eq_of_fst_eq {α : Type*} {β : α → Type*} {g : α} (ξ : Σ a, β a)
    (h : ξ.1 = g) : (⟨g, h ▸ ξ.2⟩ : Σ a, β a) = ξ := by
  obtain ⟨a, b⟩ := ξ
  subst h
  rfl

/-- The value of `Fd.overFunctor` on an object `f : T ⟶ S` of `Sch/S` **is** the set of strict
equivalence classes of quadruples over `f`: the fibre of a dependent sum over a fixed value of
the index is the summand at that index. -/
def Fd.overFunctorObjEquiv (X : Over S) :
    Fd.over A d X ≃ Quotient (Quadruple.setoid X.hom A d) where
  toFun ξ := ξ.2 ▸ ξ.1.2
  invFun q := ⟨⟨X.hom, q⟩, rfl⟩
  left_inv ξ := Subtype.ext (sigma_mk_eq_of_fst_eq ξ.1 ξ.2)
  right_inv _ := rfl

/-- The inverse of `Fd.overFunctorObjEquiv` sends a class `q` of quadruples over `f : T ⟶ S` to
the point of `F_d(T)` given by the pair `(f, q)`. -/
@[simp] theorem Fd.overFunctorObjEquiv_symm_apply (X : Over S)
    (q : Quotient (Quadruple.setoid X.hom A d)) :
    ((Fd.overFunctorObjEquiv A d X).symm q).1 = ⟨X.hom, q⟩ := rfl

/-- The class of a quadruple over the structure morphism, as a point of the fibre. -/
theorem Fd.overFunctorObjEquiv_symm_mk (X : Over S) (P : Quadruple X.hom A d) :
    ((Fd.overFunctorObjEquiv A d X).symm (Quotient.mk _ P)).1 = Fd.mk X.hom P := rfl

/-- **The action of `Fd.overFunctor` on a morphism of `Sch/S` is the pullback of a quadruple.**
Read through the identification of the fibres with the sets of classes, the image of the class of
a quadruple `P` over `f : T ⟶ S` along a morphism `φ` of `Sch/S` with underlying morphism
`g : T' ⟶ T` is the class of `P.pullback g`, a quadruple over `g ≫ f = f'`. -/
theorem Fd.overFunctorObjEquiv_map {X Y : Over S} (φ : op X ⟶ op Y) (P : Quadruple X.hom A d) :
    ((Fd.overFunctor A d).map φ ((Fd.overFunctorObjEquiv A d X).symm (Quotient.mk _ P))
        : Fd.over A d Y).1 =
      Fd.mk (φ.unop.left ≫ X.hom) (P.pullback φ.unop.left) :=
  rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
