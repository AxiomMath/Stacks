module

public import StacksFrontier.Homology.DerivedCategory.RetractSplittingApproximation

/-!
# The iteration of [Stacks, Tag 09IN]: a tower of split lifts, coned one stage at a time

[Stacks, Tag 09IM] produces, from a perfect object `P` of `D(𝒪_U)` and a map `α : P ⟶ E|_U`, a
perfect object `R` of `D(𝒪_X)` with a map `β : R ⟶ E` such that `P` is a direct summand of
`R|_U` compatibly with `α` and `β|_U`; the proof shows moreover that
`R|_U ≅ P ⊕ P^{⊕n_1}⟦1⟧ ⊕ ⋯ ⊕ P^{⊕n_m}⟦m⟧`, so that the complement is a sum of *positive*
shifts of `P`. [Stacks, Tag 09IN] is the remark that, by repeating the construction on the
complement and taking cones, the cohomology sheaves of `R|_U` and of `P` can be made to agree
above any prescribed degree.

This file is the iteration, with no geometry in it. The degree bookkeeping happens in the derived
category `D(C)` of an abelian category; the objects whose cones have to be formed live in an
auxiliary category `D` carrying a functor `res : D ⥤ D(C)`, because the construction is only
allowed to cone morphisms that exist upstairs — downstairs they are only restrictions.

## The quantifier order

The remark asks for agreement "above any given degree", and the degree is fixed *first*: for
every `n` there is a lift depending on `n` whose restriction agrees with `P` in all degrees
`> n`. The other reading, a single lift serving every `n` at once, is false: a perfect lift is
bounded, so agreement in every degree would make `P ⟶ R|_U` an isomorphism and extend `P` to a
perfect object of `D(𝒪_X)`, which is exactly what the `F ⊕ F⟦1⟧` of [Stacks, Tag 08EI] exists to
work around. Accordingly `DerivedCategory.exists_approximatesFrom_of_splitLiftOracle` takes `n`
and returns an object depending on it.

## Why the positive shifts make it work, and what the invariant is

`H^i(P⟦j⟧) = H^{i+j}(P)`, so a shift by `j ≥ 1` carries cohomology downwards: if `H^i(P) = 0`
for `i > b` then a sum of shifts of `P` by `≥ 1` has vanishing cohomology in every degree
`> b - 1`. One application of the construction therefore already gives the remark's first
sentence, that the top cohomology sheaf of `R|_U` is that of `P`.

The iteration is driven by a *self-reproducing* invariant: an object `Y` of `D` together with an
isomorphism `res Y ≅ P ⊞ Q` and a bound `m` with `H^i(Q) = 0` for `i > m`. Feeding the
construction the complement `Q` and the inclusion `Q ⟶ res Y` produces `ρ : R ⟶ Y` with
`res R ≅ Q ⊞ Q'`, the complement `Q'` a sum of shifts of `Q` by `≥ 1` — so `H^i(Q') = 0` for
`i > m - 1` — and, crucially, with `res ρ` equal to `biprod.fst ≫ biprod.inr` in these
coordinates. The cone of `ρ`, formed upstairs, then restricts to `P ⊞ Q'⟦1⟧`: the `Q` summand
cancels, and `H^i(Q'⟦1⟧) = H^{i+1}(Q')` vanishes for `i > m - 2`. So the invariant holds again
with the bound lowered, and iterating it `k` times and then reading off
`DerivedCategory.approximatesFrom_biprod_inl_iff` gives agreement above any degree.

The *strengthened* compatibility `e.inv ≫ res ρ = biprod.fst ≫ α` — that the map to the ambient
object is, in the coordinates of the splitting, the projection followed by the given map — is
what makes the invariant reproduce itself, and it is what the proof of [Stacks, Tag 09IM]
actually supplies: the map glued over `U` by [Stacks, Tag 08DG] there is
`P ⊕ P⟦1⟧ ⟶ P ⟶ E|_U`, the projection followed by `α`. With only the weak compatibility
`biprod.inl ≫ φ = biprod.inr` the first cone is `cone(c : Q' ⟶ P)`, which is *not* split over
`P`; that is enough for one stage — it is
`DerivedCategory.approximatesFrom_cone_of_biprod_inl_comp` — but the iteration then stalls,
because coning a further morphism *into* a non-split cone can only pass to a quotient of the
cohomology already reached, never repair the degree in which `P ⟶ cone(c)` is merely
epimorphic.

## Main results

* `CategoryTheory.Limits.Biprod.exists_iso_biprod_shift_of_distTriang_fst_comp_inr`: the step, as
  pure triangulated algebra. If a morphism is `biprod.fst ≫ biprod.inr : Q ⊞ Q' ⟶ P ⊞ Q` in
  suitable coordinates, its cone is `P ⊞ Q'⟦1⟧`, by an isomorphism carrying the restriction of
  the cone map to the `P` summand to `biprod.inl`. This is
  `CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_inl_comp` at a vanishing
  component, followed by
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` on the rotation of
  the triangle of a zero morphism.
* `DerivedCategory.exists_biprod_iso_of_splitLiftOracle`: the invariant, iterated `k` times.
* `DerivedCategory.exists_approximatesFrom_of_splitLiftOracle`: **the degree clause of
  [Stacks, Tag 09IN]**, for the approximating map alone. Given the first splitting and the ability
  to repeat the construction over perfect ambient objects, for every `n` there is an object `Y` in
  the good class and a map `P ⟶ res Y` which is an isomorphism on `H^i` for every `i > n` and an
  epimorphism on `H^n`.
* `Stacks.SplitLiftTower.exists_biprod_iso_lift_of_fibre_octahedron`,
  `Stacks.SplitLiftTower.exists_fibre_invariant_succ` and
  `Stacks.SplitLiftTower.exists_fibre_invariant_base`: the *fibre device* — one stage of the
  iteration that carries the map to the ambient object along with the splitting. See the next
  section.
* `DerivedCategory.exists_hom_biprod_iso_of_fibreOracle` and
  `DerivedCategory.exists_hom_biprod_iso_isZero_homology_of_fibreOracle`: the fibre device
  iterated, and **the degree clause of [Stacks, Tag 09IN] with the map to the ambient object
  retained**: for every `n` there are `R`, a map `β : R ⟶ E`, and a splitting
  `res R ≅ P ⊞ J` with `e.inv ≫ res β = biprod.fst ≫ α` and `H^i(J) = 0` for every `i ≥ n`.

## The fibre device: how the map to the ambient object survives the cone

The iteration driven by `oracle` above carries a splitting of `P` off `res Y` and nothing else:
the object produced at each stage is the cone of a morphism `ρ : R ⟶ Y`, and a map out of that
cone extends a map out of `Y` only when its composite with `ρ` vanishes. The source's literal
recipe — "repeating the construction for the map `P^{⊕n_1}[1] ⊕ ⋯ ⟶ R|_U`" — applies 09IM with
*ambient object `E`*, which produces `ρ : R' ⟶ R` with no reason at all for `ρ ≫ β` to vanish.

The map is nevertheless recoverable, and the repair is to change the ambient object. Carry at
stage `k` the distinguished triangle `F_k ⟶ R_k ⟶ E ⟶ F_k⟦1⟧` — so `F_k` is the *fibre* of
`β_k` — together with a lift `λ_k : J_k ⟶ res F_k` of the junk inclusion, and apply 09IM with
ambient object `F_k`. The resulting `β'' : R' ⟶ F_k` is coned after composing with `F_k ⟶ R_k`,
and then `ρ ≫ β_k = β'' ≫ (F_k ⟶ R_k ⟶ E) = 0` globally and for free: two consecutive morphisms
of a distinguished triangle. The octahedral axiom applied to that factorization hands back both
the new map `β_{k+1} : cone ρ ⟶ E` and the new fibre `F_{k+1} = cone β''` at once, so the
invariant reproduces itself. The lift `λ_k` exists exactly because of the *strengthened*
compatibility: `β_k|_U` is `biprod.fst ≫ α` in the coordinates of the splitting, so the junk
inclusion kills it and `Triangle.coyoneda_exact₂` factors the inclusion through the fibre.

What made this look impossible is the single predicate `GD`: the `oracle` above requires its
ambient object to lie in the good class — perfect and supported on `T` — and the fibre of a map
to `E` does not. The fibre device therefore separates that one predicate into two, an `Out` class
the *output* objects must lie in and a larger `Amb` class the *ambient* object may lie in, with
`Out ⊆ Amb` and both stable under cones; geometrically `Out` is "perfect and supported on `T`"
and `Amb` is "quasi-coherent cohomology sheaves". Restoring complement-zero at the next stage is
the one non-formal step and is recorded in the docstring of
`Stacks.SplitLiftTower.exists_biprod_iso_lift_of_fibre_octahedron`.

## Implementation notes

The auxiliary category `D` is a bare `Category`: no triangulated structure is imposed on it, and
no compatibility of `res` with shifts or triangles is assumed. Everything needed is packaged in
the hypothesis `hcone`, which says that a morphism between objects of the good class has a cone
in `D`, again in the good class, whose restriction sits in a distinguished triangle downstairs.
That is precisely what a triangulated restriction functor supplies, and stating it this way keeps
`CategoryTheory.Functor.CommShift` out of the statement.

The distinguished triangles are stated as explicit `Triangle.mk`s with reduced vertices, and the
rotation of the triangle of the zero morphism is restated as one before it is used:
`CategoryTheory.Pretriangulated.Triangle.rotate` is not reducible at `implicit` transparency, so
a rewrite under it produces a term that `rw` and `simp` then silently decline to work in.

## References

* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open CategoryTheory.Pretriangulated

namespace CategoryTheory.Limits.Biprod

section Step

open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasBinaryBiproducts D]

/-- **The cone of `Q ⊞ Q' ⟶ P ⊞ Q` given by `biprod.fst ≫ biprod.inr` is `P ⊞ Q'⟦1⟧`.**
Let `ρ : S ⟶ Y` sit in a distinguished triangle with cone map `v : Y ⟶ Z`, and let
`eS : S ≅ Q ⊞ Q'` and `eY : Y ≅ P ⊞ Q` be coordinates in which `ρ` is the projection onto `Q`
followed by its inclusion. Then `Z ≅ P ⊞ Q'⟦1⟧`, by an isomorphism carrying the restriction of
the cone map to the `P` summand to `biprod.inl`.

This is the step of the iteration of [Stacks, Tag 09IN]: the `Q` summand, which the previous
stage contributed, cancels, and the new complement `Q'⟦1⟧` is a shift of the complement the
construction just produced, hence one degree lower. Both halves of the conclusion matter: the
object, because the next stage needs a splitting again, and the compatibility, because the
remark's conclusion names the map `P ⟶ Z` and not only `Z`. -/
theorem exists_iso_biprod_shift_of_distTriang_fst_comp_inr {P Q Q' S Y Z : D} {ρ : S ⟶ Y}
    {v : Y ⟶ Z} {w : Z ⟶ S⟦(1 : ℤ)⟧} (hT : Triangle.mk ρ v w ∈ distTriang D)
    (eS : S ≅ Q ⊞ Q') (eY : Y ≅ P ⊞ Q)
    (hρ : eS.inv ≫ ρ ≫ eY.hom =
      (biprod.fst : Q ⊞ Q' ⟶ Q) ≫ (biprod.inr : Q ⟶ P ⊞ Q)) :
    ∃ e : Z ≅ P ⊞ (Q'⟦(1 : ℤ)⟧),
      (biprod.inl : P ⟶ P ⊞ Q) ≫ eY.inv ≫ v ≫ e.hom = biprod.inl := by
  -- the given triangle, read in the coordinates `eS` and `eY`
  have hTc : Triangle.mk (eS.inv ≫ ρ ≫ eY.hom) (eY.inv ≫ v)
      (w ≫ (shiftFunctor D (1 : ℤ)).map eS.hom) ∈ distTriang D :=
    isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ eS.symm eY.symm (Iso.refl _) (by simp) (by simp)
        (by simp [← CategoryTheory.Functor.map_comp]))
  rw [hρ] at hTc
  -- the `Q' ⟶ P` component of that morphism vanishes, so its cone is a cone of `0 : Q' ⟶ P`
  obtain ⟨Z₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle (0 : Q' ⟶ P)
  have hT₀' : Triangle.mk ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫
      ((biprod.fst : Q ⊞ Q' ⟶ Q) ≫ (biprod.inr : Q ⟶ P ⊞ Q)) ≫
        (biprod.fst : P ⊞ Q ⟶ P)) v₀ w₀ ∈ distTriang D := by
    rw [show (biprod.inr : Q' ⟶ Q ⊞ Q') ≫
      ((biprod.fst : Q ⊞ Q' ⟶ Q) ≫ (biprod.inr : Q ⟶ P ⊞ Q)) ≫
        (biprod.fst : P ⊞ Q ⟶ P) = 0 from by simp]
    exact hT₀
  obtain ⟨e₀, he₀⟩ := nonempty_iso_of_distTriang_biprod_inl_comp _ (by simp) hTc hT₀'
  -- a cone of a zero morphism is the biproduct with the shift of its source; the rotated
  -- triangle is restated as a `Triangle.mk`, `Triangle.rotate` not being reducible at
  -- `implicit` transparency
  have hrot : Triangle.mk v₀ w₀ (0 : (Q'⟦(1 : ℤ)⟧) ⟶ P⟦(1 : ℤ)⟧) ∈ distTriang D := by
    have h : Triangle.mk v₀ w₀ (-(shiftFunctor D (1 : ℤ)).map (0 : Q' ⟶ P)) ∈ distTriang D :=
      rot_of_distTriang _ hT₀
    rwa [CategoryTheory.Functor.map_zero, neg_zero] at h
  obtain ⟨e₁, he₁, -⟩ := exists_iso_binaryBiproduct_of_distTriang
    (Triangle.mk v₀ w₀ (0 : (Q'⟦(1 : ℤ)⟧) ⟶ P⟦(1 : ℤ)⟧)) hrot rfl
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  calc (biprod.inl : P ⟶ P ⊞ Q) ≫ eY.inv ≫ v ≫ (e₀ ≪≫ e₁).hom
      = ((biprod.inl : P ⟶ P ⊞ Q) ≫ (eY.inv ≫ v) ≫ e₀.hom) ≫ e₁.hom := by simp
    _ = biprod.inl := by rw [he₀]; exact he₁

end Step

end CategoryTheory.Limits.Biprod

namespace Stacks.SplitLiftTower

/-! ### The fibre device, as pure triangulated algebra

One stage of the iteration of [Stacks, Tag 09IN] in the form described in the module docstring:
the map to the ambient object is kept by applying [Stacks, Tag 09IM] over the *fibre* of the map
of the previous stage and reading the new map and the new fibre off the octahedral axiom. There
is no degree bookkeeping here and no mention of perfectness or support — `Out` and `Amb` are
abstract predicates, and the consumers in `DerivedCategory` below do the arithmetic. -/

section Fibre

open CategoryTheory.Triangulated

variable {A : Type*} [Category A]
variable {B : Type*} [Category B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
  [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
  [HasBinaryBiproducts B]

/-- **The octahedral step of the fibre device.** Everything upstairs is in `A` — think
`D_QCoh(𝒪_X)` — and `res` is the restriction to the open `U`. At stage `k` the data are a
distinguished triangle `res Fk ⟶ res Rk ⟶ res E` downstairs, a splitting
`eR : res Rk ≅ P ⊞ J` in which the map to the ambient object is `biprod.fst ≫ α`, a lift
`lam : J ⟶ res Fk` of the junk inclusion through the fibre, and [Stacks, Tag 09IM] applied over
`Fk`, giving `b2 : R2 ⟶ Fk` with `res R2 ≅ J ⊞ N` and `b2` the projection onto `J` followed by
`lam`. The cone of `b2 ≫ u` and the octahedron on that factorization are given; the conclusion is
the same datum one stage on, with junk `N⟦1⟧`.

Four things happen, and only the third is more than formal.

* In the coordinates of the two splittings, `res (b2 ≫ u)` is `biprod.fst ≫ biprod.inr`, so
  `CategoryTheory.Limits.Biprod.exists_iso_biprod_shift_of_distTriang_fst_comp_inr` identifies the
  cone with `P ⊞ N⟦1⟧` and carries `biprod.inl` to `biprod.inl`. On the `P` summand the new map to
  `E` is therefore `α`, by the octahedron's third compatibility `v ≫ m₃ = βk`.
* Over `U` the map `b2` factors through `b2 ≫ u`, namely as
  `res (b2 ≫ u) ≫ eR.hom ≫ biprod.snd ≫ lam`; that is the one `biprod.inr ≫ biprod.snd = 𝟙`
  computation. Hence by the octahedron's fourth compatibility the new map to `E` composes to zero
  with the connecting map of stage `k`, and `Triangle.coyoneda_exact₃` factors it through `βk`,
  which factors through `α`.
* **Complement-zero at the next stage is not automatic, and this is where it is restored.** The
  factorization just obtained gives a map `t` with `res m₃ = t ≫ eR.hom ≫ biprod.fst ≫ α`; shearing
  the splitting by `s := biprod.inr ≫ e.inv ≫ t ≫ eR.hom ≫ biprod.fst` with
  `CategoryTheory.Limits.Biprod.shear` leaves the `P` component unchanged and replaces the `N⟦1⟧`
  component of the map to `E` by `s ≫ α - s ≫ α = 0`.
* With complement-zero back, the junk inclusion of the next stage kills the new map to `E`, so
  `Triangle.coyoneda_exact₂` on the octahedral triangle lifts it through the new fibre and
  produces `lam'`. The invariant is reproduced. -/
theorem exists_biprod_iso_lift_of_fibre_octahedron (res : A ⥤ B) {E Rk Fk R2 Z F' : A}
    {P J N : B} (α : P ⟶ res.obj E)
    {u : Fk ⟶ Rk} {βk : Rk ⟶ E} {wk : res.obj E ⟶ (res.obj Fk)⟦(1 : ℤ)⟧}
    (hTk : Triangle.mk (res.map u) (res.map βk) wk ∈ distTriang B)
    (eR : res.obj Rk ≅ P ⊞ J)
    (hβk : eR.inv ≫ res.map βk = (biprod.fst : P ⊞ J ⟶ P) ≫ α)
    (lam : J ⟶ res.obj Fk)
    (hlam : lam ≫ res.map u = (biprod.inr : J ⟶ P ⊞ J) ≫ eR.inv)
    {b2 : R2 ⟶ Fk} (e' : res.obj R2 ≅ J ⊞ N)
    (hb2 : e'.inv ≫ res.map b2 = (biprod.fst : J ⊞ N ⟶ J) ≫ lam)
    {v : Rk ⟶ Z} {w13 : res.obj Z ⟶ (res.obj R2)⟦(1 : ℤ)⟧}
    (h13 : Triangle.mk (res.map (b2 ≫ u)) (res.map v) w13 ∈ distTriang B)
    {m1 : F' ⟶ Z} {m3 : Z ⟶ E} {wnew : res.obj E ⟶ (res.obj F')⟦(1 : ℤ)⟧}
    (hcomm₃ : v ≫ m3 = βk)
    (hcomm₄ : w13 ≫ (shiftFunctor B (1 : ℤ)).map (res.map b2) = res.map m3 ≫ wk)
    (hmem : Triangle.mk (res.map m1) (res.map m3) wnew ∈ distTriang B) :
    ∃ (e2 : res.obj Z ≅ P ⊞ (N⟦(1 : ℤ)⟧)) (lam' : N⟦(1 : ℤ)⟧ ⟶ res.obj F'),
      e2.inv ≫ res.map m3 = (biprod.fst : P ⊞ (N⟦(1 : ℤ)⟧) ⟶ P) ≫ α ∧
        lam' ≫ res.map m1 = (biprod.inr : N⟦(1 : ℤ)⟧ ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) ≫ e2.inv := by
  -- in the coordinates of the two splittings, `b2 ≫ u` is `biprod.fst ≫ biprod.inr`
  have hρ : e'.inv ≫ res.map (b2 ≫ u) ≫ eR.hom =
      (biprod.fst : J ⊞ N ⟶ J) ≫ (biprod.inr : J ⟶ P ⊞ J) := by
    rw [res.map_comp, ← Category.assoc, ← Category.assoc, hb2]
    simp only [Category.assoc, reassoc_of% hlam]
    simp
  -- so its cone is `P ⊞ N⟦1⟧`, with `P` carried to `biprod.inl`
  obtain ⟨e, he⟩ := CategoryTheory.Limits.Biprod.exists_iso_biprod_shift_of_distTriang_fst_comp_inr
    h13 e' eR hρ
  have heinv : (biprod.inl : P ⟶ P ⊞ J) ≫ eR.inv ≫ res.map v = biprod.inl ≫ e.inv := by
    rw [← he]; simp
  -- on the `P` summand the new map to `E` is `α`
  have hP : (biprod.inl : P ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) ≫ e.inv ≫ res.map m3 = α := by
    rw [← Category.assoc, ← heinv]
    rw [Category.assoc, Category.assoc, ← res.map_comp, hcomm₃, hβk]
    simp
  -- over `U` the map `b2` factors through `b2 ≫ u`
  have hfac : res.map b2 = res.map (b2 ≫ u) ≫ (eR.hom ≫ (biprod.snd : P ⊞ J ⟶ J) ≫ lam) := by
    have h : res.map b2 = e'.hom ≫ (biprod.fst : J ⊞ N ⟶ J) ≫ lam := by
      rw [← hb2]; simp
    rw [res.map_comp, h]
    simp only [Category.assoc, reassoc_of% hlam]
    simp
  -- hence the new map to `E` composes to zero with the connecting map of stage `k`
  have h0 : w13 ≫ (shiftFunctor B (1 : ℤ)).map (res.map (b2 ≫ u)) = 0 :=
    comp_distTriang_mor_zero₃₁ _ h13
  have hzero : res.map m3 ≫ wk = 0 := by
    rw [← hcomm₄, hfac, CategoryTheory.Functor.map_comp, ← Category.assoc, h0, zero_comp]
  -- so it factors through `βk`, hence through `α`
  obtain ⟨t, ht⟩ := Triangle.coyoneda_exact₃ _ hTk (res.map m3) hzero
  have hσ : res.map m3 = (t ≫ eR.hom ≫ (biprod.fst : P ⊞ J ⟶ P)) ≫ α := by
    rw [ht]
    simp only [Triangle.mk_obj₂, Triangle.mk_mor₂, Category.assoc]
    rw [← hβk]
    simp
  -- shear the splitting to make the complement's component to `E` vanish
  set s : N⟦(1 : ℤ)⟧ ⟶ P :=
    (biprod.inr : N⟦(1 : ℤ)⟧ ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) ≫ e.inv ≫ t ≫ eR.hom ≫
      (biprod.fst : P ⊞ J ⟶ P) with hs
  have hinl : (biprod.inl : P ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) ≫
      (CategoryTheory.Limits.Biprod.shear s).hom = biprod.inl := by
    simp [CategoryTheory.Limits.Biprod.shear]
  have hinr : (biprod.inr : N⟦(1 : ℤ)⟧ ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) ≫
      (CategoryTheory.Limits.Biprod.shear s).hom =
      biprod.inr - s ≫ (biprod.inl : P ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) := by
    simp [CategoryTheory.Limits.Biprod.shear]
  have hcomp : (e ≪≫ (CategoryTheory.Limits.Biprod.shear s).symm).inv ≫ res.map m3 =
      (biprod.fst : P ⊞ (N⟦(1 : ℤ)⟧) ⟶ P) ≫ α := by
    have hkey : (CategoryTheory.Limits.Biprod.shear s).hom ≫ e.inv ≫ res.map m3 =
        (biprod.fst : P ⊞ (N⟦(1 : ℤ)⟧) ⟶ P) ≫ α := by
      refine biprod.hom_ext' _ _ ?_ ?_
      · rw [← Category.assoc, hinl, hP]; simp
      · rw [← Category.assoc, hinr, Preadditive.sub_comp, Category.assoc, hP,
          Category.assoc]
        rw [hσ]
        simp
    simpa using hkey
  refine ⟨e ≪≫ (CategoryTheory.Limits.Biprod.shear s).symm, ?_⟩
  obtain ⟨lam', hlam'⟩ := Triangle.coyoneda_exact₂ _ hmem
    ((biprod.inr : N⟦(1 : ℤ)⟧ ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) ≫
      (e ≪≫ (CategoryTheory.Limits.Biprod.shear s).symm).inv)
    (by rw [Category.assoc]; simp only [Triangle.mk_mor₂]; rw [hcomp]; simp)
  exact ⟨lam', hcomp, hlam'.symm⟩

variable {A' : Type*} [Category A'] [Preadditive A'] [HasZeroObject A'] [HasShift A' ℤ]
  [∀ n : ℤ, (shiftFunctor A' n).Additive] [Pretriangulated A'] [IsTriangulated A']

/-- **The stage of the fibre device, with the cones and the octahedron constructed.** Nothing is
hypothesised about cones or octahedra: `A'` is triangulated and `res` is a triangulated functor,
so the cone of `b2` — which is the new fibre — the cone of `b2 ≫ u` — which is the new lift — and
the octahedron relating them all exist, and `CategoryTheory.Triangulated.someOctahedron` produces
the latter from the factorization `b2 ≫ u = b2 ≫ u`.

The two class predicates enter only here, and in the two ways the module docstring describes. The
new lift `R'` is the cone of `b2 ≫ u : R2 ⟶ Rk`, so it is in the `Out` class as soon as that class
is stable under cones. The new fibre `F'` is the cone of `b2 : R2 ⟶ Fk`, whose source is in `Out`
and whose target is only in `Amb`; so `F'` is in `Amb`, and this is the step that a single class
forbids. -/
theorem exists_fibre_invariant_succ (res : A' ⥤ B) [res.CommShift ℤ] [res.IsTriangulated]
    (Out Amb : A' → Prop) (hOutAmb : ∀ Y : A', Out Y → Amb Y)
    (hOutCone : ∀ {Y₁ Y₂ Y₃ : A'} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A' → Out Y₁ → Out Y₂ → Out Y₃)
    (hAmbCone : ∀ {Y₁ Y₂ Y₃ : A'} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A' → Amb Y₁ → Amb Y₂ → Amb Y₃)
    {E Rk Fk R2 : A'} {P J N : B} (α : P ⟶ res.obj E)
    (hRk : Out Rk) (hFk : Amb Fk) (hR2 : Out R2)
    {u : Fk ⟶ Rk} {βk : Rk ⟶ E} {wk : E ⟶ Fk⟦(1 : ℤ)⟧}
    (hTk : Triangle.mk u βk wk ∈ distTriang A')
    (eR : res.obj Rk ≅ P ⊞ J)
    (hβk : eR.inv ≫ res.map βk = (biprod.fst : P ⊞ J ⟶ P) ≫ α)
    (lam : J ⟶ res.obj Fk)
    (hlam : lam ≫ res.map u = (biprod.inr : J ⟶ P ⊞ J) ≫ eR.inv)
    {b2 : R2 ⟶ Fk} (e' : res.obj R2 ≅ J ⊞ N)
    (hb2 : e'.inv ≫ res.map b2 = (biprod.fst : J ⊞ N ⟶ J) ≫ lam) :
    ∃ (R' F' : A') (u' : F' ⟶ R') (β' : R' ⟶ E) (w' : E ⟶ F'⟦(1 : ℤ)⟧)
      (e2 : res.obj R' ≅ P ⊞ (N⟦(1 : ℤ)⟧)) (lam' : N⟦(1 : ℤ)⟧ ⟶ res.obj F'),
      Out R' ∧ Amb F' ∧ Triangle.mk u' β' w' ∈ distTriang A' ∧
        e2.inv ≫ res.map β' = (biprod.fst : P ⊞ (N⟦(1 : ℤ)⟧) ⟶ P) ≫ α ∧
          lam' ≫ res.map u' = (biprod.inr : N⟦(1 : ℤ)⟧ ⟶ P ⊞ (N⟦(1 : ℤ)⟧)) ≫ e2.inv := by
  obtain ⟨F', p, q, h12⟩ := distinguished_cocone_triangle b2
  obtain ⟨Z, v, w13, h13⟩ := distinguished_cocone_triangle (b2 ≫ u)
  have oct := Triangulated.someOctahedron (rfl : b2 ≫ u = b2 ≫ u) h12 hTk h13
  obtain ⟨e2, lam', hcompat, hlam'⟩ := exists_biprod_iso_lift_of_fibre_octahedron res α
    (res.map_distinguished _ hTk) eR hβk lam hlam e' hb2 (res.map_distinguished _ h13)
    oct.comm₃ (by simpa [Triangulated.Octahedron.map_m₃] using (oct.map res).comm₄)
    (by simpa [Triangulated.Octahedron.map_m₁, Triangulated.Octahedron.map_m₃]
      using (oct.map res).mem)
  refine ⟨Z, F', oct.m₁, oct.m₃, wk ≫ (shiftFunctor A' (1 : ℤ)).map p, e2, lam',
    hOutCone _ _ _ h13 hR2 hRk, hAmbCone _ _ _ h12 (hOutAmb _ hR2) hFk, ?_, hcompat, hlam'⟩
  simpa using oct.mem

omit [IsTriangulated B] [IsTriangulated A'] in
/-- **The base of the fibre device.** [Stacks, Tag 09IM]'s output is already the invariant:
take for `F` the fibre of the given `β`, and the strengthened compatibility
`eR.inv ≫ res β = biprod.fst ≫ α` makes the junk inclusion `biprod.inr ≫ eR.inv` kill `res β`, so
`Triangle.coyoneda_exact₂` lifts it through `res F`. That lift is the only datum of the invariant
beyond 09IM's own conclusion, and this is the one place the strengthening is used.

`F` is in the `Amb` class because it is the first vertex of a distinguished triangle whose other
two vertices are; it is not in the `Out` class, and does not have to be. -/
theorem exists_fibre_invariant_base (res : A' ⥤ B) [res.CommShift ℤ] [res.IsTriangulated]
    (Amb : A' → Prop)
    (hAmbFib : ∀ {Y₁ Y₂ Y₃ : A'} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A' → Amb Y₂ → Amb Y₃ → Amb Y₁)
    {E R1 : A'} {P J : B} (α : P ⟶ res.obj E) (β : R1 ⟶ E) (hE : Amb E) (hR1 : Amb R1)
    (eR : res.obj R1 ≅ P ⊞ J)
    (hβ : eR.inv ≫ res.map β = (biprod.fst : P ⊞ J ⟶ P) ≫ α) :
    ∃ (F : A') (u : F ⟶ R1) (w : E ⟶ F⟦(1 : ℤ)⟧) (lam : J ⟶ res.obj F),
      Amb F ∧ Triangle.mk u β w ∈ distTriang A' ∧
        lam ≫ res.map u = (biprod.inr : J ⟶ P ⊞ J) ≫ eR.inv := by
  obtain ⟨F, u, w, hT⟩ := distinguished_cocone_triangle₁ β
  have hTB : Triangle.mk (res.map u) (res.map β)
      (res.map w ≫ (res.commShiftIso (1 : ℤ)).hom.app F) ∈ distTriang B :=
    res.map_distinguished _ hT
  obtain ⟨lam, hlam⟩ := Triangle.coyoneda_exact₂ _ hTB ((biprod.inr : J ⟶ P ⊞ J) ≫ eR.inv)
    (by simp only [Triangle.mk_mor₂, Category.assoc, hβ]; simp)
  exact ⟨F, u, w, lam, hAmbFib u β w hT hR1 hE, hT, hlam.symm⟩

end Fibre

end Stacks.SplitLiftTower

namespace DerivedCategory

open CategoryTheory.Triangulated

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsTriangulated (DerivedCategory C)]

variable {D : Type*} [Category D] (res : D ⥤ DerivedCategory C)
  (G : DerivedCategory C → Prop) (GD : D → Prop)

/-- **The invariant of the iteration of [Stacks, Tag 09IN], run `k` times.**

The hypotheses are the ones the affine-cover induction of [Stacks, Tag 09IM] supplies:

* `hGshift`: the good class downstairs — perfect and supported on `T ∩ U` — is stable under the
  shift;
* `hcone`: a morphism between objects of the good class upstairs has a cone there, again in the
  class, whose restriction sits in a distinguished triangle downstairs;
* `oracle`: [Stacks, Tag 09IM] itself, in the form its proof gives. For a good `Q` with
  cohomology vanishing above `m` and a map `α` to a good ambient object `Y`, it produces
  `ρ : R ⟶ Y` with `R` good, a splitting `res R ≅ Q ⊞ Q'` whose complement is good with
  cohomology vanishing above `m - 1`, and the compatibility `e.inv ≫ res ρ = biprod.fst ≫ α`:
  in the coordinates of the splitting the map to the ambient object is the projection followed
  by `α`;
* `e₁`: the first application of the oracle, to `P` itself, with the complement a sum of
  positive shifts of `P` and so with cohomology vanishing above `b - 1`.

The conclusion is the same splitting datum with the bound lowered to `b - 1 - k`. -/
theorem exists_biprod_iso_of_splitLiftOracle
    (hGshift : ∀ A : DerivedCategory C, G A → G (A⟦(1 : ℤ)⟧))
    (hcone : ∀ (A B : D) (f : A ⟶ B), GD A → GD B →
      ∃ (Z : D) (v : B ⟶ Z) (w : res.obj Z ⟶ (res.obj A)⟦(1 : ℤ)⟧),
        GD Z ∧ Triangle.mk (res.map f) (res.map v) w ∈ distTriang (DerivedCategory C))
    (oracle : ∀ (Y : D), GD Y → ∀ (Q : DerivedCategory C), G Q → ∀ m : ℤ,
      (∀ i : ℤ, m < i → IsZero ((homologyFunctor C i).obj Q)) → ∀ α : Q ⟶ res.obj Y,
        ∃ (R : D) (ρ : R ⟶ Y) (Q' : DerivedCategory C) (e : res.obj R ≅ Q ⊞ Q'),
          GD R ∧ G Q' ∧ (∀ i : ℤ, m - 1 < i → IsZero ((homologyFunctor C i).obj Q')) ∧
            e.inv ≫ res.map ρ = (biprod.fst : Q ⊞ Q' ⟶ Q) ≫ α)
    {P : DerivedCategory C} {b : ℤ} {R₁ : D} {Q₁ : DerivedCategory C}
    (hR₁ : GD R₁) (hQ₁ : G Q₁) (e₁ : res.obj R₁ ≅ P ⊞ Q₁)
    (hQ₁b : ∀ i : ℤ, b - 1 < i → IsZero ((homologyFunctor C i).obj Q₁)) (k : ℕ) :
    ∃ (Y : D) (Q : DerivedCategory C) (_ : res.obj Y ≅ P ⊞ Q),
      GD Y ∧ G Q ∧ ∀ i : ℤ, b - 1 - (k : ℤ) < i → IsZero ((homologyFunctor C i).obj Q) := by
  induction k with
  | zero =>
    refine ⟨R₁, Q₁, e₁, hR₁, hQ₁, fun i hi => hQ₁b i ?_⟩
    simpa using hi
  | succ k ih =>
    obtain ⟨Y, Q, e, hGDY, hGQ, hQ⟩ := ih
    obtain ⟨R, ρ, Q', e', hGDR, hGQ', hQ', hcompat⟩ :=
      oracle Y hGDY Q hGQ (b - 1 - (k : ℤ)) hQ ((biprod.inr : Q ⟶ P ⊞ Q) ≫ e.inv)
    obtain ⟨Z, v, w, hGDZ, hTZ⟩ := hcone R Y ρ hGDR hGDY
    have hρ : e'.inv ≫ res.map ρ ≫ e.hom =
        (biprod.fst : Q ⊞ Q' ⟶ Q) ≫ (biprod.inr : Q ⟶ P ⊞ Q) := by
      rw [← Category.assoc, hcompat]
      simp
    obtain ⟨ee, -⟩ :=
      CategoryTheory.Limits.Biprod.exists_iso_biprod_shift_of_distTriang_fst_comp_inr
        hTZ e' e hρ
    exact ⟨Z, Q'⟦(1 : ℤ)⟧, ee, hGDZ, hGshift _ hGQ', fun i hi =>
      isZero_homology_shift_of_one_le Q' _ hQ' 1 le_rfl i (by push_cast at hi; lia)⟩

/-- **The degree clause of [Stacks, Tag 09IN].** Under the hypotheses of
`DerivedCategory.exists_biprod_iso_of_splitLiftOracle`, for every degree `n` there is an object
`Y` of the good class upstairs and a map `P ⟶ res Y` which is an isomorphism on `H^i` for every
`i > n` and an epimorphism on `H^n` — the cohomology of `res Y` agrees with that of `P` above
`n`.

The degree is fixed first and `Y` depends on it; see the module docstring for why the other
reading of the remark is false, and for the map to the ambient object that this does not
provide. -/
theorem exists_approximatesFrom_of_splitLiftOracle
    (hGshift : ∀ A : DerivedCategory C, G A → G (A⟦(1 : ℤ)⟧))
    (hcone : ∀ (A B : D) (f : A ⟶ B), GD A → GD B →
      ∃ (Z : D) (v : B ⟶ Z) (w : res.obj Z ⟶ (res.obj A)⟦(1 : ℤ)⟧),
        GD Z ∧ Triangle.mk (res.map f) (res.map v) w ∈ distTriang (DerivedCategory C))
    (oracle : ∀ (Y : D), GD Y → ∀ (Q : DerivedCategory C), G Q → ∀ m : ℤ,
      (∀ i : ℤ, m < i → IsZero ((homologyFunctor C i).obj Q)) → ∀ α : Q ⟶ res.obj Y,
        ∃ (R : D) (ρ : R ⟶ Y) (Q' : DerivedCategory C) (e : res.obj R ≅ Q ⊞ Q'),
          GD R ∧ G Q' ∧ (∀ i : ℤ, m - 1 < i → IsZero ((homologyFunctor C i).obj Q')) ∧
            e.inv ≫ res.map ρ = (biprod.fst : Q ⊞ Q' ⟶ Q) ≫ α)
    {P : DerivedCategory C} {b : ℤ} {R₁ : D} {Q₁ : DerivedCategory C}
    (hR₁ : GD R₁) (hQ₁ : G Q₁) (e₁ : res.obj R₁ ≅ P ⊞ Q₁)
    (hQ₁b : ∀ i : ℤ, b - 1 < i → IsZero ((homologyFunctor C i).obj Q₁)) (n : ℤ) :
    ∃ (Y : D) (ν : P ⟶ res.obj Y), GD Y ∧ ApproximatesFrom ν n := by
  obtain ⟨Y, Q, e, hGDY, -, hQ⟩ := exists_biprod_iso_of_splitLiftOracle res G GD hGshift hcone
    oracle hR₁ hQ₁ e₁ hQ₁b (b - n).toNat
  refine ⟨Y, (biprod.inl : P ⟶ P ⊞ Q) ≫ e.inv, hGDY, ?_⟩
  have hb : b - n ≤ ((b - n).toNat : ℤ) := Int.self_le_toNat _
  have happrox : ApproximatesFrom (biprod.inl : P ⟶ P ⊞ Q) n :=
    (approximatesFrom_biprod_inl_iff P Q n).2 fun i hi => hQ i (by lia)
  simpa using approximatesFrom_comp_iso e.symm happrox

/-! ### The fibre device iterated: the degree clause with the map to the ambient object -/

section Fibre

variable {A : Type*} [Category A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
  [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A] [IsTriangulated A]

/-- **The invariant of the fibre device, run `k` times.** The hypotheses are the ones the
affine-cover induction of [Stacks, Tag 09IM] supplies, with the single good class of
`DerivedCategory.exists_biprod_iso_of_splitLiftOracle` separated in two:

* `Out` is the class the lifts must lie in — geometrically, perfect and supported on `T` — and
  `Amb` the class the ambient objects may lie in — geometrically, quasi-coherent cohomology
  sheaves. Both are stable under cones, `Out` is contained in `Amb`, and `Amb` is stable under
  passing to the first vertex of a distinguished triangle. That last closure is what the fibre
  needs and what a single class cannot give.
* `GQ` is the class downstairs that [Stacks, Tag 09IM] accepts as input — perfect and supported on
  `T ∩ U` — and it is stable under the shift, which is all the junk ever undergoes.
* `oracle` is [Stacks, Tag 09IM] in the strengthened form its proof gives, over an ambient object
  of the class `Amb`: a perfect supported `R` with a map `β` to the ambient object and a splitting
  `res R ≅ F ⊞ N` in which `β` is the projection followed by the given map, with the complement
  `N` again in `GQ` and its cohomology one degree lower than `F`'s. That last clause is the
  remark's first sentence: the affine-cover induction of 09IM produces for `N` a finite biproduct
  of *positive* shifts of `F`, and
  `Stacks.SumOfPositiveShifts.isZero_homology_of_isSumOfPositiveShifts` in
  `StacksFrontier/CategoryTheory/SumOfPositiveShifts.lean` turns that shape into the degree bound.

The conclusion is the full invariant at stage `k`: the lift, its map to `E`, the fibre of that
map, the splitting with the strengthened compatibility, the lift of the junk inclusion through the
fibre, and the bound `b - 1 - 2k` on the junk — two degrees per stage, the oracle's complement
contributing one and the cone's shift another. -/
theorem exists_hom_biprod_iso_of_fibreOracle (res : A ⥤ DerivedCategory C) [res.CommShift ℤ]
    [res.IsTriangulated] (Out Amb : A → Prop) (GQ : DerivedCategory C → Prop)
    (hOutAmb : ∀ Y : A, Out Y → Amb Y)
    (hOutCone : ∀ {Y₁ Y₂ Y₃ : A} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A → Out Y₁ → Out Y₂ → Out Y₃)
    (hAmbCone : ∀ {Y₁ Y₂ Y₃ : A} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A → Amb Y₁ → Amb Y₂ → Amb Y₃)
    (hAmbFib : ∀ {Y₁ Y₂ Y₃ : A} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A → Amb Y₂ → Amb Y₃ → Amb Y₁)
    (hGQshift : ∀ F : DerivedCategory C, GQ F → GQ (F⟦(1 : ℤ)⟧))
    (oracle : ∀ Y : A, Amb Y → ∀ F : DerivedCategory C, GQ F → ∀ m : ℤ,
      (∀ i : ℤ, m < i → IsZero ((homologyFunctor C i).obj F)) → ∀ α : F ⟶ res.obj Y,
        ∃ (R : A) (β : R ⟶ Y) (N : DerivedCategory C) (e : res.obj R ≅ F ⊞ N),
          Out R ∧ GQ N ∧ (∀ i : ℤ, m - 1 < i → IsZero ((homologyFunctor C i).obj N)) ∧
            e.inv ≫ res.map β = (biprod.fst : F ⊞ N ⟶ F) ≫ α)
    {E : A} (hE : Amb E) {P : DerivedCategory C} (hP : GQ P) {b : ℤ}
    (hPb : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj P))
    (α : P ⟶ res.obj E) (k : ℕ) :
    ∃ (R F : A) (u : F ⟶ R) (β : R ⟶ E) (w : E ⟶ F⟦(1 : ℤ)⟧) (J : DerivedCategory C)
      (e : res.obj R ≅ P ⊞ J) (lam : J ⟶ res.obj F),
      Out R ∧ Amb F ∧ GQ J ∧ Triangle.mk u β w ∈ distTriang A ∧
        e.inv ≫ res.map β = (biprod.fst : P ⊞ J ⟶ P) ≫ α ∧
          lam ≫ res.map u = (biprod.inr : J ⟶ P ⊞ J) ≫ e.inv ∧
            ∀ i : ℤ, b - 1 - 2 * (k : ℤ) < i → IsZero ((homologyFunctor C i).obj J) := by
  induction k with
  | zero =>
    obtain ⟨R₁, β₁, J₁, e₁, hOutR₁, hGQJ₁, hJ₁b, hcompat₁⟩ := oracle E hE P hP b hPb α
    obtain ⟨F₁, u₁, w₁, lam₁, hAmbF₁, hT₁, hlam₁⟩ :=
      Stacks.SplitLiftTower.exists_fibre_invariant_base res Amb hAmbFib α β₁ hE
        (hOutAmb _ hOutR₁) e₁ hcompat₁
    refine ⟨R₁, F₁, u₁, β₁, w₁, J₁, e₁, lam₁, hOutR₁, hAmbF₁, hGQJ₁, hT₁,
      hcompat₁, hlam₁, fun i hi => hJ₁b i ?_⟩
    push_cast at hi
    lia
  | succ k ih =>
    obtain ⟨R, F, u, β, w, J, e, lam, hR, hF, hJ, hT, hcompat, hlam, hbound⟩ := ih
    obtain ⟨R₂, b₂, N, e', hR₂, hGQN, hNb, hb₂⟩ :=
      oracle F hF J hJ (b - 1 - 2 * (k : ℤ)) hbound lam
    obtain ⟨R', F', u', β', w', e₂, lam', hR', hF', hT', hcompat', hlam'⟩ :=
      Stacks.SplitLiftTower.exists_fibre_invariant_succ res Out Amb hOutAmb hOutCone hAmbCone
        α hR hF hR₂ hT e hcompat lam hlam e' hb₂
    exact ⟨R', F', u', β', w', N⟦(1 : ℤ)⟧, e₂, lam', hR', hF', hGQshift _ hGQN, hT', hcompat',
      hlam', fun i hi =>
        isZero_homology_shift_of_one_le N _ hNb 1 le_rfl i (by push_cast at hi; lia)⟩

/-- **The degree clause of [Stacks, Tag 09IN], with the map to the ambient object retained.**
Under the hypotheses of `DerivedCategory.exists_hom_biprod_iso_of_fibreOracle`, for every degree
`n` there are an object `R` of the class `Out`, a map `β : R ⟶ E` to the ambient object, and a
splitting `res R ≅ P ⊞ J` through which `β` restricts to the projection followed by the given
`α : P ⟶ res E`, with the junk `J` having no cohomology in any degree `≥ n`.

This is the fibre device run `(b - n).toNat` times, which is enough in both of the two cases: when
`n > b` the junk is already clear of `n` at stage `0`, and otherwise each stage lowers its top
degree by two.

The degree is fixed first and `R` depends on it; see the module docstring for why the other
reading of the remark is false. -/
theorem exists_hom_biprod_iso_isZero_homology_of_fibreOracle (res : A ⥤ DerivedCategory C)
    [res.CommShift ℤ] [res.IsTriangulated] (Out Amb : A → Prop) (GQ : DerivedCategory C → Prop)
    (hOutAmb : ∀ Y : A, Out Y → Amb Y)
    (hOutCone : ∀ {Y₁ Y₂ Y₃ : A} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A → Out Y₁ → Out Y₂ → Out Y₃)
    (hAmbCone : ∀ {Y₁ Y₂ Y₃ : A} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A → Amb Y₁ → Amb Y₂ → Amb Y₃)
    (hAmbFib : ∀ {Y₁ Y₂ Y₃ : A} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang A → Amb Y₂ → Amb Y₃ → Amb Y₁)
    (hGQshift : ∀ F : DerivedCategory C, GQ F → GQ (F⟦(1 : ℤ)⟧))
    (oracle : ∀ Y : A, Amb Y → ∀ F : DerivedCategory C, GQ F → ∀ m : ℤ,
      (∀ i : ℤ, m < i → IsZero ((homologyFunctor C i).obj F)) → ∀ α : F ⟶ res.obj Y,
        ∃ (R : A) (β : R ⟶ Y) (N : DerivedCategory C) (e : res.obj R ≅ F ⊞ N),
          Out R ∧ GQ N ∧ (∀ i : ℤ, m - 1 < i → IsZero ((homologyFunctor C i).obj N)) ∧
            e.inv ≫ res.map β = (biprod.fst : F ⊞ N ⟶ F) ≫ α)
    {E : A} (hE : Amb E) {P : DerivedCategory C} (hP : GQ P) {b : ℤ}
    (hPb : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj P))
    (α : P ⟶ res.obj E) (n : ℤ) :
    ∃ (R : A) (β : R ⟶ E) (J : DerivedCategory C) (e : res.obj R ≅ P ⊞ J),
      Out R ∧ e.inv ≫ res.map β = (biprod.fst : P ⊞ J ⟶ P) ≫ α ∧
        ∀ i : ℤ, n ≤ i → IsZero ((homologyFunctor C i).obj J) := by
  obtain ⟨R, -, -, β, -, J, e, -, hR, -, -, -, hcompat, -, hbound⟩ :=
    exists_hom_biprod_iso_of_fibreOracle res Out Amb GQ hOutAmb hOutCone hAmbCone hAmbFib
      hGQshift oracle hE hP hPb α (b - n).toNat
  have hb : b - n ≤ ((b - n).toNat : ℤ) := Int.self_le_toNat _
  have hb0 : (0 : ℤ) ≤ ((b - n).toNat : ℤ) := Int.natCast_nonneg _
  exact ⟨R, β, J, e, hR, hcompat, fun i hi => hbound i (by lia)⟩

end Fibre

end DerivedCategory

end
