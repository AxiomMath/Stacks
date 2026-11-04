module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Homology.DerivedComplete.ConstantTowerEventualInverses

/-!
# Pro-vanishing of the morphisms out of an inverse system

Let `W : ℕᵒᵖ ⥤ 𝒞` be an inverse system and `E` an object of `𝒞`. The system of abelian groups
`n ↦ Hom(W_n, E)` is *inductive*, its transition maps being precomposition with the transition
maps of `W`, and this file studies the condition that its colimit vanish. Written without
colimits — which is how it is used, and which needs no hypothesis on `𝒞` beyond zero morphisms —
the condition is

`NoetherianAdicCompletion.HomProVanishing W E`: every morphism `W_n ⟶ E` is annihilated by some
transition map `W_m ⟶ W_n`.

Two things are proved about it, and then one application.

## It is a triangulated condition on the target

`NoetherianAdicCompletion.homProVanishingProperty W` is pro-vanishing read as an
`CategoryTheory.ObjectProperty` of the target. It is closed under isomorphism, holds at a zero
object, and satisfies two-out-of-three for distinguished triangles
(`CategoryTheory.ObjectProperty.IsTriangulatedClosed₂`): the three instances below. The
two-out-of-three property is the one with content, and it is the exactness of a filtered colimit
of long exact sequences, done by hand: a morphism `W_n ⟶ Y` whose composite into `Z` already
vanishes factors through `X`, and the factor is then killed further along.

## Hence it is a condition on the cohomology of a bounded target

`NoetherianAdicCompletion.prop_of_isGE_of_isLE` is the dévissage along the canonical truncation
triangles of a t-structure: a property of objects which is closed under isomorphism, holds at a
zero object and satisfies two-out-of-three holds at every object concentrated in finitely many
degrees as soon as it holds at every object concentrated in a single degree. Specialised to
pro-vanishing this is `NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE`.

The statement is about `t.IsGE` and `t.IsLE`, that is about the *cohomology* of the target being
bounded, and not about a representing complex having finitely many nonzero terms; the latter
reduction is already in the library, privately, in
`StacksFrontier/Homology/DerivedComplete/CechCompletion.lean`.

## The dévissage restricted to a subcategory

In that unrestricted form the single-degree hypothesis is frequently too strong to be
dischargeable: see the discussion at
`NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem`, which weakens it to the
single-degree objects of a subcategory `Q` and correspondingly weakens the conclusion to the
objects of `Q`. The *only* thing asked of `Q` is that the two canonical truncation functors
preserve it, that being what keeps the induction inside `Q`; in particular `Q` need satisfy no
two-out-of-three of its own.

The single-degree hypothesis is moreover only ever needed in the degrees the system `W` itself
occupies: in a degree strictly above them there is no nonzero morphism out of `W` at all, by the
orthogonality of the two halves of the t-structure. That is
`NoetherianAdicCompletion.homProVanishing_of_lt`, and
`NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem_of_isLE` is the dévissage with
the hypothesis so restricted.

Two mechanisms discharge that closure, and between them they settle the question for the two
candidate forms of an `ℐ`-power-torsion subcategory.

* Uniform annihilation. The objects `E` with `u_E = 0` for a family of natural endomorphisms
  `u : 𝟭 D ⟶ 𝟭 D` of the identity — multiplication by global scalars — are closed under both
  truncations, by naturality of `u` at `τ^{<n}E ⟶ E` and at `E ⟶ τ^{≥n}E` together with the
  two injectivity statements
  `NoetherianAdicCompletion.eq_zero_of_comp_truncLTι_app_eq_zero` and
  `NoetherianAdicCompletion.eq_zero_of_truncGEπ_app_comp_eq_zero`. The resulting dévissage is
  `NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_app_eq_zero`. This is the form
  the Koszul application supplies and the form the sheaf-level base case
  `Stacks.Sites.homProVanishing_idealPowTower` consumes, the latter asking for a target killed by
  one power `ℐᴺ`.
* Vanishing of a family of functors. The kernel of a triangulated functor preserving both
  `t`-bounds is closed under both truncations
  (`NoetherianAdicCompletion.isZero_map_truncLT_and_truncGE_of_isZero_map`). This is the shape
  `AlgebraicGeometry.RingedSite.DerivedPowerTorsion` is written in, as the vanishing of the
  derived localizations `𝒪_{f_i} ⊗^𝐋_𝒪 -`; see that theorem for what remains to be supplied
  before it applies to them.

## The application

`NoetherianAdicCompletion.hasEventualInverses_const_of_homProVanishing` replaces the two
level-by-level vanishing hypotheses of
`NoetherianAdicCompletion.hasEventualInverses_const_of_triangles` by a single uniform one. The
uniform hypothesis is **stronger** — it quantifies over every morphism out of the system, not
only over the two structural ones — and the point of stating it is that it, rather than the two
structural vanishings, is what a derived-torsion theorem delivers. Let
`φ : (Functor.const ℕᵒᵖ).obj V ⟶ G` be the augmentation of an inverse system out of the constant
system at `V`, presented by a *functorial* family of distinguished triangles

`W_m ⟶ V ⟶ G_m ⟶ (W_m)⟦1⟧`.

Then `φ` has eventual inverses as soon as the morphisms out of `W` into `V` pro-vanish and the
morphisms out of `W` into each `W_n` pro-vanish. Both are instances of one condition on the
system `W`, and by the dévissage above both are conditions on the cohomology of `V` and of the
`W_n` when those are bounded.

This is the shape in which the derived `ℐ`-torsion input of [Stacks, Tag 0A0K] part (1) would be
consumed. There `V` is a dual Koszul complex `(Kⁿ)^∨` at a fixed Koszul index, `G_m` is
`V ⊗^𝐋 𝒪/ℐᵐ⁺¹` and `W_m` is `V ⊗^𝐋 ℐᵐ⁺¹`, so the hypotheses read `colim_m Hom(V ⊗^𝐋 ℐᵐ⁺¹, -) = 0`
at `V` and at each `V ⊗^𝐋 ℐⁿ⁺¹`; by the tensor–internal-Hom adjunction those are
`colim_m Hom(ℐᵐ⁺¹, E) = 0` for `E` the derived internal Hom out of `V`, which is bounded with
`ℐ`-power-torsion cohomology. That vanishing is not supplied here. Its degree-zero case at sheaf
level is `Stacks.Sites.homProVanishing_idealPowTower_singleFunctor`, on an arbitrary site; the
higher degrees are not in the library, because on a site `Hom_{D(𝒪)}(𝒪, F⟦j⟧)` is the sheaf
cohomology `H^j(F)`, so the long exact sequence of `ℐᵏ ⊆ 𝒪` does not reduce them to degree zero
the way it does over a ring, where `𝒪` is free. Over a commutative ring the whole statement is
`Stacks.LocalCohomology.localCohomology_isHomotopyColimit_derivedHomPowers`, [Stacks, Tag 0954].
Nothing below is conditional on it and nothing below carries a `@[stacks]` attribute: these are
the reductions, and the vanishing is a hypothesis.

## Main definitions

* `NoetherianAdicCompletion.HomProVanishing` — the morphisms out of the system into the target
  are each killed by a transition map.
* `NoetherianAdicCompletion.homProVanishingProperty` — the same, as an object property of the
  target.

## Main results

* `NoetherianAdicCompletion.HomProVanishing.of_triangle` — two-out-of-three for a distinguished
  triangle in the target.
* `NoetherianAdicCompletion.prop_of_isGE_of_isLE` — dévissage of a triangulated object property
  along the truncations of a t-structure.
* `NoetherianAdicCompletion.prop_of_isGE_of_isLE_of_mem` — the same dévissage restricted to a
  subcategory the truncations preserve.
* `NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE` — pro-vanishing into a target with
  bounded cohomology follows from pro-vanishing into the objects concentrated in one degree.
* `NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem` — the same restricted to a
  subcategory the truncations preserve.
* `NoetherianAdicCompletion.homProVanishing_of_lt` — pro-vanishing is vacuous into a target
  concentrated strictly above the degrees of the system.
* `NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem_of_isLE` — the restricted
  dévissage with its single-degree hypothesis asked for only in the degrees the system occupies.
* `NoetherianAdicCompletion.eq_zero_of_comp_truncLTι_app_eq_zero`,
  `NoetherianAdicCompletion.eq_zero_of_truncGEπ_app_comp_eq_zero` — a morphism out of `τ^{<n}E`'s
  degree range, resp. into `τ^{≥n}E`'s, is detected by its composite with the truncation map.
* `NoetherianAdicCompletion.app_truncLT_eq_zero_of_app_eq_zero`,
  `NoetherianAdicCompletion.app_truncGE_eq_zero_of_app_eq_zero` — the objects annihilated by a
  natural endomorphism of the identity are closed under both truncations.
* `NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_app_eq_zero` — the dévissage
  restricted to the objects annihilated by a family of such endomorphisms.
* `NoetherianAdicCompletion.isZero_map_truncLT_and_truncGE_of_isZero_map` — the kernel of a
  `t`-exact triangulated functor is closed under both truncations.
* `NoetherianAdicCompletion.hasEventualInverses_const_of_homProVanishing` — eventual inverses for
  the augmentation of a constant tower, from one pro-vanishing hypothesis on the system
  presenting it.

## References

* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated Opposite

universe u v u' v'

namespace NoetherianAdicCompletion

/-! ### The condition -/

section Definition

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- **The morphisms out of an inverse system into `E` pro-vanish**: every morphism `W_n ⟶ E` is
annihilated by some transition map `W_m ⟶ W_n` of the system. Equivalently the colimit of the
inductive system of abelian groups `n ↦ Hom(W_n, E)` vanishes; the colimit is avoided so that no
hypothesis on `C` beyond zero morphisms is needed. -/
def HomProVanishing (W : ℕᵒᵖ ⥤ C) (E : C) : Prop :=
  ∀ (n : ℕ) (x : W.obj (op n) ⟶ E), ∃ (m : ℕ) (h : n ≤ m), W.map (homOfLE h).op ≫ x = 0

/-- Pro-vanishing is invariant under isomorphism of the target. -/
theorem HomProVanishing.of_iso {W : ℕᵒᵖ ⥤ C} {E E' : C} (h : HomProVanishing W E) (e : E ≅ E') :
    HomProVanishing W E' := by
  intro n x
  obtain ⟨m, hm, hx⟩ := h n (x ≫ e.inv)
  refine ⟨m, hm, ?_⟩
  have := congrArg (fun f : W.obj (op m) ⟶ E => f ≫ e.hom) hx
  simpa using this

/-- Pro-vanishing holds at a zero target, there being no nonzero morphism into it at all. -/
theorem HomProVanishing.of_isZero (W : ℕᵒᵖ ⥤ C) {E : C} (hE : IsZero E) :
    HomProVanishing W E := fun n x =>
  ⟨n, le_rfl, by rw [hE.eq_of_tgt x 0, comp_zero]⟩

/-- Once a morphism out of the system has been killed at level `m`, it stays killed at every
later level. -/
theorem HomProVanishing.comp_eq_zero_of_le {W : ℕᵒᵖ ⥤ C} {E : C} {n m m' : ℕ}
    {x : W.obj (op n) ⟶ E} (hm : n ≤ m) (hm' : m ≤ m')
    (hx : W.map (homOfLE hm).op ≫ x = 0) :
    W.map (homOfLE (hm.trans hm')).op ≫ x = 0 := by
  rw [← map_homOfLE_op_comp W hm' hm, Category.assoc, hx, comp_zero]

end Definition

/-! ### Pro-vanishing is a triangulated condition on the target -/

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Two-out-of-three for pro-vanishing.** If the morphisms out of `W` pro-vanish into the first
and the third vertex of a distinguished triangle, they pro-vanish into the second.

Given `x : W_n ⟶ T.obj₂`, its composite into `T.obj₃` is killed at some level `m`; the morphism
`W_m ⟶ T.obj₂` so obtained therefore factors through `T.obj₁`, and the factor is killed at some
later level, which kills the morphism itself. This is the exactness of a filtered colimit of the
long exact sequences `Hom(W_n, T.obj₁) ⟶ Hom(W_n, T.obj₂) ⟶ Hom(W_n, T.obj₃)`, carried out by
hand on the two levels it needs. -/
theorem HomProVanishing.of_triangle {W : ℕᵒᵖ ⥤ D} (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : HomProVanishing W T.obj₁) (h₃ : HomProVanishing W T.obj₃) :
    HomProVanishing W T.obj₂ := by
  intro n x
  obtain ⟨m, hm, hx⟩ := h₃ n (x ≫ T.mor₂)
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT (W.map (homOfLE hm).op ≫ x)
    (by rw [Category.assoc]; exact hx)
  obtain ⟨m', hm', hg'⟩ := h₁ m g
  refine ⟨m', hm.trans hm', ?_⟩
  rw [← map_homOfLE_op_comp W hm' hm, Category.assoc, hg, ← Category.assoc, hg', zero_comp]

/-- Pro-vanishing of the morphisms out of a fixed inverse system, read as a property of the
target. -/
def homProVanishingProperty (W : ℕᵒᵖ ⥤ D) : ObjectProperty D := fun E => HomProVanishing W E

/-- Pro-vanishing of the morphisms out of `W` is invariant under isomorphism of the target. -/
instance (W : ℕᵒᵖ ⥤ D) : (homProVanishingProperty W).IsClosedUnderIsomorphisms where
  of_iso e h := HomProVanishing.of_iso h e

/-- The morphisms out of `W` pro-vanish into a zero object. -/
instance (W : ℕᵒᵖ ⥤ D) : (homProVanishingProperty W).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := D)
    exact ⟨Z, hZ, HomProVanishing.of_isZero W hZ⟩

/-- Pro-vanishing of the morphisms out of `W` is closed under extensions: in a distinguished
triangle it passes from the first and third vertices to the second. -/
instance (W : ℕᵒᵖ ⥤ D) : (homProVanishingProperty W).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ =>
    HomProVanishing.of_triangle T hT h₁ h₃

end Triangulated

/-! ### Dévissage along the truncations of a t-structure -/

section Devissage

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  (t : TStructure D)

private theorem prop_of_isGE_of_isLE_aux (P Q : ObjectProperty D)
    [P.IsTriangulatedClosed₂] [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hQLT : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncLT n).obj X))
    (hQGE : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncGE n).obj X))
    (hP : ∀ (n : ℤ) (Z : D), t.IsLE Z n → t.IsGE Z n → Q Z → P Z) (k : ℕ) :
    ∀ (a b : ℤ), b ≤ a + (k : ℤ) → ∀ E : D, t.IsGE E a → t.IsLE E b → Q E → P E := by
  induction k with
  | zero =>
    intro a b hba E hGE hLE hQ
    exact hP a E (t.isLE_of_le E b a (by omega)) hGE hQ
  | succ k ih =>
    intro a b hba E hGE hLE hQ
    refine P.ext_of_isTriangulatedClosed₂ _ (t.triangleLTGE_distinguished b E) ?_ ?_
    · exact ih a (b - 1) (by omega) ((t.truncLT b).obj E) inferInstance inferInstance
        (hQLT b E hQ)
    · exact hP b ((t.truncGE b).obj E) inferInstance inferInstance (hQGE b E hQ)

/-- **Dévissage of a triangulated object property along the canonical truncations, inside a
subcategory.** Let `Q` be any property of objects which the two canonical truncation functors
preserve. A property `P` which is closed under isomorphism, holds at a zero object and satisfies
two-out-of-three for distinguished triangles holds at every object of `Q` whose cohomology is
concentrated in finitely many degrees, as soon as it holds at every object *of `Q`* concentrated
in a single degree.

The point of the restriction is that the unrestricted hypothesis — `P` at every single-degree
object whatever — is frequently too strong to be dischargeable while the hypothesis restricted to
a subcategory is exactly what is available; see
`NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem`. The closure of `Q` under
`CategoryTheory.Triangulated.TStructure.truncLT` and
`CategoryTheory.Triangulated.TStructure.truncGE` is what makes the induction stay inside `Q`, and
it is the only thing asked of `Q`: no two-out-of-three, no isomorphism closure, no zero object.
Closure under `t.truncLE n = t.truncLT (n + 1)` is the same condition.

The induction is on `b - a` along the triangles `τ^{<b} E ⟶ E ⟶ τ^{≥b} E`: the first vertex is
concentrated in degrees `[a, b - 1]` and lies in `Q`, so the inductive hypothesis applies to it,
and the third is concentrated in the single degree `b` and lies in `Q`. The base case `b ≤ a` is
itself an object concentrated in one degree, `t.IsLE E b` forcing `t.IsLE E a`, so no separate
appeal to the zero object is needed — the zero object enters only through
`CategoryTheory.ObjectProperty.IsTriangulatedClosed₂`. -/
theorem prop_of_isGE_of_isLE_of_mem (P Q : ObjectProperty D)
    [P.IsTriangulatedClosed₂] [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hQLT : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncLT n).obj X))
    (hQGE : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncGE n).obj X))
    (hP : ∀ (n : ℤ) (Z : D), t.IsLE Z n → t.IsGE Z n → Q Z → P Z)
    (E : D) (a b : ℤ) (hGE : t.IsGE E a) (hLE : t.IsLE E b) (hQ : Q E) : P E :=
  prop_of_isGE_of_isLE_aux t P Q hQLT hQGE hP (b - a).toNat a b (by omega) E hGE hLE hQ

/-- **Dévissage of a triangulated object property along the canonical truncations.** A property
of objects which is closed under isomorphism, holds at a zero object and satisfies
two-out-of-three for distinguished triangles holds at every object whose cohomology is
concentrated in finitely many degrees, as soon as it holds at every object concentrated in a
single degree.

This is `NoetherianAdicCompletion.prop_of_isGE_of_isLE_of_mem` with no restricting subcategory,
`Q = ⊤`. -/
theorem prop_of_isGE_of_isLE (P : ObjectProperty D)
    [P.IsTriangulatedClosed₂] [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (n : ℤ) (Z : D), t.IsLE Z n → t.IsGE Z n → P Z)
    (E : D) (a b : ℤ) (hGE : t.IsGE E a) (hLE : t.IsLE E b) : P E :=
  prop_of_isGE_of_isLE_of_mem t P ⊤ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun n Z h₁ h₂ _ => hP n Z h₁ h₂) E a b hGE hLE trivial

/-- **Pro-vanishing into a target with bounded cohomology is a condition on the pieces of the
target.** If the morphisms out of `W` pro-vanish into every object concentrated in a single
degree, they pro-vanish into every object whose cohomology is concentrated in finitely many
degrees.

With `W_m = V ⊗^𝐋 ℐᵐ⁺¹` and the target a bounded complex with `ℐ`-power-torsion cohomology, this
is the reduction of the derived-torsion input of [Stacks, Tag 0A0K] part (1) to its single-degree
case. -/
theorem homProVanishing_of_isGE_of_isLE (W : ℕᵒᵖ ⥤ D)
    (hW : ∀ (n : ℤ) (Z : D), t.IsLE Z n → t.IsGE Z n → HomProVanishing W Z)
    (E : D) (a b : ℤ) (hGE : t.IsGE E a) (hLE : t.IsLE E b) : HomProVanishing W E :=
  prop_of_isGE_of_isLE t (homProVanishingProperty W) hW E a b hGE hLE

/-- **The torsion-restricted dévissage.** Let `Q` be a property of objects preserved by the two
canonical truncation functors. If the morphisms out of `W` pro-vanish into every object *of `Q`*
concentrated in a single degree, they pro-vanish into every object of `Q` whose cohomology is
concentrated in finitely many degrees.

`NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE` is the case `Q = ⊤`, and it is too
strong to be used in the intended application. With `W_m = V ⊗^𝐋 ℐᵐ⁺¹` the tensor–internal-Hom
adjunction turns the unrestricted hypothesis into pro-vanishing of
`Hom(ℐᵐ⁺¹, R𝑆heafHom(V, Z))` for an *arbitrary* single-degree `Z`; at `Z = 𝒪` that already fails,
the inclusion `ℐᵏ ⊆ 𝒪` being annihilated by no transition map unless `ℐ` is nilpotent. Taking for
`Q` a subcategory of `ℐ`-power-torsion objects removes exactly those targets, and the
single-degree hypothesis then becomes the sheaf-level degree-zero statement
`Stacks.Sites.homProVanishing_idealPowTower_singleFunctor` in degree zero.

Two mechanisms for the closure hypotheses are provided below:
`NoetherianAdicCompletion.app_truncLT_eq_zero_of_app_eq_zero` and its companion, for the
objects annihilated by a family of natural endomorphisms of the identity (uniform annihilation,
which is the form the Koszul application has it in and the form the sheaf-level base case
consumes), and `NoetherianAdicCompletion.isZero_map_truncLT_and_truncGE_of_isZero_map`, for the
objects killed by a family of `t`-exact triangulated functors (the form
`AlgebraicGeometry.RingedSite.DerivedPowerTorsion` is defined in). -/
theorem homProVanishing_of_isGE_of_isLE_of_mem (W : ℕᵒᵖ ⥤ D) (Q : ObjectProperty D)
    (hQLT : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncLT n).obj X))
    (hQGE : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncGE n).obj X))
    (hW : ∀ (n : ℤ) (Z : D), t.IsLE Z n → t.IsGE Z n → Q Z → HomProVanishing W Z)
    (E : D) (a b : ℤ) (hGE : t.IsGE E a) (hLE : t.IsLE E b) (hQ : Q E) :
    HomProVanishing W E :=
  prop_of_isGE_of_isLE_of_mem t (homProVanishingProperty W) Q hQLT hQGE hW E a b hGE hLE hQ

omit [IsTriangulated D] in
/-- **Pro-vanishing is automatic into a target strictly above the system.** If every term of the
inverse system `W` is concentrated in degrees `≤ c` and `Z` is concentrated in degrees `≥ n` for
some `n > c`, then `Hom(W_m, Z) = 0` outright — the orthogonality of the two halves of a
t-structure, `CategoryTheory.Triangulated.TStructure.zero` — and the pro-vanishing holds
vacuously, at the level `m` one starts from.

This is what makes the single-degree hypothesis of the dévissage free above the degrees the
system itself occupies; see
`NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem_of_isLE`. -/
theorem homProVanishing_of_lt {W : ℕᵒᵖ ⥤ D} (c n : ℤ) (hcn : c < n)
    (hW : ∀ m : ℕ, t.IsLE (W.obj (op m)) c) (Z : D) (hZ : t.IsGE Z n) :
    HomProVanishing W Z := fun m x =>
  ⟨m, le_rfl, by rw [t.zero_of_isLE_of_isGE x c n hcn (hW m) hZ, comp_zero]⟩

/-- **The dévissage needs the single-degree hypothesis only in the degrees the system occupies.**
`NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem` asks for pro-vanishing into
every single-degree object of `Q`, in every degree. If the terms of `W` are concentrated in
degrees `≤ c` then the degrees `> c` carry no nonzero morphism out of `W` at all
(`NoetherianAdicCompletion.homProVanishing_of_lt`), so only the degrees `≤ c` have to be
supplied.

For the tower of powers of a sheaf of ideals placed in degree zero this cuts the hypothesis down
to the degrees `≤ 0`, that is to `colim_m Ext^j(ℐᵐ⁺¹, -) = 0` for `j ≥ 0`: the degree `0` is the
base case `Stacks.Sites.homProVanishing_idealPowTower_singleFunctor` and the degrees `< 0`, the
higher `Ext`, are what remains. See
`Stacks.Sites.homProVanishing_idealPowTower_singleFunctor_of_isGE_of_isLE`. -/
theorem homProVanishing_of_isGE_of_isLE_of_mem_of_isLE (W : ℕᵒᵖ ⥤ D) (Q : ObjectProperty D)
    (c : ℤ) (hWLE : ∀ m : ℕ, t.IsLE (W.obj (op m)) c)
    (hQLT : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncLT n).obj X))
    (hQGE : ∀ (n : ℤ) (X : D), Q X → Q ((t.truncGE n).obj X))
    (hW : ∀ (n : ℤ), n ≤ c → ∀ Z : D, t.IsLE Z n → t.IsGE Z n → Q Z → HomProVanishing W Z)
    (E : D) (a b : ℤ) (hGE : t.IsGE E a) (hLE : t.IsLE E b) (hQ : Q E) :
    HomProVanishing W E :=
  homProVanishing_of_isGE_of_isLE_of_mem t W Q hQLT hQGE
    (fun n Z hZLE hZGE hQZ => if hn : n ≤ c then hW n hn Z hZLE hZGE hQZ
      else homProVanishing_of_lt t c n (by omega) hWLE Z hZGE) E a b hGE hLE hQ

end Devissage

/-! ### Subcategories the canonical truncations preserve -/

section TruncClosure

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (t : TStructure D)

/-- **A morphism into `τ^{<n} E` out of an object in degrees `≤ n - 1` is detected by its
composite into `E`.** Equivalently, composing with `τ^{<n} E ⟶ E` is injective on morphisms out
of such an object.

Such a morphism killed by the composite factors through `(τ^{≥n} E)⟦-1⟧`, by the coyoneda
exactness of the inverse rotation of the truncation triangle, and that object is in degrees
`≥ n + 1`, so the factor vanishes. -/
theorem eq_zero_of_comp_truncLTι_app_eq_zero (n : ℤ) (E : D) {A : D} [t.IsLE A (n - 1)]
    (f : A ⟶ (t.truncLT n).obj E) (hf : f ≫ (t.truncLTι n).app E = 0) : f = 0 := by
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _
    (inv_rot_of_distTriang _ (t.triangleLTGE_distinguished n E)) f hf
  have hg0 : g = 0 := by
    have : t.IsGE ((((t.triangleLTGE n).obj E).invRotate).obj₁) (n + 1) :=
      t.isGE_shift ((t.truncGE n).obj E) n (-1) (n + 1) (by omega)
    exact t.zero g (n - 1) (n + 1) (by omega)
  rw [hg0, zero_comp] at hg
  exact hg

/-- **A morphism out of `τ^{≥n} E` into an object in degrees `≥ n` is detected by its composite
from `E`.** Equivalently, composing with `E ⟶ τ^{≥n} E` is injective on morphisms into such an
object.

Such a morphism killed by the composite factors through `(τ^{<n} E)⟦1⟧`, by the yoneda exactness
of the truncation triangle, and that object is in degrees `≤ n - 2`, so the factor vanishes. -/
theorem eq_zero_of_truncGEπ_app_comp_eq_zero (n : ℤ) (E : D) {B : D} [t.IsGE B n]
    (f : (t.truncGE n).obj E ⟶ B) (hf : (t.truncGEπ n).app E ≫ f = 0) : f = 0 := by
  obtain ⟨g, hg⟩ :=
    Triangle.yoneda_exact₃ _ (t.triangleLTGE_distinguished n E) f hf
  have hg0 : g = 0 := by
    have : t.IsLE ((((t.triangleLTGE n).obj E).obj₁)⟦(1 : ℤ)⟧) (n - 2) :=
      t.isLE_shift ((t.truncLT n).obj E) (n - 1) 1 (n - 2) (by omega)
    exact t.zero g (n - 2) n (by omega)
  rw [hg0, comp_zero] at hg
  exact hg

/-- **The objects annihilated by a natural endomorphism of the identity are closed under
`τ^{<n}`.** For `u : 𝟭 D ⟶ 𝟭 D` — multiplication by a global scalar, in the application — the
naturality square at `τ^{<n} E ⟶ E` reads
`u_{τ^{<n}E} ≫ ι = ι ≫ u_E`, so `u_E = 0` forces `u_{τ^{<n}E} ≫ ι = 0`, and
`NoetherianAdicCompletion.eq_zero_of_comp_truncLTι_app_eq_zero` then forces `u_{τ^{<n}E} = 0`. -/
theorem app_truncLT_eq_zero_of_app_eq_zero (u : 𝟭 D ⟶ 𝟭 D) (n : ℤ) (E : D) (hu : u.app E = 0) :
    u.app ((t.truncLT n).obj E) = 0 := by
  have h := u.naturality ((t.truncLTι n).app E)
  dsimp at h
  refine eq_zero_of_comp_truncLTι_app_eq_zero t n E (A := (t.truncLT n).obj E)
    (u.app ((t.truncLT n).obj E)) ?_
  rw [← h, hu, comp_zero]

/-- **The objects annihilated by a natural endomorphism of the identity are closed under
`τ^{≥n}`.** The companion of
`NoetherianAdicCompletion.app_truncLT_eq_zero_of_app_eq_zero`, read off the naturality square at
`E ⟶ τ^{≥n} E`. -/
theorem app_truncGE_eq_zero_of_app_eq_zero (u : 𝟭 D ⟶ 𝟭 D) (n : ℤ) (E : D) (hu : u.app E = 0) :
    u.app ((t.truncGE n).obj E) = 0 := by
  have h := u.naturality ((t.truncGEπ n).app E)
  dsimp at h
  refine eq_zero_of_truncGEπ_app_comp_eq_zero t n E (B := (t.truncGE n).obj E)
    (u.app ((t.truncGE n).obj E)) ?_
  rw [h, hu, zero_comp]

end TruncClosure

/-! ### The dévissage inside a subcategory of annihilated objects -/

section AnnihilatedDevissage

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  (t : TStructure D)

/-- **The dévissage restricted to the objects annihilated by a family of scalars.** Let
`u : ι → (𝟭 D ⟶ 𝟭 D)` be a family of natural endomorphisms of the identity — in the application,
multiplication by a finite family of global sections generating a power of `ℐ`. If the morphisms
out of `W` pro-vanish into every single-degree object annihilated by all the `u i`, they
pro-vanish into every object annihilated by all the `u i` whose cohomology is concentrated in
finitely many degrees.

This is `NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem` with the uniform
annihilation condition for `Q`, whose closure under the truncations is
`NoetherianAdicCompletion.app_truncLT_eq_zero_of_app_eq_zero` and its companion. The uniform form
is the one the Koszul application supplies — multiplication by each member of the defining family
is null-homotopic on a Koszul complex
(`Stacks.Sheaves.KoszulGlobalSections.koszulSmulNullHomotopic`), so for a dual Koszul complex
`V = (Kⁿ)^∨` the identity `𝟙_V` is annihilated by the ideal generated by the `f_i^{n+1}`, and
additivity in the first variable passes that annihilator to every `R𝑆heafHom(V, Z)` — and it is
the one the sheaf-level base case
`Stacks.Sites.homProVanishing_idealPowTower` consumes, that result asking for a target killed by
a single power `ℐᴺ` rather than for sections each killed by some power. -/
theorem homProVanishing_of_isGE_of_isLE_of_app_eq_zero (W : ℕᵒᵖ ⥤ D)
    {ι : Type*} (u : ι → (𝟭 D ⟶ 𝟭 D))
    (hW : ∀ (n : ℤ) (Z : D), t.IsLE Z n → t.IsGE Z n → (∀ i, (u i).app Z = 0) →
      HomProVanishing W Z)
    (E : D) (a b : ℤ) (hGE : t.IsGE E a) (hLE : t.IsLE E b)
    (hE : ∀ i, (u i).app E = 0) : HomProVanishing W E :=
  homProVanishing_of_isGE_of_isLE_of_mem t W (fun Z => ∀ i, (u i).app Z = 0)
    (fun n X hX i => app_truncLT_eq_zero_of_app_eq_zero t (u i) n X (hX i))
    (fun n X hX i => app_truncGE_eq_zero_of_app_eq_zero t (u i) n X (hX i))
    hW E a b hGE hLE hE

end AnnihilatedDevissage

/-! ### The dévissage inside the kernel of a `t`-exact functor -/

section KernelDevissage

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {D' : Type u'} [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  (t : TStructure D) (t' : TStructure D')

/-- **The kernel of a `t`-exact triangulated functor is closed under both canonical
truncations.** Let `F : D ⥤ D'` be triangulated and `t`-exact, in the sense that it preserves
both bounds `t.IsLE` and `t.IsGE`. If `F E = 0` then `F` kills both truncations of `E`.

Applying `F` to `τ^{<n} E ⟶ E ⟶ τ^{≥n} E` gives a distinguished triangle with vanishing middle
vertex, so its connecting morphism is an isomorphism `F(τ^{≥n} E) ≅ F(τ^{<n} E)⟦1⟧`. The source
is in degrees `≥ n` and the target in degrees `≤ n - 2`, so both are zero.

This is the closure hypothesis of
`NoetherianAdicCompletion.homProVanishing_of_isGE_of_isLE_of_mem` for a subcategory presented as
the vanishing locus of a family of functors, which is the shape
`AlgebraicGeometry.RingedSite.DerivedPowerTorsion` is written in: the vanishing of the derived
localizations `𝒪_{f_i} ⊗^𝐋_𝒪 -`. Those functors are `t`-exact, `𝒪_{f_i}` being flat over `𝒪`
(`AlgebraicGeometry.RingedSite.isFlatMap_toAwaySheaf`), and that is the content of
`AlgebraicGeometry.RingedSite.derivedPowerTorsion_iff`, which through
`Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso` reads the torsion condition off the
cohomology sheaves one degree at a time. What this development does **not** have is a
`CategoryTheory.Functor.CommShift ℤ` and a `CategoryTheory.Functor.IsTriangulated` for those
partially applied derived tensor functors — only the homotopy-category descent
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated` — so the hypotheses here are
not discharged for them below, and the instantiation is left to the consumer. -/
theorem isZero_map_truncLT_and_truncGE_of_isZero_map (F : D ⥤ D') [F.CommShift ℤ]
    [F.IsTriangulated]
    (hLE : ∀ (n : ℤ) (X : D), t.IsLE X n → t'.IsLE (F.obj X) n)
    (hGE : ∀ (n : ℤ) (X : D), t.IsGE X n → t'.IsGE (F.obj X) n)
    (n : ℤ) (E : D) (hE : IsZero (F.obj E)) :
    IsZero (F.obj ((t.truncLT n).obj E)) ∧ IsZero (F.obj ((t.truncGE n).obj E)) := by
  have hT : F.mapTriangle.obj ((t.triangleLTGE n).obj E) ∈ distTriang D' :=
    F.map_distinguished _ (t.triangleLTGE_distinguished n E)
  have hiso : IsIso (F.mapTriangle.obj ((t.triangleLTGE n).obj E)).mor₃ :=
    (Triangle.isZero₂_iff_isIso₃ _ hT).1 hE
  have e : F.obj ((t.truncGE n).obj E) ≅ (F.obj ((t.truncLT n).obj E))⟦(1 : ℤ)⟧ :=
    @asIso D' _ _ _ (F.mapTriangle.obj ((t.triangleLTGE n).obj E)).mor₃ hiso
  have h₁ : t'.IsLE (F.obj ((t.truncLT n).obj E)) (n - 1) := hLE (n - 1) _ inferInstance
  have h₃ : t'.IsGE (F.obj ((t.truncGE n).obj E)) n := hGE n _ inferInstance
  have hs : t'.IsGE ((F.obj ((t.truncLT n).obj E))⟦(1 : ℤ)⟧) n := t'.isGE_of_iso e n
  have hge : t'.IsGE (F.obj ((t.truncLT n).obj E)) (n + 1) :=
    t'.isGE_of_shift (F.obj ((t.truncLT n).obj E)) (n + 1) 1 n (by omega)
  have hl : t'.IsLE ((F.obj ((t.truncLT n).obj E))⟦(1 : ℤ)⟧) (n - 2) :=
    t'.isLE_shift (F.obj ((t.truncLT n).obj E)) (n - 1) 1 (n - 2) (by omega)
  have hl' : t'.IsLE (F.obj ((t.truncGE n).obj E)) (n - 2) := t'.isLE_of_iso e.symm (n - 2)
  exact ⟨t'.isZero _ (n - 1) (n + 1) (by omega), t'.isZero _ (n - 2) n (by omega)⟩

end KernelDevissage

/-! ### Eventual inverses from one pro-vanishing hypothesis -/

section Application

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] {V : D} {G W : ℕᵒᵖ ⥤ D}

/-- **Eventual inverses for the augmentation of a constant tower, from one pro-vanishing
hypothesis.** Let `φ : (Functor.const ℕᵒᵖ).obj V ⟶ G` be presented by a functorial family of
distinguished triangles `W_m ⟶ V ⟶ G_m ⟶ (W_m)⟦1⟧`, the maps `ψ` and `δ` being morphisms of
inverse systems. Then `φ` has eventual inverses as soon as the morphisms out of `W` pro-vanish
into `V` and into every `W_n`.

This refines `NoetherianAdicCompletion.hasEventualInverses_const_of_triangles`, whose two
hypotheses it produces — and only in that direction: the hypotheses here are strictly stronger,
asking a vanishing of *every* morphism out of the system rather than of the two structural ones.
The first is immediate: `ψ_m` is the image of `ψ_n` under a transition
map, so pro-vanishing into `V` kills it outright at some later level, and it stays zero
afterwards. For the second, fix `n` and write `y_m = G.map (hm).op ≫ δ_n`. Naturality of `φ` on a
constant source gives `φ_m ≫ y_m = φ_n ≫ δ_n = 0`, so `y_m` factors as `δ_m ≫ g` with
`g : (W_m)⟦1⟧ ⟶ (W_n)⟦1⟧`; the shift is an equivalence, so `g` is the shift of a morphism
`W_m ⟶ W_n`, which pro-vanishing into `W_n` kills at a later level; naturality of `δ` then shows
`y` itself vanishes at that level.

What the argument does **not** do is supply the pro-vanishing. On the tower of [Stacks, Tag 0A0K]
part (1) that is the derived `ℐ`-torsion statement, which the library does not have for sheaves on
a ringed site; see the module documentation. -/
theorem hasEventualInverses_const_of_homProVanishing
    (φ : (Functor.const ℕᵒᵖ).obj V ⟶ G) (ψ : W ⟶ (Functor.const ℕᵒᵖ).obj V)
    (δ : G ⟶ W ⋙ shiftFunctor D (1 : ℤ))
    (hT : ∀ m : ℕ, Triangle.mk (ψ.app (op m)) (φ.app (op m)) (δ.app (op m)) ∈ distTriang D)
    (hV : HomProVanishing W V) (hW : ∀ n : ℕ, HomProVanishing W (W.obj (op n))) :
    HasEventualInverses φ := by
  have hψnat : ∀ {a b : ℕ} (h : a ≤ b),
      W.map (homOfLE h).op ≫ ψ.app (op a) = ψ.app (op b) := by
    intro a b h
    simp
  have hφnat : ∀ {a b : ℕ} (h : a ≤ b),
      φ.app (op b) ≫ G.map (homOfLE h).op = φ.app (op a) := by
    intro a b h
    have := φ.naturality (homOfLE h).op
    simpa using this.symm
  refine hasEventualInverses_const_of_triangles φ (fun m => W.obj (op m))
    (fun m => ψ.app (op m)) (fun m => δ.app (op m)) hT fun n => ?_
  -- First: a level at which `ψ` vanishes.
  obtain ⟨m₁, hm₁, h1⟩ := hV n (ψ.app (op n))
  -- Second: a later level at which the transition composed with `δ n` vanishes.
  have hφy : φ.app (op m₁) ≫ (G.map (homOfLE hm₁).op ≫ δ.app (op n)) = 0 := by
    rw [← Category.assoc, hφnat hm₁]
    exact comp_distTriang_mor_zero₂₃ _ (hT n)
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (hT m₁)
    (G.map (homOfLE hm₁).op ≫ δ.app (op n)) hφy
  obtain ⟨g₀, hg₀⟩ := (shiftFunctor D (1 : ℤ)).map_surjective g
  obtain ⟨m₂, hm₂, hg'⟩ := hW n m₁ g₀
  refine ⟨m₂, hm₁.trans hm₂, ?_, ?_⟩
  · rw [← hψnat (hm₁.trans hm₂)]
    exact HomProVanishing.comp_eq_zero_of_le hm₁ hm₂ h1
  · rw [← map_homOfLE_op_comp G hm₂ hm₁, Category.assoc, hg, ← Category.assoc]
    simp only [Triangle.mk_mor₃]
    rw [δ.naturality (homOfLE hm₂).op, Functor.comp_map, Category.assoc, ← hg₀,
      ← Functor.map_comp, hg', Functor.map_zero, comp_zero]

end Application

end NoetherianAdicCompletion

end
