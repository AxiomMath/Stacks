module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsLeftExact
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap

/-!
# Global sections of the sequence of a sum of divisors

Let `D` be an effective Cartier divisor on a scheme `X` and let `C` be an ideal sheaf with
`C · D ≤ D`. The sequence of [Stacks, Tag 0C4T]

`0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{C + D} ⟶ 𝒪_D ⟶ 0`

is short exact, with its kernel inclusion named `Stacks.Divisors.sumKernelMap`
(`Stacks.Divisors.shortExact_sumKernelMap`). This file records what taking global sections does
to it on the left: the kernel inclusion stays injective, and a global function on `C + D`
restricting to zero on `D` is the image of a global section of `𝒪_X(-D)|_C`.

Both statements are unconditional. The surjectivity on the right is not — it needs
`H¹(X, 𝒪_X(-D)|_C)` to vanish, and that is
`AlgebraicGeometry.Scheme.IdealSheafData.surjective_inclusion_appTop`. What is used here is only
the left exactness of `Γ(X, -)`, through
`Stacks.Cohomology.injective_sections_of_shortExact` and
`Stacks.Cohomology.exists_sections_of_sections_eq_zero`.

Together the two statements say that `Γ(X, 𝒪_X(-D)|_C)` *is* the kernel of the restriction
`Γ(𝒪_{C + D}) ⟶ Γ(𝒪_D)`, and they say it about the named morphism rather than about some
morphism with the right kernel. That distinction is the point: a statement about an
existentially bound isomorphism cannot be composed with anything, whereas these can be
multiplied. The intended consumer is the graded piece `Iₙ / Iₙ₊₁` of the formal neighbourhood of
an exceptional curve, where the identification has to be compatible with multiplication across
all pairs of degrees before it can produce the monomial structure that [Stacks, Tag 0C2K]
computes with.

## Main results

* `Stacks.Divisors.injective_sumKernelMap_appTop` — the kernel inclusion is injective on global
  sections.
* `Stacks.Divisors.exists_sumKernelMap_appTop_eq` — a global function on the sum whose
  restriction vanishes is the image of a global section of the twisted ideal sheaf.
* `Stacks.Divisors.exists_sumKernelMap_appTop_eq_of_inclusion_appTop_eq_zero` — the same, with
  the hypothesis written through the inclusion of subschemes, which is the spelling in which
  `AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestriction` is defined.
* `Stacks.Divisors.appTop_sumKernelMap_smul_eq_mul` — **the kernel inclusion is semilinear over
  the restriction of scalars `Γ(C + D, 𝒪) ⟶ Γ(C, 𝒪)`**: it carries the action of a global
  function on the sum, acting through its restriction to `C`, to multiplication by that function.
  It is the instance at the kernel inclusion of
  `AlgebraicGeometry.Scheme.IdealSheafData.app_smul_eq_mul_of_app_eq`, which says the same for an
  arbitrary morphism of `𝒪_X`-modules into the direct image of the structure sheaf of a closed
  subscheme, and of its two specialisations
  `AlgebraicGeometry.Scheme.IdealSheafData.app_smul_eq_mul_of_closedSubschemeRestriction_app` and
  `AlgebraicGeometry.Scheme.IdealSheafData.appTop_smul_eq_mul_of_appTop_inclusion`.
* `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction_app_subschemeι_app` — the
  restriction between nested closed subschemes agrees with the two structure-sheaf maps out of
  the ambient scheme, on sections over any open.

## Main definitions

* `Stacks.Divisors.sumKernelMapOf` — the kernel inclusion with its target renamed along an
  equality of ideal sheaves, and `Stacks.Divisors.thickeningKernelMap` its value at the
  thickenings of a divisor, where the sum is `D ^ (n + 2)`.

The two statements above transported to the thickenings are
`Stacks.Divisors.injective_thickeningKernelMap_appTop` and
`Stacks.Divisors.exists_thickeningKernelMap_appTop_eq`; together they identify
`Γ(X, 𝒪_X(-(n + 1)E)|_E)` with `RingHom.ker (thickeningRestriction D n)`.

## References

* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **The kernel inclusion of the sequence of a sum of divisors is injective on global
sections.** A global section of `𝒪_X(-D)|_C` is determined by the global function it induces on
`C + D`.

This is the left exactness of `Γ(X, -)` at the short exact sequence
`Stacks.Divisors.shortExact_sumKernelMap`; no cohomology vanishes to make it true. -/
theorem injective_sumKernelMap_appTop (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) :
    Function.Injective fun m : Γ((Scheme.Modules.pushforward C.subschemeι).obj
          ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), (⊤ : X.Opens)) =>
      (sumKernelMap D C hD).app ⊤ m :=
  Stacks.Cohomology.injective_sections_of_shortExact X ⊤ (shortExact_sumKernelMap D C hD hsub)

/-- **A global function on the sum restricting to zero comes from the twisted ideal sheaf.** If a
global function on `C + D` restricts to zero on `D`, it is the image under
`Stacks.Divisors.sumKernelMap` of a global section of `𝒪_X(-D)|_C`.

With `Stacks.Divisors.injective_sumKernelMap_appTop` this identifies `Γ(X, 𝒪_X(-D)|_C)` with the
kernel of the restriction. -/
theorem exists_sumKernelMap_appTop_eq (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D)
    (x : Γ(closedSubschemeStructureSheaf (C * D), (⊤ : X.Opens)))
    (hx : (closedSubschemeRestriction hsub).app ⊤ x = 0) :
    ∃ a : Γ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), (⊤ : X.Opens)),
      (sumKernelMap D C hD).app ⊤ a = x :=
  Stacks.Cohomology.exists_sections_of_sections_eq_zero X ⊤
    (shortExact_sumKernelMap D C hD hsub) x hx

/-- **The same, with the restriction written as the structure-sheaf map of an inclusion of
subschemes.** `AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestriction` is defined as
`(inclusion h).appTop`, so this is the form in which a statement about the thickenings of a
divisor meets the sequence. The two spellings agree by
`AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction_appTop`. -/
theorem exists_sumKernelMap_appTop_eq_of_inclusion_appTop_eq_zero (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D)
    (x : Γ(closedSubschemeStructureSheaf (C * D), (⊤ : X.Opens)))
    (hx : (inclusion hsub).appTop x = 0) :
    ∃ a : Γ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), (⊤ : X.Opens)),
      (sumKernelMap D C hD).app ⊤ a = x :=
  exists_sumKernelMap_appTop_eq D C hD hsub x
    ((closedSubschemeRestriction_appTop hsub x).trans hx)

/-! ### The sequence at a sum presented under another name

`Stacks.Divisors.sumKernelMap` has the product `C · D` in its type. A consumer indexing the
infinitesimal thickenings of a divisor by their exponent meets `D ^ (n + 2)` instead, and
`D · D ^ (n + 1) = D ^ (n + 2)` is an equality of ideal sheaves which is not a definitional one,
so the two spellings are not interchangeable and the transport has to be named.

The transport is a plain definition rather than an `abbrev`, and that matters. `sumKernelMap` is
itself `@[no_expose]`: its body is the descent of a morphism along the cokernel of a short exact
sequence, which no consumer should reduce through. A *reducible* transport of it defeats that —
unification unfolds the transport and then the descent, and checking either of the thickening
statements below against its specialisation then exceeded the kernel's reduction budget, twice.
A plain definition together with one rewrite by the defining equation
(`Stacks.Divisors.thickeningKernelMap_eq`) discharges both in seconds. Marking the transport
`@[no_expose]` instead does not work: the defining equation is itself exported, so proving it
needs the body visible. -/

/-- **The kernel inclusion of the sequence of [Stacks, Tag 0C4T], with its target renamed along
an equality of ideal sheaves.** For `hsum : C · D = D'` this is
`Stacks.Divisors.sumKernelMap` followed by the transport of its target from `C · D` to `D'`. -/
public noncomputable def sumKernelMapOf (D C D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsum : C * D = D') :
    (Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)) ⟶
      closedSubschemeStructureSheaf D' :=
  sumKernelMap D C hD ≫ eqToHom (congrArg closedSubschemeStructureSheaf hsum)

/-- At the sum as the sequence itself spells it, the renaming is the identity. -/
public theorem sumKernelMapOf_rfl (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) :
    sumKernelMapOf D C (C * D) hD rfl = sumKernelMap D C hD := by
  rw [sumKernelMapOf, eqToHom_refl, Category.comp_id]

/-- **The renamed kernel inclusion is injective on global sections.** -/
public theorem injective_sumKernelMapOf_appTop (D C D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsum : C * D = D') (hsub : D' ≤ D) :
    Function.Injective fun m : Γ((Scheme.Modules.pushforward C.subschemeι).obj
          ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), (⊤ : X.Opens)) =>
      (sumKernelMapOf D C D' hD hsum).app ⊤ m := by
  subst hsum
  rw [sumKernelMapOf_rfl]
  exact injective_sumKernelMap_appTop D C hD hsub

/-- **A global function on the sum restricting to zero comes from the twisted ideal sheaf**, for
the sum presented under any name equal to `C · D`. -/
public theorem exists_sumKernelMapOf_appTop_eq (D C D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsum : C * D = D') (hsub : D' ≤ D)
    (x : Γ(closedSubschemeStructureSheaf D', (⊤ : X.Opens)))
    (hx : (inclusion hsub).appTop x = 0) :
    ∃ a : Γ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D)), (⊤ : X.Opens)),
      (sumKernelMapOf D C D' hD hsum).app ⊤ a = x := by
  subst hsum
  rw [sumKernelMapOf_rfl]
  exact exists_sumKernelMap_appTop_eq_of_inclusion_appTop_eq_zero D C hD hsub x hx

/-! ### The sequence at the infinitesimal thickenings of a divisor -/

/-- Multiplying by `D` once more raises the exponent: `D · D ^ (n + 1) = D ^ (n + 2)`. -/
public theorem mul_pow_succ_eq (D : X.IdealSheafData) (n : ℕ) :
    D * D ^ (n + 1) = D ^ (n + 2) :=
  (mul_comm D (D ^ (n + 1))).trans (pow_succ D (n + 1)).symm

/-- **The kernel inclusion of [Stacks, Tag 0C4T] at the thickenings of an effective Cartier
divisor**: `𝒪_X(-(n + 1)E)|_E ⟶ 𝒪_{Eₙ₊₂}`, the sequence's named kernel inclusion for
`D ^ (n + 2) = D · D ^ (n + 1)`. -/
public noncomputable def thickeningKernelMap (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    (Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))) ⟶
      closedSubschemeStructureSheaf (D ^ (n + 2)) :=
  sumKernelMapOf (D ^ (n + 1)) D (D ^ (n + 2)) inferInstance (mul_pow_succ_eq D n)

/-- The thickening kernel inclusion is the sequence's, at `D ^ (n + 1)` and `D`. -/
public theorem thickeningKernelMap_eq (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    thickeningKernelMap D n =
      sumKernelMapOf (D ^ (n + 1)) D (D ^ (n + 2)) inferInstance (mul_pow_succ_eq D n) :=
  rfl

/-- **Global sections of `𝒪_X(-(n + 1)E)|_E` inject into global functions on the `(n + 2)`-nd
thickening.** -/
public theorem injective_thickeningKernelMap_appTop (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    Function.Injective fun m : Γ((Scheme.Modules.pushforward D.subschemeι).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))),
        (⊤ : X.Opens)) => (thickeningKernelMap D n).app ⊤ m := by
  rw [thickeningKernelMap_eq]
  exact injective_sumKernelMapOf_appTop (D ^ (n + 1)) D (D ^ (n + 2)) inferInstance
    (mul_pow_succ_eq D n) (pow_succ_le_pow_succ D (Nat.le_succ n))

/-- **The kernel of restriction between successive thickenings is the global sections of the
twisted ideal sheaf.** A global function on the `(n + 2)`-nd infinitesimal thickening of `D`
which restricts to zero on the `(n + 1)`-st is the image under
`Stacks.Divisors.thickeningKernelMap` of a global section of `𝒪_X(-(n + 1)E)|_E`.

With `Stacks.Divisors.injective_thickeningKernelMap_appTop` this identifies
`Γ(X, 𝒪_X(-(n + 1)E)|_E)` with `RingHom.ker (thickeningRestriction D n)`. It is the graded piece
of the formal neighbourhood of `D`, the object whose multiplicative structure across all pairs of
degrees is what [Stacks, Tag 0C2K] computes with. -/
public theorem exists_thickeningKernelMap_appTop_eq (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ)
    (x : Γ(thickening D (n + 1), (⊤ : (thickening D (n + 1)).Opens)))
    (hx : thickeningRestriction D n x = 0) :
    ∃ a : Γ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))),
      (⊤ : X.Opens)), (thickeningKernelMap D n).app ⊤ a = x := by
  rw [thickeningKernelMap_eq]
  exact exists_sumKernelMapOf_appTop_eq (D ^ (n + 1)) D (D ^ (n + 2)) inferInstance
    (mul_pow_succ_eq D n) (pow_succ_le_pow_succ D (Nat.le_succ n)) x hx

end Stacks.Divisors

/-! ### The kernel inclusion is semilinear over the functions on the sum

`Stacks.Divisors.sumKernelMap` runs from a module pushed forward from `C` to the structure sheaf
of `C + D`. Its source therefore carries an action of the global functions on `C` and its target
is a ring, and the two are linked by the restriction of scalars `Γ(C + D, 𝒪) ⟶ Γ(C, 𝒪)` along the
inclusion of `C` into `C + D`. What follows says that the kernel inclusion turns that action into
multiplication,

`sumKernelMap (ι^# t • w) = t * sumKernelMap w`,

which is the multiplicativity a graded piece of a formal neighbourhood asks of the identification
recorded above: the scalar is a function on the thickening, and the kernel of the restriction is
a module over it only once this is known.

The proof needs the kernel inclusion to be a morphism of `𝒪_X`-modules and needs nothing else of
it, so it is proved for an arbitrary such morphism and specialised afterwards. The reason it
holds is local. Over an affine open `V` of `X` the function `t` is the image of a function `a` on
`V` under the structure-sheaf map of a closed immersion, which is surjective there; the
restricted scalar `ι^# t` then acts on sections of the direct image exactly as `a` does, and a
morphism of `𝒪_X`-modules commutes with the action of `a`. Both sides are sections of a sheaf on
`X`, so agreement on a cover by affine opens is agreement.

**The value of the morphism is named rather than written twice.** `Γ(I.subscheme, ⊤)` and
`Γ(closedSubschemeStructureSheaf I, ⊤)` are the same type, but the `Mul` instance is found for
the first spelling and `Scheme.Modules.Hom.app` produces the second, so the product
`t * sumKernelMap w` cannot be written down — the elaborator looks for `HMul` across the two
spellings and finds none. Each statement below therefore takes the value as a variable `x`
together with the equation `hx` that defines it. That is the same assertion, and it is also the
shape in which a consumer meets it: `Stacks.Divisors.exists_thickeningKernelMap_appTop_eq` hands
out exactly such an `x` with such an `hx`.

**The closed subscheme is abstracted before anything is proved, and that is not cosmetic.** A
section of `closedSubschemeStructureSheaf I` and a global function on `I.subscheme` are
interchangeable after `I.subscheme` is unfolded to the colimit that glues it, and a proof that
asks the kernel for a handful of those comparisons exhausts its reduction budget at
the stage where the restriction of scalars enters. Carried out for a variable scheme `Z` and a
variable closed immersion `Z ⟶ X` the same comparisons are immediate, and the single instance at
`I.subscheme` is paid in the specialisation. -/

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Restricting a section of a pushed-forward module is restricting it as a section of the
module. -/
private lemma pushforward_presheaf_map_apply {Y : Scheme.{u}} (i : Y ⟶ X) (P : Y.Modules)
    {U V : X.Opens} (hVU : V ≤ U) (m : Γ(P, i ⁻¹ᵁ U)) :
    ((Scheme.Modules.pushforward i).obj P).presheaf.map (homOfLE hVU).op m =
      P.presheaf.map (homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from fun _ hz => hVU hz)).op m := rfl

/-- A function on the ambient scheme acts on a section of a pushed-forward module through the
structure-sheaf map of the morphism. -/
private lemma pushforward_smul_apply {Y : Scheme.{u}} (i : Y ⟶ X) (P : Y.Modules) (U : X.Opens)
    (a : Γ(X, U)) (m : Γ((Scheme.Modules.pushforward i).obj P, U)) (m' : Γ(P, i ⁻¹ᵁ U))
    (hm : m = m') : a • m = i.app U a • m' := by
  subst hm; rfl

/-- Restricting a section of a pushed-forward structure sheaf is restricting the function. -/
private lemma unit_pushforward_presheaf_map_apply {Z : Scheme.{u}} (i : Z ⟶ X) {U V : X.Opens}
    (hVU : V ≤ U) (z : Γ(Z, i ⁻¹ᵁ U)) :
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (homOfLE hVU).op z =
      Z.presheaf.map (homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from fun _ hy => hVU hy)).op z := rfl

/-- A function on the ambient scheme acts on a pushed-forward structure sheaf by multiplication
by its image under the structure-sheaf map of the morphism. -/
private lemma unit_pushforward_smul_apply {Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens)
    (a : Γ(X, U))
    (z : Γ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf), U))
    (z' : Γ(Z, i ⁻¹ᵁ U)) (hz : z = z') : a • z = i.app U a * z' := by
  subst hz; rfl

/-- A morphism of `𝒪_X`-modules commutes with the restriction maps, on sections. -/
private lemma map_app_apply {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (hVU : V ≤ U)
    (m : Γ(M, U)) :
    N.presheaf.map (homOfLE hVU).op (φ.app U m) =
      φ.app V (M.presheaf.map (homOfLE hVU).op m) := by
  have hnat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hVU).op) m
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op,
    ConcreteCategory.comp_apply] at hnat
  exact hnat.symm

private lemma unitToPushforward_app_apply' {Y Z : Scheme.{u}} (r : Y ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) :
    Scheme.Modules.Hom.app (M := SheafOfModules.unit Z.ringCatSheaf)
      (N := (Scheme.Modules.pushforward r).obj (SheafOfModules.unit Y.ringCatSheaf))
      (SheafOfModules.unitToPushforwardObjUnit r.toRingCatSheafHom) U a = r.app U a := rfl

/-- **The restriction between nested closed subschemes agrees with the structure-sheaf maps out
of the ambient scheme.** For `I ≤ J` and a function `a` over an open `U` of `X`, carrying `a` to
the subscheme cut out by `I` and restricting to the one cut out by `J` is carrying `a` to the
latter directly.

This is `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction_appTop` over an
arbitrary open rather than over the whole space. The statement over an arbitrary open cannot be
written with `AlgebraicGeometry.Scheme.IdealSheafData.inclusion` on the right, because
`inclusion h ≫ I.subschemeι` and `J.subschemeι` take different preimages of `U` and the two
sides would not be of the same type; through the structure-sheaf maps the preimages agree and the
equality of the two composites is what is being used. -/
theorem closedSubschemeRestriction_app_subschemeι_app {I J : X.IdealSheafData} (h : I ≤ J)
    (U : X.Opens) (a : Γ(X, U)) :
    (closedSubschemeRestriction h).app U (I.subschemeι.app U a) = J.subschemeι.app U a := by
  rw [closedSubschemeRestriction]
  refine Eq.trans (comp_app_apply _ _ U _) ?_
  refine Eq.trans (comp_app_apply _ _ U _) ?_
  refine eqToHom_app_heq _ U _ _ ?_
  refine HEq.trans (heq_of_eq ?_) (heq_scheme_app (inclusion_subschemeι h) U a)
  refine Eq.trans (pushforwardComp_app_apply _ _ _ U _) ?_
  refine Eq.trans (pushforward_map_app_apply _ _ U _) ?_
  refine Eq.trans (unitToPushforward_app_apply' (inclusion h) (I.subschemeι ⁻¹ᵁ U) _) ?_
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_app (inclusion h) I.subschemeι U) a).symm

/-- **A morphism of `𝒪_X`-modules into the direct image of the structure sheaf of a closed
subscheme is semilinear over the restriction of scalars.** Let `iZ : Z ⟶ X` be a closed immersion
and `iY : Y ⟶ X` any morphism of schemes. Let `ρ : iZ_* 𝒪_Z ⟶ iY_* 𝒪_Y` be a morphism of
`𝒪_X`-modules which sends the image on `Z` of a function on `X` to its image on `Y`, and let
`ψ : iY_* P ⟶ iZ_* 𝒪_Z` be any morphism of `𝒪_X`-modules out of a direct image from `Y`. Then
`ψ` carries the action of `t : Γ(Z, iZ⁻¹U)` through `ρ` to multiplication by `t`.

Over an affine open `V` the function `t` is the image of a function `a` on `V`, because the
structure-sheaf map of a closed immersion is surjective over an affine open; the scalar `ρ t`
then acts on sections of `iY_* P` over `V` exactly as `a` does, and `ψ` commutes with the action
of `a` because it is a morphism of `𝒪_X`-modules. Both sides are sections of a sheaf, so this is
enough.

The value `ψ.app U w` is taken as a variable `x` with the equation `hx` defining it; see the
section introduction for why the product cannot be written with that value in place. -/
theorem app_smul_eq_mul_of_app_eq {Y Z : Scheme.{u}} (iY : Y ⟶ X) (iZ : Z ⟶ X)
    [IsClosedImmersion iZ]
    (ρ : (Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward iY).obj (SheafOfModules.unit Y.ringCatSheaf))
    (hρ : ∀ (W : X.Opens) (a : Γ(X, W)), ρ.app W (iZ.app W a) = iY.app W a) (P : Y.Modules)
    (ψ : (Scheme.Modules.pushforward iY).obj P ⟶
      (Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf))
    (U : X.Opens) (t : Γ(Z, iZ ⁻¹ᵁ U)) (s : Γ(Y, iY ⁻¹ᵁ U)) (hs : ρ.app U t = s)
    (w : Γ(P, iY ⁻¹ᵁ U)) {x : Γ(Z, iZ ⁻¹ᵁ U)} (hx : ψ.app U w = x) :
    ψ.app U (s • w) = t * x := by
  refine ((Scheme.Modules.pushforward iZ).obj
    (SheafOfModules.unit Z.ringCatSheaf)).isSheaf.section_ext (U := Opposite.op U) ?_
  intro y hy
  obtain ⟨V, hVaff, hyV, hVU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hy
  refine ⟨V, hVU, hyV, ?_⟩
  have hle : ∀ {W : Scheme.{u}} (f : W ⟶ X), f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := fun _ _ hz => hVU hz
  obtain ⟨a, ha⟩ := Scheme.Hom.app_surjective iZ V hVaff
    (Z.presheaf.map (homOfLE (hle iZ)).op t)
  have hsV : Y.presheaf.map (homOfLE (hle iY)).op s =
      iY.app V a :=
    (congrArg (fun r => Y.presheaf.map
          (homOfLE (hle iY)).op r) hs).symm.trans
      ((unit_pushforward_presheaf_map_apply iY hVU _).symm.trans
        ((map_app_apply ρ hVU t).trans
          ((congrArg (fun z => ρ.app V z)
              ((unit_pushforward_presheaf_map_apply iZ hVU t).trans ha.symm)).trans
            (hρ V a))))
  have hres : ψ.app V (((Scheme.Modules.pushforward iY).obj P).presheaf.map (homOfLE hVU).op w) =
      Z.presheaf.map (homOfLE (hle iZ)).op x :=
    (map_app_apply ψ hVU w).symm.trans
      ((congrArg (fun z => ((Scheme.Modules.pushforward iZ).obj
            (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map (homOfLE hVU).op z) hx).trans
        (unit_pushforward_presheaf_map_apply iZ hVU x))
  have hfinal : a •
        ψ.app V (((Scheme.Modules.pushforward iY).obj P).presheaf.map (homOfLE hVU).op w) =
      ((Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
        (homOfLE hVU).op (t * x) :=
    (unit_pushforward_smul_apply iZ V a _ _ hres).trans
      (((congrArg (fun r => r * Z.presheaf.map
              (homOfLE (hle iZ)).op x) ha).trans
          ((Z.presheaf.map (homOfLE (hle iZ)).op).hom.map_mul t x).symm).trans
        (unit_pushforward_presheaf_map_apply iZ hVU (t * x)).symm)
  refine Eq.trans ?_ hfinal
  calc ((Scheme.Modules.pushforward iZ).obj (SheafOfModules.unit Z.ringCatSheaf)).presheaf.map
          (homOfLE hVU).op (ψ.app U (s • w))
      = ψ.app V (((Scheme.Modules.pushforward iY).obj P).presheaf.map
          (homOfLE hVU).op (s • w)) := map_app_apply ψ hVU _
    _ = ψ.app V (P.presheaf.map (homOfLE (hle iY)).op (s • w)) :=
        congrArg (fun z => ψ.app V z) (pushforward_presheaf_map_apply iY P hVU (s • w))
    _ = ψ.app V ((Y.presheaf.map (homOfLE (hle iY)).op s) •
          (P.presheaf.map (homOfLE (hle iY)).op w)) :=
        congrArg (fun z => ψ.app V z)
          (Scheme.Modules.map_smul P
            (homOfLE (hle iY)) s w)
    _ = ψ.app V ((iY.app V a) •
          (P.presheaf.map (homOfLE (hle iY)).op w)) :=
        congrArg (fun r => ψ.app V (r •
          (P.presheaf.map (homOfLE (hle iY)).op w)))
          hsV
    _ = ψ.app V (a • (((Scheme.Modules.pushforward iY).obj P).presheaf.map
          (homOfLE hVU).op w)) :=
        congrArg (fun z => ψ.app V z)
          (pushforward_smul_apply iY P V a _ _ (pushforward_presheaf_map_apply iY P hVU w)).symm
    _ = a • ψ.app V (((Scheme.Modules.pushforward iY).obj P).presheaf.map (homOfLE hVU).op w) :=
        Scheme.Modules.Hom.app_smul ψ a _

/-- **Semilinearity over the restriction between two nested closed subschemes**, for a morphism
of `𝒪_X`-modules out of a module pushed forward from the smaller one. This is
`AlgebraicGeometry.Scheme.IdealSheafData.app_smul_eq_mul_of_app_eq` at the two closed immersions
of subschemes and at `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction`, whose
compatibility with the structure-sheaf maps is
`AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction_app_subschemeι_app`. -/
theorem app_smul_eq_mul_of_closedSubschemeRestriction_app {I J : X.IdealSheafData} (h : I ≤ J)
    (P : J.subscheme.Modules)
    (ψ : (Scheme.Modules.pushforward J.subschemeι).obj P ⟶ closedSubschemeStructureSheaf I)
    (U : X.Opens) (t : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U))
    (s : Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U))
    (hs : (closedSubschemeRestriction h).app U t = s) (w : Γ(P, J.subschemeι ⁻¹ᵁ U))
    {x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)} (hx : ψ.app U w = x) :
    ψ.app U (s • w) = t * x :=
  app_smul_eq_mul_of_app_eq J.subschemeι I.subschemeι (closedSubschemeRestriction h)
    (closedSubschemeRestriction_app_subschemeι_app h) P ψ U t s hs w hx

/-- **Semilinearity on global sections, with the restriction of scalars written as the
structure-sheaf map of the inclusion of subschemes.** For `I ≤ J` and a morphism `ψ` of
`𝒪_X`-modules from a module pushed forward from the subscheme cut out by `J` to the structure
sheaf of the one cut out by `I`, a global function `t` on the latter acts on the source through
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion`, and `ψ` carries that action to
multiplication by `t`.

This is the spelling in which the statement meets
`AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestriction`, which is defined as
`(inclusion h).appTop`; the two forms of the restriction of scalars agree by
`AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction_appTop`. -/
theorem appTop_smul_eq_mul_of_appTop_inclusion {I J : X.IdealSheafData} (h : I ≤ J)
    (P : J.subscheme.Modules)
    (ψ : (Scheme.Modules.pushforward J.subschemeι).obj P ⟶ closedSubschemeStructureSheaf I)
    (t : Γ(I.subscheme, (⊤ : I.subscheme.Opens))) (w : Γ(P, (⊤ : J.subscheme.Opens)))
    {x : Γ(I.subscheme, (⊤ : I.subscheme.Opens))} (hx : ψ.app ⊤ w = x) :
    ψ.app ⊤ ((inclusion h).appTop t • w) = t * x :=
  app_smul_eq_mul_of_closedSubschemeRestriction_app h P ψ ⊤ t ((inclusion h).appTop t)
    (closedSubschemeRestriction_appTop h t) w hx

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **The kernel inclusion of the sequence of [Stacks, Tag 0C4T] is semilinear over the
restriction of scalars `Γ(C + D, 𝒪) ⟶ Γ(C, 𝒪)`.** A global function `t` on the sum `C + D` acts
on global sections of `𝒪_X(-D)|_C` through its restriction to `C`, because the source of the
kernel inclusion is pushed forward from `C`; the kernel inclusion carries that action to
multiplication by `t` in the ring of global functions on the sum.

Together with `Stacks.Divisors.injective_sumKernelMap_appTop` and
`Stacks.Divisors.exists_sumKernelMap_appTop_eq` this makes the identification of
`Γ(X, 𝒪_X(-D)|_C)` with the kernel of `Γ(𝒪_{C + D}) ⟶ Γ(𝒪_D)` one of modules over the functions
on the sum, which is what a graded piece of a formal neighbourhood is asked to be: the kernel of
`Γ(Eₘ₊₁, 𝒪) ⟶ Γ(Eₘ, 𝒪)` carries the action of the functions on `Eₘ₊₁`, and a comparison of that
kernel with sections of a sheaf on the exceptional curve has to match it.

The order of the subscheme containments is forced: `C · D ≤ C` holds for every pair of ideal
sheaves (`AlgebraicGeometry.Scheme.IdealSheafData.mul_le_left`), so the subscheme cut out by `C`
sits inside the sum, and the restriction of scalars runs from the functions on the sum to the
functions on `C`.

The value `(sumKernelMap D C hD).app ⊤ w` is taken as a variable `x` with the equation `hx`
defining it; see the section introduction. -/
theorem appTop_sumKernelMap_smul_eq_mul (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (t : Γ((C * D).subscheme, (⊤ : (C * D).subscheme.Opens)))
    (w : Γ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D),
      (⊤ : C.subscheme.Opens)))
    {x : Γ((C * D).subscheme, (⊤ : (C * D).subscheme.Opens))}
    (hx : (sumKernelMap D C hD).app ⊤ w = x) :
    (sumKernelMap D C hD).app ⊤ ((inclusion (mul_le_left C D)).appTop t • w) = t * x :=
  appTop_smul_eq_mul_of_appTop_inclusion (mul_le_left C D) _ (sumKernelMap D C hD) t w hx

end Stacks.Divisors

end
