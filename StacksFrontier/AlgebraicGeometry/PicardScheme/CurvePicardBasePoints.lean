module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicardSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyOfAPoint
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardScheme
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.CategoryTheory.Limits.CoproductPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The `k`-points of the Picard scheme of a curve: clause (2) of Tag 0BA0

Let `X` be a curve over a field `k` with a `k`-rational point, and suppose the Picard functor
`Pic_{X/k}` of [Stacks, Tag 0B9L] is representable — that is [Stacks, Tag 0B9Z], carried here as
a hypothesis exactly as in `StacksFrontier/AlgebraicGeometry/PicardScheme/CurvePicardScheme.lean`.
This file supplies the comparison that clause (2) of [Stacks, Tag 0BA0] needs and that
`CurvePicardScheme.lean` records as missing: **the fppf sheafification changes nothing at the
base**, so `Pic(X) ≅ Pic_{X/k}(Spec k)` and the `k`-points of the Picard scheme are the
invertible `𝒪_X`-modules.

## The comparison, and where its two halves come from

`Pic_{X/k}` is by definition the fppf sheafification of the presheaf `T ↦ Pic(X_T)`
(`Stacks.PicardFunctor.picardFunctor`), and the comparison map is the sheafification unit
`Stacks.PicardFunctor.toPicardFunctor`. The assertion is that the unit is *bijective* at the
base object `Spec k`. Both halves are read off the split exact sequence of [Stacks, Tag 0B9N],

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T) ⟶ 0`,

which `StacksFrontier/AlgebraicGeometry/PicardScheme/PicardSequenceSplitExact.lean` already proves
for every test scheme `T`:

* *Surjectivity* is `Stacks.PicardFunctor.surjective_toPicardFunctorHom` at `T = Spec k`, with no
  further input. This is where fppf descent of line bundles enters, and it is already discharged
  there: effectivity of fpqc descent for quasi-coherent modules
  (`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`) produces the module,
  and `Stacks.Picard.isInvertible_of_pullback_fpqcCover` makes it invertible.
* *Injectivity* is new, and is the one place where the base being a **field** is used. By
  exactness in the middle,
  `Stacks.PicardFunctor.exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom`, the kernel
  of the comparison at `T` is the image of `Pic(T)`. At `T = Spec k` that group vanishes —
  `AlgebraicGeometry.subsingleton_picardGroup_spec_field`, Tag 03QV — so the kernel is zero.

So the mathematics of the comparison is: *the relative Picard sequence at the base has
`Pic(Spec k) = 0` on its left, hence its right-hand map is injective as well as surjective.*

## Main definitions

* `Stacks.PicardFunctor.baseOver`: `Spec k` itself, as the terminal object of the big fppf site
  over it, with `Stacks.PicardFunctor.isTerminalBaseOver`.
* `Stacks.PicardFunctor.baseChangeBaseOverIso`: `X ≅ X ×_k Spec k`.
* `Stacks.PicardFunctor.picardBaseAddEquiv`: **`Pic(X) ≅ Pic_{X/k}(Spec k)`**.
* `Stacks.PicardFunctor.picardPointsEquiv`: the `k`-points of the Picard scheme are the
  invertible `𝒪_X`-modules.
* `Stacks.PicardFunctor.degreePointsEquiv`: **Tag 0BA0, clause (2)**.

## Main results

* `Stacks.PicardFunctor.injective_toPicardFunctorHom_baseOver` and
  `Stacks.PicardFunctor.bijective_toPicardFunctorHom_baseOver`: **the fppf sheafification unit of
  the relative Picard presheaf is bijective at the base**.

## Implementation notes

**What is hypothesis and what is conclusion.** Representability of the Picard functor
(Tag 0B9Z) is the instance hypothesis `(picardFunctor B hX hk f).IsRepresentable`, as in
`CurvePicardScheme.lean`. The `k`-rational point of `X` is carried as `σ` together with `hσ`;
Tag 0BA0 assumes `k` separably closed and `X` a smooth projective curve, under which such a
point exists, and the proof of 0BA0 in the Stacks Project opens by picking one. The
isomorphism `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` for every test scheme is carried as `hOiso`; this is the
standing hypothesis of Tag 0B9N and holds for a proper curve with `H⁰(X, 𝒪_X) = k`. Nothing
here asserts that any of these exist.

**The two models of the Picard group.** `Pic(X_T)` in the relative Picard presheaf is
`Stacks.Picard.ofScheme`, the unshrunk skeleton in `Type (u+1)`, while
`AlgebraicGeometry.picardDegree` is defined on `AlgebraicGeometry.schemePicard`, the shrunk model
in `Type u`. The two are translated by `Stacks.GluePicard.picardModelAddEquiv`, which is pinned
on invertible modules by `Stacks.GluePicard.picardModelAddEquiv_classOf`; clause (2) is stated
with the genuine degree homomorphism across that translation, not with an abstract degree.

**What clause (2) carries.** That `P d` is the degree-`d` component `Pic^d_{X/k}` is not proved
here — it is the part of clause (1) that rests on the openness of the degree subfunctors
(Tag 0B9T) together with the degree of `𝒪(D)`, and `CurvePicardScheme.lean` likewise carries the
degree decomposition rather than constructing it. The degree of `𝒪(D)` is no longer among the
missing ingredients —
`AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_divisorSubscheme_eq_invertibleCurveDegree`
gives it — so what `hdeg` still carries is the openness of the degree subfunctors. It enters as
the family `j` of monomorphisms together with `hdeg`, which says precisely that a `k`-point of
`Pic_{X/k}` factors through `j d` exactly when the corresponding invertible module has degree `d`.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Picard

/-- **Pullback along an isomorphism of schemes is an isomorphism of Picard groups.** Pullback
along `e.inv` is the two-sided inverse, the two composites being pullback along an identity. -/
def schemePullbackClassAddEquiv {X Y : Scheme.{u}} (e : X ≅ Y) : ofScheme Y ≃+ ofScheme X where
  toFun := schemePullbackClass e.hom
  invFun := schemePullbackClass e.inv
  left_inv x := by rw [schemePullbackClass_comp, e.inv_hom_id, schemePullbackClass_id]
  right_inv x := by rw [schemePullbackClass_comp, e.hom_inv_id, schemePullbackClass_id]
  map_add' := schemePullbackClass_add e.hom

/-- Pullback along an isomorphism, as an additive equivalence, is pullback along its forward
map. -/
@[simp]
theorem schemePullbackClassAddEquiv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (x : ofScheme Y) :
    schemePullbackClassAddEquiv e x = schemePullbackClass e.hom x :=
  rfl

end Stacks.Picard

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

/-! ### The base object of the site -/

/-- `Spec k` itself, as an object of the big fppf site over `Spec k`: the test scheme at which
the values of the Picard functor are its `k`-points. -/
abbrev baseOver : BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))

/-- The base object is terminal, so the morphisms into any object of the site from it are that
object's `k`-points. -/
def isTerminalBaseOver : IsTerminal (baseOver B hk) := Over.mkIdTerminal

/-- The scheme underlying the base object is `Spec k`. -/
theorem toScheme_obj_baseOver :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseOver B hk) = Spec (.of k) := rfl

/-! ### `Pic(X ×_k Spec k) = Pic(X)` -/

/-- **`X ≅ X ×_k Spec k`**: the base change of `X ⟶ Spec k` along the base object is `X`, the
structure morphism of that object being an identity. -/
def baseChangeBaseOverIso : X ≅ baseChange B hX hk f (baseOver B hk) :=
  pullbackRightIdIso (B.inclusion.map f)

/-- **`Pic(X) ≅ Pic(X ×_k Spec k)`**, pullback along `Stacks.PicardFunctor.baseChangeBaseOverIso`.
-/
def picardAtBaseOverAddEquiv :
    Stacks.Picard.ofScheme X ≃+ picardAt B hX hk f (baseOver B hk) :=
  (Stacks.Picard.schemePullbackClassAddEquiv (baseChangeBaseOverIso B hX hk f)).symm

/-! ### The sheafification unit is bijective at the base -/

include σ hσ in
/-- **The fppf sheafification unit of the relative Picard presheaf is injective at the base.**
By exactness in the middle of the sequence of [Stacks, Tag 0B9N] the kernel of
`Pic(X_T) ⟶ Pic_{X/k}(T)` is the image of `Pic(T)`; at `T = Spec k` that group is trivial, the
Picard group of the spectrum of a field vanishing ([Stacks, Tag 03QV]). -/
theorem injective_toPicardFunctorHom_baseOver
    (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c) :
    Function.Injective (toPicardFunctorHom B hX hk f (baseOver B hk)) := by
  have : Subsingleton (Stacks.Picard.ofScheme
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseOver B hk))) :=
    AlgebraicGeometry.subsingleton_picardGroup_spec_field k
  intro a b hab
  have hz : toPicardFunctorHom B hX hk f (baseOver B hk) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨N, hN⟩ := (exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom
    B hX hk f σ hσ hOiso (baseOver B hk) (a - b)).1 hz
  rw [Subsingleton.elim N 0] at hN
  rw [← sub_eq_zero, ← hN]
  exact map_zero
    (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hk f (baseOver B hk)))

include σ hσ in
/-- **The fppf sheafification changes nothing at the base**: the unit
`Pic(X) = Pic(X ×_k Spec k) ⟶ Pic_{X/k}(Spec k)` is bijective. Surjectivity is
[Stacks, Tag 0B9N] at the base object, which is where fppf descent of invertible modules enters;
injectivity is `Stacks.PicardFunctor.injective_toPicardFunctorHom_baseOver`. -/
theorem bijective_toPicardFunctorHom_baseOver
    (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c) :
    Function.Bijective (toPicardFunctorHom B hX hk f (baseOver B hk)) :=
  ⟨injective_toPicardFunctorHom_baseOver B hX hk f σ hσ hOiso,
    surjective_toPicardFunctorHom B hX hk f σ hσ hOiso (baseOver B hk)⟩

include σ hσ in
/-- **`Pic(X) ≅ Pic_{X/k}(Spec k)`.** The composite of
`Stacks.PicardFunctor.picardAtBaseOverAddEquiv` with the sheafification unit at the base, which
is bijective by `Stacks.PicardFunctor.bijective_toPicardFunctorHom_baseOver`. -/
def picardBaseAddEquiv
    (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c) :
    Stacks.Picard.ofScheme X ≃+ (picardFunctor B hX hk f).obj (op (baseOver B hk)) :=
  (picardAtBaseOverAddEquiv B hX hk f).trans
    { Equiv.ofBijective _ (bijective_toPicardFunctorHom_baseOver B hX hk f σ hσ hOiso) with
      map_add' := map_add (toPicardFunctorHom B hX hk f (baseOver B hk)) }

/-! ### Clause (2): the `k`-points of the Picard scheme -/

section Representable

variable [(picardFunctor B hX hk f).IsRepresentable]

include σ hσ in
/-- **The `k`-points of the Picard scheme are the invertible `𝒪_X`-modules.** Yoneda identifies
them with `Pic_{X/k}(Spec k)` (`Stacks.PicardFunctor.picardHomEquiv`), and
`Stacks.PicardFunctor.picardBaseAddEquiv` identifies that with `Pic(X)`. -/
def picardPointsEquiv
    (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c) :
    (baseOver B hk ⟶ picardSchemeOver B hX hk f) ≃ Stacks.Picard.ofScheme X :=
  (picardHomEquiv B hX hk f).trans
    (picardBaseAddEquiv B hX hk f σ hσ hOiso).toEquiv.symm

include σ hσ in
/-- **The `k`-points of a degree component of the Picard scheme** (the shape of [Stacks, Tag 0BA0],
clause (2), for a carried degree decomposition). Let `X` be a curve over a field `k` with a
`k`-rational point whose Picard functor is representable. Then the `k`-points of the degree-`d`
component `Pic^d_{X/k}` correspond to the invertible `𝒪_X`-modules of degree `d`.

The substance is `Stacks.PicardFunctor.picardBaseAddEquiv`, `Pic(X) ≅ Pic_{X/k}(Spec k)`: the
fppf sheafification defining `Pic_{X/k}` changes nothing at the base. Composing with Yoneda
identifies the `k`-points of the whole Picard scheme with `Pic(X)`; `hdeg` then cuts out the
degree-`d` component on each side, and `j d` being a monomorphism makes the factorisation
through it unique. -/
def degreePointsEquiv
    (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
      IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
    [IsProper (B.inclusion.map f)] [IsCurve k (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1)
    {P : ℤ → BigFppfOver B (Spec (.of k)) hk}
    (j : ∀ d : ℤ, P d ⟶ picardSchemeOver B hX hk f) (d : ℤ) [Mono (j d)]
    (hdeg : ∀ p : baseOver B hk ⟶ picardSchemeOver B hX hk f,
      (∃ q : baseOver B hk ⟶ P d, q ≫ j d = p) ↔
        picardDegree k (B.inclusion.map f) hdim (Stacks.GluePicard.picardModelAddEquiv
          X.toRingedSpace (picardPointsEquiv B hX hk f σ hσ hOiso p)) = d) :
    (baseOver B hk ⟶ P d) ≃
      {L : Stacks.Picard.ofScheme X //
        picardDegree k (B.inclusion.map f) hdim
          (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace L) = d} :=
  Equiv.ofBijective
    (fun q => ⟨picardPointsEquiv B hX hk f σ hσ hOiso (q ≫ j d), (hdeg _).1 ⟨q, rfl⟩⟩)
    ⟨fun q₁ q₂ h => (cancel_mono (j d)).1
        ((picardPointsEquiv B hX hk f σ hσ hOiso).injective (Subtype.ext_iff.1 h)),
      fun L => by
        obtain ⟨q, hq⟩ :=
          (hdeg ((picardPointsEquiv B hX hk f σ hσ hOiso).symm L.1)).2
            (by rw [Equiv.apply_symm_apply]; exact L.2)
        refine ⟨q, Subtype.ext ?_⟩
        change picardPointsEquiv B hX hk f σ hσ hOiso (q ≫ j d) = L.1
        rw [hq, Equiv.apply_symm_apply]⟩

end Representable

end Stacks.PicardFunctor

end
