module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPresentationComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Reducing a parallel arrow of Stacks 03M8 for a general morphism to the chart alone

In the notation of Stacks 03M8 — `f : X ⟶ Y`, a chart `τ : U ⟶ X`, `R = U ×_X U` with its
projections `t, s : R ⟶ U`, `a = τ ≫ f` and `b = (t ≫ τ) ≫ f` — the two parallel arrows of the
asserted sequence arise in two shapes.  Their *natural* shape is the one the source writes: the
unit of the Stacks 03D7 adjunction at `t`, pushed forward along `a`, followed by the composition
comparisons of Stacks 03LU; their *transported* shape is the direct image along `f` of the
corresponding arrow for the identity of `X`, conjugated by the comparisons `τ_* ⋙ f_* ≅ a_*` and
`(t ≫ τ)_* ⋙ f_* ≅ b_*`, which is
`AlgebraicGeometry.Space.modulePullbackChartParallelArrow`.

That the two shapes agree is what reduces the asserted sequence for a general `f` to the
sequence for the identity of `X`: the direct image along `f` preserves limits, being a right
adjoint (`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`), so a limiting fork for the
identity transports to one for `f` by `CategoryTheory.Limits.isLimitForkOfMap`, and the
hypotheses that transport asks for — that the two parallel arrows correspond to the
pushed-forward ones under the two comparisons — are exactly that agreement.

This file proves the agreement **generically in the three comparisons**, and supplies the one
coherence of the comparison of direct images that the generic form consumes.  It does **not**
reach the statement at `AlgebraicGeometry.Space.modulePushforward`: instantiating the generic
form there is rejected by the kernel, for the reason recorded in the implementation notes below.

## Main results

* `CategoryTheory.Functor.compIso_comp_unitArrow_tail`: **the agreement of the two shapes, for an
  arbitrary triple of composition comparisons satisfying the associativity cocycle law**, an
  arbitrary morphism `η` into the image of the first functor and an arbitrary morphism `L`.  With
  `p = g_*`, `q = i_*`, `r = f_*`, `η` the unit of the Stacks 03D7 adjunction at `g` and `L` the
  comparison of inverse images, this is the clause of Stacks 03M8 described above.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc_app`: **the associativity coherence of
  `AlgebraicGeometry.Space.modulePushforwardCompIso` at a single module**, which is the cocycle
  hypothesis the generic clause takes.  It is
  `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`, which the library carries as an
  equality of isomorphisms of functors, read at one module by
  `CategoryTheory.Functor.cocycle_app_of_iso`.

## Implementation notes

**Why the clause is not stated at `AlgebraicGeometry.Space.modulePushforward`.**  The two shapes meet at the triple composite, which the two comparisons spell
differently: `AlgebraicGeometry.Space.modulePushforwardCompIso g (i ≫ f)` has `(g ≫ i ≫ f)_*` as
its target and `AlgebraicGeometry.Space.modulePushforwardCompIso (g ≫ i) f` has
`((g ≫ i) ≫ f)_*`, so a statement mentioning both at a module forces the identification of the
two.  Composition in `AlgebraicGeometry.AlgebraicSpaces` is definitionally associative, so no
transport is needed for such a statement to typecheck, and each identification is cheap on its
own.  With no `set_option` anywhere:

* `(g ≫ i ≫ f)_* = ((g ≫ i) ≫ f)_*` by `Eq.refl` — as functors, as objects
  `(g ≫ i ≫ f)_*M = ((g ≫ i) ≫ f)_*M`, and as morphisms
  `(g ≫ i ≫ f)_*a = ((g ≫ i) ≫ f)_*a` — is **checked in a fifth of a second** in each of the
  three cases;
* the clause itself, with the arrows written out and its proof left open, is elaborated and
  kernel-checked in a fifth of a second, in either spelling of the composite;
* `CategoryTheory.Functor.cocycle_app_of_iso` instantiated at the three comparisons — which is
  `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc_app` below — costs a fifth of a second,
  and so does each naturality square of a comparison, *including* one whose two sides are stated
  at the two different spellings of the composite;
* **instantiating a generic lemma whose conclusion carries the identification is not available.**
  With the four comparisons and the cocycle law supplied as arguments,
  `CategoryTheory.Functor.compIso_comp_unitArrow_tail` elaborates in a third of a second when it
  is elaborated with no expected type, and `exact` of the result against the written-out clause
  then reaches the elaborator's limit at `whnf`; raising that limit eightfold does not finish it,
  so the reduction does not terminate rather than merely cost more than the default allows.
  Supplying the shared target functor, the three module arguments and the middle objects
  explicitly, and matching the spellings of the statement to the ones the application produces,
  moves the failure from the elaborator to the **kernel**, which then exceeds its own budget on
  the instantiated type.  The same happens for a four-step chain lemma stated in a bare category
  and instantiated here, even when its three hypotheses are taken as binders of the consuming
  statement in exactly the shape the chain expects.  So what is unavailable is the identification
  of the two spellings *as part of matching an instantiated generic type against a declared one*,
  although the same identification alone costs a fifth of a second.

This is the obstruction the library records in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompTransport.lean`: a spelling
that puts a transport into a composition of *morphisms* of `𝒪`-modules sends the reduction of
`AlgebraicGeometry.Space.modulePushforward` somewhere it does not come back from, while the same
content at the level of isomorphisms of *functors* is cheap.  The route that would avoid it is the
one the library already takes for inverse images: `AlgebraicGeometry.Space.modulePullbackTriangle`
presents a composite as a *single* morphism `k` with `f ≫ g = k` as a hypothesis, so that two
comparisons meeting at a triple composite meet at one named morphism and no identification of
spellings arises at all.  The corresponding `modulePushforwardTriangle`, its associativity
coherence and its reading at a module do not exist in this repository, and building them is what a
statement of the clause at `AlgebraicGeometry.Space.modulePushforward` needs.

**The generic clause keeps the arrows as variables** — `η` and `L` are arbitrary morphisms rather
than the unit of Stacks 03D7 and the comparison of inverse images — which is the economy the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackPresentationComplex.lean` record: at these
types a clause whose arrows enter only as *arguments* is checked structurally, where the same
clause with the arrows written into the proof is not.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

/-! ### The agreement of the two shapes, generically in the comparisons -/

namespace CategoryTheory.Functor

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]

/-- **An arrow built from a morphism `η` and a comparison, pushed through a further
comparison.**  Let `P : p ⋙ q ≅ pq`, `Q : q ⋙ r ≅ qr`, `PQ : pq ⋙ r ≅ pqr` and
`QR : p ⋙ qr ≅ pqr` be comparisons satisfying the associativity cocycle law, and let
`η : M ⟶ p.obj N` and `L : N ⟶ N'` be arbitrary morphisms.  Then `Q` at `M`, followed by the
arrow `qr.map η ≫ QR.hom.app N` and then by `pqr.map L`, is the image under `r` of the arrow
`q.map η ≫ P.hom.app N ≫ pq.map L`, followed by `PQ` at `N'`.

In Stacks 03M8, with `p = g_*`, `q = i_*`, `r = f_*` the direct images of Stacks 03LU, `η` the
unit of the Stacks 03D7 adjunction at `g` and `L` the comparison of inverse images, this is the
step that identifies the parallel arrow for `i ≫ f` with the direct image along `f` of the
parallel arrow for `i`.

The three inputs are naturality of `Q` at `η`, the cocycle law
`CategoryTheory.Functor.cocycle_app_of_iso` at `N`, and naturality of `PQ` at `L`. -/
theorem compIso_comp_unitArrow_tail {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {r : A₂ ⥤ A₃} {pq : A₀ ⥤ A₂}
    {qr : A₁ ⥤ A₃} {pqr : A₀ ⥤ A₃} (P : p ⋙ q ≅ pq) (Q : q ⋙ r ≅ qr) (PQ : pq ⋙ r ≅ pqr)
    (QR : p ⋙ qr ≅ pqr)
    (h : isoWhiskerLeft p Q ≪≫ QR = (associator p q r).symm ≪≫ isoWhiskerRight P r ≪≫ PQ)
    {M : A₁} {N N' : A₀} (η : M ⟶ p.obj N) (L : N ⟶ N') :
    Q.hom.app M ≫ (qr.map η ≫ QR.hom.app N) ≫ pqr.map L =
      r.map (q.map η ≫ P.hom.app N ≫ pq.map L) ≫ PQ.hom.app N' := by
  have hcoc := cocycle_app_of_iso P Q PQ QR h N
  simp only [Iso.app_hom] at hcoc
  simp only [Category.assoc, Functor.map_comp]
  rw [← Q.hom.naturality_assoc, ← reassoc_of% hcoc, ← PQ.hom.naturality]
  rfl

end CategoryTheory.Functor

/-! ### The coherence it consumes, at the direct images of Stacks 03LU -/

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z U X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03LU, associativity of the composition comparison for direct images, at a single
module.**  For three composable morphisms `g : Z ⟶ U`, `i : U ⟶ X`, `f : X ⟶ Y` of algebraic
spaces and an `𝒪_Z`-module `N`, the two ways of comparing `f_*(i_*(g_*N))` with the direct image
of `N` along the triple composite agree.

This is `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`, an equality of isomorphisms of
functors, read at one module by `CategoryTheory.Functor.cocycle_app_of_iso`.  It is the cocycle
hypothesis of `CategoryTheory.Functor.compIso_comp_unitArrow_tail`. -/
theorem modulePushforwardCompIso_assoc_app (g : Z ⟶ U) (i : U ⟶ X) (f : X ⟶ Y)
    (N : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePushforward B S hS f).map ((modulePushforwardCompIso B S hS g i).hom.app N) ≫
        (modulePushforwardCompIso B S hS (g ≫ i) f).hom.app N =
      (modulePushforwardCompIso B S hS i f).hom.app ((modulePushforward B S hS g).obj N) ≫
        (modulePushforwardCompIso B S hS g (i ≫ f)).hom.app N :=
  Functor.cocycle_app_of_iso (modulePushforwardCompIso B S hS g i)
    (modulePushforwardCompIso B S hS i f) (modulePushforwardCompIso B S hS (g ≫ i) f)
    (modulePushforwardCompIso B S hS g (i ≫ f))
    (modulePushforwardCompIso_assoc B S hS g i f) N

end AlgebraicGeometry.Space

end
