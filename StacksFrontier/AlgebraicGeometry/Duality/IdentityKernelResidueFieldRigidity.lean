module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.StacksAttribute

/-!
# A self-map fixing the residue field of every closed point is the identity

Let `X` be a reduced scheme whose underlying space is Jacobson, let `p : X ⟶ Z` be a separated
morphism and let `g : X ⟶ X` satisfy `g ≫ p = p`.  If for every closed point `x` of `X` the
canonical morphism `Spec κ(x) ⟶ X` is unchanged by composition with `g`, then `g = 𝟙 X`.

This is the reduction of the last step of the proof of [Stacks, Tag 0G0E] to a statement about
residue fields.  That step asks, of a morphism `g = pr_1 ∘ s` whose derived pullback is isomorphic
to the identity on `D_perf(𝒪_X)`, that `g = 𝟙 X`; the topological half of it —
`g` fixes every point of the underlying space — is
`AlgebraicGeometry.base_comp_fst_eq_self_of_representsIdentityOnPerfect`, and the topological half
is *not enough*: the absolute Frobenius of a scheme over a finite field induces the identity of
the underlying space without being the identity, which is
`AlgHom.exists_comap_eq_ne_id_of_finite_field`.  What the statements below isolate is exactly the
extra input needed, namely that `g` fix each closed point *as a point with its residue field*.

## Main results

* `AlgebraicGeometry.eq_id_of_forall_mem_closedPoints_fromSpecResidueField_comp_eq` — the
  statement above, for an arbitrary reduced scheme with Jacobson underlying space.
* `AlgebraicGeometry.comp_fst_eq_id_of_forall_closedPoint_fromSpecResidueField` — the same in the
  shape the proof of [Stacks, Tag 0G0E] uses it: for `X` smooth and proper over a field `k` and
  `s : X ⟶ X ×_k X` a section of the second projection, `pr_1 ∘ s = 𝟙 X` as soon as `pr_1 ∘ s`
  fixes the `κ(x)`-point of every closed point `x`.

## Implementation notes

*Why closed points suffice.*  Mathlib's `AlgebraicGeometry.ext_of_fromSpecResidueField_eq` says
that two morphisms out of a reduced scheme which agree over a separated morphism and agree on the
residue-field points of a *dense* set of points are equal.  On a Jacobson space the closed points
are dense (`closure_closedPoints`), and a scheme locally of finite type over a field has Jacobson
underlying space (`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`, the spectrum of a field
being Jacobson), so the closed points are an admissible dense set.  No hypothesis of
positive dimension appears, and `g` is not assumed to be an automorphism — which is what
distinguishes this from `AlgebraicGeometry.eq_id_of_isIso_of_eq_on_points` of
[Stacks, Tag 0G05], whose conclusion needs both.

*The hypotheses discharged in the second statement.*  `X` smooth over a field is regular
([Stacks, Tag 056S], `AlgebraicGeometry.isRegular_of_smooth_over_field`), a regular scheme is
normal ([Stacks, Tag 0569]) and a normal scheme is reduced, which gives `IsReduced X`;
properness gives `LocallyOfFiniteType f` and `IsSeparated f`, and the former gives
`JacobsonSpace X`.  That `pr_1 ∘ s` is a morphism over `k` is the compatibility of the two
projections with `f` together with `s ≫ pr_2 = 𝟙`.

*Where the residue-field hypothesis comes from.*  It is where the *naturality* of the
isomorphism `L g^* ≅ 𝟭` enters: a single isomorphism `g^*ℱ ≅ ℱ` for each coherent `ℱ` cannot see
it, since over `Spec 𝔽_4` the Frobenius twist of a module is always abstractly isomorphic to the
module.  Naturality at the morphisms `𝒪_X ⟶ 𝒪_X/𝔪_x` is what forces the residue-field map at `x`
to be the identity, and that computation is now carried out:
`Stacks.Duality.fromSpecResidueField_comp_eq_of_natIso` of
`StacksFrontier/AlgebraicGeometry/Duality/IdentityKernelComorphism.lean` supplies the hypothesis of
`AlgebraicGeometry.comp_fst_eq_id_of_forall_closedPoint_fromSpecResidueField` at every closed
point, and `Stacks.Duality.comp_fst_eq_id_of_representsIdentityOnPerfect` is the two combined.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 0569](https://stacks.math.columbia.edu/tag/0569)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A self-map of a reduced scheme with Jacobson underlying space which fixes the residue-field
point of every closed point is the identity.**

`X` is reduced and its underlying space is Jacobson, `p : X ⟶ Z` is separated, and `g : X ⟶ X`
is a morphism over `p` whose composition with `Spec κ(x) ⟶ X` is that same morphism for every
closed point `x`.  Then `g = 𝟙 X`.

The closed points of a Jacobson space are dense, so this is
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq` at the set of closed points.  Neither
`IsIso g` nor any hypothesis on the dimension of `X` is needed. -/
theorem eq_id_of_forall_mem_closedPoints_fromSpecResidueField_comp_eq
    {X Z : Scheme.{u}} [IsReduced X] [JacobsonSpace X] (p : X ⟶ Z) [IsSeparated p]
    (g : X ⟶ X) (hp : g ≫ p = p)
    (h : ∀ x : X, x ∈ closedPoints X →
      X.fromSpecResidueField x ≫ g = X.fromSpecResidueField x) :
    g = 𝟙 X := by
  refine ext_of_fromSpecResidueField_eq g (𝟙 X) p (closedPoints X : Set X)
    (dense_iff_closure_eq.2 closure_closedPoints) (fun x hx => ?_) ?_
  · simpa using h x hx
  · simpa using hp

/-- **The last step of the proof of [Stacks, Tag 0G0E], reduced to residue fields.**  Let `X` be
smooth and proper over a field `k` and let `s : X ⟶ X ×_k X` be a section of the second
projection.  If `pr_1 ∘ s` leaves the canonical morphism `Spec κ(x) ⟶ X` of every closed point
`x` unchanged, then `pr_1 ∘ s = 𝟙 X`.

Together with `Stacks.Duality.iso_diagonalFourierMukaiKernel_of_isSection` this turns a kernel of
the form `Rs_*𝒪_X` into `Δ_*𝒪_X`: a morphism sectioning both projections is the diagonal.  The
hypothesis is supplied by `Stacks.Duality.fromSpecResidueField_comp_eq_of_natIso`; see the
implementation notes of this file. -/
theorem comp_fst_eq_id_of_forall_closedPoint_fromSpecResidueField
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]
    (s : X ⟶ Limits.pullback f f) (hsnd : s ≫ Limits.pullback.snd f f = 𝟙 X)
    (h : ∀ x : X, x ∈ closedPoints X →
      X.fromSpecResidueField x ≫ (s ≫ Limits.pullback.fst f f) =
        X.fromSpecResidueField x) :
    s ≫ Limits.pullback.fst f f = 𝟙 X := by
  have : IsNormal X := isNormal_of_isRegular X (isRegular_of_smooth_over_field f)
  have : IsReduced X := isReduced_of_isNormal X
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  refine eq_id_of_forall_mem_closedPoints_fromSpecResidueField_comp_eq f _ ?_ h
  calc (s ≫ Limits.pullback.fst f f) ≫ f
      = s ≫ Limits.pullback.fst f f ≫ f := by rw [Category.assoc]
    _ = s ≫ Limits.pullback.snd f f ≫ f := by rw [Limits.pullback.condition]
    _ = (s ≫ Limits.pullback.snd f f) ≫ f := by rw [Category.assoc]
    _ = f := by rw [hsnd, Category.id_comp]

end AlgebraicGeometry

end
