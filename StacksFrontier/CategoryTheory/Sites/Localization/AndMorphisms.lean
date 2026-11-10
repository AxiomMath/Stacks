module
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Exchange isomorphisms for a commutative square of sites with cocontinuous verticals

Consider four sites `(C', J')`, `(C, J)`, `(D', K')`, `(D, K)` and four functors forming a square
```
  C' --v'--> C
  |          |
  u'         u
  v          v
  D' --v---> D
```
which commutes on the nose, `u' ⋙ v = v' ⋙ u`. Assume `u` and `u'` are cocontinuous, so that they
give rise to morphisms of topoi `f : Sh(C) ⟶ Sh(D)` and `f' : Sh(C') ⟶ Sh(D')` (Stacks 00XO) whose
direct images are `f_* = {}_su` and `f'_* = {}_su'`, and assume `v` and `v'` are continuous, so
that restriction along them, `v^p` and `(v')^p`, takes sheaves to sheaves. Write
`{}^u_V I = CostructuredArrow u V` for the category of pairs `(U, ψ : u(U) ⟶ V)` of Section 00XF.
If for every object `V'` of `D'` the comparison functor
```
  {}^{u'}_{V'} I ⥤ {}^u_{v(V')} I,    (U', ψ) ↦ (v'(U'), v(ψ) : u(v'(U')) = v(u'(U')) ⟶ v(V')),
```
that is `CostructuredArrow.map₂` applied to the square, is final, then the square of topoi
commutes in the strong, Beck–Chevalley sense:
```
  f'_* ∘ (g')⁻¹ = g⁻¹ ∘ f_*    and    g'_! ∘ (f')⁻¹ = f⁻¹ ∘ g_!,
```
where `g⁻¹ = v^p` and `(g')⁻¹ = (v')^p` are the restrictions, `g_!` and `g'_!` their left
adjoints, and `f⁻¹`, `(f')⁻¹` the inverse images.

## Main results

* `nonempty_sheafPushforwardContinuousCompCocontinuousIso_and_leftAdjointCompPullbackIso_of_final`
  (in `CategoryTheory.Functor`; Stacks 0FN1): for a commutative square of sites as above with `u`,
  `u'` cocontinuous and `v`, `v'` continuous, finality of all the comparison functors
  `{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` implies `f'_* ∘ (g')⁻¹ ≅ g⁻¹ ∘ f_*`, and, whenever the four
  pushforwards involved have left adjoints, `g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!`.

## References

* [Stacks 0FN1](https://stacks.math.columbia.edu/tag/0FN1), in the section "Cocontinuous
  functors and localization" (Stacks 03EF); the category `{}^u_V I` is Section 00XF, the morphism
  of topoi of a cocontinuous functor is Stacks 00XO, the inverse image of a continuous and
  cocontinuous functor is Stacks 00XR, cofinal and initial functors are Categories, Section 09WN,
  and the module-theoretic consequence is Stacks 0FN3.
-/

section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
open CategoryTheory Limits
open CategoryTheory Opposite

namespace Stacks.Sites.CocontinuousExchange

section Presheaf

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {A : Type u₅} [Category.{v₅} A] {u' : C' ⥤ D'}
  {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D}

/-- The commutative square `u' ⋙ v = v' ⋙ u` read as a `2`-square `v' ⋙ u ⟶ u' ⋙ v`. -/
public abbrev twoSquare (hsq : u' ⋙ v = v' ⋙ u) : TwoSquare v' u' u v :=
  TwoSquare.mk v' u' u v (eqToHom hsq.symm)

/-- The comparison functor `{}^{u'}_{V'} I ⥤ {}^{u}_{v(V')} I`, sending `ψ : u'(U') ⟶ V'` to
`v(ψ) : u(v'(U')) = v(u'(U')) ⟶ v(V')`, is isomorphic to the functor
`TwoSquare.costructuredArrowRightwards` of the `2`-square at `V'`. -/
private def map₂IsoCostructuredArrowRightwards (hsq : u' ⋙ v = v' ⋙ u) (V' : D') :
    CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V')) ≅
      (twoSquare hsq).costructuredArrowRightwards V' :=
  NatIso.ofComponents
    (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _)
      (by simp [TwoSquare.costructuredArrowRightwards, CostructuredArrow.post,
        CostructuredArrow.pre, Comma.mapLeft]))
    (fun _ ↦ CostructuredArrow.ext _ _
      (by simp [TwoSquare.costructuredArrowRightwards, CostructuredArrow.post,
        CostructuredArrow.pre, Comma.mapLeft]))

/-- If every comparison functor `{}^{u'}_{V'} I ⥤ {}^{u}_{v(V')} I` is final, then the `2`-square
`TwoSquare.mk v' u' u v (eqToHom hsq.symm)` of the commutative square is Guitart exact. -/
public lemma guitartExact_twoSquare_mk (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal :
      ∀ V' : D',
        (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
            (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final) :
    (TwoSquare.mk v' u' u v (eqToHom hsq.symm)).GuitartExact :=
  (TwoSquare.guitartExact_iff_final _).mpr fun V' ↦
    have := hfinal V'
    Functor.final_of_natIso (map₂IsoCostructuredArrowRightwards hsq V')

variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
  [∀ F : C'ᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F]

/-- For a Guitart exact square, right Kan extension along `u.op` followed by restriction along
`v.op` is isomorphic to restriction along `v'.op` followed by right Kan extension along `u'.op`,
by the base change transformation of the opposite square. -/
private noncomputable def presheafIso (hsq : u' ⋙ v = v' ⋙ u) [(twoSquare hsq).GuitartExact] :
    u.op.ran ⋙ (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ A).obj v.op ≅
      (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ A).obj v'.op ⋙ u'.op.ran :=
  asIso (twoSquare hsq).op.ranBaseChange

end Presheaf

section Sheaf

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (A : Type u₅) [Category.{v₅} A]
  (J' : GrothendieckTopology C') (J : GrothendieckTopology C) (K' : GrothendieckTopology D')
  (K : GrothendieckTopology D) {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D}
  [u.IsCocontinuous J K] [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v'.IsContinuous J' J]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
  [∀ F : C'ᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F]

/-- For a Guitart exact square, `f'_* ∘ (g')⁻¹ ≅ g⁻¹ ∘ f_*`. -/
private noncomputable def sheafIso (hsq : u' ⋙ v = v' ⋙ u) [(twoSquare hsq).GuitartExact] :
    v'.sheafPushforwardContinuous A J' J ⋙ u'.sheafPushforwardCocontinuous A J' K' ≅
      u.sheafPushforwardCocontinuous A J K ⋙ v.sheafPushforwardContinuous A K' K :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K' A)
    (Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafIso hsq).symm)

/-- For a Guitart exact square whose four pushforwards have left adjoints,
`g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!`. -/
private noncomputable def sheafPullbackIso (hsq : u' ⋙ v = v' ⋙ u) [(twoSquare hsq).GuitartExact]
    [(u.sheafPushforwardCocontinuous A J K).IsRightAdjoint]
    [(u'.sheafPushforwardCocontinuous A J' K').IsRightAdjoint]
    [(v'.sheafPushforwardContinuous A J' J).IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K' K).IsRightAdjoint] :
    (u'.sheafPushforwardCocontinuous A J' K').leftAdjoint ⋙ v'.sheafPullback A J' J ≅
      v.sheafPullback A K' K ⋙ (u.sheafPushforwardCocontinuous A J K).leftAdjoint :=
  ((Adjunction.ofIsRightAdjoint (u'.sheafPushforwardCocontinuous A J' K')).comp
        (v'.sheafAdjunctionContinuous A J' J)).leftAdjointUniq
    (((v.sheafAdjunctionContinuous A K' K).comp
          (Adjunction.ofIsRightAdjoint (u.sheafPushforwardCocontinuous A J K))).ofNatIsoRight
      (sheafIso A J' J K' K hsq).symm)

end Sheaf

end Stacks.Sites.CocontinuousExchange

namespace CategoryTheory.Functor

@[expose] public section

open Stacks.Sites.CocontinuousExchange in
/-- Let `(C', J')`, `(C, J)`, `(D', K')`, `(D, K)` be sites and consider a square
of functors
```
  C' --v'--> C
  |          |
  u'         u
  v          v
  D' --v---> D
```
with `u' ⋙ v = v' ⋙ u`, where `u` and `u'` are cocontinuous — giving rise to morphisms of topoi `f`
and `f'` with `f_* = {}_su`, `f'_* = {}_su'` (Stacks 00XO) — and `v` and `v'` are continuous, so
that `g⁻¹ = v^p` and `(g')⁻¹ = (v')^p` are restriction (Stacks 00XR). Assume that for every object
`V'` of `D'` the comparison functor
```
  {}^{u'}_{V'} I ⥤ {}^u_{v(V')} I,   (U', ψ) ↦ (v'(U'), v(ψ) : u(v'(U')) = v(u'(U')) ⟶ v(V')),
```
on the categories of Section 00XF is cofinal, i.e. final. Then `f'_* ∘ (g')⁻¹ ≅ g⁻¹ ∘ f_*`, and
moreover `g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!` whenever the two restrictions have left adjoints `g_!`, `g'_!`
and the two pushforwards have left adjoints `f⁻¹`, `(f')⁻¹`. This holds for sheaves with values
in an arbitrary category `A`. -/
@[stacks 0FN1 "Beck–Chevalley for a commutative square of sites whose vertical functors are
  cocontinuous and whose horizontal functors are continuous: if the comparison functors
  `{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` are all cofinal then `f'_* (g')⁻¹ = g⁻¹ f_*`, and
  `g'_! (f')⁻¹ = f⁻¹ g_!` whenever the relevant left adjoints exist — a hypothesis of the second
  conjunct only, the first equality being the cofinality content and using no adjoint. For
  coefficients in an arbitrary category, the source's sheaves of sets being the case `A = Type u`;
  cocontinuity of the horizontal functors is not needed once their inverse images are read as
  restriction (Stacks 00XR)."]
public theorem
  nonempty_sheafPushforwardContinuousCompCocontinuousIso_and_leftAdjointCompPullbackIso_of_final
    {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
    [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (A : Type u₅) [Category.{v₅} A]
    (J' : GrothendieckTopology C') (J : GrothendieckTopology C) (K' : GrothendieckTopology D')
    (K : GrothendieckTopology D) (u' : C' ⥤ D') (u : C ⥤ D) (v' : C' ⥤ C) (v : D' ⥤ D)
    [u.IsCocontinuous J K] [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v'.IsContinuous J' J]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
    [∀ F : C'ᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F] (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal :
      ∀ V' : D',
        (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
            (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final) :
    Nonempty
        (v'.sheafPushforwardContinuous A J' J ⋙ u'.sheafPushforwardCocontinuous A J' K' ≅
          u.sheafPushforwardCocontinuous A J K ⋙ v.sheafPushforwardContinuous A K' K) ∧
      ∀ [(u.sheafPushforwardCocontinuous A J K).IsRightAdjoint]
        [(u'.sheafPushforwardCocontinuous A J' K').IsRightAdjoint]
        [(v'.sheafPushforwardContinuous A J' J).IsRightAdjoint]
        [(v.sheafPushforwardContinuous A K' K).IsRightAdjoint],
        Nonempty
          ((u'.sheafPushforwardCocontinuous A J' K').leftAdjoint ⋙ v'.sheafPullback A J' J ≅
            v.sheafPullback A K' K ⋙ (u.sheafPushforwardCocontinuous A J K).leftAdjoint) := by
  have := guitartExact_twoSquare_mk hsq hfinal
  exact ⟨⟨sheafIso A J' J K' K hsq⟩, fun {_ _ _ _} => ⟨sheafPullbackIso A J' J K' K hsq⟩⟩

end

end CategoryTheory.Functor

end

/-! # The site of objects of `C` lying over an object of `D` through a cocontinuous functor

Let `(C, J)` and `(D, K)` be sites, let `u : C ⥤ D` be a cocontinuous functor and let `V` be an
object of `D`. Stacks 00XF attaches to `u` and `V` the category `{}^u_V I` of pairs
`(U, ψ : u(U) ⟶ V)`, a morphism `(U, ψ) ⟶ (U', ψ')` being a morphism `α : U ⟶ U'` of `C` with
`ψ = ψ' ∘ u(α)`: this is Mathlib's `CostructuredArrow u V`. It comes with two projections,
`j = CostructuredArrow.proj u V : {}^u_V I ⥤ C`, `(U, ψ) ↦ U`, and
`u' = CostructuredArrow.toOver u V : {}^u_V I ⥤ D/V`, `(U, ψ) ↦ (ψ : u(U) ⟶ V)`, and the square of
categories they form with `u` and the localization functor `j_V = Over.forget V` commutes on the
nose: `j ⋙ u = u' ⋙ j_V`.

Give `{}^u_V I` the coverings induced by `C`: a sieve on `(U, ψ)` is covering exactly when its
image under `j` is a covering sieve of `U` for `J`.
Then this is a Grothendieck topology, `j` is continuous and cocontinuous for it, `u'` is
cocontinuous, and the two cocontinuous functors `u` and `u'` induce morphisms of topoi `f` and `f'`
(Stacks 00XO) fitting into a commutative square with the localization morphisms `j` and `j_V`.
Moreover `f'_* ∘ j⁻¹ = j_V⁻¹ ∘ f_*`, the identity of Stacks 03CF.

## Main results

* `CategoryTheory.Functor.exists_grothendieckTopology_costructuredArrow` (Stacks 0D5R): the
  commutative square `j ⋙ u = u' ⋙ j_V` of sites, together with a Grothendieck topology `H` on
  `CostructuredArrow u V` whose covering sieves are those with covering image under `j` — parts (1)
  to (5) of the tag, in order: `H` exists (1), `j` is continuous and cocontinuous for `(H, J)` (2),
  `u'` is cocontinuous for `(H, K.over V)` (3), the square of topoi commutes, i.e.
  `j_* ⋙ f_* ≅ f'_* ⋙ j_{V*}` (4), and `j⁻¹ ⋙ f'_* ≅ f_* ⋙ j_V⁻¹` (5).

## References

* [Stacks 0D5R](https://stacks.math.columbia.edu/tag/0D5R), in the section "Cocontinuous
  functors and localization" (Stacks 03EF); the category `{}^u_V I` is Section 00XF, the morphism
  of topoi of a cocontinuous functor is Stacks 00XO, the inverse image of a continuous and
  cocontinuous functor is Stacks 00XR, the localized topology is Stacks 00XZ, and part (5) is the
  identity of Stacks 03CF. The neighbouring square, with `C/U` in place of `{}^u_{u(U)} I`, is
  Stacks 03EG, where parts (3) and (4) hold but part (5) does not.
-/

section

universe u
open CategoryTheory Limits
open CategoryTheory

namespace Stacks.Sites.CocontinuousLocalization

section RanComp

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E] (A : Type*)
  [Category* A]

/-- Right Kan extension along a composite is isomorphic to the composite of the right Kan
extensions. -/
private noncomputable def ranComp (F : C ⥤ D) (G : D ⥤ E) [∀ P : C ⥤ A, F.HasRightKanExtension P]
    [∀ P : D ⥤ A, G.HasRightKanExtension P] [∀ P : C ⥤ A, (F ⋙ G).HasRightKanExtension P] :
    (F ⋙ G).ran (H := A) ≅ F.ran (H := A) ⋙ G.ran (H := A) :=
  ((F ⋙ G).ranAdjunction A).rightAdjointUniq
    (((G.ranAdjunction A).comp (F.ranAdjunction A)).ofNatIsoLeft
      (eqToIso
        (rfl :
          (Functor.whiskeringLeft D E A).obj G ⋙ (Functor.whiskeringLeft C D A).obj F =
            (Functor.whiskeringLeft C E A).obj (F ⋙ G))))

end RanComp

section PushforwardComp

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] {E : Type u}
  [SmallCategory E] (A : Type*) [Category* A] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (L : GrothendieckTopology E) (F : C ⥤ D) (G : D ⥤ E)
  [F.IsCocontinuous J K] [G.IsCocontinuous K L]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
  [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ A, (F ⋙ G).op.HasPointwiseRightKanExtension P]

/-- The composition law for pushforward along cocontinuous functors:
`(F ⋙ G)_* ≅ F_* ⋙ G_*`. -/
private noncomputable def sheafPushforwardCocontinuousComp :
    letI := isCocontinuous_comp F G J K (L := L)
    (F ⋙ G).sheafPushforwardCocontinuous A J L ≅
      F.sheafPushforwardCocontinuous A J K ⋙ G.sheafPushforwardCocontinuous A K L :=
  letI := isCocontinuous_comp F G J K (L := L)
  haveI : ∀ P : Cᵒᵖ ⥤ A, (F.op ⋙ G.op).HasPointwiseRightKanExtension P := fun P =>
    inferInstanceAs ((F ⋙ G).op.HasPointwiseRightKanExtension P)
  Functor.fullyFaithfulCancelRight (sheafToPresheaf L A)
    (Functor.isoWhiskerLeft (sheafToPresheaf J A) (ranComp A F.op G.op))

end PushforwardComp

section Site

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (u : C ⥤ D) [u.IsCocontinuous J K] (V : D)

/-- The canonical lift of `g : Y ⟶ X.left` to a morphism of `{}^u_V I` with target `X`, the
morphism over `g`. -/
private abbrev liftHom (X : CostructuredArrow u V) {Y : C} (g : Y ⟶ X.left) :
    CostructuredArrow.mk (u.map g ≫ X.hom) ⟶ X :=
  CostructuredArrow.homMk g rfl

/-- For a morphism `f` of `{}^u_V I` with target `X`, the image under
`j = CostructuredArrow.proj u V` of a sieve `S` of `X` contains `j(f)` exactly when `S` contains
`f`. -/
private lemma mem_functorPushforward_proj_iff {X Z : CostructuredArrow u V} (S : Sieve X)
    (f : Z ⟶ X) :
    (S.functorPushforward (CostructuredArrow.proj u V)).arrows f.left ↔ S.arrows f := by
  refine ⟨fun ⟨W, h, a, hS, e⟩ => ?_, fun hf => ⟨Z, f, 𝟙 Z.left, hf, by simp⟩⟩
  have w : u.map a ≫ W.hom = Z.hom := by
    rw [← CostructuredArrow.w f, show f.left = a ≫ h.left from e, u.map_comp, Category.assoc,
      CostructuredArrow.w h]
  have hk : (CostructuredArrow.homMk a w : Z ⟶ W) ≫ h = f := by
    ext; simpa using e.symm
  exact hk ▸ S.downward_closed hS _

/-- The image under `j` of a sieve `S` of `X` contains `g : Y ⟶ X.left` exactly when `S` contains
the canonical lift of `g`. -/
private lemma mem_functorPushforward_proj_lift_iff {X : CostructuredArrow u V} (S : Sieve X)
    {Y : C} (g : Y ⟶ X.left) :
    (S.functorPushforward (CostructuredArrow.proj u V)).arrows g ↔ S.arrows (liftHom u V X g) :=
  mem_functorPushforward_proj_iff u V S (liftHom u V X g)

/-- `Sieve.functorPullback j` undoes `Sieve.functorPushforward j`. -/
private lemma functorPullback_functorPushforward_proj {X : CostructuredArrow u V} (S : Sieve X) :
    (S.functorPushforward (CostructuredArrow.proj u V)).functorPullback
        (CostructuredArrow.proj u V) =
      S :=
  Sieve.ext fun _ f => mem_functorPushforward_proj_iff u V S f

/-- `Sieve.functorPushforward j` undoes `Sieve.functorPullback j`. -/
private lemma functorPushforward_functorPullback_proj {X : CostructuredArrow u V}
    (T : Sieve X.left) :
    (T.functorPullback (CostructuredArrow.proj u V)).functorPushforward
        (CostructuredArrow.proj u V) =
      T :=
  Sieve.ext fun _ g => mem_functorPushforward_proj_lift_iff u V _ g

/-- Pushing a sieve forward along `j` commutes with pullback. -/
private lemma functorPushforward_proj_pullback {X₁ X₂ : CostructuredArrow u V} (f : X₁ ⟶ X₂)
    (S : Sieve X₂) :
    (S.pullback f).functorPushforward (CostructuredArrow.proj u V) =
      (S.functorPushforward (CostructuredArrow.proj u V)).pullback
        ((CostructuredArrow.proj u V).map f) := by
  rw [←
    functorPushforward_functorPullback_proj u V
      ((S.functorPushforward (CostructuredArrow.proj u V)).pullback
        ((CostructuredArrow.proj u V).map f)),
    Sieve.functorPullback_pullback, functorPullback_functorPushforward_proj]

/-- The topology on `{}^u_V I = CostructuredArrow u V` whose covering sieves are those whose image
under `j` is covering. -/
private def topology : GrothendieckTopology (CostructuredArrow u V) where
  sieves X := {S | S.functorPushforward (CostructuredArrow.proj u V) ∈ J X.left}
  top_mem' X := by simp
  pullback_stable' X₁ X₂ S f hS := by
    rw [Set.mem_ofPred_eq, functorPushforward_proj_pullback]
    exact J.pullback_stable _ hS
  transitive' X S hS R hR :=
    J.transitive hS _ fun Y g hg => by
      have h :
        (R.pullback (liftHom u V X g)).functorPushforward (CostructuredArrow.proj u V) ∈ J Y :=
        hR ((mem_functorPushforward_proj_lift_iff u V S g).1 hg)
      rwa [functorPushforward_proj_pullback] at h

private lemma mem_topology_iff (X : CostructuredArrow u V) (S : Sieve X) :
    S ∈ topology J u V X ↔ S.functorPushforward (CostructuredArrow.proj u V) ∈ J X.left :=
  Iff.rfl

/-- The square `j ⋙ u = u' ⋙ j_V` commutes. -/
private lemma square :
    CostructuredArrow.proj u V ⋙ u = CostructuredArrow.toOver u V ⋙ Over.forget V :=
  rfl

/-- `j` is cocontinuous for the induced topology. -/
private instance isCocontinuous_proj :
    (CostructuredArrow.proj u V).IsCocontinuous (topology J u V) J where
  cover_lift {X} {S} hS := by
    rwa [mem_topology_iff, functorPushforward_functorPullback_proj]

/-- `j` is cover-preserving for the induced topology. -/
private lemma coverPreserving_proj :
    CoverPreserving (topology J u V) J (CostructuredArrow.proj u V)
    where
  cover_preserve hS := hS

/-- `j` is compatible-preserving for the induced topology. -/
private lemma compatiblePreserving_proj : CompatiblePreserving.{u} J (CostructuredArrow.proj u V)
    where
  compatible {_ Z _ _ hx Y₁ Y₂ _ f₁ f₂ g₁ g₂ hg₁ hg₂ h} :=
    hx (liftHom u V Y₁ f₁)
      (CostructuredArrow.homMk f₂
        (show u.map f₂ ≫ Y₂.hom = u.map f₁ ≫ Y₁.hom by
          rw [← CostructuredArrow.w g₂, ← CostructuredArrow.w g₁, ← u.map_comp_assoc, ←
            u.map_comp_assoc, show f₁ ≫ g₁.left = f₂ ≫ g₂.left from h]))
      hg₁ hg₂
      (by ext; exact h)

/-- `j` is continuous for the induced topology. -/
private instance isContinuous_proj :
    (CostructuredArrow.proj u V).IsContinuous (topology J u V) J :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_proj J u V)
    (coverPreserving_proj J u V)

/-- Pulling a sieve of `u'(X)` back along `u'` and pushing forward along `j` is pulling it back
along `u` after `Over.forget V`. -/
private lemma functorPushforward_functorPullback_toOver (X : CostructuredArrow u V)
    (S : Sieve ((CostructuredArrow.toOver u V).obj X)) :
    (S.functorPullback (CostructuredArrow.toOver u V)).functorPushforward
        (CostructuredArrow.proj u V) =
      (Sieve.overEquiv _ S).functorPullback u :=
  Sieve.ext fun _ g =>
    (mem_functorPushforward_proj_lift_iff u V _ g).trans (Sieve.overEquiv_iff S (u.map g)).symm

/-- `u' = CostructuredArrow.toOver u V` is cocontinuous for the induced topology and
`K.over V`. -/
private instance isCocontinuous_toOver :
    (CostructuredArrow.toOver u V).IsCocontinuous (topology J u V) (K.over V)
    where
  cover_lift {X} {S} hS := by
    rw [mem_topology_iff, functorPushforward_functorPullback_toOver]
    exact u.cover_lift J K hS

/-- The square of topoi commutes: `j_* ⋙ f_* ≅ f'_* ⋙ j_{V*}`. -/
private noncomputable def sheafPushforwardSquare :
    (CostructuredArrow.proj u V).sheafPushforwardCocontinuous (Type u) (topology J u V) J ⋙
        u.sheafPushforwardCocontinuous (Type u) J K ≅
      (CostructuredArrow.toOver u V).sheafPushforwardCocontinuous (Type u) (topology J u V)
          (K.over V) ⋙
        (Over.forget V).sheafPushforwardCocontinuous (Type u) (K.over V) K :=
  haveI : (CostructuredArrow.proj u V ⋙ u).IsCocontinuous (topology J u V) K :=
    isCocontinuous_comp _ _ _ J
  (sheafPushforwardCocontinuousComp (Type u) (topology J u V) J K (CostructuredArrow.proj u V)
        u).symm ≪≫
    (sheafPushforwardCocontinuousComp (Type u) (topology J u V) (K.over V) K
        (CostructuredArrow.toOver u V) (Over.forget V) :
      (CostructuredArrow.proj u V ⋙ u).sheafPushforwardCocontinuous (Type u) (topology J u V) K ≅
        _)

/-- The comparison functor of the square `j ⋙ u = u' ⋙ j_V` at an object `V'` of `D/V` is
final. -/
private lemma final_cmp (V' : Over V) :
    (CostructuredArrow.map₂ (S := CostructuredArrow.toOver u V) (T := V') (U := u) (V :=
        (Over.forget V).obj V') (F := CostructuredArrow.proj u V) (G := Over.forget V)
        (eqToHom (square u V)) (𝟙 ((Over.forget V).obj V'))).Final :=
  have : (CostructuredArrow.costructuredArrowToOverEquivalence.functor u V').Final :=
    Functor.final_of_adjunction
      (CostructuredArrow.costructuredArrowToOverEquivalence u V').symm.toAdjunction
  Functor.final_of_natIso (F := CostructuredArrow.costructuredArrowToOverEquivalence.functor u V')
    (NatIso.ofComponents
      (fun Z =>
        CostructuredArrow.isoMk (Iso.refl Z.left.left)
          (show u.map (𝟙 Z.left.left) ≫ 𝟙 (u.obj Z.left.left) ≫ Z.hom.left ≫ 𝟙 V'.left = Z.hom.left
            by
            rw [u.map_id, Category.id_comp, Category.id_comp]; exact Category.comp_id _))
      (fun f => by
        ext
        change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
        simp))

open CategoryTheory.Functor in
/-- `f'_* ∘ j⁻¹ ≅ j_V⁻¹ ∘ f_*`. -/
private lemma nonempty_exchange :
    Nonempty
      ((CostructuredArrow.proj u V).sheafPushforwardContinuous (Type u) (topology J u V) J ⋙
          (CostructuredArrow.toOver u V).sheafPushforwardCocontinuous (Type u) (topology J u V)
            (K.over V) ≅
        u.sheafPushforwardCocontinuous (Type u) J K ⋙
          (Over.forget V).sheafPushforwardContinuous (Type u) (K.over V) K) :=
  (nonempty_sheafPushforwardContinuousCompCocontinuousIso_and_leftAdjointCompPullbackIso_of_final
      (Type u) (topology J u V) J (K.over V) K (CostructuredArrow.toOver u V) u
      (CostructuredArrow.proj u V) (Over.forget V) (square u V).symm (final_cmp u V)).1

end Site

end Stacks.Sites.CocontinuousLocalization

namespace CategoryTheory.Functor

@[expose] public section

open Stacks.Sites.CocontinuousLocalization in
/-- Let `(C, J)` and `(D, K)` be sites, let `u : C ⥤ D` be cocontinuous and let
`V` be an object of `D`. Let `{}^u_V I = CostructuredArrow u V` be the category of pairs
`(U, ψ : u(U) ⟶ V)` of Section 00XF, with the two projections `j = CostructuredArrow.proj u V`,
`(U, ψ) ↦ U`, and `u' = CostructuredArrow.toOver u V`, `(U, ψ) ↦ (ψ : u(U) ⟶ V)`. Then the square
```
  {}^u_V I --j--> C
     |            |
     u'           u
     v            v
    D/V --j_V---> D
```
commutes, and declaring a sieve of `(U, ψ)` to be covering when its image under `j` is a covering
sieve of `U`:

1. this is a Grothendieck topology `H` on `{}^u_V I`, i.e. `{}^u_V I` is a site;
2. `j` is continuous and cocontinuous;
3. `u'` is cocontinuous;
4. the induced square of topoi commutes, `j_* ⋙ f_* ≅ f'_* ⋙ j_{V*}`, where `f` and `f'` are the
   morphisms of topoi of Stacks 00XO attached to the cocontinuous functors `u` and `u'`; and
5. `f'_* ∘ j⁻¹ = j_V⁻¹ ∘ f_*`, where the inverse images of the continuous and cocontinuous functors
   `j` and `j_V` are restriction (Stacks 00XR). -/
@[stacks 0D5R "The site of pairs `(U, ψ : u(U) → V)` for a cocontinuous `u`: `j` is continuous and
  cocontinuous, `u'` is cocontinuous, the resulting square of topoi commutes and
  `f'_* j⁻¹ = j_V⁻¹ f_*`. For sheaves of sets on small sites.",
  sga "3 IV 4.5.1" "partial, special case",
  sga "4 III 5.2" "special case"]
public theorem exists_grothendieckTopology_costructuredArrow {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsCocontinuous J K] (V : D) :
    CostructuredArrow.proj u V ⋙ u = CostructuredArrow.toOver u V ⋙ Over.forget V ∧
      ∃ H : GrothendieckTopology (CostructuredArrow u V),
        (∀ (X : CostructuredArrow u V) (S : Sieve X),
            S ∈ H X ↔ Sieve.functorPushforward (CostructuredArrow.proj u V) S ∈ J X.left) ∧
          ∃ (_ : (CostructuredArrow.proj u V).IsContinuous H J) (_ :
            (CostructuredArrow.proj u V).IsCocontinuous H J) (_ :
            (CostructuredArrow.toOver u V).IsCocontinuous H (K.over V)),
            Nonempty
                ((CostructuredArrow.proj u V).sheafPushforwardCocontinuous (Type u) H J ⋙
                    u.sheafPushforwardCocontinuous (Type u) J K ≅
                  (CostructuredArrow.toOver u V).sheafPushforwardCocontinuous (Type u) H
                      (K.over V) ⋙
                    (Over.forget V).sheafPushforwardCocontinuous (Type u) (K.over V) K) ∧
              Nonempty
                ((CostructuredArrow.proj u V).sheafPushforwardContinuous (Type u) H J ⋙
                    (CostructuredArrow.toOver u V).sheafPushforwardCocontinuous (Type u) H
                      (K.over V) ≅
                  u.sheafPushforwardCocontinuous (Type u) J K ⋙
                    (Over.forget V).sheafPushforwardContinuous (Type u) (K.over V) K) :=
  ⟨square u V, topology J u V, mem_topology_iff J u V, isContinuous_proj J u V,
    isCocontinuous_proj J u V, isCocontinuous_toOver J K u V, ⟨sheafPushforwardSquare J K u V⟩,
    nonempty_exchange J K u V⟩

end

end CategoryTheory.Functor

end

/-! # Exchange for a commutative square of sites whose horizontal functors are continuous

Consider four sites `(C', J')`, `(C, J)`, `(D', K')`, `(D, K)` and four functors forming a square
```
  C' --v'--> C
  ↑          ↑
  u'         u
  D' --v---> D
```
which commutes on the nose, `v ⋙ u = u' ⋙ v'`. Assume `u` and `u'` are continuous, so that they
give rise to morphisms of sites `f : C ⟶ D` and `f' : C' ⟶ D'` (Stacks 00X0) with
`f_* = u^s`, `f'_* = (u')^s` restriction along `u`, `u'` and with `f⁻¹ = u_s`, `(f')⁻¹ = (u')_s`
their left adjoints, and assume `v` and `v'` are continuous as well as cocontinuous, so that the
morphisms of topoi `g : Sh(D') ⟶ Sh(D)` and `g' : Sh(C') ⟶ Sh(C)` they define (Stacks 00XN) have
`g⁻¹ = v^p` and `(g')⁻¹ = (v')^p` restriction, with no sheafification, and `g_!`, `g'_!` the left
adjoints of those restrictions (Stacks 00XR). Then
```
  f'_* ∘ (g')⁻¹ = g⁻¹ ∘ f_*    and    g'_! ∘ (f')⁻¹ = f⁻¹ ∘ g_!.
```
This does not say that `f ∘ g'` and `g ∘ f'` agree as morphisms of topoi: in this generality
there is only a canonical `2`-arrow from the first to the second, which need not be invertible.

## Main results

* `CategoryTheory.Functor.sheafPushforwardContinuous_comp_eq_and_nonempty_sheafPullbackCompIso`
  (Stacks 0FN2): for a commutative square of sites as above with all four functors continuous,
  `f'_* ∘ (g')⁻¹ = g⁻¹ ∘ f_*` and `g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!`.

## References

* [Stacks 0FN2](https://stacks.math.columbia.edu/tag/0FN2), in the section "Cocontinuous functors
  and localization" (Stacks 03EF); morphisms of sites are Section 00X0, the morphism of topoi of a
  cocontinuous functor is Section 00XN, the inverse image of a continuous and cocontinuous functor
  and its left adjoint are Stacks 00XR, and the module-theoretic consequence is Stacks 0FN4.
-/

section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
open CategoryTheory

namespace Stacks.Sites.ContinuousExchange

section Congr

variable {X : Type*} [Category X] {Y : Type*} [Category Y] (A : Type*) [Category A]
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)

/-- Equal continuous functors between sites induce equal pushforward functors on `A`-valued
sheaves. -/
private theorem sheafPushforwardContinuous_congr {w w' : X ⥤ Y} [w.IsContinuous JX JY]
    [w'.IsContinuous JX JY] (h : w = w') :
    w.sheafPushforwardContinuous A JX JY = w'.sheafPushforwardContinuous A JX JY := by
  subst h
  rfl

end Congr

section Square

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (A : Type u₅) [Category.{v₅} A]
  (J' : GrothendieckTopology C') (J : GrothendieckTopology C) (K' : GrothendieckTopology D')
  (K : GrothendieckTopology D) (u : D ⥤ C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ C)
  [u.IsContinuous K J] [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v'.IsContinuous J' J]

/-- For a commutative square of continuous functors, `f'_* ∘ (g')⁻¹ = g⁻¹ ∘ f_*`. -/
private theorem sheafPushforwardContinuous_comp_eq (hsq : v ⋙ u = u' ⋙ v') :
    v'.sheafPushforwardContinuous A J' J ⋙ u'.sheafPushforwardContinuous A K' J' =
      u.sheafPushforwardContinuous A K J ⋙ v.sheafPushforwardContinuous A K' K := by
  have : (v ⋙ u).IsContinuous K' J := Functor.isContinuous_comp v u K' K J
  have : (u' ⋙ v').IsContinuous K' J := Functor.isContinuous_comp u' v' K' J' J
  exact sheafPushforwardContinuous_congr A K' J hsq.symm

/-- For a commutative square of continuous functors whose four pushforwards have left adjoints,
`g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!`. -/
private theorem nonempty_sheafPullbackCompIso [(u.sheafPushforwardContinuous A K J).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A K' J').IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K' K).IsRightAdjoint]
    [(v'.sheafPushforwardContinuous A J' J).IsRightAdjoint] (hsq : v ⋙ u = u' ⋙ v') :
    Nonempty
      (u'.sheafPullback A K' J' ⋙ v'.sheafPullback A J' J ≅
        v.sheafPullback A K' K ⋙ u.sheafPullback A K J) :=
  ⟨((u'.sheafAdjunctionContinuous A K' J').comp
          (v'.sheafAdjunctionContinuous A J' J)).leftAdjointUniq
      (((v.sheafAdjunctionContinuous A K' K).comp
            (u.sheafAdjunctionContinuous A K J)).ofNatIsoRight
        (eqToIso (sheafPushforwardContinuous_comp_eq A J' J K' K u u' v v' hsq).symm))⟩

end Square

end Stacks.Sites.ContinuousExchange

namespace CategoryTheory.Functor

@[expose] public section

open Stacks.Sites.ContinuousExchange in
/-- Let `(C', J')`, `(C, J)`, `(D', K')`, `(D, K)` be sites and consider a square
of functors
```
  C' --v'--> C
  ↑          ↑
  u'         u
  D' --v---> D
```
with `v ⋙ u = u' ⋙ v'`, where `u` and `u'` are continuous — giving rise to morphisms of sites `f`
and `f'` with `f_* = u^s`, `f'_* = (u')^s` and `f⁻¹ = u_s`, `(f')⁻¹ = (u')_s` (Stacks 00X0) — and
`v` and `v'` are continuous, so that `g⁻¹ = v^p` and `(g')⁻¹ = (v')^p` are restriction and `g_!`,
`g'_!` are their left adjoints (Stacks 00XR, for `v`, `v'` also cocontinuous). Then
`f'_* ∘ (g')⁻¹ = g⁻¹ ∘ f_*` and `g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!`. -/
@[stacks 0FN2 "Exchange for a commutative square of sites whose horizontal functors `u`, `u'` are
  continuous and whose vertical functors `v`, `v'` are continuous (in the source, continuous and
  cocontinuous): `f'_* (g')⁻¹ = g⁻¹ f_*` on the nose, and `g'_! (f')⁻¹ ≅ f⁻¹ g_!`. For coefficients
  in an arbitrary category; cocontinuity of `v`, `v'` is not needed once their inverse images are
  read as restriction (Stacks 00XR)."]
public theorem sheafPushforwardContinuous_comp_eq_and_nonempty_sheafPullbackCompIso {C' : Type u₁}
    [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃} [Category.{v₃} D']
    {D : Type u₄} [Category.{v₄} D] (A : Type u₅) [Category.{v₅} A] (J' : GrothendieckTopology C')
    (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
    (u : D ⥤ C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ C) [u.IsContinuous K J]
    [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v'.IsContinuous J' J]
    [(u.sheafPushforwardContinuous A K J).IsRightAdjoint]
    [(u'.sheafPushforwardContinuous A K' J').IsRightAdjoint]
    [(v.sheafPushforwardContinuous A K' K).IsRightAdjoint]
    [(v'.sheafPushforwardContinuous A J' J).IsRightAdjoint] (hsq : v ⋙ u = u' ⋙ v') :
    v'.sheafPushforwardContinuous A J' J ⋙ u'.sheafPushforwardContinuous A K' J' =
        u.sheafPushforwardContinuous A K J ⋙ v.sheafPushforwardContinuous A K' K ∧
      Nonempty
        (u'.sheafPullback A K' J' ⋙ v'.sheafPullback A J' J ≅
          v.sheafPullback A K' K ⋙ u.sheafPullback A K J) :=
  ⟨sheafPushforwardContinuous_comp_eq A J' J K' K u u' v v' hsq,
    nonempty_sheafPullbackCompIso A J' J K' K u u' v v' hsq⟩

end

end CategoryTheory.Functor

end
