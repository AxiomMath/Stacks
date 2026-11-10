module
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

/-!
# Sheaves on the site `C/F` of elements of a sheaf

Let `(C, J)` be a site and let `F` be a sheaf of sets on `C`. The category `C/F` has as objects
the pairs `(U, s)` with `U` an object of `C` and `s ∈ F(U)`, and as morphisms
`(V, t) ⟶ (U, s)` the morphisms `f : V ⟶ U` of `C` with `f^*s = t`; by the Yoneda lemma this is
`CostructuredArrow yoneda F`, and the source's functor `j : C/F ⥤ C` is
`CostructuredArrow.proj yoneda F`. A family `{(U_i, s_i) ⟶ (U, s)}` is declared to be a covering
exactly when `{U_i ⟶ U}` is a covering of `C`, that is, the coverings of `C/F` are the presieves
of `Precoverage.comap j J.toPrecoverage`, and the topology they generate is
`j.restrictedTopology J`.

Stacks 0791 asserts that `j` is a continuous and cocontinuous functor of sites, so that it induces
a morphism of topoi `j : Sh(C/F) ⟶ Sh(C)`, and that there is an equivalence
`Sh(C/F) = Sh(C)/F` which turns `j` into the localization morphism `j_F` of Stacks 04GZ.

At the level of presheaves that equivalence is Mathlib's
`CategoryTheory.overEquivPresheafCostructuredArrow F : Over F ≌ PSh(C/F)`: it sends an object
`φ : G ⟶ F` of `PSh(C)/F` to the presheaf `(U, s) ↦ {t ∈ G(U) | φ(t) = s}` on `C/F`, which is the
sheaf `a(G/F)` written down in the source's proof, and its inverse sends a presheaf `H` on `C/F`
to the presheaf `U ↦ ∐_{s ∈ F(U)} H(U, s)` over `F`, which is `j_!` on presheaves. The engine of
Stacks 0791 is that this equivalence matches sheaves with sheaves; the equivalence
`Sh(C/F) ≌ Sh(C)/F` of the source is its restriction to the two full subcategories of sheaves
(`sheafToPresheaf` being fully faithful, `Sh(C)/F` is the full subcategory of `PSh(C)/F` on the
objects whose source is a sheaf), and the functor `Sh(C/F) ⟶ Sh(C)` obtained from it by
forgetting the structure morphism is `j_!` — with no sheafification, because the sum presheaf
`U ↦ ∐_{s ∈ F(U)} H(U, s)` of a sheaf `H` on `C/F` is already a sheaf on `C`.

Since `j_!` is left adjoint to `j^{-1}` and `Over.forget` is the `j_{F!}` of Stacks 04GZ (3), that
last identification is exactly the source's "turns `j` into `j_F`": the equivalence carries the
inverse image `j^{-1}` of `j` to the inverse image `- × F` of `j_F`.

## Main definitions

* `CategoryTheory.Presheaf.IsSheaf.SheafEquivalenceCostructuredArrowYoneda` and
  `CategoryTheory.Presheaf.IsSheaf.sheafEquivalenceCostructuredArrowYoneda`: the last assertion of
  Stacks 0791 as data — one equivalence `Sh(C/F) ≌ Sh(C)/F` together with the identification of
  its inverse with the fibre construction and the adjunction exhibiting its functor followed by
  `Over.forget` as `j_!`. The existence statement below is obtained from it, and anything that
  must compare the two descriptions of the same equivalence uses this rather than the existence
  statement, whose conjuncts speak about separate choices.

## Main results

* `CategoryTheory.Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda`:
  Stacks 0791, for a sheaf `F` on `C`, as the conjunction of the source's assertions:
  the covering sieves of `j.restrictedTopology J` are the source's, i.e. `C/F` is a site with the
  coverings of the tag; the canonical equivalence `Over F ≌ PSh(C/F)` matches sheaves with
  sheaves, i.e. `(U, s) ↦ {t ∈ G(U) | φ(t) = s}` is a sheaf on `C/F` if and only if `G` is a sheaf
  on `C`; `j` is continuous and cocontinuous; and there is an equivalence `Sh(C/F) ≌ Sh(C)/F`
  restricting the canonical one, under which the forgetful functor `Sh(C)/F ⥤ Sh(C)` is `j_!`, so
  that `j` becomes the localization morphism `j_F` of Stacks 04GZ.
* `CategoryTheory.Presheaf.IsSheaf.app_fibers_inv_comp_unitInv`: the two
  descriptions of the equivalence agree on `j_!j^{-1}G`. Identifying the fibre sheaf of
  `j_!j^{-1}G` with `j^{-1}G`, by the fibre description of `E.inverse` and the unit of `E`, sends
  a section of `j_!j^{-1}G` lying in the fibre over `s ∈ F(U)` to its image under the counit of
  the adjunction `j_! ⊣ j^{-1}`.
* `CategoryTheory.Presheaf.IsSheaf.app_fibers_inv_comp_homEquiv_shriek`: the same for an
  arbitrary object `T` of `Sh(C)/F` and an arbitrary morphism `β : T.left ⟶ G`, in place of the
  counit — transposing `β` across `j_! ⊣ j^{-1}` is evaluation of `β` on fibre sections. This is
  the form a comparison built from the fibre description must be fed through, since `T.left` for
  `T` in the image of `E` has no description except by its fibres.

## Implementation notes

* The topology of `C/F` is written as `j.restrictedTopology J`, the topology generated by the
  source's coverings, rather than by a bespoke definition analogous to Mathlib's
  `GrothendieckTopology.over` for the localization at an object. Nothing is lost even before the
  first conjunct is known: a presheaf is a sheaf for a generated topology exactly when it is a
  sheaf for the generating coverings and their pullbacks
  (`CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff`), so the sheaf conditions appearing
  here are literally the source's.
* The first conjunct, `S ∈ j.restrictedTopology J (U, s) ↔ S.functorPushforward j ∈ J U`, is the
  verification the source omits: that the source's coverings already form a topology, so that
  `C/F` is a site with those coverings and no others. Its `←` half is Mathlib's
  `CategoryTheory.Functor.mem_restrictedTopology_of_functorPushforward_mem`, and its `→` half is
  `CategoryTheory.Functor.coverPreserving_restrictedTopology` once `j` is known to be locally
  cover dense, which holds because every `f : V ⟶ U` lifts uniquely to `(V, f^*s) ⟶ (U, s)`.
* The morphism of topoi of the source is not a separate conjunct: for a functor that is both
  continuous and cocontinuous it is Mathlib's
  `CategoryTheory.Functor.sheafAdjunctionCocontinuous`, the adjunction
  `j^{-1} = j.sheafPushforwardContinuous ⊣ j.sheafPushforwardCocontinuous = j_*`, which the two
  continuity conjuncts produce with nothing further to prove. This is the reading of Stacks 00XR:
  the inverse image of a continuous and cocontinuous functor is restriction.
* The last conjunct is an adjunction rather than an isomorphism with `Functor.sheafPullback`
  because `sheafPullback` is only defined under `[HasWeakSheafify]` and an `IsRightAdjoint`
  hypothesis on `j^{-1}`, and the existence of `j_!` is part of what the source asserts rather
  than a hypothesis it makes. Stating `(E.functor ⋙ Over.forget) ⊣ j^{-1}` therefore says both
  that `j_!` exists and that it is `Over.forget` transported along `E`; whenever `sheafPullback`
  is defined, uniqueness of left adjoints turns it into the isomorphism
  `E.functor ⋙ Over.forget ≅ j.sheafPullback`, which is the shape of this repository's
  `CategoryTheory.OverShriek.sheafFunctorToOverForgetIso` for the case `F = h_U^#`. Dually, since
  `Over.forget ⊣ Over.star` in `Sh(C)`, it gives `j^{-1} ≅ Over.star F ⋙ E.inverse`, i.e. the
  inverse image of `j` is the inverse image `- × F` of `j_F` (Stacks 04GZ (1)).
* The equivalence `E` is pinned rather than merely asserted to exist: the first `Nonempty` says
  that its inverse is, on underlying presheaves, the canonical
  `overEquivPresheafCostructuredArrow F`, so both `E` and `E.symm` are the constructions the
  source writes down — `E.inverse` is `(F, φ) ↦ ((U, s) ↦ {t ∈ G(U) | φ(t) = s})` and `E.functor`
  is `j_!`. The sheaf-matching conjunct is what makes such an `E` exist at all.
* Every hypothesis is used, and `hF` in both directions of the sheaf-matching conjunct. For `→`,
  take `φ = 𝟙_F`: the presheaf `(U, s) ↦ {t ∈ F(U) | t = s}` on `C/F` is the terminal one, hence a
  sheaf for any presheaf `F`, while `T.left = F` is a sheaf only when `F` is. For `←`, take for
  `C` a single object `U` with only its identity and for `J` the topology in which the empty sieve
  covers, so that a presheaf is a sheaf exactly when its value at `U` is a singleton; for `F` with
  two sections over `U`, and `G` the terminal presheaf mapping to one of them, `G` is a sheaf while
  the presheaf `(U, s) ↦ {t ∈ G(U) | φ(t) = s}` is empty at the other section, hence not a sheaf.
  `hF` is also what makes `Sh(C)/F` meaningful: it is the slice of `Sh(C)` at `F`.
* The site is the source's: the topology on `C` is the given `J`, the sheaves are sheaves of sets
  (`Type v`-valued, as in `Sheaf J (Type v)`), and no refinement of `J` and no change of sites
  intervenes — the source's proof of the *localization* statement 04GZ passes through Stacks 03CI,
  but 0791 itself does not.
* The instantiation is not degenerate: for `C` the site of opens of a topological space and
  `F = h_U^#` the sheaf represented by an open `U`, the category `C/F` is the localization `C/U`,
  the topology is `J.over U`, and the statement is the identification `Sh(C/U) = Sh(C)/h_U^#` of
  Stacks 00Y1, in which none of the categories involved is equivalent to `Sh(C)`.
* Sharper than the sheaf-matching conjunct, and available to whoever proves it: its `←` half needs
  only that `j^{-1}F` is separated, not that `F` is a sheaf, and in that form it is the
  repository's `CategoryTheory.OverShriek.isSheaf_fiber` with `C/U` replaced by `C/F`. The `→`
  half is where `F` is glued, and it is what makes the sum presheaf of a sheaf a sheaf.
  Continuity of `j` is the `←` half applied to the projection `G × F ⟶ F`, whose associated
  presheaf on `C/F` is `(U, s) ↦ {(t, a) ∈ (G × F)(U) | a = s} ≅ G(U) = (j^{-1}G)(U, s)`, and
  cocontinuity is immediate from the first conjunct.

## References

* [Stacks 0791](https://stacks.math.columbia.edu/tag/0791). The source omits the verifications
  that `C/F` is a site and that `j` is continuous and cocontinuous, obtains the morphism of topoi
  from Stacks 00XR, computes `j_!* = F` — a morphism `* ⟶ j^{-1}G` on `C/F` is a rule assigning to
  every `(U, s)` a section of `G(U)` compatible with restrictions, i.e. a morphism `F ⟶ G` — and
  then exhibits `a(G/F) : (U, s) ↦ {t ∈ G(U) | φ(t) = s}` as an inverse to
  `H ↦ (j_!H ⟶ j_!* = F)`.
* [Stacks 04GZ](https://stacks.math.columbia.edu/tag/04GZ) for the localization morphism `j_F`
  into which `j` is turned, and [Stacks 00Y1](https://stacks.math.columbia.edu/tag/00Y1) for the
  case `F = h_U^#`.
* [Kashiwara2006], Lemma 1.4.12, for the presheaf level equivalence
  `overEquivPresheafCostructuredArrow`.
-/

namespace CategoryTheory

section

universe v u
open CategoryTheory Opposite Presieve OverPresheafAux
variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type v) (J : GrothendieckTopology C)

public section

/-- **The data of Stacks 0791's identification of `Sh(C/F)` with `Sh(C)/F`**: the equivalence,
the identification of its inverse with the fibre construction on underlying presheaves, and the
adjunction exhibiting its functor followed by `Over.forget` as `j_!`.

The three witnesses are packaged together because they are statements about **one** equivalence:
each one separately is a statement about an unrelated choice, and the comparisons built from them
downstream — the inverse image of a localization morphism, read through the equivalence — are only
pinned down when the same equivalence carries all three. -/
structure Presheaf.IsSheaf.SheafEquivalenceCostructuredArrowYoneda {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf J F)
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J] where
  /-- The equivalence `Sh(C/F) ≌ Sh(C)/F`. -/
  equivalence : Sheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≌
    Over (⟨F, hF⟩ : Sheaf J (Type v))
  /-- The inverse of the equivalence is the fibre construction
  `(G, φ) ↦ ((U, s) ↦ {t ∈ G(U) | φ(t) = s})` on underlying presheaves. -/
  fibers : equivalence.inverse ⋙
      sheafToPresheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≅
    Over.post (X := (⟨F, hF⟩ : Sheaf J (Type v))) (sheafToPresheaf J (Type v)) ⋙
      (overEquivPresheafCostructuredArrow F).functor
  /-- The functor of the equivalence followed by `Over.forget` is `j_!`, i.e. is left adjoint to
  restriction along the projection `j : C/F ⥤ C`. -/
  shriek : equivalence.functor ⋙ Over.forget (⟨F, hF⟩ : Sheaf J (Type v)) ⊣
    (CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J

end

namespace Stacks.Topos.Localized

@[expose] public section

/-- The canonical lift of `g : Y ⟶ X.left` to a morphism of `C/F` with target `X`. -/
abbrev liftHom (X : CostructuredArrow yoneda F) {Y : C} (g : Y ⟶ X.left) :
    CostructuredArrow.mk (yoneda.map g ≫ X.hom) ⟶ X :=
  CostructuredArrow.homMk g rfl

/-- **`j` is a discrete fibration**, in the form the topology needs: for a morphism `f` of `C/F`
with target `X`, the image under `j` of a sieve `S` of `X` contains `j(f)` exactly when `S`
contains `f` itself. -/
lemma mem_functorPushforward_proj_iff {X Z : CostructuredArrow yoneda F} (S : Sieve X)
    (f : Z ⟶ X) :
    (S.functorPushforward (CostructuredArrow.proj yoneda F)).arrows f.left ↔ S.arrows f := by
  constructor
  · rintro ⟨W, h, a, hS, e⟩
    have w : yoneda.map a ≫ W.hom = Z.hom := by
      rw [← CostructuredArrow.w f, show f.left = a ≫ h.left from e, yoneda.map_comp,
        Category.assoc, CostructuredArrow.w h]
    have hk : (CostructuredArrow.homMk a w : Z ⟶ W) ≫ h = f := by
      ext
      simpa using e.symm
    exact hk ▸ S.downward_closed hS _
  · exact fun hf => ⟨Z, f, 𝟙 Z.left, hf, by simp⟩

/-- `mem_functorPushforward_proj_iff` at the canonical lift of `g`. -/
lemma mem_functorPushforward_proj_lift_iff {X : CostructuredArrow yoneda F} (S : Sieve X)
    {Y : C} (g : Y ⟶ X.left) :
    (S.functorPushforward (CostructuredArrow.proj yoneda F)).arrows g ↔ S.arrows (liftHom F X g) :=
  mem_functorPushforward_proj_iff F S (liftHom F X g)

/-- `Sieve.functorPullback j` undoes `Sieve.functorPushforward j`. -/
lemma functorPullback_functorPushforward_proj {X : CostructuredArrow yoneda F}
    (S : Sieve X) :
    (S.functorPushforward (CostructuredArrow.proj yoneda F)).functorPullback
        (CostructuredArrow.proj yoneda F) =
      S :=
  Sieve.ext fun _ f => mem_functorPushforward_proj_iff F S f

/-- `Sieve.functorPushforward j` undoes `Sieve.functorPullback j`. -/
lemma functorPushforward_functorPullback_proj {X : CostructuredArrow yoneda F}
    (T : Sieve X.left) :
    (T.functorPullback (CostructuredArrow.proj yoneda F)).functorPushforward
        (CostructuredArrow.proj yoneda F) =
      T :=
  Sieve.ext fun _ g => mem_functorPushforward_proj_lift_iff F _ g

/-- Pushing forward along `j` commutes with pullback. -/
lemma functorPushforward_proj_pullback {X₁ X₂ : CostructuredArrow yoneda F} (f : X₁ ⟶ X₂)
    (S : Sieve X₂) :
    (S.pullback f).functorPushforward (CostructuredArrow.proj yoneda F) =
      (S.functorPushforward (CostructuredArrow.proj yoneda F)).pullback
        ((CostructuredArrow.proj yoneda F).map f) := by
  rw [←
    functorPushforward_functorPullback_proj F
      ((S.functorPushforward (CostructuredArrow.proj yoneda F)).pullback
        ((CostructuredArrow.proj yoneda F).map f)),
    Sieve.functorPullback_pullback, functorPullback_functorPushforward_proj]

/-! ### The site `C/F` -/

/-- The topology on `C/F` whose covering sieves are those whose image under `j` is covering. -/
def topology : GrothendieckTopology (CostructuredArrow yoneda F) where
  sieves X := {S | S.functorPushforward (CostructuredArrow.proj yoneda F) ∈ J X.left}
  top_mem' X := by
    rw [Set.mem_ofPred_eq, Sieve.functorPushforward_top]
    exact J.top_mem X.left
  pullback_stable' X₁ X₂ S f hS := by
    rw [Set.mem_ofPred_eq, functorPushforward_proj_pullback]
    exact J.pullback_stable _ hS
  transitive' X S hS R hR :=
    J.transitive hS _ fun Y g hg => by
      have h :
        (R.pullback (liftHom F X g)).functorPushforward (CostructuredArrow.proj yoneda F) ∈ J Y :=
        hR ((mem_functorPushforward_proj_lift_iff F S g).1 hg)
      rwa [functorPushforward_proj_pullback] at h

/-- A sieve `S` of `X` covers in `topology F J` exactly when its image under `j` covers `X.left`
in `J`. -/
lemma mem_topology_iff (X : CostructuredArrow yoneda F) (S : Sieve X) :
    S ∈ topology F J X ↔ S.functorPushforward (CostructuredArrow.proj yoneda F) ∈ J X.left :=
  Iff.rfl

/-- **Stacks 0791, first assertion.** The source's coverings of `C/F` already form a topology: the
topology they generate consists of exactly the sieves whose image under `j` is covering. -/
lemma restrictedTopology_eq_topology :
    (CostructuredArrow.proj yoneda F).restrictedTopology J = topology F J := by
  refine le_antisymm ?_ (fun X S hS => ?_)
  · rw [Functor.restrictedTopology, Precoverage.toGrothendieck_eq_sInf]
    refine sInf_le fun X R hR => ?_
    rwa [mem_topology_iff, ← Sieve.generate_map_eq_functorPushforward]
  · exact Functor.mem_restrictedTopology_of_functorPushforward_mem hS

/-- **Stacks 0791, first assertion.** -/
lemma mem_restrictedTopology_iff (X : CostructuredArrow yoneda F) (S : Sieve X) :
    S ∈ (CostructuredArrow.proj yoneda F).restrictedTopology J X ↔
      Sieve.functorPushforward (CostructuredArrow.proj yoneda F) S ∈ J X.left := by
  rw [restrictedTopology_eq_topology]
  exact mem_topology_iff F J X S

/-- **Stacks 0791, cocontinuity of `j`.** -/
instance isCocontinuous_proj :
    (CostructuredArrow.proj yoneda F).IsCocontinuous (topology F J) J where
  cover_lift {X} {S} hS := by
    rwa [mem_topology_iff, functorPushforward_functorPullback_proj]

/-- The projection `j : C/F ⥤ C` sends covering sieves of `topology F J` to covering sieves of
`J`. -/
lemma coverPreserving_proj :
    CoverPreserving (topology F J) J (CostructuredArrow.proj yoneda F) where
  cover_preserve hS := hS

/-- The canonical lift of `f₁` receives `f₂` as well, because `f₁ ≫ j(g₁) = f₂ ≫ j(g₂)`. -/
lemma compatiblePreserving_proj :
    CompatiblePreserving.{max u v} J (CostructuredArrow.proj yoneda F) where
  compatible {_ Z _ _ hx Y₁ Y₂ _ f₁ f₂ g₁ g₂ hg₁ hg₂ h} :=
    hx (liftHom F Y₁ f₁)
      (CostructuredArrow.homMk f₂
        (show yoneda.map f₂ ≫ Y₂.hom = yoneda.map f₁ ≫ Y₁.hom by
          rw [← CostructuredArrow.w g₂, ← CostructuredArrow.w g₁, ← yoneda.map_comp_assoc, ←
            yoneda.map_comp_assoc, show f₁ ≫ g₁.left = f₂ ≫ g₂.left from h]))
      hg₁ hg₂ (by ext; exact h)

/-- **Stacks 0791, continuity of `j`.** -/
instance isContinuous_proj :
    (CostructuredArrow.proj yoneda F).IsContinuous (topology F J) J :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_proj F J)
    (coverPreserving_proj F J)

/-- The projection `j : C/F ⥤ C` is cocontinuous for the topology on `C/F` induced from `J`. -/
instance isCocontinuous_proj_restricted :
    (CostructuredArrow.proj yoneda F).IsCocontinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J := by
  rw [restrictedTopology_eq_topology]
  infer_instance

/-- The projection `j : C/F ⥤ C` is continuous for the topology on `C/F` induced from `J`. -/
instance isContinuous_proj_restricted :
    (CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J := by
  rw [restrictedTopology_eq_topology]
  infer_instance

/-! ### The fibre presheaf of a map to `F` -/

section Fibre

variable {K : GrothendieckTopology (CostructuredArrow yoneda F)} {G : Cᵒᵖ ⥤ Type v}

/-- **Lying in a fibre of `φ : G ⟶ F` is a local condition**, the converse of
`OverPresheafAux.MakesOverArrow.map₂`: if the restriction of `t` along `p g` lies in the fibre of
`φ` over the restriction of `s`, for every `g` in a presieve `R` for which `p^{-1}F` is separated,
then `t` lies in the fibre of `φ` over `s`. -/
lemma makesOverArrow_of_isSeparatedFor {D : Type*} [Category D] (p : D ⥤ C) (φ : G ⟶ F)
    {X : D} {R : Presieve X} (hR : Presieve.IsSeparatedFor (p.op ⋙ F) R)
    {s : yoneda.obj (p.obj X) ⟶ F} {t : G.obj (op (p.obj X))}
    (h :
      ∀ ⦃Y : D⦄ ⦃g : Y ⟶ X⦄,
        R g → MakesOverArrow φ (yoneda.map (p.map g) ≫ s) (G.map (p.map g).op t)) :
    MakesOverArrow φ s t := by
  refine ⟨hR.ext fun {Y} {g} hg => ?_⟩
  dsimp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  rw [← NatTrans.naturality_apply φ (p.map g).op t, (h hg).app, yonedaEquiv_naturality]

/-- **The fibre presheaf `(U, s) ↦ {t ∈ G(U) | φ(t) = s}` of `φ : G ⟶ F` is a sheaf** as soon as
`G` and `F` are: a compatible family amalgamates in the sheaf `j^{-1}G`, and the amalgamation lies
in the fibre because `j^{-1}F` is separated. -/
lemma isSheaf_restrictedYonedaObj [(CostructuredArrow.proj yoneda F).IsContinuous K J]
    (hF : Presieve.IsSheaf J F) (φ : G ⟶ F) (hG : Presieve.IsSheaf J G) :
    Presieve.IsSheaf K (restrictedYonedaObj φ) := by
  have hGj : Presieve.IsSheaf K ((CostructuredArrow.proj yoneda F).op ⋙ G) :=
    Functor.op_comp_isSheaf_of_isSheaf_type _ _ hG
  have hFj : Presieve.IsSeparated K ((CostructuredArrow.proj yoneda F).op ⋙ F) :=
    (Functor.op_comp_isSheaf_of_isSheaf_type _ _ hF).isSeparated
  intro X S hS x hx
  obtain ⟨t, ht, htu⟩ :=
    hGj S hS (fun Y g hg => (x g hg).val)
      (fun {Y₁ Y₂ Z} g₁ g₂ f₁ f₂ h₁ h₂ e => congrArg OverArrows.val (hx g₁ g₂ h₁ h₂ e))
  have ht' :
    ∀ {Y : CostructuredArrow yoneda F} (g : Y ⟶ X) (hg : S.arrows g),
      G.map g.left.op t = (x g hg).val :=
    fun g hg => ht g hg
  have hmem : MakesOverArrow φ X.hom t :=
    makesOverArrow_of_isSeparatedFor F (CostructuredArrow.proj yoneda F) φ (hFj S hS)
      fun {Y} {g} hg =>
      ⟨by
        dsimp only [CostructuredArrow.proj_obj, CostructuredArrow.proj_map]
        rw [ht' g hg, OverArrows.app_val (x g hg), CostructuredArrow.w g]⟩
  refine ⟨⟨t, hmem⟩, fun {Y} g hg => OverArrows.ext (ht' g hg), fun y hy => OverArrows.ext ?_⟩
  exact htu y.val fun {Y} g hg => congrArg OverArrows.val (hy g hg)

/-- **Conversely, if the fibre presheaf of `φ : G ⟶ F` is a sheaf, so is `G`.** A compatible
family in `G` pushes to one in `F`, which glues to a section `s` of `F`; the family then lives in
the fibre over `s` and glues there. -/
lemma isSheaf_of_isSheaf_restrictedYonedaObj
    [(CostructuredArrow.proj yoneda F).IsCocontinuous K J] (hF : Presieve.IsSheaf J F) (φ : G ⟶ F)
    (h : Presieve.IsSheaf K (restrictedYonedaObj φ)) : Presieve.IsSheaf J G := by
  intro U S hS x hx
  obtain ⟨s, hs, -⟩ :=
    hF S hS (fun V f hf => φ.app (op V) (x f hf))
      (fun {V₁ V₂ W} g₁ g₂ f₁ f₂ h₁ h₂ e => by
        rw [← NatTrans.naturality_apply φ g₁.op (x f₁ h₁), ←
          NatTrans.naturality_apply φ g₂.op (x f₂ h₂)]
        exact congrArg _ (hx g₁ g₂ h₁ h₂ e))
  have key :
    ∀ {Y : CostructuredArrow yoneda F} (g : Y ⟶ CostructuredArrow.mk (yonedaEquiv.symm s))
      (hg : S.arrows g.left), MakesOverArrow φ Y.hom (x g.left hg) := by
    intro Y g hg
    refine ⟨(hs g.left hg).symm.trans ?_⟩
    have hw : yoneda.map g.left ≫ yonedaEquiv.symm s = Y.hom := CostructuredArrow.w g
    rw [← hw, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  have hSX :=
    (CostructuredArrow.proj yoneda F).cover_lift K J (U :=
      CostructuredArrow.mk (yonedaEquiv.symm s)) hS
  obtain ⟨t, ht, htu⟩ :=
    h _ hSX (fun Y g hg => ⟨x g.left hg, key g hg⟩)
      (fun {Y₁ Y₂ Z} g₁ g₂ f₁ f₂ h₁ h₂ e =>
        OverArrows.ext (hx g₁.left g₂.left h₁ h₂ (congrArg CommaMorphism.left e)))
  refine ⟨t.val, fun {V} f hf => ?_, fun y hy => ?_⟩
  · exact congrArg OverArrows.val (ht (liftHom F (CostructuredArrow.mk (yonedaEquiv.symm s)) f) hf)
  · have hmem : MakesOverArrow φ (CostructuredArrow.mk (yonedaEquiv.symm s)).hom y :=
      makesOverArrow_of_isSeparatedFor F (𝟭 C) φ (hF S hS).isSeparatedFor fun {V} {f} hf => by
        dsimp only [Functor.id_map, CostructuredArrow.mk_hom_eq_self]
        rw [hy f hf]
        exact key (liftHom F (CostructuredArrow.mk (yonedaEquiv.symm s)) f) hf
    refine congrArg OverArrows.val (htu ⟨y, hmem⟩ fun {Y} g hg => OverArrows.ext ?_)
    exact hy g.left hg

end Fibre

/-! ### The equivalence `Sh(C/F) ≌ Sh(C)/F` -/

section Equivalence

variable (hF : Presheaf.IsSheaf J F)

/-- The source's functor `Sh(C)/F ⥤ Sh(C/F)`, `(G, φ) ↦ ((U, s) ↦ {t ∈ G(U) | φ(t) = s})`: the
restriction of `overEquivPresheafCostructuredArrow F` to the subcategories of sheaves. -/
def fiberFunctor :
    Over (⟨F, hF⟩ : Sheaf J (Type v)) ⥤
      Sheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) :=
  ObjectProperty.lift _
    (Over.post (sheafToPresheaf J (Type v)) ⋙ (overEquivPresheafCostructuredArrow F).functor)
    (fun T =>
      (isSheaf_iff_isSheaf_of_type _ _).2
        (isSheaf_restrictedYonedaObj F J ((isSheaf_iff_isSheaf_of_type _ _).1 hF) T.hom.hom
          ((isSheaf_iff_isSheaf_of_type _ _).1 T.left.property)))

/-- The fibre functor is faithful. -/
instance : (fiberFunctor F J hF).Faithful := by
  unfold fiberFunctor
  infer_instance

/-- The fibre functor is full. -/
instance : (fiberFunctor F J hF).Full := by
  unfold fiberFunctor
  infer_instance

/-- The fibre functor is essentially surjective. -/
instance : (fiberFunctor F J hF).EssSurj where
  mem_essImage H := by
    have hT :
      Presheaf.IsSheaf J ((overEquivPresheafCostructuredArrow F).inverse.obj H.obj).left := by
      refine
        (isSheaf_iff_isSheaf_of_type _ _).2
          (isSheaf_of_isSheaf_restrictedYonedaObj F J (K :=
            (CostructuredArrow.proj yoneda F).restrictedTopology J)
            ((isSheaf_iff_isSheaf_of_type _ _).1 hF)
            ((overEquivPresheafCostructuredArrow F).inverse.obj H.obj).hom ?_)
      exact
        (isSheaf_iff_isSheaf_of_type _ _).1
          ((Presheaf.isSheaf_of_iso_iff
                ((overEquivPresheafCostructuredArrow F).counitIso.app H.obj)).2
            H.property)
    refine
      ⟨Over.mk (Y := (⟨_, hT⟩ : Sheaf J (Type v)))
          (ObjectProperty.homMk ((overEquivPresheafCostructuredArrow F).inverse.obj H.obj).hom),
        ?_⟩
    exact
      ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
          ((overEquivPresheafCostructuredArrow F).counitIso.app H.obj)⟩

/-- The fibre functor is an equivalence of categories. -/
instance : (fiberFunctor F J hF).IsEquivalence where

/-- **Stacks 0791**, the equivalence `Sh(C/F) ≌ Sh(C)/F`, whose inverse is the fibre functor. -/
noncomputable def sheafEquivalence :
    Sheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≌
      Over (⟨F, hF⟩ : Sheaf J (Type v)) :=
  (fiberFunctor F J hF).asEquivalence.symm

/-- **Stacks 0791**, the equivalence `Sh(C/F) ≌ Sh(C)/F` is the fibre construction: its inverse
sends an object `φ : G ⟶ F` of `Sh(C)/F` to the sheaf `(U, s) ↦ {t ∈ G(U) | φ(t) = s}` on `C/F`,
which on underlying presheaves is `overEquivPresheafCostructuredArrow F`. The inverse of
`sheafEquivalence` is the fibre functor by construction, so this is the identity isomorphism. -/
public noncomputable def sheafEquivalenceFibers :
    (sheafEquivalence F J hF).inverse ⋙
        sheafToPresheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≅
      Over.post (X := (⟨F, hF⟩ : Sheaf J (Type v))) (sheafToPresheaf J (Type v)) ⋙
        (overEquivPresheafCostructuredArrow F).functor :=
  Iso.refl _

section HomEquiv

variable {G : Cᵒᵖ ⥤ Type v}

/-- The object `(U, φ(x))` of `C/F` in whose fibre a section `x` of `G` over `U` lies. -/
abbrev fiberObj (φ : G ⟶ F) {U : Cᵒᵖ} (x : G.obj U) : CostructuredArrow yoneda F :=
  CostructuredArrow.mk (yonedaEquiv.symm (φ.app U x))

/-- A section `x` of `G` over `U`, as an element of the fibre of `φ` over `(U, φ(x))`. -/
def fiberElem (φ : G ⟶ F) {U : Cᵒᵖ} (x : G.obj U) : OverArrows φ (fiberObj F φ x).hom :=
  ⟨x, ⟨by simp⟩⟩

/-- Pulling back `φ(x)` along `g` gives `φ(g^*x)`: the triangle defining `fiberMap`. -/
lemma fiberMap_w (φ : G ⟶ F) {U V : Cᵒᵖ} (g : U ⟶ V) (x : G.obj U) :
    yoneda.map g.unop ≫ yonedaEquiv.symm (φ.app U x) = yonedaEquiv.symm (φ.app V (G.map g x)) := by
  rw [NatTrans.naturality_apply φ g x]
  exact yonedaEquiv_symm_naturality_left g.unop F (φ.app U x)

/-- The canonical morphism `(V, φ(g^*x)) ⟶ (U, φ(x))` of `C/F` above `g : V ⟶ U`. -/
def fiberMap (φ : G ⟶ F) {U V : Cᵒᵖ} (g : U ⟶ V) (x : G.obj U) :
    fiberObj F φ (G.map g x) ⟶ fiberObj F φ x :=
  CostructuredArrow.homMk g.unop (fiberMap_w F φ g x)

/-- The canonical morphism `(U, φ(t)) ⟶ (U, s)` of `C/F` above the identity of `U`, attached to an
element `t` of the fibre of `φ` over `(U, s)`. -/
def fiberHomId (φ : G ⟶ F) {X : CostructuredArrow yoneda F} (p : OverArrows φ X.hom) :
    fiberObj F φ p.val ⟶ X :=
  CostructuredArrow.homMk (𝟙 X.left) (by simp [p.app_val])

/-- Restricting an element `p` of the fibre of `φ` over `X` along `fiberHomId F φ p` gives `p`
regarded as an element of the fibre over `fiberObj F φ p.val`. -/
lemma map_fiberHomId_self (φ : G ⟶ F) {X : CostructuredArrow yoneda F}
    (p : OverArrows φ X.hom) :
    (restrictedYonedaObj φ).map (fiberHomId F φ p).op p = fiberElem F φ p.val :=
  OverArrows.ext (show G.map (𝟙 X.left).op p.val = p.val by simp)

/-- A morphism from the fibre presheaf of `φ : G ⟶ F` to `j^{-1}P` is a morphism `G ⟶ P`: every
section of `G` lies in exactly one fibre. -/
def homEquivFiber (φ : G ⟶ F) (P : Cᵒᵖ ⥤ Type v) :
    (G ⟶ P) ≃ (restrictedYonedaObj φ ⟶ (CostructuredArrow.proj yoneda F).op ⋙ P)
    where
  toFun β :=
    { app := fun X => ↾fun p => β.app (op X.unop.left) p.val
      naturality := fun X Y g => by
        ext p
        exact NatTrans.naturality_apply β g.unop.left.op p.val }
  invFun α :=
    { app := fun U => ↾fun x => α.app (op (fiberObj F φ x)) (fiberElem F φ x)
      naturality := fun U V g => by
        ext x
        exact NatTrans.naturality_apply α (fiberMap F φ g x).op (fiberElem F φ x) }
  left_inv β := rfl
  right_inv α := by
    ext X p
    have key :
      α.app (op (fiberObj F φ p.val)) ((restrictedYonedaObj φ).map (fiberHomId F φ p).op p) =
        P.map (𝟙 X.unop.left).op (α.app X p) :=
      NatTrans.naturality_apply α (fiberHomId F φ p).op p
    exact
      (TypeCat.congr_arg (α.app (op (fiberObj F φ p.val))) (map_fiberHomId_self F φ p).symm).trans
        (key.trans (by simp))

end HomEquiv

/-- The right adjoint `j^{-1}` of the statement, i.e. restriction along `j`. -/
abbrev restrictionFunctor :
    Sheaf J (Type v) ⥤ Sheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) :=
  (CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
    ((CostructuredArrow.proj yoneda F).restrictedTopology J) J

/-- The sheaf level form of `homEquivFiber`: a morphism of sheaves `T.left ⟶ G` over `C` is a
morphism `fiberFunctor T ⟶ j^{-1}G` over `C/F`. -/
def homEquivFiberSheaf (T : Over (⟨F, hF⟩ : Sheaf J (Type v))) (G : Sheaf J (Type v)) :
    (T.left ⟶ G) ≃ ((fiberFunctor F J hF).obj T ⟶ (restrictionFunctor F J).obj G) :=
  Sheaf.homEquiv.trans
    ((homEquivFiber F T.hom.hom G.obj).trans
      (Sheaf.homEquiv (X := (fiberFunctor F J hF).obj T) (Y :=
          (restrictionFunctor F J).obj G)).symm)

/-- The hom bijection underlying `forgetAdjunction`: a morphism of sheaves `T.left ⟶ G` over `C` is
a morphism `T ⟶ j^{-1}G` in `Over F`, the sheaf `j^{-1}G` on `C/F` being read in `Over F` along the
equivalence `fiberFunctor`. -/
noncomputable def homEquivShriek (T : Over (⟨F, hF⟩ : Sheaf J (Type v)))
    (G : Sheaf J (Type v)) :
    (T.left ⟶ G) ≃ (T ⟶ (restrictionFunctor F J ⋙ (fiberFunctor F J hF).inv).obj G) :=
  (homEquivFiberSheaf F J hF T G).trans
    ((fiberFunctor F J hF).asEquivalence.toAdjunction.homEquiv T ((restrictionFunctor F J).obj G))

/-- `homEquivShriek` is natural in `T`: `homEquivFiberSheaf` is, and so is the hom bijection of the
adjunction `fiberFunctor ⊣ fiberFunctor.inv`. -/
lemma homEquivShriek_naturality_left {T T' : Over (⟨F, hF⟩ : Sheaf J (Type v))}
    {G : Sheaf J (Type v)} (f : T' ⟶ T) (β : T.left ⟶ G) :
    homEquivShriek F J hF T' G (f.left ≫ β) = f ≫ homEquivShriek F J hF T G β :=
  Adjunction.homEquiv_naturality_left (fiberFunctor F J hF).asEquivalence.toAdjunction f
    (homEquivFiberSheaf F J hF T G β)

/-- `homEquivShriek_naturality_left`, in the form `Adjunction.mkOfHomEquiv` asks for. -/
lemma homEquivShriek_naturality_left_symm {T T' : Over (⟨F, hF⟩ : Sheaf J (Type v))}
    {G : Sheaf J (Type v)} (f : T' ⟶ T)
    (g : T ⟶ (restrictionFunctor F J ⋙ (fiberFunctor F J hF).inv).obj G) :
    (homEquivShriek F J hF T' G).symm (f ≫ g) = f.left ≫ (homEquivShriek F J hF T G).symm g := by
  apply (homEquivShriek F J hF T' G).injective
  rw [Equiv.apply_symm_apply, homEquivShriek_naturality_left, Equiv.apply_symm_apply]

/-- `homEquivShriek` is natural in `G`. -/
lemma homEquivShriek_naturality_right (T : Over (⟨F, hF⟩ : Sheaf J (Type v)))
    {G G' : Sheaf J (Type v)} (β : T.left ⟶ G) (g : G ⟶ G') :
    homEquivShriek F J hF T G' (β ≫ g) =
      homEquivShriek F J hF T G β ≫ (restrictionFunctor F J ⋙ (fiberFunctor F J hF).inv).map g :=
  Adjunction.homEquiv_naturality_right (fiberFunctor F J hF).asEquivalence.toAdjunction
    (homEquivFiberSheaf F J hF T G β) ((restrictionFunctor F J).map g)

/-- `Over.forget` on `Sh(C)/F` is left adjoint to `j^{-1}` read in `Over F` along the equivalence
`fiberFunctor`. -/
noncomputable def forgetAdjunction :
    Over.forget (⟨F, hF⟩ : Sheaf J (Type v)) ⊣
      restrictionFunctor F J ⋙ (fiberFunctor F J hF).inv :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquivShriek F J hF
      homEquiv_naturality_left_symm := fun f g => homEquivShriek_naturality_left_symm F J hF f g
      homEquiv_naturality_right := fun f g => homEquivShriek_naturality_right F J hF _ f g }

/-- The counit of `fiberFunctor` identifies the right adjoint of `forgetAdjunction`, read back in
`Sh(C/F)`, with `j^{-1}`. -/
noncomputable def restrictionInvCompInverseIso :
    (restrictionFunctor F J ⋙ (fiberFunctor F J hF).inv) ⋙ (sheafEquivalence F J hF).inverse ≅
      restrictionFunctor F J :=
  Functor.isoWhiskerLeft (restrictionFunctor F J) (fiberFunctor F J hF).asEquivalence.counitIso

/-- **Stacks 0791**, the last assertion: `j_!`, i.e. the functor of `sheafEquivalence` followed by
`Over.forget`, is left adjoint to `j^{-1}`. -/
noncomputable def shriekAdjunction :
    (sheafEquivalence F J hF).functor ⋙ Over.forget (⟨F, hF⟩ : Sheaf J (Type v)) ⊣
      (CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
        ((CostructuredArrow.proj yoneda F).restrictedTopology J) J :=
  ((sheafEquivalence F J hF).toAdjunction.comp (forgetAdjunction F J hF)).ofNatIsoRight
    (restrictionInvCompInverseIso F J hF)

/-- The coherence identity behind `homEquiv_shriekAdjunction_counit_comp`, for an arbitrary
equivalence: the unit, the counit followed by its inverse, and the inverse unit compose away. -/
private theorem equivalence_unit_comp_map_comp {A : Type*} [Category A] {B : Type*} [Category B]
    (E : B ≌ A) {T : A} {Y : B} (ξ : E.inverse.obj T ⟶ Y) :
    E.unit.app (E.inverse.obj T) ≫
        E.inverse.map (E.counit.app T ≫ E.counitInv.app T ≫ E.functor.map ξ) ≫
          E.unitInv.app Y =
      ξ := by
  simp

/-- **The hom bijection of `shriekAdjunction` is the fibre hom bijection.** A morphism
`β : T.left ⟶ G` of sheaves on `C`, read as a morphism out of `j_!` of the fibre sheaf of `T` and
transposed across `shriekAdjunction`, is the fibre transpose `homEquivFiberSheaf` of `β`.

Everything cancels: the twisting isomorphism and the unit of `sheafEquivalence` cancel against
each other by `Equivalence.unit_inverse_comp` and `Equivalence.unit_app_inverse`, and the
naturality of `homEquivFiberSheaf` in `T` absorbs the counit. -/
private theorem homEquiv_shriekAdjunction_counit_comp
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J]
    (T : Over (⟨F, hF⟩ : Sheaf J (Type v))) (G : Sheaf J (Type v)) (β : T.left ⟶ G) :
    (shriekAdjunction F J hF).homEquiv ((sheafEquivalence F J hF).inverse.obj T) G
        ((Over.forget (⟨F, hF⟩ : Sheaf J (Type v))).map
            ((sheafEquivalence F J hF).counit.app T) ≫ β) =
      homEquivFiberSheaf F J hF T G β := by
  change ((((sheafEquivalence F J hF).toAdjunction.comp (forgetAdjunction F J hF)).ofNatIsoRight
    (restrictionInvCompInverseIso F J hF)).homEquiv _ G) _ = _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (sheafEquivalence F J hF).toAdjunction.homEquiv _ _
      ((forgetAdjunction F J hF).homEquiv _ G
        ((Over.forget (⟨F, hF⟩ : Sheaf J (Type v))).map
          ((sheafEquivalence F J hF).counit.app T) ≫ β)) ≫
      (restrictionInvCompInverseIso F J hF).hom.app G = _
  rw [forgetAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change (sheafEquivalence F J hF).toAdjunction.homEquiv _ _
      (homEquivShriek F J hF _ G
        (((sheafEquivalence F J hF).counit.app T).left ≫ β)) ≫
      (restrictionInvCompInverseIso F J hF).hom.app G = _
  rw [homEquivShriek_naturality_left, Adjunction.homEquiv_unit,
    show (restrictionInvCompInverseIso F J hF).hom.app G =
      (sheafEquivalence F J hF).unitInv.app ((restrictionFunctor F J).obj G) from rfl]
  change (sheafEquivalence F J hF).unit.app _ ≫
      (sheafEquivalence F J hF).inverse.map
        ((sheafEquivalence F J hF).counit.app T ≫ homEquivShriek F J hF T G β) ≫
      (sheafEquivalence F J hF).unitInv.app _ = _
  have hz : homEquivShriek F J hF T G β =
      (sheafEquivalence F J hF).counitInv.app T ≫
        (sheafEquivalence F J hF).functor.map (homEquivFiberSheaf F J hF T G β) :=
    Adjunction.homEquiv_unit (fiberFunctor F J hF).asEquivalence.toAdjunction T
      ((restrictionFunctor F J).obj G) (homEquivFiberSheaf F J hF T G β)
  rw [hz]
  exact equivalence_unit_comp_map_comp (sheafEquivalence F J hF)
    (homEquivFiberSheaf F J hF T G β)

/-- **The counit of `shriekAdjunction` is the unit of the equivalence, transposed through the
fibre hom bijection.** The counit at `G` is the morphism `j_!j^{-1}G ⟶ G` of sheaves on `C`
corresponding, under the bijection `homEquivFiberSheaf` between morphisms `T.left ⟶ G` and
morphisms of sheaves on `C/F` from the fibre sheaf of `T` to `j^{-1}G`, to the canonical
identification of the fibre sheaf of `j_!j^{-1}G` with `j^{-1}G`.

All the coherence in `shriekAdjunction` cancels: the natural isomorphism it is twisted by is the
unit of `sheafEquivalence`, so transposing it across `sheafEquivalence.toAdjunction` gives the
identity by the triangle identity, and the composite adjunction's hom bijection then contributes
only the counit of `fiberFunctor`. -/
private theorem shriekAdjunction_counit_app
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J] (G : Sheaf J (Type v)) :
    (shriekAdjunction F J hF).counit.app G =
      (homEquivFiberSheaf F J hF
          ((sheafEquivalence F J hF).functor.obj ((restrictionFunctor F J).obj G)) G).symm
        ((sheafEquivalence F J hF).unitInv.app ((restrictionFunctor F J).obj G)) := by
  rw [← Adjunction.homEquiv_symm_id]
  change ((((sheafEquivalence F J hF).toAdjunction.comp (forgetAdjunction F J hF)).ofNatIsoRight
      (restrictionInvCompInverseIso F J hF)).homEquiv _ G).symm (𝟙 _) = _
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.id_comp, Adjunction.comp_homEquiv]
  have hinner : ((sheafEquivalence F J hF).toAdjunction.homEquiv
        ((restrictionFunctor F J).obj G)
        ((restrictionFunctor F J ⋙ (fiberFunctor F J hF).inv).obj G)).symm
      ((restrictionInvCompInverseIso F J hF).inv.app G) =
      𝟙 ((sheafEquivalence F J hF).functor.obj ((restrictionFunctor F J).obj G)) := by
    rw [Adjunction.homEquiv_counit,
      show (restrictionInvCompInverseIso F J hF).inv.app G =
        (sheafEquivalence F J hF).unit.app ((restrictionFunctor F J).obj G) from rfl]
    exact (sheafEquivalence F J hF).functor_unit_comp _
  change ((forgetAdjunction F J hF).homEquiv _ G).symm
      (((sheafEquivalence F J hF).toAdjunction.homEquiv _ _).symm
        ((restrictionInvCompInverseIso F J hF).inv.app G)) = _
  rw [hinner, forgetAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change (homEquivFiberSheaf F J hF _ G).symm
      (((fiberFunctor F J hF).asEquivalence.toAdjunction.homEquiv _
        ((restrictionFunctor F J).obj G)).symm (𝟙 _)) = _
  rw [Adjunction.homEquiv_symm_id]
  rfl

/-- The fibre identification of a morphism `β : T.left ⟶ G`, transposed by `homEquivFiberSheaf`, is
evaluation of `β` on sections. -/
private theorem app_sheafEquivalenceFibers_inv_comp_homEquivFiberSheaf
    (T : Over (⟨F, hF⟩ : Sheaf J (Type v))) (G : Sheaf J (Type v)) (β : T.left ⟶ G)
    (X : CostructuredArrow yoneda F) (p : OverArrows T.hom.hom X.hom) :
    ((sheafEquivalenceFibers F J hF).inv.app T ≫ (homEquivFiberSheaf F J hF T G β).hom).app
        (op X) p =
      β.hom.app (op X.left) p.val := by
  simp only [sheafEquivalenceFibers, Iso.refl_inv, NatTrans.id_app]
  rfl

/-- The fibre identification of `j_!j^{-1}G` with `j^{-1}G` is evaluation of the counit of
`shriekAdjunction`, for the concrete equivalence of this section. -/
private theorem app_sheafEquivalenceFibers_inv_comp_unitInv
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J]
    (G : Sheaf J (Type v)) (X : CostructuredArrow yoneda F)
    (p : OverArrows ((sheafEquivalence F J hF).functor.obj
        (((CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
          ((CostructuredArrow.proj yoneda F).restrictedTopology J) J).obj G)).hom.hom X.hom) :
    ((sheafEquivalenceFibers F J hF).inv.app
          ((sheafEquivalence F J hF).functor.obj
            (((CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
              ((CostructuredArrow.proj yoneda F).restrictedTopology J) J).obj G)) ≫
        ((sheafEquivalence F J hF).unitInv.app
            (((CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
              ((CostructuredArrow.proj yoneda F).restrictedTopology J) J).obj G)).hom).app
        (op X) p =
      ((shriekAdjunction F J hF).counit.app G).hom.app (op X.left) p.val := by
  have h := app_sheafEquivalenceFibers_inv_comp_homEquivFiberSheaf F J hF _ G
    ((shriekAdjunction F J hF).counit.app G) X p
  rwa [(Equiv.eq_symm_apply _).1 (shriekAdjunction_counit_app F J hF G)] at h

/-- The transpose across `shriekAdjunction` of a morphism `β : T.left ⟶ G`, read on the fibre
sheaf of `T`, is evaluation of `β`, for the concrete equivalence of this section. -/
private theorem app_sheafEquivalenceFibers_inv_comp_homEquiv
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J]
    (T : Over (⟨F, hF⟩ : Sheaf J (Type v))) (G : Sheaf J (Type v)) (β : T.left ⟶ G)
    (X : CostructuredArrow yoneda F) (p : OverArrows T.hom.hom X.hom) :
    ((sheafEquivalenceFibers F J hF).inv.app T ≫
        ((shriekAdjunction F J hF).homEquiv ((sheafEquivalence F J hF).inverse.obj T) G
            ((Over.forget (⟨F, hF⟩ : Sheaf J (Type v))).map
              ((sheafEquivalence F J hF).counit.app T) ≫ β)).hom).app (op X) p =
      β.hom.app (op X.left) p.val := by
  rw [homEquiv_shriekAdjunction_counit_comp]
  exact app_sheafEquivalenceFibers_inv_comp_homEquivFiberSheaf F J hF T G β X p

/-- **Stacks 0791**, the identification of `Sh(C/F)` with `Sh(C)/F`, as data: the equivalence
`sheafEquivalence`, the identification `sheafEquivalenceFibers` of its inverse with the fibre
construction, and the adjunction `shriekAdjunction` exhibiting its functor followed by
`Over.forget` as `j_!`, all three for the same equivalence. -/
public noncomputable def
    _root_.CategoryTheory.Presheaf.IsSheaf.sheafEquivalenceCostructuredArrowYoneda
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf J F)
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J] :
    hF.SheafEquivalenceCostructuredArrowYoneda where
  equivalence := sheafEquivalence F J hF
  fibers := sheafEquivalenceFibers F J hF
  shriek := shriekAdjunction F J hF

end Equivalence

private theorem Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda_proof
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf J F) :
    (∀ (X : CostructuredArrow yoneda F) (S : Sieve X),
        S ∈ (CostructuredArrow.proj yoneda F).restrictedTopology J X ↔
          Sieve.functorPushforward (CostructuredArrow.proj yoneda F) S ∈ J X.left) ∧
      (∀ T : Over F,
        Presheaf.IsSheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J)
            ((overEquivPresheafCostructuredArrow F).functor.obj T) ↔
          Presheaf.IsSheaf J T.left) ∧
      ∃ (_ :
        (CostructuredArrow.proj yoneda F).IsContinuous
          ((CostructuredArrow.proj yoneda F).restrictedTopology J) J)
        (_ :
        (CostructuredArrow.proj yoneda F).IsCocontinuous
          ((CostructuredArrow.proj yoneda F).restrictedTopology J) J)
        (E :
        Sheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≌
          Over (⟨F, hF⟩ : Sheaf J (Type v))),
        Nonempty
            (E.inverse ⋙
                sheafToPresheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≅
              Over.post (X := (⟨F, hF⟩ : Sheaf J (Type v))) (sheafToPresheaf J (Type v)) ⋙
                (overEquivPresheafCostructuredArrow F).functor) ∧
          Nonempty
            (E.functor ⋙ Over.forget (⟨F, hF⟩ : Sheaf J (Type v)) ⊣
              (CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
                ((CostructuredArrow.proj yoneda F).restrictedTopology J) J) := by
  have hF' : Presieve.IsSheaf J F := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  refine
    ⟨mem_restrictedTopology_iff F J, fun T => ⟨fun h => ?_, fun h => ?_⟩, inferInstance,
      inferInstance, hF.sheafEquivalenceCostructuredArrowYoneda.equivalence,
      ⟨hF.sheafEquivalenceCostructuredArrowYoneda.fibers⟩,
      ⟨hF.sheafEquivalenceCostructuredArrowYoneda.shriek⟩⟩
  · exact
      (isSheaf_iff_isSheaf_of_type _ _).2
        (isSheaf_of_isSheaf_restrictedYonedaObj F J hF' T.hom
          ((isSheaf_iff_isSheaf_of_type _ _).1 h))
  · exact
      (isSheaf_iff_isSheaf_of_type _ _).2
        (isSheaf_restrictedYonedaObj F J hF' T.hom ((isSheaf_iff_isSheaf_of_type _ _).1 h))

end

end Stacks.Topos.Localized

@[expose] public section

open Stacks.Topos.Localized in
/-- **Stacks 0791: the fibre identification of `j_!j^{-1}G` is evaluation of the shriek counit.**
Write `E` for the equivalence of `sheafEquivalenceCostructuredArrowYoneda` and
`T = E(j^{-1}G)` for the object of `Sh(C)/F` whose source is `j_!j^{-1}G`. The equivalence
identifies the fibre sheaf of `T` with `j^{-1}G`: on underlying presheaves the fibre sheaf of `T`
is `(U, s) ↦ {t ∈ T.left(U) | T.hom(t) = s}` by the `fibers` field, and `E.inverse (E T) ≅ T` by
the unit. This says that the identification sends a section `t` of `j_!j^{-1}G` over `U` lying in
the fibre over `s ∈ F(U)` to its image under the counit of `j_! ⊣ j^{-1}`, a section of `G` over
`U`.

This is the statement connecting the package's two descriptions of `E`. A comparison built from
the *fibre* field — such as Stacks 04J4's identification of the inverse image of a relocalization
with a base change — and one built from the *counit* of `j_!` — such as Stacks 04IE's
identification of the inverse image of a localization with a product — are otherwise assertions
about data that nothing relates, even though both come from the same `E`. Both sides here are
morphisms out of the fibre presheaf of `T`, so comparing them needs no further transport. -/
@[stacks 0791 "the fibre identification of `j_!j^{-1}G` is evaluation of the counit of `j_!`"]
theorem Presheaf.IsSheaf.app_fibers_inv_comp_unitInv {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf J F)
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J]
    (G : Sheaf J (Type v)) (X : CostructuredArrow yoneda F)
    (p : OverArrows (hF.sheafEquivalenceCostructuredArrowYoneda.equivalence.functor.obj
        (((CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
          ((CostructuredArrow.proj yoneda F).restrictedTopology J) J).obj G)).hom.hom X.hom) :
    (hF.sheafEquivalenceCostructuredArrowYoneda.fibers.inv.app
          (hF.sheafEquivalenceCostructuredArrowYoneda.equivalence.functor.obj
            (((CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
              ((CostructuredArrow.proj yoneda F).restrictedTopology J) J).obj G)) ≫
        (hF.sheafEquivalenceCostructuredArrowYoneda.equivalence.unitInv.app
            (((CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
              ((CostructuredArrow.proj yoneda F).restrictedTopology J) J).obj G)).hom).app
        (op X) p =
      (hF.sheafEquivalenceCostructuredArrowYoneda.shriek.counit.app G).hom.app (op X.left)
        p.val :=
  app_sheafEquivalenceFibers_inv_comp_unitInv F J hF G X p

open Stacks.Topos.Localized in
/-- **Stacks 0791: transposing across `j_! ⊣ j^{-1}` is evaluation on fibres.** Let `T` be an
object of `Sh(C)/F` and `β : T.left ⟶ G` a morphism of sheaves on `C`. Reading `β` as a morphism
out of `j_!` of the fibre sheaf of `T` — which is what precomposing with the counit of the
equivalence does — and transposing it across `j_! ⊣ j^{-1}` gives a morphism from the fibre sheaf
of `T` to `j^{-1}G`. This says that that morphism sends a section `t` of `T.left` over `U` lying
in the fibre over `s ∈ F(U)` to `β(t)`.

This is the general form of `app_fibers_inv_comp_unitInv`, which is the case
`T = E(j^{-1}G)`, `β` the counit; it is what a comparison built from the `fibers` field has to be
fed through in order to be compared with one built from the counit of `j_!`, since the underlying
sheaf `T.left` of an object in the image of `E` has no description other than by its fibres.
Everything in `j_!`'s adjunction cancels against the equivalence, so the content is exactly the
fibre hom bijection of the source's proof. -/
@[stacks 0791 "transposing across `j_! ⊣ j^{-1}` is evaluation on fibres"]
theorem Presheaf.IsSheaf.app_fibers_inv_comp_homEquiv_shriek {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf J F)
    [(CostructuredArrow.proj yoneda F).IsContinuous
      ((CostructuredArrow.proj yoneda F).restrictedTopology J) J]
    (T : Over (⟨F, hF⟩ : Sheaf J (Type v))) (G : Sheaf J (Type v)) (β : T.left ⟶ G)
    (X : CostructuredArrow yoneda F) (p : OverArrows T.hom.hom X.hom) :
    (hF.sheafEquivalenceCostructuredArrowYoneda.fibers.inv.app T ≫
        (hF.sheafEquivalenceCostructuredArrowYoneda.shriek.homEquiv
            (hF.sheafEquivalenceCostructuredArrowYoneda.equivalence.inverse.obj T) G
            ((Over.forget (⟨F, hF⟩ : Sheaf J (Type v))).map
              (hF.sheafEquivalenceCostructuredArrowYoneda.equivalence.counit.app T) ≫
                β)).hom).app
        (op X) p =
      β.hom.app (op X.left) p.val :=
  app_sheafEquivalenceFibers_inv_comp_homEquiv F J hF T G β X p

open Stacks.Topos.Localized in
/-- **Stacks 0791.** Let `(C, J)` be a site and let `F` be a sheaf of sets on `C`. Let
`C/F = CostructuredArrow yoneda F` be the category of pairs `(U, s)` with `s ∈ F(U)`, with its
projection `j = CostructuredArrow.proj yoneda F` to `C`, and declare a family
`{(U_i, s_i) ⟶ (U, s)}` to be a covering when `{U_i ⟶ U}` is a covering of `C`, i.e. give `C/F`
the topology `j.restrictedTopology J` generated by those families. Then:

1. `C/F` is a site with exactly those coverings: a sieve of `(U, s)` is covering for
   `j.restrictedTopology J` if and only if its image under `j` is a covering sieve of `U`;
2. the canonical equivalence `Over F ≌ PSh(C/F)` of `overEquivPresheafCostructuredArrow` matches
   sheaves with sheaves: for an object `φ : G ⟶ F` of `PSh(C)/F`, the presheaf
   `(U, s) ↦ {t ∈ G(U) | φ(t) = s}` on `C/F` is a sheaf if and only if `G` is a sheaf on `C`;
3. `j` is continuous and cocontinuous, so that it induces a morphism of topoi
   `j : Sh(C/F) ⟶ Sh(C)` with `j^{-1}` restriction (Stacks 00XR); and
4. there is an equivalence `E : Sh(C/F) ≌ Sh(C)/F`, namely the restriction of that canonical
   equivalence — `E.inverse` is `(G, φ) ↦ ((U, s) ↦ {t ∈ G(U) | φ(t) = s})` on underlying
   presheaves — for which `E.functor` followed by `Over.forget` is left adjoint to `j^{-1}`, that
   is, is `j_!`. Since `Over.forget` is the `j_{F!}` of Stacks 04GZ, this is the assertion that
   `E` turns `j` into the localization morphism `j_F`. -/
@[stacks 0791 "Sheaves on the site `C/F` of pairs `(U, s)` with `s ∈ F(U)`, whose coverings are
  those of `C`: `C/F` is a site, `j` is continuous and cocontinuous, the canonical equivalence
  `PSh(C)/F ≌ PSh(C/F)` matches sheaves with sheaves, and it restricts to an equivalence
  `Sh(C/F) ≌ Sh(C)/F` carrying `j_!` to `Over.forget`, i.e. turning `j` into `j_F`.",
  sga "4 III 5.2" "special case"]
public theorem Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda {C : Type u}
    [Category.{v} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type v} (hF : Presheaf.IsSheaf J F) :
    (∀ (X : CostructuredArrow yoneda F) (S : Sieve X),
        S ∈ (CostructuredArrow.proj yoneda F).restrictedTopology J X ↔
          Sieve.functorPushforward (CostructuredArrow.proj yoneda F) S ∈ J X.left) ∧
      (∀ T : Over F,
        Presheaf.IsSheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J)
            ((overEquivPresheafCostructuredArrow F).functor.obj T) ↔
          Presheaf.IsSheaf J T.left) ∧
      ∃ (_ :
        (CostructuredArrow.proj yoneda F).IsContinuous
          ((CostructuredArrow.proj yoneda F).restrictedTopology J) J)
        (_ :
        (CostructuredArrow.proj yoneda F).IsCocontinuous
          ((CostructuredArrow.proj yoneda F).restrictedTopology J) J)
        (E :
        Sheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≌
          Over (⟨F, hF⟩ : Sheaf J (Type v))),
        Nonempty
            (E.inverse ⋙
                sheafToPresheaf ((CostructuredArrow.proj yoneda F).restrictedTopology J) (Type v) ≅
              Over.post (X := (⟨F, hF⟩ : Sheaf J (Type v))) (sheafToPresheaf J (Type v)) ⋙
                (overEquivPresheafCostructuredArrow F).functor) ∧
          Nonempty
            (E.functor ⋙ Over.forget (⟨F, hF⟩ : Sheaf J (Type v)) ⊣
              (CostructuredArrow.proj yoneda F).sheafPushforwardContinuous (Type v)
                ((CostructuredArrow.proj yoneda F).restrictedTopology J) J) := by
  apply
      Stacks.Topos.Localized.Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda_proof

end

end

end CategoryTheory
