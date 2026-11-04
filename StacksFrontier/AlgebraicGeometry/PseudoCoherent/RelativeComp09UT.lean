module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 09UT, relative pseudo-coherence and composition of the base

Let `f : X ⟶ Y` be locally of finite type and let `g : Y ⟶ S` be pseudo-coherent. Stacks 36.61.17
says that an object `E` of `D(𝒪_X)` is `m`-pseudo-coherent relative to `Y` if and only if it is
`m`-pseudo-coherent relative to `S`.

Both directions are the equivalence of Stacks 09UJ, `AlgebraicGeometry.affinePairComparison`,
together with one move on the local condition of Stacks 09UI at a compatible pair of affine opens.
The move is the affine-pair statement of Stacks 09VD and Stacks 09VA applied to the restriction
`g.resLE W V : V ⟶ W` of `g` to a compatible pair of affine opens of `Y` and `S`, which is
pseudo-coherent by `AlgebraicGeometry.pseudoCoherent_resLE`; the two directions use the two
directions
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_comp` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_of_comp` of that move.

The bookkeeping that remains is that a pair of affine opens for the composite does not come with
a compatible affine open of the intermediate scheme: for `U ⊆ (f ≫ g) ⁻¹ᵁ W` there is no reason
for `f '' U` to lie in a single affine open of `g ⁻¹ᵁ W`. So in each direction the pair condition
is proved one point of `U` at a time and glued by Stacks 09VE, exactly as in the proof of
Stacks 09UJ itself.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_forall_mem_basicOpen`: the
  pair condition of Stacks 09UI at `(U, V)` follows from the pair condition at
  `(X_r, V)` for a family of `r : Γ(X, U)` whose standard opens cover `U`. This is
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_forall_mem` restated so that
  its hypothesis is again a pair condition rather than the local condition at a standard open of
  `U`.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.comp_base` and
  `.of_comp_base`: the pair condition is carried **both ways** along a pseudo-coherent morphism
  `g : Y ⟶ S` of the base, at a compatible triple of affine opens `U ⊆ f ⁻¹ᵁ V`, `V ⊆ g ⁻¹ᵁ W`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp` and
  `isPseudoCoherentFrom_of_comp`: the two implications of Stacks 09UT.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_comp`: **Stacks 09UT.**
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_comp_of_isModulePseudoCoherent`:
  Stacks 09UT with pseudo-coherence of `g` in the shape of condition (3) of Stacks 067Y, namely
  that `g` is locally of finite type with `𝒪_Y` pseudo-coherent relative to `S`. The two shapes
  are interchangeable by the unconditional
  `AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent`.

## Implementation notes

**Why no side condition appears here.** The pushforward side condition of Stacks 09VA is
discharged inside the affine-pair moves by the `AlgebraicGeometry.Scheme.Modules` result
`pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_pseudoCoherent`,
which takes pseudo-coherence of the base morphism as its only input. Nothing in this file
mentions a pushforward of the structure sheaf, so nothing here can use the bare,
compatibility-free form of that side condition whose unsoundness is recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SideCondition.lean`.

**The two spellings of a small open.** As in the proof of Stacks 09UJ, the small open produced
around a point of `U` is simultaneously an affine open `X_r` of `X`, where the pair condition
lives, and a standard open of `U`, which is what Stacks 09VE consumes. The comparison of the two
restrictions of `E` to it is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE` and the identity
of the two opens is `AlgebraicGeometry.Scheme.Opens.ι_image_basicOpen_topIso_inv`; the first
result below isolates that bookkeeping so that both directions of Stacks 09UT can ignore it.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.17 (09UT)](https://stacks.math.columbia.edu/tag/09UT)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Hom

/-! ### Gluing the pair condition from pair conditions at standard opens -/

/-- **The pair condition of Stacks 09UI is local on the source, in the pair spelling.** If around
every point of an affine open `U` with `U ⊆ f ⁻¹ᵁ V` there is an `r : Γ(X, U)` with the pair
condition at the affine open `X_r` of `X` over `V`, then the pair condition holds at `(U, V)`.

This is `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_forall_mem`, whose
hypothesis is the local condition of Stacks 09UI at a *standard open of `U`*, restated with the
pair condition at an *affine open of `X`* instead. The translation between the two is the one made
inline in the proof of Stacks 09UJ: the standard open of `U` cut out by `U.topIso.inv r` has image
`X_r` in `X` (`AlgebraicGeometry.Scheme.Opens.ι_image_basicOpen_topIso_inv`), and restricting `E`
to it in one step or in two agrees by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE`. -/
public theorem isPseudoCoherentFromOnAffinePair_of_forall_mem_basicOpen {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {E : DerivedCategory X.Modules} {m : ℤ}
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (h : ∀ x : (U.1 : Scheme.{u}), ∃ r : Γ(X, U.1), x.1 ∈ X.basicOpen r ∧
      ∃ hrV : X.basicOpen r ≤ f ⁻¹ᵁ V.1,
        f.IsPseudoCoherentFromOnAffinePair E m ⟨X.basicOpen r, U.2.basicOpen r⟩ V hrV) :
    f.IsPseudoCoherentFromOnAffinePair E m U V hUV := by
  have hUaff : IsAffine (U.1 : Scheme.{u}) := U.2
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have := locallyOfFiniteType_resLE f V.1 U.1 hUV
  refine isPseudoCoherentFromOnAffinePair_of_forall_mem f U V hUV fun x => ?_
  obtain ⟨r, hrx, hrV, hpair⟩ := h x
  obtain ⟨n, i0, hi0, hi0o, hi0pc⟩ := hpair
  have := hi0
  have hrUle : X.basicOpen r ≤ (U.1 : X.Opens) := Scheme.basicOpen_le X r
  have hbasic : U.1.ι ⁻¹ᵁ X.basicOpen r =
      (U.1 : Scheme.{u}).basicOpen (U.1.topIso.inv r) := by
    rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv U.1 r,
      U.1.ι.preimage_image_eq ((U.1 : Scheme.{u}).basicOpen (U.1.topIso.inv r))]
  have hi0o' : i0 ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι =
      (X.basicOpen r).ι ≫ f := by
    rw [← Category.assoc, hi0o, Scheme.Hom.resLE_comp_ι]
  refine ⟨U.1.topIso.inv r, ?_, ?_⟩
  · rw [← hbasic]
    exact hrx
  · rw [← hbasic]
    refine ⟨n, (Scheme.Opens.isoOfLE hrUle).hom ≫ i0, inferInstance, ?_,
      Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE hrUle i0 E m hi0pc⟩
    rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, Category.assoc, hi0o',
      Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Opens.isoOfLE_hom_ι hrUle,
      Category.assoc]

/-! ### The pair condition along a pseudo-coherent morphism of the base -/

/-- Opens `U ≤ f ⁻¹ᵁ V` and `V ≤ g ⁻¹ᵁ W` give `U ≤ (f ≫ g) ⁻¹ᵁ W`. -/
private theorem le_comp_preimage_of_le {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    {U : X.Opens} {V : Y.Opens} {W : S.Opens} (hUV : U ≤ f ⁻¹ᵁ V) (hVW : V ≤ g ⁻¹ᵁ W) :
    U ≤ (f ≫ g) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  exact hUV.trans (f.preimage_mono hVW)

section Comp

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f]
  [PseudoCoherent g]

/-- **The pair condition of Stacks 09UI passes along a pseudo-coherent morphism of the base.**
Let `f : X ⟶ Y` be locally of finite type, let `g : Y ⟶ S` be pseudo-coherent and let
`U ⊆ f ⁻¹ᵁ V` and `V ⊆ g ⁻¹ᵁ W` be compatible affine opens. If `E` satisfies the pair condition
at `(U, V)` for `f`, then it satisfies it at `(U, W)` for `f ≫ g`.

This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_comp` along
`g.resLE W V : V ⟶ W`, which is pseudo-coherent by
`AlgebraicGeometry.pseudoCoherent_resLE`. -/
public theorem IsPseudoCoherentFromOnAffinePair.comp_base {E : DerivedCategory X.Modules} {m : ℤ}
    {U : X.affineOpens} {V : Y.affineOpens} {W : S.affineOpens} (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hVW : V.1 ≤ g ⁻¹ᵁ W.1) (hUW : U.1 ≤ (f ≫ g) ⁻¹ᵁ W.1)
    (h : f.IsPseudoCoherentFromOnAffinePair E m U V hUV) :
    (f ≫ g).IsPseudoCoherentFromOnAffinePair E m U W hUW := by
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have := locallyOfFiniteType_resLE g W.1 V.1 hVW
  have hres := Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_comp
    (f.resLE V.1 U.1 hUV) (g.resLE W.1 V.1 hVW) _ m h
  rw [Scheme.Hom.resLE_comp_resLE] at hres
  exact hres

/-- **The pair condition of Stacks 09UI descends along a pseudo-coherent morphism of the base.**
Converse of `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.comp_base`: if `E`
satisfies the pair condition at `(U, W)` for `f ≫ g`, then it satisfies it at `(U, V)` for `f`.

This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_of_comp` along
`g.resLE W V : V ⟶ W`. -/
public theorem IsPseudoCoherentFromOnAffinePair.of_comp_base {E : DerivedCategory X.Modules}
    {m : ℤ} {U : X.affineOpens} {V : Y.affineOpens} {W : S.affineOpens} (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hVW : V.1 ≤ g ⁻¹ᵁ W.1) (hUW : U.1 ≤ (f ≫ g) ⁻¹ᵁ W.1)
    (h : (f ≫ g).IsPseudoCoherentFromOnAffinePair E m U W hUW) :
    f.IsPseudoCoherentFromOnAffinePair E m U V hUV := by
  have hUaff : IsAffine (U.1 : Scheme.{u}) := U.2
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have := locallyOfFiniteType_resLE f V.1 U.1 hUV
  have := locallyOfFiniteType_resLE g W.1 V.1 hVW
  refine Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_of_comp
    (f.resLE V.1 U.1 hUV) (g.resLE W.1 V.1 hVW) _ m ?_
  rw [Scheme.Hom.resLE_comp_resLE]
  exact h

/-! ### Stacks 09UT -/

/-- **Stacks 09UT, the implication from `Y` to `S`.** If `E` is `m`-pseudo-coherent relative to
`f : X ⟶ Y` then it is `m`-pseudo-coherent relative to `f ≫ g` for `g : Y ⟶ S` pseudo-coherent.

By `AlgebraicGeometry.affinePairComparison` it suffices to prove the pair condition at every
compatible pair `U ⊆ (f ≫ g) ⁻¹ᵁ W` of affine opens of `X` and `S`. There need be no affine open
of `Y` containing `f '' U`, so the condition is proved around each point `x` of `U`: choose an
affine open `V ⊆ g ⁻¹ᵁ W` of `Y` containing `f x`, shrink `U` to an affine standard open
`X_r ⊆ U ⊓ f ⁻¹ᵁ V` around `x`, take the pair condition at `(X_r, V)` for `f` from the hypothesis
and push it to `(X_r, W)` for `f ≫ g` by
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.comp_base`. -/
public theorem isPseudoCoherentFrom_comp (E : DerivedCategory X.Modules) (m : ℤ)
    (h : f.IsPseudoCoherentFrom E m) : (f ≫ g).IsPseudoCoherentFrom E m := by
  refine (affinePairComparison (f ≫ g) E m).mpr fun U W hUW => ?_
  refine isPseudoCoherentFromOnAffinePair_of_forall_mem_basicOpen (f ≫ g) U W hUW fun x => ?_
  have hfx : f.base x.1 ∈ g ⁻¹ᵁ W.1 := by
    have hx := hUW x.2
    rwa [Scheme.Hom.comp_preimage] at hx
  have hmem : f.base x.1 ∈
      (⨆ V : {V : Y.affineOpens // V.1 ≤ g ⁻¹ᵁ W.1}, (V.1.1 : Y.Opens)) := by
    rw [iSup_affineOpens_subtype_eq]
    exact hfx
  obtain ⟨V, hxV⟩ := Opens.mem_iSup.mp hmem
  obtain ⟨r, hrV, hrx⟩ := U.2.exists_basicOpen_le (V := f ⁻¹ᵁ (V.1.1 : Y.Opens)) ⟨x.1, hxV⟩ x.2
  have hrW := le_comp_preimage_of_le f g hrV V.2
  exact ⟨r, hrx, hrW, IsPseudoCoherentFromOnAffinePair.comp_base f g hrV V.2 hrW
    ((affinePairComparison f E m).mp h ⟨X.basicOpen r, U.2.basicOpen r⟩ V.1 hrV)⟩

/-- **Stacks 09UT, the implication from `S` to `Y`.** If `E` is `m`-pseudo-coherent relative to
`f ≫ g` for `g : Y ⟶ S` pseudo-coherent, then it is `m`-pseudo-coherent relative to `f : X ⟶ Y`.

By `AlgebraicGeometry.affinePairComparison` it suffices to prove the pair condition at every
compatible pair `U ⊆ f ⁻¹ᵁ V` of affine opens of `X` and `Y`, and again this is done around each
point `x` of `U`: choose an affine open `W` of `S` containing `g (f x)`, shrink `V` to an affine
standard open `Y_b ⊆ V ⊓ g ⁻¹ᵁ W` around `f x`, shrink `U` to an affine standard open
`X_r ⊆ U ⊓ f ⁻¹ᵁ Y_b` around `x`, take the pair condition at `(X_r, W)` for `f ≫ g` from the
hypothesis, descend it to `(X_r, Y_b)` for `f` by
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.of_comp_base` and enlarge the base
back to `V` by `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.of_base_le`. -/
public theorem isPseudoCoherentFrom_of_comp (E : DerivedCategory X.Modules) (m : ℤ)
    (h : (f ≫ g).IsPseudoCoherentFrom E m) : f.IsPseudoCoherentFrom E m := by
  refine (affinePairComparison f E m).mpr fun U V hUV => ?_
  refine isPseudoCoherentFromOnAffinePair_of_forall_mem_basicOpen f U V hUV fun x => ?_
  have hxV : f.base x.1 ∈ V.1 := hUV x.2
  obtain ⟨W, hxW⟩ : ∃ W : S.affineOpens, g.base (f.base x.1) ∈ (W.1 : S.Opens) := by
    have hmem : g.base (f.base x.1) ∈ (⨆ W : S.affineOpens, (W.1 : S.Opens)) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    exact Opens.mem_iSup.mp hmem
  obtain ⟨b, hbW, hbx⟩ := V.2.exists_basicOpen_le (V := g ⁻¹ᵁ W.1) ⟨f.base x.1, hxW⟩ hxV
  have hbV : Y.basicOpen b ≤ (V.1 : Y.Opens) := Scheme.basicOpen_le Y b
  obtain ⟨r, hrb, hrx⟩ := U.2.exists_basicOpen_le (V := f ⁻¹ᵁ Y.basicOpen b) ⟨x.1, hbx⟩ x.2
  have hrV : X.basicOpen r ≤ f ⁻¹ᵁ (V.1 : Y.Opens) := hrb.trans (f.preimage_mono hbV)
  have hrW := le_comp_preimage_of_le f g hrb hbW
  refine ⟨r, hrx, hrV, ?_⟩
  refine IsPseudoCoherentFromOnAffinePair.of_base_le f
    (T := ⟨Y.basicOpen b, V.2.basicOpen b⟩) hbV hrb hrV ?_
  exact IsPseudoCoherentFromOnAffinePair.of_comp_base f g hrb hbW hrW
    ((affinePairComparison (f ≫ g) E m).mp h ⟨X.basicOpen r, U.2.basicOpen r⟩ W hrW)

/-- **Stacks 09UT.** Let `f : X ⟶ Y` be locally of finite type, let `g : Y ⟶ S` be
pseudo-coherent, let `E` be an object of `D(𝒪_X)` and let `m` be an integer. Then `E` is
`m`-pseudo-coherent relative to `Y` if and only if it is `m`-pseudo-coherent relative to `S`.

The two implications are
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp` and
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_comp`. -/
@[stacks 09UT "the equivalence, with pseudo-coherence of g as a class",
  sga "6 III 1.12",
  sga "6 I 2.14" "(ii)", sga "6 III 1.11" "b), g pseudo-coherent"]
public theorem isPseudoCoherentFrom_iff_comp (E : DerivedCategory X.Modules) (m : ℤ) :
    f.IsPseudoCoherentFrom E m ↔ (f ≫ g).IsPseudoCoherentFrom E m :=
  ⟨isPseudoCoherentFrom_comp f g E m, isPseudoCoherentFrom_of_comp f g E m⟩

end Comp

/-- **Stacks 09UT with pseudo-coherence of `g` in the shape of condition (3) of Stacks 067Y.**
Let `f : X ⟶ Y` be locally of finite type and let `g : Y ⟶ S` be locally of finite type with
`𝒪_Y` pseudo-coherent relative to `S`. Then an object `E` of `D(𝒪_X)` is `m`-pseudo-coherent
relative to `Y` if and only if it is `m`-pseudo-coherent relative to `S`.

The hypothesis is condition (3) of Stacks 067Y rather than
`AlgebraicGeometry.PseudoCoherent`; the two are interchangeable by the unconditional
`AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent`, so this is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_comp`. -/
@[stacks 09UT "the equivalence, with the hypothesis in the shape of condition (3) of 067Y",
  sga "6 III 1.12", sga "6 I 2.14" "(ii)", sga "6 III 1.11" "b), g pseudo-coherent"]
public theorem isPseudoCoherentFrom_iff_comp_of_isModulePseudoCoherent {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f]
    (hg : ∃ hft : LocallyOfFiniteType g,
      letI := hft
      Scheme.Hom.IsModulePseudoCoherent g (SheafOfModules.unit Y.ringCatSheaf))
    (E : DerivedCategory X.Modules) (m : ℤ) :
    letI : LocallyOfFiniteType g := hg.choose
    letI : LocallyOfFiniteType (f ≫ g) := locallyOfFiniteType_comp f g
    f.IsPseudoCoherentFrom E m ↔ (f ≫ g).IsPseudoCoherentFrom E m :=
  let : PseudoCoherent g := (pseudoCoherent_iff_isModulePseudoCoherent g).mpr hg
  isPseudoCoherentFrom_iff_comp f g E m

end Scheme.Hom

end AlgebraicGeometry

end
