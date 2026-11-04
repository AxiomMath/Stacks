module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Serre's condition on an effective Cartier divisor of an algebraic space

Let `X` be a locally Noetherian algebraic space over a scheme `S` and let `D ⊆ X` be an
effective Cartier divisor.  If `X` satisfies Serre's condition `(S_k)` then `D` satisfies
`(S_{k-1})` (Stacks 0B4G), and if `X` is normal then `D` satisfies `(S_1)` (Stacks 0B4H).

Both are the scheme case read on one étale chart.  Local Noetherianity together with `(S_k)` is
a property of schemes local in the étale topology, so by Stacks 03E6 it defines a property of
algebraic spaces whose value may be read on any étale scheme chart (Stacks 03E8); and by
Stacks 083C an effective Cartier divisor of `X` pulls back to an effective Cartier ideal sheaf
on such a chart.  Choosing a *surjective* étale chart `U` of `X` makes the resulting closed
subscheme of `U` a surjective étale chart of `D`, which is exactly the datum the property of
`D` asks for.

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_hasPropertySk`: **Stacks 0B4G.**  An
  effective Cartier divisor on a locally Noetherian algebraic space satisfying `(S_k)`
  satisfies `(S_{k-1})`.
* `AlgebraicGeometry.Space.isNormal_effectiveCartierDivisor_hasPropertySk_one`:
  **Stacks 0B4H.**  An effective Cartier divisor on a locally Noetherian normal algebraic
  space satisfies `(S_1)`.
* `AlgebraicGeometry.Space.isLocallyNoetherian_and_hasPropertySk_isLocal_etale`: local
  Noetherianity together with `(S_k)` is local for étale coverings of schemes, which is what
  makes the two statements above independent of the chart.

## The two statements, and why they are not one

Stacks 0B4H is not Stacks 0B4G at `k = 2`: the source deduces it from the *scheme* case
Stacks 0B3S, not from the space case of `(S_k)`.  That is mirrored here, and
`AlgebraicGeometry.isNormal_effectiveCartierDivisor_hasPropertySk_one` is where Serre's
criterion enters — it is the scheme lemma which passes from normality to `(S_2)` through
`AlgebraicGeometry.hasPropertySk_two_of_isNormal` and then applies Stacks 0B3R.  So the
normal case needs no hypothesis of the form `(S_k)` on `X`, only normality and local
Noetherianity, each of them an étale-local property in its own right.

## Implementation notes

`(S_k)` for an algebraic space is `AlgebraicGeometry.Space.HasEtaleLocalProperty` (Stacks 03E6)
taken at the property of schemes `fun T => ∃ h : IsLocallyNoetherian T, HasPropertySk T k`.
Local Noetherianity is bundled into the property as an existential because
`AlgebraicGeometry.HasPropertySk` takes it as an instance argument, and that is already the
shape in which `AlgebraicGeometry.isLocallyNoetherian_and_hasPropertySk_isLocal_syntomic`
(Stacks 036A) records its locality.  No new predicate is introduced: the ambient hypothesis
and the conclusion are that one application.

**The `k - 1` convention.** The index is a natural number and `k - 1` is truncated
subtraction, so at `k = 0` the conclusion reads `(S_0)`.  That is the weakest instance of the
condition — `min (0, dim 𝒪) ≤ depth 𝒪` holds for every local ring — and it is proved here from
`AlgebraicGeometry.hasPropertySk_zero` rather than from the scheme lemma, which asks for
`1 ≤ k`.  For every `k ≥ 1` the statement is the source's, and no hypothesis `1 ≤ k` is
needed.

**Normality of the ambient space.** The hypothesis is `AlgebraicGeometry.Space.IsNormal`,
the existing abbreviation for `HasEtaleLocalProperty` at normality; local Noetherianity is
written out as the corresponding application, there being no abbreviation for it.  The chart
produced by Stacks 083C need not be the chart witnessing either hypothesis, which is why both
are transported to it by `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`; normality
is étale-local by `AlgebraicGeometry.isLocal_isNormal_etalePrecoverage` (Stacks 034F) and
local Noetherianity by `AlgebraicGeometry.isLocallyNoetherian_isLocal_etale`.

**The chart of the divisor.** Condition (2) of Stacks 083C,
`AlgebraicGeometry.Space.HasEffectiveCartierEtaleCover`, supplies a surjective étale chart
`g : h_U ⟶ X` of the ambient space together with an effective Cartier ideal sheaf `I` of `U`
and a closed immersion `j : R ⟶ U` of objects of the site whose range is the inverse image
`D ×_X U`.  Surjectivity is what condition (2) adds over condition (3), and it is needed
because `HasEtaleLocalProperty` asks for a surjective chart; the identification of the range
with the inverse image turns `h_R` into the fibre product, hence into an étale surjective
chart of `D`, by `AlgebraicGeometry.Space.isEtale_of_isPullback_yoneda` and
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf` (Stacks 03H4).

That identification is `isPullback_of_range_eq_preimage` below, a general statement about
subfunctors of a type-valued functor; the module
`StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorDimension` carries a private
variant of it specialized to represented presheaves.

The étale locality of local Noetherianity together with `(S_k)` is item (3) of Remark 03E7.
It is stated here in the `AlgebraicGeometry.Space` namespace, as
`AlgebraicGeometry.Space.isCohenMacaulay_isLocal_etale` in
`StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts` is for item (4), and it
carries no tag: the tag for the remark belongs on a declaration collecting the whole list.

## References

* [Stacks Project, Tag 0B4G](https://stacks.math.columbia.edu/tag/0B4G)
* [Stacks Project, Tag 0B4H](https://stacks.math.columbia.edu/tag/0B4H)
* [Stacks Project, Tag 0B3R](https://stacks.math.columbia.edu/tag/0B3R)
* [Stacks Project, Tag 0B3S](https://stacks.math.columbia.edu/tag/0B3S)
* [Stacks Project, Tag 036A](https://stacks.math.columbia.edu/tag/036A)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E7](https://stacks.math.columbia.edu/tag/03E7)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry.Space

/-- **Local Noetherianity together with Serre's condition `(S_k)` is local for étale coverings
of schemes.** This is item (3) of Stacks 03E7: the syntomic case is Stacks 036A,
`AlgebraicGeometry.isLocallyNoetherian_and_hasPropertySk_isLocal_syntomic`, and every étale
morphism of schemes is syntomic, so every étale covering family is a syntomic one and locality
for the coarser precoverage follows. -/
instance isLocallyNoetherian_and_hasPropertySk_isLocal_etale (k : ℕ) :
    ObjectProperty.IsLocal
      (fun T : Scheme.{u} => ∃ h : IsLocallyNoetherian T, @HasPropertySk T h k)
      Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le
    (Scheme.precoverage_mono (P := @Etale.{u}) (Q := @Syntomic.{u}) fun _ _ f hf => by
      have : Etale f := hf
      exact syntomic_of_etale f)

/-- **A monomorphism whose range is the inverse image of a subfunctor exhibits that subfunctor
as a fibre product.** Let `H ⊆ A` be a subfunctor, let `a : A' ⟶ A`, and let `f : E ⟶ A'` be a
monomorphism whose range is the inverse image `H.preimage a`.  Then a morphism
`b : E ⟶ H.toFunctor` lying over `f` makes `E` the fibre product `H ×_A A'`.

The square is a pullback section by section: injectivity of the comparison is injectivity of
`f` at that section, and surjectivity is the hypothesis that the range of `f` exhausts the
inverse image. -/
private lemma isPullback_of_range_eq_preimage {C : Type u} [Category.{v} C]
    {A A' E : C ⥤ Type w} (H : Subfunctor A) (a : A' ⟶ A) (f : E ⟶ A')
    (b : E ⟶ H.toFunctor) [Mono f] (hb : b ≫ H.ι = f ≫ a)
    (hr : Subfunctor.range f = H.preimage a) :
    IsPullback b f H.ι a := by
  apply IsPullback.of_forall_isPullback_app
  intro V
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app V) hb, ?_, ?_⟩
  · intro x y hxy
    exact ((mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).mp inferInstance V)) hxy.2
  · intro x y hxy
    have hy : y ∈ (Subfunctor.range f).obj V := by
      rw [hr]
      show a.app V y ∈ H.obj V
      exact hxy ▸ x.property
    obtain ⟨d, hd⟩ := hy
    refine ⟨d, ?_, hd⟩
    apply Subtype.ext
    have hc := congrArg (fun k => k.app V d) hb
    change (b.app V d).val = a.app V (f.app V d) at hc
    exact hc.trans ((congrArg (a.app V) hd).trans hxy.symm)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale-local property of schemes passes from a surjective étale chart of an algebraic
space to its effective Cartier divisor.** Suppose the inverse image of a closed subspace
`D ⊆ X` on a surjective étale scheme chart `g : h_U ⟶ X` is the closed subscheme cut out by an
effective Cartier ideal sheaf, which is the chart condition of Stacks 083C (2), and suppose
`U` is locally Noetherian and `(S_m)` holds of the closed subscheme cut out by *any* effective
Cartier ideal sheaf of `U` (which is locally Noetherian, being of finite type over `U`).  Then `D`
has local Noetherianity together with `(S_m)` in the sense of Stacks 03E6.

The closed immersion `j : R ⟶ U` presenting the inverse image has range `D ×_X U`, so `h_R` is
the fibre product of `g` with the inclusion of `D`; base change makes it a surjective étale
chart of `D`, and the identification of `R` with the subscheme cut out by the ideal sheaf
transports `P` to it. -/
private theorem hasEtaleLocalProperty_of_isSchemeEffectiveCartierPullback
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (m : ℕ) (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X.1)
    (hgEtale : IsEtale B S hS g) (hgSurj : IsSurjective B S hS g)
    (hchart : IsSchemeEffectiveCartierPullback B S hS X D U g)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (hP : ∀ I : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData,
      Stacks.Divisors.IsEffectiveCartierDivisor I →
        ∀ [h : IsLocallyNoetherian I.subscheme], @HasPropertySk I.subscheme h m) :
    HasEtaleLocalProperty B S hS D.1.toFunctor
      (fun T : Scheme.{u} => ∃ h : IsLocallyNoetherian T, @HasPropertySk T h m) := by
  obtain ⟨I, R, j, e, hI, hmap, hpre⟩ := hchart
  have hrange : Subfunctor.range (yoneda.map j ≫ g) ≤ D.1 := by
    rintro V _ ⟨y, rfl⟩
    exact hpre.ge V ⟨y, rfl⟩
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := by rw [hmap]; infer_instance
  have : Mono j := Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) inferInstance
  have : Mono (yoneda.map j) := Functor.map_mono yoneda j
  set d := Subfunctor.lift (yoneda.map j ≫ g) hrange
  have hdι : d ≫ D.1.ι = yoneda.map j ≫ g := Subfunctor.lift_ι _ hrange
  have hpb : IsPullback (yoneda.map j) d g D.1.ι :=
    (isPullback_of_range_eq_preimage D.1 g (yoneda.map j) d hdι hpre.symm).flip
  refine ⟨R, d, ?_,
    presheaf_etale_of_isEtale B S hS (isEtale_of_isPullback_yoneda B S hS hpb hgEtale),
    ObjectProperty.IsClosedUnderIsomorphisms.of_iso
      (P := fun T : Scheme.{u} => ∃ h : IsLocallyNoetherian T, @HasPropertySk T h m) e.symm
      (by have := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
          exact ⟨inferInstance, hP I hI⟩)⟩
  refine (surjective_iff_surjective_pointsMap B S hS D.1.toFunctor D.2.1 R d).mpr fun x => ?_
  obtain ⟨p, hp⟩ := hgSurj (pointsMap B S hS D.1.toFunctor D.1.ι x)
  obtain ⟨y, -, hy⟩ := exists_point_of_isPullback_presheaf B S hS hpb p x hp
  exact ⟨y, hy⟩

/-- **Stacks 0B4G.** Let `X` be a locally Noetherian algebraic space over a scheme `S`
satisfying Serre's condition `(S_k)`, and let `D ⊆ X` be an effective Cartier divisor.  Then
`D` satisfies `(S_{k-1})`.

Both hypothesis and conclusion are Stacks 03E6 taken at the property of schemes "locally
Noetherian and `(S_k)`", which is item (3) of Remark 03E7.  By Stacks 083C the divisor is cut
out on a surjective étale chart `U` of `X` by an effective Cartier ideal sheaf; `U` inherits
`(S_k)` from `X` by Stacks 03E8, and the closed subscheme it cuts out satisfies `(S_{k-1})` by
the scheme case `AlgebraicGeometry.isEffectiveCartierDivisor_hasPropertySk` (Stacks 0B3R).
That closed subscheme is a surjective étale chart of `D`.

The index `k - 1` is truncated subtraction of natural numbers; at `k = 0` the conclusion is
the vacuous condition `(S_0)` and is supplied by
`AlgebraicGeometry.hasPropertySk_zero`, so no hypothesis `1 ≤ k` is required. -/
@[stacks 0B4G]
theorem isEffectiveCartierDivisor_hasPropertySk
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) (k : ℕ)
    (hX : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => ∃ h : IsLocallyNoetherian T, @HasPropertySk T h k)) :
    HasEtaleLocalProperty B S hS D.1.toFunctor
      (fun T : Scheme.{u} => ∃ h : IsLocallyNoetherian T, @HasPropertySk T h (k - 1)) := by
  obtain ⟨U, g, hgEtale, hgSurj, hchart⟩ :=
    hasEffectiveCartierEtaleCover_of_isEffectiveCartier B S hS X D hD
  obtain ⟨hUnoeth, hUsk⟩ :=
    (exists_atlas_iff_forall_etale B S hS X.1
        (fun T : Scheme.{u} => ∃ h : IsLocallyNoetherian T, @HasPropertySk T h k) X.2).mp
      hX U g (presheaf_etale_of_isEtale B S hS hgEtale)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hUnoeth
  refine hasEtaleLocalProperty_of_isSchemeEffectiveCartierPullback B S hS X D _ U g
    hgEtale hgSurj hchart fun I hI _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hasPropertySk_zero I.subscheme
  · exact _root_.AlgebraicGeometry.isEffectiveCartierDivisor_hasPropertySk I hI k hk hUsk

/-- **Stacks 0B4H.** Let `X` be a locally Noetherian normal algebraic space over a scheme `S`
and let `D ⊆ X` be an effective Cartier divisor.  Then `D` satisfies Serre's condition
`(S_1)`.

Normality and local Noetherianity of `X` are each Stacks 03E6 taken at the corresponding
property of schemes, items (7) and (1) of Remark 03E7.  By Stacks 083C the divisor is cut out
on a surjective étale chart `U` of `X` by an effective Cartier ideal sheaf; `U` is locally
Noetherian and normal by Stacks 03E8, and the closed subscheme it cuts out satisfies `(S_1)`
by the scheme case `AlgebraicGeometry.isNormal_effectiveCartierDivisor_hasPropertySk_one`
(Stacks 0B3S), which is where Serre's criterion is used.  That closed subscheme is a
surjective étale chart of `D`. -/
@[stacks 0B4H]
theorem isNormal_effectiveCartierDivisor_hasPropertySk_one
    (X : AlgebraicSpaces B S hS)
    (hXnoeth : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXnormal : IsNormal B S hS X.1) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    HasEtaleLocalProperty B S hS D.1.toFunctor
      (fun T : Scheme.{u} => ∃ h : IsLocallyNoetherian T, @HasPropertySk T h 1) := by
  obtain ⟨U, g, hgEtale, hgSurj, hchart⟩ :=
    hasEffectiveCartierEtaleCover_of_isEffectiveCartier B S hS X D hD
  have hgE := presheaf_etale_of_isEtale B S hS hgEtale
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) X.2).mp hXnoeth U g hgE
  have : _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T) X.2).mp hXnormal U g hgE
  exact hasEtaleLocalProperty_of_isSchemeEffectiveCartierPullback B S hS X D _ U g
    hgEtale hgSurj hchart fun I hI _ =>
    _root_.AlgebraicGeometry.isNormal_effectiveCartierDivisor_hasPropertySk_one
      ((BigFppfOver.toScheme B S hS).obj U) I hI

end AlgebraicGeometry.Space

end
