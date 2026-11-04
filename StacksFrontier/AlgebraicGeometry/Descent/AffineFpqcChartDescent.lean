module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFlatChartCandidate
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.CandidateEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteCofanBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Subcanonical

/-!
# Effective descent of affine morphisms along a flat affine chart

`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc` of
`StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal` proves the conclusion of Stacks 041Z
— affineness of morphisms of algebraic spaces over `S` is fpqc local on the base — from one
named hypothesis, `AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc`, which its
docstring describes as *Stacks 0245 together with Stacks 02L5, 0APL and 041Y*. This file
discharges that hypothesis from **Stacks 0APL alone**: if every algebraic space over `S` is a
sheaf for the fpqc topology of the big fppf site of `S`, then effective descent for affine
morphisms along a finite fpqc covering of an affine object of the site holds.

So the residue of Stacks 041Z in this development is exactly Stacks 0APL, and no part of it is
owed to Stacks 0245, 02L5 or 041Y: those three are supplied here, by the affine descent of
`StacksFrontier.AlgebraicGeometry.Descent.AffineFlatChartCandidate` and by sheaf theory.

## Main definitions

There are no new definitions, and no new named hypothesis is coined: the fpqc sheaf condition
is carried as an ordinary hypothesis in the shape in which
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition` states Stacks 0APL.

## Main results

* `AlgebraicGeometry.Space.sieve_generate_singleton_mem_fpqcTopology_over`: a surjective flat
  quasi-compact morphism of the site generates an fpqc covering sieve.
* `AlgebraicGeometry.Space.isLocallySurjective_datumToPullback_of_fpqc`: the datum covers the
  descended fibre product, for a flat quasi-compact chart and the fpqc topology.
* `AlgebraicGeometry.Space.exists_comparison_of_invariant_of_isSheaf`: the comparison morphism
  of a candidate for the descended object, for an arbitrary topology on the site.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc`: **the
  descent step from a candidate, along a surjective flat quasi-compact chart.** This is the
  fpqc analogue of
  `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant`, which asks for an
  étale chart.
* `AlgebraicGeometry.Space.isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc`:
  **`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` from Stacks 0APL.**

## Implementation notes

*Where the fpqc sheaf condition is used, and where it is not.* The proof of the étale descent
step has five parts, and four of them transpose to a chart which is only surjective, flat and
quasi-compact with no input beyond the fpqc covering condition of such a chart: the local
surjectivity of the canonical morphism out of the datum, the construction of the comparison
morphism `l` by sheafifying the range of that morphism, and the local injectivity and local
surjectivity of `l`. Each of those is a diagram chase over a one-element covering, and the only
sheaf conditions they consume are those of the *representable* presheaves `yoneda.obj bb` and
`yoneda.obj a`, which are fpqc sheaves unconditionally by
`AlgebraicGeometry.BigFppfOver.isSheaf_fpqc_yoneda_obj` — fpqc subcanonicity of the site.

The fifth part is the step which turns local bijectivity of `l` into invertibility, and it is
the whole of the hypothesis: `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso` asks for both
ends to be sheaves for the topology in question, and the source end is the descended fibre
product `X ×[Y] yoneda.obj a`, an algebraic space. Its fpqc *separatedness* is available
unconditionally, as `AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`; what is missing is
the existence half, the amalgamation of a compatible family on an fpqc covering, which is
Gabber's Stacks 0APL.

*Why the comparison lemma is restated rather than reused.*
`AlgebraicGeometry.Space.exists_comparison_of_invariant` is stated at
`AlgebraicGeometry.BigFppfOver.topology`, so it cannot be instantiated at the fpqc topology;
`AlgebraicGeometry.Space.exists_comparison_of_invariant_of_isSheaf` is the same proof with the
topology abstracted and its two sheaf conditions taken as hypotheses, and the fppf statement is
its instance at `AlgebraicGeometry.BigFppfOver.topology`. The older statement is left in place,
so the two coexist; whoever next touches
`StacksFrontier.AlgebraicGeometry.Descent.CandidateEtaleDescent` should replace its body by an
application of this one.

*What the composition of the pieces is.* The chart of
`AlgebraicGeometry.BigFppfOver.exists_affine_chart_of_finite_fpqc` replaces the finite covering
family by the single morphism out of its coproduct, which is affine because a finite coproduct
of affine objects of the site is affine; the per-member data is glued over that coproduct by
`AlgebraicGeometry.Space.presheaf_pullback_snd_cofanDesc_of_finite`, which is Zariski gluing
and needs only the fppf sheaf conditions that `AlgebraicGeometry.IsAlgebraicSpace` carries; the
descended affine object is produced as a candidate by
`AlgebraicGeometry.Space.exists_affineCandidate_of_isPullback`, which is the affine case of
Stacks 0245 with its descended morphism affine by construction, so that Stacks 02L5 is not
needed either; and Stacks 041Y is not needed because the comparison morphism is shown to be an
isomorphism by local bijectivity rather than by fpqc descent of the property of being an
isomorphism.

*Nothing is tagged.* Every statement here carries the fpqc sheaf condition as a hypothesis, so
none of them is Stacks 041Z, and the two steps of Stacks 0245 and 02L5 they use are already
tagged where they are proved. In particular `@[stacks 041Z]` is **not** placed here.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 03NY](https://stacks.math.columbia.edu/tag/03NY)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-! ### A flat affine chart generates an fpqc covering sieve -/

/-- A surjective, flat, quasi-compact morphism of the big fppf site of `S` generates a covering
sieve for the fpqc topology of the site. -/
theorem sieve_generate_singleton_mem_fpqcTopology_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (q : T' ⟶ T)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q)) :
    Sieve.generate (Presieve.singleton q) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck T := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Precoverage.mem_comap_iff, Presieve.map_singleton]
  have := hqs
  have := hqf
  have := hqc
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

/-- A sieve on `T` containing every composite `u ≫ pullback.fst s q`, where `q` is surjective, flat
and quasi-compact, is a covering sieve for the fpqc topology of the site. -/
private theorem mem_fpqcTopology_over_of_forall_comp_pullback_fst
    {T : BigFppfOver B S hS} (s : T ⟶ a) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q)) (R : Sieve T)
    (hR : ∀ {Z : BigFppfOver B S hS} (u : Z ⟶ pullback s q), R.arrows (u ≫ pullback.fst s q)) :
    R ∈ (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck T := by
  have sqS : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst s q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd s q))
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map q) :=
    (IsPullback.of_hasPullback s q).map (BigFppfOver.toScheme B S hS)
  refine (Scheme.fpqcPrecoverage.comap
      (BigFppfOver.toScheme B S hS)).toGrothendieck.superset_covering ?_
    (sieve_generate_singleton_mem_fpqcTopology_over B S hS (pullback.fst s q)
      (MorphismProperty.of_isPullback sqS.flip hqs) (MorphismProperty.of_isPullback sqS.flip hqf)
      (MorphismProperty.of_isPullback sqS.flip hqc))
  rintro Z _ ⟨Z', u, _, ⟨⟩, rfl⟩
  exact hR u

/-- A section `ξ` of the descended fibre product over `s` lifts, over the base change of `q`, to a
morphism `α` to the datum `A`, and `α` composed with the canonical morphism out of the datum is
the restriction of `ξ`. -/
private theorem exists_lift_comp_eq_of_descentDatum (sq : IsPullback m r f (yoneda.map q ≫ h))
    {T : BigFppfOver B S hS} {s : T ⟶ a} (ξ : yoneda.obj T ⟶ pullback f h)
    (hξ : ξ ≫ pullback.snd f h = yoneda.map s) :
    ∃ α : yoneda.obj (pullback s q) ⟶ A, α ≫ r = yoneda.map (pullback.snd s q) ∧
      α ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]) = yoneda.map (pullback.fst s q) ≫ ξ := by
  obtain ⟨α, h₁, h₂⟩ := exists_lift_of_descentDatum sq ξ hξ
    (pullback.fst s q) (pullback.snd s q) pullback.condition
  refine ⟨α, h₂, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, (IsPullback.of_hasPullback f h).lift_fst, h₁, Category.assoc]
  · rw [Category.assoc, (IsPullback.of_hasPullback f h).lift_snd, ← Category.assoc, h₂,
      Category.assoc, hξ, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-! ### The datum covers the descended fibre product, for a flat affine chart -/

/-- **The datum covers the descended fibre product, for a flat chart, in the fpqc topology.**
Let `(m, r)` present `A` as the base change of `f` along `yoneda.map q ≫ h`, with `q`
surjective, flat and quasi-compact. Then the canonical morphism from `A` to
`X ×[Y] yoneda.obj a` — the one whose components are `m` and `r ≫ yoneda.map q` — is locally
surjective for the *fpqc* topology of the site.

This is `AlgebraicGeometry.Space.isLocallySurjective_datumToPullback` with étaleness of the
chart replaced by flatness together with quasi-compactness, and the fppf topology replaced by
the fpqc one: the covering on which a section lifts is the one generated by the base change of
the chart, which is an fpqc covering of the site by
`AlgebraicGeometry.Space.sieve_generate_singleton_mem_fpqcTopology_over`. -/
theorem isLocallySurjective_datumToPullback_of_fpqc (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q)) :
    Presheaf.IsLocallySurjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
      ((IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc])) := by
  constructor
  intro T x
  obtain ⟨α, -, hα⟩ := exists_lift_comp_eq_of_descentDatum sq (yonedaEquiv.symm x)
    (yonedaEquiv_symm_comp_pullback_snd x)
  refine mem_fpqcTopology_over_of_forall_comp_pullback_fst
    ((pullback.snd f h).app (op T) x) hqs hqf hqc _ fun u => ?_
  refine ⟨yonedaEquiv (yoneda.map u ≫ α), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, hα, ← Category.assoc, ← Functor.map_comp]
  exact (map_op_eq_yonedaEquiv (F := pullback f h) x _).symm

/-! ### The comparison morphism, for an arbitrary topology of the site -/

/-- The invariance of `k`, read on sections: two sections of the datum `A` with the same image in
the descended fibre product have the same image under `e.hom ≫ yoneda.map k`. -/
private theorem app_eq_of_app_eq_of_invariant {bb v : BigFppfOver B S hS} {k : v ⟶ bb}
    {w : v ⟶ c} {κ : A ⟶ pullback f h} (hκ1 : κ ≫ pullback.fst f h = m)
    (hκ2 : κ ≫ pullback.snd f h = r ≫ yoneda.map q)
    (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r)
    (hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ k = ζ₂ ≫ k)
    (W : BigFppfOver B S hS) (z₁ z₂ : A.obj (op W)) (hz : κ.app (op W) z₁ = κ.app (op W) z₂) :
    (e.hom ≫ yoneda.map k).app (op W) z₁ = (e.hom ≫ yoneda.map k).app (op W) z₂ := by
  have hym : ∀ {W : BigFppfOver B S hS} (x : W ⟶ v), yonedaEquiv.symm x = yoneda.map x :=
    fun x => (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map x).symm
  have hmz : yonedaEquiv.symm z₁ ≫ m = yonedaEquiv.symm z₂ ≫ m := by
    rw [← hκ1, ← Category.assoc, ← Category.assoc, ← yonedaEquiv_symm_comp κ z₁,
      ← yonedaEquiv_symm_comp κ z₂, hz]
  have hrz : yonedaEquiv.symm z₁ ≫ r ≫ yoneda.map q
      = yonedaEquiv.symm z₂ ≫ r ≫ yoneda.map q := by
    rw [← hκ2, ← Category.assoc, ← Category.assoc, ← yonedaEquiv_symm_comp κ z₁,
      ← yonedaEquiv_symm_comp κ z₂, hz]
  have key : ∀ z : A.obj (op W),
      yoneda.map (e.hom.app (op W) z) = yonedaEquiv.symm z ≫ e.hom := by
    intro z
    rw [← hym, yonedaEquiv_symm_comp e.hom z]
  have key1 : ∀ z : A.obj (op W), yoneda.map (e.hom.app (op W) z) ≫ e.inv ≫ m
      = yonedaEquiv.symm z ≫ m := by
    intro z
    rw [key z, Category.assoc, Iso.hom_inv_id_assoc]
  have key2 : ∀ z : A.obj (op W), yoneda.map (e.hom.app (op W) z ≫ w ≫ q)
      = yonedaEquiv.symm z ≫ r ≫ yoneda.map q := by
    intro z
    rw [Functor.map_comp, Functor.map_comp, key z, ← he]
    simp only [Category.assoc]
  show e.hom.app (op W) z₁ ≫ k = e.hom.app (op W) z₂ ≫ k
  exact hinv _ _ (by rwa [key1 z₁, key1 z₂])
    (yoneda.map_injective (by rwa [key2 z₁, key2 z₂]))

/-- **The comparison morphism of a candidate for the descended object, for an arbitrary
topology.** This is `AlgebraicGeometry.Space.exists_comparison_of_invariant` with the fppf
topology of the site replaced by an arbitrary Grothendieck topology `J` on it, the two sheaf
conditions it used being taken as hypotheses.

Let `κ` be the canonical morphism from the datum `A` to the descended fibre product, given by
its two components, and assume it is locally surjective for `J`. Let `k : v ⟶ bb` and
`i : bb ⟶ a` with `k ≫ i = w ≫ q`, let `e : A ≅ yoneda.obj v` lie over `yoneda.obj c`, and
assume the invariance: two morphisms `W ⟶ v` which agree over `X` and over `a` agree after `k`.
Then there is a morphism `l` from the descended fibre product to `yoneda.obj bb` which restricts
to the candidate along the datum, `κ ≫ l = e.hom ≫ yoneda.map k`, and lies over
`yoneda.obj a`.

Nothing of the fppf topology was used in the original proof beyond the sheaf condition of the
two representables involved, which is why the statement is available at the fpqc topology,
where the representables are sheaves by
`AlgebraicGeometry.BigFppfOver.isSheaf_fpqc_yoneda_obj`. -/
theorem exists_comparison_of_invariant_of_isSheaf
    (J : GrothendieckTopology (BigFppfOver B S hS))
    {bb v : BigFppfOver B S hS} {i : bb ⟶ a} {k : v ⟶ bb} {w : v ⟶ c}
    {κ : A ⟶ pullback f h} (hκ1 : κ ≫ pullback.fst f h = m)
    (hκ2 : κ ≫ pullback.snd f h = r ≫ yoneda.map q)
    (hls : Presheaf.IsLocallySurjective J κ)
    (hbb : Presheaf.IsSheaf J (yoneda.obj bb)) (ha : Presheaf.IsSheaf J (yoneda.obj a))
    (hki : k ≫ i = w ≫ q)
    (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r)
    (hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ k = ζ₂ ≫ k) :
    ∃ l : pullback f h ⟶ yoneda.obj bb,
      κ ≫ l = e.hom ≫ yoneda.map k ∧ l ≫ yoneda.map i = pullback.snd f h := by
  set t := e.hom ≫ yoneda.map k with htdef
  -- the range of `κ`, whose sheafification is everything
  have hGtop : (Subfunctor.range κ).sheafify J = ⊤ :=
    (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' _ κ).1 hls
  have hbbsheaf : Presieve.IsSheaf J (yoneda.obj bb) := (isSheaf_iff_isSheaf_of_type _ _).1 hbb
  have hasheaf : Presieve.IsSheaf J (yoneda.obj a) := (isSheaf_iff_isSheaf_of_type _ _).1 ha
  have hcomp : t ≫ yoneda.map i = κ ≫ pullback.snd f h := by
    rw [htdef, hκ2, Category.assoc, ← Functor.map_comp, hki, ← he, Functor.map_comp,
      Category.assoc]
  obtain ⟨t', htr⟩ := Subfunctor.exists_hom_range_of_invariant κ t fun W =>
    app_eq_of_app_eq_of_invariant hκ1 hκ2 e he hinv W.unop
  have hiso : IsIso ((Subfunctor.range κ).sheafify J).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 hGtop
  refine ⟨inv ((Subfunctor.range κ).sheafify J).ι ≫
    (Subfunctor.range κ).sheafifyLift t' hbbsheaf, ?_, ?_⟩
  · have h1 : κ ≫ inv ((Subfunctor.range κ).sheafify J).ι
        = Subfunctor.toRange κ ≫ Subfunctor.homOfLe ((Subfunctor.range κ).le_sheafify J) := by
      rw [IsIso.comp_inv_eq, Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
    rw [← Category.assoc, h1, Category.assoc, Subfunctor.to_sheafifyLift, htr]
  · have huniq : (Subfunctor.range κ).sheafifyLift t' hbbsheaf ≫ yoneda.map i
        = ((Subfunctor.range κ).sheafify J).ι ≫ pullback.snd f h := by
      refine Subfunctor.to_sheafify_lift_unique _ hasheaf _ _ ?_
      rw [← Category.assoc, Subfunctor.to_sheafifyLift, ← Category.assoc,
        Subfunctor.homOfLe_ι]
      refine (cancel_epi (Subfunctor.toRange κ)).1 ?_
      rw [← Category.assoc, htr, hcomp, ← Category.assoc, Subfunctor.toRange_ι]
    rw [Category.assoc, huniq, IsIso.inv_hom_id_assoc]

/-- A morphism of presheaves which is an isomorphism followed by the image of a morphism `i` of
the site with `P` is representable with `P`. -/
private theorem presheaf_inverseImage_of_isIso_comp_yoneda_map
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {bb : BigFppfOver B S hS} {i : bb ⟶ a}
    {g : F ⟶ yoneda.obj a} (l : F ⟶ yoneda.obj bb) [IsIso l] (hl : l ≫ yoneda.map i = g)
    (hi : P ((BigFppfOver.toScheme B S hS).map i)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g := by
  have := (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))).respectsIso
  rw [← hl]
  exact MorphismProperty.RespectsIso.precomp _ l _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P i).2 hi)

/-! ### Effective descent from a candidate, along a flat quasi-compact chart -/

/-- **Local injectivity of the comparison morphism, along a flat quasi-compact chart.** A
morphism `l` from the descended fibre product to `yoneda.obj bb` which restricts to the
candidate along the datum and lies over `yoneda.obj a` is locally injective for the fpqc
topology of the site. -/
private theorem isLocallyInjective_comparison_of_fpqc
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    {bb v : BigFppfOver B S hS} {i : bb ⟶ a} {k : v ⟶ bb} {w : v ⟶ c}
    (csq : IsPullback k w i q) (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r)
    {l : pullback f h ⟶ yoneda.obj bb}
    (hlκ : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ l = e.hom ≫ yoneda.map k)
    (hlfac : l ≫ yoneda.map i = pullback.snd f h) :
    Presheaf.IsLocallyInjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck l := by
  constructor
  intro T x y hxy
  have hxyl : yonedaEquiv.symm x ≫ l = yonedaEquiv.symm y ≫ l := by
    rw [← yonedaEquiv_symm_comp l x, ← yonedaEquiv_symm_comp l y, hxy]
  set s := (pullback.snd f h).app T x
  have hxs : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s :=
    yonedaEquiv_symm_comp_pullback_snd x
  have hys : yonedaEquiv.symm y ≫ pullback.snd f h = yoneda.map s := by
    rw [← hxs, ← hlfac, ← Category.assoc, ← Category.assoc, hxyl]
  obtain ⟨α, hα2, hα⟩ := exists_lift_comp_eq_of_descentDatum sq _ hxs
  obtain ⟨α', hα2', hα'⟩ := exists_lift_comp_eq_of_descentDatum sq _ hys
  have hαα : α = α' := by
    have hw : α ≫ e.hom ≫ yoneda.map w = α' ≫ e.hom ≫ yoneda.map w := by
      rw [he, hα2, hα2']
    have hk : α ≫ e.hom ≫ yoneda.map k = α' ≫ e.hom ≫ yoneda.map k := by
      rw [← hlκ, ← Category.assoc, hα, ← Category.assoc, hα', Category.assoc, Category.assoc,
        hxyl]
    exact (cancel_mono e.hom).1 ((csq.map yoneda).hom_ext hk hw)
  have key : yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm x =
      yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm y := by
    rw [← hα, ← hα', hαα]
  refine mem_fpqcTopology_over_of_forall_comp_pullback_fst s hqs hqf hqc _ fun u => ?_
  change (pullback f h).map (u ≫ pullback.fst s q).op x =
    (pullback f h).map (u ≫ pullback.fst s q).op y
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
    map_op_eq_yonedaEquiv x, map_op_eq_yonedaEquiv y, key]

/-- **Local surjectivity of the comparison morphism, along a flat quasi-compact chart.** A
morphism `l` from the descended fibre product to `yoneda.obj bb` which restricts to the
candidate along the datum is locally surjective for the fpqc topology of the site. -/
private theorem isLocallySurjective_comparison_of_fpqc
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    {bb v : BigFppfOver B S hS} {i : bb ⟶ a} {k : v ⟶ bb} {w : v ⟶ c}
    (csq : IsPullback k w i q) (e : A ≅ yoneda.obj v) {l : pullback f h ⟶ yoneda.obj bb}
    (hlκ : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ l = e.hom ≫ yoneda.map k) :
    Presheaf.IsLocallySurjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck l := by
  constructor
  intro T w₀
  refine mem_fpqcTopology_over_of_forall_comp_pullback_fst (w₀ ≫ i) hqs hqf hqc _ fun u => ?_
  have hcond : (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀) ≫ i =
      (u ≫ pullback.snd (w₀ ≫ i) q) ≫ q := by
    rw [Category.assoc, Category.assoc, Category.assoc, ← pullback.condition]
  have hζk : csq.lift (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀)
      (u ≫ pullback.snd (w₀ ≫ i) q) hcond ≫ k = (u ≫ pullback.fst (w₀ ≫ i) q) ≫ w₀ := by
    rw [csq.lift_fst, Category.assoc]
  refine ⟨yonedaEquiv (yoneda.map (csq.lift (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀)
    (u ≫ pullback.snd (w₀ ≫ i) q) hcond) ≫ e.inv ≫
      (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc])), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, hlκ, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, hζk, yonedaEquiv_yoneda_map]
  rfl

/-- **The descent step from a candidate, along a surjective flat quasi-compact chart.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` and `Y` sheaves for
the **fpqc** topology of the site, let `h : yoneda.obj a ⟶ Y`, let `q : c ⟶ a` be surjective,
flat and quasi-compact and let `(m, r)` present `A` as the base change of `f` along
`yoneda.map q ≫ h`. Suppose given a candidate for the descended object: an object `bb` of the
site with a morphism `i : bb ⟶ a` carrying `P`, a Cartesian square `IsPullback k w i q`
exhibiting `v` as the base change of `i` along `q`, an isomorphism `e : A ≅ yoneda.obj v` over
`yoneda.obj c`, and the invariance of `k`. Then `pullback.snd f h` is representable with `P`.

This is `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant` with the
étale chart replaced by a flat quasi-compact one. Every step of that proof goes through
unchanged in the fpqc topology — local surjectivity of the canonical morphism out of the datum
is `AlgebraicGeometry.Space.isLocallySurjective_datumToPullback_of_fpqc`, the comparison
morphism is `AlgebraicGeometry.Space.exists_comparison_of_invariant_of_isSheaf`, and local
injectivity and local surjectivity of the comparison are the same two diagram chases — except
for the very last step, where local bijectivity is turned into invertibility: that needs the
descended fibre product to be an fpqc **sheaf**, which for an algebraic space is Stacks 0APL
and is the reason this statement carries `hX` and `hY` for the fpqc topology rather than for
the fppf one. -/
theorem presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hX : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck X)
    (hY : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck Y)
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    {bb v : BigFppfOver B S hS} {i : bb ⟶ a} {k : v ⟶ bb} {w : v ⟶ c}
    (hi : P ((BigFppfOver.toScheme B S hS).map i))
    (csq : IsPullback k w i q) (e : A ≅ yoneda.obj v)
    (he : e.hom ≫ yoneda.map w = r)
    (hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ k = ζ₂ ≫ k) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have hκ1 : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ pullback.fst f h = m :=
    (IsPullback.of_hasPullback f h).lift_fst _ _ _
  have hκ2 : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ pullback.snd f h = r ≫ yoneda.map q :=
    (IsPullback.of_hasPullback f h).lift_snd _ _ _
  obtain ⟨l, hlκ, hlfac⟩ := exists_comparison_of_invariant_of_isSheaf _ hκ1 hκ2
    (isLocallySurjective_datumToPullback_of_fpqc sq hqs hqf hqc)
    (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS bb)
    (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS a) csq.w e he hinv
  -- the comparison is an isomorphism
  have hFsheaf : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
      (pullback f h) :=
    BigFppfOver.isSheaf_fpqc_pullback_yoneda_obj f h hX hY
  have hbsheaf : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
      (yoneda.obj bb) :=
    BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS bb
  have hliso : IsIso l := by
    have hsh : IsIso ((⟨l⟩ :
        (⟨pullback f h, hFsheaf⟩ : Sheaf
          (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
            (Type u)) ⟶ ⟨yoneda.obj bb, hbsheaf⟩)) :=
      (Sheaf.isLocallyBijective_iff_isIso _).1
        ⟨isLocallyInjective_comparison_of_fpqc sq hqs hqf hqc csq e he hlκ hlfac,
          isLocallySurjective_comparison_of_fpqc sq hqs hqf hqc csq e hlκ⟩
    exact inferInstanceAs (IsIso ((sheafToPresheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
        (Type u)).map
      ((⟨l⟩ : (⟨pullback f h, hFsheaf⟩ : Sheaf
        (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
          (Type u)) ⟶ ⟨yoneda.obj bb, hbsheaf⟩))))
  exact presheaf_inverseImage_of_isIso_comp_yoneda_map l hlfac hi

/-! ### Effective descent for affine morphisms along an fpqc covering, from Stacks 0APL -/

/-- A Cartesian square exhibiting the base change of `f` along `g` as represented over a
morphism of affine objects of the site makes `pullback.snd f g` representable by affine
morphisms. -/
private theorem presheaf_pullback_snd_of_isPullback_affine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {V W : BigAffineFppf B S hS}
    {g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ G}
    {p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ F}
    {qq : (BigAffineFppf.inclusion B S hS).obj W ⟶ (BigAffineFppf.inclusion B S hS).obj V}
    (hpb : IsPullback p (yoneda.map qq) f g) :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g) := by
  have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj W)) := W.property
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  have hqq : (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map qq) := inferInstance
  exact presheaf_inverseImage_of_isIso_comp_yoneda_map
    ((IsPullback.of_hasPullback f g).isoIsPullback _ _ hpb).hom
    ((IsPullback.of_hasPullback f g).isoIsPullback_hom_snd _ _ hpb) hqq

/-- **`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` follows from Stacks 0APL.**
If every algebraic space over `S` is a sheaf for the fpqc topology of the big fppf site of `S`
— which is Stacks 0APL — then effective descent for affine morphisms along a finite fpqc
covering of an affine object of the site holds, and hence, through
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc`, so does Stacks 041Z.

Every other ingredient of the source's proof is already available, and the proof below is their
composition: `AlgebraicGeometry.BigFppfOver.exists_affine_chart_of_finite_fpqc` replaces the
finite family by the single surjective flat quasi-compact morphism out of its coproduct,
`AlgebraicGeometry.Space.presheaf_pullback_snd_cofanDesc_of_finite` glues the per-member data
over that coproduct by Zariski descent,
`AlgebraicGeometry.Space.exists_affineCandidate_of_isPullback` produces the descended affine
object as a candidate — this is the affine case of Stacks 0245 together with Stacks 02L5 — and
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc` identifies
the descended fibre product with it, which is the step that consumes the fpqc sheaf condition
and therefore the whole of the hypothesis. The conclusion is read back as a Cartesian square
over an affine object through `AlgebraicGeometry.Space.isAffineHom_of_presheaf`, taking the test
morphism to be the identity of the base. -/
theorem isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hAPL : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      Presheaf.IsSheaf
        (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck F) :
    IsEffectiveAffineDescentAlongFpqc B S hS := by
  have hzar : IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      _root_.AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instRespectsIsoScheme _ _
      _root_.AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine
  have _hfppf : MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    have := hzar
    _root_.AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc _
  intro Z 𝒰 hfin hmem F G hF hG f k hall
  -- the chart: the single surjective flat quasi-compact morphism out of the coproduct
  have hmem' : Presieve.ofArrows (fun j => (BigAffineFppf.inclusion B S hS).obj (𝒰.X j))
      (fun j => (BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).coverings
        ((BigAffineFppf.inclusion B S hS).obj Z) := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    rwa [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hmem
  obtain ⟨c, inj, q, ⟨hcol⟩, hcaff, hqs, hqf, hqc, hq⟩ :=
    BigFppfOver.exists_affine_chart_of_finite_fpqc (Z := (BigAffineFppf.inclusion B S hS).obj Z)
      Z.property (fun j => (BigAffineFppf.inclusion B S hS).obj (𝒰.X j))
      (fun j => (BigAffineFppf.inclusion B S hS).map (𝒰.f j))
      (fun j => (𝒰.X j).property) hmem'
  -- the per-member data, as representability with affineness
  have hall' : ∀ j, (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f (yoneda.map ((BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ≫ k)) := by
    intro j
    obtain ⟨W, p, qq, hpb⟩ := hall j
    exact presheaf_pullback_snd_of_isPullback_affine hpb
  -- the datum over the coproduct, by Zariski gluing
  have hr := presheaf_pullback_snd_cofanDesc_of_finite f hF.isSheaf hG.isSheaf k
    (fun j => (BigAffineFppf.inclusion B S hS).obj (𝒰.X j))
    (fun j => (BigAffineFppf.inclusion B S hS).map (𝒰.f j)) hcol q hq hall'
  -- the candidate for the descended object, and its identification with the fibre product
  obtain ⟨bb, v, i, kk, w, hi, csq, e, he, hinv⟩ :=
    exists_affineCandidate_of_isPullback (IsPullback.of_hasPullback f (yoneda.map q ≫ k)) hr
      Z.property hcaff hqs hqf
  have hfinal := presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc (hAPL hF) (hAPL hG)
    (IsPullback.of_hasPullback f (yoneda.map q ≫ k)) hqs hqf hqc hi csq e he hinv
  -- read the conclusion back as a Cartesian square over the affine base
  obtain ⟨W, p, qq, hpb⟩ := isAffineHom_of_presheaf hfinal Z (𝟙 _)
  exact ⟨W, p ≫ pullback.fst f k, qq,
    by simpa using hpb.paste_horiz (IsPullback.of_hasPullback f k)⟩

end AlgebraicGeometry.Space

end
