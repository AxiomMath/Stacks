module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent

/-!
# Effective descent along a surjective étale chart, from a candidate and its invariance

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` asks for the
representability of `X ×[Y] yoneda.obj a` with property `P` whenever the base change of
`f : X ⟶ Y` along a surjective étale `q : c ⟶ a` of the big fppf site of `S` is representable
with `P`. For `P` contained in the monomorphisms,
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms` reduces this to
the production of a candidate for the descended object: an object `b` of the site with
`i : b ⟶ a` carrying `P` whose base change along `q` is the given datum. **This file removes the
hypothesis that `P` be contained in the monomorphisms**, at the cost of one extra equation, and
that equation is the descent datum's own invariance.

*What monomorphy was doing, and what replaces it.* For a monomorphic candidate the comparison
morphism `l : X ×[Y] yoneda.obj a ⟶ yoneda.obj b` is free: the range of `yoneda.map i` is a
subsheaf of `yoneda.obj a`, so a section of the descended fibre product which lies in it names a
section of `yoneda.obj b`. For a general candidate there is no such shortcut, and `l` has to be
produced by descending the morphism `A ⟶ yoneda.obj b` of the datum along the covering. That is
done here with `CategoryTheory.Subfunctor.sheafify`: the canonical morphism
`κ : A ⟶ X ×[Y] yoneda.obj a` is locally surjective
(`AlgebraicGeometry.Space.isLocallySurjective_datumToPullback`), so the sheafification of its
range is everything, and the morphism to `yoneda.obj b` defined on that range —
`CategoryTheory.Subfunctor.exists_hom_range_of_invariant` — extends to the whole fibre product by
`CategoryTheory.Subfunctor.sheafifyLift`. Defining it on the range is exactly where the extra
hypothesis is used: two sections of the datum with the same image in the fibre product must have
the same image in `yoneda.obj b`.

*Why the extra hypothesis is not the conclusion in disguise.* It is the equation
`ζ₁ ≫ k = ζ₂ ≫ k` for two morphisms `ζ₁, ζ₂ : W ⟶ v` of the site which agree over `X` and over
`a` — a single equality of morphisms of the site between given objects, with no existential. For
a monomorphic `P` it is automatic.

## Main results

* `CategoryTheory.Subfunctor.exists_hom_range_of_invariant`: a morphism of type-valued presheaves
  which identifies sections with the same image under another morphism factors through the range
  of that other morphism.
* `AlgebraicGeometry.Space.isLocallySurjective_datumToPullback`: **the datum covers the descended
  fibre product.** The canonical morphism from the datum `A` to `X ×[Y] yoneda.obj a` is locally
  surjective for the fppf topology, because every section of the fibre product lifts to the datum
  over the base change of the chart.
* `AlgebraicGeometry.Space.exists_comparison_of_invariant`: **the comparison morphism.** Given a
  candidate `k : v ⟶ b` for the descended object and the invariance equation, there is a morphism
  `l : X ×[Y] yoneda.obj a ⟶ yoneda.obj b` restricting to the candidate on the datum and lying
  over `yoneda.obj a`.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant`: **the descent step
  from a candidate, for an arbitrary property.** The comparison morphism is locally injective and
  locally surjective, hence an isomorphism, so `pullback.snd f h` is representable with `P`.
* `Space.isEffectiveDescentAlongSurjectiveEtale_of_exists_isPullback_of_invariant` is the same
  statement as a reduction of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` to the production of a
  candidate together with its invariance.

## Implementation notes

Local injectivity of the comparison morphism is *not* local injectivity of the datum: for a
property which is not contained in the monomorphisms the datum `r` is not a monomorphism and
`AlgebraicGeometry.Space.isLocallyInjective_pullback_snd` does not apply. Instead two sections of
the fibre product with the same image under `l` are lifted to the datum over the base change of
the chart, and the two lifts are *equal*: they agree over `b` because `l` does, and over `c`
because both lie over the same section, and the candidate square identifies the datum with
`b ×_a c`, so `CategoryTheory.IsPullback.hom_ext` applies. The comparison is therefore locally
injective because the lifts already agree on a single covering.

The invariance hypothesis is stated through `e.inv ≫ m`, the leg to `X` of the Cartesian square
read on the representing object, rather than through the canonical morphism `κ` to the fibre
product: the two forms are equivalent, and the first mentions only the data of the statement.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Subfunctor

/-- **A morphism which cannot tell apart sections with the same image factors through the
range.** Let `p : F ⟶ G` and `t : F ⟶ H` be morphisms of type-valued functors, and suppose that
`t` identifies any two sections of `F` with the same image under `p`. Then `t` factors through
the range of `p`, as a morphism `Subfunctor.range p ⟶ H` whose composite with
`CategoryTheory.Subfunctor.toRange` is `t`.

The factorization is defined by choosing, for a section of the range, a preimage under `p`; the
hypothesis is what makes that choice irrelevant, and is therefore both the well-definedness and
the naturality of the result. -/
theorem exists_hom_range_of_invariant {D : Type u} [Category.{v} D] {F G H : D ⥤ Type w}
    (p : F ⟶ G) (t : F ⟶ H)
    (hinv : ∀ (W : D) (z₁ z₂ : F.obj W), p.app W z₁ = p.app W z₂ → t.app W z₁ = t.app W z₂) :
    ∃ t' : (Subfunctor.range p).toFunctor ⟶ H, Subfunctor.toRange p ≫ t' = t := by
  refine ⟨{ app := fun W => ↾fun y => t.app W y.2.choose, naturality := ?_ }, ?_⟩
  · intro W W' g
    ext y
    refine Eq.trans ?_ (NatTrans.naturality_apply t g y.2.choose)
    refine hinv W' _ _ ?_
    rw [((Subfunctor.range p).toFunctor.map g y).2.choose_spec,
      NatTrans.naturality_apply p g y.2.choose, y.2.choose_spec]
    rfl
  · ext W z
    exact hinv W _ z ((Subfunctor.toRange p).app W z).2.choose_spec

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

/-- Naming a section of a presheaf of types as a morphism out of a representable presheaf is
compatible with postcomposition. -/
public theorem yonedaEquiv_symm_comp {C : Type*} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u}
    (g : F ⟶ G) {W : Cᵒᵖ} (z : F.obj W) :
    yonedaEquiv.symm (g.app W z) = yonedaEquiv.symm z ≫ g := by
  refine (Equiv.symm_apply_eq _).2 ?_
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-! ### The datum covers the descended fibre product -/

/-- The base change of a surjective étale `q : c ⟶ a` along `s : T ⟶ a` generates a covering
sieve of `T`. -/
private theorem sieve_generate_pullback_fst_mem
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) {T : BigFppfOver B S hS} (s : T ⟶ a) :
    Sieve.generate (Presieve.singleton (pullback.fst s q)) ∈ BigFppfOver.topology B S hS T := by
  have sqS : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst s q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd s q))
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map q) :=
    (IsPullback.of_hasPullback s q).map (BigFppfOver.toScheme B S hS)
  exact sieve_generate_singleton_mem_topology_over B S hS (pullback.fst s q)
    (MorphismProperty.of_isPullback sqS.flip hqs) (MorphismProperty.of_isPullback sqS.flip hqe)

/-- A section `ξ` of `X ×[Y] yoneda.obj a` lying over `s : T ⟶ a` lifts, over the base change of
the chart along `s`, to the datum `A`: the lift lies over `yoneda.obj c` and is, after the
canonical morphism `κ` to the fibre product, the restriction of `ξ`. -/
private theorem exists_lift_comp_eq (sq : IsPullback m r f (yoneda.map q ≫ h))
    {κ : A ⟶ pullback f h} (hκ1 : κ ≫ pullback.fst f h = m)
    (hκ2 : κ ≫ pullback.snd f h = r ≫ yoneda.map q) {T : BigFppfOver B S hS} {s : T ⟶ a}
    (ξ : yoneda.obj T ⟶ pullback f h) (hξ : ξ ≫ pullback.snd f h = yoneda.map s) :
    ∃ β : yoneda.obj (pullback s q) ⟶ A,
      β ≫ κ = yoneda.map (pullback.fst s q) ≫ ξ ∧ β ≫ r = yoneda.map (pullback.snd s q) := by
  obtain ⟨β, h1, h2⟩ := exists_lift_of_descentDatum sq ξ hξ
    (pullback.fst s q) (pullback.snd s q) pullback.condition
  refine ⟨β, pullback.hom_ext ?_ ?_, h2⟩
  · rw [Category.assoc, hκ1, h1, Category.assoc]
  · rw [Category.assoc, hκ2, ← Category.assoc, h2, Category.assoc, hξ,
      ← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-- **The datum covers the descended fibre product.** Let `(m, r)` present `A` as the base change
of `f` along `yoneda.map q ≫ h`, with `q` surjective étale. Then the canonical morphism from `A`
to `X ×[Y] yoneda.obj a` — the one whose components are `m` and `r ≫ yoneda.map q` — is locally
surjective for the fppf topology of the site.

A section of `X ×[Y] yoneda.obj a` over `T` lies over some `s : T ⟶ a`, and over the base change
`T ×_a c` of the chart, which covers `T`, it lifts to the datum by
`AlgebraicGeometry.Space.exists_lift_of_descentDatum`. -/
theorem isLocallySurjective_datumToPullback (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc])) := by
  constructor
  intro T x
  obtain ⟨s, hs⟩ : ∃ s : T ⟶ a, (pullback.snd f h).app (op T) x = s := ⟨_, rfl⟩
  have hx : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s := by
    rw [yonedaEquiv_symm_comp_pullback_snd, hs]
  obtain ⟨α, hακ, -⟩ := exists_lift_comp_eq sq
    ((IsPullback.of_hasPullback f h).lift_fst _ _ (by rw [sq.w, Category.assoc]))
    ((IsPullback.of_hasPullback f h).lift_snd _ _ _) (yonedaEquiv.symm x) hx
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (sieve_generate_pullback_fst_mem hqs hqe s)
  rintro Z k₀ ⟨Z', u, bb, hbb, hfac⟩
  cases hbb
  refine ⟨yonedaEquiv (yoneda.map u ≫ α), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, hακ, ← Category.assoc, ← Functor.map_comp, hfac]
  exact (map_op_eq_yonedaEquiv (F := pullback f h) x _).symm


/-! ### The comparison morphism -/

/-- **The comparison morphism of a candidate for the descended object.** Let `κ` be the canonical
morphism from the datum `A` to the descended fibre product, given by its two components, and
assume it is locally surjective — which is
`AlgebraicGeometry.Space.isLocallySurjective_datumToPullback`. Let `k : v ⟶ b` and `i : b ⟶ a`
with `k ≫ i = w ≫ q`, let `e : A ≅ yoneda.obj v` lie over `yoneda.obj c`, and assume the
invariance: two morphisms `W ⟶ v` which agree over `X` and over `a` agree after `k`. Then there
is a morphism `l` from the descended fibre product to `yoneda.obj b` which restricts to the
candidate along the datum, `κ ≫ l = e.hom ≫ yoneda.map k`, and lies over `yoneda.obj a`.

This is pure sheaf theory: `l` is the extension to the sheafification of the range of `κ` of the
morphism which the invariance defines on that range. Its second property is forced, because
`CategoryTheory.Subfunctor.toRange` is an epimorphism. -/
theorem exists_comparison_of_invariant
    {bb v : BigFppfOver B S hS} {i : bb ⟶ a} {k : v ⟶ bb} {w : v ⟶ c}
    {κ : A ⟶ pullback f h} (hκ1 : κ ≫ pullback.fst f h = m)
    (hκ2 : κ ≫ pullback.snd f h = r ≫ yoneda.map q)
    (hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) κ)
    (hki : k ≫ i = w ≫ q)
    (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r)
    (hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ k = ζ₂ ≫ k) :
    ∃ l : pullback f h ⟶ yoneda.obj bb,
      κ ≫ l = e.hom ≫ yoneda.map k ∧ l ≫ yoneda.map i = pullback.snd f h := by
  set t := e.hom ≫ yoneda.map k with htdef
  have hym : ∀ {W : BigFppfOver B S hS} (x : W ⟶ v), yonedaEquiv.symm x = yoneda.map x := by
    intro W x
    refine (Equiv.symm_apply_eq _).2 ?_
    rw [yonedaEquiv_yoneda_map]
  -- the invariance, read on sections
  have hinv' : ∀ (W : BigFppfOver B S hS) (z₁ z₂ : A.obj (op W)),
      κ.app (op W) z₁ = κ.app (op W) z₂ → t.app (op W) z₁ = t.app (op W) z₂ := by
    intro W z₁ z₂ hz
    have hκz : yonedaEquiv.symm z₁ ≫ κ = yonedaEquiv.symm z₂ ≫ κ := by
      rw [← yonedaEquiv_symm_comp κ z₁, ← yonedaEquiv_symm_comp κ z₂, hz]
    have hmz : yonedaEquiv.symm z₁ ≫ m = yonedaEquiv.symm z₂ ≫ m := by
      rw [← hκ1, ← Category.assoc, ← Category.assoc, hκz]
    have hrz : yonedaEquiv.symm z₁ ≫ r ≫ yoneda.map q
        = yonedaEquiv.symm z₂ ≫ r ≫ yoneda.map q := by
      rw [← hκ2, ← Category.assoc, ← Category.assoc, hκz]
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
    have hta : ∀ z : A.obj (op W), t.app (op W) z = e.hom.app (op W) z ≫ k := fun _ => rfl
    rw [hta, hta]
    refine hinv _ _ ?_ ?_
    · rw [key1 z₁, key1 z₂]
      exact hmz
    · refine yoneda.map_injective ?_
      rw [key2 z₁, key2 z₂]
      exact hrz
  -- the range of `κ`, whose sheafification is everything
  have hGtop : (Subfunctor.range κ).sheafify (BigFppfOver.topology B S hS) = ⊤ :=
    (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' _ κ).1 hls
  have hbbsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj bb) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS bb)
  have hasheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj a) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS a)
  have hcomp : t ≫ yoneda.map i = κ ≫ pullback.snd f h := by
    rw [htdef, hκ2, Category.assoc, ← Functor.map_comp, hki, ← he, Functor.map_comp,
      Category.assoc]
  obtain ⟨t', htr⟩ := Subfunctor.exists_hom_range_of_invariant κ t fun W => hinv' W.unop
  have hiso : IsIso ((Subfunctor.range κ).sheafify (BigFppfOver.topology B S hS)).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 hGtop
  refine ⟨inv ((Subfunctor.range κ).sheafify (BigFppfOver.topology B S hS)).ι ≫
    (Subfunctor.range κ).sheafifyLift t' hbbsheaf, ?_, ?_⟩
  · have h1 : κ ≫ inv ((Subfunctor.range κ).sheafify (BigFppfOver.topology B S hS)).ι
        = Subfunctor.toRange κ ≫ Subfunctor.homOfLe
          ((Subfunctor.range κ).le_sheafify (BigFppfOver.topology B S hS)) := by
      rw [IsIso.comp_inv_eq, Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
    rw [← Category.assoc, h1, Category.assoc, Subfunctor.to_sheafifyLift, htr]
  · have huniq : (Subfunctor.range κ).sheafifyLift t' hbbsheaf ≫ yoneda.map i
        = ((Subfunctor.range κ).sheafify (BigFppfOver.topology B S hS)).ι
            ≫ pullback.snd f h := by
      refine Subfunctor.to_sheafify_lift_unique _ hasheaf _ _ ?_
      rw [← Category.assoc, Subfunctor.to_sheafifyLift, ← Category.assoc,
        Subfunctor.homOfLe_ι]
      refine (cancel_epi (Subfunctor.toRange κ)).1 ?_
      rw [← Category.assoc, htr, hcomp, ← Category.assoc, Subfunctor.toRange_ι]
    rw [Category.assoc, huniq, IsIso.inv_hom_id_assoc]

/-! ### Effective descent from a candidate -/

/-- **The descent step from a candidate, for a property which need not be monomorphic.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` and `Y` sheaves, let
`h : yoneda.obj a ⟶ Y`, let `q : c ⟶ a` be surjective étale and let `(m, r)` present `A` as the
base change of `f` along `yoneda.map q ≫ h`. Suppose given a candidate for the descended object:
an object `b` of the site with `i : b ⟶ a` carrying `P`, a Cartesian square `IsPullback k w i q`
exhibiting `v` as the base change of `i` along `q`, an isomorphism `e : A ≅ yoneda.obj v` over
`yoneda.obj c`, and the invariance of `k`. Then `pullback.snd f h` is representable with `P`.

This is `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms` with
the hypothesis `P ≤ monomorphisms` traded for the invariance equation. The comparison morphism is
`AlgebraicGeometry.Space.exists_comparison_of_invariant`; it is locally surjective because the
Cartesian square lifts every section of `yoneda.obj b` over a base change of the chart, and
locally injective because two lifts of sections with the same image agree on both legs of the
square. -/
theorem presheaf_pullback_snd_of_isPullback_of_invariant
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {bb v : BigFppfOver B S hS} {i : bb ⟶ a} {k : v ⟶ bb} {w : v ⟶ c}
    (hi : P ((BigFppfOver.toScheme B S hS).map i))
    (csq : IsPullback k w i q) (e : A ≅ yoneda.obj v)
    (he : e.hom ≫ yoneda.map w = r)
    (hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ k = ζ₂ ≫ k) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have hRIpre : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have hinvr : e.inv ≫ r = yoneda.map w := by rw [← he, Iso.inv_hom_id_assoc]
  have hκ1 : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ pullback.fst f h = m :=
    (IsPullback.of_hasPullback f h).lift_fst _ _ _
  have hκ2 : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ pullback.snd f h = r ≫ yoneda.map q :=
    (IsPullback.of_hasPullback f h).lift_snd _ _ _
  obtain ⟨l, hlκ, hlfac⟩ := exists_comparison_of_invariant hκ1 hκ2
    (isLocallySurjective_datumToPullback sq hqs hqe) csq.w e he hinv
  have hysq : IsPullback (yoneda.map k) (yoneda.map w) (yoneda.map i) (yoneda.map q) :=
    csq.map yoneda
  -- local injectivity
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) l := by
    constructor
    intro T x y hxy
    have hxyl : yonedaEquiv.symm x ≫ l = yonedaEquiv.symm y ≫ l := by
      rw [← yonedaEquiv_symm_comp l x, ← yonedaEquiv_symm_comp l y, hxy]
    obtain ⟨s, hs⟩ : ∃ s : T.unop ⟶ a, (pullback.snd f h).app T x = s := ⟨_, rfl⟩
    have hxs : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s := by
      rw [yonedaEquiv_symm_comp_pullback_snd, hs]
    have hys : yonedaEquiv.symm y ≫ pullback.snd f h = yoneda.map s := by
      rw [← hxs, ← hlfac, ← Category.assoc, ← Category.assoc, hxyl]
    obtain ⟨α, hακx, hα2⟩ := exists_lift_comp_eq sq hκ1 hκ2 (yonedaEquiv.symm x) hxs
    obtain ⟨α', hακy, hα2'⟩ := exists_lift_comp_eq sq hκ1 hκ2 (yonedaEquiv.symm y) hys
    have hαα : α = α' := by
      have hw : α ≫ e.hom ≫ yoneda.map w = α' ≫ e.hom ≫ yoneda.map w := by
        rw [he, hα2, hα2']
      have hk : α ≫ e.hom ≫ yoneda.map k = α' ≫ e.hom ≫ yoneda.map k := by
        rw [← hlκ, ← Category.assoc, hακx, ← Category.assoc, hακy, Category.assoc,
          Category.assoc, hxyl]
      exact (cancel_mono e.hom).1 (hysq.hom_ext hk hw)
    have key : yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm x =
        yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm y := by
      rw [← hακx, ← hακy, hαα]
    have h1 : (pullback f h).map (pullback.fst s q).op x =
        (pullback f h).map (pullback.fst s q).op y := by
      rw [map_op_eq_yonedaEquiv x, map_op_eq_yonedaEquiv y, key]
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (sieve_generate_pullback_fst_mem hqs hqe s)
    rintro Z k₀ ⟨Z', u, bb', hbb, hfac⟩
    cases hbb
    show (pullback f h).map k₀.op x = (pullback f h).map k₀.op y
    rw [← hfac, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h1]
  -- local surjectivity
  have hlsur : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) l := by
    constructor
    intro T w₀
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (sieve_generate_pullback_fst_mem hqs hqe (w₀ ≫ i))
    rintro Z k₀ ⟨Z', u, bb', hbb, hfac⟩
    cases hbb
    have hcond : (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀) ≫ i =
        (u ≫ pullback.snd (w₀ ≫ i) q) ≫ q := by
      rw [Category.assoc, Category.assoc, Category.assoc, ← pullback.condition]
    have hζk : csq.lift (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀)
        (u ≫ pullback.snd (w₀ ≫ i) q) hcond ≫ k = k₀ ≫ w₀ := by
      rw [csq.lift_fst, ← hfac, Category.assoc]
    refine ⟨yonedaEquiv (yoneda.map (csq.lift (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀)
      (u ≫ pullback.snd (w₀ ≫ i) q) hcond) ≫ e.inv ≫
        (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
          (by rw [sq.w, Category.assoc])), ?_⟩
    rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, hlκ, Iso.inv_hom_id_assoc,
      ← Functor.map_comp, hζk, yonedaEquiv_yoneda_map]
    rfl
  -- the comparison is an isomorphism
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hbsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj bb) :=
    BigFppfOver.isSheaf_yoneda_obj B S hS bb
  have hliso : IsIso l := by
    have hsh : IsIso ((⟨l⟩ :
        (⟨pullback f h, hFsheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨yoneda.obj bb, hbsheaf⟩)) :=
      (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hli, hlsur⟩
    exact inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map
      ((⟨l⟩ : (⟨pullback f h, hFsheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨yoneda.obj bb, hbsheaf⟩))))
  rw [← hlfac]
  exact MorphismProperty.RespectsIso.precomp _ l _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P i).2 hi)

/-- **Effective descent along the surjective étale morphisms of the site, reduced to the
production of a candidate and its invariance.** For a property `P` of morphisms of schemes stable
under base change, effective descent along the surjective étale morphisms of the big fppf site of
`S` follows from producing, for every descent datum, an object `b` of the site with a morphism
`i : b ⟶ a` carrying `P` whose base change along the chart is the datum — as a Cartesian square
of the site together with an isomorphism identifying the datum's presheaf with the represented
one over `yoneda.obj c` — and the invariance of the resulting morphism `v ⟶ b`. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_exists_isPullback_of_invariant
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∃ (bb v : BigFppfOver B S hS) (i : bb ⟶ a) (k : v ⟶ bb) (w : v ⟶ c),
            P ((BigFppfOver.toScheme B S hS).map i) ∧ IsPullback k w i q ∧
            ∃ e : A ≅ yoneda.obj v, e.hom ≫ yoneda.map w = r ∧
              ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
                yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
                ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ k = ζ₂ ≫ k) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  intro X' Y' f' hX hY a' c' h' q' hqs hqe A' m' r' sq' hr'
  obtain ⟨bb, v, i, k, w, hi, csq, e, he, hinv⟩ := H f' hX hY h' q' hqs hqe m' r' sq' hr'
  exact presheaf_pullback_snd_of_isPullback_of_invariant hX hY sq' hqs hqe hi csq e he hinv

end AlgebraicGeometry.Space

end
