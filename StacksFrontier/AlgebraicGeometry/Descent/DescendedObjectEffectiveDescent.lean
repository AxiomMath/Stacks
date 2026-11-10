module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent

/-!
# A descent datum with a descended object of the site is effective

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` is the one geometric
hypothesis of Stacks 03I2: morphisms of schemes with property `P` descend *effectively* along a
surjective étale morphism of the big fppf site of `S`. Discharging it at a given `P` splits into
two tasks of completely different character:

* produce, from the descent datum, an object `o` of the site over `a` whose base change along
  the chart `q : c ⟶ a` is the object `v` of the datum, in such a way that the action of the
  groupoid `c ×_a c` on `v` is a morphism over `o`;
* identify `yoneda.obj o` with the fibre product `X ×[Y] yoneda.obj a`.

The first is where the geometry sits and depends on `P`. **The second is formal, and this file
proves it once and for all**: a Cartesian square `v = c ×_a o` of the site, together with the
compatibility of the action with `o`, already forces `X ×[Y] yoneda.obj a` to be represented by
`o`, with the projection to `yoneda.obj a` the morphism `yoneda.map n`. Every property of `n`
then passes to the projection.

## Main results

* `AlgebraicGeometry.Space.exists_isIso_comp_pullback_snd_of_descendedObject`: the comparison.
  Given a descent datum presented by `v` over the chart `c`, its action `s`, and an object `o`
  of the site over `a` with `v = c ×_a o` over which the action is a morphism, there is an
  isomorphism `yoneda.obj o ≅ X ×[Y] yoneda.obj a` carrying `yoneda.map n` to the projection.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_of_descendedObject`: the consequence for a
  property of morphisms of schemes stable under base change — the projection
  `X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is representable with `P` as soon as `n` has `P`.

## Implementation notes

The comparison morphism is the amalgamation, over the covering `t : v ⟶ o`, of the section of
`X ×[Y] yoneda.obj a` carried by `v`. Three things make that work, and all three are already
available:

* `t` is a covering of `o`: it is the base change of the chart `q` along `n`, by the Cartesian
  square, so it is surjective and étale.
* the section is compatible with that covering, which is
  `AlgebraicGeometry.Space.descentSection_eq_of_comp_eq` — this is the only place the action and
  its compatibility with `o` are used;
* `X ×[Y] yoneda.obj a` is a sheaf, by
  `AlgebraicGeometry.BigFppfOver.isSheaf_pullback_yoneda_obj`, and `yoneda.obj o` is a sheaf by
  subcanonicality of the site.

The amalgamation is then an isomorphism because it is locally injective and locally surjective
between two sheaves, by `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`. Local surjectivity
is the statement that every section of the fibre product becomes, after one base change of the
chart, a section of the descent datum, which is
`AlgebraicGeometry.Space.exists_lift_of_descentDatum`; local injectivity is the uniqueness of
the action, `AlgebraicGeometry.Space.descentAction_unique`, applied to the translate of one of
the two sections by the other.

Nothing is assumed about `o`, `n` or `v` beyond the Cartesian square: in particular neither is
required to be affine, and no ring enters. That is what makes the statement reusable for a
property whose descended object is not affine — the datum of a quasi-affine morphism descends to
an open subscheme of an affine object, not to an affine one.

`AlgebraicGeometry.Space.presheaf_pullback_snd_isAffineHom_of_isPullback` is the instance of
this statement in which `o` is the spectrum of the descended algebra; the two arguments are the
same and a consolidation pass should route that one through this file.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 02W2](https://stacks.math.columbia.edu/tag/02W2)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c v o : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a} {w : v ⟶ c}
    {n : o ⟶ a} {t : v ⟶ o}
    {P₂ : BigFppfOver B S hS} {ρ₁ : P₂ ⟶ c} {ρ₂ s : P₂ ⟶ v}

/-- A presheaf of types on the big fppf site of `S` which is a sheaf is a sheaf for the
one-element presieve of a surjective étale morphism of the site. -/
private theorem isSheafFor_singleton_of_isSheaf'
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hgs : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hge : Etale ((BigFppfOver.toScheme B S hS).map g)) :
    Presieve.IsSheafFor F (Presieve.singleton g) :=
  ((isSheaf_iff_isSheaf_of_type _ _).1 hF).isSheafFor _
    (sieve_generate_singleton_mem_topology_over B S hS g hgs hge)

/-- **A descent datum with a descended object of the site is effective.** Let `f : X ⟶ Y` be a
morphism of sheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y` be a morphism from a
representable presheaf and let `q : c ⟶ a` be a surjective étale morphism of the site. Let
`(m, r)` present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `A₀` represented
by an object `v` of the site through an isomorphism `e` carrying `r` to `w : v ⟶ c`, and let
`s : P₂ ⟶ v` be the action of the groupoid `P₂ = c ×_a v` on `v` — a morphism over the first
projection agreeing with the second over `X`.

Suppose given an object `o` of the site, a morphism `n : o ⟶ a` and a morphism `t : v ⟶ o`
presenting `v` as `c ×_a o`, over which the action `s` is a morphism. Then `yoneda.obj o` *is*
the base change of `f` along `h`: there is an isomorphism `yoneda.obj o ≅ X ×[Y] yoneda.obj a`
carrying `yoneda.map n` to the projection `pullback.snd f h`.

The isomorphism is the amalgamation over the covering `t` of the section carried by `v`; see the
implementation notes of this file. -/
theorem exists_isIso_comp_pullback_snd_of_descendedObject
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (e : A₀ ≅ yoneda.obj v) (hew : e.hom ≫ yoneda.map w = r)
    (sq₂ : IsPullback ρ₁ ρ₂ q (w ≫ q)) (hs₁ : s ≫ w = ρ₁)
    (hs₂ : yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m)
    (sqv : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map n))
    (hst : s ≫ t = ρ₂ ≫ t) :
    ∃ ℓ : yoneda.obj o ⟶ pullback f h, IsIso ℓ ∧ ℓ ≫ pullback.snd f h = yoneda.map n := by
  have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) :=
    sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
      (by rw [Iso.refl_hom, Category.comp_id, hew]) (by simp) (by simp)
  have hwq : w ≫ q = t ≫ n := comp_eq_comp_of_isPullback_map sqv
  obtain ⟨σ, hσ₁, hσ₂⟩ : ∃ σ : yoneda.obj v ⟶ pullback f h,
      σ ≫ pullback.fst f h = e.inv ≫ m ∧ σ ≫ pullback.snd f h = yoneda.map (w ≫ q) :=
    ⟨pullback.lift _ _ (by rw [vsq.w, Functor.map_comp, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hts : Surjective ((BigFppfOver.toScheme B S hS).map t) :=
    MorphismProperty.of_isPullback sqv hqs
  have hte : Etale ((BigFppfOver.toScheme B S hS).map t) :=
    MorphismProperty.of_isPullback sqv hqe
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  obtain ⟨ℓ₀, hℓ₀, -⟩ := (Presieve.isSheafFor_singleton (P := pullback f h)).1
    (isSheafFor_singleton_of_isSheaf' hFsheaf t hts hte) (yonedaEquiv σ) (by
      intro Z p₁ p₂ hp
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
      -- the section carried by `v` is compatible with the covering `t`
      refine congrArg yonedaEquiv (pullback.hom_ext ?_ ?_)
      · simp only [Category.assoc, hσ₁]
        exact descentSection_eq_of_comp_eq sqv sq₂ hs₁ hs₂ hst hp
      · simp only [Category.assoc, hσ₂, ← Functor.map_comp]
        refine congrArg yoneda.map ?_
        rw [hwq, ← Category.assoc, hp, Category.assoc])
  have htl : yoneda.map t ≫ yonedaEquiv.symm ℓ₀ = σ := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hℓ₀]
  -- the amalgamation lies over `n`
  have hln : yonedaEquiv.symm ℓ₀ ≫ pullback.snd f h = yoneda.map n := by
    have hsep : Function.Injective ((yoneda.obj a).map t.op) :=
      Presieve.isSeparatedFor_singleton.1
        (isSheafFor_singleton_of_isSheaf' (BigFppfOver.isSheaf_yoneda_obj B S hS a) t
          hts hte).isSeparatedFor
    refine yonedaEquiv.injective (hsep ?_)
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    refine congrArg yonedaEquiv ?_
    rw [← Category.assoc, htl, hσ₂, ← Functor.map_comp, hwq]
  -- the amalgamation is locally surjective
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (yonedaEquiv.symm ℓ₀) := by
    constructor
    intro T z
    obtain ⟨g, hg⟩ : ∃ g : T ⟶ a, (pullback.snd f h).app (Opposite.op T) z = g := ⟨_, rfl⟩
    have hz : yonedaEquiv.symm z ≫ pullback.snd f h = yoneda.map g := by
      rw [yonedaEquiv_symm_comp_pullback_snd, hg]
    have sqT : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst g q))
        ((BigFppfOver.toScheme B S hS).map (pullback.snd g q))
        ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map q) :=
      (IsPullback.of_hasPullback g q).map (BigFppfOver.toScheme B S hS)
    obtain ⟨α, hα₁, hα₂⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm z) hz
      (pullback.fst g q) (pullback.snd g q) pullback.condition
    obtain ⟨β, hβ⟩ : ∃ β : Limits.pullback g q ⟶ v, yoneda.map β = α ≫ e.hom :=
      ⟨yoneda.preimage (α ≫ e.hom), Functor.map_preimage _ _⟩
    have hβw : β ≫ w = pullback.snd g q := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, hβ, Category.assoc, hew, hα₂]
    have hβσ : yoneda.map β ≫ σ = yoneda.map (pullback.fst g q) ≫ yonedaEquiv.symm z := by
      refine pullback.hom_ext ?_ ?_
      · simpa only [Category.assoc, hσ₁, hβ, Iso.hom_inv_id_assoc] using hα₁
      · simp only [Category.assoc, hσ₂, hz, ← Functor.map_comp]
        refine congrArg yoneda.map ?_
        rw [← Category.assoc, hβw]
        exact pullback.condition.symm
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (sieve_generate_singleton_mem_topology_over B S hS (pullback.fst g q)
        (MorphismProperty.of_isPullback sqT.flip hqs)
        (MorphismProperty.of_isPullback sqT.flip hqe))
    rintro Z κ ⟨Z', u, _, ⟨⟩, hfac⟩
    refine ⟨u ≫ β ≫ t, ?_⟩
    calc (yonedaEquiv.symm ℓ₀).app (Opposite.op Z) (u ≫ β ≫ t)
        = yonedaEquiv (yoneda.map (u ≫ β ≫ t) ≫ yonedaEquiv.symm ℓ₀) := by
          rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      _ = yonedaEquiv (yoneda.map κ ≫ yonedaEquiv.symm z) := by
          rw [← hfac]
          simp only [Functor.map_comp, Category.assoc, htl, hβσ]
      _ = (pullback f h).map κ.op z := by
          rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  -- the amalgamation is locally injective
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (yonedaEquiv.symm ℓ₀) := by
    constructor
    intro T x y hxy
    have hxyl : yoneda.map x ≫ yonedaEquiv.symm ℓ₀ = yoneda.map y ≫ yonedaEquiv.symm ℓ₀ := by
      refine yonedaEquiv.injective ?_
      rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    have hxn : x ≫ n = y ≫ n := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, Functor.map_comp, ← hln, ← Category.assoc, ← Category.assoc, hxyl]
    have sqX : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst x t))
        ((BigFppfOver.toScheme B S hS).map (pullback.snd x t))
        ((BigFppfOver.toScheme B S hS).map x) ((BigFppfOver.toScheme B S hS).map t) :=
      (IsPullback.of_hasPullback x t).map (BigFppfOver.toScheme B S hS)
    -- the translate of the second projection by the other section of `o`
    have hcond : ((BigFppfOver.toScheme B S hS).map (pullback.snd x t ≫ w)) ≫
        (BigFppfOver.toScheme B S hS).map q =
        ((BigFppfOver.toScheme B S hS).map (pullback.fst x t ≫ y)) ≫
          (BigFppfOver.toScheme B S hS).map n := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      refine congrArg (BigFppfOver.toScheme B S hS).map ?_
      simp only [Category.assoc]
      rw [hwq, ← Category.assoc, ← pullback.condition, Category.assoc, hxn]
    have hβ₂cond : (sqv.lift ((BigFppfOver.toScheme B S hS).map (pullback.snd x t ≫ w))
          ((BigFppfOver.toScheme B S hS).map (pullback.fst x t ≫ y)) hcond) ≫
          B.inclusion.map v.hom = B.inclusion.map (Limits.pullback x t).hom := by
      rw [← BigFppfOver.toScheme_map_comp_hom w, ← Category.assoc, sqv.lift_fst,
        Functor.map_comp, Category.assoc, BigFppfOver.toScheme_map_comp_hom w,
        BigFppfOver.toScheme_map_comp_hom (pullback.snd x t)]
    obtain ⟨β₂, hβ₂⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS _ hβ₂cond
    have hβ₂w : β₂ ≫ w = pullback.snd x t ≫ w := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, hβ₂, sqv.lift_fst]
    have hβ₂t : β₂ ≫ t = pullback.fst x t ≫ y := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, hβ₂, sqv.lift_snd]
    have e1 : yoneda.map (pullback.snd x t) ≫ σ =
        yoneda.map (pullback.fst x t) ≫ yoneda.map x ≫ yonedaEquiv.symm ℓ₀ := by
      rw [← htl, ← Category.assoc, ← Functor.map_comp, ← pullback.condition,
        Functor.map_comp, Category.assoc]
    have e2 : yoneda.map β₂ ≫ σ =
        yoneda.map (pullback.fst x t) ≫ yoneda.map y ≫ yonedaEquiv.symm ℓ₀ := by
      rw [← htl, ← Category.assoc, ← Functor.map_comp, hβ₂t, Functor.map_comp, Category.assoc]
    have hβ₂eq : pullback.snd x t = β₂ := by
      refine descentAction_unique vsq hβ₂w.symm ?_
      have h2 := congrArg (fun κ => κ ≫ pullback.fst f h) (e1.trans (hxyl ▸ e2.symm))
      simp only [Category.assoc, hσ₁] at h2
      exact h2
    have hxy' : pullback.fst x t ≫ x = pullback.fst x t ≫ y := by
      rw [pullback.condition, hβ₂eq, hβ₂t]
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (sieve_generate_singleton_mem_topology_over B S hS (pullback.fst x t)
        (MorphismProperty.of_isPullback sqX.flip hts) (MorphismProperty.of_isPullback sqX.flip hte))
    rintro Z κ ⟨Z', u, _, ⟨⟩, hfac⟩
    change κ ≫ x = κ ≫ y
    rw [← hfac, Category.assoc, Category.assoc, hxy']
  -- two locally bijective morphisms of sheaves are isomorphisms
  let φ : (⟨yoneda.obj o, BigFppfOver.isSheaf_yoneda_obj B S hS o⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨pullback f h, hFsheaf⟩ :=
    ⟨yonedaEquiv.symm ℓ₀⟩
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨hli, hls⟩
  exact ⟨yonedaEquiv.symm ℓ₀,
    inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map φ)), hln⟩

/-- **The projection of a descent datum with a descended object of the site carries every
property of that object's structure morphism.** In the situation of
`AlgebraicGeometry.Space.exists_isIso_comp_pullback_snd_of_descendedObject`, if the structure
morphism `n : o ⟶ a` of the descended object has a property `P` of morphisms of schemes stable
under base change, then the base change of `f` along `h` is representable with `P`.

This is the shape in which `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`
consumes the comparison. -/
theorem presheaf_pullback_snd_of_descendedObject {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (e : A₀ ≅ yoneda.obj v) (hew : e.hom ≫ yoneda.map w = r)
    (sq₂ : IsPullback ρ₁ ρ₂ q (w ≫ q)) (hs₁ : s ≫ w = ρ₁)
    (hs₂ : yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m)
    (sqv : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map n))
    (hst : s ≫ t = ρ₂ ≫ t)
    (hn : P ((BigFppfOver.toScheme B S hS).map n)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  obtain ⟨ℓ, _, hℓn⟩ := exists_isIso_comp_pullback_snd_of_descendedObject hX hY hqs hqe
    sq e hew sq₂ hs₁ hs₂ sqv hst
  have hRI : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  rw [show pullback.snd f h = inv ℓ ≫ yoneda.map n by rw [← hℓn, IsIso.inv_hom_id_assoc]]
  exact MorphismProperty.RespectsIso.precomp _ (inv ℓ) _
    (presheaf_yoneda_map_of_inverseImage B S hS hP n hn)

end AlgebraicGeometry.Space

end
