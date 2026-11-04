module

public import StacksCore.Tactic.StacksAttribute

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace

/-!
# Effective descent of open immersions along a surjective étale chart

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` is the one geometric
hypothesis of Stacks 03I2: morphisms of schemes with property `P` descend *effectively* along a
surjective étale morphism of the big fppf site of `S`. This file discharges it for
`P = AlgebraicGeometry.IsOpenImmersion`, outright and with no further hypothesis.

Effective descent is in general the content of Stacks 02W8, whose proof passes through Zariski's
main theorem (Stacks 02LR) and effective descent for quasi-affine morphisms (Stacks 0247). For
open immersions none of that is needed: an open immersion into a scheme is determined by the open
*subset* which is its image, and an open subset of the chart which is stable under the descent
datum descends by elementary topology, because a surjective étale morphism of schemes is an open
surjection, hence a topological quotient map. Concretely, if `A' ⟶ c` is the open piece of the
chart cut out by the descent datum then its image `V` in `a` is open, satisfies
`q⁻¹(V) = A'`, and the open subscheme of `a` on `V` — which is again an object of the site, by
`AlgebraicGeometry.exists_restrict_bigFppfOver` — represents `X ×[Y] yoneda.obj a`.

## Main results

* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion` is Stacks
  03I2's geometric input for open immersions: open immersions of schemes descend effectively
  along the surjective étale morphisms of the big fppf site of `S`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_and_isOpenImmersion_of_surjectiveEtaleChart` is
  Stacks 03I2 itself for open immersions, unconditionally: a morphism from a sheaf to an
  algebraic space over `S` which becomes an open immersion over one surjective étale chart of
  its target has an algebraic space as its source and is itself an open immersion.
* `AlgebraicGeometry.Space.isOpenImmersion_tfae_of_isAlgebraicSpace` is **Stacks 03M4 for open
  immersions**, unconditionally: the five conditions of that tag are equivalent for an open
  immersion of algebraic spaces over `S`. It is
  `AlgebraicGeometry.Space.isOpenImmersion_tfae` with its hypothesis discharged.
* `AlgebraicGeometry.Space.isOpenSubspace_invariantSubspace` is the open-subscheme case of
  Stacks 07TW, unconditionally: the subspace of an algebraic space cut out by an invariant open
  subscheme of a surjective étale chart is an open subspace.
* `AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion`: a morphism of the site whose image lies
  in the image of an open immersion of the site factors through it.
* `AlgebraicGeometry.range_snd_of_isPullback`: the image of one projection of a Cartesian square
  of schemes is the preimage of the image of the opposite morphism. This is the `IsPullback`
  form, which Mathlib has only for the category of types
  (`CategoryTheory.Limits.Types.range_snd_of_isPullback`).
* `AlgebraicGeometry.Space.preimage_range_eq_preimage_range` is the stability of the open piece
  under the descent datum: the two pullbacks to `c ×_a c` of the open subset cut out on the chart
  agree.

## Implementation notes

The identification of the descended fibre product with the open subscheme is made through
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`: the comparison morphism
`X ×[Y] yoneda.obj a ⟶ yoneda.obj b` is shown to be locally injective and locally surjective,
and both presheaves are sheaves — the fibre product by
`AlgebraicGeometry.BigFppfOver.isSheaf_pullback_yoneda_obj` and the representable by
subcanonicality of the site, `AlgebraicGeometry.BigFppfOver.isSheaf_yoneda_obj`. No global
gluing is performed by hand: local injectivity is the mono-ness of the descent datum, read on a
single surjective étale covering, and local surjectivity is the factorization of that covering
through the open piece.

The two statements which actually use the geometry are
`AlgebraicGeometry.Space.range_subset_image_range` — the image of a section of the descended
fibre product lies in `V`, proved by lifting a point along the surjective chart — and
`AlgebraicGeometry.Space.preimage_range_eq_preimage_range`, the stability of the open piece. The
latter is where the descent datum enters: the two base changes of the datum to `c ×_a c` are
pullbacks of `f` along *the same* morphism `yoneda.map (pr₁ ≫ q) ≫ h = yoneda.map (pr₂ ≫ q) ≫ h`,
so they are isomorphic over `c ×_a c` and their images coincide.

This argument is specific to open immersions and does **not** extend to the other two immersion
properties: a closed subscheme of the chart is not determined by its underlying closed subset, so
descending it is descent of a quasi-coherent ideal and needs Stacks 0247. The underlying sets do
descend — the image of a stable closed subset under an open surjection is closed, and the image
of a stable locally closed subset is locally closed, since saturated sets have saturated closures
under a quotient map — but the scheme structure does not.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- The image of the second projection of a Cartesian square of schemes is the preimage of the
image of the opposite morphism. This is
`AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback` taken at the whole source. -/
theorem range_snd_of_isPullback {P X Y Z : Scheme.{u}} {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    {g₁ : X ⟶ Z} {g₂ : Y ⟶ Z} (sq : IsPullback p₁ p₂ g₁ g₂) :
    Set.range p₂.base = g₂.base ⁻¹' Set.range g₁.base := by
  simpa using Scheme.image_preimage_eq_of_isPullback sq Set.univ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the big fppf category over `S` whose image lies in the image of an open
immersion of that category factors through it, and the factorization is again a morphism of the
category: the underlying factorization of schemes exists by
`AlgebraicGeometry.IsOpenImmersion.lift`, and it is compatible with the structure morphisms
because the open immersion is. -/
theorem exists_comp_eq_of_isOpenImmersion {V U T : BigFppfOver B S hS} (i : V ⟶ U)
    (hi : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i)) (g : T ⟶ U)
    (hg : Set.range ((BigFppfOver.toScheme B S hS).map g).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map i).base) :
    ∃ k : T ⟶ V, k ≫ i = g := by
  have := hi
  have hfac : IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map g) hg ≫ (BigFppfOver.toScheme B S hS).map i =
      (BigFppfOver.toScheme B S hS).map g := IsOpenImmersion.lift_fac _ _ hg
  refine ⟨Over.homMk (ObjectProperty.homMk (IsOpenImmersion.lift
    ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map g) hg)) ?_, ?_⟩
  · refine B.inclusion.map_injective ?_
    have hwg := congrArg B.inclusion.map (Over.w g)
    have hwi := congrArg B.inclusion.map (Over.w i)
    simp only [Functor.map_comp] at hwg hwi ⊢
    show IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map g) hg ≫ B.inclusion.map V.hom = _
    rw [← hwi, ← Category.assoc]
    show (_ ≫ (BigFppfOver.toScheme B S hS).map i) ≫ _ = _
    rw [hfac]
    exact hwg
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp]
    show IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map g) hg ≫ (BigFppfOver.toScheme B S hS).map i = _
    exact hfac

namespace Space

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-- Restricting a section of a presheaf of types along a morphism, in terms of the morphism out
of a representable presheaf which the section names. -/
public theorem map_op_eq_yonedaEquiv {C : Type*} [Category.{v} C] {F : Cᵒᵖ ⥤ Type v}
    {T : Cᵒᵖ} (x : F.obj T) {Z : C} (k : Z ⟶ T.unop) :
    F.map k.op x = yonedaEquiv (yoneda.map k ≫ yonedaEquiv.symm x) := by
  rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- A section of a fibre product over a representable presheaf, viewed as a morphism out of a
representable presheaf, lies over the morphism of the site which is its second component. -/
theorem yonedaEquiv_symm_comp_pullback_snd {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (pullback f h).obj T) :
    yonedaEquiv.symm x ≫ pullback.snd f h =
      yoneda.map ((pullback.snd f h).app T x) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]

/-- The universal property of the descent datum. Let `m, r` present `A` as the base change of
`f` along `yoneda.map q ≫ h`, let `xt` be a section of `X ×[Y] yoneda.obj a` over an object `T`
of the site lying over `s : T ⟶ a`, and let `p₁, p₂` be a pair of morphisms with
`p₁ ≫ s = p₂ ≫ q`. Then the restriction of `xt` along `p₁`, taken together with `p₂`, is a
section of `A`. -/
theorem exists_lift_of_descentDatum (sq : IsPullback m r f (yoneda.map q ≫ h))
    {T T' : BigFppfOver B S hS} (xt : yoneda.obj T ⟶ pullback f h) {s : T ⟶ a}
    (hxs : xt ≫ pullback.snd f h = yoneda.map s)
    (p₁ : T' ⟶ T) (p₂ : T' ⟶ c) (hp : p₁ ≫ s = p₂ ≫ q) :
    ∃ α : yoneda.obj T' ⟶ A, α ≫ m = yoneda.map p₁ ≫ xt ≫ pullback.fst f h ∧
      α ≫ r = yoneda.map p₂ := by
  refine ⟨sq.lift (yoneda.map p₁ ≫ xt ≫ pullback.fst f h) (yoneda.map p₂) ?_,
    sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  calc (yoneda.map p₁ ≫ xt ≫ pullback.fst f h) ≫ f
      = yoneda.map p₁ ≫ (xt ≫ pullback.snd f h) ≫ h := by
        rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition]
    _ = yoneda.map (p₂ ≫ q) ≫ h := by
        rw [hxs, ← Category.assoc, ← Functor.map_comp, hp]
    _ = yoneda.map p₂ ≫ yoneda.map q ≫ h := by rw [Functor.map_comp, Category.assoc]

/-- The image of a morphism of schemes of the site lies in the image of another one when the first
factors through the second. -/
private theorem range_map_subset_of_comp_eq {P P' Q : BigFppfOver B S hS} (u : P ⟶ P')
    (v : P ⟶ Q) (v' : P' ⟶ Q) (h : u ≫ v' = v) :
    Set.range ((BigFppfOver.toScheme B S hS).map v).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map v').base := by
  rintro x ⟨y, rfl⟩
  exact ⟨((BigFppfOver.toScheme B S hS).map u).base y, by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, h]⟩

/-- A pullback square of the site gives a pullback square of the underlying schemes. -/
private theorem isPullback_map_toScheme_pullback {T a c : BigFppfOver B S hS} (s : T ⟶ a)
    (q : c ⟶ a) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst s q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd s q))
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map q) :=
  (IsPullback.of_hasPullback s q).map (BigFppfOver.toScheme B S hS)

/-- The first projection of the pullback of a surjective étale morphism of the site generates a
covering sieve. -/
private theorem sieve_generate_fst_mem_topology {T a c : BigFppfOver B S hS} (s : T ⟶ a)
    (q : c ⟶ a) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    Sieve.generate (Presieve.singleton (pullback.fst s q)) ∈ BigFppfOver.topology B S hS T :=
  sieve_generate_singleton_mem_topology_over B S hS (pullback.fst s q)
    (MorphismProperty.of_isPullback (isPullback_map_toScheme_pullback s q).flip hqs)
    (MorphismProperty.of_isPullback (isPullback_map_toScheme_pullback s q).flip hqe)

/-- **Every section of the descended fibre product lies over the image of the open piece.** If
`xt` is a section of `X ×[Y] yoneda.obj a` over an object `T` of the site lying over
`s : T ⟶ a`, then the image of `s` on underlying schemes is contained in the image under the
chart of the piece of `c` cut out by the descent datum.

The chart is surjective, so a point of `T` is covered by a point of `T ×_a c`; the descent datum
turns that point into a point of the representing object of `A`, by the universal property of
`A` as the base change of `f`. -/
theorem range_subset_image_range (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hrep : yoneda.relativelyRepresentable r)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    {T : BigFppfOver B S hS} (xt : yoneda.obj T ⟶ pullback f h) {s : T ⟶ a}
    (hxs : xt ≫ pullback.snd f h = yoneda.map s) :
    Set.range ((BigFppfOver.toScheme B S hS).map s).base ⊆
      ((BigFppfOver.toScheme B S hS).map q).base ''
        Set.range ((BigFppfOver.toScheme B S hS).map
          (hrep.snd (𝟙 (yoneda.obj c)))).base := by
  rintro t ⟨t0, rfl⟩
  have sqS := isPullback_map_toScheme_pullback s q
  have hp1surj : Surjective ((BigFppfOver.toScheme B S hS).map (pullback.fst s q)) :=
    MorphismProperty.of_isPullback sqS.flip hqs
  obtain ⟨t', ht'⟩ := ((BigFppfOver.toScheme B S hS).map (pullback.fst s q)).surjective t0
  obtain ⟨α, -, hα2⟩ := exists_lift_of_descentDatum sq xt hxs (pullback.fst s q)
    (pullback.snd s q) pullback.condition
  have hβ : hrep.lift α (pullback.snd s q) (by rw [hα2, Category.comp_id]) ≫
      hrep.snd (𝟙 (yoneda.obj c)) = pullback.snd s q := hrep.lift_snd _ _ _
  refine ⟨((BigFppfOver.toScheme B S hS).map (pullback.snd s q)).base t',
    range_map_subset_of_comp_eq _ _ _ hβ ⟨t', rfl⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← sqS.w, Scheme.Hom.comp_apply, ht']

/-- **The open piece cut out on the chart by a descent datum is stable.** The two pullbacks to
`c ×_a c` of the piece of `c` cut out by the descent datum agree as subsets of the underlying
scheme.

This is the only place where the Cartesian square of the descent datum is used for more than a
universal property: the two base changes of the datum to `c ×_a c` are base changes of `f` along
the *same* morphism, because `pr₁ ≫ q = pr₂ ≫ q`, hence isomorphic over `c ×_a c`. -/
theorem preimage_range_eq_preimage_range
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hrep : yoneda.relativelyRepresentable r) :
    ((BigFppfOver.toScheme B S hS).map (pullback.fst q q)).base ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map
          (hrep.snd (𝟙 (yoneda.obj c)))).base =
      ((BigFppfOver.toScheme B S hS).map (pullback.snd q q)).base ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map
          (hrep.snd (𝟙 (yoneda.obj c)))).base := by
  have key : ∀ d : Limits.pullback q q ⟶ c,
      ((BigFppfOver.toScheme B S hS).map d).base ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map (hrep.snd (𝟙 (yoneda.obj c)))).base =
      Set.range ((BigFppfOver.toScheme B S hS).map (hrep.snd (yoneda.map d))).base := by
    intro d
    obtain ⟨l, hl⟩ := exists_isPullback_snd_comp B S hS hrep (𝟙 (yoneda.obj c)) d
      (yoneda.map d) (Category.comp_id _)
    exact (range_snd_of_isPullback hl).symm
  rw [key, key]
  have big : ∀ d : Limits.pullback q q ⟶ c,
      IsPullback (hrep.fst (yoneda.map d) ≫ m)
        (yoneda.map (hrep.snd (yoneda.map d))) f (yoneda.map d ≫ yoneda.map q ≫ h) :=
    fun d => (hrep.isPullback (yoneda.map d)).paste_horiz sq
  have hcond' : yoneda.map (pullback.fst q q) ≫ yoneda.map q ≫ h
      = yoneda.map (pullback.snd q q) ≫ yoneda.map q ≫ h := by
    rw [← Category.assoc, ← Functor.map_comp, pullback.condition, Functor.map_comp,
      Category.assoc]
  have e1 : IsPullback (hrep.fst (yoneda.map (pullback.fst q q)) ≫ m)
      (yoneda.map (hrep.snd (yoneda.map (pullback.fst q q)))) f
      (yoneda.map (pullback.snd q q) ≫ yoneda.map q ≫ h) := hcond' ▸ big (pullback.fst q q)
  have e2 := big (pullback.snd q q)
  set θ := e1.isoIsPullback X (yoneda.obj (Limits.pullback q q)) e2
  have hθs : θ.hom ≫ yoneda.map (hrep.snd (yoneda.map (pullback.snd q q))) =
      yoneda.map (hrep.snd (yoneda.map (pullback.fst q q))) :=
    e1.isoIsPullback_hom_snd _ _ e2
  set pre := yoneda.preimage θ.hom
  have hmap : yoneda.map pre = θ.hom := yoneda.map_preimage _
  have hfac : pre ≫ hrep.snd (yoneda.map (pullback.snd q q)) =
      hrep.snd (yoneda.map (pullback.fst q q)) :=
    yoneda.map_injective (by rw [Functor.map_comp, hmap, hθs])
  have hiso : IsIso pre := by
    have h' : IsIso (yoneda.map pre) := by
      rw [hmap]
      infer_instance
    exact isIso_of_reflects_iso _ yoneda
  have hinv : inv pre ≫ hrep.snd (yoneda.map (pullback.fst q q)) =
      hrep.snd (yoneda.map (pullback.snd q q)) := by
    rw [← hfac, IsIso.inv_hom_id_assoc]
  exact Set.Subset.antisymm (range_map_subset_of_comp_eq _ _ _ hfac)
    (range_map_subset_of_comp_eq _ _ _ hinv)

/-- **The descended morphism is locally injective.** If the descent datum `r` is a
monomorphism, then the projection `X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is locally injective for
the fppf topology: two sections with the same image agree after the base change of the chart,
because they then define the same section of `A`. -/
theorem isLocallyInjective_pullback_snd (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hrmono : Mono r) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) (pullback.snd f h) := by
  constructor
  intro T x y hxy
  obtain ⟨s, hs⟩ : ∃ s : T.unop ⟶ a, (pullback.snd f h).app T x = s := ⟨_, rfl⟩
  have hx : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s := by
    rw [yonedaEquiv_symm_comp_pullback_snd, hs]
  have hy : yonedaEquiv.symm y ≫ pullback.snd f h = yoneda.map s := by
    rw [yonedaEquiv_symm_comp_pullback_snd, ← hxy, hs]
  obtain ⟨α, hα1, hα2⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm x) hx
    (pullback.fst s q) (pullback.snd s q) pullback.condition
  obtain ⟨α', hα1', hα2'⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm y) hy
    (pullback.fst s q) (pullback.snd s q) pullback.condition
  have hαα : α = α' := (cancel_mono r).1 (hα2.trans hα2'.symm)
  have key : yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm x =
      yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm y := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← hα1, ← hα1', hαα]
    · rw [Category.assoc, Category.assoc, hx, hy]
  have h1 : (pullback f h).map (pullback.fst s q).op x =
      (pullback f h).map (pullback.fst s q).op y := by
    rw [map_op_eq_yonedaEquiv (F := pullback f h) x, map_op_eq_yonedaEquiv (F := pullback f h) y,
      key]
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (sieve_generate_fst_mem_topology s q hqs hqe)
  rintro Z k ⟨Z', u, bb, hbb, hfac⟩
  cases hbb
  show (pullback f h).map k.op x = (pullback f h).map k.op y
  rw [← hfac, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h1]

/-- **The geometric input of Stacks 03I2 for open immersions, outright.** Open immersions of
schemes descend effectively along the surjective étale morphisms of the big fppf site of `S`:
whenever a morphism `f : X ⟶ Y` of sheaves becomes representable by an open immersion after base
change along a surjective étale morphism `q : c ⟶ a` of the site, its base change along
`h : yoneda.obj a ⟶ Y` is already representable by an open immersion.

The descended object is the open subscheme of `a` on the image `V` of the open piece cut out on
`c`. That image is open because a surjective étale morphism of schemes is an open map (Stacks
01UA), it satisfies `q⁻¹(V) = A'` by
`AlgebraicGeometry.Space.preimage_range_eq_preimage_range`, and it is an object of the site by
`AlgebraicGeometry.exists_restrict_bigFppfOver`. The comparison with `X ×[Y] yoneda.obj a` is an
isomorphism because it is locally injective and locally surjective between two sheaves.

This discharges the hypothesis `hdesc` of every theorem which takes
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at the open immersions, or at a
property contained in them. It does **not** discharge it at `AlgebraicGeometry.IsImmersion`, at
`AlgebraicGeometry.IsClosedImmersion` or at `AlgebraicGeometry.IsQuasiAffineHom`: see the
implementation notes. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) := by
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  have hRIoi : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hRIpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have hmono : (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) ≤
      MorphismProperty.monomorphisms Scheme.{u} := fun _ _ g hg => by
    have := hg
    exact (inferInstance : Mono g)
  have hrmono : Mono r := mono_of_presheaf hmono hr
  have hr'oi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hr.rep.snd (𝟙 (yoneda.obj c)))) :=
    hr.property_snd (𝟙 (yoneda.obj c))
  obtain ⟨Vc, hVcdef⟩ : ∃ Vc : Set ((BigFppfOver.toScheme B S hS).obj c),
      Set.range ((BigFppfOver.toScheme B S hS).map
        (hr.rep.snd (𝟙 (yoneda.obj c)))).base = Vc := ⟨_, rfl⟩
  have hVcopen : IsOpen Vc := by
    rw [← hVcdef]
    have := hr'oi
    exact IsOpenImmersion.isOpen_range _
  have hqopen : IsOpenMap ((BigFppfOver.toScheme B S hS).map q).base := by
    have := hqe
    exact ((BigFppfOver.toScheme B S hS).map q).isOpenMap
  -- stability of the open piece: `q⁻¹(q(Vc)) = Vc`
  have hstab : ((BigFppfOver.toScheme B S hS).map q).base ⁻¹'
      (((BigFppfOver.toScheme B S hS).map q).base '' Vc) ⊆ Vc := by
    have sqD := isPullback_map_toScheme_pullback q q
    have hkey := preimage_range_eq_preimage_range sq hr.rep
    rw [hVcdef] at hkey
    have h1 := Scheme.image_preimage_eq_of_isPullback sqD Vc
    rw [hkey] at h1
    rw [← h1]
    exact Set.image_preimage_subset _ _
  -- the descended open subscheme of `a`
  obtain ⟨b, i, hioi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver a
    ⟨((BigFppfOver.toScheme B S hS).map q).base '' Vc, hqopen _ hVcopen⟩
  have hirange' : Set.range ((BigFppfOver.toScheme B S hS).map i).base =
      ((BigFppfOver.toScheme B S hS).map q).base '' Vc := hirange
  have hmonoi : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (by have := hioi; exact (inferInstance : Mono ((BigFppfOver.toScheme B S hS).map i)))
  have hlr : Subfunctor.range (pullback.snd f h) ≤ Subfunctor.range (yoneda.map i) := by
    intro T s hsmem
    obtain ⟨x, rfl⟩ := hsmem
    have hsub := range_subset_image_range sq hr.rep hqs (yonedaEquiv.symm x)
      (yonedaEquiv_symm_comp_pullback_snd x)
    rw [hVcdef] at hsub
    obtain ⟨g, hg⟩ := hiuniv ((pullback.snd f h).app T x) hsub
    exact ⟨g, hg⟩
  obtain ⟨l, hlfac⟩ : ∃ l : pullback f h ⟶ yoneda.obj b,
      l ≫ yoneda.map i = pullback.snd f h := by
    have h1 : inv (Subfunctor.toRange (yoneda.map i)) ≫ yoneda.map i =
        (Subfunctor.range (yoneda.map i)).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι (yoneda.map i)).symm
    refine ⟨Subfunctor.lift (pullback.snd f h) hlr ≫
      inv (Subfunctor.toRange (yoneda.map i)), ?_⟩
    rw [Category.assoc, h1, Subfunctor.lift_ι]
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) l :=
    have := isLocallyInjective_pullback_snd sq hrmono hqs hqe
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac _ hlfac
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) l := by
    constructor
    intro T w
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (sieve_generate_fst_mem_topology (w ≫ i) q hqs hqe)
    rintro Z k ⟨Z', u, bb, hbb, hfac⟩
    cases hbb
    have heq : (u ≫ pullback.snd (w ≫ i) q) ≫ q = (k ≫ w) ≫ i := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hfac, Category.assoc]
    have hrangesub : Set.range ((BigFppfOver.toScheme B S hS).map
        (u ≫ pullback.snd (w ≫ i) q)).base ⊆ Vc := by
      rintro z ⟨z0, rfl⟩
      refine hstab ?_
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Functor.map_comp, heq,
        Functor.map_comp, Scheme.Hom.comp_apply, ← hirange']
      exact ⟨_, rfl⟩
    obtain ⟨vv, hvv⟩ := exists_comp_eq_of_isOpenImmersion (hr.rep.snd (𝟙 (yoneda.obj c)))
      hr'oi (u ≫ pullback.snd (w ≫ i) q) (by rw [hVcdef]; exact hrangesub)
    have hw0 : hr.rep.fst (𝟙 (yoneda.obj c)) ≫ r =
        yoneda.map (hr.rep.snd (𝟙 (yoneda.obj c))) := by
      have hw := hr.rep.w (𝟙 (yoneda.obj c))
      rwa [Category.comp_id] at hw
    have hsqw : m ≫ f = (r ≫ yoneda.map q) ≫ h := by rw [sq.w, Category.assoc]
    have hxisnd : (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
          pullback.lift m (r ≫ yoneda.map q) hsqw) ≫ pullback.snd f h =
        yoneda.map ((k ≫ w) ≫ i) := by
      calc (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
            pullback.lift m (r ≫ yoneda.map q) hsqw) ≫ pullback.snd f h
          = yoneda.map vv ≫ (hr.rep.fst (𝟙 (yoneda.obj c)) ≫ r) ≫ yoneda.map q := by
            simp only [Category.assoc, pullback.lift_snd]
        _ = yoneda.map ((vv ≫ hr.rep.snd (𝟙 (yoneda.obj c))) ≫ q) := by
            rw [hw0, Functor.map_comp, Functor.map_comp, Category.assoc]
        _ = yoneda.map ((k ≫ w) ≫ i) := by rw [hvv, heq]
    have hxil : (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
        pullback.lift m (r ≫ yoneda.map q) hsqw) ≫ l = yoneda.map (k ≫ w) := by
      rw [← cancel_mono (yoneda.map i), Category.assoc, hlfac, hxisnd, ← Functor.map_comp]
    refine ⟨yonedaEquiv (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
      pullback.lift m (r ≫ yoneda.map q) hsqw), ?_⟩
    rw [← yonedaEquiv_comp, hxil, yonedaEquiv_yoneda_map]
    rfl
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hbsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj b) :=
    BigFppfOver.isSheaf_yoneda_obj B S hS b
  have hliso : IsIso l := by
    have hsh : IsIso ((⟨l⟩ :
        (⟨pullback f h, hFsheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨yoneda.obj b, hbsheaf⟩)) :=
      (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hli, hls⟩
    exact inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map
      ((⟨l⟩ : (⟨pullback f h, hFsheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨yoneda.obj b, hbsheaf⟩))))
  rw [← hlfac]
  exact MorphismProperty.RespectsIso.precomp _ l _
    (presheaf_yoneda_map_of_inverseImage B S hS inferInstance i hioi)

/-- **Stacks 03I2 for open immersions**, unconditionally. Let `f : X ⟶ Y` be a morphism of
presheaves on the big fppf site of `S` with `X` a sheaf and `Y` an algebraic space over `S`. If
some surjective étale chart `g` of `Y` makes the base change of `f` an open immersion, then `X`
is an algebraic space over `S` and `f` is an open immersion.

This is
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`
with its descent hypothesis supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`. -/
theorem isAlgebraicSpace_and_isOpenImmersion_of_surjectiveEtaleChart
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : IsAlgebraicSpace B S hS Y)
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : IsOpenImmersion B S hS (pullback.snd f g)) :
    IsAlgebraicSpace B S hS X ∧ IsOpenImmersion B S hS f :=
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS) hX hY hs he hV

/-- **Stacks 03M4 for open immersions**, unconditionally.

A morphism of algebraic spaces over `S` is an open immersion exactly when every one of its base
changes to a representable presheaf is, exactly when every one of its base changes to an affine
object of the site is, exactly when its base change along one surjective étale scheme chart of
the target is, and exactly when its base changes along the members of some Zariski covering of
the target are.

This is `AlgebraicGeometry.Space.isOpenImmersion_tfae` with its hypothesis `hdesc` — Stacks 03I2
for open immersions — supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`. -/
@[stacks 03M4 "open immersions"]
theorem isOpenImmersion_tfae_of_isAlgebraicSpace
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE [
      IsOpenImmersion B S hS f,
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsOpenImmersion B S hS (pullback.snd f g)),
      (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsOpenImmersion B S hS (pullback.snd f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ G),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsOpenImmersion B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor G),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsOpenImmersion B S hS (pullback.snd f (U i).ι))
    ] :=
  isOpenImmersion_tfae B S hS
    (isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS) hF hG f

section InvariantOpen

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ F}

/-- **The subspace cut out by an invariant open subscheme of a chart is an open subspace,
unconditionally.** Let `F` be an algebraic space over `S` with a surjective étale chart
`φ : U ⟶ F`, and let `Z ⊆ U` be an open subscheme invariant under the relation `R = U ×_F U`.
Then the subfunctor `AlgebraicGeometry.Space.invariantSubspace B S hS φ Z` of `F` which `Z`
cuts out is an algebraic space over `S` and its inclusion into `F` is an open immersion.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_invariantSubspace` at
`P = AlgebraicGeometry.IsOpenImmersion`, where its descent hypothesis is supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`. It is the
open-subscheme case of the forward direction of Stacks 07TW together with the openness
clause, and unlike
`AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv` it carries no hypothesis: the
general case is Stacks 03I2 at `AlgebraicGeometry.IsImmersion`, which still needs the
effective fppf descent of immersions, Stacks 02W8. -/
@[stacks 07TW "forward direction at an invariant open subscheme, unconditionally"]
theorem isOpenSubspace_invariantSubspace
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hF : IsAlgebraicSpace B S hS F)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : _root_.AlgebraicGeometry.IsOpenImmersion Z.arrow)
    (hinv : IsInvariantSubscheme B S hS hs Z) :
    IsOpenSubspace B S hS (invariantSubspace B S hS φ Z) :=
  have := hZ
  isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS) hF Z
    (inferInstance : _root_.AlgebraicGeometry.IsImmersion Z.arrow) hZ hinv

end InvariantOpen

end Space

end AlgebraicGeometry

end
