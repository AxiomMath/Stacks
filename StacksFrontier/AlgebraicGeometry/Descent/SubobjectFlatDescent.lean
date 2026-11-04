module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.SubobjectEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition

/-!
# Effective descent of a subobject along a surjective flat chart, without Gabber's theorem

`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms` descends a
subobject along a surjective **étale** chart of the big fppf site of `S`. This file proves the
same statement for a chart which is only surjective, flat and quasi-compact, at the cost of
asking the descended fibre product to be an algebraic space.

The point is that it costs *no* fpqc sheaf condition, so it does not need Gabber's Stacks 0APL,
which is what
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc` — the other
flat-chart comparison in this library — consumes.

## Main results

* `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms_of_flat`:
  **the descent step from a monomorphic candidate, along a surjective flat quasi-compact
  chart.**

## Implementation notes

*Where the étale argument uses the chart, and what replaces it here.* The étale proof uses
surjectivity and étaleness of the chart in exactly three places, and each becomes something
else.

The chart's base change is used to see that every section of the descended fibre product
factors through the candidate. There the étale proof appeals to
`AlgebraicGeometry.Space.mem_obj_of_surjective_etale`, locality of membership in a subsheaf for
the *fppf* topology. Here the subsheaf is the range of `yoneda.map i` for a monomorphism `i`,
hence a representable presheaf, and a representable presheaf is an *fpqc* sheaf
unconditionally, by subcanonicity of the fpqc topology
(`AlgebraicGeometry.BigFppfOver.isSheaf_fpqc_yoneda_obj`). That is
`AlgebraicGeometry.Space.exists_comp_eq_of_mono_of_flatCover`.

Local injectivity of the descended projection is replaced by honest injectivity: the two lifts
of two sections to the datum agree because the datum is a monomorphism, so the two sections
agree after the flat base change of the chart, and an algebraic space is *separated* for every
fpqc covering presieve with no hypothesis, by
`AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`. So the descended projection is a
monomorphism outright — `AlgebraicGeometry.Space.mono_pullback_snd_of_isAlgebraicSpace` — and
with it the comparison morphism `l`.

Local surjectivity of `l` is the one place where a genuinely new covering is needed, because
the chart is not an fppf covering and cannot be used. It is supplied by a surjective étale
atlas `u : yoneda.obj U ⟶ X ×[Y] yoneda.obj a` of the descended fibre product, which exists
because that fibre product is an algebraic space. The composite `u ≫ l` is a morphism of
representable presheaves, so it is `yoneda.map u₀` for a morphism `u₀ : U ⟶ b` of the site, and
`u₀` is surjective and étale: its base change along `k : v ⟶ b` — the chart's own base change,
which is surjective, flat and quasi-compact — is the base change of the atlas along the datum,
because `l` is a monomorphism, and `AlgebraicGeometry.Surjective` and `AlgebraicGeometry.Etale`
descend along surjective flat quasi-compact morphisms of schemes. So `u₀` generates an fppf
covering sieve, over which `l` is surjective by construction. That is
`AlgebraicGeometry.Space.exists_surjective_etale_comparison_atlas`.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02L2](https://stacks.math.columbia.edu/tag/02L2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Two general categorical facts -/

/-- **A Cartesian square stays Cartesian after postcomposing both legs of its base with a
monomorphism.** If `l` is a monomorphism then the square over `W` has the same lifts as the
square over `Z`, because the equation a lift has to satisfy may be cancelled against `l`. -/
theorem isPullback_comp_mono {C : Type*} [Category C] {A X Y Z W : C}
    {fst : A ⟶ X} {snd : A ⟶ Y} {g₁ : X ⟶ Z} {g₂ : Y ⟶ Z}
    (sq : IsPullback fst snd g₁ g₂) (l : Z ⟶ W) [Mono l] :
    IsPullback fst snd (g₁ ≫ l) (g₂ ≫ l) := by
  have hw : fst ≫ g₁ ≫ l = snd ≫ g₂ ≫ l := by
    rw [← Category.assoc, ← Category.assoc, sq.w]
  have hcanc : ∀ s : PullbackCone (g₁ ≫ l) (g₂ ≫ l), s.fst ≫ g₁ = s.snd ≫ g₂ := by
    intro s
    refine (cancel_mono l).1 ?_
    simpa only [Category.assoc] using s.condition
  exact ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun s => sq.lift s.fst s.snd (hcanc s))
    (fun s => sq.lift_fst _ _ (hcanc s)) (fun s => sq.lift_snd _ _ (hcanc s))
    (fun s m h₁ h₂ => sq.hom_ext (by rw [h₁, sq.lift_fst]) (by rw [h₂, sq.lift_snd]))⟩⟩

/-! ### A flat quasi-compact chart as an fpqc covering presieve -/

/-- The presieve generated by a single surjective, flat and quasi-compact morphism of the big
fppf category over `S` is an fpqc covering presieve. -/
theorem singleton_mem_fpqcPrecoverage_comap {T' T : BigFppfOver B S hS} (p : T' ⟶ T)
    (hps : Surjective ((BigFppfOver.toScheme B S hS).map p))
    (hpf : Flat ((BigFppfOver.toScheme B S hS).map p))
    (hpc : QuasiCompact ((BigFppfOver.toScheme B S hS).map p)) :
    Presieve.singleton p ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).coverings T := by
  rw [Precoverage.mem_comap_iff, Presieve.map_singleton]
  have := hps
  have := hpf
  have := hpc
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

/-- **Sections of an algebraic space are determined by their restriction along a surjective flat
quasi-compact morphism.** This is the separatedness half of the fpqc sheaf condition, which an
algebraic space satisfies with no hypothesis by
`AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`. -/
theorem eq_of_map_eq_of_flatCover {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {T' T : BigFppfOver B S hS} (p : T' ⟶ T)
    (hps : Surjective ((BigFppfOver.toScheme B S hS).map p))
    (hpf : Flat ((BigFppfOver.toScheme B S hS).map p))
    (hpc : QuasiCompact ((BigFppfOver.toScheme B S hS).map p))
    (x y : F.obj (op T)) (hxy : F.map p.op x = F.map p.op y) : x = y :=
  Presieve.isSeparatedFor_singleton.1 (IsAlgebraicSpace.isSeparatedFor_fpqc hF
    (singleton_mem_fpqcPrecoverage_comap p hps hpf hpc)) hxy

/-! ### The descended projection is a monomorphism -/

/-- A property stable under base change passes to the first projection of the pullback of a
morphism of the site along `s`, once it holds for the other leg. -/
private theorem toScheme_map_pullback_fst {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {T a c : BigFppfOver B S hS} (s : T ⟶ a) (q : c ⟶ a)
    (hq : P ((BigFppfOver.toScheme B S hS).map q)) :
    P ((BigFppfOver.toScheme B S hS).map (pullback.fst s q)) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback s q).map (BigFppfOver.toScheme B S hS)).flip hq

/-- Restricting a section of a presheaf along a morphism of the site, read on the morphism out
of a representable presheaf which the section names. -/
private theorem map_op_eq_yonedaEquiv_symm {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : F.obj T) {Z : BigFppfOver B S hS} (p : Z ⟶ T.unop) :
    F.map p.op x = yonedaEquiv (yoneda.map p ≫ yonedaEquiv.symm x) := by
  rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-- The canonical morphism from a descent datum to the descended fibre product sends a lift of a
section to that section, read over the base change of the chart. -/
private theorem comp_lift_eq (sq : IsPullback m r f (yoneda.map q ≫ h))
    {T T' : BigFppfOver B S hS} {s : T ⟶ a} {p₁ : T' ⟶ T} {p₂ : T' ⟶ c}
    (hp : p₁ ≫ s = p₂ ≫ q) (xt : yoneda.obj T ⟶ Limits.pullback f h)
    (hxs : xt ≫ pullback.snd f h = yoneda.map s) (α : yoneda.obj T' ⟶ A)
    (hα1 : α ≫ m = yoneda.map p₁ ≫ xt ≫ pullback.fst f h) (hα2 : α ≫ r = yoneda.map p₂) :
    α ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]) = yoneda.map p₁ ≫ xt := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, (IsPullback.of_hasPullback f h).lift_fst, hα1, Category.assoc]
  · rw [Category.assoc, (IsPullback.of_hasPullback f h).lift_snd, ← Category.assoc, hα2,
      Category.assoc, hxs, ← Functor.map_comp, ← Functor.map_comp, hp]

/-- **The descended projection of a monomorphic datum is a monomorphism, for a surjective flat
quasi-compact chart.** Let `(m, r)` present `A` as the base change of `f : X ⟶ Y` along
`yoneda.map q ≫ h`, with `r` a monomorphism and `q` surjective, flat and quasi-compact, and
suppose the descended fibre product is an algebraic space. Then `pullback.snd f h` is a
monomorphism.

Two sections over `T` with the same image in `yoneda.obj a` lift to the datum over the base
change `T ×_a c` of the chart, and the two lifts agree because `r` is a monomorphism; so the two
sections agree after restriction along a surjective flat quasi-compact morphism, and an
algebraic space is separated for the fpqc covering presieve that morphism generates. For an
étale chart the corresponding statement is only *local* injectivity,
`AlgebraicGeometry.Space.isLocallyInjective_pullback_snd`; here fpqc separatedness gives
equality on the nose. -/
theorem mono_pullback_snd_of_isAlgebraicSpace (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hrmono : Mono r) (hPb : IsAlgebraicSpace B S hS (Limits.pullback f h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q)) :
    Mono (pullback.snd f h) := by
  have happ : ∀ T, Mono ((pullback.snd f h).app T) := by
    intro T
    rw [mono_iff_injective]
    intro x y hxy
    obtain ⟨s₀, hs₀⟩ : ∃ s : T.unop ⟶ a, (pullback.snd f h).app T x = s := ⟨_, rfl⟩
    have hxs : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s₀ := by
      rw [yonedaEquiv_symm_comp_pullback_snd, hs₀]
    have hys : yonedaEquiv.symm y ≫ pullback.snd f h = yoneda.map s₀ := by
      rw [yonedaEquiv_symm_comp_pullback_snd, ← hxy, hs₀]
    obtain ⟨α, hα1, hα2⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm x) hxs
      (pullback.fst s₀ q) (pullback.snd s₀ q) pullback.condition
    obtain ⟨α', hα1', hα2'⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm y) hys
      (pullback.fst s₀ q) (pullback.snd s₀ q) pullback.condition
    have hαα : α = α' := (cancel_mono r).1 (by rw [hα2, hα2'])
    have key : yoneda.map (pullback.fst s₀ q) ≫ yonedaEquiv.symm x =
        yoneda.map (pullback.fst s₀ q) ≫ yonedaEquiv.symm y := by
      rw [← comp_lift_eq sq pullback.condition _ hxs α hα1 hα2,
        ← comp_lift_eq sq pullback.condition _ hys α' hα1' hα2', hαα]
    have hrestrict : (Limits.pullback f h).map (pullback.fst s₀ q).op x =
        (Limits.pullback f h).map (pullback.fst s₀ q).op y := by
      rw [map_op_eq_yonedaEquiv_symm x (pullback.fst s₀ q),
        map_op_eq_yonedaEquiv_symm y (pullback.fst s₀ q), key]
    exact eq_of_map_eq_of_flatCover hPb (pullback.fst s₀ q)
      (toScheme_map_pullback_fst s₀ q hqs) (toScheme_map_pullback_fst s₀ q hqf)
      (toScheme_map_pullback_fst s₀ q hqc) x y hrestrict
  exact NatTrans.mono_of_mono_app _

/-! ### Factoring through a monomorphism of the site after a flat cover -/

/-- **A morphism of the site which factors through a monomorphism after a surjective flat
quasi-compact base change already factors through it.** This is the flat-chart replacement for
`AlgebraicGeometry.Space.mem_obj_of_surjective_etale`, and it needs no fpqc sheaf condition
beyond that of the *representable* presheaves `yoneda.obj b` and `yoneda.obj a`, which holds
unconditionally because the fpqc topology of the site is subcanonical. -/
theorem exists_comp_eq_of_mono_of_flatCover {b a T T' : BigFppfOver B S hS} {i : b ⟶ a}
    (hmono : Mono i) (p : T' ⟶ T)
    (hps : Surjective ((BigFppfOver.toScheme B S hS).map p))
    (hpf : Flat ((BigFppfOver.toScheme B S hS).map p))
    (hpc : QuasiCompact ((BigFppfOver.toScheme B S hS).map p))
    (s₀ : T ⟶ a) (δ : T' ⟶ b) (hδ : δ ≫ i = p ≫ s₀) :
    ∃ γ : T ⟶ b, γ ≫ i = s₀ := by
  have hgen : Sieve.generate (Presieve.singleton p) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck T :=
    Precoverage.generate_mem_toGrothendieck
      (singleton_mem_fpqcPrecoverage_comap p hps hpf hpc)
  have hbsheaf := (isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS b)
  have hfor : Presieve.IsSheafFor (yoneda.obj b) (Presieve.singleton p) :=
    (Presieve.isSheafFor_iff_generate _).2 (hbsheaf _ hgen)
  have hcompat : ∀ {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ T'), p₁ ≫ p = p₂ ≫ p →
      (yoneda.obj b).map p₁.op δ = (yoneda.obj b).map p₂.op δ := by
    intro Z p₁ p₂ hpp
    show p₁ ≫ δ = p₂ ≫ δ
    refine (cancel_mono i).1 ?_
    rw [Category.assoc, Category.assoc, hδ, ← Category.assoc, ← Category.assoc, hpp]
  obtain ⟨γ, hγ, -⟩ := Presieve.isSheafFor_singleton.1 hfor δ hcompat
  refine ⟨γ, eq_of_map_eq_of_flatCover (isAlgebraicSpace_yoneda B S hS a) p hps hpf hpc
    (γ ≫ i) s₀ ?_⟩
  show p ≫ γ ≫ i = p ≫ s₀
  rw [← Category.assoc, show p ≫ γ = δ from hγ, hδ]

/-! ### A surjective étale chart of the descended fibre product -/

/-- **The comparison morphism admits a surjective étale chart from the site.** Let `l` be a
morphism from the descended fibre product to `yoneda.obj b` over `yoneda.obj a`, and suppose it
is a monomorphism and sends the datum to the candidate. Then a surjective étale atlas
`u : yoneda.obj U ⟶ X ×[Y] yoneda.obj a` of the descended fibre product — which exists because
that fibre product is an algebraic space — composes with `l` to `yoneda.map u₀` for a morphism
`u₀ : U ⟶ b` of the site which is itself surjective and étale.

The reason is that the base change of `u₀` along `k : v ⟶ b` *is* the base change of the atlas
along the datum: a section of `U ×_b v` is a pair agreeing in `yoneda.obj b`, hence, `l` being a
monomorphism, agreeing in the fibre product. The chart's own base change `k` is surjective, flat
and quasi-compact, and both `AlgebraicGeometry.Surjective` and `AlgebraicGeometry.Etale` descend
along such morphisms, so the properties pass from the base change to `u₀`. -/
theorem exists_surjective_etale_comparison_atlas
    (hPb : IsAlgebraicSpace B S hS (Limits.pullback f h))
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    {b v : BigFppfOver B S hS} {i : b ⟶ a} {k : v ⟶ b} {w : v ⟶ c}
    (csq : IsPullback ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map q))
    (e : A ≅ yoneda.obj v)
    (l : Limits.pullback f h ⟶ yoneda.obj b) (hlmono : Mono l)
    (hlκ : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ l = e.hom ≫ yoneda.map k) :
    ∃ (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ Limits.pullback f h) (u₀ : U ⟶ b),
      Surjective ((BigFppfOver.toScheme B S hS).map u₀) ∧
      Etale ((BigFppfOver.toScheme B S hS).map u₀) ∧ u ≫ l = yoneda.map u₀ := by
  obtain ⟨U, u, husurj, huetale⟩ := hPb.exists_atlas
  refine ⟨U, u, yoneda.preimage (u ≫ l), ?_, ?_, (Functor.map_preimage _ _).symm⟩ <;>
  · obtain ⟨U', snd₀, fst₀, hpb₀⟩ := husurj.1 (e.inv ≫ (IsPullback.of_hasPullback f h).lift m
      (r ≫ yoneda.map q) (by rw [sq.w, Category.assoc]))
    have hvk : (e.inv ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc])) ≫ l = yoneda.map k := by
      rw [Category.assoc, hlκ, Iso.inv_hom_id_assoc]
    have hpb₂ : IsPullback (yoneda.map (yoneda.preimage fst₀)) (yoneda.map snd₀)
        (yoneda.map (yoneda.preimage (u ≫ l))) (yoneda.map k) := by
      rw [Functor.map_preimage, Functor.map_preimage, ← hvk]
      exact isPullback_comp_mono hpb₀ l
    have hpb₃ : IsPullback (yoneda.preimage fst₀) snd₀ (yoneda.preimage (u ≫ l)) k :=
      IsPullback.of_map yoneda (yoneda.map_injective (by
        simpa only [Functor.map_comp] using hpb₂.w)) hpb₂
    have hpb₄ := hpb₃.map (BigFppfOver.toScheme B S hS)
    have hkQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        ((BigFppfOver.toScheme B S hS).map k) :=
      ⟨⟨MorphismProperty.of_isPullback csq.flip hqs, MorphismProperty.of_isPullback csq.flip hqf⟩,
        MorphismProperty.of_isPullback csq.flip hqc⟩
    first
    | exact MorphismProperty.of_isPullback_of_descendsAlong hpb₄.flip hkQ
        (husurj.2 _ fst₀ snd₀ hpb₀)
    | exact MorphismProperty.of_isPullback_of_descendsAlong hpb₄.flip hkQ
        (huetale.2 _ fst₀ snd₀ hpb₀)

/-! ### The descent step along a surjective flat quasi-compact chart -/

/-- **Every section of the descended fibre product factors through the candidate**, for a
surjective flat quasi-compact chart and a monomorphic candidate `i`. -/
theorem range_pullback_snd_le_range_yoneda_map (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    {b v : BigFppfOver B S hS} {i : b ⟶ a} {k : v ⟶ b} {w : v ⟶ c}
    (hmonoi : Mono i) (hcomm : k ≫ i = w ≫ q) (e : A ≅ yoneda.obj v)
    (he : e.hom ≫ yoneda.map w = r) :
    Subfunctor.range (pullback.snd f h) ≤ Subfunctor.range (yoneda.map i) := by
  intro T s hs
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨s₀, hs₀⟩ : ∃ s : T.unop ⟶ a, (pullback.snd f h).app T x = s := ⟨_, rfl⟩
  have hxs : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s₀ := by
    rw [yonedaEquiv_symm_comp_pullback_snd, hs₀]
  obtain ⟨α, -, hα2⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm x) hxs
    (pullback.fst s₀ q) (pullback.snd s₀ q) pullback.condition
  have hβw : yoneda.preimage (α ≫ e.hom) ≫ w = pullback.snd s₀ q := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage, Category.assoc, he, hα2]
  have hδ : (yoneda.preimage (α ≫ e.hom) ≫ k) ≫ i = pullback.fst s₀ q ≫ s₀ := by
    rw [Category.assoc, hcomm, ← Category.assoc, hβw, ← pullback.condition]
  obtain ⟨γ, hγ⟩ := exists_comp_eq_of_mono_of_flatCover hmonoi (pullback.fst s₀ q)
    (toScheme_map_pullback_fst s₀ q hqs) (toScheme_map_pullback_fst s₀ q hqf)
    (toScheme_map_pullback_fst s₀ q hqc) s₀ _ hδ
  exact ⟨γ, hγ.trans hs₀.symm⟩

/-- A morphism to a representable presheaf is locally surjective as soon as it receives a
morphism from a representable presheaf which it sends to a surjective étale morphism of the site.
-/
theorem isLocallySurjective_of_comp_eq_yoneda_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {b U : BigFppfOver B S hS} (l : F ⟶ yoneda.obj b) (u : yoneda.obj U ⟶ F) (u₀ : U ⟶ b)
    (hu₀s : Surjective ((BigFppfOver.toScheme B S hS).map u₀))
    (hu₀e : Etale ((BigFppfOver.toScheme B S hS).map u₀)) (hu₀ : u ≫ l = yoneda.map u₀) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) l := by
  constructor
  intro T w₀
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (sieve_generate_singleton_mem_topology_over B S hS (pullback.fst w₀ u₀)
      (toScheme_map_pullback_fst w₀ u₀ hu₀s) (toScheme_map_pullback_fst w₀ u₀ hu₀e))
  rintro Z κ₀ ⟨Z', z, bb, hbb, hfac⟩
  cases hbb
  refine ⟨yonedaEquiv (yoneda.map (z ≫ pullback.snd w₀ u₀) ≫ u), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, hu₀, ← Functor.map_comp, Category.assoc,
    ← pullback.condition, ← Category.assoc, hfac, yonedaEquiv_yoneda_map]
  rfl

/-- **The descent step from a monomorphic candidate, along a surjective flat quasi-compact
chart.** Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` and
`Y` sheaves, let `h : yoneda.obj a ⟶ Y` with `X ×[Y] yoneda.obj a` an algebraic space over `S`,
let `q : c ⟶ a` be surjective, flat and quasi-compact, and let `(m, r)` present `A` as the base
change of `f` along `yoneda.map q ≫ h`, with `r` representable with a property `P` below the
monomorphisms. Suppose given a candidate for the descended object: an object `b` of the site
with `i : b ⟶ a` carrying `P`, morphisms `k : v ⟶ b` and `w : v ⟶ c` whose square with `i` and
`q` is Cartesian on underlying schemes, and an isomorphism `e : A ≅ yoneda.obj v` over
`yoneda.obj c`. Then `pullback.snd f h` is representable with `P`.

This is `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms` with
the chart's étaleness traded for flatness and quasi-compactness, plus the hypothesis that the
descended fibre product is an algebraic space. In exchange it asks for **no fpqc sheaf
condition**, so unlike
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc` it does not
depend on Stacks 0APL. -/
theorem presheaf_pullback_snd_of_isPullback_of_le_monomorphisms_of_flat
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hPmono : P ≤ MorphismProperty.monomorphisms Scheme.{u})
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hPb : IsAlgebraicSpace B S hS (Limits.pullback f h))
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    {b v : BigFppfOver B S hS} {i : b ⟶ a} {k : v ⟶ b} {w : v ⟶ c}
    (hi : P ((BigFppfOver.toScheme B S hS).map i))
    (csq : IsPullback ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map q))
    (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have hcomm : k ≫ i = w ≫ q := (BigFppfOver.toScheme B S hS).map_injective
    (by simpa only [Functor.map_comp] using csq.w)
  have hRIpre : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have hmonoi : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map (hPmono _ hi)
  have hmonoyi : Mono (yoneda.map i) := inferInstance
  have hrmono : Mono r := mono_of_presheaf hPmono hr
  have hsndmono : Mono (pullback.snd f h) :=
    mono_pullback_snd_of_isAlgebraicSpace sq hrmono hPb hqs hqf hqc
  have hlr := range_pullback_snd_le_range_yoneda_map sq hqs hqf hqc hmonoi hcomm e he
  obtain ⟨l, hlfac⟩ : ∃ l : Limits.pullback f h ⟶ yoneda.obj b,
      l ≫ yoneda.map i = pullback.snd f h := by
    have h1 : inv (Subfunctor.toRange (yoneda.map i)) ≫ yoneda.map i =
        (Subfunctor.range (yoneda.map i)).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι (yoneda.map i)).symm
    refine ⟨Subfunctor.lift (pullback.snd f h) hlr ≫
      inv (Subfunctor.toRange (yoneda.map i)), ?_⟩
    rw [Category.assoc, h1, Subfunctor.lift_ι]
  have hlmono : Mono l := mono_of_mono_fac hlfac
  have hlκ : (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc]) ≫ l = e.hom ≫ yoneda.map k := by
    refine (cancel_mono (yoneda.map i)).1 ?_
    rw [Category.assoc, hlfac, (IsPullback.of_hasPullback f h).lift_snd, Category.assoc,
      ← Functor.map_comp, hcomm, ← he, Functor.map_comp, Category.assoc]
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) l :=
    Presheaf.isLocallyInjective_of_injective _ l
      (fun T => (mono_iff_injective (l.app T)).1 inferInstance)
  obtain ⟨U, u, u₀, hu₀s, hu₀e, hu₀⟩ := exists_surjective_etale_comparison_atlas hPb sq
    hqs hqf hqc csq e l hlmono hlκ
  have hls := isLocallySurjective_of_comp_eq_yoneda_map l u u₀ hu₀s hu₀e hu₀
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (Limits.pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hbsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj b) :=
    BigFppfOver.isSheaf_yoneda_obj B S hS b
  have hliso : IsIso l := by
    have hsh : IsIso ((⟨l⟩ :
        (⟨Limits.pullback f h, hFsheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨yoneda.obj b, hbsheaf⟩)) :=
      (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hli, hls⟩
    exact inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map
      ((⟨l⟩ : (⟨Limits.pullback f h, hFsheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨yoneda.obj b, hbsheaf⟩))))
  rw [← hlfac]
  exact MorphismProperty.RespectsIso.precomp _ l _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P i).2 hi)

end AlgebraicGeometry.Space

end
