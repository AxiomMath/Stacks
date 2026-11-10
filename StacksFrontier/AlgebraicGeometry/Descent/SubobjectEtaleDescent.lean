module

public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace

/-!
# Effective descent of a subobject along a surjective étale chart, from a Cartesian square

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` asks for the
*representability* of `X ×[Y] yoneda.obj a` whenever the base change of `f : X ⟶ Y` along a
surjective étale `q : c ⟶ a` of the big fppf site of `S` is representable with `P`. This file
isolates the part of that statement which is pure sheaf theory, for a property `P` below the
monomorphisms: **once a candidate for the descended object has been produced, together with a
Cartesian square identifying its base change along `q` with the given datum, representability
and the property follow with no further geometric input.**

That reduction is what makes the remaining work in each concrete case purely a construction
problem. For `P = AlgebraicGeometry.IsOpenImmersion` the construction is elementary topology
and is carried out inline in
`StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent`; the present file replays the
sheaf-theoretic half of that argument once, in a form which does not use that an open immersion
is determined by its image.

## Main results

* `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms`: **the
  descent step from a candidate.** Let `(m, r)` present `A` as the base change of `f` along
  `yoneda.map q ≫ h`, with `r` representable with `P` and `P` below the monomorphisms. Suppose
  given an object `b` of the site with `i : b ⟶ a` carrying `P`, morphisms `k : v ⟶ b` and
  `w : v ⟶ c` of the site whose square with `i` and `q` is Cartesian on underlying schemes, and
  an isomorphism `e : A ≅ yoneda.obj v` over `yoneda.obj c`. Then `pullback.snd f h` is
  representable with `P`.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_exists_isPullback`: the
  same statement packaged as a reduction of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` to the production of such a
  candidate.
* `AlgebraicGeometry.Space.exists_comp_eq_snd_of_isPullback_map`: a square of the site which is
  Cartesian on underlying schemes lifts a pair of morphisms of the site to a morphism of the
  site.

## Implementation notes

*Why `P ≤ monomorphisms` is what the argument needs.* Monomorphy enters three times, and each
time it replaces a gluing argument by nothing at all. The datum `r` is a monomorphism, so the
descended projection `pullback.snd f h` is locally injective — that is
`AlgebraicGeometry.Space.isLocallyInjective_pullback_snd`, which is already stated for an
arbitrary monomorphic datum. The candidate inclusion `yoneda.map i` is a monomorphism, so its
range is a *subsheaf* of `yoneda.obj a` — isomorphic to `yoneda.obj b` through
`CategoryTheory.Subfunctor.toRange` — and membership in a subsheaf is local, by
`AlgebraicGeometry.Space.mem_obj_of_surjective_etale`; this is how a section of the descended
fibre product is seen to factor through `i`, where the open-immersion argument instead used the
universal property of an open immersion against a containment of images. Finally monomorphy of
`yoneda.map i` is what makes the comparison morphism `l` unique, so that the identity
`l ≫ yoneda.map i = pullback.snd f h` determines it and the local surjectivity of `l` can be
read off from the Cartesian square.

*What the Cartesian square does.* It is used twice, in opposite directions, and only two of its
four pieces of content are consumed. In the range containment it turns a section of the datum
over a base change of the chart into a morphism to `b`, by composing with `k`; all that is used
there is the commutativity `k ≫ i = w ≫ q`. In the local surjectivity it turns a section of
`yoneda.obj b` into a section of the datum, by lifting against the square; all that is used
there is the existence of a lift over `c`, which is
`AlgebraicGeometry.Space.exists_comp_eq_snd_of_isPullback_map`. Neither the uniqueness of the
lift nor its first triangle is needed — the latter is automatic, since `i` is a monomorphism.
This is strictly less work than the open-immersion argument needs, since there the corresponding
factorization had to be produced from a containment of images and the stability of the open
piece.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A Cartesian square of schemes between objects of the site lifts morphisms of the site.**
Let `k, w, i, q` be morphisms of the big fppf category over `S` whose underlying square of
schemes is Cartesian, and let `α : T ⟶ b`, `β : T ⟶ c` satisfy `α ≫ i = β ≫ q`. Then the lift
of `α` and `β` provided by the square is itself a morphism of the site.

Only the second triangle is recorded: when `i` is a monomorphism the first one follows from it,
and the second is what
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms` consumes. The
lift is put back into the site by `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`: it
commutes with the structure morphisms to `S` because it does so after composition with `w`, whose
own compatibility is `CategoryTheory.Over.w`. -/
theorem exists_comp_eq_snd_of_isPullback_map {b c v a : BigFppfOver B S hS} {k : v ⟶ b}
    {w : v ⟶ c} {i : b ⟶ a} {q : c ⟶ a}
    (csq : IsPullback ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map q))
    {T : BigFppfOver B S hS} (α : T ⟶ b) (β : T ⟶ c) (hαβ : α ≫ i = β ≫ q) :
    ∃ γ : T ⟶ v, γ ≫ w = β := by
  have hcond : (BigFppfOver.toScheme B S hS).map α ≫ (BigFppfOver.toScheme B S hS).map i =
      (BigFppfOver.toScheme B S hS).map β ≫ (BigFppfOver.toScheme B S hS).map q := by
    rw [← Functor.map_comp, ← Functor.map_comp, hαβ]
  set γ₀ := csq.lift ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map β) hcond
  have h2 : γ₀ ≫ (BigFppfOver.toScheme B S hS).map w =
      (BigFppfOver.toScheme B S hS).map β := csq.lift_snd _ _ hcond
  have hcompat : γ₀ ≫ B.inclusion.map v.hom = B.inclusion.map T.hom := by
    have hwv := congrArg B.inclusion.map (Over.w w)
    have hβv := congrArg B.inclusion.map (Over.w β)
    simp only [Functor.map_comp] at hwv hβv
    rw [← hwv, ← Category.assoc]
    change (γ₀ ≫ (BigFppfOver.toScheme B S hS).map w) ≫ _ = _
    rw [h2]
    exact hβv
  obtain ⟨γ, hγ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS γ₀ hcompat
  exact ⟨γ, (BigFppfOver.toScheme B S hS).map_injective
    (by rw [Functor.map_comp, hγ, h2])⟩

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-- The first projection of the pullback of a morphism `s` along the surjective étale `q` is
surjective and étale on underlying schemes. -/
private theorem surjective_and_etale_map_pullback_fst
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) {T : BigFppfOver B S hS} (s : T ⟶ a) :
    Surjective ((BigFppfOver.toScheme B S hS).map (pullback.fst s q)) ∧
      Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst s q)) :=
  have sq := ((IsPullback.of_hasPullback s q).map (BigFppfOver.toScheme B S hS)).flip
  ⟨MorphismProperty.of_isPullback sq hqs, MorphismProperty.of_isPullback sq hqe⟩

/-- Every section of `X ×[Y] yoneda.obj a` factors through `i`, when the base change of `f`
along the surjective étale `q` is identified with `yoneda.obj v` over `yoneda.obj c` and
`k ≫ i = w ≫ q`. -/
private theorem range_pullback_snd_le_range_yoneda_map (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {b v : BigFppfOver B S hS} {i : b ⟶ a} [Mono i] {k : v ⟶ b} {w : v ⟶ c}
    (hcomm : k ≫ i = w ≫ q) (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r) :
    Subfunctor.range (pullback.snd f h) ≤ Subfunctor.range (yoneda.map i) := by
  -- the range of the candidate inclusion is a subsheaf of `yoneda.obj a`
  have hrangesheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Subfunctor.range (yoneda.map i)).toFunctor :=
    (Presheaf.isSheaf_of_iso_iff (asIso (Subfunctor.toRange (yoneda.map i)))).1
      (BigFppfOver.isSheaf_yoneda_obj B S hS b)
  intro T s hs
  obtain ⟨x, rfl⟩ := hs
  set s₀ : T.unop ⟶ a := (pullback.snd f h).app T x with hs₀
  refine mem_obj_of_surjective_etale B S hS (BigFppfOver.isSheaf_yoneda_obj B S hS a)
    (Subfunctor.range (yoneda.map i)) hrangesheaf (pullback.fst s₀ q)
    (surjective_and_etale_map_pullback_fst hqs hqe s₀).1
    (surjective_and_etale_map_pullback_fst hqs hqe s₀).2 s₀ ?_
  have hxs : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s₀ := by
    rw [yonedaEquiv_symm_comp_pullback_snd, hs₀]
  obtain ⟨α, -, hα2⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm x) hxs
    (pullback.fst s₀ q) (pullback.snd s₀ q) pullback.condition
  set β : Limits.pullback s₀ q ⟶ v := yoneda.preimage (α ≫ e.hom)
  have hβmap : yoneda.map β = α ≫ e.hom := Functor.map_preimage _ _
  have hβw : β ≫ w = pullback.snd s₀ q :=
    yoneda.map_injective (by rw [Functor.map_comp, hβmap, Category.assoc, he, hα2])
  refine ⟨β ≫ k, ?_⟩
  change (β ≫ k) ≫ i = pullback.fst s₀ q ≫ s₀
  rw [Category.assoc, hcomm, ← Category.assoc, hβw, ← pullback.condition]

/-- A morphism `l : X ×[Y] yoneda.obj a ⟶ yoneda.obj b` with `l ≫ yoneda.map i = pullback.snd f h`
is locally surjective, when the base change of `f` along `q` is identified with `yoneda.obj v`
and the square of `k, w, i, q` is Cartesian on underlying schemes. -/
private theorem isLocallySurjective_of_comp_eq_pullback_snd (sq : CommSq m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {b v : BigFppfOver B S hS} {i : b ⟶ a} [Mono i] {k : v ⟶ b} {w : v ⟶ c}
    (csq : IsPullback ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map q))
    (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r)
    {l : Limits.pullback f h ⟶ yoneda.obj b} (hlfac : l ≫ yoneda.map i = pullback.snd f h) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) l := by
  -- the inverse of `e` lies over `yoneda.obj c` as well
  have hinv : e.inv ≫ r = yoneda.map w := by rw [← he, Iso.inv_hom_id_assoc]
  constructor
  intro T w₀
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (sieve_generate_singleton_mem_topology_over B S hS (pullback.fst (w₀ ≫ i) q)
      (surjective_and_etale_map_pullback_fst hqs hqe _).1
      (surjective_and_etale_map_pullback_fst hqs hqe _).2)
  rintro Z κ₀ ⟨Z', u, bb, hbb, hfac⟩
  cases hbb
  -- the lift of the chosen section against the Cartesian square
  have hcond : (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀) ≫ i =
      (u ≫ pullback.snd (w₀ ≫ i) q) ≫ q := by
    rw [Category.assoc, Category.assoc, Category.assoc, ← pullback.condition]
  obtain ⟨ζ, hζw⟩ := exists_comp_eq_snd_of_isPullback_map csq
    (u ≫ pullback.fst (w₀ ≫ i) q ≫ w₀) (u ≫ pullback.snd (w₀ ≫ i) q) hcond
  have hζq : ζ ≫ w ≫ q = κ₀ ≫ w₀ ≫ i := by
    rw [← Category.assoc, hζw, Category.assoc, ← pullback.condition, ← Category.assoc,
      hfac]
  have hcond2 : (yoneda.map ζ ≫ e.inv ≫ m) ≫ f = yoneda.map (κ₀ ≫ w₀ ≫ i) ≫ h := by
    rw [Category.assoc, Category.assoc, sq.w, ← Category.assoc (e.inv), hinv,
      ← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
      Category.assoc, hζq]
  set ξ : yoneda.obj Z ⟶ Limits.pullback f h :=
    pullback.lift (yoneda.map ζ ≫ e.inv ≫ m) (yoneda.map (κ₀ ≫ w₀ ≫ i)) hcond2
  have hξsnd : ξ ≫ pullback.snd f h = yoneda.map (κ₀ ≫ w₀ ≫ i) :=
    pullback.lift_snd _ _ hcond2
  have hξl : ξ ≫ l = yoneda.map (κ₀ ≫ w₀) := by
    rw [← cancel_mono (yoneda.map i), Category.assoc, hlfac, hξsnd, ← Functor.map_comp,
      Category.assoc]
  refine ⟨yonedaEquiv ξ, ?_⟩
  rw [← yonedaEquiv_comp, hξl, yonedaEquiv_yoneda_map]
  rfl

/-- **The descent step from a candidate for the descended object.** Let `f : X ⟶ Y` be a
morphism of presheaves on the big fppf site of `S` with `X` and `Y` sheaves, let
`h : yoneda.obj a ⟶ Y`, let `q : c ⟶ a` be surjective étale, and let `(m, r)` present `A` as the
base change of `f` along `yoneda.map q ≫ h`, with `r` representable with a property `P` below the
monomorphisms.

Suppose given a candidate for the descended object: an object `b` of the site with a morphism
`i : b ⟶ a` carrying `P`, morphisms `k : v ⟶ b` and `w : v ⟶ c` of the site whose square with
`i` and `q` is Cartesian *on underlying schemes*, and an isomorphism `e : A ≅ yoneda.obj v`
lying over `yoneda.obj c`, that is with `e.hom ≫ yoneda.map w = r`. Then `pullback.snd f h` is
representable with `P`.

The Cartesian square is asked for on underlying schemes rather than in the site because that is
the form in which a construction produces it, and nothing is lost:
`AlgebraicGeometry.Space.exists_comp_eq_snd_of_isPullback_map` puts the lifts it provides back
into the site.

The comparison morphism `l : X ×[Y] yoneda.obj a ⟶ yoneda.obj b` is locally injective because
the datum is a monomorphism, and locally surjective because the Cartesian square lifts every
section of `yoneda.obj b` over a base change of the chart; both presheaves are sheaves, so `l`
is an isomorphism by `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`. -/
theorem presheaf_pullback_snd_of_isPullback_of_le_monomorphisms
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hPmono : P ≤ MorphismProperty.monomorphisms Scheme.{u})
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {b v : BigFppfOver B S hS} {i : b ⟶ a} {k : v ⟶ b} {w : v ⟶ c}
    (hi : P ((BigFppfOver.toScheme B S hS).map i))
    (csq : IsPullback ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map q))
    (e : A ≅ yoneda.obj v) (he : e.hom ≫ yoneda.map w = r) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have hcomm : k ≫ i = w ≫ q := (BigFppfOver.toScheme B S hS).map_injective
    (by rw [Functor.map_comp, Functor.map_comp, csq.w])
  have hPri : MorphismProperty.RespectsIso P := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRIpre : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  -- the monomorphisms the argument runs on
  have hmonoi : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map (hPmono _ hi)
  -- the comparison morphism, determined by the candidate inclusion; every section of the
  -- descended fibre product factors through the candidate
  obtain ⟨l, hlfac⟩ : ∃ l : Limits.pullback f h ⟶ yoneda.obj b,
      l ≫ yoneda.map i = pullback.snd f h := by
    have h1 : inv (Subfunctor.toRange (yoneda.map i)) ≫ yoneda.map i =
        (Subfunctor.range (yoneda.map i)).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι (yoneda.map i)).symm
    refine ⟨Subfunctor.lift (pullback.snd f h)
      (range_pullback_snd_le_range_yoneda_map sq hqs hqe hcomm e he) ≫
      inv (Subfunctor.toRange (yoneda.map i)), ?_⟩
    rw [Category.assoc, h1, Subfunctor.lift_ι]
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) l :=
    have := isLocallyInjective_pullback_snd sq (mono_of_presheaf hPmono hr) hqs hqe
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac _ hlfac
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) l :=
    isLocallySurjective_of_comp_eq_pullback_snd sq.toCommSq hqs hqe csq e he hlfac
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

/-- **Effective descent along the surjective étale morphisms of the site, reduced to the
production of a descended subobject.** For a property `P` of morphisms of schemes which is
stable under base change and contained in the monomorphisms, effective descent along the
surjective étale morphisms of the big fppf site of `S` follows from producing, for every descent
datum, an object `b` of the site with a morphism `i : b ⟶ a` carrying `P` whose base change
along the chart is the datum — as a square which is Cartesian on underlying schemes, together
with an isomorphism identifying the datum's presheaf with the represented one over
`yoneda.obj c`.

The hypothesis `H` asks for exactly the geometric content of the descent: a candidate for the
descended object and the verification that it restricts to the given one. Everything else is
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms`. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_exists_isPullback
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hPmono : P ≤ MorphismProperty.monomorphisms Scheme.{u})
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∃ (b v : BigFppfOver B S hS) (i : b ⟶ a) (k : v ⟶ b) (w : v ⟶ c)
            (e : A ≅ yoneda.obj v),
            P ((BigFppfOver.toScheme B S hS).map i) ∧
              IsPullback ((BigFppfOver.toScheme B S hS).map k)
                ((BigFppfOver.toScheme B S hS).map w)
                ((BigFppfOver.toScheme B S hS).map i)
                ((BigFppfOver.toScheme B S hS).map q) ∧
              e.hom ≫ yoneda.map w = r) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  obtain ⟨b, v, i, k, w, e, hi, csq, he⟩ := H f hX hY h q hqs hqe m r sq hr
  exact presheaf_pullback_snd_of_isPullback_of_le_monomorphisms hPmono hX hY sq hr hqs hqe
    hi csq e he

end AlgebraicGeometry.Space

end
