module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials

/-!
# The crystalline differentials of an affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `(U, T, δ)` of the big
crystalline category `CRIS(X/S)` whose ambient scheme `T` is affine and whose structure morphism
`T ⟶ S` factors through an affine open `V ⊆ S`.  The sections of the presheaf of crystalline
differentials `Ω_{X/S}` over that object are then the ring-theoretic module of divided power
differentials `Ω¹_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}`, compatibly with the universal derivations.

By construction the sections of `Ω_{X/S}` over `(U, T, δ)` are the divided power differentials of
`Γ(T, 𝒪_T)` relative to `Γ(S, 𝒪_S)` modulo the differentials of every section pulled back from
*some* open of `S` receiving `T`.  Dividing out only the sections pulled back from the single open
`V` already produces the differentials relative to `Γ(V, 𝒪_S)`, so the comparison amounts to
showing that the remaining base sections have vanishing differential there.  That is where
affineness enters: a section pulled back from another open `V'` of `S` becomes, over a basic open
of `V` contained in `V'`, a fraction whose numerator and denominator are pulled back from `V`, so
a power of the denominator annihilates its differential; and those denominators generate the unit
ideal of `Γ(T, 𝒪_T)` because `T` is affine and maps into `V'`.

Nothing in that argument is special to the global sections of an affine scheme, nor to an object
of `CRIS(X/S)`: it runs over any affine open `W` of the ambient scheme of a divided power scheme
`T` mapping to a scheme `Y`, and gives the sections of the presheaf of divided power differentials
of [Stacks, Tag 07IY] over `W` as `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}`.  That form,
`Crystalline.affineDpIso`, is proved here as well, and the statement about an affine object of
`CRIS(X/S)` is its case `W = ⊤`.

## Main definitions

* `Crystalline.affineBaseGenerators` — the sections of an affine open `V` of the base whose basic
  opens lie in a given open `V'`, pulled back to the sections over an open of a scheme over `V`.
* `Crystalline.affineDpObj` — the module `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}` of divided power
  differentials of the sections over an open `W` relative to an open `V` of the base receiving it.
* `Crystalline.affineDpHom` and `Crystalline.affineDpInv` — the two comparison maps between it and
  the sections of the presheaf of divided power differentials over `W`.
* `Crystalline.GlobalCrystallineSituation.affineBaseAppLE` — the map `Γ(V, 𝒪_S) ⟶ Γ(T, 𝒪_T)` on
  sections given by a factorization of the structure morphism of `(U, T, δ)` through `V`.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsObj` — the module
  `Ω¹_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}` of divided power differentials relative to `V`.
* `Crystalline.GlobalCrystallineSituation.affineCrysDerivation` and `crysAffineDerivation` — the
  two universal differentials, each read as a derivation relative to the base ring of the other.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsHom` and
  `affineCrysDifferentialsInv` — the two comparison maps.

## Main results

* `Crystalline.span_affineBaseGenerators_eq_top` — those pulled back sections generate the unit
  ideal.
* `Crystalline.exists_pow_smul_d_eq_zero` — a power of one of them annihilates the differential of
  any global section pulled back from `V'`.
* `Crystalline.d_appLE_eq_zero` — on an affine open `W` mapping into an affine open `V` of the
  base, a derivation of the sections over `W` killing everything pulled back from `V` kills every
  section pulled back from an arbitrary open of the base.
* `Crystalline.affineDpIso` — **the identification of [Stacks, Tag 07J0] at an affine open**: for
  an affine open `W` of a divided power scheme `T` lying over an affine open `V` of a scheme `Y`,
  the sections of the presheaf of divided power differentials of `T` over `Y` on `W` are
  `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}`, compatibly with the universal differentials
  (`Crystalline.affineDpIso_hom_d`, `Crystalline.affineDpIso_inv_dpd`).
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso` — **Stacks, Tag 07J0**: for
  an affine object `(U, T, δ)` of `CRIS(X/S)` mapping into an affine open `V ⊆ S` the sections of
  `Ω_{X/S}` over `(U, T, δ)` are `Ω¹_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}`.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso_hom_d` and
  `affineCrysDifferentialsIso_inv_dpd` — the identification carries `d_{X/S}` to
  `d_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}` and back, which is what makes it canonical.
* `Crystalline.GlobalCrystallineSituation.existsUnique_affineCrysDifferentialsIso` — **the
  equality sign of [Stacks, Tag 07J0]**: that identification is the *only* isomorphism of the two
  modules carrying `d_{X/S}` to `d_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}`.

## Implementation notes

The source states the lemma for the small crystalline site `Cris(X/S)`; it is proved here for the
big crystalline category `CRIS(X/S)`, of which the small site is a full subcategory, so the small
site statement is the restriction of this one along that inclusion.  Being an object of the small
site is not used anywhere in the argument.  That restriction costs nothing to read off:
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentials_obj` of
`DeRhamComplex.lean` says the sections of the small-site `Ω_{X/S}` over an object of
`Cris(X/S)` are the sections of the big-site `Ω_{X/S}` over the same object of `CRIS(X/S)`, by
`rfl`, so `affineCrysDifferentialsIso` at that object is the small site statement.

The hypothesis that the ambient scheme is affine is used only through the quasi-compactness of its
underlying space and the fact that the sections over a basic open are the corresponding
localization of the global sections; the hypothesis that `V` is affine is used only to produce
enough basic opens of `V` inside a given open of the base.

## References

* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### Derivations of an affine scheme relative to an affine open of the base -/

section AffineBase

variable {T Y : Scheme.{u}} (g : T ⟶ Y) {V : Y.Opens} {W : T.Opens}

/-- The sections of `𝒪_Y` over an open `V` whose basic open is contained in a given open `V'`,
pulled back to the sections over an open `W` of a scheme lying over `V`. -/
def affineBaseGenerators (hgV : W ≤ g ⁻¹ᵁ V) (V' : Y.Opens) : Set Γ(T, W) :=
  (fun r ↦ g.appLE V W hgV r) '' {r : Γ(Y, V) | Y.basicOpen r ≤ V'}

/-- **The pulled back sections of an affine open `V` of the base whose basic opens lie in `V'`
generate the unit ideal** of the sections over an affine open `W` lying over both: the image of
each point of `W` lies in `V` and in `V'`, hence in a basic open of `V` contained in `V'`. -/
theorem span_affineBaseGenerators_eq_top (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hgV : W ≤ g ⁻¹ᵁ V) {V' : Y.Opens} (hgV' : W ≤ g ⁻¹ᵁ V') :
    Ideal.span (affineBaseGenerators g hgV V') = ⊤ := by
  rw [← hW.self_le_iSup_basicOpen_iff]
  intro x hx
  have hxV : g.base x ∈ V := hgV hx
  have hxV' : g.base x ∈ V' := hgV' hx
  obtain ⟨r, hrV', hxr⟩ := hV.exists_basicOpen_le (⟨g.base x, hxV'⟩ : V') hxV
  refine Opens.mem_iSup.mpr ⟨⟨g.appLE V W hgV r, ⟨r, hrV', rfl⟩⟩, ?_⟩
  rw [Scheme.basicOpen_appLE]
  exact ⟨hx, hxr⟩

/-- Restricting a section pulled back from an open of the base to a basic open of the source is
the same as pulling back its restriction to the corresponding basic open of the base. -/
theorem appLE_basicOpen_map (hgV : W ≤ g ⁻¹ᵁ V) {r : Γ(Y, V)} {V' : Y.Opens}
    (hV' : Y.basicOpen r ≤ V') (hgV' : W ≤ g ⁻¹ᵁ V')
    (he : T.basicOpen (g.appLE V W hgV r) ≤ g ⁻¹ᵁ Y.basicOpen r) (x : Γ(Y, V')) :
    g.appLE (Y.basicOpen r) (T.basicOpen (g.appLE V W hgV r)) he
        (Y.presheaf.map (homOfLE hV').op x) =
      T.presheaf.map (homOfLE (T.basicOpen_le (g.appLE V W hgV r))).op
        (g.appLE V' W hgV' x) := by
  simp only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- **A power of a pulled back section of an affine open `V` of the base whose basic open lies in
`V'` annihilates the differential of any global section pulled back from `V'`.**  Over that basic
open the section is a fraction whose numerator and denominator come from `V`; clearing
denominators turns the resulting equality into one of global sections, where the derivation kills
everything pulled back from `V`. -/
theorem exists_pow_smul_d_eq_zero (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hgV : W ≤ g ⁻¹ᵁ V)
    {M : ModuleCat.{u} Γ(T, W)} (d : Γ(T, W) → M)
    (hmul : ∀ b b' : Γ(T, W), d (b * b') = b • d b' + b' • d b)
    (hbase : ∀ x : Γ(Y, V), d (g.appLE V W hgV x) = 0)
    {V' : Y.Opens} (hgV' : W ≤ g ⁻¹ᵁ V') (a : Γ(Y, V'))
    {r : Γ(Y, V)} (hrV' : Y.basicOpen r ≤ V') :
    ∃ n : ℕ, (g.appLE V W hgV r) ^ n • d (g.appLE V' W hgV' a) = 0 := by
  have he : T.basicOpen (g.appLE V W hgV r) ≤ g ⁻¹ᵁ Y.basicOpen r :=
    (Scheme.basicOpen_appLE g W V hgV r).le.trans inf_le_right
  have := hV.isLocalization_basicOpen r
  have := hW.isLocalization_basicOpen (g.appLE V W hgV r)
  obtain ⟨⟨c, dd⟩, hcd⟩ := IsLocalization.surj (Submonoid.powers r)
    (Y.presheaf.map (homOfLE hrV').op a)
  obtain ⟨n, hn⟩ := dd.2
  -- The fraction relation, pulled back to the basic open of the source.
  have hcd' : Y.presheaf.map (homOfLE hrV').op a *
        Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op (r ^ n) =
      Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op c := by
    rw [show r ^ n = (dd : Γ(Y, V)) from hn]
    exact hcd
  have hfrac := congrArg
    (fun z ↦ g.appLE (Y.basicOpen r) (T.basicOpen (g.appLE V W hgV r)) he z) hcd'
  rw [map_mul, appLE_basicOpen_map g hgV hrV' hgV' he a,
    appLE_basicOpen_map g hgV (Y.basicOpen_le r) hgV he (r ^ n),
    appLE_basicOpen_map g hgV (Y.basicOpen_le r) hgV he c] at hfrac
  -- Hence a power of the denominator kills the difference of the sections over `W`.
  have hzero : algebraMap Γ(T, W) Γ(T, T.basicOpen (g.appLE V W hgV r))
      (g.appLE V' W hgV' a * g.appLE V W hgV r ^ n - g.appLE V W hgV c) = 0 := by
    rw [map_sub, map_mul, map_pow, sub_eq_zero]
    simpa only [RingHom.algebraMap_toAlgebra, map_pow] using hfrac
  obtain ⟨mm, hmm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (g.appLE V W hgV r))
    Γ(T, T.basicOpen (g.appLE V W hgV r)) _).mp hzero
  obtain ⟨m, hm⟩ := mm.2
  rw [← hm, mul_sub, sub_eq_zero] at hmm
  -- Apply the derivation: both sides are pulled back from `V` up to the factor `a`.
  refine ⟨m + n, ?_⟩
  have hprod : g.appLE V W hgV r ^ m * (g.appLE V' W hgV' a * g.appLE V W hgV r ^ n) =
      g.appLE V W hgV (r ^ (m + n)) * g.appLE V' W hgV' a := by
    rw [map_pow, pow_add]
    ring
  have hd1 : d (g.appLE V W hgV (r ^ (m + n)) * g.appLE V' W hgV' a) =
      g.appLE V W hgV r ^ (m + n) • d (g.appLE V' W hgV' a) := by
    rw [hmul, hbase, smul_zero, add_zero, map_pow]
  have hd2 : d (g.appLE V W hgV r ^ m * g.appLE V W hgV c) = 0 := by
    have hc : g.appLE V W hgV r ^ m * g.appLE V W hgV c = g.appLE V W hgV (r ^ m * c) := by
      rw [map_mul, map_pow]
    rw [hc, hbase]
  rw [← hd1, ← hprod, hmm, hd2]

/-- **A derivation of the sections over an affine open relative to an affine open `V` of
the base kills every section pulled back from an arbitrary open of the base.**  A power of
each of the pulled back sections of `V` cutting out a basic open inside that open annihilates the
differential, and those sections generate the unit ideal. -/
theorem d_appLE_eq_zero (hW : IsAffineOpen W) (hV : IsAffineOpen V) (hgV : W ≤ g ⁻¹ᵁ V)
    {M : ModuleCat.{u} Γ(T, W)} (d : Γ(T, W) → M)
    (hmul : ∀ b b' : Γ(T, W), d (b * b') = b • d b' + b' • d b)
    (hbase : ∀ x : Γ(Y, V), d (g.appLE V W hgV x) = 0)
    {V' : Y.Opens} (hgV' : W ≤ g ⁻¹ᵁ V') (a : Γ(Y, V')) :
    d (g.appLE V' W hgV' a) = 0 := by
  have key : ∀ t : affineBaseGenerators g hgV V',
      ∃ n : ℕ, ((t : Γ(T, W)) ^ n) • d (g.appLE V' W hgV' a) ∈
        (⊥ : Submodule Γ(T, W) M) := by
    rintro ⟨x, r, hrV', rfl⟩
    obtain ⟨n, hn⟩ := exists_pow_smul_d_eq_zero g hW hV hgV d hmul hbase hgV' a hrV'
    exact ⟨n, (Submodule.mem_bot _).mpr hn⟩
  simpa using Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule Γ(T, W) M) _
    (span_affineBaseGenerators_eq_top g hW hV hgV hgV') (d (g.appLE V' W hgV' a)) key

end AffineBase

/-! ### The divided power differentials of a divided power scheme over an affine open -/

section AffineOpen

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  {W : T.scheme.Opens} {V : Y.Opens} (h : W ≤ f ⁻¹ᵁ V)

/-- **The module `Ω¹_{Γ(W, 𝒪_T)/Γ(V, 𝒪_Y), δ}`** of divided power differentials of the sections of
a divided power scheme over an open `W`, relative to the sections of the base over an open `V`
through which `W` maps. -/
abbrev affineDpObj : ModuleCat.{u} Γ(T.scheme, W) :=
  dpDifferentials (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))

/-- The map on sections over `W` from the global sections of the base is the restriction to an
open `V` through which `W` maps, followed by the map on sections over `V`. -/
theorem baseAppLE_eq :
    Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ f.appLE V W h = baseAppLE T Y f W :=
  Scheme.Hom.map_appLE f h (homOfLE (le_top : V ≤ ⊤)).op

/-- `Crystalline.baseAppLE_eq` on sections. -/
theorem baseAppLE_apply (a : Γ(Y, ⊤)) :
    baseAppLE T Y f W a =
      f.appLE V W h (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a) :=
  (congrArg (fun φ : Γ(Y, ⊤) ⟶ Γ(T.scheme, W) ↦ φ a) (baseAppLE_eq T Y f h)).symm.trans
    (CommRingCat.comp_apply _ _ a)

/-- **The universal divided power differential relative to `Γ(V, 𝒪_Y)`, read as a derivation
relative to the global sections of the base.**  It kills the latter because they restrict to
sections over `V`. -/
def affineDpDerivation : (affineDpObj T Y f h).Derivation (baseAppLE T Y f W) :=
  ModuleCat.Derivation.mk
    (fun b ↦ dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b)
    (fun b b' ↦ dpd_add (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b b')
    (fun b b' ↦ dpd_mul (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b b')
    (fun a ↦ (congrArg
          (fun z ↦ dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) z)
          (baseAppLE_apply T Y f h a)).trans
      (dpd_map (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) _))

/-- The derivation `Crystalline.affineDpDerivation` sends a section to its universal divided power
differential relative to `Γ(V, 𝒪_Y)`. -/
@[simp]
theorem affineDpDerivation_d (b : Γ(T.scheme, W)) :
    (affineDpDerivation T Y f h).d b =
      dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b := rfl

/-- **The universal differential of the presheaf of divided power differentials over an open `W`,
read as a derivation relative to the sections of the base over an open `V` through which `W`
maps.**  It kills those sections because they are pulled back from the base. -/
def dpConstAffineDerivation :
    ((dpDifferentialsPresheaf T Y f).obj (op W)).Derivation (f.appLE V W h) :=
  ModuleCat.Derivation.mk (fun b ↦ (presheafD T Y f W).d b)
    (fun b b' ↦ ModuleCat.Derivation.d_add (presheafD T Y f W) b b')
    (fun b b' ↦ ModuleCat.Derivation.d_mul (presheafD T Y f W) b b')
    (fun a ↦ dpConstD_base (baseAppLE T Y f W) (T.dividedPowers.dividedPowers (op W))
      (appLE_mem_baseSections T Y f W V h a))

/-- The derivation `Crystalline.dpConstAffineDerivation` sends a section to its universal
differential in the presheaf of divided power differentials. -/
@[simp]
theorem dpConstAffineDerivation_d (b : Γ(T.scheme, W)) :
    (dpConstAffineDerivation T Y f h).d b = (presheafD T Y f W).d b := rfl

/-- **The comparison map from the divided power differentials relative to an open of the base to
the sections of the presheaf of divided power differentials over `W`.**  The universal
differential of the presheaf kills the sections over that open, so it descends. -/
def affineDpInv : affineDpObj T Y f h ⟶ (dpDifferentialsPresheaf T Y f).obj (op W) :=
  dpDesc (dpConstAffineDerivation T Y f h)
    (fun n x hx ↦ dpConstD_dpow (baseAppLE T Y f W) (T.dividedPowers.dividedPowers (op W))
      (baseSections T Y f W) n x hx)

/-- The comparison map `Crystalline.affineDpInv` sends the universal divided power differential of
a section relative to `Γ(V, 𝒪_Y)` to its universal differential in the presheaf. -/
@[simp]
theorem affineDpInv_dpd (b : Γ(T.scheme, W)) :
    (affineDpInv T Y f h).hom
        (dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b) =
      (presheafD T Y f W).d b :=
  dpDesc_d (dpConstAffineDerivation T Y f h) _ b

variable (hW : IsAffineOpen W) (hV : IsAffineOpen V)

/-- **The comparison map from the sections of the presheaf of divided power differentials over an
affine open to the divided power differentials relative to an affine open of the base.**  The
universal differential relative to `V` kills every section pulled back from the base, so it
descends. -/
def affineDpHom : (dpDifferentialsPresheaf T Y f).obj (op W) ⟶ affineDpObj T Y f h :=
  dpConstDesc (affineDpDerivation T Y f h)
    (fun n x hx ↦ dpd_dpow (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) n x hx)
    (fun _ hs ↦ by
      obtain ⟨V', h', a, rfl⟩ := hs
      exact d_appLE_eq_zero f hW hV h
        (fun b ↦ dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b)
        (fun b b' ↦ dpd_mul (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b b')
        (fun x ↦ dpd_map (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) x) h' a)

/-- The comparison map `Crystalline.affineDpHom` sends the universal differential of a section in
the presheaf to its universal divided power differential relative to `Γ(V, 𝒪_Y)`. -/
@[simp]
theorem affineDpHom_d (b : Γ(T.scheme, W)) :
    (affineDpHom T Y f h hW hV).hom ((presheafD T Y f W).d b) =
      dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b :=
  dpConstDesc_d (affineDpDerivation T Y f h) _ _ b

/-- **The sections of the presheaf of divided power differentials over an affine open `W` lying
over an affine open `V` of the base are `Ω¹_{Γ(W, 𝒪_T)/Γ(V, 𝒪_Y), δ}`.**  This is the
[Stacks, Tag 07J0] identification, read on a divided power scheme over a scheme and over an
arbitrary affine open rather than on an affine object of `CRIS(X/S)`;
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso` is its case `W = ⊤`.

Both sides receive a universal divided power differential, and each descends along the other's
universal property: the differential relative to `Γ(V, 𝒪_Y)` kills every section pulled back from
*any* open of the base by `Crystalline.d_appLE_eq_zero`, and the differential of the presheaf
kills the sections pulled back from `V` because those are among the ones divided out. -/
def affineDpIso : (dpDifferentialsPresheaf T Y f).obj (op W) ≅ affineDpObj T Y f h where
  hom := affineDpHom T Y f h hW hV
  inv := affineDpInv T Y f h
  hom_inv_id := dpConstDifferentials_ext fun b ↦
    (congrArg (fun z ↦ (affineDpInv T Y f h).hom z)
      (affineDpHom_d T Y f h hW hV b)).trans (affineDpInv_dpd T Y f h b)
  inv_hom_id := dpDifferentials_ext fun b ↦
    (congrArg (fun z ↦ (affineDpHom T Y f h hW hV).hom z)
      (affineDpInv_dpd T Y f h b)).trans (affineDpHom_d T Y f h hW hV b)

/-- The identification carries the universal differential of the presheaf to the universal
divided power differential relative to `Γ(V, 𝒪_Y)`. -/
@[simp]
theorem affineDpIso_hom_d (b : Γ(T.scheme, W)) :
    (affineDpIso T Y f h hW hV).hom.hom ((presheafD T Y f W).d b) =
      dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b :=
  affineDpHom_d T Y f h hW hV b

/-- The identification carries the universal divided power differential relative to `Γ(V, 𝒪_Y)`
to the universal differential of the presheaf. -/
@[simp]
theorem affineDpIso_inv_dpd (b : Γ(T.scheme, W)) :
    (affineDpIso T Y f h hW hV).inv.hom
        (dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b) =
      (presheafD T Y f W).d b :=
  affineDpInv_dpd T Y f h b

end AffineOpen

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (A : Thickening S) {V : S.S.scheme.Opens}
  (hVA : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V)

/-- The map `Γ(V, 𝒪_S) ⟶ Γ(T, 𝒪_T)` on sections given by a factorization of the structure
morphism of an object `(U, T, δ)` of `CRIS(X/S)` through an open `V` of the divided power base. -/
abbrev affineBaseAppLE : Γ(S.S.scheme, V) ⟶ Γ(A.thickening.target.scheme, ⊤) :=
  A.toBase.hom.appLE V ⊤ hVA

/-- **The module `Ω¹_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}`** of divided power differentials of the global
sections of the ambient scheme of an object of `CRIS(X/S)`, relative to the sections of the
divided power base over an open through which the structure morphism factors. -/
abbrev affineCrysDifferentialsObj : ModuleCat.{u} Γ(A.thickening.target.scheme, ⊤) :=
  dpDifferentials (affineBaseAppLE S A hVA) (crysDividedPowers S A)

/-- The map on global sections of the structure morphism of an object of `CRIS(X/S)` is the
restriction to an open through which it factors, followed by the map on sections over it. -/
theorem crysBaseAppLE_eq :
    S.S.scheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ affineBaseAppLE S A hVA =
      crysBaseAppLE S A :=
  baseAppLE_eq A.thickening.target S.S.scheme A.toBase.hom hVA

/-- The map on global sections of the structure morphism of an object of `CRIS(X/S)`, on
sections. -/
theorem crysBaseAppLE_apply (a : Γ(S.S.scheme, ⊤)) :
    crysBaseAppLE S A a =
      affineBaseAppLE S A hVA (S.S.scheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a) :=
  baseAppLE_apply A.thickening.target S.S.scheme A.toBase.hom hVA a

/-- **The universal divided power differential relative to `Γ(V, 𝒪_S)`, read as a derivation
relative to the global sections of the divided power base.**  It kills the latter because they
restrict to sections over `V`. -/
def affineCrysDerivation :
    (affineCrysDifferentialsObj S A hVA).Derivation (crysBaseAppLE S A) :=
  affineDpDerivation A.thickening.target S.S.scheme A.toBase.hom hVA

/-- The derivation `Crystalline.GlobalCrystallineSituation.affineCrysDerivation` sends a global
section to its universal divided power differential relative to `Γ(V, 𝒪_S)`. -/
@[simp]
theorem affineCrysDerivation_d (b : Γ(A.thickening.target.scheme, ⊤)) :
    (affineCrysDerivation S A hVA).d b =
      dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b := rfl

/-- **The universal differential of `Ω_{X/S}` at an object, read as a derivation relative to the
sections of the divided power base over an open through which the structure morphism factors.**
It kills those sections because they are pulled back from the base. -/
def crysAffineDerivation :
    (crysDifferentialsObj S A).Derivation (affineBaseAppLE S A hVA) :=
  dpConstAffineDerivation A.thickening.target S.S.scheme A.toBase.hom hVA

/-- The derivation `Crystalline.GlobalCrystallineSituation.crysAffineDerivation` sends a global
section to its universal differential in `Ω_{X/S}`. -/
@[simp]
theorem crysAffineDerivation_d (b : Γ(A.thickening.target.scheme, ⊤)) :
    (crysAffineDerivation S A hVA).d b = (crysDifferentialsD S A).d b := rfl

/-- **The comparison map from the sections of `Ω_{X/S}` at an affine object to the divided power
differentials relative to an affine open of the base.**  The universal differential relative to
`V` kills every section pulled back from the base, so it descends. -/
def affineCrysDifferentialsHom [IsAffine A.thickening.target.scheme] (hV : IsAffineOpen V) :
    crysDifferentialsObj S A ⟶ affineCrysDifferentialsObj S A hVA :=
  affineDpHom A.thickening.target S.S.scheme A.toBase.hom hVA (isAffineOpen_top _) hV

/-- The comparison map `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsHom` sends
the universal differential of a global section in `Ω_{X/S}` to its universal divided power
differential relative to `Γ(V, 𝒪_S)`. -/
@[simp]
theorem affineCrysDifferentialsHom_d [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) (b : Γ(A.thickening.target.scheme, ⊤)) :
    (affineCrysDifferentialsHom S A hVA hV) ((crysDifferentialsD S A).d b) =
      dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b :=
  affineDpHom_d A.thickening.target S.S.scheme A.toBase.hom hVA (isAffineOpen_top _) hV b

/-- **The comparison map from the divided power differentials relative to an open of the base to
the sections of `Ω_{X/S}` at an object.**  The universal differential of `Ω_{X/S}` kills the
sections over that open, so it descends. -/
def affineCrysDifferentialsInv :
    affineCrysDifferentialsObj S A hVA ⟶ crysDifferentialsObj S A :=
  affineDpInv A.thickening.target S.S.scheme A.toBase.hom hVA

/-- The comparison map `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsInv` sends
the universal divided power differential of a global section relative to `Γ(V, 𝒪_S)` to its
universal differential in `Ω_{X/S}`. -/
@[simp]
theorem affineCrysDifferentialsInv_dpd (b : Γ(A.thickening.target.scheme, ⊤)) :
    (affineCrysDifferentialsInv S A hVA)
        (dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b) =
      (crysDifferentialsD S A).d b :=
  affineDpInv_dpd A.thickening.target S.S.scheme A.toBase.hom hVA b

/-- For an affine object `(U, T, δ)` of `CRIS(X/S)` whose structure morphism factors through an
affine open `V ⊆ S`, the sections of `Ω_{X/S}` over `(U, T, δ)` are the divided power
differentials `Ω¹_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}`. -/
@[stacks 07J0 "Γ((U, T, δ), Ω_{X/S}) = Ω¹_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ} for an affine object of the \
crystalline category mapping into an affine open V ⊆ S"]
def affineCrysDifferentialsIso [IsAffine A.thickening.target.scheme] (hV : IsAffineOpen V) :
    crysDifferentialsObj S A ≅ affineCrysDifferentialsObj S A hVA where
  hom := affineCrysDifferentialsHom S A hVA hV
  inv := affineCrysDifferentialsInv S A hVA
  hom_inv_id := by
    refine dpConstDifferentials_ext fun b ↦ ?_
    simp
  inv_hom_id := by
    refine dpDifferentials_ext fun b ↦ ?_
    simp

/-- The identification carries the universal `S`-derivation `d_{X/S}` to the universal divided
power differential relative to `Γ(V, 𝒪_S)`. -/
@[simp]
theorem affineCrysDifferentialsIso_hom_d [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) (b : Γ(A.thickening.target.scheme, ⊤)) :
    (affineCrysDifferentialsIso S A hVA hV).hom ((crysSDerivation S).app A b) =
      dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b :=
  affineCrysDifferentialsHom_d S A hVA hV b

/-- The identification carries the universal divided power differential relative to `Γ(V, 𝒪_S)`
to the universal `S`-derivation `d_{X/S}`. -/
@[simp]
theorem affineCrysDifferentialsIso_inv_dpd [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) (b : Γ(A.thickening.target.scheme, ⊤)) :
    (affineCrysDifferentialsIso S A hVA hV).inv
        (dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b) =
      (crysSDerivation S).app A b :=
  affineCrysDifferentialsInv_dpd S A hVA b

/-- **The identification of [Stacks, Tag 07J0] is the only one compatible with the universal
derivations.**  This is what the equality sign of the source asserts: not that the two modules
happen to be isomorphic, but that there is exactly one isomorphism carrying `d_{X/S}` to
`d_{Γ(T, 𝒪_T)/Γ(V, 𝒪_S), δ}`, namely `affineCrysDifferentialsIso`.  Uniqueness holds because
the universal differentials generate the sections of `Ω_{X/S}` over the object, which is
`Crystalline.dpConstDifferentials_ext`. -/
@[stacks 07J0 "the equality sign of the tag: exactly one isomorphism \
Γ((U, T, δ), Ω_{X/S}) ≅ Ω¹_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ} carries d_{X/S} to the universal divided \
power differential"]
theorem existsUnique_affineCrysDifferentialsIso [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) :
    ∃! e : crysDifferentialsObj S A ≅ affineCrysDifferentialsObj S A hVA,
      ∀ b : Γ(A.thickening.target.scheme, ⊤),
        e.hom ((crysSDerivation S).app A b) =
          dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b :=
  ⟨affineCrysDifferentialsIso S A hVA hV, affineCrysDifferentialsIso_hom_d S A hVA hV,
    fun _e he ↦ Iso.ext (dpConstDifferentials_ext fun b ↦
      (he b).trans (affineCrysDifferentialsIso_hom_d S A hVA hV b).symm)⟩

end GlobalCrystallineSituation

end Crystalline

end
