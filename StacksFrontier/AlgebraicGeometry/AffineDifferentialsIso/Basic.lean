module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Vanishing
public import StacksFrontier.AlgebraicGeometry.DifferentialsAffine.Basic

/-!
# Relative derivations out of ring data on an affine open

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine open of `S` and let
`U ≤ f ⁻¹ᵁ V` be an affine open of `X`. This file constructs, from a single additive Leibniz
map on the coordinate ring of `U` annihilating the image of `Γ(S, V)`, a relative derivation
of `𝒪_X` over `f⁻¹ 𝒪_S` — the global-sections form of Stacks 01UO relative to a base — and
hence a morphism out of the sheaf of relative differentials of `f`.

## Main definitions

* `pushforwardDerivation`: a Leibniz, restriction-compatible family of additive maps on a
  scheme `Z` over `X`, read through the comorphism of `Z ⟶ X` as a derivation of `𝒪_X` along
  the comorphism of `f`, with values in the pushforward.

## Main results

* `d_comorphism_eq_zero`: over an affine base open, a Leibniz, restriction-compatible family
  annihilating the sections pulled back from `Γ(S, V)` annihilates the sections pulled back
  from every open of `S`.
* `appLE_base_eq_zero` is the restriction-stable form of the hypothesis of the previous result.
* `fromSpec_comp_preimage_base`: the canonical morphism from `Spec Γ(X, U)` composed with `f`
  lands in `V`.
* `exists_relativeDifferentials_hom_of_affine`: the global-sections form of Stacks 01UO
  relative to the base, as stated above.

## Implementation notes

Two inputs are not formal, and the file is organised around them.

The first is that the sections of `𝒪_S` on an arbitrary open are not restrictions of global
sections, so a family annihilating only the image of `Γ(S, V)` is not visibly a derivation
relative to the comorphism. Affineness of `V` replaces the missing computation: the basic
opens of `V` form a basis of its topology, on a basic open the sections of `𝒪_S` are a
localization of `Γ(S, V)`, and an additive Leibniz map out of a localization is determined by
its restriction along the structure map of that localization. So on each basic open the family
annihilates everything pulled back from `𝒪_S`, and since the coefficient sheaf of modules is
separated, annihilating on a cover is annihilating. This uses
`DifferentialsAffine.addMonoidHom_eq_of_isLocalization` with the zero map as one of the two
competing maps, which is why no inversion of the localizing element is needed anywhere.

The second is the comparison of the two vanishing conditions, which is
`AffineDifferentialsIso.toStructuralDerivation`.

With both in hand the construction is: transport the single Leibniz map on `Γ(Spec Γ(X, U), ⊤)`
to a family on all opens of `Spec Γ(X, U)` by the affine-open form of Stacks 01UO (which
applies to `⊤`, since the spectrum is affine), read that family on `X` through the comorphism
of `hU.fromSpec`, which is a morphism of schemes with image `U` and whose pushforward has
`Γ(k_* T, W) = Γ(T, k ⁻¹ᵁ W)` on the nose, and then apply the universal property of the sheaf
of relative differentials. The scheme `Spec Γ(X, U)` rather than `U` as an open subscheme is
used on purpose: `hU.fromSpec` makes the coordinate ring literally `Γ(X, U)`, so the Kähler
differentials of `f.appLE V U hUV` need no transport along a comparison of rings, and
`hU.fromSpec_preimage_self` makes the preimage of `U` the whole spectrum.

Reading the family through the comorphism rather than through the intersection with `U` is
also deliberate. A family indexed by the opens of `X` contained in `U` extends to all opens
only after identifying `Γ(k_* T, W)` with `Γ(k_* T, W ⊓ U)`, which is a comparison between
sections over two different (if equal) opens; composing with the comorphism of `k` gives the
components of the derivation on the nose, with no comparison at all.

Everything is in a single universe. The schemes are in `Scheme.{u}` and `X.Modules` is
`SheafOfModules.{u} X.ringCatSheaf`, so the universe parameters of the sheaf-theoretic module
of relative differentials are all `u` and no universe side condition arises.

Three transparency points. The restriction-compatibility hypothesis is
stated for an arbitrary morphism of opens rather than for `homOfLE`, since the comorphism of
`k` is natural for the morphisms produced by `Opens.map`, and the two forms are interchangeable
only by proof irrelevance in a poset. The Leibniz and naturality fields of
`pushforwardDerivation` are discharged by `congrArg` and `Eq.trans` on named intermediate
equalities rather than by `rw`: a goal mentioning the underlying presheaf of a sheaf of modules
is not type-correct at implicit transparency, `TopCat.Sheaf` and `Scheme.Modules` both being
definitions, and `rw [map_mul]` fails to find a pattern the goal displays. For the same reason
the restriction of a section of `𝒪_S` along `appLE` is rewritten by first proving the
corresponding equality of ring morphisms and then applying `congrArg`.

## What is not done here

The sheaf of relative differentials is not computed: nothing here says that the morphism out
of it produced by `exists_relativeDifferentials_hom_of_affine` is an isomorphism for any
particular coefficient sheaf. The companion file
`StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Kaehler` specializes it to the
quasi-coherent sheaf attached to the Kähler differentials and gets one half of Stacks 01UT; the
other half is not proved. No tag attribute is attached to any declaration here.

## References

* [Stacks Project, Tag 01UO](https://stacks.math.columbia.edu/tag/01UO)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

/-! ### Vanishing on the comorphism when the base open is affine -/

section AffineBase

variable {Z S : Scheme.{u}} {T : Z.Modules} (h : Z ⟶ S) {V : S.Opens} (hV : IsAffineOpen V)
  (htop : h ⁻¹ᵁ V = ⊤) (E : ∀ W : Z.Opens, Γ(Z, W) →+ Γ(T, W))
  (hmul : ∀ (W : Z.Opens) (a b : Γ(Z, W)), E W (a * b) = a • E W b + b • E W a)
  (hres : ∀ (W W' : Z.Opens) (i : W' ⟶ W) (a : Γ(Z, W)),
    E W' (Z.presheaf.map i.op a) = T.presheaf.map i.op (E W a))
  (hbase : ∀ r : Γ(S, V), E ⊤ (h.appLE V ⊤ (le_of_eq htop.symm) r) = 0)

include htop hres hbase in
/-- A Leibniz, restriction-compatible family annihilating the sections pulled back from the
affine open `V` annihilates their restrictions to every smaller open. -/
theorem appLE_base_eq_zero {W : Z.Opens} (e : W ≤ h ⁻¹ᵁ V) (r : Γ(S, V)) :
    E W (h.appLE V W e r) = 0 := by
  have hsplit : h.appLE V W e =
      h.appLE V ⊤ (le_of_eq htop.symm) ≫ Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op :=
    (Scheme.Hom.appLE_map h (le_of_eq htop.symm) (homOfLE (le_top : W ≤ ⊤)).op).symm
  have h1 : E W (h.appLE V W e r) =
      E W (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (h.appLE V ⊤ (le_of_eq htop.symm) r)) :=
    congrArg (E W) (ConcreteCategory.congr_hom hsplit r)
  rw [h1, hres _ _ (homOfLE (le_top : W ≤ ⊤)), hbase r, map_zero]

include hV htop hmul hres hbase in
/-- **The vanishing condition, over an affine base open.** Let `h : Z ⟶ S` be a morphism of
schemes whose image lies in an affine open `V` of `S`. A Leibniz, restriction-compatible
family of additive maps into a sheaf of `𝒪_Z`-modules that annihilates the sections of `𝒪_Z`
pulled back from `Γ(S, V)` annihilates the sections pulled back from *every* open of `S`.

This is the step that a sections-level computation of the inverse image sheaf would be needed
for if the family were only known on `Γ(S, V)`: the sections of `𝒪_S` on an arbitrary open
are not restrictions of global ones. Affineness of `V` replaces that computation, because the
basic opens of `V` form a basis and on a basic open the sections of `𝒪_S` are a localization
of `Γ(S, V)`, where a derivation is determined by its restriction to the base ring. -/
theorem d_comorphism_eq_zero (V' : S.Opens) (b : Γ(S, V')) :
    E (h ⁻¹ᵁ V') ((h.app V').hom b) = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext T.isSheaf ?_
  intro x hx
  have hxV : h.base x ∈ V := by
    have : x ∈ h ⁻¹ᵁ V := by rw [htop]; trivial
    exact this
  obtain ⟨s, hs1, hs2⟩ :=
    hV.exists_basicOpen_le (V := V' ⊓ V) ⟨h.base x, ⟨hx, hxV⟩⟩ hxV
  have hsV' : S.basicOpen s ≤ V' := le_trans hs1 inf_le_left
  have hsV : S.basicOpen s ≤ V := S.basicOpen_le s
  refine ⟨h ⁻¹ᵁ S.basicOpen s, fun y hy => hsV' hy, hs2, ?_⟩
  set W' : Z.Opens := h ⁻¹ᵁ S.basicOpen s with hW'
  have hle : W' ≤ h ⁻¹ᵁ V' := fun y hy => hsV' hy
  have hleV : W' ≤ h ⁻¹ᵁ V := fun y hy => hsV hy
  rw [← hres _ _ (homOfLE hle)]
  have emor : h.app V' ≫ Z.presheaf.map (homOfLE hle).op =
      S.presheaf.map (homOfLE hsV').op ≫
        h.appLE (S.basicOpen s) W' (fun y hy => hy) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hcast : Z.presheaf.map (homOfLE hle).op ((h.app V').hom b) =
      (h.appLE (S.basicOpen s) W' (fun y hy => hy))
        (S.presheaf.map (homOfLE hsV').op b) :=
    ConcreteCategory.congr_hom emor b
  rw [hcast]
  have := hV.isLocalization_basicOpen s
  have key := DifferentialsAffine.addMonoidHom_eq_of_isLocalization
    (A := Γ(S, V)) (S := Γ(S, S.basicOpen s)) (Submonoid.powers s)
    (N := Γ(T, W')) (h.appLE (S.basicOpen s) W' (fun y hy => hy)).hom
    (AddMonoidHom.mk' (fun y => E W' ((h.appLE (S.basicOpen s) W' (fun y hy => hy)) y))
      (fun y y' => by rw [map_add, map_add]))
    0
    (fun y y' => by
      show E W' ((h.appLE (S.basicOpen s) W' _) (y * y')) = _
      rw [map_mul, hmul]
      rfl)
    (fun _ _ => by simp)
    (fun a => by
      show E W' ((h.appLE (S.basicOpen s) W' _)
        (algebraMap Γ(S, V) Γ(S, S.basicOpen s) a)) = (0 : Γ(T, W'))
      have halg : (h.appLE (S.basicOpen s) W' (fun y hy => hy))
            (algebraMap Γ(S, V) Γ(S, S.basicOpen s) a) =
          h.appLE V W' hleV a := by
        rw [show algebraMap Γ(S, V) Γ(S, S.basicOpen s) a =
            S.presheaf.map (homOfLE hsV).op a from rfl,
          ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      rw [halg, appLE_base_eq_zero h htop E hres hbase hleV a])
  have hfin := DFunLike.congr_fun key (S.presheaf.map (homOfLE hsV').op b)
  simpa using hfin

end AffineBase


/-! ### A derivation on `X` from a family on a scheme over it -/

section Pushforward

variable {Z X S : Scheme.{u}} (k : Z ⟶ X) (f : X ⟶ S) {T : Z.Modules}
  (E : ∀ W : Z.Opens, Γ(Z, W) →+ Γ(T, W))
  (hmul : ∀ (W : Z.Opens) (a b : Γ(Z, W)), E W (a * b) = a • E W b + b • E W a)
  (hres : ∀ (W W' : Z.Opens) (i : W' ⟶ W) (a : Γ(Z, W)),
    E W' (Z.presheaf.map i.op a) = T.presheaf.map i.op (E W a))
  (hzero : ∀ (V' : S.Opens) (b : Γ(S, V')), E ((k ≫ f) ⁻¹ᵁ V') (((k ≫ f).app V').hom b) = 0)

include hmul hres hzero

/-- A Leibniz, restriction-compatible family of additive maps on `Z`, annihilating the
sections pulled back from `S` along `k ≫ f`, read on the pushforward along `k` as a
derivation of the structure sheaf of `X` along the comorphism of `f`. -/
noncomputable def pushforwardDerivation :
    ((Scheme.Modules.pushforward k).obj T).val.Derivation f.c where
  d {W} := (E (k ⁻¹ᵁ W.unop)).comp (k.app W.unop).hom.toAddMonoidHom
  d_mul {W} a b := by
    have h1 : E (k ⁻¹ᵁ W.unop) ((k.app W.unop).hom (a * b)) =
        (k.app W.unop).hom a • E (k ⁻¹ᵁ W.unop) ((k.app W.unop).hom b) +
          (k.app W.unop).hom b • E (k ⁻¹ᵁ W.unop) ((k.app W.unop).hom a) :=
      (congrArg (fun y => E (k ⁻¹ᵁ W.unop) y) (map_mul (k.app W.unop).hom a b)).trans
        (hmul _ _ _)
    exact h1
  d_map {W W'} i x := by
    have hnat : (k.app W'.unop).hom ((X.presheaf.map i) x) =
        (Z.presheaf.map ((Opens.map k.base).map i.unop).op) ((k.app W.unop).hom x) :=
      congrArg (fun g => (CommRingCat.Hom.hom g) x) (k.naturality i)
    have h1 : E (k ⁻¹ᵁ W'.unop) ((k.app W'.unop).hom ((X.presheaf.map i) x)) =
        (T.presheaf.map ((Opens.map k.base).map i.unop).op)
          (E (k ⁻¹ᵁ W.unop) ((k.app W.unop).hom x)) :=
      (congrArg (fun y => E (k ⁻¹ᵁ W'.unop) y) hnat).trans
        (hres _ _ ((Opens.map k.base).map i.unop) _)
    exact h1
  d_app {V'} b := by
    have hcomp : (k.app (f ⁻¹ᵁ V'.unop)).hom ((f.app V'.unop).hom b) =
        ((k ≫ f).app V'.unop).hom b :=
      congrArg (fun g => (CommRingCat.Hom.hom g) b) (Scheme.Hom.comp_app k f V'.unop).symm
    have h1 : E (k ⁻¹ᵁ (f ⁻¹ᵁ V'.unop))
        ((k.app (f ⁻¹ᵁ V'.unop)).hom ((f.app V'.unop).hom b)) = 0 :=
      (congrArg (fun y => E (k ⁻¹ᵁ (f ⁻¹ᵁ V'.unop)) y) hcomp).trans (hzero V'.unop b)
    exact h1

/-- The derivation of `pushforwardDerivation` on an open of `X` is the given family on its
preimage, precomposed with the comorphism. -/
theorem pushforwardDerivation_d (W : X.Opens) (a : Γ(X, W)) :
    (pushforwardDerivation k f E hmul hres hzero).d (X := op W) a =
      E (k ⁻¹ᵁ W) ((k.app W).hom a) := rfl

end Pushforward


/-! ### Relative derivations from ring data on an affine open -/

section Affine

variable {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}


/-- The spectrum of `Γ(X, U)` maps onto the affine open `U`, hence into `V`. -/
theorem fromSpec_comp_preimage_base (hUV : U ≤ f ⁻¹ᵁ V) :
    (hU.fromSpec ≫ f) ⁻¹ᵁ V = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : x ∈ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]; trivial
  exact hUV h1

/-- **Stacks 01UO, relative global-sections form.** Let `f : X ⟶ S` be a morphism of schemes,
let `V` be an affine open of `S` and let `U ≤ f ⁻¹ᵁ V` be an affine open of `X`, and let `T` be
a sheaf of modules on `Spec Γ(X, U)`. A single additive Leibniz map
`Γ(Spec Γ(X, U), ⊤) → Γ(T, ⊤)` annihilating the image of `Γ(S, V)` is the value on `⊤` of a
relative derivation of `𝒪_X` over `f⁻¹ 𝒪_S` with values in the pushforward of `T` to `X`, and
that relative derivation therefore factors the universal relative derivation of `f`, giving a
morphism out of the sheaf of relative differentials.

The two inputs that are not formal are both discharged here: the sections of `𝒪_S` on an
arbitrary open are not restrictions of global ones, which is handled by
`d_comorphism_eq_zero` using affineness of `V`; and the vanishing condition of a relative
derivation is stated on the inverse image sheaf rather than on the comorphism, which is
handled by `toStructuralDerivation`. -/
theorem exists_relativeDifferentials_hom_of_affine (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)
    {T : (Spec Γ(X, U)).Modules}
    (D : Γ(Spec Γ(X, U), ⊤) →+ Γ(T, ⊤))
    (hD : ∀ a b : Γ(Spec Γ(X, U), ⊤), D (a * b) = a • D b + b • D a)
    (hDbase : ∀ r : Γ(S, V), D (hU.fromSpec.appLE U ⊤
      (le_of_eq hU.fromSpec_preimage_self.symm) (f.appLE V U hUV r)) = 0) :
    ∃ (E : ∀ W : (Spec Γ(X, U)).Opens, Γ(Spec Γ(X, U), W) →+ Γ(T, W))
      (ψ : Scheme.Hom.relativeDifferentials f ⟶
        (Scheme.Modules.pushforward hU.fromSpec).obj T),
      E ⊤ = D ∧
      (∀ (W W' : (Spec Γ(X, U)).Opens) (i : W' ⟶ W) (a : Γ(Spec Γ(X, U), W)),
        E W' ((Spec Γ(X, U)).presheaf.map i.op a) = T.presheaf.map i.op (E W a)) ∧
      ∀ (W : X.Opens) (a : Γ(X, W)),
        (ψ.val.app (op W)).hom ((Scheme.Hom.universalRelativeDerivation f).d a) =
          E (hU.fromSpec ⁻¹ᵁ W) ((hU.fromSpec.app W).hom a) := by
  obtain ⟨E₀, hd1, hd2, hd3⟩ :=
    DifferentialsAffine.exists_restrictions (isAffineOpen_top (Spec Γ(X, U))) D hD
  have hmul : ∀ (W : (Spec Γ(X, U)).Opens) (a b : Γ(Spec Γ(X, U), W)),
      E₀ W le_top (a * b) = a • E₀ W le_top b + b • E₀ W le_top a :=
    fun W a b => hd1 W le_top a b
  have hres : ∀ (W W' : (Spec Γ(X, U)).Opens) (i : W' ⟶ W) (a : Γ(Spec Γ(X, U), W)),
      E₀ W' le_top ((Spec Γ(X, U)).presheaf.map i.op a) =
        T.presheaf.map i.op (E₀ W le_top a) :=
    fun W W' i a => hd2 W W' le_top i.le a
  have htop : (hU.fromSpec ≫ f) ⁻¹ᵁ V = ⊤ := fromSpec_comp_preimage_base f hU hUV
  have hsplit : f.appLE V U hUV ≫ hU.fromSpec.appLE U ⊤
        (le_of_eq hU.fromSpec_preimage_self.symm) =
      (hU.fromSpec ≫ f).appLE V ⊤ (le_of_eq htop.symm) :=
    Scheme.Hom.appLE_comp_appLE hU.fromSpec f V U ⊤ hUV
      (le_of_eq hU.fromSpec_preimage_self.symm)
  have hbase : ∀ r : Γ(S, V),
      E₀ ⊤ le_top ((hU.fromSpec ≫ f).appLE V ⊤ (le_of_eq htop.symm) r) = 0 := by
    intro r
    rw [show E₀ ⊤ le_top = D from hd3,
      show (hU.fromSpec ≫ f).appLE V ⊤ (le_of_eq htop.symm) r =
        hU.fromSpec.appLE U ⊤ (le_of_eq hU.fromSpec_preimage_self.symm)
          (f.appLE V U hUV r) from
        (ConcreteCategory.congr_hom hsplit r).symm]
    exact hDbase r
  have hzero := d_comorphism_eq_zero (hU.fromSpec ≫ f) hV htop
    (fun W => E₀ W le_top) hmul hres hbase
  obtain ⟨ψ, hψ, -⟩ := SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap f) ((Scheme.Modules.pushforward hU.fromSpec).obj T)
    (toStructuralDerivation f _
      (pushforwardDerivation hU.fromSpec f (fun W => E₀ W le_top) hmul hres hzero))
  exact ⟨fun W => E₀ W le_top, ψ, hd3, hres,
    fun W a => PresheafOfModules.Derivation.congr_d hψ a⟩

end Affine

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end
