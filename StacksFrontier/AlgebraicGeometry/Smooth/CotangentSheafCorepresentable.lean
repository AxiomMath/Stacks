module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentLocalization
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafAffine

/-!
# Uniqueness in the corepresentation of derivations by the pullback of `Ω_{X/S}`

Let `f : X ⟶ S` be a morphism of schemes, let `W` be an affine open of `X`, let `a : T ⟶ X` be a
morphism of schemes mapping into `W`, and let `N` be a sheaf of modules on `T`. Composing a
morphism `φ : a^*Ω_{X/S} ⟶ N` with the pullback `Stacks.Smooth.pullbackD` of the universal
differential produces a derivation of `Γ(X, W)` with values in `Γ(N, ⊤)`; that this assignment
is a bijection onto the derivations over `Γ(S, V)`, for `V` an affine open of `S` with
`W ≤ f ⁻¹ᵁ V`, is the affine computation of [Stacks Project, Tag 01UM] in the form that
[Stacks Project, Tag 02H6] consumes, and is equivalent to bijectivity of
`Stacks.Smooth.cotangentComparison` together with quasi-coherence of `a^*Ω_{X/S}`.

This file proves that the assignment is **injective**, with no affineness hypothesis on `T` and
no reference to `V` at all. The surjectivity half is proved elsewhere — see the implementation
notes — so the two together give the full corepresentation.

## Main results

* `Stacks.Smooth.pullbackCotangentSheaf_hom_ext`: two morphisms `a^*Ω_{X/S} ⟶ N` whose
  composites with `Stacks.Smooth.pullbackD` agree on `Γ(X, W)` are equal; and the special case
  `Stacks.Smooth.pullbackCotangentSheaf_eq_zero`.
* `Stacks.Smooth.eq_zero_of_leibniz_basicOpen`: a map from the sections of `𝒪_X` over a basic
  open of `W` satisfying the Leibniz rule and killing the sections restricted from `W` is zero.
  This is the local step; it is `Stacks.Smooth.eq_zero_of_leibniz_of_apply_algebraMap_eq_zero`
  for the localization `Γ(X, W) → Γ(X, X.basicOpen g)`.
* `Stacks.Smooth.section_ext_of_restrict_basicOpen`: two sections of `N` over `a ⁻¹ᵁ V` agreeing
  on the preimages of the basic opens of `W` contained in `V` agree. This is the global step;
  the relevant cover is `Stacks.Smooth.preimage_le_iSup_preimage_basicOpen`.
* `Stacks.Smooth.cotangentSheaf_hom_ext`: the uniqueness half of [Stacks Project, Tag 04BL] for
  `Ω_{X/S}`, in scheme vocabulary.
* `Stacks.Smooth.pullbackCotangentSheafHomEquiv_app`, `Stacks.Smooth.pullbackD_self`,
  `Stacks.Smooth.pullbackD_map`, `Stacks.Smooth.app_pullbackD_mul`: the dictionary identifying
  `φ.app (a ⁻¹ᵁ V) ∘ pullbackD` with the sectionwise differential of the sheaf derivation
  adjoint to `φ`, and its Leibniz rule and naturality.

## Implementation notes

The proof is the standard local argument, and it is run on the adjoint side. A morphism
`φ : a^*Ω_{X/S} ⟶ N` corresponds by `Stacks.Smooth.pullbackCotangentSheafHomEquiv` to a
morphism `Ω_{X/S} ⟶ a_*N`, hence by the universal property of `Ω_{X/S}` to a derivation of
`𝒪_X` over `f⁻¹𝒪_S` with values in `a_*N`, that is, to a compatible family of maps
`Γ(X, V) → Γ(N, a ⁻¹ᵁ V)` satisfying the Leibniz rule, one for each open `V` of `X`. The
family attached to `φ` is `x ↦ φ.app (a ⁻¹ᵁ V) (pullbackD f a V le_rfl x)`. Two such families
agree as soon as they agree over `W`:

* over a basic open `X.basicOpen g` of `W`, because `Γ(X, X.basicOpen g)` is a localization of
  `Γ(X, W)` and a derivation of a localization is determined by its restriction to the base —
  this is `Stacks.Smooth.eq_zero_of_leibniz_of_apply_algebraMap_eq_zero`, applied to the
  difference of the two families; and
* over an arbitrary open `V`, because the preimages of those basic opens of `W` that are
  contained in `V` cover `a ⁻¹ᵁ V` — here the hypothesis that `a` map into `W` is used, since
  it makes `a ⁻¹ᵁ V = a ⁻¹ᵁ (V ⊓ W)` — and `N` is a sheaf.

Neither step needs `V` or `T` affine, and neither needs the structure map
`f⁻¹𝒪_S ⟶ 𝒪_X`: only the Leibniz rule is used, not the vanishing on the base. That is why the
statements below mention no open of `S`.

The other half of the corepresentation is **existence**:

> for `f : X ⟶ S`, affine opens `V ⊆ S` and `W ⊆ X` with `W ≤ f ⁻¹ᵁ V`, a morphism `a : T ⟶ X`
> with `(⊤ : T.Opens) ≤ a ⁻¹ᵁ W`, a sheaf of modules `N` on `T`, and a `Γ(S, V)`-derivation
> `δ : Γ(X, W) → Γ(N, ⊤)` for the module structure `Stacks.Smooth.moduleAppLE a N hUW`, there is
> a morphism `φ : a^*Ω_{X/S} ⟶ N` with `φ.app ⊤ (pullbackD f a W hUW b) = δ b` for every
> `b : Γ(X, W)`.

That is `Stacks.Smooth.exists_hom_pullbackCotangentSheaf`, and combined with the uniqueness
proved here it is `Stacks.Smooth.existsUnique_hom_pullbackCotangentSheaf` in
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentExistence`. Bijectivity of
`Stacks.Smooth.cotangentComparison` follows and is
`Stacks.Smooth.bijective_cotangentComparison`; the computation of the sections of `Ω_{X/S}`
itself over an affine open — [Stacks Project, Tag 01UT] — is
`Stacks.Smooth.existsUnique_linearEquiv_universalD`.

Existence is a construction, not a uniqueness argument, and it is run as the construction
sketched by the two halves proved here, taken in the existence direction: extend `δ` along the
localization `Γ(X, W) → Γ(X, X.basicOpen g)` by
`Stacks.Smooth.derivationLocalizationLift`, check that two such extensions agree on
`X.basicOpen (g * g')` (again by uniqueness along a localization), and glue with
`TopCat.Sheaf.existsUnique_gluing'` to a section of `N` over `a ⁻¹ᵁ V` for every open `V` of
`X`; then verify the Leibniz rule, the naturality in `V` and the vanishing on the image of
`f⁻¹𝒪_S` for the glued family — each of them locally, by the same two steps — and feed the
resulting derivation to `Stacks.Sheaves.Differentials.universalDerivation_isUniversal`.

One route that was considered and *not* taken is the affine dictionary for quasi-coherent
sheaves (`AlgebraicGeometry.tilde.adjunction` and
`StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange`), on the grounds that every
statement there computes a quasi-coherent sheaf from its sections and so needs `a^*Ω_{X/S}` to
be quasi-coherent. That obstruction has since been removed rather than circumvented:
quasi-coherence of `Ω_{X/S}`, and of `a^*Ω_{X/S}` for an arbitrary `a`, is unconditional, by
`Stacks.Smooth.isQuasicoherent_cotangentSheaf` and
`Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf'`. The dictionary route is therefore
available too, and `Stacks.Smooth.bijective_cotangentComparison` does use `tilde` — but only to
manufacture a sheaf of modules out of a given module, never to compute `a^*Ω_{X/S}` from its
sections.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials

universe u

namespace Stacks.Smooth

/-! ### Naturality of sections of sheaves of modules -/

/-- Restriction of sections commutes with a morphism of sheaves of modules on a scheme. -/
theorem app_map_section {X : Scheme.{u}} {M M' : X.Modules} (θ : M ⟶ M') {U V : X.Opens}
    (hVU : V ≤ U) (s : Γ(M, U)) :
    θ.app V (M.presheaf.map (homOfLE hVU).op s)
      = M'.presheaf.map (homOfLE hVU).op (θ.app U s) :=
  congr($(θ.mapPresheaf.naturality (homOfLE hVU).op) s)

section Naturality

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X)

/-- The universal differential commutes with restriction of sections. -/
theorem universalD_map {U V : X.Opens} (hVU : V ≤ U) (x : Γ(X, U)) :
    universalD f V ((X.presheaf.map (homOfLE hVU).op).hom x)
      = (cotangentSheaf f).presheaf.map (homOfLE hVU).op (universalD f U x) :=
  (universalDerivation (ringedSpaceHom f)).d_map (homOfLE hVU).op x

/-- Over the full preimage of an open, the pullback of the universal differential is the unit of
`a^* ⊣ a_*` applied to the universal differential, with no restriction of sections. -/
theorem pullbackD_self (V : X.Opens) (x : Γ(X, V)) :
    pullbackD f a V (le_refl (a ⁻¹ᵁ V)) x
      = (pullbackCotangentUnitApp f a V).hom (universalD f V x) := by
  rw [pullbackD_apply, show (homOfLE (le_refl (a ⁻¹ᵁ V))) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The pullback of the universal differential commutes with restriction along an inclusion of
opens of `X`. -/
theorem pullbackD_map {U V : X.Opens} (hVU : V ≤ U) (x : Γ(X, U)) :
    pullbackD f a V (le_refl (a ⁻¹ᵁ V)) ((X.presheaf.map (homOfLE hVU).op).hom x)
      = (pullbackCotangentSheaf f a).presheaf.map
          (homOfLE ((Opens.map a.base).map (homOfLE hVU)).le).op
          (pullbackD f a U (le_refl (a ⁻¹ᵁ U)) x) := by
  rw [pullbackD_self, pullbackD_self, universalD_map f hVU x]
  exact app_map_section (pullbackCotangentUnit f a) hVU (universalD f U x)

end Naturality

/-! ### The adjoint description of a morphism out of `a^*Ω_{X/S}` -/

section Adjoint

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (N : T.Modules)

/-- The adjunction bijection of `Stacks.Smooth.pullbackCotangentSheafHomEquiv` is composition
with the unit of `a^* ⊣ a_*`. -/
theorem pullbackCotangentSheafHomEquiv_eq (φ : pullbackCotangentSheaf f a ⟶ N) :
    pullbackCotangentSheafHomEquiv f a N φ
      = pullbackCotangentUnit f a ≫ (Scheme.Modules.pushforward a).map φ :=
  Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction a) _ _ _

/-- On sections, the morphism `Ω_{X/S} ⟶ a_*N` adjoint to `φ : a^*Ω_{X/S} ⟶ N` is `φ` composed
with the unit of `a^* ⊣ a_*`. -/
theorem pullbackCotangentSheafHomEquiv_app (φ : pullbackCotangentSheaf f a ⟶ N) (U : X.Opens)
    (s : Γ(cotangentSheaf f, U)) :
    (pullbackCotangentSheafHomEquiv f a N φ).app U s
      = φ.app (a ⁻¹ᵁ U) ((pullbackCotangentUnitApp f a U).hom s) := by
  rw [pullbackCotangentSheafHomEquiv_eq]
  rfl

/-- **Morphisms out of `Ω_{X/S}` are determined by the derivations they induce.** Two morphisms
of sheaves of modules out of `Ω_{X/S}` whose composites with the universal derivation agree are
equal. This is the uniqueness half of [Stacks Project, Tag 04BL] applied to `Ω_{X/S}`. -/
theorem cotangentSheaf_hom_ext {F : X.Modules} {k₁ k₂ : cotangentSheaf f ⟶ F}
    (h : (universalDerivation (ringedSpaceHom f)).postcomp k₁.val
      = (universalDerivation (ringedSpaceHom f)).postcomp k₂.val) : k₁ = k₂ := by
  obtain ⟨_, _, huniq⟩ := Stacks.Sheaves.Differentials.universalDerivation_isUniversal
    (inverseImageSheaf (ringedSpaceHom f)) _ (inverseImageStructureMap (ringedSpaceHom f)) F
    ((universalDerivation (ringedSpaceHom f)).postcomp k₁.val)
  exact (huniq k₁ rfl).trans (huniq k₂ h.symm).symm

/-- The Leibniz rule for the derivation `b ↦ φ (d b)` induced by a morphism
`φ : a^*Ω_{X/S} ⟶ N`, on sections over an open `V` of `X` and its full preimage. -/
theorem app_pullbackD_mul (φ : pullbackCotangentSheaf f a ⟶ N) (V : X.Opens)
    (b₁ b₂ : Γ(X, V)) :
    φ.app (a ⁻¹ᵁ V) (pullbackD f a V (le_refl (a ⁻¹ᵁ V)) (b₁ * b₂))
      = (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom b₁ •
            φ.app (a ⁻¹ᵁ V) (pullbackD f a V (le_refl (a ⁻¹ᵁ V)) b₂)
          + (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom b₂ •
            φ.app (a ⁻¹ᵁ V) (pullbackD f a V (le_refl (a ⁻¹ᵁ V)) b₁) := by
  rw [pullbackD_mul' f a V (le_refl (a ⁻¹ᵁ V)) b₁ b₂, map_add,
    Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]

end Adjoint

/-! ### Locality of sections along the preimages of basic opens -/

section Locality

variable {X T : Scheme.{u}} (a : T ⟶ X) (N : T.Modules) {W : X.Opens}

/-- The preimages of the basic opens of an affine open `W` contained in an open `V` cover the
preimage of `V`, provided the morphism `a` maps into `W`. -/
theorem preimage_le_iSup_preimage_basicOpen (hW : IsAffineOpen W)
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (V : X.Opens) :
    a ⁻¹ᵁ V ≤ ⨆ g : {g : Γ(X, W) // X.basicOpen g ≤ V}, a ⁻¹ᵁ X.basicOpen g.1 := by
  intro t ht
  obtain ⟨g, hg₁, hg₂⟩ := hW.exists_basicOpen_le (V := V) ⟨a.base t, ht⟩
    (hUW (Opens.mem_top t))
  exact Opens.mem_iSup.mpr ⟨⟨g, hg₁⟩, hg₂⟩

/-- **Sections are determined on the preimages of basic opens.** Two sections of a sheaf of
modules over the preimage of an open `V` of `X` which agree on the preimage of every basic open
of an affine open `W` contained in `V` agree, provided `a` maps into `W`. -/
theorem section_ext_of_restrict_basicOpen (hW : IsAffineOpen W)
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (V : X.Opens) (s t : Γ(N, a ⁻¹ᵁ V))
    (h : ∀ (g : Γ(X, W)) (hg : X.basicOpen g ≤ V),
      N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hg)).le).op s
        = N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hg)).le).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun g : {g : Γ(X, W) // X.basicOpen g ≤ V} ↦ a ⁻¹ᵁ X.basicOpen g.1)
    (a ⁻¹ᵁ V) (fun g ↦ homOfLE ((Opens.map a.base).map (homOfLE g.2)).le)
    (preimage_le_iSup_preimage_basicOpen a hW hUW V) s t fun g ↦ h g.1 g.2

/-- **A derivation on a basic open is determined by the sections it comes from.** A map from the
sections of `𝒪_X` over a basic open `X.basicOpen g` of an affine open `W` to the sections of a
sheaf of modules over its preimage, which satisfies the Leibniz rule and vanishes on sections
restricted from `W`, vanishes identically.

The sections over `X.basicOpen g` are a localization of the sections over `W`, so this is
`Stacks.Smooth.eq_zero_of_leibniz_of_apply_algebraMap_eq_zero`. -/
theorem eq_zero_of_leibniz_basicOpen (hW : IsAffineOpen W) (g : Γ(X, W))
    (e : Γ(X, X.basicOpen g) → Γ(N, a ⁻¹ᵁ X.basicOpen g))
    (hmul : ∀ x y : Γ(X, X.basicOpen g),
      e (x * y) = (a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom x • e y
        + (a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom y • e x)
    (hzero : ∀ b : Γ(X, W), e ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom b) = 0)
    (x : Γ(X, X.basicOpen g)) : e x = 0 := by
  let := moduleAppLE a N (le_refl (a ⁻¹ᵁ X.basicOpen g))
  let := moduleAppLE a N ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  have := hW.isLocalization_basicOpen g
  have key : X.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫
      a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl
      = a.appLE W (a ⁻¹ᵁ X.basicOpen g)
        ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le := a.map_appLE _ _
  have : IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) Γ(N, a ⁻¹ᵁ X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul fun c n ↦ by
      change (a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom
            ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom c) • n
          = (a.appLE W (a ⁻¹ᵁ X.basicOpen g)
              ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le).hom c • n
      rw [← CommRingCat.comp_apply, key]
  exact eq_zero_of_leibniz_of_apply_algebraMap_eq_zero Γ(X, X.basicOpen g)
    (Submonoid.powers g) e hmul hzero x

end Locality

/-! ### Uniqueness of the morphism attached to a derivation -/

section Uniqueness

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (N : T.Modules) {W : X.Opens}

/-- Two morphisms `a^*Ω_{X/S} ⟶ N` inducing the same derivation of `Γ(X, W)` induce the same
derivation of the sections over a basic open of `W`.

Their difference satisfies the Leibniz rule and, by the hypothesis, kills the sections
restricted from `W`, so it vanishes because `Γ(X, X.basicOpen g)` is a localization of
`Γ(X, W)`. -/
theorem app_pullbackD_ext_basicOpen (hW : IsAffineOpen W) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W)
    {φ ψ : pullbackCotangentSheaf f a ⟶ N}
    (h : ∀ b : Γ(X, W), φ.app ⊤ (pullbackD f a W hUW b) = ψ.app ⊤ (pullbackD f a W hUW b))
    (g : Γ(X, W)) (x : Γ(X, X.basicOpen g)) :
    φ.app (a ⁻¹ᵁ X.basicOpen g) (pullbackD f a (X.basicOpen g) (le_refl _) x)
      = ψ.app (a ⁻¹ᵁ X.basicOpen g) (pullbackD f a (X.basicOpen g) (le_refl _) x) := by
  refine sub_eq_zero.mp (eq_zero_of_leibniz_basicOpen a N hW g
    (fun y ↦ φ.app (a ⁻¹ᵁ X.basicOpen g) (pullbackD f a (X.basicOpen g) (le_refl _) y)
      - ψ.app (a ⁻¹ᵁ X.basicOpen g) (pullbackD f a (X.basicOpen g) (le_refl _) y))
    (fun y z ↦ ?_) (fun b ↦ ?_) x)
  · rw [app_pullbackD_mul, app_pullbackD_mul, smul_sub, smul_sub]
    abel
  · have h0 : N.presheaf.map (homOfLE hUW).op
          (φ.app (a ⁻¹ᵁ W) (pullbackD f a W (le_refl (a ⁻¹ᵁ W)) b))
        = N.presheaf.map (homOfLE hUW).op
          (ψ.app (a ⁻¹ᵁ W) (pullbackD f a W (le_refl (a ⁻¹ᵁ W)) b)) := by
      rw [← app_map_section φ hUW, ← app_map_section ψ hUW,
        map_pullbackD f a W (le_refl (a ⁻¹ᵁ W)) hUW hUW b]
      exact h b
    have hfac : ∀ z : Γ(N, a ⁻¹ᵁ W),
        N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le).op z
          = N.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ X.basicOpen g ≤ ⊤)).op
              (N.presheaf.map (homOfLE hUW).op z) := fun z ↦ by
      rw [← Functor.map_comp_apply]
      rfl
    rw [pullbackD_map f a (X.basicOpen_le g) b,
      app_map_section φ ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le,
      app_map_section ψ ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le,
      hfac, hfac, h0, sub_self]

/-- **At most one morphism out of `a^*Ω_{X/S}` induces a given derivation.** Let `f : X ⟶ S` be
a morphism of schemes, let `W` be an affine open of `X`, let `a : T ⟶ X` be a morphism mapping
into `W`, and let `N` be a sheaf of modules on `T`. Two morphisms `a^*Ω_{X/S} ⟶ N` whose
composites with the pullback `Stacks.Smooth.pullbackD` of the universal differential agree on
the sections of `𝒪_X` over `W` are equal.

This is the uniqueness half of the corepresentability of the derivation functor by
`a^*Ω_{X/S}`, which is the form of the affine computation of [Stacks Project, Tag 01UM] that
[Stacks Project, Tag 02H6] consumes. Neither `T` nor the open `V` of `S` below `W` is required
to be affine, and no relation `W ≤ f ⁻¹ᵁ V` is needed: uniqueness is insensitive to the base. -/
theorem pullbackCotangentSheaf_hom_ext (hW : IsAffineOpen W) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W)
    {φ ψ : pullbackCotangentSheaf f a ⟶ N}
    (h : ∀ b : Γ(X, W), φ.app ⊤ (pullbackD f a W hUW b) = ψ.app ⊤ (pullbackD f a W hUW b)) :
    φ = ψ := by
  have key : ∀ (V : X.Opens) (x : Γ(X, V)),
      φ.app (a ⁻¹ᵁ V) ((pullbackCotangentUnitApp f a V).hom (universalD f V x))
        = ψ.app (a ⁻¹ᵁ V) ((pullbackCotangentUnitApp f a V).hom (universalD f V x)) := by
    intro V x
    rw [← pullbackD_self]
    refine section_ext_of_restrict_basicOpen a N hW hUW V _ _ fun g hg ↦ ?_
    rw [← app_map_section φ ((Opens.map a.base).map (homOfLE hg)).le,
      ← app_map_section ψ ((Opens.map a.base).map (homOfLE hg)).le,
      ← pullbackD_map f a hg x]
    exact app_pullbackD_ext_basicOpen f a N hW hUW h g _
  refine (pullbackCotangentSheafHomEquiv f a N).injective (cotangentSheaf_hom_ext f ?_)
  ext U x
  change (pullbackCotangentSheafHomEquiv f a N φ).app U.unop (universalD f U.unop x)
      = (pullbackCotangentSheafHomEquiv f a N ψ).app U.unop (universalD f U.unop x)
  rw [pullbackCotangentSheafHomEquiv_app, pullbackCotangentSheafHomEquiv_app]
  exact key U.unop x

/-- A morphism out of `a^*Ω_{X/S}` killing the pullbacks of the universal differentials of the
sections over an affine open `W` into which `a` maps is zero. -/
theorem pullbackCotangentSheaf_eq_zero (hW : IsAffineOpen W) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W)
    {φ : pullbackCotangentSheaf f a ⟶ N}
    (h : ∀ b : Γ(X, W), φ.app ⊤ (pullbackD f a W hUW b) = 0) : φ = 0 :=
  pullbackCotangentSheaf_hom_ext f a N hW hUW fun b ↦ by
    rw [h b, Scheme.Modules.Hom.zero_app]
    simp

end Uniqueness

end Stacks.Smooth

end
