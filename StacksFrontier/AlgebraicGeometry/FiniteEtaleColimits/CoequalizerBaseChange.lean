module

public import Mathlib.Algebra.Category.Ring.Under.Property
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.BaseChangeCoproducts
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.EqualizerBaseChange
import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FlatBaseChangeOnIntersection

/-!
# Base change preserves the finite colimits of finite étale covers

Let `f : X ⟶ S` be a morphism of schemes. This file proves the **fourth assertion of Stacks Tag
0BN9**: the base-change functor `FÉt_S ⥤ FÉt_X` preserves finite colimits.

By `Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleBaseChange_of_preservesCoequalizers`
only the coequalizers are at issue, and a coequalizer in `FÉt_S` is the relative spectrum of the
equalizer algebra `𝓐 = Eq(a^♯, b^♯)` (`Stacks.FundamentalGroup.isColimit_finiteEtaleCofork`). So
what is proved is that the canonical comparison
```
Spec_X Eq((f^*a)^♯, (f^*b)^♯)  ⟶  (Spec_S 𝓐) ×_S X
```
is an isomorphism, and the route is Zariski-local on `X`:

* the comparison is a morphism of affine `X`-schemes, so it is an isomorphism as soon as it is one
  on sections over every affine open `W` of `X`, and those opens that moreover lie over an affine
  open `V` of `S` form a basis (`Stacks.FundamentalGroup.isBasis_compatibleAffineOpens`);
* over such a pair `W ⊆ f ⁻¹ V` everything in sight is affine, and the sections of the
  pushed-forward structure sheaf of a base-changed cover form a **pushout** of commutative rings
  (`Stacks.FundamentalGroup.isPushout_app_pullback`), because the corresponding square of affine
  schemes is cartesian;
* a pushout of commutative rings preserves the equalizer of two maps of finite étale algebras,
  by `RingHom.FiniteEtale.hasStableEqualizers` through Mathlib's
  `RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd`;
* and taking sections over an open sends the equalizer of two quasi-coherent algebras to the
  equalizer of their sections, because the equalizer algebra *is* the subalgebra of agreement on
  sections (`Stacks.FundamentalGroup.preservesLimit_parallelPair_quasicoherentSectionsFunctor`).

No base-change isomorphism for the relative spectrum over an arbitrary base is used, and no
quasi-coherent pullback of sheaves of modules: the only geometric input is that the square
```
M ×_S X ⟶ M
   |        |
   v        v
   X   ⟶    S
```
restricts to a cartesian square of *affine* schemes over a compatible pair of affine opens, which
is Mathlib's `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`, and that `Γ` turns a cartesian
square of affine schemes into a pushout, which is Mathlib's
`AlgebraicGeometry.isPushout_appTop_of_isPullback`.

## Main definitions

* `Stacks.FundamentalGroup.algebraSectionsFunctor` and
  `Stacks.FundamentalGroup.quasicoherentSectionsFunctor` — taking sections over an open, as a
  functor to the algebras over the sections of the structure sheaf.
* `Stacks.FundamentalGroup.coequalizerBaseChangeComparison` — the comparison from the coequalizer
  of the base changes to the base change of the coequalizer.

## Main results

* `Stacks.FundamentalGroup.isPushout_app_pullback` — the sections of the pushed-forward structure
  sheaf of `M ×_S X` over a compatible pair of affine opens are the pushout of the sections of
  `M_* 𝒪` along the map on sections of `f`.
* `Stacks.FundamentalGroup.isLimitForkOfIsPushoutFiniteEtale` — the base change of an equalizer
  fork of finite étale algebras is an equalizer fork, with the base change presented by pushout
  squares.
* `Stacks.FundamentalGroup.isIso_comparison` — **the base change of the coequalizer of two
  morphisms of finite étale covers is the coequalizer of their base changes.**
* `Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleBaseChange` — **the fourth
  assertion of Stacks Tag 0BN9**: base change of finite étale covers preserves finite colimits.

## Implementation notes

No `@[stacks]` attribute appears here. Tag 0BN9 has four assertions, of which this file completes
the fourth; the audit scanner keys on the bare four-character tag, so an attribute on a partial
result would report the whole tag formalized. The remaining assertion is the fpqc-local
description of the coequalizers, the extra field of
`Stacks.FundamentalGroup.HasFiniteColimitsWithLocalCoequalizers`.

The transport of the limit along the three pushout identifications is carried out in
`Stacks.FundamentalGroup.isLimitForkOfIsPushoutFiniteEtale`, where every object is a variable.
That is deliberate: `CategoryTheory.Under.pushout` is semireducible, so the apex
`((Under.pushout ρ).obj A).right` of its value is not the term `pushout A.hom ρ` at `implicit`
transparency, and a `rw` or `simp` that would retype a subterm of a composite of the two fails
with `motive is not type correct` even though the composite elaborates. Stating the transport
generically makes every such composite well-typed by construction, and the geometric instance is
then supplied by `exact`, which checks at default transparency. The one place where a composite
of the two spellings is unavoidable,
`Stacks.FundamentalGroup.map_comp_underIsoPushout`, is proved by a `calc` chain of `congrArg`s
rather than by rewriting.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.QuasicoherentAlgebraEqualizer

universe u

namespace Stacks.FundamentalGroup

/-! ### Sections over an open, as a functor to algebras over the sections of the structure sheaf -/

/-- Evaluation of a sheaf of commutative rings at an open. -/
def sheafSectionsFunctor (X : Scheme.{u}) (V : X.Opens) :
    TopCat.Sheaf CommRingCat.{u} X ⥤ CommRingCat.{u} where
  obj A := A.obj.obj (op V)
  map f := f.hom.app (op V)

/-- Evaluation of a sheaf of `𝒪_X`-algebras at an open `V`, as a functor to the category of
algebras over `Γ(X, V)`. -/
def algebraSectionsFunctor (X : Scheme.{u}) (V : X.Opens) :
    AlgebraSheaf X ⥤ Under Γ(X, V) :=
  Under.post (X := X.sheaf) (sheafSectionsFunctor X V)

/-- Evaluation of a quasi-coherent sheaf of `𝒪_X`-algebras at an open `V`. -/
def quasicoherentSectionsFunctor (X : Scheme.{u}) (V : X.Opens) :
    QuasicoherentAlgebra X ⥤ Under Γ(X, V) :=
  (IsQuasicoherentAlgebra X).ι ⋙ algebraSectionsFunctor X V

/-- **The equalizer of two morphisms of quasi-coherent algebras is computed on sections.** Taking
sections over an open preserves it, because the equalizer algebra is by construction the subring
of agreement on sections and that is the equalizer of the two maps of algebras on sections. -/
theorem preservesLimit_parallelPair_quasicoherentSectionsFunctor {X : Scheme.{u}}
    {A B : QuasicoherentAlgebra X} (φ ψ : A ⟶ B) (V : X.Opens) :
    PreservesLimit (parallelPair φ ψ) (quasicoherentSectionsFunctor X V) := by
  refine preservesLimit_of_preserves_limit_cone (isLimitQuasicoherentFork φ ψ) ?_
  refine (isLimitMapConeForkEquiv _ (quasicoherentEqualizerι_comp φ ψ)).symm ?_
  exact CommRingCat.Under.equalizerForkIsLimit _ _

/-! ### Sections of a pushforward over an affine open base change to a pushout -/

/-- The map on global sections of the restriction of a morphism to a pair of opens is the map on
sections over that pair. -/
public alias resLE_appTop_comp := AlgebraicGeometry.resLE_appTop_topIso

/-- **The sections of a pushed-forward structure sheaf base change to a pushout of rings.** Let
`q : M ⟶ S` be a morphism of schemes, let `f : X ⟶ S` be arbitrary, and let `V` be an affine
open of `S` and `W` an affine open of `X` inside `f ⁻¹ V` such that `q ⁻¹ V` is affine. Then the
square
```
Γ(S, V)  ⟶  Γ(M, q ⁻¹ V)
   |             |
   v             v
Γ(X, W)  ⟶  Γ(M ×_S X, pr ⁻¹ W)
```
is a pushout of commutative rings.

All four schemes in the corresponding square of schemes are affine and that square is a
pullback, so this is Mathlib's `AlgebraicGeometry.isPushout_appTop_of_isPullback` applied to
the restriction `AlgebraicGeometry.Scheme.Hom.isPullback_resLE` of the defining pullback square
of `M ×_S X`. -/
theorem isPushout_app_pullback {S X M : Scheme.{u}} (f : X ⟶ S) (q : M ⟶ S)
    {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V)
    (hqV : IsAffineOpen (q ⁻¹ᵁ V))
    (hsub : pullback.snd q f ⁻¹ᵁ W ≤ pullback.fst q f ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPushout (q.app V) (f.appLE V W hWV)
      ((pullback.fst q f).appLE (q ⁻¹ᵁ V) (pullback.snd q f ⁻¹ᵁ W) hsub)
      ((pullback.snd q f).app W) := by
  have hpb := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback q f) hWV
    (le_refl (q ⁻¹ᵁ V)) (UY := pullback.snd q f ⁻¹ᵁ W) (inf_eq_right.mpr hsub).symm
  have : IsAffine (V : Scheme.{u}) := hV
  have : IsAffine (W : Scheme.{u}) := hW
  have : IsAffine ((q ⁻¹ᵁ V : M.Opens) : Scheme.{u}) := hqV
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  refine (isPushout_appTop_of_isPullback hpb).of_iso V.topIso (q ⁻¹ᵁ V).topIso W.topIso
    (pullback.snd q f ⁻¹ᵁ W).topIso ?_ ?_ ?_ ?_
  all_goals exact resLE_appTop_comp _ _ _ _

/-! ### Base change of an equalizer of finite étale algebras -/

/-- **Base change preserves equalizers of finite étale algebras.** For a homomorphism
`ρ : R ⟶ R'` of commutative rings and two maps `α, β : C ⟶ B` of `R`-algebras whose structure
morphisms are finite étale, the pushout functor along `ρ` preserves the equalizer of `α` and
`β`.

This is `RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd` for the property
`RingHom.FiniteEtale`, whose stable equalizers are
`RingHom.FiniteEtale.hasStableEqualizers`. -/
theorem preservesLimit_parallelPair_underPushout_finiteEtale
    {R R' : CommRingCat.{u}} (ρ : R ⟶ R') {C B : Under R} (α β : C ⟶ B)
    (hC : RingHom.FiniteEtale C.hom.hom) (hB : RingHom.FiniteEtale B.hom.hom) :
    PreservesLimit (parallelPair α β) (CategoryTheory.Under.pushout ρ) := by
  algebraize [ρ.hom]
  rw [← CommRingCat.ofHom_hom ρ,
    ← preservesLimit_iff_of_natIso _ (CommRingCat.tensorProdIsoPushout R R')]
  exact RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd
    RingHom.FiniteEtale.hasStableEqualizers α β hC hB

/-- The left inclusion into a pushout of rings is natural in the object pushed out. -/
theorem inl_comp_underPushout_map_right {R R' : CommRingCat.{u}} (ρ : R ⟶ R') {a b : Under R}
    (m : a ⟶ b) :
    pushout.inl a.hom ρ ≫ ((CategoryTheory.Under.pushout ρ).map m).right =
      m.right ≫ pushout.inl b.hom ρ := by
  rw [CategoryTheory.Under.pushout_map]
  exact pushout.inl_desc _ _ _

/-- The right inclusion into a pushout of rings is the structure morphism of the pushout, so it
is carried to itself. -/
theorem inr_comp_underPushout_map_right {R R' : CommRingCat.{u}} (ρ : R ⟶ R') {a b : Under R}
    (m : a ⟶ b) :
    pushout.inr a.hom ρ ≫ ((CategoryTheory.Under.pushout ρ).map m).right =
      pushout.inr b.hom ρ := by
  rw [CategoryTheory.Under.pushout_map]
  exact pushout.inr_desc _ _ _

section Transport

variable {R R' : CommRingCat.{u}} (ρ : R ⟶ R')

/-- The identification of the chosen pushout along `ρ` with the apex of any other pushout square
on the same span, as an isomorphism of `R'`-algebras. -/
def underIsoPushout {A : Under R} {A' : Under R'} {jA : A.right ⟶ A'.right}
    (hA : IsPushout A.hom ρ jA A'.hom) :
    (CategoryTheory.Under.pushout ρ).obj A ≅ A' :=
  Under.isoMk ((IsPushout.of_hasPushout A.hom ρ).isoIsPushout _ _ hA)
    (IsPushout.inr_isoIsPushout_hom _ _ _ _)

/-- The isomorphism `underIsoPushout ρ hA` carries the left inclusion of the chosen pushout to
the map `jA` of the given pushout square. -/
theorem inl_underIsoPushout {A : Under R} {A' : Under R'} {jA : A.right ⟶ A'.right}
    (hA : IsPushout A.hom ρ jA A'.hom) :
    pushout.inl A.hom ρ ≫ (underIsoPushout ρ hA).hom.right = jA :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- The identification of `Stacks.FundamentalGroup.underIsoPushout` is compatible with any
morphism whose two base changes are compatible on the apexes. -/
theorem map_comp_underIsoPushout {A B : Under R} {A' B' : Under R'}
    {jA : A.right ⟶ A'.right} {jB : B.right ⟶ B'.right}
    (hA : IsPushout A.hom ρ jA A'.hom) (hB : IsPushout B.hom ρ jB B'.hom)
    (m : A ⟶ B) (m' : A' ⟶ B') (hm : jA ≫ m'.right = m.right ≫ jB) :
    (CategoryTheory.Under.pushout ρ).map m ≫ (underIsoPushout ρ hB).hom =
      (underIsoPushout ρ hA).hom ≫ m' := by
  ext : 1
  refine (IsPushout.of_hasPushout A.hom ρ).hom_ext ?_ ?_
  · rw [Under.comp_right, Under.comp_right]
    erw [← Category.assoc, inl_comp_underPushout_map_right, Category.assoc, inl_underIsoPushout,
      ← Category.assoc, inl_underIsoPushout, hm]
  · rw [Under.comp_right, Under.comp_right]
    erw [← Category.assoc, inr_comp_underPushout_map_right, IsPushout.inr_isoIsPushout_hom,
      ← Category.assoc, IsPushout.inr_isoIsPushout_hom, Under.w]

/-- **The base change of an equalizer fork of finite étale algebras is an equalizer fork**,
in the form consumed by the geometric application: the three objects of the base-changed fork
are given as the apexes of three pushout squares over the same map `ρ`, and the three maps of
the fork are given as maps compatible with those squares.

The fork is the image of the given one under `CategoryTheory.Under.pushout ρ`, which preserves
it by `Stacks.FundamentalGroup.preservesLimit_parallelPair_underPushout_finiteEtale`, up to the
identifications of `Stacks.FundamentalGroup.underIsoPushout`. -/
def isLimitForkOfIsPushoutFiniteEtale
    {A C B : Under R} {α β : C ⟶ B} {p : A ⟶ C} (hp : p ≫ α = p ≫ β)
    (hlim : IsLimit (Fork.ofι p hp))
    (hCfe : RingHom.FiniteEtale C.hom.hom) (hBfe : RingHom.FiniteEtale B.hom.hom)
    {A' C' B' : Under R'} {α' β' : C' ⟶ B'} {p' : A' ⟶ C'} (hp' : p' ≫ α' = p' ≫ β')
    {jA : A.right ⟶ A'.right} {jC : C.right ⟶ C'.right} {jB : B.right ⟶ B'.right}
    (hA : IsPushout A.hom ρ jA A'.hom) (hC : IsPushout C.hom ρ jC C'.hom)
    (hB : IsPushout B.hom ρ jB B'.hom)
    (hpj : jA ≫ p'.right = p.right ≫ jC)
    (haj : jC ≫ α'.right = α.right ≫ jB)
    (hbj : jC ≫ β'.right = β.right ≫ jB) :
    IsLimit (Fork.ofι p' hp') := by
  have := preservesLimit_parallelPair_underPushout_finiteEtale ρ α β hCfe hBfe
  have h2 := (isLimitMapConeForkEquiv (CategoryTheory.Under.pushout ρ) hp)
    (isLimitOfPreserves (CategoryTheory.Under.pushout ρ) hlim)
  have hinv : ∀ {D D' : Under R} {E E' : Under R'} {k : D ⟶ D'} {k' : E ⟶ E'}
      (e : (CategoryTheory.Under.pushout ρ).obj D ≅ E)
      (e' : (CategoryTheory.Under.pushout ρ).obj D' ≅ E'),
      (CategoryTheory.Under.pushout ρ).map k ≫ e'.hom = e.hom ≫ k' →
        e.inv ≫ (CategoryTheory.Under.pushout ρ).map k = k' ≫ e'.inv := by
    intro D D' E E' k k' e e' h
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hPC := map_comp_underIsoPushout ρ hA hC p p' hpj
  have hα := hinv (underIsoPushout ρ hC) (underIsoPushout ρ hB)
    (map_comp_underIsoPushout ρ hC hB α α' haj)
  have hβ := hinv (underIsoPushout ρ hC) (underIsoPushout ρ hB)
    (map_comp_underIsoPushout ρ hC hB β β' hbj)
  have hπ := hinv (underIsoPushout ρ hA) (underIsoPushout ρ hC) hPC
  have key : ∀ s : Fork α' β', (s.ι ≫ (underIsoPushout ρ hC).inv) ≫
      (CategoryTheory.Under.pushout ρ).map α =
      (s.ι ≫ (underIsoPushout ρ hC).inv) ≫ (CategoryTheory.Under.pushout ρ).map β := by
    intro s
    rw [Category.assoc, Category.assoc, hα, hβ, ← Category.assoc, ← Category.assoc,
      s.condition]
  have hfac : ∀ s : Fork α' β',
      h2.lift (Fork.ofι _ (key s)) ≫ (CategoryTheory.Under.pushout ρ).map p =
        s.ι ≫ (underIsoPushout ρ hC).inv := by
    intro s
    have h := h2.fac (Fork.ofι _ (key s)) WalkingParallelPair.zero
    simpa only [Fork.ι_ofι, Fork.app_zero_eq_ι] using h
  refine Fork.IsLimit.mk _ (fun s ↦ h2.lift (Fork.ofι _ (key s)) ≫ (underIsoPushout ρ hA).hom)
    (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · rw [Fork.ι_ofι, Category.assoc, ← hPC, ← Category.assoc, hfac s, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · rw [Fork.ι_ofι] at hm
    refine (Iso.comp_inv_eq (underIsoPushout ρ hA)).1 (Fork.IsLimit.hom_ext h2 ?_)
    rw [Fork.ι_ofι, hfac s, Category.assoc, hπ, ← Category.assoc, hm]

end Transport

/-! ### The comparison of the two ways of taking sections after base change -/

section BaseChangeSections

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The structure morphism of a finite étale cover is affine. -/
instance isAffineHom_hom_finiteEtaleOver (A : FiniteEtaleOver S) : IsAffineHom A.hom := by
  have : IsFinite A.hom := A.prop.1
  infer_instance

/-- The preimage in `A ×_S X` of an open of `X` inside `f ⁻¹ V` lies over `A ⁻¹ V`. -/
theorem snd_preimage_le_fst_preimage (A : FiniteEtaleOver S) {V : S.Opens} {W : X.Opens}
    (hWV : W ≤ f ⁻¹ᵁ V) :
    pullback.snd A.hom f ⁻¹ᵁ W ≤ pullback.fst A.hom f ⁻¹ᵁ (A.hom ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
  exact fun _ hx ↦ hWV hx

/-- The map on sections of a morphism of finite étale covers, over an open of the base. -/
theorem quasicoherentSectionsFunctor_map_pushforward {A B : (FiniteEtaleOver S)ᵒᵖ} (u : A ⟶ B)
    (V : S.Opens) :
    ((quasicoherentSectionsFunctor S V).map
        ((finiteEtalePushforwardFunctor S).map u)).right =
      u.unop.left.appLE ((unop A).hom ⁻¹ᵁ V) ((unop B).hom ⁻¹ᵁ V)
        (by rw [← MorphismProperty.Over.w u.unop, Scheme.Hom.comp_preimage]) :=
  pushforwardAlgebraMapAux_app (unop A).hom u.unop.left (unop B).hom
    (MorphismProperty.Over.w u.unop) V _

/-- The map on sections over a pair of opens does not depend on which of two equal morphisms it
is taken of. -/
theorem appLE_congr_hom {Y Z : Scheme.{u}} {g₁ g₂ : Y ⟶ Z} (h : g₁ = g₂) (U : Z.Opens)
    (W : Y.Opens) (e₁ : W ≤ g₁ ⁻¹ᵁ U) (e₂ : W ≤ g₂ ⁻¹ᵁ U) :
    g₁.appLE U W e₁ = g₂.appLE U W e₂ := by
  subst h; rfl

/-- **The projections to the covers of `S` are compatible with the maps of covers.** This is the
naturality, on sections, of the base-change comparison: `AlgebraicGeometry.Scheme.Hom.appLE` of
the cartesian square `Stacks.FundamentalGroup.finiteEtaleBaseChange_map_left_fst`. -/
theorem appLE_fst_naturality {A B : FiniteEtaleOver S} (v : B ⟶ A) {V : S.Opens} {W : X.Opens}
    (e₁ : (B.hom ⁻¹ᵁ V) ≤ v.left ⁻¹ᵁ (A.hom ⁻¹ᵁ V))
    (e₂ : pullback.snd B.hom f ⁻¹ᵁ W ≤ pullback.fst B.hom f ⁻¹ᵁ (B.hom ⁻¹ᵁ V))
    (e₃ : pullback.snd A.hom f ⁻¹ᵁ W ≤ pullback.fst A.hom f ⁻¹ᵁ (A.hom ⁻¹ᵁ V))
    (e₄ : pullback.snd B.hom f ⁻¹ᵁ W ≤
      ((finiteEtaleBaseChange f).map v).left ⁻¹ᵁ (pullback.snd A.hom f ⁻¹ᵁ W)) :
    v.left.appLE (A.hom ⁻¹ᵁ V) (B.hom ⁻¹ᵁ V) e₁ ≫
        (pullback.fst B.hom f).appLE (B.hom ⁻¹ᵁ V) (pullback.snd B.hom f ⁻¹ᵁ W) e₂ =
      (pullback.fst A.hom f).appLE (A.hom ⁻¹ᵁ V) (pullback.snd A.hom f ⁻¹ᵁ W) e₃ ≫
        ((finiteEtaleBaseChange f).map v).left.appLE (pullback.snd A.hom f ⁻¹ᵁ W)
          (pullback.snd B.hom f ⁻¹ᵁ W) e₄ :=
  (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e₁ e₂).trans
    ((appLE_congr_hom (finiteEtaleBaseChange_map_left_fst f v).symm _ _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e₃ e₄).symm)

/-- **The sections over an affine open of a finite étale cover are finite étale** over the
sections of the structure sheaf: the affine-local description of finiteness and étaleness. -/
theorem finiteEtale_app (A : FiniteEtaleOver S) {V : S.Opens} (hV : IsAffineOpen V) :
    RingHom.FiniteEtale (A.hom.app V).hom := by
  have hf : IsFinite A.hom := A.prop.1
  have he : Etale A.hom := A.prop.2
  exact ⟨hf.finite_app V hV, (etale_iff_app A.hom).1 he V hV⟩

/-- The affine opens of `X` lying inside the preimage of an affine open of `S`. -/
def compatibleAffineOpens : Type u :=
  { p : X.affineOpens × S.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : S.Opens) }

/-- **The affine opens of `X` lying over an affine open of `S` form a basis.** Every point has an
affine neighbourhood inside the preimage of an affine neighbourhood of its image. -/
theorem isBasis_compatibleAffineOpens :
    Opens.IsBasis (Set.range fun p : compatibleAffineOpens f ↦ (p.1.1 : X.Opens)) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hx ↦ ?_
  obtain ⟨V, hV, hfxV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWU⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U ⊓ f ⁻¹ᵁ V from ⟨hx, hfxV⟩)
  exact ⟨W, ⟨⟨(⟨W, hW⟩, ⟨V, hV⟩), le_trans hWU inf_le_right⟩, rfl⟩, hxW,
    le_trans hWU inf_le_left⟩

end BaseChangeSections

/-! ### Base change of the coequalizer of two morphisms of finite étale covers -/

section Comparison

variable {S X : Scheme.{u}} (f : X ⟶ S) {Y Z : FiniteEtaleOver S} (a b : Y ⟶ Z)

/-- The base change of the projection onto the coequalizer coequalizes the base changes. -/
theorem baseChange_comp_coequalizerπ :
    (finiteEtaleBaseChange f).map a ≫
        (finiteEtaleBaseChange f).map (finiteEtaleCoequalizerπ a b) =
      (finiteEtaleBaseChange f).map b ≫
        (finiteEtaleBaseChange f).map (finiteEtaleCoequalizerπ a b) := by
  rw [← Functor.map_comp, ← Functor.map_comp, comp_finiteEtaleCoequalizerπ]

/-- **The comparison from the coequalizer of the base changes to the base change of the
coequalizer**, the morphism of finite étale covers of `X` whose invertibility is the fourth
assertion of Stacks Tag 0BN9. -/
def coequalizerBaseChangeComparison :
    finiteEtaleCoequalizer ((finiteEtaleBaseChange f).map a) ((finiteEtaleBaseChange f).map b) ⟶
      (finiteEtaleBaseChange f).obj (finiteEtaleCoequalizer a b) :=
  (isColimit_finiteEtaleCofork ((finiteEtaleBaseChange f).map a)
    ((finiteEtaleBaseChange f).map b)).desc
      (Cofork.ofπ ((finiteEtaleBaseChange f).map (finiteEtaleCoequalizerπ a b))
        (baseChange_comp_coequalizerπ f a b))

/-- The comparison morphism composed with the projection onto the coequalizer of the base changes
is the base change of the projection onto the coequalizer. -/
theorem coequalizerπ_comp_comparison :
    finiteEtaleCoequalizerπ ((finiteEtaleBaseChange f).map a) ((finiteEtaleBaseChange f).map b) ≫
        coequalizerBaseChangeComparison f a b =
      (finiteEtaleBaseChange f).map (finiteEtaleCoequalizerπ a b) :=
  Cofork.IsColimit.π_desc (isColimit_finiteEtaleCofork _ _)

/-- Under `finiteEtalePushforwardFunctor X`, the image of the opposite of the comparison morphism
followed by that of the opposite of the projection onto the coequalizer of the base changes is the
image of the opposite of the base change of the projection onto the coequalizer. -/
theorem map_op_comparison_comp :
    (finiteEtalePushforwardFunctor X).map (coequalizerBaseChangeComparison f a b).op ≫
        (finiteEtalePushforwardFunctor X).map (finiteEtaleCoequalizerπ
          ((finiteEtaleBaseChange f).map a) ((finiteEtaleBaseChange f).map b)).op =
      (finiteEtalePushforwardFunctor X).map
        ((finiteEtaleBaseChange f).map (finiteEtaleCoequalizerπ a b)).op := by
  rw [← Functor.map_comp, ← op_comp, coequalizerπ_comp_comparison]

/-- The image of the base-changed cofork under taking sections over an open of `X` is a cofork. -/
theorem sections_condition {V : X.Opens} :
    (quasicoherentSectionsFunctor X V).map ((finiteEtalePushforwardFunctor X).map
        ((finiteEtaleBaseChange f).map (finiteEtaleCoequalizerπ a b)).op) ≫
      (quasicoherentSectionsFunctor X V).map ((finiteEtalePushforwardFunctor X).map
        ((finiteEtaleBaseChange f).map a).op) =
    (quasicoherentSectionsFunctor X V).map ((finiteEtalePushforwardFunctor X).map
        ((finiteEtaleBaseChange f).map (finiteEtaleCoequalizerπ a b)).op) ≫
      (quasicoherentSectionsFunctor X V).map ((finiteEtalePushforwardFunctor X).map
        ((finiteEtaleBaseChange f).map b).op) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← op_comp, ← op_comp, baseChange_comp_coequalizerπ]

/-- **The sections over an affine open of `X` of the base-changed cofork are an equalizer.** This
is `Stacks.FundamentalGroup.isLimitForkOfIsPushoutFiniteEtale` fed with the three pushout squares
of `Stacks.FundamentalGroup.isPushout_app_pullback` and the three naturality squares of
`Stacks.FundamentalGroup.appLE_fst_naturality`. -/
def isLimitForkSectionsBaseChange {V : S.Opens} (hV : IsAffineOpen V)
    {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) :
    IsLimit (Fork.ofι _ (sections_condition f a b (V := W))) := by
  have hpres := preservesLimit_parallelPair_quasicoherentSectionsFunctor
    ((finiteEtalePushforwardFunctor S).map a.op) ((finiteEtalePushforwardFunctor S).map b.op) V
  have hS := (isLimitMapConeForkEquiv (quasicoherentSectionsFunctor S V)
      (map_op_finiteEtaleCoequalizerπ_comp a b))
    (isLimitOfPreserves (quasicoherentSectionsFunctor S V)
      (isLimitForkMapOpFiniteEtaleCoequalizerπ a b))
  refine isLimitForkOfIsPushoutFiniteEtale (f.appLE V W hWV) _ hS
    (finiteEtale_app Z hV) (finiteEtale_app Y hV) _
    (isPushout_app_pullback f (finiteEtaleCoequalizer a b).hom hV hW hWV
      (hV.preimage _) (snd_preimage_le_fst_preimage f _ hWV))
    (isPushout_app_pullback f Z.hom hV hW hWV (hV.preimage _)
      (snd_preimage_le_fst_preimage f Z hWV))
    (isPushout_app_pullback f Y.hom hV hW hWV (hV.preimage _)
      (snd_preimage_le_fst_preimage f Y hWV)) ?_ ?_ ?_
  · rw [quasicoherentSectionsFunctor_map_pushforward,
      quasicoherentSectionsFunctor_map_pushforward]
    exact (appLE_fst_naturality f (finiteEtaleCoequalizerπ a b) _ _ _ _).symm
  · rw [quasicoherentSectionsFunctor_map_pushforward,
      quasicoherentSectionsFunctor_map_pushforward]
    exact (appLE_fst_naturality f a _ _ _ _).symm
  · rw [quasicoherentSectionsFunctor_map_pushforward,
      quasicoherentSectionsFunctor_map_pushforward]
    exact (appLE_fst_naturality f b _ _ _ _).symm

/-- The comparison is an isomorphism on sections over an affine open of `X` lying over an affine
open of `S`: both the base-changed cofork and the cofork of the coequalizer of the base changes
are equalizers of the same pair there, and the comparison is a morphism between them. -/
theorem isIso_sections_comparison {V : S.Opens} (hV : IsAffineOpen V) {W : X.Opens}
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) :
    IsIso ((quasicoherentSectionsFunctor X W).map
      ((finiteEtalePushforwardFunctor X).map (coequalizerBaseChangeComparison f a b).op)) := by
  have hpres := preservesLimit_parallelPair_quasicoherentSectionsFunctor
    ((finiteEtalePushforwardFunctor X).map ((finiteEtaleBaseChange f).map a).op)
    ((finiteEtalePushforwardFunctor X).map ((finiteEtaleBaseChange f).map b).op) W
  have hXX := (isLimitMapConeForkEquiv (quasicoherentSectionsFunctor X W)
      (map_op_finiteEtaleCoequalizerπ_comp ((finiteEtaleBaseChange f).map a)
        ((finiteEtaleBaseChange f).map b)))
    (isLimitOfPreserves (quasicoherentSectionsFunctor X W)
      (isLimitForkMapOpFiniteEtaleCoequalizerπ ((finiteEtaleBaseChange f).map a)
        ((finiteEtaleBaseChange f).map b)))
  have h1 := isLimitForkSectionsBaseChange f a b hV hW hWV
  have heq : (quasicoherentSectionsFunctor X W).map
        ((finiteEtalePushforwardFunctor X).map (coequalizerBaseChangeComparison f a b).op) =
      (h1.conePointUniqueUpToIso hXX).hom := by
    refine Fork.IsLimit.hom_ext hXX ?_
    have h := IsLimit.conePointUniqueUpToIso_hom_comp h1 hXX WalkingParallelPair.zero
    rw [Fork.app_zero_eq_ι, Fork.app_zero_eq_ι] at h
    rw [h, Fork.ι_ofι, Fork.ι_ofι, ← Functor.map_comp, map_op_comparison_comp]
  rw [heq]
  infer_instance

/-- **The base change of the coequalizer of two morphisms of finite étale covers is the
coequalizer of their base changes.** This is the content of the fourth assertion of Stacks Tag
0BN9: the comparison `Stacks.FundamentalGroup.coequalizerBaseChangeComparison` is an
isomorphism.

It is an isomorphism of quasi-coherent algebras on `X` because it is one on sections over every
affine open of `X` lying over an affine open of `S`, and those form a basis; the pushforward
functor on finite étale covers and the inclusion of the quasi-coherent algebras are fully
faithful, so they reflect it back to an isomorphism of covers. -/
theorem isIso_comparison : IsIso (coequalizerBaseChangeComparison f a b) := by
  have h : ∀ p : compatibleAffineOpens f,
      IsIso ((quasicoherentSectionsFunctor X (p.1.1 : X.Opens)).map
        ((finiteEtalePushforwardFunctor X).map
          (coequalizerBaseChangeComparison f a b).op)) :=
    fun p ↦ isIso_sections_comparison f a b p.1.2.2 p.1.1.2 p.2
  have hsh : IsIso (((IsQuasicoherentAlgebra X).ι.map ((finiteEtalePushforwardFunctor X).map
      (coequalizerBaseChangeComparison f a b).op)).right) := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_compatibleAffineOpens f) ?_
    intro i
    have h2 := h i
    exact (CategoryTheory.Under.forget Γ(X, (i.1.1 : X.Opens))).map_isIso
      ((quasicoherentSectionsFunctor X (i.1.1 : X.Opens)).map
        ((finiteEtalePushforwardFunctor X).map (coequalizerBaseChangeComparison f a b).op))
  have h3 : IsIso ((CategoryTheory.Under.forget X.sheaf).map
      ((IsQuasicoherentAlgebra X).ι.map ((finiteEtalePushforwardFunctor X).map
        (coequalizerBaseChangeComparison f a b).op))) := hsh
  have h4 : IsIso ((IsQuasicoherentAlgebra X).ι.map ((finiteEtalePushforwardFunctor X).map
      (coequalizerBaseChangeComparison f a b).op)) :=
    isIso_of_reflects_iso _ (CategoryTheory.Under.forget X.sheaf)
  have h5 : IsIso ((finiteEtalePushforwardFunctor X).map
      (coequalizerBaseChangeComparison f a b).op) :=
    isIso_of_reflects_iso _ (IsQuasicoherentAlgebra X).ι
  have h6 : IsIso (coequalizerBaseChangeComparison f a b).op :=
    isIso_of_reflects_iso _ (finiteEtalePushforwardFunctor X)
  exact isIso_of_op _

/-- **Base change preserves the coequalizer of two morphisms of finite étale covers.** -/
instance preservesColimit_parallelPair_finiteEtaleBaseChange :
    PreservesColimit (parallelPair a b) (finiteEtaleBaseChange f) := by
  have hiso := isIso_comparison f a b
  refine preservesColimit_of_preserves_colimit_cocone (isColimit_finiteEtaleCofork a b) ?_
  refine (isColimitMapCoconeCoforkEquiv (finiteEtaleBaseChange f)
    (comp_finiteEtaleCoequalizerπ a b)).symm ?_
  exact IsColimit.ofIsoColimit (isColimit_finiteEtaleCofork ((finiteEtaleBaseChange f).map a)
      ((finiteEtaleBaseChange f).map b))
    (Cofork.ext (asIso (coequalizerBaseChangeComparison f a b))
      (coequalizerπ_comp_comparison f a b))

end Comparison

/-! ### The fourth assertion of Stacks Tag 0BN9 -/

/-- **Base change preserves all coequalizers of finite étale covers.** -/
instance preservesColimitsOfShape_walkingParallelPair_finiteEtaleBaseChange
    {S X : Scheme.{u}} (f : X ⟶ S) :
    PreservesColimitsOfShape WalkingParallelPair (finiteEtaleBaseChange f) :=
  ⟨fun {K} ↦ preservesColimit_of_iso_diagram _ (diagramIsoParallelPair K).symm⟩

/-- **Stacks 0BN9, the fourth assertion: base change of finite étale covers preserves finite
colimits.**

Finite colimits of `FÉt_S` are generated by its finite coproducts, which base change preserves by
`Stacks.FundamentalGroup.preservesFiniteCoproducts_finiteEtaleBaseChange`, and its coequalizers,
which it preserves by
`Stacks.FundamentalGroup.preservesColimitsOfShape_walkingParallelPair_finiteEtaleBaseChange`. -/
-- Tag 0BN9 is split over FOUR
-- declarations; this is the fourth, and the second -- the fpqc-local description of the
-- coequalizers, the extra field of `HasFiniteColimitsWithLocalCoequalizers` -- is still open.
-- The attribute below covers only this part of 0BN9, as its note says; the tag as a whole
-- is not formalized until the second part is.
@[stacks 0BN9 "base change preserves finite colimits"]
theorem preservesFiniteColimits_finiteEtaleBaseChange {S X : Scheme.{u}} (f : X ⟶ S) :
    PreservesFiniteColimits (finiteEtaleBaseChange f) :=
  preservesFiniteColimits_finiteEtaleBaseChange_of_preservesCoequalizers f

end Stacks.FundamentalGroup

end
