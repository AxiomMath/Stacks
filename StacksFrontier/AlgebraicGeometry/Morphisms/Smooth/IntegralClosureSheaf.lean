module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.IntegralClosure
public import StacksCore.Tactic.StacksAttribute

/-!
# Integral closure and smooth pullback, as an equality of subsheaves

Let `g : Y ⟶ S` be a smooth morphism of schemes, let `𝒜` be a quasi-coherent sheaf of
`𝒪_S`-algebras and let `𝒜' ⊆ 𝒜` be the integral closure of `𝒪_S` in `𝒜`. This file proves that
`g^*𝒜'` is the integral closure of `𝒪_Y` in `g^*𝒜` as an equality of subsheaves of `g^*𝒜`, over
every open of `Y`.

For an affine `f : X ⟶ S` the quasi-coherent algebra `𝒜 = f_* 𝒪_X` has
`𝒜' = (f.fromNormalization)_* 𝒪_{f.normalization}`: over an affine open `U` both have as
sections the integral closure of `Γ(S, U)` in `Γ(X, f⁻¹U)`
(`AlgebraicGeometry.Scheme.Hom.normalizationObjIso` and
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.range_integralClosureAlgebraι_app_of_isAffineOpen`),
and two subsheaves of a sheaf agreeing on a basis agree everywhere. Normalization commutes with
smooth base change (`AlgebraicGeometry.Scheme.Hom.normalizationPullback`), so the integral closure
of `𝒪_Y` in `g^*𝒜 = (X ×_S Y)_* 𝒪` is the direct image of the structure sheaf of
`f.normalization ×_S Y`, which is `g^*𝒜'` by `isIso_baseChangeAlgebraHom_fromNormalization`.

## Main results

* `mem_range_app_of_locally`, `range_app_eq_of_isBasis`, `injective_app_of_isBasis`: a
  monomorphic subsheaf of a sheaf of rings is determined by its sections on a basis of opens.
* `range_integralClosureAlgebraι_app_eq_range_normalizationAlgebraι_app`: for `f` affine the
  integral closure of `𝒪_S` in `f_* 𝒪_X` is `(f.fromNormalization)_* 𝒪`, over every open of `S`.
* `range_integralClosureAlgebraι_app_pullback_eq`: for `g` smooth and `f` affine, the integral
  closure of `𝒪_Y` in `g^*(f_* 𝒪_X)` is the pullback of the integral closure of `𝒪_S` in
  `f_* 𝒪_X`, as an equality of subsheaves.
* `isIso_baseChangeAlgebraHom_self` and `isIso_baseChangeAlgebraHom_fromNormalization`: the
  ambient algebra of that equality is the pullback `g^*𝒜`, and its right-hand side is `g^*𝒜'`.
* `range_integralClosureAlgebraι_app_pullback_relativeSpec_eq`: the same for an arbitrary
  quasi-coherent `𝒪_S`-algebra, entered through its relative spectrum.

## Implementation notes

A subsheaf is recorded as a morphism of sheaves whose components are injective, and equality of
two subsheaves as equality of the ranges of their components, as for
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.integralClosureAlgebraι`.

The quasi-coherent algebra is presented as `f_* 𝒪_X` for `f` affine, and the pullback as a
direct image from a fibre product; every quasi-coherent algebra is `f_* 𝒪_X` for the structure
morphism of its relative spectrum (`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`).

## References

* [Stacks Project, Tag 081K](https://stacks.math.columbia.edu/tag/081K)
* [Stacks Project, Tag 03GG](https://stacks.math.columbia.edu/tag/03GG)
* [Stacks Project, Tag 03GV](https://stacks.math.columbia.edu/tag/03GV)
* [Stacks Project, Tag 035F](https://stacks.math.columbia.edu/tag/035F)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence AlgebraicGeometry.Scheme.QuasicoherentAlgebra

universe u

namespace Stacks.IntegralClosure.SheafLevel

section Gluing

variable {Z : TopCat.{u}} {F G : TopCat.Sheaf CommRingCat.{u} Z}

/-- A morphism of sheaves commutes with restriction, elementwise. -/
private theorem app_map_apply (φ : F ⟶ G) {A B : Opens Z} (k : A ⟶ B)
    (c : F.presheaf.obj (op B)) :
    φ.hom.app (op A) (F.presheaf.map k.op c) = G.presheaf.map k.op (φ.hom.app (op B) c) := by
  rw [← ConcreteCategory.comp_apply, φ.hom.naturality k.op, ConcreteCategory.comp_apply]

/-- The opens of a basis contained in `W` cover `W`. -/
private theorem le_iSup_of_isBasis {B : Set (Opens Z)} (hB : Opens.IsBasis B) (W : Opens Z) :
    W ≤ iSup (fun V : {V : Opens Z // V ∈ B ∧ V ≤ W} => V.1) := by
  intro x hx
  obtain ⟨V, hVB, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  exact Opens.mem_iSup.mpr ⟨⟨V, hVB, hVW⟩, hxV⟩

/-- A section lying locally in the range of a morphism of sheaves with injective components
lies in its range. -/
public theorem mem_range_app_of_locally (φ : F ⟶ G)
    (hinj : ∀ V : Opens Z, Function.Injective (φ.hom.app (op V)))
    {ι : Type*} {W : Opens Z} (V : ι → Opens Z) (hVW : ∀ i, V i ≤ W) (hcov : W ≤ iSup V)
    (s : G.presheaf.obj (op W))
    (hs : ∀ i, G.presheaf.map (homOfLE (hVW i)).op s ∈ Set.range (φ.hom.app (op (V i)))) :
    s ∈ Set.range (φ.hom.app (op W)) := by
  choose t ht using hs
  have key : ∀ (i : ι) {A : Opens Z} (k : A ⟶ V i),
      φ.hom.app (op A) (F.presheaf.map k.op (t i)) =
        G.presheaf.map (homOfLE (k.le.trans (hVW i))).op s := by
    intro i A k
    rw [app_map_apply, ht i, ← ConcreteCategory.comp_apply, ← G.presheaf.map_comp]
    rfl
  have hcompat : F.presheaf.IsCompatible V t := by
    intro i j
    apply hinj (V i ⊓ V j)
    rw [key i (Opens.infLELeft (V i) (V j)), key j (Opens.infLERight (V i) (V j))]
  obtain ⟨u, hu, -⟩ := TopCat.Sheaf.existsUnique_gluing' F V W (fun i => homOfLE (hVW i)) hcov
    t hcompat
  refine ⟨u, TopCat.Sheaf.eq_of_locally_eq' G V W (fun i => homOfLE (hVW i)) hcov _ s ?_⟩
  intro i
  rw [← app_map_apply, hu i, ht i]

/-- Two subsheaves of a sheaf — morphisms with injective components — whose ranges agree on a
family of opens that is a basis agree on every open. -/
public theorem range_app_eq_of_isBasis {F₁ F₂ : TopCat.Sheaf CommRingCat.{u} Z}
    (φ₁ : F₁ ⟶ G) (φ₂ : F₂ ⟶ G)
    (h₁ : ∀ V : Opens Z, Function.Injective (φ₁.hom.app (op V)))
    (h₂ : ∀ V : Opens Z, Function.Injective (φ₂.hom.app (op V)))
    {B : Set (Opens Z)} (hB : Opens.IsBasis B)
    (hBr : ∀ V ∈ B, Set.range (φ₁.hom.app (op V)) = Set.range (φ₂.hom.app (op V)))
    (W : Opens Z) :
    Set.range (φ₁.hom.app (op W)) = Set.range (φ₂.hom.app (op W)) := by
  have main : ∀ {H₁ H₂ : TopCat.Sheaf CommRingCat.{u} Z} (ψ₁ : H₁ ⟶ G) (ψ₂ : H₂ ⟶ G),
      (∀ V : Opens Z, Function.Injective (ψ₂.hom.app (op V))) →
      (∀ V ∈ B, Set.range (ψ₁.hom.app (op V)) ⊆ Set.range (ψ₂.hom.app (op V))) →
      Set.range (ψ₁.hom.app (op W)) ⊆ Set.range (ψ₂.hom.app (op W)) := by
    intro H₁ H₂ ψ₁ ψ₂ hinj hsub
    rintro s ⟨r, rfl⟩
    refine mem_range_app_of_locally ψ₂ hinj
      (ι := {V : Opens Z // V ∈ B ∧ V ≤ W}) (fun V => V.1) (fun V => V.2.2)
      (le_iSup_of_isBasis hB W) _ ?_
    intro V
    exact hsub V.1 V.2.1 ⟨H₁.presheaf.map (homOfLE V.2.2).op r, app_map_apply ψ₁ _ r⟩
  exact le_antisymm (main φ₁ φ₂ h₂ fun V hV => (hBr V hV).le)
    (main φ₂ φ₁ h₁ fun V hV => (hBr V hV).ge)

/-- A morphism of sheaves whose components are injective on a basis of opens has injective
components on every open. -/
public theorem injective_app_of_isBasis (φ : F ⟶ G)
    {B : Set (Opens Z)} (hB : Opens.IsBasis B)
    (hinj : ∀ V ∈ B, Function.Injective (φ.hom.app (op V)))
    (W : Opens Z) : Function.Injective (φ.hom.app (op W)) := by
  intro a b hab
  refine TopCat.Sheaf.eq_of_locally_eq' F (ι := {V : Opens Z // V ∈ B ∧ V ≤ W})
    (fun V => V.1) W (fun V => homOfLE V.2.2) (le_iSup_of_isBasis hB W) a b ?_
  intro V
  exact hinj V.1 V.2.1 (by rw [app_map_apply, app_map_apply, hab])

end Gluing

section Normalization

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]

/-- The preimage of an open of `S` under `f` is the preimage under `f.toNormalization` of its
preimage under `f.fromNormalization`. -/
public theorem preimage_toNormalization_fromNormalization (W : S.Opens) :
    f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ W) = f ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]

/-- The factorisation `X ⟶ f.normalization` of `f`, as a morphism of schemes over `S`. -/
public def normalizationOver : Over.mk f ⟶ Over.mk f.fromNormalization :=
  Over.homMk f.toNormalization f.toNormalization_fromNormalization

/-- The canonical map of `𝒪_S`-algebras `(f.fromNormalization)_* 𝒪 ⟶ f_* 𝒪_X` induced by
`f.toNormalization`. -/
public def normalizationAlgebraι :
    pushforwardAlgebra f.fromNormalization ⟶ pushforwardAlgebra f :=
  pushforwardAlgebraMap (normalizationOver f)

/-- The sections of `normalizationAlgebraι` over an open `W` of `S` are the map on sections
induced by `f.toNormalization`. -/
public theorem normalizationAlgebraι_app (W : S.Opens) :
    (normalizationAlgebraι f).right.hom.app (op W) =
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ W) (f ⁻¹ᵁ W)
        (preimage_toNormalization_fromNormalization f W).ge :=
  pushforwardAlgebraMap_app (normalizationOver f) W _

/-- Over an affine open `U` of `S` the sections of `normalizationAlgebraι` are, under the
identification `Scheme.Hom.normalizationObjIso`, the inclusion of the integral closure of
`Γ(S, U)` in `Γ(X, f⁻¹U)`. -/
public theorem normalizationAlgebraι_app_apply {U : S.Opens} (hU : IsAffineOpen U)
    (t : (pushforwardAlgebra f.fromNormalization).right.presheaf.obj (op U)) :
    letI := (f.app U).hom.toAlgebra
    (normalizationAlgebraι f).right.hom.app (op U) t =
      (((f.normalizationObjIso hU).hom t : integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)) :
        Γ(X, f ⁻¹ᵁ U)) := by
  let := (f.app U).hom.toAlgebra
  rw [normalizationAlgebraι_app f U, ← Scheme.Hom.normalizationObjIso_hom_val f hU]
  rfl

/-- `normalizationAlgebraι` is injective on sections over every open. -/
public theorem injective_normalizationAlgebraι_app (W : S.Opens) :
    Function.Injective ((normalizationAlgebraι f).right.hom.app (op W)) := by
  refine injective_app_of_isBasis _ S.isBasis_affineOpens (fun U hU => ?_) W
  intro a b hab
  rw [normalizationAlgebraι_app_apply f hU, normalizationAlgebraι_app_apply f hU] at hab
  exact (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom).1
    (Subtype.ext hab)

/-- The integral closure of `𝒪_S` in the quasi-coherent algebra `f_* 𝒪_X` is the direct image of
the structure sheaf of the relative normalization of `f`: the two subsheaves of `f_* 𝒪_X` have
the same sections over every open of `S`. -/
public theorem range_integralClosureAlgebraι_app_eq_range_normalizationAlgebraι_app
    [IsAffineHom f] (W : S.Opens) :
    Set.range ((integralClosureAlgebraι (pushforwardAlgebra f)).right.hom.app (op W)) =
      Set.range ((normalizationAlgebraι f).right.hom.app (op W)) := by
  have hqc : (underlyingModule (pushforwardAlgebra f)).IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra f
  refine range_app_eq_of_isBasis _ _ (fun V => injective_integralClosureAlgebraι_app _ V)
    (injective_normalizationAlgebraι_app f) S.isBasis_affineOpens (fun U hU => ?_) W
  rw [range_integralClosureAlgebraι_app_of_isAffineOpen _ U hU]
  let := (f.app U).hom.toAlgebra
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso
      (f.normalizationObjIso hU).hom).2 (⟨x, hx⟩ : integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))
    exact ⟨t, (normalizationAlgebraι_app_apply f hU t).trans (congrArg Subtype.val ht)⟩
  · rintro ⟨t, rfl⟩
    exact Set.mem_of_eq_of_mem (normalizationAlgebraι_app_apply f hU t)
      ((f.normalizationObjIso hU).hom t).2

end Normalization

section Functoriality

variable {S : Scheme.{u}}

/-- The sections of the canonical map on pushed-forward structure sheaves attached to an
isomorphism of schemes over `S` are surjective. -/
public theorem surjective_pushforwardAlgebraMap_app_of_isIso {A B : Over S} (h : A ⟶ B)
    [IsIso h] (W : S.Opens) :
    Function.Surjective ((pushforwardAlgebraMap h).right.hom.app (op W)) := by
  intro y
  have hid : pushforwardAlgebraMap (inv h) ≫ pushforwardAlgebraMap h =
      𝟙 (pushforwardAlgebra A.hom) := by
    rw [← pushforwardAlgebraMap_comp h (inv h), IsIso.hom_inv_id, pushforwardAlgebraMap_id]
  refine ⟨(pushforwardAlgebraMap (inv h)).right.hom.app (op W) y, ?_⟩
  exact congrArg (fun φ : pushforwardAlgebra A.hom ⟶ pushforwardAlgebra A.hom =>
    (Under.Hom.right φ).hom.app (op W) y) hid

/-- Precomposing with a map that is surjective on sections over `W` does not change the range
on sections over `W`. -/
public theorem range_comp_right_app {A B C : Under S.sheaf} (φ : A ⟶ B) (ψ : B ⟶ C)
    (W : S.Opens) (hφ : Function.Surjective (φ.right.hom.app (op W))) :
    Set.range ((φ ≫ ψ).right.hom.app (op W)) = Set.range (ψ.right.hom.app (op W)) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨φ.right.hom.app (op W) t, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := hφ t
    exact ⟨u, rfl⟩

end Functoriality

section SmoothBaseChange

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [Smooth g]

/-- The base change `f.normalization ×_S Y ⟶ Y` of the relative normalization of `f`, receiving
the relative normalization of the base change of `f`. -/
public def normalizationPullbackOver :
    Over.mk (pullback.snd f g).fromNormalization ⟶
      Over.mk (pullback.snd f.fromNormalization g) :=
  Over.homMk (f.normalizationPullback g) (Scheme.Hom.normalizationPullback_snd f g)

/-- **Normalization commutes with smooth base change**:
`AlgebraicGeometry.Scheme.Hom.normalizationPullback` is an isomorphism in `Over Y`. -/
@[ega "IV 6.14.4" "partial"]
public instance isIso_normalizationPullbackOver : IsIso (normalizationPullbackOver f g) :=
  (isIso_iff_of_reflects_iso (normalizationPullbackOver f g) (Over.forget Y)).mp
    (by change IsIso (f.normalizationPullback g); infer_instance)

/-- The canonical morphism `X ×_S Y ⟶ f.normalization ×_S Y` of schemes over `Y`. -/
public def toBaseChangeNormalizationOver :
    Over.mk (pullback.snd f g) ⟶ Over.mk (pullback.snd f.fromNormalization g) :=
  Over.homMk ((pullback.snd f g).toNormalization ≫ f.normalizationPullback g) (by simp)

omit [Smooth g] in
/-- `toBaseChangeNormalizationOver` factors through the relative normalization of the base
change, followed by `normalizationPullbackOver`. -/
public theorem toBaseChangeNormalizationOver_eq :
    toBaseChangeNormalizationOver f g =
      normalizationOver (pullback.snd f g) ≫ normalizationPullbackOver f g := by
  ext : 1
  rfl

/-- The comparison map of `𝒪_Y`-algebras from the direct image of the structure sheaf of
`f.normalization ×_S Y` — the base change of the integral closure of `𝒪_S` in `f_* 𝒪_X` — into
`(X ×_S Y)_* 𝒪`. -/
public def baseChangeNormalizationAlgebraι :
    pushforwardAlgebra (pullback.snd f.fromNormalization g) ⟶
      pushforwardAlgebra (pullback.snd f g) :=
  pushforwardAlgebraMap (toBaseChangeNormalizationOver f g)

/-- The sections over an open `W` of `Y` of the base-changed normalization are those of the
relative normalization of the base change: the two presentations of `g^*𝒜'` agree. -/
public theorem range_baseChangeNormalizationAlgebraι_app (W : Y.Opens) :
    Set.range ((baseChangeNormalizationAlgebraι f g).right.hom.app (op W)) =
      Set.range ((normalizationAlgebraι (pullback.snd f g)).right.hom.app (op W)) := by
  rw [baseChangeNormalizationAlgebraι, toBaseChangeNormalizationOver_eq,
    pushforwardAlgebraMap_comp]
  exact range_comp_right_app _ _ W
    (surjective_pushforwardAlgebraMap_app_of_isIso (normalizationPullbackOver f g) W)

/-- Let `g : Y ⟶ S` be a smooth morphism, let `𝒜 = f_* 𝒪_X` be a quasi-coherent sheaf of
`𝒪_S`-algebras with `f : X ⟶ S` affine, and let `𝒜' ⊆ 𝒜` be the integral closure of `𝒪_S` in
`𝒜`. Then `g^*𝒜'` is the integral closure of `𝒪_Y` in `g^*𝒜`: inside `g^*𝒜 = (X ×_S Y)_* 𝒪`,
the two subsheaves have the same sections over every open `W` of `Y`. Here `𝒜'` is presented as
`(f.fromNormalization)_* 𝒪`, by
`range_integralClosureAlgebraι_app_eq_range_normalizationAlgebraι_app`, and its pullback as the
direct image of the structure sheaf of `f.normalization ×_S Y`, which is `g^*𝒜'` by
`isIso_baseChangeAlgebraHom_fromNormalization`. -/
@[stacks 081K "the equality of subsheaves, over an arbitrary open of `Y`. The quasi-coherent
algebra is presented as `f_* 𝒪_X` for `f` affine rather than as an abstract quasi-coherent
algebra, and the pullback as a direct image from a fibre product rather than through
`algebraPullback`; the latter two agree by `isIso_baseChangeAlgebraHom_fromNormalization`, and
the integral-closure subalgebra `𝒜'` is identified with the relative normalization by
`range_integralClosureAlgebraι_app_eq_range_normalizationAlgebraι_app`. The affine-open
comparison map, which is where Stacks 03GG is consumed, is
`Stacks.IntegralClosure.SmoothPullback.bijective_toIntegralClosure_sections`. Transport of the
integral-closure subalgebra along an isomorphism of algebra sheaves, which removes the
presentation of `𝒜` as `f_* 𝒪_X`, is
`Stacks.IntegralClosure.SheafLevel.image_range_integralClosureAlgebraι_app`, and the resulting
presentation-free form of this clause is
`Stacks.IntegralClosure.SheafLevel.range_integralClosureAlgebraι_app_algebraPullback_eq`. See
the module docstring.",
  ega "IV 18.12.15", ega "IV 6.14.5" "smooth base change"]
public theorem range_integralClosureAlgebraι_app_pullback_eq [IsAffineHom f] (W : Y.Opens) :
    Set.range ((integralClosureAlgebraι
        (pushforwardAlgebra (pullback.snd f g))).right.hom.app (op W)) =
      Set.range ((baseChangeNormalizationAlgebraι f g).right.hom.app (op W)) := by
  have : IsAffineHom (pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g)
      ‹IsAffineHom f›
  rw [range_integralClosureAlgebraι_app_eq_range_normalizationAlgebraι_app (pullback.snd f g) W,
    range_baseChangeNormalizationAlgebraι_app]

omit [Smooth g] in
/-- The source of `baseChangeNormalizationAlgebraι` is the pullback `g^*𝒜'`: the canonical
base-change comparison `g^*((f.fromNormalization)_* 𝒪) ⟶ (f.normalization ×_S Y)_* 𝒪` is an
isomorphism, `f.fromNormalization` being integral and hence affine. -/
public theorem isIso_baseChangeAlgebraHom_fromNormalization :
    IsIso (baseChangeAlgebraHom g (Over.mk f.fromNormalization)) :=
  have : IsAffineHom (Over.mk f.fromNormalization).hom :=
    inferInstanceAs (IsAffineHom f.fromNormalization)
  Stacks.AlgebraPullbackQcoh.isIso_baseChangeAlgebraHom g (Over.mk f.fromNormalization)

omit [QuasiCompact f] [QuasiSeparated f] [Smooth g] in
/-- The ambient algebra of `range_integralClosureAlgebraι_app_pullback_eq` is the pullback
`g^*𝒜`: the canonical base-change comparison `g^*(f_* 𝒪_X) ⟶ (X ×_S Y)_* 𝒪` is an isomorphism
for `f` affine. -/
public theorem isIso_baseChangeAlgebraHom_self [IsAffineHom f] :
    IsIso (baseChangeAlgebraHom g (Over.mk f)) :=
  have : IsAffineHom (Over.mk f).hom := inferInstanceAs (IsAffineHom f)
  Stacks.AlgebraPullbackQcoh.isIso_baseChangeAlgebraHom g (Over.mk f)

end SmoothBaseChange

section Quasicoherent

variable {S Y : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] (g : Y ⟶ S) [Smooth g]

/-- Let `g : Y ⟶ S` be smooth and let `𝒜` be any quasi-coherent sheaf of `𝒪_S`-algebras, with
`𝒜' ⊆ 𝒜` the integral closure of `𝒪_S` in `𝒜`. Writing `X = Spec_S(𝒜)` for the relative
spectrum, so that `𝒜 ≅ (relativeSpecToBase 𝒜)_* 𝒪_X` by
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` and `g^*𝒜 ≅ (X ×_S Y)_* 𝒪` by
`isIso_baseChangeAlgebraHom_self` at `X`, the integral closure of `𝒪_Y` in `g^*𝒜` is `g^*𝒜'`:
the two subsheaves have the same sections over every open `W` of `Y`. No hypothesis is placed on
`𝒜` beyond quasi-coherence. -/
@[stacks 081K "the equality of subsheaves for an arbitrary quasi-coherent `𝒪_S`-algebra `𝒜`,
over an arbitrary open of `Y`. `𝒜` enters through its relative spectrum, so that `𝒜` itself is
`(relativeSpecToBase 𝒜)_* 𝒪` up to the isomorphism
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`. Invariance of the integral-closure
subalgebra under an isomorphism of algebra sheaves, which lets the statement be read off
`integralClosureAlgebra 𝒜` directly, is
`Stacks.IntegralClosure.SheafLevel.image_range_integralClosureAlgebraι_app`, and the resulting
statement — the equality of the subsheaves `integralClosureAlgebra (g^*𝒜)` and
`g^*(integralClosureAlgebra 𝒜)` of `g^*𝒜` — is
`Stacks.IntegralClosure.SheafLevel.range_integralClosureAlgebraι_app_algebraPullback_eq`. See
the module docstring and `range_integralClosureAlgebraι_app_pullback_eq`.", ega "IV 18.12.15"]
public theorem range_integralClosureAlgebraι_app_pullback_relativeSpec_eq (W : Y.Opens) :
    haveI : IsSeparated (relativeSpecToBase A) := IsSeparated.of_isAffineHom _
    Set.range ((integralClosureAlgebraι (pushforwardAlgebra
        (pullback.snd (relativeSpecToBase A) g))).right.hom.app (op W)) =
      Set.range ((baseChangeNormalizationAlgebraι (relativeSpecToBase A) g).right.hom.app
        (op W)) :=
  have : IsSeparated (relativeSpecToBase A) := IsSeparated.of_isAffineHom _
  range_integralClosureAlgebraι_app_pullback_eq (relativeSpecToBase A) g W

end Quasicoherent

end Stacks.IntegralClosure.SheafLevel

end
