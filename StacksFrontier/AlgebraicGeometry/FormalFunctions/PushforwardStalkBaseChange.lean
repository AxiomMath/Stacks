module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs

/-!
# The stalk of a pushforward is the functions on the base change to the spectrum of the stalk

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, let `y` be a point of
`Y`, write `A = 𝒪_{Y,y}` and let

  `X' = X ×_Y Spec 𝒪_{Y,y}`

be the base change of `f` along `Y.fromSpecStalk y`, with projections `q : X' ⟶ X` and
`g : X' ⟶ Spec 𝒪_{Y,y}`. This file proves that the canonical map

  `(f_* 𝒪_X)_y ⟶ Γ(X', 𝒪_{X'})`,

which carries the germ at `y` of a function on `f ⁻¹ᵁ U` to its pullback along `q`, is an
isomorphism of `𝒪_{Y,y}`-modules.

Both sides are localisations of one and the same ring. Choose an affine open `U₀ ∋ y` and put
`R = Γ(Y, U₀)` and `B = Γ(X, f ⁻¹ᵁ U₀)`; let `𝔭 ⊆ R` be the prime of `y`. Then

* `(f_* 𝒪_X)_y` is the localisation of `B` at the image of `R ∖ 𝔭`, which is
  `AlgebraicGeometry.Scheme.pushforwardStalk_isLocalization`;
* `Γ(X', 𝒪_{X'})` is the pushout of `B ← R → Γ(Spec 𝒪_{Y,y}, ⊤)` — this is Mathlib's
  `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, applicable because
  `Y.fromSpecStalk y` is flat (`AlgebraicGeometry.flat_fromSpecStalk`), `U₀` and the whole of
  `Spec 𝒪_{Y,y}` are affine, and `f ⁻¹ᵁ U₀` is quasi-compact and quasi-separated — and
  `Γ(Spec 𝒪_{Y,y}, ⊤)` is the localisation of `R` at `R ∖ 𝔭`
  (`AlgebraicGeometry.isLocalization_sections_fromSpecStalk`), so that pushout is again the
  localisation of `B` at the image of `R ∖ 𝔭`, by
  `Algebra.isLocalization_iff_isPushout`.

Two localisations of one module at one submonoid are uniquely isomorphic, and the comparison is
linear over `𝒪_{Y,y}` because `𝒪_{Y,y}` is a localisation of `R`.

## Main definitions

* `Stacks.FormalFunctions.pullbackFromSpecStalkAlgebra`: `Γ(X ×_Y Spec 𝒪_{Y,y}, ⊤)` as an
  `𝒪_{Y,y}`-algebra, scalars acting through the identification of `𝒪_{Y,y}` with the global
  functions on its spectrum followed by the second projection.

## Main results

* `Stacks.FormalFunctions.top_le_preimage_pullbackFst`: the whole of `X ×_Y Spec 𝒪_{Y,y}` lies
  over `f ⁻¹ᵁ U` for every open neighbourhood `U` of `y`. This is what makes the pullback of a
  section of `𝒪_X` over `f ⁻¹ᵁ U` a *global* function on the base change.
* `Stacks.FormalFunctions.exists_linearEquiv_pushforwardStalk_appTop_pullback`: **the
  comparison together with its normalisation.** There is an `𝒪_{Y,y}`-linear isomorphism
  `Γ(X ×_Y Spec 𝒪_{Y,y}, ⊤) ≅ (f_* 𝒪_X)_y` carrying the pullback of a section of `𝒪_X` over
  `f ⁻¹ᵁ U`, for *any* open neighbourhood `U` of `y`, to its germ at `y`. The normalisation is
  what identifies the isomorphism as the canonical comparison rather than as some isomorphism of
  the two sides.
* `Stacks.FormalFunctions.exists_appLE_eq_of_appTop_pullback`: the surjectivity half, in the
  shape its consumers carry. A global function on `X ×_Y Spec 𝒪_{Y,y}` is the pullback of a
  section of `𝒪_X` over `f ⁻¹ᵁ U` for some open neighbourhood `U` of `y`.

## Implementation notes

The `𝒪_{Y,y}`-algebra structure on `Γ(X ×_Y Spec 𝒪_{Y,y}, ⊤)` is a restriction of scalars, so it
is not an instance; it is supplied as a `letI` in the statement, as in
`StacksFrontier/AlgebraicGeometry/PullbackSections/Stalk.lean`. The comparison is stated as an
existential together with its normalisation rather than as a definition plus a `simp` lemma, for
the same reason as there: the type carries that module structure as a `let`, and a `let`-headed
function type is not seen through by the coercion to a function.

The normalisation is proved first for a neighbourhood `W ≤ U₀` of `y`, where `U₀` is the affine
open the two localisation statements are taken at, and then for an arbitrary neighbourhood `U` by
restricting to `U ⊓ U₀`. The step at `W` is not immediate from the step at `U₀`, because a
section over `f ⁻¹ᵁ W` need not be the restriction of a section over `f ⁻¹ᵁ U₀`: it is obtained
by writing its germ as a fraction `b / m` with `b ∈ Γ(X, f ⁻¹ᵁ U₀)` and `m ∈ Γ(Y, U₀) ∖ 𝔭`,
transporting the resulting identity of germs to `Γ(X ×_Y Spec 𝒪_{Y,y}, ⊤)` along the open on
which it already holds, and cancelling the unit `m`.

Several facts are stated twice, once with the morphism applied through `CommRingCat.Hom.hom` and
once through `algebraMap`: the two are definitionally equal, but `rw` matches syntactically, so
the bridging equation `hbridge` of the proof is needed to pass between them.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.FormalFunctions

variable {X Y : Scheme.{u}}

/-- **The whole of `X ×_Y Spec 𝒪_{Y,y}` lies over `f ⁻¹ᵁ U` for every open neighbourhood `U` of
`y`.** Through the second projection the base change lies over `Spec 𝒪_{Y,y}`, which lies over
`U` by `AlgebraicGeometry.le_preimage_fromSpecStalk_of_mem`; the two routes around the cartesian
square agree. Consequently the pullback of a section of `𝒪_X` over `f ⁻¹ᵁ U` is a global function
on the base change. -/
public theorem top_le_preimage_pullbackFst (f : X ⟶ Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    (⊤ : (Limits.pullback f (Y.fromSpecStalk y)).Opens) ≤
      Limits.pullback.fst f (Y.fromSpecStalk y) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro z _
  have hz : ((Limits.pullback.snd f (Y.fromSpecStalk y) ≫ Y.fromSpecStalk y).base z) ∈ U :=
    AlgebraicGeometry.le_preimage_fromSpecStalk_of_mem y U hy (Set.mem_univ _)
  rw [← Limits.pullback.condition] at hz
  exact hz

/-- The global functions on the base change `X ×_Y Spec 𝒪_{Y,y}`, as an `𝒪_{Y,y}`-algebra:
scalars act through the identification of `𝒪_{Y,y}` with the global functions on its spectrum,
followed by the second projection. -/
@[instance_reducible]
public noncomputable def pullbackFromSpecStalkAlgebra (f : X ⟶ Y) (y : Y) :
    Algebra (Y.presheaf.stalk y) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
  ((Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv ≫
      (Limits.pullback.snd f (Y.fromSpecStalk y)).appLE ⊤ ⊤
        (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top _ ⊤)).hom.toAlgebra

/-- **The stalk of `f_* 𝒪_X` at `y` is the ring of global functions on the base change
`X ×_Y Spec 𝒪_{Y,y}`, together with the normalisation of the comparison.** For `f` quasi-compact
and quasi-separated there is an `𝒪_{Y,y}`-linear isomorphism

  `Γ(X ×_Y Spec 𝒪_{Y,y}, 𝒪) ≅ (f_* 𝒪_X)_y`

carrying the pullback along the first projection of a section of `𝒪_X` over `f ⁻¹ᵁ U`, for an
open neighbourhood `U` of `y`, to the germ of that section at `y`. The normalisation is what
makes this usable: it identifies the isomorphism as the canonical comparison rather than as some
isomorphism of the two sides, and it holds for *every* neighbourhood `U`, not only for the affine
one the proof is run at. -/
public theorem exists_linearEquiv_pushforwardStalk_appTop_pullback
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (y : Y) :
    letI := pullbackFromSpecStalkAlgebra f y
    ∃ e : Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) ≃ₗ[Y.presheaf.stalk y]
        pushforwardStalkModule f y,
      ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)),
        e ((Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U) ⊤
            (top_le_preimage_pullbackFst f y U hy) s) =
          pushforwardStalkGerm f y U hy s := by
  let := pullbackFromSpecStalkAlgebra f y
  obtain ⟨U₀, hU₀, hy₀, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := y) (U := (⊤ : Y.Opens))
      (TopologicalSpace.Opens.mem_top y)
  -- the cartesian square and the opens it is read on
  have H : IsPullback (Limits.pullback.fst f (Y.fromSpecStalk y))
      (Limits.pullback.snd f (Y.fromSpecStalk y)) f (Y.fromSpecStalk y) :=
    IsPullback.of_hasPullback f (Y.fromSpecStalk y)
  have hUST : (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ≤ Y.fromSpecStalk y ⁻¹ᵁ U₀ :=
    AlgebraicGeometry.le_preimage_fromSpecStalk_of_mem y U₀ hy₀
  have hqle : (⊤ : (Limits.pullback f (Y.fromSpecStalk y)).Opens) ≤
      Limits.pullback.fst f (Y.fromSpecStalk y) ⁻¹ᵁ (f ⁻¹ᵁ U₀) :=
    top_le_preimage_pullbackFst f y U₀ hy₀
  have hkle : (⊤ : (Limits.pullback f (Y.fromSpecStalk y)).Opens) ≤
      Limits.pullback.snd f (Y.fromSpecStalk y) ⁻¹ᵁ (⊤ : (Spec (Y.presheaf.stalk y)).Opens) :=
    Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top _ ⊤
  have hUY : (⊤ : (Limits.pullback f (Y.fromSpecStalk y)).Opens) =
      Limits.pullback.fst f (Y.fromSpecStalk y) ⁻¹ᵁ (f ⁻¹ᵁ U₀) ⊓
        Limits.pullback.snd f (Y.fromSpecStalk y) ⁻¹ᵁ (⊤ : (Spec (Y.presheaf.stalk y)).Opens) :=
    le_antisymm (le_inf hqle hkle) le_top
  have : Flat (Y.fromSpecStalk y) := AlgebraicGeometry.flat_fromSpecStalk Y y
  have hiso : IsIso (pushoutSection H hUST (show f ⁻¹ᵁ U₀ ≤ f ⁻¹ᵁ U₀ from le_rfl) hUY) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUST
      (show f ⁻¹ᵁ U₀ ≤ f ⁻¹ᵁ U₀ from le_rfl) hUY hU₀ (isAffineOpen_top _)
      (f.isCompact_preimage hU₀.isCompact) (f.isQuasiSeparated_preimage hU₀.isQuasiSeparated)
  -- the scalar structures on the four rings of the square
  let algRB : Algebra Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀) := (f.app U₀).hom.toAlgebra
  let algRA' : Algebra Γ(Y, U₀) Γ(Spec (Y.presheaf.stalk y), ⊤) :=
    ((Y.fromSpecStalk y).appLE U₀ ⊤ hUST).hom.toAlgebra
  let algBC : Algebra Γ(X, f ⁻¹ᵁ U₀) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
    ((Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle).hom.toAlgebra
  let algA'C : Algebra Γ(Spec (Y.presheaf.stalk y), ⊤)
      Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
    ((Limits.pullback.snd f (Y.fromSpecStalk y)).appLE ⊤ ⊤ hkle).hom.toAlgebra
  let algRC : Algebra Γ(Y, U₀) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
    (f.app U₀ ≫
      (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle).hom.toAlgebra
  have towerRBC : IsScalarTower Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀)
      Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the square, read on sections
  have hcong : ∀ (g₁ g₂ : Limits.pullback f (Y.fromSpecStalk y) ⟶ Y) (_ : g₁ = g₂)
      (e₁ : (⊤ : (Limits.pullback f (Y.fromSpecStalk y)).Opens) ≤ g₁ ⁻¹ᵁ U₀)
      (e₂ : (⊤ : (Limits.pullback f (Y.fromSpecStalk y)).Opens) ≤ g₂ ⁻¹ᵁ U₀),
      g₁.appLE U₀ ⊤ e₁ = g₂.appLE U₀ ⊤ e₂ := by
    rintro g₁ g₂ rfl e₁ e₂
    rfl
  have hsq : f.app U₀ ≫
      (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle =
      (Y.fromSpecStalk y).appLE U₀ ⊤ hUST ≫
        (Limits.pullback.snd f (Y.fromSpecStalk y)).appLE ⊤ ⊤ hkle := by
    rw [← Scheme.Hom.appLE_eq_app f (U := U₀), Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact hcong _ _ Limits.pullback.condition _ _
  have hsq' : ∀ r : Γ(Y, U₀),
      algebraMap Γ(Y, U₀) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) r
        = ((Limits.pullback.snd f (Y.fromSpecStalk y)).appLE ⊤ ⊤ hkle)
            (((Y.fromSpecStalk y).appLE U₀ ⊤ hUST) r) := fun r =>
    (ConcreteCategory.congr_hom hsq r).trans (CommRingCat.comp_apply _ _ r)
  have towerRA'C : IsScalarTower Γ(Y, U₀) Γ(Spec (Y.presheaf.stalk y), ⊤)
      Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
    IsScalarTower.of_algebraMap_eq hsq'
  have hlocA' : IsLocalization (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl
      Γ(Spec (Y.presheaf.stalk y), ⊤) :=
    AlgebraicGeometry.isLocalization_sections_fromSpecStalk y hU₀ hy₀
  -- the functions on the base change are the pushout, hence the localisation
  have hpush : Algebra.IsPushout Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀)
      Γ(Spec (Y.presheaf.stalk y), ⊤) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    rw [show CommRingCat.ofHom (algebraMap Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀))
          = f.appLE U₀ (f ⁻¹ᵁ U₀) le_rfl from by rw [Scheme.Hom.appLE_eq_app]; rfl,
      show CommRingCat.ofHom (algebraMap Γ(Y, U₀) Γ(Spec (Y.presheaf.stalk y), ⊤))
          = (Y.fromSpecStalk y).appLE U₀ ⊤ hUST from rfl,
      show CommRingCat.ofHom
            (algebraMap Γ(X, f ⁻¹ᵁ U₀) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤))
          = (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle from rfl,
      show CommRingCat.ofHom (algebraMap Γ(Spec (Y.presheaf.stalk y), ⊤)
            Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤))
          = (Limits.pullback.snd f (Y.fromSpecStalk y)).appLE ⊤ ⊤ hkle from rfl]
    exact (isIso_pushoutSection_iff H hUST (show f ⁻¹ᵁ U₀ ≤ f ⁻¹ᵁ U₀ from le_rfl) hUY).mp hiso
  have hlocC : IsLocalization
      (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U₀)
        (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl)
      Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
    (Algebra.isLocalization_iff_isPushout (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl
      Γ(Spec (Y.presheaf.stalk y), ⊤)).mpr hpush
  -- the stalk of the pushforward is the same localisation
  let algBD : Algebra Γ(X, f ⁻¹ᵁ U₀) (pushforwardStalkModule f y) :=
    (((f.base _* X.presheaf).germ U₀ y hy₀).hom).toAlgebra
  let algRD : Algebra Γ(Y, U₀) (pushforwardStalkModule f y) :=
    (f.app U₀ ≫ (f.base _* X.presheaf).germ U₀ y hy₀).hom.toAlgebra
  have towerRBD : IsScalarTower Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀) (pushforwardStalkModule f y) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hlocD : IsLocalization
      (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U₀)
        (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl)
      (pushforwardStalkModule f y) :=
    AlgebraicGeometry.Scheme.pushforwardStalk_isLocalization f U₀ hU₀ y hy₀
  -- the local ring acts on both sides through `Γ(Y, U₀)`
  let algRA : Algebra Γ(Y, U₀) (Y.presheaf.stalk y) := (Y.presheaf.germ U₀ y hy₀).hom.toAlgebra
  have hlocA : IsLocalization.AtPrime (Y.presheaf.stalk y)
      (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal := hU₀.isLocalization_stalk ⟨y, hy₀⟩
  have hgerm : ∀ r : Γ(Y, U₀),
      (toPushforwardStalk f y).hom ((Y.presheaf.germ U₀ y hy₀).hom r)
        = ((f.base _* X.presheaf).germ U₀ y hy₀).hom ((f.app U₀).hom r) := fun r =>
    (CommRingCat.comp_apply _ _ r).symm.trans ((ConcreteCategory.congr_hom
      (TopCat.Presheaf.stalkFunctor_map_germ (C := CommRingCat.{u}) U₀ y hy₀ f.c) r).trans
        (CommRingCat.comp_apply _ _ r))
  have towerRAC : IsScalarTower Γ(Y, U₀) (Y.presheaf.stalk y)
      Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [hsq' r, AlgebraicGeometry.fromSpecStalk_appLE_top_apply y hy₀ r]
      exact (CommRingCat.comp_apply _ _ _).symm
  have towerRAD : IsScalarTower Γ(Y, U₀) (Y.presheaf.stalk y) (pushforwardStalkModule f y) := by
    refine ⟨fun r a d => ?_⟩
    change (toPushforwardStalk f y).hom ((Y.presheaf.germ U₀ y hy₀).hom r * a) * d
      = (f.app U₀ ≫ (f.base _* X.presheaf).germ U₀ y hy₀).hom r *
        ((toPushforwardStalk f y).hom a * d)
    rw [map_mul, mul_assoc, hgerm r, CommRingCat.comp_apply]
  -- the comparison of the two localisations
  have ilmC : IsLocalizedModule (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl
      (IsScalarTower.toAlgHom Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀)
        Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hlocC
  have ilmD : IsLocalizedModule (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl
      (IsScalarTower.toAlgHom Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀)
        (pushforwardStalkModule f y)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hlocD
  obtain ⟨e, he0⟩ : ∃ e : Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) ≃ₗ[Y.presheaf.stalk y]
      pushforwardStalkModule f y,
      ∀ b : Γ(X, f ⁻¹ᵁ U₀),
        e (algebraMap Γ(X, f ⁻¹ᵁ U₀) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) b)
          = algebraMap Γ(X, f ⁻¹ᵁ U₀) (pushforwardStalkModule f y) b :=
    ⟨(IsLocalizedModule.linearEquiv (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl
        (IsScalarTower.toAlgHom Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀)
          Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤)).toLinearMap
        (IsScalarTower.toAlgHom Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀)
          (pushforwardStalkModule f y)).toLinearMap).extendScalarsOfIsLocalization
      (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl (Y.presheaf.stalk y),
      fun b => IsLocalizedModule.linearEquiv_apply _ _ _ b⟩
  -- `e` is linear over `Γ(Y, U₀)`, the local ring being a localisation of it
  have hlin : ∀ (r : Γ(Y, U₀)) (c : Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤)),
      e (r • c) = r • e c := by
    intro r c
    rw [← IsScalarTower.algebraMap_smul (Y.presheaf.stalk y) r c, map_smul,
      IsScalarTower.algebraMap_smul]
  -- the two spellings of the structure map
  have hbridge : ∀ z : Γ(X, f ⁻¹ᵁ U₀),
      algebraMap Γ(X, f ⁻¹ᵁ U₀) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤) z
        = (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle z :=
    fun _ => rfl
  -- the two sides are compatible with restriction
  have hres : ∀ (V W : Y.Opens) (hVW : V ≤ W) (hyV : y ∈ V) (hyW : y ∈ W) (z : Γ(X, f ⁻¹ᵁ W)),
      (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ V) ⊤
            (top_le_preimage_pullbackFst f y V hyV)
          (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hVW)).op z)
        = (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ W) ⊤
            (top_le_preimage_pullbackFst f y W hyW) z := by
    intro V W hVW hyV hyW z
    have h := ConcreteCategory.congr_hom (Scheme.Hom.map_appLE
      (Limits.pullback.fst f (Y.fromSpecStalk y))
      (top_le_preimage_pullbackFst f y V hyV)
      (homOfLE (Scheme.Hom.preimage_mono f hVW)).op) z
    rw [CommRingCat.comp_apply] at h
    exact h
  have hgres : ∀ (V W : Y.Opens) (hVW : V ≤ W) (hyV : y ∈ V) (hyW : y ∈ W) (z : Γ(X, f ⁻¹ᵁ W)),
      pushforwardStalkGerm f y V hyV
          (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hVW)).op z)
        = pushforwardStalkGerm f y W hyW z := fun V W hVW hyV hyW z =>
    (f.base _* X.presheaf).germ_res_apply (homOfLE hVW) y hyV z
  have hgmul : ∀ (W : Y.Opens) (hyW : y ∈ W) (z w : Γ(X, f ⁻¹ᵁ W)),
      pushforwardStalkGerm f y W hyW (z * w)
        = pushforwardStalkGerm f y W hyW z * pushforwardStalkGerm f y W hyW w :=
    fun W hyW z w => map_mul ((f.base _* X.presheaf).germ W y hyW).hom z w
  -- the normalisation, first on a neighbourhood contained in `U₀`
  have key : ∀ (W : Y.Opens) (hyW : y ∈ W) (hWU₀ : W ≤ U₀) (t : Γ(X, f ⁻¹ᵁ W)),
      e ((Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ W) ⊤
          (top_le_preimage_pullbackFst f y W hyW) t)
        = pushforwardStalkGerm f y W hyW t := by
    intro W hyW hWU₀ t
    obtain ⟨⟨b, m⟩, hbm⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U₀)
        (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal.primeCompl)
      (pushforwardStalkGerm f y W hyW t)
    obtain ⟨r, hrS, hrm⟩ := m.2
    -- the identity `hbm`, read on `W`
    have hgW : pushforwardStalkGerm f y W hyW
          (t * X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hWU₀)).op
            (m : Γ(X, f ⁻¹ᵁ U₀)))
        = pushforwardStalkGerm f y W hyW
          (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hWU₀)).op b) := by
      rw [hgmul, hgres W U₀ hWU₀ hyW hy₀ (m : Γ(X, f ⁻¹ᵁ U₀)), hgres W U₀ hWU₀ hyW hy₀ b]
      exact hbm
    obtain ⟨V, hyV, i₁, i₂, hV⟩ := (f.base _* X.presheaf).germ_eq y hyW hyW
      (t * X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hWU₀)).op (m : Γ(X, f ⁻¹ᵁ U₀)))
      (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hWU₀)).op b) hgW
    have hV' : X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f i₁.le)).op
          (t * X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hWU₀)).op
            (m : Γ(X, f ⁻¹ᵁ U₀)))
        = X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f i₂.le)).op
          (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f hWU₀)).op b) := hV
    -- the same identity in the global functions on the base change
    have hC : (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ W) ⊤
            (top_le_preimage_pullbackFst f y W hyW) t *
          (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle
            (m : Γ(X, f ⁻¹ᵁ U₀))
        = (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle b := by
      rw [← hres W U₀ hWU₀ hyW hy₀ (m : Γ(X, f ⁻¹ᵁ U₀)), ← hres W U₀ hWU₀ hyW hy₀ b, ← map_mul,
        ← hres V W i₁.le hyV hyW, ← hres V W i₂.le hyV hyW]
      exact congrArg _ hV'
    -- transport along `e` and cancel the unit `m`
    refine (IsLocalization.map_units (pushforwardStalkModule f y) m).mul_left_cancel ?_
    have hsm : (r : Γ(Y, U₀)) •
          ((Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ W) ⊤
            (top_le_preimage_pullbackFst f y W hyW) t)
        = (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U₀) ⊤ hqle b := by
      rw [Algebra.smul_def, mul_comm, ← hC, IsScalarTower.algebraMap_apply Γ(Y, U₀)
        Γ(X, f ⁻¹ᵁ U₀) Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤), hrm, hbridge]
    have hD := hlin r ((Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ W) ⊤
      (top_le_preimage_pullbackFst f y W hyW) t)
    rw [hsm, ← hbridge b, he0 b, Algebra.smul_def,
      IsScalarTower.algebraMap_apply Γ(Y, U₀) Γ(X, f ⁻¹ᵁ U₀) (pushforwardStalkModule f y),
      hrm] at hD
    rw [← hD, ← hbm]
    exact mul_comm _ _
  -- an arbitrary neighbourhood, by restricting to its intersection with `U₀`
  refine ⟨e, fun U hy s => ?_⟩
  have hyW : y ∈ U ⊓ U₀ := ⟨hy, hy₀⟩
  rw [← hres (U ⊓ U₀) U inf_le_left hyW hy s, ← hgres (U ⊓ U₀) U inf_le_left hyW hy s]
  exact key (U ⊓ U₀) hyW inf_le_right _

/-- **A global function on the base change `X ×_Y Spec 𝒪_{Y,y}` is the pullback of a section of
`𝒪_X` over `f ⁻¹ᵁ U` for some open neighbourhood `U` of `y`.** This is the surjectivity half of
`Stacks.FormalFunctions.exists_linearEquiv_pushforwardStalk_appTop_pullback`: the comparison
carries the pullback of a section to its germ, every element of the stalk `(f_* 𝒪_X)_y` is a germ
by `Stacks.FormalFunctions.exists_pushforwardStalkGerm_eq`, and the comparison is injective. -/
public theorem exists_appLE_eq_of_appTop_pullback
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (y : Y)
    (a : Γ(Limits.pullback f (Y.fromSpecStalk y), ⊤)) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (s : Γ(X, f ⁻¹ᵁ U)),
      (Limits.pullback.fst f (Y.fromSpecStalk y)).appLE (f ⁻¹ᵁ U) ⊤
        (top_le_preimage_pullbackFst f y U hy) s = a := by
  obtain ⟨e, he⟩ := exists_linearEquiv_pushforwardStalk_appTop_pullback f y
  obtain ⟨U, hy, s, hs⟩ := exists_pushforwardStalkGerm_eq f y (e a)
  exact ⟨U, hy, s, e.injective ((he U hy s).trans hs)⟩

end Stacks.FormalFunctions

end
