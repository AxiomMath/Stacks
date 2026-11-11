module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.AlgebraicGeometry.Crystalline.SheafComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDeRhamNilpotentReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorLevels

/-!
# The levels of the system of [Stacks, Tag 07JN] stabilise when `p` is nilpotent on `S`

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, and let
`(X, T(n)_e, δ(n))` be the cosimplicial system of thickenings
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem`, with `T(n)_e` the spectrum
of `D(n)/(p)^{N + e}`.  If moreover `p` is nilpotent in `A = Γ(S, ⊤)`, say `p^k = 0`, then `p^k`
is zero in every `A`-algebra, in particular in every `D(n)`, so for `e ≥ k` the ideal
`(p)^{N + e}` is zero and the levels `T(n)_e` no longer change.  This file proves the
consequences of this that the comparison of [Stacks, Tag 07MW] uses.

## Main definitions

* `DividedPowerRing.isoOfBijective` — a divided power morphism which is bijective and maps the
  divided power ideal onto the divided power ideal is an isomorphism of divided power rings.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceStableLevel` — a level `k` past which
  the system is constant: the nilpotency exponent of `p` in `A`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceComponent` — the component
  `M(n) → Γ(T(n)_e, ℱ)` of the module `M(n) = lim_e Γ(T(n)_e, ℱ)` of a quasi-coherent crystal, as
  a map semilinear over `D(n) → Γ(T(n)_e, 𝒪)`, in every cosimplicial degree.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceLevelRetraction` — for `e` past the
  stable level, the map `T(n)_j ⟶ T(n)_e` through which every tower map into a level above `e`
  factors; it is what builds an element of `M(n)` from its component at `e`.

## Main results

* `...SmallSite.natCast_pow_eq_zero_wholeSpaceEnvelopeRing`,
  `...SmallSite.natCast_pow_eq_zero_wsEnvelope` — `p^{N + e} = 0` in `D(n)` and in the
  uncompleted envelope `E(n)` past the stable level.
* `...SmallSite.bijective_levelSectionsScalars` — `D(n) → Γ(T(n)_e, 𝒪)` is bijective past the
  stable level.
* `...SmallSite.isIso_wholeSpaceSystem_map` — **the tower maps `T(n)_e ⟶ T(n)_{e'}` are
  isomorphisms past the stable level.**
* `...SmallSite.isIso_limit_π_wholeSpaceSystem` — the projection of the limit over the levels of
  any abelian presheaf on `Cris(X/S)` onto a level past the stable one is an isomorphism.
* `...SmallSite.bijective_wholeSpaceComponent` — the component `M(n) → Γ(T(n)_e, ℱ)` is bijective
  past the stable level, and `...SmallSite.wholeSpaceComponent_trans` — it is natural in the
  cosimplicial direction.
* `...SmallSite.bijective_wsCompletionMap`, `...SmallSite.bijective_envLevelMap` — the envelope
  `E(n)` is its own `p`-adic completion, and `E(n) → Γ(T(n)_e, 𝒪)` is bijective past the stable
  level.

## What is and is not proved

Everything here is proved under the single extra hypothesis `hA : IsNilpotent (S.p : Γ(S, ⊤))`.
Nothing is said about the cohomology of `Cris(X/S)`, and [Stacks, Tag 07MW] itself is not proved
here; no tag attribute is placed in this file.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u v w

noncomputable section

/-! ### Bijective divided power morphisms -/

namespace DividedPowerRing

/-- **A bijective divided power morphism which maps the divided power ideal onto the divided
power ideal is an isomorphism of divided power rings**: the inverse ring map is again a divided
power morphism. -/
def isoOfBijective {R R' : DividedPowerRing.{w}} (f : R ⟶ R')
    (hf : Function.Bijective f.toRingHom) (hJ : R'.ideal ≤ R.ideal.map f.toRingHom) :
    R ≅ R' :=
  let e := RingEquiv.ofBijective f.toRingHom hf
  have he : ∀ y, e.symm (f.toRingHom y) = y := e.symm_apply_apply
  have hmem : ∀ x ∈ R'.ideal, ∃ y ∈ R.ideal, f.toRingHom y = x := fun x hx ↦
    (Ideal.mem_map_iff_of_surjective _ hf.2).1 (hJ hx)
  { hom := f
    inv := DividedPowers.DPMorphism.mk' (f := (e.symm : R' →+* R))
      { ideal_comp := Ideal.map_le_iff_le_comap.2 fun x hx ↦ by
          obtain ⟨y, hy, rfl⟩ := hmem x hx
          change e.symm (f.toRingHom y) ∈ R.ideal
          rw [he]
          exact hy
        dpow_comp := fun {n} x hx ↦ by
          obtain ⟨y, hy, rfl⟩ := hmem x hx
          change R.dividedPowers.dpow n (e.symm (f.toRingHom y)) =
            e.symm (R'.dividedPowers.dpow n (f.toRingHom y))
          rw [he, f.dpow_comp y hy, he] }
    hom_inv_id := by
      apply DividedPowers.DPMorphism.ext
      funext y
      exact he y
    inv_hom_id := by
      apply DividedPowers.DPMorphism.ext
      funext x
      exact e.apply_symm_apply x }

/-- The forward map of `DividedPowerRing.isoOfBijective` is the given morphism. -/
@[simp]
theorem isoOfBijective_hom {R R' : DividedPowerRing.{w}} (f : R ⟶ R')
    (hf : Function.Bijective f.toRingHom) (hJ : R'.ideal ≤ R.ideal.map f.toRingHom) :
    (isoOfBijective f hf hJ).hom = f := rfl

end DividedPowerRing

/-! ### Levels at which `p` already vanishes -/

namespace Crystalline

/-- If `p^k = 0` in `D`, then the ideal `(p)^k` is zero. -/
theorem pAdicIdeal_pow_eq_bot_of_pow_eq_zero {D : Type*} [CommRing D] {p k : ℕ}
    (hk : (p : D) ^ k = 0) :
    DividedPowers.pAdicIdeal (A := D) p ^ k = ⊥ := by
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, hk,
    Ideal.span_singleton_eq_bot.mpr rfl]

/-- The quotient map `D → D/(p)^k` is bijective when `p^k = 0` in `D`. -/
theorem bijective_mk_pAdicIdeal_pow {D : Type*} [CommRing D] {p k : ℕ} (hk : (p : D) ^ k = 0) :
    Function.Bijective (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := D) p ^ k)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ ?_, Ideal.Quotient.mk_surjective⟩
  rwa [Ideal.Quotient.eq_zero_iff_mem, pAdicIdeal_pow_eq_bot_of_pow_eq_zero hk, Ideal.mem_bot] at ha

variable {s : AffineCrystallineSituation.{u, u}}

/-- **The transition map of the tower of levels of a completed crystalline thickening is an
isomorphism once `p` vanishes at the smaller level.**  If `p^{k'} = 0` in the ambient ring of `X`
and `k' ≤ k`, both `X/(p)^k` and `X/(p)^{k'}` are the ambient ring itself, and the map
`X/(p)^k ⟶ X/(p)^{k'}` of the little affine crystalline site is invertible. -/
theorem isIso_levelThickeningMap_id (X : CompletedCrystallineThickening.{u, u, u} s) {k k' : ℕ}
    (h : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p k)
    (h' : IsPAdicLevel X.ring.ideal X.ring.dividedPowers s.p k') (hk : k' ≤ k)
    (hp : (s.p : X.ring) ^ k' = 0) :
    IsIso (levelThickeningMap h h' (𝟙 X) hk) := by
  have hp' : (s.p : X.ring) ^ k = 0 := pow_eq_zero_of_le hk hp
  let f : dpQuotientLevelRing s.p X.ring k h ⟶ dpQuotientLevelRing s.p X.ring k' h' :=
    levelHom s.p h h' (𝟙 X.ring) hk
  have hcomp : f.toRingHom.comp (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := X.ring) s.p ^ k))
      = Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := X.ring) s.p ^ k') := by
    ext a
    rfl
  have hbij : Function.Bijective f.toRingHom := by
    have h2 := bijective_mk_pAdicIdeal_pow hp
    rw [← hcomp, RingHom.coe_comp] at h2
    exact (Function.Bijective.of_comp_iff _ (bijective_mk_pAdicIdeal_pow hp')).1 h2
  have hJ : (dpQuotientLevelRing s.p X.ring k' h').ideal ≤
      (dpQuotientLevelRing s.p X.ring k h).ideal.map f.toRingHom := by
    change X.ring.ideal.map _ ≤ (X.ring.ideal.map _).map f.toRingHom
    rw [Ideal.map_map, hcomp]
  let e := DividedPowerThickening.isoOfRingIso (X := (levelThickening X k h).obj)
    (Y := (levelThickening X k' h').obj) (DividedPowerRing.isoOfBijective f hbij hJ)
    (levelThickeningMap h h' (𝟙 X) hk).hom.fromBase_comp
    (levelThickeningMap h h' (𝟙 X) hk).hom.toQuotient_comp
  have : IsIso ((ObjectProperty.ι (DividedPowerThickening.IsCrystalline (S := s))).map
      (levelThickeningMap h h' (𝟙 X) hk)) :=
    e.isIso_hom
  exact isIso_of_reflects_iso _ (ObjectProperty.ι (DividedPowerThickening.IsCrystalline (S := s)))

end Crystalline

/-! ### The stable level -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hA : IsNilpotent (S.p : Γ(S.S.scheme, ⊤)))

/-- **A level past which the system of [Stacks, Tag 07JN] is constant**, when `p` is nilpotent
in `A = Γ(S, ⊤)`: a nilpotency exponent `k` of `p` in `A`, so that `p^k = 0` in every
`A`-algebra. -/
def wholeSpaceStableLevel : ℕ := Classical.choose hA

/-- `p` raised to the stable level vanishes in `A = Γ(S, ⊤)`. -/
theorem natCast_pow_wholeSpaceStableLevel :
    (S.p : Γ(S.S.scheme, ⊤)) ^ wholeSpaceStableLevel hA = 0 :=
  Classical.choose_spec hA

/-- **`p` raised to any exponent past the stable level vanishes in every `A`-algebra.** -/
theorem natCast_pow_eq_zero_of_ringHom {R : Type*} [CommRing R] (f : Γ(S.S.scheme, ⊤) →+* R)
    {k : ℕ} (hk : wholeSpaceStableLevel hA ≤ k) : (S.p : R) ^ k = 0 := by
  rw [← map_natCast f, ← map_pow, pow_eq_zero_of_le hk (natCast_pow_wholeSpaceStableLevel hA),
    map_zero]

variable (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **`p^{N + e} = 0` in the uncompleted envelope `E(n)` past the stable level.** -/
theorem natCast_pow_eq_zero_wsEnvelope [IsAffine S.X] [IsAffine S.S.scheme] (n : ℕ) {e : ℕ}
    (he : wholeSpaceStableLevel hA ≤ e) :
    (S.p : wsEnvelope hp n) ^ (uniformLevel (affineSituation S hp) + e) = 0 :=
  natCast_pow_eq_zero_of_ringHom hA
    (tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
      n).structureMap.toRingHom
    (he.trans (Nat.le_add_left _ _))

/-- **`p^{N + e} = 0` in `D(n)` past the stable level.** -/
theorem natCast_pow_eq_zero_wholeSpaceEnvelopeRing [IsAffine S.X] [IsAffine S.S.scheme] (n : ℕ)
    {e : ℕ} (he : wholeSpaceStableLevel hA ≤ e) :
    (S.p : ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) ^
      (uniformLevel (affineSituation S hp) + e) = 0 :=
  natCast_pow_eq_zero_of_ringHom hA ((wsCompletionMap hp n).comp
    (tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
      n).structureMap.toRingHom)
    (he.trans (Nat.le_add_left _ _))

variable [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The scalars `D(n) → Γ(T(n)_e, 𝒪)` are bijective past the stable level**: the level
`D(n)/(p)^{N + e}` is `D(n)` itself. -/
theorem bijective_levelSectionsScalars (n : SimplexCategory) {e : ℕ}
    (he : wholeSpaceStableLevel hA ≤ e) :
    Function.Bijective (levelSectionsScalars hp n e) :=
  (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm.bijective.comp
    (bijective_mk_pAdicIdeal_pow (natCast_pow_eq_zero_wholeSpaceEnvelopeRing hA hp n.len he))

/-! ### The tower maps are isomorphisms past the stable level -/

/-- **The tower maps `T(n)_e ⟶ T(n)_{e'}` of the system of [Stacks, Tag 07JN] are isomorphisms
past the stable level.**  On the little affine site the map is the projection
`D(n)/(p)^{N + e'} ⟶ D(n)/(p)^{N + e}`, which is the identity of `D(n)` once `(p)^{N + e} = 0`;
the equivalence with `Cris(X/S)` carries isomorphisms to isomorphisms. -/
theorem isIso_wholeSpaceSystem_map (n : ℕ) {e e' : ℕ} (h : e ⟶ e')
    (he : wholeSpaceStableLevel hA ≤ e) :
    IsIso (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map h) := by
  have hX : IsIso (((affineLevelSystem (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp)).obj ⦋n⦌).map h.op) :=
    isIso_levelThickeningMap_id _ _ _ _ (natCast_pow_eq_zero_of_ringHom hA
      (tensorPowerEnvelopeThickening (affineSituation S hp) (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) n).thickening.fromBase.toRingHom
      (he.trans (Nat.le_add_left _ _)))
  change IsIso ((affineToWholeSite S hp).map
    (((affineLevelSystem (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp)).obj ⦋n⦌).map h.op)).unop
  infer_instance

/-- **The limit over the levels of an abelian presheaf on `Cris(X/S)` is its value at any level
past the stable one**: the projection `lim_e G(T(n)_e) → G(T(n)_e)` is an isomorphism, the
diagram being constant from that level on. -/
theorem isIso_limit_π_wholeSpaceSystem (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (n e : ℕ) (he : wholeSpaceStableLevel hA ≤ e) :
    IsIso (limit.π ((((wholeSpaceSystem S hp).obj (op ⦋n⦌)).op ⋙ G)) (op e)) := by
  have hconst : (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).op ⋙ G).IsEventuallyConstantTo (op e) :=
    fun i f ↦ by
      have := isIso_wholeSpaceSystem_map hA hp n f.unop he
      change IsIso (G.map (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map f.unop).op)
      infer_instance
  exact hconst.isIso_π_of_isLimit (limit.isLimit _)

/-! ### The components of `M(n)` -/

variable (Fc : QuasiCoherentCrystal S)

/-- **The component `M(n) → Γ(T(n)_e, ℱ)` of the module `M(n) = lim_e Γ(T(n)_e, ℱ)`** of a
quasi-coherent crystal, in any cosimplicial degree `n`, as a map semilinear over the scalars
`D(n) → Γ(T(n)_e, 𝒪)` of `...SmallSite.levelSectionsScalars`.  In degree `⦋0⦌` it is
`...SmallSite.pairComponent`. -/
def wholeSpaceComponent (n : SimplexCategory) (e : ℕ) :
    wholeSpaceSections hp Fc n →ₛₗ[levelSectionsScalars hp n e]
      Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) where
  toFun m := wholeSpaceSectionsVal hp Fc m e
  map_add' x y := wholeSpaceSectionsVal_add hp Fc x y e
  map_smul' r m := wholeSpaceSectionsVal_smul hp Fc r m e

/-- The component of `m ∈ M(n)` at the level `e` is `...SmallSite.wholeSpaceSectionsVal`. -/
@[simp]
theorem wholeSpaceComponent_apply (n : SimplexCategory) (e : ℕ)
    (m : wholeSpaceSections hp Fc n) :
    wholeSpaceComponent hp Fc n e m = wholeSpaceSectionsVal hp Fc m e := rfl

/-- **The components are natural in the cosimplicial direction**: the component of the
transition of `x` is the restriction of the component of `x`. -/
theorem wholeSpaceComponent_trans {m n : SimplexCategory} (φ : m ⟶ n) (e : ℕ)
    (x : wholeSpaceSections hp Fc m) :
    wholeSpaceComponent hp Fc n e (wholeSpaceSectionsTrans hp Fc φ x) =
      Fc.obj.val.map (wholeSpaceTrans hp φ e).op (wholeSpaceComponent hp Fc m e x) :=
  rfl

/-! ### The component is bijective past the stable level -/

/-- The tower maps `T(n)_e ⟶ T(n)_{e'}` are isomorphisms past the stable level, in a degree given
as an object of the simplex category. -/
theorem isIso_wholeSpaceSystem_map' (n : SimplexCategory) {e e' : ℕ} (h : e ⟶ e')
    (he : wholeSpaceStableLevel hA ≤ e) :
    IsIso (((wholeSpaceSystem S hp).obj (op n)).map h) :=
  isIso_wholeSpaceSystem_map hA hp n.len h he

/-- **The map `T(n)_j ⟶ T(n)_e` to a level `e` past the stable one**: the tower map to the level
`max j e` followed by the inverse of the tower map `T(n)_e ⟶ T(n)_{max j e}`, which is an
isomorphism.  For `j ≤ e` it is the tower map, and for `j = e` the identity. -/
def wholeSpaceLevelRetraction (n : SimplexCategory) {e : ℕ} (he : wholeSpaceStableLevel hA ≤ e)
    (j : ℕ) :
    ((wholeSpaceSystem S hp).obj (op n)).obj j ⟶ ((wholeSpaceSystem S hp).obj (op n)).obj e :=
  haveI := isIso_wholeSpaceSystem_map' hA hp n (homOfLE (le_max_right j e)) he
  ((wholeSpaceSystem S hp).obj (op n)).map (homOfLE (le_max_left j e)) ≫
    inv (((wholeSpaceSystem S hp).obj (op n)).map (homOfLE (le_max_right j e)))

/-- `wholeSpaceLevelRetraction` followed by any tower map out of `T(n)_e` is the tower map. -/
theorem wholeSpaceLevelRetraction_comp_map (n : SimplexCategory) {e : ℕ}
    (he : wholeSpaceStableLevel hA ≤ e) {j M : ℕ} (h₁ : j ⟶ M) (h₂ : e ⟶ M) :
    wholeSpaceLevelRetraction hA hp n he j ≫ ((wholeSpaceSystem S hp).obj (op n)).map h₂ =
      ((wholeSpaceSystem S hp).obj (op n)).map h₁ := by
  have hM : max j e ≤ M := max_le (leOfHom h₁) (leOfHom h₂)
  have e₁ : h₁ = homOfLE (le_max_left j e) ≫ homOfLE hM := Subsingleton.elim _ _
  have e₂ : h₂ = homOfLE (le_max_right j e) ≫ homOfLE hM := Subsingleton.elim _ _
  have := isIso_wholeSpaceSystem_map' hA hp n (homOfLE (le_max_right j e)) he
  rw [e₁, e₂, Functor.map_comp, Functor.map_comp, wholeSpaceLevelRetraction, Category.assoc,
    IsIso.inv_hom_id_assoc]

/-- **`wholeSpaceLevelRetraction` is the only map that factors a tower map through the tower map
out of `T(n)_e`**, the latter being an isomorphism. -/
theorem eq_wholeSpaceLevelRetraction (n : SimplexCategory) {e : ℕ}
    (he : wholeSpaceStableLevel hA ≤ e) {j M : ℕ} (h₁ : j ⟶ M) (h₂ : e ⟶ M)
    (g : ((wholeSpaceSystem S hp).obj (op n)).obj j ⟶ ((wholeSpaceSystem S hp).obj (op n)).obj e)
    (hg : g ≫ ((wholeSpaceSystem S hp).obj (op n)).map h₂ =
      ((wholeSpaceSystem S hp).obj (op n)).map h₁) :
    g = wholeSpaceLevelRetraction hA hp n he j := by
  have := isIso_wholeSpaceSystem_map' hA hp n h₂ he
  rw [← cancel_mono (((wholeSpaceSystem S hp).obj (op n)).map h₂), hg,
    wholeSpaceLevelRetraction_comp_map]

/-- The map `wholeSpaceLevelRetraction` from the level `e` itself is the identity. -/
theorem wholeSpaceLevelRetraction_self (n : SimplexCategory) {e : ℕ}
    (he : wholeSpaceStableLevel hA ≤ e) :
    wholeSpaceLevelRetraction hA hp n he e = 𝟙 _ :=
  (eq_wholeSpaceLevelRetraction hA hp n he (𝟙 e) (𝟙 e) _ (Category.id_comp _)).symm

/-- The maps `wholeSpaceLevelRetraction` are compatible with the tower maps. -/
theorem map_comp_wholeSpaceLevelRetraction (n : SimplexCategory) {e : ℕ}
    (he : wholeSpaceStableLevel hA ≤ e) {a b : ℕ} (h : a ⟶ b) :
    ((wholeSpaceSystem S hp).obj (op n)).map h ≫ wholeSpaceLevelRetraction hA hp n he b =
      wholeSpaceLevelRetraction hA hp n he a := by
  refine eq_wholeSpaceLevelRetraction hA hp n he
    (homOfLE ((leOfHom h).trans (le_max_left b e))) (homOfLE (le_max_right b e)) _ ?_
  rw [Category.assoc, wholeSpaceLevelRetraction_comp_map (h₁ := homOfLE (le_max_left b e)),
    ← Functor.map_comp]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **The component `M(n) → Γ(T(n)_e, ℱ)` is bijective past the stable level**: every tower map
past `e` is an isomorphism, so a compatible family of sections over the levels is determined by,
and can be built from, its section over `T(n)_e`. -/
theorem bijective_wholeSpaceComponent (n : SimplexCategory) {e : ℕ}
    (he : wholeSpaceStableLevel hA ≤ e) :
    Function.Bijective (wholeSpaceComponent hp Fc n e) := by
  refine ⟨fun m m' hmm ↦ wholeSpaceSectionsVal_injective hp Fc fun j ↦ ?_, fun x ↦ ?_⟩
  · have hM : wholeSpaceSectionsVal hp Fc m (max j e) =
        wholeSpaceSectionsVal hp Fc m' (max j e) := by
      have := isIso_wholeSpaceSystem_map' hA hp n (homOfLE (le_max_right j e)) he
      refine (PresheafOfModules.bijective_map_of_isIso Fc.obj.val
        (((wholeSpaceSystem S hp).obj (op n)).map (homOfLE (le_max_right j e))).op).1 ?_
      rw [wholeSpaceSectionsVal_restrict, wholeSpaceSectionsVal_restrict]
      exact hmm
    rw [← wholeSpaceSectionsVal_restrict hp Fc m (homOfLE (le_max_left j e)),
      ← wholeSpaceSectionsVal_restrict hp Fc m' (homOfLE (le_max_left j e)), hM]
  · refine ⟨wholeSpaceSectionsMk hp Fc
      (fun j ↦ Fc.obj.val.map (wholeSpaceLevelRetraction hA hp n he j).op x) ?_, ?_⟩
    · intro a b h
      rw [← PresheafOfModules.map_comp_apply]
      exact PresheafOfModules.congr_map_apply Fc.obj.val
        (by rw [← op_comp, map_comp_wholeSpaceLevelRetraction]) x
    · change Fc.obj.val.map (wholeSpaceLevelRetraction hA hp n he e).op x = x
      have hρ : (wholeSpaceLevelRetraction hA hp n he e).op = 𝟙 _ := by
        rw [wholeSpaceLevelRetraction_self, op_id]
      exact (PresheafOfModules.congr_map_apply Fc.obj.val hρ x).trans
        (PresheafOfModules.map_id_apply_self Fc.obj.val x)

/-! ### The envelope `E(n)` is its own completion -/

omit [IsAffine S.X] [IsAffine S.S.scheme] in
include hA in
/-- **The envelope `E(n)` is its own `p`-adic completion** when `p` is nilpotent in `A`: the map
`E(n) → D(n)` is bijective, every `E(n)`-module being `p`-adically complete. -/
theorem bijective_wsCompletionMap (n : ℕ) : Function.Bijective (wsCompletionMap hp n) := by
  have hc := isAdicComplete_of_pow_eq_zero (p := S.p) (D := wsEnvelope hp n)
    ⟨_, natCast_pow_eq_zero_of_ringHom hA
      (tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
        n).structureMap.toRingHom le_rfl⟩ (wsEnvelope hp n)
  have hb := (AdicCompletion.of_bijective_iff (I := DividedPowers.pAdicIdeal
    (A := wsEnvelope hp n) S.p) (M := wsEnvelope hp n)).2 hc
  have hx (x : wsEnvelope hp n) : wsCompletionMap hp n x = AdicCompletion.of _ _ x := rfl
  refine ⟨fun a b hab ↦ hb.1 ((hx a).symm.trans (hab.trans (hx b))), fun y ↦ ?_⟩
  · obtain ⟨x, hxy⟩ := hb.2 y
    exact ⟨x, (hx x).trans hxy⟩

/-- **The reduction `E(n) → Γ(T(n)_e, 𝒪)` is bijective past the stable level.** -/
theorem bijective_envLevelMap (n : ℕ) {e : ℕ} (he : wholeSpaceStableLevel hA ≤ e) :
    Function.Bijective (envLevelMap hp n e) :=
  (bijective_levelSectionsScalars hA hp ⦋n⦌ he).comp (bijective_wsCompletionMap hA hp n)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
