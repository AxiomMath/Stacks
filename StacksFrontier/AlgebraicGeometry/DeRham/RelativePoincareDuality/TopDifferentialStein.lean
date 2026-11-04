module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TopDifferentialAssembly
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.StructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.CancelEtale

/-!
# The top de Rham differential and the Stein factorization over an affine base

Let `g : Y ⟶ Spec A` be proper, surjective and smooth of relative dimension `n`, and let
`B = Γ(Y, 𝒪_Y)`. The morphism `g` factors as `Y ⟶ Spec B ⟶ Spec A`, the Stein factorization of
`g` over the affine base `Spec A` ([Stacks, Tag 03H2]); `A ⟶ B` is étale by [Stacks, Tag 0G8H],
so `Y ⟶ Spec B` is again proper, surjective and smooth of relative dimension `n`
([Stacks, Tag 0G80]), and `Ω_{Y/A} = Ω_{Y/B}` compatibly with the de Rham differentials
([Stacks, Tag 0FLV]). The vanishing of `d : H^n(Y, Ω^{n-1}) ⟶ H^n(Y, Ω^n)` for `Y/A` is therefore
the same statement for `Y/B`, where moreover `B ⟶ Γ(Y, 𝒪_Y)` is bijective.

## Main results

* `AlgebraicGeometry.Scheme.Hom.rightDerived_map_deRham_d_comp_etale_eq_zero_iff`: the de Rham
  differential of `a ≫ t` and that of `a` induce the same map on cohomology up to isomorphism, for
  `t` étale; one vanishes exactly when the other does.
* `AlgebraicGeometry.smoothOfRelativeDimension_of_comp_of_etale`: if `f ≫ g` is smooth of relative
  dimension `n` and `g` is étale, then `f` is smooth of relative dimension `n`.
* `AlgebraicGeometry.Scheme.surjective_toSpecΓ`: for `Y ⟶ Spec A` proper, the canonical morphism
  `Y ⟶ Spec Γ(Y, 𝒪_Y)` is surjective.
* `AlgebraicGeometry.TopDegreeDifferential.rightDerived_map_deRham_d_eq_zero_of_isIso_appTop`:
  the reduction of the vanishing of the top de Rham differential on top cohomology to the case
  where `A ⟶ Γ(Y, 𝒪_Y)` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Cohomology.SupportedComplexes (abelianRestrictOpen)
open Stacks.AffineAlgebraEquivalence (pushforwardAlgebra)

universe u

namespace AlgebraicGeometry

/-- **Relative dimension cancels along an étale morphism.** If `f ≫ g` is smooth of relative
dimension `n` and `g` is étale, then `f` is smooth of relative dimension `n`: `f` is the graph
`X ⟶ X ×_Z Y`, a base change of the diagonal of `g` and hence an open immersion, followed by the
base change of `f ≫ g` along `g`. -/
theorem smoothOfRelativeDimension_of_comp_of_etale {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Y)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n (f ≫ g)] [Etale g] :
    SmoothOfRelativeDimension n f := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  let gr : X ⟶ pullback (f ≫ g) g := pullback.lift (𝟙 X) f (by simp)
  have hfac : f = gr ≫ pullback.snd _ _ := (pullback.lift_snd _ _ _).symm
  have : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback f g) inferInstance
  have : SmoothOfRelativeDimension n (pullback.snd (f ≫ g) g) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
      (IsPullback.of_hasPullback (f ≫ g) g) inferInstance
  have h := smoothOfRelativeDimension_comp (n := 0) (m := n) gr (pullback.snd (f ≫ g) g)
  rwa [zero_add, ← hfac] at h

/-- A morphism `g : Y ⟶ Spec A` factors as `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec A`. -/
private theorem Scheme.toSpecΓ_comp_Spec_map_appTop {Y : Scheme.{u}} {A : CommRingCat.{u}}
    (g : Y ⟶ Spec A) :
    Y.toSpecΓ ≫ Spec.map g.appTop ≫ Spec.map (Scheme.ΓSpecIso A).inv = g := by
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- If `g : Y ⟶ Spec A` is proper, then so is `Y ⟶ Spec Γ(Y, 𝒪_Y)`. -/
private theorem isProper_toSpecΓ {Y : Scheme.{u}} {A : CommRingCat.{u}} (g : Y ⟶ Spec A)
    [IsProper g] : IsProper Y.toSpecΓ := by
  have hfac := (Scheme.toSpecΓ_comp_Spec_map_appTop g).symm
  have : IsProper (Y.toSpecΓ ≫ (Spec.map g.appTop ≫ Spec.map (Scheme.ΓSpecIso A).inv)) :=
    hfac ▸ inferInstance
  exact IsProper.of_comp _ (Spec.map g.appTop ≫ Spec.map (Scheme.ΓSpecIso A).inv)

/-- **The morphism to the spectrum of the global functions is surjective, for a proper
morphism to an affine scheme.** Its scheme-theoretic image is everything, since its kernel is
zero, and its image is closed. -/
theorem Scheme.surjective_toSpecΓ {Y : Scheme.{u}} {A : CommRingCat.{u}} (g : Y ⟶ Spec A)
    [IsProper g] : Surjective Y.toSpecΓ := by
  have : CompactSpace Y := (quasiCompact_iff_compactSpace g).1 inferInstance
  have := isProper_toSpecΓ g
  have hdense : closure (Set.range Y.toSpecΓ.base) = Set.univ := by
    rw [← Scheme.Hom.support_ker, Scheme.ker_toSpecΓ]
    rfl
  rw [Y.toSpecΓ.isClosedMap.isClosed_range.closure_eq] at hdense
  exact ⟨Set.range_eq_univ.1 hdense⟩

namespace Scheme.Hom

variable {X S S' : Scheme.{u}}

/-- For a morphism `a : X ⟶ S` and an étale `t : S ⟶ S'`, the forms of `a ≫ t`, restricted to the
open subscheme `⊤` of `X`, are the forms of `⊤ ⟶ X ⟶ S`. -/
theorem isIso_relativeDifferentialFormsMap_top_comp_etale (a : X ⟶ S) (t : S ⟶ S') [Etale t]
    (n : ℤ) :
    IsIso (relativeDifferentialFormsMap (⊤ : X.Opens).ι (a ≫ t) ((⊤ : X.Opens).ι ≫ a) t
      (Category.assoc _ _ _).symm n) :=
  isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ n

/-- **The de Rham differential on cohomology is insensitive to an étale change of base.** For
`a : X ⟶ S` and `t : S ⟶ S'` étale, the de Rham differential `Ω^p_{X/S'} ⟶ Ω^{p+1}_{X/S'}` of
`a ≫ t` induces zero on `H^q(X, -)` exactly when that of `a` does: the canonical maps
`Ω^p_{X/S'} ⟶ Ω^p_{X/S}` are isomorphisms compatible with the differentials
([Stacks, Tag 0FLV]). -/
theorem rightDerived_map_deRham_d_comp_etale_eq_zero_iff (a : X ⟶ S) (t : S ⟶ S') [Etale t]
    (p q : ℕ) :
    ((sectionsFunctor X.carrier ⊤).rightDerived q).map
        ((SheafOfModules.toSheaf _).map ((a ≫ t).deRhamComplex.d p (p + 1))) = 0 ↔
      ((sectionsFunctor X.carrier ⊤).rightDerived q).map
        ((SheafOfModules.toSheaf _).map (a.deRhamComplex.d p (p + 1))) = 0 := by
  let U : X.Opens := ⊤
  let E := Stacks.Cohomology.AbelianSheaf.cohomologyOverIsoRestrictTop.{u} (X := X.carrier) U q
  let F := Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u}
    (X := (Opens.toTopCat X.carrier).obj U) ⊤ q
  have hres : ∀ {G H : X.carrier.Sheaf AddCommGrpCat.{u}} (φ : G ⟶ H),
      ((sectionsFunctor X.carrier ⊤).rightDerived q).map φ = 0 ↔
        F.map ((abelianRestrictOpen U).map φ) = 0 := by
    intro G H φ
    show (Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U q).map φ = 0 ↔ _
    rw [← Preadditive.IsIso.comp_right_eq_zero
      ((Stacks.Cohomology.AbelianSheaf.cohomologyOver.{u, u} U q).map φ) (E.hom.app H),
      E.hom.naturality φ, Preadditive.IsIso.comp_left_eq_zero]
    exact Iff.rfl
  refine (hres _).trans (Iff.trans ?_ (hres _).symm)
  exact (functor_map_restrict_deRham_d_eq_zero_iff U (a ≫ t) (U.ι ≫ a) t
      (Category.assoc _ _ _).symm (isIso_relativeDifferentialFormsMap_top_comp_etale a t)
      F p).trans
    (functor_map_restrict_deRham_d_eq_zero_iff U a (U.ι ≫ a) (𝟙 S) (Category.comp_id _).symm
      (isIso_relativeDifferentialFormsMap_top_comp_etale a (𝟙 S)) F p).symm

end Scheme.Hom

namespace TopDegreeDifferential

/-- The global functions of a proper smooth scheme over an affine scheme are étale over the
base ([Stacks, Tag 0G8H]). -/
theorem etale_globalRingHom {A : CommRingCat.{u}} {Y : Scheme.{u}} (g : Y ⟶ Spec A) [IsProper g]
    [Smooth g] : Etale (Spec.map g.appTop ≫ Spec.map (Scheme.ΓSpecIso A).inv) := by
  rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Etale)]
  let := isQuasicoherent_pushforwardAlgebra_of_quasiCompact g
  have h := (isFinite_and_etale_relativeSpecToBase_pushforwardAlgebra g).2
  have := isAffine_of_isAffineHom
    (Stacks.AffineAlgebraEquivalence.relativeSpecToBase (pushforwardAlgebra g))
  have h1 := (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 h
  have h2 : RingHom.Etale (g.app ⊤).hom :=
    (Stacks.QuasicoherentAlgebraEqualizer.respectsIso_app_relativeSpecToBase
      (pushforwardAlgebra g) RingHom.Etale.respectsIso ⟨⊤, isAffineOpen_top _⟩).1 h1
  rw [CommRingCat.hom_comp]
  exact (RingHom.Etale.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso A).inv g.appTop).2 h2

/-- The de Rham differential `Ω^{n-1} ⟶ Ω^n` of a morphism `g` induces zero on `H^n(Y, -)`. -/
abbrev TopDifferentialVanishes {Y S : Scheme.{u}} (g : Y ⟶ S) (n : ℕ) : Prop :=
  ((sectionsFunctor Y.carrier ⊤).rightDerived n).map
    ((SheafOfModules.toSheaf _).map (g.deRhamComplex.d (n - 1) n)) = 0

/-- In degree `0` the differential `Ω^{-1} ⟶ Ω^0` is zero, so it vanishes on `H^0`. -/
theorem topDifferentialVanishes_zero {Y S : Scheme.{u}} (g : Y ⟶ S) :
    TopDifferentialVanishes g 0 := by
  unfold TopDifferentialVanishes
  rw [HomologicalComplex.shape _ _ _ (by simp), Functor.map_zero, Functor.map_zero]

/-- **The top de Rham differential is insensitive to an étale change of base**: for `t` étale,
`d : H^n(Y, Ω^{n-1}) ⟶ H^n(Y, Ω^n)` vanishes for `a ≫ t` exactly when it vanishes for `a`. -/
theorem topDifferentialVanishes_comp_etale_iff {Y S S' : Scheme.{u}} (a : Y ⟶ S) (t : S ⟶ S')
    [Etale t] (n : ℕ) : TopDifferentialVanishes (a ≫ t) n ↔ TopDifferentialVanishes a n := by
  cases n with
  | zero => exact iff_of_true (topDifferentialVanishes_zero _) (topDifferentialVanishes_zero _)
  | succ e => exact Scheme.Hom.rightDerived_map_deRham_d_comp_etale_eq_zero_iff a t e (e + 1)

/-- **Reduction of the top de Rham differential to `Γ(Y, 𝒪_Y) = A`** (the Stein factorization
step of [Stacks, Tag 0G8J]), within a class `P` of rings stable under ring maps of finite type.
If `d : H^n(Y, Ω^{n-1}_{Y/B}) ⟶ H^n(Y, Ω^n_{Y/B})` vanishes for every proper surjective
`Y ⟶ Spec B` smooth of relative dimension `n` with `B` in `P` and `B ⟶ Γ(Y, 𝒪_Y)` bijective, then
it vanishes for every proper `Y ⟶ Spec A` smooth of relative dimension `n` with `A` in `P`: such a
morphism factors as `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec A` with the second factor étale. -/
theorem topDifferentialVanishes_of_isIso_appTop_of_mem (P : CommRingCat.{u} → Prop)
    (hP : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), P A → φ.hom.FiniteType → P B) (n : ℕ)
    (h : ∀ (B : CommRingCat.{u}), P B → ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec B) [IsProper g]
      [SmoothOfRelativeDimension n g] [Surjective g] [IsIso g.appTop],
      TopDifferentialVanishes g n)
    {A : CommRingCat.{u}} (hA : P A) {Y : Scheme.{u}} (g : Y ⟶ Spec A) [IsProper g]
    [SmoothOfRelativeDimension n g] : TopDifferentialVanishes g n := by
  have : Smooth g := SmoothOfRelativeDimension.smooth n g
  let φ : A ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso A).inv ≫ g.appTop
  let t : Spec Γ(Y, ⊤) ⟶ Spec A := Spec.map g.appTop ≫ Spec.map (Scheme.ΓSpecIso A).inv
  have ht : t = Spec.map φ := (Spec.map_comp _ _).symm
  have hfac : g = Y.toSpecΓ ≫ t := (Scheme.toSpecΓ_comp_Spec_map_appTop g).symm
  have : Etale t := etale_globalRingHom g
  have het : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 (ht ▸ inferInstance)
  have hB : P Γ(Y, ⊤) := by
    refine hP φ hA ?_
    algebraize [φ.hom]
    exact (inferInstance : Algebra.FiniteType A Γ(Y, ⊤))
  have : SmoothOfRelativeDimension n (Y.toSpecΓ ≫ t) := hfac ▸ inferInstance
  have := isProper_toSpecΓ g
  have : SmoothOfRelativeDimension n Y.toSpecΓ :=
    smoothOfRelativeDimension_of_comp_of_etale n Y.toSpecΓ t
  have : Surjective Y.toSpecΓ := Scheme.surjective_toSpecΓ g
  have : IsIso Y.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  rw [hfac]
  exact (topDifferentialVanishes_comp_etale_iff Y.toSpecΓ t n).2 (h _ hB Y Y.toSpecΓ)

/-- **Reduction of the top de Rham differential to `Γ(Y, 𝒪_Y) = A`** (the Stein factorization
step of [Stacks, Tag 0G8J]). If `d : H^n(Y, Ω^{n-1}_{Y/B}) ⟶ H^n(Y, Ω^n_{Y/B})` vanishes for every
proper surjective `Y ⟶ Spec B` smooth of relative dimension `n` with `B ⟶ Γ(Y, 𝒪_Y)` bijective,
then it vanishes for every proper `Y ⟶ Spec A` smooth of relative dimension `n`. -/
theorem topDifferentialVanishes_of_isIso_appTop (n : ℕ)
    (h : ∀ (B : CommRingCat.{u}) (Y : Scheme.{u}) (g : Y ⟶ Spec B) [IsProper g]
      [SmoothOfRelativeDimension n g] [Surjective g] [IsIso g.appTop],
      TopDifferentialVanishes g n)
    {A : CommRingCat.{u}} {Y : Scheme.{u}} (g : Y ⟶ Spec A) [IsProper g]
    [SmoothOfRelativeDimension n g] : TopDifferentialVanishes g n :=
  topDifferentialVanishes_of_isIso_appTop_of_mem (fun _ => True) (fun _ _ _ => trivial) n
    (fun B _ => h B) trivial g

end TopDegreeDifferential

end AlgebraicGeometry
