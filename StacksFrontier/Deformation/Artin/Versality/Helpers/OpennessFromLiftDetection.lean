module

public import StacksFrontier.Deformation.Artin.Versality.Helpers.OpennessOfVersalitySquareZeroEffective
public import StacksFrontier.Deformation.Artin.Versality.WeakTowerEffectivity

/-!
# Openness of versality from lift detection over bases of finite type

This is the proof of Stacks 0CYF with its hypotheses (4) and (5) asked only where the proof uses
them: at objects over the spectrum of a ring `A` of finite type over an affine open of `S`, and,
for the obstruction theory, only along morphisms of deformation situations over the same `A` and
the same object (the footnote to assumption (4) of the source). The towers of square-zero
thickenings `⋯ → R₁ → R₀` to which the proof of Stacks 0CXU applies condition (4) have `R₀`
of finite type over `S`.

* `Deformation.Artin.TangentPreservesCountableProductsOfFiniteType`: assumption (5)(a) over
  bases of finite type.
* `Deformation.Artin.HasLiftOfCountableProductsOfFiniteType`: what assumptions (4) and (5)(b)
  give over a base of finite type (`Deformation.Artin.ObstructionTheory.hasLift_of_injective`):
  an object lifts across a deformation situation whose kernel is the product of the kernels of
  deformation situations it lifts across.

## Main results

* `Deformation.Artin.isSquareZeroTowerEffectiveOnClassesOfFiniteType_of_hasLift`: square-zero
  towers over a base of finite type are effective on lift classes.
* `Deformation.Artin.isOpenVersality_of_hasLiftOfCountableProductsOfFiniteType`: openness of
  versality, at any universe of morphisms of `𝒳`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

variable (B S hS p hp) in
/-- **Assumption (5)(a) of Stacks 0CYF over bases of finite type.** For every object `x` over the
spectrum of an `S`-algebra `A` with `Spec A → S` locally of finite type and every sequence of
`A`-modules `Mₙ`, the map `T_x(∏ Mₙ) → ∏ T_x(Mₙ)` induced by the projections is bijective. -/
abbrev TangentPreservesCountableProductsOfFiniteType (hRS : SatisfiesRSStar B S hS p hp) : Prop :=
  ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))),
    LocallyOfFiniteType toS →
    ∀ (x : X) (hx : p.obj x = algebraOver A B S hS toS hA),
    ∀ (M : ℕ → SiteModule A B) (hM : IsSiteModule A B (ModuleCat.of A (∀ n, ((M n).obj : Type u)))),
      Function.Bijective (fun t : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
          ⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ =>
        fun n => (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map
          (ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj n)) :
            (⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ : SiteModule A B) ⟶ M n) t)

variable (B S hS p hp) in
/-- **Lifts across a product of kernels, over bases of finite type.** For an object `x` over
`Spec A`, with `Spec A → S` locally of finite type and mapping into an affine open, a deformation
situation `t` of `A` and deformation situations `sₙ` of `A` with morphisms `t → sₙ` over the
identity of `(x, A)`, surjective on thickened rings, whose kernel maps identify `Ker(t)` with
`∏ Ker(sₙ)`: if `x` lifts across every `sₙ`, it lifts across `t`. This is what assumptions (4)
and (5)(b) of Stacks 0CYF are used for
(`Deformation.Artin.ObstructionTheory.hasLift_of_injective`). -/
def HasLiftOfCountableProductsOfFiniteType : Prop :=
  ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (hU : MapsIntoAffineOpen S toS), LocallyOfFiniteType toS →
    ∀ (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
      (t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA))
      (s : ℕ → DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA))
      (m : ∀ n, DeformationSituation.Hom B S hS p (P := AugmentedSiteRing.affineObject x hx hU)
        (Q := AugmentedSiteRing.affineObject x hx hU) t (s n)),
      (∀ n, (m n).base = AffineObject.Hom.id _) → (∀ n, Function.Surjective (m n).top.ringMap) →
      ∀ (fk : ∀ n, t.kernelObj ⟶ (s n).kernelObj),
        (∀ n z, (s n).kernelVal (fk n z) = (m n).top.ringMap (t.kernelVal z)) →
        Function.Bijective (fun z n => fk n z) →
        (∀ n, AffineObject.HasLift hp (AugmentedSiteRing.affineObject x hx hU) (s n)) →
        AffineObject.HasLift hp (AugmentedSiteRing.affineObject x hx hU) t

variable (B S hS p hp) in
/-- **Effectivity of square-zero towers on lift classes, over bases of finite type.** The
property `Deformation.Artin.IsSquareZeroTowerEffectiveOnClasses`, asked for towers
`⋯ → R₁ → R₀` with `Spec R₀ → S` locally of finite type. -/
def IsSquareZeroTowerEffectiveOnClassesOfFiniteType : Prop :=
  ∀ (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n),
    (∀ n, Function.Surjective (f n)) →
    (∀ n, RingHom.ker (SquareZeroTower.toBase f n) ^ 2 = ⊥) →
    ∀ (toS : Spec (.of (R 0)) ⟶ S) (hA : B.Contains (Spec (.of (R 0))))
    (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
    (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
    (hR : ∀ n, B.Contains (Spec (.of (R n)))),
    MapsIntoAffineOpen S toS → LocallyOfFiniteType toS →
    ∀ (x : X) (hx : p.obj x = algebraOver (R 0) B S hS toS hA)
      (b : ∀ n, BasedSiteRing.classes p x hx (SquareZeroTower.level f Λ β hβ hβ0 hR n)),
      (∀ n, BasedSiteRing.map p x hx hp (SquareZeroTower.transition f Λ β hβ hβ0 hR n) (b (n + 1)) =
        b n) →
      ∃ ξ : BasedSiteRing.classes p x hx (SquareZeroTower.limitRing f Λ β hβ hβ0 hR),
        ∀ n, BasedSiteRing.map p x hx hp (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n) ξ = b n

namespace SquareZeroTower

open BasedSiteRing

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
  (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
  {toS : Spec (.of (R 0)) ⟶ S} {hA : B.Contains (Spec (.of (R 0)))}
  (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
  (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
  (hR : ∀ n, B.Contains (Spec (.of (R n))))
  {x : X} {hx : p.obj x = algebraOver (R 0) B S hS toS hA}

/-- **Assumption (5)(a) for a tower over a base of finite type.** -/
theorem bijective_classes_productSquareZero_ofFiniteType (hRS : SatisfiesRSStar B S hS p hp)
    (hT : TangentPreservesCountableProductsOfFiniteType B S hS p hp hRS)
    (hlft : LocallyOfFiniteType toS) :
    Function.Bijective fun d : classes p x hx (productSquareZero f hf hsq Λ hR) =>
      fun n => BasedSiteRing.map p x hx hp (squareZeroProj f hf hsq Λ hR n) d := by
  let T := tangentFunctor (R 0) B S hS toS hA p x hx hp hRS
  have h := hT (R 0) toS hA hlft x hx (levelModule f hf hsq hR)
    (isSiteModule_kernelProduct f hf hsq hR)
  let g := fun t : T.functor.obj (productModule f hf hsq hR) =>
    fun n => T.functor.map (productProj f hf hsq hR n) t
  have key : (fun d : classes p x hx (productSquareZero f hf hsq Λ hR) =>
      fun n => BasedSiteRing.map p x hx hp (squareZeroProj f hf hsq Λ hR n) d) =
      (fun t n => T.liftEquiv (levelModule f hf hsq hR n) (t n)) ∘ g ∘
        (T.liftEquiv (productModule f hf hsq hR)).symm := by
    funext d n
    obtain ⟨t, rfl⟩ := (T.liftEquiv (productModule f hf hsq hR)).surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply, g]
    exact tangent_natural p x hx Λ hp T (productProj f hf hsq hR n) t
  rw [key]
  exact (Equiv.piCongrRight fun n => T.liftEquiv (levelModule f hf hsq hR n)).bijective.comp
    (h.comp (T.liftEquiv (productModule f hf hsq hR)).symm.bijective)

include hf in
/-- The projections `R̃ → Rₙ` are surjective. -/
theorem proj_surjective (n : ℕ) : Function.Surjective (proj f n) := by
  classical
  intro a
  let r : ∀ m, R m :=
    Function.update (fun m => (toBase_surjective f hf m (toBase f n a)).choose) n a
  have hr : ∀ m, toBase f m (r m) = toBase f n a := by
    intro m
    by_cases hm : m = n
    · subst hm
      simp only [r, Function.update_self]
    · simp only [r, Function.update_of_ne hm]
      exact (toBase_surjective f hf m (toBase f n a)).choose_spec
  refine ⟨⟨r, fun m => ?_⟩, ?_⟩
  · rw [hr m, ← hr 0]
    rfl
  · change r n = a
    simp only [r, Function.update_self]

variable {f hf hsq Λ β hβ hβ0 hR}

include hf hsq in
/-- **The lift to `R̃` over a base of finite type.** -/
theorem nonempty_classes_sameBaseRing_of_hasLift
    (hL : HasLiftOfCountableProductsOfFiniteType B S hS p hp) (hU : MapsIntoAffineOpen S toS)
    (hlft : LocallyOfFiniteType toS) (b : ∀ n, classes p x hx (level f Λ β hβ hβ0 hR n)) :
    Nonempty (classes p x hx (sameBaseRing f Λ β hβ hβ0 hR)) :=
  (AugmentedSiteRing.hasLift_situation_iff hp x hx hU _ _ _).1
    (hL (R 0) toS hA hU hlft x hx (sameBaseSituation f hf hsq Λ β hβ hβ0 hR)
      (levelSituation f hf hsq Λ β hβ hβ0 hR) (situationProj f hf hsq Λ β hβ hβ0 hR hU)
      (fun _ => rfl) (proj_surjective f hf) (kernelProj f hf hsq Λ β hβ hβ0 hR)
      (fun n z => kernelVal_kernelProjFun f hf hsq Λ β hβ hβ0 hR n z)
      (bijective_kernelPi f hf hsq Λ β hβ hβ0 hR)
      (fun n => (AugmentedSiteRing.hasLift_situation_iff hp x hx hU _ _ _).2 ⟨b n⟩))

end SquareZeroTower

/-- **The proof of Stacks 0CYF, over bases of finite type.** -/
theorem isSquareZeroTowerEffectiveOnClassesOfFiniteType_of_hasLift
    (hRS : SatisfiesRSStar B S hS p hp)
    (hT : TangentPreservesCountableProductsOfFiniteType B S hS p hp hRS)
    (hL : HasLiftOfCountableProductsOfFiniteType B S hS p hp) :
    IsSquareZeroTowerEffectiveOnClassesOfFiniteType B S hS p hp := by
  intro R _ f hf hsq toS hA Λ β hβ hβ0 hR hU hlft x hx b hb
  exact SquareZeroTower.exists_limit_classes f hf hsq Λ β hβ hβ0 hR hRS
    (SquareZeroTower.bijective_classes_productSquareZero_ofFiniteType f hf hsq Λ hR hRS hT hlft)
    (SquareZeroTower.nonempty_classes_sameBaseRing_of_hasLift (hf := hf) (hsq := hsq) hL hU hlft
      b).some b hb

section Tower

variable (hp : p.IsFiberedInGroupoids)

/-- **A cocone over a tower of first-order thickenings of a scheme of finite type, from lift
classes.** -/
theorem exists_cocone_of_isSquareZeroTowerEffectiveOnClassesOfFiniteType
    (hE : IsSquareZeroTowerEffectiveOnClassesOfFiniteType B S hS p hp)
    (obj : ℕ → X) (a : ∀ m, obj m ⟶ obj (m + 1)) (c : ∀ m, obj 0 ⟶ obj m)
    (hc0 : c 0 = 𝟙 _) (hc : ∀ m, c (m + 1) = c m ≫ a m)
    (haff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj (obj 0))))
    (hlft : LocallyOfFiniteType (B.inclusion.map (p.obj (obj 0)).hom))
    (W : S.Opens) (hWaff : IsAffineOpen W)
    (hW : Set.range (B.inclusion.map (p.obj (obj 0)).hom).base ⊆ (W : Set S))
    (hthick : ∀ m, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (c m))))
    (hcl : ∀ m, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (a m)))) :
    ∃ (ξ : X) (ι : ∀ m, obj m ⟶ ξ), (∀ m, c m ≫ ι m = ι 0) ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (ι 0))) := by
  classical
  let VS := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Y : ℕ → AlgebraicGeometry.BigFppfOver B S hS := fun m => p.obj (obj m)
  have hYaff : ∀ m, IsAffine (VS.obj (Y m)) := fun m =>
    Stacks.Thickenings.isAffine_of_isThickening (hthick m).isThickening
  let R : ℕ → Type u := fun m => Γ(VS.obj (Y m), ⊤)
  let fm : ∀ m, R (m + 1) →+* R m := fun m => (VS.map (p.map (a m))).appTop.hom
  have hf : ∀ m, Function.Surjective (fm m) := fun m => by
    have := hcl m
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (VS.map (p.map (a m)))).2
  have htoBase : ∀ m, SquareZeroTower.toBase fm m = (VS.map (p.map (c m))).appTop.hom := by
    intro m
    induction m with
    | zero =>
      rw [hc0]
      simp only [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
      rfl
    | succ m ih =>
      rw [SquareZeroTower.toBase, ih, hc, Functor.map_comp, Functor.map_comp,
        Scheme.Hom.comp_appTop]
      rfl
  have hsq : ∀ m, RingHom.ker (SquareZeroTower.toBase fm m) ^ 2 = ⊥ := fun m => by
    rw [htoBase]
    exact ker_appTop_sq_of_isFirstOrderThickening _ (hthick m)
  have hR : ∀ m, B.Contains (Spec (.of (R m))) := fun m =>
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion (VS.obj (Y m)).isoSpec.inv) (Y m).left.2
  -- the structure morphisms factor through `W`
  have hYS : ∀ {m n : ℕ} (g : obj m ⟶ obj n),
      VS.map (p.map g) ≫ B.inclusion.map (Y n).hom = B.inclusion.map (Y m).hom := fun g =>
    (B.inclusion.map_comp (p.map g).left (Y _).hom).symm.trans
      (congrArg B.inclusion.map (Over.w (p.map g)))
  have hYW : ∀ m, Set.range (B.inclusion.map (Y m).hom).base ⊆ Set.range W.ι.base := by
    intro m
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    obtain ⟨t₀, rfl⟩ := (hthick m).isThickening.2 t
    rw [← Scheme.Hom.comp_apply, hYS (c m)]
    exact hW ⟨t₀, rfl⟩
  let τ : ∀ m, VS.obj (Y m) ⟶ W := fun m =>
    IsOpenImmersion.lift W.ι (B.inclusion.map (Y m).hom) (hYW m)
  have hτ : ∀ m, τ m ≫ W.ι = B.inclusion.map (Y m).hom := fun m => IsOpenImmersion.lift_fac _ _ _
  have hτa : ∀ m, VS.map (p.map (a m)) ≫ τ (m + 1) = τ m := fun m => by
    rw [← cancel_mono W.ι, Category.assoc, hτ, hτ]
    exact hYS (a m)
  have : IsAffine W := hWaff
  have hWc : B.Contains W := lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion W.ι) hS
  have hΛc : B.Contains (Spec Γ(W, ⊤)) :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion (W : Scheme.{u}).isoSpec.inv) hWc
  let toS : Spec (.of (R 0)) ⟶ S := (VS.obj (Y 0)).isoSpec.inv ≫ B.inclusion.map (Y 0).hom
  let β : ∀ m, Γ(W, ⊤) →+* R m := fun m => (τ m).appTop.hom
  have hspec : ∀ m, Spec.map (CommRingCat.ofHom (β m)) ≫ (W : Scheme.{u}).isoSpec.inv ≫ W.ι =
      (VS.obj (Y m)).isoSpec.inv ≫ B.inclusion.map (Y m).hom := fun m => by
    change Spec.map (τ m).appTop ≫ _ = _
    rw [Scheme.isoSpec_inv_naturality_assoc, hτ]
  let Λ : AugmentedSiteRing (R 0) B S hS toS (hR 0) :=
    { ring := Γ(W, ⊤)
      contains := hΛc
      structureMap := ObjectProperty.homMk ((W : Scheme.{u}).isoSpec.inv ≫ W.ι)
      aug := β 0
      arrow := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (β 0))))
        (ObjectProperty.hom_ext _ (hspec 0))
      arrow_eq := rfl }
  have hβ : ∀ m, (fm m).comp (β (m + 1)) = β m := fun m => by
    change ((VS.map (p.map (a m))).appTop.hom).comp ((τ (m + 1)).appTop.hom) = (τ m).appTop.hom
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hτa]
  have hU : MapsIntoAffineOpen S toS := by
    refine ⟨W, hWaff, fun t => ?_⟩
    have h : (B.inclusion.map (Y 0).hom).base ((VS.obj (Y 0)).isoSpec.inv.base t) ∈
        Set.range W.ι.base := hYW 0 ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h
    exact h
  have htoS : LocallyOfFiniteType toS := by
    have := hlft
    exact inferInstanceAs (LocallyOfFiniteType ((VS.obj (Y 0)).isoSpec.inv ≫
      B.inclusion.map (p.obj (obj 0)).hom))
  let L := SquareZeroTower.level fm Λ β hβ rfl hR
  let A₀ := algebraOver (R 0) B S hS toS (hR 0)
  let isoA : A₀ ⟶ Y 0 := Over.homMk (ObjectProperty.homMk (VS.obj (Y 0)).isoSpec.inv) rfl
  let isoL : ∀ m, (L m).siteOver ⟶ Y m := fun m =>
    Over.homMk (ObjectProperty.homMk (VS.obj (Y m)).isoSpec.inv)
      (ObjectProperty.hom_ext _ (hspec m).symm)
  have : IsIso isoA := by
    have : IsIso (VS.map isoA) := inferInstanceAs (IsIso (VS.obj (Y 0)).isoSpec.inv)
    exact isIso_of_reflects_iso isoA VS
  have hisoL : ∀ m, IsIso (isoL m) := fun m => by
    have : IsIso (VS.map (isoL m)) := inferInstanceAs (IsIso (VS.obj (Y m)).isoSpec.inv)
    exact isIso_of_reflects_iso (isoL m) VS
  have harrow : ∀ m, isoA ≫ p.map (c m) = (L m).arrow ≫ isoL m := fun m => by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (VS.obj (Y 0)).isoSpec.inv ≫ VS.map (p.map (c m)) =
      Spec.map (CommRingCat.ofHom (SquareZeroTower.toBase fm m)) ≫ (VS.obj (Y m)).isoSpec.inv
    rw [htoBase, CommRingCat.ofHom_hom, Scheme.isoSpec_inv_naturality]
  -- an isomorphism of the base lifts to an isomorphism of `X`
  have hlift : ∀ (z : X) (A : BigFppfOver B S hS) (e : A ⟶ p.obj z) [IsIso e],
      ∃ (y : X) (ψ : y ⟶ z) (h : p.obj y = A), IsIso ψ ∧ p.map ψ = eqToHom h ≫ e := by
    intro z A e _
    obtain ⟨y, ψ, hψ⟩ := hp.exists_lift e z rfl
    have := hp.isStronglyCartesian_homLift e ψ
    refine ⟨y, ψ, IsHomLift.domain_eq p e ψ,
      Functor.IsStronglyCartesian.isIso_of_base_isIso p e ψ, ?_⟩
    rw [IsHomLift.fac' p e ψ]
    simp
  obtain ⟨x', φx, hx', _, hφxmap⟩ := hlift (obj 0) A₀ isoA
  choose y ψ hy hψiso hψmap using fun m => hlift (obj m) (L m).siteOver (isoL m)
  let d : ∀ m, x' ⟶ y m := fun m => φx ≫ c m ≫ inv (ψ m)
  have hdmap : ∀ m, p.map (d m) ≫ eqToHom (hy m) = eqToHom hx' ≫ (L m).arrow := fun m => by
    simp only [d, Functor.map_comp, Functor.map_inv, hφxmap, hψmap, IsIso.inv_comp, inv_eqToHom,
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc isoA, harrow, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  let D : ∀ m, (Under.post p).Fiber (Under.mk (eqToHom hx' ≫ (L m).arrow)) := fun m =>
    ⟨Under.mk (d m), under_mk_eq_of_comp_eqToHom _ _ (hy m) (hdmap m)⟩
  let b : ∀ m, BasedSiteRing.classes p x' hx' (L m) := fun m => Quotient.mk _ (D m)
  have hb : ∀ m, BasedSiteRing.map p x' hx' hp (SquareZeroTower.transition fm Λ β hβ rfl hR m)
      (b (m + 1)) = b m := by
    intro m
    let T := (SquareZeroTower.transition fm Λ β hβ rfl hR m).toHom
    let θ : y m ⟶ y (m + 1) := ψ m ≫ a m ≫ inv (ψ (m + 1))
    have hstep : isoL m ≫ p.map (a m) = T.right ≫ isoL (m + 1) := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change (VS.obj (Y m)).isoSpec.inv ≫ VS.map (p.map (a m)) =
        Spec.map (CommRingCat.ofHom (fm m)) ≫ (VS.obj (Y (m + 1))).isoSpec.inv
      rw [CommRingCat.ofHom_hom, Scheme.isoSpec_inv_naturality]
    have hθ : p.IsHomLift T.right θ := by
      refine IsHomLift.of_fac' p T.right θ (hy m) (hy (m + 1)) ?_
      simp only [θ, Functor.map_comp, Functor.map_inv, hψmap, IsIso.inv_comp, inv_eqToHom,
        Category.assoc]
      rw [reassoc_of% hstep]
      simp only [IsIso.hom_inv_id_assoc]
    have hcart := hp.isStronglyCartesian_homLift T.right θ
    refine AugmentedSiteRing.map_eq_of_lift p x' hx' hp T (D (m + 1)) (D m) θ hcart ?_
    change d m ≫ θ = d (m + 1)
    simp only [d, θ, Category.assoc, IsIso.inv_hom_id_assoc, hc]
  obtain ⟨ξc, hξc⟩ := hE R fm hf hsq toS (hR 0) Λ β hβ rfl hR hU htoS x' hx' b hb
  induction ξc using Quotient.inductionOn with
  | h Dξ =>
  obtain ⟨Q, hQ⟩ := Dξ
  have hm : ∀ m, ∃ μ : y m ⟶ Q.right, d m ≫ μ = Q.hom := by
    intro m
    obtain ⟨e, φ, -, hφ, hmap⟩ := AugmentedSiteRing.representative_map p x' hx' hp
      (SquareZeroTower.limitProj fm Λ β hβ rfl hR m).toHom ⟨Q, hQ⟩
    have h := hξc m
    change AugmentedSiteRing.map p x' hx' hp _ (Quotient.mk _ ⟨Q, hQ⟩) = Quotient.mk _ (D m) at h
    rw [hmap] at h
    obtain ⟨ε⟩ := Quotient.exact h
    refine ⟨ε.inv.1.right ≫ φ, ?_⟩
    have hw := Under.w ε.inv.1
    change d m ≫ ε.inv.1.right = e.1.hom at hw
    rw [← Category.assoc, hw, hφ]
  choose μ hμ using hm
  have h₀ : inv (ψ 0) ≫ μ 0 = inv φx ≫ Q.hom := by
    rw [show inv (ψ 0) = inv φx ≫ d 0 by simp [d, hc0], Category.assoc, hμ]
  refine ⟨Q.right, fun m => inv (ψ m) ≫ μ m, ?_, ?_⟩
  · intro m
    dsimp only
    have h₁ : c m ≫ inv (ψ m) = inv φx ≫ d m := by
      simp only [d, IsIso.inv_hom_id_assoc]
    rw [reassoc_of% h₁, hμ, h₀]
  · dsimp only
    rw [h₀]
    have hDhom := under_hom_eq_of_eq_mk _ hQ
    change p.map Q.hom = _ at hDhom
    rw [Functor.map_comp, Functor.map_comp]
    refine isFirstOrderThickening_iso_comp _ _ ?_
    rw [hDhom]
    refine isFirstOrderThickening_map_eqToHom_comp _ _ _ ?_
    change Stacks.Thickenings.IsFirstOrderThickening
      (Spec.map (CommRingCat.ofHom (SquareZeroTower.limitBase fm)))
    exact Stacks.Smooth.isFirstOrderThickening_specMap
      (CommRingCat.ofHom (SquareZeroTower.limitBase fm))
      (SquareZeroTower.limitBase_surjective fm hf) (SquareZeroTower.ker_limitBase_sq fm hsq)

/-- **Weak effectivity of towers from effectivity on lift classes over bases of finite type.** -/
theorem hasWeaklyEffectiveThickeningTowers_of_isSquareZeroTowerEffectiveOnClassesOfFiniteType
    (hE : IsSquareZeroTowerEffectiveOnClassesOfFiniteType B S hS p hp) :
    HasWeaklyEffectiveThickeningTowers B S hS p IsAffineOpen := by
  intro x xs step fromX ⟨hzero, hfrom0⟩ hfromS haff hlft ⟨W, hWaff, hxW⟩ hthick hstep
  subst hzero
  have hc0 : fromX 0 = 𝟙 _ := by rw [hfrom0, eqToHom_refl]
  have hthick' : ∀ m, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX m))) := by
    rintro (_ | m)
    · rw [hc0, CategoryTheory.Functor.map_id]
      exact isFirstOrderThickening_map_id _
    · exact hthick m
  have hcl : ∀ m, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (step m))) := by
    rintro (_ | m)
    · have h := (hthick 0).1
      rwa [hfromS 0, hc0, Category.id_comp] at h
    · exact hstep m
  obtain ⟨ξ, ι, hι, hι0⟩ := exists_cocone_of_isSquareZeroTowerEffectiveOnClassesOfFiniteType hp hE
    xs step fromX hc0 hfromS haff hlft W hWaff hxW hthick' hcl
  refine ⟨ξ, fun n => ι (n + 1), fun n => ?_, ?_⟩
  · rw [hι, hι]
  · rw [hι]
    exact hι0

end Tower

/-- **Openness of versality from lift detection over bases of finite type** (the proof of Stacks
0CYF, at any universe of morphisms of `𝒳`). Let `S` be locally Noetherian and `𝒳` a category
fibred in groupoids over the big fppf site of `S` whose diagonal is representable by algebraic
spaces, which has (RS*) and is limit preserving, whose tangent spaces at objects over bases of
finite type commute with countable products, and whose objects over bases of finite type lift
across a deformation situation whose kernel is the product of the kernels of deformation
situations they lift across. Then `𝒳` satisfies openness of versality. -/
theorem isOpenVersality_of_hasLiftOfCountableProductsOfFiniteType [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳)
    (hT : TangentPreservesCountableProductsOfFiniteType B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids hRS)
    (hL : HasLiftOfCountableProductsOfFiniteType B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx :=
  isOpenVersality_of_hasLocalRetractions B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids hRS
    (hasLocalRetractions_of_hasRepresentableDiagonal B S hS 𝒳 hΔ
      (AlgebraicGeometry.Stack.isLocallyOfFiniteType_terminal_of_isLocallyOfFiniteType_diagonal
        B S hS 𝒳 hΔ
        (AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal_univ B S hS 𝒳 hΔ hlim))
      (satisfiesRS_of_satisfiesRSStar B S hS _ _ hRS))
    (hasThickeningDescent_of_isLimitPreserving B S hS 𝒳 hlim)
    (fun W => IsAffineOpen W)
    (fun s => by
      obtain ⟨G, hG, hsG, -⟩ :=
        exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top s)
      exact ⟨G, hG, hG, hsG⟩)
    (hasWeaklyEffectiveThickeningTowers_of_isSquareZeroTowerEffectiveOnClassesOfFiniteType
      𝒳.isFiberedInGroupoids
      (isSquareZeroTowerEffectiveOnClassesOfFiniteType_of_hasLift hRS hT hL))

end Deformation.Artin

end
