module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.Main
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap

/-!
# The stalk at the centre of a comparison invertible away from it

Let `φ : F ⟶ G` be a morphism of quasi-coherent `𝒪_X`-modules and `w` a point of `X` at which
the local ring `A = 𝒪_{X,w}` is Noetherian of Krull dimension at least two. Suppose the stalks of
`F` and of `G` at `w` are both free of rank one over `A`, and suppose `φ` is invertible at every
point other than `w`. Then `φ_w` is invertible too, hence so is `φ`.

## Main results

* `Stacks.BlowupTwistUnit.notMem_of_surjective_of_isLocalizedModule`: a scalar whose
  multiplication map becomes surjective after localizing at a prime lies outside that prime.
* `Stacks.BlowupTwistUnit.isLocalizedModule_stalkSpecializesₗ_fromSpecStalk`: the stalk of a
  quasi-coherent module at the point named by a prime `q` of `𝒪_{X,w}` is the localization of the
  stalk at `w` at `q`.
* `Stacks.BlowupTwistUnit.isIso_stalk_of_isIso_restrict`: invertibility of the stalks inside an
  open over which a morphism is invertible.
* `Stacks.BlowupTwistUnit.isIso_stalk_of_forall_ne`: the stalk at `w` is invertible once every
  other stalk is and both stalks at `w` are free of rank one.
* `Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_stalk_free`: a morphism of quasi-coherent
  modules invertible outside one point is invertible, under the same hypotheses at that point.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 01J6](https://stacks.math.columbia.edu/tag/01J6)
* [Stacks Project, Tag 00KE](https://stacks.math.columbia.edu/tag/00KE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.ModuleStalkSpecialization

universe u

namespace Stacks.BlowupTwistUnit

/-! ### The membership statement from one surjective localization -/

/-- Let `q` be a prime of `A`, let `g` and `k` exhibit two modules as localizations of `A` at `q`,
and let `Ψ` be a map between them carrying `g a` to `k (a * t)`. If `Ψ` is surjective then
`t ∉ q`. -/
theorem notMem_of_surjective_of_isLocalizedModule {A : Type u} [CommRing A]
    {M' N' : Type u} [AddCommGroup M'] [Module A M'] [AddCommGroup N'] [Module A N']
    (q : Ideal A) [q.IsPrime] (t : A) (g : A →ₗ[A] M') (k : A →ₗ[A] N')
    (hg : IsLocalizedModule q.primeCompl g) (hk : IsLocalizedModule q.primeCompl k)
    (Ψ : M' →ₗ[A] N') (hcomm : ∀ a : A, Ψ (g a) = k (a * t))
    (hΨ : Function.Surjective Ψ) : t ∉ q := by
  intro ht
  obtain ⟨m', hm'⟩ := hΨ (k 1)
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj q.primeCompl g m'
  have hsm : (s : A) • m' = g a := by simpa [Submonoid.smul_def] using hs
  have e1 : Ψ ((s : A) • m') = k (a * t) := by rw [hsm, hcomm]
  have e2 : Ψ ((s : A) • m') = k (s : A) := by
    rw [map_smul, hm', ← map_smul, smul_eq_mul, mul_one]
  have e3 : k ((s : A) - a * t) = 0 := by rw [map_sub, ← e2, e1, sub_self]
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl k).mp e3
  rw [Submonoid.smul_def, smul_eq_mul, mul_sub, sub_eq_zero] at hs'
  have hns : (s' : A) * (s : A) ∈ q.primeCompl := mul_mem s'.2 s.2
  exact hns (by rw [hs']; exact q.mul_mem_left _ (q.mul_mem_left _ ht))

/-! ### Primes of the local ring and points specializing to the point -/

variable {X : Scheme.{u}}

/-- The point of `X` named by a prime of `𝒪_{X,w}` specializes to `w`. -/
theorem specializes_fromSpecStalk (w : X) (q : PrimeSpectrum (X.presheaf.stalk w)) :
    X.fromSpecStalk w q ⤳ w := by
  have hr : X.fromSpecStalk w q ∈ Set.range ⇑(X.fromSpecStalk w) := ⟨q, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at hr

/-- A prime of `𝒪_{X,w}` other than the maximal ideal names a point other than `w`. -/
theorem fromSpecStalk_ne_of_ne_closedPoint (w : X) (q : PrimeSpectrum (X.presheaf.stalk w))
    (hq : q ≠ IsLocalRing.closedPoint (X.presheaf.stalk w)) : X.fromSpecStalk w q ≠ w := by
  intro hqw
  exact hq ((X.fromSpecStalk w).isEmbedding.injective
    (hqw.trans Scheme.fromSpecStalk_closedPoint.symm))

/-- The stalk of a quasi-coherent module at the point named by a prime `q` of `𝒪_{X,w}` is the
localization at `q` of the stalk at `w`. -/
theorem isLocalizedModule_stalkSpecializesₗ_fromSpecStalk (F : X.Modules) [F.IsQuasicoherent]
    (w : X) (q : PrimeSpectrum (X.presheaf.stalk w)) :
    letI := stalkModule F w
    letI := stalkSpecializesModule F (specializes_fromSpecStalk w q)
    IsLocalizedModule.AtPrime q.asIdeal
      (stalkSpecializesₗ F (specializes_fromSpecStalk w q)) := by
  have hspec := specializes_fromSpecStalk w q
  let : Algebra (X.presheaf.stalk w) (X.presheaf.stalk (X.fromSpecStalk w q)) :=
    (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  let := stalkModule F w
  let := stalkModule F (X.fromSpecStalk w q)
  let := stalkSpecializesModule F hspec
  have : IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk w q)) q.asIdeal :=
    Stacks.Chow.isLocalization_stalk_of_specializes hspec q rfl
  have hprime : (IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk w q))).under
      (X.presheaf.stalk w) = q.asIdeal := IsLocalization.AtPrime.under_maximalIdeal _ _
  exact isLocalizedModule_atPrime_of_eq hprime
    (isLocalizedModule_atPrime_stalkSpecializes F hspec)

/-! ### Stalks of a morphism of modules -/

/-- The square relating the stalk of `φ` at a point to its stalk at a specialization of that point
commutes, applied to an element. -/
theorem stalkMap_stalkSpecializes_apply {F G : X.Modules} (φ : F ⟶ G) {x y : X} (h : y ⤳ x)
    (m : F.presheaf.stalk x) :
    ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ.mapPresheaf).hom
        ((F.presheaf.stalkSpecializes h).hom m)
      = (G.presheaf.stalkSpecializes h).hom
          (((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf).hom m) :=
  congrArg (fun f ↦ (ConcreteCategory.hom f) m)
    (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map φ.mapPresheaf h)

/-- The stalk of a morphism of `𝒪_X`-modules at a generalization `y ⤳ x`, as a linear map over the
local ring at `x`, whose scalars act through the comparison of local rings. -/
def stalkSpecializesMapₗ {F G : X.Modules} (φ : F ⟶ G) {x y : X} (h : y ⤳ x) :
    letI := stalkSpecializesModule F h
    letI := stalkSpecializesModule G h
    F.presheaf.stalk y →ₗ[X.presheaf.stalk x] G.presheaf.stalk y :=
  letI := stalkModule F y
  letI := stalkModule G y
  letI := stalkSpecializesModule F h
  letI := stalkSpecializesModule G h
  let Φ : F.presheaf.stalk y →ₗ[X.presheaf.stalk y] G.presheaf.stalk y :=
    AlgebraicGeometry.stalkMapLinear F.val G.val φ.val y
  { toFun := Φ
    map_add' := map_add Φ
    map_smul' := fun r m ↦ Φ.map_smul ((X.presheaf.stalkSpecializes h).hom r) m }

/-- The stalks inside an open over which a morphism is invertible are invertible. -/
theorem isIso_stalk_of_isIso_restrict {F G : X.Modules} (φ : F ⟶ G) (V : X.Opens)
    (hV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)) (x : X) (hx : x ∈ V) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) := by
  have key : ∀ y : V.toScheme, IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (V.ι y)).map φ) := by
    intro y
    have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) := hV
    have h3 : IsIso ((Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.toPresheaf _ ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ) :=
      Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} y) _
    have h2 : IsIso ((Scheme.Modules.restrictStalkNatIso V.ι y).hom.app F ≫
        (Scheme.Modules.toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} (V.ι y)).map φ) := by
      rw [← (Scheme.Modules.restrictStalkNatIso V.ι y).hom.naturality φ]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictStalkNatIso V.ι y).hom.app F) _
  exact key ⟨x, hx⟩

/-! ### The stalk at the centre -/

/-- The stalk at `w` of a morphism of quasi-coherent modules invertible at every other point is
invertible, as soon as both stalks at `w` are free of rank one over the local ring `A` and `A` is
Noetherian of Krull dimension at least two. -/
theorem isIso_stalk_of_forall_ne {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (φ : F ⟶ G) (w : X) [IsNoetherianRing (X.presheaf.stalk w)]
    (hdim : 2 ≤ ringKrullDim (X.presheaf.stalk w))
    (hne : ∀ y : X, y ≠ w → IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ.mapPresheaf)) :
    letI := stalkModule F w
    letI := stalkModule G w
    ∀ (_d : F.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] X.presheaf.stalk w)
      (_e : G.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] X.presheaf.stalk w),
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} w).map φ.mapPresheaf) := by
  let := stalkModule F w
  let := stalkModule G w
  intro d e
  set Φ : F.presheaf.stalk w →ₗ[X.presheaf.stalk w] G.presheaf.stalk w :=
    AlgebraicGeometry.stalkMapLinear F.val G.val φ.val w with hΦ
  set ψ : X.presheaf.stalk w →ₗ[X.presheaf.stalk w] G.presheaf.stalk w :=
    Φ ∘ₗ (d.symm : X.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] F.presheaf.stalk w).toLinearMap
    with hψ
  have hψapp : ∀ a : X.presheaf.stalk w, e (ψ a) = a * e (ψ 1) := by
    intro a
    have : ψ a = a • ψ 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  have hbij : Function.Bijective ψ := by
    refine bijective_of_forall_notMem_isPrime hdim e ψ ?_
    intro p hp hpne
    have : p.IsPrime := hp
    have hqne : (⟨p, hp⟩ : PrimeSpectrum (X.presheaf.stalk w)) ≠
        IsLocalRing.closedPoint (X.presheaf.stalk w) := fun hqc ↦
      hpne (congrArg PrimeSpectrum.asIdeal hqc)
    have hspec := specializes_fromSpecStalk w (⟨p, hp⟩ : PrimeSpectrum (X.presheaf.stalk w))
    have hyne := fromSpecStalk_ne_of_ne_closedPoint w
      (⟨p, hp⟩ : PrimeSpectrum (X.presheaf.stalk w)) hqne
    let := stalkModule F (X.fromSpecStalk w (⟨p, hp⟩ : PrimeSpectrum (X.presheaf.stalk w)))
    let := stalkModule G (X.fromSpecStalk w (⟨p, hp⟩ : PrimeSpectrum (X.presheaf.stalk w)))
    let := stalkSpecializesModule F hspec
    let := stalkSpecializesModule G hspec
    have hlocF : IsLocalizedModule p.primeCompl (stalkSpecializesₗ F hspec) :=
      isLocalizedModule_stalkSpecializesₗ_fromSpecStalk F w ⟨p, hp⟩
    have hlocG : IsLocalizedModule p.primeCompl (stalkSpecializesₗ G hspec) :=
      isLocalizedModule_stalkSpecializesₗ_fromSpecStalk G w ⟨p, hp⟩
    refine notMem_of_surjective_of_isLocalizedModule p (e (ψ 1))
      (stalkSpecializesₗ F hspec ∘ₗ d.symm.toLinearMap)
      (stalkSpecializesₗ G hspec ∘ₗ e.symm.toLinearMap)
      (IsLocalizedModule.of_linearEquiv_right _ _ _)
      (IsLocalizedModule.of_linearEquiv_right _ _ _)
      (stalkSpecializesMapₗ φ hspec) (fun a ↦ ?_) ?_
    · change AlgebraicGeometry.stalkMapLinear F.val G.val φ.val _
          ((F.presheaf.stalkSpecializes hspec).hom (d.symm a))
        = (G.presheaf.stalkSpecializes hspec).hom (e.symm (a * e (ψ 1)))
      rw [show e.symm (a * e (ψ 1)) = ψ a from by rw [← hψapp a, e.symm_apply_apply]]
      exact stalkMap_stalkSpecializes_apply φ hspec (d.symm a)
    · have := hne _ hyne
      exact (ConcreteCategory.bijective_of_isIso
        ((TopCat.Presheaf.stalkFunctor Ab.{u} _).map φ.mapPresheaf)).2
  rw [ConcreteCategory.isIso_iff_bijective]
  have hΦbij : Function.Bijective Φ := by
    simpa [hψ, Function.comp_def] using hbij.comp d.bijective
  exact hΦbij

/-- A morphism of quasi-coherent modules invertible outside one point is invertible, as soon as
both its stalks at that point are free of rank one over the local ring there and that local ring
is Noetherian of Krull dimension at least two. -/
theorem isIso_of_isIso_restrict_of_stalk_free {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (φ : F ⟶ G) (w : X) (V : X.Opens)
    (hV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ))
    (hVw : ∀ y : X, y ≠ w → y ∈ V) [IsNoetherianRing (X.presheaf.stalk w)]
    (hdim : 2 ≤ ringKrullDim (X.presheaf.stalk w)) :
    letI := stalkModule F w
    letI := stalkModule G w
    ∀ (_d : F.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] X.presheaf.stalk w)
      (_e : G.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] X.presheaf.stalk w), IsIso φ := by
  let := stalkModule F w
  let := stalkModule G w
  intro d e
  refine isIso_of_isIso_restrict_of_isIso_stalk_compl φ V hV fun x hx ↦ ?_
  obtain rfl : x = w := not_not.mp fun hne ↦ hx (hVw x hne)
  exact isIso_stalk_of_forall_ne φ _ hdim
    (fun y hy ↦ isIso_stalk_of_isIso_restrict φ V hV y (hVw y hy)) d e

end Stacks.BlowupTwistUnit

end
