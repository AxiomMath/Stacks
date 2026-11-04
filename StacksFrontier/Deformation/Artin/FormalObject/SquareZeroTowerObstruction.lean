module

public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTowerLimit
public import StacksFrontier.Deformation.Artin.Obstruction.LiftDetection

/-!
# Lifts over the limit of a square-zero tower from an obstruction theory

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` satisfying (RS*), and
let `⋯ → R₁ → R₀ = A` be a tower of square-zero thickenings of `A` in the site, all algebras
under a ring `Λ` whose spectrum maps into an affine open of `S`. Assume that the tangent spaces
of `𝒳` commute with countable products of modules (assumption (5)(a) of Stacks 0CYF) and that
`𝒳` has an obstruction theory whose obstruction modules are injective on countable products
(assumptions (4) and (5)(b)). Then every compatible system of lift classes of an object `x` over
`Spec A` to the levels `Rₙ` is the restriction of one lift class over `lim Rₙ`.

This is the proof of Stacks 0CYF. The obstruction to lifting `x` to the ring `R̃` of sequences
with a common base lies in `𝒪_x(∏ Mₙ)` and maps to the obstructions over the `Rₙ`, which vanish;
by (5)(b) it vanishes, so `x` lifts to `R̃`
(`Deformation.Artin.ObstructionTheory.hasLift_of_injective`). The rest is
`Deformation.Artin.SquareZeroTower.exists_limit_classes`, whose hypothesis on `A[∏ Mₙ]` is
assumption (5)(a), through the identification of `T_x(M)` with the lift classes over `A[M]`.

## Main definitions

* `Deformation.Artin.TangentPreservesCountableProducts` — assumption (5)(a) of Stacks 0CYF.
* `Deformation.Artin.ObstructionTheory.InjectiveOnCountableProducts` — assumption (5)(b).
* `Deformation.Artin.IsSquareZeroTowerEffectiveOnClasses` — every compatible system of lift
  classes over a square-zero tower comes from one lift class over the limit.

## Main results

* `Deformation.Artin.SquareZeroTower.exists_limit_classes_of_obstructionTheory`.
* `Deformation.Artin.isSquareZeroTowerEffectiveOnClasses_of_obstructionTheory`.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

variable (B S hS p hp) in
/-- **Assumption (5)(a) of Stacks 0CYF.** For every object `x` over the spectrum of an
`S`-algebra `A` and every sequence of `A`-modules `Mₙ`, the map `T_x(∏ Mₙ) → ∏ T_x(Mₙ)` induced by
the projections is bijective. The tangent functor is defined on the modules `M` for which
`Spec A[M]` lies in the site, so the product and its factors are required to be such. -/
public abbrev TangentPreservesCountableProducts (hRS : SatisfiesRSStar B S hS p hp) : Prop :=
  ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (x : X) (hx : p.obj x = algebraOver A B S hS toS hA),
    ∀ (M : ℕ → SiteModule A B) (hM : IsSiteModule A B (ModuleCat.of A (∀ n, ((M n).obj : Type u)))),
      Function.Bijective (fun t : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
          ⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ =>
        fun n => (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map
          (ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj n)) :
            (⟨ModuleCat.of A (∀ n, ((M n).obj : Type u)), hM⟩ : SiteModule A B) ⟶ M n) t)

/-- **Assumption (5)(b) of Stacks 0CYF.** For every object `x` over the spectrum of an
`S`-algebra mapping into an affine open and every sequence of modules `Mₙ`, the map
`𝒪_x(∏ Mₙ) → ∏ 𝒪_x(Mₙ)` induced by the projections is injective. -/
public abbrev ObstructionTheory.InjectiveOnCountableProducts
    (O : ObstructionTheory B S hS p hp) : Prop :=
  ∀ (P : AffineObject B S hS p) (M : ℕ → ModuleCat.{u} P.alg.carrier),
    Function.Injective (fun z : (O.obstruction P).functor.obj
        (ModuleCat.of P.alg.carrier (∀ n, (M n : Type u))) =>
      fun n => (O.obstruction P).functor.map
        (ModuleCat.ofHom (LinearMap.proj n) :
          ModuleCat.of P.alg.carrier (∀ n, (M n : Type u)) ⟶ M n) z)


/-- Multiplication by `a' ∈ A'` on the kernel of a deformation situation `A' → A` is the scalar
action of its image in `A`. -/
public theorem DeformationSituation.kernelVal_smul {a : SiteAlgebra B S hS}
    (t : DeformationSituation B S hS a) (d : t.top.carrier) (z : t.kernelObj) :
    t.kernelVal (t.hom.ringMap d • z) = d * t.kernelVal z := by
  let := t.kernelModule
  exact congrArg Subtype.val (Stacks.Smooth.kerModule_smul t.surjective t.sq_eq_bot d
    (show RingHom.ker t.hom.ringMap from z))

namespace AugmentedSiteRing

variable {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-- `A`, as an `S`-algebra of the site. -/
public abbrev siteAlgebra (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) : SiteAlgebra B S hS :=
  ⟨A, hA, ObjectProperty.homMk toS⟩

/-- The deformation situation `(D → A)` attached to an augmented ring whose augmentation is
surjective with square-zero kernel. -/
public def situation (D : AugmentedSiteRing A B S hS toS hA) (hsurj : Function.Surjective D.aug)
    (hsq : RingHom.ker D.aug ^ 2 = ⊥) : DeformationSituation B S hS (siteAlgebra A toS hA) where
  top := ⟨D.ring, D.contains, D.structureMap⟩
  hom := ⟨D.aug, D.arrow, D.arrow_eq⟩
  surjective := hsurj
  sq_eq_bot := hsq

/-- The object `x` over `Spec A`, as an object over an `S`-algebra mapping into an affine open. -/
public abbrev affineObject (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
    (hU : MapsIntoAffineOpen S toS) : AffineObject B S hS p :=
  ⟨siteAlgebra A toS hA, hU, ⟨x, hx⟩⟩

/-- `x` lifts across the deformation situation `(D → A)` exactly when it has a lift class over
`D`. -/
public theorem hasLift_situation_iff (hp : p.IsFiberedInGroupoids) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA) (hU : MapsIntoAffineOpen S toS)
    (D : AugmentedSiteRing A B S hS toS hA) (hsurj : Function.Surjective D.aug)
    (hsq : RingHom.ker D.aug ^ 2 = ⊥) :
    AffineObject.HasLift hp (affineObject x hx hU) (situation D hsurj hsq) ↔
      Nonempty (classes p x hx D) := by
  let : p.IsFibered := hp.isFibered
  let c := Functor.chosenPullbacks p
  let x₀ : p.Fiber (algebraOver A B S hS toS hA) := ⟨x, hx⟩
  constructor
  · rintro ⟨x', ⟨e⟩⟩
    let t : Functor.IsoFiber (c.pullbackFunctor D.arrow) x₀ :=
      ⟨CostructuredArrow.mk e.hom, show IsIso e.hom from inferInstance⟩
    exact ⟨Quotient.mk _ (isoFiberToUnderObj p c D.arrow x₀ t)⟩
  · rintro ⟨z⟩
    induction z using Quotient.ind with
    | _ a =>
      obtain ⟨t, -⟩ := isoFiberToUnder_surjective p hp c D.arrow x₀ a
      exact ⟨t.obj.left, ⟨@asIso _ _ _ _ t.obj.hom t.property⟩⟩

end AugmentedSiteRing

namespace SquareZeroTower

open BasedSiteRing

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
  (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
  {toS : Spec (.of (R 0)) ⟶ S} {hA : B.Contains (Spec (.of (R 0)))}
  (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
  (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
  (hR : ∀ n, B.Contains (Spec (.of (R n))))
  {x : X} {hx : p.obj x = algebraOver (R 0) B S hS toS hA}

/-- **Assumption (5)(a) for the tower.** If the tangent spaces commute with countable products,
the lift classes over `A[∏ Mₙ]` are, through the projections, the products of those over the
`A[Mₙ]`. -/
public theorem bijective_classes_productSquareZero (hRS : SatisfiesRSStar B S hS p hp)
    (hT : TangentPreservesCountableProducts B S hS p hp hRS) :
    Function.Bijective fun d : classes p x hx (productSquareZero f hf hsq Λ hR) =>
      fun n => BasedSiteRing.map p x hx hp (squareZeroProj f hf hsq Λ hR n) d := by
  let T := tangentFunctor (R 0) B S hS toS hA p x hx hp hRS
  have h := hT (R 0) toS hA x hx (levelModule f hf hsq hR) (isSiteModule_kernelProduct f hf hsq hR)
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

/-- The deformation situation `(R̃ → A)`. -/
public abbrev sameBaseSituation :=
  AugmentedSiteRing.situation (sameBaseRing f Λ β hβ hβ0 hR).toAffine (base_surjective f hf)
    (ker_base_sq f hsq)

/-- The deformation situation `(Rₙ → A)`. -/
public abbrev levelSituation (n : ℕ) :=
  AugmentedSiteRing.situation (level f Λ β hβ hβ0 hR n).toAffine (toBase_surjective f hf n)
    (hsq n)

/-- The projection `(x, R̃ → A) → (x, Rₙ → A)` of deformation situations. -/
public def situationProj (hU : MapsIntoAffineOpen S toS) (n : ℕ) :
    DeformationSituation.Hom B S hS p (P := AugmentedSiteRing.affineObject x hx hU)
      (Q := AugmentedSiteRing.affineObject x hx hU)
      (sameBaseSituation f hf hsq Λ β hβ hβ0 hR) (levelSituation f hf hsq Λ β hβ hβ0 hR n) where
  base := AffineObject.Hom.id _
  top := ⟨proj f n, (projMap f Λ β hβ hβ0 hR n).toHom.right, rfl⟩
  comm := by
    rw [RingHom.id_comp]
    exact toBase_comp_proj f n

/-- The element of `Mₙ` given by the `n`-th component of an element of `Ker(R̃ → A)`. -/
public def kernelProjFun (n : ℕ) (z : (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelObj) :
    (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelObj :=
  show RingHom.ker (toBase f n) from
    ⟨proj f n (show sameBase f from (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelVal z), by
      rw [RingHom.mem_ker, ← RingHom.comp_apply, toBase_comp_proj]
      exact (show RingHom.ker (base f) from z).2⟩

/-- The underlying element of `kernelProjFun n z` in `Rₙ` is the `n`-th projection of the
underlying element of `z` in `R̃`. -/
theorem kernelVal_kernelProjFun (n : ℕ)
    (z : (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelObj) :
    (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelVal (kernelProjFun f hf hsq Λ β hβ hβ0 hR n z) =
      proj f n (show sameBase f from (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelVal z) :=
  rfl

/-- The projection of kernels `Ker(R̃ → A) → Mₙ`, as a linear map. -/
public def kernelProjLinear (n : ℕ) :
    (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelObj →ₗ[R 0]
      (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelObj where
  toFun := kernelProjFun f hf hsq Λ β hβ hβ0 hR n
  map_add' := fun _ _ => rfl
  map_smul' := fun a z => by
    obtain ⟨d, rfl⟩ := base_surjective f hf a
    apply (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelVal_injective
    rw [RingHom.id_apply]
    have e1 := DeformationSituation.kernelVal_smul (sameBaseSituation f hf hsq Λ β hβ hβ0 hR) d z
    have e2 := DeformationSituation.kernelVal_smul (levelSituation f hf hsq Λ β hβ hβ0 hR n)
      (proj f n d) (kernelProjFun f hf hsq Λ β hβ hβ0 hR n z)
    have hd : (levelSituation f hf hsq Λ β hβ hβ0 hR n).hom.ringMap (proj f n d) = base f d :=
      RingHom.congr_fun (toBase_comp_proj f n) d
    rw [hd] at e2
    refine Eq.trans ?_ e2.symm
    refine (kernelVal_kernelProjFun f hf hsq Λ β hβ hβ0 hR n _).trans ?_
    refine (congrArg (proj f n) e1).trans ?_
    exact map_mul (proj f n) d _

/-- The projection of kernels `Ker(R̃ → A) → Mₙ`. -/
public def kernelProj (n : ℕ) :
    (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelObj ⟶
      (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelObj :=
  letI := (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelModule
  letI := (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelModule
  ModuleCat.ofHom (kernelProjLinear f hf hsq Λ β hβ hβ0 hR n)

/-- `Ker(R̃ → A) = ∏ Mₙ`. -/
public theorem bijective_kernelPi :
    Function.Bijective (fun z n => kernelProjLinear f hf hsq Λ β hβ hβ0 hR n z) := by
  constructor
  · intro z z' h
    apply (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelVal_injective
    apply Subtype.ext
    funext n
    exact congrArg (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelVal (congrFun h n)
  · intro m
    let v : ∀ n, R n := fun n => (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelVal (m n)
    have hm : ∀ n, toBase f n (v n) = 0 := fun n =>
      (show RingHom.ker (toBase f n) from m n).2
    let r : sameBase f := ⟨v, fun n => by
      rw [hm n]
      exact (hm 0).symm⟩
    have hr : r ∈ RingHom.ker (base f) := hm 0
    refine ⟨show RingHom.ker (base f) from ⟨r, hr⟩, funext fun n => ?_⟩
    apply (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelVal_injective
    rfl

variable {f hf hsq Λ β hβ hβ0 hR}

include hf hsq in
/-- **The lift to `R̃`, in the proof of Stacks 0CYF.** If the obstruction modules are injective
on countable products and `x` lifts to every level `Rₙ`, then `x` lifts to `R̃`. -/
public theorem nonempty_classes_sameBaseRing (O : ObstructionTheory B S hS p hp)
    (hO : O.InjectiveOnCountableProducts) (hU : MapsIntoAffineOpen S toS)
    (b : ∀ n, classes p x hx (level f Λ β hβ hβ0 hR n)) :
    Nonempty (classes p x hx (sameBaseRing f Λ β hβ hβ0 hR)) := by
  let P := AugmentedSiteRing.affineObject x hx hU
  let : ∀ n, Module P.alg.carrier
      (RingHom.ker (levelSituation f hf hsq Λ β hβ hβ0 hR n).hom.ringMap) :=
    fun n => (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelModule
  let : Module P.alg.carrier
      (RingHom.ker (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).hom.ringMap) :=
    (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelModule
  let M : ℕ → ModuleCat.{u} P.alg.carrier := fun n =>
    (levelSituation f hf hsq Λ β hβ hβ0 hR n).kernelObj
  let e := LinearEquiv.ofBijective (LinearMap.pi fun n => kernelProjLinear f hf hsq Λ β hβ hβ0 hR n)
    (bijective_kernelPi f hf hsq Λ β hβ hβ0 hR)
  let fn := fun n => kernelProj f hf hsq Λ β hβ hβ0 hR n
  have hinj : Function.Injective fun (o : (O.obstruction P).functor.obj
      (sameBaseSituation f hf hsq Λ β hβ hβ0 hR).kernelObj) (n : ℕ) =>
        ((O.obstruction P).functor.map (fn n)) o := by
    have hfac : ∀ n, fn n =
        (LinearEquiv.toModuleIso e).hom ≫
          (ModuleCat.ofHom (LinearMap.proj n) : ModuleCat.of P.alg.carrier (∀ n, (M n : Type u)) ⟶
            M n) := fun n => by ext z; rfl
    intro o o' h
    apply (ConcreteCategory.bijective_of_isIso
      ((O.obstruction P).functor.map (LinearEquiv.toModuleIso e).hom)).1
    apply hO P M
    funext n
    have h' := congrFun h n
    simp only [hfac] at h'
    have hc := (O.obstruction P).functor.map_comp (LinearEquiv.toModuleIso e).hom
      (ModuleCat.ofHom (LinearMap.proj n) : ModuleCat.of P.alg.carrier (∀ n, (M n : Type u)) ⟶ M n)
    exact (ConcreteCategory.congr_hom hc o).symm.trans (h'.trans (ConcreteCategory.congr_hom hc o'))
  have hlift := O.hasLift_of_injective P (sameBaseSituation f hf hsq Λ β hβ hβ0 hR)
    (levelSituation f hf hsq Λ β hβ hβ0 hR) (situationProj f hf hsq Λ β hβ hβ0 hR hU)
    (fun _ => rfl) fn
    (fun n z => kernelVal_kernelProjFun f hf hsq Λ β hβ hβ0 hR n z) hinj
    (fun n => (AugmentedSiteRing.hasLift_situation_iff hp x hx hU _ _ _).2 ⟨b n⟩)
  exact (AugmentedSiteRing.hasLift_situation_iff hp x hx hU _ _ _).1 hlift

include hf hsq in
/-- **The proof of Stacks 0CYF, on lift classes.** Let `𝒳` satisfy (RS*), let its tangent spaces
commute with countable products (assumption (5)(a)), and let it have an obstruction theory whose
obstruction modules are injective on countable products (assumptions (4) and (5)(b)). Then for a
tower of square-zero thickenings `⋯ → R₁ → R₀ = A` in the site over a ring mapping into an
affine open of `S`, every system of lift classes of `x` over the `Rₙ`, compatible under the
transition maps, is the restriction of one lift class over `lim Rₙ`. -/
public theorem exists_limit_classes_of_obstructionTheory (hRS : SatisfiesRSStar B S hS p hp)
    (hT : TangentPreservesCountableProducts B S hS p hp hRS)
    (O : ObstructionTheory B S hS p hp) (hO : O.InjectiveOnCountableProducts)
    (hU : MapsIntoAffineOpen S toS)
    (b : ∀ n, classes p x hx (level f Λ β hβ hβ0 hR n))
    (hb : ∀ n, BasedSiteRing.map p x hx hp (transition f Λ β hβ hβ0 hR n) (b (n + 1)) = b n) :
    ∃ ξ : classes p x hx (limitRing f Λ β hβ hβ0 hR),
      ∀ n, BasedSiteRing.map p x hx hp (limitProj f Λ β hβ hβ0 hR n) ξ = b n :=
  exists_limit_classes f hf hsq Λ β hβ hβ0 hR hRS
    (bijective_classes_productSquareZero f hf hsq Λ hR hRS hT)
    (nonempty_classes_sameBaseRing (hf := hf) (hsq := hsq) O hO hU b).some b hb

end SquareZeroTower

variable (B S hS p hp) in
/-- **Effectivity of square-zero towers, on lift classes.** For every tower of square-zero
thickenings `⋯ → R₁ → R₀ = A` in the site, under a ring `Λ` of the site whose spectrum maps into
an affine open of `S`, and every object `x` over `Spec A`, every system of lift classes of `x` over
the `Rₙ`, compatible under the transition maps, is the restriction of one lift class of `x` over
`lim Rₙ`.

This is the form of condition (4) of Stacks 0CXU which its proof uses: it only needs, for the
tower `x → x₁ → x₂ → ⋯` it constructs, an object over `Spec (lim Rₙ)` receiving compatible
arrows from the `xₙ` up to isomorphism of lifts. -/
public def IsSquareZeroTowerEffectiveOnClasses : Prop :=
  ∀ (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
    (hf : ∀ n, Function.Surjective (f n))
    (hsq : ∀ n, RingHom.ker (SquareZeroTower.toBase f n) ^ 2 = ⊥)
    (toS : Spec (.of (R 0)) ⟶ S) (hA : B.Contains (Spec (.of (R 0))))
    (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
    (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
    (hR : ∀ n, B.Contains (Spec (.of (R n)))),
    MapsIntoAffineOpen S toS →
    ∀ (x : X) (hx : p.obj x = algebraOver (R 0) B S hS toS hA)
      (b : ∀ n, BasedSiteRing.classes p x hx (SquareZeroTower.level f Λ β hβ hβ0 hR n)),
      (∀ n, BasedSiteRing.map p x hx hp (SquareZeroTower.transition f Λ β hβ hβ0 hR n) (b (n + 1)) =
        b n) →
      ∃ ξ : BasedSiteRing.classes p x hx (SquareZeroTower.limitRing f Λ β hβ hβ0 hR),
        ∀ n, BasedSiteRing.map p x hx hp (SquareZeroTower.limitProj f Λ β hβ hβ0 hR n) ξ = b n

/-- **The proof of Stacks 0CYF.** Condition (RS*), assumption (5)(a), and an obstruction theory
satisfying assumption (5)(b) give the effectivity of square-zero towers on lift classes, which
is the form of condition (4) of Stacks 0CXU that its proof uses. -/
public theorem isSquareZeroTowerEffectiveOnClasses_of_obstructionTheory
    (hRS : SatisfiesRSStar B S hS p hp) (hT : TangentPreservesCountableProducts B S hS p hp hRS)
    (O : ObstructionTheory B S hS p hp) (hO : O.InjectiveOnCountableProducts) :
    IsSquareZeroTowerEffectiveOnClasses B S hS p hp := by
  intro R _ f hf hsq toS hA Λ β hβ hβ0 hR hU x hx b hb
  exact SquareZeroTower.exists_limit_classes_of_obstructionTheory (hf := hf) (hsq := hsq)
    hRS hT O hO hU b hb

end Deformation.Artin
