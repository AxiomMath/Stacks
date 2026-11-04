module

public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftsAlong
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldConnectingArrow
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityTangentNaturality

/-!
# The class equation of Stacks 07YM

Let `x` be an object of a category fibred in groupoids over the big fppf site of `S`, lying
over `Spec A`, and let `θ : Ω_{A/Λ} →ₐ k` be an `A`-linear map into a residue field `k` of `A`.
This file assembles the preceding pieces of the construction into the class equation
connecting the canonical tangent map to the lifting description of
`Deformation.Artin.IsVersalAt`: the class of `Deformation.Artin.canonicalTangentMap θ`, moved
across the identification `Deformation.Artin.canonicalFieldBaseChangeEquiv` of lift classes
over `A[k]` with lift classes over `k[k]`, is the class of the connecting arrow
`Deformation.Artin.canonicalDualNumbersConnectingArrow`, for *any* lift `(y, φ)` of `x` along
`Deformation.Artin.canonicalDualNumbersArrow θ`.

## Main results

* `Deformation.Artin.squareZeroOverBaseMap_eq_comp_squareZeroOverMap` — the arrow attached to
  `θ` by `Deformation.Artin.squareZeroOverBaseMap` factors through the module `k` alone,
  followed by `Deformation.Artin.squareZeroOverMap` at `θ`'s underlying module map. This is the
  key module-level prerequisite for the class equation.
* `Deformation.Artin.canonicalDualNumbersArrow_def` — `canonicalDualNumbersArrow θ` unfolded to
  its defining composite, the base-change arrow attached to `θ`'s `AddMonoidHom` followed by the
  canonical deformation element's `sectionScheme`.
* `Deformation.Artin.canonicalDualNumbersArrow_eq_comp_sectionScheme` — the same arrow
  re-expressed, via `squareZeroOverBaseMap_eq_comp_squareZeroOverMap`, as the base-change map
  along `coeffCompare A k` followed by `squareZeroOverMap` at `θ`'s module map followed by
  `sectionScheme`.
* `Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap` — the class equation
  itself: the class of `Deformation.Artin.canonicalTangentMap θ`, moved across
  `Deformation.Artin.canonicalFieldBaseChangeEquiv`, equals the class of
  `Deformation.Artin.canonicalDualNumbersConnectingArrow`, for any lift `(y, φ)` of `x` along
  `Deformation.Artin.canonicalDualNumbersArrow θ`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

/-- **Prerequisite for Stacks 07YM.** For a map `f` of `B`-site modules over `A` and a
ring-plus-module base-change map `ψ` out of `f`'s target module, applying `ψ`'s
`squareZeroRingBaseMap` to the `squareZeroRing`-level image of an element under `squareZeroRingMap
A B f` is computed by first applying `f`'s underlying module map, then `ψ`. Stated abstractly
over the site modules `M N` (rather than at the concrete modules it is used at below), and as a
direct function application (never forming `(squareZeroRingBaseMap r ψ hψ).comp (squareZeroRingMap
A B f).hom` as a `RingHom`), so that the one fact needed about `squareZeroRingMap A B f` —
`squareZeroRingMap_hom_apply` — is applied by `rw` to a goal in which `f` is still a bound
variable and no `RingHom.comp` is ever formed: forming that composite forces Lean to unify the
bundled `squareZeroRing`-instance on its middle object against the raw `TrivSqZeroExt` instance,
which elaboration accepts (they are defeq) but `rw`'s `kabstract` cannot see past, since the
elaborated term carries a coercion invisible in the pretty-printed goal. -/
theorem squareZeroRingBaseMap_apply_squareZeroRingMap_hom {M N : SiteModule A B} (f : M ⟶ N)
    {A' : Type u} [CommRing A'] (r : A →+* A') {P : ModuleCat.{u} A'}
    (ψ : (N.obj : Type u) →+ (P : Type u))
    (hψ : ∀ (a : A) (m : N.obj), ψ (a • m) = r a • ψ m) (z : TrivSqZeroExt A M.obj) :
    squareZeroRingBaseMap r ψ hψ ((squareZeroRingMap A B f).hom z) =
      (r z.fst, ψ (f.hom.hom z.snd)) := by
  rw [squareZeroRingMap_hom_apply]
  rfl

include B hΩ hk in
/-- **Prerequisite for Stacks 07YM.** The ring-plus-module base-change map of step (a) at the
module `θ : Ω[A⁄Λ] →ₗ[A] k` factors, at the level of `squareZeroRing`, through the module-change
map alone (at fixed ring `A`), followed by the ring-change map along `algebraMap A k` (at fixed
module `k`). Routed through `squareZeroRingMap` rather than a fresh `TrivSqZeroExt.map θ`: the
latter needs `Module Aᵒᵖ Ω[A⁄Λ]`, which a discrimination tree cannot see through the named
abbreviation `Ω[A⁄Λ]` down to the `ModuleCat` literal that the project's `oppositeModule`
instance is keyed to, whereas `squareZeroRingMap`'s defining instance was already resolved once,
abstractly, when it was stated. The `.comp ... .hom` on the right is unfolded by `show` (full
`isDefEq`, which sees past it) into a bare application, at which point the goal is closed by
chaining two `rfl`-level unfoldings of `squareZeroRingBaseMap` around the one genuinely
propositional step, `squareZeroRingBaseMap_apply_squareZeroRingMap_hom`. -/
theorem squareZeroRingBaseMap_eq_comp_squareZeroRingMap (θ : Ω[A⁄Λ] →ₗ[A] k) :
    squareZeroRingBaseMap (M := differentialsModule Λ A) (N := ModuleCat.of k k)
        (algebraMap A k) θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ) =
      (squareZeroRingBaseMap (M := ModuleCat.of A k) (N := ModuleCat.of k k) (algebraMap A k)
          (coeffCompare A k) (coeffCompare_smul A k)).comp
        (squareZeroRingMap A B
          (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
            (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))).hom := by
  apply RingHom.ext
  intro z
  show squareZeroRingBaseMap (M := differentialsModule Λ A) (N := ModuleCat.of k k)
      (algebraMap A k) θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ) z =
    squareZeroRingBaseMap (M := ModuleCat.of A k) (N := ModuleCat.of k k) (algebraMap A k)
      (coeffCompare A k) (coeffCompare_smul A k)
      ((squareZeroRingMap A B
        (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))).hom z)
  have hLHS :
      squareZeroRingBaseMap (M := differentialsModule Λ A) (N := ModuleCat.of k k)
          (algebraMap A k) θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ) z =
        (algebraMap A k z.fst, θ.toAddMonoidHom z.snd) := rfl
  have hRHS := squareZeroRingBaseMap_apply_squareZeroRingMap_hom A B
    (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
    (algebraMap A k) (coeffCompare A k) (coeffCompare_smul A k) z
  exact hLHS.trans hRHS.symm

/-- **Prerequisite for Stacks 07YM.** The morphism `Deformation.Artin.squareZeroOverMap` is the
morphism of spectra determined by `Deformation.Artin.squareZeroRingMap`, exactly as
`Deformation.Artin.squareZeroOverBaseMap_spec` records the analogous fact for
`Deformation.Artin.squareZeroOverBaseMap`. Stated abstractly over the site modules `M N` (rather
than at the concrete modules it is used at below) and proved by `rfl`, matching
`squareZeroOverBaseMap_spec`'s own proof: both `squareZeroOverMap` and `BigFppfOver.toScheme`'s
action on morphisms unfold, definitionally, straight to the stated `Spec.map`. -/
theorem squareZeroOverMap_toScheme_spec {M N : SiteModule A B} (f : M ⟶ N) :
    (BigFppfOver.toScheme B S hS).map (squareZeroOverMap A B S hS toS f) =
      Spec.map (squareZeroRingMap A B f) :=
  rfl

include B S hS toS in
/-- **Prerequisite for Stacks 07YM.** For any module map `g : M₀ ⟶ N₀` of `B`-site modules over
`A`, and any `algebraMap A k`-semilinear map `ψ` out of `N₀`, the base-change arrow attached to
`ψ ∘ g` factors as the base-change arrow attached to `ψ` alone, followed by the contravariant
arrow `Deformation.Artin.squareZeroOverMap` attached to `g`. This is the general shape of
`Deformation.Artin.squareZeroOverBaseMap_eq_comp_squareZeroOverMap` below, stated with the
`B`-site modules `M₀ N₀ P` kept as abstract bound variables throughout (as `squareZeroOverBaseMap`
and `squareZeroOverMap` themselves are stated): instantiating them afterwards at concrete modules
substitutes into this already-elaborated statement and its proof term, rather than triggering a
fresh `CommRing`/`NonAssocSemiring` instance search at a module expression (a literal built from
the anonymous constructor of `SiteModule`) that a discrimination tree cannot see through. Proved
by transporting the equation to `Scheme` morphisms along the faithful functor
`BigFppfOver.toScheme` via its `map_injective`. The two `Spec.map (CommRingCat.ofHom ·)` factors
on the right are merged by `specMap_ofHom_comp`, used in term mode rather than `rw`: the
combined morphism's category-instance path is not syntactically the one `Spec.map_comp`'s own
pattern carries, which blocks `rw`'s `kabstract` even though the two are definitionally equal;
unification (`refine ... Eq.trans`) sees through this where syntactic matching cannot. The
remaining ring-level identity is closed exactly as
`squareZeroRingBaseMap_eq_comp_squareZeroRingMap` above: a `show` to make the `AddMonoidHom.comp`
explicit, one `rfl`-level unfolding of `squareZeroRingBaseMap` on each side, and the one genuinely
propositional step, `squareZeroRingBaseMap_apply_squareZeroRingMap_hom`. -/
theorem squareZeroOverBaseMap_comp_squareZeroOverMap {M₀ N₀ : SiteModule A B} (g : M₀ ⟶ N₀)
    {P : SiteModule k B} (ψ : (N₀.obj : Type u) →+ (P.obj : Type u))
    (hψ : ∀ (a : A) (m : N₀.obj), ψ (a • m) = algebraMap A k a • ψ m) :
    squareZeroOverBaseMap (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl M₀ P (ψ.comp g.hom.hom)
        (fun a m => by
          change ψ (g.hom.hom (a • m)) = algebraMap A k a • ψ (g.hom.hom m)
          rw [map_smul, hψ]) =
      squareZeroOverBaseMap (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl N₀ P ψ hψ ≫
        squareZeroOverMap A B S hS toS g := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, squareZeroOverBaseMap_spec, squareZeroOverBaseMap_spec,
    squareZeroOverMap_toScheme_spec,
    show squareZeroRingMap A B g = CommRingCat.ofHom (TrivSqZeroExt.map g.hom.hom).toRingHom
      from rfl]
  refine Eq.trans ?_ (specMap_ofHom_comp (TrivSqZeroExt.map g.hom.hom).toRingHom
    (squareZeroRingBaseMap (algebraMap A k) ψ hψ))
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  show squareZeroRingBaseMap (algebraMap A k) (ψ.comp g.hom.hom)
      (fun a m => by
        show ψ (g.hom.hom (a • m)) = algebraMap A k a • ψ (g.hom.hom m)
        rw [map_smul, hψ]) z =
    squareZeroRingBaseMap (algebraMap A k) ψ hψ ((squareZeroRingMap A B g).hom z)
  have hLHS : squareZeroRingBaseMap (algebraMap A k) (ψ.comp g.hom.hom)
      (fun a m => by
        show ψ (g.hom.hom (a • m)) = algebraMap A k a • ψ (g.hom.hom m)
        rw [map_smul, hψ]) z = (algebraMap A k z.fst, ψ (g.hom.hom z.snd)) := rfl
  exact hLHS.trans
    (squareZeroRingBaseMap_apply_squareZeroRingMap_hom A B g (algebraMap A k) ψ hψ z).symm

include B S hS toS hk hkk in
/-- **Prerequisite for Stacks 07YM.** The arrow `Spec k[k] ⟶ Spec A[Ω[A⁄Λ]]` attached to `θ`
by `Deformation.Artin.squareZeroOverBaseMap` factors as the analogous arrow at the module `k`
alone (at fixed ring `A`), followed by the contravariant arrow
`Deformation.Artin.squareZeroOverMap` attached to the module map underlying `θ`. An instance of
`Deformation.Artin.squareZeroOverBaseMap_comp_squareZeroOverMap` at the module map underlying
`θ`, once the `ψ ∘ g` it produces on the left is identified with `θ.toAddMonoidHom` itself (both
being, by `squareZeroRingBaseMap_eq_comp_squareZeroRingMap`'s own computation, the pair of
`algebraMap A k` and the plain evaluation of `θ`) via `squareZeroOverBaseMap`'s congruence in its
semilinear-map argument. -/
theorem squareZeroOverBaseMap_eq_comp_squareZeroOverMap (θ : Ω[A⁄Λ] →ₗ[A] k) :
    squareZeroOverBaseMap (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl
        (differentialsSiteModule Λ A B hΩ) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
        θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ) =
      squareZeroOverBaseMap (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
          (coeffCompare A k) (coeffCompare_smul A k) ≫
        squareZeroOverMap A B S hS toS
          (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
            (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)) := by
  let ψ' : ((⟨ModuleCat.of A k, hk⟩ : SiteModule A B).obj : Type u) →+
      ((⟨ModuleCat.of k k, hkk⟩ : SiteModule k B).obj : Type u) := coeffCompare A k
  have hψ' : ∀ (a : A) (m : (⟨ModuleCat.of A k, hk⟩ : SiteModule A B).obj),
      ψ' (a • m) = algebraMap A k a • ψ' m := coeffCompare_smul A k
  have hcomp := squareZeroOverBaseMap_comp_squareZeroOverMap A k B S hS toS
    (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
    ψ' hψ'
  exact hcomp

section SquareLiftClassesWitness

open CategoryTheory.Functor CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] (q : D ⥤ C)
  (c : q.ChoiceOfPullbacks) (hq : q.IsFiberedInGroupoids) {U V W Z : C}
  (α : U ⟶ V) (β : U ⟶ W) (γ : V ⟶ Z) (δ : W ⟶ Z) (hc : α ≫ γ = β ≫ δ)

/-- **Prerequisite for Stacks 07YM.** Characterizes `squareLiftClassesEquiv`'s action on an
arbitrary class of lifts: given any representative `b₀` of a lift of `y` along `γ`, the class
`squareLiftClassesEquiv` carries it to is represented by a lift `b₁` of the restriction of `y`
along `α`, along `β`, related to `b₀` by an arrow `ρ` strongly cartesian over `δ` that factors
the chosen restriction arrow `c.map α y` through `b₀`'s own arrow. Proved via the comparison
`isoFiberToUnder_surjective` between the iso-fibre of a pullback functor and the fibre of lifts,
which is surjective on the nose (not merely essentially), so that an arbitrary `b₀` is literally
an `isoFiberToUnder`-image and the whole computation reduces to the arrow-level factorization
`isoFiberArrow_squareLiftEquivalence_fac` of the (RS*) comparison together with three
definitional unfoldings of `squareLiftClassesEquiv`'s constituent `Equiv`s on a `Quotient.mk`. -/
theorem exists_isStronglyCartesian_squareLiftClassesEquiv_apply
    (hE : (fiberSquareComparison q c α β γ δ hc).IsEquivalence) (y : q.Fiber V)
    (b₀ : (Under.post q).Fiber (Under.mk (eqToHom y.2 ≫ γ))) :
    ∃ (b₁ : (Under.post q).Fiber (Under.mk (eqToHom ((c.pullbackFunctor α).obj y).2 ≫ β)))
      (ρ : b₁.1.right ⟶ b₀.1.right),
      squareLiftClassesEquiv q c α β γ δ hc hq hE y (Quotient.mk _ b₀) = Quotient.mk _ b₁ ∧
      q.IsStronglyCartesian δ ρ ∧ b₁.1.hom ≫ ρ = c.map α y ≫ b₀.1.hom := by
  obtain ⟨t₀, ht₀⟩ := isoFiberToUnder_surjective q hq c γ y b₀
  subst ht₀
  set t₁ := (squareLiftEquivalence q c α β γ δ hc hE y).functor.obj t₀ with ht₁def
  refine ⟨isoFiberToUnderObj q c β ((c.pullbackFunctor α).obj y) t₁, c.map δ t₀.obj.left,
    ?_, ?_, ?_⟩
  · have hA : (isoFiberUnderClassesEquiv q hq c γ y).symm
        (Quotient.mk _ ((isoFiberToUnder q c γ y).obj t₀)) = Quotient.mk _ t₀ := by
      rw [Equiv.symm_apply_eq]
      rfl
    have hB : (Equiv.ofBijective (isoClassMap (squareLiftEquivalence q c α β γ δ hc hE y).functor)
          (isoClassMap_bijective_of_essSurj
            (squareLiftEquivalence q c α β γ δ hc hE y).functor)) (Quotient.mk _ t₀) =
        Quotient.mk _ t₁ := rfl
    have hC : (isoFiberUnderClassesEquiv q hq c β ((c.pullbackFunctor α).obj y))
        (Quotient.mk _ t₁) =
        Quotient.mk _ (isoFiberToUnderObj q c β ((c.pullbackFunctor α).obj y) t₁) := rfl
    unfold squareLiftClassesEquiv
    rw [Equiv.trans_apply, Equiv.trans_apply, hA, hB]
    exact hC
  · exact c.isStronglyCartesian δ t₀.obj.left
  · exact isoFiberArrow_squareLiftEquivalence_fac q c α β γ δ hc hE y t₀

end SquareLiftClassesWitness

section ClassEquation

open CategoryTheory.Functor CategoryTheory.Limits

include B S hS toS hA hAk x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- **Prerequisite for Stacks 07YM.** The connecting arrow
`Deformation.Artin.canonicalDualNumbersConnectingArrow` is, as an object of `Under x'.1` (where
`x'` is the chosen restriction of `x` to `Spec k`), a lift of `x'.1` along the square-zero
immersion at `k`. This is what lets its isomorphism class be compared with the isomorphism
classes of lifts that `Deformation.Artin.canonicalFieldBaseChangeEquiv` identifies. Proved by
converting the strong cartesianness of the connecting arrow
(`Deformation.Artin.isStronglyCartesian_canonicalDualNumbersConnectingArrow`) into the defining
membership equation via `IsHomLift.fac'`, exactly as `Deformation.Artin.underPost_map_mem_fiber`
converts a homlift fact in the other direction. -/
theorem canonicalDualNumbersConnectingArrow_mem_fiber (θ : Ω[A⁄Λ] →ₗ[A] k) (y : X) (φ : y ⟶ x)
    (hφ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ) :
    letI : p.IsFibered := hp.isFibered
    (Under.post p).obj (Under.mk
        (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
          baseMap baseFactorization θ y φ hφ)) =
      Under.mk (eqToHom (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2 ≫
        squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) := by
  have : p.IsFibered := hp.isFibered
  have hχSC := isStronglyCartesian_canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p
    x hx hp hRS hΩ hkk baseMap baseFactorization θ y φ hφ
  have hχlift : p.IsHomLift
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
      (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
        baseMap baseFactorization θ y φ hφ) := hχSC.toIsHomLift
  refine StructuredArrow.obj_ext _ _ (IsHomLift.codomain_eq p
    (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
      (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
    (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
      baseMap baseFactorization θ y φ hφ)) ?_
  show p.map
      (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
        baseMap baseFactorization θ y φ hφ) ≫
      eqToHom (IsHomLift.codomain_eq p
        (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
        (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
          baseMap baseFactorization θ y φ hφ)) =
    eqToHom (((Functor.chosenPullbacks p).pullbackFunctor
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2 ≫
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
  rw [IsHomLift.fac' p
    (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
      (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
    (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
      baseMap baseFactorization θ y φ hφ)]
  simp

include B S hS toS hA x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- `canonicalDualNumbersArrow θ` unfolded to the defining composite: the base-change map
attached to `θ.toAddMonoidHom` followed by the canonical deformation element's `sectionScheme`.
A pure unfolding, split off as its own lemma so later lemmas never need to unfold
`canonicalDualNumbersArrow` themselves against the much larger goals they state. -/
theorem canonicalDualNumbersArrow_def (θ : Ω[A⁄Λ] →ₗ[A] k) :
    canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ =
      squareZeroOverBaseMap (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl
          (differentialsSiteModule Λ A B hΩ) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
          θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ) ≫
        (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).sectionScheme :=
  rfl

include B S hS toS hA x hx hp hRS hΩ hk hkk baseMap baseFactorization in
/-- The canonical dual-numbers arrow `canonicalDualNumbersArrow θ` factors as the base-change map
along `coeffCompare A k` followed by the module map induced by `θ`, followed by the canonical
deformation element's `sectionScheme`. Obtained from `canonicalDualNumbersArrow_def` (a pure
unfolding) and `squareZeroOverBaseMap_eq_comp_squareZeroOverMap`, re-associated so the
`squareZeroOverMap`/`sectionScheme` composite sits together as a single factor. -/
theorem canonicalDualNumbersArrow_eq_comp_sectionScheme (θ : Ω[A⁄Λ] →ₗ[A] k) :
    canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ =
      squareZeroOverBaseMap (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
          (coeffCompare A k) (coeffCompare_smul A k) ≫
        (squareZeroOverMap A B S hS toS
            (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
              (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)) ≫
          (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
            baseFactorization).sectionScheme) :=
  (canonicalDualNumbersArrow_def Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ).trans
    ((congrArg (· ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).sectionScheme)
        (squareZeroOverBaseMap_eq_comp_squareZeroOverMap Λ A k B S hS toS hΩ hk hkk θ)).trans
      (Category.assoc _ _ _))

include B S hS toS hA hAk x hx hp hRS hΩ hk hkk baseMap baseFactorization in
/-- **Stacks 07YM, the class equation.** The class of `canonicalTangentMap θ`, moved across the
identification `canonicalFieldBaseChangeEquiv` of lift classes over `A[k]` with lift classes over
`k[k]`, is the class of the connecting arrow `canonicalDualNumbersConnectingArrow`, for *any* lift
`(y, φ)` of `x` along `canonicalDualNumbersArrow θ`. This is the class equation underlying the
construction connecting the canonical tangent map to the lifting description of
`Deformation.Artin.IsVersalAt`.

The proof assembles a single strongly Cartesian arrow `τ` from `b₁.1.right` to `x` lying over
`canonicalDualNumbersArrow θ`, built by composing: the arrow `ρ` from
`exists_isStronglyCartesian_squareLiftClassesEquiv_apply` witnessing
`canonicalFieldBaseChangeEquiv`'s action on the class of `b'`; the arrow `ψ₀` from
`IsPullbackOfSquareZeroLift`'s destructuring of `isPullbackOfSquareZeroLift_canonicalTangentMap`;
the isomorphism `e` (via `Quotient.exact`) identifying `a'` with the canonical representative,
whose `right`-component `κ` is strongly Cartesian over an identity by
`underPost_isHomLift_right` and fibered-in-groupoids; and the canonical representative's own
cartesian arrow back to `x`. The factorization property of `τ` against `φ` then follows from the
individual factorization properties, chained through
`squareZeroOverBaseMap_eq_comp_squareZeroOverMap` to identify `canonicalDualNumbersArrow θ` with
the base-changed arrow `τ` lies over, and from `canonicalDualNumbersConnectingArrow_fac`. The
conclusion is then `liftAlongClassMk_eq_of_cartesian` applied to `τ` and `φ`, both strongly
Cartesian over `canonicalDualNumbersArrow θ`. -/
theorem canonicalFieldBaseChangeEquiv_canonicalTangentMap (θ : Ω[A⁄Λ] →ₗ[A] k) (y : X) (φ : y ⟶ x)
    (hφ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ) :
    letI : p.IsFibered := hp.isFibered
    canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
          (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
            baseFactorization θ)) =
      Quotient.mk _ (⟨Under.mk (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x
            hx hp hRS hΩ hkk baseMap baseFactorization θ y φ hφ),
          canonicalDualNumbersConnectingArrow_mem_fiber Λ A k B S hS toS hA hAk p x hx hp hRS hΩ
            hkk baseMap baseFactorization θ y φ hφ⟩) := by
  let : p.IsFibered := hp.isFibered
  obtain ⟨a', b', ha', hb', ψ₀, hψ₀SC, hψ₀fac⟩ :=
    isPullbackOfSquareZeroLift_canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk
      baseMap baseFactorization θ
  obtain ⟨e⟩ := Quotient.exact ha'
  have hκlift : p.IsHomLift (𝟙 (squareZeroOver A B S hS toS (differentialsSiteModule Λ A B hΩ)))
      e.hom.1.right :=
    underPost_isHomLift_right p _ _ e.hom.2
  have hκSC : p.IsStronglyCartesian
      (𝟙 (squareZeroOver A B S hS toS (differentialsSiteModule Λ A B hΩ))) e.hom.1.right :=
    hp.isStronglyCartesian_homLift _ _
  have : IsIso e.hom.1.right :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso p
      (𝟙 (squareZeroOver A B S hS toS (differentialsSiteModule Λ A B hΩ))) e.hom.1.right
  have hκfac : a'.1.hom ≫ e.hom.1.right =
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).representative.1.hom := Under.w e.hom.1
  have := (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
    baseFactorization).cartesian
  have hΦSC : p.IsStronglyCartesian
      ((canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionScheme)
      (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).cartesianMap) := by
    have : p.IsStronglyCartesian
        (𝟙 (squareZeroOver A B S hS toS (differentialsSiteModule Λ A B hΩ)) ≫
          (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
            baseFactorization).sectionScheme)
        (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).cartesianMap) := inferInstance
    simpa using this
  have hΦfac : a'.1.hom ≫
      (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).cartesianMap) = 𝟙 x := by
    rw [← Category.assoc, hκfac,
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).restrictsToOriginal]
  have hψΦSC : p.IsStronglyCartesian
      (squareZeroOverMap A B S hS toS
          (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
            (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)) ≫
        (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization).sectionScheme)
      (ψ₀ ≫ (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
        baseMap baseFactorization).cartesianMap)) :=
    inferInstance
  have hψΦfac : b'.1.hom ≫
      (ψ₀ ≫ (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
        baseMap baseFactorization).cartesianMap)) = 𝟙 x := by
    rw [← Category.assoc, hψ₀fac]
    exact hΦfac
  obtain ⟨b₁, ρ, hb₁eq, hρSC, hρfac⟩ := exists_isStronglyCartesian_squareLiftClassesEquiv_apply p
    (Functor.chosenPullbacks p) hp
    (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
    (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
      (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
    (squareZeroArrow A B S hS toS hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
    (squareZeroOverBaseMap (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
      (coeffCompare A k) (coeffCompare_smul A k))
    (algebraOverMap_comp_squareZeroArrow (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
      (coeffCompare A k) (coeffCompare_smul A k))
    (baseChangeSquare_isEquivalence (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
      (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k))
    (Functor.Fiber.mk hx) b'
  have hkey : canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
      (Quotient.mk _ b') = Quotient.mk _ b₁ := by
    show squareLiftClassesEquiv p (Functor.chosenPullbacks p)
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
        (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
        (squareZeroArrow A B S hS toS hA (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
        (squareZeroOverBaseMap (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
          (coeffCompare A k) (coeffCompare_smul A k))
        (algebraOverMap_comp_squareZeroArrow (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
          (coeffCompare A k) (coeffCompare_smul A k))
        hp
        (baseChangeSquare_isEquivalence (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
          (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k))
        (Functor.Fiber.mk hx) (Quotient.mk _ b') = _
    exact hb₁eq
  have hArrowEq := canonicalDualNumbersArrow_eq_comp_sectionScheme Λ A k B S hS toS hA p x hx
    hp hRS hΩ hk hkk baseMap baseFactorization θ
  have hτSC : p.IsStronglyCartesian
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ)
      (ρ ≫ (ψ₀ ≫ (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS
        hΩ baseMap baseFactorization).cartesianMap))) := by
    rw [hArrowEq]
    exact inferInstance
  have hφSC : p.IsStronglyCartesian
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ :=
    hp.isStronglyCartesian_homLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ
  have hcombined : b₁.1.hom ≫
      (ρ ≫ (ψ₀ ≫ (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS
        hΩ baseMap baseFactorization).cartesianMap))) =
      canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ y φ hφ ≫ φ := by
    set Y := ψ₀ ≫ (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS
      hΩ baseMap baseFactorization).cartesianMap) with hYdef
    have step1 := (Category.assoc b₁.1.hom ρ Y).symm
    have step2 := congrArg (· ≫ Y) hρfac
    have step3 := (step1.trans step2).trans (Category.assoc _ _ _)
    have step4 := congrArg ((Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
        (Functor.Fiber.mk hx) ≫ ·) hψΦfac
    have step5 := (step3.trans step4).trans (Category.comp_id _)
    exact step5.trans
      (canonicalDualNumbersConnectingArrow_fac Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
        baseMap baseFactorization θ y φ hφ).symm
  have hclasseq : liftAlongClassMk b₁ =
      liftAlongClassMk (⟨Under.mk (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p
          x hx hp hRS hΩ hkk baseMap baseFactorization θ y φ hφ),
        canonicalDualNumbersConnectingArrow_mem_fiber Λ A k B S hS toS hA hAk p x hx hp hRS hΩ
          hkk baseMap baseFactorization θ y φ hφ⟩) :=
    liftAlongClassMk_eq_of_cartesian b₁
      (⟨Under.mk (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ
          hkk baseMap baseFactorization θ y φ hφ),
        canonicalDualNumbersConnectingArrow_mem_fiber Λ A k B S hS toS hA hAk p x hx hp hRS hΩ
          hkk baseMap baseFactorization θ y φ hφ⟩)
      (ρ ≫ (ψ₀ ≫ (e.hom.1.right ≫ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS
        hΩ baseMap baseFactorization).cartesianMap)))
      φ hτSC hφSC hcombined
  rw [← hb', hkey]
  exact hclasseq

end ClassEquation

end Deformation.Artin
