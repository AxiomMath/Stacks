module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Basic
public import StacksFrontier.Algebra.Module.FinitePresentation.Transport

/-!
# Transporting finiteness and localization along a ring isomorphism

Replacing the base ring by an isomorphic one and the module by a module carrying a compatible
additive isomorphism changes none of the finiteness properties. Mathlib's transport lemmas
(`Module.Finite.equiv`, `Module.FinitePresentation.of_equiv`, `Module.Flat.of_linearEquiv`) all
keep the base ring fixed, so the semilinear versions have to be supplied; two of the three already
are — `finitePresentation_of_ringEquiv` in
`StacksFrontier/Algebra/Module/FinitePresentation/Transport.lean` and
`Module.Flat.of_semilinearEquiv` in
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningStratification/AffineFlatness.lean` — and this
file adds the one that was missing, for `Module.Finite`, together with the two transports that the
same change of rings needs beyond a single module: finite presentation of an *algebra*, and the
property of *being a localization*.

The device is the same in each case. A ring isomorphism `e : A ≃+* B` makes `B` an `A`-algebra
whose structure map is bijective, so `B` is a finite `A`-module; the property for the `B`-module
then descends to `A` by transitivity. The additive isomorphism is folded in first, by giving the
source module the `B`-action obtained from its `A`-action through `e.symm`, which makes the
isomorphism `B`-linear. For an algebra the same remark says that a ring isomorphism is a ring map
of finite presentation, and `RingHom.FinitePresentation` is closed under composition, so the finite
presentation of `algebraMap R S` can be conjugated by the two isomorphisms.

The leading application is a change of universe. A statement proved for `R`, `S`, `M` sharing one
universe is transported to independent universes by lifting the data with `ULift` and reading the
conclusion back along `ULift.ringEquiv` and `ULift.moduleEquiv`; the conclusion itself costs
nothing when it is stated at an arbitrary model of a localization, which is what
`Module.FinitePresentation.of_isLocalizedModule_of_isLocalization` provides.

## Main results

* `Module.Finite.of_semilinearEquiv`: finite generation transports along a ring isomorphism
  together with a compatible additive isomorphism of modules. This is the `Module.Finite`
  companion of `Module.Flat.of_semilinearEquiv` and of `finitePresentation_of_ringEquiv`.
* `RingEquiv.finitePresentation`: a ring isomorphism is a ring map of finite presentation.
* `Algebra.FinitePresentation.of_ringEquiv`: finite presentation of an algebra under an
  isomorphism of the base ring together with a compatible isomorphism of the algebra.
* `IsLocalizedModule.of_ringEquiv`: being a localization is transported by an isomorphism of the
  base ring together with compatible additive isomorphisms of the source and the target.
* `Module.FinitePresentation.of_isLocalizedModule_of_isLocalization`: finite presentation of a
  localized module over the localized ring does not depend on which models of the two
  localizations are used, and the models may lie in arbitrary universes.

## Implementation notes

The compatibility hypothesis is stated as `∀ a m, f (a • m) = e a • f m` rather than by bundling
`f` as a semilinear equivalence, matching `Module.Flat.of_semilinearEquiv`: at the call sites `f`
is produced as an `AddEquiv` (or as a `LinearEquiv` over a third ring, whose `toAddEquiv` is then
used) and the compatibility is usually `rfl`.

`Module.FinitePresentation.of_isLocalizedModule_of_isLocalization` obtains the semilinearity of
`IsLocalizedModule.linearEquiv` over `IsLocalization.algEquiv` — both of which are only linear
over the base ring — from `IsLocalizedModule.linearMap_ext` applied to `Algebra.linearMap S A₂`:
two base-ring-linear maps out of a localization of `S` agree as soon as they agree on the image of
`S`, and there the two sides are both multiplication by a scalar coming from `S`.
-/

@[expose] public section

universe u u' v v' w w'

namespace Module

/-- **Finite generation along a ring isomorphism.** If `e : A ≃+* B` and `f : M ≃+ N` satisfy
`f (a • m) = e a • f m`, then finiteness of `N` over `B` gives finiteness of `M` over `A`.

This is the `Module.Finite` companion of `Module.Flat.of_semilinearEquiv`. -/
public theorem Finite.of_semilinearEquiv {A : Type u} [CommRing A] {B : Type u'}
    [CommRing B] (e : A ≃+* B) {M : Type v} [AddCommGroup M] [Module A M] {N : Type v'}
    [AddCommGroup N] [Module B N] (f : M ≃+ N)
    (hf : ∀ (a : A) (m : M), f (a • m) = e a • f m) [Module.Finite B N] :
    Module.Finite A M := by
  let : Module B M := Module.compHom M e.symm.toRingHom
  have hsm : ∀ (b : B) (m : M), b • m = e.symm b • m := fun _ _ => rfl
  have h : ∀ (a : A) (m : M), a • m = (e a : B) • m := by
    intro a m
    rw [hsm (e a) m, e.symm_apply_apply]
  have hfB : ∀ (b : B) (m : M), f (b • m) = b • f m := by
    intro b m
    rw [hsm b m, hf, e.apply_symm_apply]
  let fB : M ≃ₗ[B] N := { f.toEquiv with map_add' := f.map_add, map_smul' := hfB }
  have : Module.Finite B M := Module.Finite.equiv fB.symm
  let : Algebra A B := e.toRingHom.toAlgebra
  have : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun a m => (h a m).symm
  have : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B) e.surjective
  exact Module.Finite.trans B M

end Module

/-- A ring isomorphism is a ring map of finite presentation: the target is the base itself,
presented by no generators and no relations. -/
public theorem RingEquiv.finitePresentation {A : Type u} [CommRing A] {B : Type u'} [CommRing B]
    (e : A ≃+* B) : e.toRingHom.FinitePresentation := by
  let : Algebra A B := e.toRingHom.toAlgebra
  exact Algebra.FinitePresentation.equiv ({ e with commutes' := fun _ => rfl } : A ≃ₐ[A] B)

/-- **Finite presentation of an algebra under an isomorphism of the data.** If `eR : R ≃+* R'`
and `eS : S ≃+* S'` intertwine the two structure maps and `S` is a finitely presented
`R`-algebra, then `S'` is a finitely presented `R'`-algebra. The four rings lie in four
independent universes. -/
public theorem Algebra.FinitePresentation.of_ringEquiv {R : Type u} [CommRing R] {R' : Type u'}
    [CommRing R'] {S : Type v} [CommRing S] {S' : Type v'} [CommRing S'] [Algebra R S]
    [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (h : ∀ r : R, algebraMap R' S' (eR r) = eS (algebraMap R S r))
    [Algebra.FinitePresentation R S] : Algebra.FinitePresentation R' S' := by
  refine RingHom.finitePresentation_algebraMap.mp ?_
  have hcomp : algebraMap R' S'
      = eS.toRingHom.comp ((algebraMap R S).comp eR.symm.toRingHom) := by
    ext r'
    simpa using h (eR.symm r')
  rw [hcomp]
  exact RingHom.FinitePresentation.comp eS.finitePresentation
    (RingHom.FinitePresentation.comp
      (RingHom.finitePresentation_algebraMap.mpr ‹_›) eR.symm.finitePresentation)

/-- **Being a localization is transported by an isomorphism of the base ring.** Let
`e : S' ≃+* S` identify two rings, `p` a submonoid of `S` and `p'` a submonoid of `S'` with the
same elements through `e`. Given compatible additive isomorphisms `eM : M' ≃+ M` and
`eN : N' ≃+ N` intertwining `f' : M' →ₗ[S'] N'` with `f : M →ₗ[S] N`, the map `f'` is a
localization at `p'` as soon as `f` is one at `p`. -/
public theorem IsLocalizedModule.of_ringEquiv {S : Type u} [CommRing S] {S' : Type u'}
    [CommRing S'] (e : S' ≃+* S) {p : Submonoid S} {p' : Submonoid S'}
    (hp : ∀ s' : S', s' ∈ p' ↔ e s' ∈ p)
    {M : Type v} [AddCommGroup M] [Module S M] {M' : Type v'} [AddCommGroup M'] [Module S' M']
    {N : Type w} [AddCommGroup N] [Module S N] {N' : Type w'} [AddCommGroup N'] [Module S' N']
    (f : M →ₗ[S] N) (f' : M' →ₗ[S'] N') (eM : M' ≃+ M) (eN : N' ≃+ N)
    (hM : ∀ (s' : S') (m' : M'), eM (s' • m') = e s' • eM m')
    (hN : ∀ (s' : S') (n' : N'), eN (s' • n') = e s' • eN n')
    (hcomm : ∀ m' : M', eN (f' m') = f (eM m')) [IsLocalizedModule p f] :
    IsLocalizedModule p' f' := by
  have hmem : ∀ s : p, e.symm (s : S) ∈ p' := fun s => (hp _).mpr (by simp)
  refine ⟨fun x' => ?_, fun y' => ?_, fun {x₁ x₂} hx => ?_⟩
  · refine (Module.End.isUnit_iff _).mpr ?_
    have hb : Function.Bijective ⇑(algebraMap S (Module.End S N) (e (x' : S'))) :=
      (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f ⟨e x', (hp x').mp x'.2⟩)
    have heq : ⇑(algebraMap S' (Module.End S' N') (x' : S'))
        = eN.symm ∘ ⇑(algebraMap S (Module.End S N) (e (x' : S'))) ∘ eN := by
      funext n'
      simp only [Module.algebraMap_end_apply, Function.comp_apply]
      rw [← hN, eN.symm_apply_apply]
    rw [heq]
    exact eN.symm.bijective.comp (hb.comp eN.bijective)
  · obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj p f (eN y')
    refine ⟨⟨eM.symm m, ⟨e.symm (s : S), hmem s⟩⟩, eN.injective ?_⟩
    simp only [Submonoid.smul_def]
    rw [hN, hcomm, eM.apply_symm_apply, e.apply_symm_apply]
    simpa only [Submonoid.smul_def] using hms
  · have hx' : f (eM x₁) = f (eM x₂) := by rw [← hcomm, ← hcomm, hx]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p) (f := f) hx'
    refine ⟨⟨e.symm (c : S), hmem c⟩, eM.injective ?_⟩
    simp only [Submonoid.smul_def]
    rw [hM, hM, e.apply_symm_apply]
    simpa only [Submonoid.smul_def] using hc

/-- **Finite presentation of a localized module does not depend on the model.** Let `p` be a
submonoid of `S`, let `A₁` and `A₂` be two localizations of `S` at `p`, and let `f₁ : M →ₗ[S] N₁`
and `f₂ : M →ₗ[S] N₂` exhibit two localizations of `M` at `p`. If `N₁` is a finitely presented
`A₁`-module then `N₂` is a finitely presented `A₂`-module.

The two models may lie in different universes; this is what makes the statement useful, since the
stalk of a quasi-coherent module on an affine scheme and `LocalizedModule` are two such models,
and so are a localization and a `ULift` of it. -/
public theorem Module.FinitePresentation.of_isLocalizedModule_of_isLocalization {S : Type u}
    [CommRing S] (p : Submonoid S) {A₁ : Type u'} [CommRing A₁] [Algebra S A₁]
    [IsLocalization p A₁] {A₂ : Type v} [CommRing A₂] [Algebra S A₂] [IsLocalization p A₂]
    {M : Type v'} [AddCommGroup M] [Module S M]
    {N₁ : Type w} [AddCommGroup N₁] [Module S N₁] [Module A₁ N₁] [IsScalarTower S A₁ N₁]
    (f₁ : M →ₗ[S] N₁) [IsLocalizedModule p f₁]
    {N₂ : Type w'} [AddCommGroup N₂] [Module S N₂] [Module A₂ N₂] [IsScalarTower S A₂ N₂]
    (f₂ : M →ₗ[S] N₂) [IsLocalizedModule p f₂] [Module.FinitePresentation A₁ N₁] :
    Module.FinitePresentation A₂ N₂ := by
  let e : A₂ ≃ₐ[S] A₁ := IsLocalization.algEquiv p A₂ A₁
  let g : N₂ ≃ₗ[S] N₁ := IsLocalizedModule.linearEquiv p f₂ f₁
  have hcompat : ∀ (a : A₂) (n : N₂), g (a • n) = e a • g n := by
    intro a n
    have key : (g.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A₂ N₂ n).restrictScalars S)
        = ((LinearMap.toSpanSingleton A₁ N₁ (g n)).restrictScalars S) ∘ₗ
          e.toLinearEquiv.toLinearMap := by
      refine IsLocalizedModule.linearMap_ext p (Algebra.linearMap S A₂) f₁ ?_
      ext
      simp [LinearMap.toSpanSingleton, Algebra.linearMap]
    exact LinearMap.congr_fun key a
  refine finitePresentation_of_ringEquiv A₁ A₂ e.toRingEquiv.symm N₁ N₂ g.toAddEquiv.symm
    (fun a n => g.injective ?_) ‹_›
  show g (g.symm (a • n)) = g (e.toRingEquiv.symm a • g.symm n)
  rw [hcompat, g.apply_symm_apply, g.apply_symm_apply]
  exact congrArg (fun t : A₁ => t • n) (e.apply_symm_apply a).symm

end
