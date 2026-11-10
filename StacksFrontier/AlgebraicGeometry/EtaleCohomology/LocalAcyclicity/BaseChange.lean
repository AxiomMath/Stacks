module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.Basic

/-!
# Étale local rings of a cartesian square, and local acyclicity under base change

Let `f : X ⟶ S` be a morphism of schemes, let `g : S' ⟶ S` be a second one, and let

```
X' --g'--> X
|f'        |f
S' --g---> S
```

be a cartesian square. A geometric point `x'` of `X'` has images `x = g'(x')` in `X`,
`s' = f'(x')` in `S'` and `s = f(x) = g(s')` in `S`, and the four étale local rings at these
points form a commutative square. This file proves that this square is a *pushout* of rings when
`g` is integral,

`𝒪^sh_{X',x'} = 𝒪^sh_{S',s'} ⊗_{𝒪^sh_{S,s}} 𝒪^sh_{X,x}`,

which is Lemma 0GIP read at a point of a cartesian square of schemes instead of at a prime of a
tensor product of rings. The same conclusion is proved when `g` is locally of finite type and
locally quasi-finite, which is the faithful rendering of the source's hypothesis that `g` be
locally quasi-finite in the sense of Tag 03WT, and when `S'` is the limit of a cofiltered inverse
system of schemes locally of finite type and locally quasi-finite over `S`, with affine transition
morphisms.

The passage from the rings to the schemes is an affine chart of the cartesian square at the point
of `X'`: affine opens `U` of `S`, `V` of `X` and `W` of `S'` with `V` and `W` over `U`. Over such
a chart the sections form a pushout square of rings, the Zariski stalks at the four images of the
point are the localizations of those sections at the contractions of one prime, and the four étale
local rings are strict henselizations of those localizations. That is exactly the input of
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_isIntegral`, of
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_quasiFiniteAt` and of
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_forall_finset`, whose conclusion is
the asserted pushout. In the integral case the chart must be taken with `W = g⁻¹(U)`, which is
affine because an integral morphism is affine: an arbitrary affine open of `S'` over `U` need not
have integral sections over `Γ(S, U)`. In the limit case the chart must be taken with `W` the
preimage of an affine open of one stage, which is affine because the limit projections of a
system with affine transition morphisms are affine, and over which the sections of `g` are
covered by the sections of the later stages.

## Main results

* `Algebra.IsPushout.of_bijective_tensorProduct_lift` reads the bijectivity of the canonical map
  out of a tensor product as the statement that a square of algebras is a pushout.
* `AlgebraicGeometry.etaleLocalRingHom_structureSheafStalkFromLocalRing_germ` and
  `AlgebraicGeometry.baseChangeEtaleLocalRingHom_structureSheafStalkFromLocalRing_germ` compute
  the induced homomorphism of étale local rings on the étale germ of a section over an open set:
  it is the étale germ of the pulled-back section. These are the compatibilities which present an
  affine chart of the cartesian square as an instance of the ring-theoretic situation of Lemma
  0GIP.
* `AlgebraicGeometry.isPushout_etaleLocalRingHom_of_isIntegralHom` — **[Stacks, Tag 0GIP (4)]**
  the square of étale local rings attached to a cartesian square with `g` integral is a pushout.
* `AlgebraicGeometry.isPushout_etaleLocalRingHom_of_locallyQuasiFinite` — **[Stacks, Tag 0GIP
  (1)]** the same when `g` is locally of finite type and locally quasi-finite.
* `AlgebraicGeometry.isPushout_etaleLocalRingHom_of_limit` — **[Stacks, Tag 0GIP (2)]** the same
  when `S'` is the limit of a cofiltered inverse system of schemes locally of finite type and
  locally quasi-finite over `S`, with affine transition morphisms.

Tag 0GJS itself is *not* proved here; see the section "What is not proved" below.

## What is not proved

Tag 0GJS deduces from the pushout property that `f'` is locally acyclic at `x'` relative to
`(g')⁻¹K` whenever `f` is locally acyclic at `x` relative to `K`. That deduction identifies the
variety of vanishing cycles `F_{x',t'}` of `f'` at `x'` and a geometric point `t'` of
`Spec 𝒪^sh_{S',s'}` with the variety of vanishing cycles `F_{x,t}` of `f` at `x` and the image
`t` of `t'` in `Spec 𝒪^sh_{S,s}`, and then transports the isomorphy of the canonical map
`AlgebraicGeometry.vanishingCyclesFibreMap` along that identification.

The identification of the two schemes is what the pushout proved here gives: by
`AlgebraicGeometry.vanishingCyclesFibreIsoSpecTensor` both are the spectrum of a tensor product,
the pushout rewrites `𝒪^sh_{X',x'}` as `𝒪^sh_{S',s'} ⊗_{𝒪^sh_{S,s}} 𝒪^sh_{X,x}`, and the residue
fields of `t` and of `t'` agree definitionally because `AlgebraicGeometry.GeometricPoint.map`
preserves the residue field. Transporting the canonical map along that isomorphism is what is
missing, and the precise missing statements are recorded in the implementation notes.

## Implementation notes

The square is an arbitrary cartesian square `IsPullback g' f' f g`, not the canonical fibre
product: the two readings of the image in `S` of a geometric point of `X'`, through `X` and
through `S'`, are handled by `AlgebraicGeometry.baseChangeEtaleLocalRingHom`, which is where the
substrate isolates that transport, and by
`AlgebraicGeometry.etaleLocalRingHom_comp_baseChangeEtaleLocalRingHom`, which is the commuting
square the pushout needs. The image through `X` is the base throughout, so the étale local ring of
`S` appearing below is the one at `(x'.map g').map f`.

The two missing ingredients of Tag 0GJS, stated precisely, are:

* a natural isomorphism `smallEtalePullbackAb g' ⋙ smallEtaleStalkAb x'.hom ≅
  smallEtaleStalkAb (x'.map g').hom` of functors
  `Sheaf (smallEtaleTopology X) Ab ⥤ Ab`, all three named in `Stacks.EtaleCohomology` — the
  stalk at a geometric point of an inverse image of an abelian étale sheaf is its stalk at the
  image point; and
* for an isomorphism `e : T₁ ≅ T₂` of schemes over the strict henselization at a geometric point
  `x` of `X`, with `q₁ = e.hom ≫ q₂`, a compatibility of
  `AlgebraicGeometry.vanishingCyclesMap` at `(T₁, q₁)` and at `(T₂, q₂)`.

The second needs `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction`, which this
library does have, to be an isomorphism when the morphism of schemes is one; what it does not have
is that, nor the underlying statement on abelian sheaves. By
`AlgebraicGeometry.etaleStalkToSectionsAb_toPresheafFiber` the underived form of the second
ingredient is the naturality of `AlgebraicGeometry.etaleStalkToSectionsAb` in the scheme over the
strict henselization, which in turn is
`Stacks.EtaleCohomology.map_comp_smallEtaleSectionsPullbackAb` read in the other variable.

Given both ingredients the transport of `IsIso ((vanishingCyclesFibreMap ...).app K)` is formal:
`AlgebraicGeometry.vanishingCyclesMap_fac_app` reduces the required commuting square of derived
natural transformations to the underived one, and the uniqueness of a transformation out of a
right derived functor turns that reduction into an equality.

## References

* [Stacks Project, Tag 0GIP](https://stacks.math.columbia.edu/tag/0GIP)
* [Stacks Project, Tag 0GJP](https://stacks.math.columbia.edu/tag/0GJP)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing TensorProduct

universe u

/-! ### Pushouts of algebras from bijectivity of the canonical map -/

namespace Algebra.IsPushout

variable {R Sa Ra Sb : Type u} [CommRing R] [CommRing Sa] [CommRing Ra] [CommRing Sb]
  [Algebra R Sa] [Algebra R Ra] [Algebra R Sb] [Algebra Sa Sb] [Algebra Ra Sb]
  [IsScalarTower R Sa Sb] [IsScalarTower R Ra Sb]

/-- A commutative square of algebras is a pushout as soon as the canonical map out of the tensor
product of the two sides over the base is bijective. The map is `Sa`-linear, so a bijection makes
it an isomorphism of `Sa`-modules, which is the base-change condition. -/
public theorem of_bijective_tensorProduct_lift
    (h : Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R Sa Sb)
      (IsScalarTower.toAlgHom R Ra Sb) fun _ _ => .all _ _)) :
    Algebra.IsPushout R Sa Ra Sb := by
  set ψ : Sa ⊗[R] Ra →ₐ[Sa] Sb := Algebra.TensorProduct.lift
    (Algebra.ofId Sa Sb) (IsScalarTower.toAlgHom R Ra Sb) fun _ _ => .all _ _ with hψ
  have hagree : ∀ z : Sa ⊗[R] Ra, ψ z =
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R Sa Sb)
        (IsScalarTower.toAlgHom R Ra Sb) (fun _ _ => .all _ _) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [hψ, Algebra.ofId_apply]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have hbij : Function.Bijective ψ := by
    rwa [show ⇑ψ = _ from funext hagree]
  exact ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective ψ.toLinearMap hbij) fun c => by simp [hψ]⟩

end Algebra.IsPushout

namespace AlgebraicGeometry

/-- An identification of a ring with the localization of another at a prime transports along an
equality of primes. -/
private theorem isLocalizationAtPrime_of_eq {R T : Type u} [CommRing R] [CommRing T]
    [Algebra R T] {P Q : Ideal R} [P.IsPrime] [hQ : Q.IsPrime] (h : P = Q)
    [hloc : IsLocalization.AtPrime T Q] : IsLocalization.AtPrime T P := by
  subst h
  exact hloc

/-- Quasi-finiteness at a prime transports along an equality of primes. -/
private theorem algebraQuasiFiniteAt_of_eq {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    {P Q : Ideal T} [P.IsPrime] [Q.IsPrime] (h : P = Q)
    [hqf : Algebra.QuasiFiniteAt R Q] : Algebra.QuasiFiniteAt R P := by
  subst h
  exact hqf

/-- Quasi-finiteness of a ring homomorphism at a prime transports along an equality of primes. -/
private theorem ringHomQuasiFiniteAt_of_eq {R T : Type u} [CommRing R] [CommRing T]
    (ψ : R →+* T) {P Q : Ideal T} [P.IsPrime] [Q.IsPrime] (h : P = Q)
    (hqf : ψ.QuasiFiniteAt Q) : ψ.QuasiFiniteAt P := by
  subst h
  exact hqf

/-! ### The induced homomorphism of étale local rings on germs of sections -/

section Germ

variable (B : BigEtaleSite.{u}) {Y Z : Scheme.{u}} (hZ : B.Contains Z) (hY : B.Contains Y)
  (k : Z ⟶ Y) (z : GeometricPoint Z)

/-- The germ in the Zariski stalk at a point of a section over an open set, pushed into the étale
local ring there and carried along the homomorphism induced by a morphism of schemes, is the
étale germ of the pulled-back section. This is the Zariski-germ description of
`AlgebraicGeometry.etaleLocalRingHom`, obtained from its compatibility with the ordinary-to-étale
germ maps together with the compatibility of ordinary stalk maps with germs. -/
public theorem etaleLocalRingHom_structureSheafStalkFromLocalRing_germ
    (U : Y.Opens) (V : Z.Opens) (hVU : V ≤ k ⁻¹ᵁ U)
    (hz : z.hom (closedPoint z.residueField) ∈ V) (a : ↥Γ(Y, U)) :
    etaleLocalRingHom B hZ hY k z
        (structureSheafStalkFromLocalRing B Y hY (z.map k)
          (Y.presheaf.germ U ((z.map k).hom (closedPoint (z.map k).residueField))
            (hVU hz) a)) =
      structureSheafStalkFromLocalRing B Z hZ z
        (Z.presheaf.germ V (z.hom (closedPoint z.residueField)) hz
          ((k.appLE U V hVU).hom a)) := by
  refine Eq.trans (RingHom.congr_fun (etaleLocalRingHom_comp_fromLocalRing B hZ hY k z) _) ?_
  refine congrArg (structureSheafStalkFromLocalRing B Z hZ z) ?_
  refine Eq.trans (Scheme.Hom.germ_stalkMap_apply k U _ (hVU hz) a) ?_
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    Z.presheaf.germ_res_apply]

end Germ

section BaseChangeGerm

variable (B : BigEtaleSite.{u}) {X S S' X' : Scheme.{u}} (hS : B.Contains S)
  (hS' : B.Contains S') {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- Transport along an equality of geometric points of a homomorphism out of an étale local ring
does not change its value on the étale germ of a section over an open set: the two germs are the
germs of one section at one point. -/
public theorem etaleLocalRingHomCongr_structureSheafStalkFromLocalRing_germ {T : Type u}
    [CommRing T] {s t : GeometricPoint S} (e : s = t) (φ : ↥(etaleLocalRing B S hS s) →+* T)
    (U : S.Opens) (hs : s.hom (closedPoint s.residueField) ∈ U)
    (ht : t.hom (closedPoint t.residueField) ∈ U) (a : ↥Γ(S, U)) :
    etaleLocalRingHomCongr B hS e φ
        (structureSheafStalkFromLocalRing B S hS t
          (S.presheaf.germ U (t.hom (closedPoint t.residueField)) ht a)) =
      φ (structureSheafStalkFromLocalRing B S hS s
        (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hs a)) := by
  subst e
  rfl

/-- The canonical homomorphism from the étale local ring of the base at the image through `X` of a
geometric point of the fibre product, computed on the étale germ of a section over an open set of
`S`: it is the étale germ on `S'` of that section pulled back along `g`. -/
public theorem baseChangeEtaleLocalRingHom_structureSheafStalkFromLocalRing_germ
    (sq : IsPullback g' f' f g) (x' : GeometricPoint X') (U : S.Opens) (W : S'.Opens)
    (hWU : W ≤ g ⁻¹ᵁ U)
    (hx : ((x'.map g').map f).hom (closedPoint ((x'.map g').map f).residueField) ∈ U)
    (hx' : (x'.map f').hom (closedPoint (x'.map f').residueField) ∈ W) (a : ↥Γ(S, U)) :
    baseChangeEtaleLocalRingHom B hS hS' sq x'
        (structureSheafStalkFromLocalRing B S hS ((x'.map g').map f)
          (S.presheaf.germ U _ hx a)) =
      structureSheafStalkFromLocalRing B S' hS' (x'.map f')
        (S'.presheaf.germ W _ hx' ((g.appLE U W hWU).hom a)) :=
  (etaleLocalRingHomCongr_structureSheafStalkFromLocalRing_germ B hS
    (GeometricPoint.map_eq_of_isPullback sq x') (etaleLocalRingHom B hS' hS g (x'.map f'))
    U (hWU hx') hx a).trans
    (etaleLocalRingHom_structureSheafStalkFromLocalRing_germ B hS' hS g (x'.map f') U W hWU hx' a)

end BaseChangeGerm

/-! ### The square of étale local rings over a cartesian square is a pushout -/

section Pushout

variable (B : BigEtaleSite.{u}) {X S S' X' : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (hS' : B.Contains S') (hX' : B.Contains X') {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
  {f' : X' ⟶ S'}

/-- The square of étale local rings over a cartesian square is a pushout, given an affine chart of
the square at the point of the fibre product over which the sections form a pushout square of
rings and over which the sections of `g` are either integral, or of finite type and quasi-finite
at the prime of the point.

This presents the chart as an instance of the ring-theoretic situation of Lemma 0GIP: the Zariski
stalks at the four images of the point are the localizations of the four rings of sections at the
contractions of the prime of `Γ(X', U')` at the point, and the four étale local rings are strict
henselizations of those localizations, in the shape
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_isIntegral`,
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_quasiFiniteAt` and
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_forall_finset` consume. The three
cases differ only in which of those three is invoked at the end.

The third case is the one a cofiltered limit of schemes supplies: there the sections of `g` over
the chart are not of finite type over `Γ(S, U)`, but every finite subset of them comes from a
stage of the system, which is of finite type and quasi-finite there. It is stated with the ring
maps written out — `ψ` from the sections of the base to those of a stage, `φ` from a stage to
the sections of `g` — because the algebra structures of the ring-theoretic statement are the
ones this proof installs below, and a hypothesis cannot refer to them. -/
private theorem isPushout_etaleLocalRingHom_of_chart (sq : IsPullback g' f' f g)
    (x' : GeometricPoint X') {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) {W : S'.Opens} (hW : IsAffineOpen W) (hVU : V ≤ f ⁻¹ᵁ U)
    (hWU : W ≤ g ⁻¹ᵁ U) (hpV : (x'.map g').hom (closedPoint (x'.map g').residueField) ∈ V)
    (hpW : (x'.map f').hom (closedPoint (x'.map f').residueField) ∈ W)
    (hcase : RingHom.IsIntegral (g.appLE U W hWU).hom ∨
      ((g.appLE U W hWU).hom.FiniteType ∧ (g.appLE U W hWU).hom.QuasiFiniteAt
        (hW.primeIdealOf ⟨(x'.map f').hom (closedPoint (x'.map f').residueField),
          hpW⟩).asIdeal) ∨
      ∀ F : Finset ↥Γ(S', W), ∃ (T : Type u) (_ : CommRing T) (ψ : ↥Γ(S, U) →+* T)
        (φ : T →+* ↥Γ(S', W)), φ.comp ψ = (g.appLE U W hWU).hom ∧ ψ.FiniteType ∧
          ψ.QuasiFiniteAt ((hW.primeIdealOf ⟨(x'.map f').hom
            (closedPoint (x'.map f').residueField), hpW⟩).asIdeal.comap φ) ∧
          (F : Set ↥Γ(S', W)) ⊆ Set.range φ) :
    IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')) := by
  classical
  -- the chart of the fibre product over `V` and `W`, and the point in it
  have hU' := isAffineOpen_of_isPullback sq hU hV hW hVU hWU rfl
  have hpush := isPushout_appLE_of_isPullback_inter sq hU hV hW hVU hWU rfl inf_le_left inf_le_right
  set U' := g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W
  have hU'V : U' ≤ g' ⁻¹ᵁ V := inf_le_left
  have hU'W : U' ≤ f' ⁻¹ᵁ W := inf_le_right
  have hp : x'.hom (closedPoint x'.residueField) ∈ U' := ⟨hpV, hpW⟩
  have hpU : ((x'.map g').map f).hom (closedPoint ((x'.map g').map f).residueField) ∈ U :=
    hVU hpV
  -- the five rings of the chart, as algebras over one another
  let _ : Algebra ↥Γ(S, U) ↥Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let _ : Algebra ↥Γ(S, U) ↥Γ(S', W) := (g.appLE U W hWU).hom.toAlgebra
  let _ : Algebra ↥Γ(X, V) ↥Γ(X', U') := (g'.appLE V U' hU'V).hom.toAlgebra
  let _ : Algebra ↥Γ(S', W) ↥Γ(X', U') := (f'.appLE W U' hU'W).hom.toAlgebra
  let _ : Algebra ↥Γ(S, U) ↥Γ(X', U') :=
    ((g'.appLE V U' hU'V).hom.comp (f.appLE U V hVU).hom).toAlgebra
  have _ : IsScalarTower ↥Γ(S, U) ↥Γ(X, V) ↥Γ(X', U') := .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥Γ(S, U) ↥Γ(S', W) ↥Γ(X', U') :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  have _ : Algebra.IsPushout ↥Γ(S, U) ↥Γ(X, V) ↥Γ(S', W) ↥Γ(X', U') :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have _ : Algebra.IsPushout ↥Γ(S, U) ↥Γ(S', W) ↥Γ(X, V) ↥Γ(X', U') := .symm inferInstance
  -- the prime of the chart at the point of the fibre product, and its contractions
  have hPp : ((hU'.primeIdealOf ⟨_, hp⟩).asIdeal).IsPrime := (hU'.primeIdealOf ⟨_, hp⟩).isPrime
  have hPA : (hU'.primeIdealOf ⟨_, hp⟩).asIdeal.under ↥Γ(S, U) =
      (hU.primeIdealOf ⟨_, hpU⟩).asIdeal :=
    comap_primeIdealOf_appLE_comp_appLE hU hU' hVU hU'V hp hpU
  have hPB : (hU'.primeIdealOf ⟨_, hp⟩).asIdeal.under ↥Γ(S', W) =
      (hW.primeIdealOf ⟨_, hpW⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW U' hU' hU'W hp)
  have hPC : (hU'.primeIdealOf ⟨_, hp⟩).asIdeal.under ↥Γ(X, V) =
      (hV.primeIdealOf ⟨_, hpV⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V hV U' hU' hU'V hp)
  -- the Zariski stalks at the four images are the localizations at those contractions
  let _ : Algebra ↥Γ(S, U)
      ↥(S.presheaf.stalk (((x'.map g').map f).hom
        (closedPoint ((x'.map g').map f).residueField))) :=
    S.presheaf.algebra_section_stalk ⟨_, hpU⟩
  let _ : Algebra ↥Γ(S', W)
      ↥(S'.presheaf.stalk ((x'.map f').hom (closedPoint (x'.map f').residueField))) :=
    S'.presheaf.algebra_section_stalk ⟨_, hpW⟩
  let _ : Algebra ↥Γ(X, V)
      ↥(X.presheaf.stalk ((x'.map g').hom (closedPoint (x'.map g').residueField))) :=
    X.presheaf.algebra_section_stalk ⟨_, hpV⟩
  let _ : Algebra ↥Γ(X', U') ↥(X'.presheaf.stalk (x'.hom (closedPoint x'.residueField))) :=
    X'.presheaf.algebra_section_stalk ⟨_, hp⟩
  have _ : IsLocalization.AtPrime
      ↥(S.presheaf.stalk (((x'.map g').map f).hom
        (closedPoint ((x'.map g').map f).residueField)))
      ((hU'.primeIdealOf ⟨_, hp⟩).asIdeal.under ↥Γ(S, U)) :=
    isLocalizationAtPrime_of_eq hPA (hloc := hU.isLocalization_stalk ⟨_, hpU⟩)
  have _ : IsLocalization.AtPrime
      ↥(S'.presheaf.stalk ((x'.map f').hom (closedPoint (x'.map f').residueField)))
      ((hU'.primeIdealOf ⟨_, hp⟩).asIdeal.under ↥Γ(S', W)) :=
    isLocalizationAtPrime_of_eq hPB (hloc := hW.isLocalization_stalk ⟨_, hpW⟩)
  have _ : IsLocalization.AtPrime
      ↥(X.presheaf.stalk ((x'.map g').hom (closedPoint (x'.map g').residueField)))
      ((hU'.primeIdealOf ⟨_, hp⟩).asIdeal.under ↥Γ(X, V)) :=
    isLocalizationAtPrime_of_eq hPC (hloc := hV.isLocalization_stalk ⟨_, hpV⟩)
  have _ : IsLocalization.AtPrime
      ↥(X'.presheaf.stalk (x'.hom (closedPoint x'.residueField)))
      (hU'.primeIdealOf ⟨_, hp⟩).asIdeal := hU'.isLocalization_stalk ⟨_, hp⟩
  -- the structure maps from the Zariski stalks to the étale local rings are local
  have _ : IsLocalHom (algebraMap
      ↥(S.presheaf.stalk (((x'.map g').map f).hom
        (closedPoint ((x'.map g').map f).residueField)))
      ↥(etaleLocalRing B S hS ((x'.map g').map f))) :=
    IsLocalRing.IsHenselization.isLocalHom
      (L := ResidueField ↥(etaleLocalRing B S hS ((x'.map g').map f)))
  have _ : IsLocalHom (algebraMap
      ↥(S'.presheaf.stalk ((x'.map f').hom (closedPoint (x'.map f').residueField)))
      ↥(etaleLocalRing B S' hS' (x'.map f'))) :=
    IsLocalRing.IsHenselization.isLocalHom
      (L := ResidueField ↥(etaleLocalRing B S' hS' (x'.map f')))
  have _ : IsLocalHom (algebraMap
      ↥(X.presheaf.stalk ((x'.map g').hom (closedPoint (x'.map g').residueField)))
      ↥(etaleLocalRing B X hX (x'.map g'))) :=
    IsLocalRing.IsHenselization.isLocalHom
      (L := ResidueField ↥(etaleLocalRing B X hX (x'.map g')))
  have _ : IsLocalHom (algebraMap ↥(X'.presheaf.stalk (x'.hom (closedPoint x'.residueField)))
      ↥(etaleLocalRing B X' hX' x')) :=
    IsLocalRing.IsHenselization.isLocalHom
      (L := ResidueField ↥(etaleLocalRing B X' hX' x'))
  -- the chart rings are algebras over the étale local rings through the Zariski stalks
  let _ : Algebra ↥Γ(S, U) ↥(etaleLocalRing B S hS ((x'.map g').map f)) :=
    ((structureSheafStalkFromLocalRing B S hS ((x'.map g').map f)).comp
      (S.presheaf.germ U _ hpU).hom).toAlgebra
  let _ : Algebra ↥Γ(S', W) ↥(etaleLocalRing B S' hS' (x'.map f')) :=
    ((structureSheafStalkFromLocalRing B S' hS' (x'.map f')).comp
      (S'.presheaf.germ W _ hpW).hom).toAlgebra
  let _ : Algebra ↥Γ(X, V) ↥(etaleLocalRing B X hX (x'.map g')) :=
    ((structureSheafStalkFromLocalRing B X hX (x'.map g')).comp
      (X.presheaf.germ V _ hpV).hom).toAlgebra
  let _ : Algebra ↥Γ(X', U') ↥(etaleLocalRing B X' hX' x') :=
    ((structureSheafStalkFromLocalRing B X' hX' x').comp
      (X'.presheaf.germ U' _ hp).hom).toAlgebra
  have _ : IsScalarTower ↥Γ(S, U)
      ↥(S.presheaf.stalk (((x'.map g').map f).hom
        (closedPoint ((x'.map g').map f).residueField)))
      ↥(etaleLocalRing B S hS ((x'.map g').map f)) := .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥Γ(S', W)
      ↥(S'.presheaf.stalk ((x'.map f').hom (closedPoint (x'.map f').residueField)))
      ↥(etaleLocalRing B S' hS' (x'.map f')) := .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥Γ(X, V)
      ↥(X.presheaf.stalk ((x'.map g').hom (closedPoint (x'.map g').residueField)))
      ↥(etaleLocalRing B X hX (x'.map g')) := .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥Γ(X', U') ↥(X'.presheaf.stalk (x'.hom (closedPoint x'.residueField)))
      ↥(etaleLocalRing B X' hX' x') := .of_algebraMap_eq fun _ => rfl
  -- the square of étale local rings
  let _ : Algebra ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B S' hS' (x'.map f')) :=
    (baseChangeEtaleLocalRingHom B hS hS' sq x').toAlgebra
  let _ : Algebra ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B X hX (x'.map g')) :=
    (etaleLocalRingHom B hX hS f (x'.map g')).toAlgebra
  let _ : Algebra ↥(etaleLocalRing B S' hS' (x'.map f')) ↥(etaleLocalRing B X' hX' x') :=
    (etaleLocalRingHom B hX' hS' f' x').toAlgebra
  let _ : Algebra ↥(etaleLocalRing B X hX (x'.map g')) ↥(etaleLocalRing B X' hX' x') :=
    (etaleLocalRingHom B hX' hX g' x').toAlgebra
  let _ : Algebra ↥(etaleLocalRing B S hS ((x'.map g').map f)) ↥(etaleLocalRing B X' hX' x') :=
    ((etaleLocalRingHom B hX' hX g' x').comp
      (etaleLocalRingHom B hX hS f (x'.map g'))).toAlgebra
  have _ : IsScalarTower ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B X hX (x'.map g')) ↥(etaleLocalRing B X' hX' x') :=
    .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B S' hS' (x'.map f')) ↥(etaleLocalRing B X' hX' x') :=
    .of_algebraMap_eq'
      (etaleLocalRingHom_comp_baseChangeEtaleLocalRingHom B hS hS' hX hX' sq x')
  have _ : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B S' hS' (x'.map f'))) :=
    inferInstanceAs (IsLocalHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
  have _ : IsLocalHom (algebraMap ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B X hX (x'.map g'))) :=
    inferInstanceAs (IsLocalHom (etaleLocalRingHom B hX hS f (x'.map g')))
  have _ : IsLocalHom (algebraMap ↥(etaleLocalRing B X hX (x'.map g'))
      ↥(etaleLocalRing B X' hX' x')) :=
    inferInstanceAs (IsLocalHom (etaleLocalRingHom B hX' hX g' x'))
  -- the chart rings as algebras over the far corners, through two routes each
  let _ : Algebra ↥Γ(S, U) ↥(etaleLocalRing B S' hS' (x'.map f')) :=
    ((algebraMap ↥Γ(S', W) ↥(etaleLocalRing B S' hS' (x'.map f'))).comp
      (algebraMap ↥Γ(S, U) ↥Γ(S', W))).toAlgebra
  let _ : Algebra ↥Γ(S, U) ↥(etaleLocalRing B X hX (x'.map g')) :=
    ((algebraMap ↥Γ(X, V) ↥(etaleLocalRing B X hX (x'.map g'))).comp
      (algebraMap ↥Γ(S, U) ↥Γ(X, V))).toAlgebra
  let _ : Algebra ↥Γ(S', W) ↥(etaleLocalRing B X' hX' x') :=
    ((algebraMap ↥Γ(X', U') ↥(etaleLocalRing B X' hX' x')).comp
      (algebraMap ↥Γ(S', W) ↥Γ(X', U'))).toAlgebra
  let _ : Algebra ↥Γ(X, V) ↥(etaleLocalRing B X' hX' x') :=
    ((algebraMap ↥Γ(X', U') ↥(etaleLocalRing B X' hX' x')).comp
      (algebraMap ↥Γ(X, V) ↥Γ(X', U'))).toAlgebra
  have _ : IsScalarTower ↥Γ(S, U) ↥Γ(S', W) ↥(etaleLocalRing B S' hS' (x'.map f')) :=
    .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥Γ(S, U) ↥Γ(X, V) ↥(etaleLocalRing B X hX (x'.map g')) :=
    .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥Γ(S', W) ↥Γ(X', U') ↥(etaleLocalRing B X' hX' x') :=
    .of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower ↥Γ(X, V) ↥Γ(X', U') ↥(etaleLocalRing B X' hX' x') :=
    .of_algebraMap_eq fun _ => rfl
  -- the four compatibilities of the two routes: this is where the germ lemmas enter
  have _ : IsScalarTower ↥Γ(S, U) ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B S' hS' (x'.map f')) :=
    .of_algebraMap_eq fun a =>
      (baseChangeEtaleLocalRingHom_structureSheafStalkFromLocalRing_germ B hS hS' sq x' U W hWU
        hpU hpW a).symm
  have _ : IsScalarTower ↥Γ(S, U) ↥(etaleLocalRing B S hS ((x'.map g').map f))
      ↥(etaleLocalRing B X hX (x'.map g')) :=
    .of_algebraMap_eq fun a =>
      (etaleLocalRingHom_structureSheafStalkFromLocalRing_germ B hX hS f (x'.map g') U V hVU
        hpV a).symm
  have _ : IsScalarTower ↥Γ(S', W) ↥(etaleLocalRing B S' hS' (x'.map f'))
      ↥(etaleLocalRing B X' hX' x') :=
    .of_algebraMap_eq fun a =>
      (etaleLocalRingHom_structureSheafStalkFromLocalRing_germ B hX' hS' f' x' W U' hU'W
        hp a).symm
  have _ : IsScalarTower ↥Γ(X, V) ↥(etaleLocalRing B X hX (x'.map g'))
      ↥(etaleLocalRing B X' hX' x') :=
    .of_algebraMap_eq fun a =>
      (etaleLocalRingHom_structureSheafStalkFromLocalRing_germ B hX' hX g' x' V U' hU'V
        hp a).symm
  -- Lemma 0GIP, in whichever of its three cases the chart satisfies
  refine CommRingCat.isPushout_iff_isPushout.mpr
    (Algebra.IsPushout.of_bijective_tensorProduct_lift ?_)
  refine IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_forall_finset
    (A := ↥Γ(S, U)) (B := ↥Γ(S', W)) (C := ↥Γ(X, V)) (D := ↥Γ(X', U'))
    (hU'.primeIdealOf ⟨_, hp⟩).asIdeal
    (Bp := ↥(S'.presheaf.stalk ((x'.map f').hom (closedPoint (x'.map f').residueField))))
    (Cp := ↥(X.presheaf.stalk ((x'.map g').hom (closedPoint (x'.map g').residueField))))
    (Dp := ↥(X'.presheaf.stalk (x'.hom (closedPoint x'.residueField))))
    (Ash := ↥(etaleLocalRing B S hS ((x'.map g').map f)))
    (Bsh := ↥(etaleLocalRing B S' hS' (x'.map f')))
    (Csh := ↥(etaleLocalRing B X hX (x'.map g')))
    (Dsh := ↥(etaleLocalRing B X' hX' x'))
    (Ap := ↥(S.presheaf.stalk (((x'.map g').map f).hom
      (closedPoint ((x'.map g').map f).residueField)))) fun F => ?_
  rcases hcase with hint | ⟨hft, hqf⟩ | hcol
  · have _ : Algebra.IsIntegral ↥Γ(S, U) ↥Γ(S', W) := ⟨hint⟩
    exact IsLocalRing.IsHenselization.forall_finset_of_isIntegral _ F
  · have _ : Algebra.FiniteType ↥Γ(S, U) ↥Γ(S', W) := hft
    exact ⟨_, inferInstance, inferInstance, AlgHom.id _ _, inferInstance,
      algebraQuasiFiniteAt_of_eq hPB (hqf := hqf), fun x _ => ⟨x, rfl⟩⟩
  · obtain ⟨T, _, ψ, φ, hcomp, hft, hqf, hrange⟩ := hcol F
    let _ : Algebra ↥Γ(S, U) T := ψ.toAlgebra
    exact ⟨T, inferInstance, inferInstance,
      { φ with commutes' := fun r => DFunLike.congr_fun hcomp r }, hft,
      algebraQuasiFiniteAt_of_eq (congrArg (Ideal.comap φ) hPB) (hqf := hqf), hrange⟩

/-- **The scheme-level Lemma 0GIP, integral case.** For a cartesian square of schemes

```
X' --g'--> X
|f'        |f
S' --g---> S
```

with `g` integral, and a geometric point `x'` of `X'` with images `x` in `X`, `s'` in `S'` and `s`
in `S`, the commutative square of étale local rings

`𝒪^sh_{S,s} ⟶ 𝒪^sh_{S',s'}`, `𝒪^sh_{S,s} ⟶ 𝒪^sh_{X,x}`, both followed by maps to `𝒪^sh_{X',x'}`

is a pushout square of commutative rings, that is

`𝒪^sh_{X',x'} = 𝒪^sh_{S',s'} ⊗_{𝒪^sh_{S,s}} 𝒪^sh_{X,x}`.

That it commutes is
`AlgebraicGeometry.etaleLocalRingHom_comp_baseChangeEtaleLocalRingHom`; the image of `x'` in `S`
is read through `X`, so the étale local ring of `S` is the one at `(x'.map g').map f`.

The proof takes an affine open `U` of `S` containing the image of `x'`, an affine open `V` of `X`
over `U` containing the image of `x'` there, and `W = g⁻¹(U)`, which is affine because an integral
morphism is affine and which carries integral sections. Over that chart the sections of the four
schemes form a pushout square of rings whose strict henselizations at the images of `x'` are the
four étale local rings, and
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_isIntegral` applies. Taking
`W = g⁻¹(U)` rather than an arbitrary affine open of `S'` over `U` is what makes `Γ(S, U) ⟶
Γ(S', W)` integral.

This is the geometric reading of clause (4) of Stacks 0GIP, which is an algebra statement about
ring maps `A → B`, `A → C` and a prime of a tensor product; the hypothesis that `B` is integral
over `A` becomes `IsIntegralHom g`, and the conclusion `B^sh ⊗_(A^sh) C^sh = D^sh` becomes the
statement that the square of étale local rings at a geometric point of the fibre product is a
pushout square of commutative rings. It carries no `@[stacks 0GIP]` attribute: the tag is an
algebra lemma and is covered by
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_isIntegral`, from which this is
deduced. The image in `S` of the geometric point is read through `X`, so the étale local ring of
`S` is the one at `(x'.map g').map f`, and the comparison with the reading through `S'` is
`AlgebraicGeometry.baseChangeEtaleLocalRingHom`. -/
theorem isPushout_etaleLocalRingHom_of_isIntegralHom (sq : IsPullback g' f' f g)
    [IsIntegralHom g] (x' : GeometricPoint X') :
    IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')) := by
  classical
  obtain ⟨U, hU, V, hV, _, _, hVU, hWU, hpV, hpW⟩ :=
    exists_affineOpen_chart_of_isPullback sq (x'.hom (closedPoint x'.residueField))
  refine isPushout_etaleLocalRingHom_of_chart B hX hS hS' hX' sq x' hU hV (hU.preimage g) hVU
    le_rfl hpV (hWU hpW) (Or.inl ?_)
  rw [show g.appLE U (g ⁻¹ᵁ U) le_rfl = g.app U by simp [Scheme.Hom.appLE]]
  exact IsIntegralHom.isIntegral_app g (U : S.Opens) hU

/-- **The scheme-level Lemma 0GIP, quasi-finite case.** For a cartesian square of schemes

```
X' --g'--> X
|f'        |f
S' --g---> S
```

with `g` locally of finite type and locally quasi-finite, and a geometric point `x'` of `X'`, the
commutative square of étale local rings at `x'` and at its images is a pushout square of
commutative rings, that is

`𝒪^sh_{X',x'} = 𝒪^sh_{S',s'} ⊗_{𝒪^sh_{S,s}} 𝒪^sh_{X,x}`.

Both hypotheses on `g` are needed: a morphism locally quasi-finite in the sense of Tag 03WT is in
particular locally of finite type, while
`AlgebraicGeometry.LocallyQuasiFinite` does not include that condition, so the two together are
what the source asks for.

The proof takes any affine chart `U ⊆ S`, `V ⊆ X`, `W ⊆ S'` of the square at the image of `x'`,
over which the sections of `g` are of finite type and quasi-finite at the prime of the image of
`x'`, and applies
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_quasiFiniteAt`.

This is the geometric reading of clause (1) of Stacks 0GIP, which is an algebra statement about
ring maps and a prime of a tensor product; the hypothesis that `A → B` be of finite type and
quasi-finite at `P ∩ B` becomes `LocallyOfFiniteType g` together with `LocallyQuasiFinite g`, and
the conclusion `B^sh ⊗_(A^sh) C^sh = D^sh` becomes the statement that the square of étale local
rings at a geometric point of the fibre product is a pushout square of commutative rings. It
carries no `@[stacks 0GIP]` attribute: the tag is an algebra lemma and is covered by
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_quasiFiniteAt`, from which this is
deduced. The image in `S` of the geometric point is read through `X`, so the étale local ring of
`S` is the one at `(x'.map g').map f`. -/
theorem isPushout_etaleLocalRingHom_of_locallyQuasiFinite (sq : IsPullback g' f' f g)
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] (x' : GeometricPoint X') :
    IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')) := by
  classical
  obtain ⟨U, hU, V, hV, W, hW, hVU, hWU, hpV, hpW⟩ :=
    exists_affineOpen_chart_of_isPullback sq (x'.hom (closedPoint x'.residueField))
  refine isPushout_etaleLocalRingHom_of_chart B hX hS hS' hX' sq x' hU hV hW hVU hWU hpV hpW
    (Or.inr (Or.inl ⟨LocallyOfFiniteType.finiteType_appLE g hU hW hWU, ?_⟩))
  exact (g.quasiFiniteAt ((x'.map f').hom (closedPoint (x'.map f').residueField))).quasiFiniteAt
    hW hU hWU hpW

end Pushout

/-! ### The limit case: base change along a cofiltered limit of quasi-finite schemes -/

section PushoutLimit

variable (B : BigEtaleSite.{u}) {X S X' : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)] {c : Cone D} (hc : IsLimit c)
  (hS' : B.Contains c.pt) (hX' : B.Contains X') {f : X ⟶ S} {g : c.pt ⟶ S} {g' : X' ⟶ X}
  {f' : X' ⟶ c.pt}

include hc in
/-- **The scheme-level Lemma 0GIP, limit case.** Let `{ Dᵢ }` be an inverse system of schemes
indexed by a cofiltered category, with affine transition morphisms, let `c` be a limit cone over
it, and let every stage be locally of finite type and locally quasi-finite over `S`, compatibly
with the transition morphisms and with a morphism `g : lim Dᵢ ⟶ S`. For a cartesian square

```
X' --g'--> X
|f'        |f
lim Dᵢ --g--> S
```

and a geometric point `x'` of `X'`, the commutative square of étale local rings at `x'` and at
its images is a pushout square of commutative rings, that is

`𝒪^sh_{X',x'} = 𝒪^sh_{S',s'} ⊗_{𝒪^sh_{S,s}} 𝒪^sh_{X,x}` with `S' = lim Dᵢ`.

The chart of the square is built so that its open of `lim Dᵢ` is the preimage of an affine open
`W₀` of one stage `D i₀`: that preimage is affine because the limit projection of a system with
affine transition morphisms is affine, and it lies over the affine open `U` of `S` because `W₀`
was chosen inside `p i₀ ⁻¹ᵁ U`. Over such a chart the sections of `g` need not be of finite type
over `Γ(S, U)`, but every finite subset of them comes from the sections of a later stage over
the preimage of `W₀` there — that is
`AlgebraicGeometry.exists_subset_range_appLE_π_of_isAffineOpen_of_isLimit` — and those sections
are of finite type and quasi-finite over `Γ(S, U)` because the stage is locally of finite type
and locally quasi-finite over `S`. That is exactly the covered case of Lemma 0GIP.

This is the geometric reading of clause (2) of Stacks 0GIP, which is an algebra statement; the
hypothesis that `B` be a filtered colimit of quasi-finite `A`-algebras becomes the presentation
of `S'` as a cofiltered limit of schemes locally quasi-finite over `S` with affine transition
morphisms. It carries no `@[stacks 0GIP]` attribute: the tag is an algebra lemma and is covered
by `IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_ind_quasiFinite` and
`IsLocalRing.IsHenselization.bijective_tensorProduct_lift_of_forall_finset`, from which this is
deduced. The image in `S` of the geometric point is read through `X`, so the étale local ring of
`S` is the one at `(x'.map g').map f`. -/
theorem isPushout_etaleLocalRingHom_of_limit (sq : IsPullback g' f' f g)
    (p : ∀ i : I, D.obj i ⟶ S) (hp : ∀ i : I, c.π.app i ≫ p i = g)
    (hcompat : ∀ {i j : I} (a : i ⟶ j), D.map a ≫ p j = p i)
    [∀ i : I, LocallyOfFiniteType (p i)] [∀ i : I, LocallyQuasiFinite (p i)]
    (x' : GeometricPoint X') :
    IsPushout (CommRingCat.ofHom (baseChangeEtaleLocalRingHom B hS hS' sq x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX hS f (x'.map g')))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hS' f' x'))
      (CommRingCat.ofHom (etaleLocalRingHom B hX' hX g' x')) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U, hU, V, hV, _, _, hVU, hWU', hpV, hpW⟩ :=
    exists_affineOpen_chart_of_isPullback sq (x'.hom (closedPoint x'.residueField))
  have hpi : c.π.app i₀ (f' (x'.hom (closedPoint x'.residueField))) ∈
      (p i₀ ⁻¹ᵁ (U : S.Opens)).1 := by
    have h := hWU' hpW
    rwa [← hp i₀, Scheme.Hom.comp_preimage] at h
  obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hpW₀, hW₀U⟩ :=
    (D.obj i₀).isBasis_affineOpens.exists_subset_of_mem_open hpi (p i₀ ⁻¹ᵁ (U : S.Opens)).2
  have _ : IsAffineHom (c.π.app i₀) := isAffineHom_π_app D c hc i₀
  have hW : IsAffineOpen (c.π.app i₀ ⁻¹ᵁ (W₀ : (D.obj i₀).Opens)) := hW₀.preimage (c.π.app i₀)
  have hle₀ : ∀ {Y : Scheme.{u}} (k : Y ⟶ D.obj i₀) (q : Y ⟶ S), k ≫ p i₀ = q →
      k ⁻¹ᵁ (W₀ : (D.obj i₀).Opens) ≤ q ⁻¹ᵁ (U : S.Opens) := fun k q h => by
    rw [← h, Scheme.Hom.comp_preimage]
    exact k.preimage_mono hW₀U
  have hWU := hle₀ _ _ (hp i₀)
  refine isPushout_etaleLocalRingHom_of_chart B hX hS hS' hX' sq x' hU hV hW hVU hWU hpV hpW₀
    (Or.inr (Or.inr fun F => ?_))
  obtain ⟨j, a, hF⟩ := exists_subset_range_appLE_π_of_isAffineOpen_of_isLimit D c hc i₀ hW₀ F
  have hWj : IsAffineOpen (D.map a ⁻¹ᵁ (W₀ : (D.obj i₀).Opens)) := hW₀.preimage (D.map a)
  have hWjU := hle₀ _ _ (hcompat a)
  have hle : c.π.app i₀ ⁻¹ᵁ (W₀ : (D.obj i₀).Opens) ≤
      c.π.app j ⁻¹ᵁ (D.map a ⁻¹ᵁ (W₀ : (D.obj i₀).Opens)) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, c.w])
  refine ⟨↥Γ(D.obj j, D.map a ⁻¹ᵁ (W₀ : (D.obj i₀).Opens)), inferInstance,
    ((p j).appLE (U : S.Opens) (D.map a ⁻¹ᵁ (W₀ : (D.obj i₀).Opens)) hWjU).hom,
    ((c.π.app j).appLE (D.map a ⁻¹ᵁ (W₀ : (D.obj i₀).Opens))
      (c.π.app i₀ ⁻¹ᵁ (W₀ : (D.obj i₀).Opens)) hle).hom, ?_,
    LocallyOfFiniteType.finiteType_appLE (p j) hU hWj hWjU, ?_, hF⟩
  · rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_congr_hom (hp j) (U : S.Opens) _ _ hWU)
  · exact ringHomQuasiFiniteAt_of_eq _
      (congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE _ hWj _ hW hle hpW₀))
      (((p j).quasiFiniteAt
          (c.π.app j (f' (x'.hom (closedPoint x'.residueField))))).quasiFiniteAt
        hWj hU hWjU (hle hpW₀))

end PushoutLimit

end AlgebraicGeometry

end
