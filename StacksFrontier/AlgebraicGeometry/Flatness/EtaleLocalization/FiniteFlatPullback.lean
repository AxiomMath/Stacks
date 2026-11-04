module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.FlatPullback
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatPoint
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Module.LocallyFree.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Weakly associated points and finite flat pullback

For a finite flat morphism of schemes, a point is weakly associated to the pullback of a
quasi-coherent module exactly when its image is weakly associated to the original module.

One implication is the general flat-pullback statement of Stacks 05F0: a finite morphism has
discrete fibres, so every point of the source is a generic point of its fibre. The other
implication is local and reduces to the ring-theoretic statement that for a finite flat
`A`-algebra `B` a prime of `A` weakly associated to `B ⊗[A] M` is weakly associated to `M`
itself, which follows after localising at the prime, where `B` becomes free.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_finite_flat` characterises weakly
  associated points of a pullback along a finite flat morphism.

## Implementation notes

Pullback is Mathlib's canonical functor `AlgebraicGeometry.Scheme.Modules.pullback`. The image
point is written as `g.base t`, incorporating into the statement the source's choice of the
image point.

The reduction to the affine case proceeds in two steps. A finite morphism is affine, so an
affine open of the target has affine preimage, and the restriction of `g` to those two opens is
again finite and flat (transported along `AlgebraicGeometry.arrowResLEAppIso`). On affine
schemes the morphism is then replaced by `Spec` of the induced map of global sections, modulo
the two open immersions `X.isoSpec.hom` and `Y.isoSpec.inv`, where
`AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion` applies.

## References

* [Stacks Project, Tag 05FN](https://stacks.math.columbia.edu/tag/05FN)
-/

@[expose] public section

open CategoryTheory
open TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

/-- For a finite flat algebra `B` over `A`, a prime weakly associated to `B ⊗[A] M` is weakly
associated to `M`. After localising at the prime, `B` is free over the local ring, and weak
association descends through a tensor product with a free module. -/
@[ega "IV 3.3.8" "special case"]
private theorem weaklyAssociatedPrime_of_finiteFlat_tensorProduct
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Finite A B] [Module.Flat A B]
    {p : Ideal A} [p.IsPrime]
    (h : IsWeaklyAssociatedPrime A (B ⊗[A] M) p) : IsWeaklyAssociatedPrime A M p := by
  let R := Localization.AtPrime p
  let S := p.primeCompl
  have : Module.Free R (LocalizedModule S B) := Module.free_of_flat_of_isLocalRing
  have hloc := (weaklyAssociated_iff_localization p).mp h
  let e₀ : LocalizedModule S (B ⊗[A] M) ≃ₗ[R] R ⊗[A] (B ⊗[A] M) :=
    LocalizedModule.equivTensorProduct S (B ⊗[A] M)
  let e₁ : R ⊗[A] (B ⊗[A] M) ≃ₗ[R] (R ⊗[A] B) ⊗[R] (R ⊗[A] M) :=
    AlgebraTensorModule.distribBaseChange A R B M
  let eB : LocalizedModule S B ≃ₗ[R] R ⊗[A] B := LocalizedModule.equivTensorProduct S B
  let eM : LocalizedModule S M ≃ₗ[R] R ⊗[A] M := LocalizedModule.equivTensorProduct S M
  let e : LocalizedModule S (B ⊗[A] M) ≃ₗ[R]
      LocalizedModule S B ⊗[R] LocalizedModule S M :=
    e₀.trans (e₁.trans (TensorProduct.congr eB.symm eM.symm))
  have hlocal : IsWeaklyAssociatedPrime R
      (LocalizedModule S B ⊗[R] LocalizedModule S M) (IsLocalRing.maximalIdeal R) := by
    have hloc' : IsWeaklyAssociatedPrime R (LocalizedModule S (B ⊗[A] M))
        (IsLocalRing.maximalIdeal R) := by
      change ∃ z, (IsLocalRing.maximalIdeal R) ∈
        (annihilatorOfElem_semiring (R := R) z).minimalPrimes at hloc
      obtain ⟨z, hz⟩ := hloc
      refine ⟨z, ?_⟩
      have heq : annihilatorOfElem_semiring (R := R) z = (R ∙ z).annihilator := by
        ext r
        simp [annihilatorOfElem_semiring]
      rwa [← heq]
    exact Module.weaklyAssociatedPrimes_subset_of_injective
      (f := e.toLinearMap) e.injective hloc'
  exact (weaklyAssociated_iff_localization p).mpr
    (IsWeaklyAssociatedPrime.of_tensorProduct_free (R := R)
      (M := LocalizedModule S M) (P := LocalizedModule S B) hlocal)

/-- The fibres of a finite morphism are discrete, so every point of the source is a generic
point of the fibre through it. -/
private theorem asFiber_mem_genericPoints_of_finite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (x : X) : f.asFiber x ∈ genericPoints (f.fiber (f x)) := by
  let Z := f.fiber (f x)
  let y : Z := f.asFiber x
  have : DiscreteTopology Z := inferInstance
  have hcomp : irreducibleComponent y = {y} := by
    obtain ⟨z, hz⟩ :=
      (isIrreducible_iff_singleton (S := irreducibleComponent y)).mp
        isIrreducible_irreducibleComponent
    have hy : y ∈ ({z} : Set Z) := by
      simpa [hz] using (mem_irreducibleComponent (x := y))
    have : y = z := Set.mem_singleton_iff.mp hy
    simpa [this] using hz
  rw [genericPoints]
  show closure ({y} : Set Z) ∈ irreducibleComponents Z
  rw [show closure ({y} : Set Z) = {y} by simp, ← hcomp]
  exact irreducibleComponent_mem_irreducibleComponents y

/-- A point is weakly associated to the pullback along `h = f ≫ g` exactly when it is weakly
associated to the iterated pullback along `g` and then `f`. -/
private theorem isWeaklyAssociatedPoint_pullback_comp_iff {X Y Z : Scheme.{u}}
    {h : X ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : h = f ≫ g) (G : Z.Modules) (x : X) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback h).obj G) x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj G)) x := by
  subst hfg
  exact (isWeaklyAssociatedPoint_iff_of_iso ((Scheme.Modules.pullbackComp f g).app G) x).symm

/-- The nontrivial implication for a finite flat map of affine spectra: a point weakly
associated to the pullback has weakly associated image. -/
private theorem specPullback_reverse
    (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
    (hfin : φ.Finite) (hflat : φ.Flat)
    (G : (Spec (.of R)).Modules) [G.IsQuasicoherent] (x : Spec (.of S)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj G) x →
      Stacks.Divisors.IsWeaklyAssociatedPoint G
        ((Spec.map (CommRingCat.ofHom φ)).base x) := by
  let A := CommRingCat.of R
  let B := CommRingCat.of S
  let f := CommRingCat.ofHom φ
  let p : Ideal R := Ideal.comap φ x.asIdeal
  have : x.asIdeal.IsPrime := x.isPrime
  have : p.IsPrime := Ideal.IsPrime.comap _
  let : Algebra R S := φ.toAlgebra
  have : Module.Finite R S := RingHom.finite_algebraMap.mp hfin
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  have : ((Scheme.Modules.pullback (Spec.map f)).obj G).IsQuasicoherent :=
    @_root_.AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent
      (Spec (.of S)).toRingedSpace (Spec (.of R)).toRingedSpace
      (Spec.map f).toLRSHom.toShHom G (inferInstance : G.IsQuasicoherent)
  intro hx
  have hq : IsWeaklyAssociatedPrime S
      ((moduleSpecΓFunctor (R := B)).obj ((Scheme.Modules.pullback (Spec.map f)).obj G))
      x.asIdeal :=
    (isWeaklyAssociatedPoint_Spec_iff S _ x).mp hx
  let N := ((moduleSpecΓFunctor (R := B)).obj ((Scheme.Modules.pullback (Spec.map f)).obj G))
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hpN : IsWeaklyAssociatedPrime R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        ((moduleSpecΓFunctor (R := B)).obj
          ((Scheme.Modules.pullback (Spec.map f)).obj G))) p :=
    comap_isWeaklyAssociatedPrime_of_finite (R := R) (S := S)
      (M := ((moduleSpecΓFunctor (R := B)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj G)))
      inferInstance x.asIdeal hq
  let e := (ModuleCat.restrictScalars (algebraMap R S)).mapIso
    (specPullbackSectionsIso A B f G)
  have he : Function.Injective e.hom.hom := fun a b hab => by
    simpa using congrArg e.inv.hom hab
  have hpT : IsWeaklyAssociatedPrime R (S ⊗[R] ((moduleSpecΓFunctor (R := A)).obj G)) p := by
    show IsWeaklyAssociatedPrime R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj
          ((moduleSpecΓFunctor (R := A)).obj G))) p
    exact Module.weaklyAssociatedPrimes_subset_of_injective (f := e.hom.hom) he hpN
  have hpM := weaklyAssociatedPrime_of_finiteFlat_tensorProduct (A := R) (B := S)
    (M := ((moduleSpecΓFunctor (R := A)).obj G)) hpT
  exact (isWeaklyAssociatedPoint_Spec_iff R G ((Spec.map f).base x)).mpr hpM

/-- The nontrivial implication for a finite flat morphism of affine schemes. -/
private theorem finiteFlat_affine_pullback_reverse
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (h : X ⟶ Y) [IsFinite h] [Flat h]
    (G : Y.Modules) [G.IsQuasicoherent] (x : X) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback h).obj G) x →
      Stacks.Divisors.IsWeaklyAssociatedPoint G (h.base x) := by
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let φ : R →+* S := h.appTop.hom
  let hSpec : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ)
  let jX : X ⟶ Spec (.of S) := X.isoSpec.hom
  let jYinv : Spec (.of R) ⟶ Y := Y.isoSpec.inv
  let k : Spec (.of S) ⟶ Y := hSpec ≫ jYinv
  let G' := (Scheme.Modules.pullback jYinv).obj G
  let x' : Spec (.of S) := jX.base x
  have hfin : φ.Finite := h.finite_appTop
  have hflat : φ.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 inferInstance
  have : G'.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion jYinv G
  have hh : h = jX ≫ k := by
    simpa [jX, hSpec, k, jYinv, φ] using
      (Scheme.isoSpec_hom_naturality_assoc h Y.isoSpec.inv).symm
  have hxcomp : h.base x = jYinv.base (hSpec.base x') := by
    simpa [x', jX, k] using congrArg (fun q : X ⟶ Y => q.base x) hh
  intro hx
  have hx1 := (isWeaklyAssociatedPoint_pullback_comp_iff hh G x).mp hx
  have hx2 : Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback k).obj G) x' :=
    (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion jX _ x).mp hx1
  have hx3 : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback hSpec).obj G') x' :=
    (isWeaklyAssociatedPoint_pullback_comp_iff (h := k) rfl G x').mp hx2
  rw [hxcomp]
  exact (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion jYinv G (hSpec.base x')).mp
    (specPullback_reverse R S φ hfin hflat G' x' hx3)

/-- The nontrivial implication of Stacks 05FN, obtained from the affine case by restricting to
an affine open of the target and its preimage. -/
private theorem finiteFlat_pullback_reverse
    {T S : Scheme.{u}} (g : T ⟶ S) [IsFinite g] [Flat g]
    (G : S.Modules) [G.IsQuasicoherent] (t : T) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback g).obj G) t →
      Stacks.Divisors.IsWeaklyAssociatedPoint G (g.base t) := by
  obtain ⟨V, hV, htV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show g.base t ∈ (⊤ : S.Opens) from trivial)
  let U : T.Opens := g ⁻¹ᵁ V
  have hU : IsAffineOpen U := hV.preimage g
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let y : U.toScheme := ⟨t, htV⟩
  let e : U ≤ g ⁻¹ᵁ V := le_rfl
  let k : U.toScheme ⟶ V.toScheme := g.resLE V U e
  have hLEfin : (g.appLE V U e).hom.Finite := by
    rw [Scheme.Hom.appLE_eq_app]
    exact g.finite_app V hV
  have hKflat : (k.appTop).hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso g V U e)).mpr
      (g.flat_appLE hV hU e)
  have : IsFinite (Spec.map (g.appLE V U e)) := (IsFinite.SpecMap_iff _).mpr hLEfin
  have hIU : IsFinite U.toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  have hIV : IsFinite V.toSpecΓ := by
    rw [← hV.isoSpec_hom]
    infer_instance
  have hcompFin : IsFinite (k ≫ V.toSpecΓ) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE]
    infer_instance
  have : IsFinite k := IsFinite.comp_iff.mp hcompFin
  have : Flat k := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).2 hKflat
  let Gv : V.toScheme.Modules := (Scheme.Modules.pullback V.ι).obj G
  have : Gv.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion V.ι G
  have hfac : U.ι ≫ g = k ≫ V.ι := (Scheme.Hom.resLE_comp_ι g e).symm
  intro ht
  have ht' : Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback k).obj Gv) y :=
    (isWeaklyAssociatedPoint_pullback_comp_iff hfac G y).mp
      ((isWeaklyAssociatedPoint_pullback_comp_iff (h := U.ι ≫ g) rfl G y).mpr
        ((isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion U.ι
          ((Scheme.Modules.pullback g).obj G) y).mpr ht))
  have hpoint := congrArg (fun q : U.toScheme ⟶ S => q.base y) hfac
  change g.base t = V.ι.base (k.base y) at hpoint
  rw [hpoint]
  exact (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion V.ι G (k.base y)).mp
    (finiteFlat_affine_pullback_reverse k Gv y ht')

/-- **Stacks Project, Tag 05FN.** A point is weakly associated to the pullback of a
quasi-coherent module along a finite flat morphism if and only if its image is weakly
associated to the original module. -/
@[stacks 05FN]
lemma isWeaklyAssociatedPoint_pullback_iff_of_finite_flat
    {T S : Scheme.{u}} (g : T ⟶ S) [IsFinite g] [Flat g]
    (G : S.Modules) [G.IsQuasicoherent] (t : T) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback g).obj G) t ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G (g.base t) :=
  ⟨finiteFlat_pullback_reverse g G t, fun hs =>
    isWeaklyAssociatedPoint_pullback_of_isGenericPoint_fiber
      (f := g) (G := G) (x := t) ((Flat.iff_flat_stalkMap g).1 inferInstance t)
      (asFiber_mem_genericPoints_of_finite g t) hs⟩

end AlgebraicGeometry

end
