module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing

/-!
# Smoothness from locally free differentials in characteristic zero

A scheme locally of finite type over a field of characteristic zero is smooth as soon as its
sheaf of relative differentials is locally free.

## Main results

* `AlgebraicGeometry.smooth_of_isLocallyFree_relativeDifferentials_of_charZero`: the structure
  morphism of a scheme locally of finite type over a characteristic-zero field with locally free
  sheaf of relative differentials is smooth.

## Implementation notes

Smoothness is tested pointwise: a morphism locally of finite presentation is smooth exactly when
its smooth locus is everything, and membership in the smooth locus at a point is formal
smoothness of the stalk map. Local finite presentation is automatic here, since the spectrum of a
field is locally Noetherian.

The commutative-algebra input is Stacks Tag 00TX, which for a finite type algebra over a field of
characteristic zero turns freeness of the Kähler differentials of a localization at a prime into
smoothness at that prime. Three identifications feed it:

* the stalk of a locally free sheaf of modules is free over the local ring
  (`Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree`);
* the stalk of the sheaf of relative differentials is the module of Kähler differentials of the
  stalk map (`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, Tag
  01V0 read at a point);
* taking differentials relative to a localization of the base changes nothing
  (`omega_localization_base`, Tag 00RT), which replaces the local ring of the base by the ring of
  global sections of the base; here the base is the spectrum of a field, so that ring is the
  field itself, transported along `AlgebraicGeometry.Scheme.ΓSpecIso`.

## References

* [Stacks Project, Tag 04QN](https://stacks.math.columbia.edu/tag/04QN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.RelativeDifferentialStalkMap

universe u

namespace AlgebraicGeometry

/-- The stalk at a point of the sheaf of relative differentials of a morphism with locally free
relative differentials is a free module over the local ring of the source at that point, in the
spelling `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]` of the Kähler differentials of the stalk map. -/
private theorem free_kaehlerDifferential_stalkMap_of_isLocallyFree
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} f.relativeDifferentials) (x : X) :
    let _ := algebraStalkMap f x
    Module.Free (ToType (X.sheaf.presheaf.stalk x))
      (KaehlerDifferential (ToType (S.presheaf.stalk (f x)))
        (ToType (X.sheaf.presheaf.stalk x))) := by
  classical
  let := algebraStalkMap f x
  have := hΩ
  exact (Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree.{u}
    f.relativeDifferentials x).of_equiv (relativeDifferentialsStalkKaehlerEquiv f x)

/-- The stalk map of a morphism from a scheme locally of finite type over a characteristic-zero
field with locally free relative differentials is formally smooth at every point.

On an affine chart `V` of the source the local ring at the point is the localization of `Γ(X, V)`
at the corresponding prime, `Γ(X, V)` is a finite type algebra over the field, and the Kähler
differentials of that localization over the field are free; Stacks Tag 00TX then gives smoothness
at the prime, which is formal smoothness of the stalk map. -/
private theorem formallySmooth_stalkMap_of_isLocallyFree_relativeDifferentials
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} f.relativeDifferentials) (x : X) :
    (f.stalkMap x).hom.FormallySmooth := by
  classical
  let U : (Spec (.of k)).Opens := ⊤
  have hU : IsAffineOpen U := isAffineOpen_top _
  have hxU : f x ∈ U := trivial
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU : V ≤ f ⁻¹ᵁ U := fun _ _ => trivial
  let R := ToType Γ(Spec (.of k), U)
  let A := ToType Γ(X, V)
  let T := ToType ((Spec (.of k)).presheaf.stalk (f x))
  let Sx := ToType (X.sheaf.presheaf.stalk x)
  let eR := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field R := (eR.toMulEquiv.isField (Field.toIsField k)).toField
  let : CharZero R := charZero_of_injective_ringHom eR.symm.injective
  let p := hU.primeIdealOf ⟨f x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxV⟩
  let : Algebra R T := ((Spec (.of k)).presheaf.germ U (f x) hxU).hom.toAlgebra
  have : IsLocalization.AtPrime T p.asIdeal := hU.isLocalization_stalk ⟨f x, hxU⟩
  let : Algebra T Sx := algebraStalkMap f x
  let : Algebra R Sx := ((algebraMap T Sx).comp (algebraMap R T)).toAlgebra
  have : IsScalarTower R T Sx := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R A := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType R A :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hU hV hVU)
  let : Algebra A Sx := (X.presheaf.germ V x hxV).hom.toAlgebra
  have : IsLocalization.AtPrime Sx q.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  have hcompat : f.appLE U V hVU ≫ X.presheaf.germ V x hxV =
      (Spec (.of k)).presheaf.germ U (f x) hxU ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res (homOfLE hVU) x hxV]
    exact (Scheme.Hom.germ_stalkMap f U x hxU).symm
  have : IsScalarTower R A Sx := IsScalarTower.of_algebraMap_eq fun r =>
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcompat) r).symm
  have hfreeT : Module.Free Sx Ω[Sx⁄T] :=
    free_kaehlerDifferential_stalkMap_of_isLocallyFree f hΩ x
  have hfreeR : Module.Free Sx Ω[Sx⁄R] :=
    hfreeT.of_equiv (LinearEquiv.ofBijective (KaehlerDifferential.map R T Sx Sx)
      (omega_localization_base R Sx p.asIdeal.primeCompl T)).symm
  exact (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mpr
    (((Algebra.isSmoothAt_tfae_free_kaehlerDifferential_isRegularLocalRing
      (k := R) (S := A) q.asIdeal Sx).out 2 1).mp hfreeR)

/-- **Stacks Project, Tag 04QN.** A scheme locally of finite type over a field of
characteristic zero is smooth if its sheaf of relative differentials is locally free. -/
@[stacks 04QN,
  ega "IV 17.15.6" "characteristic zero",
  ega "IV 16.12.2" "base field, finite type",
  ega "IV 17.15.7" "free ⇒ smooth"]
theorem smooth_of_isLocallyFree_relativeDifferentials_of_charZero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hΩ : _root_.SheafOfModules.IsLocallyFree.{u, u, u} f.relativeDifferentials) :
    Smooth f :=
  f.smoothLocus_eq_top_iff.mp (top_le_iff.mp fun x _ =>
    Scheme.Hom.mem_smoothLocus.mpr
      (formallySmooth_stalkMap_of_isLocallyFree_relativeDifferentials f hΩ x))

end AlgebraicGeometry

end
