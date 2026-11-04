module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.LocalRingHom

/-!
# Flatness over the base at a point, read in an affine chart

The two stalkwise flatness conditions of a morphism of schemes — flatness of the morphism at a
point and flatness over the target of a quasi-coherent module at a point — are conditions on
local rings and their modules. On an affine chart each of them becomes a statement about a
localization of a ring of sections, and this file supplies the two translations.

For a morphism `f : X ⟶ S` and compatible affine opens `x ∈ V ⊆ f⁻¹(U)`, flatness of `f` at
`x` is flatness of the localization of `Γ(X, V)` at the prime of `x`, as a module over
`Γ(S, U)`. For a ring map `A → B` and a `B`-module `M`, flatness of `M^~` over `Spec A` at a
prime `q` of `B` is flatness of the localization `M_q` as an `A`-module.

## Main results

* `AlgebraicGeometry.isFlatAt_iff_flat_localizedModule_appLE`: the translation for a morphism.
* `AlgebraicGeometry.isFlatOverAt_spec_tilde_iff_flat_localizedModule`: the translation for a
  quasi-coherent module on an affine scheme.

## Implementation notes

The first translation is Mathlib's `AlgebraicGeometry.IsAffineOpen.arrowStalkMapIso`, which
identifies the stalk map of `f` at `x` with the induced map of localizations of `f.appLE U V`,
followed by `Module.flat_localizationAtPrime_iff_flat_localRingHom`.

The second is the identification of the stalk of `M^~` at `q` with the localized module `M_q`
(`AlgebraicGeometry.tilde.toStalk`, which is a localization map by
`AlgebraicGeometry.tilde.isLocalizedModule_toStalk`), together with the fact that the base
stalk `A_p` is a localization of `A` through which the module structure factors
(`Module.flat_iff_of_isLocalization`). That the two composites `A → A_p → M_q` and
`A → B → M_q` agree is `AlgebraicGeometry.stalkMap_toStalk`.

Since `Localization q.primeCompl` is by definition `LocalizedModule q.primeCompl B`, the first
statement's conclusion is also a statement about the local ring of `X` at `x`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

/-- **Flatness of a morphism at a point, in an affine chart.** For compatible affine opens
`x ∈ V ⊆ f⁻¹(U)`, the morphism `f` is flat at `x` exactly when the localization of `Γ(X, V)` at
the prime of `x` is flat as a module over `Γ(S, U)`, the scalars acting through `f.appLE U V`. -/
theorem isFlatAt_iff_flat_localizedModule_appLE {X S : Scheme.{u}} (f : X ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {x : X}
    (hx : x ∈ V) :
    IsFlatAt f.toLRSHom.toShHom x ↔
      letI : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
      Module.Flat Γ(S, U)
        (LocalizedModule.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal Γ(X, V)) := by
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  show (f.stalkMap x).hom.Flat ↔ _
  rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)]
  exact (Module.flat_localizationAtPrime_iff_flat_localRingHom p q).symm

/-- **Flatness of `M^~` over an affine base at a prime.** For a ring map `φ : A ⟶ B` presenting
`B` as an `A`-algebra and a `B`-module `M`, the module `M^~` on `Spec B` is flat over `Spec A` at
a prime `q` exactly when the localization `M_q` is flat as an `A`-module. -/
theorem isFlatOverAt_spec_tilde_iff_flat_localizedModule {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M : ModuleCat.{u} B) [Algebra (A : Type u) (B : Type u)] [Module (A : Type u) (M : Type u)]
    [IsScalarTower (A : Type u) (B : Type u) (M : Type u)]
    (hφ : φ.hom = algebraMap (A : Type u) (B : Type u)) (q : PrimeSpectrum (B : Type u)) :
    IsFlatOverAt (Spec.map φ).toLRSHom.toShHom (tilde M) q ↔
      Module.Flat (A : Type u) (LocalizedModule.AtPrime q.asIdeal (M : Type u)) := by
  let : q.asIdeal.IsPrime := q.isPrime
  let p : Ideal (A : Type u) := q.asIdeal.comap φ.hom
  have hp : p.IsPrime := Ideal.comap_isPrime φ.hom q.asIdeal
  let : Algebra (B : Type u) ((Spec B).presheaf.stalk q) := StructureSheaf.stalkAlgebra B q
  let : Algebra (A : Type u) ((Spec A).presheaf.stalk ⟨p, hp⟩) :=
    StructureSheaf.stalkAlgebra A ⟨p, hp⟩
  let : IsLocalization.AtPrime ((Spec A).presheaf.stalk ⟨p, hp⟩) p :=
    StructureSheaf.IsLocalization.to_stalk A ⟨p, hp⟩
  let : Module ((Spec B).presheaf.stalk q) ((tilde M).presheaf.stalk q) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec B).presheaf) (tilde M).val q
  let : Module (B : Type u) ((tilde M).presheaf.stalk q) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M q
  have hB (b : B) (m : (tilde M).presheaf.stalk q) :
      (algebraMap (B : Type u) ((Spec B).presheaf.stalk q) b) • m = b • m := rfl
  let : Module (A : Type u) ((tilde M).presheaf.stalk q) :=
    Module.compHom _ (algebraMap (A : Type u) (B : Type u))
  let : IsScalarTower (A : Type u) (B : Type u) ((tilde M).presheaf.stalk q) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module ((Spec A).presheaf.stalk ⟨p, hp⟩) ((tilde M).presheaf.stalk q) :=
    Module.compHom _ ((Spec.map φ).stalkMap q).hom
  have hbase (r : (A : Type u)) : ((Spec.map φ).stalkMap q).hom
      (algebraMap (A : Type u) ((Spec A).presheaf.stalk ⟨p, hp⟩) r) =
      (algebraMap (B : Type u) ((Spec B).presheaf.stalk q)) (φ.hom r) :=
    congrArg (fun k : CommRingCat.Hom _ _ => k.hom r) (stalkMap_toStalk φ q)
  let : IsScalarTower (A : Type u) ((Spec A).presheaf.stalk ⟨p, hp⟩)
      ((tilde M).presheaf.stalk q) :=
    IsScalarTower.of_algebraMap_smul fun r n => by
      show ((Spec.map φ).stalkMap q).hom
        (algebraMap (A : Type u) ((Spec A).presheaf.stalk ⟨p, hp⟩) r) • n = r • n
      rw [hbase r, hB, hφ]
      exact IsScalarTower.algebraMap_smul (B : Type u) r n
  let e : LocalizedModule.AtPrime q.asIdeal (M : Type u) ≃ₗ[(B : Type u)]
      ((tilde M).presheaf.stalk q) :=
    IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ (M : Type u)) (tilde.toStalk M q).hom
  show Module.Flat ((Spec A).presheaf.stalk ⟨p, hp⟩) ((tilde M).presheaf.stalk q) ↔ _
  rw [Module.flat_iff_of_isLocalization ((Spec A).presheaf.stalk ⟨p, hp⟩) p.primeCompl]
  exact (Module.Flat.equiv_iff (e.restrictScalars (A : Type u))).symm

end

end AlgebraicGeometry
