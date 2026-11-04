module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Kaehler
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective

/-!
# The global sections of the relative differentials of `Spec` of a ring map

For a morphism `ψ : R ⟶ C` of commutative rings, [Stacks, Tag 01UT] identifies the global
sections of `Ω_{Spec C/Spec R}` with the Kähler differentials of the induced map on global
sections, `Γ(Spec R, ⊤) ⟶ Γ(Spec C, ⊤)`. That is the form in which the tag is available in
this library, as `Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections`.
This file transports it onto the rings `R` and `C` themselves:

`Ω[C⁄R] ≃ₗ[C] Γ(Spec C, Ω_{Spec C/Spec R})`,

carrying the universal differential `d c` to the universal relative differential of the global
function `c` corresponds to.

The ring-level form matters because `AlgebraicGeometry.moduleSpecΓFunctor` lands in
`ModuleCat C` and not in `ModuleCat Γ(Spec C, ⊤)`: an exterior power formed over the section ring
is not even the same type as one formed over `C`.

## Main results

* `CommRingCat.KaehlerDifferential.bijective_map`: **the Kähler differentials of a square of
  commutative rings whose two horizontal arrows are invertible are in bijection.**
* `Stacks.AlgebraicGeometry.AffineDifferentials.exists_specKaehlerEquiv`: **[Stacks, Tag 01UT]
  over the ring itself.** For `ψ : R ⟶ C` there is a `C`-linear equivalence from `Ω[C⁄R]` to
  the global sections of `Ω_{Spec C/Spec R}` carrying `d c` to the universal relative
  differential of the global function attached to `c`, for any `Algebra R C` instance whose
  structure map is `ψ`.

## Implementation notes

The transport is `CommRingCat.KaehlerDifferential.map` of Mathlib, applied to the naturality
square of `AlgebraicGeometry.Scheme.ΓSpecIso`; what is added here is that it is bijective when
the square's horizontal arrows are invertible. Its two-sided inverse is the transport of the
inverse square, and the two composites are the identity by
`CommRingCat.KaehlerDifferential.ext`, which needs the composite to be a morphism of
`ModuleCat`: the composite of two transports lands in a module whose scalars have been
restricted twice, so the identity is compared with it through `restrictScalarsRoundTrip`, the
identity map read as a semilinear map into that twice-restricted module. Doing the same
computation by `Submodule.span_induction` on `Ω[C⁄R]` instead fails: the spanning statement
`KaehlerDifferential.span_range_derivation` is about `Ω[↥B⁄↥A]` formed with the `Algebra`
instance that `letI` introduces, whose scalar action is not the one the bundled module
`CommRingCat.KaehlerDifferential` carries, so the induction's scalar step is not type-correct.

No scalar-restriction bookkeeping is needed for the target: the global sections functor
`AlgebraicGeometry.moduleSpecΓFunctor` *is* `ModuleCat.restrictScalars` of the sections over
`⊤` along `AlgebraicGeometry.Scheme.ΓSpecIso`, so the composite of the two comparisons has the
right type on the nose.

The section-ring form of Tag 01UT is
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso`.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace CommRingCat.KaehlerDifferential

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'} {g : A ⟶ A'} {g' : B ⟶ B'}

/-- The inverse of a commutative square of commutative rings whose two horizontal arrows are
invertible. -/
theorem invFac [IsIso g] [IsIso g'] (fac : g ≫ f' = f ≫ g') : inv g ≫ f = f' ≫ inv g' := by
  rw [IsIso.eq_comp_inv, Category.assoc, ← fac, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

/-- The identity map of a module, read as a semilinear map into the module obtained from it by
restricting its scalars twice along two ring maps whose composite is the identity. -/
def restrictScalarsRoundTrip {B B' : CommRingCat.{u}} (M : ModuleCat.{u} B) (u : B ⟶ B')
    (v : B' ⟶ B) (huv : u ≫ v = 𝟙 B) :
    M ⟶ (ModuleCat.restrictScalars u.hom).obj ((ModuleCat.restrictScalars v.hom).obj M) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars u.hom).obj
      ((ModuleCat.restrictScalars v.hom).obj M))
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun b x =>
        congrArg (fun z => z • x) (congrArg (fun h => (CommRingCat.Hom.hom h) b) huv).symm }

/-- Transporting Kähler differentials along two squares in opposite directions is the identity
when the composite of the two horizontal arrows on the target is the identity. -/
private theorem map_map_eq_self {h : A' ⟶ A} {h' : B' ⟶ B} (fac : g ≫ f' = f ≫ g')
    (fac' : h ≫ f = f' ≫ h') (hh : g' ≫ h' = 𝟙 B) (x : CommRingCat.KaehlerDifferential f) :
    (CommRingCat.KaehlerDifferential.map fac').hom
        ((CommRingCat.KaehlerDifferential.map fac).hom x) = x := by
  have key : CommRingCat.KaehlerDifferential.map fac ≫
      (ModuleCat.restrictScalars g'.hom).map (CommRingCat.KaehlerDifferential.map fac') =
      restrictScalarsRoundTrip (CommRingCat.KaehlerDifferential f) g' h' hh := by
    refine CommRingCat.KaehlerDifferential.ext fun b => ?_
    have h1 := CommRingCat.KaehlerDifferential.map_d fac b
    have h2 := CommRingCat.KaehlerDifferential.map_d fac' (g'.hom b)
    exact ((congrArg (fun z => (CommRingCat.KaehlerDifferential.map fac').hom z) h1).trans
      h2).trans (congrArg (fun z => CommRingCat.KaehlerDifferential.d (f := f) z)
        (congrArg (fun h => (CommRingCat.Hom.hom h) b) hh))
  exact congrArg (fun h => (ModuleCat.Hom.hom h) x) key

/-- The transport of Kähler differentials along the inverse square is a left inverse of the
transport along the square. -/
theorem map_invFac_map [IsIso g] [IsIso g'] (fac : g ≫ f' = f ≫ g')
    (x : CommRingCat.KaehlerDifferential f) :
    (CommRingCat.KaehlerDifferential.map (invFac fac)).hom
        ((CommRingCat.KaehlerDifferential.map fac).hom x) = x :=
  map_map_eq_self fac (invFac fac) (IsIso.hom_inv_id g') x

/-- The transport of Kähler differentials along the inverse square is a right inverse of the
transport along the square. -/
theorem map_map_invFac [IsIso g] [IsIso g'] (fac : g ≫ f' = f ≫ g')
    (y : CommRingCat.KaehlerDifferential f') :
    (CommRingCat.KaehlerDifferential.map fac).hom
        ((CommRingCat.KaehlerDifferential.map (invFac fac)).hom y) = y :=
  map_map_eq_self (invFac fac) fac (IsIso.inv_hom_id g') y

/-- **The Kähler differentials of two morphisms of commutative rings related by a commutative
square whose horizontal arrows are invertible are in bijection.** The bijection is the
transport `CommRingCat.KaehlerDifferential.map` along the square, and its inverse is the
transport along the inverse square. -/
theorem bijective_map [IsIso g] [IsIso g'] (fac : g ≫ f' = f ≫ g') :
    Function.Bijective (CommRingCat.KaehlerDifferential.map fac).hom :=
  ⟨fun x y hxy => by
      rw [← map_invFac_map fac x, ← map_invFac_map fac y, hxy],
    fun y => ⟨_, map_map_invFac fac y⟩⟩

end CommRingCat.KaehlerDifferential

namespace Stacks.AlgebraicGeometry.AffineDifferentials

variable {R C : CommRingCat.{u}} (ψ : R ⟶ C)

/-- The naturality square of `AlgebraicGeometry.Scheme.ΓSpecIso` for a morphism of commutative
rings, written with the map on global sections in the `appLE` spelling that
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections` uses. -/
theorem specAppLEFac :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map ψ).appLE ⊤ ⊤ le_top = ψ ≫ (Scheme.ΓSpecIso C).inv := by
  have htop : (Spec.map ψ).appLE ⊤ ⊤ le_top = (Spec.map ψ).appTop :=
    (Scheme.Hom.app_eq_appLE (Spec.map ψ)).symm
  rw [htop]
  exact (Scheme.ΓSpecIso_inv_naturality ψ).symm

/-- The comparison of the Kähler differentials of `ψ : R ⟶ C` with the global sections of the
sheaf of relative differentials of `Spec ψ`: the transport of
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections` along the naturality square of
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
def specKaehlerHom :
    CommRingCat.KaehlerDifferential ψ ⟶
      moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (Spec.map ψ)) :=
  CommRingCat.KaehlerDifferential.map (specAppLEFac ψ) ≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso C).inv.hom).map
      (kaehlerToSections (Spec.map ψ) ⊤ ⊤ le_top)

/-- The comparison carries the universal differential of `c` to the universal relative
differential of the global function attached to `c`. -/
theorem specKaehlerHom_d (c : ↥C) :
    (specKaehlerHom ψ).hom (CommRingCat.KaehlerDifferential.d c) =
      (Scheme.Hom.universalRelativeDerivation (Spec.map ψ)).d ((Scheme.ΓSpecIso C).inv.hom c) :=
  (congrArg (fun z => (kaehlerToSections (Spec.map ψ) ⊤ ⊤ le_top).hom z)
      (CommRingCat.KaehlerDifferential.map_d (specAppLEFac ψ) c)).trans
    (kaehlerToSections_d (Spec.map ψ) ⊤ ⊤ le_top ((Scheme.ΓSpecIso C).inv.hom c))

/-- **The comparison is bijective.** The transport along the naturality square is bijective
because that square's horizontal arrows are invertible, and
`Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections` is invertible for the affine
pair `(⊤, ⊤)` by [Stacks, Tag 01UT]. -/
theorem bijective_specKaehlerHom : Function.Bijective (specKaehlerHom ψ).hom := by
  have hk : IsIso (kaehlerToSections (Spec.map ψ) ⊤ ⊤ le_top) :=
    AffineDifferentialsIso.isIso_kaehlerToSections (Spec.map ψ) (isAffineOpen_top (Spec C))
      le_top (isAffineOpen_top (Spec R))
  have hη : Function.Bijective
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso C).inv.hom).map
        (kaehlerToSections (Spec.map ψ) ⊤ ⊤ le_top)).hom :=
    have : IsIso ((ModuleCat.restrictScalars (Scheme.ΓSpecIso C).inv.hom).map
        (kaehlerToSections (Spec.map ψ) ⊤ ⊤ le_top)) :=
      Functor.map_isIso _ _
    ConcreteCategory.bijective_of_isIso _
  exact hη.comp (CommRingCat.KaehlerDifferential.bijective_map (specAppLEFac ψ))

/-- **[Stacks, Tag 01UT] over the ring itself.** For a morphism `ψ : R ⟶ C` of commutative
rings there is a `C`-linear equivalence from the Kähler differentials `Ω[C⁄R]` to the global
sections of the sheaf of relative differentials of `Spec ψ`, carrying the universal
differential of `c` to the universal relative differential of the global function attached to
`c` by `AlgebraicGeometry.Scheme.ΓSpecIso`.

The `Algebra R C` structure is an arbitrary instance whose structure map is `ψ`, rather than the
one `ψ` induces: two such instances (for a polynomial ring, `MvPolynomial.algebra` and
`RingHom.toAlgebra` of `MvPolynomial.C`) are equal (`Algebra.algebra_ext`) but need not be the
same term, so `Ω[C⁄R]` formed with one of them is not the type formed with the other. -/
theorem exists_specKaehlerEquiv [inst : Algebra ↥R ↥C]
    (hψ : ψ = CommRingCat.ofHom (algebraMap ↥R ↥C)) :
    ∃ e : Ω[↥C⁄↥R] ≃ₗ[↥C]
        ↥(moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (Spec.map ψ))),
      ∀ c : ↥C, e (KaehlerDifferential.D ↥R ↥C c) =
        (Scheme.Hom.universalRelativeDerivation (Spec.map ψ)).d
          ((Scheme.ΓSpecIso C).inv.hom c) := by
  have halg : inst = ψ.hom.toAlgebra :=
    Algebra.algebra_ext _ _ fun r => by rw [hψ]; rfl
  subst halg
  exact ⟨LinearEquiv.ofBijective (specKaehlerHom ψ).hom (bijective_specKaehlerHom ψ),
    specKaehlerHom_d ψ⟩

end Stacks.AlgebraicGeometry.AffineDifferentials

end
