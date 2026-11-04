module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPostcomposition
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.InternalHomTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# Internal Hom on an affine scheme

For a finitely presented module `M` over a commutative ring `R` and an arbitrary `R`-module `N`,
the internal Hom between their associated sheaves on `Spec R` is the sheaf associated to the
module of `R`-linear maps from `M` to `N`.

## Main definitions

* `AlgebraicGeometry.InternalHomTildeIso` packages the affine internal-Hom isomorphism together
  with its canonical comparison-map characterization.

## Main results

* `AlgebraicGeometry.internalHomTildeIso`: **[Stacks, Tag 01I8]**, the canonical isomorphism
  between the internal Hom of two associated sheaves and the associated sheaf of module
  homomorphisms.
* `AlgebraicGeometry.internalHomTildeIsoIso` is that isomorphism itself, projected out of the
  package so that the tag's assertion is readable as a type, and
  `AlgebraicGeometry.internalHomTildeIsoIso_inv_app_toOpen` is the equation making it canonical.
  Naturality in both arguments is proved in
  `StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHomNatural`.

## Implementation notes

The internal Hom is represented by a `SheafHom` package, which carries an honest sheaf of
modules together with the identification of its sections over `U` with the morphisms
`M̃|_U ⟶ Ñ|_U`. The inverse of the displayed isomorphism is characterized on global sections: a
linear map `f : M ⟶ N` is sent to the sheaf map `tilde.map f`. Since the global-section map of
`tilde` is an isomorphism and `tilde` is left adjoint to global sections, this specifies the
canonical comparison morphism.

Quasi-coherence of the internal Hom is the quasi-coherence clause of [Stacks, Tag 0AXZ],
`AlgebraicGeometry.sheafHom_isQuasicoherent`, which is stated for
`Stacks.SheafOfModules.InternalHom.sheafInternalHom` rather than for a `SheafHom` package. The
two are reconciled here by `SheafHom.objIso`, the canonical isomorphism between the underlying
modules of two internal-Hom packages for the same pair of modules. That lets the clause be read
off at an arbitrary package, which is the shape in which the statement is used.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0AXZ](https://stacks.math.columbia.edu/tag/0AXZ)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

/-- The associated-sheaf functor followed by restriction to the largest open of `Spec R`. -/
private noncomputable abbrev tildeOverTop (R : CommRingCat.{u}) :=
  tilde.functor R ⋙ SheafOfModules.overFunctor (Spec R).ringCatSheaf (⊤ : (Spec R).Opens)

/-- The localized comparison map of `StructureSheaf.Localizations.comapFun` is linear in the
linear map it localizes. -/
private lemma comapFun_smul {A : Type u} [CommRing A] {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (φ : M →ₗ[A] N) (r : A) (y : PrimeSpectrum.Top A)
    (z : LocalizedModule (PrimeSpectrum.comap (RingHom.id A) y).asIdeal.primeCompl M) :
    r • StructureSheaf.Localizations.comapFun (σ := RingHom.id A) φ y z =
      StructureSheaf.Localizations.comapFun (σ := RingHom.id A) (r • φ) y z := by
  induction z using LocalizedModule.induction_on with
  | h a b =>
      rw [StructureSheaf.Localizations.comapFun_mk, StructureSheaf.Localizations.comapFun_mk]
      simp [LocalizedModule.smul'_mk]

/-- The internal Hom of two associated sheaves on `Spec R` is quasi-coherent as soon as the
source module is of finite presentation: it is compared by `SheafHom.objIso` with the canonical
internal-Hom package, for which this is the quasi-coherence clause of [Stacks, Tag 0AXZ]. -/
@[ega "I 9.1.1" "special case"]
private theorem sheafHomObj_isQuasicoherent (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    [(tilde M).IsFinitePresentation]
    (H : SheafHom (Spec R).sheaf (tilde M) (tilde N)) :
    H.obj.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (SheafHom.objIso (Stacks.SheafOfModules.SheafHomStalk.internalSheafHom
      (Spec R).toTopCat (Spec R).sheaf (tilde M) (tilde N)) H)
    (sheafHom_isQuasicoherent (tilde M) (tilde N))

/-- An isomorphism from an affine internal Hom to the associated sheaf of the module of linear
maps, together with the characterization that makes the isomorphism canonical.

The inverse sends the global section associated to `f : M ⟶ N` to the section of the internal
Hom represented by the sheaf morphism `tilde.map f`. This is the content of
[Stacks, Tag 01I8]. -/
@[stacks 01I8 "internal_hom"]
structure InternalHomTildeIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (H : SheafHom (Spec R).sheaf (tilde M) (tilde N)) where
  /-- The isomorphism of sheaves of modules. -/
  iso : H.obj ≅ tilde (ModuleCat.of R (M ⟶ N))
  /-- The inverse is the canonical comparison induced by functoriality of `tilde`. -/
  inv_app_toOpen (f : M ⟶ N) :
    H.sectionsEquiv ⊤
        (iso.inv.val.app (op ⊤)
          (tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤ f)) =
      (tilde.map f).over ⊤

/-- **Stacks Project, Tag 01I8 (`internal_hom`).**

Let `M` and `N` be modules over a commutative ring `R`, with `M` finitely presented. The
internal Hom between the associated sheaves of `M` and `N` on `Spec R` is canonically
isomorphic to the sheaf associated to the `R`-module `Hom_R(M, N)`. -/
@[stacks 01I8 "internal_hom", no_expose, ega "I 1.3.12" "(ii)"]
noncomputable def internalHomTildeIso (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M]
    (H : SheafHom (Spec R).sheaf (tilde M) (tilde N)) :
    InternalHomTildeIso R M N H := by
  haveI : (tilde M).IsFinitePresentation :=
    (tilde_isFinitePresentation_iff M).2 ‹Module.FinitePresentation R M›
  haveI : (tilde N).IsQuasicoherent := inferInstance
  haveI : H.obj.IsQuasicoherent := sheafHomObj_isQuasicoherent R M N H
  let e := AlgebraicGeometry.sheafHomTildeΓLinearEquiv R M N H
  let eₘ : moduleSpecΓFunctor.obj H.obj ≅ ModuleCat.of R (M ⟶ N) := e.toModuleIso
  haveI : IsIso (Scheme.Modules.fromTildeΓ H.obj) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent H.obj
  refine ⟨(asIso (Scheme.Modules.fromTildeΓ H.obj)).symm ≪≫
    (tilde.functor R).mapIso eₘ, ?_⟩
  intro f
  have h_inv : eₘ.inv.hom f =
      (H.sectionsEquiv ⊤).symm ((tilde.map f).over ⊤) := rfl
  rw [← (H.sectionsEquiv ⊤).apply_symm_apply ((tilde.map f).over ⊤)]
  apply congrArg (H.sectionsEquiv ⊤)
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso]
  rw [← h_inv]
  have hcanon := congrArg (fun k : ModuleCat.of R (M ⟶ N) ⟶ moduleSpecΓFunctor.obj H.obj => k f)
    (AlgebraicGeometry.tilde_adjunction_unit_map_counit (R := R) H.obj eₘ.inv)
  convert hcanon using 1
  all_goals rfl

/-- **Stacks Project, Tag 01I8 (`internal_hom`).**

The affine internal-Hom isomorphism itself: for `M` finitely presented, the internal Hom of the
associated sheaves of `M` and `N` on `Spec R` is isomorphic to the associated sheaf of the
`R`-module `Hom_R(M, N)`. This is the `iso` field of `internalHomTildeIso`, named so that the
isomorphism asserted by the tag is readable as a type. It is canonical by
`internalHomTildeIsoIso_inv_app_toOpen`. -/
@[stacks 01I8 "internal_hom"]
noncomputable def internalHomTildeIsoIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M]
    (H : SheafHom (Spec R).sheaf (tilde M) (tilde N)) :
    H.obj ≅ tilde (ModuleCat.of R (M ⟶ N)) :=
  (internalHomTildeIso R M N H).iso

/-- **Stacks Project, Tag 01I8 (`internal_hom`).** The affine internal-Hom isomorphism is
canonical: its inverse sends the global section associated to `f : M ⟶ N` to the section of the
internal Hom represented by the sheaf morphism `tilde.map f`. -/
@[stacks 01I8 "internal_hom"]
theorem internalHomTildeIsoIso_inv_app_toOpen (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M]
    (H : SheafHom (Spec R).sheaf (tilde M) (tilde N)) (f : M ⟶ N) :
    H.sectionsEquiv ⊤
        ((internalHomTildeIsoIso R M N H).inv.val.app (op ⊤)
          (tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤ f)) =
      (tilde.map f).over ⊤ :=
  (internalHomTildeIso R M N H).inv_app_toOpen f

end AlgebraicGeometry

end
