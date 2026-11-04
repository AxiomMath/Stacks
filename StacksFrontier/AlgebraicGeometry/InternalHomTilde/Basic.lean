module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Global sections of the internal hom of two associated sheaves on an affine scheme

Let `R` be a commutative ring and let `M`, `N` be `R`-modules. The internal hom
`SheafHom_{𝒪_X}(M~, N~)` on `X = Spec R` has global sections the `R`-module `Hom_R(M, N)`.

## Main results

* `AlgebraicGeometry.fullyFaithfulTildeOverTop`: the associated-sheaf functor stays fully
  faithful after restriction to the largest open of `Spec R`, so a morphism
  `M~|_⊤ ⟶ N~|_⊤` is the restriction of a unique `R`-linear map `M ⟶ N`.
* `AlgebraicGeometry.sheafHomTildeΓEquiv`: the resulting additive identification of the
  global sections of the internal hom with `Hom_R(M, N)`.

## Implementation notes

The internal hom is taken in the axiomatic form `SheafHom` of [Stacks, Tag 01CO]: an honest
sheaf of modules `H.obj` together with an additive identification of its sections over `U`
with `Hom_{𝒪_U}(M~|_U, N~|_U)`, natural in restriction and compatible with the
`𝒪_X`-action. Only the identification at `U = ⊤` is used here.

The identification at `⊤` is obtained from full faithfulness of `tilde` (Mathlib's
`AlgebraicGeometry.tilde.fullyFaithfulFunctor`, which is [Stacks, Tag 01I7]) composed with
full faithfulness of restriction to `⊤`. The latter is not formal: `SheafOfModules.overFunctor`
at `⊤` is identified with pullback along the isomorphism `Scheme.topIso`, and pullback along an
isomorphism of schemes is an equivalence.

This is the `Γ`-level half of [Stacks, Tag 01I8] (3). The sheaf-level statement of that clause
additionally needs quasi-coherence of the internal hom, which is not available in this library;
see the note on `AlgebraicGeometry.InternalHomTildeIso'`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Pullback of sheaves of modules along an isomorphism of schemes is an equivalence. -/
theorem isEquivalence_modulesPullback_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pullback e.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫
      Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫
      Scheme.Modules.pullbackId Y).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
      Scheme.Modules.pullbackId X)

/-- Restriction of sheaves of modules to the largest open subscheme is fully faithful. -/
def fullyFaithfulOverFunctorTop {X : Scheme.{u}} :
    (SheafOfModules.overFunctor X.ringCatSheaf (⊤ : X.Opens)).FullyFaithful := by
  have hRestr : (Scheme.Modules.restrictFunctor X.topIso.hom).FullyFaithful := by
    have hPullback : (Scheme.Modules.pullback X.topIso.hom).FullyFaithful := by
      letI : (Scheme.Modules.pullback X.topIso.hom).IsEquivalence :=
        isEquivalence_modulesPullback_of_iso X.topIso
      exact {
        preimage := (Scheme.Modules.pullback X.topIso.hom).preimage
        map_preimage := fun f => (Scheme.Modules.pullback X.topIso.hom).map_preimage f
        preimage_map := fun f => (Scheme.Modules.pullback X.topIso.hom).preimage_map f }
    exact Functor.FullyFaithful.ofIso hPullback
      (Scheme.Modules.restrictFunctorIsoPullback X.topIso.hom).symm
  have hComposite :
      (SheafOfModules.overFunctor X.ringCatSheaf (⊤ : X.Opens) ⋙
        (Scheme.Modules.overEquiv (⊤ : X.Opens)).functor).FullyFaithful :=
    Functor.FullyFaithful.ofIso hRestr
      (Scheme.Modules.overFunctorEquiv (⊤ : X.Opens)).symm
  haveI : (Scheme.Modules.overEquiv (⊤ : X.Opens)).functor.Faithful := inferInstance
  exact Functor.FullyFaithful.ofCompFaithful
    (G := (Scheme.Modules.overEquiv (⊤ : X.Opens)).functor) hComposite

/-- The associated-sheaf functor of `Spec R`, followed by restriction to the largest open,
is fully faithful. -/
def fullyFaithfulTildeOverTop (R : CommRingCat.{u}) :
    (tilde.functor R ⋙
      SheafOfModules.overFunctor (structureSheaf (Spec.structureSheaf R))
        (⊤ : Opens (PrimeSpectrum.Top R))).FullyFaithful := by
  change (tilde.functor R ⋙
    SheafOfModules.overFunctor (Spec R).ringCatSheaf (⊤ : (Spec R).Opens)).FullyFaithful
  exact (tilde.fullyFaithfulFunctor).comp (fullyFaithfulOverFunctorTop (X := Spec R))

/-- The associated-sheaf functor followed by restriction to the largest open is additive on
morphisms. -/
theorem tildeOverTop_map_add (R : CommRingCat.{u})
    {M N : ModuleCat.{u} R} (f g : M ⟶ N) :
    (tilde.functor R ⋙
      SheafOfModules.overFunctor (structureSheaf (Spec.structureSheaf R))
        (⊤ : Opens (PrimeSpectrum.Top R))).map (f + g) =
      (tilde.functor R ⋙
        SheafOfModules.overFunctor (structureSheaf (Spec.structureSheaf R))
          (⊤ : Opens (PrimeSpectrum.Top R))).map f +
      (tilde.functor R ⋙
        SheafOfModules.overFunctor (structureSheaf (Spec.structureSheaf R))
          (⊤ : Opens (PrimeSpectrum.Top R))).map g := by
  show (SheafOfModules.overFunctor (structureSheaf (Spec.structureSheaf R))
    (⊤ : Opens (PrimeSpectrum.Top R))).map (tilde.map (f + g)) = _
  rw [tilde.map_add]
  ext U x
  rfl

/-- **Stacks Project, Tag 01I8 (3), global sections.** The global sections of the internal hom
`SheafHom_{𝒪_{Spec R}}(M~, N~)` are additively identified with the `R`-module homomorphisms
`M ⟶ N`. No finiteness hypothesis on `M` is needed at this level. -/
def sheafHomTildeΓEquiv
    (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (H : SheafHom (Spec.structureSheaf R) (tilde M) (tilde N)) :
    H.obj.val.obj (op (⊤ : Opens (PrimeSpectrum.Top R))) ≃+
      ModuleCat.of R (M ⟶ N) := by
  let T := tilde.functor R ⋙ SheafOfModules.overFunctor
    (structureSheaf (Spec.structureSheaf R)) (⊤ : Opens (PrimeSpectrum.Top R))
  let F := fullyFaithfulTildeOverTop R
  refine
    { toFun := fun s => F.preimage (H.sectionsEquiv ⊤ s)
      invFun := fun f => (H.sectionsEquiv ⊤).symm (T.map f)
      left_inv := fun s => (H.sectionsEquiv ⊤).injective <|
        ((H.sectionsEquiv ⊤).apply_symm_apply (T.map (F.preimage (H.sectionsEquiv ⊤ s)))).trans
          (F.map_preimage (H.sectionsEquiv ⊤ s))
      right_inv := fun f =>
        (congrArg F.preimage ((H.sectionsEquiv ⊤).apply_symm_apply (T.map f))).trans
          (F.preimage_map f)
      map_add' := fun s t => F.map_injective <|
        (F.map_preimage _).trans <|
          ((H.sectionsEquiv ⊤).map_add s t).trans <|
          (congrArg₂ (· + ·) (F.map_preimage _).symm (F.map_preimage _).symm).trans
            (tildeOverTop_map_add R _ _).symm }

/-- The comparison map `M_y ⟶ N_y` on localizations induced by an `R`-linear map `g : M ⟶ N`
is `R`-linear in `g`: scaling `g` by `r` scales the induced map by the image of `r` in the
localization of `R`. -/
lemma localizationsComapFun_smul {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : R) (g : M →ₗ[R] N) (y : PrimeSpectrum.Top R)
    (z : LocalizedModule y.asIdeal.primeCompl M) :
    (LocalizedModule.mk r 1 : LocalizedModule y.asIdeal.primeCompl R) •
        StructureSheaf.Localizations.comapFun (σ := RingHom.id R) g y z =
      StructureSheaf.Localizations.comapFun (σ := RingHom.id R) (r • g) y z := by
  induction z using LocalizedModule.induction_on with
  | h a b =>
    have h1 : StructureSheaf.Localizations.comapFun (σ := RingHom.id R) g y
          (LocalizedModule.mk a b) = LocalizedModule.mk (g a) b :=
      StructureSheaf.Localizations.comapFun_mk g y a b
    have h2 : StructureSheaf.Localizations.comapFun (σ := RingHom.id R) (r • g) y
          (LocalizedModule.mk a b) = LocalizedModule.mk (r • g a) b :=
      StructureSheaf.Localizations.comapFun_mk (r • g) y a b
    refine (congrArg _ h1).trans (Eq.trans ?_ h2.symm)
    rw [← LocalizedModule.smul'_mk]
    simp

/-- **Stacks Project, Tag 01I8 (3), global sections.** The additive identification of the
global sections of the internal hom with `Hom_R(M, N)` is `R`-linear. -/
def sheafHomTildeΓLinearEquiv
    (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (H : SheafHom (Spec.structureSheaf R) (tilde M) (tilde N)) :
    ((moduleSpecΓFunctor (R := R)).obj H.obj) ≃ₗ[R] ModuleCat.of R (M ⟶ N) := by
  let e := sheafHomTildeΓEquiv R M N H
  let T := tilde.functor R ⋙ SheafOfModules.overFunctor
    (structureSheaf (Spec.structureSheaf R)) (⊤ : Opens (PrimeSpectrum.Top R))
  let F := fullyFaithfulTildeOverTop R
  letI : Module R (H.obj.val.obj (op (⊤ : Opens (PrimeSpectrum.Top R)))) :=
    ((moduleSpecΓFunctor (R := R)).obj H.obj).isModule
  refine e.toLinearEquiv fun r s => F.map_injective ?_
  change T.map (F.preimage (H.sectionsEquiv ⊤ (r • s))) =
    T.map (r • F.preimage (H.sectionsEquiv ⊤ s))
  let rO : (structureSheaf (Spec.structureSheaf R)).obj.obj (op ⊤) :=
    (Scheme.ΓSpecIso R).inv.hom r
  refine (F.map_preimage (H.sectionsEquiv ⊤ (r • s))).trans ?_
  change H.sectionsEquiv ⊤ (rO • s) = T.map (r • F.preimage (H.sectionsEquiv ⊤ s))
  apply SheafOfModules.hom_ext
  change (H.sectionsEquiv ⊤ (rO • s)).val =
    (T.map (r • F.preimage (H.sectionsEquiv ⊤ s))).val
  refine PresheafOfModules.hom_ext fun ⟨⟨W, Z, i⟩⟩ => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let : Module ((structureSheaf (Spec.structureSheaf R)).obj.obj (op W))
      ((tilde N).val.obj (op W)) := ((tilde N).val.obj (op W)).isModule
  let : Module ((structureSheaf (Spec.structureSheaf R)).obj.obj (op W))
      ((structureSheafInType R N).obj.obj (op W)) := ((tilde N).val.obj (op W)).isModule
  let : Module ((structureSheaf (Spec.structureSheaf R)).obj.obj
      (op ((CategoryTheory.Functor.id (Opens (PrimeSpectrum.Top R))).obj W)))
      ((structureSheafInType R N).obj.obj (op W)) := by
    change Module ((Spec R).ringCatSheaf.obj.obj (op W))
      ((structureSheafInType R N).obj.obj (op W))
    exact ((tilde N).val.obj (op W)).isModule
  let : Module ((structureSheaf (Spec.structureSheaf R)).obj.obj
      (op ((CategoryTheory.Functor.id (Opens (PrimeSpectrum.Top R))).obj W)))
      ((tilde N).val.obj (op W)) := by
    change Module ((Spec R).ringCatSheaf.obj.obj (op W)) ((tilde N).val.obj (op W))
    exact ((tilde N).val.obj (op W)).isModule
  let psi : R →+* Γ(Spec R, W) :=
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom
  let : Algebra R Γ(Spec R, W) := psi.toAlgebra
  let : Algebra R ((structureSheaf (Spec.structureSheaf R)).obj.obj (op W)) := by
    change Algebra R Γ(Spec R, W)
    infer_instance
  change ((H.sectionsEquiv ⊤ (rO • s)).val.app
      (op (Over.mk (homOfLE (leOfHom i))))) x = _
  have hqV :
      ((T.map (F.preimage (H.sectionsEquiv ⊤ s))).val.app
          (op (Over.mk (homOfLE (leOfHom i))))) x =
      ((H.sectionsEquiv ⊤ s).val.app
          (op (Over.mk (homOfLE (leOfHom i))))) x :=
    congrFun (congrArg (fun q => q.val.app (op (Over.mk (homOfLE (leOfHom i)))))
      (F.map_preimage (H.sectionsEquiv ⊤ s))) x
  rw [H.smul_natural ⊤ rO s (W := W) (leOfHom i) x, ← hqV]
  change ((structureSheaf (Spec.structureSheaf R)).obj.map i.op) rO •
      ((tilde.map (F.preimage (H.sectionsEquiv ⊤ s))).val.app (op W)).hom x =
      ((tilde.map (r • F.preimage (H.sectionsEquiv ⊤ s))).val.app
        (op W)).hom x
  refine Subtype.ext (funext fun y => ?_)
  change ((algebraMap R ((structureSheaf (Spec.structureSheaf R)).obj.obj (op W)) r) •
      StructureSheaf.comapₗ
      (ModuleCat.Hom.hom (F.preimage (H.sectionsEquiv ⊤ s))) W W (fun z hz => hz) x).1 y =
    (StructureSheaf.comapₗ
      (r • ModuleCat.Hom.hom (F.preimage (H.sectionsEquiv ⊤ s)))
      W W (fun z hz => hz) x).1 y
  dsimp [StructureSheaf.comapₗ, StructureSheaf.comapFun]
  change ((algebraMap R ((structureSheaf (Spec.structureSheaf R)).obj.obj (op W)) r).1 y) •
      StructureSheaf.Localizations.comapFun
        (ModuleCat.Hom.hom (F.preimage (H.sectionsEquiv ⊤ s))) y (x.1 y) =
    StructureSheaf.Localizations.comapFun
      (r • ModuleCat.Hom.hom (F.preimage (H.sectionsEquiv ⊤ s))) y (x.1 y)
  have hscalarValue :
      ((algebraMap R ((structureSheaf (Spec.structureSheaf R)).obj.obj (op W)) r).1 y) =
        LocalizedModule.mk r 1 := by
    let : Algebra R ((Spec.structureSheaf R).presheaf.obj (op W)) := inferInstance
    change ((algebraMap R ((Spec.structureSheaf R).presheaf.obj (op W)) r).1 y) = _
    have hmap : algebraMap R ((Spec.structureSheaf R).presheaf.obj (op W)) r =
        (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op).hom r) :=
      congrArg (fun f : R ⟶ (Spec.structureSheaf R).presheaf.obj (op W) => f.hom r)
        (Scheme.toOpen_eq (R := R) W)
    rw [hmap]
    change ((structureSheafInType R R).1.map (homOfLE le_top).op
      (StructureSheaf.const r 1 ⊤ (by simp))).1 y = _
    simp [StructureSheaf.res_const]
    rfl
  rw [hscalarValue]
  exact localizationsComapFun_smul r
    (ModuleCat.Hom.hom (F.preimage (H.sectionsEquiv ⊤ s))) y (x.1 y)

/-- The unit of the `tilde`--global-sections adjunction followed by the global sections of the
transpose of a map recovers that map. -/
theorem tilde_adjunction_unit_map_counit {R : CommRingCat.{u}}
    {M : ModuleCat R} (Q : (Spec R).Modules)
    (g : M ⟶ moduleSpecΓFunctor.obj Q) :
    (tilde.adjunction (R := R)).unit.app M ≫
      moduleSpecΓFunctor.map
        ((tilde.functor R).map g ≫ (tilde.adjunction (R := R)).counit.app Q) = g := by
  simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] using
    ((tilde.adjunction (R := R)).homEquiv M Q).apply_symm_apply g

/-- An isomorphism from the internal hom of two associated sheaves on `Spec R` to the sheaf
associated to the module of `R`-linear maps, together with the characterization that pins the
isomorphism down: its inverse sends the canonical global section attached to `f : M ⟶ N` to the
section of the internal hom represented by the sheaf morphism `tilde.map f`.

The internal hom is taken over `AlgebraicGeometry.Spec.structureSheaf R`, the sheaf of rings on
the prime spectrum of `R`.  `AlgebraicGeometry.InternalHomTildeIso` is the same notion over the
structure sheaf of the scheme `Spec R`, which is the spelling the affine internal-Hom
development uses; the two sheaves of rings agree, but not as terms. -/
structure InternalHomTildeIso' (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    (H : SheafHom (Spec.structureSheaf R) (tilde M) (tilde N)) where
  /-- The isomorphism of sheaves of modules. -/
  iso : H.obj ≅ tilde (ModuleCat.of R (M ⟶ N))
  /-- The inverse is the canonical comparison induced by functoriality of `tilde`. -/
  inv_app_toOpen (f : M ⟶ N) :
    H.sectionsEquiv ⊤
        (iso.inv.val.app (op ⊤)
          (tilde.toOpen (ModuleCat.of R (M ⟶ N)) ⊤ f)) =
      (tilde.map f).over ⊤

/-- **Stacks Project, Tag 01I8 (3), given quasi-coherence of the internal hom.**

For `R`-modules `M`, `N` with `M` finitely presented, the internal hom
`SheafHom_{𝒪_{Spec R}}(M~, N~)` is canonically isomorphic to `Hom_R(M, N)~`.

The isomorphism is produced from the global-sections identification
`AlgebraicGeometry.sheafHomTildeΓLinearEquiv` and the fact that a quasi-coherent sheaf on
`Spec R` is the associated sheaf of its global sections.

Quasi-coherence of `H.obj` is taken as a hypothesis because this library does not have it:
it is the content of [Stacks, Tag 0AXZ], which is not formalized here. Consequently this
declaration does NOT carry the `01I8` tag — the clause asserts the isomorphism outright.
The finite-presentation hypothesis enters only through that missing input, which is why it is
unused in the proof below. -/
def internalHomTildeIsoOfQuasicoherent (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M]
    (H : SheafHom (Spec.structureSheaf R) (tilde M) (tilde N))
    [hHqc : H.obj.IsQuasicoherent] :
    InternalHomTildeIso' R M N H := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ H.obj) :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent R H.obj hHqc
  let e := sheafHomTildeΓLinearEquiv R M N H
  let em : moduleSpecΓFunctor.obj H.obj ≅ ModuleCat.of R (M ⟶ N) := e.toModuleIso
  refine ⟨(asIso (Scheme.Modules.fromTildeΓ H.obj)).symm ≪≫
    (tilde.functor R).mapIso em, ?_⟩
  intro f
  have h_inv : em.inv.hom f =
      (H.sectionsEquiv ⊤).symm ((tilde.map f).over ⊤) := rfl
  rw [← (H.sectionsEquiv ⊤).apply_symm_apply ((tilde.map f).over ⊤)]
  apply congrArg (H.sectionsEquiv ⊤)
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso]
  rw [← h_inv]
  have hcanon := congrArg (fun k : ModuleCat.of R (M ⟶ N) ⟶ moduleSpecΓFunctor.obj H.obj => k f)
    (tilde_adjunction_unit_map_counit (R := R) H.obj em.inv)
  convert hcanon using 1
  all_goals rfl

end AlgebraicGeometry

end
