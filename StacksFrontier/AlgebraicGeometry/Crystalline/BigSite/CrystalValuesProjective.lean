module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.ChangeBaseCrystals
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CrystalValues

/-!
# The values of a crystal in finite locally free modules on an affine object are finite projective

Let `F` be a crystal in finite locally free modules on the big crystalline site `CRIS(X/S)`,
[Stacks, Tag 07IU], and let `(U, T, δ)` be an object whose ambient scheme `T` is affine.  Then
`F(U, T, δ)` is a finite projective `Γ(T, 𝒪_T)`-module.

## The proof

Write `A = Γ(T, 𝒪_T)` and `M = F(U, T, δ)`.  Finite local freeness gives a covering of the object
on whose members `F` is finite free; cocontinuity of the restrictions to the opens of `T` refines
it by restrictions `(U ∩ D(r), D(r), δ)` to basic opens, so there is a set `s ⊆ A` generating the
unit ideal such that `F` is finite free over the restriction of the object to every `D(r)`,
`r ∈ s`. On such a restriction the value of `F` is then a finite free `Γ(D(r), 𝒪) = A_r`-module.
Since `F` is quasi-coherent, the base change of sections along the restriction is an isomorphism
`A_r ⊗_A M ≅ F(U ∩ D(r), D(r), δ)`
(`Crystalline.GlobalCrystallineSituation.extensionSectionsLinearEquivAlong`).  Hence every
localization `M_r = A_r ⊗_A M`, `r ∈ s`, is finite free over `A_r`; finite presentation and
flatness are local for such a covering, and a finitely presented flat module is projective.

## Main results

* `SheafOfModules.IsFiniteFree.exists_linearEquiv` — the sections of a finite free sheaf of modules
  over an object are a finite free module over the sections of the structure sheaf.
* `SheafOfModules.isFiniteFree_over_of_hom` — finite freeness on the localization at an object
  passes to the localization at any object mapping to it.
* `...GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal.projective_val_obj`
  and `...IsFiniteLocallyFreeQuasicoherentCrystal.finite_val_obj` — **the value of a crystal in
  finite locally free modules on an object with affine ambient scheme is a finite projective
  module.**
* `...IsFiniteLocallyFreeQuasicoherentCrystal.projective_bigModuleULift_val_obj` and
  `...extensionSectionsULiftLinearEquivAlong` — the same, and the base change of sections, at the
  module universe `u + 1` of the cohomology.

## References

* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe w m u₁ v₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- **The sections of a finite free sheaf of modules over an object are a finite free module** over
the sections of the structure sheaf: a finite coproduct of copies of the structure sheaf is a
finite biproduct, and evaluating at an object is additive, so it is carried to a finite biproduct
of copies of the ring, which is the module of functions on the index set. -/
theorem IsFiniteFree.exists_linearEquiv {R : Sheaf J RingCat.{w}} {F : SheafOfModules.{m} R}
    (h : IsFiniteFree R F) (U : Cᵒᵖ) :
    ∃ n : ℕ, Nonempty (F.val.obj U ≃ₗ[R.obj.obj U] (Fin n → R.obj.obj U)) := by
  obtain ⟨n, N, ι, ⟨hc⟩, e, -⟩ := h
  let Ev : SheafOfModules.{w} R ⥤ ModuleCat.{w} (R.obj.obj U) :=
    SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U
  have hb := isBilimitOfPreserves Ev (biconeIsBilimitOfColimitCoconeOfIsColimit hc)
  let i := IsLimit.conePointUniqueUpToIso hb.isLimit
    (ModuleCat.HasLimit.productLimitCone fun _ : Fin n ↦ Ev.obj (SheafOfModules.unit R)).isLimit
  exact ⟨n, ⟨(e U).symm.trans i.toLinearEquiv⟩⟩

/-- The sections of a finite free sheaf of modules over an object are a free module. -/
theorem IsFiniteFree.free_val_obj {R : Sheaf J RingCat.{w}} {F : SheafOfModules.{m} R}
    (h : IsFiniteFree R F) (U : Cᵒᵖ) : Module.Free (R.obj.obj U) (F.val.obj U) := by
  obtain ⟨n, ⟨e⟩⟩ := h.exists_linearEquiv U
  exact Module.Free.of_equiv e.symm

/-- The sections of a finite free sheaf of modules over an object are a finite module. -/
theorem IsFiniteFree.finite_val_obj {R : Sheaf J RingCat.{w}} {F : SheafOfModules.{m} R}
    (h : IsFiniteFree R F) (U : Cᵒᵖ) : Module.Finite (R.obj.obj U) (F.val.obj U) := by
  obtain ⟨n, ⟨e⟩⟩ := h.exists_linearEquiv U
  exact Module.Finite.equiv e.symm

/-- Finite freeness is invariant under isomorphism. -/
theorem IsFiniteFree.of_iso {R : Sheaf J RingCat.{w}} {F G : SheafOfModules.{w} R} (α : F ≅ G)
    (h : IsFiniteFree R F) : IsFiniteFree R G := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := (isFiniteFree_iff_exists_isColimit R F).mp h
  exact (isFiniteFree_iff_exists_isColimit R G).mpr
    ⟨n, fun i ↦ ι i ≫ α.hom, ⟨hc.ofIsoColimit (Cocone.ext α fun _ ↦ rfl)⟩⟩

/-- **Finite freeness on the localization at an object passes to the localization at any object
mapping to it**: the localization at `X` is the restriction along `Over.map a` of the localization
at `Y`. -/
theorem isFiniteFree_over_of_hom {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) {X Y : C}
    (a : X ⟶ Y) (h : IsFiniteFree (R.over Y) (M.over Y)) : IsFiniteFree (R.over X) (M.over X) :=
  IsFiniteFree.of_iso ((SheafOfModules.overFunctorMap R a).app M)
    (isFiniteFree_pushforward (G := Over.map a) (Sheaf.pushforwardOverMapIso R a).inv
      (M.over Y) h)

end SheafOfModules

namespace Crystalline.GlobalCrystallineSituation

open TopologicalSpace

variable {S : GlobalCrystallineSituation.{u}} {M : SheafOfModules.{u} (crystallineStructureSheaf S)}

/-- **A crystal in finite locally free modules is finite free over the restrictions of an affine
object to small enough basic opens.**  Finite local freeness gives a covering of the object on
whose members the module is finite free; cocontinuity of the restrictions to the opens of the
ambient scheme refines it by a restriction to an open neighbourhood of a given point, and the basic
opens form a basis of the topology of an affine scheme. -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.exists_basicOpen_isFiniteFree
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] (x : A.thickening.target.scheme) :
    ∃ r : Γ(A.thickening.target.scheme, ⊤), x ∈ A.thickening.target.scheme.basicOpen r ∧
      SheafOfModules.IsFiniteFree
        ((crystallineStructureSheaf S).over
          (A.restrictOpen (A.thickening.target.scheme.basicOpen r)))
        (M.over (A.restrictOpen (A.thickening.target.scheme.basicOpen r))) := by
  obtain ⟨I, Y, f, hcov, hY⟩ := hM.isFiniteLocallyFree A
  have hpb : (Sieve.ofArrows Y f).pullback (A.restrictOpenHom ⊤) ∈
      topology S (A.restrictOpenFunctor.obj ⊤) :=
    (topology S).pullback_stable _ hcov
  obtain ⟨V, g, hg, hxV⟩ :=
    A.restrictOpenFunctor.cover_lift (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      (topology S) hpb x (Opens.mem_top x)
  have hfac : A.restrictOpenFunctor.map g ≫ A.restrictOpenHom ⊤ = A.restrictOpenHom V :=
    Thickening.restrictOpenLE_restrictOpenHom A g.le
  have hV : (Sieve.ofArrows Y f).arrows (A.restrictOpenHom V) := by
    rwa [← hfac]
  obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff Y f _).1 hV
  obtain ⟨r, hrV, hxr⟩ :=
    (isAffineOpen_top A.thickening.target.scheme).exists_basicOpen_le ⟨x, hxV⟩ (Opens.mem_top x)
  exact ⟨r, hxr, SheafOfModules.isFiniteFree_over_of_hom M (A.restrictOpenLE hrV ≫ a) (hY i)⟩

/-- **The value of a crystal in finite locally free modules on an object with affine ambient scheme
is finitely presented and flat.**  See the module documentation. -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.finitePresentation_flat_val_obj
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    Module.FinitePresentation (crysSheafRing S A) (M.val.obj (op A)) ∧
      Module.Flat (crysSheafRing S A) (M.val.obj (op A)) := by
  let X := A.thickening.target.scheme
  let R := crysSheafRing S A
  let s : Set R := {r | SheafOfModules.IsFiniteFree
    ((crystallineStructureSheaf S).over (A.restrictOpen (X.basicOpen r)))
    (M.over (A.restrictOpen (X.basicOpen r)))}
  have hs : Ideal.span s = ⊤ := by
    refine ((isAffineOpen_top X).iSup_basicOpen_eq_self_iff (s := s)).1 ?_
    refine top_le_iff.1 fun x _ ↦ ?_
    obtain ⟨r, hxr, hr⟩ := hM.exists_basicOpen_isFiniteFree A x
    exact Opens.mem_iSup.2 ⟨⟨r, hr⟩, hxr⟩
  let g : ∀ r : s, A.restrictOpen (X.basicOpen r.1) ⟶ A := fun r ↦ A.restrictOpenHom _
  have : ∀ r : s, IsAffine (A.restrictOpen (X.basicOpen r.1)).thickening.target.scheme :=
    fun r ↦ (isAffineOpen_top X).basicOpen r.1
  have hloc : ∀ r : s, IsLocalization.Away r.1 (ringAlong (g r)) :=
    fun r ↦ Γ_restrict_isLocalization X r.1
  have hfree : ∀ r : s, Module.Projective (ringAlong (g r))
        (ringAlong (g r) ⊗[R] M.val.obj (op A)) ∧
      Module.Finite (ringAlong (g r)) (ringAlong (g r) ⊗[R] M.val.obj (op A)) := by
    intro r
    let e := extensionSectionsLinearEquivAlong M (g r) hM.isQuasicoherentOnSite
    have h₁ : Module.Free (ringAlong (g r)) (M.val.obj (op (A.restrictOpen (X.basicOpen r.1)))) :=
      r.2.free_val_obj (op (Over.mk (𝟙 _)))
    have h₂ : Module.Finite (ringAlong (g r))
        (M.val.obj (op (A.restrictOpen (X.basicOpen r.1)))) :=
      r.2.finite_val_obj (op (Over.mk (𝟙 _)))
    have := Module.Free.of_equiv e.symm
    exact ⟨Module.Projective.of_free, Module.Finite.equiv e.symm⟩
  have : ∀ r : s, Module.FinitePresentation (ringAlong (g r))
      (ringAlong (g r) ⊗[R] M.val.obj (op A)) := fun r ↦
    have := (hfree r).1
    have := (hfree r).2
    Module.finitePresentation_of_projective _ _
  refine ⟨Module.FinitePresentation.of_localizationSpan' s hs
    (Rₚ := fun r ↦ ringAlong (g r)) (Mₚ := fun r ↦ ringAlong (g r) ⊗[R] M.val.obj (op A))
    (fun r ↦ TensorProduct.mk R (ringAlong (g r)) (M.val.obj (op A)) 1) inferInstance, ?_⟩
  refine Module.flat_of_isLocalized_span R (M.val.obj (op A)) s hs
    (fun r ↦ ringAlong (g r) ⊗[R] M.val.obj (op A))
    (fun r ↦ TensorProduct.mk R (ringAlong (g r)) (M.val.obj (op A)) 1) fun r ↦ ?_
  have := (hfree r).1
  have : Module.Flat (ringAlong (g r)) (ringAlong (g r) ⊗[R] M.val.obj (op A)) :=
    Module.Flat.of_projective
  have : Module.Flat R (ringAlong (g r)) := IsLocalization.flat _ (Submonoid.powers r.1)
  exact Module.Flat.trans R (ringAlong (g r)) _

/-- **Stacks Project, Tag 07IU, the values of a crystal in finite locally free modules.**  The
value of a crystal in finite locally free modules on `CRIS(X/S)` at an object `(U, T, δ)` whose
ambient scheme `T` is affine is a finite projective `Γ(T, 𝒪_T)`-module. -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.projective_val_obj
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    Module.Projective (crysSheafRing S A) (M.val.obj (op A)) :=
  have h := hM.finitePresentation_flat_val_obj A
  have := h.1
  have := h.2
  Module.Flat.projective_of_finitePresentation

/-- **The value of a crystal in finite locally free modules on an object with affine ambient scheme
is a finite module.** -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.finite_val_obj
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    Module.Finite (crysSheafRing S A) (M.val.obj (op A)) :=
  have := (hM.finitePresentation_flat_val_obj A).1
  inferInstance

/-- **The value of a crystal in finite locally free modules on an object with affine ambient scheme
is a flat module.** -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.flat_val_obj
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    Module.Flat (crysSheafRing S A) (M.val.obj (op A)) :=
  (hM.finitePresentation_flat_val_obj A).2

/-! ### At the module universe of the cohomology

The cohomology of this chapter lives at the module universe `u + 1`, through
`Crystalline.GlobalCrystallineSituation.SmallSite.bigModuleULift`, whose sections are the universe
lifts of the sections of the module. -/

/-- **The value of the universe lift of a crystal in finite locally free modules on an object with
affine ambient scheme is a finite projective module.** -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.projective_bigModuleULift_val_obj
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    Module.Projective (crysSheafRing S A) (((SmallSite.bigModuleULift S).obj M).val.obj (op A)) :=
  have := hM.projective_val_obj A
  Module.Projective.of_equiv (ULift.moduleEquiv (R := crysSheafRing S A)).symm

/-- **The value of the universe lift of a crystal in finite locally free modules on an object with
affine ambient scheme is a finite module.** -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.finite_bigModuleULift_val_obj
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    Module.Finite (crysSheafRing S A) (((SmallSite.bigModuleULift S).obj M).val.obj (op A)) :=
  have := hM.finite_val_obj A
  Module.Finite.equiv (ULift.moduleEquiv (R := crysSheafRing S A)).symm

/-- **The value of the universe lift of a crystal in finite locally free modules on an object with
affine ambient scheme is a flat module.** -/
theorem IsFiniteLocallyFreeQuasicoherentCrystal.flat_bigModuleULift_val_obj
    (hM : IsFiniteLocallyFreeQuasicoherentCrystal M) (A : Thickening S)
    [IsAffine A.thickening.target.scheme] :
    Module.Flat (crysSheafRing S A) (((SmallSite.bigModuleULift S).obj M).val.obj (op A)) :=
  have := hM.flat_val_obj A
  Module.Flat.of_linearEquiv (ULift.moduleEquiv (R := crysSheafRing S A))

/-- **The base change of the sections of the universe lift of a quasi-coherent sheaf of
`𝒪_{X/S}`-modules along a morphism of affine objects**, as a linear equivalence over
`Γ(T', 𝒪_{T'})`: the universe lift of
`Crystalline.GlobalCrystallineSituation.extensionSectionsLinearEquivAlong`. -/
noncomputable def extensionSectionsULiftLinearEquivAlong {A A' : Thickening S} (g : A' ⟶ A)
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    (hM : M.IsQuasicoherentOnSite) :
    ringAlong g ⊗[crysSheafRing S A] ULift.{u + 1} (M.val.obj (op A)) ≃ₗ[ringAlong g]
      ULift.{u + 1} (M.val.obj (op A')) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ringAlong g) (ringAlong g))
      (ULift.moduleEquiv (R := crysSheafRing S A))).trans
    ((extensionSectionsLinearEquivAlong M g hM).trans
      (ULift.moduleEquiv (R := ringAlong g)).symm)

/-- `Crystalline.GlobalCrystallineSituation.extensionSectionsULiftLinearEquivAlong` on a pure
tensor. -/
theorem extensionSectionsULiftLinearEquivAlong_tmul {A A' : Thickening S} (g : A' ⟶ A)
    [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
    (hM : M.IsQuasicoherentOnSite) (t : ringAlong g) (x : ULift.{u + 1} (M.val.obj (op A))) :
    extensionSectionsULiftLinearEquivAlong g hM (t ⊗ₜ[crysSheafRing S A] x) =
      ULift.up (siteRingAlong g t • moduleSiteRestrict M g x.down) :=
  rfl

end Crystalline.GlobalCrystallineSituation
