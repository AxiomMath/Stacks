module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.AffineLocallySmall
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FppfDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import StacksFrontier.Homology.PseudoCoherent.Local
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import Mathlib.LinearAlgebra.DFinsupp
import StacksCore.Tactic.StacksAttribute

/-!
# `m`-pseudo-coherence descends along an fpqc covering

Let `{f_i : X_i ⟶ X}` be an fpqc covering of schemes, let `E` be an object of `D_QCoh(𝒪_X)` and
let `m` be an integer. Stacks 09UE says that `E` is `m`-pseudo-coherent if and only if every
derived pullback `Lf_i^*E` is.

The forward implication is Stacks 09U7 and needs no hypothesis on the morphisms. The converse is
the source's argument. `m`-pseudo-coherence is local on `X`, so it suffices to treat the
restriction `E|_U` to an affine open `U`. Because the covering is fpqc, Stacks 03L7 produces
finitely many *affine* opens `V_j ⊆ X_{a(j)}` with `f_{a(j)}(V_j) ⊆ U` whose images cover `U`;
so the covering may be replaced by the finite family of flat morphisms of affine schemes
`g_j : V_j ⟶ U`, which is jointly surjective and therefore makes `Γ(U) ⟶ ∏_j Γ(V_j)` faithfully
flat. On `U ≅ Spec A` the object `E|_U` is the derived sheafification `M̃^•` of a complex `M^•`
of `A`-modules (Stacks 06Z0), each `Lg_j^*(E|_U)` is the sheafification of `B_j ⊗_A M^•`, and
Stacks 08E7 converts both sheaf-level conditions into `m`-pseudo-coherence of complexes of
modules. What remains is the algebra: `m`-pseudo-coherence descends along a faithfully flat ring
map (Stacks 068R), and the passage from the family `{A ⟶ B_j}` to the single map `A ⟶ ∏_j B_j`
is Stacks 066D applied to the idempotents `e_j = (0, …, 1, …, 0)` of the product, whose
localizations recover the factors.

Nothing here repeats the argument of Stacks 09UF. That one descends along an *fppf* covering and
its converse rests on the descent of finite type along an open flat surjection (Stacks 09UB),
which needs the covering morphisms to be open, hence locally of finite presentation. An fpqc
covering gives no finite presentation, and the affine reduction together with Stacks 068R is
exactly the substitute: faithfully flat descent of pseudo-coherence over a ring asks for no
openness. Only the forward direction is shared.

## Main results

* `Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_iff_forall_fpqc`:
  **Stacks 09UE.**
* `Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_of_faithfullyFlat_pi_spec`:
  the affine case, for a finite family of flat ring maps whose product is faithfully flat.
* `Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_of_faithfullyFlat_pi`: its
  algebraic content, at the level of complexes of modules.
* `Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_derivedPullback_of_isFlat`:
  Stacks 09U7 for a flat morphism, at a free choice of derived category.
* `Stacks.Cohomology.PseudoCoherence.FpqcDescent.exists_affineOpen_affine_images_cover`: the
  reduction of the covering over an affine open, from Stacks 03L7.

## Implementation notes

**The two models of the derived category.** `CategoryTheory.HasDerivedCategory` carries the
localized category as data, so the standard model and the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` give different types. Stacks 06Z0 and
Stacks 08DW are available only at the locally small model, while Stacks 09U7, Stacks 068R and
the module-level predicate `StacksDraft.PseudoCoherence.IsPseudoCoherentFrom` are stated at the
standard one. The split is crossed with *complexes*, never with objects: the statements of
`isPseudoCoherentComplexFrom_of_isoComplex`,
`isPseudoCoherentComplexFrom_modulePullback_of_isFlat` and
`isPseudoCoherentComplexFrom_tilde_of_faithfullyFlat_pi` mention no derived category of
`𝒪`-modules at all, so each can be proved at the standard model, inside a section which pins it
at priority `2000` — the default priority loses to the global locally small instance — and then
consumed at the locally small one. The bridge from the sheaf-level object to the sheaf-level
complex is `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_obj_iff`, whose
`HasDerivedCategory` binder is free.

**Why the pullbacks are taken along flat morphisms.** Every morphism occurring in the converse
is flat: the members of an fpqc covering are flat by Stacks 03L7, and the remaining ones are
open immersions or isomorphisms. For a flat morphism degreewise pullback is exact, so
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso` computes `Lf^*` on the class of a
complex as the class of the degreewise pullback (`derivedPullbackObjQIso`), which is what lets the
whole argument run on complexes. Flatness is also what makes the forward direction above reduce to
the complex level rather than needing a K-flat resolution.

**The affine comparison.** The identification `(Spec φ)^*(M̃^•) ≅ (S ⊗_R M^•)̃ ` used here is the
*degreewise* one, `AlgebraicGeometry.tildePullbackComplexIso` (Stacks 01I9 on complexes), not the
derived comparison square of Stacks 08DW part (2); for a flat `φ` the two agree and the
degreewise form mentions no derived category.

## References

* [Stacks Project, Lemma 36.12.4 (09UE)](https://stacks.math.columbia.edu/tag/09UE)
* [Stacks Project, Lemma 36.12.3 (09UF)](https://stacks.math.columbia.edu/tag/09UF)
* [Stacks Project, Lemma 20.47.3 (09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 15.66.14 (068R)](https://stacks.math.columbia.edu/tag/068R)
* [Stacks Project, Lemma 15.64.11 (066D)](https://stacks.math.columbia.edu/tag/066D)
* [Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.61.4 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Lemma 34.9.1 (03L7)](https://stacks.math.columbia.edu/tag/03L7)
* [Stacks Project, Lemma 20.46.9 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 29.5.2 (01I9)](https://stacks.math.columbia.edu/tag/01I9)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HigherDirectImage

universe u v

namespace Stacks.Cohomology.PseudoCoherence.FpqcDescent

/-! ### Complex-level statements, proved at the standard model -/

section Standard

attribute [local instance 2000] _root_.HasDerivedCategory.standard

/-- transport of complex-level pseudo-coherence along an isomorphism of complexes -/
public theorem isPseudoCoherentComplexFrom_of_isoComplex {X : RingedSpace.{u, u}}
    {K K' : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} (m : ℤ)
    (h : IsPseudoCoherentComplexFrom K m) (e : K ≅ K') :
    IsPseudoCoherentComplexFrom K' m :=
  Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso
    (DerivedCategory.Q.obj K) m ⟨K, h, ⟨Iso.refl _⟩⟩ K' (DerivedCategory.Q.mapIso e.symm)

/-- complex level of Stacks 09U7 for a flat morphism of ringed spaces -/
public theorem isPseudoCoherentComplexFrom_modulePullback_of_isFlat {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (hf : AlgebraicGeometry.IsFlat f)
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u} Y) ℤ) (m : ℤ)
    (hK : IsPseudoCoherentComplexFrom K m) :
    IsPseudoCoherentComplexFrom
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m :=
  Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso _ m
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback
      f (DerivedCategory.Q.obj K) m ⟨K, hK, ⟨Iso.refl _⟩⟩)
    _ (AlgebraicGeometry.RingedSpace.derivedPullbackQIso f hf K).symm

end Standard

/-! ### Descent of module-level pseudo-coherence along a finite family of flat ring maps -/

section Pi

attribute [local instance 2000] _root_.HasDerivedCategory.standard

open StacksDraft.PseudoCoherence

variable {n : ℕ} {S : Fin n → Type u} [∀ i, CommRing (S i)]

/-- The idempotents `Pi.single i 1` of a finite product of rings generate the unit ideal. -/
public theorem piSingle_span_eq_top :
    Ideal.span (Set.range fun i : Fin n => (Pi.single i (1 : S i) : ∀ j, S j)) = ⊤ := by
  classical
  rw [Ideal.eq_top_iff_one]
  have hsum : (∑ i : Fin n, Pi.single i (1 : S i) : ∀ j, S j) = 1 := by
    ext j
    simp
  rw [← hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.subset_span (Set.mem_range_self i)

/-- The `i`-th factor of a finite product of rings is the localization of the product away from
the idempotent `Pi.single i 1`, compatibly with the two maps out of the product. -/
public theorem exists_ringEquiv_localizationAway_piSingle (i : Fin n) :
    ∃ e : S i ≃+* Localization.Away (Pi.single i (1 : S i) : ∀ j, S j),
      e.toRingHom.comp (Pi.evalRingHom S i) =
        algebraMap (∀ j, S j) (Localization.Away (Pi.single i (1 : S i) : ∀ j, S j)) := by
  classical
  let C : Type u := ∀ j, S j
  let e₀ : C := Pi.single i 1
  let π : C →+* S i := Pi.evalRingHom S i
  let _ : Algebra C (S i) := π.toAlgebra
  have hloc : IsLocalization.Away e₀ (S i) := by
    apply IsLocalization.away_of_isIdempotentElem
    · change e₀ * e₀ = e₀
      rw [← Pi.single_mul_left]
      simp [e₀]
    · exact RingHom.ker_evalRingHom _ _
    · exact π.surjective
  let eAlg : Localization.Away e₀ ≃ₐ[C] S i :=
    IsLocalization.algEquiv (Submonoid.powers e₀) (Localization.Away e₀) (S i)
  exact ⟨eAlg.symm.toRingEquiv, RingHom.ext eAlg.symm.commutes⟩

/-- Extension of scalars along a flat ring map is additive and preserves finite limits and
finite colimits. -/
private theorem extendScalars_exact_of_flat {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat) :
    (ModuleCat.extendScalars.{u, u, u} φ).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).leftAdjoint_preservesColimits
  exact ⟨extendScalars_additive.{u, u} _, extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hφ,
    PreservesColimitsOfSize.preservesFiniteColimits _⟩

/-- Extension of scalars along an isomorphism of rings preserves `m`-pseudo-coherence. -/
public theorem isPseudoCoherentFrom_extendScalars_of_ringEquiv {A B : Type u} [CommRing A]
    [CommRing B] (e : A ≃+* B) (K : CochainComplex (ModuleCat.{u} A) ℤ) (m : ℤ)
    (h : IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) m := by
  let F := ModuleCat.extendScalars.{u, u, u} e.toRingHom
  obtain ⟨_, _, _⟩ := extendScalars_exact_of_flat e.toRingHom
    (RingHom.Flat.of_bijective (f := e.toRingHom) e.bijective)
  have hF : ∀ M : ModuleCat.{u} A, Module.Finite A M → Module.Free A M →
      Module.Finite B (F.obj M) ∧ Module.Free B (F.obj M) := by
    intro M _ _
    have hG := restrictScalars_finiteFree e.symm M
    let eM := (ModuleCat.extendScalarsIsoRestrictScalarsSymm e).app M
    have h1 : Module.Finite B ((ModuleCat.restrictScalars.{u} e.symm.toRingHom).obj M) := hG.1
    have h2 : Module.Free B ((ModuleCat.restrictScalars.{u} e.symm.toRingHom).obj M) := hG.2
    exact ⟨Module.Finite.equiv eM.toLinearEquiv.symm, Module.Free.of_equiv eM.toLinearEquiv.symm⟩
  exact ((exactFunctor_preserves_pseudoCoherent F hF (DerivedCategory.Q.obj K)).1 m h).ofIso
    (F.mapDerivedCategoryFactors.app K)

/-- **Descent of `m`-pseudo-coherence along a finite family of ring maps whose product is
faithfully flat.** -/
@[sga "6 III 1.10" "clause b), special case"]
public theorem isPseudoCoherentFrom_of_faithfullyFlat_pi {R : Type u} [CommRing R]
    (φ : ∀ i, R →+* S i) (hff : (RingHom.pi φ).FaithfullyFlat)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (h : ∀ i, IsPseudoCoherentFrom (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (φ i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) m) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m := by
  classical
  let C : Type u := ∀ i, S i
  let ψ : R →+* C := RingHom.pi φ
  let _ : (ModuleCat.extendScalars.{u, u, u} ψ).Additive := extendScalars_additive.{u, u} _
  let N := ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj M
  have key : IsPseudoCoherentFrom (DerivedCategory.Q.obj N) m := by
    refine (isPseudoCoherentFrom_and_isPseudoCoherent_of_localization.{u, u}
      (fun i : Fin n => (Pi.single i (1 : S i) : C)) piSingle_span_eq_top _ m).1 ?_
    intro i
    obtain ⟨η, hη⟩ := exists_ringEquiv_localizationAway_piSingle (S := S) i
    set L := Localization.Away (Pi.single i (1 : S i) : C)
    let α : C →+* L := algebraMap C L
    let _ : (ModuleCat.extendScalars.{u, u, u} α).Additive := extendScalars_additive.{u, u} _
    let _ : (ModuleCat.extendScalars.{u, u, u} (α.comp ψ)).Additive :=
      extendScalars_additive.{u, u} _
    let _ : (ModuleCat.extendScalars.{u, u, u} (φ i)).Additive := extendScalars_additive.{u, u} _
    let _ : (ModuleCat.extendScalars.{u, u, u} η.toRingHom).Additive :=
      extendScalars_additive.{u, u} _
    let _ : (ModuleCat.extendScalars.{u, u, u} (η.toRingHom.comp (φ i))).Additive :=
      extendScalars_additive.{u, u} _
    have heq : α.comp ψ = η.toRingHom.comp (φ i) :=
      RingHom.ext fun a => (RingHom.congr_fun hη (ψ a)).symm
    have iso1 : (localizationAwayFunctorAux.{u, u} (Pi.single i (1 : S i) : C)).obj
        (DerivedCategory.Q.obj N) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) := by
      obtain ⟨_, _, _⟩ := extendScalars_exact_of_flat α
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat L (Submonoid.powers (Pi.single i (1 : S i) : C))))
      exact (ModuleCat.extendScalars.{u, u, u} α).mapDerivedCategoryFactors.app N
    have iso2 : (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) ≅
        ((ModuleCat.extendScalars.{u, u, u} (η.toRingHom.comp (φ i))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M :=
      (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp ψ α).symm
        (ComplexShape.up ℤ)).app M ≪≫
        eqToIso (congrArg (fun k : R →+* L =>
          ((ModuleCat.extendScalars.{u, u, u} k).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) heq)
    have iso3 :
        ((ModuleCat.extendScalars.{u, u, u} (η.toRingHom.comp (φ i))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M ≅
        ((ModuleCat.extendScalars.{u, u, u} η.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{u, u, u} (φ i)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) :=
      ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp (φ i) η.toRingHom).symm
        (ComplexShape.up ℤ)).app M).symm
    exact ((isPseudoCoherentFrom_extendScalars_of_ringEquiv η _ m (h i)).ofIso
      (DerivedCategory.Q.mapIso (iso2 ≪≫ iso3)).symm).ofIso iso1.symm
  exact (isPseudoCoherentFrom_and_isPseudoCoherent_of_faithfullyFlat_baseChange.{u, u, u}
    ψ hff M m).1 key

/-- **A finite jointly surjective family of flat morphisms of affine schemes induces a
faithfully flat map to the product of the rings of sections.** Each map is flat on global
sections, hence so is the product (a finite product of flat modules is flat), and joint
surjectivity makes the induced map of spectra surjective. -/
@[sga "3 VIB 11.9.1" "partial"]
public theorem faithfullyFlat_pi_of_affine_cover {T : Scheme.{u}} [IsAffine T] {k : ℕ}
    (Z : Fin k → Scheme.{u}) [∀ i, IsAffine (Z i)] (g : ∀ i, Z i ⟶ T)
    (hflat : ∀ i, Flat (g i)) (hcover : ∀ x : T, ∃ i, ∃ y : Z i, g i y = x) :
    (RingHom.pi fun i => (g i).appTop.hom).FaithfullyFlat := by
  classical
  let A : Type u := Γ(T, ⊤)
  let B : Fin k → Type u := fun i => Γ(Z i, ⊤)
  let φi : ∀ i, A →+* B i := fun i => (g i).appTop.hom
  let φ : A →+* (∀ i, B i) := RingHom.pi φi
  let _ : ∀ i, Algebra A (B i) := fun i => (φi i).toAlgebra
  let _ : Algebra A (∀ i, B i) := φ.toAlgebra
  have hflatComp : ∀ i, Module.Flat A (B i) := by
    intro i
    have happ : RingHom.Flat (φi i) := by
      simpa [φi, A, B] using (g i).flat_appTop
    exact RingHom.flat_algebraMap_iff.mp happ
  have hflatPi : Module.Flat A (∀ i, B i) := by
    have _ : Module.Flat A (Π₀ i, B i) := Module.Flat.dfinsupp_iff.mpr hflatComp
    exact Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := A) (M := B)).symm
  have hsurj : Function.Surjective (PrimeSpectrum.comap φ) := by
    intro p
    let x : T := T.isoSpec.inv ⟨p, p.isPrime⟩
    obtain ⟨i, y, hy⟩ := hcover x
    let qi : PrimeSpectrum (B i) := (Z i).isoSpec.hom y
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom B i) qi, ?_⟩
    have hcmp : (Pi.evalRingHom B i).comp φ = φi i := RingHom.ext fun _ => rfl
    have hpointSpec : Spec.map (g i).appTop ((Z i).isoSpec.hom y) = T.isoSpec.hom x := by
      simpa only [Scheme.Hom.comp_apply, hy] using
        congrArg (fun q : Z i ⟶ Spec Γ(T, ⊤) => q y) (Scheme.isoSpec_hom_naturality (g i))
    have hpoint : PrimeSpectrum.comap (φi i) qi = p := by
      rw [← Spec.map_apply, hpointSpec]
      change (T.isoSpec).hom ((T.isoSpec).inv ⟨p, p.isPrime⟩) = p
      exact congrArg (fun q : Spec Γ(T, ⊤) ⟶ Spec Γ(T, ⊤) =>
        q ⟨p, p.isPrime⟩) (T.isoSpec.inv_hom_id)
    rw [← hpoint, ← hcmp]
    exact (congrFun (PrimeSpectrum.comap_comp φ (Pi.evalRingHom B i)) qi).symm
  exact (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective (f := φ)).2
    ⟨RingHom.flat_algebraMap_iff.mpr hflatPi, hsurj⟩

end Pi

/-! ### The affine case at the complex level -/

section Affine

attribute [local instance 2000] _root_.HasDerivedCategory.standard

/-- **The affine case of fpqc descent, at the complex level.** -/
@[sga "6 III 1.1.3" "special case"]
public theorem isPseudoCoherentComplexFrom_tilde_of_faithfullyFlat_pi {R : CommRingCat.{u}}
    {n : ℕ} {S : Fin n → CommRingCat.{u}} (φ : ∀ i, R ⟶ S i)
    (hff : (RingHom.pi fun i => (φ i).hom).FaithfullyFlat)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (h : ∀ i, IsPseudoCoherentComplexFrom (X := (Spec (S i)).toRingedSpace)
      (((tilde.functor (S i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u} (φ i).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) m) :
    IsPseudoCoherentComplexFrom (X := (Spec R).toRingedSpace)
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) m :=
  (isPseudoCoherentComplexFrom_tilde_iff M m).mpr
    (isPseudoCoherentFrom_of_faithfullyFlat_pi (S := fun i => (S i : Type u))
      (fun i => (φ i).hom) hff M m
      fun i => (isPseudoCoherentComplexFrom_tilde_iff _ m).mp (h i))

end Affine

/-! ### Derived pullback, at a free choice of derived category -/

section Free

variable {X Y Z W : RingedSpace.{u, u}}

/-- Degreewise pullback along a morphism between two open subspaces, passed to homotopy
categories, has a left derived functor.

This is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy` seated
at such a morphism, where instance search does not find it: the goal reaches the structure sheaf of
an open subspace through the `Stacks.Cohomology.HigherDirectImage.restrictToOpen` spelling and the
general instance reaches it through `structureSheafRing`. It is
`AlgebraicGeometry.RingedSpace.hasLeftDerivedFunctor_pullbackOnHomotopy_openSubspaces` with
the morphism universe of the derived category left free, which is what makes it apply at the
locally small model as well as at the standard one. -/
public instance hasLeftDerivedFunctor_pullbackOnHomotopy_restrictToOpen
    {U : TopologicalSpace.Opens X.carrier} {V : TopologicalSpace.Opens Y.carrier}
    (g : restrictToOpen Y V ⟶ restrictToOpen X U) :
    (pullbackOnHomotopy g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing (restrictToOpen X U)))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy g

/-- For a flat morphism of ringed spaces the derived pullback of the class of a complex is the
class of its degreewise pullback. -/
public def derivedPullbackObjQIso (f : X ⟶ Y) (hf : AlgebraicGeometry.IsFlat f)
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u} Y) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  have _ : PreservesFiniteLimits (modulePullback f) :=
    preservesFiniteLimits_modulePullback_of_isFlat f hf
  have _ : PreservesFiniteColimits (modulePullback f) := preservesFiniteColimits_modulePullback f
  (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso f).app (DerivedCategory.Q.obj K) ≪≫
    ((modulePullback f).mapDerivedCategoryFactors).app K

/-- **Stacks 09U7 for a flat morphism of ringed spaces, at a free choice of derived category.** -/
public theorem isPseudoCoherentFrom_derivedPullback_of_isFlat (f : X ⟶ Y)
    (hf : AlgebraicGeometry.IsFlat f) (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} Y))
    (m : ℤ) (hE : IsPseudoCoherentFrom E m) :
    IsPseudoCoherentFrom ((derivedPullback f).obj E) m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact ⟨_, isPseudoCoherentComplexFrom_modulePullback_of_isFlat f hf K m hK,
    ⟨(derivedPullbackObjQIso f hf K).symm ≪≫ (derivedPullback f).mapIso e⟩⟩

/-- Derived pullback along the identity is the identity. -/
public def derivedPullbackIdIso (Y : RingedSpace.{u, u}) :
    derivedPullback (𝟙 Y) ≅ 𝟭 (DerivedCategory (StrictlyPerfect.OXMod.{u, u} Y)) :=
  have _ : PreservesFiniteLimits (modulePullback (𝟙 Y)) :=
    preservesFiniteLimits_of_natIso (RingedSpaceModuleAdjunction.modulePullbackId Y).symm
  have _ : PreservesFiniteColimits (modulePullback (𝟙 Y)) :=
    preservesFiniteColimits_modulePullback (𝟙 Y)
  AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso (𝟙 Y) ≪≫
    Functor.mapDerivedCategoryCongr (RingedSpaceModuleAdjunction.modulePullbackId Y) ≪≫
    Functor.mapDerivedCategoryId _

/-- The two ways round a commuting square of derived pullbacks. -/
public def derivedPullbackCommSquareIso (p : W ⟶ Y) (q : W ⟶ Z) (a : Y ⟶ X)
    (b : Z ⟶ X) (hsq : p ≫ a = q ≫ b) (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) :
    (derivedPullback p).obj ((derivedPullback a).obj E) ≅
      (derivedPullback q).obj ((derivedPullback b).obj E) :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).app E ≪≫
    eqToIso (congrArg (fun k : W ⟶ X => (derivedPullback k).obj E) hsq) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical q b).app E).symm

end Free

/-! ### Pullback along an isomorphism of schemes -/

section Iso

variable {X Y : Scheme.{u}}

/-- Pulling back along an isomorphism of schemes and then along its inverse changes nothing. -/
public def derivedPullbackInvHomIso (e : X ≅ Y)
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} Y.toRingedSpace)) :
    (derivedPullback e.inv.toLRSHom.toShHom).obj
      ((derivedPullback e.hom.toLRSHom.toShHom).obj E) ≅ E :=
  have he : e.inv.toLRSHom.toShHom ≫ e.hom.toLRSHom.toShHom = 𝟙 Y.toRingedSpace :=
    congrArg (fun q : Y ⟶ Y => q.toLRSHom.toShHom) e.inv_hom_id
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical e.inv.toLRSHom.toShHom
      e.hom.toLRSHom.toShHom).app E ≪≫
    eqToIso (congrArg (fun q : Y.toRingedSpace ⟶ Y.toRingedSpace =>
      (derivedPullback q).obj E) he) ≪≫ (derivedPullbackIdIso Y.toRingedSpace).app E

/-- **`m`-pseudo-coherence is reflected by derived pullback along an isomorphism of schemes.** -/
public theorem isPseudoCoherentFrom_of_derivedPullback_iso (e : X ≅ Y)
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} Y.toRingedSpace)) (m : ℤ)
    (h : IsPseudoCoherentFrom ((derivedPullback e.hom.toLRSHom.toShHom).obj E) m) :
    IsPseudoCoherentFrom E m :=
  (isPseudoCoherentFrom_derivedPullback_of_isFlat e.inv.toLRSHom.toShHom
    (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom e.inv) _ m h).ofIso
      (derivedPullbackInvHomIso e E)

end Iso


/-! ### The affine case at the level of objects -/

section AffineObjects

/-- Degreewise sheafification of a complex of `R`-modules, in the ringed-space spelling of the
category of `𝒪_{Spec R}`-modules. -/
public abbrev tildeCochainComplex (R : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      CochainComplex (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace) ℤ :=
  (tilde.functor R : ModuleCat.{u} R ⥤
      StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- A morphism of affine schemes obtained from a flat ring map has flat stalk maps. -/
@[ega "III 1.4.15.5" "Second assertion"]
public theorem isFlat_toShHom_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Flat) :
    AlgebraicGeometry.IsFlat (Spec.map φ).toLRSHom.toShHom :=
  have _ : Flat (Spec.map φ) := AlgebraicGeometry.Flat.SpecMap_iff.mpr hφ
  Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom (Spec.map φ)

/-- **Stacks 06Z0 in the form the descent uses it.** An object of the derived category of
`𝒪_{Spec R}`-modules whose cohomology sheaves are quasi-coherent is the class of the degreewise
sheafification of a complex of `R`-modules. -/
public theorem exists_iso_Q_tildeCochainComplex (R : CommRingCat.{u})
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace) i).obj E).IsQuasicoherent) :
    ∃ M : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty ((DerivedCategory.Q
        (C := StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace)).obj
          ((tildeCochainComplex R).obj M) ≅ E) := by
  obtain ⟨N, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := derivedTilde R)
    (⟨E, hE⟩ : Stacks.Duality.quasiCoherentDerivedCategory (Spec R))
  exact ⟨DerivedCategory.Q.objPreimage N, ⟨((tilde.functor R).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage N)).symm ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso N) ≪≫
    ((derivedTildeCompι R).app N).symm ≪≫
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.mapIso e⟩⟩

/-- **The affine case of Stacks 09UE.** Let `R` be a commutative ring and let `R → S i` be
finitely many flat ring maps whose product is faithfully flat. An object of `D_QCoh(𝒪_{Spec R})`
whose derived pullback to each `Spec (S i)` is `m`-pseudo-coherent is `m`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_of_faithfullyFlat_pi_spec {R : CommRingCat.{u}} {n : ℕ}
    {S : Fin n → CommRingCat.{u}} (φ : ∀ i, R ⟶ S i)
    (hff : (RingHom.pi fun i => (φ i).hom).FaithfullyFlat) (hflat : ∀ i, (φ i).hom.Flat)
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace) i).obj E).IsQuasicoherent) (m : ℤ)
    (h : ∀ i, IsPseudoCoherentFrom
      ((derivedPullback (Spec.map (φ i)).toLRSHom.toShHom).obj E) m) :
    IsPseudoCoherentFrom E m := by
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_Q_tildeCochainComplex R E hE
  refine ⟨(tildeCochainComplex R).obj M, ?_, ⟨e⟩⟩
  refine isPseudoCoherentComplexFrom_tilde_of_faithfullyFlat_pi φ hff M m fun i => ?_
  exact isPseudoCoherentComplexFrom_of_isoComplex m
    ((isPseudoCoherentFrom_Q_obj_iff _ m).mp
      (((h i).ofIso ((derivedPullback (Spec.map (φ i)).toLRSHom.toShHom).mapIso e).symm).ofIso
        (derivedPullbackObjQIso (Spec.map (φ i)).toLRSHom.toShHom
          (isFlat_toShHom_specMap (φ i) (hflat i)) ((tildeCochainComplex R).obj M))))
    ((AlgebraicGeometry.tildePullbackComplexIso R (S i) (φ i)).app M)

end AffineObjects

/-! ### Restriction and derived pullback across a square of open immersions -/

section Square

variable {X Y : RingedSpace.{u, u}}

/-- **The derived pullback of a derived restriction is the derived restriction of the derived
pullback**, across a commuting square of a flat morphism with two open immersions, at a free
choice of derived category. This is
`AlgebraicGeometry.RingedSpace.derivedPullbackRestrictIso` with the model not pinned. -/
public def derivedPullbackRestrictIsoFree (f : Y ⟶ X) (hf : AlgebraicGeometry.IsFlat f)
    (U : TopologicalSpace.Opens X.carrier) (V : TopologicalSpace.Opens Y.carrier)
    (g : restrictToOpen Y V ⟶ restrictToOpen X U) (hg : AlgebraicGeometry.IsFlat g)
    (hsq : g ≫ openSubspaceInclusion X U = openSubspaceInclusion Y V ≫ f)
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) :
    (derivedPullback g).obj ((derivedRestrictModules X U).obj E) ≅
      (derivedRestrictModules Y V).obj ((derivedPullback f).obj E) :=
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  (derivedPullback g).mapIso ((derivedRestrictModules X U).mapIso e.symm) ≪≫
    (derivedPullback g).mapIso (derivedRestrictModulesObjQIso X U K) ≪≫
    derivedPullbackObjQIso g hg (restrictComplex K U) ≪≫
    DerivedCategory.Q.mapIso (restrictComplexPullbackSquareIso f U V g hsq K) ≪≫
    (derivedRestrictModulesObjQIso Y V
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (derivedRestrictModules Y V).mapIso (derivedPullbackObjQIso f hf K).symm ≪≫
    (derivedRestrictModules Y V).mapIso ((derivedPullback f).mapIso e)

end Square

/-! ### The fpqc refinement over an affine open -/

section Refinement

/-- **The reduction of Stacks 09UE to the affine case, from Stacks 03L7.** Every point of the
target of an fpqc covering has an affine open neighbourhood `U` which is covered by the images
of finitely many affine opens of the members of the covering. -/
public theorem exists_affineOpen_affine_images_cover {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ (n : ℕ) (a : Fin n → I)
      (V : ∀ j, (Y (a j)).Opens), (∀ j, IsAffineOpen (V j)) ∧
        ⋃ j, f (a j) '' (V j : Set (Y (a j))) = (U : Set X) := by
  obtain ⟨-, A, U, hUaff, hUcover, hfin⟩ :=
    (AlgebraicGeometry.mem_fpqcPrecoverage_iff_exists_affine_open_cover f).mp hf
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ a, (U a : Set X) by simp [hUcover])
  obtain ⟨n, i, V, hVc, hEq⟩ := hfin a
  have hcov : IsCompactOpenCovered (fun k => (f k).base) (U a : Set X) :=
    IsCompactOpenCovered.of_finite i V hVc hEq
  obtain ⟨n', a', W, hWb, hWcov⟩ := hcov.exists_mem_of_isBasis
    (fun j => (Y j).isBasis_affineOpens) (fun _ _ hW => hW.isCompact)
  exact ⟨U a, hUaff a, hxa, n', a', W, hWb, hWcov⟩

end Refinement

/-! ### Stacks 09UE -/

section Main

/-- Every member of an fpqc covering family is flat. -/
public theorem flat_of_mem_fpqcPrecoverage {X : Scheme.{u}} {I : Type v} (Y : I → Scheme.{u})
    (f : ∀ i, Y i ⟶ X) (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X) (i : I) :
    Flat (f i) :=
  (AlgebraicGeometry.mem_fpqcPrecoverage_iff_affine_finite_support f).mp hf |>.1 i

/-- **Stacks 09UE.** -/
@[stacks 09UE]
public theorem isPseudoCoherentFrom_iff_forall_fpqc {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (E : Stacks.Duality.quasiCoherentDerivedCategory X) (m : ℤ) :
    IsPseudoCoherentFrom E.obj m ↔
      ∀ i : I, IsPseudoCoherentFrom
        ((Stacks.Duality.quasiCoherentDerivedPullback' (f i)).obj E).obj m := by
  refine ⟨fun hE i => ?_, fun hEi => ?_⟩
  · have := flat_of_mem_fpqcPrecoverage Y f hf i
    exact isPseudoCoherentFrom_derivedPullback_of_isFlat (f i).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom (f i)) E.obj m hE
  · have hflat : ∀ i, Flat (f i) := flat_of_mem_fpqcPrecoverage Y f hf
    refine isPseudoCoherentFrom_of_local_restrict E.obj m fun x => ?_
    obtain ⟨U, hU, hxU, n, a, V, hV, hVcov⟩ := exists_affineOpen_affine_images_cover Y f hf x
    refine ⟨U, hxU, ?_⟩
    have hUaff : IsAffine U.toScheme := hU
    have hVaff : ∀ j, IsAffine (V j).toScheme := hV
    have hVU : ∀ j, V j ≤ (f (a j)) ⁻¹ᵁ U := by
      intro j y hy
      change (f (a j)) y ∈ (U : Set X)
      rw [← hVcov]
      exact Set.mem_iUnion.mpr ⟨j, ⟨y, hy, rfl⟩⟩
    have hgcover : ∀ y : U.toScheme, ∃ j, ∃ z : (V j).toScheme,
        (f (a j)).resLE U (V j) (hVU j) z = y := by
      intro y
      have hy : (U.ι) y ∈ (⋃ j, (f (a j)) '' (V j : Set (Y (a j)))) := by
        rw [hVcov]
        exact y.2
      obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
      refine ⟨j, ⟨z, hz⟩, Subtype.ext ?_⟩
      change ((f (a j)).resLE U (V j) (hVU j) ≫ U.ι) ⟨z, hz⟩ = U.ι y
      rw [Scheme.Hom.resLE_comp_ι]
      exact hzy
    have hEUqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) i).obj
          ((derivedRestrictModules X.toRingedSpace U).obj E.obj)).IsQuasicoherent := by
      intro i
      have hres : (((restrictModules.{u, u} X.toRingedSpace U).obj
          ((DerivedCategory.homologyFunctor
            (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj E.obj))).IsQuasicoherent :=
        (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
          ((restrictModulesIsoRestrictFunctor X U).app _).symm
          (@Scheme.Modules.isQuasicoherent_restrictFunctor U.toScheme X U.ι inferInstance
            ((DerivedCategory.homologyFunctor X.Modules i).obj E.obj) (E.property i))
      exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (restrictModules.{u, u} X.toRingedSpace U) i).app E.obj).symm hres
    have hgpc : ∀ j, IsPseudoCoherentFrom
        ((derivedPullback ((f (a j)).resLE U (V j) (hVU j)).toLRSHom.toShHom).obj
          ((derivedRestrictModules X.toRingedSpace U).obj E.obj)) m := fun j =>
      (isPseudoCoherentFrom_derivedRestrictModules
        ((derivedPullback (f (a j)).toLRSHom.toShHom).obj E.obj) m (hEi (a j)) (V j)).ofIso
        (derivedPullbackRestrictIsoFree (f (a j)).toLRSHom.toShHom
          (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom (f (a j))) U (V j)
          ((f (a j)).resLE U (V j) (hVU j)).toLRSHom.toShHom
          (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)
          (Stacks.Cohomology.PseudoCoherence.FlatDescent.resLE_square (f (a j)) U (V j)
            (hVU j)) E.obj).symm
    refine isPseudoCoherentFrom_of_derivedPullback_iso U.toScheme.isoSpec.symm _ m ?_
    refine isPseudoCoherentFrom_of_faithfullyFlat_pi_spec
      (fun j => ((f (a j)).resLE U (V j) (hVU j)).appTop) ?_ (fun j => Scheme.Hom.flat_appTop _)
      _ ?_ m ?_
    · exact faithfullyFlat_pi_of_affine_cover (fun j => (V j).toScheme)
        (fun j => (f (a j)).resLE U (V j) (hVU j)) (fun _ => inferInstance) hgcover
    · exact fun i => Stacks.Duality.isQuasicoherent_homology_derivedPullback'
        U.toScheme.isoSpec.inv ⟨_, hEUqc⟩ i
    · intro j
      have hsq := congrArg
        (fun q : Spec Γ((V j).toScheme, ⊤) ⟶ U.toScheme => q.toLRSHom.toShHom)
        (Scheme.isoSpec_inv_naturality ((f (a j)).resLE U (V j) (hVU j)))
      exact (isPseudoCoherentFrom_derivedPullback_of_isFlat
        ((V j).toScheme.isoSpec.inv).toLRSHom.toShHom
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _) _ m
        (hgpc j)).ofIso (derivedPullbackCommSquareIso _ _ _ _ hsq _).symm

end Main

end Stacks.Cohomology.PseudoCoherence.FpqcDescent

end
