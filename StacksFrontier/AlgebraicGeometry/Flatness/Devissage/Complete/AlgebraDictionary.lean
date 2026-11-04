module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraComparison
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.RingTheory.Flat.CompleteDevissageChain
public import StacksFrontier.RingTheory.Smooth.GenericFibrePoint

/-!
# A one-step dévissage as a stage of an algebraic complete dévissage

All four schemes of a one-step dévissage `(Z, Y, i, π, 𝒢)` of `ℱ/X/S` are affine, so the whole
datum is determined by the rings of functions on them, and
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraComparison.lean` translates
each of its conditions into the corresponding condition on those rings. This file assembles
that translation into a single object: a `Module.DevissageStageData`, the datum `(A, B, M, α)` of
one stage of an algebraic complete dévissage in the sense of Stacks 05HX, with `A = Γ(Z, ⊤)`,
`B = Γ(Y, ⊤)` and `M = Γ(𝒢, ⊤)` over the base ring `R = Γ(S, ⊤)`.

Two of the twelve items of a stage are not determined by the one-step dévissage alone and are
taken as arguments: the rank of the finite free module and the map out of it, which a
scheme-theoretic dévissage records as a map of sheaves rather than of modules, and the
condition that this map is an isomorphism over the residue field of the prime `rB`, which a
scheme-theoretic dévissage records at the generic point of the fibre.

For a stage of a *complete* dévissage, which carries a free map and its generic-fibre
isomorphism, the first of those two arguments is supplied here:
`AlgebraicGeometry.DevissageStage.sectionsAlpha` is the map of modules induced by the free map
of the stage.

## Main definitions

* `AlgebraicGeometry.OneStepDevissage.toDevissageStage`: a one-step dévissage, together with a
  module-level map out of a finite free module which is an isomorphism over the residue field
  of `rB`, is a stage of an algebraic complete dévissage over `r`.
* `AlgebraicGeometry.OneStepDevissage.pushforwardSectionsEquiv`: the sections of a direct image,
  read as a module over the ring of functions downstairs in the two spellings of the restriction
  of scalars.
* `AlgebraicGeometry.DevissageStage.sectionsAlpha`: the map of modules induced by the free map of
  a stage of a complete dévissage, and
  `AlgebraicGeometry.DevissageStage.sectionsAlphaSourceEquiv` the identification of its source
  with the global sections of the free module of the stage.
* `AlgebraicGeometry.DevissageStage.cokerSectionsEquiv`: the cokernel of that map of modules is
  the module of global sections of the cokernel of the free map of the stage.

## Main results

* `AlgebraicGeometry.OneStepDevissage.toDevissageStage_A`,
  `AlgebraicGeometry.OneStepDevissage.toDevissageStage_B` and
  `AlgebraicGeometry.OneStepDevissage.toDevissageStage_M`: the three types of the stage are the
  rings of functions on the closed subscheme and on the smooth scheme, and the sections of the
  module on the closed subscheme.
* `AlgebraicGeometry.asIdeal_isoSpec_hom_fiberι_eq_map`: the prime of `Γ(Y, ⊤)` corresponding to
  a generic point of the fibre of `g` over `s` is the extension `rΓ(Y, ⊤)`.
* `AlgebraicGeometry.DevissageStage.fiber_bijective_sectionsAlpha`: **the generic-fibre condition
  of a stage is the bijectivity condition of an algebraic stage**, which is the last of the
  twelve items of Stacks 05HX left open by
  `AlgebraicGeometry.OneStepDevissage.toDevissageStage`.
* `AlgebraicGeometry.DevissageStage.surjective_sectionsAlpha_of_isZero`: the vanishing of the
  cokernel of a final stage is surjectivity of its map of modules.

## Implementation notes

The `Γ(S, ⊤)`-algebra structures are the ones induced by the morphisms themselves, through
`RingHom.toAlgebra`, so that `algebraMap` is literally a map on functions; this is what lets the
conditions proved in `AlgebraComparison` be used without transport. On `Γ(Z, ⊤)` the structure
chosen is the one induced by `f.appTop ≫ i.appTop`, the route through the scheme being
dévissed, so that the map `Γ(X, ⊤) → Γ(Z, ⊤)` of the stage commutes with the structure maps by
`rfl`; the other map of the stage, `Γ(Y, ⊤) → Γ(Z, ⊤)`, then commutes with them by
`AlgebraicGeometry.OneStepDevissage.appTop_over_base`.

`AlgebraicGeometry.DevissageStage.sectionsAlpha` is built out of three identifications, each of
which is the identity on the underlying sets or a named comparison, so that the result is
literally the map on global sections of the free map of the stage:
`AlgebraicGeometry.freeSectionsEquiv` for the sections of the free module on the affine scheme
`Y`, `AlgebraicGeometry.Scheme.Modules.sectionsLinearMap` for the sections of the morphism, and
`AlgebraicGeometry.OneStepDevissage.pushforwardSectionsEquiv` for the two spellings of the
restriction of scalars along `π` on the sections of the direct image. The index type is
`ULift (Fin rank)`, since `AlgebraicGeometry.SheafOfModules.free` takes its index type in the
universe of the sheaf of rings, and `Finsupp.domLCongr` removes the `ULift`.

The remaining condition of a stage, `fiber_bijective`, is supplied by
`AlgebraicGeometry.DevissageStage.fiber_bijective_sectionsAlpha`, and it needs two
identifications. The generic point of the fibre of `g` over `s`, at which
`AlgebraicGeometry.DevissageStage.genericFiber_isIso` asserts invertibility, has to be identified
with the prime `rB` of `Γ(Y, ⊤)` shown to be prime by
`Ideal.isPrime_map_of_smooth_of_geometricallyIrreducible`; that is
`AlgebraicGeometry.asIdeal_isoSpec_hom_fiberι_eq_map`, which reads the ring-theoretic
`Ideal.eq_map_of_mem_fiber_of_fiber_le` through `Y ≅ Spec Γ(Y, ⊤)`. And the invertibility of the
pullback of `α` to the spectrum of that residue field has to be turned into bijectivity of the
base change of the map of modules; that is
`AlgebraicGeometry.bijective_baseChange_sectionsLinearMap_of_isIso_pullback`, resting on
`AlgebraicGeometry.bijective_rTensor_of_isIso_pullback_map_tilde`, the converse of
`AlgebraicGeometry.isIso_pullback_map_tilde`.

The vanishing of the final cokernel and the identification of the module dévissed by the next
stage are the other two items a chain of stages needs, and both are the affine dictionary applied
to `α` once more: `AlgebraicGeometry.surjective_sectionsLinearMap_of_epi` and
`AlgebraicGeometry.sectionsCokernelEquiv`. The ranges that the two sides quotient by agree by
`AlgebraicGeometry.DevissageStage.map_range_sectionsLinearMap`, the source identification of
`sectionsAlpha` being bijective.

## References

* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.OneStepDevissage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

variable (D : OneStepDevissage f F s)

/-- The functions on the smooth scheme of a one-step dévissage, as an algebra over the functions
on the base. -/
public abbrev algebraSmooth : Algebra Γ(S, ⊤) Γ(D.Y, ⊤) := D.g.appTop.hom.toAlgebra

/-- The functions on the scheme being dévissed, as an algebra over the functions on the base. -/
public abbrev algebraSource : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra

/-- The functions on the closed subscheme of a one-step dévissage, as an algebra over the
functions on the base, through the scheme being dévissed. -/
public abbrev algebraClosed : Algebra Γ(S, ⊤) Γ(D.Z, ⊤) :=
  (f.appTop ≫ D.i.appTop).hom.toAlgebra

/-- The closed immersion of a one-step dévissage, as a map of algebras over the functions on the
base. -/
public def closedAlgHom :
    letI := algebraSource (f := f)
    letI := D.algebraClosed
    Γ(X, ⊤) →ₐ[Γ(S, ⊤)] Γ(D.Z, ⊤) :=
  letI := algebraSource (f := f)
  letI := D.algebraClosed
  { D.i.appTop.hom with commutes' := fun _ => rfl }

/-- The finite morphism of a one-step dévissage, as a map of algebras over the functions on the
base. -/
public def finiteAlgHom :
    letI := D.algebraSmooth
    letI := D.algebraClosed
    Γ(D.Y, ⊤) →ₐ[Γ(S, ⊤)] Γ(D.Z, ⊤) :=
  letI := D.algebraSmooth
  letI := D.algebraClosed
  { D.π.appTop.hom with
    commutes' := fun x => congrArg (fun φ => CommRingCat.Hom.hom φ x) D.appTop_over_base.symm }

/-- The underlying ring map of `closedAlgHom` is the map on global sections of the closed
immersion. -/
@[simp]
public lemma closedAlgHom_toRingHom :
    letI := algebraSource (f := f)
    letI := D.algebraClosed
    (D.closedAlgHom).toRingHom = D.i.appTop.hom := rfl

/-- The underlying ring map of `finiteAlgHom` is the map on global sections of the finite
morphism. -/
@[simp]
public lemma finiteAlgHom_toRingHom :
    letI := D.algebraSmooth
    letI := D.algebraClosed
    (D.finiteAlgHom).toRingHom = D.π.appTop.hom := rfl

/-- **A one-step dévissage is a stage of an algebraic complete dévissage.**

Given a prime `r` of the functions on the base, a rank and a map `alpha` out of the finite free
module of that rank over the functions on the smooth scheme, landing in the sections of the
module on the closed subscheme, and given that `alpha` becomes an isomorphism over the residue
field of `rB`, the rings of functions of a one-step dévissage form one stage of a complete
dévissage over `r` in the sense of Stacks 05HX. -/
public def toDevissageStage (r : Ideal Γ(S, ⊤)) [r.IsPrime] (multiplicity : ℕ)
    (alpha :
      letI := D.algebraSmooth
      letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
      (Fin multiplicity →₀ Γ(D.Y, ⊤)) →ₗ[Γ(D.Y, ⊤)] Γ(D.G, ⊤))
    (fiber_bijective :
      letI := D.algebraSmooth
      letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
      letI : (Ideal.map (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) r).IsPrime := D.map_isPrime_g_appTop r
      Function.Bijective
        (alpha.baseChange (Ideal.map (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) r).ResidueField)) :
    Module.DevissageStageData.{u, u} Γ(S, ⊤) r where
  A := Γ(D.Z, ⊤)
  B := Γ(D.Y, ⊤)
  algebraRA := D.algebraClosed
  algebraRB := D.algebraSmooth
  M := Γ(D.G, ⊤)
  toLeft := D.finiteAlgHom
  multiplicity := multiplicity
  alpha := alpha
  finiteM := D.finite_sections_closedModule
  finite_toLeft := D.finite_π_appTop
  smooth := D.algebraSmooth_g_appTop
  geometricallyIrreducibleFibers := D.geometricallyIrreducible_specMap_algebraMap
  map_isPrime := D.map_isPrime_g_appTop r
  fiber_bijective := fiber_bijective

section

variable (r : Ideal Γ(S, ⊤)) [r.IsPrime] (multiplicity : ℕ)
  (alpha :
    letI := D.algebraSmooth
    letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
    (Fin multiplicity →₀ Γ(D.Y, ⊤)) →ₗ[Γ(D.Y, ⊤)] Γ(D.G, ⊤))
  (fiber_bijective :
    letI := D.algebraSmooth
    letI : Module Γ(D.Y, ⊤) Γ(D.G, ⊤) := Module.compHom Γ(D.G, ⊤) D.π.appTop.hom
    letI : (Ideal.map (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) r).IsPrime := D.map_isPrime_g_appTop r
    Function.Bijective
      (alpha.baseChange (Ideal.map (algebraMap Γ(S, ⊤) Γ(D.Y, ⊤)) r).ResidueField))

/-- The upper algebra of the stage of a one-step dévissage is the ring of functions on its
closed subscheme. -/
@[simp]
public lemma toDevissageStage_A :
    (D.toDevissageStage r multiplicity alpha fiber_bijective).A = Γ(D.Z, ⊤) := rfl

/-- The lower algebra of the stage of a one-step dévissage is the ring of functions on its
smooth scheme. -/
@[simp]
public lemma toDevissageStage_B :
    (D.toDevissageStage r multiplicity alpha fiber_bijective).B = Γ(D.Y, ⊤) := rfl

/-- The module of the stage of a one-step dévissage is the module of global sections of the
module on its closed subscheme. -/
@[simp]
public lemma toDevissageStage_M :
    (D.toDevissageStage r multiplicity alpha fiber_bijective).M = Γ(D.G, ⊤) := rfl

/-- The map of the stage of a one-step dévissage is the finite morphism on functions. -/
@[simp]
public lemma toDevissageStage_toLeft :
    (D.toDevissageStage r multiplicity alpha fiber_bijective).toLeft = D.finiteAlgHom := rfl

end

/-- The sections of a direct image over the whole space, as a module over the ring of functions
downstairs, are the sections of the original module with scalars restricted along the morphism.
Both module structures are the restriction of scalars, so the equivalence is the identity; it
exists to launder the two spellings, the one `AlgebraicGeometry.Scheme.Modules` produces for a
direct image and the `Module.compHom` one `Module.CompleteDevissage` is stated in. -/
public def pushforwardSectionsEquiv {Y Z : Scheme.{u}} (π : Z ⟶ Y) (G : Z.Modules) :
    letI : Module Γ(Y, (⊤ : Y.Opens)) Γ(G, (⊤ : Z.Opens)) :=
      Module.compHom Γ(G, (⊤ : Z.Opens)) π.appTop.hom
    Γ((Scheme.Modules.pushforward π).obj G, (⊤ : Y.Opens)) ≃ₗ[Γ(Y, (⊤ : Y.Opens))]
      Γ(G, (⊤ : Z.Opens)) :=
  letI : Module Γ(Y, (⊤ : Y.Opens)) Γ(G, (⊤ : Z.Opens)) :=
    Module.compHom Γ(G, (⊤ : Z.Opens)) π.appTop.hom
  { toFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end AlgebraicGeometry.OneStepDevissage

namespace AlgebraicGeometry.DevissageStage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

/-- **The map of modules induced by the free map of a stage of a complete dévissage.**

A stage records its free map as a morphism `𝒪_Y^{⊕ rank} ⟶ π_* 𝒢` of sheaves of modules. Its
global sections are a `Γ(Y, ⊤)`-linear map out of the free module on `Fin rank`, by the
computation `AlgebraicGeometry.freeSectionsEquiv` of the sections of a free module on an affine
scheme, and into the sections of `𝒢` with scalars restricted along `π`. This is the map `α` of
`Module.DevissageStageData`, in the shape
`AlgebraicGeometry.OneStepDevissage.toDevissageStage` takes it. -/
public def sectionsAlpha (stage : DevissageStage f F s) :
    letI : Module Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens))
        Γ(stage.oneStep.G, (⊤ : stage.oneStep.Z.Opens)) :=
      Module.compHom Γ(stage.oneStep.G, (⊤ : stage.oneStep.Z.Opens))
        stage.oneStep.π.appTop.hom
    (Fin stage.rank →₀ Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens)))
      →ₗ[Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens))]
      Γ(stage.oneStep.G, (⊤ : stage.oneStep.Z.Opens)) :=
  haveI := stage.oneStep.affine_Y
  letI : Module Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens))
      Γ(stage.oneStep.G, (⊤ : stage.oneStep.Z.Opens)) :=
    Module.compHom Γ(stage.oneStep.G, (⊤ : stage.oneStep.Z.Opens)) stage.oneStep.π.appTop.hom
  (OneStepDevissage.pushforwardSectionsEquiv stage.oneStep.π
        stage.oneStep.G).toLinearMap ∘ₗ
    Scheme.Modules.sectionsLinearMap stage.alpha ⊤ ∘ₗ
      (freeSectionsEquiv stage.oneStep.Y (ULift.{u} (Fin stage.rank))).symm.toLinearMap ∘ₗ
      (Finsupp.domLCongr (R := Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens)))
        (Equiv.ulift.{u, 0} (α := Fin stage.rank)).symm).toLinearMap

end AlgebraicGeometry.DevissageStage

namespace AlgebraicGeometry

/-- **The prime of `Γ(Y, ⊤)` corresponding to a generic point of the fibre of `g` over `s` is the
extension `rΓ(Y, ⊤)` of the prime `r` corresponding to `s`.**

This is the scheme-theoretic reading of `Ideal.eq_map_of_mem_fiber_of_fiber_le`: the canonical
isomorphism `Y ≅ Spec Γ(Y, ⊤)` carries the fibre of `g` over `s` to the fibre of
`Spec Γ(Y, ⊤) → Spec Γ(S, ⊤)` over `r`, and specializations to containments of primes. -/
public theorem asIdeal_isoSpec_hom_fiberι_eq_map {Y S : Scheme.{u}} (g : Y ⟶ S) [IsAffine Y]
    [IsAffine S] (s : S) (ξ : g.fiber s) (hξ : IsGenericPoint ξ Set.univ)
    (r : Ideal Γ(S, (⊤ : S.Opens))) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r)
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))]
    (halg : algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) = (g.appTop).hom)
    [Algebra.Smooth Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)))))] :
    (Y.isoSpec.hom (g.fiberι s ξ)).asIdeal =
      Ideal.map (algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))) r := by
  have hnat : ∀ y : Y, PrimeSpectrum.comap
      (algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))) (Y.isoSpec.hom y) =
      S.isoSpec.hom (g y) := by
    intro y
    rw [halg]
    show Spec.map g.appTop (Y.isoSpec.hom y) = _
    rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality g, Scheme.Hom.comp_apply]
  have hfib : ∀ ξ' : g.fiber s, g (g.fiberι s ξ') = s := by
    intro ξ'
    have h : g.fiberι s ξ' ∈ g ⁻¹' {s} := (g.range_fiberι s) ▸ Set.mem_range_self ξ'
    simpa using h
  have hs : S.isoSpec.hom s = ⟨r, ‹_›⟩ := PrimeSpectrum.ext hr
  refine Ideal.eq_map_of_mem_fiber_of_fiber_le Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) r
    (Y.isoSpec.hom (g.fiberι s ξ)) ?_ ?_
  · rw [hnat, hfib, hs]
  · intro q' hq'
    have hhom : Y.isoSpec.hom (Y.isoSpec.inv q') = q' :=
      (Scheme.homeoOfIso Y.isoSpec).apply_symm_apply q'
    have hgy : g (Y.isoSpec.inv q') = s := by
      refine (Scheme.homeoOfIso S.isoSpec).injective ?_
      show S.isoSpec.hom _ = S.isoSpec.hom s
      rw [← hnat, hhom, hq', hs]
    obtain ⟨ξ', hξ'⟩ : Y.isoSpec.inv q' ∈ Set.range (g.fiberι s) := by
      rw [g.range_fiberι s]
      exact hgy
    have hsp : ξ ⤳ ξ' := specializes_iff_mem_closure.2 (hξ ▸ Set.mem_univ ξ')
    have hsp2 : (Y.isoSpec.hom (g.fiberι s ξ)) ⤳ (Y.isoSpec.hom (g.fiberι s ξ')) :=
      (hsp.map (g.fiberι s).continuous).map Y.isoSpec.hom.continuous
    rw [hξ', hhom] at hsp2
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 hsp2)

namespace DevissageStage

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

/-- **The generic-fibre condition of a stage is the bijectivity condition of an algebraic
stage.** The map of modules induced by the free map of a stage of a complete dévissage becomes
bijective after base change to the residue field of the extended prime `rΓ(Y, ⊤)`.

This is the last of the twelve items of Stacks 05HX for the stage
`AlgebraicGeometry.OneStepDevissage.toDevissageStage` builds, and the shape in which that
definition takes it. -/
public theorem fiber_bijective_sectionsAlpha [IsAffine S] (stage : DevissageStage f F s)
    (r : Ideal Γ(S, ⊤)) [r.IsPrime] (hr : (S.isoSpec.hom s).asIdeal = r) :
    letI := stage.oneStep.algebraSmooth
    letI : Module Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.G, ⊤) :=
      Module.compHom Γ(stage.oneStep.G, ⊤) stage.oneStep.π.appTop.hom
    letI : (Ideal.map (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)) r).IsPrime :=
      stage.oneStep.map_isPrime_g_appTop r
    Function.Bijective (stage.sectionsAlpha.baseChange
      (Ideal.map (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)) r).ResidueField) := by
  let _ := stage.oneStep.algebraSmooth
  let _ : Module Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.G, ⊤) :=
    Module.compHom Γ(stage.oneStep.G, ⊤) stage.oneStep.π.appTop.hom
  have _ : (Ideal.map (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)) r).IsPrime :=
    stage.oneStep.map_isPrime_g_appTop r
  have hY : IsAffine stage.oneStep.Y := stage.oneStep.affine_Y
  have hZ : IsAffine stage.oneStep.Z := stage.oneStep.affine_Z
  have hfin : IsFinite stage.oneStep.π := stage.oneStep.finite
  have hqG : stage.oneStep.G.IsQuasicoherent := stage.oneStep.quasi_coherent_G
  have := Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
    stage.oneStep.π stage.oneStep.G
  have hsm : Algebra.Smooth Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤) :=
    stage.oneStep.algebraSmooth_g_appTop
  have hgi : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)))) :=
    stage.oneStep.geometricallyIrreducible_specMap_algebraMap
  have hp := asIdeal_isoSpec_hom_fiberι_eq_map stage.oneStep.g s stage.genericPoint
    stage.genericPoint_spec r hr (RingHom.algebraMap_toAlgebra _)
  have hbase := bijective_baseChange_sectionsLinearMap_of_isIso_pullback stage.alpha
    (stage.oneStep.g.fiberι s stage.genericPoint)
    (Ideal.map (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)) r) hp stage.genericFiber_isIso
  refine LinearMap.bijective_baseChange_comp _ _ _
    (((Finsupp.domLCongr (R := Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens)))
        (Equiv.ulift.{u, 0} (α := Fin stage.rank)).symm).trans
      (freeSectionsEquiv stage.oneStep.Y (ULift.{u} (Fin stage.rank))).symm))
    (OneStepDevissage.pushforwardSectionsEquiv stage.oneStep.π stage.oneStep.G) ?_ hbase
  rfl

/-- The free module of a stage, as an object of the category of modules on the smooth scheme.
Instance synthesis does not unfold `AlgebraicGeometry.Scheme.Modules`, so the sections of the
free module are only recognised as a module when the free sheaf is read in `Y.Modules`; see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Modules/FreeSections.lean`. -/
public abbrev freeModule (stage : DevissageStage f F s) : stage.oneStep.Y.Modules :=
  Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank))

/-- The identification of the source of `AlgebraicGeometry.DevissageStage.sectionsAlpha` with the
global sections of the free module of the stage. -/
public def sectionsAlphaSourceEquiv (stage : DevissageStage f F s) :
    letI := stage.oneStep.affine_Y
    (Fin stage.rank →₀ Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens)))
      ≃ₗ[Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens))]
      Γ(stage.freeModule, (⊤ : stage.oneStep.Y.Opens)) :=
  letI := stage.oneStep.affine_Y
  (Finsupp.domLCongr (R := Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens)))
      (Equiv.ulift.{u, 0} (α := Fin stage.rank)).symm).trans
    (freeSectionsEquiv stage.oneStep.Y (ULift.{u} (Fin stage.rank))).symm

/-- The map of modules of a stage is the map on global sections of its free map, read through
`AlgebraicGeometry.DevissageStage.sectionsAlphaSourceEquiv`. -/
public lemma sectionsAlpha_apply (stage : DevissageStage f F s)
    (a : Fin stage.rank →₀ Γ(stage.oneStep.Y, (⊤ : stage.oneStep.Y.Opens))) :
    letI := stage.oneStep.affine_Y
    stage.sectionsAlpha a =
      Scheme.Modules.sectionsLinearMap (M := stage.freeModule) stage.alpha ⊤
        (stage.sectionsAlphaSourceEquiv a) := rfl

/-- The image of `AlgebraicGeometry.DevissageStage.sectionsAlpha` is the image of the map on
global sections of the free map, the identification of the sources being bijective. -/
public lemma map_range_sectionsLinearMap (stage : DevissageStage f F s) :
    letI := stage.oneStep.affine_Y
    letI := stage.oneStep.algebraSmooth
    letI : Module Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.G, ⊤) :=
      Module.compHom Γ(stage.oneStep.G, ⊤) stage.oneStep.π.appTop.hom
    Submodule.map
        (OneStepDevissage.pushforwardSectionsEquiv stage.oneStep.π
          stage.oneStep.G).toLinearMap
        (LinearMap.range (Scheme.Modules.sectionsLinearMap (M := stage.freeModule) stage.alpha
          (⊤ : stage.oneStep.Y.Opens))) =
      LinearMap.range stage.sectionsAlpha := by
  let _ := stage.oneStep.affine_Y
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨stage.sectionsAlphaSourceEquiv.symm b, ?_⟩
    rw [stage.sectionsAlpha_apply, LinearEquiv.apply_symm_apply]
    rfl
  · rintro x ⟨a, rfl⟩
    exact ⟨_, ⟨stage.sectionsAlphaSourceEquiv a, rfl⟩, rfl⟩

/-- **The vanishing of the cokernel of a final stage is surjectivity of its map of modules.**
This is the field `Module.CompleteDevissage.final_surjective` for the stage
`AlgebraicGeometry.OneStepDevissage.toDevissageStage` builds. -/
public lemma surjective_sectionsAlpha_of_isZero (stage : DevissageStage f F s)
    (h : Limits.IsZero stage.coker) :
    letI := stage.oneStep.algebraSmooth
    letI : Module Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.G, ⊤) :=
      Module.compHom Γ(stage.oneStep.G, ⊤) stage.oneStep.π.appTop.hom
    Function.Surjective stage.sectionsAlpha := by
  let _ := stage.oneStep.affine_Y
  let _ := stage.oneStep.affine_Z
  let _ := stage.oneStep.finite
  let _ := stage.oneStep.quasi_coherent_G
  have hepi : @Epi stage.oneStep.Y.Modules _ stage.freeModule _ stage.alpha :=
    Abelian.epi_of_cokernel_π_eq_zero _ (h.eq_of_tgt _ _)
  have := Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
    stage.oneStep.π stage.oneStep.G
  have hsurj := @surjective_sectionsLinearMap_of_epi _ _ stage.freeModule _ _ _ stage.alpha hepi
  intro y
  obtain ⟨b, hb⟩ := hsurj y
  refine ⟨stage.sectionsAlphaSourceEquiv.symm b, ?_⟩
  rw [stage.sectionsAlpha_apply, LinearEquiv.apply_symm_apply]
  exact hb

/-- **The cokernel of the map of modules of a stage is the module of global sections of the
cokernel of its free map.** This is the field `Module.CompleteDevissage.cokerEquiv` for the stage
`AlgebraicGeometry.OneStepDevissage.toDevissageStage` builds, and identifies the module the next
algebraic stage dévisses with the module the next geometric stage dévisses. -/
public def cokerSectionsEquiv (stage : DevissageStage f F s) :
    letI := stage.oneStep.affine_Y
    letI := stage.oneStep.algebraSmooth
    letI : Module Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.G, ⊤) :=
      Module.compHom Γ(stage.oneStep.G, ⊤) stage.oneStep.π.appTop.hom
    (Γ(stage.oneStep.G, (⊤ : stage.oneStep.Z.Opens)) ⧸ LinearMap.range stage.sectionsAlpha)
      ≃ₗ[Γ(stage.oneStep.Y, ⊤)] Γ(stage.coker, (⊤ : stage.oneStep.Y.Opens)) :=
  letI := stage.oneStep.affine_Y
  letI := stage.oneStep.affine_Z
  letI := stage.oneStep.finite
  letI := stage.oneStep.quasi_coherent_G
  letI := stage.oneStep.algebraSmooth
  letI : Module Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.G, ⊤) :=
    Module.compHom Γ(stage.oneStep.G, ⊤) stage.oneStep.π.appTop.hom
  letI : ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom _ _
  (Submodule.Quotient.equiv _ _
      (OneStepDevissage.pushforwardSectionsEquiv stage.oneStep.π stage.oneStep.G)
      stage.map_range_sectionsLinearMap).symm.trans
    (sectionsCokernelEquiv (M := stage.freeModule) stage.alpha)

end DevissageStage

end AlgebraicGeometry

end
