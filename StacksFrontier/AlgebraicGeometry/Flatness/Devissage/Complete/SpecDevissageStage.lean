module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraDictionary
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ModelOverField
public import StacksFrontier.RingTheory.Flat.DevissageLength

/-!
# The one-step dévissage on spectra attached to an algebraic stage

Let `N/S/R` be a finite module over a finite-type `R`-algebra and let `r` be a prime of `R`. One
stage of an algebraic complete dévissage of `N/S/R` over `r` in the sense of Stacks 05HX is a
`Module.DevissageStage R S N r`: a pair of `R`-algebras `A` and `B`, a finite `A`-module `M`
identified with `N` along a surjection `S → A` of finite presentation, a finite map `B → A`, a
smooth `R`-algebra `B` with geometrically irreducible fibres, and a map `α : Bᵐ → M` of
`B`-modules which becomes bijective over the residue field of `rB`.

Applying `Spec` to that datum produces the geometric stage of Stacks 05H4 and 05I0: the
one-step dévissage of `Ñ` along `Spec S → Spec R` over `r` whose closed subscheme is `Spec A`,
whose smooth scheme is `Spec B`, whose module is `M̃`, and whose free map is `α̃`. This is the
direction converse to
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/AlgebraDictionary.lean`, which reads a
geometric stage on an arbitrary affine base as an algebraic one.

The only field of the geometric notion not determined by the algebraic one is the dimension
condition `AlgebraicGeometry.OneStepDevissage.fiber_dimension`, which compares the dimension of
every fibre of `Spec B → Spec R` with the dimension of the support of `Ñ` on the fibre over `r`;
it is taken as the hypothesis `hdim`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberGenericPoint`: the generic point of the fibre of a morphism
  with geometrically irreducible fibres.
* `Module.DevissageStage.toOneStepDevissage`: the one-step dévissage of `Ñ/Spec S/Spec R` over
  `r` attached to one stage of an algebraic complete dévissage.
* `Module.DevissageStage.toGeometricStage`: the same datum together with its free map and the
  generic-fibre isomorphism, i.e. a stage of a geometric complete dévissage.

## Main results

* `AlgebraicGeometry.asIdeal_fiberι_eq_map`: the generic point of the fibre of `Spec B → Spec R`
  over `q` is the prime `qB`.
* `AlgebraicGeometry.isIso_pullback_map_tilde_comp`: a map of modules on `Spec B` presented as
  the associated sheaf of a map of modules, up to an isomorphism on each side, becomes invertible
  over the residue field of a prime at which the base change of that map of modules is bijective.
* `Module.DevissageStage.toOneStepDevissage_Z`,
  `Module.DevissageStage.toOneStepDevissage_Y`,
  `Module.DevissageStage.toOneStepDevissage_i`,
  `Module.DevissageStage.toOneStepDevissage_π`,
  `Module.DevissageStage.toOneStepDevissage_g` and
  `Module.DevissageStage.toOneStepDevissage_G`: the two schemes, the three morphisms and the
  module of the one-step dévissage are the spectra of `A` and `B`, the spectra of the three ring
  maps of the stage, and the associated sheaf of `M`.
* `Module.DevissageStage.toGeometricStage_oneStep` and
  `Module.DevissageStage.toGeometricStage_rank`: the underlying one-step dévissage of the
  geometric stage is the one above, and its rank is the multiplicity of the algebraic stage.

## Implementation notes

That `Spec` of a finitely generated algebra is locally of finite type over the base is
`AlgebraicGeometry.locallyOfFiniteType_specMap_algebraMap`, a theorem and not an instance; it is
made a local instance here, because the statement of a one-step dévissage of `Ñ` along
`Spec S → Spec R` carries that hypothesis.

The commuting triangle `AlgebraicGeometry.OneStepDevissage.over_base` is `Spec` of the equality
of ring maps `A₀ ∘ (R → S) = (B → A) ∘ (R → B)`, both sides being the structure map
`R → A`. Each of the remaining conditions is the image under `Spec` of the corresponding
condition on rings, through `AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`,
`AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff`,
`AlgebraicGeometry.IsFinite.SpecMap_iff` and `Stacks.MoreMorphisms.smooth_specMap`; quasi-
compactness and quasi-separatedness, the two conditions of
`AlgebraicGeometry.FinitePresentation` besides being locally of finite presentation, hold on a
morphism of affine schemes.

The identification of the module, `AlgebraicGeometry.OneStepDevissage.module_iso`, and the free
map of the stage are both built from `AlgebraicGeometry.pushforwardTildeIso`, the comparison of
the direct image of an associated sheaf with the associated sheaf of the restriction of scalars:
the first composes it with the associated sheaf of `Module.DevissageStage.initialEquiv`, and the
second with the associated sheaf of `Module.DevissageStage.alpha` and with
`AlgebraicGeometry.tildeFinsupp`, which identifies the associated sheaf of a finite free module
with the free module of sheaves. The index type of the latter is `ULift (Fin multiplicity)`,
since `AlgebraicGeometry.SheafOfModules.free` takes its index type in the universe of the sheaf
of rings, and `Finsupp.domLCongr` removes the `ULift`.

Because the two outer factors of the free map are isomorphisms, the generic-fibre condition
reduces to the middle one, and there it is `AlgebraicGeometry.isIso_pullback_map_tilde`. That
reduction needs the generic point of the fibre of `Spec B → Spec R` over `r` to be the point
`rB`, which is `AlgebraicGeometry.asIdeal_fiberι_eq_map`, a restatement of
`Ideal.eq_map_of_mem_fiber_of_fiber_le` for the scheme-theoretic fibre; and it needs the
bijectivity hypothesis `Module.DevissageStage.fiber_bijective`, phrased with
`LinearMap.baseChange`, in the form `LinearMap.rTensor` that
`AlgebraicGeometry.isIso_pullback_map_tilde` asks for, which is `LinearMap.baseChange_eq_lTensor`
followed by `LinearMap.lTensor_bij_iff_rTensor_bij`.

The distinguished point of the stage is `AlgebraicGeometry.Scheme.Hom.fiberGenericPoint`, the
generic point of the fibre, which exists because the fibre of a morphism with geometrically
irreducible fibres is an irreducible space and a scheme is a sober space. It is formed for the
morphism `Spec B → Spec R` itself rather than for the morphism `g` of the one-step dévissage
constructed from the stage: the two are the same morphism, but the irreducibility of the fibre is
only found by instance synthesis for the first spelling.

## References

* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.locallyOfFiniteType_specMap_algebraMap

namespace AlgebraicGeometry

/-- **The generic point of the fibre of a morphism with geometrically irreducible fibres.** The
fibre is an irreducible space, and a scheme is a sober space, so it has a generic point. -/
public def Scheme.Hom.fiberGenericPoint {X T : Scheme.{u}} (f : X ⟶ T)
    [GeometricallyIrreducible f] (t : T) : f.fiber t := genericPoint _

/-- The fibre of a morphism with geometrically irreducible fibres is the closure of its generic
point. -/
public theorem Scheme.Hom.isGenericPoint_fiberGenericPoint {X T : Scheme.{u}} (f : X ⟶ T)
    [GeometricallyIrreducible f] (t : T) :
    IsGenericPoint (f.fiberGenericPoint t) Set.univ := genericPoint_spec _

/-- **The prime of `B` at a generic point of the fibre of `Spec B → Spec R` over a prime `q` is
the extension `qB`**, for `R → B` smooth with geometrically irreducible fibres.

This is `Ideal.eq_map_of_mem_fiber_of_fiber_le` read on the scheme-theoretic fibre: a point of the
fibre contracts to `q`, and a point of `Spec B` contracting to `q` lies in the fibre, so it is a
specialization of the generic point and its prime is the larger one. -/
public theorem asIdeal_fiberι_eq_map (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap A B)))] (q : Ideal A)
    [q.IsPrime]
    (ξ : (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
      (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A)))
    (hξ : IsGenericPoint ξ Set.univ) :
    ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι
        (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A)) ξ).asIdeal =
      Ideal.map (algebraMap A B) q := by
  have hmem : ∀ ξ' : (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
      (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A)),
      PrimeSpectrum.comap (algebraMap A B)
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι
          (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A)) ξ') = ⟨q, ‹q.IsPrime›⟩ := by
    intro ξ'
    have h := ((Spec.map (CommRingCat.ofHom (algebraMap A B))).range_fiberι
      (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A))) ▸ Set.mem_range_self ξ'
    exact (Spec.map_apply _ _).symm.trans (Set.mem_singleton_iff.mp h)
  refine Ideal.eq_map_of_mem_fiber_of_fiber_le A B q _ (hmem ξ) ?_
  intro q' hq'
  have hq'mem : (show ↥(Spec (CommRingCat.of B)) from q') ∈
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹'
        {(⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A))} :=
    (Spec.map_apply _ _).trans hq'
  have hξ' := Scheme.Hom.fiberι_fiberHomeo_symm (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A)) ⟨_, hq'mem⟩
  set ξ' := ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberHomeo
    (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A))).symm ⟨_, hq'mem⟩
  have hsp : ξ ⤳ ξ' := specializes_iff_mem_closure.2 (hξ ▸ Set.mem_univ ξ')
  have hsp2 := hsp.map ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι
    (⟨q, ‹q.IsPrime›⟩ : Spec (CommRingCat.of A))).continuous
  rw [hξ'] at hsp2
  exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 hsp2)

/-- **A map of modules on `Spec B` presented as the associated sheaf of a map `φ` of `B`-modules,
up to an isomorphism on each side, becomes invertible after pullback to the spectrum of the
residue field of a point `y` as soon as the base change of `φ` to that residue field is
bijective.**

Pullback along the map from the spectrum of the residue field factors through the spectrum of the
residue field of the prime of `y`, where `AlgebraicGeometry.isIso_pullback_map_tilde` applies to
the middle factor; the two outer factors are isomorphisms, and a functor carries isomorphisms to
isomorphisms. -/
public theorem isIso_pullback_map_tilde_comp {B : Type u} [CommRing B]
    {M N : ModuleCat.{u} (CommRingCat.of B)} (φ : M ⟶ N)
    {ℳ 𝒩 : (Spec (CommRingCat.of B)).Modules}
    (eM : ℳ ≅ (tilde.functor (CommRingCat.of B)).obj M)
    (eN : (tilde.functor (CommRingCat.of B)).obj N ≅ 𝒩)
    (y : Spec (CommRingCat.of B)) (p : Ideal B) [p.IsPrime] (hy : y.asIdeal = p)
    (hbij : Function.Bijective (φ.hom.baseChange p.ResidueField)) :
    IsIso ((Scheme.Modules.pullback ((Spec (CommRingCat.of B)).fromSpecResidueField y)).map
      (eM.hom ≫ (tilde.functor (CommRingCat.of B)).map φ ≫ eN.hom)) := by
  subst hy
  have hcomp : ∀ {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) {P Q : X₃.Modules}
      (α : P ⟶ Q), IsIso ((Scheme.Modules.pullback b).map α) →
      IsIso ((Scheme.Modules.pullback (a ≫ b)).map α) := by
    intro X₁ X₂ X₃ a b P Q α h
    exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp a b) α).mp
      (let := h; Functor.map_isIso (Scheme.Modules.pullback a) _)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  refine hcomp _ _ _ ?_
  set P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap ↥(CommRingCat.of B) y.asIdeal.ResidueField))) with hP
  rw [P.map_comp, P.map_comp]
  have h3 : IsIso (P.map ((tilde.functor (CommRingCat.of B)).map φ)) := by
    rw [hP]
    refine isIso_pullback_map_tilde B y.asIdeal.ResidueField
      (algebraMap ↥(CommRingCat.of B) y.asIdeal.ResidueField) M N φ ?_
    have hm : @Algebra.toModule ↥(CommRingCat.of B) y.asIdeal.ResidueField _ _
        (algebraMap ↥(CommRingCat.of B) y.asIdeal.ResidueField).toAlgebra =
        (inferInstance : Module ↥(CommRingCat.of B) y.asIdeal.ResidueField) :=
      Module.ext' _ _ fun b x => (Algebra.smul_def b x).symm
    rw [hm]
    rw [LinearMap.baseChange_eq_lTensor] at hbij
    exact (LinearMap.lTensor_bij_iff_rTensor_bij _ φ.hom).1 hbij
  infer_instance

end AlgebraicGeometry

namespace Module.DevissageStage

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime]

/-- **The one-step dévissage on spectra attached to one stage of an algebraic complete
dévissage.** The closed subscheme is `Spec A`, the smooth scheme is `Spec B`, the three morphisms
are the spectra of the three ring maps of the stage, and the module on the closed subscheme is
the sheaf associated with `M`.

The dimension of the fibres of `Spec B → Spec R`, which the algebraic datum does not record, is
the hypothesis `hdim`. -/
public def toOneStepDevissage (st : Module.DevissageStage R S N r)
    (hdim : ∀ t : Spec (CommRingCat.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R st.B))).fiber t) =
        topologicalKrullDim (SheafOfModules.supp
          ((Scheme.Modules.pullback
            ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
              (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
            (tilde (ModuleCat.of (CommRingCat.of S) N))))) :
    AlgebraicGeometry.OneStepDevissage
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (tilde (ModuleCat.of (CommRingCat.of S) N))
      (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)) where
  Z := Spec (CommRingCat.of st.A)
  Y := Spec (CommRingCat.of st.B)
  i := Spec.map (CommRingCat.ofHom st.toA₀.toRingHom)
  π := Spec.map (CommRingCat.ofHom st.toLeft.toRingHom)
  g := Spec.map (CommRingCat.ofHom (algebraMap R st.B))
  G := tilde (ModuleCat.of (CommRingCat.of st.A) st.M)
  quasi_coherent_G := inferInstance
  finite_type_G := inferInstance
  over_base := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (Spec.map ∘ CommRingCat.ofHom)
      (st.toA₀.comp_algebraMap.trans st.toLeft.comp_algebraMap.symm)
  affine_X := inferInstance
  affine_S := inferInstance
  affine_Z := inferInstance
  affine_Y := inferInstance
  closed_immersion := IsClosedImmersion.spec_of_surjective _ st.initial_surjective
  finite_presentation :=
    ⟨(LocallyOfFinitePresentation.SpecMap_iff _).mpr st.initial_finitePresentation,
      inferInstance, inferInstance⟩
  module_iso :=
    (tilde.functor (CommRingCat.of S)).mapIso st.initialEquiv.toModuleIso ≪≫
      ((AlgebraicGeometry.pushforwardTildeIso (CommRingCat.of S) (CommRingCat.of st.A)
        (CommRingCat.ofHom st.toA₀.toRingHom)).app
          (ModuleCat.of (CommRingCat.of st.A) st.M)).symm
  finite := (IsFinite.SpecMap_iff _).mpr st.left_finite
  smooth := Stacks.MoreMorphisms.smooth_specMap _ (RingHom.smooth_algebraMap.mpr st.smooth)
  geometrically_irreducible := st.geometricallyIrreducibleFibers
  fiber_dimension := hdim

/-- The closed subscheme of the one-step dévissage of a stage is the spectrum of the upper
algebra. -/
@[simp]
public theorem toOneStepDevissage_Z (st : Module.DevissageStage R S N r) (hdim) :
    (st.toOneStepDevissage hdim).Z = Spec (CommRingCat.of st.A) := rfl

/-- The smooth scheme of the one-step dévissage of a stage is the spectrum of the lower
algebra. -/
@[simp]
public theorem toOneStepDevissage_Y (st : Module.DevissageStage R S N r) (hdim) :
    (st.toOneStepDevissage hdim).Y = Spec (CommRingCat.of st.B) := rfl

/-- The closed immersion of the one-step dévissage of a stage is the spectrum of the surjection
from `S`. -/
@[simp]
public theorem toOneStepDevissage_i (st : Module.DevissageStage R S N r) (hdim) :
    (st.toOneStepDevissage hdim).i = Spec.map (CommRingCat.ofHom st.toA₀.toRingHom) := rfl

/-- The finite morphism of the one-step dévissage of a stage is the spectrum of the finite map
from the lower algebra. -/
@[simp]
public theorem toOneStepDevissage_π (st : Module.DevissageStage R S N r) (hdim) :
    (st.toOneStepDevissage hdim).π = Spec.map (CommRingCat.ofHom st.toLeft.toRingHom) := rfl

/-- The smooth structure morphism of the one-step dévissage of a stage is the spectrum of the
structure map of the lower algebra. -/
@[simp]
public theorem toOneStepDevissage_g (st : Module.DevissageStage R S N r) (hdim) :
    (st.toOneStepDevissage hdim).g = Spec.map (CommRingCat.ofHom (algebraMap R st.B)) := rfl

/-- The module of the one-step dévissage of a stage is the sheaf associated with the module of
the stage. -/
@[simp]
public theorem toOneStepDevissage_G (st : Module.DevissageStage R S N r) (hdim) :
    (st.toOneStepDevissage hdim).G = tilde (ModuleCat.of (CommRingCat.of st.A) st.M) := rfl

/-- **The geometric stage of a complete dévissage attached to one stage of an algebraic complete
dévissage.** Its one-step dévissage is `Module.DevissageStage.toOneStepDevissage`, its rank is
the multiplicity of the stage, its free map is the sheaf associated with the map `α` of the
stage, and its distinguished point is the generic point of the fibre of `Spec B → Spec R` over
`r`, namely the point `rB`. -/
public def toGeometricStage (st : Module.DevissageStage R S N r)
    (hdim : ∀ t : Spec (CommRingCat.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R st.B))).fiber t) =
        topologicalKrullDim (SheafOfModules.supp
          ((Scheme.Modules.pullback
            ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
              (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
            (tilde (ModuleCat.of (CommRingCat.of S) N))))) :
    AlgebraicGeometry.DevissageStage
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (tilde (ModuleCat.of (CommRingCat.of S) N))
      (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)) where
  oneStep := st.toOneStepDevissage hdim
  rank := st.multiplicity
  alpha :=
    (AlgebraicGeometry.tildeFinsupp (R := CommRingCat.of st.B)
        (ULift.{u} (Fin st.multiplicity))).symm.hom ≫
      (tilde.functor (CommRingCat.of st.B)).map
          (ModuleCat.ofHom (st.alpha ∘ₗ (Finsupp.domLCongr (M := st.B) (R := st.B)
            (Equiv.ulift.{u, 0} (α := Fin st.multiplicity))).toLinearMap)) ≫
        ((AlgebraicGeometry.pushforwardTildeIso (CommRingCat.of st.B) (CommRingCat.of st.A)
          (CommRingCat.ofHom st.toLeft.toRingHom)).app
            (ModuleCat.of (CommRingCat.of st.A) st.M)).symm.hom
  genericPoint := (Spec.map (CommRingCat.ofHom (algebraMap R st.B))).fiberGenericPoint
    (⟨r, inferInstance⟩ : Spec (CommRingCat.of R))
  genericPoint_spec := (Spec.map
    (CommRingCat.ofHom (algebraMap R st.B))).isGenericPoint_fiberGenericPoint
      (⟨r, inferInstance⟩ : Spec (CommRingCat.of R))
  genericFiber_isIso := by
    refine AlgebraicGeometry.isIso_pullback_map_tilde_comp _ _ _ _
      (Ideal.map (algebraMap R st.B) r) ?_ ?_
    · exact AlgebraicGeometry.asIdeal_fiberι_eq_map R st.B r _
        ((Spec.map (CommRingCat.ofHom (algebraMap R st.B))).isGenericPoint_fiberGenericPoint
          (⟨r, inferInstance⟩ : Spec (CommRingCat.of R)))
    · exact LinearMap.bijective_baseChange_comp _ st.alpha _
        (Finsupp.domLCongr (M := st.B) (R := st.B)
          (Equiv.ulift.{u, 0} (α := Fin st.multiplicity))) (LinearEquiv.refl st.B st.M) rfl
        st.fiber_bijective

/-- The one-step dévissage underlying the geometric stage of an algebraic stage. -/
@[simp]
public theorem toGeometricStage_oneStep (st : Module.DevissageStage R S N r) (hdim) :
    (st.toGeometricStage hdim).oneStep = st.toOneStepDevissage hdim := rfl

/-- The rank of the geometric stage of an algebraic stage is the multiplicity of the stage. -/
@[simp]
public theorem toGeometricStage_rank (st : Module.DevissageStage R S N r) (hdim) :
    (st.toGeometricStage hdim).rank = st.multiplicity := rfl

end Module.DevissageStage

end
