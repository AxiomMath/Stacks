module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedConormalSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceComparisonMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence.ExistenceAndTransport
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a formally unramified morphism, on its source

Let `S` be a scheme, let `Y` be an algebraic space over `S` (the base, written `B` in the source;
the letter `B` is taken here by the big fppf site) and let `h : Z ⟶ X` be a formally unramified
morphism of algebraic spaces over `Y`, with universal first order thickening
`t : AlgebraicGeometry.Space.UniversalFirstOrderThickening B S hS h` (Stacks 0607; one exists by
Stacks 0606, `AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`).  This file
states Stacks 060F for `h` itself: the sequence
```
  𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of sheaves of `𝒪_Z`-modules on the small étale site of `Z`, with `𝒞_{Z/X}` the conormal sheaf
`AlgebraicGeometry.Space.conormalSheaf` of Stacks 0607, is exact, and its first arrow is induced
by `d_{Z'/Y}`.

## Proof

`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_conormalSequence_exact` proves
the statement on the smaller space `Z₀ ⊂ Z'` of the thickening, for the morphism `ι ≫ h'`.  The
identification `σ : Z ≅ Z₀` of the thickening carries it to `Z`.  Inverse image along `σ` is a
left adjoint, so it is additive and preserves cokernels and epimorphisms; it therefore carries
the exact sequence on `Z₀`, whose second arrow is an epimorphism, to an exact sequence.
Moreover `σ^*ι^*(h')^*Ω_{X/Y}` is `h^*Ω_{X/Y}` by the comparison of Stacks 03LU and
`σ ≫ ι ≫ h' = h`; `σ^*Ω_{Z₀/Y}` is `Ω_{Z/Y}` by Stacks 04CU, since an isomorphism is étale; and
`σ^*𝒞_{Z₀/Z'}` is by definition the conormal sheaf `𝒞_{Z/X}`.

## Main results

* `AlgebraicGeometry.Space.exists_conormalSequence_exact_of_formallyUnramified`:
  **Stacks 060F**, for a formally unramified `h`.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.exists_conormalSequence_exact`: the same
  statement for any given universal first order thickening of `h`.

## References

* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leave a stuck universe constraint against the modules on the small étale sites here; the abelian
structure used is the one at the pinned universes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace UniversalFirstOrderThickening

variable {B S hS} {Z X Y : AlgebraicSpaces B S hS} {h : Z ⟶ X}
  (t : UniversalFirstOrderThickening B S hS h) (p : X ⟶ Y)

/-- The identification `σ : Z ≅ Z₀` of the source of `h` with the smaller space of its universal
first order thickening, as an isomorphism of algebraic spaces. -/
noncomputable def sourceIsoSubSpace : Z ≅ t.subSpace :=
  ObjectProperty.isoMk _ t.sourceIso

/-- `h` factors as `σ ≫ ι ≫ h'` through the universal first order thickening. -/
theorem sourceIsoSubSpace_hom_comp : (t.sourceIsoSubSpace).hom ≫
    (universalThickeningInclusion B S hS t.isUniversal ≫ t.toBase) = h :=
  ObjectProperty.hom_ext _ t.sourceIso_ι_toBase

/-- The comparison `h^*Ω_{X/Y} ≅ σ^*ι^*(h')^*Ω_{X/Y}`, from `h = σ ≫ ι ≫ h'` and the
comparison isomorphism of Stacks 03LU, applied twice. -/
noncomputable def pullbackDifferentialsIso :
    (modulePullback B S hS h).obj (sheafOfDifferentials B S hS p) ≅
      (modulePullback B S hS t.sourceIsoSubSpace.hom).obj
        ((modulePullback B S hS (universalThickeningInclusion B S hS t.isUniversal)).obj
          ((modulePullback B S hS t.toBase).obj (sheafOfDifferentials B S hS p))) :=
  eqToIso (congrArg (fun φ => (modulePullback B S hS φ).obj (sheafOfDifferentials B S hS p))
      t.sourceIsoSubSpace_hom_comp).symm ≪≫
    ((modulePullbackCompIso B S hS t.sourceIsoSubSpace.hom
      (universalThickeningInclusion B S hS t.isUniversal ≫ t.toBase)).app _).symm ≪≫
    (modulePullback B S hS t.sourceIsoSubSpace.hom).mapIso
      ((modulePullbackCompIso B S hS (universalThickeningInclusion B S hS t.isUniversal)
        t.toBase).app _).symm

instance isIso_pullbackDifferentialsMap_sourceIsoSubSpace {W : AlgebraicSpaces B S hS}
    (g : t.subSpace ⟶ W) :
    IsIso (pullbackDifferentialsMap B S hS t.sourceIsoSubSpace.hom g) :=
  have : IsIso t.sourceIsoSubSpace.hom.hom := inferInstanceAs (IsIso t.sourceIso.hom)
  isIso_pullbackDifferentialsMap_of_isEtale B S hS _
    (isEtale_of_isIso B S hS t.sourceIsoSubSpace.hom.hom) g

/-- The comparison `σ^*Ω_{Z₀/Y} ≅ Ω_{Z/Y}`: the comparison map of Stacks 04CX along the
isomorphism `σ`, which is invertible by Stacks 04CU. -/
noncomputable def differentialsIso :
    (modulePullback B S hS t.sourceIsoSubSpace.hom).obj
        (sheafOfDifferentials B S hS
          (universalThickeningInclusion B S hS t.isUniversal ≫ (t.toBase ≫ p))) ≅
      sheafOfDifferentials B S hS (h ≫ p) :=
  asIso (pullbackDifferentialsMap B S hS t.sourceIsoSubSpace.hom
      (universalThickeningInclusion B S hS t.isUniversal ≫ (t.toBase ≫ p))) ≪≫
    eqToIso (congrArg (sheafOfDifferentials B S hS) (by
      simpa only [Category.assoc] using congrArg (· ≫ p) t.sourceIsoSubSpace_hom_comp))

/-- The inverse image along `σ` of the arrow `AlgebraicGeometry.Space.thickeningConormalFirstMap`
on `Z₀`, read through
`AlgebraicGeometry.Space.UniversalFirstOrderThickening.pullbackDifferentialsIso`; its source is
`σ^*𝒞_{Z₀/Z'}`, which is `𝒞_{Z/X}` by definition. -/
noncomputable def pullbackThickeningConormalFirstMap :
    (modulePullback B S hS t.sourceIsoSubSpace.hom).obj
        (conormalModule B S hS t.ambient (thickeningClosedSubspace B S hS t.isUniversal)) ⟶
      (modulePullback B S hS h).obj (sheafOfDifferentials B S hS p) :=
  (modulePullback B S hS t.sourceIsoSubSpace.hom).map
      (thickeningConormalFirstMap B S hS t.isUniversal p
        (t.isUniversal.isIso_thickeningSheafOfDifferentialsMap B S hS p)) ≫
    (t.pullbackDifferentialsIso p).inv

/-- The first arrow `𝒞_{Z/X} ⟶ h^*Ω_{X/Y}` of the sequence of Stacks 060F, with `𝒞_{Z/X}` the
conormal sheaf of Stacks 0607: the inverse image along `σ` of the arrow
`AlgebraicGeometry.Space.thickeningConormalFirstMap` on `Z₀`, read through
`AlgebraicGeometry.Space.UniversalFirstOrderThickening.pullbackDifferentialsIso`. -/
noncomputable def conormalSequenceFirstMap :
    conormalSheaf B S hS t ⟶ (modulePullback B S hS h).obj (sheafOfDifferentials B S hS p) :=
  t.pullbackThickeningConormalFirstMap p

/-- The second arrow `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` of the sequence of Stacks 060F: the inverse image
along `σ` of the arrow `AlgebraicGeometry.Space.thickeningConormalSecondMap` on `Z₀`, read
through the comparisons on both sides. -/
noncomputable def conormalSequenceSecondMap :
    (modulePullback B S hS h).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (h ≫ p) :=
  (t.pullbackDifferentialsIso p).hom ≫
    (modulePullback B S hS t.sourceIsoSubSpace.hom).map
      (thickeningConormalSecondMap B S hS t.isUniversal p) ≫
    (t.differentialsIso p).hom

/-- Let `h : Z ⟶ X` be a morphism of algebraic spaces over `Y`, with universal first order
thickening `t` (`Z ⊂ Z'`, structure morphism
`h' : Z' ⟶ X`).  The canonical sequence
```
  𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of `𝒪_Z`-modules, with `𝒞_{Z/X}` the conormal sheaf of Stacks 0607, is exact: the composite
of the two arrows is zero, it is exact at `h^*Ω_{X/Y}`, and the second arrow is an
epimorphism.  The first arrow is induced by `d_{Z'/Y}`: followed by the isomorphism of
Stacks 060E (pulled back to `Z`) it is the inverse image along `σ : Z ≅ Z₀` of the arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` of the closed subspace `Z₀ ⊂ Z'`, whose
transpose sends a local section of the ideal of `Z₀` to its differential
(`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`). -/
theorem exists_conormalSequence_exact :
    ∃ hc : t.conormalSequenceFirstMap p ≫ t.conormalSequenceSecondMap p = 0,
      (ShortComplex.mk _ _ hc).Exact ∧ Epi (t.conormalSequenceSecondMap p) ∧
        t.conormalSequenceFirstMap p ≫ (t.pullbackDifferentialsIso p).hom ≫
            (modulePullback B S hS t.sourceIsoSubSpace.hom).map
              (thickeningSheafOfDifferentialsMap B S hS t.isUniversal p) =
          (modulePullback B S hS t.sourceIsoSubSpace.hom).map
            (AlgebraicGeometry.Space.conormalSequenceFirstMap B S hS
              (thickeningClosedSubspace B S hS t.isUniversal) (t.toBase ≫ p)) := by
  obtain ⟨hc₀, hex, hepi, hd⟩ := t.isUniversal.exists_conormalSequence_exact B S hS p
  have hleft := (modulePullbackAdjunction B S hS t.sourceIsoSubSpace.hom).isLeftAdjoint
  have hbiprod : PreservesBinaryBiproducts (modulePullback B S hS t.sourceIsoSubSpace.hom) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hadd : (modulePullback B S hS t.sourceIsoSubSpace.hom).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have hc' : t.pullbackThickeningConormalFirstMap p ≫ t.conormalSequenceSecondMap p = 0 := by
    simp only [pullbackThickeningConormalFirstMap, conormalSequenceSecondMap, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc, hc₀, Functor.map_zero, zero_comp]
  refine ⟨hc', ?_, ?_, ?_⟩
  · have hiso : ShortComplex.mk _ _ hc' ≅
        (ShortComplex.mk _ _ hc₀).map (modulePullback B S hS t.sourceIsoSubSpace.hom) :=
      ShortComplex.isoMk (Iso.refl _) (t.pullbackDifferentialsIso p) (t.differentialsIso p).symm
        (by simp [pullbackThickeningConormalFirstMap])
        (by simp [conormalSequenceSecondMap])
    exact (ShortComplex.exact_iff_of_iso hiso).2
      (hex.map_of_epi_of_preservesCokernel (modulePullback B S hS t.sourceIsoSubSpace.hom)
        hepi inferInstance)
  · have : Epi ((modulePullback B S hS t.sourceIsoSubSpace.hom).map
        (thickeningConormalSecondMap B S hS t.isUniversal p)) := inferInstance
    unfold conormalSequenceSecondMap
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' this (IsIso.epi_of_iso _))
  · change t.pullbackThickeningConormalFirstMap p ≫ _ = _
    simp only [pullbackThickeningConormalFirstMap, Category.assoc, Iso.inv_hom_id_assoc,
      ← Functor.map_comp, hd]

end UniversalFirstOrderThickening

/-- **Stacks 060F.**  Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces
over `Y` (the base `B` of the source), and let `Z ⊂ Z'` be the universal first order
neighbourhood of `Z` over `X` (it exists by Stacks 0606), with structure morphism `h' : Z' ⟶ X`.
There is a canonical exact sequence
```
  𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0
```
of `𝒪_Z`-modules, with `𝒞_{Z/X}` the conormal sheaf of Stacks 0607: the composite of the two
arrows is zero, the sequence is exact at `h^*Ω_{X/Y}`, and the second arrow is an epimorphism.
The first arrow is induced by `d_{Z'/Y}`: followed by the isomorphism `h^*Ω_{X/Y} ≅ Ω_{Z'/Y} ⊗ 𝒪_Z`
of Stacks 060E it is the inverse image along `Z ≅ Z₀` of the arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` of the closed subspace `Z₀ ⊂ Z'`, whose
transpose sends a local section of the ideal of `Z₀` to its differential
(`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply`).  The statement
for any given universal first order neighbourhood is
`AlgebraicGeometry.Space.UniversalFirstOrderThickening.exists_conormalSequence_exact`. -/
@[stacks 060F]
theorem exists_conormalSequence_exact_of_formallyUnramified {Z X Y : AlgebraicSpaces B S hS}
    (h : Z ⟶ X) (hh : FormallyUnramified h.hom) (p : X ⟶ Y) :
    ∃ t : UniversalFirstOrderThickening B S hS h,
      ∃ hc : t.conormalSequenceFirstMap p ≫ t.conormalSequenceSecondMap p = 0,
        (ShortComplex.mk _ _ hc).Exact ∧ Epi (t.conormalSequenceSecondMap p) ∧
          t.conormalSequenceFirstMap p ≫ (t.pullbackDifferentialsIso p).hom ≫
              (modulePullback B S hS t.sourceIsoSubSpace.hom).map
                (thickeningSheafOfDifferentialsMap B S hS t.isUniversal p) =
            (modulePullback B S hS t.sourceIsoSubSpace.hom).map
              (conormalSequenceFirstMap B S hS
                (thickeningClosedSubspace B S hS t.isUniversal) (t.toBase ≫ p)) := by
  obtain ⟨t⟩ := nonempty_universalFirstOrderThickening B S hS h hh
  exact ⟨t, t.exists_conormalSequence_exact p⟩

end AlgebraicGeometry.Space

end
