module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceEpiImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness at the middle term of the conormal sequence of Stacks 05ZA

Let `Z ⊆ X` be a closed subspace of an algebraic space over `B` with structure morphism
`b : X ⟶ B`, and let `i` be a morphism with target `X` whose structure map has the defining ideal
sheaf of `Z` for its kernel.  Stacks 05ZA attaches to this datum the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleDescent.lean` constructs, for every
morphism `θ : i^*Ω_{X/B} ⟶ W` annihilating the first arrow, a morphism
`AlgebraicGeometry.Space.conormalSequenceMiddleDesc : Ω_{Z/B} ⟶ W`, and leaves open the single
identity which says that morphism factors `θ`.

**This file closes that identity and deduces exactness at the middle term.**

## Main results

* `AlgebraicGeometry.Space.pushforwardUniversalDerivation_eq_descent`: **the identity.**  The
  `B`-derivation `i_*d_{Z/B} ∘ i♯` of Stacks 04CX *is* the restriction along `i♯` of the
  transpose of `d_{Z/B}`.
* `AlgebraicGeometry.Space.pullbackDifferentialsMap_comp_conormalSequenceMiddleDesc`: the
  factorization, `pullbackDifferentialsMap ≫ conormalSequenceMiddleDesc … = θ`.
* `AlgebraicGeometry.Space.isColimitCokernelCoforkPullbackDifferentialsMapAt`: the second arrow
  is a cokernel of the first.
* `AlgebraicGeometry.Space.conormalSequenceAt_exact`: **Stacks 05ZA, exactness at the middle
  term**, with the inclusion an explicit parameter and the kernel of its structure map described
  by the two hypotheses `hi` and `hker`.
* `AlgebraicGeometry.Space.conormalSequence_exact`: **Stacks 05ZA, exactness at the middle term,
  unconditionally** — the previous statement at the canonical inclusion, where `hi` and `hker`
  are the two halves of `AlgebraicGeometry.Space.mem_definingIdealAt_iff` and `hclosed` is part
  (4) of Stacks 02YU.  This is where the tag is registered.

## Implementation notes

**Where the identity lives.**  Both sides of it are `i♯` followed by the direct image of
`d_{Z/B}`; what had to be compared was the two *spellings* of that composite, one through
`AlgebraicGeometry.Space.pushforwardUniversalDerivationHom` and the other through the hom-set
bijection of Stacks 03D3.  The comparison is the triangle identity: the ring-data transport
`AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` inserts the commutative-ring
counit `i^{-1}i_*𝒪_Z ≅ 𝒪_Z`, and the transposition of Stacks 08TQ inserts the unit of
`i^{-1} ⊣ i_*`; the two cancel, by
`AlgebraicGeometry.Space.ringUnit_comp_pushforward_counitRingMap` carried to underlying sheaves
of sets.  That is
`AlgebraicGeometry.Space.homEquiv_derivationSheafHom_ringDataIso_symm`, and everything else in
the chain is a value computation.

**The casts all vanish.**  Two steps of the chain pass through a transport along an equality of
sheaves (or presheaves) of modules which differ only in their scalar action:
`AlgebraicGeometry.Space.restrictModuleAlong_moduleDirectImage` inside
`AlgebraicGeometry.Space.directImageDerivationKernelEquiv`, and the `eqToIso` inside
`AlgebraicGeometry.Space.directImageCoefficientIso`.  Neither can be unfolded, since
`AlgebraicGeometry.Space.structureSharpCommRing` is irreducible and the triangle identity is not
`rfl`.  The remedy in both cases is to describe the transport's action on sections by a `cast`,
proved by `cases` on the equation
(`AlgebraicGeometry.Space.derivationSubtypeTransport_coe_d`,
`AlgebraicGeometry.Space.sheafOfModules_eqToHom_val_app_apply`), and then to observe that the
cast's own equation is between *definitionally equal* types — the two presheaves have the same
sections — so definitional proof irrelevance identifies it with `rfl` and the cast disappears.

**`rw` is unusable here.**  The six rewriting steps of
`AlgebraicGeometry.Space.homEquiv_derivationSheafHom_ringDataIso_symm` were first written as one
`rw` chain and exhausted the heartbeat budget at `isDefEq`, because the motive check runs over
the whole sections term; as `congrArg`/`Eq.trans` the same six steps check in seconds.  For the
same reason `AlgebraicGeometry.Space.derivationDirectImageEquiv_comp` goes through
`AlgebraicGeometry.Space.derivationDirectImageEquiv_apply` explicitly at both ends rather than
leaving the unfolding of Equation (0619) to the kernel, which times out on it.

**Why the unconditional statement is transported across an isomorphism, with every component
written out.**  The short complex of `AlgebraicGeometry.Space.conormalSequence_exact` differs
from the one of `AlgebraicGeometry.Space.conormalSequenceAt_exact_subspaceInclusion` only in how
the source of the first arrow is written — `𝒞_{Z/X}` against `i^*𝓘` — and the two are
definitionally equal, `AlgebraicGeometry.Space.conormalModule_eq` being `rfl`.  Of three routes to
the transport, only the third is affordable:

* ascribing the one statement to the other directly *elaborates* and then exhausts the
  **kernel's** budget, because the conversion is re-checked underneath
  `CategoryTheory.ShortComplex.Exact`, whose unfolding carries the homology data of the complex
  with it;
* `CategoryTheory.ShortComplex.exact_iff_of_iso` with the components left as `Iso.refl _` dies in
  the elaborator instead, at `whnf` — the metavariable, not the conversion, is what costs;
* with all three components written out (`Iso.refl` at each of the three objects, named), the
  conversion is confined to one object comparison and to the two commuting squares, which are
  equations between morphisms, and the file checks in seconds.  The two squares are
  `Category.id_comp` and `Category.comp_id` with their morphisms given explicitly, for the same
  reason.

This is the same lesson as the `key` step of
`AlgebraicGeometry.Space.thickeningConormalSequence_exact`: at these concrete small étale ringed
topoi a conversion between two spellings is cheap when it is asked of named terms and ruinous when
it is asked of a metavariable.

**Why `HasSheafify` is named rather than inferred.**
`CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat` is in this file's import closure and is typed at
`AddCommGrpCat.{max u v w}` with `w` occurring nowhere else; against the small étale site, whose
objects live one universe above its arrows, that can never apply and the search reports
`u =?= max (u + 1) ?w` as *stuck* rather than discarding the candidate.
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify` is named in a `haveI` instead; no instance is
disabled and no option is set.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the derivation
  `i_*d_{Z/B} ∘ i♯` and the comparison map.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619).
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ), the transposition of
  derivations along an inverse image.
* [Stacks Project, Tag 08TF](https://stacks.math.columbia.edu/tag/08TF), whose middle exactness
  the descent of derivations is.
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU), part (4), for `hclosed`.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

section EqToHom

universe w₀ v₀ u₀

variable {E : Type u₀} [Category.{v₀} E] {J₀ : GrothendieckTopology E}
  {R₀ : Sheaf J₀ RingCat.{w₀}}

/-- `eqToHom` between sheaves of modules acts on local sections by the cast that the equality
induces on sections. -/
theorem sheafOfModules_eqToHom_val_app_apply {M N : _root_.SheafOfModules.{w₀} R₀} (h : M = N)
    (U : Eᵒᵖ) (y : ToType (M.val.obj U)) :
    ((eqToHom h).val.app U).hom y =
      cast (congrArg (fun K : _root_.SheafOfModules.{w₀} R₀ ↦ ToType (K.val.obj U)) h) y := by
  cases h
  rfl

end EqToHom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Zs : AlgebraicSpaces B S hS}

/-- **The coefficient identification of
`AlgebraicGeometry.Space.directImageCoefficientIso` is the identity on local sections.** -/
theorem directImageCoefficientIso_inv_val_app_apply (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : ToType (((directImageModules (smallEtaleRingedToposHom B S hS i).toToposHom
      (directImageStructureRingSheaf B S hS i)).obj
        (counitRestrictScalars B S hS i hi W)).val.obj U)) :
    (((directImageCoefficientIso B S hS i hi W).inv.val.app U)).hom z = z :=
  sheafOfModules_eqToHom_val_app_apply
    (congrArg (fun m ↦ (_root_.SheafOfModules.restrictScalars m).obj
        ((moduleDirectImage B S hS i).obj W))
      (ringUnit_comp_pushforward_counitRingMap B S hS i hi)) U z

/-- The sheaf hom of the transport of a derivation along the ring data of the counit square is
the counit followed by the sheaf hom of the derivation. -/
theorem derivationSheafHom_derivationEquivOfRingDataIso_symm (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (D : PresheafOfModulesOfCommRing.Derivation' W.val
      (structureSharpInverseImage B S hS (i ≫ b)).hom) :
    derivationSheafHom
        ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImageRing.map
          (directImageBase B S hS i b))
        (counitRestrictScalars B S hS i hi W)
        ((AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i b).app
            (smallEtaleRingedTopos B S hS Bb).O)
          (structureCounitIso B S hS i hi)
          (inverseImageStructureSharpCounit_square B S hS i hi b) W).symm D) =
      commRingSetHom (structureCounitIso B S hS i hi).hom ≫
        derivationSheafHom (structureSharpInverseImage B S hS (i ≫ b)) W D :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The transposition of `AlgebraicGeometry.Space.directImageDerivationEquiv` on local sections:
it is the adjunct of the sheaf hom of the transported derivation. -/
theorem directImageDerivationEquiv_symm_d (i : Zs ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (b : X ⟶ Bb) (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (D : PresheafOfModulesOfCommRing.Derivation' W.val
      (structureSharpInverseImage B S hS (i ≫ b)).hom)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType (((pushforwardCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj
      (smallEtaleRingedTopos B S hS Zs).O).obj.obj U)) :
    ((directImageDerivationEquiv B S hS i hi b W).symm D).d y =
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        ((smallEtaleRingedToposHom B S hS i).toToposHom.adj.homEquiv _ _
          (derivationSheafHom
            ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImageRing.map
              (directImageBase B S hS i b))
            (counitRestrictScalars B S hS i hi W)
            ((AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso
              ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i b).app
                (smallEtaleRingedTopos B S hS Bb).O)
              (structureCounitIso B S hS i hi)
              (inverseImageStructureSharpCounit_square B S hS i hi b) W).symm D))) y :=
  rfl

/-- **The triangle identity on underlying sheaves of sets.** -/
theorem unit_comp_directImage_commRingSetHom_structureCounitIso (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (smallEtaleRingedToposHom B S hS i).toToposHom.adj.unit.app
          (Sheaf.ringSheaf (directImageStructureRingSheaf B S hS i)) ≫
        (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward.map
          (commRingSetHom (structureCounitIso B S hS i hi).hom) =
      𝟙 (Sheaf.ringSheaf (directImageStructureRingSheaf B S hS i)) := by
  have h2 := congrArg
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
    (ringUnit_comp_pushforward_counitRingMap B S hS i hi)
  simp only [pushforwardRingMap] at h2
  exact h2

/-- **The adjunct of the transported derivation is the direct image of the derivation.**  This is
where the two spellings of `i_*d_{Z/B} ∘ i♯` meet: the counit the transport inserts is cancelled
by the unit of `i^{-1} ⊣ i_*`, by the triangle identity. -/
theorem homEquiv_derivationSheafHom_ringDataIso_symm (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (D : PresheafOfModulesOfCommRing.Derivation' W.val
      (structureSharpInverseImage B S hS (i ≫ b)).hom) :
    (smallEtaleRingedToposHom B S hS i).toToposHom.adj.homEquiv _ _
        (derivationSheafHom
          ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImageRing.map
            (directImageBase B S hS i b))
          (counitRestrictScalars B S hS i hi W)
          ((AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso
            ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i b).app
              (smallEtaleRingedTopos B S hS Bb).O)
            (structureCounitIso B S hS i hi)
            (inverseImageStructureSharpCounit_square B S hS i hi b) W).symm D)) =
      (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward.map
        (derivationSheafHom (structureSharpInverseImage B S hS (i ≫ b)) W D) := by
  refine Eq.trans (congrArg
    (fun m ↦ (smallEtaleRingedToposHom B S hS i).toToposHom.adj.homEquiv _ _ m)
    (derivationSheafHom_derivationEquivOfRingDataIso_symm B S hS i hi b W D)) ?_
  refine Eq.trans ((smallEtaleRingedToposHom B S hS i).toToposHom.adj.homEquiv_unit _ _ _) ?_
  refine Eq.trans (congrArg
    (fun m ↦ (smallEtaleRingedToposHom B S hS i).toToposHom.adj.unit.app
      (Sheaf.ringSheaf (directImageStructureRingSheaf B S hS i)) ≫ m)
    ((smallEtaleRingedToposHom B S hS i).toToposHom.pushforward.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward.map
      (derivationSheafHom (structureSharpInverseImage B S hS (i ≫ b)) W D))
    (unit_comp_directImage_commRingSetHom_structureCounitIso B S hS i hi)) ?_
  exact Category.id_comp _

/-- `AlgebraicGeometry.Space.directImageDerivationEquiv` read on local sections: the derivation
of `i_*𝒪_Z` it transposes a `B`-derivation `D` of `𝒪_Z` back to is the direct image of `D`. -/
theorem directImageDerivationEquiv_symm_d_apply (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (D : PresheafOfModulesOfCommRing.Derivation' W.val
      (structureSharpInverseImage B S hS (i ≫ b)).hom)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType (((pushforwardCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj
      (smallEtaleRingedTopos B S hS Zs).O).obj.obj U)) :
    ((directImageDerivationEquiv B S hS i hi b W).symm D).d y =
      ((smallEtaleDirectImage B S hS i).map
        (derivationSheafHom (structureSharpInverseImage B S hS (i ≫ b)) W D)).hom.app U y :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map m y)
    (homEquiv_derivationSheafHom_ringDataIso_symm B S hS i hi b W D)

/-- **The descent of a `B`-derivation of `𝒪_Z` is `i♯` followed by the direct image of that
derivation.** -/
theorem directImageDerivationKernelEquiv_coe_d_apply (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (D : PresheafOfModulesOfCommRing.Derivation' W.val
      (structureSharpInverseImage B S hS (i ≫ b)).hom)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : ToType ((structureRingSheaf B S hS X).obj.obj U)) :
    ((directImageDerivationKernelEquiv B S hS i hi b W D).1).d t =
      ((smallEtaleDirectImage B S hS i).map
          (derivationSheafHom (structureSharpInverseImage B S hS (i ≫ b)) W D)).hom.app U
        ((structureSharpSet B S hS i).hom.app U t) := by
  refine (directImageDerivationKernelEquiv_coe_d B S hS i hi b W D U t).trans ?_
  refine (PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply _ _ _).trans ?_
  refine (directImageCoefficientIso_inv_val_app_apply B S hS i hi W U _).trans ?_
  refine (directImageDerivationEquiv_symm_d_apply B S hS i hi b W D U _).trans ?_
  exact congrArg (fun z ↦ ((smallEtaleDirectImage B S hS i).map
      (derivationSheafHom (structureSharpInverseImage B S hS (i ≫ b)) W D)).hom.app U z)
    (structureSharpCommRing_app_apply B S hS i U t)

/-- **The 04CX derivation `i_*d_{Z/B} ∘ i♯` is the descent of `d_{Z/B}`.** -/
theorem pushforwardUniversalDerivation_eq_descent (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb) :
    pushforwardUniversalDerivation B S hS i b (i ≫ b) (𝟙 Bb) (by simp) =
      (directImageDerivationKernelEquiv B S hS i hi b (sheafOfDifferentials B S hS (i ≫ b))
        (universalDerivation B S hS (i ≫ b))).1 :=
  PresheafOfModulesOfCommRing.Derivation.ext (funext fun U ↦ AddMonoidHom.ext fun t ↦
    (directImageDerivationKernelEquiv_coe_d_apply B S hS i hi b
      (sheafOfDifferentials B S hS (i ≫ b)) (universalDerivation B S hS (i ≫ b)) U t).symm)

/-- **Equation (0619) is natural in the coefficient module.** -/
theorem derivationDirectImageEquiv_comp (a : Zs ⟶ X) (b : X ⟶ Bb)
    {C C' : Modules.{u, u} B S hS Zs.1 Zs.2}
    (k : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ C) (g : C ⟶ C') :
    derivationDirectImageEquiv B S hS a b C' (k ≫ g) =
      (derivationDirectImageEquiv B S hS a b C k).postcomp
        ((modulePushforward B S hS a).map g).val := by
  refine (derivationDirectImageEquiv_apply B S hS a b C' (k ≫ g)).trans ?_
  refine Eq.trans (congrArg
    (fun m ↦ (universalDerivation B S hS b).postcomp (_root_.SheafOfModules.Hom.val m))
    (Adjunction.homEquiv_naturality_right (modulePullbackAdjunction B S hS a) k g)) ?_
  refine (PresheafOfModulesOfCommRing.Derivation'.postcomp_comp (universalDerivation B S hS b)
    (((modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS b) C) k).val
    ((modulePushforward B S hS a).map g).val).trans ?_
  exact congrArg (fun m ↦ m.postcomp ((modulePushforward B S hS a).map g).val)
    (derivationDirectImageEquiv_apply B S hS a b C k).symm

/-- **The descent of derivations along the structure map of a closed immersion is natural in the
coefficient module.** -/
theorem directImageDerivationKernelEquiv_coe_postcomp (i : Zs ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    {W W' : Modules.{u, u} B S hS Zs.1 Zs.2} (k : W ⟶ W')
    (D : PresheafOfModulesOfCommRing.Derivation' W.val
      (structureSharpInverseImage B S hS (i ≫ b)).hom) :
    ((directImageDerivationKernelEquiv B S hS i hi b W' (D.postcomp k.val)).1) =
      ((directImageDerivationKernelEquiv B S hS i hi b W D).1).postcomp
        ((modulePushforward B S hS i).map k).val := by
  refine PresheafOfModulesOfCommRing.Derivation.ext (funext fun U ↦ AddMonoidHom.ext fun t ↦ ?_)
  refine (directImageDerivationKernelEquiv_coe_d_apply B S hS i hi b W'
    (D.postcomp k.val) U t).trans ?_
  refine Eq.trans (congrArg
    (fun m ↦ m.hom.app U (((structureSharpSet B S hS i).hom.app U) t))
    ((congrArg (smallEtaleDirectImage B S hS i).map
        (derivationSheafHom_postcomp (structureSharpInverseImage B S hS (i ≫ b)) k D)).trans
      ((smallEtaleDirectImage B S hS i).map_comp _ _))) ?_
  refine Eq.trans ?_ (PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply
      ((directImageDerivationKernelEquiv B S hS i hi b W D).1)
      ((modulePushforward B S hS i).map k).val t).symm
  exact congrArg (fun z ↦ ((((modulePushforward B S hS i).map k).val.app U).hom) z)
    (directImageDerivationKernelEquiv_coe_d_apply B S hS i hi b W D U t).symm

/-- **Exactness at the middle term of Stacks 05ZA, the factorization.**  The morphism
`AlgebraicGeometry.Space.conormalSequenceMiddleDesc` really is a factorization of `θ` through
the second arrow `AlgebraicGeometry.Space.pullbackDifferentialsMap` of the conormal sequence.

This is the clause the *What is not proved* section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleDescent.lean` recorded as the single
residue, and it is now `AlgebraicGeometry.Space.pushforwardUniversalDerivation_eq_descent`
together with the naturality of the two bijections involved. -/
theorem pullbackDifferentialsMap_comp_conormalSequenceMiddleDesc
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : Zs ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hker : StructureSharpKernelLeDefiningIdeal B S hS Z i)
    (hclosed : IsClosedImmersion B S hS i.hom) (W : Modules.{u, u} B S hS Zs.1 Zs.2)
    (θ : (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) ⟶ W)
    (hθ : conormalSequenceFirstMapAt B S hS Z b i hi ≫ θ = 0) :
    pullbackDifferentialsMap B S hS i b ≫
        conormalSequenceMiddleDesc B S hS Z b i hi hker hclosed W θ hθ = θ := by
  refine (derivationDirectImageEquiv B S hS i b W).injective ?_
  refine Eq.trans (derivationDirectImageEquiv_comp B S hS i b
    (pullbackDifferentialsMap B S hS i b)
    (conormalSequenceMiddleDesc B S hS Z b i hi hker hclosed W θ hθ)) ?_
  refine Eq.trans (congrArg (fun m ↦ m.postcomp ((modulePushforward B S hS i).map
      (conormalSequenceMiddleDesc B S hS Z b i hi hker hclosed W θ hθ)).val)
    (((derivationDirectImageEquiv B S hS i b
        (sheafOfDifferentials B S hS (i ≫ b))).apply_symm_apply
      (pushforwardUniversalDerivation B S hS i b (i ≫ b) (𝟙 Bb) (by simp))).trans
      (pushforwardUniversalDerivation_eq_descent B S hS i hclosed b))) ?_
  refine Eq.trans (directImageDerivationKernelEquiv_coe_postcomp B S hS i hclosed b
    (conormalSequenceMiddleDesc B S hS Z b i hi hker hclosed W θ hθ)
    (universalDerivation B S hS (i ≫ b))).symm ?_
  refine Eq.trans (congrArg
    (fun m ↦ ((directImageDerivationKernelEquiv B S hS i hclosed b W) m).1)
    ((differentialsHomEquiv B S hS (i ≫ b) W).apply_symm_apply
      (conormalSequenceMiddleDerivation B S hS Z b i hi hker hclosed W θ hθ))) ?_
  exact congrArg (fun p ↦ p.1)
    ((directImageDerivationKernelEquiv B S hS i hclosed b W).apply_symm_apply
      ⟨derivationDirectImageEquiv B S hS i b W θ,
        fun U x hx ↦ derivationDirectImageEquiv_d_eq_zero_of_mem B S hS Z b i hi W θ hθ U x
          (hker U x hx)⟩)

/-- **`Ω_{Z/B}` is a cokernel of the first arrow of the conormal sequence of Stacks 05ZA.**
Existence of the factorization is
`AlgebraicGeometry.Space.pullbackDifferentialsMap_comp_conormalSequenceMiddleDesc`; uniqueness
is exactness at the right term, i.e. that the second arrow is an epimorphism, which
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion` supplies from the closed
immersion. -/
noncomputable def isColimitCokernelCoforkPullbackDifferentialsMapAt
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : Zs ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hker : StructureSharpKernelLeDefiningIdeal B S hS Z i)
    (hclosed : IsClosedImmersion B S hS i.hom) :
    Limits.IsColimit (Limits.CokernelCofork.ofπ (pullbackDifferentialsMap B S hS i b)
      (conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS Z b i hi)) :=
  haveI : Epi (pullbackDifferentialsMap B S hS i b) :=
    epi_pullbackDifferentialsMap_of_isImmersion B S hS i b
      (isImmersion_of_isClosedImmersion B S hS hclosed)
  Limits.CokernelCofork.IsColimit.ofπ' _ _ fun {_} k hk ↦
    ⟨conormalSequenceMiddleDesc B S hS Z b i hi hker hclosed _ k hk,
      pullbackDifferentialsMap_comp_conormalSequenceMiddleDesc B S hS Z b i hi hclosed
        (hker := hker) _ k hk⟩

/-- **Stacks 05ZA, exactness at the middle term.**  The short complex
`𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B}` of the conormal sequence of a closed subspace is exact at
`i^*Ω_{X/B}`.

Together with `AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion` (exactness
at the right term) and
`AlgebraicGeometry.Space.conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero` (the
composite is zero) this is the exactness of the whole sequence.

Nothing is assumed beyond the data of the tag: `hi` and `hker` together say the kernel of `i♯`
is the defining ideal sheaf of `Z`, which for the inclusion of `Z` itself is
`AlgebraicGeometry.Space.mem_definingIdealAt_iff` in its two directions, and `hclosed` is that
the inclusion is a closed immersion, which part (4) of Stacks 02YU gives.

**This is the general form, with the inclusion an explicit parameter**, kept because consumers
holding the inclusion under another name — `AlgebraicGeometry.Space.universalThickeningInclusion`
— instantiate it directly, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceInclusionParameter.lean`.  The tag is
registered on `AlgebraicGeometry.Space.conormalSequence_exact`, which is this statement at the
canonical inclusion with all three hypotheses discharged, so that no registration of Stacks 05ZA
carries a stand-in for a clause of the tag. -/
theorem conormalSequenceAt_exact (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : Zs ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hker : StructureSharpKernelLeDefiningIdeal B S hS Z i)
    (hclosed : IsClosedImmersion B S hS i.hom) :
    (ShortComplex.mk _ _
      (conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS Z b i hi)).Exact :=
  have : HasSheafify (smallEtaleRingedSite B S hS Zs.1 Zs.2).J AddCommGrpCat.{u} :=
    SmallEtale.instHasSheafify B S hS Zs.1 AddCommGrpCat.{u}
  ShortComplex.exact_of_g_is_cokernel _
    (isColimitCokernelCoforkPullbackDifferentialsMapAt B S hS Z b i hi hker hclosed)

/-- **The inclusion of a closed subspace is a closed immersion.**  This is the second half of
part (4) of Stacks 02YU, read off the bundled `AlgebraicGeometry.Space.ClosedSubspaces`; it is
what discharges the `hclosed` hypothesis of
`AlgebraicGeometry.Space.conormalSequenceAt_exact` at the inclusion itself. -/
theorem isClosedImmersion_subspaceInclusion (V : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS V.1) :
    IsClosedImmersion B S hS (subspaceInclusion B S hS V Z).hom :=
  Z.2.2

/-- **Stacks 05ZA, exactness at the middle term, at the canonical inclusion, written out of
`i^*𝓘`.**  `AlgebraicGeometry.Space.conormalSequenceAt_exact` at `i := subspaceInclusion`, with
all three of its hypotheses discharged: the two halves of
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`
(`AlgebraicGeometry.Space.structureSharpKillsDefiningIdeal_subspaceInclusion` and
`AlgebraicGeometry.Space.structureSharpKernelLeDefiningIdeal_subspaceInclusion`) and part (4) of
Stacks 02YU (`AlgebraicGeometry.Space.isClosedImmersion_subspaceInclusion`).

The same statement with the source of the first arrow read as the conormal module `𝒞_{Z/X}` is
`AlgebraicGeometry.Space.conormalSequence_exact`, which is where the tag is registered. -/
theorem conormalSequenceAt_exact_subspaceInclusion (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) :
    (ShortComplex.mk _ _ (conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero
      B S hS Z b (subspaceInclusion B S hS X Z)
      (structureSharpKillsDefiningIdeal_subspaceInclusion B S hS Z))).Exact :=
  conormalSequenceAt_exact B S hS Z b (subspaceInclusion B S hS X Z)
    (structureSharpKillsDefiningIdeal_subspaceInclusion B S hS Z)
    (structureSharpKernelLeDefiningIdeal_subspaceInclusion B S hS Z)
    (isClosedImmersion_subspaceInclusion B S hS X Z)

/-- **Stacks 05ZA, exactness at the middle term, unconditionally.**  For a subspace
`Z ⊆ X` of an algebraic space over `B` with structure morphism `b : X ⟶ Bb`, the short complex
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B}
```
built from the canonical first arrow `AlgebraicGeometry.Space.conormalSequenceFirstMap` and the
second arrow `AlgebraicGeometry.Space.pullbackDifferentialsMap` is exact at `i^*Ω_{X/B}`.

**No hypothesis is carried.**  This is
`AlgebraicGeometry.Space.conormalSequenceAt_exact_subspaceInclusion`, read with the source of the
first arrow written as the conormal module `𝒞_{Z/X}` of Stacks 04CN rather than as `i^*𝓘`; the
two readings are the same morphism, by `AlgebraicGeometry.Space.conormalModule_eq`.

The transport is through `CategoryTheory.ShortComplex.exact_iff_of_iso`, with every component of
the isomorphism written out, rather than by ascribing the statement directly; the implementation
notes of this file record what each of the other routes costs. -/
@[stacks 05ZA "exactness at the middle term `i^*Ω_{X/B}`: the second arrow is a cokernel of the \
first, at a subspace inclusion `Z ⊆ X` — the case the tag's own proof reduces the immersion case \
to.  Unconditional: stated at the canonical inclusion and at the registered first arrow \
`conormalSequenceFirstMap`, with no hypothesis beyond the tag's own data.  The general form with \
the inclusion an explicit parameter is `conormalSequenceAt_exact`, whose three hypotheses this \
discharges — the two halves of `mem_definingIdealAt_iff` and the closed-immersion clause of \
02YU(4); the inclusion is left a parameter there for the reason recorded in \
`ConormalSequenceInclusionParameter.lean`.  The same clause at the first arrow of an arbitrary \
immersion, over the ambient open of 04CE, is `conormalSequenceOfImmersion_exact`"]
theorem conormalSequence_exact (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    (ShortComplex.mk _ _
      (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS Z b)).Exact := by
  refine (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (Iso.refl (conormalModule B S hS X Z))
    (Iso.refl ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
      (sheafOfDifferentials B S hS b)))
    (Iso.refl (sheafOfDifferentials B S hS (subspaceInclusion B S hS X Z ≫ b)))
    ?_ ?_)).mpr (conormalSequenceAt_exact_subspaceInclusion B S hS Z b)
  · exact (Category.id_comp (conormalSequenceFirstMapAt B S hS Z b
      (subspaceInclusion B S hS X Z)
      (structureSharpKillsDefiningIdeal_subspaceInclusion B S hS Z))).trans
      (Category.comp_id (conormalSequenceFirstMap B S hS Z b)).symm
  · simp

end AlgebraicGeometry.Space

end
