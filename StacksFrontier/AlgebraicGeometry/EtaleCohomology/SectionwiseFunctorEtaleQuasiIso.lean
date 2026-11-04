module

public import StacksFrontier.CategoryTheory.Sites.Point.SectionwiseFunctorQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Point.InjectiveFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.InjectiveSheafSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sectionwise functors on resolutions of étale sheaves with injective stalks

Let `X` be a scheme, `R` a finite ring and `H : Mod_R ⥤ Mod_S` an additive functor preserving
limits and filtered colimits. Applying `H` to sections carries a quasi-isomorphism of bounded
below complexes of sheaves of `R`-modules on the small étale site of `X`, all of whose stalks at
the separable closures of the residue fields are injective modules, to a quasi-isomorphism. The
stalks of an injective sheaf of `R`-modules are injective modules, so this applies to an
injective resolution of a sheaf with injective stalks.

This is the exactness input of Step 7 of the proof of [Stacks, Tag 03UG].

## Main definitions

* `AlgebraicGeometry.Scheme.residueEtalePoint`: the point of the small étale site at the
  separable closure of the residue field of a point of `X`, universe-lifted.

## Main results

* `AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_residueEtalePoint`
* `AlgebraicGeometry.Scheme.moduleInjective_residueEtalePoint_sheafFiber`
* `AlgebraicGeometry.Scheme.quasiIso_sheafCompose_map_of_injective_stalks`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u r

/-- Modules over a ring in a smaller universe satisfy AB5 in the module universe, filtered
colimits and finite limits being computed in abelian groups. -/
instance _root_.ModuleCat.ab5OfSize_of_small (R : Type r) [Ring R] [Small.{w} R] :
    AB5OfSize.{w, w} (ModuleCat.{w} R) where
  ofShape J _ _ :=
    HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The point of the small étale site of `X` at the separable closure of the residue field of
`x`, with fibers in `Type (max (u + 1) r)`. -/
@[sga "4 VIII 3.4"]
abbrev residueEtalePoint (x : X) :
    GrothendieckTopology.Point.{max (u + 1) r} X.smallEtaleTopology :=
  (pointSmallEtale ((SpecToEquivOfField (SeparableClosure (X.residueField x)) _).2
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩)).ulift.{max (u + 1) r}

/-- The points at the separable closures of the residue fields form a conservative family. -/
theorem isConservativeFamilyOfPoints_residueEtalePoint :
    (ObjectProperty.ofObj (residueEtalePoint.{u, r} X)).IsConservativeFamilyOfPoints :=
  isConservative_pointSmallEtale_ulift _ (Set.eq_univ_of_forall fun s =>
    Set.mem_iUnion.2 ⟨s, default, by simp [SpecToEquivOfField]⟩)

variable {X}

/-- **The stalks of an injective sheaf of modules over a finite ring are injective modules.** -/
theorem moduleInjective_residueEtalePoint_sheafFiber {R : Type r} [Ring R] [Finite R]
    (I : Stacks.EtaleCohomology.EtaleModules.{u, r} R X) [Injective I] (x : X) :
    Module.Injective R (((residueEtalePoint.{u, r} X x).sheafFiber
      (A := ModuleCat.{max (u + 1) r} R)).obj I) :=
  (residueEtalePoint X x).moduleInjective_sheafFiber I fun W =>
    Stacks.EtaleCohomology.moduleInjective_etaleModule_sections R I W.unop

/-- **A sectionwise functor carries a quasi-isomorphism of bounded below complexes of étale sheaves
with injective stalks to a quasi-isomorphism.** -/
theorem quasiIso_sheafCompose_map_of_injective_stalks {R S : Type r} [Ring R] [Ring S]
    (H : ModuleCat.{max (u + 1) r} R ⥤ ModuleCat.{max (u + 1) r} S) [H.Additive]
    [X.smallEtaleTopology.HasSheafCompose H]
    [PreservesFilteredColimitsOfSize.{max (u + 1) r, max (u + 1) r} H]
    {K L : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} R X) ℤ} (φ : K ⟶ L)
    [QuasiIso φ] (d : ℤ) [K.IsStrictlyGE d] [L.IsStrictlyGE d]
    (hK : ∀ (x : X) (n : ℤ), Module.Injective R (((residueEtalePoint.{u, r} X x).sheafFiber
      (A := ModuleCat.{max (u + 1) r} R)).obj (K.X n)))
    (hL : ∀ (x : X) (n : ℤ), Module.Injective R (((residueEtalePoint.{u, r} X x).sheafFiber
      (A := ModuleCat.{max (u + 1) r} R)).obj (L.X n))) :
    QuasiIso (((sheafCompose X.smallEtaleTopology H).mapHomologicalComplex _).map φ) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{max (u + 1) r} S)) :=
    preservesLimitsOfSize_shrink.{u + 1, max (u + 1) r, u, max (u + 1) r} _
  have : X.smallEtaleTopology.HasSheafCompose
      (CategoryTheory.forget (ModuleCat.{max (u + 1) r} S)) :=
    inferInstance
  have : ∀ (T : Type r) [Ring T] (Φ : GrothendieckTopology.Point.{max (u + 1) r}
      X.smallEtaleTopology), (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} T)).Additive :=
    fun T _ Φ => Functor.additive_of_preserves_binary_products _
  have : ∀ (T : Type r) [Ring T] (Φ : GrothendieckTopology.Point.{max (u + 1) r}
      X.smallEtaleTopology), (Φ.sheafFiber (A := ModuleCat.{max (u + 1) r} T)).PreservesHomology :=
    fun T _ Φ => Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact (isConservativeFamilyOfPoints_residueEtalePoint.{u, r} X).quasiIso_sheafCompose_map
    (R := R) (S := S) H φ d (fun ⟨_, ⟨x⟩⟩ => hK x) fun ⟨_, ⟨x⟩⟩ => hL x

end AlgebraicGeometry.Scheme

end
