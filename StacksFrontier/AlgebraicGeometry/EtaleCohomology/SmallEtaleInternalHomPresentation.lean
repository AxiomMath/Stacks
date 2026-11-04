module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTransfer
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.InternalHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleFiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FirstVariableLeftExact

/-!
# The internal Hom out of a globally presented module on the small étale site

Clause (6) of Stacks 0GNB asserts that the internal Hom `𝓗om_𝒪(𝓕, 𝓖)` of two quasi-coherent
`𝒪`-modules on the small étale site of a scheme is quasi-coherent when `𝓕` is of finite
presentation.  This file proves it **for a `𝓕` which is globally the cokernel of a map of finite
free modules**, at the module universe `u` of the schemes, which is the universe in which the
other five clauses of the tag are stated.

Three things have to be put together, and the universe is what makes that delicate.  The
internal Hom of the small étale *ringed* site, `AlgebraicGeometry.RingedSite.internalHomSheaf`,
raises the module universe from `u` to `u + 1`, because the objects of the site form a type in
`Type (u + 1)`; `AlgebraicGeometry.SmallEtale.internalHomSheaf` is its descent to `u` along the
universe lift `Stacks.SheafOfModules.moduleULift`, which is fully faithful and exact.  The
closure of quasi-coherence under kernels on this site, Stacks 0GNB (3), is available at `u` and
not at `u + 1`.  So the kernel presentation of the internal Hom — Stacks 03EN, available with
free universes as `AlgebraicGeometry.RingedSite.isLimit_kernelFork_internalHomPre` — is pulled
down the lift here, and the kernel clause is then applied at `u`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.internalHomSheafPre`: the first-variable action of
  `AlgebraicGeometry.SmallEtale.internalHomSheaf`, obtained from the one of the ringed site by
  full faithfulness of the universe lift.

## Main results

* `Stacks.SheafOfModules.isFiniteFree_of_isColimit_cofan_unit` and
  `Stacks.SheafOfModules.isFiniteLocallyFree_of_isColimit_cofan_unit`: a finite coproduct of
  copies of the structure sheaf is finite free, and finite locally free.  The second is the
  hypothesis in which Stacks 0GNC,
  `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`, consumes a finite free
  module.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_isColimit_cofan`:
  **the internal Hom out of a finite free module into a quasi-coherent module is
  quasi-coherent**, at module universe `u`.  This is Stacks 0GNC at `u + 1` read down the
  universe lift, which neither creates nor destroys quasi-coherence
  (`SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'`).
* `AlgebraicGeometry.SmallEtale.isColimit_cokernelCofork_over`: restriction to a slice carries a
  cokernel presentation to a cokernel presentation at module universe `u` — the input `hb` of
  `AlgebraicGeometry.RingedSite.isLimit_kernelFork_internalHomPre`, discharged on this site
  because restriction of modules to a slice is a left adjoint there
  (`SheafOfModules.overPushforwardOverAdj`, the small étale site having binary products).
* `AlgebraicGeometry.SmallEtale.isLimit_kernelFork_internalHomSheafPre`: **Stacks 03EN, the
  cokernel half, for `AlgebraicGeometry.SmallEtale.internalHomSheaf` at module universe `u`** —
  if `𝓕` is the cokernel of `a : 𝓠 ⟶ 𝓟` then `𝓗om_𝒪(𝓕, 𝓖)` is the kernel of the dual of `a`.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_presentation`:
  **clause (6) of Stacks 0GNB for a module with a global presentation by finite free
  modules.**

## Implementation notes

**No `@[stacks 0GNB]` attribute is carried and no clause of Stacks 0GNB is claimed here.**  The
finite-presentation hypothesis of clause (6) is Stacks 03DL (7), which is local: every object of
the site has a covering on whose members the module has a finite global presentation.  The
hypotheses of
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_presentation` are a
presentation on the site itself, which is strictly stronger, so that statement is not the
clause; the convention — a reduction carries no tag — is the one of
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentFree`, which is the same statement
for the small étale site of an algebraic space and is in addition conditional on Descent,
Proposition 03DX (2).  Here nothing is conditional: 03DX (2) at `τ = étale` is proved, so the
kernel clause of 0GNB (3) is unconditional on this site.

What separates this from the clause is the passage from a local presentation to the site, and
that passage is carried out in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomFinitePresentation`, where
the clause itself is `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf`.  It
needs two comparisons, both of which that file builds and neither of which is here: the
restriction of the internal Hom to a slice (Stacks 0E8H,
`Stacks.SheafOfModules.InternalHom.internalHomOverIso`) in the
`AlgebraicGeometry.SmallEtale.internalHomSheaf` spelling, and the transport of the internal Hom
along the localization equivalence of the slice at an object with the small étale site of the
scheme of that object, the shape in which
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso` states such a transport.  The
two together are `AlgebraicGeometry.SmallEtale.objRestrictInternalHomSheafIso`.

A second gap of spelling, not of mathematics, separates the presentation hypothesis here from
`SheafOfModules.HasFiniteGlobalPresentation`: the latter presents the *universe lift* of the
module, its coproducts and cokernel being taken in `max u v w m`, which on this site is `u + 1`,
while the hypotheses here are at `u`.  The two are interchangeable by full faithfulness and
exactness of the lift; that exchange is not made here either, and it is made in that same file,
by `SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation'`.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace Stacks.SheafOfModules

/-- A sheaf of modules which is a finite coproduct of copies of the structure sheaf is finite
free. -/
theorem isFiniteFree_of_isColimit_cofan_unit
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M : _root_.SheafOfModules.{u} R} {I : Type u} [Finite I]
    (ι : I → (_root_.SheafOfModules.unit R ⟶ M))
    (h : IsColimit (Cofan.mk M ι)) :
    _root_.SheafOfModules.IsFiniteFree R M := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  refine ((_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R M).2
    ⟨n, fun j => ι (e.symm j), ⟨?_⟩⟩)
  exact (Cofan.isColimitEquivOfEquiv (ε := e.symm) (Cofan.mk M ι)) h

/-- A sheaf of modules which is a finite coproduct of copies of the structure sheaf is finite
locally free: it is isomorphic to a free module on a finite index type. -/
theorem isFiniteLocallyFree_of_isColimit_cofan_unit
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : _root_.SheafOfModules.{u} R} {I : Type u} [Finite I]
    (ι : I → (_root_.SheafOfModules.unit R ⟶ M))
    (h : IsColimit (Cofan.mk M ι)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, v₁, u₁} M := by
  have e : _root_.SheafOfModules.free (R := R) I ≅ M :=
    (_root_.SheafOfModules.isColimitFreeCofan I).coconePointUniqueUpToIso h
  have h₀ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, v₁, u₁} M :=
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso e
  exact ⟨h₀.exists_isFiniteLocallyFreeData⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The internal Hom out of a finite free module -/

/-- **The internal Hom out of a finite free module into a quasi-coherent module is
quasi-coherent**, at the module universe of the schemes. -/
theorem isQuasicoherentOnSite_internalHomSheaf_of_isColimit_cofan
    {I : Type u} [Finite I]
    {P G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O)}
    (ι : I → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O) ⟶ P))
    (hP : IsColimit (Cofan.mk P ι)) (hG : G.IsQuasicoherentOnSite) :
    (internalHomSheaf B S hS P G).IsQuasicoherentOnSite := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u + 1} P :=
    Stacks.SheafOfModules.isFiniteLocallyFree_of_isColimit_cofan_unit ι hP
  have : P.IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_hasGlobalPresentation P
      (SheafOfModules.hasFiniteGlobalPresentation_of_isFiniteFree
        (Stacks.SheafOfModules.isFiniteFree_of_isColimit_cofan_unit ι hP)).hasGlobalPresentation
  have : G.IsQuasicoherentOnSite := hG
  have hbig : SheafOfModules.IsQuasicoherentOnSite
      (RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS) P G) :=
    RingedSite.internalHomSheaf_isQuasicoherent (smallEtaleRingedSite B S hS) P G
  exact SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (moduleULiftInternalHomSheafIso B S hS P G).symm hbig)

/-! ### The first-variable action at the module universe of the schemes -/

/-- **The first-variable action of the internal Hom of the small étale site**, at the module
universe of the schemes: the action on the internal Hom of the ringed site, read down the
universe lift, which is fully faithful. -/
noncomputable def internalHomSheafPre
    {A A' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O)} (f : A ⟶ A')
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O)) :
    internalHomSheaf B S hS A' G ⟶ internalHomSheaf B S hS A G :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).preimage
    ((moduleULiftInternalHomSheafIso B S hS A' G).hom ≫
      RingedSite.internalHomPre (smallEtaleRingedSite B S hS) f ≫
        (moduleULiftInternalHomSheafIso B S hS A G).inv)

/-- The universe lift of `AlgebraicGeometry.SmallEtale.internalHomSheafPre` is the
first-variable action on the internal Hom of the ringed site. -/
theorem moduleULift_map_internalHomSheafPre
    {A A' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O)} (f : A ⟶ A')
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O)) :
    (Stacks.SheafOfModules.moduleULift.{u + 1, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).map
          (internalHomSheafPre B S hS f G) =
      (moduleULiftInternalHomSheafIso B S hS A' G).hom ≫
        RingedSite.internalHomPre (smallEtaleRingedSite B S hS) f ≫
          (moduleULiftInternalHomSheafIso B S hS A G).inv :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).map_preimage _

section Presentation

variable
  {M P Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS).O)}
  {a : Q ⟶ P} {b : P ⟶ M}
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))

/-- **The dual of `a` kills the dual of `b`**, at the module universe of the schemes. -/
theorem internalHomSheafPre_comp_internalHomSheafPre (hab : a ≫ b = 0) :
    internalHomSheafPre B S hS b G ≫ internalHomSheafPre B S hS a G = 0 := by
  have := (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).faithful
  apply (Stacks.SheafOfModules.moduleULift.{u + 1, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).map_injective
  rw [Functor.map_comp, moduleULift_map_internalHomSheafPre,
    moduleULift_map_internalHomSheafPre, Functor.map_zero, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc,
    reassoc_of% RingedSite.internalHomPre_comp_internalHomPre (smallEtaleRingedSite B S hS) G hab,
    zero_comp, comp_zero]

/-- Restriction to a slice of the small étale site carries a cokernel presentation to a
cokernel presentation, at the module universe of the schemes: restriction is a left adjoint
there, the site having binary products. -/
noncomputable def isColimit_cokernelCofork_over (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab)) (V : SmallEtale B S hS) :
    IsColimit (CokernelCofork.ofπ (SheafOfModules.Hom.over b V)
      (RingedSite.over_comp_over_eq_zero (smallEtaleRingedSite B S hS) hab V)) := by
  haveI : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor.{u} (structureSheaf B S hS) V) :=
    (SheafOfModules.overPushforwardOverAdj (R := structureSheaf B S hS)
      V).leftAdjoint_preservesColimits
  haveI : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{u} (structureSheaf B S hS) V) :=
    preservesColimitsOfSize_shrink _
  exact RingedSite.isColimitCokernelCoforkOver (smallEtaleRingedSite B S hS) hab hb V

/-- **Stacks 03EN, the cokernel half, on the small étale site of a scheme at the module
universe of the schemes.**  If `𝓕` is the cokernel of `a : 𝓠 ⟶ 𝓟` then `𝓗om_𝒪(𝓕, 𝓖)` is the
kernel of the dual of `a`. -/
noncomputable def isLimit_kernelFork_internalHomSheafPre (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab)) :
    IsLimit (KernelFork.ofι (internalHomSheafPre B S hS b G)
      (internalHomSheafPre_comp_internalHomSheafPre B S hS G hab)) := by
  haveI := (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).full
  haveI := (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).faithful
  have hbig := RingedSite.isLimit_kernelFork_internalHomPre (smallEtaleRingedSite B S hS) G hab
    (fun V => isColimit_cokernelCofork_over B S hS hab hb V)
  -- the two parallel pairs are conjugate by the universe-lift comparisons
  have hcomm : ∀
    {A A' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O)}
      (f : A ⟶ A'), (moduleULiftInternalHomSheafIso B S hS A' G).hom ≫
        RingedSite.internalHomPre (smallEtaleRingedSite B S hS) f (C := G) =
      (ringedSiteModuleULift B S hS).map (internalHomSheafPre B S hS f G) ≫
        (moduleULiftInternalHomSheafIso B S hS A G).hom := by
    intro A A' f
    rw [moduleULift_map_internalHomSheafPre]
    simp
  let α : parallelPair ((ringedSiteModuleULift B S hS).map
        (internalHomSheafPre B S hS a G)) 0 ≅
      parallelPair (RingedSite.internalHomPre (smallEtaleRingedSite B S hS) a (C := G)) 0 :=
    parallelPair.ext (moduleULiftInternalHomSheafIso B S hS P G)
      (moduleULiftInternalHomSheafIso B S hS Q G)
      (by
        change (ringedSiteModuleULift B S hS).map (internalHomSheafPre B S hS a G) ≫
            (moduleULiftInternalHomSheafIso B S hS Q G).hom =
          (moduleULiftInternalHomSheafIso B S hS P G).hom ≫
            RingedSite.internalHomPre (smallEtaleRingedSite B S hS) a (C := G)
        exact (hcomm a).symm)
      (by simp)
  refine isLimitOfReflects (ringedSiteModuleULift B S hS) ?_
  refine (isLimitMapConeForkEquiv' (ringedSiteModuleULift B S hS)
    (internalHomSheafPre_comp_internalHomSheafPre B S hS G hab)).symm ?_
  refine (IsLimit.postcomposeHomEquiv α _) (IsLimit.ofIsoLimit hbig (Iso.symm (Fork.ext
    (moduleULiftInternalHomSheafIso B S hS M G) ?_)))
  change (moduleULiftInternalHomSheafIso B S hS M G).hom ≫
      RingedSite.internalHomPre (smallEtaleRingedSite B S hS) b (C := G) =
    (ringedSiteModuleULift B S hS).map (internalHomSheafPre B S hS b G) ≫
      (moduleULiftInternalHomSheafIso B S hS P G).hom
  exact hcomm b

/-- **Clause (6) of Stacks 0GNB for a module with a global presentation by finite free
modules.**  This is not the clause itself: the clause asks for a presentation only
étale-locally. -/
theorem isQuasicoherentOnSite_internalHomSheaf_of_presentation
    {I K : Type u} [Finite I] [Finite K]
    (ιP : I → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O) ⟶ P))
    (hιP : IsColimit (Cofan.mk P ιP))
    (ιQ : K → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS).O) ⟶ Q))
    (hιQ : IsColimit (Cofan.mk Q ιQ))
    (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    (hG : G.IsQuasicoherentOnSite) :
    (internalHomSheaf B S hS M G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isLimit_kernelFork B S hS (internalHomSheafPre B S hS a G)
    (isQuasicoherentOnSite_internalHomSheaf_of_isColimit_cofan B S hS ιP hιP hG)
    (isQuasicoherentOnSite_internalHomSheaf_of_isColimit_cofan B S hS ιQ hιQ hG)
    (isLimit_kernelFork_internalHomSheafPre B S hS G hab hb)

end Presentation

end AlgebraicGeometry.SmallEtale

end
