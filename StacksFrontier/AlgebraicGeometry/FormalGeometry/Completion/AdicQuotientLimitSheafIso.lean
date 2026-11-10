module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientLimitHomologyComparison
public import StacksFrontier.Topology.Sheaves.Basis.LocallyBijectiveBasisIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSpace

/-!
# Part (2) of the theorem on formal functions

Let `X` be a locally Noetherian scheme, `ℐ ⊂ 𝒪_X` an arbitrary quasi-coherent sheaf of ideals and
`K` a pseudo-coherent object of `D(𝒪_X)`. This file proves part (2) of [Stacks, Tag 0A0K],

`H^q(K^∧) = lim_n H^q(K)/ℐⁿ H^q(K)`,

as an isomorphism of sheaves of `𝒪_X`-modules, at the tag's own hypotheses and nothing more:
`Stacks.Algebraization.nonempty_iso_homology_derivedCompletion_limit_adicQuotientSystem`.

## The route, and what it avoids

`Completion/AdicQuotientLimitHomologyComparison.lean` proves part (2) over an affine open `V`, on
the sections of the tag's own right-hand side: there is exactly one `Γ(X, V)`-linear map

`c_V : Γ(V, lim H^q(K)/ℐⁿH^q(K)) ⟶ H^q(V, K^∧)`

extending `H^q(RΓ(V, η_K))` over the completion, and it is bijective. Its documentation records
that the step from there to the sheaf statement looked circular: the tag's left-hand side is the
*cohomology sheaf* `H^q(K^∧)`, whose sections over `V` are not known to be the hypercohomology
`H^q(V, K^∧)` — that identification is the hypercohomology edge isomorphism at `K^∧`, which needs
the cohomology sheaves of `K^∧` to be acyclic on the affine opens, and that is part (5) read at
the very limit sheaf part (2) is about.

**The circle is avoided by not asking for the edge isomorphism at all.** `H^q(V, K^∧)` is the
value over `V` of the degree-`q` hypercohomology *presheaf* of `K^∧`, and the cohomology sheaf
`H^q(K^∧)` is that presheaf's sheafification — `Stacks.Cohomology.HypercohomologyEdge`
`.sheafificationCohomologyPresheafIso`, which carries no acyclicity hypothesis whatever. So the
`c_V` are isomorphisms onto the sections over `V` of a *presheaf* whose sheafification is the
tag's left-hand side, and `Stacks.BasisRestriction.moduleSheafIsoOfBasisSectionsIso` turns exactly
that datum into an isomorphism of sheaves: the `c_V` followed by the sheafification unit glue to a
morphism of sheaves which is *locally* bijective — bijective on the basis it is not, since the
unit is not — and a locally bijective morphism of sheaves of modules is invertible.

**Neither the affine projection formula, nor part (1) of the tag, nor any Mittag-Leffler condition
enters.** All three are named as the obstruction by the route analyses of
`Completion/CohomologyAffineAdicComparison.lean`, `Completion/AffineAdicTowerR1LimVanishing.lean`
and `Completion/AffineDerivedReductionTowerLimit.lean`. **Those analyses are wrong**, and the
error is worth naming: each considers only routes through
`AlgebraicGeometry.RingedSite.adicReductionTower` or through the edge isomorphism at `K^∧`, and
concludes from their failure that the affine projection formula is "the whole of the affine-level
gap". It is not the gap at all. The affine comparison those files already had, plus the fact that
a cohomology sheaf *is* a sheafified hypercohomology presheaf, is enough.

## What the compatibility with restriction needs, and why it is split

The one thing a family of isomorphisms on a basis must satisfy is compatibility with restriction,
which is `Stacks.Algebraization.isCompatibleOnBasisPresheaf_adicQuotientLimitSectionsComparison`.
It is proved from the *uniqueness* half of the affine comparison rather than by inspecting it:
both of the two maps `Γ(V, lim H^q(K)/ℐⁿH^q(K)) ⟶ H^q(W, K^∧)` it compares restrict, along the
completion map, to the same map out of `H^q(V, K)` — because that restriction is in each case the
component over `V` of a *morphism of presheaves* — and a map out of an adic completion is
determined by its restriction along the completion map as soon as the target is separated.

Written as one declaration that proof exceeds the 200000-heartbeat budget at `whnf` on its own
statement, because the two sides are restriction maps between two affine opens of two different
presheaves and the semilinear module structures on their sections have to be reconciled. It is
therefore split: the separatedness of the target is
`Stacks.Algebraization.isAdicComplete_cohomologyPresheaf_derivedCompletion`, the agreement of the
two restrictions is
`Stacks.Algebraization.adicQuotientLimitSectionsComparison_restrict_comp_of`, and the filtration
bookkeeping is `Stacks.Algebraization.mem_pow_smul_top_of_semilinear`; each is stated against
types spelled out in full, and only their assembly is left to the compatibility itself.

## Main results

* `Stacks.Algebraization.cohomologyPresheafUnitToSheaf` — the canonical map from the degree-`q`
  hypercohomology presheaf to the degree-`q` cohomology sheaf, and
  `Stacks.Algebraization.hypercohomologyEdge_eq_sheafificationUnit`, the statement that the edge
  morphism of [Stacks, Tag 0BKT] over an open is its component there. Being a morphism of
  presheaves, its compatibility with restriction is its own naturality.
* `Stacks.Algebraization.homologyToAdicQuotientLimitPresheaf` — the canonical morphism of
  presheaves `H^q(-, K) ⟶ Γ(-, lim H^q(K)/ℐⁿH^q(K))`, and
  `Stacks.Algebraization.adicCompletionHomologyLimitSectionsEquiv_of`: over an affine open it is
  the completion map the affine comparison extends. This is what makes the *pinning* data of the
  affine comparison natural in the open with nothing to prove.
* `Stacks.Algebraization.adicQuotientLimitSectionsComparison` — the affine comparison read into
  the hypercohomology presheaf, with
  `Stacks.Algebraization.adicQuotientLimitSectionsComparison_comp_of` and
  `Stacks.Algebraization.bijective_adicQuotientLimitSectionsComparison`.
* `Stacks.Algebraization.isCompatibleOnBasisPresheaf_adicQuotientLimitSectionsComparison` — the
  compatibility with restriction, and the three declarations it is split over.
* `Stacks.Algebraization.nonempty_iso_homology_derivedCompletion_limit_adicQuotientSystem` —
  **part (2) of the tag**, which carries the attribute.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HypercohomologyEdge
open Stacks.SheafOfModules (opensRingedSite)

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.hasSheafify_opens
  Stacks.SheafOfModules.wEqualsLocallyBijective_opens

/-! The module structures on sections are `local instance`s of
`Completion/IdealPowerQuasicoherent.lean`; they are reactivated here rather than restated. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf sectionsModuleΓSheafPresheaf sectionsModuleΓSheafVal

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
  (K : DerivedCategory X.Modules)

/-! ### The hypercohomology presheaf and its sheafification unit -/

/-- **The canonical map from the degree-`q` hypercohomology presheaf of `E` to its cohomology
sheaf.** It is the unit of sheafification followed by the identification
`Stacks.Cohomology.HypercohomologyEdge.sheafificationCohomologyPresheafIso` of the sheafified
hypercohomology presheaf with the cohomology sheaf, of [Stacks, Tag 0BKV].

This is the hypercohomology edge morphism of [Stacks, Tag 0BKT] assembled over all opens at once:
`Stacks.Algebraization.hypercohomologyEdge_eq_sheafificationUnit` below. The point of having it
as a morphism of presheaves is that its compatibility with restriction is then automatic. -/
def cohomologyPresheafUnitToSheaf (q : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj E) ⟶
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) q).obj E).val :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing X.toRingedSpace).obj)).unit.app _ ≫
    ((sheafificationCohomologyPresheafIso (structureSheafRing X.toRingedSpace) q).hom.app E).val

omit [IsLocallyNoetherian X] in
/-- **The hypercohomology edge morphism over an open is the sheafification unit read there.**
This is the definition of `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge`, with the
two factors other than the unit collected into
`Stacks.Algebraization.cohomologyPresheafUnitToSheaf`. -/
theorem hypercohomologyEdge_eq_sheafificationUnit (q : ℤ) (V : X.Opens)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (hypercohomologyEdge (structureSheafRing X.toRingedSpace) V q).app E =
      (sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V q).inv.app E ≫
        (cohomologyPresheafUnitToSheaf (X := X) q E).app (op V) := rfl


/-! ### The affine comparison as a family, and the canonical map it extends -/

variable (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ)

/-- **The canonical presheaf map `H^q(-, K) ⟶ Γ(-, lim H^q(K)/𝓘ⁿH^q(K))`.** It is the
sheafification unit on the hypercohomology presheaf of `K` — which lands in the cohomology sheaf
`H^q(K)` — followed by the sections of the canonical map
`Stacks.Algebraization.adicQuotientLimitComparison` of `H^q(K)` into the limit of its adic
quotient tower.

Over an affine open this is the map the comparison of
`Stacks.Algebraization.existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion`
extends over the completion — `Stacks.Algebraization.adicCompletionHomologyLimitSectionsEquiv_of`
below — and being a morphism of presheaves it commutes with restriction with nothing to prove. -/
def homologyToAdicQuotientLimitPresheaf :
    (DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj K) ⟶
      (limit (C := X.Modules)
        (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val :=
  cohomologyPresheafUnitToSheaf (X := X) q K ≫
    (adicQuotientLimitComparison X 𝓘 (homologyCoherentModule K hK q)).val

/-- **The completion map over an affine open is the component there of
`Stacks.Algebraization.homologyToAdicQuotientLimitPresheaf`.** The identification
`Stacks.Algebraization.adicCompletionHomologyLimitSectionsEquiv` carries `AdicCompletion.of` to
the sections of the canonical map `H^q(K) ⟶ lim H^q(K)/𝓘ⁿH^q(K)` applied to the image of the
hypercohomology class under the edge morphism, and the edge morphism is the sheafification unit
read over the open. -/
theorem adicCompletionHomologyLimitSectionsEquiv_of (V : X.affineOpens)
    (x : (DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj K) |>.obj (op V.1)) :
    adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q
        (AdicCompletion.of (𝓘.ideal V) _
          ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).hom.app K x)) =
      (homologyToAdicQuotientLimitPresheaf 𝓘 K hK q).app (op V.1) x := by
  have hqcK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent := by
    obtain ⟨P, hP, e⟩ := hK
    exact AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X K ⟨P, hP, e⟩
  have hsev : (sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app K
      ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).hom.app K x) = x :=
    ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).app K).hom_inv_id_apply x
  change (adicQuotientLimitSectionsEquiv X 𝓘 (homologyCoherentModule K hK q) V)
      (AdicCompletion.of (𝓘.ideal V) _
        ((homologyIso_derivedSections_of_isAffineOpen X K hqcK V q).toLinearEquiv
          ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).hom.app K x))) = _
  refine Eq.trans
    (adicQuotientLimitSectionsEquiv_of X 𝓘 (homologyCoherentModule K hK q) V _) ?_
  exact congrArg (fun y => Scheme.Modules.Hom.app
    (adicQuotientLimitComparison X 𝓘 (homologyCoherentModule K hK q)) V.1
      ((cohomologyPresheafUnitToSheaf (X := X) q K).app (op V.1) y)) hsev

/-! ### The affine comparison as a family of maps into the hypercohomology presheaf -/

/-- **The affine comparison of part (2), read into the hypercohomology presheaf of `K^∧`.** Over
affine open `V` this is the unique `Γ(X, V)`-linear map `Γ(V, lim H^q(K)/𝓘ⁿH^q(K)) ⟶ H^q(V, K^∧)`
extending `H^q(RΓ(V, η_K))` over the completion, of
`existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion`, composed with the
identification of `H^q(V, K^∧)` with the value over `V` of the degree-`q` hypercohomology presheaf
of `K^∧`. -/
def adicQuotientLimitSectionsComparison (V : X.affineOpens) :
    ModuleCat.of Γ(X, V.1)
        Γ((limit (C := X.Modules)
          (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)), V.1) ⟶
      ((DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K))).obj (op V.1) :=
  ModuleCat.ofHom
      (existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion
        𝓘 K V hK q).choose ≫
    (sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app _

/-- **The affine comparison restricts along the completion map to `H^q` of the derived
completion unit** — in the presheaf spelling, where both sides are components of morphisms of
presheaves. -/
theorem adicQuotientLimitSectionsComparison_comp_of (V : X.affineOpens)
    (x : ((DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj K)).obj (op V.1)) :
    adicQuotientLimitSectionsComparison 𝓘 K hK q V
        ((homologyToAdicQuotientLimitPresheaf 𝓘 K hK q).app (op V.1) x) =
      ((DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).map
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).map
          ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).app K))).app (op V.1) x := by
  have hnat := (sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).hom.naturality
    ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
      (idealSheafSiteSubmodule 𝓘)).app K)
  have hspec := (existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion
    𝓘 K V hK q).choose_spec.1
    ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).hom.app K x)
  change (sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app _
      ((existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion
        𝓘 K V hK q).choose
          ((homologyToAdicQuotientLimitPresheaf 𝓘 K hK q).app (op V.1) x)) = _
  rw [← adicCompletionHomologyLimitSectionsEquiv_of 𝓘 K hK q V x, hspec]
  refine Eq.trans (congrArg
    ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app _)
    (ConcreteCategory.congr_hom hnat.symm x)) ?_
  exact ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).app _).hom_inv_id_apply
    (((DerivedCategory.homologyFunctor
        (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).map
      ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).map
        ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
          (idealSheafSiteSubmodule 𝓘)).app K))).app (op V.1) x)

/-- The affine comparison is bijective. -/
theorem bijective_adicQuotientLimitSectionsComparison (V : X.affineOpens) :
    Function.Bijective (adicQuotientLimitSectionsComparison 𝓘 K hK q V) := by
  have hb := (existsUnique_bijective_adicQuotientLimitSections_homology_derivedCompletion
    𝓘 K V hK q).choose_spec.2.1
  have hiso : Function.Bijective
      ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app
        ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
          (idealSheafSiteSubmodule 𝓘)).obj K)) :=
    ConcreteCategory.bijective_of_isIso ((sectionsEvaluationIso _ V.1 q).app _).symm.hom
  exact hiso.comp hb

/-! ### An ingredient of the compatibility with restriction -/

/-- **An additive map that is semilinear over a ring map carries the `I`-adic filtration of its
source into the `J`-adic filtration of its target**, as soon as the image of `I` lies in `J`.

This is the semilinear counterpart of `Stacks.Algebraization.pow_smul_top_le_comap`, which is
about a linear map over one ring, and it is what
`Stacks.Algebraization.eq_of_separated_filtration_of_comp_eq` consumes when the two maps compared
are the restriction maps of a presheaf of modules between two affine opens: those are semilinear
over `Γ(X, V) ⟶ Γ(X, W)` and over no smaller ring, and
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` is exactly the hypothesis `hIJ`. -/
theorem mem_pow_smul_top_of_semilinear {A B : Type*} [CommRing A] [CommRing B] (ρ : A →+* B)
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁] {M₂ : Type*} [AddCommGroup M₂] [Module B M₂]
    (g : M₁ →+ M₂) (hg : ∀ (a : A) (y : M₁), g (a • y) = ρ a • g y)
    {I : Ideal A} {J : Ideal B} (hIJ : Ideal.map ρ I ≤ J) (n : ℕ) {x : M₁}
    (hx : x ∈ I ^ n • (⊤ : Submodule A M₁)) :
    g x ∈ J ^ n • (⊤ : Submodule B M₂) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [hg]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    refine Ideal.pow_right_mono hIJ n ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-! ### The two halves of the compatibility, each in its own declaration

The compatibility with restriction is one application of
`Stacks.Algebraization.eq_of_separated_filtration_of_comp_eq`, but written as a single
declaration its *statement* exhausts the heartbeat budget at `whnf`: the two sides are
restriction maps between two affine opens of two different presheaves, and the semilinear module
structures on their sections have to be reconciled. The separatedness of the target and the
agreement of the two restrictions are therefore proved here, against types spelled out in full,
and only the filtration bookkeeping is left to the compatibility itself. -/

include hK in
/-- **The sections over an affine open of the hypercohomology presheaf of `K^∧` are adically
complete.** The affine comparison at that open is a bijection onto them from
`Γ(V, lim H^q(K)/𝓘ⁿH^q(K))`, which
`Stacks.Algebraization.adicCompletionHomologyLimitSectionsEquiv` presents as an adic completion,
and `IsAdicComplete` transports along a linear equivalence. This is what makes the target of the
compatibility separated, which is the hypothesis the uniqueness of an extension over a completion
rests on. -/
theorem isAdicComplete_cohomologyPresheaf_derivedCompletion (V : X.affineOpens) :
    IsAdicComplete (𝓘.ideal V)
      (((DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K))).obj (op V.1)) := by
  refine Stacks.Coherent.isAdicComplete_of_linearEquiv (𝓘.ideal V)
    ((LinearEquiv.ofBijective (adicQuotientLimitSectionsComparison 𝓘 K hK q V).hom
        (bijective_adicQuotientLimitSectionsComparison 𝓘 K hK q V)).symm.trans
      (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q).symm) ?_
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  exact AdicCompletion.isAdicComplete (𝓘.ideal V).fg_of_isNoetherianRing

/-- **The two sides of the compatibility agree on the image of the completion map.** Both are
components of morphisms of presheaves: the completion map over an affine open is the component
there of `Stacks.Algebraization.homologyToAdicQuotientLimitPresheaf`, the affine comparison
restricts along it to `H^q(RΓ(-, η_K))` by
`Stacks.Algebraization.adicQuotientLimitSectionsComparison_comp_of`, and `H^q(RΓ(-, η_K))` is the
component of a morphism of presheaves as well. So the agreement is two naturality squares and no
calculation. -/
theorem adicQuotientLimitSectionsComparison_restrict_comp_of (V W : X.affineOpens)
    (h : W.1 ≤ V.1)
    (x : ((DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj K)).obj (op V.1)) :
    ((DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K))).map (homOfLE h).op
        (adicQuotientLimitSectionsComparison 𝓘 K hK q V
          ((homologyToAdicQuotientLimitPresheaf 𝓘 K hK q).app (op V.1) x)) =
      adicQuotientLimitSectionsComparison 𝓘 K hK q W
        ((limit (C := X.Modules)
            (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val.map (homOfLE h).op
          ((homologyToAdicQuotientLimitPresheaf 𝓘 K hK q).app (op V.1) x)) := by
  refine Eq.trans (congrArg _ (adicQuotientLimitSectionsComparison_comp_of 𝓘 K hK q V x)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply _ (homOfLE h).op x).symm ?_
  refine Eq.trans ?_ (congrArg _
    (PresheafOfModules.naturality_apply (homologyToAdicQuotientLimitPresheaf 𝓘 K hK q)
      (homOfLE h).op x))
  exact (adicQuotientLimitSectionsComparison_comp_of 𝓘 K hK q W _).symm

/-! ### The compatibility with restriction -/

include hK in
/-- **The affine comparisons of part (2) are compatible with restriction between affine opens.**
This is the hypothesis `Stacks.BasisRestriction.moduleSheafIsoOfBasisSectionsIso` consumes.

Both sides are `Γ(X, V)`-semilinear maps out of `Γ(V, lim H^q(K)/𝓘ⁿH^q(K))`, which
`Stacks.Algebraization.adicCompletionHomologyLimitSectionsEquiv` presents as an adic completion,
so `Stacks.Algebraization.eq_of_separated_filtration_of_comp_eq` applies: the filtration
hypothesis is `Stacks.Algebraization.mem_pow_smul_top_of_semilinear` fed with
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`, the separatedness of the target is
`Stacks.Algebraization.isAdicComplete_cohomologyPresheaf_derivedCompletion`, and the agreement of
the two restrictions along the completion map is
`Stacks.Algebraization.adicQuotientLimitSectionsComparison_restrict_comp_of`. -/
theorem isCompatibleOnBasisPresheaf_adicQuotientLimitSectionsComparison :
    Stacks.BasisRestriction.IsCompatibleOnBasisPresheaf
      (limit (C := X.Modules) (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj))
      ((DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K)))
      (fun V : X.affineOpens => V.1)
      (fun V => adicQuotientLimitSectionsComparison 𝓘 K hK q V) := by
  intro V W h s
  have := (isAdicComplete_cohomologyPresheaf_derivedCompletion 𝓘 K hK q W).toIsHausdorff
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨z, rfl⟩ := (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q).surjective s
  have hIJ : Ideal.map (X.presheaf.map (homOfLE h).op).hom (𝓘.ideal V) ≤ 𝓘.ideal W :=
    le_of_eq (Scheme.IdealSheafData.map_ideal 𝓘 (show W ≤ V from h))
  have hs₁ : ∀ (a : Γ(X, V.1)) (y : AdicCompletion (𝓘.ideal V) _),
      ((DerivedCategory.homologyFunctor _ q).obj
          ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
            ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
              (idealSheafSiteSubmodule 𝓘)).obj K))).map (homOfLE h).op
            (adicQuotientLimitSectionsComparison 𝓘 K hK q V
              (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q (a • y))) =
          (X.presheaf.map (homOfLE h).op).hom a •
            ((DerivedCategory.homologyFunctor _ q).obj
              ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
                ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
                  (idealSheafSiteSubmodule 𝓘)).obj K))).map (homOfLE h).op
                (adicQuotientLimitSectionsComparison 𝓘 K hK q V
                  (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q y)) := by
    intro a y
    rw [map_smul, map_smul]
    exact PresheafOfModules.map_smul _ _ _ _
  have hs₂ : ∀ (a : Γ(X, V.1)) (y : AdicCompletion (𝓘.ideal V) _),
      adicQuotientLimitSectionsComparison 𝓘 K hK q W
          ((limit (C := X.Modules)
              (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val.map (homOfLE h).op
            (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q (a • y))) =
        (X.presheaf.map (homOfLE h).op).hom a •
          adicQuotientLimitSectionsComparison 𝓘 K hK q W
            ((limit (C := X.Modules)
                (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val.map
              (homOfLE h).op
              (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q y)) := by
    intro a y
    rw [map_smul]
    refine Eq.trans (congrArg _ (PresheafOfModules.map_smul _ _ _ _)) ?_
    exact map_smul (adicQuotientLimitSectionsComparison 𝓘 K hK q W).hom _ _
  have hof : ∀ m, ((DerivedCategory.homologyFunctor _ q).obj
          ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
            ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
              (idealSheafSiteSubmodule 𝓘)).obj K))).map (homOfLE h).op
            (adicQuotientLimitSectionsComparison 𝓘 K hK q V
              (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q
                (AdicCompletion.of (𝓘.ideal V) _ m))) =
        adicQuotientLimitSectionsComparison 𝓘 K hK q W
          ((limit (C := X.Modules)
              (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val.map (homOfLE h).op
            (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q
              (AdicCompletion.of (𝓘.ideal V) _ m))) := by
    intro m
    have hm : (sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).hom.app K
        ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app K m) = m :=
      ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).app K).inv_hom_id_apply m
    have he : adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q
          (AdicCompletion.of (𝓘.ideal V) _ m) =
        (homologyToAdicQuotientLimitPresheaf 𝓘 K hK q).app (op V.1)
          ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app K m) := by
      rw [← adicCompletionHomologyLimitSectionsEquiv_of 𝓘 K hK q V
        ((sectionsEvaluationIso (structureSheafRing X.toRingedSpace) V.1 q).inv.app K m), hm]
    rw [he]
    exact adicQuotientLimitSectionsComparison_restrict_comp_of 𝓘 K hK q V W h _
  refine (DFunLike.congr_fun (eq_of_separated_filtration_of_comp_eq (𝓘.ideal V)
    (𝓘.ideal V).fg_of_isNoetherianRing
    (fun n => ((𝓘.ideal W) ^ n • (⊤ : Submodule Γ(X, W.1)
        (((DerivedCategory.homologyFunctor _ q).obj
          ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
            ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
              (idealSheafSiteSubmodule 𝓘)).obj K))).obj (op W.1)))).toAddSubgroup)
    (AddMonoidHom.mk' (fun y => ((DerivedCategory.homologyFunctor _ q).obj
        ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K))).map (homOfLE h).op
          (adicQuotientLimitSectionsComparison 𝓘 K hK q V
            (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q y)))
      (fun a b => by simp only [map_add]; try rfl))
    (AddMonoidHom.mk' (fun y => adicQuotientLimitSectionsComparison 𝓘 K hK q W
        ((limit (C := X.Modules)
            (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val.map (homOfLE h).op
          (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q y)))
      (fun a b => by
        refine Eq.trans (congrArg _ (congrArg
          (fun w => (limit (C := X.Modules)
              (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val.map
            (homOfLE h).op w)
          (map_add (adicCompletionHomologyLimitSectionsEquiv 𝓘 K V hK q) a b))) ?_
        refine Eq.trans (congrArg _ (map_add
          ((limit (C := X.Modules)
            (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)).val.map
              (homOfLE h).op).hom _ _)) ?_
        exact map_add (adicQuotientLimitSectionsComparison 𝓘 K hK q W).hom _ _))
    (fun n x hx => Submodule.sub_mem _
      (mem_pow_smul_top_of_semilinear (X.presheaf.map (homOfLE h).op).hom _ hs₁ hIJ n hx)
      (mem_pow_smul_top_of_semilinear (X.presheaf.map (homOfLE h).op).hom _ hs₂ hIJ n hx))
    (fun y hy => IsHausdorff.haus' y fun n => SModEq.zero.2 (hy n)) hof) z).symm

/-! ### Part (2) of the tag -/

include hK in
/-- **Part (2) of [Stacks, Tag 0A0K].** For a pseudo-coherent object `K` of `D(𝒪_X)` on a locally
Noetherian scheme `X` and an arbitrary quasi-coherent sheaf of ideals `𝓘`,

`H^q(K^∧) ≅ lim_n H^q(K)/𝓘ⁿ H^q(K)`.

The isomorphism is `Stacks.BasisRestriction.moduleSheafIsoOfBasisSectionsIso` applied to the
affine comparisons `Stacks.Algebraization.adicQuotientLimitSectionsComparison`, which are
bijective and compatible with restriction, against the unit of sheafification on the degree-`q`
hypercohomology presheaf of `K^∧`; the sheafification of that presheaf is the cohomology sheaf by
[Stacks, Tag 0BKV]. -/
@[stacks 0A0K "part (2), `H^q(K^∧) = lim H^q(K)/𝓘ⁿ H^q(K)`: for a **pseudo-coherent** object `K` \
of `D(𝒪_X)` on a locally Noetherian scheme `X` and an **arbitrary** quasi-coherent sheaf of \
ideals `𝓘`, the degree-`q` cohomology sheaf of the derived completion `K^∧` is isomorphic to the \
inverse limit of the adic quotient tower of the coherent module `H^q(K)`, with nothing further \
assumed — no quasi-compactness of `X`, no generation of `𝓘` by global sections, no \
Mittag-Leffler hypothesis and no appeal to part (1) of the tag. The limit is the same object \
parts (3), (4) and (5) are registered over, `Stacks.Algebraization.adicQuotientSystem`, read at \
the coherent module the tag's own footnote names. The isomorphism is non-canonical in the \
statement only because the source's canonical maps go the other way; it is produced by gluing \
the canonical affine comparisons, which are unique"]
theorem nonempty_iso_homology_derivedCompletion_limit_adicQuotientSystem :
    Nonempty ((DerivedCategory.homologyFunctor X.Modules q).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K) ≅
        limit (C := X.Modules)
          (adicQuotientSystem 𝓘 (homologyCoherentModule K hK q).obj)) := by
  have hb : Opens.IsBasis (Set.range (fun V : X.affineOpens => V.1)) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  have hli : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf (structureSheafRing X.toRingedSpace).obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheafRing X.toRingedSpace).obj)).unit.app
          ((DerivedCategory.homologyFunctor
            (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
            ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
              ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
                (idealSheafSiteSubmodule 𝓘)).obj K))))) :=
    PresheafOfModules.isLocallyInjective_sheafificationAdjunction_unit_app
      (α := 𝟙 (structureSheafRing X.toRingedSpace).obj) _
  have hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf (structureSheafRing X.toRingedSpace).obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheafRing X.toRingedSpace).obj)).unit.app
          ((DerivedCategory.homologyFunctor
            (PresheafOfModules.{u} (structureSheafRing X.toRingedSpace).obj) q).obj
            ((derivedSectionsPresheaf (structureSheafRing X.toRingedSpace)).obj
              ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
                (idealSheafSiteSubmodule 𝓘)).obj K))))) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
      (α := 𝟙 (structureSheafRing X.toRingedSpace).obj) _
  refine ⟨(Iso.trans (Stacks.BasisRestriction.moduleSheafIsoOfBasisSectionsIso _ _ _
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheafRing X.toRingedSpace).obj)).unit.app _)
      (fun V : X.affineOpens => V.1)
      (fun V => adicQuotientLimitSectionsComparison 𝓘 K hK q V) hb
      (isCompatibleOnBasisPresheaf_adicQuotientLimitSectionsComparison 𝓘 K hK q)
      (fun V => bijective_adicQuotientLimitSectionsComparison 𝓘 K hK q V) hli hls)
    ((sheafificationCohomologyPresheafIso (structureSheafRing X.toRingedSpace) q).app
      ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
        (idealSheafSiteSubmodule 𝓘)).obj K))).symm⟩

end Stacks.Algebraization

end
