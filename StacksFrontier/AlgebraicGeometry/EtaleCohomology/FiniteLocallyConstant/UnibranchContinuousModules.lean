module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.UniversalHomeomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# Locally constant module sheaves on a geometrically unibranch scheme

Let `X` be an irreducible, geometrically unibranch scheme, let `x` be a geometric point of `X` and
let `Λ` be a ring. Stacks Tag 0GIY asserts that the finite type locally constant sheaves of
`Λ`-modules on `X_étale` are equivalent to the finite `Λ`-modules endowed with a continuous
`π₁(X, x)`-action.

This module sets up both categories, proves the group-theoretic step at which the finite type
hypothesis enters, transports the category of continuous modules along an isomorphism of
topological groups, and carries out the source's reduction of the tag to the case of the
normalization.

## Main definitions

* `Stacks.ConstantSheaf.FiniteTypeLocallyConstantModuleCategory` — the finite type locally constant
  sheaves of `Λ`-modules on a site, as a full subcategory of all sheaves of `Λ`-modules. This is
  the left-hand side of the tag, for `Λ` an arbitrary ring.
* `Stacks.GroupCohomology.FiniteTypeContinuousModule` — the finite `Λ`-modules with a continuous
  `G`-action, as the full subcategory of the `Λ`-`G`-modules of Tag 04JP whose underlying module
  is finitely generated. This is the right-hand side of the tag.
* `Stacks.GroupCohomology.continuousModuleKer` — the subgroup of elements acting trivially on a
  `Λ`-`G`-module.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleResEquiv` — restriction of finite type
  continuous modules along an isomorphism of topological groups.
* `AlgebraicGeometry.Scheme.normalizationSchemeOfIrreducible` and
  `AlgebraicGeometry.Scheme.normalizationOfIrreducible` — the normalization of an irreducible
  scheme, which is defined because the quasi-compact opens of such a scheme have finitely many
  irreducible components.

## Main results

* `Stacks.GroupCohomology.isOpen_continuousModuleKer` and
  `Stacks.GroupCohomology.exists_isOpen_normal_subgroup_ρ_eq_one` — a finite `Λ`-module with a
  continuous `G`-action is acted on through a discrete quotient: the elements acting trivially form
  an open normal subgroup. This is the step "pick generators `m_1, …, m_r`; by continuity there are
  open subgroups fixing each of them; their intersection is open and fixes `M`" of the source's
  construction, and it is where the finite type hypothesis is used.
* `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModuleOfComparison` — the tag for `X`
  follows from the tag for a scheme `Y` whose finite type locally constant module category is
  equivalent to that of `X` and whose fundamental group is isomorphic to that of `X`.
* `AlgebraicGeometry.finiteTypeLocallyConstantEquivContinuousModule` — **Tag 0GIY** in the
  restricted form described below.

## No unrestricted `@[stacks 0GIY]`

The tag is carried in a restricted form: its geometric input is taken as hypotheses. What the
declaration proves is the source's first reduction. Geometric unibranchness and irreducibility are
used to produce the universal homeomorphism `ν : X^ν → X` of Tag 0GIQ
(`AlgebraicGeometry.Scheme.universalHomeomorphism_normalization`), the hypothesis on the locally
constant categories is instantiated at it, the fundamental group comparison is derived from the
hypothesis that base change along `ν` is an equivalence of finite étale covers, and the resulting
equivalences are composed with the transport of the continuous module category along that
comparison. The hypotheses are, by tag number:

* **0BQN** — that base change along a universal homeomorphism is an equivalence of finite étale
  covers. Only faithfulness of the base change functor is available
  (`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_universalHomeomorphism`); fullness and
  essential surjectivity, for which the source invokes Tag 0BTP, are not. Carried here as the
  instance hypothesis `[(finiteEtaleBaseChange (Scheme.normalizationOfIrreducible X.obj))
  .IsEquivalence]`. The isomorphism `π₁(X^ν, x^ν) ≅ π₁(X, x)` of topological groups is *not* a
  hypothesis: it is deduced from this by Tag 0BQA part (2),
  `AlgebraicGeometry.etaleFundamentalGroupContinuousMulEquivOfIsEquivalence`.
* **04DZ** — the topological invariance of the small étale site, which is what identifies the
  finite type locally constant module categories of `X` and `X^ν`. There is no `@[stacks 04DZ]`
  declaration in this library. Carried here as `hinvariance`.
* That the geometric point `x` of `X` lifts to the normalization, carried here as `xν` together
  with `hx`. Every point does lift, `ν` being surjective
  (`AlgebraicGeometry.Scheme.surjective_normalization`), but lifting a *geometric* point needs the
  residue field extension, which is not assembled here. Without the lift the statement would have
  to invoke the change of base point of Tag 0BND part (2), which is itself conditional in this
  library.
* **0GIY itself for an integral normal scheme** — the source's Steps 2 and 3. Carried here as
  `hnormal`. Its own inputs are in mixed shape: the surjection
  `Gal(κ(η)^{sep}/κ(η)) = π₁(η, η̄) → π₁(X, η̄)` of **0BQM** is available
  (`AlgebraicGeometry.surjective_galoisToFundamentalGroup`), the description of its kernel in
  **0BTD** is available only in the incomplete forms recorded in
  `StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalKernelLocalRings`, and **0BQI** has no
  declaration in this library. The construction of the sheaf attached to a module,
  `F = f_*Z ⊗_{Z[G]} M` for `f : Y → X` the Galois cover with group `G = π₁(X, η̄)/H`, needs the
  dictionary of **03RV** between finite locally constant sheaves and finite étale covers, which is
  available only granted effective descent along an étale covering, Tag **0245**
  (`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent`),
  together with descent of `Λ`-modules along a Galois cover, Section **03QW**, of which there is
  nothing here.

Sizes, as a rough guide: the lift of the geometric point is a short argument from surjectivity of
the normalization; 04DZ is a self-contained site-theoretic statement; the missing half of 0BQN
rests on 0BTP; the normal case 0GIY for integral normal schemes is the bulk of the tag and rests
on 03RV, 0245 and 03QW.

## Implementation notes

The approach of Tag 0DV5, which is carried in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModules` for abelian sheaves, does
not apply: the source observes that "a finite `Λ`-module may not have a finite underlying set", so
the finiteness condition on the two sides of 0GIY is not the one 0DV5 transports. Accordingly
nothing here is obtained from that module, and the finiteness property used on the module side is
`ModuleCat.isFG`, not finiteness of the underlying set.

`Λ` is an arbitrary ring, as in the source. The left-hand category is therefore built from
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`, whose coefficient ring is arbitrary and whose
module universe is free, rather than from
`AlgebraicGeometry.FiniteTypeLocallyConstantModuleSheaves`, which additionally assumes `Λ`
commutative and Noetherian. The right-hand category is built from
`Stacks.Injectives.ContinuousModule`, the spelling of Tag 04JP.

The restriction equivalence
`Stacks.GroupCohomology.finiteTypeContinuousModuleResEquiv` is obtained from Mathlib's
`ContAction.resEquiv` by restricting twice along
`CategoryTheory.Equivalence.congrFullSubcategory`: once to the discrete actions and once to the
finite type ones. Both restrictions are identities on underlying objects, so both comparisons of
properties hold by definitional unfolding.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v v' w c cv r

namespace Stacks.GroupCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

local instance isClosedUnderIsomorphisms_moduleCatIsFG (R : Type u) [Ring R] :
    (ModuleCat.isFG.{w} R).IsClosedUnderIsomorphisms where
  of_iso {X _Y} e hX :=
    have : Module.Finite R X := hX
    Module.Finite.equiv e.toLinearEquiv

local instance isClosedUnderIsomorphisms_isDiscrete (R : Type u) [Ring R] (G : Type v)
    [Group G] [TopologicalSpace G] :
    (show ObjectProperty (ContAction (ModuleCat.{w} R) G) from
      ContAction.IsDiscrete).IsClosedUnderIsomorphisms where
  of_iso _ _ := ⟨rfl⟩

section Kernel

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The subgroup of elements acting trivially on an `R`-`G`-module. -/
public def continuousModuleKer (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    Subgroup G where
  carrier := {g | M.obj.obj.ρ g = 1}
  mul_mem' {a b} ha hb := show M.obj.obj.ρ (a * b) = 1 by
    rw [map_mul, show M.obj.obj.ρ a = 1 from ha, show M.obj.obj.ρ b = 1 from hb, one_mul]
  one_mem' := show M.obj.obj.ρ 1 = 1 from map_one M.obj.obj.ρ
  inv_mem' {a} ha := show M.obj.obj.ρ a⁻¹ = 1 by
    calc M.obj.obj.ρ a⁻¹ = M.obj.obj.ρ a⁻¹ * M.obj.obj.ρ a := by
          rw [show M.obj.obj.ρ a = 1 from ha, mul_one]
      _ = M.obj.obj.ρ (a⁻¹ * a) := (map_mul _ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, map_one]

/-- Membership in `Stacks.GroupCohomology.continuousModuleKer` is acting trivially. -/
public theorem mem_continuousModuleKer_iff
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) (g : G) :
    g ∈ continuousModuleKer R G M ↔ M.obj.obj.ρ g = 1 := Iff.rfl

/-- The elements acting trivially on an `R`-`G`-module form a normal subgroup. -/
public instance normal_continuousModuleKer
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    (continuousModuleKer R G M).Normal where
  conj_mem n hn g := by
    rw [mem_continuousModuleKer_iff] at hn ⊢
    rw [map_mul, map_mul, hn, mul_one, ← map_mul, mul_inv_cancel, map_one]

/-- **The elements acting trivially on a finite type `R`-`G`-module form an open subgroup.**
The module is generated by finitely many elements, each of which has open stabilizer because the
action is continuous and the module discrete; the intersection of those finitely many stabilizers
is an open neighbourhood of `1` contained in the subgroup. -/
public theorem isOpen_continuousModuleKer [IsTopologicalGroup G]
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (hM : ModuleCat.isFG R M.obj.obj.V) :
    IsOpen (continuousModuleKer R G M : Set G) := by
  have hfin : Module.Finite R M.obj.obj.V := hM
  obtain ⟨S, hS, hspan⟩ := Submodule.fg_def.mp (Module.finite_def.mp hfin)
  refine (continuousModuleKer R G M).isOpen_of_one_mem_interior
    (mem_interior.mpr ⟨⋂ x ∈ S, {g : G | (M.obj.obj.ρ g).hom x = x}, ?_, ?_, ?_⟩)
  · intro g hg
    simp only [Set.mem_iInter] at hg
    refine (mem_continuousModuleKer_iff R G M g).mpr (ModuleCat.hom_ext ?_)
    rw [show (1 : End M.obj.obj.V) = 𝟙 _ from rfl, ModuleCat.hom_id]
    exact LinearMap.ext_on hspan fun x hx => hg x hx
  · exact hS.isOpen_biInter fun x _ => isOpen_stabilizer R G M x
  · exact Set.mem_iInter₂.mpr fun x _ => by simp

/-- **A finite type `R`-`G`-module is acted on through a finite discrete quotient.** There is an
open normal subgroup of `G` acting trivially on it: this is the step at which the finite type
hypothesis is used. -/
public theorem exists_isOpen_normal_subgroup_ρ_eq_one [IsTopologicalGroup G]
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (hM : ModuleCat.isFG R M.obj.obj.V) :
    ∃ H : Subgroup G, H.Normal ∧ IsOpen (H : Set G) ∧ ∀ g ∈ H, M.obj.obj.ρ g = 1 :=
  ⟨continuousModuleKer R G M, normal_continuousModuleKer R G M,
    isOpen_continuousModuleKer R G M hM, fun _ hg => hg⟩

end Kernel

section FiniteType

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying `R`-module of an `R`-`G`-module. -/
public abbrev continuousModuleToModuleCat :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Action.forget (ModuleCat.{w} R) G

/-- Finite generation of the underlying module, as a property of `R`-`G`-modules. -/
public abbrev continuousModuleIsFG :
    ObjectProperty (Stacks.Injectives.ContinuousModule.{u, v, w} R G) :=
  (ModuleCat.isFG.{w} R).inverseImage (continuousModuleToModuleCat.{u, v, w} R G)

/-- An `R`-`G`-module is of finite type exactly when its underlying module is finitely
generated. -/
public theorem continuousModuleIsFG_iff
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    continuousModuleIsFG.{u, v, w} R G M ↔ Module.Finite R M.obj.obj.V := Iff.rfl

/-- **Finite `R`-modules with a continuous `G`-action.** The full subcategory of the `R`-`G`-modules
of Tag 04JP whose underlying `R`-module is finitely generated. In the terminology of the Stacks
project these are the finite `R`-modules endowed with a continuous `G`-action. -/
public abbrev FiniteTypeContinuousModule :=
  (continuousModuleIsFG.{u, v, w} R G).FullSubcategory

/-- The inclusion of the finite type `R`-`G`-modules into all `R`-`G`-modules. -/
public abbrev finiteTypeContinuousModuleι :
    FiniteTypeContinuousModule.{u, v, w} R G ⥤
      Stacks.Injectives.ContinuousModule.{u, v, w} R G :=
  (continuousModuleIsFG.{u, v, w} R G).ι

/-- Every object of `Stacks.GroupCohomology.FiniteTypeContinuousModule` is acted on through a
finite discrete quotient: there is an open normal subgroup acting trivially. -/
public theorem exists_isOpen_normal_subgroup_ρ_eq_one_finiteType [IsTopologicalGroup G]
    (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    ∃ H : Subgroup G, H.Normal ∧ IsOpen (H : Set G) ∧ ∀ g ∈ H, M.obj.obj.obj.ρ g = 1 :=
  exists_isOpen_normal_subgroup_ρ_eq_one R G M.obj M.property

end FiniteType

section Res

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G]
  {H : Type v'} [Group H] [TopologicalSpace H]

/-- **Restriction of `R`-`G`-modules along an isomorphism of topological groups.** The
`R`-`H`-modules are the `R`-`G`-modules, read through `e`. -/
public def continuousModuleResEquiv (e : G ≃ₜ* H) :
    Stacks.Injectives.ContinuousModule.{u, v', w} R H ≌
      Stacks.Injectives.ContinuousModule.{u, v, w} R G :=
  (ContAction.resEquiv (ModuleCat.{w} R) e).congrFullSubcategory rfl

/-- **Restriction of finite type `R`-`G`-modules along an isomorphism of topological groups.**
Restriction does not change the underlying module, so it preserves finite generation. -/
public def finiteTypeContinuousModuleResEquiv (e : G ≃ₜ* H) :
    FiniteTypeContinuousModule.{u, v', w} R H ≌ FiniteTypeContinuousModule.{u, v, w} R G :=
  (continuousModuleResEquiv.{u, v, v', w} R e).congrFullSubcategory (by funext M; rfl)

end Res

end Stacks.GroupCohomology

namespace Stacks.ConstantSheaf

variable (R : Type r) [Ring R] {C : Type c} [Category.{cv} C] (J : GrothendieckTopology C)
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]

/-- Local constancy of finite type, as a property of sheaves of `R`-modules on a site. -/
public abbrev isFiniteTypeLocallyConstantModuleProperty :
    ObjectProperty (Sheaf J (ModuleCat.{w} R)) :=
  IsFiniteTypeLocallyConstant R J

/-- **The finite type locally constant sheaves of `R`-modules on a site**, as a full subcategory
of all sheaves of `R`-modules on it. -/
public abbrev FiniteTypeLocallyConstantModuleCategory :=
  (isFiniteTypeLocallyConstantModuleProperty R J).FullSubcategory

/-- The inclusion of the finite type locally constant sheaves of `R`-modules into all sheaves of
`R`-modules. -/
public abbrev finiteTypeLocallyConstantModuleCategoryι :
    FiniteTypeLocallyConstantModuleCategory R J ⥤ Sheaf J (ModuleCat.{w} R) :=
  (isFiniteTypeLocallyConstantModuleProperty R J).ι

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

open Stacks.ConstantSheaf Stacks.GroupCohomology

/-- The normalization of an irreducible scheme, which is defined because every quasi-compact open
of an irreducible scheme has finitely many irreducible components. -/
public abbrev Scheme.normalizationSchemeOfIrreducible (X : Scheme.{u}) [IrreducibleSpace X] :
    Scheme.{u} :=
  Scheme.normalizationScheme X (Scheme.finite_irreducibleComponents_of_irreducibleSpace X)

/-- The normalization morphism of an irreducible scheme. -/
public abbrev Scheme.normalizationOfIrreducible (X : Scheme.{u}) [IrreducibleSpace X] :
    Scheme.normalizationSchemeOfIrreducible X ⟶ X :=
  Scheme.normalization X (Scheme.finite_irreducibleComponents_of_irreducibleSpace X)

/-- **Transport of the correspondence between finite type locally constant module sheaves and
finite type continuous modules along a comparison of schemes.** If the finite type locally
constant sheaves of `Λ`-modules on `X_étale` are equivalent to those on `Y_étale`, if the latter
are equivalent to the finite `Λ`-modules with a continuous action of `π₁(Y, y)`, and if `π₁(Y, y)`
is isomorphic as a topological group to `π₁(X, x)`, then the finite type locally constant sheaves
of `Λ`-modules on `X_étale` are equivalent to the finite `Λ`-modules with a continuous action of
`π₁(X, x)`.

This is the formal content of the first reduction in the proof of Stacks Tag 0GIY: the statement
for `X` follows from the statement for a scheme `Y` comparable to it in this way. -/
public def finiteTypeLocallyConstantEquivContinuousModuleOfComparison
    (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.obj] (x : GeometricPoint X.obj)
    (Y : B.Scheme) [ConnectedSpace Y.obj] (y : GeometricPoint Y.obj)
    (Λ : Type r) [Ring Λ]
    [∀ V : SmallEtale B X.obj X.property,
      HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) (ModuleCat.{w} Λ)]
    [∀ V : SmallEtale B Y.obj Y.property,
      HasWeakSheafify ((SmallEtale.topology B Y.obj Y.property).over V) (ModuleCat.{w} Λ)]
    (eF : FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B X.obj X.property) ≌
      FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B Y.obj Y.property))
    (eN : FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B Y.obj Y.property) ≌
      FiniteTypeContinuousModule Λ (EtaleFundamentalGroup Y.obj y))
    (φ : EtaleFundamentalGroup Y.obj y ≃ₜ* EtaleFundamentalGroup X.obj x) :
    FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B X.obj X.property) ≌
      FiniteTypeContinuousModule Λ (EtaleFundamentalGroup X.obj x) :=
  eF.trans (eN.trans (finiteTypeContinuousModuleResEquiv Λ φ).symm)

/-- **Stacks Project, Tag 0GIY.** Let `X` be an irreducible, geometrically unibranch scheme, let
`x` be a geometric point of `X` and let `Λ` be a ring. The finite type locally constant sheaves of
`Λ`-modules on `X_étale` are equivalent to the finite `Λ`-modules endowed with a continuous
`π₁(X, x)`-action.

The source proves this by reducing to the case of an integral normal scheme along the
normalization `ν : X^ν → X`, which is a universal homeomorphism by Tag 0GIQ precisely because `X`
is irreducible and geometrically unibranch. That reduction is what is carried out here: the
geometric unibranchness is used to produce the universal homeomorphism, the equivalence of the
finite type locally constant module categories of `X` and `X^ν` is instantiated at it, the
isomorphism `π₁(X^ν, x^ν) ≅ π₁(X, x)` is obtained from the hypothesis that base change along `ν`
is an equivalence of finite étale covers — the content of Tag 0BQN — through Tag 0BQA part (2),
and the tag itself for the normalization is a hypothesis. See the module docstring for the gaps by
tag number. -/
@[stacks 0GIY "the equivalence, with the geometric input carried as hypotheses. Proved here: the \
source's reduction along the normalization — geometric unibranchness yields the universal \
homeomorphism of Tag 0GIQ, at which the hypothesis on the locally constant categories is \
instantiated; the fundamental group comparison is derived from the hypothesis that base change on \
finite étale covers along the normalization is an equivalence, which is the content of Tag 0BQN, \
by Tag 0BQA part (2); and the category of finite type continuous modules is \
transported along that comparison. Carried as hypotheses, none of them proved in this library: \
that base change on finite étale covers along a universal homeomorphism is an equivalence (Tag \
0BQN, of which only faithfulness is available, the rest resting on Tag 0BTP), that a universal \
homeomorphism induces an equivalence of the finite type locally constant module categories (Tag \
04DZ), the existence of a lift of the geometric point to the normalization, and the tag itself \
for the normalization, i.e. for an integral normal scheme (Tags 0BQM, 0BTD, 0BQI, 03RV, 0245, \
03QW)"]
public def finiteTypeLocallyConstantEquivContinuousModule
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IrreducibleSpace X.obj]
    (hX : IsGeometricallyUnibranch X.obj) (x : GeometricPoint X.obj)
    (Λ : Type r) [Ring Λ]
    [∀ V : SmallEtale B X.obj X.property,
      HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) (ModuleCat.{w} Λ)]
    (hν : B.Contains (Scheme.normalizationSchemeOfIrreducible X.obj))
    [ConnectedSpace (Scheme.normalizationSchemeOfIrreducible X.obj)]
    [∀ V : SmallEtale B (Scheme.normalizationSchemeOfIrreducible X.obj) hν,
      HasWeakSheafify
        ((SmallEtale.topology B (Scheme.normalizationSchemeOfIrreducible X.obj) hν).over V)
        (ModuleCat.{w} Λ)]
    [(finiteEtaleBaseChange (Scheme.normalizationOfIrreducible X.obj)).IsEquivalence]
    (xν : GeometricPoint (Scheme.normalizationSchemeOfIrreducible X.obj))
    (hx : xν.map (Scheme.normalizationOfIrreducible X.obj) = x)
    (hinvariance : UniversalHomeomorphism (Scheme.normalizationOfIrreducible X.obj) →
      (FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B X.obj X.property) ≌
        FiniteTypeLocallyConstantModuleCategory Λ
          (SmallEtale.topology B (Scheme.normalizationSchemeOfIrreducible X.obj) hν)))
    (hnormal : FiniteTypeLocallyConstantModuleCategory Λ
        (SmallEtale.topology B (Scheme.normalizationSchemeOfIrreducible X.obj) hν) ≌
      FiniteTypeContinuousModule Λ
        (EtaleFundamentalGroup (Scheme.normalizationSchemeOfIrreducible X.obj) xν)) :
    FiniteTypeLocallyConstantModuleCategory Λ (SmallEtale.topology B X.obj X.property) ≌
      FiniteTypeContinuousModule Λ (EtaleFundamentalGroup X.obj x) := by
  subst hx
  exact finiteTypeLocallyConstantEquivContinuousModuleOfComparison B X _
    (B.obj (Scheme.normalizationSchemeOfIrreducible X.obj) hν) xν Λ
    (hinvariance (Scheme.universalHomeomorphism_normalization X.obj hX)) hnormal
    (etaleFundamentalGroupContinuousMulEquivOfIsEquivalence
      (Scheme.normalizationOfIrreducible X.obj) xν)

end AlgebraicGeometry

end
