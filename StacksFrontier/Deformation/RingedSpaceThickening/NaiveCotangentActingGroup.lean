module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtZero
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCanonicalExtZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSite
public import StacksFrontier.Deformation.RingedSpaceThickening.PulledNaiveCotangentTwoTerm
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep
import StacksCore.Tactic.StacksAttribute

/-!
# The acting group of clause (2) of Stacks 08U8

Let `g : (X₂, 𝒪_{X₂}) ⟶ (X₁, 𝒪_{X₁})` and `f₁ : (X₁, 𝒪_{X₁}) ⟶ (S₁, 𝒪_{S₁})` be morphisms of
ringed spaces and let `𝒢₂` be an `𝒪_{X₂}`-module.  Clause (2) of **Stacks 08U8** asserts that
the morphisms `X'₂ ⟶ X'₁` filling the source's diagram form a principal homogeneous space
under a group it writes three ways,

`Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂) = Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)
  = Ext⁰_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`.

The principal homogeneous space structure itself is
`Deformation.ToposThickening.LiftDiagram.existsUnique_translateHom`
(`StacksFrontier/Deformation/ToposThickening/LiftingDerivationGroup.lean`), which assumes nothing
and acts by the first group of the display, `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`; both clauses
together are
`AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstruction_and_principalHomogeneousSpace`
(`StacksFrontier/Deformation/RingedSpaceThickening/LiftingObstructionBothClauses.lean`).  That same
torsor structure, read on the `Ext`-side group `Hom(H⁰(NL(α)), 𝒢₂)` written as the `Hom` out of
the cokernel of the differential of a two-term structure, is
`AlgebraicGeometry.RingedSpaceThickening.existsUnique_liftTranslate`
(`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentLiftingObstruction.lean`).  Read
at the two-term structure
`pulledNaiveCotangentTwoTerm g f₁` of `g^*𝖭𝖫_{X₁/S₁}` that group is
`Hom_{𝒪_{X₂}}(coker (g^*(conormal map)), 𝒢₂)`, and this file identifies it with each of the
three groups of the source's display.

## Main definitions

* `CategoryTheory.Adjunction.cokernelHomAddEquiv`: for an adjunction `F ⊣ R` of additive
  functors between preadditive categories and a morphism `d`, the additive identification
  `Hom(coker (F d), G) = Hom(coker d, R G)`.  Both sides are the homomorphisms out of the
  codomain of `d` that kill `d`, so no exactness or preservation of colimits is needed.
* `CategoryTheory.Iso.precompHomAddEquiv`: precomposition with an isomorphism as an additive
  identification, for a merely preadditive ambient category.
* `Stacks.SheafOfModules.canonicalConormalCokernelAdjEquiv`: that identification combined with
  `Stacks.SheafOfModules.canonicalConormalCokernelIsoDifferentials` — the cokernel of the
  conormal map of the canonical polynomial presentation of `B` over `A` is `Ω_{B/A}`, the
  degree `0` half of **Stacks 08TY**, proved in
  `StacksFrontier/CategoryTheory/Sites/Modules/NaiveCotangentCanonicalExtZero.lean` — at the level
  of sheaves of rings on a site.
* `AlgebraicGeometry.RingedSpaceThickening.pulledModuleAdjunction`: the adjunction `g^* ⊣ g_*`
  of sheaves of modules on ringed spaces, in the spelling in which `g^*𝖭𝖫_{X₁/S₁}` is built —
  inverse image of modules followed by extension of scalars, adjoint to restriction of scalars
  followed by pushforward of modules.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.actingGroupEquivPushforward`: **Stacks 08U8**,
  clause (2), the acting group is `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`.
* `AlgebraicGeometry.RingedSpaceThickening.actingGroupEquivPullback`: **Stacks 08U8**,
  clause (2), the acting group is `Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)`.
* `AlgebraicGeometry.RingedSpaceThickening.twoTermExtZeroAddEquivCokernel` and
  `extZeroPulledNaiveCotangentAddEquiv`: **Stacks 08U8**, clause (2), the acting group is
  `Ext⁰_{𝒪_{X₂}}(g^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`.

## Implementation notes

Nothing is assumed: the three identifications are constructed, not quantified over.

`Ω_{X₁/S₁}` is `moduleOfDifferentialsOfSite` of the structure map `f₁⁻¹𝒪_{S₁} ⟶ 𝒪_{X₁}`, the
spelling in which `𝖭𝖫_{X₁/S₁}` is built; it is the open-cover-site sheaf of relative
differentials `AlgebraicGeometry.SheafOfModules.moduleOfDifferentials` by
`moduleOfDifferentialsOfSite_eq_moduleOfDifferentials`.

The first identification goes through `Adjunction.cokernelHomAddEquiv` rather than through
`coker (g^* d) ≅ g^*(coker d)`: the universal property of the cokernel plus the hom-set
bijection suffices, and no preservation of colimits by `g^*` has to be invoked.  The second is
then the hom-set bijection at `Ω_{X₁/S₁}` itself.

The site-level `canonicalConormalCokernelAdjEquiv` is stated for an arbitrary adjunction out of
the category of `B`-modules and instantiated at `pulledModuleAdjunction g`, rather than
assembled at the ringed space.  This is forced: at a concrete ringed space the two spellings of
`coker (conormal map of the canonical presentation)` — the one Lean synthesises for a written
type and the one carried by the site-level isomorphism — do not join within the heartbeat
budget, while the same composite formed once at the generic site costs nothing.  The same
consideration puts the `Ext⁰` identification in the generic form
`twoTermExtZeroAddEquivCokernel`, with `extZeroPulledNaiveCotangentAddEquiv` its instance at
`pulledNaiveCotangentTwoTerm g f₁` and its type left to be inferred.

### Scope

The source writes the third group with the *derived* pullback `Lg^*𝖭𝖫_{X₁/S₁}`; what appears
here is the degreewise pullback `g^*𝖭𝖫_{X₁/S₁}` of
`Stacks.SheafOfModules.pulledNaiveCotangentComplex`, as throughout the forms of
**Stacks 0GQ1** and **Stacks 0GQ7** in this library, for the reason recorded in the
implementation notes of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedExt.lean`: the library does
not identify the degreewise pullback of `𝖭𝖫` in the spelling the comparison `Lg^*K ⟶ g^*K` of
**Stacks 06YJ** uses with the spelling the base change map of **Stacks 0E1Y** uses.

That divergence is confined to the `Ext⁰` re-spelling and does not reach the statement of
clause (2).  The source displays the acting group three ways and calls the equalities
"immediate from the definitions"; the first of the three,
`Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`, mentions no pullback at all, derived or degreewise, and it
is the group that `Deformation.ToposThickening.LiftDiagram.existsUnique_translateHom`
(`StacksFrontier/Deformation/ToposThickening/LiftingDerivationGroup.lean`) proves the morphisms
`X'₂ ⟶ X'₁` to be a principal homogeneous space under, with nothing assumed.  So clause (2)
is proved for a group the source itself names, and `actingGroupEquivPushforward` below is the
bridge from it to the `Hom` out of a cokernel.  The `Ext⁰` group formed with the source's own
*derived* pullback is that same group, and
`AlgebraicGeometry.RingedSpaceThickening.extZeroDerivedPullbackNaiveCotangentAddEquiv`
(`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedPullbackActingGroup.lean`)
identifies the two, with nothing assumed beyond the two morphisms of ringed spaces: it computes
`Ext⁰` out of `Lg^*𝖭𝖫_{X₁/S₁}` from a K-flat resolution directly, and so needs neither the
comparison map above nor the flatness that the source's reduction step invokes.  The whole of
the source's three-way display is therefore proved; what the degreewise reading below adds is
the form of the group carried by the two-term structure `pulledNaiveCotangentTwoTerm g f₁`.

Nothing below claims clause (1) of **Stacks 08U8**, nor Steps 1 to 3 of its proof.  Those are
proved elsewhere, and assumed nowhere: the bijection between the morphisms `X'₂ ⟶ X'₁` and the
factorizations of the difference homomorphism is
`Deformation.ToposThickening.LiftDiagram.nonempty_lift_iff_exists_factorization`, and clause (1)
at the canonical class is
`AlgebraicGeometry.RingedSpaceThickening.liftDiagramObstructionClass_eq_zero_iff`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), `H⁰(NL(α)) = Ω_{B/A}`
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096), `g^* ⊣ g_*`
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension and
  restriction of scalars
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.Adjunction

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R) [F.Additive]
  {M₀ M₁ : A} (d : M₀ ⟶ M₁) [HasCokernel d] [HasCokernel (F.map d)] (G : B)

omit [HasCokernel d] in
/-- The transpose of a homomorphism out of `coker (F d)` kills `d`. -/
theorem comp_homEquiv_eq_zero (k : cokernel (F.map d) ⟶ G) :
    d ≫ adj.homEquiv M₁ G (cokernel.π (F.map d) ≫ k) = 0 := by
  rw [← adj.homEquiv_naturality_left, ← Category.assoc, cokernel.condition, zero_comp,
    adj.homAddEquiv_zero]

omit [HasCokernel (F.map d)] in
/-- The transpose of a homomorphism out of `coker d` with values in `R G` kills `F d`. -/
theorem comp_homEquiv_symm_eq_zero (l : cokernel d ⟶ R.obj G) :
    F.map d ≫ (adj.homEquiv M₁ G).symm (cokernel.π d ≫ l) = 0 := by
  rw [← adj.homEquiv_naturality_left_symm, ← Category.assoc, cokernel.condition, zero_comp,
    adj.homAddEquiv_symm_zero]

/-- **Adjunction on the cokernel.** For an adjunction `F ⊣ R` of additive functors between
preadditive categories and a morphism `d` of the source category, the homomorphisms out of
`coker (F d)` are the homomorphisms out of `coker d` with values in `R` of the target: both
are the homomorphisms out of the codomain of `d` killing `d`, matched by the hom-set
bijection. -/
def cokernelHomAddEquiv : (cokernel (F.map d) ⟶ G) ≃+ (cokernel d ⟶ R.obj G) where
  toFun k := cokernel.desc d _ (comp_homEquiv_eq_zero adj d G k)
  invFun l := cokernel.desc (F.map d) _ (comp_homEquiv_symm_eq_zero adj d G l)
  left_inv k := by
    refine (cancel_epi (cokernel.π (F.map d))).1 ?_
    rw [cokernel.π_desc, cokernel.π_desc, Equiv.symm_apply_apply]
  right_inv l := by
    refine (cancel_epi (cokernel.π d)).1 ?_
    rw [cokernel.π_desc, cokernel.π_desc, Equiv.apply_symm_apply]
  map_add' k₁ k₂ := by
    refine (cancel_epi (cokernel.π d)).1 ?_
    simp only [Preadditive.comp_add, cokernel.π_desc, adj.homAddEquiv_add]

/-- Precomposition with an isomorphism, as an isomorphism of additive groups. This is
`StacksDraft.TwoTermExt.precompAddEquiv` without the hypothesis that the ambient category is
abelian, which a derived category is not. -/
def _root_.CategoryTheory.Iso.precompHomAddEquiv {C : Type u} [Category.{v} C] [Preadditive C]
    {P Q : C} (e : P ≅ Q) (G : C) : (Q ⟶ G) ≃+ (P ⟶ G) where
  toFun k := e.hom ≫ k
  invFun k := e.inv ≫ k
  left_inv k := e.inv_hom_id_assoc k
  right_inv k := e.hom_inv_id_assoc k
  map_add' k l := Preadditive.comp_add _ _ _ e.hom k l

end CategoryTheory.Adjunction

/-! ### The cokernel of the conormal map of the canonical presentation -/

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules ( moduleOfDifferentialsOfSite)

universe w z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-- **The acting group of clause (2) of Stacks 08U8, at the level of sheaves of rings on a
site.** For an adjunction `F ⊣ R` out of the category of `B`-modules, the homomorphisms out of
`H⁰(F 𝖭𝖫_{B/A})` with values in an object of the target are the homomorphisms
`Ω_{B/A} ⟶ R(-)`: the adjunction moves a homomorphism out of the cokernel of `F` of the
conormal map to one out of the cokernel of the conormal map itself, and that cokernel is
`Ω_{B/A}` by the degree `0` half of **Stacks 08TY**. -/
def canonicalConormalCokernelAdjEquiv {D : Type u'} [Category.{v'} D] [Preadditive D]
    {F : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⥤ D}
    {R : D ⥤ _}
    (adj : F ⊣ R) [F.Additive] (G : D)
    [HasCokernel (F.map (canonicalConormalSequence.{v, u, w, z} J A B a).f)] :
    (cokernel (F.map (canonicalConormalSequence.{v, u, w, z} J A B a).f) ⟶ G) ≃+
      (moduleOfDifferentialsOfSite.{v, u, w, z} A B a ⟶ R.obj G) :=
  (Adjunction.cokernelHomAddEquiv adj (canonicalConormalSequence.{v, u, w, z} J A B a).f G).trans
    ((canonicalConormalCokernelIsoDifferentials.{v, u, w, z} J A B a).precompHomAddEquiv
      (R.obj G)).symm

end Stacks.SheafOfModules

/-! ### The acting group of clause (2) of Stacks 08U8 -/

namespace AlgebraicGeometry.RingedSpaceThickening

open TopologicalSpace
open AlgebraicGeometry.SheafOfModules ( underlyingRingHomOfSite
  inverseImageRingHom moduleOfDifferentialsOfSite)
open Stacks.SheafOfModules (towerExtendScalars towerExtendRestrictAdjunction
  inverseImageMiddleRing ringedSpaceStructureMap inverseImageBaseRingOnMiddle
  canonicalConormalSequence pulledNaiveCotangentComplex
  canonicalConormalCokernelIsoDifferentials canonicalConormalCokernelAdjEquiv)

variable {X₁ X₂ S₁ : RingedSpace.{u, u}} (g : X₂ ⟶ X₁) (f₁ : X₁ ⟶ S₁)
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X₂.carrier) X₂.sheaf))

/-- The pullback `g^*` of sheaves of modules, in the spelling in which `g^*𝖭𝖫_{X₁/S₁}` is
built: inverse image of modules followed by extension of scalars. Its source and target are
written with the ring sheaves `Stacks.SheafOfModules.Tensor.ringSheaf` of the two structure
sheaves, the spelling `𝖭𝖫_{X₁/S₁}` and `𝒢₂` are stated in. -/
@[ega "0 12.1.3" "partial", ega "0 4.3.1"]
abbrev pulledModuleFunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X₁.carrier) X₁.sheaf) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X₂.carrier) X₂.sheaf) :=
  inverseImageModulePullback g ⋙ inverseImageExtendScalars g

/-- The pushforward `g_*` of sheaves of modules, in the spelling adjoint to the `g^*` of
`pulledNaiveCotangentComplex`: restriction of scalars along `g^♯` followed by pushforward of
modules along `g⁻¹`. -/
abbrev pushedModuleFunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X₂.carrier) X₂.sheaf) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X₁.carrier) X₁.sheaf) :=
  SheafOfModules.restrictScalars.{u}
      (underlyingRingHomOfSite.{u, u, u} (ringedSpaceStructureMap g)) ⋙
    SheafOfModules.pushforward.{u} (inverseImageRingHom g.hom.base X₁.sheaf)

/-- `g_*𝒢`, the pushforward of an `𝒪_{X₂}`-module along `g : X₂ ⟶ X₁`. -/
abbrev pushedModule := (pushedModuleFunctor g).obj G

/-- The adjunction `g^* ⊣ g_*` for sheaves of modules on ringed spaces, in the spelling in
which `g^*𝖭𝖫_{X₁/S₁}` is built: the composite of the inverse image/pushforward adjunction for
modules and the extension/restriction of scalars adjunction of **Stacks 03CZ**. -/
def pulledModuleAdjunction : pulledModuleFunctor g ⊣ pushedModuleFunctor g :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (inverseImageRingHom g.hom.base X₁.sheaf)).comp
    (towerExtendRestrictAdjunction.{u, u, u} (Opens.grothendieckTopology X₂.carrier)
      (inverseImageMiddleRing g) X₂.sheaf (ringedSpaceStructureMap g))

/-- `g^*` is additive: both of the functors whose composite it is are. The general instance for
a composite is applied rather than searched for, as in
`RingedSpaceModuleAdjunction.twoStepPullback_additive`: the two factors reach the preadditive
structure of the middle category through two spellings of the inverse-image sheaf of rings,
which instance search does not identify. -/
instance pulledModuleFunctor_additive : (pulledModuleFunctor g).Additive :=
  RingedSpaceModuleAdjunction.twoStepPullback_additive g

/-- The conormal map of the canonical polynomial presentation of `𝒪_{X₁}` over `f₁⁻¹𝒪_{S₁}`,
the differential of `𝖭𝖫_{X₁/S₁}`. -/
abbrev canonicalConormalMap :=
  (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X₁.carrier)
    (inverseImageBaseRingOnMiddle f₁) X₁.sheaf (ringedSpaceStructureMap f₁)).f

/-- The differential of `g^*𝖭𝖫_{X₁/S₁}` is `g^*` of the conormal map. -/
theorem pulledConormalMap_eq :
    pulledConormalMap g f₁ = (pulledModuleFunctor g).map (canonicalConormalMap f₁) := rfl

/-- `Ω_{X₁/S₁}`, the sheaf of relative differentials of `𝒪_{X₁}` over `f₁⁻¹𝒪_{S₁}`, in the
spelling in which `𝖭𝖫_{X₁/S₁}` is built. -/
abbrev relativeDifferentials :=
  moduleOfDifferentialsOfSite.{u, u, u, u} (inverseImageBaseRingOnMiddle f₁) X₁.sheaf
    (ringedSpaceStructureMap f₁)

/-- The acting group of clause (2) with the adjunction `g^* ⊣ g_*` not yet applied: a
homomorphism out of `H⁰(g^*𝖭𝖫_{X₁/S₁})` is a homomorphism out of `H⁰(𝖭𝖫_{X₁/S₁})` with values
in `g_*𝒢₂`. -/
def actingGroupEquivCokernel :
    (cokernel ((pulledModuleFunctor g).map (canonicalConormalMap f₁)) ⟶ G) ≃+
      (cokernel (canonicalConormalMap f₁) ⟶ pushedModule g G) :=
  Adjunction.cokernelHomAddEquiv (pulledModuleAdjunction g) (canonicalConormalMap f₁) G

/-- **Stacks Project, Tag 08U8**, clause (2): the first identification of the acting group.
The group `Hom_{𝒪_{X₂}}(H⁰(g^*𝖭𝖫_{X₁/S₁}), 𝒢₂)` under which the morphisms `X'₂ ⟶ X'₁` fitting
into the source's diagram form a principal homogeneous space is
`Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`. -/
def actingGroupEquivPushforward :
    (cokernel ((pulledModuleFunctor g).map (canonicalConormalMap f₁)) ⟶ G) ≃+
      (relativeDifferentials f₁ ⟶ pushedModule g G) :=
  canonicalConormalCokernelAdjEquiv (Opens.grothendieckTopology X₁.carrier)
    (inverseImageBaseRingOnMiddle f₁) X₁.sheaf (ringedSpaceStructureMap f₁)
    (pulledModuleAdjunction g) G

/-- **Stacks Project, Tag 08U8**, clause (2): the second identification of the acting group.
The adjunction `g^* ⊣ g_*` rewrites `Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)` as
`Hom_{𝒪_{X₂}}(g^*Ω_{X₁/S₁}, 𝒢₂)`. -/
def actingGroupEquivPullback :
    (cokernel ((pulledModuleFunctor g).map (canonicalConormalMap f₁)) ⟶ G) ≃+
      ((pulledModuleFunctor g).obj (relativeDifferentials f₁) ⟶ G) :=
  (actingGroupEquivPushforward g f₁ G).trans
    ((pulledModuleAdjunction g).homAddEquiv (relativeDifferentials f₁) G).symm

/-! ### The acting group as an `Ext⁰` group -/

section Derived

universe t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]

/-- **Stacks Project, Tag 08U8**, clause (2): the acting group as an `Ext⁰` group. A two-term
complex concentrated in degrees `-1` and `0` lives in cohomological degrees `≤ 0`, so an
`Ext⁰`-class out of it is exactly a homomorphism out of its degree `0` cohomology object, the
cokernel of its differential. Read at `pulledNaiveCotangentTwoTerm g f₁`, whose underlying
object is `g^*𝖭𝖫_{X₁/S₁}` and whose differential is `pulledConormalMap g f₁`, this is the
identification `Hom_{𝒪_{X₂}}(H⁰(g^*𝖭𝖫_{X₁/S₁}), 𝒢₂) = Ext⁰_{𝒪_{X₂}}(g^*𝖭𝖫_{X₁/S₁}, 𝒢₂)` of
the source's display. -/
def twoTermExtZeroAddEquivCokernel {M₀ M₁ : C} (d : M₀ ⟶ M₁) {Z : DerivedCategory C}
    (e : Z ≅ DerivedCategory.Q.obj (StacksDraft.TwoTermExt.twoTermComplex d)) (G : C) :
    (Z ⟶ ((DerivedCategory.singleFunctor C 0).obj G)⟦(0 : ℤ)⟧) ≃+ (cokernel d ⟶ G) :=
  (e.precompHomAddEquiv
      (((DerivedCategory.singleFunctor C 0).obj G)⟦(0 : ℤ)⟧)).symm.trans
    (StacksDraft.TwoTermExt.twoTermExtZeroAddEquiv.{v, u, t} d G)

end Derived

section RingedSpaceDerived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 08U8**, clause (2), the acting group in its `Ext⁰` form at the
pullback of the naive cotangent complex: the group `Hom(H⁰(g^*𝖭𝖫_{X₁/S₁}), 𝒢₂)` acting on the
morphisms `X'₂ ⟶ X'₁` is `Ext⁰_{𝒪_{X₂}}(g^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`. This is
`twoTermExtZeroAddEquivCokernel` read at the two-term structure
`pulledNaiveCotangentTwoTerm g f₁` of `g^*𝖭𝖫_{X₁/S₁}`. -/
def extZeroPulledNaiveCotangentAddEquiv :=
  twoTermExtZeroAddEquivCokernel (pulledConormalMap g f₁)
    (DerivedCategory.Q.mapIso (pulledNaiveCotangentIsoDouble g f₁)).symm G

end RingedSpaceDerived

end AlgebraicGeometry.RingedSpaceThickening

end
