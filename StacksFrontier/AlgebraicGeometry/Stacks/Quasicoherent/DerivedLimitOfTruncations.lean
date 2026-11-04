module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceAcyclicCover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleOfTower

/-!
# A complex in `LQCoh^fbc` is the derived limit of its truncations (Stacks 08IY)

Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒪_𝒳)` whose cohomology sheaves are
locally quasi-coherent (**Stacks 06WJ**) and have the flat base change property
(**Stacks 0762**). **Stacks 08IY** says that there is a distinguished triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`

in `D(𝒪_𝒳)`; that is, `K` is the derived limit of the tower of its canonical truncations from
below.  In the vocabulary of this repository that conclusion is
`CategoryTheory.Pretriangulated.IsDerivedLimit` (**Stacks 08TC**) at the tower
`Stacks.DerivedLimit.truncGETower`, since the triangle `IsDerivedLimit` asserts is exactly the
displayed one.

The source's proof has two steps.  The first is the vanishing

`H^p(x, ℱ) = 0` for `p > 0`, `ℱ` locally quasi-coherent with flat base change and `x` an object
of `𝒳_fppf` lying over an *affine* scheme,

which it obtains by combining Sheaves on Stacks **Stacks 075R** and **Stacks 075F** with
Descent **Stacks 0756** and Cohomology of Schemes **Stacks 01XB**.  The second is the citation of
Cohomology on Sites **Stacks 0D6P** with `d = 0`, for the class `ℬ` of objects lying over an
affine scheme.

The second step is what this file proves.  The first is carried as the explicit hypothesis
`hvan`; none of its four inputs is available here, and the implementation notes record where each
stands.

## Main results

* `AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver`: **the objects of `𝒳_fppf` lying over
  an affine scheme cover every object of `𝒳_fppf`** — the class `ℬ` of the source is a covering
  class.  This is proved outright, with no hypothesis beyond fibredness in groupoids.
* `AlgebraicGeometry.Stack.isIso_to_isDerivedLimit_truncGETower_of_lqcFbc`: the convergence
  criterion of **Stacks 0D6P** with `d = 0` transported to the fppf site of a category fibred in
  groupoids: the canonical map from `K` to *any* derived limit of the tower of its truncations is
  invertible.
* `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc`: **Stacks 08IY** for a
  category fibred in groupoids, with `ℬ` covering carried as the hypothesis `hB`.
* `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc'`: **Stacks 08IY**, with
  `hB` discharged — the form that applies to an algebraic stack, whose fppf site has hom universe
  `u + 1`.
* `AlgebraicGeometry.Stack.enoughInjectives_fppfSiteModules_of_univLE`: the enough-injectives
  hypothesis of the statements above is satisfiable — it is an instance whenever the total
  category of the fibred category and its homs inject into the module universe.

## What is carried, and why

The hypothesis `hvan` is the vanishing of the higher fppf cohomology of a module in
`LQCoh^fbc(𝒪_𝒳)` over an object lying over an affine scheme.  It is the first sentence of the
source's proof, and all four of its inputs are missing from this repository:

* **Stacks 075R** — the agreement of fppf and étale cohomology for a module in `LQCoh^fbc` — is
  not formalized.  Its own proof needs the comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale` as a
  morphism of topoi, which is not constructed; only the underlying functor `ε_*` for a pair of
  comparable topologies exists, as `Stacks.SheafOfModules.comparisonPushforward`.
* **Stacks 075F** is available for abelian sheaves and an arbitrary topology on the base, as
  `AlgebraicGeometry.Stack.cohomologyOverObjectIso`, but its own attribute records that the case
  of *modules over the structure sheaf* — the case needed here — is not included.
* **Stacks 0756** is available only as its step from Stacks 0755, as
  `AlgebraicGeometry.BigFppfOver.bigFppfCohomology_map_bijective_of_isParasitic`; the
  identification of Stacks 03DW that turns it into the cohomology comparison is not.
* **Stacks 01XB** is available only for the small Zariski site of a scheme, as
  `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`.  The vanishing of the higher
  cohomology of a quasi-coherent module on the *big fppf site* of an affine scheme is not
  available; the
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModuleCohomologyDegreeZero.lean` record that
  the degree-zero case is all that is claimed there.

So `hvan` stands for a chain of four cited lemmas and for nothing else: it is a statement about
the modules in `LQCoh^fbc(𝒪_𝒳)` and the objects over affine schemes, not about `K`, and it is
*not* the conclusion of Stacks 08IY in disguise — the conclusion is a statement about one
unbounded complex and the hypothesis says nothing about complexes at all.

## Implementation notes

The module universe is the universe `u` of the schemes, as
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` pins it; the ring universe is
`u` as well, since `AlgebraicGeometry.Stack.ringStructureSheafCore` is valued in `RingCat.{u}`.
Being abelian, having a derived category, having enough injectives and sheafifying at the module
universe are instance hypotheses on the fppf modules of `𝒳`, exactly as they are for the
Verdier quotient of **Stacks 07B6** in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedQuasicoherent.lean`.  They are not
vacuous: `AlgebraicGeometry.Stack.enoughInjectives_moduleSheaves` supplies the enough-injectives
instance whenever the site, its homs and the rings inject into the module universe, which holds
for a category fibred in groupoids whose total category is `u`-small, and
`AlgebraicGeometry.Stack.enoughInjectives_fppfSiteModules_of_univLE` records that
instantiation.

`AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver` is stated at hom universe `u + 1`
because `CategoryTheory.GrothendieckTopology.HasEnoughObjects` indexes its covering family in the
hom universe of the site, while
`AlgebraicGeometry.FibredSite.exists_affine_ofArrows` produces a family indexed in `Type (u + 1)`
— the universe of the covering families of the big fppf site.  Hom universe `u + 1` is the
configuration of an algebraic stack: the underlying category of an object of
`AlgebraicGeometry.Stack.AlgebraicStacks` is a `CategoryTheory.BasedCategory.{u + 1, u + 1}`.

## References

* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 075F](https://stacks.math.columbia.edu/tag/075F)
* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Stack

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **The objects lying over an affine scheme cover the fppf site of a category fibred in
groupoids.**  This is the class `ℬ` of the proof of **Stacks 08IY**, and the statement that it is
a covering class in the sense of **Stacks 090L** (3).

It is `AlgebraicGeometry.FibredSite.exists_affine_ofArrows` read as
`CategoryTheory.GrothendieckTopology.HasEnoughObjects`: an affine open cover of the scheme below
an object is a covering family of the big fppf site, and lifting it along a functor fibred in
groupoids gives a covering family upstairs whose members lie over affine schemes.  The hom
universe is `u + 1` because that is where the covering families of the big fppf site are
indexed, and it is the hom universe of an algebraic stack. -/
theorem hasEnoughObjects_isAffineOver {𝒳 : Type v} [Category.{u + 1} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) :
    (BigFppfOver.associatedTopology B S hS p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B S hS (p.obj x)) := by
  intro x
  obtain ⟨I, y, φ, hyaff, hcov⟩ := FibredSite.exists_affine_ofArrows B S hS p hp x
  exact ⟨I, y, φ, hcov, hyaff⟩

section

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The structure sheaf of rings on the fppf site of a category fibred in groupoids: the sheaf of
**Stacks 06TV** at the fppf topology, read through the forgetful functor to rings so that module
constructions use the same scalars.

This is `AlgebraicGeometry.FibredSite.ringStructureSheafCore` at `SiteKind.fppf`, named here so
that the statements below are readable. -/
abbrev fppfSiteRingSheaf : Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) RingCat.{u} :=
  FibredSite.ringStructureSheafCore B S hS p hp .fppf

/-- The category `Mod(𝒪_𝒳)` of sheaves of modules on the fppf site of a category fibred in
groupoids, at the module universe `u` of the schemes. -/
abbrev fppfSiteModules := SheafOfModules.{u} (fppfSiteRingSheaf B S hS p hp)

variable
  [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The truncation tower `n ↦ τ_{≥ -n}K` of an object of `D(𝒪_𝒳)`, whose derived limit
**Stacks 08IY** identifies with `K`. -/
abbrev fppfTruncGETower (K : DerivedCategory (fppfSiteModules B S hS p hp)) :=
  Stacks.DerivedLimit.truncGETower (fppfSiteModules B S hS p hp) K

variable [EnoughInjectives (fppfSiteModules B S hS p hp)]

/-- The vanishing of the higher fppf cohomology of a module in `LQCoh^fbc(𝒪_𝒳)` over an object
lying over an affine scheme: the first sentence of the proof of **Stacks 08IY**, which the source
obtains from **Stacks 075R**, **Stacks 075F**, **Stacks 0756** and **Stacks 01XB**.

None of those four is available in this repository in the form needed; see the section *What is
carried, and why* in this file's module documentation.  This predicate names the conjunction so
that the statements below can carry it as a single hypothesis. -/
def HasAffineAcyclicLqcFbcModules : Prop :=
  ∀ F : fppfSiteModules B S hS p hp,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F.val →
    ∀ x : 𝒳, IsAffineOver B S hS (p.obj x) → ∀ i : ℕ, 0 < i →
      IsZero (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp)
        (.op x)).rightDerived i).obj F)

/-- **The convergence criterion of Stacks 0D6P with `d = 0` on the fppf site of a category fibred
in groupoids.**  If the cohomology sheaves of `K` lie in `LQCoh^fbc(𝒪_𝒳)`, then the canonical map
from `K` to any derived limit of the tower `n ↦ τ_{≥ -n}K` is invertible.

The derived limit is presented by its structural map `pr` to the product of the tower together
with the distinguished triangle `hT` characterising it, and `c` is the canonical map because its
composites with the product projections are the truncation maps.

This is
`Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic` — Stacks 0D6P at
independent site, ring and module universes — applied with `ℬ` the objects over an affine scheme
and the uniform bound supplied by `hvan`. -/
theorem isIso_to_isDerivedLimit_truncGETower_of_lqcFbc
    (K : DerivedCategory (fppfSiteModules B S hS p hp))
    (hK : ∀ i : ℤ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) i).obj K).val)
    (hB : (BigFppfOver.associatedTopology B S hS p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B S hS (p.obj x)))
    (hvan : HasAffineAcyclicLqcFbcModules B E h S hS p hp)
    [HasProduct fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩]
    (L : DerivedCategory (fppfSiteModules B S hS p hp)) (c : K ⟶ L)
    (pr : L ⟶ ∏ᶜ fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk pr (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩) (n + 1) ≫
          (fppfTruncGETower B S hS p hp K).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory (fppfSiteModules B S hS p hp)))
    (hc : ∀ n : ℕ, c ≫ pr ≫
        Pi.π (fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) :
    IsIso c :=
  Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
    (fppfSiteRingSheaf B S hS p hp) K (fun x => IsAffineOver B S hS (p.obj x)) hB
    (fun x hx i hi m => hvan _ (hK m) x hx i hi) L c pr δ hT hc

/-- **Stacks 08IY** for a category fibred in groupoids, with the covering class carried as `hB`.
An object `K` of `D(𝒪_𝒳)` whose cohomology sheaves are locally quasi-coherent with the flat base
change property sits in a distinguished triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`,

that is, `K` *is* a derived limit of the tower of its canonical truncations from below.  The
product of the tower exists because each stage is bounded below (**Stacks 0BK7**).

The vanishing `hvan` is carried; see this file's module documentation. -/
theorem exists_isDerivedLimit_truncGETower_of_lqcFbc
    (K : DerivedCategory (fppfSiteModules B S hS p hp))
    (hK : ∀ i : ℤ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) i).obj K).val)
    (hB : (BigFppfOver.associatedTopology B S hS p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B S hS (p.obj x)))
    (hvan : HasAffineAcyclicLqcFbcModules B E h S hS p hp) :
    ∃ _ : HasProduct fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩,
      IsDerivedLimit (fppfTruncGETower B S hS p hp K) K := by
  have hprod := Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower
    (fppfSiteRingSheaf B S hS p hp) K
  refine ⟨hprod, ?_⟩
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (fppfTruncGETower B S hS p hp K)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
    (fun n ↦ Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map K
      (homOfLE (Nat.le_succ n)).op)
    fun L c pr d hT hcn ↦
      isIso_to_isDerivedLimit_truncGETower_of_lqcFbc B E h S hS p hp K hK hB hvan L c pr d hT hcn
  exact ⟨_, δ, hδ⟩

end

/-- **Stacks 08IY.** Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒪_𝒳)` whose
cohomology sheaves are locally quasi-coherent (**Stacks 06WJ**) and have the flat base change
property (**Stacks 0762**).  Then there is a distinguished triangle

`K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ ∏_{n ≥ 0} τ_{≥ -n}K ⟶ K[1]`

in `D(𝒪_𝒳)`: `K` is the derived limit of its canonical truncations from below.

This is `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc` with the covering
class of the source's proof discharged by
`AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver`, at the hom universe `u + 1` of the fppf
site of an algebraic stack.  The hypothesis `hvan` is the source's first sentence, carried; see
this file's module documentation for the four cited lemmas it stands for and for why none of them
is available. -/
@[stacks 08IY "K is the derived limit of its canonical truncations from below, for a complex \
of fppf modules with cohomology sheaves in LQCoh^fbc; the affine-object vanishing the \
source cites is carried as the hypothesis `hvan`"]
theorem exists_isDerivedLimit_truncGETower_of_lqcFbc' {𝒳 : Type v} [Category.{u + 1} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
    [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (fppfSiteModules B S hS p hp)]
    (K : DerivedCategory (fppfSiteModules B S hS p hp))
    (hK : ∀ i : ℤ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) i).obj K).val)
    (hvan : HasAffineAcyclicLqcFbcModules B E h S hS p hp) :
    ∃ _ : HasProduct fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩,
      IsDerivedLimit (fppfTruncGETower B S hS p hp K) K :=
  exists_isDerivedLimit_truncGETower_of_lqcFbc B E h S hS p hp K hK
    (hasEnoughObjects_isAffineOver B S hS p hp) hvan


section Satisfiable

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) [UnivLE.{v, u}] [UnivLE.{w, u}]
  [HasWeakSheafify (associatedTopology B S hS p B.topology) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p B.topology).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The enough-injectives hypothesis of this file is satisfiable.** Sheaves of `𝒪_𝒳`-modules at
the module universe `u` of the schemes have enough injectives as soon as the total category of
the fibred category and its homs inject into `u`; the rings already live in `u`.

This is `AlgebraicGeometry.Stack.enoughInjectives_moduleSheaves` read through
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_fppf_eq_stack`.  It is recorded so that the
instance hypotheses carried by
`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc` are visibly inhabited and
not an empty class: taking `v = w = u` makes all three of them instances.

It does not apply to an object of `AlgebraicGeometry.Stack.AlgebraicStacks`, whose total
category and homs live in `u + 1`.  There the mathematical reason the class is inhabited is the
essential `u`-smallness of the fppf site, which
`AlgebraicGeometry.Stack.essentiallySmall_obj` supplies from local smallness and essential
smallness of the fibres; transporting Grothendieck abelianness across that equivalence is not
available in this repository, which is why the hypothesis is carried rather than discharged. -/
theorem enoughInjectives_fppfSiteModules_of_univLE :
    EnoughInjectives (fppfSiteModules B S hS p hp) :=
  enoughInjectives_moduleSheaves.{u, v, w, u} B S hS p hp B.topology le_rfl

end Satisfiable

end AlgebraicGeometry.Stack

end
