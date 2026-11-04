module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence

/-!
# The local vanishing input, over a scheme, of the truncation-tower convergence

Stacks 0D6M says that the canonical map from an object `E` of the derived category of modules on
a ringed site to the derived limit of its truncations from below is an isomorphism, provided the
site is locally covered by objects carrying cofinal systems of coverings on whose members the
cohomology of the cohomology sheaves of `E` vanishes above an object- and degree-dependent bound.
Stacks 08D3 is its instance for a scheme and an object with quasi-coherent cohomology: the
distinguished objects are the affine opens, the distinguished coverings are the coverings by
affine opens, and the bound is identically `0` by Serre vanishing (Stacks 01XB).

This file supplies that instantiating data, and nothing else. All four pieces are *model-free* —
none of them mentions a derived category at all — so they serve the convergence statement at
whichever `CategoryTheory.HasDerivedCategory` instance it is eventually stated for.

## Main definitions

* `AlgebraicGeometry.Scheme.affineZeroHypercover`: the covering family of an open of a scheme by
  *all* the affine opens it contains, as a `CategoryTheory.PreZeroHypercover`.
* `AlgebraicGeometry.Scheme.affineCoverings`: the covering families of an open of a scheme all of
  whose members are affine.
* `AlgebraicGeometry.Scheme.affineRefinement`: the refinement of a covering family obtained by
  covering each of its members by the affine opens inside it.

## Main results

* `Stacks.Cohomology.isZero_moduleCohomology_of_isAffineOpen`: **Serre vanishing in the
  `Stacks.Cohomology.moduleCohomology` spelling**: the positive-degree cohomology of a
  quasi-coherent module over an affine open of a scheme vanishes, as a module over the sections of
  the structure sheaf there. This is the form the `vanishing` hypothesis of Stacks 0D6M asks for;
  Stacks 01XB is stated for the `AddCommGrpCat`-valued cohomology `Hgroup` instead.
* `AlgebraicGeometry.Scheme.affineZeroHypercover_sieve₀_mem` and
  `AlgebraicGeometry.Scheme.isAffineOpen_affineZeroHypercover_X`: the affine opens inside an open
  do cover it, and are affine; together, the `basisCover` hypothesis for `B = X.affineOpens`.
* `AlgebraicGeometry.Scheme.sieve₀_mem_of_mem_affineCoverings` and
  `AlgebraicGeometry.Scheme.exists_mem_affineCoverings_nonempty_hom`: the affine coverings of an
  open are coverings, and are cofinal under refinement among all of its coverings; together, the
  `Cov_isCover` and `Cov_cofinal` hypotheses.

## Implementation notes

The index type of `affineZeroHypercover U` is the subtype of affine opens contained in `U`, and
that of `affineRefinement 𝒰` is the sigma type of pairs `(i, W)` with `W` an affine open inside
`𝒰.X i`. Both live in the universe of `X.Opens`, which is the universe `max u v` that
`CategoryTheory.PreZeroHypercover` is required to be indexed in for the site of opens of a scheme
(`v = 0`, the order category having `Prop`-valued morphisms). Taking *all* affine opens rather
than choosing some avoids every choice principle and makes the cofinality statement a one-line
construction, at the cost of a large index type — which is harmless, the index type of a
`PreZeroHypercover` being unconstrained beyond its universe.

The cohomology bridge goes through `CategoryTheory.Functor.rightDerived` only, with no derived
category in sight. Its two ingredients — that an exact post-composition commutes with right
derived functors, and that right derived functors transport along a natural isomorphism of the
functor — are `Stacks.Cohomology.rightDerivedExactPostcompositionIso` and
`Stacks.Cohomology.rightDerivedIsoOfFunctorIso`. The evaluation functor they are applied to is
the `private` `Stacks.Cohomology.moduleEvaluation`, reached with `import all` rather than
re-proved; it appears only inside the proof, never in a statement, which is what that mechanism
permits. The crossing between the two spellings of the
sections functor is free: `Stacks.Cohomology.moduleCohomology`'s `SheafOfModules.evaluation`
followed by `forget₂` to `AddCommGrpCat` and the `Hgroup` of Stacks 01E3 are the *same term*, so
the comparison is `Iso.refl`. Vanishing of the `ModuleCat`-valued cohomology is then recovered
from vanishing of its underlying group because `forget₂` is faithful and additive.

## References

* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Cohomology

/-- **Serre vanishing in the `moduleCohomology` spelling.** The positive-degree cohomology of a
quasi-coherent `𝒪_X`-module over an affine open `U` of a scheme vanishes, as a module over
`Γ(X, U)`.

Stacks 01XB gives this for the `AddCommGrpCat`-valued cohomology `Hgroup`. The two differ only by
the post-composition of `SheafOfModules.evaluation` with the forgetful functor to
`AddCommGrpCat` — which is literally how `Hgroup` is built, so the comparison of functors is
`Iso.refl` — and that functor is exact, hence commutes with right derived functors, and faithful,
hence reflects zero objects. -/
theorem isZero_moduleCohomology_of_isAffineOpen (X : Scheme.{u}) (F : X.Modules)
    (hF : F.IsQuasicoherent) (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCohomology X.ringCatSheaf U p F) := by
  have := hF
  have h01XB := Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F U hU p hp
  let E := moduleEvaluation X.ringCatSheaf U
  let G := forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (.op U))) AddCommGrpCat.{u}
  have hEadd : E.Additive := moduleEvaluation_additive X.ringCatSheaf U
  have hGadd : G.Additive := by
    dsimp only [G]
    infer_instance
  have hcomp : E ⋙ G ≅ secF X.ringCatSheaf U := Iso.refl _
  have hCadd : (E ⋙ G).Additive := inferInstance
  have hGz : IsZero (G.obj ((E.rightDerived p).obj F)) :=
    h01XB.of_iso ((rightDerivedExactPostcompositionIso E G F p).trans
      ((rightDerivedIsoOfFunctorIso hcomp p).app F))
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact hGz.eq_of_src _ _

end Stacks.Cohomology

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **The covering of an open of a scheme by the affine opens it contains**, as a family of
morphisms with fixed target. The index type is the subtype of affine opens below `U`; taking all
of them rather than choosing some is what makes `affineZeroHypercover_sieve₀_mem` and the
cofinality statement choice-free. -/
def affineZeroHypercover (U : X.Opens) : PreZeroHypercover.{u} U where
  I₀ := { V : X.Opens // IsAffineOpen V ∧ V ≤ U }
  X V := V.1
  f V := homOfLE V.2.2

/-- The member of `affineZeroHypercover U` indexed by an affine open `V ≤ U` is `V` itself. -/
@[simp]
theorem affineZeroHypercover_X (U : X.Opens) (i : (X.affineZeroHypercover U).I₀) :
    (X.affineZeroHypercover U).X i = i.1 :=
  rfl

/-- Every member of `affineZeroHypercover U` is an affine open. -/
theorem isAffineOpen_affineZeroHypercover_X (U : X.Opens)
    (i : (X.affineZeroHypercover U).I₀) :
    IsAffineOpen ((X.affineZeroHypercover U).X i) :=
  i.2.1

/-- Every point of an open `U` of a scheme lies in an affine open contained in `U`. -/
private theorem exists_isAffineOpen_mem_le (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U :=
  Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx

/-- **The affine opens contained in an open of a scheme cover it.** This is the `basisCover`
hypothesis of Stacks 0D6M for the collection `B = X.affineOpens`, the affine opens forming a
basis of the topology. -/
theorem affineZeroHypercover_sieve₀_mem (U : X.Opens) :
    (X.affineZeroHypercover U).sieve₀ ∈ Opens.grothendieckTopology (↥X) U := by
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := X.exists_isAffineOpen_mem_le U hx
  exact ⟨V, homOfLE hVU, (X.affineZeroHypercover U).sieve₀_f ⟨V, hV, hVU⟩, hxV⟩

/-- **The affine coverings of an open of a scheme**: the covering families all of whose members
are affine opens. This is the `Cov` datum of Stacks 0D6M. -/
def affineCoverings (V : X.Opens) : Set (PreZeroHypercover.{u} V) :=
  {𝒰 | 𝒰.sieve₀ ∈ Opens.grothendieckTopology (↥X) V ∧ ∀ i, IsAffineOpen (𝒰.X i)}

/-- An affine covering is a covering. This is the `Cov_isCover` hypothesis of Stacks 0D6M. -/
theorem sieve₀_mem_of_mem_affineCoverings {V : X.Opens} {𝒰 : PreZeroHypercover.{u} V}
    (h : 𝒰 ∈ X.affineCoverings V) :
    𝒰.sieve₀ ∈ Opens.grothendieckTopology (↥X) V :=
  h.1

/-- The members of an affine covering are affine opens. -/
theorem isAffineOpen_of_mem_affineCoverings {V : X.Opens} {𝒰 : PreZeroHypercover.{u} V}
    (h : 𝒰 ∈ X.affineCoverings V) (i : 𝒰.I₀) : IsAffineOpen (𝒰.X i) :=
  h.2 i

/-- **The affine refinement of a covering family**: cover each member of `𝒰` by the affine opens
contained in it. The index type is the sigma type of pairs `(i, W)` with `W` affine and
`W ≤ 𝒰.X i`. -/
def affineRefinement {V : X.Opens} (𝒰 : PreZeroHypercover.{u} V) : PreZeroHypercover.{u} V where
  I₀ := Σ i : 𝒰.I₀, { W : X.Opens // IsAffineOpen W ∧ W ≤ 𝒰.X i }
  X p := p.2.1
  f p := homOfLE (p.2.2.2.trans (leOfHom (𝒰.f p.1)))

/-- The affine refinement refines the family it was built from. -/
def affineRefinementHom {V : X.Opens} (𝒰 : PreZeroHypercover.{u} V) :
    (X.affineRefinement 𝒰).Hom 𝒰 where
  s₀ p := p.1
  h₀ p := homOfLE p.2.2.2

/-- **The affine coverings of an open of a scheme are cofinal under refinement.** Every covering
family of `V` is refined by one whose members are affine opens. Together with
`sieve₀_mem_of_mem_affineCoverings` this is the `Cov_cofinal` hypothesis of Stacks 0D6M, and it
makes `fun _ _ ↦ X.affineCoverings _` a `Stacks.Cohomology.CofinalCoveringSystem`. -/
theorem exists_mem_affineCoverings_nonempty_hom {V : X.Opens} (𝒰 : PreZeroHypercover.{u} V)
    (h𝒰 : 𝒰.sieve₀ ∈ Opens.grothendieckTopology (↥X) V) :
    ∃ 𝒱 ∈ X.affineCoverings V, Nonempty (𝒱.Hom 𝒰) := by
  refine ⟨X.affineRefinement 𝒰, ⟨?_, fun p => p.2.2.1⟩, ⟨X.affineRefinementHom 𝒰⟩⟩
  intro x hx
  obtain ⟨W, g, hg, hxW⟩ := h𝒰 x hx
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  obtain ⟨W', hW', hxW', hW'i⟩ := X.exists_isAffineOpen_mem_le (𝒰.X i) (leOfHom a hxW)
  exact ⟨W', homOfLE (hW'i.trans (leOfHom (𝒰.f i))),
    (X.affineRefinement 𝒰).sieve₀_f ⟨i, W', hW', hW'i⟩, hxW'⟩

end AlgebraicGeometry.Scheme

end
