module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ClassRestrictionToAnObject

/-!
# First fppf cohomology of an abelian scheme and the generic point

Let `W` be a two dimensional regular integral Noetherian scheme with function field `K` and let
`G → W` be an abelian scheme. Restriction to the generic point is injective on first fppf
cohomology with coefficients in `G`.

## Main definitions

* `AlgebraicGeometry.pointsCommGrpPresheaf` is the presheaf of points of a commutative group
  scheme over `W`, written multiplicatively, and `AlgebraicGeometry.pointsPresheaf` is it
  written additively on the big fppf site over `W`.
* `AlgebraicGeometry.pointsSheaf` is the abelian sheaf of points of a commutative group scheme
  over `W` on the big fppf site over `W`.
* `AlgebraicGeometry.IsAbelianScheme` is the predicate that a commutative group scheme over `W`
  is an abelian scheme.
* `AlgebraicGeometry.genericPointObj` and `AlgebraicGeometry.genericPointToBase` are the
  spectrum of the function field of `W` and its canonical morphism to `W`, taken in the big
  fppf site over `W`.

## Main results

* `AlgebraicGeometry.pointsPresheaf_isSheaf` says that the points of a commutative group scheme
  over `W` form an abelian sheaf on the big fppf site over `W`.
* `AlgebraicGeometry.fppfH1_restriction_genericPoint_injective`: the cohomological half of
  Stacks 0AF9, from the triviality of torsors with a section over `Spec K`, see below. The
  unconditional Stacks 0AF9 is
  `AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_dim_two` in
  `AbelianSchemeFirstCohomologyInjective.lean`.

## Implementation notes

`H^1_{fppf}(W, G)` is the first cohomology of the fppf sheaf of points of `G`, and
`H^1_{fppf}(\Spec(K), G)` is the same sheaf's cohomology over the object `Spec K` of the big
fppf site over `W`. Both are values of Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf`,
which sends an object `U` of a site to the cohomology of the sheaf over `U`; the map of the
source is therefore the restriction map of that presheaf along the canonical morphism
`Spec K → W`, so there is no separate base-change datum and no choice of map to get wrong.
Over the terminal object of the big fppf site over `W` — which is `W` itself — the value of
that presheaf is global fppf cohomology, by
`Stacks.Cohomology.TerminalCohomology.h'AddEquivH`.

The points of `G` form a sheaf because they are represented by `G` itself, an object of the
site once `W` and `G` are small enough to lie in it, and the big fppf topology is subcanonical
(`AlgebraicGeometry.BigFppfOver.subcanonical_topology`); this is the same argument as for the
multiplicative sheaf of Tag 040N. The commutativity of `G`, which an abelian scheme has, is
what makes the source's `H^1` an abelian cohomology group, so it is no restriction on `G`.

**The hypothesis.** The theorem of this file takes as its hypothesis `htrivial` the geometric
statement that an fppf `G`-torsor with a section over `Spec K` is trivial, and proves the
passage from it to the cohomological statement: a class in the kernel of the restriction map is
the class of a torsor (Tag 03AJ), the restriction of that class to `Spec K` vanishes exactly when
the torsor acquires a section over `Spec K`, and a trivial torsor has vanishing class. That
passage is `Stacks.Cohomology.Torsors.injective_cohomologyPresheaf_map_of_isTrivial`. The
geometric statement itself, for which the source's sketch leaves a step to an unwritten
reference on resolving indeterminacies of surfaces, is proved in
`AbelianSchemeFirstCohomologyInjective.lean`, which also states Stacks 0AF9 unconditionally.

`IsAbelianScheme` is the definition the source uses in the footnote of its Section 110.74: a
flat proper group scheme of finite presentation all of whose fibres are abelian varieties.
Quasi-compactness and quasi-separatedness are not listed because properness supplies them, so
only the local part of finite presentation is an extra condition. A fibre is the base change of
`G` along `Spec κ(w) → W`, taken with the cartesian-monoidal base-change functor on `Over`, so
that it carries its group structure canonically, and it is required to be an abelian variety in
the sense of Tag 03RO. None of these conditions, nor regularity, integrality, Noetherianness or
two-dimensionality of `W`, is used in the proof of the implication; they are the hypotheses of
the source statement and are kept so that the statement is the source's.

## References

* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe w u

namespace AlgebraicGeometry

/-- The presheaf of points of a commutative group scheme over `W`, written multiplicatively. -/
public def pointsCommGrpPresheaf {W : Scheme.{u}} (G : Over W) [GrpObj G] [IsCommMonObj G] :
    (Over W)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (T.unop ⟶ G)
  map φ := CommGrpCat.ofHom ((yonedaGrpObj G).map φ).hom
  map_id _ := by ext f; exact congrArg Over.Hom.left (Category.id_comp f)
  map_comp _ _ := by ext f; exact Category.assoc _ _ _

/-- An abelian scheme over `W` is a commutative flat proper group scheme of finite presentation
over `W` all of whose fibres are abelian varieties. -/
public class IsAbelianScheme {W : Scheme.{u}} (G : Over W) [GrpObj G] : Prop extends
    IsCommMonObj G, Flat G.hom, IsProper G.hom, LocallyOfFinitePresentation G.hom where
  /-- The fibre over a point is an abelian variety over the residue field of that point. -/
  fibre_isAbelianVariety (x : W) :
    @IsAbelianVariety (W.residueField x) _
      ((Over.pullback (W.fromSpecResidueField x)).mapGrp.obj (.mk G)).X
      ((Over.pullback (W.fromSpecResidueField x)).mapGrp.obj (.mk G)).grp

variable (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- The abelian presheaf of points of a commutative group scheme over `W` on the big fppf site
over `W`. -/
public def pointsPresheaf (G : Over W) [GrpObj G] [IsCommMonObj G] :
    (BigFppfOver B W hW)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Over.post B.inclusion : BigFppfOver B W hW ⥤ Over W).op ⋙
    pointsCommGrpPresheaf G ⋙ CommGrpCat.toAddCommGrp

/-- A group scheme over `W` contained in the big fppf site, as an object of the big fppf site
over `W`. -/
public def groupSchemeObj (G : Over W) (hG : B.Contains G.left) : BigFppfOver B W hW :=
  Over.mk (ObjectProperty.homMk G.hom : B.obj hG ⟶ B.obj hW)

/-- **The points of a commutative group scheme over `W` form an abelian sheaf on the big fppf
site over `W`**: the underlying presheaf of sets is represented by the group scheme itself, and
the big fppf topology is subcanonical. -/
public theorem pointsPresheaf_isSheaf (G : Over W) [GrpObj G] [IsCommMonObj G]
    (hG : B.Contains G.left) :
    Presheaf.IsSheaf (BigFppfOver.topology B W hW) (pointsPresheaf B W hW G) := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u}) ?_
  have e₁ : yoneda.obj (groupSchemeObj B W hW G hG) ≅
      (Over.post (X := B.obj hW) B.inclusion).op ⋙ yoneda.obj G := by
    refine NatIso.ofComponents (fun Z => Equiv.toIso
      ((Functor.FullyFaithful.ofFullyFaithful
        (Over.post (X := B.obj hW) B.inclusion)).homEquiv)) ?_
    intro Z Z' φ
    ext g
    exact (Over.post (X := B.obj hW) B.inclusion).map_comp φ.unop g
  have e₂ : (Over.post (X := B.obj hW) B.inclusion).op ⋙ yoneda.obj G ≅
      pointsPresheaf B W hW G ⋙ forget AddCommGrpCat.{u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro Z Z' φ; ext g; rfl)
  exact (Presheaf.isSheaf_of_iso_iff (e₁ ≪≫ e₂)).mp
    (BigFppfOver.isSheaf_yoneda_obj B W hW (groupSchemeObj B W hW G hG))

/-- The abelian sheaf of points of a commutative group scheme over `W` on the big fppf site
over `W`. -/
public def pointsSheaf (G : Over W) [GrpObj G] [IsCommMonObj G] (hG : B.Contains G.left) :
    Sheaf (BigFppfOver.topology B W hW) AddCommGrpCat.{u} :=
  ⟨pointsPresheaf B W hW G, pointsPresheaf_isSheaf B W hW G hG⟩

/-- The spectrum of the function field of an irreducible `W`, as an object of the big fppf site
over `W`. -/
public def genericPointObj [IrreducibleSpace W]
    (hK : B.Contains (Spec W.functionField)) : BigFppfOver B W hW :=
  Over.mk (ObjectProperty.homMk (W.fromSpecStalk (genericPoint W)) : B.obj hK ⟶ B.obj hW)

/-- The canonical morphism `Spec K ⟶ W` in the big fppf site over `W`, the structure morphism
of `Spec K` as an object over `W`. -/
public def genericPointToBase [IrreducibleSpace W]
    (hK : B.Contains (Spec W.functionField)) :
    genericPointObj B W hW hK ⟶ Over.mk (𝟙 (B.obj hW)) :=
  Over.mkIdTerminal.from (genericPointObj B W hW hK)

/-- **The passage from torsors to cohomology in Stacks 0AF9.** If every fppf `G`-torsor with a
section over `Spec K` is trivial (the hypothesis `htrivial`), then the restriction map
`H¹_fppf(W, G) → H¹_fppf(Spec K, G)` along the generic point is injective.

The hypothesis `htrivial` is proved for a two dimensional regular integral Noetherian `W` and an
abelian scheme `G` in `AlgebraicGeometry.isTrivial_of_nonempty_sections_genericPoint`, and the
unconditional Stacks 0AF9 is
`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_dim_two`. -/
public theorem fppfH1_restriction_genericPoint_injective
    [IsIntegral W] [AlgebraicGeometry.IsNoetherian W] (_hreg : IsRegular W)
    (_hdim : topologicalKrullDim (W : Type u) = (2 : WithBot ℕ∞))
    (hK : B.Contains (Spec W.functionField))
    (G : Over W) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    [HasSheafify (BigFppfOver.topology B W hW) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B W hW) AddCommGrpCat.{u})]
    (htrivial : ∀ F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG),
      Nonempty (F.1.presheaf.obj (op (genericPointObj B W hW hK))) → F.1.IsTrivial) :
    Function.Injective (((pointsSheaf B W hW G hG).cohomologyPresheaf 1).map
      (genericPointToBase B W hW hK).op) :=
  Stacks.Cohomology.Torsors.injective_cohomologyPresheaf_map_of_isTrivial
    (pointsSheaf B W hW G hG) Over.mkIdTerminal (genericPointToBase B W hW hK) htrivial

end AlgebraicGeometry

end
