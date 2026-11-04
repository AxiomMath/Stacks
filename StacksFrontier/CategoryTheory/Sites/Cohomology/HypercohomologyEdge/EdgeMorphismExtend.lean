module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismMapHomologyIso
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The homology comparison of a left exact functor against extension by zero

`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison` is the map
`H^q(G K) ⟶ G(H^q K)` that a left exact additive functor supplies on a cochain complex indexed
by `ℤ`; `CategoryTheory.ShortComplex.mapCyclesIso` and
`CategoryTheory.ShortComplex.mapHomologyIso` are the corresponding isomorphisms for a complex
indexed by an arbitrary shape, where `G` preserves the left homology that occurs, and
`EdgeMorphismMapHomologyIso.lean` proves that the two agree in the `ℤ`-indexing.

What is still owed, and is supplied here, is the comparison **across an embedding of shapes**.
Extension by zero along `e : c.Embedding (ComplexShape.up ℤ)` does not change homology in the
degrees `e` hits (`HomologicalComplex.extendHomologyIso`) and commutes with an additive functor
applied termwise (`Stacks.DerivedIndexing.mapExtendIso`), and this file proves that the homology
comparison of `G` is carried by those two identifications onto the one for the unextended
complex. This is the bridge between the `ℕ`-indexed comparison that the degreewise collapse of
[Stacks, Tag 01XK] is built from — `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`, whose
component is `CategoryTheory.ShortComplex.mapHomologyIso` by
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app` — and the `ℤ`-indexed comparison
that the edge morphism of an unbounded right derived functor is built from.

## Main results

* `extendCyclesIso_comp_cyclesComparison`: **the cycles comparison is carried across the
  extension**, both sides being computed by cancelling the monomorphism `G` applied to the
  inclusion of cycles.
* `extendHomotopyHomologyNatIso_hom_app_quotient`: the homotopy-category comparison of the two
  indexings, at the image of a complex, is `HomologicalComplex.extendHomologyIso` conjugated by
  the three factorisations it is lifted from.
* `extendHomologyIso_comp_homologyComparison`: **the homology comparison is carried across the
  extension.** The square whose vertical edges are the comparison for the extended complex and
  `CategoryTheory.ShortComplex.mapHomologyIso` for the unextended one, and whose horizontal
  edges are `HomologicalComplex.extendHomologyIso` at the image complex and `G` applied to
  `HomologicalComplex.extendHomologyIso` at the complex itself.

## Implementation notes

*Every reassociation is hoisted onto variables.* The goals here carry both spellings of the
degree-`j` cycles of `G` applied to `N` termwise — `CategoryTheory.ShortComplex.cycles` of the
image short complex, which is what `CategoryTheory.ShortComplex.mapCyclesIso` is stated at, and
`HomologicalComplex.cycles`, which is what `HomologicalComplex.extendCyclesIso` is stated at.
The two are the same object definitionally and not syntactically, so such a goal is not
type-correct at the `implicit` transparency level at which a rewrite builds its motive, and
`rw`, `simp only [CategoryTheory.Category.assoc]` included, is unavailable on it. The chases are
therefore stated at variables of an abstract category — `comp_two`, `chase_left`, `comp_tail`,
`congr_tail`, `mono_pair`, `epi_pair` — and applied in argument position, where the elaborator
checks against the goal at default transparency and sees the two spellings as one.

## What the collapse mirror is, and where it is

The consumer these two results are for is the `Gamma(V, -)`-exactness mirror of
`Stacks.Cohomology.AffineComparison.singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`
(`AlgebraicGeometry/AffineCohomologyComparison/UnboundedModel.lean`), that is of
[Stacks, Tag 01XK] rather than [Stacks, Tag 089W]. The two tags share their first factor
exactly — `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at
`Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop`, which is
`Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso` whiskered — and differ only
in the second: 089W collapses the **inner** functor at an acyclic object, through
`Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso`, while 01XK collapses the
**outer** one, through `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`. So the mirror is

> `(singleCompDerivedCompHomologyIsoRightDerived (F ⋙ G) RFG αFG hresA n).hom.app (E.obj X) ≫`
> `(rightDerivedCompNatIso E F G n h).inv.app X`
> `= Hⁿ(θ.app ((E.obj X)[0])) ≫`
> `(derivedHomologyComparison G RG αG hresB n).app (RF.obj ((E.obj X)[0])) ≫`
> `G.map ((singleCompDerivedCompHomologyIsoRightDerived F RF αF hresA n).hom.app (E.obj X))`,

with the same data and the same `hθ` as the 089W mirror; its right-hand side is the last two
factors of `Stacks.EdgeCompat.derivedHomologyComparison_comp`, which is why the splitting of the
edge morphism is what assembles it. The `E` is kept general rather than specialised to `𝟭`,
because 01XK whiskers by the inclusion of the quasi-coherent modules and because an
`(𝟭 _).obj` in that slot is the unfolding problem recorded at
`…TopDegreeBaseChange.rightDerivedPlusRestrictObjIso_hom_naturality_unit`.

Cancelling the two model crossings — each of which is `Hⁿ(Rw(sᵧ))` followed by the inverse of
the unit at the extended chosen resolution, by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` — and consuming `hθ`,
the naturality of `θ` and the naturality of the edge morphism of `G` reduces the mirror to a
statement with **no derived functor and no unit left in it**: the factorisation of the
cohomology functor followed by `Stacks.DerivedIndexing.rightDerivedIsoRes` inverted and by
`rightDerivedCompNatIso` inverted, against
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopyHomologyComparisonToDerived`
and `G` of the same factorisation. That residue is what the two results above are for:
`rightDerivedIsoRes` is `Stacks.DerivedIndexing.extendMapHomologyIso` at the chosen resolution
(`Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_eq`),
`Stacks.DerivedIndexing.extendMapHomologyIso_hom_comp` splits off the inner functor, and what is
then left on either side is `homologyComparison` for `G` on the extended complex against
`CategoryTheory.ShortComplex.mapHomologyIso` for `G` on the unextended one — which is
`extendHomologyIso_comp_homologyComparison`, together with
`…HomologyComparison.homologyComparison_eq_mapHomologyIso_hom` and
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app`.

The remaining step of that reduction — the component of
`Stacks.DerivedIndexing.extendMapHomologyIso` read against the complex-level data, namely

> `(extendMapHomologyIso G N i).hom ≫ (homologyFunctorFactors B (up ℤ) i).hom.app (G(N.extend e))`
> `= (homologyFunctorFactors B (up ℕ) i).hom.app (G N) ≫ ((G N).extendHomologyIso e rfl).inv ≫`
> `HomologicalComplex.homologyMap (mapExtendIso G e N).hom i`

— is `Stacks.DerivedIndexing.extendMapHomologyIso_hom_comp_homologyFunctorFactors`. It is not
`rfl`: `extendHomotopyHomologyNatIso_hom_app_quotient` above is its first half,
`Stacks.DerivedIndexing.mapExtendHomotopyNatIso_hom_app`, which is `rfl`, is its second, and
what joins them is the naturality of `HomotopyCategory.homologyFunctorFactors` together with the
observation the implementation notes of `StacksFrontier/Homology/DerivedIndexing/Extend.lean`
record — that
`ComplexShape.Embedding.extendHomotopyFunctorFactors` and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` are `CategoryTheory.Iso.refl`, so that the
object `(G.mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj N)` and the object
`(HomotopyCategory.quotient _ _).obj ((G.mapHomologicalComplex _).obj N)` must be reconciled in
argument position and not by a rewrite. It cannot live in this file: it names
`extendMapHomologyIso`, which is declared in `Homology/DerivedIndexing/Composite.lean`, a module
this one does not import, so it lives in `EdgeMorphismExtendComposite.lean`, above both.

The other end of the residue is also in the tree and is **not** owed:
`Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient` evaluates the transported
comparison at the image of a complex, in terms of `homologyComparison` and the factorisations of
the cohomology functor, and `Stacks.EdgeCompat.factorsh_hom_app_comp_map_mapHomotopyCategory`
`Factors` is the crossing it absorbs.

**The mirror is proved.** The displayed equation is
`Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv`
(`AlgebraicGeometry/TopDegreeBaseChange/EdgeCompatCollapseMirror.lean`), and the two results
above are consumed by its residue,
`Stacks.Cohomology.AffineBase.rightDerivedIsoRes_comp_homologyComparison`
(`AlgebraicGeometry/AffineCohomologyVanishing/AffineBaseCompositionResidue.lean`), which is the
statement left of the mirror once every derived functor and every unit has been cancelled out of
it. The ingredients the paragraphs above name are the ones the two files use:

* the two crossings, by `singleCompDerivedCompHomologyIsoRightDerived_hom_app_res`
  (`Algebra/Homology/DerivedCategory/DerivedFunctorSingleRightDerived.lean`), which reads the
  crossing off its construction — `Hⁿ(Rw(X[0] ≅ Qh(resH X)))`, the unit of `Rw` at the extended
  chosen resolution inverted, the derived category's cohomology factorisation, and
  `rightDerivedIsoRes` inverted — rather than through
  `CategoryTheory.Functor.boundedDerivedIso`, which is the route
  `singleCompDerivedCompHomologyIsoRightDerived_hom_app` takes and which cancels against 089W
  instead;
* the edge morphism at a complex, by `derivedHomologyComparison_fac_app` and
  `Stacks.EdgeCompat.homotopyHomologyComparisonToDerived_app_quotient`;
* the residue, by the chain of the two paragraphs above.

The splitting of the edge morphism, `Stacks.EdgeCompat.derivedHomologyComparison_comp`, is **not**
used: the composite's own edge morphism lands in `(F ⋙ G)(Hⁿ(X[0]))`, which is zero for `n ≠ 0`,
so the whole split says nothing at a single complex. What the mirror uses in its place is `hθ`
together with the naturality of `θ` at the comparison of the object with its extended chosen
resolution and the naturality of the edge morphism of `G`, which is the assembly
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/EdgeCompatCollapseMirror.lean` performs.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe v v' u u'

/-! ### The chases, on variables -/

section Abstract

variable {C : Type*} [Category* C]

/-- The first two factors of a three-fold composite replaced by a known value. At variables. -/
private theorem comp_two {P Q R S T : C} (p : P ⟶ Q) (a : Q ⟶ R) (r : R ⟶ S) {cm : P ⟶ T}
    {pi : T ⟶ R} (h : p ≫ a = cm ≫ pi) : p ≫ a ≫ r = cm ≫ pi ≫ r := by
  rw [← Category.assoc p, h, Category.assoc]

/-- **The chase down a four-fold composite whose three consecutive pairs are known.** Each
hypothesis replaces one pair by a factorisation through a new object, and the last collects the
three leading factors into a single known morphism. At variables. -/
private theorem chase_left {P Q R S T U V W : C} {p : P ⟶ Q} {a : Q ⟶ R} {b : R ⟶ S} {k : S ⟶ T}
    {cm : P ⟶ U} {pi : U ⟶ R} (h1 : p ≫ a = cm ≫ pi)
    {cc : U ⟶ V} {g : V ⟶ S} (h2 : pi ≫ b = cc ≫ g)
    {gc : V ⟶ W} {gp : W ⟶ T} (h3 : g ≫ k = gc ≫ gp)
    {x : P ⟶ W} (h4 : cm ≫ cc ≫ gc = x) : p ≫ a ≫ b ≫ k = x ≫ gp := by
  rw [← h4]
  simp only [Category.assoc]
  rw [← Category.assoc p, h1]
  simp only [Category.assoc]
  rw [← Category.assoc pi, h2]
  simp only [Category.assoc, h3]

/-- The last two factors of a three-fold composite replaced by a known value, and then the
whole. At variables. -/
private theorem comp_tail {P Q R S T : C} (u : P ⟶ Q) {v : Q ⟶ R} {m : R ⟶ S} {vm : Q ⟶ S}
    (h1 : v ≫ m = vm) {w : P ⟶ T} {z : T ⟶ S} (h2 : u ≫ vm = w ≫ z) :
    u ≫ v ≫ m = w ≫ z := by rw [h1, h2]

/-- A known identity of second factors, read under a leading morphism given explicitly. At
variables, so that the leading morphism's target and the identity's source — the two spellings
of one object — are reconciled in argument position. -/
private theorem congr_tail {P Q R : C} (x : P ⟶ Q) {v w : Q ⟶ R} (h : v = w) :
    x ≫ v = x ≫ w := by rw [h]

/-- Two three-fold composites that agree after a monomorphism agree. At variables. -/
private theorem mono_pair {P Q R S T U V : C} (m : S ⟶ T) [Mono m] {a : P ⟶ Q} {b : Q ⟶ R}
    {k : R ⟶ S} {u : P ⟶ U} {v : U ⟶ S} {w : P ⟶ V} {z : V ⟶ T}
    (h1 : a ≫ b ≫ k ≫ m = w ≫ z) (h2 : u ≫ v ≫ m = w ≫ z) : a ≫ b ≫ k = u ≫ v := by
  refine (cancel_mono m).1 ?_
  simp only [Category.assoc]
  rw [h1, h2]

/-- Two composites that agree after an epimorphism on the left agree. At variables. -/
private theorem epi_pair {P Q R S T U : C} (p : P ⟶ Q) [Epi p] {a : Q ⟶ R} {b : R ⟶ S}
    {k : S ⟶ T} {u : Q ⟶ U} {v : U ⟶ T} (h1 : p ≫ a ≫ b ≫ k = p ≫ u ≫ v) :
    a ≫ b ≫ k = u ≫ v :=
  (cancel_epi p).1 h1

/-- A functor carries an equality of two-fold composites to an equality of composites. -/
private theorem map_comp_eq_map_comp {D : Type*} [Category* D] (G : C ⥤ D) {P Q R S : C}
    {f : P ⟶ Q} {g : Q ⟶ R} {f' : P ⟶ S} {g' : S ⟶ R} (h : f ≫ g = f' ≫ g') :
    G.map f ≫ G.map g = G.map f' ≫ G.map g' := by
  rw [← G.map_comp, ← G.map_comp, h]

end Abstract

/-! ### The homotopy-category comparison of the two indexings, read at a complex -/

section Lift

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} {A : Type u}
  [Category.{v} A] [Preadditive A] [HasZeroObject A] [CategoryWithHomology A]
  (e : c.Embedding c') [e.IsRelIff] {j : ι} {j' : ι'} (hj : e.f j = j')

/-- **`Stacks.DerivedIndexing.extendHomotopyHomologyNatIso` at the image of a complex.** It is
the lift along the quotient functor of a four-fold composite, and
`CategoryTheory.Quotient.natTransLift_app` evaluates such a lift at the image of an object on the
nose, so the component is that composite: the degree-`j'` homotopy-category homology of the
factorisation of `ComplexShape.Embedding.extendHomotopyFunctor`, the factorisation of the
degree-`j'` homotopy-category homology at the extended complex,
`HomologicalComplex.extendHomologyIso`, and the factorisation of the degree-`j`
homotopy-category homology inverted.

Stated as a `rfl` lemma so that the identification is performed once, where no rewrite has to
match a pattern against a term whose type involves the quotient's lift. -/
public theorem extendHomotopyHomologyNatIso_hom_app_quotient (K : HomologicalComplex A c) :
    (Stacks.DerivedIndexing.extendHomotopyHomologyNatIso e hj).hom.app
        ((HomotopyCategory.quotient A c).obj K) =
      (HomotopyCategory.homologyFunctor A c' j').map
          ((e.extendHomotopyFunctorFactors A).hom.app K) ≫
        (HomotopyCategory.homologyFunctorFactors A c' j').hom.app ((e.extendFunctor A).obj K) ≫
          (K.extendHomologyIso e hj).hom ≫
            (HomotopyCategory.homologyFunctorFactors A c j).inv.app K :=
  rfl

end Lift

/-! ### The comparison across an embedding of shapes -/

section Extend

variable {ι : Type*} {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ))
  {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] (N : HomologicalComplex A c)
  {j : ι} {j' : ℤ} (hj' : e.f j = j') [G.PreservesLeftHomologyOf (N.sc j)]

omit [Abelian B] [G.Additive] [G.PreservesLeftHomologyOf (N.sc j)] in
/-- **`G` applied to the inclusion of cycles is a monomorphism**, for a complex indexed by an
arbitrary shape. `mono_map_iCycles` says this for a cochain complex indexed by `ℤ`, by exhibiting
the image of the inclusion as a kernel fork; here it is simply that a functor preserving finite
limits preserves monomorphisms, which `CategoryTheory.preservesMonomorphisms_of_preservesLimits`
`OfShape` supplies and which the inclusion of cycles being a monomorphism then transports. The
instance is named in a `have` because its synthesis is what the conclusion rests on. -/
private theorem mono_map_iCycles' : Mono (G.map (N.iCycles j)) := by
  have : G.PreservesMonomorphisms := inferInstance
  infer_instance

/-- **The cycles comparison of a left exact functor is carried across extension by zero.** For
an embedding of shapes `e`, a complex `N` indexed by the source shape, a degree `j` with
`e.f j = j'`, and an additive left exact `G` preserving the left homology of the degree-`j`
short complex of `N`, the comparison `Z^{j'}(G(N.extend e)) ⟶ G(Z^{j'}(N.extend e))`, read
through `HomologicalComplex.extendCyclesIso` at either end and through
`Stacks.DerivedIndexing.mapExtendIso`, is `CategoryTheory.ShortComplex.mapCyclesIso` for `G` on
the degree-`j` short complex of `N`.

Both sides are computed by cancelling the monomorphism `G` applied to the inclusion of cycles:
on the left `cyclesComparison_comp_map_iCycles` and
`HomologicalComplex.extendCyclesIso_hom_iCycles`, on the right
`CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles` and the same extension identity at the
image complex. -/
public theorem extendCyclesIso_comp_cyclesComparison :
    HomologicalComplex.cyclesMap (Stacks.DerivedIndexing.mapExtendIso G e N).hom j' ≫
        cyclesComparison G (N.extend e) j' ≫ G.map ((N.extendCyclesIso e hj').hom) =
      (((G.mapHomologicalComplex c).obj N).extendCyclesIso e hj').hom ≫
        ((N.sc j).mapCyclesIso G).hom := by
  have := mono_map_iCycles' G N (j := j)
  have hleft := map_comp_eq_map_comp G (N.extendCyclesIso_hom_iCycles e hj')
  have hL : HomologicalComplex.cyclesMap (Stacks.DerivedIndexing.mapExtendIso G e N).hom j' ≫
        cyclesComparison G (N.extend e) j' ≫ G.map ((N.extendCyclesIso e hj').hom) ≫
          G.map (N.iCycles j) =
      (((G.mapHomologicalComplex c).obj N).extend e).iCycles j' ≫
        (((G.mapHomologicalComplex c).obj N).extendXIso e hj').hom := by
    rw [hleft, cyclesComparison_comp_map_iCycles_assoc, HomologicalComplex.cyclesMap_i_assoc,
      Stacks.DerivedIndexing.mapExtendIso_hom_f_comp_map_extendXIso G e N hj']
  exact mono_pair (G.map (N.iCycles j)) hL
    (comp_tail (((G.mapHomologicalComplex c).obj N).extendCyclesIso e hj').hom
      ((N.sc j).mapCyclesIso_hom_iCycles G)
      (((G.mapHomologicalComplex c).obj N).extendCyclesIso_hom_iCycles e hj'))

/-- **The homology comparison of a left exact functor is carried across extension by zero.** For
an embedding of shapes `e`, a complex `N` indexed by the source shape, a degree `j` with
`e.f j = j'`, and an additive left exact `G` preserving the left homology of the degree-`j`
short complex of `N`, the comparison `H^{j'}(G(N.extend e)) ⟶ G(H^{j'}(N.extend e))`, read
through `HomologicalComplex.extendHomologyIso` at either end and through
`Stacks.DerivedIndexing.mapExtendIso`, is `CategoryTheory.ShortComplex.mapHomologyIso` for `G`
on the degree-`j` short complex of `N`.

So a statement about the `ℤ`-indexed comparison that the edge morphism of an unbounded right
derived functor is built from is a statement about the comparison that the degreewise collapse
of [Stacks, Tag 01XK] is built from, and conversely.

The projection from cycles is an epimorphism, so the identity follows from
`extendCyclesIso_comp_cyclesComparison` together with the two factorisations of the comparisons
through it — `homologyπ_comp_homologyComparison` on the `ℤ` side and
`homologyπ_comp_mapHomologyIso_hom` on the other — and
`HomologicalComplex.homologyπ_extendHomologyIso_hom` at either complex. -/
public theorem extendHomologyIso_comp_homologyComparison :
    HomologicalComplex.homologyMap (Stacks.DerivedIndexing.mapExtendIso G e N).hom j' ≫
        homologyComparison G (N.extend e) j' ≫ G.map ((N.extendHomologyIso e hj').hom) =
      (((G.mapHomologicalComplex c).obj N).extendHomologyIso e hj').hom ≫
        ((N.sc j).mapHomologyIso G).hom := by
  have hleftG := map_comp_eq_map_comp G (N.homologyπ_extendHomologyIso_hom e hj')
  have hR := ((comp_two ((((G.mapHomologicalComplex c).obj N).extend e).homologyπ j')
        (((G.mapHomologicalComplex c).obj N).extendHomologyIso e hj').hom
        ((N.sc j).mapHomologyIso G).hom
        (((G.mapHomologicalComplex c).obj N).homologyπ_extendHomologyIso_hom e hj')).trans
      (congr_tail (((G.mapHomologicalComplex c).obj N).extendCyclesIso e hj').hom
        (homologyπ_comp_mapHomologyIso_hom (N.sc j) G))).trans
    (Category.assoc _ _ _).symm
  exact epi_pair ((((G.mapHomologicalComplex c).obj N).extend e).homologyπ j')
    ((chase_left
      (HomologicalComplex.homologyπ_naturality
        (Stacks.DerivedIndexing.mapExtendIso G e N).hom j')
      (homologyπ_comp_homologyComparison G (N.extend e) j') hleftG
      (extendCyclesIso_comp_cyclesComparison e G N hj')).trans hR.symm)

end Extend

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
