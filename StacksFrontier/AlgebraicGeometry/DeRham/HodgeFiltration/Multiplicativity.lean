module

public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration
import StacksCore.Tactic.StacksAttribute

/-!
# The Hodge filtration is multiplicative on complexes

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space and let
`Ω^•_{𝒪_X/A}` be the relative de Rham complex. Stacks Section 50.7 filters it by the brutal
truncations `σ^{≥k}Ω^•_{𝒪_X/A}` and asserts, of the wedge product `∧` of Tag 0FM2, that it
carries

`Tot(σ^{≥i}Ω^•_{𝒪_X/A} ⊗_A σ^{≥j}Ω^•_{𝒪_X/A})`

into `σ^{≥(i + j)}Ω^•_{𝒪_X/A}`. That assertion is what this file proves, and the reason it holds
is a degree count: the `(p, q)` summand of the total complex in total degree `n < i + j` has
`p < i` or `q < j`, so one of its two tensor factors is the zero subobject. The total complex
therefore vanishes in every degree below `i + j`, and the composite of `∧` with the two inclusions
of the truncations factors through the subcomplex `σ^{≥(i + j)}Ω^•_{𝒪_X/A}` uniquely.

## Main definitions

* `HomologicalComplex.subcomplexOfSubobjectsLift`: the factorisation of a morphism into a complex
  through the subcomplex cut out by a family of subobjects, when every component factors.
* `CochainComplex.liftBrutal`: the factorisation of a morphism `N ⟶ L` through `σ^{≥k}L` when `N`
  has no components in degrees below `k`.
* `AlgebraicGeometry.SheafOfModules.deRhamBrutal`: the brutal truncation `σ^{≥k}Ω^•_{𝒪_X/A}`.
* `AlgebraicGeometry.SheafOfModules.truncatedTensorSquare` and
  `AlgebraicGeometry.SheafOfModules.truncatedTensorSquareMap`:
  `Tot(σ^{≥i}Ω^•_{𝒪_X/A} ⊗_A σ^{≥j}Ω^•_{𝒪_X/A})` and the inclusions between these total complexes
  induced by the inclusions of the truncations.
* `AlgebraicGeometry.SheafOfModules.truncatedWedge`: the wedge product of Tag 0FM2 restricted to
  that total complex, as a morphism into the unfiltered `Ω^•_{𝒪_X/A}`.
* `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge`: **the multiplication
  `Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•) ⟶ σ^{≥(i + j)}Ω^•` of Section 50.7.**

## Main results

* `AlgebraicGeometry.SheafOfModules.isZero_truncatedTensorSquare_X`: the total complex vanishes in
  degrees below `i + j`, which is the degree count above.
* `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge_ιBrutal`: composing the multiplication
  with the inclusion `σ^{≥(i + j)}Ω^• ⟶ Ω^•` returns the wedge product.
* `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge_unique`: it is the only morphism with
  that property, the inclusion of a brutal truncation being a monomorphism.
* `AlgebraicGeometry.SheafOfModules.truncatedTensorSquareMap_comp_ι`: the multiplication is a
  multiplication of the filtration, deeper steps mapping to deeper steps.

## Implementation notes

**Which brutal truncation.** The truncation used here is `CochainComplex.brutal` of
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration`, the subcomplex of an `ℕ`-indexed cochain
complex cut out by the subobjects `⊤` in degrees `≥ k` and `⊥` below. That is the presentation in
which the de Rham complex carries a wedge product: the wedge product of Tag 0FM2,
`AlgebraicGeometry.SheafOfModules.wedgeProduct`, is a morphism out of the total complex
`AlgebraicGeometry.SheafOfModules.tensorSquare` of `ℕ`-indexed complexes, whose existence rests on
the instance `AlgebraicGeometry.SheafOfModules.hasMapBifunctorNat`, and no multiplication on the
`ℤ`-indexed extension `AlgebraicGeometry.SheafOfModules.deRhamComplexInt` is in the library.

`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic` presents the same truncation as
Mathlib's `HomologicalComplex.stupidTrunc` along `ComplexShape.embeddingUpIntGE p`, applied to
`deRhamComplexInt`, because filtered complexes and the Hodge filtration on hypercohomology are
stated for `ℤ`-indexed complexes. Nothing below needs the two presentations to be related;
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.BrutalPresentations` relates them, and
reads `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge` in the presentation the filtration
on hypercohomology uses.

## References

* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FM8](https://stacks.math.columbia.edu/tag/0FM8)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 0FLK](https://stacks.math.columbia.edu/tag/0FLK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Tensor (sheafTensor)
-- The additivity of `⊗_A` in each variable, and hence its preservation of zero morphisms, is
-- `Stacks.Topology.SheafTensorAdditiveOnOpens`; instance search cannot reach it on its own at the
-- open-cover site of a space, so the scoped instances are enabled here, as
-- `StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeProduct` does.
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {I : Type*} {c : ComplexShape I}

/-- **The factorisation of a morphism through a subcomplex cut out by subobjects.** If every
component of `g : N ⟶ L` factors through the subobject `F n ⊆ L.X n`, then `g` factors through
the subcomplex `subcomplexOfSubobjects L F hF`. -/
def subcomplexOfSubobjectsLift (L : HomologicalComplex C c) (F : ∀ n, Subobject (L.X n))
    (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j)) {N : HomologicalComplex C c} (g : N ⟶ L)
    (hg : ∀ n, (F n).Factors (g.f n)) : N ⟶ subcomplexOfSubobjects L F hF where
  f n := (F n).factorThru (g.f n) (hg n)
  comm' i j _ := by
    rw [← cancel_mono (F j).arrow, Category.assoc, Category.assoc]
    change (F i).factorThru (g.f i) (hg i) ≫
        (F j).factorThru ((F i).arrow ≫ L.d i j) (hF i j) ≫ (F j).arrow =
      N.d i j ≫ (F j).factorThru (g.f j) (hg j) ≫ (F j).arrow
    rw [Subobject.factorThru_arrow, Subobject.factorThru_arrow, ← Category.assoc,
      Subobject.factorThru_arrow]
    exact g.comm i j

/-- The component in degree `n` of the factorisation through a subcomplex is the factorisation
of `g.f n` through the subobject `F n`. -/
@[simp]
lemma subcomplexOfSubobjectsLift_f (L : HomologicalComplex C c) (F : ∀ n, Subobject (L.X n))
    (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j)) {N : HomologicalComplex C c} (g : N ⟶ L)
    (hg : ∀ n, (F n).Factors (g.f n)) (n : I) :
    (subcomplexOfSubobjectsLift L F hF g hg).f n = (F n).factorThru (g.f n) (hg n) :=
  rfl

/-- The factorisation through a subcomplex is one: composing it with the inclusion returns the
original morphism. -/
@[reassoc (attr := simp)]
lemma subcomplexOfSubobjectsLift_ι (L : HomologicalComplex C c) (F : ∀ n, Subobject (L.X n))
    (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j)) {N : HomologicalComplex C c} (g : N ⟶ L)
    (hg : ∀ n, (F n).Factors (g.f n)) :
    subcomplexOfSubobjectsLift L F hF g hg ≫ subcomplexOfSubobjectsι L F hF = g := by
  ext n
  exact Subobject.factorThru_arrow _ _ (hg n)

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The inclusion of a brutal truncation is a monomorphism, being the inclusion of the subcomplex
cut out by a family of subobjects. -/
instance mono_ιBrutal (L : CochainComplex C ℕ) (k : ℕ) : Mono (ιBrutal L k) :=
  inferInstanceAs (Mono (HomologicalComplex.subcomplexOfSubobjectsι L (brutalStep L k)
    (brutalStep_factors L k)))

/-- **The factorisation of a morphism through a brutal truncation.** A morphism `g : N ⟶ L^•`
whose components vanish in degrees below `k` factors through `σ^{≥k}L^•`. -/
def liftBrutal (L : CochainComplex C ℕ) (k : ℕ) {N : CochainComplex C ℕ} (g : N ⟶ L)
    (hg : ∀ n, n < k → g.f n = 0) : N ⟶ brutal L k :=
  HomologicalComplex.subcomplexOfSubobjectsLift L (brutalStep L k) (brutalStep_factors L k) g
    fun n => by
      by_cases hn : k ≤ n
      · simpa only [brutalStep, ite_eq_left hn] using Subobject.top_factors (g.f n)
      · rw [show brutalStep L k n = ⊥ from by simp [brutalStep, hn]]
        exact (Subobject.bot_factors_iff_zero _).2 (hg n (Nat.lt_of_not_le hn))

/-- The factorisation through a brutal truncation is one: composing it with the inclusion
`σ^{≥k}L^• ⟶ L^•` returns the original morphism. -/
@[reassoc (attr := simp)]
lemma liftBrutal_ι (L : CochainComplex C ℕ) (k : ℕ) {N : CochainComplex C ℕ} (g : N ⟶ L)
    (hg : ∀ n, n < k → g.f n = 0) : liftBrutal L k g hg ≫ ιBrutal L k = g :=
  HomologicalComplex.subcomplexOfSubobjectsLift_ι _ _ _ _ _

end CochainComplex

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

-- `abelianModules`, `hasSheafifyOpens` and `wEqualsLocallyBijectiveOpens` are `local instance`s
-- of `WedgeFiltration`, and `local` scopes the attribute rather than the name, so the three are
-- re-enabled here instead of being declared again. The last two are what let
-- `SheafOfModules.instAbelian` be found at `Stacks.SheafOfModules.Tensor.ringSheaf A`: without
-- them the search for them is what thrashes, since it must solve `max ?v u =?= u` for the
-- category level of `Opens X.carrier` first.
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- An additive functor of two variables sends a zero object in its first variable to a zero
object. -/
lemma isZero_tensorFunctor_obj_obj_of_left
    {M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (hM : IsZero M)
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) :
    IsZero (((sheafTensor.{u, u, u, u, u} A).obj M).obj N) :=
  ((sheafTensor.{u, u, u, u, u} A).map_isZero hM).obj N

/-- An additive functor of two variables sends a zero object in its second variable to a zero
object. -/
lemma isZero_tensorFunctor_obj_obj_of_right
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    {N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (hN : IsZero N) :
    IsZero (((sheafTensor.{u, u, u, u, u} A).obj M).obj N) :=
  ((sheafTensor.{u, u, u, u, u} A).obj M).map_isZero hN

/-! ### The total complex of a tensor product of two brutal truncations -/

/-- `σ^{≥k}Ω^•_{𝒪_X/A}`, the `k`-th brutal truncation of the relative de Rham complex: the
subcomplex which agrees with `Ω^•_{𝒪_X/A}` in degrees `≥ k` and vanishes below `k`. -/
abbrev deRhamBrutal (k : ℕ) :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ :=
  CochainComplex.brutal (deRhamComplex B D) k

/-- **The tensor product over `A`, as a bifunctor on `ℕ`-indexed cochain complexes of sheaves of
`A`-modules.** It is the generic
`CochainComplex.bifunctorNat` of
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.WedgeImageSystem` at
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the bifunctor the wedge map
`CochainComplex.wedgeAlong` and the total-complex instance
`AlgebraicGeometry.SheafOfModules.hasMapBifunctorNat` of `WedgeFiltration` are stated over.

The ring sheaf is named here as `Stacks.SheafOfModules.Tensor.ringSheaf A`, the spelling
`Stacks.SheafOfModules.Tensor.sheafTensor` and `deRhamComplex` carry, rather than as the
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A` of the surrounding development: the two
are definitionally equal but only at default transparency, so at the other spelling every
instance goal raised by this bifunctor — its preservation of zero morphisms in each variable
above all — is posed at a type instance search cannot match against the additivity of
`Stacks.Topology.SheafTensorAdditiveOnOpens`. -/
abbrev tensorBifunctorNat :
    CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ ⥤
      CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ ⥤
        CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ :=
  CochainComplex.bifunctorNat (sheafTensor.{u, u, u, u, u} A)

/-- **`Tot(σ^{≥i}Ω^•_{𝒪_X/A} ⊗_A σ^{≥j}Ω^•_{𝒪_X/A})`**, the total complex of the tensor product
over `A` of two brutal truncations of the relative de Rham complex. -/
abbrev truncatedTensorSquare (i j : ℕ) :=
  ((tensorBifunctorNat (A := A)).obj (deRhamBrutal B D i)).obj (deRhamBrutal B D j)

/-- The inclusion `Tot(σ^{≥i'}Ω^• ⊗_A σ^{≥j'}Ω^•) ⟶ Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•)` of total
complexes induced by the inclusions of brutal truncations, for `i ≤ i'` and `j ≤ j'`. -/
def truncatedTensorSquareMap {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    truncatedTensorSquare B D i' j' ⟶ truncatedTensorSquare B D i j :=
  ((tensorBifunctorNat (A := A)).map (CochainComplex.brutalMap (deRhamComplex B D) hi)).app
      (deRhamBrutal B D j') ≫
    ((tensorBifunctorNat (A := A)).obj (deRhamBrutal B D i)).map
      (CochainComplex.brutalMap (deRhamComplex B D) hj)

/-- **`Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•)` vanishes in every degree below `i + j`.** In total degree
`n` the summands are indexed by the pairs `(p, q)` with `p + q = n`; if `n < i + j` then every
such pair has `p < i` or `q < j`, so one of the two tensor factors is the zero subobject and the
summand vanishes. -/
lemma isZero_truncatedTensorSquare_X (i j n : ℕ) (hn : n < i + j) :
    IsZero ((truncatedTensorSquare B D i j).X n) := by
  change IsZero ((HomologicalComplex.mapBifunctor (deRhamBrutal B D i) (deRhamBrutal B D j)
    (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ)).X n)
  refine HomologicalComplex₂.isZero_total_X_of_isZero _ _ n fun p q hpq => ?_
  have hpq' : p + q = n := hpq
  change IsZero (((sheafTensor.{u, u, u, u, u} A).obj ((deRhamBrutal B D i).X p)).obj
    ((deRhamBrutal B D j).X q))
  rcases Nat.lt_or_ge p i with hp | hp
  · exact isZero_tensorFunctor_obj_obj_of_left
      (CochainComplex.isZero_brutal_X (k := i) (n := p) (deRhamComplex B D) (by omega)) _
  · exact isZero_tensorFunctor_obj_obj_of_right _
      (CochainComplex.isZero_brutal_X (k := j) (n := q) (deRhamComplex B D) (by omega))

/-! ### The multiplication of the Hodge filtration -/

/-- **The wedge product of Tag 0FM2 restricted to the brutal truncations**, as a morphism
`Tot(σ^{≥i}Ω^• ⊗_A σ^{≥j}Ω^•) ⟶ Ω^•_{𝒪_X/A}` into the unfiltered de Rham complex: the two
inclusions `σ^{≥i}Ω^• ⟶ Ω^•` and `σ^{≥j}Ω^• ⟶ Ω^•` tensored, followed by `∧`. -/
def truncatedWedge (i j : ℕ) : truncatedTensorSquare B D i j ⟶ deRhamComplex B D :=
  ((tensorBifunctorNat (A := A)).obj (deRhamBrutal B D i)).map
      (CochainComplex.ιBrutal (deRhamComplex B D) j) ≫
    CochainComplex.wedgeAlong (sheafTensor.{u, u, u, u, u} A) (wedgeProduct B D)
      (deRhamBrutal B D i) (CochainComplex.ιBrutal (deRhamComplex B D) i)

/-- **The multiplication of the Hodge filtration**

`Tot(σ^{≥i}Ω^•_{𝒪_X/A} ⊗_A σ^{≥j}Ω^•_{𝒪_X/A}) ⟶ σ^{≥(i + j)}Ω^•_{𝒪_X/A}`

induced by the wedge product of Tag 0FM2: the restriction of `∧` to the brutal truncations lands
in the `(i + j)`-th step of the filtration, because its source vanishes in every lower degree
(`AlgebraicGeometry.SheafOfModules.isZero_truncatedTensorSquare_X`). -/
@[stacks 0FM7 "the wedge product of equation 0FM2 sends \
Tot(σ^{≥i}Ω^•_{X/S} ⊗_{p⁻¹𝒪_S} σ^{≥j}Ω^•_{X/S}) into σ^{≥(i+j)}Ω^•_{X/S}: the multiplication \
of the Hodge filtration on complexes. One assertion of the section; the hypercohomology \
diagrams it leads to are registered on `truncatedDeRhamCohomologyAbelianMap_hodgeFiltrationCup` \
and `deRhamCup_mem_hodgeFiltrationAbelian`, and the filtration, its graded \
pieces and its spectral sequence on the declarations named in this file's module docstring"]
def hodgeFiltrationWedge (i j : ℕ) :
    truncatedTensorSquare B D i j ⟶ deRhamBrutal B D (i + j) :=
  CochainComplex.liftBrutal (deRhamComplex B D) (i + j) (truncatedWedge B D i j)
    fun n hn => (isZero_truncatedTensorSquare_X B D i j n hn).eq_of_src _ _

/-- **The multiplication of the Hodge filtration is the wedge product**: composing it with the
inclusion `σ^{≥(i + j)}Ω^• ⟶ Ω^•_{𝒪_X/A}` returns `∧` restricted to the truncations. -/
@[reassoc (attr := simp), stacks 0FM7 "that the morphism \
Tot(σ^{≥i}Ω^• ⊗ σ^{≥j}Ω^•) ⟶ σ^{≥(i+j)}Ω^• of the previous declaration really is the wedge \
product of equation 0FM2, i.e. that it lies over ∧ under the inclusion σ^{≥(i+j)}Ω^• ⟶ Ω^•. \
Without this the previous declaration would be some morphism into the (i+j)-th step rather than \
the section's assertion about ∧"]
theorem hodgeFiltrationWedge_ιBrutal (i j : ℕ) :
    hodgeFiltrationWedge B D i j ≫ CochainComplex.ιBrutal (deRhamComplex B D) (i + j) =
      truncatedWedge B D i j :=
  CochainComplex.liftBrutal_ι _ _ _ _

/-- **The tensor product of the two inclusions is compatible with the filtration**: restricting
both tensor factors to deeper steps of the Hodge filtration and then including them into
`Tot(Ω^• ⊗_A Ω^•)` is including the deeper steps.

Composing with the wedge product of Tag 0FM2 gives the same statement for
`AlgebraicGeometry.SheafOfModules.truncatedWedge`. -/
theorem truncatedTensorSquareMap_comp_ι {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    truncatedTensorSquareMap B D hi hj ≫
        ((tensorBifunctorNat (A := A)).obj (deRhamBrutal B D i)).map
          (CochainComplex.ιBrutal (deRhamComplex B D) j) ≫
        ((tensorBifunctorNat (A := A)).map
          (CochainComplex.ιBrutal (deRhamComplex B D) i)).app (deRhamComplex B D) =
      ((tensorBifunctorNat (A := A)).obj (deRhamBrutal B D i')).map
          (CochainComplex.ιBrutal (deRhamComplex B D) j') ≫
        ((tensorBifunctorNat (A := A)).map
          (CochainComplex.ιBrutal (deRhamComplex B D) i')).app (deRhamComplex B D) := by
  rw [truncatedTensorSquareMap]
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp, CochainComplex.brutalMap_ι]
  slice_lhs 1 2 => rw [← ((tensorBifunctorNat (A := A)).map
    (CochainComplex.brutalMap (deRhamComplex B D) hi)).naturality]
  slice_lhs 2 3 => rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
    CochainComplex.brutalMap_ι]

/-- **The multiplication of the Hodge filtration is the unique one** lying over the wedge product:
the inclusion of a brutal truncation is a monomorphism, so a morphism into `σ^{≥(i + j)}Ω^•` is
determined by its composite with that inclusion. -/
theorem hodgeFiltrationWedge_unique (i j : ℕ)
    (g : truncatedTensorSquare B D i j ⟶ deRhamBrutal B D (i + j))
    (hg : g ≫ CochainComplex.ιBrutal (deRhamComplex B D) (i + j) = truncatedWedge B D i j) :
    g = hodgeFiltrationWedge B D i j := by
  rw [← cancel_mono (CochainComplex.ιBrutal (deRhamComplex B D) (i + j)), hg,
    hodgeFiltrationWedge_ιBrutal]

end AlgebraicGeometry.SheafOfModules

end
