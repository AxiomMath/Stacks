module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafExt
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Ext sheaves computed by a strictly perfect resolution

Let `(X, O_X)` be a ringed space, let `K` be a complex of `O_X`-modules and let `P ⟶ K` be a
quasi-isomorphism from a strictly perfect complex — a bounded complex each of whose terms is a
direct summand of a finite free `O_X`-module. Then for every complex `M` and every `n` the Ext
sheaf `Ext^n_{O_X}(K, M)` is the `n`-th cohomology sheaf of the ordinary internal Hom complex

`SheafHom^•(P, M)`,

with no injective resolution of `M` entering. This is the sheaf-level counterpart of the usual
computation of `Ext` by a projective resolution: a locally free resolution of `K` replaces `K`
in the first variable, and against a strictly perfect source the derived internal Hom is already
computed by the naive Hom complex.

Combined with the degreewise description `Stacks.SheafOfModules.strictlyPerfectHomDegreeIso`,
which writes the degree-`n` term of `SheafHom^•(P, M)` as `⊕_{n = p + q} Hom_{O_X}(P^{-q}, M^p)`,
this turns a question about Ext sheaves into a question about an explicit complex of sheaves.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafExtMapIso`: the isomorphism of Ext sheaves induced by an
  isomorphism of the source and an isomorphism of the target.
* `Stacks.SheafOfModules.derivedSheafExtIsoHomologySheafHomComplex`: for a strictly perfect
  complex `P` and an isomorphism `P ≅ A` in the derived category, the identification of
  `Ext^n_{O_X}(A, M)` with `H^n(SheafHom^•(P, M))`.
* `Stacks.SheafOfModules.derivedSheafExtIsoHomologyOfResolution`: the same identification
  presented through a quasi-isomorphism `P ⟶ K` of complexes, that is through a strictly
  perfect resolution of `K`.

## Main results

* `Stacks.SheafOfModules.isIso_derivedSheafExtMap`: a map of Ext sheaves induced by two
  isomorphisms is an isomorphism.

## Implementation notes

The two forms of the main identification differ only in how the source is presented. The
derived-category form takes an isomorphism `Q(P) ≅ A` and so applies to any object of `D(O_X)`
that `P` represents; the resolution form takes a quasi-isomorphism of complexes `P ⟶ K` and
specialises the first to `A = Q(K)`. The latter is the shape a resolution provides, the former
the shape in which the statement is used when the object of the derived category is given
first.

Strict perfectness enters as the two hypotheses of Stacks 08DM: boundedness, the finiteness of
the set of degrees in which `P` does not vanish, and the termwise condition
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`, that each term be a direct summand of a
finite free module. No condition whatever is imposed on `M`.

`CategoryTheory.sheafCompose` is made `implicit_reducible` locally. The ring sheaf of
`StructureSheafModules Rc` is spelled through `sheafCompose`, while the canonical ring sheaf of a
ringed site is the syntactically different `Tensor.ringSheaf`; the two agree only after that plain
`def` is unfolded. Term elaboration unfolds it, so the statements below typecheck as written, but
instance synthesis does not, so the `Abelian` and `HasDerivedCategory` instances carried by the
type of `strictlyPerfectHomComparison_isIso` are not recognised as the ones carried by
`DerivedCategory.homologyFunctor`, and the `IsIso` of the image of the comparison under that
functor cannot be found. Several instance arguments are involved rather than one — supplying the
`IsIso` of the image positionally only moves the failure to the `IsIso` of the comparison itself
— so the attribute, which is what the files upstream of this one already use, is the structural
fix rather than a list of explicit instance arguments.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The isomorphism of Ext sheaves `Ext^n_{O_X}(K, L) ≅ Ext^n_{O_X}(K', L')` induced
contravariantly by an isomorphism `k : K' ≅ K` and covariantly by an isomorphism `l : L ≅ L'`.
Its inverse is the map induced by the two inverse isomorphisms. -/
def derivedSheafExtMapIso (n : ℤ) {K K' L L' : DerivedCategory (StructureSheafModules Rc)}
    (k : K' ≅ K) (l : L ≅ L') :
    derivedSheafExt Rc K L n ≅ derivedSheafExt Rc K' L' n where
  hom := derivedSheafExtMap Rc n k.hom l.hom
  inv := derivedSheafExtMap Rc n k.inv l.inv
  hom_inv_id := by
    rw [derivedSheafExtMap_comp, Iso.inv_hom_id, Iso.hom_inv_id, derivedSheafExtMap_id]
  inv_hom_id := by
    rw [derivedSheafExtMap_comp, Iso.hom_inv_id, Iso.inv_hom_id, derivedSheafExtMap_id]

/-- The forward map of the isomorphism `derivedSheafExtMapIso` is `derivedSheafExtMap` of
`k.hom` and `l.hom`. -/
@[simp]
theorem derivedSheafExtMapIso_hom (n : ℤ)
    {K K' L L' : DerivedCategory (StructureSheafModules Rc)} (k : K' ≅ K) (l : L ≅ L') :
    (derivedSheafExtMapIso Rc n k l).hom = derivedSheafExtMap Rc n k.hom l.hom :=
  rfl

/-- The inverse of the isomorphism `derivedSheafExtMapIso` is `derivedSheafExtMap` of `k.inv`
and `l.inv`. -/
@[simp]
theorem derivedSheafExtMapIso_inv (n : ℤ)
    {K K' L L' : DerivedCategory (StructureSheafModules Rc)} (k : K' ≅ K) (l : L ≅ L') :
    (derivedSheafExtMapIso Rc n k l).inv = derivedSheafExtMap Rc n k.inv l.inv :=
  rfl

/-- A map of Ext sheaves induced by an isomorphism of the source and an isomorphism of the
target is an isomorphism. -/
theorem isIso_derivedSheafExtMap (n : ℤ)
    {K K' L L' : DerivedCategory (StructureSheafModules Rc)}
    (k : K' ⟶ K) (l : L ⟶ L') [IsIso k] [IsIso l] :
    IsIso (derivedSheafExtMap Rc n k l) :=
  (derivedSheafExtMapIso Rc n (asIso k) (asIso l)).isIso_hom

variable (P M : CochainComplex (StructureSheafModules Rc) ℤ)

/-- **The Ext sheaves of a strictly perfect source are the cohomology sheaves of the naive Hom
complex.** For `P` bounded with every term a direct summand of a finite free `O_X`-module, and
for any object `A` of `D(O_X)` presented by an isomorphism `Q(P) ≅ A`, the Ext sheaf
`Ext^n_{O_X}(A, M)` is the `n`-th cohomology sheaf of the internal Hom complex
`SheafHom^•(P, M)`.

It is the composite of three isomorphisms: transport along `Q(P) ≅ A` in the first variable,
the inverse of the comparison of Stacks 08DM on `n`-th cohomology sheaves, and the factorisation
of the cohomology functor on the derived category through the cohomology functor on complexes.
-/
def derivedSheafExtIsoHomologySheafHomComplex (n : ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (P.X i))
    (A : DerivedCategory (StructureSheafModules Rc))
    (e : DerivedCategory.Q.obj P ≅ A) :
    derivedSheafExt Rc A (DerivedCategory.Q.obj M) n ≅
      (RingedSite.sheafHomComplex (ringedSite Rc) P M).obj.homology n :=
  derivedSheafExtMapIso Rc n e (Iso.refl _) ≪≫
    ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).mapIso
      (@asIso _ _ _ _ (strictlyPerfectHomComparison Rc P M)
        (strictlyPerfectHomComparison_isIso Rc P M hbdd hterm))).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) n).app
      (RingedSite.sheafHomComplex (ringedSite Rc) P M).obj

/-- **Ext sheaves are computed by a strictly perfect resolution.** Let `π : P ⟶ K` be a
quasi-isomorphism of complexes of `O_X`-modules with `P` bounded and every term of `P` a direct
summand of a finite free `O_X`-module. Then for every complex `M` of `O_X`-modules and every
`n`, the Ext sheaf `Ext^n_{O_X}(K, M)` is the `n`-th cohomology sheaf of the internal Hom
complex `SheafHom^•(P, M)`.

This is the special case of `derivedSheafExtIsoHomologySheafHomComplex` in which the object of
the derived category is `Q(K)` and the isomorphism `Q(P) ≅ Q(K)` is the image of the
quasi-isomorphism `π`. -/
def derivedSheafExtIsoHomologyOfResolution (n : ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (P.X i))
    {K : CochainComplex (StructureSheafModules Rc) ℤ} (π : P ⟶ K) [QuasiIso π] :
    derivedSheafExt Rc (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) n ≅
      (RingedSite.sheafHomComplex (ringedSite Rc) P M).obj.homology n :=
  have : IsIso (DerivedCategory.Q.map π) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ π).2 inferInstance
  derivedSheafExtIsoHomologySheafHomComplex Rc P M n hbdd hterm _
    (asIso (DerivedCategory.Q.map π))

end Stacks.SheafOfModules

end
