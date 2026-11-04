module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a homotopy colimit

Let `(C, O)` be a ringed site, let `(Kₙ, fₙ)` be a system of objects of `D(O)`, let
`K = hocolim Kₙ` and let `E` be an object of `D(O)`.  **Stacks 0A0A** says that when
the `Kₙ` are perfect

`RSheafHom(K, E) = R lim (E ⊗^L_O Kₙ^∨)`,

the right-hand side being the derived limit of the inverse system of tensor products with the
dual perfect complexes.

The source's proof has two halves.  The formal half rewrites the right-hand side as
`R lim RSheafHom(Kₙ, E)` and compares the triangle defining that derived limit with the image
under `RSheafHom(-, E)` of the triangle `⊕ Kₙ → ⊕ Kₙ → K` defining the derived colimit; the
comparison needs `RSheafHom(⊕ Kₙ, E) = ∏ RSheafHom(Kₙ, E)`.  The other half is the rewriting
itself, which is clause 3 of **Stacks 08JJ**: the canonical map
`E ⊗^L_O Kₙ^∨ ⟶ RSheafHom(Kₙ, E)` of Stacks 08JD is an isomorphism when `Kₙ` is perfect.

This file proves the formal half in full and assembles the two, carrying each of the two inputs
it does not prove as an explicit hypothesis.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality_source`: the canonical map
  of Stacks 08JD is contravariantly functorial in the object being dualized.  Stacks 08JD records
  functoriality in the other variable only, which is
  `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality`.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit`:
  `RSheafHom(hocolim Kₙ, E) = R lim RSheafHom(Kₙ, E)`, granted that the canonical map
  `RSheafHom(⊕ Kₙ, E) ⟶ ∏ RSheafHom(Kₙ, E)` is an isomorphism.  No perfectness is needed.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit`:
  **Stacks 0A0A**, granted that same isomorphism and clause 3 of Stacks 08JJ for each `Kₙ`.

## Implementation notes

The triangulated bookkeeping is carried out once and for all in
`CategoryTheory.Pretriangulated.isDerivedLimit_of_isHomotopyColimit`, for an arbitrary additive
functor `H : Dᵒᵖ ⥤ D'` between pre-triangulated categories which carries distinguished triangles
to distinguished triangles.  Here `H` is `RSheafHom(-, E)`; the triangle hypothesis is Stacks
08JC in its contravariant variable,
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`, and the additivity is
`AlgebraicGeometry.RingedSite.additive_derivedSheafHom_flip_obj`.

The two systems are `AlgebraicGeometry.RingedSite.derivedSheafHomSystem` and
`AlgebraicGeometry.RingedSite.tensorDerivedDualSystem`.

**No existence assumption is carried.** `CategoryTheory.Pretriangulated.IsHomotopyColimit` and
`CategoryTheory.Pretriangulated.IsDerivedLimit` mention `⊕ Kₙ` and `∏` of the system in their very
types, so each takes a `Limits.HasCoproduct` or `Limits.HasProduct` instance argument.  Those are
not hypotheses of the source: a derived category of modules has all direct sums and all products.
Here they are discharged by instance search, from the two unconditional instances of Stacks 07D9
for the derived category of a Grothendieck abelian category,
`Stacks.Injectives.hasCoproducts_derivedCategory` and
`Stacks.Injectives.hasProducts_derivedCategory`, together with the Grothendieck abelianness of
sheaves of modules on a site, `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`.  Nothing
new is proved for this; the module
`StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts` is imported for those
instances.  The two systems are `abbrev`s rather than `def`s so that instance search sees that
their values are objects of `D(O)` rather than stopping at an opaque constant.

Perfectness of the `Kₙ` is *not* a hypothesis of the main theorem.  In the source it is used for
exactly one thing, namely to invoke clause 3 of Stacks 08JJ; since that clause is carried here as
the hypothesis `hdual`, assuming perfectness in addition would restrict the statement without
strengthening it.

## What this file does not contain

Neither of the two hypotheses of
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit` is
discharged here, and no declaration below asserts either of them. Both are discharged
elsewhere: the direct sum comparison by
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts`, and `hdual` by
being unnecessary at a perfect `Kₙ` —
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isPerfect` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorDerivedLimit`
replaces the canonical map by the isomorphism of Stacks 08JJ that is available there.

* **The direct sum comparison.** That the canonical map
  `RSheafHom(⊕ Kₙ, E) ⟶ ∏ RSheafHom(Kₙ, E)` is an isomorphism is the last step of the source's
  proof.  The library has the analogous statement in the *covariant* variable and for a constant
  family only, `AlgebraicGeometry.RingedSite.preservesLimit_derivedSheafHom`, whose complex-level
  input is `AlgebraicGeometry.RingedSite.isIso_homPiComparison`; the contravariant counterpart
  `SheafHom(⊕ Aⱼ, I) ≅ ∏ SheafHom(Aⱼ, I)` is not in the library, so the reduction to complexes
  that `preservesLimit_derivedSheafHom` performs — through
  `StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts` for the identification of the direct
  sum in `D(O)` with the termwise one, and through
  `AlgebraicGeometry.RingedSite.isLimit_fan_Q_pi` for the product — cannot be run in that
  variable yet.
* **Clause 3 of Stacks 08JJ, in the shape `hdual` takes it:** that the canonical map of
  Stacks 08JD, `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`, is an isomorphism.
  The clause itself is available — `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom` is the isomorphism
  `M ⊗^L_O K^∨ ≅ RSheafHom(K, M)` for perfect `K` — but it is built from the diagonal of
  Stacks 0BYS rather than from that canonical map, and the two morphisms are nowhere compared;
  the section "What this file does not contain" of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals` records that no declaration of the
  library asserts *this* map to be an isomorphism. So `hdual` stays a hypothesis.

## References

* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The inverse system `n ↦ RSheafHom(Kₙ, E)` attached to a system `F : ℕ ⥤ D(O)` of objects of
`D(O)` and an object `E` of `D(O)`. -/
abbrev derivedSheafHomSystem
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  F.op ⋙ (derivedSheafHomBifunctor X).flip.obj E

/-- **Derived internal Hom out of a derived colimit is the derived limit of the derived internal
Homs out of the terms**: if `K = hocolim Kₙ` and the canonical map
`RSheafHom(⊕ Kₙ, E) ⟶ ∏ RSheafHom(Kₙ, E)` is an isomorphism, then
`RSheafHom(K, E) = R lim RSheafHom(Kₙ, E)`.

This is the formal half of Stacks 0A0A, and holds for an arbitrary system of objects of `D(O)`:
no perfectness is involved, and neither the direct sum nor the product is assumed to exist, both
being supplied by the instances of Stacks 07D9.  The input is Stacks 08JC in its contravariant
variable, which makes
`RSheafHom(-, E)` carry the triangle `⊕ Kₙ → ⊕ Kₙ → K → (⊕ Kₙ)⟦1⟧` defining the derived colimit
to a distinguished triangle; the comparison isomorphism then turns its middle morphism into the
difference morphism of the system `n ↦ RSheafHom(Kₙ, E)`. -/
theorem isDerivedLimit_derivedSheafHom_of_isHomotopyColimit
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hcomp : IsIso (Pi.lift (fun n : ℕ ↦
        ((derivedSheafHomBifunctor X).flip.obj E).map (Sigma.ι F.obj n).op) :
      ((derivedSheafHomBifunctor X).flip.obj E).obj (op (∐ F.obj)) ⟶
        ∏ᶜ fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (derivedSheafHomSystem X F E)
      (((derivedSheafHomBifunctor X).flip.obj E).obj (op K)) :=
  isDerivedLimit_of_isHomotopyColimit ((derivedSheafHomBifunctor X).flip.obj E) F
    (fun T hT ↦ exists_distinguished_derivedSheafHom X E T hT) hcomp hK

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The canonical map `M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)` of Stacks 08JD is contravariantly
functorial in `L`.**  A morphism `f : L' ⟶ L` acts on the duals by `RSheafHom(f, O)` and on the
internal Homs by `RSheafHom(f, M)`, and the canonical map intertwines the two.

This is the contravariant naturality of the composition morphism of Stacks 0A98 in its source
object, together with the naturality in the dualized object of the identification of `M` with
`RSheafHom(O, M)` — which here is trivial, the identification not depending on `L`, so what is
used is the naturality of the natural transformation `M ⊗^L_O - ⟶ RSheafHom(O, M) ⊗^L_O -`.

The two sides are spelled out rather than produced by unfolding the canonical map, for the reason
recorded with `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality`: the source of
derived composition and the tensor product with the dual agree only at default transparency. -/
theorem derivedTensorDualToSheafHom_naturality_source
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : L' ⟶ L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (T.tensor.obj M).map
          (((derivedSheafHomBifunctor X).map f.op).app (derivedStructureSheaf X)) ≫
        derivedTensorDualToSheafHom X T L' M =
      derivedTensorDualToSheafHom X T L M ≫ ((derivedSheafHomBifunctor X).map f.op).app M := by
  have hnat : derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
          (derivedStructureSheaf X) M ≫ ((derivedSheafHomBifunctor X).map f.op).app M =
      (T.tensor.obj (((derivedSheafHomBifunctor X).obj
            (op (derivedStructureSheaf X))).obj M)).map
          (((derivedSheafHomBifunctor X).map f.op).app (derivedStructureSheaf X)) ≫
        derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L'
          (derivedStructureSheaf X) M :=
    (derivedSheafHomCompositionConstruction X T (derivedInternalHomOfBifunctor X)).natural_source f
  have hsq : (T.tensor.obj M).map
          (((derivedSheafHomBifunctor X).map f.op).app (derivedStructureSheaf X)) ≫
        (T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L') =
      (T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L) ≫
        (T.tensor.obj (((derivedSheafHomBifunctor X).obj
            (op (derivedStructureSheaf X))).obj M)).map
          (((derivedSheafHomBifunctor X).map f.op).app (derivedStructureSheaf X)) :=
    (T.tensor.map (derivedStructureSheafHomIso X M).inv).naturality _
  have key : (T.tensor.obj M).map
          (((derivedSheafHomBifunctor X).map f.op).app (derivedStructureSheaf X)) ≫
        ((T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L') ≫
          derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L'
            (derivedStructureSheaf X) M) =
      ((T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L) ≫
          derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
            (derivedStructureSheaf X) M) ≫
        ((derivedSheafHomBifunctor X).map f.op).app M := by
    rw [Category.assoc, hnat, ← Category.assoc, ← Category.assoc, hsq]
  exact key

/-- The inverse system `n ↦ E ⊗^L_O Kₙ^∨` attached to a system `F : ℕ ⥤ D(O)` of objects of `D(O)`
and an object `E` of `D(O)`: the opposite system followed by the derived dual and by the derived
tensor product with `E`. -/
abbrev tensorDerivedDualSystem
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  F.op ⋙ (derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X) ⋙ T.tensor.obj E

/-- The system `n ↦ E ⊗^L_O Kₙ^∨` is isomorphic to the system `n ↦ RSheafHom(Kₙ, E)` as soon as
the canonical map of Stacks 08JD is an isomorphism at every term.  The isomorphism is that
canonical map, and its naturality is
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_naturality_source`. -/
def tensorDerivedDualSystemIso
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hdual : ∀ n : ℕ, IsIso (derivedTensorDualToSheafHom X T (F.obj n) E)) :
    tensorDerivedDualSystem X T F E ≅ derivedSheafHomSystem X F E :=
  NatIso.ofComponents
    (fun n ↦ haveI := hdual n.unop; asIso (derivedTensorDualToSheafHom X T (F.obj n.unop) E))
    (fun g ↦ derivedTensorDualToSheafHom_naturality_source X T (F.map g.unop) E)

/-- **Stacks 0A0A.**  Let `(Kₙ)` be a system of objects of `D(O)` and let `K = hocolim Kₙ`.  For
every object `E` of `D(O)`,

`RSheafHom(K, E) = R lim (E ⊗^L_O Kₙ^∨)`,

granted the two inputs the source's proof uses and the library does not have: that the canonical
map `RSheafHom(⊕ Kₙ, E) ⟶ ∏ RSheafHom(Kₙ, E)` is an isomorphism, and that the canonical map
`E ⊗^L_O Kₙ^∨ ⟶ RSheafHom(Kₙ, E)` of Stacks 08JD is an isomorphism for every `n`, which is
clause 3 of Stacks 08JJ and is where the perfectness of the `Kₙ` is used in the source.

Given the second hypothesis the tensor-dual system is isomorphic to the system
`n ↦ RSheafHom(Kₙ, E)`, so the assertion is
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit` transported
along that isomorphism. -/
@[stacks 0A0A "the stated identity `RSheafHom(K, E) = R lim (E ⊗^L_O Kₙ^∨)` for `K = hocolim Kₙ`, \
with two inputs of the source's proof assumed rather than proved: `hcomp`, that the canonical map \
`RSheafHom(⊕ Kₙ, E) ⟶ ∏ RSheafHom(Kₙ, E)` is an isomorphism, which is the last step of the \
proof; and `hdual`, clause 3 of Stacks 08JJ, that the canonical map of Stacks 08JD \
`E ⊗^L_O Kₙ^∨ ⟶ RSheafHom(Kₙ, E)` is an isomorphism, which no declaration of this library \
asserts. The perfectness of the `Kₙ` is used in the source only to invoke that clause, so it is \
not assumed here, and the existence of the direct sum `⊕ Kₙ` and of the two products is not \
assumed either, being supplied by the instances of Stacks 07D9; everything else of the tag is \
proved, in particular the whole comparison of triangles."]
theorem isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hcomp : IsIso (Pi.lift (fun n : ℕ ↦
        ((derivedSheafHomBifunctor X).flip.obj E).map (Sigma.ι F.obj n).op) :
      ((derivedSheafHomBifunctor X).flip.obj E).obj (op (∐ F.obj)) ⟶
        ∏ᶜ fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)))
    (hdual : ∀ n : ℕ, IsIso (derivedTensorDualToSheafHom X T (F.obj n) E))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (tensorDerivedDualSystem X T F E)
      (((derivedSheafHomBifunctor X).flip.obj E).obj (op K)) :=
  IsDerivedLimit.of_natIso (tensorDerivedDualSystemIso X T F E hdual).symm
    (isDerivedLimit_derivedSheafHom_of_isHomotopyColimit X F E hcomp hK)

end AlgebraicGeometry.RingedSite

end
