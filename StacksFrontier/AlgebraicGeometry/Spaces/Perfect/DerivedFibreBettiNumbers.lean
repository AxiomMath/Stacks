module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite

/-!
# The derived-fibre Betti numbers and Euler characteristic on an algebraic space

Let `Y` be an algebraic space over a scheme `S` and `K` an object of `D(𝒪_Y)`.  A point of `Y`
is represented by a field-valued point `p : Spec(k) ⟶ Y`.  The *derived fibre* of `K` at `p` is
the derived pullback `Lp^*K`, an object of the derived category of modules on the small étale
site of `Spec(k)`; its `n`-th cohomology sheaf is a module on that site, and its sections over
`Spec(k)` itself form a `k`-vector space.  The `n`-th derived-fibre Betti number of `K` at `p` is
the dimension of that vector space, and the derived-fibre Euler characteristic is the alternating
sum of the Betti numbers.  This is the function of Stacks 0D1Y and of Stacks 0D1Z, read through
the description of the points of `Y` of Stacks 03BU.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPoint.toSpace`: the morphism `Spec(k) ⟶ Y` of algebraic
  spaces of a field-valued point.
* `AlgebraicGeometry.Space.FieldValuedPoint.fieldToSections`: the field of definition acting on
  the sections of the structure sheaf of `Spec(k)` over `Spec(k)`.
* `AlgebraicGeometry.Space.derivedFibreBettiAt`: the dimension over `k` of the `n`-th cohomology
  of `Lp^*K` at a field-valued point `p`.
* `AlgebraicGeometry.Space.derivedFibreBetti` and `AlgebraicGeometry.Space.derivedFibreEuler`: the
  Betti numbers and the Euler characteristic as functions on the points `|Y|`.

## Main results

* `AlgebraicGeometry.Space.derivedFibreBettiAt_derivedPullback`: the derived fibre of `Lg^*K` at a
  field-valued point `p` of `Y'` is the derived fibre of `K` at the image point `g ∘ p`, for any
  morphism `g : Y' ⟶ Y`; this is the compatibility of derived fibres with composite derived
  pullback, `L(g ∘ p)^* ≅ Lp^* ∘ Lg^*` (Stacks 0D6D).

## Implementation notes

A point of `Y` is an equivalence class of field-valued points, and the two functions on `|Y|`
are evaluated at the representative `Quot.out x` of the class.  For a `K` with quasi-coherent
cohomology, in particular a perfect `K`, the value does not depend on the representative, because
a field extension `k ⊆ k'` is flat and the dimension of a vector space does not change under
extension of scalars; that independence is not used to define the functions, and it is the
theorem `AlgebraicGeometry.Space.derivedFibreBettiAt_eq_of_class_eq`.

The Euler characteristic is a `finsum` over all of `ℤ`, which is `0` unless finitely many Betti
numbers are nonzero.  This is the convention of
`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre` for schemes, with the same signs
`Int.negOnePow`; for a perfect `K` only finitely many Betti numbers are nonzero.

The derived pullback is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, whose existence
premise is supplied by
`AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy`.  The
sections over `Spec(k)` are the sections over the identity chart
`AlgebraicGeometry.Space.idChart`, the terminal object of the small étale site of `Spec(k)`, so
they are the global sections of the cohomology sheaf.

## References

* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
/- The standard model of the derived category is forced by
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FieldValuedPoint

variable {Y : AlgebraicSpaces B S hS}

/-- The morphism `Spec(k) ⟶ Y` of algebraic spaces corresponding to a field-valued point of `Y`,
by the Yoneda lemma. -/
def toSpace (p : FieldValuedPoint B S hS Y.1) : schemeSpace p.siteObject ⟶ Y :=
  ObjectProperty.homMk (yonedaEquiv.symm p.value)

/-- The field of definition of a field-valued point maps to the sections of the structure sheaf
of `Spec(k)` over the identity chart of its small étale site, which are the global sections
`Γ(Spec(k), 𝒪)`. -/
def fieldToSections (p : FieldValuedPoint B S hS Y.1) :
    RingCat.of p.carrier ⟶
      (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject)).obj.obj
        (Opposite.op (idChart B S hS p.siteObject)) :=
  (forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso (.of p.carrier)).inv

end FieldValuedPoint

variable (Y : AlgebraicSpaces B S hS)

/-- **The `n`-th derived-fibre Betti number at a field-valued point.**  For an object `K` of
`D(𝒪_Y)` and a field-valued point `p : Spec(k) ⟶ Y`, the dimension over `k` of the sections over
`Spec(k)` of the `n`-th cohomology sheaf of the derived pullback `Lp^*K`, that is,
`dim_k H^n(K ⊗^L k)`. -/
def derivedFibreBettiAt
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (p : FieldValuedPoint B S hS Y.1) : ℕ :=
  Module.finrank p.carrier
    ((ModuleCat.restrictScalars p.fieldToSections.hom).obj
      ((SheafOfModules.evaluation
          (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))
          (Opposite.op (idChart B S hS p.siteObject))).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))) n).obj
          ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj K))))

/-- **The `n`-th derived-fibre Betti number of an object of `D(𝒪_Y)`**, as a function on the
points `|Y|` of the algebraic space (Stacks 0D1Y): its value at a point is the Betti number at a
field-valued point representing it. -/
def derivedFibreBetti
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ) :
    points B S hS Y.1 → ℕ :=
  fun x => derivedFibreBettiAt Y K n (Quot.out x)

/-- **The derived-fibre Euler characteristic of an object of `D(𝒪_Y)`**, as a function on the
points `|Y|`: the alternating sum `∑ (-1)^n dim_k H^n(K ⊗^L k)` of its derived-fibre Betti
numbers (Stacks 0D1Z). -/
def derivedFibreEuler
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    points B S hS Y.1 → ℤ :=
  fun x => ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (derivedFibreBetti Y K n x : ℤ)

/-- The `n`-th derived-fibre Betti number at a point `x` of `|Y|` is the Betti number at the
representative `Quot.out x` of `x`. -/
theorem derivedFibreBetti_apply
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (x : points B S hS Y.1) :
    derivedFibreBetti Y K n x = derivedFibreBettiAt Y K n (Quot.out x) :=
  rfl

/-- The derived-fibre Euler characteristic at a point `x` of `|Y|` is the alternating sum
`∑ᶠ n, (-1)^n β_n(x)` of the derived-fibre Betti numbers at `x`. -/
theorem derivedFibreEuler_apply
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (x : points B S hS Y.1) :
    derivedFibreEuler Y K x = ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (derivedFibreBetti Y K n x : ℤ) :=
  rfl

/-- The derived-fibre Betti numbers at a field-valued point depend only on the isomorphism class
of the object. -/
theorem derivedFibreBettiAt_congr
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (e : K ≅ L) (n : ℤ) (p : FieldValuedPoint B S hS Y.1) :
    derivedFibreBettiAt Y K n p = derivedFibreBettiAt Y L n p :=
  ((ModuleCat.restrictScalars p.fieldToSections.hom).mapIso
    ((SheafOfModules.evaluation
        (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))
        (Opposite.op (idChart B S hS p.siteObject))).mapIso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))) n).mapIso
        ((smallEtaleDerivedModulePullback B S hS p.toSpace).mapIso e)))).toLinearEquiv.finrank_eq

/-- The derived-fibre Betti numbers depend only on the isomorphism class of the object. -/
theorem derivedFibreBetti_congr
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (e : K ≅ L) (n : ℤ) : derivedFibreBetti Y K n = derivedFibreBetti Y L n :=
  funext fun x => derivedFibreBettiAt_congr Y e n (Quot.out x)

/-- The derived-fibre Euler characteristic depends only on the isomorphism class of the
object. -/
theorem derivedFibreEuler_congr
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (e : K ≅ L) : derivedFibreEuler Y K = derivedFibreEuler Y L := by
  funext x
  simp only [derivedFibreEuler_apply, derivedFibreBetti_congr Y e]

/-- The morphism of a field-valued point of `Y'` followed by `g : Y' ⟶ Y` is the morphism of the
image field-valued point of `Y`. -/
theorem FieldValuedPoint.toSpace_map {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (p : FieldValuedPoint B S hS Y'.1) :
    (p.map B S hS Y'.1 g.hom).toSpace = p.toSpace ≫ g := by
  apply ObjectProperty.hom_ext
  show yonedaEquiv.symm (g.hom.app _ p.value) = yonedaEquiv.symm p.value ≫ g.hom
  rw [yonedaEquiv_symm_naturality_right]

/-- The comparison `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of derived pullbacks along a composite of morphisms
of algebraic spaces (Stacks 0D6D), from the pseudofunctor
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. -/
def derivedPullbackCompIso {Y' Z : AlgebraicSpaces B S hS} (f : Z ⟶ Y') (g : Y' ⟶ Y) :
    smallEtaleDerivedModulePullback B S hS (f ≫ g) ≅
      smallEtaleDerivedModulePullback B S hS g ⋙ smallEtaleDerivedModulePullback B S hS f :=
  (smallEtaleDerivedPullbackData B S hS).compIso f g

/-- **The derived fibres of a derived pullback.**  For `g : Y' ⟶ Y`, an object `K` of `D(𝒪_Y)` and
a field-valued point `p` of `Y'`, the derived-fibre Betti numbers of `Lg^*K` at `p` are those of
`K` at the image point `g ∘ p`. -/
theorem derivedFibreBettiAt_derivedPullback {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (p : FieldValuedPoint B S hS Y'.1) :
    derivedFibreBettiAt Y' ((smallEtaleDerivedModulePullback B S hS g).obj K) n p =
      derivedFibreBettiAt Y K n (p.map B S hS Y'.1 g.hom) := by
  unfold derivedFibreBettiAt
  have h := FieldValuedPoint.toSpace_map Y g p
  show _ = Module.finrank p.carrier
    ((ModuleCat.restrictScalars p.fieldToSections.hom).obj
      ((SheafOfModules.evaluation
          (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))
          (Opposite.op (idChart B S hS p.siteObject))).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))) n).obj
          ((smallEtaleDerivedModulePullback B S hS (p.map B S hS Y'.1 g.hom).toSpace).obj K))))
  rw [h]
  exact ((ModuleCat.restrictScalars p.fieldToSections.hom).mapIso
    ((SheafOfModules.evaluation (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))
      (Opposite.op (idChart B S hS p.siteObject))).mapIso
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (schemeSpace p.siteObject))) n).mapIso
        ((derivedPullbackCompIso Y p.toSpace g).app K)))).toLinearEquiv.finrank_eq.symm

end AlgebraicGeometry.Space

end
