module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The top truncation of a bounded above object is its top cohomology in a single degree

Let `C` be an abelian category and let `E` be an object of `D(C)` with `E` in `D^{≤n}`.  Then the
truncation `τ^{≥n}E` has its cohomology concentrated in degree `n`, where it is `Hⁿ(E)`, and is
therefore `Hⁿ(E)` placed in degree `n`:
```
τ^{≥n}E ≅ Hⁿ(E)[-n],      τ^{≥0}(E⟦n⟧) ≅ Hⁿ(E)[0].
```
The second form is the one the induction of Stacks 08HE (2) ⇒ (1) consumes: the local lifting step
`AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen` is stated at truncation degree
`0` — the obstruction it kills is the degree-`1` cohomology of `τ^{<a}`, which vanishes only for
`a ≤ 1` — so the shift is carried by the object and a surjection `𝒪^{⊕t} ⟶ Hⁿ(E)` has to be read
as a morphism into `τ^{≥0}(E⟦n⟧)`.

## Main definitions

* `DerivedCategory.truncGEIsoSingleHomologyOfIsLE`: `τ^{≥n}E ≅ Hⁿ(E)[-n]` for `E` in `D^{≤n}`.
* `DerivedCategory.truncGEZeroShiftIsoSingleHomology`: `τ^{≥0}(E⟦n⟧) ≅ Hⁿ(E)[0]` for the same `E`.

## Main results

* `DerivedCategory.epi_homologyMap_of_comp_truncGEπ`: a morphism whose composite with
  `E ⟶ τ^{≥n}E` is epic on `Hⁿ` is itself epic on `Hⁿ`.  This is what turns the lift produced by
  the affine-chart lifting step back into a map of complexes surjective on top cohomology, which
  is the hypothesis the cone computation of the induction needs.

## Implementation notes

Both isomorphisms are read off the natural isomorphism
`DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`, which identifies the *one-step*
truncation `τ^{≥q}τ^{<q+1}` with `H^q ⋙ single q`.  The hypothesis `E ∈ D^{≤n}` is exactly what
makes `τ^{<n+1}E ⟶ E` invertible, by Mathlib's
`CategoryTheory.Triangulated.TStructure.isLE_iff_isIso_truncLTι_app`, and so removes the inner
truncation.

The shift form is obtained by applying the unshifted one to `E⟦n⟧`, which is in `D^{≤0}` by
`CategoryTheory.Triangulated.TStructure.isLE_shift`, and then moving the degree with the shift
sequence of the homology functor: `(homologyFunctor C 0).shiftIso n 0 n` is the identification
`H⁰(E⟦n⟧) ≅ Hⁿ(E)`.

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **The top truncation of a bounded above object is its top cohomology placed in that degree**:
for `E` in `D^{≤n}` there is an isomorphism `τ^{≥n}E ≅ Hⁿ(E)[-n]`.

Since `E` is `≤ n`, the map `τ^{<n+1}E ⟶ E` is an isomorphism, so `τ^{≥n}E` is the one-step
truncation `τ^{≥n}τ^{<n+1}E`, which is
`DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`. -/
@[sga "4 XVIII 2.14.2" "more general"]
public def truncGEIsoSingleHomologyOfIsLE (E : DerivedCategory C) (n : ℤ)
    [TStructure.t.IsLE E n] :
    (TStructure.t.truncGE n).obj E ≅
      (singleFunctor C n).obj ((homologyFunctor C n).obj E) :=
  haveI : IsIso ((TStructure.t.truncLTι (n + 1)).app E) :=
    (TStructure.t.isLE_iff_isIso_truncLTι_app n (n + 1) rfl E).1 inferInstance
  ((TStructure.t.truncGE n).mapIso (asIso ((TStructure.t.truncLTι (n + 1)).app E))).symm ≪≫
    (truncGELTIsoHomologyFunctorCompSingleFunctor n).app E

/-- **The identification `τ^{≥0}(E⟦n⟧) ≅ Hⁿ(E)[0]`**, for `E` in `D^{≤n}`.

This is the form in which the induction of Stacks 08HE (2) ⇒ (1) uses the previous isomorphism: a
surjection `𝒪^{⊕t} ⟶ Hⁿ(E)` of modules becomes, through the full faithfulness of the single
functor in degree zero, a morphism `𝒪^{⊕t} ⟶ τ^{≥0}(E⟦n⟧)` of the derived category, which is what
the affine-chart lifting step lifts to a morphism `𝒪^{⊕t} ⟶ E⟦n⟧`. -/
public def truncGEZeroShiftIsoSingleHomology (E : DerivedCategory C) (n : ℤ)
    [TStructure.t.IsLE E n] :
    (TStructure.t.truncGE 0).obj (E⟦n⟧) ≅
      (singleFunctor C 0).obj ((homologyFunctor C n).obj E) :=
  haveI : TStructure.t.IsLE (E⟦n⟧) 0 := TStructure.t.isLE_shift E n n 0 (by omega)
  truncGEIsoSingleHomologyOfIsLE (E⟦n⟧) 0 ≪≫
    (singleFunctor C 0).mapIso
      (((homologyFunctor C 0).shiftIso n 0 n (by omega)).app E :
        (homologyFunctor C 0).obj (E⟦n⟧) ≅ (homologyFunctor C n).obj E)

/-- **A morphism that is epic on `Hⁿ` after composing with `E ⟶ τ^{≥n}E` is epic on `Hⁿ`.**
The canonical map `E ⟶ τ^{≥n}E` is invertible on cohomology in degree `n`
(`DerivedCategory.isIso_homologyMap_truncGEπ_app`), so the factorisation can be inverted there.

In the induction of Stacks 08HE (2) ⇒ (1) this converts the lift of a surjection
`𝒪^{⊕t} ⟶ τ^{≥n}E` into the statement that the lifted morphism `𝒪^{⊕t} ⟶ E` is surjective on
`Hⁿ`, which is what makes the cone of that morphism vanish in degrees `≥ n`. -/
public theorem epi_homologyMap_of_comp_truncGEπ (n : ℤ) {K E : DerivedCategory C}
    (f : K ⟶ E) (g : K ⟶ (TStructure.t.truncGE n).obj E)
    (hfg : f ≫ (TStructure.t.truncGEπ n).app E = g)
    (hg : Epi ((homologyFunctor C n).map g)) :
    Epi ((homologyFunctor C n).map f) := by
  have := isIso_homologyMap_truncGEπ_app (C := C) n n le_rfl E
  have : Epi ((homologyFunctor C n).map f ≫
      (homologyFunctor C n).map ((TStructure.t.truncGEπ n).app E)) := by
    rw [← Functor.map_comp, hfg]
    exact hg
  exact (epi_comp_iff_of_isIso _ _).1 this

/-- If `α ≫ i.hom = j.hom ≫ β` with `i`, `j` isomorphisms and `β` epic, then `α` is epic. -/
private theorem epi_of_comp_iso_eq_iso_comp {D : Type*} [Category D] {X Y Z W : D} {α : X ⟶ Y}
    (i : Y ≅ W) (j : X ≅ Z) {β : Z ⟶ W} [Epi β] (h : α ≫ i.hom = j.hom ≫ β) : Epi α := by
  have : Epi (α ≫ i.hom) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso α i.hom).1 this

/-- **Shifting an object moves the degree in which a morphism is surjective on cohomology.**  If
`Hᵇ'(f)` is an epimorphism and `a + b = b'`, then `Hᵇ(f⟦a⟧)` is one. -/
public theorem epi_homologyMap_shift (a b b' : ℤ) (hb : a + b = b')
    {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : Epi ((homologyFunctor C b').map f)) :
    Epi ((homologyFunctor C b).map (f⟦a⟧')) := by
  have : Epi (((homologyFunctor C 0).shift b').map f) := hf
  exact epi_of_comp_iso_eq_iso_comp (((homologyFunctor C 0).shiftIso a b b' hb).app Y)
    (((homologyFunctor C 0).shiftIso a b b' hb).app X)
    ((homologyFunctor C 0).shiftIso_hom_naturality a b b' hb f)

/-- **A morphism onto `Hⁿ(E)` read as a morphism into `τ^{≥0}(E⟦n⟧)`.**  For `E` in `D^{≤n}` and a
morphism `φ : P ⟶ Hⁿ(E)` of the abelian category, this is `φ` placed in degree zero and composed
with the inverse of `DerivedCategory.truncGEZeroShiftIsoSingleHomology`.

This is the shape in which the local surjection `𝒪^{⊕t} ⟶ Hⁿ(E)` of Stacks 08HE (2) ⇒ (1) is
handed to the affine-chart lifting step. -/
public def singleMapTruncGEZeroShift (E : DerivedCategory C) (n : ℤ) [TStructure.t.IsLE E n]
    {P : C} (φ : P ⟶ (homologyFunctor C n).obj E) :
    (singleFunctor C 0).obj P ⟶ (TStructure.t.truncGE 0).obj (E⟦n⟧) :=
  (singleFunctor C 0).map φ ≫ (truncGEZeroShiftIsoSingleHomology E n).inv

/-- **The morphism into `τ^{≥0}(E⟦n⟧)` built from an epimorphism onto `Hⁿ(E)` is epic on `H⁰`.**
The single functor in degree zero has `H⁰ ∘ single 0 ≅ 𝟭`
(`DerivedCategory.singleFunctorCompHomologyFunctorIso`), so `H⁰` of `(single 0).map φ` is `φ` up
to isomorphism, and the remaining factor is invertible. -/
public theorem epi_homologyMap_singleMapTruncGEZeroShift (E : DerivedCategory C) (n : ℤ)
    [TStructure.t.IsLE E n] {P : C} (φ : P ⟶ (homologyFunctor C n).obj E) [Epi φ] :
    Epi ((homologyFunctor C 0).map (singleMapTruncGEZeroShift E n φ)) := by
  have : Epi ((homologyFunctor C 0).map ((singleFunctor C 0).map φ)) :=
    epi_of_comp_iso_eq_iso_comp ((singleFunctorCompHomologyFunctorIso C 0).app _)
      ((singleFunctorCompHomologyFunctorIso C 0).app _)
      ((singleFunctorCompHomologyFunctorIso C 0).hom.naturality φ)
  rw [singleMapTruncGEZeroShift, Functor.map_comp]
  exact epi_comp _ _

/-- **The induction step's top-degree morphism.**  Let `f : K ⟶ E⟦n⟧` lift a morphism
`g : K ⟶ τ^{≥0}(E⟦n⟧)` which is epic on `H⁰` along the canonical `E⟦n⟧ ⟶ τ^{≥0}(E⟦n⟧)` — which is
what the affine-chart lifting step of Stacks 08HE provides.  Then the morphism `K⟦-n⟧ ⟶ E`
obtained by shifting `f` back is an epimorphism on `Hⁿ`.

For `g` one takes `DerivedCategory.singleMapTruncGEZeroShift E n φ` at the local surjection
`φ : 𝒪^{⊕t} ⟶ Hⁿ(E)`, whose `H⁰` is epic by
`DerivedCategory.epi_homologyMap_singleMapTruncGEZeroShift`; `K` is then the coproduct of copies
of the unit, which is why it is left arbitrary here.

This is the hypothesis the cone computation
`DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top` consumes, and with it the
triangle the recursion
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` consumes. -/
public theorem epi_homologyMap_shiftBack_of_lift (E : DerivedCategory C) (n : ℤ)
    {K : DerivedCategory C} (f : K ⟶ E⟦n⟧)
    (g : K ⟶ (TStructure.t.truncGE 0).obj (E⟦n⟧))
    (hf : f ≫ (TStructure.t.truncGEπ 0).app (E⟦n⟧) = g)
    (hg : Epi ((homologyFunctor C 0).map g)) :
    Epi ((homologyFunctor C n).map (f⟦(-n : ℤ)⟧' ≫ (shiftShiftNeg E n).hom)) := by
  have : Epi ((homologyFunctor C n).map (f⟦(-n : ℤ)⟧')) :=
    epi_homologyMap_shift (-n) n 0 (by omega) f
      (epi_homologyMap_of_comp_truncGEπ 0 f g hf hg)
  rw [Functor.map_comp]
  exact epi_comp _ _

end DerivedCategory

end
