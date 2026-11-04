module

public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Separable
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions

/-!
# Separability of the field factors of the global functions of a geometrically reduced space

Let `k` be a field and let `X` be an algebraic space over `k`.  Part (3) of Tag 0DMY splits the
ring `A = H⁰(X, 𝒪_X)` of global regular functions of a reduced proper `X` as a finite product
of finite field extensions of `k`, one for each connected component of `|X|`;  this file
supplies the content of part (4) of that tag: when `X` is *geometrically* reduced each of those
fields is separable over `k`.  The registered statement, which discharges finiteness from
properness, is in `StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsGeometric`.

## Main results

* `AlgebraicGeometry.Space.isGeometricallyReduced_componentFunctions`: each factor of a
  componentwise factorization of the global functions of a geometrically reduced algebraic
  space is geometrically reduced over the base field.
* `AlgebraicGeometry.Space.finite_componentFunctions_of_finite`: each factor is finite over `k`
  when the global functions are.
* `AlgebraicGeometry.Space.isSeparable_componentFunctions_of_finite`: for a geometrically
  reduced `X` with finite dimensional global functions, each factor is a field, finite and
  separable over `k`.

## Implementation notes

**The route taken.**  Tag 0DMY proves part (4) from Tag 073K, the comparison
`H⁰(X, 𝒪_X) ⊗_k K = H⁰(X_K, 𝒪_{X_K})`.  The proof here does not need it, by the argument the
scheme case uses in
`Stacks.AlgebraicGeometry.ProperSectionsGeom.GlobalSectionsFieldDecomposition.factor_isSeparable`
(Tag 0BUG): a factor `k_i` is the image of the global functions under the `k`-algebra map
`y ↦ germ (e_i · y)` into the local ring of an étale chart at a point where the idempotent
`e_i` cutting out that factor is invertible.  Such a point exists because `e_i ≠ 0` and
restriction of global functions to a surjective étale chart is injective (Tag 0BGS).  The
local ring of a chart of a geometrically reduced algebraic space is geometrically reduced over
`k` by Tags 0DMS and 035W, geometric reducedness passes to a subring, and a factor is a field,
so the map is injective.  A finite geometrically reduced field extension is separable, which is
Tag 030W followed by Tag 030O.

Finiteness of a factor is what makes the extension algebraic, and it is used: the separability
criterion of Tag 030W gives separability in the sense of Tag 030O, which is Mathlib's
`Algebra.IsSeparable` only for an algebraic extension.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0BGS](https://stacks.math.columbia.edu/tag/0BGS)
* [Stacks Project, Tag 0DMS](https://stacks.math.columbia.edu/tag/0DMS)
* [Stacks Project, Tag 035W](https://stacks.math.columbia.edu/tag/035W)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A nonzero idempotent global function on a reduced scheme has germ `1` at some point. -/
private theorem _root_.AlgebraicGeometry.Scheme.exists_germ_eq_one_of_isIdempotentElem
    (Y : Scheme.{u}) [_root_.AlgebraicGeometry.IsReduced Y] (r : Γ(Y, ⊤))
    (hr : IsIdempotentElem r) (h0 : r ≠ 0) :
    ∃ x, (Y.presheaf.germ ⊤ x trivial).hom r = 1 := by
  obtain ⟨x, hx⟩ : (Y.basicOpen r : Set Y).Nonempty := Set.nonempty_iff_ne_empty.mpr fun h =>
    h0 ((_root_.AlgebraicGeometry.basicOpen_eq_bot_iff r).mp (TopologicalSpace.Opens.ext h))
  exact ⟨x, (IsIdempotentElem.iff_eq_one_of_isUnit ((Scheme.mem_basicOpen_top _ r x).mp hx)).mp
    (hr.map (Y.presheaf.germ ⊤ x trivial).hom)⟩

/-- Let `ε` present `R` as a product of `k`-algebras `A j`, with `A i` a field, and let
`ρ : R → Γ(Y, ⊤)` be compatible with the `k`-algebra structures, for `Y` geometrically reduced
over `k`.  If the germ at `x` of the image of the idempotent cutting out `A i` is `1`, then `A i`
is geometrically reduced over `k`. -/
private theorem _root_.AlgebraicGeometry.Scheme.isGeometricallyReduced_of_germ_eq_one {k : Type u}
    [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (hg : _root_.AlgebraicGeometry.GeometricallyReduced g) {ι : Type*} [DecidableEq ι]
    {A : ι → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra k (A j)] {R : Type*} [CommRing R]
    [Algebra k R] (ε : R ≃ₐ[k] ∀ j, A j) (i : ι) (hi : IsField (A i)) (ρ : R →+* Γ(Y, ⊤))
    (hρ : ∀ a, ρ (algebraMap k R a) = ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom a)
    (x : Y) (hx : (Y.presheaf.germ ⊤ x trivial).hom (ρ (ε.symm (Pi.single i 1))) = 1) :
    Algebra.IsGeometricallyReduced k (A i) := by
  let := hi.toField
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base x)) :=
    StructureSheaf.stalkAlgebra k (g.base x)
  let : Algebra k (Y.presheaf.stalk x) :=
    ((g.stalkMap x).hom.comp (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base x)))).toAlgebra
  have : Algebra.IsGeometricallyReduced k (Y.presheaf.stalk x) :=
    (_root_.AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk g x).mp
      ((_root_.AlgebraicGeometry.geometricallyReduced_iff_forall_isGeometricallyReducedAt g).mp
        hg x)
  let germ : Γ(Y, ⊤) →ₐ[k] Y.presheaf.stalk x :=
    { (Y.presheaf.germ ⊤ x trivial).hom with
      commutes' := fun b =>
        (Stacks.AlgebraicGeometry.ProperSectionsGeom.algebraMap_stalk_apply k g x b).symm }
  let ψ := Stacks.AlgebraicGeometry.ProperSectionsGeom.piSingleAlgHom ε
    (germ.comp { ρ with commutes' := hρ }) i hx
  exact Algebra.IsGeometricallyReduced.of_injective ψ ψ.toRingHom.injective

section Field

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- **Each factor of a componentwise factorization of the global functions of a geometrically
reduced algebraic space is geometrically reduced over the base field.**

Let `e` be the idempotent global function cutting out the factor indexed by `c`.  It is nonzero,
and restriction of global functions to a surjective étale chart `Y` is injective by Tag 0BGS, so
`e` restricts to a nonzero function on `Y`;  the chart being reduced, that function is invertible
at some point `x` of `Y`.  Multiplication by `e` followed by the germ at `x` is then a
`k`-algebra map from the factor to the local ring `𝒪_{Y, x}`, which is geometrically reduced
over `k` by Tags 0DMS and 035W.  The factor is a field by part (3) of Tag 0DMY, so the map is
injective, and geometric reducedness passes to a subring. -/
theorem isGeometricallyReduced_componentFunctions
    (hgr : IsGeometricallyReduced k B hS X hX)
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    @Algebra.IsGeometricallyReduced k (componentFunctions B (Spec (.of k)) hS X c) _ _
      (fac.factorAlgebra c) := by
  classical
  let (d : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X d) := fac.factorAlgebra d
  obtain ⟨U, a, hsurj, ha, hU⟩ :=
    (isGeometricallyReduced_iff_exists_surjective_etaleChart k B hS X hX).mp hgr
  let V : SmallEtale B (Spec (.of k)) hS X :=
    ⟨CostructuredArrow.mk a, (isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hS a).mp ha⟩
  let g : (BigFppfOver.toScheme B (Spec (.of k)) hS).obj U ⟶ Spec (CommRingCat.of k) :=
    B.inclusion.map U.hom
  have hU' : _root_.AlgebraicGeometry.GeometricallyReduced g := hU
  have hYred : _root_.AlgebraicGeometry.IsReduced
      ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj U) :=
    _root_.AlgebraicGeometry.self_of_isIntegral_of_geometrically
      (P := fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)
      hU'.geometrically_isReduced
  have hfield := isField_componentFunctions k B hS X hX
    (hasEtaleLocalProperty_isReduced_of_isGeometricallyReduced k B hS X hX hgr) fac c
  let := hfield.toField
  set e : globalFunctions B (Spec (.of k)) hS X := fac.equivalence.symm (Pi.single c 1) with he
  have hidem : IsIdempotentElem e := by
    rw [he, IsIdempotentElem, ← map_mul, ← Pi.single_mul, one_mul]
  have hne : e ≠ 0 := by
    rw [he, Ne, map_eq_zero_iff _ fac.equivalence.symm.injective]
    exact fun h => one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using congrFun h c)
  have hrne : globalFunctionsChartRestriction B (Spec (.of k)) hS ⟨X, hX⟩ V e ≠ 0 := fun h =>
    hne (injective_globalFunctionsChartRestriction_of_isSurjective B (Spec (.of k)) hS ⟨X, hX⟩ V
      hsurj (h.trans (map_zero _).symm))
  obtain ⟨x, hx⟩ := Scheme.exists_germ_eq_one_of_isIdempotentElem
    ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj U) _
    (hidem.map (globalFunctionsChartRestriction B (Spec (.of k)) hS ⟨X, hX⟩ V)) hrne
  exact Scheme.isGeometricallyReduced_of_germ_eq_one g hU' fac.equivalence c hfield
    (globalFunctionsChartRestriction B (Spec (.of k)) hS ⟨X, hX⟩ V) (fun _ => rfl) x hx

omit hX in
/-- Each factor of a componentwise factorization of the global functions is finite over the base
field as soon as the global functions are:  the factorization makes the product of the factors
`k`-linearly isomorphic to the global functions, and projection onto a factor is a surjective
`k`-linear map. -/
theorem finite_componentFunctions_of_finite
    (hfin : Module.Finite k (globalFunctions B (Spec (.of k)) hS X))
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    @Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) _ _
      (@Algebra.toModule k (componentFunctions B (Spec (.of k)) hS X c) _ _
        (fac.factorAlgebra c)) := by
  let (d : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X d) := fac.factorAlgebra d
  have : Module.Finite k
      (∀ d : ConnectedComponents (points B (Spec (.of k)) hS X),
        componentFunctions B (Spec (.of k)) hS X d) :=
    Module.Finite.equiv fac.equivalence.toLinearEquiv
  exact Module.Finite.of_surjective (LinearMap.proj c) (LinearMap.proj_surjective c)

/-- **The factors of the global functions of a geometrically reduced algebraic space with finite
dimensional global functions are finite separable field extensions of the base field.**

The factor is a field by part (3) of Tag 0DMY, geometric reducedness making `X` reduced;  it is
finite over `k` by `AlgebraicGeometry.Space.finite_componentFunctions_of_finite`, and
geometrically reduced over `k` by
`AlgebraicGeometry.Space.isGeometricallyReduced_componentFunctions`.  A finite geometrically
reduced field extension is separable in the sense of Tag 030O by Tag 030W, and separability in
that sense is Mathlib's `Algebra.IsSeparable` for an algebraic extension. -/
theorem isSeparable_componentFunctions_of_finite
    (hfin : Module.Finite k (globalFunctions B (Spec (.of k)) hS X))
    (hgr : IsGeometricallyReduced k B hS X hX)
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    IsField (componentFunctions B (Spec (.of k)) hS X c) ∧
      @Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) _ _
        (@Algebra.toModule k (componentFunctions B (Spec (.of k)) hS X c) _ _
          (fac.factorAlgebra c)) ∧
      @Algebra.IsSeparable k (componentFunctions B (Spec (.of k)) hS X c) _ _
        (fac.factorAlgebra c) := by
  let (d : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X d) := fac.factorAlgebra d
  have hfield : IsField (componentFunctions B (Spec (.of k)) hS X c) :=
    isField_componentFunctions k B hS X hX
      (hasEtaleLocalProperty_isReduced_of_isGeometricallyReduced k B hS X hX hgr) fac c
  let fieldFactor : _root_.Field (componentFunctions B (Spec (.of k)) hS X c) := hfield.toField
  have hfinite : Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) :=
    finite_componentFunctions_of_finite k B hS X hfin fac c
  have hsepExt :
      Algebra.IsSeparableExtension k (componentFunctions B (Spec (.of k)) hS X c) :=
    ((Algebra.isSeparableExtension_tfae k (componentFunctions B (Spec (.of k)) hS X c)
      (ringExpChar k)).out 4 1).mp (isGeometricallyReduced_componentFunctions k B hS X hX hgr fac c)
  exact ⟨hfield, hfinite,
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension k
      (componentFunctions B (Spec (.of k)) hS X c)⟩

end Field

end AlgebraicGeometry.Space

end
