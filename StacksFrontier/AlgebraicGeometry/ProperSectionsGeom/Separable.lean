module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.Separable
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.FieldTheory.Separable.TFAE

/-!
# Separable factors of global sections

Let `X` be a geometrically reduced proper scheme over a field `k`. Every field occurring in a
finite product decomposition of the ring of global sections of `X` is a finite separable extension
of `k`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProperSectionsGeom.GlobalSectionsFieldDecomposition` packages a finite
  family of field extensions and an algebra equivalence from the global sections to their product.

## Main results

All of these live in the namespace `Stacks.AlgebraicGeometry.ProperSectionsGeom`.

* `GlobalSectionsFieldDecomposition.factor_isSeparable`: every field factor in such a
  decomposition is separable over the base field.
* `isSeparable_of_isSeparableExtension`: a finite extension separable in the sense of
  `Algebra.IsSeparableExtension` is separable in Mathlib's sense `Algebra.IsSeparable`.
* `piSingleAlgHom`: the algebra homomorphism from one factor of a finite product into a ring,
  obtained from a homomorphism out of the product that sends the complementary idempotent to `1`.
* `algebraMap_stalk_apply`: the `k`-algebra structure of a stalk of `X`, as used by
  `AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk`, is the germ of the
  `k`-algebra structure of the global sections.

## Implementation notes

Finiteness of each factor is already part of `GlobalSectionsFieldDecomposition`; the result here
supplies its separability. The decomposition is an argument, so the result applies to any
presentation of the global sections of the form provided by the reduced-sections part of Tag
0BUG, rather than only to the chosen presentation.

The proof does **not** use degree-zero flat base change for cohomology (Stacks Tag 02KH), which
the Stacks proof uses in order to see `Γ(X, ⊤) ⊗[k] k'` inside `Γ(X_{k'}, ⊤)`.  That input is
Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, instantiated
at the top open by `Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.isPushout_appTop`, and it is
not needed here.  Instead the geometric reducedness of a factor is read off a *stalk* of `X`:

* the idempotent `e` cutting out the `i`-th factor is nonzero, and `X` is reduced (a geometrically
  reduced scheme over a field is reduced), so `X.basicOpen e` is nonempty;  pick `x` in it;
* the germ at `x` of a global section is a `k`-algebra map `Γ(X, ⊤) ⟶ 𝒪_{X,x}`
  (`algebraMap_stalk_apply`) sending `e` to a unit, hence — `e` being idempotent — to `1`, so by
  `piSingleAlgHom` it induces a `k`-algebra map from the `i`-th factor to `𝒪_{X,x}`;
* that map is injective, the factor being a field and the stalk being nonzero, and `𝒪_{X,x}` is
  geometrically reduced over `k` by Tag 035W
  (`AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk`), so the factor is
  geometrically reduced over `k` by `Algebra.IsGeometricallyReduced.of_injective`.

Separability then comes from Tag 030W (`Algebra.isSeparableExtension_tfae`), whose fourth
condition is geometric reducedness and whose first is `Algebra.IsSeparableExtension`;  for a
*finite* extension the latter is Mathlib's `Algebra.IsSeparable`, which is
`isSeparable_of_isSeparableExtension`:  a transcendence basis of an algebraic extension is empty,
so the separably-generated condition at `⊤` degenerates to separability over `k` itself.

`GlobalSectionsFieldDecomposition` is only the shape in which the decomposition is handed to us;
nothing about it is proved here.  `globalSectionsFieldDecomposition_of_isReduced` in
`StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections`, which carries clause (3) of
the tag, builds one for every reduced proper `X`.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* [Stacks Project, Tag 035W](https://stacks.math.columbia.edu/tag/035W)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProperSectionsGeom

/-- A presentation of the global sections of `X` as a finite product of finite field
extensions of `k`. -/
structure GlobalSectionsFieldDecomposition (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) where
  /-- The number of field factors. -/
  numFactors : ℕ
  /-- The finite field extensions occurring as factors. -/
  factor : Fin numFactors → CommAlgCat.{u} k
  /-- Each factor is a field. -/
  factorIsField : ∀ i, IsField (factor i)
  /-- Each factor is finite-dimensional over the base field. -/
  factorModuleFinite : ∀ i, Module.Finite k (factor i)
  /-- The product decomposition, compatible with the canonical `k`-algebra structure on
  global sections. -/
  algEquiv :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Γ(X, ⊤) ≃ₐ[k] (∀ i, factor i)

/-- An algebraic, separably generated field extension is separable in Mathlib's sense:  a
transcendence basis of an algebraic extension is empty, so the separable subextension it generates
is the base field itself. -/
theorem isSeparable_of_isSeparablyGenerated (k F : Type*) [Field k] [Field F] [Algebra k F]
    [Algebra.IsAlgebraic k F] [Algebra.IsSeparablyGenerated k F] : Algebra.IsSeparable k F := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := F)
  have hempty : IsEmpty s := hs.1.isEmpty_of_isAlgebraic
  have hs0 : s = ∅ := Set.isEmpty_coe_sort.mp hempty
  subst hs0
  rw [IntermediateField.adjoin_empty] at hsep
  have := hsep
  refine Algebra.IsSeparable.of_equiv_equiv
    (IntermediateField.botEquiv k F).toRingEquiv (RingEquiv.refl F) ?_
  ext y
  change algebraMap k F ((IntermediateField.botEquiv k F) y) = y.1
  exact congrArg Subtype.val ((IntermediateField.botEquiv k F).symm_apply_apply y)

/-- For a finite field extension, separability in the sense of `Algebra.IsSeparableExtension`
(Stacks Tag 030O (2)) is Mathlib's `Algebra.IsSeparable`. -/
theorem isSeparable_of_isSeparableExtension (k F : Type*) [Field k] [Field F] [Algebra k F]
    [Module.Finite k F] [Algebra.IsSeparableExtension k F] : Algebra.IsSeparable k F := by
  have : Algebra.IsSeparable k (⊤ : IntermediateField k F) :=
    isSeparable_of_isSeparablyGenerated k (⊤ : IntermediateField k F)
  exact Algebra.IsSeparable.of_algHom k (⊤ : IntermediateField k F)
    IntermediateField.topEquiv.symm.toAlgHom

/-- Let `ε` present `R` as a finite product of `k`-algebras `A j` and let `g : R →ₐ[k] S` send the
idempotent cutting out the `i`-th factor to `1`.  Then `y ↦ g (ε.symm (Pi.single i y))` is a
`k`-algebra homomorphism from the `i`-th factor to `S`;  it is the map induced by `g` on the
quotient of `R` by the complementary idempotent. -/
def piSingleAlgHom {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι]
    {A : ι → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra k (A j)]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (ε : R ≃ₐ[k] (∀ j, A j)) (g : R →ₐ[k] S) (i : ι)
    (hg : g (ε.symm (Pi.single i 1)) = 1) : A i →ₐ[k] S where
  toFun y := g (ε.symm (Pi.single i y))
  map_one' := hg
  map_mul' y z := by
    simp only [Pi.single_mul, map_mul]
  map_zero' := by simp
  map_add' y z := by simp [Pi.single_add]
  commutes' c := by
    have h1 : Pi.single i (algebraMap k (A i) c)
        = Pi.single i (1 : A i) * algebraMap k (∀ j, A j) c := by
      rw [← Pi.single_mul_left]
      simp [Pi.algebraMap_apply]
    simp only [h1, map_mul, AlgEquiv.commutes, AlgHom.commutes, hg, one_mul]

/-- The `k`-algebra structure that a scheme over `k` induces on its stalk at a point — the one
`AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk` is stated for — is
the germ at that point of the `k`-algebra structure on the global sections.  In other words, taking
germs at `x` is a homomorphism of `k`-algebras. -/
theorem algebraMap_stalk_apply (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (x : X) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    ∀ c : k, algebraMap k (X.presheaf.stalk x) c
      = X.presheaf.germ ⊤ x trivial (algebraMap k Γ(X, ⊤) c) := by
  intro c
  change (f.stalkMap x) (StructureSheaf.toStalk k (f.base x) c) = _
  exact ConcreteCategory.congr_hom
    (Scheme.Hom.germ_stalkMap f (⊤ : (Spec (.of k)).Opens) x trivial)
    ((Scheme.ΓSpecIso (.of k)).inv c)

/-- Every field factor in a finite product decomposition of the global sections of a
geometrically reduced proper scheme is separable over the base field.
Together with `GlobalSectionsFieldDecomposition.factorModuleFinite`, this says that every factor
is a finite separable extension. -/
@[stacks 0BUG "clause (4): for a GEOMETRICALLY REDUCED proper scheme over a field k, every field \
factor of a presentation of the global sections as a finite product of finite field extensions \
of k (clause (3)) is separable over k. The decomposition is an argument, so the conclusion holds \
for every such presentation, in particular the one clause (3) constructs."]
theorem GlobalSectionsFieldDecomposition.factor_isSeparable
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyReduced f] (D : GlobalSectionsFieldDecomposition k X f)
    (i : Fin D.numFactors) : Algebra.IsSeparable k (D.factor i) := by
  classical
  let algA : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hXred : IsReduced X := self_of_isIntegral_of_geometrically (P := IsReduced)
    (inferInstance : GeometricallyReduced f).geometrically_isReduced
  let factorField : Field (D.factor i) := (D.factorIsField i).toField
  have hfinite : Module.Finite k (D.factor i) := D.factorModuleFinite i
  set e : Γ(X, ⊤) := D.algEquiv.symm (Pi.single i 1) with hedef
  have hidem : IsIdempotentElem e := by
    change e * e = e
    rw [hedef, ← map_mul, ← Pi.single_mul, one_mul]
  have hne : e ≠ 0 := by
    rw [hedef, Ne, map_eq_zero_iff _ D.algEquiv.symm.injective]
    intro h
    have h1 := congrFun h i
    simp only [Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  obtain ⟨x, hx⟩ : (X.basicOpen e : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hne ((AlgebraicGeometry.basicOpen_eq_bot_iff e).mp (TopologicalSpace.Opens.ext h))
  let algS : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
    StructureSheaf.stalkAlgebra k (f.base x)
  let algSt : Algebra k (X.presheaf.stalk x) :=
    ((f.stalkMap x).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
  have hgeomStalk : Algebra.IsGeometricallyReduced k (X.presheaf.stalk x) :=
    (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk f x).mp
      ((geometricallyReduced_iff_forall_isGeometricallyReducedAt f).mp inferInstance x)
  let germAlgHom : Γ(X, ⊤) →ₐ[k] X.presheaf.stalk x :=
    { (X.presheaf.germ ⊤ x trivial).hom with
      commutes' := fun c => (algebraMap_stalk_apply k f x c).symm }
  have hgerm1 : germAlgHom e = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit
      ((Scheme.mem_basicOpen_top X e x).mp hx)).mp (hidem.map germAlgHom)
  let φ : D.factor i →ₐ[k] X.presheaf.stalk x := piSingleAlgHom D.algEquiv germAlgHom i hgerm1
  have hfactorGeomRed : Algebra.IsGeometricallyReduced k (D.factor i) :=
    Algebra.IsGeometricallyReduced.of_injective φ φ.toRingHom.injective
  have hsepExt : Algebra.IsSeparableExtension k (D.factor i) :=
    ((Algebra.isSeparableExtension_tfae k (D.factor i) (ringExpChar k)).out 4 1).mp
      hfactorGeomRed
  exact isSeparable_of_isSeparableExtension k (D.factor i)

end Stacks.AlgebraicGeometry.ProperSectionsGeom

end
