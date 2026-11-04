module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.FieldTheory.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.ConnectedReducedBaseChange
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedGenericPoints

/-!
# Invertible functions on a variety: the four field-theoretic conditions

Stacks Tag 04L8: for `k` a field and `X` a variety over `k`, the group `𝒪^*(X)/k^*` is finitely
generated as soon as one of four conditions holds — (1) `k` is integrally closed in
`Γ(X, 𝒪_X)`, (2) `k` is algebraically closed in the function field `k(X)`, (3) `X` is
geometrically integral over `k`, or (4) `k` is the "intersection" of the residue field extensions
`κ(x)/k` over the closed points `x` of `X`.

The source deduces this from Proposition 04L7, which is the same finite-generation conclusion for
a connected reduced scheme locally of finite type over `k` with finitely many irreducible
components under condition (1), the existence of a `k`-rational point, or condition (3).  That
proposition is formalized in
`StacksFrontier/AlgebraicGeometry/InvertibleFunctions/ConnectedReducedBaseChange.lean` under its
condition (1), as `AlgebraicGeometry.fg_units_quotient_of_integrallyClosed`, and that is what the
tag is deduced from here: a variety is integral, hence connected, reduced and with a single
irreducible component, and its structure morphism is locally of finite type, so all the standing
hypotheses of 04L7 hold.

The source omits the verifications that each of its conditions (2), (3), (4) implies (1).  All
three are proved here, so the tag is unconditional.

Condition (2) gives condition (1) by the pure field theory of
`integralClosure_eq_bot_of_isAlgClosedIn_of_injective` applied to the restriction map to the
function field, which is injective on an integral scheme.  Condition (4) gives it because the
integral closure of `k` in the global sections of a connected reduced scheme is a field (Tag
04MI), so it is itself one of the extensions that condition quantifies over.

Condition (3) is routed through condition (2), which is the classical argument.  Geometric
reducedness of an integral scheme says exactly that its function field is a separable extension of
`k` (Tag 04KS), and geometric irreducibility says exactly that `k` is separably closed in the
residue field at the generic point (Tag 054Q); that residue field is the function field, because
the stalk there is already a field, so the two statements are about one extension.  A separable
extension in which every separably algebraic element is a constant has no algebraic elements
beyond the constants either — `isAlgClosedIn_of_separableClosure_eq_bot` — and that is
condition (2).

## Main results

* `integralClosure_eq_bot_of_isAlgClosedIn_of_injective`: if `k` is algebraically closed in a
  field `K` and a `k`-algebra `A` embeds in `K`, then the integral closure of `k` in `A` is `k`.
* `isAlgClosedIn_of_separableClosure_eq_bot`: a separable extension in which `k` is separably
  closed is one in which `k` is algebraically closed.
* `AlgebraicGeometry.integralClosure_globalSections_eq_bot_of_isAlgClosedIn_functionField`:
  condition (2) implies condition (1).
* `AlgebraicGeometry.integralClosure_globalSections_eq_bot_of_geometricallyIntegral`:
  condition (3) implies condition (1).
* `AlgebraicGeometry.integralClosure_globalSections_eq_bot_of_closedPoints`: condition (4)
  implies condition (1).
* `AlgebraicGeometry.fg_units_quotient_of_isVariety_of_field_conditions`: Tag 04L8.

## Implementation notes

The ground field inside the global sections is the image of the ring map induced by the structure
morphism, so condition (1) reads `integralClosure k Γ(X, ⊤) = ⊥` for the induced algebra
structure, and the constant units are the range of that map on units.  The function field is
Mathlib's stalk at the generic point and its `k`-algebra structure is the composite of the
structure map with the germ map from the global sections.

Condition (4) is expressed as: every field extension `L/k` which admits, at every closed point
`x`, a ring map `L → κ(x)` compatible with the two maps out of `k`, already equals `k`.  The
`k`-algebra structure on `κ(x)` used for the compatibility is the composite
`k → Γ(X, ⊤) → κ(x)` of the structure map with evaluation at `x`, which is the structure induced
by the structure morphism.  Quantifying `L` over `Type u` loses nothing, since an extension of `k`
embedding into some `κ(x)` is isomorphic to a subfield of it.

## References

* [Stacks Project, Tag 04L8](https://stacks.math.columbia.edu/tag/04L8)
* [Stacks Project, Tag 04L7](https://stacks.math.columbia.edu/tag/04L7)
* [Stacks Project, Tag 04MI](https://stacks.math.columbia.edu/tag/04MI)
* [Stacks Project, Tag 04KS](https://stacks.math.columbia.edu/tag/04KS)
* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
-/

@[expose] public section

open CategoryTheory IntermediateField TopologicalSpace

universe u

/-- If `k` is algebraically closed in a field `K` and the `k`-algebra `A` admits an injective
`k`-algebra map to `K`, then the integral closure of `k` in `A` is `k`.

An element of `A` integral over `k` has algebraic image in `K`, hence image in `k`; injectivity
turns this into membership in the bottom subalgebra. -/
theorem integralClosure_eq_bot_of_isAlgClosedIn_of_injective {k A K : Type*} [Field k]
    [CommRing A] [Field K] [Algebra k A] [Algebra k K] (h : IsAlgClosedIn k K)
    (γ : A →ₐ[k] K) (hγ : Function.Injective γ) : integralClosure k A = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hxmem : γ x ∈ algebraicClosure k K := mem_algebraicClosure_iff.mpr
    (IsIntegral.map γ ((mem_integralClosure_iff k A).mp hx)).isAlgebraic
  rw [show algebraicClosure k K = ⊥ from h] at hxmem
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hxmem
  exact Algebra.mem_bot.mpr ⟨a, hγ ((γ.commutes a).trans ha)⟩

/-- If `K/k` is a separable field extension and every element of `K` separably algebraic over `k`
is a constant, then every element of `K` algebraic over `k` is a constant.

The relative algebraic closure of `k` in `K` inherits separability of the extension, which by
Tag 030W is geometric reducedness and so passes to subextensions; being algebraic, it is then
separable in Mathlib's sense, hence contained in the separable closure, which is `k`. -/
theorem isAlgClosedIn_of_separableClosure_eq_bot (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparableExtension k K] (h : separableClosure k K = ⊥) : IsAlgClosedIn k K := by
  have hgr : Algebra.IsGeometricallyReduced k K :=
    ((Algebra.isSeparableExtension_tfae k K (ringExpChar k)).out 1 4).mp
      (show Algebra.IsSeparableExtension k K from inferInstance)
  have hgrA : Algebra.IsGeometricallyReduced k (algebraicClosure k K) :=
    Algebra.IsGeometricallyReduced.of_injective (algebraicClosure k K).val
      (algebraicClosure k K).val.injective
  have hseA : Algebra.IsSeparableExtension k (algebraicClosure k K) :=
    ((Algebra.isSeparableExtension_tfae k (algebraicClosure k K)
      (ringExpChar k)).out 4 1).mp hgrA
  have : Algebra.IsSeparable k (algebraicClosure k K) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension_of_isAlgebraic
      k (algebraicClosure k K)
  have hle : algebraicClosure k K ≤ separableClosure k K :=
    le_separableClosure (F := k) (E := K) (algebraicClosure k K)
  rw [h] at hle
  exact le_antisymm hle bot_le

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04L8, condition (2) implies condition (1).** Let `k` be a field and let
`X` be an integral scheme over `k`.  If `k` is algebraically closed in the function field of `X`,
then the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`.

The germ map from the global sections to the stalk at the generic point is injective on an
integral scheme, so this is the field-theoretic statement
`integralClosure_eq_bot_of_isAlgClosedIn_of_injective`. -/
@[stacks 04L8 "condition (2) implies condition (1); the source omits this verification"]
theorem integralClosure_globalSections_eq_bot_of_isAlgClosedIn_functionField
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsIntegral X] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra k X.functionField :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    IsAlgClosedIn k X.functionField → integralClosure k Γ(X, ⊤) = ⊥ := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra k X.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  intro h
  let γ : Γ(X, ⊤) →ₐ[k] X.functionField :=
    { toRingHom := (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      commutes' := fun a => rfl }
  exact integralClosure_eq_bot_of_isAlgClosedIn_of_injective h γ
    (germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial)

/-- **Stacks Project, Tag 04L8, condition (4) implies condition (1).** Let `k` be a field and let
`X` be a connected reduced scheme over `k`.  Suppose that every field extension `L` of `k` which
admits at each closed point `x` of `X` a ring map to the residue field `κ(x)` compatible with the
maps out of `k` is already equal to `k`.  Then the integral closure of `k` in `Γ(X, 𝒪_X)` is `k`.

The integral closure is a field by Tag 04MI, and evaluation at a point restricts to a ring map
from it to the residue field there which is compatible with the maps out of `k`.  So the
hypothesis applies to it and makes it `k`. -/
@[stacks 04L8 "condition (4) implies condition (1); the source omits this verification"]
theorem integralClosure_globalSections_eq_bot_of_closedPoints
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [ConnectedSpace X] [IsReduced X] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    (∀ (L : Type u) [Field L] [Algebra k L],
      (∀ x ∈ closedPoints X, ∃ ι : L →+* X.residueField x,
        ∀ a : k, ι (algebraMap k L a) = X.Γevaluation x (algebraMap k Γ(X, ⊤) a)) →
      Function.Surjective (algebraMap k L)) →
    integralClosure k Γ(X, ⊤) = ⊥ := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  intro hL
  let A := integralClosure k Γ(X, ⊤)
  let : Field A := (integralClosure_globalSections_isField k X f).toField
  have hsurj : Function.Surjective (algebraMap k A) :=
    hL A fun x _ => ⟨(X.Γevaluation x).hom.comp A.val.toRingHom,
      fun a => congrArg (fun y => (X.Γevaluation x).hom y) (A.val.commutes a)⟩
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  exact Algebra.mem_bot.mpr ⟨a, (A.val.commutes a).symm.trans (congrArg Subtype.val ha)⟩

/-- The residue field at the generic point of an integral scheme is its function field, so a
ground field separably closed in the one is separably closed in the other.

The stalk at the generic point is already a field, so the residue map out of it is bijective;
`AlgebraicGeometry.genericResidueEquiv` is that isomorphism, and it is a `k`-algebra map because
evaluation at a point is the germ followed by the residue. -/
private theorem separableClosure_functionField_eq_bot_of_residueField
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsIntegral X]
    (h : letI : Algebra k (X.residueField (genericPoint X)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.Γevaluation (genericPoint X)).hom.toAlgebra
      separableClosure k (X.residueField (genericPoint X)) = ⊥) :
    letI : Algebra k X.functionField :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    separableClosure k X.functionField = ⊥ := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  let : Algebra k X.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  let e : X.functionField ≃ₐ[k] X.residueField (genericPoint X) :=
    AlgEquiv.ofRingEquiv (f := genericResidueEquiv X) (fun a => rfl)
  rw [← separableClosure.map_eq_of_algEquiv e.symm, h, IntermediateField.map_bot]

/-- **Stacks Project, Tag 04L8, condition (3) implies condition (1).** Let `k` be a field and let
`X` be an integral scheme over `k` which is geometrically integral.  Then the integral closure of
`k` in `Γ(X, 𝒪_X)` is `k`.

Geometric integrality is geometric reducedness together with geometric irreducibility.  The first
says the function field is a separable extension of `k` (Tag 04KS) and the second says `k` is
separably closed in the residue field at the generic point (Tag 054Q), which is the same field;
so `k` is algebraically closed in the function field, which is condition (2). -/
@[stacks 04L8 "condition (3) implies condition (1); the source omits this verification"]
theorem integralClosure_globalSections_eq_bot_of_geometricallyIntegral
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsIntegral X]
    (hgi : GeometricallyIntegral f) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    integralClosure k Γ(X, ⊤) = ⊥ := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  let : Algebra k X.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  have hsep : Algebra.IsSeparableExtension k X.functionField :=
    (geometricallyReduced_iff_isSeparableExtension_functionField f).mp inferInstance
  have hirr : separableClosure k (X.residueField (genericPoint X)) = ⊥ :=
    ((geometricallyIrreducible_tfae_functionField k X f (genericPoint X)
      (genericPoint_spec X)).out 1 3).mp (show GeometricallyIrreducible f from inferInstance)
  exact integralClosure_globalSections_eq_bot_of_isAlgClosedIn_functionField k X f
    (isAlgClosedIn_of_separableClosure_eq_bot k X.functionField
      (separableClosure_functionField_eq_bot_of_residueField k X f hirr))

/-- Condition (1) of Stacks Tag 04L7 in the elementwise spelling that the library's proof of that
tag consumes: if the integral closure of `k` in `Γ(X, 𝒪_X)` is the bottom `k`-subalgebra, then
every global section integral over the structure map lies in its range. -/
private theorem mem_range_of_isIntegralElem_of_integralClosure_eq_bot
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (h : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
      integralClosure k Γ(X, ⊤) = ⊥) :
    ∀ a : Γ(X, ⊤), (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).IsIntegralElem a →
      a ∈ Set.range ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  intro a ha
  have hmem : a ∈ integralClosure k Γ(X, ⊤) := ha
  rw [h] at hmem
  exact Algebra.mem_bot.mp hmem

/-- **Stacks Project, Tag 04L8.** Let `k` be a field and let `X` be a variety over `k`.  Then the
group of invertible global functions on `X` modulo the constants coming from `k` is finitely
generated as soon as one of the following holds: the integral closure of `k` in `Γ(X, 𝒪_X)` is
`k`; `k` is algebraically closed in the function field of `X`; `X` is geometrically integral over
`k`; or no field extension of `k` other than `k` itself admits at every closed point a map to the
residue field there compatible with the maps out of `k`.

A variety is integral, hence connected and reduced with a single irreducible component, and its
structure morphism is locally of finite type, so Proposition 04L7 under its condition (1) —
`AlgebraicGeometry.fg_units_quotient_of_integrallyClosed` — applies.  Each of the other three
conditions is turned into condition (1) by the three lemmas above. -/
@[stacks 04L8]
theorem fg_units_quotient_of_isVariety_of_field_conditions
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    (integralClosure k Γ(X, ⊤) = ⊥ ∨
      (letI : Algebra k X.functionField :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
       IsAlgClosedIn k X.functionField) ∨
      GeometricallyIntegral f ∨
      (∀ (L : Type u) [Field L] [Algebra k L],
        (∀ x ∈ closedPoints X, ∃ ι : L →+* X.residueField x,
          ∀ a : k, ι (algebraMap k L a) = X.Γevaluation x (algebraMap k Γ(X, ⊤) a)) →
        Function.Surjective (algebraMap k L))) →
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  intro h
  have hfin : (irreducibleComponents (X : Type u)).Finite := by
    simpa only [irreducibleComponents_eq_singleton] using Set.finite_singleton _
  have hbot : integralClosure k Γ(X, ⊤) = ⊥ := by
    rcases h with hbot | halg | hgeom | hclosed
    · exact hbot
    · exact integralClosure_globalSections_eq_bot_of_isAlgClosedIn_functionField k X f halg
    · exact integralClosure_globalSections_eq_bot_of_geometricallyIntegral k X f hgeom
    · exact integralClosure_globalSections_eq_bot_of_closedPoints k X f hclosed
  exact fg_units_quotient_of_integrallyClosed k X f hfin
    (mem_range_of_isIntegralElem_of_integralClosure_eq_bot k X f hbot)

end AlgebraicGeometry

end
