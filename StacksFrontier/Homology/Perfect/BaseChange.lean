module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

@[expose] public section

/-!
# Perfect complexes under change of rings

Let `f : A → B` be a homomorphism of commutative rings. This module records the two change-of-ring
permanence properties of perfect complexes: restriction of scalars along `f` preserves perfectness
as soon as `B` is itself perfect as an `A`-module, and derived extension of scalars along `f`
always preserves perfectness.

## Main results

* `StacksDraft.Perfect.isPerfect_restrictScalars_of_isPerfectModule`: if `B` is perfect as an
  `A`-module, then a perfect complex of `B`-modules is perfect as a complex of `A`-modules
  ([stacks 066V]).
* `StacksDraft.Perfect.isPerfect_derivedExtensionScalars`: the derived base change `K ⊗_A^L B` of a
  perfect object of `D(A)` is a perfect object of `D(B)` ([stacks 066W]).
* `StacksDraft.Perfect.isPerfect_derivedExtensionScalars_of_comparison`: its general form, for any
  functor equipped with a comparison to termwise extension of scalars that is invertible on
  bounded-above complexes of projectives.

## Implementation notes

Both proofs work with an explicit bounded finite-projective representative, which is exactly what
`StacksDraft.Perfect.IsPerfect` provides.

For [stacks 066V] this avoids the Tor-amplitude route of the source: rather than combining
pseudo-coherence over `A` with a bound on the Tor amplitude of `B` over `A`, the argument observes
that a finite projective `B`-module is a direct summand of `Bⁿ`, hence -- by the summand statement
[stacks 066S] and the closure of perfect objects under finite direct sums, both applied in `D(A)`
-- is perfect as an `A`-module; a bounded complex of perfect `A`-modules is then perfect by
[stacks 066T]. Restriction of scalars is exact, so it induces a functor on derived categories and
the representative may be transported along it. The consequence is that this module needs no
derived tensor product and no Tor-amplitude comparison at all.

Derived extension of scalars, by contrast, cannot be described without naming the functor
computing it, since termwise extension of scalars is only right exact. [stacks 066W] is therefore
stated for the canonical total derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` of [stacks 064H]. The proof
uses only one property of that functor, namely that its comparison to termwise extension of
scalars is invertible on bounded-above complexes of projectives, so it is factored through a
general form quantifying over any functor with such a comparison.

The `A`-module carrier universe is the universe of `B` in [stacks 066V], which is what lets the
statement speak about `B` itself rather than a universe lift of it; the ring universes stay
independent. For [stacks 066W] the carrier universe is `max v uA uB`, as extension of scalars
enlarges a carrier by the universe of the target ring.

## References

* [Stacks Project, Tag 066V](https://stacks.math.columbia.edu/tag/066V)
* [Stacks Project, Tag 066W](https://stacks.math.columbia.edu/tag/066W)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe uA uB u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### Generalities on perfect objects

Three facts about `IsPerfect` used by both change-of-ring statements. They are consequences of
[stacks 066R] and are kept private, being auxiliary to the two results of this module.
-/

section Generalities

variable {R : Type u} [CommRing R]

/-- Perfectness is invariant under isomorphism in the derived category. -/
private lemma perfect_of_iso {X Y : DerivedCategory (ModuleCat.{v} R)} (e : X ≅ Y)
    (h : IsPerfect Y) : IsPerfect X := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e'⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hf, hp, ⟨e ≪≫ e'⟩⟩

/-- A binary direct sum of perfect objects is perfect: the split triangle
`X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧` is distinguished, so [stacks 066R] applies. -/
private lemma perfect_biprod (X Y : DerivedCategory (ModuleCat.{v} R)) (hX : IsPerfect X)
    (hY : IsPerfect Y) : IsPerfect (X ⊞ Y) :=
  (isPerfect_of_distinguished (binaryBiproductTriangle X Y)
    (binaryBiproductTriangle_distinguished X Y)).2.1 hX hY

/-- A zero object is perfect. The witness is produced from any perfect object via the contractible
triangle, whose third term is the zero object. -/
private lemma perfect_of_isZero {X Y : DerivedCategory (ModuleCat.{v} R)} (hX : IsZero X)
    (hY : IsPerfect Y) : IsPerfect X :=
  perfect_of_iso hX.isoZero
    ((isPerfect_of_distinguished (contractibleTriangle Y) (contractible_distinguished Y)).1 hY hY)

/-- A functor preserving zero morphisms keeps a complex bounded between degrees `a` and `b`
bounded between the same degrees. -/
private lemma isStrictlyGE_and_isStrictlyLE_map {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (P : CochainComplex C ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a ∧
      CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) b :=
  ⟨(CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
      F.map_isZero (P.isZero_of_isStrictlyGE a i hi),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
      F.map_isZero (P.isZero_of_isStrictlyLE b i hi)⟩

end Generalities

/-! ### Restriction of scalars -/

section RestrictScalars

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)

/-- Restriction of scalars along `f`, on modules whose carrier lies in the universe of `B`. -/
private noncomputable abbrev res : ModuleCat.{uB} B ⥤ ModuleCat.{uB} A :=
  ModuleCat.restrictScalars.{uB} f

/-- The `A`-module underlying `Bⁿ` is perfect as soon as `B` is perfect as an `A`-module. -/
private lemma perfect_single_res_pow
    (hB : IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{uB} A) 0).obj
      ((res f).obj (ModuleCat.of B B)))) (n : ℕ) :
    IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{uB} A) 0).obj
      ((res f).obj (ModuleCat.of B (Fin n → B)))) := by
  set S := DerivedCategory.singleFunctor (ModuleCat.{uB} A) 0
  have : PreservesBinaryBiproducts (res f) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts S := preservesBinaryBiproducts_of_preservesBiproducts _
  induction n with
  | zero =>
    exact perfect_of_isZero (Functor.map_isZero S (Functor.map_isZero (res f)
      (ModuleCat.isZero_iff_subsingleton.mpr inferInstance))) hB
  | succ n ih =>
    let X : ModuleCat.{uB} B := ModuleCat.of B B
    let Y : ModuleCat.{uB} B := ModuleCat.of B (Fin n → B)
    have e : X ⊞ Y ≅ ModuleCat.of B (Fin (n + 1) → B) :=
      ModuleCat.biprodIsoProd X Y ≪≫
        (Fin.consLinearEquiv B (fun _ : Fin (n + 1) => B)).toModuleIso
    exact perfect_of_iso
      ((S.mapIso (((res f).mapBiprod X Y).symm ≪≫ (res f).mapIso e)).symm ≪≫
        S.mapBiprod ((res f).obj X) ((res f).obj Y))
      (perfect_biprod _ _ hB ih)

/-- The `A`-module underlying a finite projective `B`-module is perfect as soon as `B` is perfect
as an `A`-module: the module is a direct summand of `Bⁿ`, and [stacks 066S] passes perfectness to
the summands. -/
private lemma perfect_single_res_of_finiteProjective
    (hB : IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{uB} A) 0).obj
      ((res f).obj (ModuleCat.of B B))))
    (M : ModuleCat.{uB} B) [Module.Finite B M] [Module.Projective B M] :
    IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{uB} A) 0).obj ((res f).obj M)) := by
  set S := DerivedCategory.singleFunctor (ModuleCat.{uB} A) 0
  have : PreservesBinaryBiproducts (res f) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts S := preservesBinaryBiproducts_of_preservesBiproducts _
  obtain ⟨n, p, s, -, -, hps⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (R := B) (M := (M : Type uB))
  let X : ModuleCat.{uB} B := ModuleCat.of B (LinearMap.ker p)
  have e : X ⊞ M ≅ ModuleCat.of B (Fin n → B) :=
    ModuleCat.biprodIsoProd X M ≪≫
      (lequivProdOfRightSplitExact (j := (LinearMap.ker p).subtype) (g := p) (f := s)
        (LinearMap.ker p).injective_subtype (Submodule.range_subtype _) hps).toModuleIso
  have key : IsPerfect (S.obj ((res f).obj X) ⊞ S.obj ((res f).obj M)) :=
    perfect_of_iso
      ((S.mapBiprod ((res f).obj X) ((res f).obj M)).symm ≪≫
        S.mapIso (((res f).mapBiprod X M).symm ≪≫ (res f).mapIso e))
      (perfect_single_res_pow f hB n)
  exact (isPerfect_of_biproduct _ _ key).2

/-- **Stacks 066V.** Let `f : A → B` be a homomorphism of commutative rings and assume that `B` is
perfect as an `A`-module. Then every perfect complex of `B`-modules is perfect as a complex of
`A`-modules. -/
@[stacks 066V]
theorem isPerfect_restrictScalars_of_isPerfectModule
    (hB : IsPerfectModule (R := A)
      ((ModuleCat.restrictScalars.{uB} f).obj (ModuleCat.of B B)))
    (K : CochainComplex (ModuleCat.{uB} B) ℤ)
    (hK : IsPerfect (DerivedCategory.Q.obj K)) :
    IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars.{uB} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨P, a, b, hPa, hPb, hfin, hproj, ⟨e⟩⟩ := hK
  have := hPa
  have := hPb
  have hB' : IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{uB} A) 0).obj
      ((res f).obj (ModuleCat.of B B))) := hB
  refine perfect_of_iso
    (((res f).mapDerivedCategoryFactors.app K).symm ≪≫
      (res f).mapDerivedCategory.mapIso e ≪≫ (res f).mapDerivedCategoryFactors.app P) ?_
  obtain ⟨hGE, hLE⟩ := isStrictlyGE_and_isStrictlyLE_map (res f) P a b
  refine isPerfect_of_bounded_of_isPerfectModule _ ⟨a, b, hGE, hLE⟩ fun i => ?_
  have : Module.Finite B (P.X i) := hfin i
  have : Module.Projective B (P.X i) := hproj i
  exact perfect_single_res_of_finiteProjective f hB' (P.X i)

end RestrictScalars

/-! ### Derived extension of scalars -/

section ExtendScalars

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
  [(ModuleCat.extendScalars.{uA, uB, max v uA uB} f).Additive]

/-- The general form of [stacks 066W]: let `f : A → B` be a homomorphism of commutative rings, let
`F` be a total left derived functor of termwise extension of scalars along `f` -- that is, a
functor `F : D(A) ⥤ D(B)` together with a comparison `c : Q ⋙ F ⟶ (B ⊗_A -) ⋙ Q` which is
invertible on bounded-above complexes of projectives -- and let `K` be a perfect object of `D(A)`.
Then `F.obj K = K ⊗_A^L B` is a perfect object of `D(B)`.

Only invertibility of the comparison on bounded-above complexes of projectives enters the proof,
so this applies to any construction of `- ⊗_A^L B`. The canonical case, which is the statement of
the source, is `StacksDraft.Perfect.isPerfect_derivedExtensionScalars`. -/
theorem isPerfect_derivedExtensionScalars_of_comparison
    (F : DerivedCategory (ModuleCat.{max v uA uB} A) ⥤
      DerivedCategory (ModuleCat.{max v uA uB} B))
    (c : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uA, uB, max v uA uB} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hc : ∀ (P : CochainComplex (ModuleCat.{max v uA uB} A) ℤ) (n : ℤ), P.IsStrictlyLE n →
      (∀ i : ℤ, Projective (P.X i)) → IsIso (c.app P))
    (K : DerivedCategory (ModuleCat.{max v uA uB} A)) (hK : IsPerfect K) :
    IsPerfect (F.obj K) := by
  obtain ⟨P, a, b, hPa, hPb, hfin, hproj, ⟨e⟩⟩ := hK
  have := hPa
  have := hPb
  have := hfin
  have := hproj
  let : Algebra A B := f.toAlgebra
  have hcP : IsIso (c.app P) := hc P b hPb fun i => inferInstance
  obtain ⟨hGE, hLE⟩ := isStrictlyGE_and_isStrictlyLE_map
    (ModuleCat.extendScalars.{uA, uB, max v uA uB} f) P a b
  refine ⟨((ModuleCat.extendScalars.{uA, uB, max v uA uB} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P, a, b, hGE, hLE, ?_, ?_, ⟨F.mapIso e ≪≫ asIso (c.app P)⟩⟩
  · intro i
    show Module.Finite B (TensorProduct A B (P.X i))
    infer_instance
  · intro i
    show Module.Projective B (TensorProduct A B (P.X i))
    infer_instance

end ExtendScalars

section CanonicalExtendScalars

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]

/-- **Stacks 066W.** Let `f : A → B` be a homomorphism of commutative rings and let `K` be a
perfect object of `D(A)`. Then the derived base change `K ⊗_A^L B` is a perfect object of
`D(B)`. -/
@[stacks 066W]
theorem isPerfect_derivedExtensionScalars (f : A →+* B)
    (K : DerivedCategory (ModuleCat.{max v uA uB} A)) (hK : IsPerfect K) :
    IsPerfect ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uB, v}
      f).functor.obj K) := by
  let : (ModuleCat.extendScalars.{uA, uB, max v uA uB} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uA v, uA, uB} f).isLeftAdjoint
  let : (ModuleCat.extendScalars.{uA, uB, max v uA uB} f).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uA, uB, v} f
  exact isPerfect_derivedExtensionScalars_of_comparison.{uA, uB, v} f D.functor D.comparison
    (fun P n hP hproj => by
      have := hP
      have := hproj
      exact D.comparison_isIso_of_projective P n) K hK

end CanonicalExtendScalars

end StacksDraft.Perfect
