module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.RingTheory.Syntomic.FiniteSquarePresentation

/-!
# Finite syntomic morphisms

A finite morphism of schemes is syntomic exactly when it is flat and a local complete
intersection morphism, and exactly when it is flat, locally of finite presentation and all of
its fibres are local complete intersections over the residue fields of their base points. A
finite morphism that is globally cut out by equally many equations as variables over suitable
affine opens of the target — over an affine open `U = Spec(A)` of the target the whole preimage,
which is affine, is `Spec(A[x_1, …, x_n]/(f_1, …, f_n))` — is syntomic as well.

## Main definitions

* `AlgebraicGeometry.HasAffineSquarePresentation`: the presentation condition, that around every
  point of the target there is an affine open `U = Spec(A)` over which the preimage is
  `Spec(A[x_1, …, x_n]/(f_1, …, f_n))`, with as many relations as variables.

## Main results

* `AlgebraicGeometry.finite_syntomic_tfae`: the equivalence of being finite and syntomic, finite
  flat and a local complete intersection morphism, and finite flat locally of finite presentation
  with local complete intersection fibres.
* `AlgebraicGeometry.finite_syntomic_of_hasAffineSquarePresentation`: a finite morphism with such
  presentations is syntomic.
* `AlgebraicGeometry.hasAffineSquarePresentation_of_finite_syntomic`: conversely, a finite
  syntomic morphism has such presentations.

## Implementation notes

The three conditions of the equivalence differ from the corresponding ones for a locally
quasi-finite morphism only in the common conjunct, `AlgebraicGeometry.IsFinite` in place of
`AlgebraicGeometry.LocallyQuasiFinite`, and a finite morphism is locally quasi-finite. So each
implication is the corresponding one for locally quasi-finite morphisms with the finiteness
conjunct carried along unused.

The presentation condition is phrased on rings of sections rather than as an isomorphism of
schemes: the `A`-algebra `Γ(Y, f⁻¹(U))` is isomorphic to `A[x_1, …, x_n]/(f_1, …, f_n)`. For a
morphism that is affine — in particular for a finite one, with which the condition is always
paired — the preimage `f⁻¹(U)` is an affine open, so this is the same as the isomorphism of
spectra. The `A`-algebra structure is the one induced by `AlgebraicGeometry.Scheme.Hom.appLE` on
the preimage, which is the restriction map `f.app U` itself
(`AlgebraicGeometry.Scheme.Hom.appLE_eq_app`); the `appLE` form is the one in which the
corresponding local conditions are stated.

Reading the presentation condition as the local presentation condition for locally quasi-finite
morphisms takes the whole preimage as the affine neighbourhood of the given point of the source,
and inverts the unit `1` (`IsLocalization.atUnits`), the local condition allowing a localization
of the polynomial ring.

*The naive cotangent complex.* Parts (5) and (6) of the source are conditions on `NL_{Y/X}`,
which appears in none of parts (1) to (4). They are treated in
`StacksFrontier/AlgebraicGeometry/Morphisms/Syntomic/FiniteNaiveCotangent.lean`, which proves the
equivalence of (1) with (5) and with (6).

*The converse implication (1) ⟹ (4).* Over an affine open `U = Spec(A)` of the target the
sections `B = Γ(Y, f⁻¹(U))` form a finite syntomic `A`-algebra, and the conormal module `I/I²`
of a presentation `B = A[x_1, …, x_n]/I` is finite locally free of rank `n`
(`Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic`). Over a base whose spectrum is
not semi-local that module need not be free, so no square presentation of `B` itself is
available; it does become free after inverting one element `g ∉ 𝔭` of `A`, by Algebra, Lemma
02M9 over the semi-local ring `B ⊗_A A_𝔭` followed by a spreading out
(`Stacks.RingTheory.SpreadFree.exists_mem_primeCompl_nonempty_basis_localizedModule`). Inverting
`g` adjoins one variable and one relation to the presentation and makes the conormal module
`(I/I²)_g ⊕ B_g` (Stacks 08JZ), free of rank `n + 1`; Algebra, Lemma 07CF
(`Algebra.Generators.exists_presentation_of_basis_cotangent`) adjoins one more of each and makes
the relations a basis of it, and quasi-finiteness makes the dimension condition of Definition
00SP automatic for the resulting square presentation. That is
`Algebra.exists_notMem_forall_isRelativeGlobalCompleteIntersection_of_finite_syntomic`, and
`AlgebraicGeometry.hasAffineSquarePresentation_of_finite_syntomic` is its scheme form, the
shrunken affine open being the basic open of `g`.

## References

* [Stacks Project, Tag 0FKY](https://stacks.math.columbia.edu/tag/0FKY)
* [Stacks Project, Tag 0BWE](https://stacks.math.columbia.edu/tag/0BWE)
* [Stacks Project, Tag 07CF](https://stacks.math.columbia.edu/tag/07CF)
* [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
* [Stacks Project, Tag 08JZ](https://stacks.math.columbia.edu/tag/08JZ)
* [Stacks Project, Tag 01UK](https://stacks.math.columbia.edu/tag/01UK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### The presentation condition -/

/-- The presentation condition of part (4) of Stacks 0FKY: for every point `x` of the target
there is an affine open `x ∈ U = Spec(A)` of the target, an integer `n` and
`f_1, …, f_n ∈ A[x_1, …, x_n]` such that the whole preimage of `U` is the spectrum of
`A[x_1, …, x_n]/(f_1, …, f_n)`, stated on rings of sections. -/
def HasAffineSquarePresentation {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    letI : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) :=
      (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
    ∃ (n : ℕ) (p : Fin n → MvPolynomial (Fin n) Γ(X, U.1)),
      Nonempty (Γ(Y, f ⁻¹ᵁ U.1) ≃ₐ[Γ(X, U.1)]
        (MvPolynomial (Fin n) Γ(X, U.1) ⧸ Ideal.span (Set.range p)))

/-- A presentation of the preimage of an affine open by as many relations as variables is, read
on that preimage as an affine neighbourhood of any of its points, a local presentation in the
sense of part (4) of Stacks 0BWE, with the unit `1` inverted. -/
private theorem hasLocalSquarePresentation_of_hasAffineSquarePresentation {Y X : Scheme.{u}}
    {f : Y ⟶ X} [IsAffineHom f] (h : HasAffineSquarePresentation f) :
    HasLocalSquarePresentation f := by
  intro y
  obtain ⟨U, hxU, n, p, ⟨e⟩⟩ := h (f.base y)
  let _ : Algebra Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1) :=
    (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  refine ⟨⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩, U, hxU, le_rfl, n, 1, p, ⟨?_⟩⟩
  have hH : Submonoid.powers (1 : MvPolynomial (Fin n) Γ(X, U.1)) ≤
      IsUnit.submonoid (MvPolynomial (Fin n) Γ(X, U.1)) := by
    rintro x ⟨k, rfl⟩
    simp
  let eloc : MvPolynomial (Fin n) Γ(X, U.1) ≃ₐ[Γ(X, U.1)]
      Localization.Away (1 : MvPolynomial (Fin n) Γ(X, U.1)) :=
    (IsLocalization.atUnits (MvPolynomial (Fin n) Γ(X, U.1)) (Submonoid.powers 1)
      (S := Localization.Away (1 : MvPolynomial (Fin n) Γ(X, U.1))) hH).restrictScalars _
  refine e.trans (Ideal.quotientEquivAlg _ _ eloc ?_)
  rw [Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  rfl

/-! ### The equivalence -/

/-- For a morphism of schemes `f : Y ⟶ X` the following are equivalent:

1. `f` is finite and syntomic;
2. `f` is finite, flat, and a local complete intersection morphism;
3. `f` is finite, flat, locally of finite presentation, and all the fibres of `f` are local
   complete intersections over the residue fields of their base points. -/
@[stacks 0FKY "the equivalence of (1), (2) and (3). Parts (5) and (6), the conditions on the
naive cotangent complex, are not among the three conditions of this equivalence; for those see
`StacksFrontier/AlgebraicGeometry/Morphisms/Syntomic/FiniteNaiveCotangent.lean`."]
theorem finite_syntomic_tfae {Y X : Scheme.{u}} (f : Y ⟶ X) :
    List.TFAE [
      IsFinite f ∧ Syntomic f,
      (IsFinite f ∧ Flat f) ∧ IsLocalCompleteIntersectionMorphism f,
      ((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
        ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x)] := by
  have key := locallyQuasiFinite_syntomic_tfae f
  have lqf : IsFinite f → LocallyQuasiFinite f := fun _ => inferInstance
  tfae_have 1 → 2 := fun h => by
    obtain ⟨⟨-, h2⟩, h3⟩ := (key.out 1 2).mp (by exact ⟨lqf h.1, h.2⟩)
    exact ⟨⟨h.1, h2⟩, h3⟩
  tfae_have 2 → 3 := fun h => by
    obtain ⟨⟨-, h2⟩, h3⟩ := (key.out 2 3).mp (by exact ⟨⟨lqf h.1.1, h.1.2⟩, h.2⟩)
    exact ⟨⟨h.1, h2⟩, h3⟩
  tfae_have 3 → 1 := fun h => by
    obtain ⟨-, h2⟩ := (key.out 3 1).mp (by exact ⟨⟨⟨lqf h.1.1.1, h.1.1.2⟩, h.1.2⟩, h.2⟩)
    exact ⟨h.1.1.1, h2⟩
  tfae_finish

/-- A finite syntomic morphism of schemes is flat and a local complete intersection morphism. -/
@[stacks 0FKY "the implication (1) ⟹ (2)"]
theorem flat_and_isLocalCompleteIntersectionMorphism_of_finite_syntomic {Y X : Scheme.{u}}
    {f : Y ⟶ X} (h : IsFinite f ∧ Syntomic f) :
    (IsFinite f ∧ Flat f) ∧ IsLocalCompleteIntersectionMorphism f :=
  (finite_syntomic_tfae f).out 1 2 |>.mp h

/-- A finite flat local complete intersection morphism of schemes is locally of finite presentation
and all of its fibres are local complete intersections over the residue fields of their base
points. -/
@[stacks 0FKY "the implication (2) ⟹ (3)", sga "6 VIII 1.4" "special case"]
theorem locallyOfFinitePresentation_and_lci_fibers_of_finite_flat_lci {Y X : Scheme.{u}}
    {f : Y ⟶ X} (h : (IsFinite f ∧ Flat f) ∧ IsLocalCompleteIntersectionMorphism f) :
    ((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x) :=
  (finite_syntomic_tfae f).out 2 3 |>.mp h

/-- A finite flat morphism of schemes which is locally of finite presentation and all of whose
fibres are local complete intersections over the residue fields of their base points is
syntomic. -/
@[stacks 0FKY "the implication (3) ⟹ (1)"]
theorem finite_syntomic_of_finite_flat_lci_fibers {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : ((IsFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x)) :
    IsFinite f ∧ Syntomic f :=
  (finite_syntomic_tfae f).out 3 1 |>.mp h

/-! ### The presentation condition and syntomicity -/

/-- A finite morphism of schemes whose preimages of suitable affine opens of the target are cut out
by as many equations as variables is syntomic. -/
@[stacks 0FKY "the implication (4) ⟹ (1)"]
theorem finite_syntomic_of_hasAffineSquarePresentation {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : IsFinite f ∧ HasAffineSquarePresentation f) : IsFinite f ∧ Syntomic f := by
  have := h.1
  exact ⟨h.1, (locallyQuasiFinite_and_syntomic_of_hasLocalSquarePresentation
    ⟨inferInstance, hasLocalSquarePresentation_of_hasAffineSquarePresentation h.2⟩).2⟩

/-! ### The converse implication (1) ⟹ (4) -/

/-- On affine opens, a syntomic morphism induces a syntomic algebra. -/
theorem algebra_syntomic_appLE {Y X : Scheme.{u}} {f : Y ⟶ X} (hf : Syntomic f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    Algebra.Syntomic Γ(X, U.1) Γ(Y, V.1) :=
  (HasRingHomProperty.iff_appLE (P := @Syntomic) (Q := RingHom.Syntomic)).mp hf U V hVU

/-- For a finite morphism, the sections over the preimage of an affine open form a module-finite
algebra, also when that preimage is presented as another open. -/
private theorem moduleFinite_appLE_of_eq {Y X : Scheme.{u}} {f : Y ⟶ X} [IsFinite f]
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : f ⁻¹ᵁ U = V) :
    letI : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hV.ge).hom.toAlgebra
    Module.Finite Γ(X, U) Γ(Y, V) := by
  have hfin : (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.Finite := by
    rw [Scheme.Hom.appLE_eq_app]
    exact f.finite_app U hU
  exact (f.appLE_congr le_rfl rfl hV (fun {_ _} g => g.hom.Finite)).mp hfin

/-- The zero algebra is cut out of a polynomial ring in one variable by the single relation `1`. -/
private theorem nonempty_algEquiv_quotient_of_subsingleton (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [Subsingleton S] :
    ∃ (n : ℕ) (p : Fin n → MvPolynomial (Fin n) R),
      Nonempty (S ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range p))) := by
  refine ⟨1, fun _ => 1, ⟨?_⟩⟩
  have htop : Ideal.span (Set.range (fun _ : Fin 1 => (1 : MvPolynomial (Fin 1) R))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, rfl⟩
  have : Subsingleton (MvPolynomial (Fin 1) R ⧸
      Ideal.span (Set.range (fun _ : Fin 1 => (1 : MvPolynomial (Fin 1) R)))) :=
    Ideal.Quotient.subsingleton_iff.mpr htop
  exact
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      commutes' := fun _ => Subsingleton.elim _ _ }

/-- A finite syntomic morphism of schemes is, over a suitable affine open neighbourhood of every
point of the target, cut out of a polynomial ring by as many equations as variables. -/
@[stacks 0FKY "the implication (1) ⟹ (4)"]
theorem hasAffineSquarePresentation_of_finite_syntomic {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : IsFinite f ∧ Syntomic f) : IsFinite f ∧ HasAffineSquarePresentation f := by
  classical
  have := h.1
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have hVY : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineHom.isAffine_preimage V hV
  let : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  have : Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := moduleFinite_appLE_of_eq hV rfl
  have : Algebra.Syntomic Γ(X, V) Γ(Y, f ⁻¹ᵁ V) :=
    algebra_syntomic_appLE h.2 ⟨V, hV⟩ ⟨f ⁻¹ᵁ V, hVY⟩ le_rfl
  obtain ⟨a, haV, hrgci⟩ :=
    Algebra.exists_notMem_forall_isRelativeGlobalCompleteIntersection_of_finite_syntomic
      (A := Γ(X, V)) (B := Γ(Y, f ⁻¹ᵁ V)) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxa : x ∈ X.basicOpen a := by
    rw [← hV.fromSpec_image_basicOpen]
    exact ⟨hV.primeIdealOf ⟨x, hxV⟩, haV, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
  have hVa : IsAffineOpen (X.basicOpen a) := hV.basicOpen a
  refine ⟨⟨X.basicOpen a, hVa⟩, hxa, ?_⟩
  have hb : f.app V a = algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V) a := by
    rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
  refine (f.appLE_congr le_rfl rfl (Scheme.preimage_basicOpen f a)
    (fun {R S} g => let := g.hom.toAlgebra
      ∃ (n : ℕ) (p : Fin n → MvPolynomial (Fin n) R),
        Nonempty (S ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range p))))).mpr ?_
  let : Algebra Γ(X, V) Γ(X, X.basicOpen a) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsLocalization.Away a Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
  let : Algebra Γ(Y, f ⁻¹ᵁ V) Γ(Y, Y.basicOpen (f.app V a)) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le (f.app V a))).op).hom.toAlgebra
  let : Algebra Γ(X, V) Γ(Y, Y.basicOpen (f.app V a)) :=
    ((algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, Y.basicOpen (f.app V a))).comp
      (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V))).toAlgebra
  let : IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, Y.basicOpen (f.app V a)) :=
    IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let : Algebra Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen (f.app V a)) :=
    (f.appLE (X.basicOpen a) (Y.basicOpen (f.app V a))
      (Scheme.preimage_basicOpen f a).ge).hom.toAlgebra
  let : IsScalarTower Γ(X, V) Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen (f.app V a)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hX : f.appLE V (f ⁻¹ᵁ V) le_rfl ≫
          Y.presheaf.map (homOfLE (Y.basicOpen_le (f.app V a))).op =
        f.appLE V (Y.basicOpen (f.app V a)) (Y.basicOpen_le (f.app V a)) := by
      rw [f.appLE_map]
    have hY : X.presheaf.map (homOfLE (X.basicOpen_le a)).op ≫
        f.appLE (X.basicOpen a) (Y.basicOpen (f.app V a))
          (Scheme.preimage_basicOpen f a).ge =
        f.appLE V (Y.basicOpen (f.app V a)) (Y.basicOpen_le (f.app V a)) := by
      rw [f.map_appLE]
    have hcg := congrArg CommRingCat.Hom.hom (hX.trans hY.symm)
    simpa only [CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra] using hcg
  let : IsLocalization.Away (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V) a)
      Γ(Y, Y.basicOpen (f.app V a)) := by
    rw [← hb]
    exact hVY.isLocalization_basicOpen (f.app V a)
  have := hrgci Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen (f.app V a))
  have : Module.Finite Γ(X, X.basicOpen a) Γ(Y, Y.basicOpen (f.app V a)) :=
    moduleFinite_appLE_of_eq hVa (Scheme.preimage_basicOpen f a)
  rcases subsingleton_or_nontrivial Γ(Y, Y.basicOpen (f.app V a)) with hsub | hnt
  · exact nonempty_algEquiv_quotient_of_subsingleton _ _
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum Γ(Y, Y.basicOpen (f.app V a))) := inferInstance
  have := q.isPrime
  obtain ⟨n, P, -⟩ := Algebra.exists_square_presentation
    (R := Γ(X, X.basicOpen a)) (S := Γ(Y, Y.basicOpen (f.app V a))) q.asIdeal
  exact ⟨n, P.relation, ⟨((Ideal.quotientEquivAlgOfEq _ P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars _)).symm⟩⟩

end AlgebraicGeometry

end
