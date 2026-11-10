module

import Mathlib.Algebra.Order.Ring.Star
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.CategoryTheory.Triangulated.Generators
import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.ThickSubcategory
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects.CellStructure

/-!
# Finite factorization and compact generators

Let `D` be a triangulated category with direct sums, and let `E : ι → D` be a family of compact
objects (`CategoryTheory.IsCompactObject`).

* Only finitely many of the generators are involved in any map into the `n`-th term `Xₙ` of a
  system of cell attachments (as in
  `StacksFrontier.CategoryTheory.Triangulated.CompactObjects.CellStructure`) out of a compact
  object: a morphism `C ⟶ Xₙ` with `C` compact factors as `C ⟶ Z ⟶ Xₙ` where `Z` lies in the
  triangulated envelope `⟨E_{i₁} ⊕ … ⊕ E_{i_t}⟩` of a *finite* subfamily.
* Consequently, for a compact object `E` the classical generators of `D_c` among the compact
  objects are exactly the generators of `D`, provided `D` has some set of compact generators at
  all: `E` is a weak generator of `D` if and only if `⟨E⟩ = D_c` and `D` is compactly generated.
  Being a generator of the big category `D` is what forces the small category `D_c` to be swept out
  by `E` under shifts, sums, extensions and direct summands.

## Main results

* `CategoryTheory.Pretriangulated.exists_fac_triangEnvelope_of_isCompactObject`: a morphism from
  a compact object to the `n`-th term of a system of cell attachments factors through an object of
  the triangulated envelope of a finite direct sum of the generators.
* `isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`
  (in the `CategoryTheory.ObjectProperty` namespace): for a compact object `E`, the property
  `ObjectProperty.singleton E` is a weak generator of `D` if and only if its triangulated envelope
  is the property of being a compact object and `D` is compactly generated.
* `triangEnvelope_eq_isCompactObject_of_isWeakTriangulatedGenerator_ofObj` (in the
  `CategoryTheory.ObjectProperty` namespace): the same identification of the compact objects with
  the triangulated envelope, for a nonempty family of compact generators rather than a single
  one.

## Implementation notes

*The finite factorization.* Here the system is a sequence `X : ℕ → D` of objects with distinguished
triangles, rather than a functor `ℕ ⥤ D`: no step uses functoriality of the system, only that
`X (n + 1)` is an extension of a direct sum of shifts of the `E i` by `X n`, so a user instantiates
`X := F.obj` and reads the triangles off the cell tower. The two hypotheses of the cell-tower
result that its own proof needs but this one does not are dropped: the system is not required to
have a derived colimit, and `⨁ E i` is not required to generate `D`. Compactness of the `E i` is
kept, because the induction factors a morphism out of the cone of `C ⟶ E'⟦1⟧` with `E'` a finite
sum of shifts of the `E i`, and that cone is compact only because `E'` is. `⟨E_{i₁} ⊕ … ⊕ E_{i_t}⟩`
is `ObjectProperty.triangEnvelope` of the singleton property of the finite coproduct `∐ i : s, E i`
over a finite set `s : Finset ι` of indices ([Stacks, Tag 0ATG]). Taking the envelope of the single
object `∐ i : s, E i` rather than of the subfamily `fun i : s ↦ E i` follows the source and is what
makes the statement correct for `s = ∅` as well: the envelope of the empty family is empty, whereas
the envelope of the zero object consists of the zero objects. Closure of a strictly full
triangulated subcategory under finite direct sums is not in Mathlib as such and is proved here as
`isClosedUnderFiniteCoproducts_of_isTriangulated`: the full subcategory it spans is
pretriangulated, hence has finite coproducts, and the inclusion is additive, hence preserves them.
The minimality of the envelope (`triangEnvelope_le_iff`) gives the monotonicity in the finite index
set that lets the three subsets produced by the induction be replaced by their union.

*Compact generators.* The condition "`E` is a classical generator for `D_c`" is stated as the
equality of object properties `(singleton E).triangEnvelope = IsCompactObject.{v}` in `D`, rather
than as `ObjectProperty.IsClassicalTriangulatedGenerator` of a singleton inside the full
subcategory spanned by the compact objects. This is the form the source's own proof uses
("`D_c = ⟨E⟩`"), and the two agree: `D_c` is a strictly full, saturated, triangulated subcategory
of `D` whose distinguished triangles are those of `D`, so each of the four operations building the
envelope — shift, binary product, retract, extension in a distinguished triangle — is computed the
same way in `D_c` as in `D`, and the envelope of `E` formed inside `D_c` is the envelope formed
inside `D`. Stating the equality in `D` also avoids transporting the statement along the inclusion
`D_c ⥤ D`, and it is an equality of `ObjectProperty D`, hence pins which objects the subcategory
has. One inequality is automatic: `E` is compact and `IsCompactObject` is stable under retracts and
triangulated, so `⟨E⟩ ≤ D_c` always, and the content of the clause is `D_c ≤ ⟨E⟩`, i.e. that every
compact object is built from `E`. The equivalence is stated for a single object, as in the source.
The implication that carries the content holds for a family `E : ι → D` of compact objects with
`ι : Type v` — the route through the cell tower and the finite factorization is already stated
family-wise — but only under the extra hypothesis that `ι` is nonempty: for `ι` empty and `D` a
category all of whose objects are zero, `ObjectProperty.ofObj E` is `⊥`, whose envelope is again
`⊥`, while every object of `D` is compact. The family form is therefore a statement of its own,
`triangEnvelope_eq_isCompactObject_of_isWeakTriangulatedGenerator_ofObj`, carrying that hypothesis;
the single-object implication is read off from it for the one-element family `fun _ : PUnit => E`,
and it is the family form that applies inside a localizing subcategory generated by a family of
compact objects, in `StacksFrontier/CategoryTheory/Triangulated/NeemanThomason.lean`.

Three steps of that argument are lemmas of the general theory: a colimit of abelian groups is
exhausted by any subgroup of its vertex containing the images of the legs of the cocone, whence
every element of a filtered colimit of abelian groups comes from a stage; that compactness in the
sense of [Stacks, Tag 07LS] is the same as the preservation of direct sums by
`preadditiveCoyoneda.obj (op K)`, which is the form [Stacks, Tag 094A] asks for (the coproduct of
the groups `Hom(K, E i)` in `AddCommGrpCat` is generated by the images of its coprojections, so the
comparison morphism is bijective as soon as the canonical map of that tag is, whence preservation
of coproducts by `Limits.PreservesCoproduct.of_iso_comparison`; the countable case is obtained from
the case `J = ULift.{v} ℕ` along `Discrete (ULift.{v} ℕ) ≌ Discrete ℕ`); and right orthogonality to
the shifts of `X` may be read on either side, i.e. all maps from shifts of `X` to `K` vanish
exactly when all maps from `X` to shifts of `K` do, which is the content of [Stacks, Tag 09SK].

## References

* [Stacks project, Tag 09SP](https://stacks.math.columbia.edu/tag/09SP)
* [Stacks project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
* [Stacks project, Tag 09SK](https://stacks.math.columbia.edu/tag/09SK)
* [Stacks project, Tag 0ATG](https://stacks.math.columbia.edu/tag/0ATG)
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Pretriangulated

open Limits ObjectProperty

/-! ### A compact object mapping into a cell object factors through finitely many generators -/

section Factorization

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{v} D]

omit [IsTriangulated D] [HasCoproducts.{v} D] in
/-- A strictly full triangulated subcategory is closed under finite direct sums: the full
subcategory it spans is pretriangulated, hence has finite coproducts, and the inclusion is
additive, hence preserves them. -/
private lemma prop_coproduct_of_isTriangulated (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated] {J : Type*} [Finite J] {f : J → D}
    [HasCoproduct f] (h : ∀ j, P (f j)) : P (∐ f) :=
  have : P.IsClosedUnderFiniteCoproducts :=
    ⟨fun _ _ ↦ P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩
  P.prop_coproduct h

omit [IsTriangulated D] [HasCoproducts.{v} D] in
/-- A strictly full triangulated subcategory is closed under binary direct sums. -/
private lemma prop_biprod_of_isTriangulated (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated] {X₁ X₂ : D} (h₁ : P X₁) (h₂ : P X₂) :
    P (X₁ ⊞ X₂) :=
  P.ext_of_isTriangulatedClosed₂ _ (binaryBiproductTriangle_distinguished X₁ X₂) h₁ h₂

omit [IsTriangulated D] in
/-- The compact objects form a strictly full triangulated subcategory. -/
private lemma compactObject_isClosedUnderIsomorphisms_and_isTriangulated :
    ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObject.{v} (C := D)) ∧
      ObjectProperty.IsTriangulated (IsCompactObject.{v} (C := D)) :=
  ⟨isClosedUnderIsomorphisms_isCompactObject, isTriangulated_isCompactObject⟩

omit [IsTriangulated D] [HasCoproducts.{v} D] in
/-- Each member of a finite subfamily is a direct summand of the finite direct sum, hence lies
in the triangulated envelope of that direct sum. -/
private lemma triangEnvelope_sigma_apply {ι : Type v} (E : ι → D) (s : Finset ι) {i : ι}
    (hi : i ∈ s) : (ObjectProperty.singleton (∐ fun i : s ↦ E i)).triangEnvelope (E i) := by
  classical
  have hr : Retract (E i) (∐ fun j : s ↦ E j) :=
    { i := Limits.Sigma.ι (fun j : s ↦ E j) ⟨i, hi⟩
      r := Limits.Sigma.desc (fun j : s ↦ if h : (j : ι) = i then eqToHom (by rw [h]) else 0)
      retract := by simp }
  exact ObjectProperty.prop_of_retract _ hr (le_triangEnvelope _ _ (by simp))

omit [HasCoproducts.{v} D] in
/-- The triangulated envelope of `∐_{i ∈ s} E i` grows with `s`. -/
private lemma triangEnvelope_mono {ι : Type v} (E : ι → D) {s t : Finset ι} (hst : s ⊆ t) :
    (ObjectProperty.singleton (∐ fun i : s ↦ E i)).triangEnvelope ≤
      (ObjectProperty.singleton (∐ fun i : t ↦ E i)).triangEnvelope := by
  rw [triangEnvelope_le_iff]
  intro Z hZ
  rw [ObjectProperty.singleton_iff] at hZ
  subst hZ
  exact prop_coproduct_of_isTriangulated
    (ObjectProperty.singleton (∐ fun i : t ↦ E i)).triangEnvelope
    fun j : s ↦ triangEnvelope_sigma_apply E t (hst j.2)

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- An object which is a direct sum of shifts of the `E i` is isomorphic to a coproduct
`∐ (E (f j))⟦m j⟧`. -/
private lemma exists_iso_sigma {ι : Type v} (E : ι → D) {W : D}
    (hW : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) W) :
    ∃ (J : Type v) (f : J → ι) (m : J → ℤ), Nonempty (W ≅ ∐ fun j ↦ (E (f j))⟦m j⟧) := by
  rw [ObjectProperty.prop_iSup_iff] at hW
  obtain ⟨J, ⟨p⟩⟩ := hW
  choose Y a e hY using p.prop_diag_obj
  choose g hg using fun j ↦ (ObjectProperty.ofObj_iff E (Y j)).1 (hY j)
  refine ⟨J, fun j ↦ g ⟨j⟩, fun j ↦ a ⟨j⟩, ⟨?_⟩⟩
  refine (p.isColimit.coconePointUniqueUpToIso (colimit.isColimit p.diag)).trans ?_
  refine (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := p.diag))).trans ?_
  exact Limits.Sigma.mapIso fun j ↦ (e ⟨j⟩).trans (eqToIso (by rw [hg ⟨j⟩]))

omit [IsTriangulated D] in
/-- A morphism from a compact object into a direct sum factors through a finite subsum. -/
private lemma exists_fac_sigma_of_isCompactObject {J : Type v} (G : J → D)
    {C : D} (hC : IsCompactObject.{v} C) (ψ : C ⟶ ∐ G) :
    ∃ (t : Finset J) (b : C ⟶ ∐ fun j : t ↦ G j),
      b ≫ Limits.Sigma.desc (fun j : t ↦ Limits.Sigma.ι G j.1) = ψ := by
  classical
  obtain ⟨-, hsurj⟩ := hC.bijective_toAddMonoid_rightComp_sigmaι G
  obtain ⟨d, hd⟩ := hsurj ψ
  have key : ψ = ∑ j ∈ DFinsupp.support d, d j ≫ Limits.Sigma.ι G j := by
    rw [← hd]
    conv_lhs => rw [← DirectSum.sum_support_of d]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ DirectSum.toAddMonoid_of _ _ _
  refine ⟨DFinsupp.support d, ∑ j ∈ (DFinsupp.support d).attach,
    d j.1 ≫ Limits.Sigma.ι (fun j : (DFinsupp.support d) ↦ G j.1) j, ?_⟩
  rw [key, Preadditive.sum_comp]
  conv_rhs => rw [← Finset.sum_attach (DFinsupp.support d) fun j ↦ d j ≫ Limits.Sigma.ι G j]
  exact Finset.sum_congr rfl fun j _ ↦ by simp

/-- **The key factorization.** A morphism from a compact object `C` into a direct sum `W` of
shifts of the `E i` factors through an object `Z` which is compact and lies in the triangulated
envelope of `∐_{i ∈ s} E i` for a finite set `s` of indices. -/
private lemma exists_fac_triangEnvelope_of_prop {ι : Type v} (E : ι → D)
    [∀ i, IsCompactObject.{v} (E i)] {W : D}
    (hW : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) W)
    {C : D} (hC : IsCompactObject.{v} C) (ψ : C ⟶ W) :
    ∃ (s : Finset ι) (Z : D), IsCompactObject.{v} Z ∧
      (ObjectProperty.singleton (∐ fun i : s ↦ E i)).triangEnvelope Z ∧
      ∃ (a : C ⟶ Z) (b : Z ⟶ W), a ≫ b = ψ := by
  classical
  obtain ⟨hiso, htri⟩ := compactObject_isClosedUnderIsomorphisms_and_isTriangulated (D := D)
  obtain ⟨J, f, m, ⟨eW⟩⟩ := exists_iso_sigma E hW
  obtain ⟨t, b, hb⟩ := exists_fac_sigma_of_isCompactObject _ hC (ψ ≫ eW.hom)
  refine ⟨t.image f, ∐ fun j : t ↦ (E (f j))⟦m j⟧, ?_, ?_, b,
    Limits.Sigma.desc (fun j : t ↦ Limits.Sigma.ι (fun j ↦ (E (f j))⟦m j⟧) j.1) ≫ eW.inv, ?_⟩
  · exact prop_coproduct_of_isTriangulated (IsCompactObject.{v} (C := D))
      fun j : t ↦ ObjectProperty.le_shift (IsCompactObject.{v} (C := D)) (m j.1) _ inferInstance
  · exact prop_coproduct_of_isTriangulated
      (ObjectProperty.singleton (∐ fun i : (t.image f) ↦ E i)).triangEnvelope
      fun j : t ↦ ObjectProperty.le_shift
        (ObjectProperty.singleton (∐ fun i : (t.image f) ↦ E i)).triangEnvelope (m j.1) _
        (triangEnvelope_sigma_apply E _ (Finset.mem_image_of_mem f j.2))
  · rw [← Category.assoc, hb, Category.assoc, eW.hom_inv_id, Category.comp_id]

/-- The shifted form of `exists_fac_triangEnvelope_of_prop`: a morphism `C ⟶ Y⟦1⟧` out of a
compact object, with `Y` a direct sum of shifts of the `E i`, factors as `C ⟶ Z⟦1⟧ ⟶ Y⟦1⟧`
with the second morphism the shift of a morphism `Z ⟶ Y`. It is deduced from the unshifted
form applied to the compact object `C⟦-1⟧`, using that the shift is an equivalence. -/
private lemma exists_fac_shift_triangEnvelope_of_prop {ι : Type v} (E : ι → D)
    [∀ i, IsCompactObject.{v} (E i)] {Y : D}
    (hY : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y)
    {C : D} (hC : IsCompactObject.{v} C) (ψ : C ⟶ Y⟦(1 : ℤ)⟧) :
    ∃ (s : Finset ι) (Z : D), IsCompactObject.{v} Z ∧
      (ObjectProperty.singleton (∐ fun i : s ↦ E i)).triangEnvelope Z ∧
      ∃ (u : C ⟶ Z⟦(1 : ℤ)⟧) (b : Z ⟶ Y), u ≫ b⟦(1 : ℤ)⟧' = ψ := by
  have ε : (C⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ C :=
    (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by simp)).app C
  obtain ⟨s, Z, hZc, hZe, a, b, hab⟩ :=
    exists_fac_triangEnvelope_of_prop E hY (isCompactObject_shift hC (-1))
      ((shiftFunctor D (1 : ℤ)).preimage
        (show (C⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ⟶ Y⟦(1 : ℤ)⟧ from ε.hom ≫ ψ))
  refine ⟨s, Z, hZc, hZe, ε.inv ≫ a⟦(1 : ℤ)⟧', b, ?_⟩
  rw [Category.assoc, ← Functor.map_comp, hab, Functor.map_preimage, Iso.inv_hom_id_assoc]

/-- The induction of [Stacks, Tag 09SP], on the number of cell attachments. -/
private lemma exists_fac_aux {ι : Type v} (E : ι → D) [∀ i, IsCompactObject.{v} (E i)]
    {X : ℕ → D}
    (hX₀ : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) (X 0))
    (hX : ∀ n : ℕ, ∃ Y : D,
      (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y ∧
        ∃ (f : Y ⟶ X n) (g : X n ⟶ X (n + 1)) (h : X (n + 1) ⟶ Y⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang D) (n : ℕ) :
    ∀ (C : D), IsCompactObject.{v} C → ∀ φ : C ⟶ X n,
      ∃ (s : Finset ι) (Z : D), (ObjectProperty.singleton (∐ fun i : s ↦ E i)).triangEnvelope Z ∧
        ∃ (a : C ⟶ Z) (b : Z ⟶ X n), a ≫ b = φ := by
  classical
  obtain ⟨hiso, htri⟩ := compactObject_isClosedUnderIsomorphisms_and_isTriangulated (D := D)
  induction n with
  | zero =>
    intro C hC φ
    obtain ⟨s, Z, -, hZe, a, b, hab⟩ := exists_fac_triangEnvelope_of_prop E hX₀ hC φ
    exact ⟨s, Z, hZe, a, b, hab⟩
  | succ n ih =>
    intro C hC φ
    obtain ⟨Y, hY, f, g, h, hT⟩ := hX n
    obtain ⟨s₁, E', hE'c, hE'e, u, b₁, hu⟩ :=
      exists_fac_shift_triangEnvelope_of_prop E hY hC (φ ≫ h)
    obtain ⟨C', p, q, hT₁⟩ := distinguished_cocone_triangle₂ u
    have hC' : IsCompactObject.{v} C' :=
      ObjectProperty.ext_of_isTriangulatedClosed₂ (IsCompactObject.{v} (C := D)) _ hT₁ hE'c hC
    obtain ⟨β, hβ₁, -⟩ : ∃ β : C' ⟶ X n, p ≫ β = b₁ ≫ f ∧ q ≫ φ = β ≫ g :=
      complete_distinguished_triangle_morphism₂ _ _ hT₁ hT b₁ φ hu
    obtain ⟨s₂, Z₂, hZ₂e, a₂, b₂, hab₂⟩ := ih C' hC' β
    obtain ⟨Zc, c₁, c₂, hT₃⟩ := distinguished_cocone_triangle (p ≫ a₂)
    obtain ⟨w, -, hw₂⟩ :
        ∃ w : C ⟶ Zc, q ≫ w = a₂ ≫ c₁ ∧ u ≫ (𝟙 E')⟦(1 : ℤ)⟧' = w ≫ c₂ :=
      complete_distinguished_triangle_morphism _ _ hT₁ hT₃ (𝟙 E') a₂ (by simp)
    obtain ⟨v, -, hv₂⟩ :
        ∃ v : Zc ⟶ X (n + 1), c₁ ≫ v = b₂ ≫ g ∧ c₂ ≫ b₁⟦(1 : ℤ)⟧' = v ≫ h :=
      complete_distinguished_triangle_morphism _ _ hT₃ hT b₁ b₂
        (by dsimp only [Triangle.mk_mor₁]; rw [Category.assoc, hab₂]; exact hβ₁)
    have hu' : w ≫ c₂ = u := by simpa using hw₂.symm
    have hδ : (φ - w ≫ v) ≫ h = 0 := by
      have h₁ : w ≫ v ≫ h = φ ≫ h := by
        rw [← hv₂, ← Category.assoc, hu']; exact hu
      rw [Preadditive.sub_comp, Category.assoc, h₁, sub_self]
    obtain ⟨ψ', hψ'⟩ := Triangle.coyoneda_exact₃ _ hT (φ - w ≫ v) hδ
    obtain ⟨s₃, Z₃, hZ₃e, a₃, b₃, hab₃⟩ := ih C hC ψ'
    refine ⟨s₁ ∪ s₂ ∪ s₃, Zc ⊞ Z₃, ?_, biprod.lift w a₃, biprod.desc v (b₃ ≫ g), ?_⟩
    · refine prop_biprod_of_isTriangulated _ ?_ ?_
      · refine ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hT₃ ?_ ?_
        · exact triangEnvelope_mono E
            (Finset.subset_union_left.trans Finset.subset_union_left) _ hE'e
        · exact triangEnvelope_mono E
            (Finset.subset_union_right.trans Finset.subset_union_left) _ hZ₂e
      · exact triangEnvelope_mono E Finset.subset_union_right _ hZ₃e
    · have hψ'' : φ - w ≫ v = ψ' ≫ g := hψ'
      rw [biprod.lift_desc, ← Category.assoc, hab₃, ← hψ'']
      abel

/-- **Stacks 09SP**. Let `D` be a triangulated category with direct sums, `E : ι → D` a family of
compact objects, and `X : ℕ → D` a system of cell attachments as in [Stacks, Tag 09SN]: `X 0` is
a direct sum of shifts of the `E i` and each `X (n + 1)` fits into a distinguished triangle
`Yₙ ⟶ X n ⟶ X (n + 1) ⟶ Yₙ⟦1⟧` with `Yₙ` a direct sum of shifts of the `E i`. Then every
morphism `φ : C ⟶ X n` from a compact object `C` factors as `C ⟶ Z ⟶ X n` with `Z` an object of
the triangulated envelope `⟨E_{i₁} ⊕ … ⊕ E_{i_t}⟩` of a finite direct sum of the `E i`. -/
@[stacks 09SP]
public theorem exists_fac_triangEnvelope_of_isCompactObject
    {ι : Type v} (E : ι → D) [∀ i, IsCompactObject.{v} (E i)] {X : ℕ → D}
    (hX₀ : (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) (X 0))
    (hX : ∀ n : ℕ, ∃ Y : D,
      (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y ∧
        ∃ (f : Y ⟶ X n) (g : X n ⟶ X (n + 1)) (h : X (n + 1) ⟶ Y⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang D)
    {C : D} [IsCompactObject.{v} C] {n : ℕ} (φ : C ⟶ X n) :
    ∃ (s : Finset ι) (Z : D), (ObjectProperty.singleton (∐ fun i : s ↦ E i)).triangEnvelope Z ∧
      ∃ (a : C ⟶ Z) (b : Z ⟶ X n), a ≫ b = φ :=
  exists_fac_aux E hX₀ hX n C inferInstance φ

end Factorization

end CategoryTheory.Pretriangulated

/-! ### Compact generators: classical generators of `D_c` versus generators of `D` -/

namespace CategoryTheory.ObjectProperty

open Limits Opposite Preadditive DirectSum Pretriangulated

section OfObj

/-- Morphisms `X⟦n⟧ ⟶ K` all vanish exactly when morphisms `X ⟶ K⟦-n⟧` all do. -/
private lemma forall_shift_hom_eq_zero_iff_of_hasZeroMorphisms {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasShift C ℤ] (n : ℤ) (X K : C) :
    (∀ f : X⟦n⟧ ⟶ K, f = 0) ↔ ∀ g : X ⟶ K⟦-n⟧, g = 0 := by
  -- A shift is an equivalence, hence a right adjoint, hence preserves zero morphisms, and it is
  -- faithful: so it reflects the vanishing of a morphism, with no additivity assumption.
  have reflects : ∀ (m : ℤ) {X Y : C} (g : X ⟶ Y), (shiftFunctor C m).map g = 0 → g = 0 := by
    intro m X Y g hg
    have hz : (shiftFunctor C m).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isRightAdjoint _
    exact (shiftFunctor C m).map_injective (by rw [hg, hz.map_zero])
  refine ⟨fun h g => ?_, fun h f => ?_⟩
  · have e : ((K⟦-n⟧ : C)⟦n⟧ : C) ≅ K := (shiftFunctorCompIsoId C (-n) n (by simp)).app K
    have h1 : (shiftFunctor C n).map g ≫ e.hom = 0 := h _
    exact reflects n g ((cancel_mono e.hom).mp (by rw [h1, zero_comp]))
  · have e : ((X⟦n⟧ : C)⟦-n⟧ : C) ≅ X := (shiftFunctorCompIsoId C n (-n) (by simp)).app X
    have h1 : e.inv ≫ (shiftFunctor C (-n)).map f = 0 := h _
    refine reflects (-n) f ?_
    rw [← Iso.hom_inv_id_assoc e ((shiftFunctor C (-n)).map f), h1, comp_zero]

/-- A morphism out of `∐ E` vanishes exactly when all of its components do. -/
private lemma forall_sigma_hom_eq_zero_iff {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type w} (E : ι → C) [HasCoproduct E] (L : C) :
    (∀ g : ∐ E ⟶ L, g = 0) ↔ ∀ (i : ι) (g : E i ⟶ L), g = 0 := by
  classical
  refine ⟨fun h i g => ?_, fun h g => ?_⟩
  · have hd : (Limits.Sigma.desc fun j => if hj : j = i then eqToHom (congrArg E hj) ≫ g
        else (0 : E j ⟶ L)) = 0 := h _
    have key := Limits.Sigma.ι_comp_desc
      (fun j => if hj : j = i then eqToHom (congrArg E hj) ≫ g else (0 : E j ⟶ L)) i
    rw [hd, comp_zero] at key
    simpa using key.symm
  · refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [h i (Limits.Sigma.ι E i ≫ g), comp_zero]

/-- Orthogonality to the shift closure of a property, tested on the objects of the property. -/
private lemma rightOrthogonal_shiftClosure_iff_of_hasZeroMorphisms {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasShift C ℤ] (P : ObjectProperty C) (K : C) :
    (P.shiftClosure ℤ).rightOrthogonal K ↔ ∀ X, P X → ∀ (n : ℤ) (f : X⟦n⟧ ⟶ K), f = 0 := by
  refine ⟨fun h X hX n f => h f ⟨X, n, Iso.refl _, hX⟩, fun h Z f hZ => ?_⟩
  obtain ⟨X, a, e, hX⟩ := hZ
  rw [← Iso.hom_inv_id_assoc e f, h X hX a (e.inv ≫ f), comp_zero]

/-- A family of objects is a weak generator if and only if its direct sum is one: for a family
`E : ι → C` whose coproduct exists, the property of belonging to `E` is a weak generator exactly
when the single object `∐ E` is. This identifies the family-wise condition with the source's
condition on `⨁ E i` in Definition [Stacks, Tag 09SQ]. -/
@[stacks 09SQ "the source's form of the generation condition: the direct sum ∐ E is a weak \
  generator"]
public theorem isWeakTriangulatedGenerator_ofObj_iff {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasShift C ℤ] {ι : Type w} (E : ι → C) [HasCoproduct E] :
    (ofObj E).IsWeakTriangulatedGenerator ↔
      (ObjectProperty.singleton (∐ E)).IsWeakTriangulatedGenerator := by
  have main : ∀ K : C, (((ofObj E).shiftClosure ℤ).rightOrthogonal K ↔
      ((ObjectProperty.singleton (∐ E)).shiftClosure ℤ).rightOrthogonal K) := by
    intro K
    have hL : (∀ X, ofObj E X → ∀ (n : ℤ) (f : X⟦n⟧ ⟶ K), f = 0) ↔
        ∀ (n : ℤ) (i : ι) (g : E i ⟶ K⟦-n⟧), g = 0 := by
      refine ⟨fun h n i g => ?_, fun h X hX n f => ?_⟩
      · exact (forall_shift_hom_eq_zero_iff_of_hasZeroMorphisms n (E i) K).mp
          (h (E i) (ofObj_apply E i) n) g
      · obtain ⟨i, rfl⟩ := (ofObj_iff E X).mp hX
        exact (forall_shift_hom_eq_zero_iff_of_hasZeroMorphisms n (E i) K).mpr (h n i) f
    have hR : (∀ X, ObjectProperty.singleton (∐ E) X → ∀ (n : ℤ) (f : X⟦n⟧ ⟶ K), f = 0) ↔
        ∀ (n : ℤ) (g : ∐ E ⟶ K⟦-n⟧), g = 0 := by
      refine ⟨fun h n g => ?_, fun h X hX n f => ?_⟩
      · exact (forall_shift_hom_eq_zero_iff_of_hasZeroMorphisms n (∐ E) K).mp
          (h _ (ofObj_apply _ ()) n) g
      · obtain ⟨_, rfl⟩ := (ofObj_iff _ X).mp hX
        exact (forall_shift_hom_eq_zero_iff_of_hasZeroMorphisms n (∐ E) K).mpr (h n) f
    rw [rightOrthogonal_shiftClosure_iff_of_hasZeroMorphisms,
      rightOrthogonal_shiftClosure_iff_of_hasZeroMorphisms, hL, hR]
    exact forall_congr' fun n => (forall_sigma_hom_eq_zero_iff E (K⟦-n⟧)).symm
  exact forall_congr' fun K => imp_congr (main K) Iff.rfl

end OfObj

section Groups

/-- Every element of a filtered colimit of abelian groups comes from one of the stages. -/
lemma _root_.AddCommGrpCat.exists_ι_apply_eq {J : Type*} [Category J] [IsFiltered J]
    {G : J ⥤ AddCommGrpCat.{v}} {c : Cocone G} (hc : IsColimit c) (a : c.pt) :
    ∃ (j : J) (x : G.obj j), ConcreteCategory.hom (c.ι.app j) x = a := by
  have : Nonempty J := IsFiltered.nonempty
  let S : AddSubgroup c.pt :=
    { carrier := {a | ∃ (j : J) (x : G.obj j), ConcreteCategory.hom (c.ι.app j) x = a}
      zero_mem' := ⟨Classical.arbitrary J, 0, map_zero _⟩
      add_mem' := by
        rintro a b ⟨j, x, rfl⟩ ⟨j', y, rfl⟩
        refine ⟨IsFiltered.max j j', G.map (IsFiltered.leftToMax j j') x
          + G.map (IsFiltered.rightToMax j j') y, ?_⟩
        have h1 := ConcreteCategory.congr_hom (c.w (IsFiltered.leftToMax j j')) x
        have h2 := ConcreteCategory.congr_hom (c.w (IsFiltered.rightToMax j j')) y
        simp only [ConcreteCategory.comp_apply] at h1 h2
        rw [map_add, h1, h2]
      neg_mem' := by
        rintro a ⟨j, x, rfl⟩
        exact ⟨j, -x, map_neg _ _⟩ }
  exact mem_of_isColimit hc S (fun j x ↦ ⟨j, x, rfl⟩) a

end Groups

section Compact

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{v} D]

/-- For a compact object `K` and a family `E : J → D` indexed by the universe of the direct sums,
the comparison morphism `⨁ Hom(K, E i) ⟶ Hom(K, ∐ E)` is an isomorphism of abelian groups: this
is the bijectivity in the definition of compactness ([Stacks, Tag 07LS]), read as an isomorphism
in `AddCommGrpCat`. -/
private lemma isIso_sigmaComparison_preadditiveCoyoneda (K : D) [IsCompactObject.{v} K]
    {J : Type v} (E : J → D) :
    IsIso (sigmaComparison (preadditiveCoyoneda.obj (op K)) E) := by
  classical
  have hbij : Function.Bijective
      (DirectSum.toAddMonoid fun i => Preadditive.rightComp K (Limits.Sigma.ι E i)) :=
    IsCompactObject.bijective_toAddMonoid_rightComp_sigmaι E
  let α : (DirectSum J fun i => (K ⟶ E i)) ≃+ (K ⟶ ∐ E) := AddEquiv.ofBijective _ hbij
  have hα : ∀ (i : J) (g : K ⟶ E i), α (DirectSum.of _ i g) = g ≫ Limits.Sigma.ι E i := by
    intro i g
    change (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι E j))
      (DirectSum.of _ i g) = _
    rw [DirectSum.toAddMonoid_of]
    rfl
  let ι₀ : ∀ i : J, (K ⟶ E i) →+
      (((∐ fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) : AddCommGrpCat.{v}) : Type v) :=
    fun i => (Limits.Sigma.ι (fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) i).hom
  let β : (DirectSum J fun i => (K ⟶ E i)) →+
      (((∐ fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) : AddCommGrpCat.{v}) : Type v) :=
    DirectSum.toAddMonoid ι₀
  have hβ : ∀ (i : J) (g : K ⟶ E i), β (DirectSum.of _ i g) = ι₀ i g :=
    fun i g => DirectSum.toAddMonoid_of ι₀ i g
  have hsc : ∀ (i : J) (g : K ⟶ E i),
      (sigmaComparison (preadditiveCoyoneda.obj (op K)) E).hom (ι₀ i g)
        = g ≫ Limits.Sigma.ι E i := by
    intro i g
    change ((Limits.Sigma.ι (fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) i) ≫
      sigmaComparison (preadditiveCoyoneda.obj (op K)) E).hom g = _
    rw [ι_comp_sigmaComparison]
    rfl
  have key : ∀ x, (sigmaComparison (preadditiveCoyoneda.obj (op K)) E).hom (β x) = α x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero =>
      simp only [map_zero]
      rfl
    | of i g => rw [hβ, hsc, hα]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      rfl
  -- The coproduct of the groups `Hom(K, E i)` is generated by the images of its coprojections.
  have hβsurj : Function.Surjective β := by
    intro z
    exact mem_of_isColimit (colimit.isColimit (Discrete.functor
      (fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)))) β.range
      (fun j x => ⟨DirectSum.of _ j.as x, hβ j.as x⟩) z
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab => ?_, fun f => ?_⟩
  · obtain ⟨a', rfl⟩ := hβsurj a
    obtain ⟨b', rfl⟩ := hβsurj b
    rw [key, key] at hab
    rw [hbij.1 hab]
  · obtain ⟨a', ha'⟩ := hbij.2 f
    exact ⟨β a', (key a').trans ha'⟩

/-- **Compactness as preservation of direct sums.** For a compact object `K` of a preadditive
category with direct sums indexed by `Type v`, the additive corepresentable functor
`Hom(K, -) = preadditiveCoyoneda.obj (op K)` preserves coproducts indexed by any `J : Type v`.
This is the form of the hypothesis of [Stacks, Tag 094A]. -/
lemma preservesColimitsOfShape_discrete_of_isCompactObject (K : D)
    [IsCompactObject.{v} K] (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op K)) := by
  constructor
  intro F
  have : IsIso (sigmaComparison (preadditiveCoyoneda.obj (op K)) (F.obj ∘ Discrete.mk)) :=
    isIso_sigmaComparison_preadditiveCoyoneda K _
  have : PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk))
      (preadditiveCoyoneda.obj (op K)) := PreservesCoproduct.of_iso_comparison _ _
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

/-- The countable case of `preservesColimitsOfShape_discrete_of_isCompactObject`: compactness is
tested against `Type v`-indexed families, and `Discrete (ULift.{v} ℕ) ≌ Discrete ℕ`. -/
private lemma preservesColimitsOfShape_discrete_nat_of_isCompactObject (K : D)
    [IsCompactObject.{v} K] :
    PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K)) := by
  have := preservesColimitsOfShape_discrete_of_isCompactObject K (ULift.{v} ℕ)
  exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

end Compact

section Main

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{v} D]

omit [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{v} D] in
/-- A constant family with nonempty index type has the same objects as its single member. -/
private lemma ofObj_const_eq_singleton {ι : Type*} [Nonempty ι] (E : D) :
    ObjectProperty.ofObj (fun _ : ι => E) = ObjectProperty.singleton E := by
  ext Y
  rw [ObjectProperty.ofObj_iff, ObjectProperty.singleton_iff]
  exact ⟨fun ⟨_, hi⟩ => hi, fun hE => ⟨Classical.arbitrary ι, hE⟩⟩

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{v} D] in
/-- A singleton family indexed by `PUnit` generates exactly when its single member does. -/
private lemma isWeakTriangulatedGenerator_ofObj_punit (E : D) :
    (ObjectProperty.ofObj (fun _ : PUnit.{v + 1} => E)).IsWeakTriangulatedGenerator ↔
      (ObjectProperty.singleton E).IsWeakTriangulatedGenerator := by
  rw [ofObj_const_eq_singleton]

omit [HasZeroObject D] [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{v} D] in
/-- **Right orthogonality to the shifts, read on either side** ([Stacks, Tag 09SK], the formal
half). All maps from the shifts of `X` to `K` vanish if and only if all maps from `X` to the
shifts of `K` do. -/
private lemma rightOrthogonal_shiftClosure_singleton_iff (X K : D) :
    ((ObjectProperty.singleton X).shiftClosure ℤ).rightOrthogonal K ↔
      ((ObjectProperty.singleton K).shiftClosure ℤ).leftOrthogonal X := by
  have reflects : ∀ (m : ℤ) {A B : D} (g : A ⟶ B), (shiftFunctor D m).map g = 0 → g = 0 :=
    fun m _ _ g hg => (shiftFunctor D m).map_injective (by rw [hg, Functor.map_zero])
  have key : ∀ (m : ℤ) (A B : D) (g : A ⟶ B⟦m⟧), g = 0 ↔
      (shiftFunctor D (-m)).map g
        ≫ ((shiftFunctorCompIsoId D m (-m) (by simp)).app B).hom = 0 := by
    intro m A B g
    refine ⟨fun hg => by rw [hg, Functor.map_zero, zero_comp], fun hg => reflects (-m) g ?_⟩
    rw [← cancel_mono ((shiftFunctorCompIsoId D m (-m) (by simp)).app B).hom, hg, zero_comp]
  have key' : ∀ (m : ℤ) (A B : D) (g : A⟦m⟧ ⟶ B), g = 0 ↔
      ((shiftFunctorCompIsoId D m (-m) (by simp)).app A).inv
        ≫ (shiftFunctor D (-m)).map g = 0 := by
    intro m A B g
    refine ⟨fun hg => by rw [hg, Functor.map_zero, comp_zero], fun hg => reflects (-m) g ?_⟩
    rw [← cancel_epi ((shiftFunctorCompIsoId D m (-m) (by simp)).app A).inv, hg, comp_zero]
  constructor
  · intro hK Y f hY
    obtain ⟨K', m, e, hK'⟩ := hY
    rw [ObjectProperty.singleton_iff] at hK'
    subst hK'
    have hg : f ≫ e.hom = 0 := by
      rw [key m]
      exact hK _ ⟨X, -m, Iso.refl _, by simp⟩
    rw [show f = (f ≫ e.hom) ≫ e.inv by simp, hg, zero_comp]
  · intro hX Z f hZ
    obtain ⟨X', m, e, hX'⟩ := hZ
    rw [ObjectProperty.singleton_iff] at hX'
    subst hX'
    have hg : e.inv ≫ f = 0 := by
      rw [key' m]
      exact hX _ ⟨K, -m, Iso.refl _, by simp⟩
    rw [show f = e.hom ≫ e.inv ≫ f by simp, hg, comp_zero]

omit [HasCoproducts D] in
/-- The triangulated envelope of a nonempty family contains the finite direct sums
`∐_{i ∈ s} E i` of its members: a strictly full triangulated subcategory is closed under finite
direct sums, and the envelope is one as soon as the family is nonempty — which is what makes the
zero object, the empty direct sum, belong to it. -/
private lemma triangEnvelope_sigma_of_nonempty {ι : Type v} [Nonempty ι] (E : ι → D)
    (s : Finset ι) : (ObjectProperty.ofObj E).triangEnvelope (∐ fun i : s ↦ E i) := by
  exact Pretriangulated.prop_coproduct_of_isTriangulated (ObjectProperty.ofObj E).triangEnvelope
    fun i : s ↦ le_triangEnvelope _ _ (ObjectProperty.ofObj_apply E i.1)

/-- **[Stacks, Tag 09SR], (2) ⇒ (1), for a family of generators.** If a nonempty family
`E : ι → D` of compact objects, indexed by the universe of the direct sums, generates `D`, then
its triangulated envelope is exactly the subcategory of compact objects: the inclusion
`⟨E⟩ ≤ D_c` holds because `D_c` is a triangulated subcategory closed under retracts
([Stacks, Tag 09QH]), and a compact `X` lies in `⟨E⟩` because, writing `X = hocolim Xₙ` as in
[Stacks, Tag 09SN], the identity of `X` factors through some `Xₙ` ([Stacks, Tag 094A], through
`preservesColimitsOfShape_discrete_nat_of_isCompactObject`), so `X` is a direct summand of an
object of `⟨E⟩` by [Stacks, Tag 09SP].

The hypothesis `Nonempty ι` is not removable: for `ι` empty and `D` a category all of whose
objects are zero, `ObjectProperty.ofObj E` is `⊥`, whose envelope is again `⊥`, while every
object of `D` is compact. -/
theorem triangEnvelope_eq_isCompactObject_of_isWeakTriangulatedGenerator_ofObj
    {ι : Type v} [Nonempty ι] (E : ι → D) [∀ i, IsCompactObject.{v} (E i)]
    (h : (ObjectProperty.ofObj E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.ofObj E).triangEnvelope = IsCompactObject.{v, _, _} (C := D) := by
  obtain ⟨hiso, htri⟩ :=
    Pretriangulated.compactObject_isClosedUnderIsomorphisms_and_isTriangulated (D := D)
  have : ObjectProperty.IsStableUnderRetracts (IsCompactObject.{v, _, _} (C := D)) := by
    constructor
    intro A B r hB
    exact isCompactObject_of_retract hB r.i r.r r.retract
  refine le_antisymm ?_ (fun X hX => ?_)
  · rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.ofObj_le_iff]
    exact fun i => inferInstance
  -- `X` is compact: write it as a derived colimit of cells over the `E i` (Tag 09SN).
  have : IsCompactObject.{v} X := hX
  obtain ⟨F, hcolim, hF0, hFstep⟩ := exists_isHomotopyColimit_of_compactlyGenerated E h X
  obtain ⟨p, q, hT⟩ := hcolim
  -- The identity of `X` comes from one of the stages (Tag 094A).
  have := preservesColimitsOfShape_discrete_nat_of_isCompactObject X
  obtain ⟨e, he⟩ := exists_iso_colimit_preadditiveCoyoneda_of_isHomotopyColimit F X p q hT
  obtain ⟨n, a, ha⟩ := AddCommGrpCat.exists_ι_apply_eq
    (colimit.isColimit (F ⋙ preadditiveCoyoneda.obj (op X)))
    (ConcreteCategory.hom e.inv (𝟙 X))
  have hfac : a ≫ (Limits.Sigma.ι F.obj n ≫ p) = 𝟙 X := by
    have hι : ConcreteCategory.hom
        (colimit.ι (F ⋙ preadditiveCoyoneda.obj (op X)) n) a = ConcreteCategory.hom e.inv (𝟙 X) :=
      ha
    have key : ConcreteCategory.hom e.hom
        (ConcreteCategory.hom (colimit.ι (F ⋙ preadditiveCoyoneda.obj (op X)) n) a) = 𝟙 X :=
      hι ▸ Iso.inv_hom_id_apply e (𝟙 X)
    have h1 := ConcreteCategory.congr_hom (he n) a
    simp only [ConcreteCategory.comp_apply] at h1
    exact h1.symm.trans key
  -- The map `a : X ⟶ Xₙ` factors through the envelope of a finite subsum (Tag 09SP).
  obtain ⟨s, Z, hZ, α, b, hab⟩ :=
    exists_fac_triangEnvelope_of_isCompactObject E hF0
      (fun m => by
        obtain ⟨Y, hY, f, g, hTm⟩ := hFstep m
        exact ⟨Y, hY, f, F.map (homOfLE (Nat.le_succ m)), g, hTm⟩) a
  -- Hence `X` is a retract of `Z`, an object of `⟨E⟩`.
  have hZE : (ObjectProperty.ofObj E).triangEnvelope Z := by
    have hle : (ObjectProperty.singleton (∐ fun i : s => E i)).triangEnvelope
        ≤ (ObjectProperty.ofObj E).triangEnvelope := by
      rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
      exact triangEnvelope_sigma_of_nonempty E s
    exact hle Z hZ
  refine ObjectProperty.prop_of_retract _ ⟨α, b ≫ Limits.Sigma.ι F.obj n ≫ p, ?_⟩ hZE
  rwa [← Category.assoc α b, hab]

/-- **[Stacks, Tag 09SR], (2) ⇒ (1).** If the compact object `E` is a weak generator of `D`, then
the triangulated envelope of `E` is the subcategory of compact objects. This is the one-element
family case of
`triangEnvelope_eq_isCompactObject_of_isWeakTriangulatedGenerator_ofObj`. -/
private lemma triangEnvelope_eq_isCompactObject_of_isWeakTriangulatedGenerator (E : D)
    [IsCompactObject.{v} E] (h : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton E).triangEnvelope = IsCompactObject.{v, _, _} (C := D) := by
  have hEc : ∀ _ : PUnit.{v + 1}, IsCompactObject.{v} E := fun _ => inferInstance
  have := triangEnvelope_eq_isCompactObject_of_isWeakTriangulatedGenerator_ofObj
    (fun _ : PUnit.{v + 1} => E) ((isWeakTriangulatedGenerator_ofObj_punit E).mpr h)
  rwa [ofObj_const_eq_singleton] at this

omit [IsTriangulated D] [HasCoproducts.{v} D] in
/-- **[Stacks, Tag 09SR], (1) ⇒ (2).** If the envelope of `E` is the subcategory of compact
objects and `D` is compactly generated, then `E` is a weak generator: an object right orthogonal
to the shifts of `E` is left orthogonal to the shifts of every object of `⟨E⟩`
([Stacks, Tag 09SK]), in particular of a compact generating family, hence zero. -/
private lemma isWeakTriangulatedGenerator_of_triangEnvelope_eq_isCompactObject (E : D)
    [IsCompactObject.{v} E]
    (h : (ObjectProperty.singleton E).triangEnvelope = IsCompactObject.{v, _, _} (C := D))
    (hgen : IsCompactlyGenerated.{v} D) :
    (ObjectProperty.singleton E).IsWeakTriangulatedGenerator := by
  obtain ⟨ι, E', hE'c, hE'gen⟩ := hgen
  intro K hK
  have : (((ObjectProperty.singleton K).shiftClosure ℤ).leftOrthogonal).IsStableUnderRetracts := by
    constructor
    intro A B r hB Y f hY
    rw [show f = r.i ≫ (r.r ≫ f) by rw [← Category.assoc, r.retract, Category.id_comp],
      hB (r.r ≫ f) hY, comp_zero]
  have hle : (ObjectProperty.singleton E).triangEnvelope
      ≤ ((ObjectProperty.singleton K).shiftClosure ℤ).leftOrthogonal := by
    rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
    exact (rightOrthogonal_shiftClosure_singleton_iff E K).mp hK
  refine hE'gen K fun Z f hZ => ?_
  obtain ⟨A, m, ε, hA⟩ := hZ
  obtain ⟨i, rfl⟩ := (ObjectProperty.ofObj_iff E' A).mp hA
  have hQ : ((ObjectProperty.singleton K).shiftClosure ℤ).leftOrthogonal (E' i) :=
    hle _ (h.symm ▸ hE'c i)
  exact (rightOrthogonal_shiftClosure_singleton_iff (E' i) K).mpr hQ f ⟨E' i, m, ε, by simp⟩

/-- **Stacks 09SR**. Let `D` be a triangulated category with direct sums and let `E` be a compact
object of `D`. Then `E` is a weak generator of `D` if and only if `E` is a classical generator of
the subcategory `D_c` of compact objects, i.e. the triangulated envelope `⟨E⟩` is exactly the
property of being a compact object, and `D` is compactly generated. -/
@[stacks 09SR]
public theorem
    isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
    (E : D) [IsCompactObject.{v} E] :
    (ObjectProperty.singleton E).IsWeakTriangulatedGenerator ↔
      (ObjectProperty.singleton E).triangEnvelope = IsCompactObject.{v, _, _} (C := D) ∧
        IsCompactlyGenerated.{v} D :=
  ⟨fun h => ⟨triangEnvelope_eq_isCompactObject_of_isWeakTriangulatedGenerator E h,
      ⟨PUnit.{v + 1}, fun _ => E, fun _ => inferInstance,
        (isWeakTriangulatedGenerator_ofObj_punit E).mpr h⟩⟩,
    fun h => isWeakTriangulatedGenerator_of_triangEnvelope_eq_isCompactObject E h.1 h.2⟩

end Main

end CategoryTheory.ObjectProperty

end
