module

public import StacksFrontier.AlgebraicGeometry.Varieties.Kunneth
public import StacksFrontier.Homology.TensorComplex.CohomologyProduct
public import StacksFrontier.Homology.Tor.Products

/-!
# The Künneth formula in degree zero, in canonical form

Tensoring cocycles gives, for any two objects `K` and `L` of the derived category of modules over
a commutative ring, a canonical map

`Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)`

— the cohomology product of [Stacks, Tag 068H], which is
`RingTheory.TorProducts.cohomologyTensorProduct`. This file proves that **over a field, in degree
`i = j = 0`, that map is an isomorphism as soon as the cohomology of `K` and of `L` vanishes in
negative degrees**. That is the `q = 0` case of the Künneth formula for `⊗^𝐋`: the sum
`⨁_{p + q = 0} Hᵖ(K) ⊗ H^q(L)` of the general formula collapses to the single summand
`H⁰(K) ⊗ H⁰(L)` precisely under that vanishing, and what is proved here is that the surviving
summand maps isomorphically by the canonical product.

The route is the classical one. Over a field every complex of vector spaces is K-flat
(`CochainComplex.Kunneth.kFlat_of_field`), so `K ⊗^𝐋 L` is computed by the ordinary total tensor
complex of any two representatives, and every complex receives a quasi-isomorphism from the
complex of its own cohomology modules with zero differentials. Naturality of the cohomology
product in both variables reduces the claim to that case, where the degree-zero term of the
tensor complex is the single summand of bidegree `(0, 0)` because every other summand has a
vanishing factor.

## Main results

* `CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero`: over a field, the cohomology
  product of [Stacks, Tag 068H] in degree zero is an isomorphism when the cohomology of both
  arguments vanishes in negative degrees.
* `CochainComplex.Kunneth.cohomologyTensorProductIsoZero`: the same, packaged as an isomorphism
  `H⁰(K) ⊗_k H⁰(L) ≅ H⁰(K ⊗^𝐋_k L)`.
* `CochainComplex.Kunneth.isIso_tensorHomology_zero`: the statement at the level of complexes,
  for the product `CochainComplex.tensorHomology` on the cohomology of an ordinary total tensor
  complex.
* `CochainComplex.Kunneth.quasiIso_tensorHom`: over a field the total tensor product of two
  quasi-isomorphisms is a quasi-isomorphism.
* `CochainComplex.Kunneth.isIso_ιTensorObj_zero`: for complexes vanishing in negative degrees
  the inclusion of the summand of bidegree `(0, 0)` into degree zero of the tensor product is an
  isomorphism.

## Implementation notes

*Why a canonical statement is the point.* An isomorphism of the two sides already exists in this
library, `CochainComplex.Kunneth.nonempty_derivedTensorHomologyIso`, but only as
`Nonempty (… ≅ …)`: it is built by choosing a basis of each cohomology module, and no
compatibility with the cohomology product — or with anything else — is asserted. A `Nonempty`
isomorphism of two groups says nothing about which elements of the target are hit by a given map
into it, so it cannot be used to prove that a specified family of elements spans. The statements
here are about `RingTheory.TorProducts.cohomologyTensorProduct` and
`CochainComplex.tensorHomology`, the maps given by tensoring cocycles, so they do carry that
information.

*Why the field.* The degree-zero statement is false over a general commutative ring: for
`R = ℤ`, `K = (ℤ --2--> ℤ)` in degrees `0` and `1` and `L = ℤ/2` in degree zero, the cohomology
of `K` and of `L` vanishes in negative degrees, `H⁰(K) = 0`, and yet
`H⁰(K ⊗^𝐋 L) = ℤ/2` is nonzero. The vanishing of the higher `Tor` of the base is what makes the
`p ≠ 0` summands of the general formula disappear, and it is a hypothesis of
[Stacks, Tag 0G08], where the base is a field.

*What this is not.* This is not [Stacks, Tag 0FXZ], the Künneth formula for Ext on a fibre
product of schemes, and it carries no tag. It is the algebraic ingredient of that tag's `q = 0`
case: the global Künneth conclusion of [Stacks, Tag 0FLQ] over an affine base identifies
`RΓ(X ×_A Y, K ⊠ M)` with `RΓ(X, K) ⊗^𝐋_A RΓ(Y, M)`, and passing from that identification of
objects of `D(A)` to the degree-zero statement about Hom groups is exactly an application of the
theorems below. The implementation notes of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Kunneth` record which further
inputs that passage still needs.

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CochainComplex.Kunneth

variable {R : Type u} [CommRing R]

/-- Tensoring on the right by `X` is tensoring on the left by `X`, through the braiding. -/
private def flipTensorIsoTensorLeft (X : ModuleCat.{u} R) :
    (curriedTensor (ModuleCat.{u} R)).flip.obj X ≅
      (curriedTensor (ModuleCat.{u} R)).obj X :=
  NatIso.ofComponents (fun Y => β_ Y X) (fun f => by simp)

/-- Tensoring on the right by a fixed module preserves finite colimits. -/
local instance preservesFiniteColimits_flipTensor (X : ModuleCat.{u} R) :
    PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).flip.obj X) :=
  preservesFiniteColimits_of_natIso (flipTensorIsoTensorLeft X).symm

/-- A tensor product whose left factor is zero is zero. -/
theorem isZero_tensor_left {A B : ModuleCat.{u} R} (h : IsZero A) : IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, h.eq_of_src (𝟙 A) 0,
    MonoidalPreadditive.zero_tensor]

/-- A tensor product whose right factor is zero is zero. -/
theorem isZero_tensor_right {A B : ModuleCat.{u} R} (h : IsZero B) : IsZero (A ⊗ B) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, h.eq_of_src (𝟙 B) 0,
    MonoidalPreadditive.tensor_zero]

/-! ### Complexes with zero differentials

Tensor products of complexes with zero differentials have zero differentials, over any
commutative ring. Over a field, every complex receives a quasi-isomorphism from a complex with
zero differentials whose terms are its cohomology objects. -/

/-- The tensor product of two complexes with zero differentials has zero differentials. -/
private lemma tensorComplex_zeroDifferentials {k : Type u} [CommRing k]
    (C D : CochainComplex (ModuleCat.{u} k) ℤ)
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) :
    ∀ i j, (HomologicalComplex.tensorObj C D).d i j = 0 := by
  intro i j
  change (HomologicalComplex.mapBifunctor C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).d i j = 0
  rw [HomologicalComplex.mapBifunctor.d_eq]
  have h₁ : HomologicalComplex.mapBifunctor.D₁ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i j = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b _
    rw [HomologicalComplex.mapBifunctor.ι_D₁]
    by_cases ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (a + 1, b) = j
    · rw [HomologicalComplex.mapBifunctor.d₁_eq C D _ _
        (ComplexShape.up_mk a (a + 1) (by simp)) b j ht]
      simp [hC]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero' C D _ _
        (ComplexShape.up_mk a (a + 1) (by simp)) b j ht]
      simp
  have h₂ : HomologicalComplex.mapBifunctor.D₂ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i j = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b _
    rw [HomologicalComplex.mapBifunctor.ι_D₂]
    by_cases ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (a, b + 1) = j
    · rw [HomologicalComplex.mapBifunctor.d₂_eq C D _ _ a
        (ComplexShape.up_mk b (b + 1) (by simp)) j ht]
      simp [hD]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' C D _ _ a
        (ComplexShape.up_mk b (b + 1) (by simp)) j ht]
      simp
  rw [h₁, h₂, zero_add]

/-- Over a field a complex `C` receives a quasi-isomorphism from a complex with zero differentials
whose degree-`i` term is the cohomology object `Hⁱ(C)` itself: a section of each projection
`Zⁱ(C) → Hⁱ(C)`, which exists because `Hⁱ(C)` is free, composed with the inclusion of cycles. -/
private lemma exists_zeroDifferential_quasiIso_X_eq_homology {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    ∃ (E : CochainComplex (ModuleCat.{u} k) ℤ) (f : E ⟶ C),
      (∀ i j, E.d i j = 0) ∧ (∀ i, E.X i = C.homology i) ∧ QuasiIso f := by
  classical
  have hproj : ∀ i : ℤ, Projective (C.homology i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis k (C.homology i))
  let E : CochainComplex (ModuleCat.{u} k) ℤ :=
    { X := fun i => C.homology i
      d := fun _ _ => 0
      shape := by intros; rfl
      d_comp_d' := by intros; simp }
  let s (i : ℤ) := Projective.factorThru (𝟙 (C.homology i)) (C.homologyπ i)
  have hs (i : ℤ) : s i ≫ C.homologyπ i = 𝟙 _ := Projective.factorThru_comp _ _
  let f : E ⟶ C :=
    { f := fun i => s i ≫ C.iCycles i
      comm' := by intros; dsimp [E]; simp }
  refine ⟨E, f, fun _ _ => rfl, fun _ => rfl, ?_⟩
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hi : IsIso (E.iCycles i) := E.isIso_iCycles _ _ rfl rfl
  have hp : IsIso (E.homologyπ i) := E.isIso_homologyπ _ _ rfl rfl
  have hc : HomologicalComplex.cyclesMap f i = E.iCycles i ≫ s i := by
    apply (cancel_mono (C.iCycles i)).1
    simp [HomologicalComplex.cyclesMap_i, f]
  have he : E.homologyπ i ≫ HomologicalComplex.homologyMap f i = E.iCycles i := by
    rw [HomologicalComplex.homologyπ_naturality, hc, Category.assoc, hs, Category.comp_id]
  have : IsIso (E.homologyπ i ≫ HomologicalComplex.homologyMap f i) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (E.homologyπ i) _

section ZeroDegree

variable (E G : CochainComplex (ModuleCat.{u} R) ℤ)
  (hE : ∀ i : ℤ, i < 0 → IsZero (E.X i)) (hG : ∀ i : ℤ, i < 0 → IsZero (G.X i))

include hE hG

/-- Every summand of `(E ⊗ G)₀` other than the one of bidegree `(0, 0)` vanishes, when `E` and
`G` vanish in negative degrees. -/
theorem isZero_tensor_of_ne_zero (p q : ℤ) (hpq : p + q = 0) (hp : p ≠ 0) :
    IsZero (E.X p ⊗ G.X q) := by
  rcases lt_or_gt_of_ne hp with h | h
  · exact isZero_tensor_left (hE p h)
  · exact isZero_tensor_right (hG q (by omega))

/-- **The inclusion of the `(0, 0)` summand into degree zero of a tensor product of complexes
vanishing in negative degrees is an isomorphism.** -/
theorem isIso_ιTensorObj_zero :
    IsIso (HomologicalComplex.ιTensorObj E G 0 0 0 (by omega)) := by
  refine ⟨HomologicalComplex.mapBifunctorDesc (fun p q h =>
    if hp : p = 0 then eqToHom (by
        have h' : p + q = 0 := h
        rw [hp, show q = 0 by omega]
        rfl) else 0), ?_, ?_⟩
  · simp only [HomologicalComplex.ιTensorObj, HomologicalComplex.ι_mapBifunctorDesc]
    simp
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    have h' : p + q = 0 := h
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, Category.comp_id]
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 0 := by omega
      simp
    · rw [dite_eq_right hp, Limits.zero_comp,
        (isZero_tensor_of_ne_zero E G hE hG p q h' hp).eq_of_src
          (HomologicalComplex.ιMapBifunctor E G (curriedTensor (ModuleCat.{u} R))
            (ComplexShape.up ℤ) p q 0 h) 0]

variable (hdE : ∀ i j, E.d i j = 0) (hdG : ∀ i j, G.d i j = 0)

include hdE hdG

/-- **The degree-zero Künneth map of two complexes with zero differentials vanishing in negative
degrees is an isomorphism.** -/
theorem isIso_tensorHomology_zero_of_zeroDifferential :
    IsIso (CochainComplex.tensorHomology E G 0 0) := by
  have hdEG := tensorComplex_zeroDifferentials E G hdE hdG
  have h : ∀ (C : CochainComplex (ModuleCat.{u} R) ℤ) (_ : ∀ i j, C.d i j = 0) (i : ℤ),
      IsIso (C.iCycles i) ∧ IsIso (C.homologyπ i) := fun C hd i =>
    ⟨C.isIso_iCycles i (i + 1) (by simp) (hd _ _),
      C.isIso_homologyπ (i - 1) i (by simp) (hd _ _)⟩
  have hiE := (h E hdE 0).1
  have hiG := (h G hdG 0).1
  have hpE := (h E hdE 0).2
  have hpG := (h G hdG 0).2
  have hiEG := (h _ hdEG (0 + 0)).1
  have hpEG := (h _ hdEG (0 + 0)).2
  have hι : IsIso (HomologicalComplex.ιTensorObj E G 0 0 (0 + 0) rfl) :=
    isIso_ιTensorObj_zero E G hE hG
  have hz : IsIso (CochainComplex.tensorCycles E G 0 0) := by
    have : IsIso (CochainComplex.tensorCycles E G 0 0 ≫
        (HomologicalComplex.tensorObj E G).iCycles (0 + 0)) := by
      rw [CochainComplex.tensorCycles_i]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((HomologicalComplex.tensorObj E G).iCycles (0 + 0))
  have key : IsIso ((E.homologyπ 0 ⊗ₘ G.homologyπ 0) ≫
      CochainComplex.tensorHomology E G 0 0) := by
    rw [CochainComplex.homologyπ_tensorHomology]
    infer_instance
  exact IsIso.of_isIso_comp_left (E.homologyπ 0 ⊗ₘ G.homologyπ 0) _

end ZeroDegree

section Field

variable {k : Type u} [Field k]

/-- **Over a field the total tensor product of two quasi-isomorphisms is a
quasi-isomorphism.** Every complex of vector spaces is K-flat, so the derived tensor product is
computed by the ordinary one; the statement is the naturality of that comparison read through
the invertibility in the derived category of the two given maps. -/
theorem quasiIso_tensorHom {P P' Q Q' : CochainComplex (ModuleCat.{u} k) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') [QuasiIso f] [QuasiIso g] :
    QuasiIso (HomologicalComplex.tensorHom f g) := by
  have hf : IsIso (DerivedCategory.Q.map f) := inferInstance
  have hg : IsIso (DerivedCategory.Q.map g) := inferInstance
  set T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct k
  have hcomp := T.comparison_naturality f g (kFlat_of_field P) (kFlat_of_field P')
    (kFlat_of_field Q) (kFlat_of_field Q')
  have hlhs : IsIso ((T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj Q) ≫
      (T.tensor.obj (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map g) ≫
      (T.comparison P' Q' (kFlat_of_field P') (kFlat_of_field Q')).hom) := by
    have : IsIso (T.tensor.map (DerivedCategory.Q.map f)) := Functor.map_isIso _ _
    infer_instance
  rw [hcomp] at hlhs
  have := IsIso.of_isIso_comp_left
    (T.comparison P Q (kFlat_of_field P) (kFlat_of_field Q)).hom
    (DerivedCategory.Q.map (HomologicalComplex.tensorHom f g))
  rwa [DerivedCategory.isIso_Q_map_iff_quasiIso] at this

/-- **The degree-zero Künneth map over a field.** For two complexes of vector spaces whose
cohomology vanishes in negative degrees, the canonical product
`H⁰(P) ⊗_k H⁰(Q) ⟶ H⁰(P ⊗ Q)` is an isomorphism. -/
theorem isIso_tensorHomology_zero (P Q : CochainComplex (ModuleCat.{u} k) ℤ)
    (hP : ∀ i : ℤ, i < 0 → IsZero (P.homology i))
    (hQ : ∀ i : ℤ, i < 0 → IsZero (Q.homology i)) :
    IsIso (CochainComplex.tensorHomology P Q 0 0) := by
  obtain ⟨E, f, hdE, hXE, hf⟩ := exists_zeroDifferential_quasiIso_X_eq_homology P
  obtain ⟨G, g, hdG, hXG, hg⟩ := exists_zeroDifferential_quasiIso_X_eq_homology Q
  have hEzero : ∀ i : ℤ, i < 0 → IsZero (E.X i) := fun i hi => (hXE i).symm ▸ hP i hi
  have hGzero : ∀ i : ℤ, i < 0 → IsZero (G.X i) := fun i hi => (hXG i).symm ▸ hQ i hi
  have hEG : IsIso (CochainComplex.tensorHomology E G 0 0) :=
    isIso_tensorHomology_zero_of_zeroDifferential E G hEzero hGzero hdE hdG
  have _ : QuasiIso (HomologicalComplex.tensorHom f g) := quasiIso_tensorHom f g
  have hnat := CochainComplex.tensorHomology_naturality E G f g 0 0
  have hrhs : IsIso ((HomologicalComplex.homologyMap f 0 ⊗ₘ
      HomologicalComplex.homologyMap g 0) ≫ CochainComplex.tensorHomology P Q 0 0) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap f 0 ⊗ₘ
    HomologicalComplex.homologyMap g 0) _

/-- A map sandwiched between isomorphisms, whose composite with them is an isomorphism, is an
isomorphism. -/
private theorem isIso_of_comp_eq {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    {a : X₀ ⟶ X₁} {a' : X₁ ⟶ X₂} {m : X₂ ⟶ X₃} {b : X₃ ⟶ X₄} {b' : X₄ ⟶ X₅}
    {t : X₀ ⟶ X₅} (h : a ≫ a' ≫ m ≫ b ≫ b' = t)
    (ha : IsIso a) (ha' : IsIso a') (hb : IsIso b) (hb' : IsIso b') (ht : IsIso t) :
    IsIso m := by
  have _ : IsIso (a ≫ a' ≫ m ≫ b ≫ b') := by rw [h]; exact ht
  have _ := IsIso.of_isIso_comp_left a (a' ≫ m ≫ b ≫ b')
  have _ := IsIso.of_isIso_comp_left a' (m ≫ b ≫ b')
  exact IsIso.of_isIso_comp_right m (b ≫ b')

/-- **The `q = 0` case of the Künneth formula for the derived tensor product over a field.** For
two objects of `D(k)` whose cohomology vanishes in negative degrees, the canonical cohomology
product of [Stacks, Tag 068H] in degree zero,

`H⁰(K) ⊗_k H⁰(L) ⟶ H⁰(K ⊗^𝐋_k L)`,

is an isomorphism. This is the degree-zero splitting of the derived tensor product in canonical
form: the isomorphism is the product induced by tensoring cocycles, not a chosen bijection. -/
theorem isIso_cohomologyTensorProduct_map_zero
    (K L : CochainComplex.DerivedTensor.DObj k)
    (hK : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj K))
    (hL : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj L)) :
    IsIso (RingTheory.TorProducts.cohomologyTensorProduct K L 0 0).map := by
  obtain ⟨P, Q, hP, hQ, eP, eQ, z, hz, heq⟩ :=
    (RingTheory.TorProducts.cohomologyTensorProduct K L 0 0).maps_cocycles
  have hzero : ∀ {X : CochainComplex.DerivedTensor.DObj k} {C : CochainComplex (ModuleCat.{u} k) ℤ}
      (e : DerivedCategory.Q.obj C ≅ X),
      (∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj X)) →
      ∀ i : ℤ, i < 0 → IsZero (C.homology i) := fun e h i hi =>
    IsZero.of_iso (IsZero.of_iso (h i hi)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).mapIso e))
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) i).app _).symm
  have hth : IsIso (CochainComplex.tensorHomology P Q 0 0) :=
    isIso_tensorHomology_zero P Q (hzero eP hK) (hzero eQ hL)
  have hzeq : z = CochainComplex.tensorCycles P Q 0 0 :=
    (cancel_mono ((HomologicalComplex.tensorObj P Q).iCycles (0 + 0))).1
      (hz.trans (CochainComplex.tensorCycles_i P Q 0 0).symm)
  have hzpi : z ≫ (P ⊗ Q).homologyπ (0 + 0) =
      (P.homologyπ 0 ⊗ₘ Q.homologyπ 0) ≫ CochainComplex.tensorHomology P Q 0 0 := by
    rw [hzeq]
    exact (CochainComplex.homologyπ_tensorHomology P Q 0 0).symm
  rw [hzpi] at heq
  have hepi : Epi (P.homologyπ 0 ⊗ₘ Q.homologyπ 0) :=
    RingTheory.TorProducts.epi_tensorHom _ _
  replace heq := (cancel_epi (P.homologyπ 0 ⊗ₘ Q.homologyπ 0)).1 heq
  refine isIso_of_comp_eq heq ?_ ?_ ?_ ?_ hth
  · exact (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) 0).app P).symm ⊗ᵢ
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) 0).app Q).symm).isIso_hom
  · exact (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso eP) ⊗ᵢ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso eQ)).isIso_hom
  · infer_instance
  · infer_instance

/-- **The degree-zero Künneth isomorphism `H⁰(K) ⊗_k H⁰(L) ≅ H⁰(K ⊗^𝐋_k L)` over a field**, for
objects of `D(k)` whose cohomology vanishes in negative degrees. Its underlying map is the
cohomology product of [Stacks, Tag 068H], so the isomorphism is the canonical one and not a
choice. -/
def cohomologyTensorProductIsoZero (K L : CochainComplex.DerivedTensor.DObj k)
    (hK : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj K))
    (hL : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj L)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj K ⊗
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj L ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (0 + 0)).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor k).obj K).obj L) :=
  @asIso _ _ _ _ (RingTheory.TorProducts.cohomologyTensorProduct K L 0 0).map
    (isIso_cohomologyTensorProduct_map_zero K L hK hL)

/-- The forward map of `cohomologyTensorProductIsoZero K L hK hL` is the cohomology product
`RingTheory.TorProducts.cohomologyTensorProduct K L 0 0`. -/
@[simp]
theorem cohomologyTensorProductIsoZero_hom (K L : CochainComplex.DerivedTensor.DObj k)
    (hK : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj K))
    (hL : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj L)) :
    (cohomologyTensorProductIsoZero K L hK hL).hom =
      (RingTheory.TorProducts.cohomologyTensorProduct K L 0 0).map :=
  rfl

end Field

end CochainComplex.Kunneth

end
