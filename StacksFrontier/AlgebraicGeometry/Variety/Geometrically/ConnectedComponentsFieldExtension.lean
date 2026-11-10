module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.SectionsIso.Descent
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedFiniteSeparable
public import StacksFrontier.RingTheory.TensorProduct.Connected
public import StacksFrontier.RingTheory.WeaklyEtale.MaximalSubalgebra
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank

/-!
# Connected components after an arbitrary extension of the base field

Let `K/k` be an extension of fields, with no finiteness, algebraicity or separability
assumption, and let `X` be a scheme over `k`. The projection `p : X_K → X` carries every
connected component of `X_K` onto a connected component of `X`. This is Gabber's theorem,
which strengthens the finite-extension statement
`AlgebraicGeometry.baseChange_image_connectedComponent_eq_connectedComponent`
(Stacks 07VM), where `p` is open and closed with finite fibres and the result is topological.

For a general extension `p` need not be closed, and the proof is arithmetic instead. One
reduces to `X` connected and reduced by replacing `X` by the reduced induced subscheme on the
connected component of the image point. Writing `A = Γ(X, ⊤)`, the greatest weakly étale
`k`-subalgebra `L ⊆ A` (Stacks 0CKS) is a field, separable algebraic over `k` (Stacks 0CKR),
because `A` has no nontrivial idempotents. The structure morphism factors through `Spec L`, and
for every finite separable `L'/L` the ring `Γ(X_{L'}, ⊤) = A ⊗[L] L'` (Stacks 0CKW) again has
greatest weakly étale `L'`-subalgebra `L'` (Stacks 0CKU), hence no nontrivial idempotents; so
`X` is geometrically connected over `L` (Stacks 0389). Finally the fibre of `X_K → (Spec L)_K`
through the given point is connected, contains it, and surjects onto `X`.

## Main results

* `AlgebraicGeometry.image_connectedComponent_baseChange` (Stacks 04PZ): for an arbitrary
  extension `K/k` and a scheme `X` over `k`, the projection `X_K → X` carries each connected
  component of `X_K` onto a connected component of `X`.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`, and `X_K` is the
pullback of `f` along `Spec K ⟶ Spec k`, with `p` the first projection, exactly as in
`...Geometrically.ConnectedComponentsFiniteExtension`. A connected component of `X_K` is the
connected component `connectedComponent t` of one of its points `t`, so the assertion is an
equality of subsets of the underlying space of `X`.

The reduction step uses the vanishing-ideal closed subscheme structure on the connected
component (`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`), which is reduced, and the
identification of the base change of that closed subscheme with the part of `X_K` lying over it.

## References

* [Stacks Project, Tag 04PZ](https://stacks.math.columbia.edu/tag/04PZ)
* Ofer Gabber, email dated June 4, 2016.
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

universe u

/-- If `S` has only trivial idempotents, so does any ring `R` with an injective map to `S`. -/
private lemma idempotent_eq_zero_or_one_of_injective {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Injective φ)
    (h : ∀ s : S, IsIdempotentElem s → s = 0 ∨ s = 1) {e : R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 :=
  (h _ (he.map φ)).imp (fun h0 => hφ (by simpa using h0)) fun h1 => hφ (by simpa using h1)

/-- The ring of sections over an open set containing a point is nontrivial. -/
private lemma nontrivial_sections_of_mem {X : Scheme.{u}} (U : X.Opens) {x : X} (hx : x ∈ U) :
    Nontrivial Γ(X, U) := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  exact Scheme.component_nontrivial X U

/-- On a connected reduced scheme, every idempotent global section is `0` or `1`. -/
private lemma idempotent_eq_zero_or_one_of_connected
    {X : Scheme.{u}} [ConnectedSpace X] [IsReduced X] (e : Γ(X, ⊤))
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hspec : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum Γ(X, ⊤))) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  have hclopen : IsClopen (X.basicOpen e : Set X) := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact hspec.preimage X.toSpecΓ.continuous
  rcases (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace X)).2
      (X.basicOpen e : Set X) hclopen with hempty | hfull
  · left
    have hbot : X.basicOpen e = ⊥ := by
      apply SetLike.coe_injective
      simp [hempty]
    exact (basicOpen_eq_bot_iff (X := X) e).mp hbot
  · right
    have hbot : X.basicOpen (1 - e) = ⊥ := by
      have hprod : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
      have htop : X.basicOpen e = ⊤ := SetLike.coe_injective hfull
      have hm := X.basicOpen_mul (e : Γ(X, ⊤)) (1 - e)
      simp [hprod, htop] at hm
      exact hm.symm
    exact (sub_eq_zero.mp ((basicOpen_eq_bot_iff (X := X) (1 - e)).mp hbot)).symm

/-- Let `B` be the greatest weakly étale `k`-subalgebra of `A`, and let `R` be a field
`k`-isomorphic to `B` compatibly with the maps to `A`. Then every weakly étale `R`-subalgebra of
`A` is `⊥`. -/
private lemma maximalWeaklyEtale_bot_of_fieldEquivSubalgebra
    {k R A : Type*} [Field k] [Field R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    (B : Subalgebra k A) [Field B]
    (e : B ≃ₐ[k] R)
    (hB : Algebra.WeaklyEtale k B)
    (hBmax : ∀ D : Subalgebra k A, Algebra.WeaklyEtale k D → D ≤ B)
    (hmap : ∀ b : B, algebraMap R A (e b) = (b : A)) :
    ∀ C : Subalgebra R A, Algebra.WeaklyEtale R C → C ≤ ⊥ := by
  intro C hC
  let : Algebra.WeaklyEtale k B := hB
  let : Algebra.WeaklyEtale k R := Algebra.WeaklyEtale.of_algEquiv k hB e
  let : Algebra k C := RingHom.toAlgebra ((algebraMap R C).comp (algebraMap k R))
  let : IsScalarTower k R C := IsScalarTower.of_algebraMap_eq' (by rfl)
  let : Algebra.WeaklyEtale R C := hC
  have hweakC : Algebra.WeaklyEtale k C := Algebra.WeaklyEtale.trans k R C
  let Ck : Subalgebra k A := C.restrictScalars k
  let eC : C ≃ₐ[k] Ck :=
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl
      commutes' r := Subtype.ext (IsScalarTower.algebraMap_apply k R A r).symm }
  intro x hx
  change (x : A) ∈ Set.range (algebraMap R A)
  exact ⟨e ⟨x, hBmax Ck (Algebra.WeaklyEtale.of_algEquiv k hweakC eC) hx⟩, hmap _⟩

/-- If every weakly étale `R`-subalgebra of the nontrivial `R`-algebra `A` is `⊥`, then for
every field extension `E/R` the only idempotents of `E ⊗[R] A` are `0` and `1`. -/
private lemma idempotent_eq_zero_or_one_after_field_baseChange
    {R E A : Type*} [Field R] [Field E] [CommRing A]
    [Algebra R E] [Algebra R A] [Nontrivial A]
    (hmax : ∀ C : Subalgebra R A, Algebra.WeaklyEtale R C → C ≤ ⊥)
    (e : E ⊗[R] A) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hbot : Algebra.WeaklyEtale R (⊥ : Subalgebra R A) :=
    Algebra.WeaklyEtale.of_algEquiv R inferInstance (Algebra.botEquiv R A).symm
  let baseMax := maximalWeaklyEtaleSubalgebra_baseChange R E A
    (⊥ : Subalgebra R A) hbot hmax
  let f : E ⊗[R] (⊥ : Subalgebra R A) →ₐ[R] E ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id R E) (⊥ : Subalgebra R A).val
  have hf : Function.Injective f := baseMax.1
  let u : (Fin 2 → E) →ₐ[E] E ⊗[R] A :=
    { toFun := fun x ↦ (algebraMap E (E ⊗[R] A) (x 0)) * e +
        (algebraMap E (E ⊗[R] A) (x 1)) * (1 - e)
      map_zero' := by simp
      map_one' := by
        simp only [Pi.one_apply, map_one]
        ring
      map_add' := by intros; simp only [Pi.add_apply, map_add]; ring
      map_mul' := by
        intros
        simp only [Pi.mul_apply, map_mul]
        rw [IsIdempotentElem] at he
        ring_nf
        simp only [pow_two, he]
        ring
      commutes' := by
        intro r
        change algebraMap E (E ⊗[R] A) r * e +
          algebraMap E (E ⊗[R] A) r * (1 - e) = algebraMap E (E ⊗[R] A) r
        ring }
  have hu : Algebra.WeaklyEtale E u.range :=
    (structure_of_weaklyEtale_over_field E (Fin 2 → E) inferInstance).2.2.2.2.1.2 _
      ⟨u.rangeRestrict, u.rangeRestrict_surjective⟩
  have heRange : e ∈ u.range := ⟨![1, 0], by
    change u ![1, 0] = e
    simp [u, ← Algebra.TensorProduct.one_def]
  ⟩
  obtain ⟨y, hy⟩ := baseMax.2.2 u.range hu ⟨e, heRange⟩
  have hyIdem : IsIdempotentElem y := hf (by rw [map_mul, hy, he.eq])
  let tensorEquiv : E ⊗[R] (⊥ : Subalgebra R A) ≃ₐ[E] E :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := E) (A₁ := E))
      (Algebra.botEquiv R A)).trans (Algebra.TensorProduct.rid R E E)
  have hyE : IsIdempotentElem (tensorEquiv y) := hyIdem.map tensorEquiv
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hyE with h | h
  · obtain rfl : y = 0 := tensorEquiv.injective (by simpa using h)
    exact .inl (by simpa [f] using hy.symm)
  · obtain rfl : y = 1 := tensorEquiv.injective (by simpa using h)
    exact .inr (by simpa [f] using hy.symm)

/-- The `k`-algebra structure on `Γ(X, ⊤)` induced by the morphism `f : X ⟶ Spec k`. -/
@[instance_reducible]
private noncomputable def structureMapAlgebra
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Algebra k Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra

/-- For a finite-dimensional `k`-algebra `E`, the morphism `Spec E ⟶ Spec k` is finite locally
free. -/
private lemma finiteLocallyFree_specMap_of_finiteDimensional
    (k E : Type u) [Field k] [CommRing E] [Algebra k E] [FiniteDimensional k E] :
    Stacks.Morphisms.IsFiniteLocallyFree
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
  have hfp : Algebra.FinitePresentation k E :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := k) (S := E)).mp
      (Module.finitePresentation_of_projective k E)
  rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation,
    IsFinite.SpecMap_iff, Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff]
  exact ⟨RingHom.finite_algebraMap.mpr inferInstance,
    RingHom.flat_algebraMap_iff.mpr inferInstance, RingHom.finitePresentation_algebraMap.mpr hfp⟩

/-- If the `k`-algebra structure on `Γ(X, ⊤)` is the one induced by `f : X ⟶ Spec k`, then for
every `k`-subalgebra `B` of `Γ(X, ⊤)` the morphism `f` factors as
`X ⟶ Spec Γ(X, ⊤) ⟶ Spec B ⟶ Spec k`. -/
private lemma structureMap_factors_through_subalgebra
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Algebra k Γ(X, ⊤)]
    (hmap : algebraMap k Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
    (B : Subalgebra k Γ(X, ⊤)) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, ⊤)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k B)) = f := by
  let : Algebra B Γ(X, ⊤) := RingHom.toAlgebra B.val.toRingHom
  let : IsScalarTower k B Γ(X, ⊤) := inferInstance
  apply (cancel_mono (Spec (.of k)).toSpecΓ).mp
  rw [Scheme.toSpecΓ_naturality f]
  simp only [Category.assoc]
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun q : Spec Γ(X, ⊤) ⟶ Spec Γ(Spec (.of k), ⊤) => X.toSpecΓ ≫ q)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (B.val.toRingHom.comp (algebraMap k B)).comp
      (Scheme.ΓSpecIso (.of k)).hom.hom = (f.appTop).hom
  calc
    (B.val.toRingHom.comp (algebraMap k B)).comp (Scheme.ΓSpecIso (.of k)).hom.hom =
        ((algebraMap B Γ(X, ⊤)).comp (algebraMap k B)).comp
          (Scheme.ΓSpecIso (.of k)).hom.hom := by rfl
    _ = (algebraMap k Γ(X, ⊤)).comp (Scheme.ΓSpecIso (.of k)).hom.hom := by
      rw [IsScalarTower.algebraMap_eq k B Γ(X, ⊤)]
    _ = (f.appTop).hom := by
      rw [hmap, ← CommRingCat.hom_comp]
      simp

/-- For a connected reduced scheme `X` with a morphism `f : X ⟶ Spec k`, the `k`-algebra
`Γ(X, ⊤)` has a greatest weakly étale `k`-subalgebra, and it is a field, separable and algebraic
over `k`. -/
private lemma exists_field_maximal_weaklyEtale_globalSections
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace X] [IsReduced X] :
    letI : Algebra k Γ(X, ⊤) := structureMapAlgebra f
    ∃ (B : Subalgebra k Γ(X, ⊤)), Algebra.WeaklyEtale k B ∧
      (∀ C : Subalgebra k Γ(X, ⊤), Algebra.WeaklyEtale k C → C ≤ B) ∧
      IsField B ∧ Algebra.IsSeparable k B ∧ Algebra.IsAlgebraic k B := by
  let : Algebra k Γ(X, ⊤) := structureMapAlgebra f
  let A := Γ(X, ⊤)
  have : Nontrivial A :=
    nontrivial_sections_of_mem ⊤ (Set.mem_univ (Classical.choice (inferInstance : Nonempty X)))
  obtain ⟨B, hB, hBmax⟩ := exists_greatest_weaklyEtale_subalgebra k A
  have hBidem (e : B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 :=
    idempotent_eq_zero_or_one_of_injective (φ := B.val.toRingHom) Subtype.val_injective
      (fun e he => idempotent_eq_zero_or_one_of_connected (X := X) e he) he
  rcases (structure_of_weaklyEtale_over_field.{u, u, u} k B hB).2.2.2.1.1.mpr hBidem with
    hzero | hfield
  · exact absurd (congrArg (fun z : B => (z : A)) (hzero.elim 0 1)) zero_ne_one
  · let : Field B := hfield.toField
    obtain ⟨hsep, halg⟩ := (structure_of_weaklyEtale_over_field.{u, u, u} k B hB).2.2.2.1.2 hfield
    exact ⟨B, hB, hBmax, hfield, hsep, halg⟩

/-- A nonempty scheme whose only idempotent global sections are `0` and `1` is connected. -/
private lemma connectedSpace_of_no_idempotents_globalSections
    {X : Scheme.{u}} [Nonempty X]
    (hidem : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace X := by
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, ?_⟩
  intro s hs
  by_cases hempty : s = ∅
  · exact Or.inl hempty
  by_cases hfull : s = Set.univ
  · exact Or.inr hfull
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hfull
  let U : X.Opens := ⟨s, hs.isOpen⟩
  let V : X.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  let W : Bool → X.Opens := fun b => if b then V else U
  have hcover : iSup W = ⊤ := by
    apply SetLike.coe_injective
    ext x
    simp [W, U, V]
    tauto
  have hdisjoint (i j : Bool) (hij : i ≠ j) : W i ⊓ W j = ⊥ := by
    cases i <;> cases j <;> simp_all [W, U, V]
  let sf : ∀ i : Bool, Γ(X, W i) := fun i => if i then 0 else 1
  have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf W sf := by
    intro i j
    by_cases hij : i = j
    · subst j
      cases i <;> simp [sf]
    · have : Subsingleton Γ(X, W i ⊓ W j) := by
        rw [hdisjoint i j hij]
        infer_instance
      exact Subsingleton.elim _ _
  obtain ⟨e, he, he_unique⟩ := X.sheaf.existsUnique_gluing' W ⊤
    (fun i => homOfLE le_top) (by rw [hcover]) sf hcompatible
  have he_sq : e * e = e := by
    apply he_unique (e * e)
    intro i
    rw [map_mul, he i]
    cases i
    · change (1 : Γ(X, U)) * 1 = 1
      simp
    · change (0 : Γ(X, V)) * 0 = 0
      simp
  rcases hidem e he_sq with hzero | hone
  · have : Nontrivial Γ(X, W false) :=
      nontrivial_sections_of_mem (W false) (x := x) (by simpa [W, U] using hx)
    have h01 := he false
    change (X.presheaf.map (homOfLE le_top).op).hom e = 1 at h01
    rw [hzero, (X.presheaf.map (homOfLE le_top).op).hom.map_zero] at h01
    exact (zero_ne_one h01).elim
  · have : Nontrivial Γ(X, W true) :=
      nontrivial_sections_of_mem (W true) (x := y) (by simpa [W, V] using hy)
    have h01 := (he true).symm
    change 0 = (X.presheaf.map (homOfLE le_top).op).hom e at h01
    rw [hone, (X.presheaf.map (homOfLE le_top).op).hom.map_one] at h01
    exact (zero_ne_one h01).elim

/-- Let `X'` be the pullback of `f : X ⟶ S` along a finite locally free morphism `g : S' ⟶ S`
of affine schemes. If `X'` is nonempty and the pushout of the rings of global sections
`Γ(X, ⊤)` and `Γ(S', ⊤)` over `Γ(S, ⊤)` has no idempotents other than `0` and `1`, then `X'` is
connected. -/
private lemma connectedSpace_of_noIdempotents_pushoutSections
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] [Stacks.Morphisms.IsFiniteLocallyFree g]
    [Nonempty X']
    (hNo : ∀ z : ↑(pushout (f.appLE ⊤ ⊤ (by simp)) (g.appLE ⊤ ⊤ (by simp))),
      IsIdempotentElem z → z = 0 ∨ z = 1) : ConnectedSpace X' := by
  let β := AlgebraicGeometry.pushoutSection h
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp)
  have hβ : IsIso β :=
    Stacks.Tag0CKW.isIso_globalSectionsBaseChange_of_finiteLocallyFree g' f' f g h
  let βIso : pushout (f.appLE ⊤ ⊤ (by simp)) (g.appLE ⊤ ⊤ (by simp)) ≅
      CommRingCat.of Γ(X', ⊤) := asIso β
  exact connectedSpace_of_no_idempotents_globalSections fun e he =>
    idempotent_eq_zero_or_one_of_injective (φ := βIso.inv.hom)
      (ConcreteCategory.injective_of_mono_of_preservesPullback βIso.inv) hNo he

/-- Let `X` be a connected scheme, `B` the greatest weakly étale `k`-subalgebra of `Γ(X, ⊤)`,
assumed to be a field, and `R` a field `k`-isomorphic to `B` compatibly with the maps to
`Γ(X, ⊤)`. Then `X ⟶ Spec Γ(X, ⊤) ⟶ Spec R` is geometrically connected. -/
private lemma geometricallyConnected_of_maximalWeaklyEtale_globalSections
    {k : Type u} [Field k] {X : Scheme.{u}}
    [ConnectedSpace X] [Algebra k Γ(X, ⊤)]
    (B : Subalgebra k Γ(X, ⊤)) [Field B]
    (hB : Algebra.WeaklyEtale k B)
    (hBmax : ∀ C : Subalgebra k Γ(X, ⊤), Algebra.WeaklyEtale k C → C ≤ B)
    {R : Type u} [Field R] [Algebra k R] [Algebra R Γ(X, ⊤)]
    [IsScalarTower k R Γ(X, ⊤)] (e : B ≃ₐ[k] R)
    (hmap : ∀ b : B, algebraMap R Γ(X, ⊤) (e b) = (b : Γ(X, ⊤))) :
    GeometricallyConnected
      (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) := by
  have hmaxR : ∀ C : Subalgebra R Γ(X, ⊤), Algebra.WeaklyEtale R C → C ≤ ⊥ :=
    maximalWeaklyEtale_bot_of_fieldEquivSubalgebra B e hB hBmax hmap
  have : Nontrivial Γ(X, ⊤) :=
    nontrivial_sections_of_mem ⊤ (Set.mem_univ (Classical.choice (inferInstance : Nonempty X)))
  let fR : X ⟶ Spec (.of R) :=
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))
  apply (AlgebraicGeometry.geometricallyConnected_iff_forall_finite_separable
    (k := R) (X := X) fR).mpr
  intro E _ _ hdim hsep
  let g : Spec (.of E) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R E))
  let g' := pullback.fst (C := Scheme) fR g
  let f' := pullback.snd (C := Scheme) fR g
  have hpull : IsPullback g' f' fR g := IsPullback.of_hasPullback _ _
  have : Surjective g :=
    ⟨fun _ => ⟨Classical.choice (inferInstance : Nonempty (Spec (.of E))), Subsingleton.elim _ _⟩⟩
  have : Nonempty (pullback (C := Scheme) fR g) :=
    ⟨(g'.surjective (Classical.choice (inferInstance : Nonempty X))).choose⟩
  have hno : ∀ z : ↑(pushout (fR.appLE ⊤ ⊤ (by simp)) (g.appLE ⊤ ⊤ (by simp))),
      IsIdempotentElem z → z = 0 ∨ z = 1 := by
    intro z hz
    let f0 : CommRingCat.of R ⟶ Γ(X, ⊤) :=
      CommRingCat.ofHom (algebraMap R Γ(X, ⊤))
    let g0 : CommRingCat.of R ⟶ CommRingCat.of E :=
      CommRingCat.ofHom (algebraMap R E)
    let f1 := fR.appLE ⊤ ⊤ (by simp)
    let g1 := g.appLE ⊤ ⊤ (by simp)
    have hf : (Scheme.ΓSpecIso (.of R)).hom ≫ f0 = f1 := by
      calc
        (Scheme.ΓSpecIso (.of R)).hom ≫ f0 =
            (Spec.map f0).appTop ≫ (Scheme.ΓSpecIso (.of Γ(X, ⊤))).hom :=
          Scheme.ΓSpecIso_naturality f0 |>.symm
        _ = (Spec.map f0).appTop ≫ X.toSpecΓ.appTop := by
          have hIso : (Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).hom =
              (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
            ext x
            rfl
          rw [hIso, Scheme.toSpecΓ_appTop]
        _ = (X.toSpecΓ ≫ Spec.map f0).appTop := by
          rw [Scheme.Hom.comp_appTop]
        _ = f1 := by simp [f1, fR, Scheme.Hom.app_eq_appLE, f0]
    have hg : (Scheme.ΓSpecIso (.of R)).hom ≫ g0 =
        g1 ≫ (Scheme.ΓSpecIso (.of E)).hom := by
      calc
        (Scheme.ΓSpecIso (.of R)).hom ≫ g0 =
            g.appTop ≫ (Scheme.ΓSpecIso (.of E)).hom :=
          (Scheme.ΓSpecIso_naturality g0).symm
        _ = g1 ≫ (Scheme.ΓSpecIso (.of E)).hom := by
          simp [g1, Scheme.Hom.app_eq_appLE]
    let F := span f1 g1
    let G := span f0 g0
    let hSpan : F ≅ G := NatIso.ofComponents
      (fun j => match j with
        | WalkingSpan.zero => Scheme.ΓSpecIso (.of R)
        | WalkingSpan.left => Iso.refl _
        | WalkingSpan.right => Scheme.ΓSpecIso (.of E))
      (by
        rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) m <;> cases m <;>
          simp [F, G, hf, hg])
    let cStd := CommRingCat.pushoutCocone R Γ(X, ⊤) E
    have hc : IsColimit ((Cocone.precompose hSpan.hom).obj cStd) :=
      (IsColimit.precomposeHomEquiv hSpan cStd).symm
        (CommRingCat.pushoutCoconeIsColimit R Γ(X, ⊤) E)
    let ePush : pushout f1 g1 ≅ CommRingCat.of (Γ(X, ⊤) ⊗[R] E) :=
      IsColimit.coconePointUniqueUpToIso (pushout.isColimit f1 g1) hc
    let e := Algebra.TensorProduct.comm R E Γ(X, ⊤)
    exact idempotent_eq_zero_or_one_of_injective
      (φ := e.symm.toRingEquiv.toRingHom.comp ePush.hom.hom)
      (e.symm.injective.comp (ConcreteCategory.injective_of_mono_of_preservesPullback ePush.hom))
      (fun t ht => idempotent_eq_zero_or_one_after_field_baseChange
        (R := R) (E := E) (A := Γ(X, ⊤)) hmaxR t ht) hz
  let : Stacks.Morphisms.IsFiniteLocallyFree g :=
    finiteLocallyFree_specMap_of_finiteDimensional R E
  exact connectedSpace_of_noIdempotents_pushoutSections g' f' fR g hpull hno

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04PZ** (Gabber). Let `K/k` be an extension of fields -- not assumed
finite, algebraic or separable -- and let `X` be a scheme over `k`. The projection `X_K ⟶ X`
sends every connected component of `X_K` onto a connected component of `X`: the image of the
connected component of a point `x` is the connected component of its image. -/
@[stacks 04PZ, ega "IV 4.4.1" "partial", sga "3 VIA 2.4.1" "partial", sga "3 VIB 1.4.1" "partial"]
theorem image_connectedComponent_baseChange
    {X : Scheme.{u}} (k K : Type u) [Field k] [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k))
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base ''
        connectedComponent x =
      connectedComponent
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base x) := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  apply Set.Subset.antisymm
  · exact p.continuous.image_connectedComponent_subset x
  · intro y hy
    let C : Set X := connectedComponent (p.base x)
    let I : X.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal ⟨C, isClosed_connectedComponent⟩
    let Y := I.subscheme
    let i := I.subschemeι
    have hi : Set.range i.base = C := by
      change Set.range I.subschemeι.base = C
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hxC : p.base x ∈ C := mem_connectedComponent
    have hyC : y ∈ C := by simpa [C] using hy
    obtain ⟨yY, hyY⟩ := Set.mem_range.mp (hi.symm ▸ hyC)
    let gK : Spec (.of K) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    let fY : Y ⟶ Spec (.of k) := i ≫ f
    let YK := pullback fY gK
    let XK := pullback f gK
    let mY : YK ⟶ XK :=
      pullback.map fY gK f gK i (𝟙 _) (𝟙 _) (by simp [fY]) (by simp)
    have hmYrange : Set.range mY.base =
        (pullback.fst f gK).base ⁻¹' Set.range i.base := by
      rw [Scheme.Pullback.range_map fY gK f gK i (𝟙 _) (𝟙 _)
        (by simp [fY]) (by simp)]
      simp
    obtain ⟨xY, hxY⟩ : x ∈ Set.range mY.base := by
      rw [hmYrange]
      change p.base x ∈ Set.range i.base
      rwa [hi]
    have : IsReduced Y :=
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
        ⟨C, isClosed_connectedComponent⟩
    have : ConnectedSpace Y := by
      apply Subtype.connectedSpace
      simpa [Y, I, C, ← hi] using isConnected_connectedComponent (x := p.base x)
    let : Algebra k Γ(Y, ⊤) := structureMapAlgebra fY
    obtain ⟨B, hB, hBmax, hBfield, _, _⟩ :=
      exists_field_maximal_weaklyEtale_globalSections fY
    let : Field B := hBfield.toField
    let : Algebra B Γ(Y, ⊤) := RingHom.toAlgebra B.val.toRingHom
    let : IsScalarTower k B Γ(Y, ⊤) := inferInstance
    let fB : Y ⟶ Spec (.of B) :=
      Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(Y, ⊤)))
    have hfactorB : fB ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) = fY :=
      structureMap_factors_through_subalgebra fY rfl B
    have hgeomB : GeometricallyConnected fB :=
      geometricallyConnected_of_maximalWeaklyEtale_globalSections
        (X := Y) B hB hBmax (AlgEquiv.refl (R := k) (A₁ := B)) (by intro b; rfl)
    let sB : Spec (.of B) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k B))
    let T := pullback sB gK
    let rB : T ⟶ Spec (.of B) := pullback.fst sB gK
    let eBase₀ := pullbackRightPullbackFstIso sB gK fB
    let eBase : pullback fB rB ≅ YK :=
      eBase₀.trans (pullback.congrHom hfactorB rfl)
    let q : pullback fB rB ⟶ T := pullback.snd fB rB
    let xAlt := eBase.inv.base xY
    let s : T := q.base xAlt
    let L := T.residueField s
    let l : Spec (.of L) ⟶ T := T.fromSpecResidueField s
    have : GeometricallyConnected q := inferInstance
    let Z := pullback q l
    have : ConnectedSpace Z := by
      change ConnectedSpace (q.fiber s)
      infer_instance
    have hxFiber : xAlt ∈ Set.range (pullback.fst q l).base := by
      rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
      simp [s]
    obtain ⟨z₀, hz₀⟩ := hxFiber
    let m : Z ⟶ XK := pullback.fst q l ≫ eBase.hom ≫ mY
    have hconnected : _root_.IsConnected (Set.range m.base) := by
      rw [← Set.image_univ]
      exact isConnected_univ.image m.base m.continuous.continuousOn
    have hxRange : x ∈ Set.range m.base := by
      refine ⟨z₀, ?_⟩
      simp [m, hz₀, xAlt, hxY]
    let lB : Spec (.of L) ⟶ Spec (.of B) := l ≫ rB
    obtain ⟨w, hw⟩ : yY ∈ Set.range (pullback.fst (C := Scheme) fB lB).base := by
      rw [Scheme.Pullback.range_fst fB lB]
      exact (⟨Classical.choice (inferInstance : Nonempty (Spec (.of L))),
        Subsingleton.elim _ _⟩ : fB.base yY ∈ Set.range lB.base)
    let eFiber : Z ≅ pullback fB lB := by
      dsimp [Z, lB, q, l]
      exact pullbackLeftPullbackSndIso fB rB (T.fromSpecResidueField s)
    let z : Z := eFiber.inv.base w
    have hzY : (pullback.fst fB rB).base ((pullback.fst q l).base z) = yY := by
      have hfst : eFiber.hom ≫ pullback.fst fB lB =
          pullback.fst q l ≫ pullback.fst fB rB := by
        dsimp [eFiber, lB, q, l]
        simp
      simpa [z, Scheme.Hom.comp_apply, hw] using (congrArg (fun h : Z ⟶ Y => h.base z) hfst).symm
    have hzImage : m.base z ∈ connectedComponent x :=
      hconnected.subset_connectedComponent hxRange ⟨z, rfl⟩
    have hmYfst : mY ≫ pullback.fst f gK = pullback.fst fY gK ≫ i := by
      change pullback.lift (pullback.fst fY gK ≫ i)
        (pullback.snd fY gK ≫ 𝟙 _) _ ≫ pullback.fst f gK = _
      rw [pullback.lift_fst]
    have heBasefst : eBase.hom ≫ pullback.fst fY gK = pullback.fst fB rB := by
      dsimp [eBase, eBase₀, rB]
      rw [pullback.congrHom_hom]
      simp only [pullback.map, pullback.lift_fst, Category.assoc, Category.comp_id]
      rw [pullbackRightPullbackFstIso_hom_fst]
    have hmproj : m ≫ p = pullback.fst q l ≫ pullback.fst fB rB ≫ i := by
      calc
        m ≫ p = pullback.fst q l ≫ (eBase.hom ≫ (mY ≫ p)) := by
          simp [m, Category.assoc]
        _ = pullback.fst q l ≫ (eBase.hom ≫ (pullback.fst fY gK ≫ i)) := by
          rw [hmYfst]
        _ = _ := by
          simpa only [Category.assoc] using
            (congrArg (fun h => pullback.fst q l ≫ (h ≫ i)) heBasefst)
    have hzX : p.base (m.base z) = y := by
      calc
        p.base (m.base z) = (m ≫ p).base z := rfl
        _ = i.base ((pullback.fst fB rB).base ((pullback.fst q l).base z)) := by
          rw [hmproj]
          simp
        _ = y := by rw [hzY, hyY]
    exact ⟨m.base z, hzImage, hzX⟩

end AlgebraicGeometry

end
