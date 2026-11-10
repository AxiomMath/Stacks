module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVect
public import StacksFrontier.RingTheory.Module.MilnorHomQuotient
public import StacksFrontier.RingTheory.MilnorPatching.OneGeneratorFrobenius

/-!
# Milnor patching of homomorphisms, for vector bundles on an affine scheme

Let `A` be a commutative ring, let `f : A` and let `J ⊆ A` be an ideal annihilated by `f ^ n`.
This file proves, for the category `Vect(Spec A)` of vector bundles, the faithfulness and the
fullness input of the comparison of Stacks Tag 0EXC: a morphism of vector bundles which restricts
to zero on `Spec (A ⧸ J)` and on `Spec (A ⧸ fA)` is killed by a high enough Frobenius twist, and a
pair of morphisms of the restrictions agreeing on `Spec (A ⧸ (J + fA))` comes from a single
morphism. Both are read through the affine comparison `AlgebraicGeometry.tildeVect` from finite
projective `A`-modules to `Vect(Spec A)`, under which restriction along `Spec φ` becomes
extension of scalars along `φ`.

## Main results

* `AlgebraicGeometry.tildeVect_map_pullback_eq_zero_iff` and
  `AlgebraicGeometry.tildeVect_map_pullback_eq_zero_iff_baseChange`: the restriction of
  `M^~ ⟶ N^~` along `Spec φ` vanishes exactly when the extension of scalars of `M ⟶ N` along `φ`
  does, equivalently when its base change as a linear map does.
  `AlgebraicGeometry.tildeVect_map_pullback_eq_iff` and
  `AlgebraicGeometry.tildeVect_map_pullback_eq_iff_baseChange` are the same statements for an
  equality of two morphisms rather than for vanishing.
* `AlgebraicGeometry.exists_tildeVect_presentation`: every pair of vector bundles on `Spec R` is
  the comparison image of a pair of finite projective modules, compatibly for all morphisms
  between them.
* `AlgebraicGeometry.vect_pullback_frobeniusPow_map_eq_zero`: a morphism of vector bundles on
  `Spec A` which restricts to zero on `Spec (A ⧸ J)` and on `Spec (A ⧸ fA)` is killed by a high
  enough Frobenius twist.
* `AlgebraicGeometry.exists_hom_of_pullback_pair`: a pair of morphisms of the restrictions to
  `Spec (A ⧸ J)` and `Spec (A ⧸ fA)`, realized by morphisms upstairs which agree on
  `Spec (A ⧸ (J + fA))`, is realized by a single morphism upstairs.

## References

* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂ u

/-! ### Conjugation by isomorphisms, and natural isomorphisms, on `= 0` and on `=` -/

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Composing with isomorphisms on both sides does not change whether a morphism is zero. -/
lemma comp_comp_eq_zero_iff [Preadditive D] {W X Y Z : D} (u : W ⟶ X) [IsIso u] (v : Y ⟶ Z)
    [IsIso v] (g : X ⟶ Y) : u ≫ g ≫ v = 0 ↔ g = 0 := by
  refine ⟨fun h ↦ (cancel_mono v).mp ((cancel_epi u).mp ?_),
    fun h ↦ by rw [h, Limits.zero_comp, Limits.comp_zero]⟩
  rw [h, Limits.zero_comp, Limits.comp_zero]

/-- Composing with isomorphisms on both sides is injective on morphisms. -/
lemma comp_comp_eq_comp_comp_iff {W X Y Z : D} (u : W ⟶ X) [IsIso u] (v : Y ⟶ Z) [IsIso v]
    (g g' : X ⟶ Y) : u ≫ g ≫ v = u ≫ g' ≫ v ↔ g = g' :=
  Iff.trans (cancel_epi u) (cancel_mono v)

/-- A morphism is recovered from its conjugate by the inverse isomorphisms. -/
lemma eq_comp_comp_of_comp_comp_eq {X Y X' Y' : D} (u : X' ≅ X) (v : Y' ≅ Y) {g : X' ⟶ Y'}
    {k : X ⟶ Y} (hg : g = u.hom ≫ k ≫ v.inv) : k = u.inv ≫ g ≫ v.hom := by
  simp [hg]

/-- The image of a morphism under a functor, conjugated by isomorphisms, is zero exactly when its
image is. -/
lemma Functor.map_comp_comp_eq_zero_iff [Preadditive D] (F : C ⥤ D) {W X Y Z : C} (u : W ⟶ X)
    [IsIso u] (v : Y ⟶ Z) [IsIso v] (g : X ⟶ Y) :
    F.map (u ≫ g ≫ v) = 0 ↔ F.map g = 0 := by
  simp only [Functor.map_comp]
  exact comp_comp_eq_zero_iff _ _ _

/-- Two morphisms conjugated by the same isomorphisms have equal images under a functor exactly
when their images are equal. -/
lemma Functor.map_comp_comp_eq_map_comp_comp_iff (F : C ⥤ D) {W X Y Z : C} (u : W ⟶ X) [IsIso u]
    (v : Y ⟶ Z) [IsIso v] (g g' : X ⟶ Y) :
    F.map (u ≫ g ≫ v) = F.map (u ≫ g' ≫ v) ↔ F.map g = F.map g' := by
  simp only [Functor.map_comp]
  exact comp_comp_eq_comp_comp_iff _ _ _ _

namespace NatIso

variable {F G : C ⥤ D}

/-- A natural isomorphism conjugates the action of one functor on a morphism into the action of
the other. -/
lemma hom_app_comp_map_comp_inv_app (α : F ≅ G) {X Y : C} (g : X ⟶ Y) :
    α.hom.app X ≫ G.map g ≫ α.inv.app Y = F.map g := by
  rw [← Category.assoc, ← α.hom.naturality g, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]

/-- Naturally isomorphic functors agree on whether a morphism is sent to zero. -/
lemma map_eq_zero_iff [Preadditive D] (α : F ≅ G) {X Y : C} (g : X ⟶ Y) :
    F.map g = 0 ↔ G.map g = 0 := by
  rw [← hom_app_comp_map_comp_inv_app α g]
  exact comp_comp_eq_zero_iff _ _ _

/-- Naturally isomorphic functors agree on whether two morphisms have the same image. -/
lemma map_eq_map_iff (α : F ≅ G) {X Y : C} (g g' : X ⟶ Y) :
    F.map g = F.map g' ↔ G.map g = G.map g' := by
  rw [← hom_app_comp_map_comp_inv_app α g, ← hom_app_comp_map_comp_inv_app α g']
  exact comp_comp_eq_comp_comp_iff _ _ _ _

end NatIso

namespace ObjectProperty

/-- Two morphisms of a full subcategory are equal exactly when their underlying morphisms are. -/
lemma hom_eq_iff (P : ObjectProperty C) {X Y : P.FullSubcategory} (f g : X ⟶ Y) :
    f = g ↔ f.hom = g.hom :=
  ⟨fun h ↦ by rw [h], ObjectProperty.hom_ext P⟩

/-- A morphism of a full subcategory of a preadditive category is zero exactly when its underlying
morphism is. -/
lemma hom_eq_zero_iff [Preadditive C] (P : ObjectProperty C) {X Y : P.FullSubcategory}
    (f : X ⟶ Y) : f = 0 ↔ f.hom = 0 :=
  ⟨fun h ↦ by rw [h]; exact rfl, fun h ↦ ObjectProperty.hom_ext P h⟩

end ObjectProperty

end CategoryTheory

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}}

/-! ### The transport dictionary -/

/-- The affine comparison preserves zero morphisms. -/
instance tildeVect_preservesZeroMorphisms (R : CommRingCat.{u}) :
    (tildeVect R).PreservesZeroMorphisms where
  map_zero L L' := ObjectProperty.hom_ext _ ((tilde.functor R).map_zero L.obj L'.obj)

/-- A morphism of finite projective modules is zero exactly when the attached morphism of vector
bundles is. -/
lemma tildeVect_map_eq_zero_iff (R : CommRingCat.{u}) {L L' : FinProj R} (ψ : L ⟶ L') :
    (tildeVect R).map ψ = 0 ↔ ψ = 0 :=
  Functor.map_eq_zero_iff _

/-- The restriction along `Spec φ` of the morphism of vector bundles attached to `ψ` vanishes
exactly when the extension of scalars of `ψ` along `φ` vanishes. -/
lemma tildeVect_map_pullback_eq_zero_iff (φ : R ⟶ S) {L L' : FinProj R} (ψ : L ⟶ L') :
    (Scheme.Vect.pullback (Spec.map φ)).map ((tildeVect R).map ψ) = 0 ↔
      (FinProj.extendScalars φ).map ψ = 0 :=
  Iff.trans (NatIso.map_eq_zero_iff (tildeVectPullbackIso φ) ψ) (tildeVect_map_eq_zero_iff S _)

/-- The same dictionary as `AlgebraicGeometry.tildeVect_map_pullback_eq_zero_iff` for an equality
of two morphisms: two restrictions agree exactly when the two extensions of scalars do. -/
lemma tildeVect_map_pullback_eq_iff (φ : R ⟶ S) {L L' : FinProj R} (ψ ψ' : L ⟶ L') :
    (Scheme.Vect.pullback (Spec.map φ)).map ((tildeVect R).map ψ) =
        (Scheme.Vect.pullback (Spec.map φ)).map ((tildeVect R).map ψ') ↔
      (FinProj.extendScalars φ).map ψ = (FinProj.extendScalars φ).map ψ' :=
  Iff.trans (NatIso.map_eq_map_iff (tildeVectPullbackIso φ) ψ ψ')
    ⟨fun h ↦ (tildeVect S).map_injective h, fun h ↦ congrArg (tildeVect S).map h⟩

/-- The restriction along `Spec φ` of the morphism of vector bundles attached to `ψ` vanishes
exactly when the base change along `φ` of the underlying linear map of `ψ` vanishes. -/
lemma tildeVect_map_pullback_eq_zero_iff_baseChange (φ : R ⟶ S) {L L' : FinProj R} (ψ : L ⟶ L') :
    letI : Algebra R S := φ.hom.toAlgebra
    (Scheme.Vect.pullback (Spec.map φ)).map ((tildeVect R).map ψ) = 0 ↔
      LinearMap.baseChange S ψ.hom.hom = 0 := by
  let _ : Algebra R S := φ.hom.toAlgebra
  exact Iff.trans (tildeVect_map_pullback_eq_zero_iff φ ψ)
    (Iff.trans (ObjectProperty.hom_eq_zero_iff _ _)
      (Stacks.MilnorHom.moduleCat_extendScalars_map_eq_zero_iff φ ψ.hom))

/-- The same dictionary as `AlgebraicGeometry.tildeVect_map_pullback_eq_zero_iff_baseChange` for
an equality of two morphisms. -/
lemma tildeVect_map_pullback_eq_iff_baseChange (φ : R ⟶ S) {L L' : FinProj R} (ψ ψ' : L ⟶ L') :
    letI : Algebra R S := φ.hom.toAlgebra
    ((Scheme.Vect.pullback (Spec.map φ)).map ((tildeVect R).map ψ) =
        (Scheme.Vect.pullback (Spec.map φ)).map ((tildeVect R).map ψ')) ↔
      LinearMap.baseChange S ψ.hom.hom = LinearMap.baseChange S ψ'.hom.hom := by
  let _ : Algebra R S := φ.hom.toAlgebra
  exact Iff.trans (tildeVect_map_pullback_eq_iff φ ψ ψ')
    (Iff.trans (ObjectProperty.hom_eq_iff _ _ _) ModuleCat.hom_ext_iff)

/-- The dictionary of `AlgebraicGeometry.tildeVect_map_pullback_eq_zero_iff_baseChange` for a ring
homomorphism between bare commutative rings. -/
lemma tildeVect_map_pullback_ofHom_eq_zero_iff_baseChange {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {L L' : FinProj (CommRingCat.of A)} (ψ : L ⟶ L') :
    letI : Algebra A B := φ.toAlgebra
    (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom φ))).map
        ((tildeVect (CommRingCat.of A)).map ψ) = 0 ↔
      LinearMap.baseChange B ψ.hom.hom = 0 :=
  tildeVect_map_pullback_eq_zero_iff_baseChange (CommRingCat.ofHom φ) ψ

/-- The dictionary of `AlgebraicGeometry.tildeVect_map_pullback_eq_iff_baseChange` for a ring
homomorphism between bare commutative rings. -/
lemma tildeVect_map_pullback_ofHom_eq_iff_baseChange {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {L L' : FinProj (CommRingCat.of A)} (ψ ψ' : L ⟶ L') :
    letI : Algebra A B := φ.toAlgebra
    ((Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom φ))).map
          ((tildeVect (CommRingCat.of A)).map ψ) =
        (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom φ))).map
          ((tildeVect (CommRingCat.of A)).map ψ')) ↔
      LinearMap.baseChange B ψ.hom.hom = LinearMap.baseChange B ψ'.hom.hom :=
  tildeVect_map_pullback_eq_iff_baseChange (CommRingCat.ofHom φ) ψ ψ'

/-! ### Reduction to the image of the affine comparison -/

/-- Every pair of vector bundles on `Spec R` is presented by a pair of finite projective modules,
compatibly for every morphism between them. -/
lemma exists_tildeVect_presentation (R : CommRingCat.{u}) (M₀ N₀ : (Spec R).Vect) :
    ∃ (L L' : FinProj R) (e : (tildeVect R).obj L ≅ M₀) (e' : (tildeVect R).obj L' ≅ N₀),
      ∀ h : M₀ ⟶ N₀, ∃ ψ : L ⟶ L', h = e.inv ≫ (tildeVect R).map ψ ≫ e'.hom :=
  ⟨(tildeVect R).objPreimage M₀, (tildeVect R).objPreimage N₀,
    (tildeVect R).objObjPreimageIso M₀, (tildeVect R).objObjPreimageIso N₀, fun h ↦
      ⟨(tildeVect R).preimage (((tildeVect R).objObjPreimageIso M₀).hom ≫ h ≫
        ((tildeVect R).objObjPreimageIso N₀).inv),
      eq_comp_comp_of_comp_comp_eq _ _ ((tildeVect R).map_preimage _)⟩⟩

/-! ### Milnor patching of homomorphisms on vector bundles -/

/-- Let `f ^ n` annihilate `J`, let the prime `p` vanish in `A` and let `n + 1 ≤ p ^ N`. A
morphism of vector bundles on `Spec A` which restricts to zero on `Spec (A ⧸ J)` and on
`Spec (A ⧸ fA)` restricts to zero along the `p ^ N`-power Frobenius endomorphism of `A`. -/
theorem vect_pullback_frobeniusPow_map_eq_zero
    (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N)
    {M₀ N₀ : (Spec (CommRingCat.of A)).Vect} (h : M₀ ⟶ N₀)
    (hJ : (Scheme.Vect.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map h = 0)
    (hf : (Scheme.Vect.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))).map h = 0) :
    (Scheme.Vect.pullback
      (Spec.map (CommRingCat.ofHom
        (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N)))).map h = 0 := by
  obtain ⟨L, L', e, e', hpres⟩ := exists_tildeVect_presentation (CommRingCat.of A) M₀ N₀
  obtain ⟨ψ, hψ⟩ := hpres h
  let _ : Module.Finite A L.obj := L.property.1
  let _ : Module.Projective A L.obj := L.property.2
  let _ : Module.Finite A L'.obj := L'.property.1
  let _ : Module.Projective A L'.obj := L'.property.2
  have hbc : ∀ I : Ideal A, (Scheme.Vect.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map h = 0 →
      LinearMap.baseChange (A ⧸ I) ψ.hom.hom = 0 := fun I hI ↦
    (tildeVect_map_pullback_ofHom_eq_zero_iff_baseChange (Ideal.Quotient.mk I) ψ).mp
      ((Functor.map_comp_comp_eq_zero_iff _ e.inv e'.hom _).mp (hψ ▸ hI))
  let _ : Algebra A A := (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N).toAlgebra
  have hker : ∀ x ∈ J ⊓ Ideal.span {f}, (algebraMap A A) x = 0 := by
    intro x hx
    change MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N x = 0
    rw [MilnorPatching.OneGeneratorFrobenius.frobeniusPow_apply]
    exact MilnorPatching.OneGeneratorFrobenius.pow_eq_zero_of_mem_inf_of_le hann hN hx
  have key : LinearMap.baseChange A ψ.hom.hom = 0 :=
    Stacks.MilnorHom.baseChange_eq_zero_of_baseChange_eq_zero_pair J (Ideal.span {f}) hker
      ψ.hom.hom (hbc _ hJ) (hbc _ hf)
  rw [hψ]
  exact (Functor.map_comp_comp_eq_zero_iff _ e.inv e'.hom _).mpr
    ((tildeVect_map_pullback_ofHom_eq_zero_iff_baseChange
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N) ψ).mpr key)

/-- If `h₁` realizes `a` on `Spec (A ⧸ J)`, if `h₂` realizes `b` on `Spec (A ⧸ fA)`, and if `h₁`
and `h₂` have the same restriction to `Spec (A ⧸ (J + fA))`, then a single morphism of vector
bundles on `Spec A` realizes both `a` and `b`. -/
theorem exists_hom_of_pullback_pair
    (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    {M₀ N₀ : (Spec (CommRingCat.of A)).Vect}
    (a : (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj M₀ ⟶
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj N₀)
    (b : (Scheme.Vect.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))).obj M₀ ⟶
      (Scheme.Vect.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))).obj N₀)
    (h₁ h₂ : M₀ ⟶ N₀)
    (ha : (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map h₁ = a)
    (hb : (Scheme.Vect.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))).map h₂ = b)
    (hcompat : (Scheme.Vect.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ⊔ Ideal.span {f}))))).map h₁ =
      (Scheme.Vect.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ⊔ Ideal.span {f}))))).map h₂) :
    ∃ h : M₀ ⟶ N₀,
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map h = a ∧
      (Scheme.Vect.pullback
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))).map h = b := by
  obtain ⟨L, L', e, e', hpres⟩ := exists_tildeVect_presentation (CommRingCat.of A) M₀ N₀
  obtain ⟨ψ₁, hψ₁⟩ := hpres h₁
  obtain ⟨ψ₂, hψ₂⟩ := hpres h₂
  let _ : Module.Finite A L.obj := L.property.1
  let _ : Module.Projective A L.obj := L.property.2
  have hcompat' : LinearMap.baseChange (A ⧸ (J ⊔ Ideal.span {f})) ψ₁.hom.hom =
      LinearMap.baseChange (A ⧸ (J ⊔ Ideal.span {f})) ψ₂.hom.hom := by
    refine (tildeVect_map_pullback_ofHom_eq_iff_baseChange
      (Ideal.Quotient.mk (J ⊔ Ideal.span {f})) ψ₁ ψ₂).mp ?_
    exact (Functor.map_comp_comp_eq_map_comp_comp_iff _ e.inv e'.hom _ _).mp (hψ₁ ▸ hψ₂ ▸ hcompat)
  obtain ⟨h₀, hh₀J, hh₀f⟩ := Stacks.MilnorHom.exists_baseChange_eq_pair J (Ideal.span {f})
    (LinearMap.baseChange (A ⧸ J) ψ₁.hom.hom)
    (LinearMap.baseChange (A ⧸ Ideal.span {f}) ψ₂.hom.hom)
    ψ₁.hom.hom ψ₂.hom.hom rfl rfl hcompat'
  refine ⟨e.inv ≫ (tildeVect (CommRingCat.of A)).map ⟨ModuleCat.ofHom h₀⟩ ≫ e'.hom, ?_, ?_⟩
  · rw [hψ₁] at ha
    refine Eq.trans ?_ ha
    refine (Functor.map_comp_comp_eq_map_comp_comp_iff _ e.inv e'.hom _ _).mpr ?_
    exact (tildeVect_map_pullback_ofHom_eq_iff_baseChange (Ideal.Quotient.mk J) _ ψ₁).mpr hh₀J
  · rw [hψ₂] at hb
    refine Eq.trans ?_ hb
    refine (Functor.map_comp_comp_eq_map_comp_comp_iff _ e.inv e'.hom _ _).mpr ?_
    exact (tildeVect_map_pullback_ofHom_eq_iff_baseChange
      (Ideal.Quotient.mk (Ideal.span {f})) _ ψ₂).mpr hh₀f

end AlgebraicGeometry

end
