module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent

/-!
# The descent datum of an affine morphism, from presheaves to rings

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` quantifies over a
Cartesian square `IsPullback m r f (yoneda.map q ≫ h)` of presheaves on the big fppf site of `S`,
with `h` out of a representable presheaf and `q : c ⟶ a` a surjective étale morphism of the site;
after `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource`
both `a` and `c` may be assumed affine. At `P = AlgebraicGeometry.IsAffineHom` the proof of Stacks
0245 then reads the square as a descent datum of *rings* along the faithfully flat map
`Γ(a) → Γ(c)` and feeds it to effective descent for algebras,
`ModuleCat.bijective_productMap_descentInvariants`. This file is that translation.

It is carried out in two steps, which are independent of one another.

*From presheaves to schemes.* The hypothesis `(P.inverseImage _).presheaf r` says in particular
that `r` is representable, so the source `A₀` of the datum is `yoneda.obj v` for an object `v` of
the site which is affine over `c`, Stacks 01S6. The descent datum itself — the isomorphism
`φ` between the two base changes of `v` to `c ×_a c` — is *not* extra data: both base changes are
base changes of the same morphism `f` along the same morphism `yoneda.map (pr₁ ≫ q) ≫ h` of
presheaves, because `pr₁ ≫ q = pr₂ ≫ q`, so the comparison isomorphism of
`CategoryTheory.IsPullback.isoIsPullback` is available and is unique. That is
`AlgebraicGeometry.Space.exists_affineDescentDatum_of_isPullback`, whose statement mentions no
rings at all: it produces `v`, the morphism `w : v ⟶ c`, and the isomorphism `φ` between
`v ×_a c` and `c ×_a v` over `c ×_a c`.

*From schemes to rings.* A Cartesian square of affine schemes becomes a pushout square of rings,
`AlgebraicGeometry.isPushout_appTop_of_isPullback`, and a pushout of `Γ(c) ← Γ(a) → Γ(v)` in
`CommRingCat` is the tensor product, `CommRingCat.isPushout_tensorProduct`. Comparing the two
presentations turns `φ` into an isomorphism of `Γ(a)`-algebras
`Γ(v) ⊗[Γ(a)] Γ(c) ≃ Γ(c) ⊗[Γ(a)] Γ(v)`, and the two compatibilities of `φ` with the projections
turn into the single equation `τ (algebraMap a b ⊗ b') = b ⊗ algebraMap a b'` which says that `τ`
is an isomorphism over `Γ(c) ⊗[Γ(a)] Γ(c)`. That is
`AlgebraicGeometry.exists_transition_of_isPushout` and its geometric form
`AlgebraicGeometry.exists_transition_of_isPullback`.

## Main results

* `AlgebraicGeometry.exists_transition_of_isPushout`: two pushout presentations of
  `Γ(v) ⊗[Γ(a)] Γ(c)` and `Γ(c) ⊗[Γ(a)] Γ(v)` together with an isomorphism between them which is
  compatible with the structure maps give the transition isomorphism of an algebra descent datum,
  in exactly the form `ModuleCat.algebraTransition` consumes.
* `AlgebraicGeometry.exists_transition_of_isPullback` is the same statement with the two pushouts
  coming from two Cartesian squares of affine schemes.
* `AlgebraicGeometry.Space.exists_affineDescentDatum_of_isPullback`: **the presheaf-level datum of
  an affine morphism is a scheme-level descent datum.** From a Cartesian square presenting `A₀` as
  the base change of `f` along `yoneda.map q ≫ h`, with that base change affine over `c`, one
  extracts the object `v` of the site representing `A₀`, the affine morphism `w : v ⟶ c`, and the
  descent isomorphism between the two base changes of `w` to `c ×_a c`.
* `AlgebraicGeometry.Space.exists_descentIso_of_isPullback` is the comparison isomorphism on its
  own: two morphisms `d ⟶ c` of the site which agree after `q` have isomorphic base changes of
  the datum, compatibly with the projection to `d`.

## Implementation notes

The object representing `A₀` is produced as `hr.rep.pullback (𝟙 (yoneda.obj c))`, the base change
of the datum along the identity; `AlgebraicGeometry.Space.descentObjIso` is the resulting
isomorphism `A₀ ≅ yoneda.obj v`. Taking the base change along the identity rather than naming a
representing object directly is what makes the two base changes to `c ×_a c` be *the same
construction* applied to `pr₁` and to `pr₂`, which is what the comparison isomorphism needs.

The Cartesian squares produced here are squares over `w ≫ q` and `q`, i.e. they present the base
changes as `v ×_a c` and `c ×_a v` rather than as `v ×_c (c ×_a c)`. The two agree, and the form
over `a` is the one the ring translation needs, since it is the one whose pushout of rings is a
tensor product over `Γ(a)` with no further base change. The passage between them is
`CategoryTheory.IsPullback.paste_horiz` against the Cartesian square of `c ×_a c` itself.

The cocycle condition is **not** produced here. It is the one part of the datum which does not
follow from the two compatibilities of `φ` with the projections: it holds in this situation only
because `φ` is the canonical comparison of two base changes of `f`, not merely some isomorphism
over `c ×_a c`. In the form in which it is still owed it is the hypothesis `hkey` of
`ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc`: coassociativity of the coaction
`σ b = τ (b ⊗ 1)`, a single equation of ring homomorphisms `Γ(v) → Γ(c) ⊗ (Γ(c) ⊗ Γ(v))`. On the
geometric side both of its sides are `Γ` of a morphism `c ×_a (c ×_a v) ⟶ v`, so one triple fibre
product has to be compared with one triple tensor product, rather than three with three; and the
equation of the two morphisms is again uniqueness of the comparison of two base changes of `f`,
now along the three projections `c ×_a c ×_a c ⟶ c`, which all agree after `q`.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 01S6](https://stacks.math.columbia.edu/tag/01S6)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct CommRingCat

namespace AlgebraicGeometry

/-! ### The transition isomorphism of an algebra descent datum -/

/-- **An isomorphism between two pushout presentations is a transition isomorphism.** Let
`R → A → T` be a tower of rings, let `Q₁` be a pushout of `A ← R → T` and let `Q₂` be a pushout of
`T ← R → A`, and let `χ : Q₁ ≅ Q₂` be an isomorphism which carries the structure map of `T` into
the structure map of `A` composed with `A → T`, and the structure map of `A` to the structure map
of `T` composed with `A → T`. Then there is an isomorphism of `R`-algebras
`τ : T ⊗[R] A ≃ A ⊗[R] T` with `τ (algebraMap A T a ⊗ b) = a ⊗ algebraMap A T b`.

That last equation is exactly the hypothesis `hτ` of `ModuleCat.algebraTransition`: it says that
`τ` is an isomorphism over `A ⊗[R] A`, since a ring homomorphism out of `T ⊗[R] A` is
`A ⊗[R] A`-linear precisely when it agrees with the structure morphisms on the elements
`algebraMap A T a ⊗ b`, which generate the image of `A ⊗[R] A`. -/
theorem exists_transition_of_isPushout
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    {Q₁ Q₂ : CommRingCat.{u}}
    {i₁ : CommRingCat.of T ⟶ Q₁} {j₁ : CommRingCat.of A ⟶ Q₁}
    (po₁ : IsPushout (ofHom (algebraMap R T)) (ofHom (algebraMap R A)) i₁ j₁)
    {i₂ : CommRingCat.of A ⟶ Q₂} {j₂ : CommRingCat.of T ⟶ Q₂}
    (po₂ : IsPushout (ofHom (algebraMap R A)) (ofHom (algebraMap R T)) i₂ j₂)
    (χ : Q₁ ≅ Q₂)
    (h1 : ofHom (algebraMap A T) ≫ i₁ ≫ χ.hom = i₂)
    (h2 : j₁ ≫ χ.hom = ofHom (algebraMap A T) ≫ j₂) :
    ∃ τ : (T ⊗[R] A) ≃ₐ[R] (A ⊗[R] T),
      ∀ a b : A, τ (algebraMap A T a ⊗ₜ[R] b) = a ⊗ₜ[R] algebraMap A T b := by
  have pt₁ := CommRingCat.isPushout_tensorProduct R T A
  have pt₂ := CommRingCat.isPushout_tensorProduct R A T
  set κ₁ := po₁.isoIsPushout (CommRingCat.of T) (CommRingCat.of A) pt₁ with hκ₁
  set κ₂ := po₂.isoIsPushout (CommRingCat.of A) (CommRingCat.of T) pt₂ with hκ₂
  set ϑ : CommRingCat.of (T ⊗[R] A) ≅ CommRingCat.of (A ⊗[R] T) := κ₁.symm ≪≫ χ ≪≫ κ₂ with hϑ
  set f : (T ⊗[R] A) ≃+* (A ⊗[R] T) := ϑ.commRingCatIsoToRingEquiv with hf
  have step : ∀ {X : CommRingCat.{u}} (g : X ⟶ Q₁) (g' : X ⟶ CommRingCat.of (T ⊗[R] A)),
      g ≫ κ₁.hom = g' →
      g' ≫ ϑ.hom = g ≫ χ.hom ≫ κ₂.hom := by
    intro _ g _ rfl
    rw [hϑ]; simp
  have eval : ∀ (g : CommRingCat.of A ⟶ CommRingCat.of (T ⊗[R] A))
      (g' : CommRingCat.of A ⟶ CommRingCat.of (A ⊗[R] T)),
      g ≫ ϑ.hom = g' → ∀ a, f (g a) = g' a := by
    rintro g _ rfl a
    rfl
  have key1 : ∀ a : A, f (algebraMap A T a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : T) := by
    intro a
    have hmain : (ofHom (algebraMap A T) ≫
        ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := T) (B := A))) ≫ ϑ.hom
        = ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := T)) := by
      rw [Category.assoc, step _ _ (po₁.inl_isoIsPushout_hom _ _ pt₁)]
      simpa only [← Category.assoc, h1] using po₂.inl_isoIsPushout_hom _ _ pt₂
    simpa using eval _ _ hmain a
  have key2 : ∀ a : A, f ((1 : T) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A T a := by
    intro a
    have hmain : ofHom (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := A)).toRingHom
        ≫ ϑ.hom = ofHom (algebraMap A T) ≫
          ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := T)).toRingHom := by
      rw [step _ _ (po₁.inr_isoIsPushout_hom _ _ pt₁), ← po₂.inr_isoIsPushout_hom _ _ pt₂,
        ← Category.assoc, h2, Category.assoc]
    simpa using eval _ _ hmain a
  have hτ : ∀ a b : A, f (algebraMap A T a ⊗ₜ[R] b) = a ⊗ₜ[R] algebraMap A T b := by
    intro a b
    have hmul : (algebraMap A T a ⊗ₜ[R] b : T ⊗[R] A)
        = (algebraMap A T a ⊗ₜ[R] (1 : A)) * ((1 : T) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hmul, map_mul, key1, key2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨AlgEquiv.ofRingEquiv (f := f) ?_, hτ⟩
  intro r
  have h0 : (algebraMap R (T ⊗[R] A)) r = algebraMap A T (algebraMap R A r) ⊗ₜ[R] (1 : A) := by
    rw [← IsScalarTower.algebraMap_apply R A T]
    rfl
  rw [h0, hτ]
  simp

/-- The isomorphism of rings of global sections induced by an isomorphism of schemes. -/
noncomputable def Scheme.appTopIso {X Y : Scheme.{u}} (e : X ≅ Y) : Γ(X, ⊤) ≅ Γ(Y, ⊤) where
  hom := e.inv.appTop
  inv := e.hom.appTop
  hom_inv_id := by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; simp
  inv_hom_id := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp

/-- **The transition isomorphism of a scheme-level descent datum of affine schemes.** Let
`Q : Sc ⟶ Sa` and `W : Sv ⟶ Sc` be morphisms of affine schemes, presented on global sections as a
tower of rings. Let `P₁` present `Sv ×_{Sa} Sc` and `P₂` present `Sc ×_{Sa} Sv`, and let
`φ : P₁ ≅ P₂` be an isomorphism lying over `Sc ×_{Sa} Sc`, i.e. matching the first projection of
`P₂` with `W` after the first projection of `P₁` and conversely. Then the induced map on global
sections is a transition isomorphism `Γ(Sv) ⊗ Γ(Sc) ≃ Γ(Sc) ⊗ Γ(Sv)` in the sense of
`ModuleCat.algebraTransition`.

This is the step of the proof of Stacks 0245 which reads the isomorphism `φ` of the descent datum
as an isomorphism of rings `φ^♯` over `Γ(Sc) ⊗ Γ(Sc)`. -/
theorem exists_transition_of_isPullback
    {Sa Sc Sv P₁ P₂ : Scheme.{u}} [IsAffine Sa] [IsAffine Sc] [IsAffine Sv]
    {Q : Sc ⟶ Sa} {W : Sv ⟶ Sc}
    [Algebra ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤)] [Algebra ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)]
    [Algebra ↥Γ(Sa, ⊤) ↥Γ(Sv, ⊤)] [IsScalarTower ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)]
    (hQ : algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) = Q.appTop.hom)
    (hW : algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) = W.appTop.hom)
    {π₁ : P₁ ⟶ Sv} {π₂ : P₁ ⟶ Sc} (sq₁ : IsPullback π₁ π₂ (W ≫ Q) Q)
    {ρ₁ : P₂ ⟶ Sc} {ρ₂ : P₂ ⟶ Sv} (sq₂ : IsPullback ρ₁ ρ₂ Q (W ≫ Q))
    (φ : P₁ ≅ P₂) (h1 : φ.hom ≫ ρ₁ = π₁ ≫ W) (h2 : φ.hom ≫ ρ₂ ≫ W = π₂) :
    ∃ τ : (↥Γ(Sv, ⊤) ⊗[↥Γ(Sa, ⊤)] ↥Γ(Sc, ⊤)) ≃ₐ[↥Γ(Sa, ⊤)]
        (↥Γ(Sc, ⊤) ⊗[↥Γ(Sa, ⊤)] ↥Γ(Sv, ⊤)),
      ∀ x y : ↥Γ(Sc, ⊤),
        τ (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) x ⊗ₜ[↥Γ(Sa, ⊤)] y)
          = x ⊗ₜ[↥Γ(Sa, ⊤)] algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) y := by
  have hQ' : (ofHom (algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤)) : Γ(Sa, ⊤) ⟶ Γ(Sc, ⊤)) = Q.appTop := by
    rw [hQ]; rfl
  have hW' : (ofHom (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sc, ⊤) ⟶ Γ(Sv, ⊤)) = W.appTop := by
    rw [hW]; rfl
  have hRT : (ofHom (algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sa, ⊤) ⟶ Γ(Sv, ⊤)) = (W ≫ Q).appTop := by
    rw [Scheme.Hom.comp_appTop, ← hQ', ← hW', ← ofHom_comp]
    congr 1
    ext x
    exact IsScalarTower.algebraMap_apply _ _ _ x
  have po₁ := isPushout_appTop_of_isPullback sq₁
  have po₂ := isPushout_appTop_of_isPullback sq₂
  rw [← hRT, ← hQ'] at po₁
  rw [← hRT, ← hQ'] at po₂
  refine exists_transition_of_isPushout po₁ po₂ (Scheme.appTopIso φ) ?_ ?_
  · have hr : ρ₁ = φ.inv ≫ π₁ ≫ W := by rw [← h1, Iso.inv_hom_id_assoc]
    rw [hW']
    show W.appTop ≫ π₁.appTop ≫ φ.inv.appTop = ρ₁.appTop
    rw [hr, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc]
  · have hr : ρ₂ ≫ W = φ.inv ≫ π₂ := by rw [← h2, Iso.inv_hom_id_assoc]
    rw [hW']
    show π₂.appTop ≫ φ.inv.appTop = W.appTop ≫ ρ₂.appTop
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hr]

/-! ### The scheme-level descent datum of a presheaf-level one -/

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}

/-- **The source of a representable descent datum is representable.** If `r : A₀ ⟶ yoneda.obj c`
is representable then `A₀` is the presheaf represented by the base change of the datum along the
identity of `yoneda.obj c`.

The representing object is produced in this form, rather than by naming one directly, so that the
two base changes to `c ×_a c` of
`AlgebraicGeometry.Space.exists_affineDescentDatum_of_isPullback` are the same construction
applied to the two projections. -/
noncomputable def descentObjIso (hrep : yoneda.relativelyRepresentable r) :
    A₀ ≅ yoneda.obj (hrep.pullback (𝟙 (yoneda.obj c))) :=
  (IsPullback.id_horiz r).isoIsPullback A₀ (yoneda.obj c) (hrep.isPullback (𝟙 _))

/-- The isomorphism `AlgebraicGeometry.Space.descentObjIso` lies over `c`: followed by the
projection `hrep.snd (𝟙 _)` of the representing object to `c`, it is `r`. -/
@[simp]
lemma descentObjIso_hom_comp (hrep : yoneda.relativelyRepresentable r) :
    (descentObjIso hrep).hom ≫ yoneda.map (hrep.snd (𝟙 (yoneda.obj c))) = r :=
  (IsPullback.id_horiz r).isoIsPullback_hom_snd _ _ (hrep.isPullback (𝟙 _))

/-- **The base change of a representable descent datum along a morphism of the site is a Cartesian
square of the site.** The base change of `r` along `yoneda.map g` for `g : d ⟶ c`, which is an
object of the site because `r` is representable, is the fibre product of `d` with the representing
object of `A₀` over `c`. -/
theorem isPullback_descentBaseChange (hrep : yoneda.relativelyRepresentable r)
    {d : BigFppfOver B S hS} (g : d ⟶ c) :
    IsPullback (yoneda.preimage (hrep.fst (yoneda.map g) ≫ (descentObjIso hrep).hom))
      (hrep.snd (yoneda.map g)) (hrep.snd (𝟙 (yoneda.obj c))) g := by
  have sq2 : IsPullback (descentObjIso hrep).hom r
      (yoneda.map (hrep.snd (𝟙 (yoneda.obj c)))) (𝟙 (yoneda.obj c)) :=
    IsPullback.of_horiz_isIso ⟨by rw [descentObjIso_hom_comp, Category.comp_id]⟩
  have hp := (hrep.isPullback (yoneda.map g)).paste_horiz sq2
  rw [Category.comp_id] at hp
  refine IsPullback.of_map_of_faithful yoneda ?_
  rwa [Functor.map_preimage]

/-- **The comparison isomorphism of a descent datum.** Let `m, r` present `A₀` as the base change
of `f` along `yoneda.map q ≫ h` with `r` representable, and let `g₁, g₂ : d ⟶ c` be two morphisms
of the site which agree after `q`. Then the two base changes of the datum along `g₁` and `g₂` are
isomorphic over `d`.

This is the descent datum of Stacks 0245: it is not extra data, because both base changes are base
changes of the *same* morphism `f` along the *same* morphism `yoneda.map (g₁ ≫ q) ≫ h` of
presheaves, so `CategoryTheory.IsPullback.isoIsPullback` applies. -/
theorem exists_descentIso_of_isPullback (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hrep : yoneda.relativelyRepresentable r)
    {d : BigFppfOver B S hS} (g₁ g₂ : d ⟶ c) (hg : g₁ ≫ q = g₂ ≫ q) :
    ∃ φ : hrep.pullback (yoneda.map g₁) ≅ hrep.pullback (yoneda.map g₂),
      φ.hom ≫ hrep.snd (yoneda.map g₂) = hrep.snd (yoneda.map g₁) := by
  have big : ∀ g : d ⟶ c,
      IsPullback (hrep.fst (yoneda.map g) ≫ m)
        (yoneda.map (hrep.snd (yoneda.map g))) f (yoneda.map g ≫ yoneda.map q ≫ h) :=
    fun g => (hrep.isPullback (yoneda.map g)).paste_horiz sq
  have hcond : yoneda.map g₁ ≫ yoneda.map q ≫ h = yoneda.map g₂ ≫ yoneda.map q ≫ h := by
    rw [← Category.assoc, ← Functor.map_comp, hg, Functor.map_comp, Category.assoc]
  have e1 : IsPullback (hrep.fst (yoneda.map g₁) ≫ m)
      (yoneda.map (hrep.snd (yoneda.map g₁))) f (yoneda.map g₂ ≫ yoneda.map q ≫ h) :=
    hcond ▸ big g₁
  set θ := e1.isoIsPullback X (yoneda.obj d) (big g₂) with hθ
  have hθs : θ.hom ≫ yoneda.map (hrep.snd (yoneda.map g₂))
      = yoneda.map (hrep.snd (yoneda.map g₁)) := e1.isoIsPullback_hom_snd _ _ (big g₂)
  set pre := yoneda.preimage θ.hom with hpre
  have hmap : yoneda.map pre = θ.hom := yoneda.map_preimage _
  have hiso : IsIso pre := by
    have h' : IsIso (yoneda.map pre) := by rw [hmap]; infer_instance
    exact isIso_of_reflects_iso _ yoneda
  refine ⟨asIso pre, yoneda.map_injective ?_⟩
  rw [Functor.map_comp, asIso_hom, hmap, hθs]

/-- **The presheaf-level datum of a representable morphism is a scheme-level descent datum.**
Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let
`h : yoneda.obj a ⟶ Y`, let `q : c ⟶ a` be a morphism of the site, and let `m, r` present `A₀`
as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by morphisms with
`P`. Then there are an object `v` of the site, a morphism `w : v ⟶ c` with `P`, an isomorphism
`A₀ ≅ yoneda.obj v` identifying `r` with `w`, and a descent datum on `w`: an isomorphism `φ`
between the fibre products `v ×_a c` and `c ×_a v` lying over `c ×_a c`.

This is the first half of the proof of Stacks 0245, and nothing in it is particular to the
affine case: the datum `(V, φ)` is read off from the Cartesian square, with `φ` the comparison
isomorphism `AlgebraicGeometry.Space.exists_descentIso_of_isPullback`. The affine case
`AlgebraicGeometry.Space.exists_affineDescentDatum_of_isPullback` only adds that `v` is then an
affine scheme, and the quasi-affine case
`AlgebraicGeometry.Space.exists_quasiAffineDescentAction_of_isPullback` of
`StacksDraft.AlgebraicGeometry.Descent.QuasiAffineHomDescentCocycle` adds nothing at all. -/
theorem exists_descentDatum_of_isPullback {P : MorphismProperty Scheme.{u}}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf r) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      P ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₁ P₂ : BigFppfOver B S hS) (π₁ : P₁ ⟶ v) (π₂ : P₁ ⟶ c)
        (ρ₁ : P₂ ⟶ c) (ρ₂ : P₂ ⟶ v) (φ : P₁ ≅ P₂),
        IsPullback π₁ π₂ (w ≫ q) q ∧ IsPullback ρ₁ ρ₂ q (w ≫ q) ∧
        φ.hom ≫ ρ₁ = π₁ ≫ w ∧ φ.hom ≫ ρ₂ ≫ w = π₂ := by
  have hrep := hr.rep
  have hsq : IsPullback (pullback.fst q q) (pullback.snd q q) q q := IsPullback.of_hasPullback q q
  have b₁ := isPullback_descentBaseChange hrep (pullback.fst q q)
  have b₂ := isPullback_descentBaseChange hrep (pullback.snd q q)
  obtain ⟨φ, hφ⟩ := exists_descentIso_of_isPullback sq hrep (pullback.fst q q)
    (pullback.snd q q) pullback.condition
  refine ⟨_, hrep.snd (𝟙 (yoneda.obj c)), descentObjIso hrep,
    hr.property_snd (𝟙 (yoneda.obj c)), descentObjIso_hom_comp hrep,
    _, _, _, _, _, _, φ, (b₁.flip.paste_horiz hsq.flip).flip, b₂.flip.paste_horiz hsq, ?_, ?_⟩
  · rw [← Category.assoc, hφ, b₁.w]
  · rw [b₂.w, ← Category.assoc, hφ]

/-- **The presheaf-level datum of an affine morphism is a scheme-level descent datum.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y`,
let `q : c ⟶ a` be a morphism of the site with `c` affine, and let `m, r` present `A₀` as the base
change of `f` along `yoneda.map q ≫ h`, with that base change affine. Then there are an object `v`
of the site, affine and affine over `c`, an isomorphism `A₀ ≅ yoneda.obj v` identifying `r` with
the structure morphism `w : v ⟶ c`, and a descent datum on `w`: an isomorphism `φ` between the
fibre products `v ×_a c` and `c ×_a v` lying over `c ×_a c`.

This is the first half of the proof of Stacks 0245 in the affine case: the datum `(V, φ)` with `V`
affine over `X = Spec A` is read off from the Cartesian square, with `V = Spec B` by Stacks 01S6
and `φ` the comparison isomorphism
`AlgebraicGeometry.Space.exists_descentIso_of_isPullback`. The second half — turning `φ` into an
isomorphism of rings over `Γ(c) ⊗ Γ(c)` — is
`AlgebraicGeometry.exists_transition_of_isPullback`. -/
theorem exists_affineDescentDatum_of_isPullback
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c)) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      IsAffine ((BigFppfOver.toScheme B S hS).obj v) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₁ P₂ : BigFppfOver B S hS) (π₁ : P₁ ⟶ v) (π₂ : P₁ ⟶ c)
        (ρ₁ : P₂ ⟶ c) (ρ₂ : P₂ ⟶ v) (φ : P₁ ≅ P₂),
        IsPullback π₁ π₂ (w ≫ q) q ∧ IsPullback ρ₁ ρ₂ q (w ≫ q) ∧
        φ.hom ≫ ρ₁ = π₁ ≫ w ∧ φ.hom ≫ ρ₂ ≫ w = π₂ := by
  obtain ⟨v, w, e, hwaff, hew, rest⟩ := exists_descentDatum_of_isPullback sq hr
  have _ := hc
  have _ := hwaff
  exact ⟨v, w, e, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map w), hwaff, hew,
    rest⟩

end Space

end AlgebraicGeometry

end
