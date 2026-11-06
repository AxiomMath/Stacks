module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.RingTheory.Derivation.Basic
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Infinitesimal automorphisms of an object

The relative infinitesimal automorphisms of a morphism in a category cofibered in groupoids
(Tag 06JP), the canonical retraction from a chosen pushforward to the dual numbers, canonical
dual-number pairs, and the infinitesimal automorphisms of an object (Tag 06JQ).
-/

@[expose] public section

namespace Deformation

/-! ### Relative infinitesimal automorphisms -/

section
open CategoryTheory
universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
  {p : F ⥤ C} {A' A : C} {x' : p.Fiber A'} {x : p.Fiber A}


/-- The endomorphism of the target induced by a fibre automorphism of the
source of a morphism in a category cofibered in groupoids. -/
@[implicit_reducible]
public noncomputable def pushforwardEndomorphism
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a : Aut x') : x.1 ⟶ x.1 := by
  letI := hf
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hp g f hf
  letI : p.IsHomLift (𝟙 A') a.asIso.hom.val := a.asIso.hom.2
  letI : p.IsHomLift g (a.asIso.hom.val ≫ f) :=
    IsHomLift.comp_lift_id_left p g f a.asIso.hom.val
  exact Functor.IsStronglyCocartesian.map p g f
    (Category.comp_id g).symm (a.asIso.hom.val ≫ f)

public instance pushforwardEndomorphism_isHomLift
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a : Aut x') :
    p.IsHomLift (𝟙 A) (pushforwardEndomorphism hp g f hf a) := by
  dsimp [pushforwardEndomorphism]
  infer_instance

/-- The induced endomorphism is uniquely characterized by this commuting
square. -/
@[reassoc]
public lemma hom_comp_eq_comp_pushforwardEndomorphism
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a : Aut x') :
    a.asIso.hom.val ≫ f = f ≫ pushforwardEndomorphism hp g f hf a := by
  let := hf
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g f hf
  let : p.IsHomLift (𝟙 A') a.asIso.hom.val := a.asIso.hom.2
  let : p.IsHomLift g (a.asIso.hom.val ≫ f) :=
    IsHomLift.comp_lift_id_left p g f a.asIso.hom.val
  exact (Functor.IsStronglyCocartesian.fac p g f
    (Category.comp_id g).symm (a.asIso.hom.val ≫ f)).symm

/-- The induced endomorphism is the identity when the automorphism fixes `f`. -/
private lemma pushforwardEndomorphism_eq_id_of_comp_eq
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a : Aut x') (h : a.asIso.hom.val ≫ f = f) :
    pushforwardEndomorphism hp g f hf a = 𝟙 x.1 := by
  let := hf
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g f hf
  let := pushforwardEndomorphism_isHomLift hp g f hf a
  let : p.IsHomLift (𝟙 A) (𝟙 x.1) := IsHomLift.id x.2
  apply Functor.IsStronglyCocartesian.ext p g f (𝟙 A)
  rw [← hom_comp_eq_comp_pushforwardEndomorphism hp g f hf a, h]
  simp

private lemma pushforwardEndomorphism_one
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) :
    pushforwardEndomorphism hp g f hf 1 = 𝟙 x.1 :=
  pushforwardEndomorphism_eq_id_of_comp_eq hp g f hf 1 (Category.id_comp f)

private lemma pushforwardEndomorphism_mul
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a b : Aut x') :
    pushforwardEndomorphism hp g f hf (a * b) =
      pushforwardEndomorphism hp g f hf b ≫ pushforwardEndomorphism hp g f hf a := by
  let := hf
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g f hf
  let := pushforwardEndomorphism_isHomLift hp g f hf (a * b)
  let := pushforwardEndomorphism_isHomLift hp g f hf a
  let := pushforwardEndomorphism_isHomLift hp g f hf b
  let : p.IsHomLift (𝟙 A) (pushforwardEndomorphism hp g f hf b ≫
      pushforwardEndomorphism hp g f hf a) := by
    simpa using IsHomLift.comp p (𝟙 A) (𝟙 A)
      (pushforwardEndomorphism hp g f hf b)
      (pushforwardEndomorphism hp g f hf a)
  apply Functor.IsStronglyCocartesian.ext p g f (𝟙 A)
  rw [← hom_comp_eq_comp_pushforwardEndomorphism hp g f hf (a * b)]
  show (b.asIso.hom.val ≫ a.asIso.hom.val) ≫ f =
    f ≫ (pushforwardEndomorphism hp g f hf b ≫
      pushforwardEndomorphism hp g f hf a)
  rw [Category.assoc, hom_comp_eq_comp_pushforwardEndomorphism hp g f hf a,
    ← Category.assoc, hom_comp_eq_comp_pushforwardEndomorphism hp g f hf b,
    Category.assoc]

/-- The fibre automorphism of the target induced by a fibre automorphism of
the source. -/
@[implicit_reducible]
public noncomputable def pushforwardAutomorphism
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a : Aut x') : Aut x := .of
  { hom := ⟨pushforwardEndomorphism hp g f hf a,
      pushforwardEndomorphism_isHomLift hp g f hf a⟩
    inv := ⟨pushforwardEndomorphism hp g f hf a⁻¹,
      pushforwardEndomorphism_isHomLift hp g f hf a⁻¹⟩
    hom_inv_id := by
      apply Functor.Fiber.hom_ext
      change pushforwardEndomorphism hp g f hf a ≫
        pushforwardEndomorphism hp g f hf a⁻¹ = 𝟙 x.1
      rw [← pushforwardEndomorphism_mul hp g f hf a⁻¹ a,
        inv_mul_cancel, pushforwardEndomorphism_one]
    inv_hom_id := by
      apply Functor.Fiber.hom_ext
      change pushforwardEndomorphism hp g f hf a⁻¹ ≫
        pushforwardEndomorphism hp g f hf a = 𝟙 x.1
      rw [← pushforwardEndomorphism_mul hp g f hf a a⁻¹,
        mul_inv_cancel, pushforwardEndomorphism_one] }

/-- Pushing fibre automorphisms forward along a morphism is a group
homomorphism. -/
@[implicit_reducible]
public noncomputable def pushforwardAutomorphismHom
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) : Aut x' →* Aut x where
  toFun := pushforwardAutomorphism hp g f hf
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    change pushforwardEndomorphism hp g f hf 1 = 𝟙 x.1
    exact pushforwardEndomorphism_one hp g f hf
  map_mul' a b := by
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    change pushforwardEndomorphism hp g f hf (a * b) =
      pushforwardEndomorphism hp g f hf b ≫ pushforwardEndomorphism hp g f hf a
    exact pushforwardEndomorphism_mul hp g f hf a b

/-- The group of infinitesimal automorphisms of `x'` relative to `x` along
`f : x' ⟶ x`: the kernel of the canonical homomorphism between the two fibre
automorphism groups. -/
@[stacks 06JP]
public noncomputable def relativeInfinitesimalAutomorphisms
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) : Subgroup (Aut x') :=
  MonoidHom.ker (pushforwardAutomorphismHom hp g f hf)

public lemma mem_relativeInfinitesimalAutomorphisms
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a : Aut x') :
    a ∈ relativeInfinitesimalAutomorphisms hp g f hf ↔
      pushforwardAutomorphismHom hp g f hf a = 1 :=
  Iff.rfl

@[simp]
public lemma mem_relativeInfinitesimalAutomorphisms_iff
    (hp : IsCofiberedInGroupoids p) (g : A' ⟶ A) (f : x'.1 ⟶ x.1)
    (hf : p.IsHomLift g f) (a : Aut x') :
    a ∈ relativeInfinitesimalAutomorphisms hp g f hf ↔ a.asIso.hom.val ≫ f = f := by
  rw [mem_relativeInfinitesimalAutomorphisms]
  constructor
  · intro h
    have hhom := congrArg (fun b : Aut x ↦ b.asIso.hom.val) h
    change pushforwardEndomorphism hp g f hf a = 𝟙 x.1 at hhom
    rw [hom_comp_eq_comp_pushforwardEndomorphism hp g f hf a, hhom, Category.comp_id]
  · intro h
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    exact pushforwardEndomorphism_eq_id_of_comp_eq hp g f hf a h

end

/-! ### Infinitesimal automorphisms of an object -/

section
open CategoryTheory
universe v₁ v₂ u₁ u₂ u v w

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
  {p : F ⥤ C} {A₀ Aε : C} {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}

/-- The canonical map back from a chosen pushforward along a split inclusion. -/
@[implicit_reducible]
public noncomputable def canonicalRetraction
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hge : g ≫ e = 𝟙 A₀)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) :
    { r : xε.1 ⟶ x₀.1 // p.IsHomLift e r ∧ i ≫ r = 𝟙 x₀.1 } := by
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hp g i hi
  letI : p.IsHomLift (𝟙 A₀) (𝟙 x₀.1) := IsHomLift.id x₀.2
  exact ⟨Functor.IsStronglyCocartesian.map p g i hge.symm (𝟙 x₀.1), inferInstance,
    Functor.IsStronglyCocartesian.fac p g i hge.symm (𝟙 x₀.1)⟩

/-- The infinitesimal automorphisms of an object, relative to a chosen pushforward
along a split inclusion. -/
public noncomputable abbrev infinitesimalAutomorphismsAlongSplitPair
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hge : g ≫ e = 𝟙 A₀)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) : Subgroup (Aut xε) :=
  relativeInfinitesimalAutomorphisms hp e
    (canonicalRetraction hp g e hge i hi).1
    (canonicalRetraction hp g e hge i hi).2.1

/-- An infinitesimal automorphism is precisely one that commutes with the
canonical map back to the original object. -/
public theorem mem_infinitesimalAutomorphismsAlongSplitPair_iff
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hge : g ≫ e = 𝟙 A₀)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) (a : Aut xε) :
    a ∈ infinitesimalAutomorphismsAlongSplitPair hp g e hge i hi ↔
      a.asIso.hom.val ≫ (canonicalRetraction hp g e hge i hi).1 =
        (canonicalRetraction hp g e hge i hi).1 :=
  mem_relativeInfinitesimalAutomorphisms_iff hp e
    (canonicalRetraction hp g e hge i hi).1
    (canonicalRetraction hp g e hge i hi).2.1 a

/-- A presentation of the constant inclusion and projection between `k` and its dual
numbers in the category of Artinian local algebras. -/
public def IsCanonicalDualNumberPair
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) : Prop :=
  ∃ (i₀ : A₀ ≃ₐ[Λ] k) (iε : Aε ≃ₐ[Λ] DualNumber k),
    (iε.toAlgHom.comp g.hom =
      (TrivSqZeroExt.inlAlgHom Λ k k).comp i₀.toAlgHom) ∧
    (i₀.toAlgHom.comp e.hom =
      (TrivSqZeroExt.fstHom Λ k k).comp iε.toAlgHom) ∧
    (g ≫ e = 𝟙 A₀)

/-- The constant inclusion followed by the dual-number projection is the identity. -/
public theorem IsCanonicalDualNumberPair.split
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {g : A₀ ⟶ Aε} {e : Aε ⟶ A₀}
    (h : IsCanonicalDualNumberPair g e) : g ≫ e = 𝟙 A₀ := by
  obtain ⟨-, -, -, -, hge⟩ := h
  exact hge

/-- An object of `𝒞_Λ` carrying a presentation as the constant inclusion into the dual numbers
is a field, so its maximal ideal vanishes. -/
public theorem maximalIdeal_eq_bot_of_isCanonicalDualNumberPair
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {g : A₀ ⟶ Aε} {e : Aε ⟶ A₀}
    (hpair : IsCanonicalDualNumberPair g e) : IsLocalRing.maximalIdeal A₀ = ⊥ := by
  obtain ⟨i₀, -, -, -, -⟩ := hpair
  rw [← IsLocalRing.isField_iff_maximalIdeal_eq]
  exact MulEquiv.isField (Field.toIsField k) i₀.toMulEquiv

/-- The group of infinitesimal automorphisms at a point, for a chosen pushforward
along the constant inclusion into the dual numbers. -/
@[stacks 06JQ "infinitesimal automorphism group"]
public noncomputable abbrev infinitesimalAutomorphisms
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) : Subgroup (Aut xε) :=
  infinitesimalAutomorphismsAlongSplitPair hp g e hpair.split i hi

/-- Membership in the pointwise infinitesimal automorphism group means that an
automorphism commutes with the canonical map back to the point. -/
@[simp]
public theorem mem_infinitesimalAutomorphisms_iff
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) (a : Aut xε) :
    a ∈ infinitesimalAutomorphisms hp g e hpair i hi ↔
      a.asIso.hom.val ≫ (canonicalRetraction hp g e hpair.split i hi).1 =
        (canonicalRetraction hp g e hpair.split i hi).1 :=
  mem_infinitesimalAutomorphismsAlongSplitPair_iff hp g e hpair.split i hi a

private theorem canonicalDualNumberHom_unique
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {g : A₀ ⟶ Aε} {e : Aε ⟶ A₀}
    (hpair : IsCanonicalDualNumberPair g e) (f : Aε ⟶ A₀)
    (hgf : g ≫ f = 𝟙 A₀) : f = e := by
  rcases hpair with ⟨i₀, iε, hg, he, hge⟩
  apply ArtinianLocalAlgCat.hom_ext
  let φ : DualNumber k →ₐ[Λ] k :=
    (i₀.toAlgHom.comp f.hom).comp iε.symm.toAlgHom
  have hφ : φ DualNumber.eps = 0 := by
    apply eq_zero_of_mul_self_eq_zero
    simpa only [map_mul, map_zero] using congrArg φ (DualNumber.eps_mul_eps (R := k))
  have hgf' : f.hom.comp g.hom = AlgHom.id Λ A₀ := by
    simpa using congrArg (fun q : A₀ ⟶ A₀ => q.hom) hgf
  have hφinl : φ.comp (TrivSqZeroExt.inlAlgHom Λ k k) = AlgHom.id Λ k := by
    ext a
    show i₀ (f.hom (iε.symm (TrivSqZeroExt.inlAlgHom Λ k k a))) = a
    have hga := congrArg (fun q : A₀ →ₐ[Λ] DualNumber k => q (i₀.symm a)) hg
    change iε (g.hom (i₀.symm a)) = TrivSqZeroExt.inlAlgHom Λ k k
      (i₀ (i₀.symm a)) at hga
    have ha : iε.symm (TrivSqZeroExt.inlAlgHom Λ k k a) = g.hom (i₀.symm a) := by
      simpa using (congrArg (fun z : DualNumber k => iε.symm z) hga).symm
    rw [ha]
    have hfg := congrArg (fun q : A₀ →ₐ[Λ] A₀ => q (i₀.symm a)) hgf'
    change f.hom (g.hom (i₀.symm a)) = i₀.symm a at hfg
    rw [hfg]
    simp
  have hφbase : φ.toRingHom.comp (algebraMap k (DualNumber k)) =
      (TrivSqZeroExt.fstHom Λ k k).toRingHom.comp (algebraMap k (DualNumber k)) := by
    ext a
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using congrArg (fun q : k →ₐ[Λ] k => q a) hφinl
  have hφfstRing : φ.toRingHom = (TrivSqZeroExt.fstHom Λ k k).toRingHom :=
    DualNumber.ringHom_ext hφbase (by simpa using hφ)
  have hφfst : φ = TrivSqZeroExt.fstHom Λ k k :=
    AlgHom.ext fun z => congrArg (fun q : DualNumber k →+* k => q z) hφfstRing
  ext x
  have hx₁ := congrArg (fun q : DualNumber k →ₐ[Λ] k => q (iε x)) hφfst
  have hx₂ := congrArg (fun q : Aε →ₐ[Λ] k => q x) he
  apply i₀.injective
  simpa [φ] using hx₁.trans hx₂.symm

/-- A chosen pushforward along the constant inclusion into the dual numbers has a
unique retraction, without a restriction on the image of that retraction in the base. -/
@[stacks 06JQ "unique map back"]
public theorem existsUnique_retraction
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i) :
    ∃! r : xε.1 ⟶ x₀.1, i ≫ r = 𝟙 x₀.1 := by
  let q := (canonicalRetraction hp g e hpair.split i hi).1
  have hq : i ≫ q = 𝟙 x₀.1 := (canonicalRetraction hp g e hpair.split i hi).2.2
  refine ⟨q, hq, fun r hr => ?_⟩
  let rbase : Aε ⟶ A₀ := eqToHom xε.2.symm ≫ p.map r ≫ eqToHom x₀.2
  have hgi : g = eqToHom x₀.2.symm ≫ p.map i ≫ eqToHom xε.2 :=
    IsHomLift.fac p g i
  have hrbasecomp : g ≫ rbase = 𝟙 A₀ := by
    calc
      g ≫ rbase =
          (eqToHom x₀.2.symm ≫ p.map i ≫ eqToHom xε.2) ≫
              (eqToHom xε.2.symm ≫ p.map r ≫ eqToHom x₀.2) := by
              rw [hgi]
      _ = eqToHom x₀.2.symm ≫ (p.map i ≫ p.map r) ≫ eqToHom x₀.2 := by
        simp [Category.assoc]
      _ = eqToHom x₀.2.symm ≫ 𝟙 (p.obj x₀.1) ≫ eqToHom x₀.2 := by
        rw [show p.map i ≫ p.map r = 𝟙 (p.obj x₀.1) by
          simpa using congrArg (fun f : x₀.1 ⟶ x₀.1 => p.map f) hr]
      _ = 𝟙 A₀ := by simp
  have hrbase : rbase = e := canonicalDualNumberHom_unique hpair rbase hrbasecomp
  let : p.IsHomLift e r := IsHomLift.of_fac p e r xε.2 x₀.2 hrbase.symm
  let : p.IsHomLift e q := (canonicalRetraction hp g e hpair.split i hi).2.1
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp g i hi
  exact Functor.IsStronglyCocartesian.ext (p := p) (f := g) (φ := i) (g := e)
    (ψ := r) (ψ' := q) (hr.trans hq.symm)

end

end Deformation
