module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalInverseImage

/-!
# Transport of the conormal sequence along an isomorphism of presentations

Let `R ⟶ A₁ ⟶ B` and `R ⟶ A₂ ⟶ B` be two presentations of one sheaf of commutative rings `B`
on a site, both locally surjective, and let `ψ : A₁ ≅ A₂` be an isomorphism over `R` and under
`B`. The maps of conormal sheaves and of tensor-differentials sheaves induced by a
factorisation, `Stacks.Sites.Conormal.conormalSheafMapOfFac` and
`Stacks.Sites.Conormal.tensorSheafMapOfFac`, are then isomorphisms, because they compose and
carry the identity factorisation to the identity.

This is what identifies the two terms of a conormal sequence formed from one presentation with
those formed from an isomorphic presentation. The use is the degree `-1` term of
[Stacks 08TZ]: the inverse image of the canonical presentation `A[B] ⟶ B` along a morphism of
topoi is a presentation of `f⁻¹B` isomorphic to, but not equal to, the canonical presentation
`(f⁻¹A)[f⁻¹B] ⟶ f⁻¹B`, so the conormal sheaf produced by
`Stacks.Sheaves.RingedToposModules.inverseImageConormalIso` has to be carried across that
isomorphism.

## Main definitions

* `Stacks.Sites.Conormal.conormalSheafIsoOfFac`: the induced isomorphism `I₁/I₁² ≅ I₂/I₂²`.
* `Stacks.Sites.Conormal.tensorSheafIsoOfFac`: the induced isomorphism
  `B ⊗[A₁] Ω[A₁/R] ≅ B ⊗[A₂] Ω[A₂/R]`.
* `Stacks.Sites.Conormal.conormalModuleIsoOfFac`: the first of the two at the spelling of
  `Stacks.Sites.Conormal.conormalModule`, in which the conormal sheaf is a sheaf of modules
  over the sheaf of rings underlying `B`.

## Main results

* `Stacks.Sites.Conormal.conormalSheafIsoOfFac_hom_comp_conormalSequence_f`: the two
  isomorphisms commute with the left-hand maps of the two conormal sequences.

## Implementation notes

The two inverses are the maps induced by the inverse factorisation, and the two round trips are
read off `Stacks.Sites.Conormal.conormalSheafMapOfFac_comp` and
`Stacks.Sites.Conormal.conormalSheafMapOfFac_id`. The composite of the two factorisations is
not syntactically the identity morphism, and the factorisation hypothesis is an argument of the
induced map, so rewriting the composite to the identity inside the induced map is done by the
auxiliary `Stacks.Sites.Conormal.conormalSheafMapOfFac_eq_id`, which substitutes the morphism
and then uses proof irrelevance for the hypothesis.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ), the inverse image of
  the naive cotangent complex.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Sites.Conormal

section PresentationIso

universe v u w z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R B A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

/-- A factorisation of a presentation through itself by a morphism equal to the identity
induces the identity map of conormal sheaves. -/
lemma conormalSheafMapOfFac_eq_id (ψ : A₁ ⟶ A₁) (hψ : ψ ≫ φ₁ = φ₁) (h : ψ = 𝟙 A₁) :
    conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₁ φ₁ φ₁ ψ hψ =
      𝟙 (conormalSheaf.{v, u, w, z} J A₁ B φ₁) := by
  subst h
  exact conormalSheafMapOfFac_id.{v, u, w, z} J A₁ B φ₁

/-- A factorisation of a presentation through itself over `R` by a morphism equal to the
identity induces the identity map of tensor-differentials sheaves. -/
lemma tensorSheafMapOfFac_eq_id (ψ : A₁ ⟶ A₁) (hψ : ψ ≫ φ₁ = φ₁) (ha : a₁ ≫ ψ = a₁)
    (h : ψ = 𝟙 A₁) :
    tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₁ a₁ a₁ φ₁ φ₁ ψ hψ ha =
      𝟙 (tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁) := by
  subst h
  exact tensorSheafMapOfFac_id.{v, u, w, z} J R A₁ B a₁ φ₁

variable (ψ : A₁ ≅ A₂)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom] in
/-- The factorisation of `φ₂` through `φ₁` inverse to a given factorisation of `φ₁` through
`φ₂` by an isomorphism. -/
lemma inv_comp_of_fac (hψ : ψ.hom ≫ φ₂ = φ₁) : ψ.inv ≫ φ₁ = φ₂ := by
  rw [← hψ, ← Category.assoc, ψ.inv_hom_id, Category.id_comp]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The factorisation of `a₂` through `a₁` inverse to a given factorisation of `a₁` through
`a₂` by an isomorphism. -/
lemma comp_inv_of_fac (ha : a₁ ≫ ψ.hom = a₂) : a₂ ≫ ψ.inv = a₁ := by
  rw [← ha, Category.assoc, ψ.hom_inv_id, Category.comp_id]

/-- **The conormal sheaves of two isomorphic presentations of `B` are isomorphic**:
`I₁/I₁² ≅ I₂/I₂²` for an isomorphism `ψ : A₁ ≅ A₂` of presentations under `B`. -/
noncomputable def conormalSheafIsoOfFac (hψ : ψ.hom ≫ φ₂ = φ₁) :
    conormalSheaf.{v, u, w, z} J A₁ B φ₁ ≅ conormalSheaf.{v, u, w, z} J A₂ B φ₂ where
  hom := conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ.hom hψ
  inv := conormalSheafMapOfFac.{v, u, w, z} J B A₂ A₁ φ₂ φ₁ ψ.inv
    (inv_comp_of_fac J B A₁ A₂ φ₁ φ₂ ψ hψ)
  hom_inv_id := by
    rw [conormalSheafMapOfFac_comp.{v, u, w, z} J B A₁ A₂ A₁ φ₁ φ₂ φ₁ ψ.hom ψ.inv hψ
      (inv_comp_of_fac J B A₁ A₂ φ₁ φ₂ ψ hψ)]
    exact conormalSheafMapOfFac_eq_id.{v, u, w, z} J B A₁ φ₁ _ _ ψ.hom_inv_id
  inv_hom_id := by
    rw [conormalSheafMapOfFac_comp.{v, u, w, z} J B A₂ A₁ A₂ φ₂ φ₁ φ₂ ψ.inv ψ.hom
      (inv_comp_of_fac J B A₁ A₂ φ₁ φ₂ ψ hψ) hψ]
    exact conormalSheafMapOfFac_eq_id.{v, u, w, z} J B A₂ φ₂ _ _ ψ.inv_hom_id

/-- The isomorphism of conormal sheaves is the map induced by the factorisation. -/
@[simp] lemma conormalSheafIsoOfFac_hom (hψ : ψ.hom ≫ φ₂ = φ₁) :
    (conormalSheafIsoOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).hom =
      conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ.hom hψ :=
  rfl

/-- **The tensor-differentials sheaves of two isomorphic presentations of `B` over `R` are
isomorphic**: `B ⊗[A₁] Ω[A₁/R] ≅ B ⊗[A₂] Ω[A₂/R]`. -/
noncomputable def tensorSheafIsoOfFac (hψ : ψ.hom ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ.hom = a₂) :
    tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁ ≅
      tensorDifferentialsSheaf.{v, u, w, z} J R A₂ B a₂ φ₂ where
  hom := tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ.hom hψ ha
  inv := tensorSheafMapOfFac.{v, u, w, z} J R B A₂ A₁ a₂ a₁ φ₂ φ₁ ψ.inv
    (inv_comp_of_fac J B A₁ A₂ φ₁ φ₂ ψ hψ) (comp_inv_of_fac J R A₁ A₂ a₁ a₂ ψ ha)
  hom_inv_id := by
    rw [tensorSheafMapOfFac_comp.{v, u, w, z} J R B A₁ A₂ A₁ a₁ a₂ a₁ φ₁ φ₂ φ₁ ψ.hom ψ.inv hψ
      (inv_comp_of_fac J B A₁ A₂ φ₁ φ₂ ψ hψ) ha (comp_inv_of_fac J R A₁ A₂ a₁ a₂ ψ ha)]
    exact tensorSheafMapOfFac_eq_id.{v, u, w, z} J R B A₁ a₁ φ₁ _ _ _ ψ.hom_inv_id
  inv_hom_id := by
    rw [tensorSheafMapOfFac_comp.{v, u, w, z} J R B A₂ A₁ A₂ a₂ a₁ a₂ φ₂ φ₁ φ₂ ψ.inv ψ.hom
      (inv_comp_of_fac J B A₁ A₂ φ₁ φ₂ ψ hψ) hψ (comp_inv_of_fac J R A₁ A₂ a₁ a₂ ψ ha) ha]
    exact tensorSheafMapOfFac_eq_id.{v, u, w, z} J R B A₂ a₂ φ₂ _ _ _ ψ.inv_hom_id

/-- The isomorphism of tensor-differentials sheaves is the map induced by the
factorisation. -/
@[simp] lemma tensorSheafIsoOfFac_hom (hψ : ψ.hom ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ.hom = a₂) :
    (tensorSheafIsoOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).hom =
      tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ.hom hψ ha :=
  rfl

/-- **The two transport isomorphisms commute with the left-hand maps of the two conormal
sequences**: the square identifying the conormal sequence of one presentation with that of an
isomorphic presentation. -/
lemma conormalSheafIsoOfFac_hom_comp_conormalSequence_f (hψ : ψ.hom ≫ φ₂ = φ₁)
    (ha : a₁ ≫ ψ.hom = a₂) :
    (conormalSheafIsoOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ).hom ≫
        (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f =
      (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ≫
        (tensorSheafIsoOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha).hom :=
  (conormalSequence_f_naturality.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ.hom hψ ha).symm

end PresentationIso

section ConormalModuleIso

universe t vv uu

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max uu vv t} RingCat.{max uu vv t})]
  {B A₁ A₂ : Sheaf J CommRingCat.{max uu vv t}} (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

/-- **The conormal sheaves of two isomorphic presentations of `B` are isomorphic**, at the
spelling of `Stacks.Sites.Conormal.conormalModule`: as sheaves of modules over the sheaf of
rings underlying `B`. -/
noncomputable def conormalModuleIsoOfFac (ψ : A₁ ≅ A₂) (hψ : ψ.hom ≫ φ₂ = φ₁) :
    conormalModule.{t, vv, uu} J φ₁ ≅ conormalModule.{t, vv, uu} J φ₂ :=
  conormalSheafIsoOfFac.{vv, uu, max uu vv t, t} J B A₁ A₂ φ₁ φ₂ ψ hψ

/-- The isomorphism of conormal modules is the map induced by the factorisation. -/
@[simp] lemma conormalModuleIsoOfFac_hom (ψ : A₁ ≅ A₂) (hψ : ψ.hom ≫ φ₂ = φ₁) :
    (conormalModuleIsoOfFac.{t, vv, uu} J φ₁ φ₂ ψ hψ).hom =
      conormalSheafMapOfFac.{vv, uu, max uu vv t, t} J B A₁ A₂ φ₁ φ₂ ψ.hom hψ :=
  rfl

end ConormalModuleIso

end Stacks.Sites.Conormal

end
