module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFieldExtension
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationFullyFaithful
public import StacksFrontier.Deformation.Artin.FormalObject.Realization

/-!
# The map of versal rings after a field extension, compatibly with `Spec A ⟶ 𝒳` (Stacks 0DR1)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x₀ : Spec k ⟶ 𝒳` be a point with `k` of finite type over `S`,
let `l/k` be a finite extension and `x_{l,0} : Spec l ⟶ 𝒳` the induced point. **Stacks 0DQY**
attaches to a versal ring `A` at `x₀` a versal ring `A'` at `x_{l,0}` and a formally smooth
`S`-algebra map `A → A'` inducing `l/k`. **Stacks 0DR1**, part (2), observes that this map may be
chosen compatible with the morphisms `Spec A ⟶ 𝒳` and `Spec A' ⟶ 𝒳` coming from the versal formal
objects (by Artin's Axioms, **Stacks 07X8**).

The morphisms are recorded as realizations (`Deformation.Artin.FormalObject.Realization`): an
object of `𝒳` over `Spec A` whose restrictions to the infinitesimal thickenings of the closed
point are the levels of the versal formal object. Compatibility is a morphism of `𝒳` from the
realizing object over `Spec A'` to the one over `Spec A`, lying over `Spec A' ⟶ Spec A`, i.e. a
2-arrow making the square of 1-morphisms 2-commute.

## Main results

* `Deformation.Artin.FormalObject.Realization.exists_pullback`: the pullback of a realization
  along a morphism of formal objects realizes the source.
* `AlgebraicGeometry.Stack.exists_isVersalRingAt_fieldExtension_realization`: **Stacks 0DR1**,
  part (2).

## Implementation notes

The proof is the source's ("our maps are compatible with versal formal elements"). Over a chart on
which `k` is finite, Stacks 0DQF produces the formal object of `𝓕_{l/k}` as the pushforward of the
given one (`Deformation.exists_versal_formalObject_changeOfFields_pushforward`); the restriction
functor of Stacks 07WX comes with cartesian arrows from its values down to the deformations it
restricts, and composing them with the pushforward arrows gives a morphism of formal objects over
the site, whose map of complete local bases is computed level by level to be `Spec f`. A general
chart is reduced to such a chart as in Stacks 0DQY, moving the formal objects between charts by
`AlgebraicGeometry.Stack.exists_isVersal_ofPredeformation_eq_residue_of_affineOpenPresentation`,
which keeps their formal objects over the site and their residue field identifications. Fullness
of the approximation functor (the fullness half of Stacks 07X8,
`Deformation.Artin.full_approximationFunctor_algebraicStacks`) turns the morphism of formal objects
into a morphism of realizing objects.

## References

* [Stacks Project, Tag 0DQF](https://stacks.math.columbia.edu/tag/0DQF)
* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
* [Stacks Project, Tag 0DQY](https://stacks.math.columbia.edu/tag/0DQY)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 07WX](https://stacks.math.columbia.edu/tag/07WX)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u w

namespace Deformation.Artin.FormalObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS}

/-- **Pulling a realization back along a morphism of formal objects.** In a category fibred in
groupoids, let `ψ : X ⟶ Y` be a morphism of formal objects whose map of complete local bases is
`a`, and let `y` realize `Y`. If the base of `X` belongs to the site, the pullback `x` of `y` along
`a` realizes `X`, and the cartesian arrow `x ⟶ y` lies over `a`. -/
theorem Realization.exists_pullback (hp : p.IsFiberedInGroupoids) {X Y : FormalObject B S hS p}
    (ψ : X ⟶ Y) {a : Spec (.of X.base.R) ⟶ Spec (.of Y.base.R)} (ha : ψ.IsBaseMap a)
    {hAY : B.Contains (Spec (.of Y.base.R))} {y : F}
    {hy : p.obj y = baseOver B S hS Y.base hAY} (Ry : Realization Y hAY y hy)
    (hAX : B.Contains (Spec (.of X.base.R))) :
    ∃ (x : F) (hx : p.obj x = baseOver B S hS X.base hAX), Nonempty (Realization X hAX x hx) ∧
      ∃ m : x ⟶ y,
        (BigFppfOver.toScheme B S hS).map (eqToHom hx.symm ≫ p.map m ≫ eqToHom hy) = a := by
  let g₀ : baseOver B S hS X.base hAX ⟶ baseOver B S hS Y.base hAY :=
    Over.homMk (ObjectProperty.homMk a) (by ext1; exact ha.1)
  have hg₀ : ∀ n, restrictionToBase B S hS X.base hAX X.contains n ≫ g₀ =
      (eqToHom (X.level_eq n).symm ≫ p.map (ψ.app n) ≫ eqToHom (Y.level_eq n)) ≫
        restrictionToBase B S hS Y.base hAY Y.contains n := by
    intro n
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      restrictionToBase_toScheme, restrictionToBase_toScheme]
    exact (ha.2 n).symm
  obtain ⟨x, φ, hφ⟩ := hp.exists_lift (g₀ ≫ eqToHom hy.symm) y rfl
  have hx : p.obj x = baseOver B S hS X.base hAX :=
    IsHomLift.domain_eq p (g₀ ≫ eqToHom hy.symm) φ
  have hφmap : p.map φ = eqToHom hx ≫ g₀ ≫ eqToHom hy.symm := by
    rw [IsHomLift.fac' p (g₀ ≫ eqToHom hy.symm) φ]
    simp
  let f : ∀ n, p.obj (X.level n) ⟶ p.obj x := fun n =>
    eqToHom (X.level_eq n) ≫ restrictionToBase B S hS X.base hAX X.contains n ≫ eqToHom hx.symm
  have hf : ∀ n, f n ≫ p.map φ = p.map (ψ.app n ≫ Ry.r n) := by
    intro n
    rw [hφmap, CategoryTheory.Functor.map_comp, Ry.map_eq n]
    simp only [f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (hg₀ n)]
    simp
  choose r hr using fun n => (hp.unique_lift φ (ψ.app n ≫ Ry.r n) (f n) (hf n)).exists
  have uniq : ∀ {b : F} (χ : b ⟶ y) (c₁ c₂ : b ⟶ x),
      p.map c₁ = p.map c₂ → c₁ ≫ φ = χ → c₂ ≫ φ = χ → c₁ = c₂ := by
    intro b χ c₁ c₂ hpc h₁ h₂
    obtain ⟨θ, -, hθ⟩ := hp.unique_lift φ χ (p.map c₁) (by rw [← Functor.map_comp, h₁])
    exact (hθ c₁ ⟨rfl, h₁⟩).trans (hθ c₂ ⟨hpc.symm, h₂⟩).symm
  refine ⟨x, hx, ⟨{ r := r, comp_transition := fun n => ?_, map_eq := fun n => (hr n).1 }⟩,
    φ, ?_⟩
  · refine uniq (ψ.app n ≫ Ry.r n) _ _ ?_ ?_ (hr n).2
    · rw [CategoryTheory.Functor.map_comp, (hr (n + 1)).1, (hr n).1, map_transition]
      simp only [f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% (restrictionToBase_succ B S hS X.base hAX X.contains n)]
    · rw [Category.assoc, (hr (n + 1)).2, ← Category.assoc, ψ.naturality n, Category.assoc,
        Ry.comp_transition n]
  · rw [hφmap]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc,
      Category.id_comp]
    rfl

end Deformation.Artin.FormalObject

namespace AlgebraicGeometry.Stack

section Levelwise

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {Λ : Type u₁} {k : Type u₃} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₂} [Category.{v₂} F] {G : Type v₃} [Category.{v₁} G]
  {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u₁, v₁, u₃} Λ k}
  {q : G ⥤ Deformation.ArtinianLocalAlgCat.{u₁, v₁, u₃} Λ k}

/-- A functor `φ` with `φ ⋙ q = p` sends an arrow over `f` for `p` to an arrow over `f` for
`q`. -/
private theorem isHomLift_map_of_comp_eq (φ : F ⥤ G) (hφ : φ ⋙ q = p) {a b : F}
    {A B : Deformation.ArtinianLocalAlgCat.{u₁, v₁, u₃} Λ k} {f : A ⟶ B} (g : a ⟶ b)
    (h : p.IsHomLift f g) : q.IsHomLift f (φ.map g) := by
  subst hφ
  exact IsHomLift.of_fac q f (φ.map g) (IsHomLift.domain_eq (φ ⋙ q) f g)
    (IsHomLift.codomain_eq (φ ⋙ q) f g) (IsHomLift.fac (φ ⋙ q) f g)

/-- The levelwise image of a formal object under a functor `φ` with `φ ⋙ q = p`, written with
the levels `φ.obj (X.level n)` and transitions `φ.map (X.transition n)`. -/
private theorem formalObjectMapOfCompEq_obj_eq (φ : F ⥤ G) (hφ : φ ⋙ q = p)
    (X : Deformation.FormalObject p) :
    (Deformation.formalObjectMapOfCompEq φ hφ).obj X =
      { base := X.base
        level := fun n => φ.obj (X.level n)
        level_eq := fun n => (Functor.congr_obj hφ (X.level n)).trans (X.level_eq n)
        transition := fun n => φ.map (X.transition n)
        transition_lift := fun n => isHomLift_map_of_comp_eq φ hφ _ (X.transition_lift n) } := by
  subst hφ
  rfl

end Levelwise

section SchemeMaps

/-- Identifications of an object with itself around a morphism are the identity. -/
private theorem eqToHom_comp_comp_eqToHom_self {C : Type*} [Category C] {X Y : C}
    (h₁ : X = X) (h₂ : Y = Y) (g : X ⟶ Y) : eqToHom h₁ ≫ g ≫ eqToHom h₂ = g := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The spectrum of a composite of two ring maps. -/
private theorem specMap_comp_two {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (α : R₂ →+* R₃) (β : R₁ →+* R₂) :
    Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom β) =
      Spec.map (CommRingCat.ofHom (α.comp β)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The spectrum of a composite of three ring maps. -/
private theorem specMap_comp_three {R₁ R₂ R₃ R₄ : Type u} [CommRing R₁] [CommRing R₂]
    [CommRing R₃] [CommRing R₄] (α : R₃ →+* R₄) (β : R₂ →+* R₃) (γ : R₁ →+* R₂) :
    Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom β) ≫
        Spec.map (CommRingCat.ofHom γ) =
      Spec.map (CommRingCat.ofHom ((α.comp β).comp γ)) := by
  rw [specMap_comp_two, specMap_comp_two]

/-- The scheme map underlying a composite of two arrows of a category over the big fppf site,
conjugated by identifications of objects of the site, computed from the scheme maps of the two
arrows. -/
private theorem bigFppfOver_left_hom_comp_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : Type*} [Category X] (P : X ⥤ BigFppfOver B S hS)
    {a b c : X} {Ua Ub Uc : Scheme.{u}}
    (ha : ((P ⋙ Over.post B.inclusion).obj a).left = Ua)
    (hb : ((P ⋙ Over.post B.inclusion).obj b).left = Ub)
    (hc : ((P ⋙ Over.post B.inclusion).obj c).left = Uc)
    (ρ : a ⟶ b) (σ : b ⟶ c) {α : Ua ⟶ Ub} {β : Ub ⟶ Uc}
    (hρ : eqToHom ha.symm ≫ ((P ⋙ Over.post B.inclusion).map ρ).left ≫ eqToHom hb = α)
    (hσ : eqToHom hb.symm ≫ ((P ⋙ Over.post B.inclusion).map σ).left ≫ eqToHom hc = β)
    {U₁ U₂ : BigFppfOver B S hS} (h₁ : U₁ = P.obj a) (h₂ : P.obj c = U₂) {Z : Scheme.{u}}
    (ι : U₂.left.obj ⟶ Z) (rhs : U₁.left.obj ⟶ Z)
    (H : (eqToHom ((congrArg (fun W : BigFppfOver B S hS => W.left.obj) h₁).trans ha) ≫ α ≫ β ≫
        eqToHom (hc.symm.trans (congrArg (fun W : BigFppfOver B S hS => W.left.obj) h₂))) ≫ ι =
          rhs) :
    (eqToHom h₁ ≫ P.map (ρ ≫ σ) ≫ eqToHom h₂).left.hom ≫ ι = rhs := by
  subst ha hb hc
  subst hρ hσ h₁ h₂
  rw [← H]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.map_comp, Over.comp_left]
  rfl

/-- A map of infinitesimal thickenings given by a ring map between Artinian algebras identified
with the truncations, and compatible with `f` on representatives, is the truncation of
`Spec f`. -/
private theorem specMap_truncation_eq {Λ k l : Type u} [CommRing Λ] [Field k] [Field l]
    [Algebra Λ k] [Algebra Λ l]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ l) (n : ℕ)
    {Aₓ Ay : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {Aₗ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l}
    (d : (Ay : Type u) →+* Aₗ) (r' : (Aₓ : Type u) →+* Ay) (f : (A : Type u) →+* A')
    (hx : (Deformation.AdicTruncation.functor n).obj A = Aₓ)
    (hℓ : (Deformation.AdicTruncation.functor n).obj A' = Aₗ)
    (hφ : ∀ r : A, (eqToHom hℓ.symm).hom (d (r' ((eqToHom hx).hom
      (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal A n) r :
        Deformation.AdicTruncation.obj A n)))) =
      (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal A' n) (f r) :
        Deformation.AdicTruncation.obj A' n))
    (w₁ : adicThickening A' (maximalIdeal A') n = Spec (.of Aₗ))
    (w₂ : Spec (.of Aₓ) = adicThickening A (maximalIdeal A) n) :
    (eqToHom w₁ ≫ Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom r') ≫
        eqToHom w₂) ≫ adicThickeningι A (maximalIdeal A) n =
      adicThickeningι A' (maximalIdeal A') n ≫ Spec.map (CommRingCat.ofHom f) := by
  subst hx hℓ
  have key : (d.comp r').comp (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) =
      (Ideal.Quotient.mk (maximalIdeal A' ^ (n + 1))).comp f :=
    RingHom.ext fun r => hφ r
  refine (congrArg (· ≫ adicThickeningι A (maximalIdeal A) n)
    (eqToHom_comp_comp_eqToHom_self w₁ w₂
      (Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom r')))).trans ?_
  refine ((Category.assoc _ _ _).trans (specMap_comp_three d r'
    (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))).trans ?_
  refine Eq.trans ?_ (specMap_comp_two (Ideal.Quotient.mk (maximalIdeal A' ^ (n + 1))) f).symm
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) key

/-- The ring map underlying the restriction of a changed deformation, after a morphism of
deformations, read on representatives. -/
private theorem deformationProjection_comp_apply (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
    {Px Py Aₙ Ax Ay : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {Bs Bₙ Bℓ : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (G : Px ⟶ Py) (I : Py ≅ (Deformation.comparisonFunctor T).functor.obj Bs)
    (ox : Px = Ax) (oy : Py = Ay) (lx : Px = Aₙ) (hh : Bs = Bℓ) (e : Bs = Bₙ)
    (hℓ : Bₙ = Bℓ) (z : Aₙ) :
    (eqToHom hℓ.symm).hom ((hh ▸ (Deformation.Artin.Site.comparisonProjection T Bs).comp
        (eqToHom oy.symm ≫ I.hom).hom.toRingHom : (Ay : Type u) →+* Bℓ)
      ((eqToHom ox.symm ≫ G ≫ eqToHom oy).hom ((eqToHom (lx.symm.trans ox)).hom z))) =
      ((Deformation.comparisonFunctor T).pullbackEquiv Bₙ
        ((eqToHom lx.symm ≫ G ≫ I.hom ≫
          (Deformation.comparisonFunctor T).functor.map (eqToHom e)).hom z)).val.1 := by
  subst ox oy lx hh e
  simp [Deformation.Artin.Site.comparisonProjection]

end SchemeMaps

/-- Two ring maps out of `Λ` whose spectra agree after an open immersion `Spec Λ ⟶ S` agree. -/
private theorem ringHom_eq_of_specMap_comp_eq {Λ A : Type u} [CommRing Λ] [CommRing A]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) [_root_.AlgebraicGeometry.IsOpenImmersion iΛ]
    (α β : Λ →+* A)
    (h : Spec.map (CommRingCat.ofHom α) ≫ iΛ = Spec.map (CommRingCat.ofHom β) ≫ iΛ) :
    α = β :=
  congrArg CommRingCat.Hom.hom (Spec.map_inj.mp ((cancel_mono iΛ).mp h))

/-- The inverse of `Deformation.Artin.FormalBase.ringEquivOfEq` is a cast. -/
private theorem ringEquivOfEq_symm_apply_eq_cast {S : Scheme.{u}}
    {A₁ A₂ : Deformation.Artin.FormalBase S} (h : A₁ = A₂) (a : A₂.R) :
    (Deformation.Artin.FormalBase.ringEquivOfEq h).symm a =
      cast (congrArg (fun A => A.R) h).symm a := by
  subst h
  rfl

/-- The inverse of `Deformation.Artin.FormalBase.ringEquivOfEq` is compatible with the structure
morphisms. -/
private theorem specMap_ringEquivOfEq_symm_toS {S : Scheme.{u}}
    {A₁ A₂ : Deformation.Artin.FormalBase S} (h : A₁ = A₂) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.FormalBase.ringEquivOfEq h).symm.toRingHom) ≫
      A₂.toS = A₁.toS := by
  rw [Deformation.Artin.FormalBase.ringEquivOfEq_symm]
  exact Deformation.Artin.FormalBase.specMap_ringEquivOfEq_toS h.symm

/-- A morphism of formal objects over the site conjugated by equalities of formal objects has the
conjugated map of complete local bases. -/
private theorem isBaseMap_eqToHom {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS}
    {X X' Y Y' : Deformation.Artin.FormalObject B S hS p} (hX : X' = X) (hY : Y = Y')
    (ψ : X ⟶ Y) {a : Spec (.of X.base.R) ⟶ Spec (.of Y.base.R)} (h : ψ.IsBaseMap a) :
    Deformation.Artin.FormalObject.Hom.IsBaseMap (eqToHom hX ≫ ψ ≫ eqToHom hY)
      (eqToHom (congrArg (fun Z : Deformation.Artin.FormalObject B S hS p => Spec (.of Z.base.R))
        hX) ≫ a ≫
        eqToHom (congrArg (fun Z : Deformation.Artin.FormalObject B S hS p => Spec (.of Z.base.R))
          hY)) := by
  subst hX hY
  simpa using h

section FieldExtension

variable (D : VersalSituation.{u, w})

/-- **The versal formal object of Stacks 0DQY maps to the given one over the site.** Over a chart
`Spec Λ` on which `k` is a finite module: given a versal formal object `ξ` over `A` at `x₀`, there
are a versal formal object `ξₗ` over `A'` at `x_{l,0}` and a local, formally smooth map
`f : A → A'` inducing `l/k`, together with a morphism of formal objects over the site from the
formal object of `ξₗ` to that of `ξ` whose map of complete local bases is `Spec f`. -/
private theorem exists_versal_ofPredeformation_hom_fieldExtension_of_finite
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l]
    [Algebra Λ l] [IsScalarTower Λ k l] [Module.Finite Λ k] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ) :
    ∃ (ξₗ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) xₗ hxₗ).projection)
      (f : ξ.base →ₐ[Λ] ξₗ.base),
      Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
        D.B D.hS iΛ D.𝒳.val.val.p xₗ hxₗ D.𝒳.val.property).cofibered ξₗ ∧
      IsLocalHom f.toRingHom ∧
      (∀ a : ξ.base, ξₗ.base.residueEquiv (residue ξₗ.base (f a)) =
        algebraMap k l (ξ.base.residueEquiv (residue ξ.base a))) ∧
      RingHom.FormallySmoothNAdic.{u} f.toRingHom (maximalIdeal ξₗ.base) ∧
      ∃ ψ : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p xₗ hxₗ
          (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ξₗ ⟶
        Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
          hfinite ξ,
        ψ.IsBaseMap (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  let T : Deformation.ChangeOfFieldsSituation.{u, u, u} := { Λ := Λ, k := k, l := l }
  let q := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion
  let C₀ := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let : Category C₀.carrier := C₀.category
  let Cₗ := Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
  let : Category Cₗ.carrier := Cₗ.category
  have hp₀ := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered
  have hpₗ := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p xₗ hxₗ D.𝒳.val.property).cofibered
  obtain ⟨A', f, hloc, hres, hsmooth, ξ', hT', hξ', g, hg, hgbase⟩ :=
    Deformation.exists_versal_formalObject_changeOfFields_pushforward.{u, u, u, u}
      T C₀.projection hp₀ ξ hξ
  subst hT'
  have hp : D.𝒳.val.val.p.IsFiberedInGroupoids := D.𝒳.val.property
  have hη : D.𝒳.val.val.p.IsCartesian (D.𝒳.val.val.p.map η) η :=
    (hp.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
  let Fn := Deformation.Artin.Site.changeOfFieldFunctor T iΛ D.B D.hS D.𝒳.val.val.p
    x₀ xₗ hx₀ hxₗ η hp hη hηbase
  have : Fn.toFunctor.IsEquivalence :=
    Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence T iΛ D.B D.hS D.𝒳.val.val.p
      x₀ xₗ hx₀ hxₗ η hp hη hηbase hfinite
      (Deformation.Artin.satisfiesRS_of_isAlgebraicStack D.B D.S D.hS D.𝒳)
  have hv := Deformation.isVersal_formalObjectMapOfCompEq Fn.toFunctor Fn.projection_comm
    (Deformation.changeOfFieldsProjection_isCofiberedInGroupoids T C₀.projection hp₀) hpₗ ξ' hξ'
  rw [formalObjectMapOfCompEq_obj_eq] at hv
  refine ⟨_, f, hv, hloc, hres, hsmooth, ⟨fun n => Fn.restriction (ξ'.level n) ≫
    (C₀.morphisms _ _ (g n)).arrow, fun n => ?_⟩, ?_⟩
  · change (Cₗ.morphisms _ _ (Fn.toFunctor.map (ξ'.transition n))).arrow ≫
        Fn.restriction (ξ'.level (n + 1)) ≫ (C₀.morphisms _ _ (g (n + 1))).arrow =
      (Fn.restriction (ξ'.level n) ≫ (C₀.morphisms _ _ (g n)).arrow) ≫
        (C₀.morphisms _ _ (ξ.transition n)).arrow
    rw [← Category.assoc, Fn.restriction_natural, Category.assoc, ← C₀.reversed_composition,
      hg, C₀.reversed_composition, Category.assoc]
  · refine ⟨?_, fun n => ?_⟩
    · change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ ξ'.base)) ≫ iΛ
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      exact f.comp_algebraMap
    · refine bigFppfOver_left_hom_comp_eq D.B D.S D.hS D.𝒳.val.val.p
        (congrArg Over.left (Cₗ.objects (Fn.toFunctor.obj (ξ'.level n))).base)
        (congrArg Over.left (C₀.objects (ξ'.level n).fst).base)
        (congrArg Over.left (C₀.objects (ξ.level n)).base)
        (Fn.restriction (ξ'.level n)) (C₀.morphisms _ _ (g n)).arrow
        (Fn.restriction_base (ξ'.level n)) (C₀.morphisms _ _ (g n)).arrow_base _ _ _ _ ?_
      refine specMap_truncation_eq ξ.base ξ'.base n _ _ f.toRingHom
        ((C₀.object_projection (ξ.level n)).symm.trans (ξ.level_eq n)).symm
        (((Functor.congr_obj Fn.projection_comm (ξ'.level n)).trans (ξ'.level_eq n)).symm.trans
          (Cₗ.object_projection _)) (fun r => ?_) _ _
      rw [← C₀.morphism_projection (g n)]
      exact (deformationProjection_comp_apply T (C₀.projection.map (g n)) (ξ'.level n).iso
        (C₀.object_projection (ξ.level n)) (C₀.object_projection (ξ'.level n).fst)
        (ξ.level_eq n) (Fn.algebra_eq (ξ'.level n)).symm (ξ'.level_eq n)
        (((Functor.congr_obj Fn.projection_comm (ξ'.level n)).trans (ξ'.level_eq n)).symm.trans
          (Cₗ.object_projection _)) _).trans (hgbase n r)

/-- **The versal formal object of Stacks 0DQY maps to the given one over the site**, for an
arbitrary affine chart `Spec Λ ⊆ S`: the statement over a principal open `Spec Λ_r` on which `k` is
finite (`exists_versal_ofPredeformation_hom_fieldExtension_of_finite`), with the formal objects
moved between the two charts keeping their formal objects over the site and their residue field
identifications. -/
private theorem exists_versal_ofPredeformation_hom_fieldExtension
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l]
    [Algebra Λ l] [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ) :
    ∃ (ξₗ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) xₗ hxₗ).projection)
      (f : ξ.base →ₐ[Λ] ξₗ.base),
      Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
        D.B D.hS iΛ D.𝒳.val.val.p xₗ hxₗ D.𝒳.val.property).cofibered ξₗ ∧
      IsLocalHom f.toRingHom ∧
      (∀ a : ξ.base, ξₗ.base.residueEquiv (residue ξₗ.base (f a)) =
        algebraMap k l (ξ.base.residueEquiv (residue ξ.base a))) ∧
      RingHom.FormallySmoothNAdic.{u} f.toRingHom (maximalIdeal ξₗ.base) ∧
      ∃ ψ : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p xₗ hxₗ
          (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ξₗ ⟶
        Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
          hfinite ξ,
        ψ.IsBaseMap (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  obtain ⟨r₀, -, ψ₀, hψ₀, hψ₀finite⟩ := exists_finite_localized_affineChart iΛ hfinite.1
  let R := Localization.Away r₀
  let : IsLocalization.Away r₀ R := Localization.isLocalization
  let : Algebra R k := ψ₀.toAlgebra
  let : Algebra R l := ((algebraMap k l).comp ψ₀).toAlgebra
  have : IsScalarTower R k l := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite R k := RingHom.finite_algebraMap.mp hψ₀finite
  have hΛRl : (algebraMap R l).comp (algebraMap Λ R) = algebraMap Λ l := by
    rw [IsScalarTower.algebraMap_eq Λ k l]
    change ((algebraMap k l).comp ψ₀).comp (algebraMap Λ R) = _
    rw [RingHom.comp_assoc, hψ₀]
  let iR : Spec (.of R) ⟶ D.S := Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ
  have hiR : _root_.AlgebraicGeometry.IsOpenImmersion iR := by
    dsimp [iR]
    infer_instance
  have hpointR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) := by
    calc
      _ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := hx₀
      _ = Over.mk (Spec.map (CommRingCat.ofHom ψ₀) ≫ iR) := by
            congr 1
            exact (awayChart_point_map_eq iΛ r₀ ψ₀ hψ₀).symm
  have hlR : Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
    dsimp only [iR]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hΛRl]
  have hxₗR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR) :=
    hxₗ.trans (congrArg Over.mk hlR.symm)
  have hfiniteR : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    finiteTypeAfterAwayLocalization iΛ r₀ ψ₀ hψ₀finite
  -- Move `ξ` to the chart `Spec R`, work there, and move the result back.
  obtain ⟨η₀, hη₀, hEq, hres₀⟩ :=
    exists_isVersal_ofPredeformation_eq_residue_of_affineOpenPresentation D iΛ hiΛ iR hiR x₀ hx₀
      hpointR hfinite hfiniteR ξ hξ
  obtain ⟨ηₗ, fR, hvR, hlocR, hresR, hsmR, ψR, hψR⟩ :=
    exists_versal_ofPredeformation_hom_fieldExtension_of_finite D iR hiR x₀ hpointR hfiniteR xₗ
      hxₗR η hηbase η₀ hη₀
  obtain ⟨ξₗ, hvₗ, hEqₗ, hresₗ⟩ :=
    exists_isVersal_ofPredeformation_eq_residue_of_affineOpenPresentation D iR hiR iΛ hiΛ xₗ hxₗR
      hxₗ (locallyOfFiniteType_and_quasiCompact_fieldExtension iR hfiniteR)
      (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ηₗ hvR
  have hB := congrArg Deformation.Artin.FormalObject.base hEq
  have hBₗ := congrArg Deformation.Artin.FormalObject.base hEqₗ
  let e : (ξ.base : Type u) ≃+* (η₀.base : Type u) :=
    (Deformation.Artin.FormalBase.ringEquivOfEq hB).symm
  let eₗ : (ηₗ.base : Type u) ≃+* (ξₗ.base : Type u) :=
    (Deformation.Artin.FormalBase.ringEquivOfEq hBₗ).symm
  let g : (ξ.base : Type u) →+* ξₗ.base := (eₗ.toRingHom.comp fR.toRingHom).comp e.toRingHom
  have hSpec_g : Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom eₗ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom fR.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) :=
    (specMap_comp_three _ _ _).symm
  have he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap R η₀.base)) ≫ iR := by
    exact specMap_ringEquivOfEq_symm_toS hB
  have heₗ : Spec.map (CommRingCat.ofHom eₗ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R ηₗ.base)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξₗ.base)) ≫ iΛ := by
    exact specMap_ringEquivOfEq_symm_toS hBₗ
  have hfR : Spec.map (CommRingCat.ofHom fR.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R η₀.base)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap R ηₗ.base)) ≫ iR := by
    rw [← Category.assoc, specMap_comp_two]
    congr 3
    exact fR.comp_algebraMap
  have hlin : g.comp (algebraMap Λ ξ.base) = algebraMap Λ ξₗ.base := by
    apply ringHom_eq_of_specMap_comp_eq iΛ
    rw [← specMap_comp_two, Category.assoc, hSpec_g]
    simp only [Category.assoc]
    rw [he, hfR, heₗ]
  let f : ξ.base →ₐ[Λ] ξₗ.base :=
    { toRingHom := g
      commutes' := fun a => DFunLike.congr_fun hlin a }
  refine ⟨ξₗ, f, hvₗ, ⟨fun a ha => ?_⟩, fun a => ?_, ?_, ?_⟩
  · exact (isUnit_map_iff e a).mp (hlocR.map_nonunit _ ((isUnit_map_iff eₗ _).mp ha))
  · have h1 : η₀.base.residueEquiv (residue η₀.base (e a)) =
        ξ.base.residueEquiv (residue ξ.base a) := by
      rw [show e a = _ from ringEquivOfEq_symm_apply_eq_cast hB a]
      exact hres₀ a
    have h2 : ξₗ.base.residueEquiv (residue ξₗ.base (eₗ (fR (e a)))) =
        ηₗ.base.residueEquiv (residue ηₗ.base (fR (e a))) := by
      rw [show eₗ (fR (e a)) = _ from ringEquivOfEq_symm_apply_eq_cast hBₗ _]
      exact hresₗ (fR (e a))
    exact h2.trans ((hresR (e a)).trans (congrArg (algebraMap k l) h1))
  · exact RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq e.symm eₗ
      (RingHom.ext fun a => congrArg (fun x => eₗ (fR x)) (e.apply_symm_apply a))
      (map_ringEquiv_maximalIdeal eₗ) hsmR
  · refine ⟨eqToHom hEqₗ ≫ ψR ≫ eqToHom hEq, ?_⟩
    have h := isBaseMap_eqToHom hEqₗ hEq ψR hψR
    have e1 : eqToHom (congrArg (fun Z : Deformation.Artin.FormalObject D.B D.S D.hS
          D.𝒳.val.val.p => Spec (.of Z.base.R)) hEqₗ) =
        Spec.map (CommRingCat.ofHom eₗ.toRingHom) :=
      (Deformation.Artin.FormalBase.specMap_ringEquivOfEq_symm hBₗ).symm
    have e2 : eqToHom (congrArg (fun Z : Deformation.Artin.FormalObject D.B D.S D.hS
          D.𝒳.val.val.p => Spec (.of Z.base.R)) hEq) =
        Spec.map (CommRingCat.ofHom e.toRingHom) :=
      (Deformation.Artin.FormalBase.specMap_ringEquivOfEq_symm hB).symm
    rw [e1, e2] at h
    exact (congrArg (fun a => Deformation.Artin.FormalObject.Hom.IsBaseMap
      (eqToHom hEqₗ ≫ ψR ≫ eqToHom hEq) a) hSpec_g).mpr h

/-- **Stacks 0DR1, part (2).** In the versal situation of Stacks 0DQU, let `x₀` be a point of `𝒳`
over `Spec k` for a field `k` of finite type over `S`, presented over an affine open `Spec Λ ⊆ S`,
let `l/k` be a finite extension of fields and `x_{l,0}` the induced point (an object `xₗ` over
`Spec l` with a morphism `η : xₗ ⟶ x₀` over `Spec l ⟶ Spec k`). Let `A` be a versal ring to `𝒳`
at `x₀`, with versal formal object `ξ`, coming from a morphism `Spec A ⟶ 𝒳` over `S`: an object
`y` of `𝒳` over `Spec A` realizing `ξ`. Then the homomorphism of **Stacks 0DQY** may be chosen
compatible with the morphisms `Spec A ⟶ 𝒳` and `Spec A' ⟶ 𝒳`: there are a versal ring `A'` to `𝒳`
at `x_{l,0}`, with versal formal object `ξₗ`, and an `S`-algebra map `f : A → A'` which is local,
induces `l/k` on residue fields and is formally smooth for the `𝔪_{A'}`-adic topology, such that

* when `Spec A'` belongs to the site, `ξₗ` comes from a morphism `Spec A' ⟶ 𝒳` (an object over
  `Spec A'` realizing `ξₗ`), and
* every object `y'` over `Spec A'` realizing `ξₗ` has a morphism `y' ⟶ y` of `𝒳` lying over
  `Spec f : Spec A' ⟶ Spec A`.

The morphism `y' ⟶ y` is the 2-arrow making the square `Spec A' ⟶ Spec A ⟶ 𝒳` 2-commute, which is
how the source's "compatible" is to be read (the remark notes that the diagrams commute only up to
a noncanonical 2-arrow). As in the source, the proof is that the maps of Stacks 0DQF and 07WX are
compatible with the versal formal objects: the formal object of `𝓕_{l/k}` produced by Stacks 0DQF
is the pushforward of `ξ` along `f`
(`Deformation.exists_versal_formalObject_changeOfFields_pushforward`), and its image under the
restriction functor of Stacks 07WX maps to `ξ` over the site over `Spec f`; fullness of the
approximation functor (Stacks 07X8, `Deformation.Artin.full_approximationFunctor_algebraicStacks`)
turns that morphism of formal objects into a morphism of the realizing objects. -/
@[stacks 0DR1 "part (2): in Lemma 0DQY the homomorphism A → A' may be chosen compatible with \
the morphisms Spec A → 𝒳, Spec A' → 𝒳"]
theorem exists_isVersalRingAt_fieldExtension_realization
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l]
    [Algebra Λ l] [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy) :
    ∃ (ξₗ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) xₗ hxₗ).projection)
      (f : ξ.base →ₐ[Λ] ξₗ.base),
      Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
        D.B D.hS iΛ D.𝒳.val.val.p xₗ hxₗ D.𝒳.val.property).cofibered ξₗ ∧
      IsLocalHom f.toRingHom ∧
      (∀ a : ξ.base, ξₗ.base.residueEquiv (residue ξₗ.base (f a)) =
        algebraMap k l (ξ.base.residueEquiv (residue ξ.base a))) ∧
      RingHom.FormallySmoothNAdic.{u} f.toRingHom (maximalIdeal ξₗ.base) ∧
      (∀ hA' : D.B.Contains (Spec (.of ξₗ.base)), ∃ (y' : D.𝒳.val.val.obj)
        (hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
          (Deformation.Artin.completeLocalAlgFormalBase iΛ
            (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ξₗ.base) hA'),
        Nonempty ((Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ
          D.𝒳.val.val.p xₗ hxₗ (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite)
            ξₗ).Realization hA' y' hy')) ∧
      ∀ {hA' : D.B.Contains (Spec (.of ξₗ.base))} {y' : D.𝒳.val.val.obj}
        {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
          (Deformation.Artin.completeLocalAlgFormalBase iΛ
            (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ξₗ.base) hA'},
        (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p xₗ hxₗ
          (locallyOfFiniteType_and_quasiCompact_fieldExtension iΛ hfinite) ξₗ).Realization
            hA' y' hy' →
        ∃ m : y' ⟶ y, (BigFppfOver.toScheme D.B D.S D.hS).map
            (eqToHom hy'.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy) =
          Spec.map (CommRingCat.ofHom f.toRingHom) := by
  obtain ⟨ξₗ, f, hv, hloc, hres, hsm, ψ, hψ⟩ := exists_versal_ofPredeformation_hom_fieldExtension
    D iΛ hiΛ x₀ hx₀ hfinite xₗ hxₗ η hηbase ξ hξ
  refine ⟨ξₗ, f, hv, hloc, hres, hsm, fun hA' => ?_, fun Ry' => ?_⟩
  · obtain ⟨y', hy', hR, -⟩ :=
      Deformation.Artin.FormalObject.Realization.exists_pullback D.𝒳.val.property ψ hψ Ry hA'
    exact ⟨y', hy', hR⟩
  · obtain ⟨m, -, hm⟩ := Deformation.Artin.FormalObject.Realization.exists_hom D.𝒳.val.property
      (Deformation.Artin.full_approximationFunctor_algebraicStacks D.𝒳) Ry' Ry ψ
    exact ⟨m, hm _ hψ⟩

end FieldExtension

end AlgebraicGeometry.Stack

end
