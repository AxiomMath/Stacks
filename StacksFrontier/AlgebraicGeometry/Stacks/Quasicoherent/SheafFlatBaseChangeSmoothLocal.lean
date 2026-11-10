module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtalePullbackComparisonComposition

/-!
# The flat base change property is smooth-local (Stacks 0764, part (3))

Let `f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of algebraic stacks over `S` with
`|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and `F` an étale sheaf of `𝒪_𝒳`-modules. **Stacks 0764** part (3)
says that if every inverse image `f j^{-1} F` has the flat base change property of
**Stacks 0762**, then so does `F`. Here the property is read on sheaves, as
`AlgebraicGeometry.Stack.HasSheafFlatBaseChangeProperty`: the comparison maps are local
isomorphisms of the small étale sites.

## Main definitions

* `AlgebraicGeometry.Stack.IsLocallyBijectiveComparison`: the comparison map at one arrow is a
  local isomorphism.

## Main results

* `AlgebraicGeometry.Stack.isLocallyBijectiveComparison_of_etaleCover`: that condition at an
  arrow is étale-local on its source.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective`:
  **Stacks 0764 (3)**.
* `AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_iff_of_isSmooth_jointlySurjective`:
  together with **Stacks 0764 (1)**, an equivalence.

## Implementation notes

The étale covering and the lifts are those of the proof of **Stacks 075Y**,
`AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift`. The comparison maps of the
inverse image are identified with those of `F` by
`AlgebraicGeometry.Stack.isLocallyBijective_pullbackComparison_modulePresheafPullback_iff`, the
composition law of **Stacks 075D (1)** is
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_comp`, and the étale case
**Stacks 075D (2)** with the étale locality of local isomorphisms is
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleModuleComparisonEtale.lean`. The
module sections are in the universe of the schemes, as the composition law is.

The statement carries no tag: **Stacks 0764** is a prerequisite of **Stacks 0771** and of the
rule clauses of **Stacks 076Z** for `LQCoh^fbc`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Composing a locally injective and locally surjective map with an isomorphism on the left
keeps it so. -/
private theorem isLocallyBijective_iso_comp {C : Type*} [Category C] {K : GrothendieckTopology C}
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (u : F₁ ⟶ F₂) [IsIso u] (v : F₂ ⟶ F₃)
    (hv : Presheaf.IsLocallyInjective K v ∧ Presheaf.IsLocallySurjective K v) :
    Presheaf.IsLocallyInjective K (u ≫ v) ∧ Presheaf.IsLocallySurjective K (u ≫ v) := by
  obtain ⟨_, _⟩ := hv
  exact ⟨inferInstance, inferInstance⟩

/-- Composing a locally injective and locally surjective map with an isomorphism on the right
keeps it so. -/
private theorem isLocallyBijective_comp_iso {C : Type*} [Category C] {K : GrothendieckTopology C}
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (v : F₁ ⟶ F₂) (w : F₂ ⟶ F₃) [IsIso w]
    (hv : Presheaf.IsLocallyInjective K v ∧ Presheaf.IsLocallySurjective K v) :
    Presheaf.IsLocallyInjective K (v ≫ w) ∧ Presheaf.IsLocallySurjective K (v ≫ w) := by
  obtain ⟨_, _⟩ := hv
  exact ⟨inferInstance, inferInstance⟩

section Comparison

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-- The comparison map `c_ψ` of **Stacks 06WC** for `F` at an arrow `ψ` is a local isomorphism of
the small étale site: locally injective and locally surjective. -/
abbrev IsLocallyBijectiveComparison {a y : 𝒳} (ψ : a ⟶ y) : Prop :=
  Presheaf.IsLocallyInjective
      (SmallEtale.topology E (p.obj a).left.1 (contains_base B E h S hS p a))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp ψ (etaleTopology B)
          (etaleTopology_le_topology B) F)) ∧
    Presheaf.IsLocallySurjective
      (SmallEtale.topology E (p.obj a).left.1 (contains_base B E h S hS p a))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp ψ (etaleTopology B)
          (etaleTopology_le_topology B) F))

/-- Being a local isomorphism of the comparison map transports along an equality of arrows. -/
theorem isLocallyBijectiveComparison_of_eq {a y : 𝒳} {ψ₁ ψ₂ : a ⟶ y} (hψ : ψ₁ = ψ₂)
    (h₁ : IsLocallyBijectiveComparison B E h S hS p hp F ψ₁) :
    IsLocallyBijectiveComparison B E h S hS p hp F ψ₂ := by
  subst hψ
  exact h₁

/-- If the comparison map at `γ` is a local isomorphism and `α` lies over an étale morphism, the
comparison map at `γ ≫ α` is a local isomorphism: by **Stacks 075D (1)** it is the inverse image
of `c_α`, an isomorphism by **Stacks 075D (2)**, followed by `c_γ`. -/
theorem isLocallyBijectiveComparison_comp_of_etale {a b y : 𝒳} (γ : a ⟶ b) (α : b ⟶ y)
    (hα : Etale (B.inclusion.map (p.map α).left))
    (hγ : IsLocallyBijectiveComparison B E h S hS p hp F γ) :
    IsLocallyBijectiveComparison B E h S hS p hp F (γ ≫ α) := by
  have hcomp := restrictModulePullbackComparison_comp B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) γ α F
  have hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp α (etaleTopology B)
      (etaleTopology_le_topology B) F) :=
    isIso_restrictModulePullbackComparisonUnivLE_of_etale.{u, v, w, u} B E h S hS p hp α hα F
  have e : restrictModulePullbackComparisonUnivLE B E h S hS p hp (γ ≫ α) (etaleTopology B)
      (etaleTopology_le_topology B) F =
      ((smallEtalePullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) γ α).app
        (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
          (etaleTopology_le_topology B) F)).inv ≫
        (PresheafOfModules.pullback.{u} (smallEtaleStructureComparison B E h S hS p hp γ
          (etaleTopology B) (etaleTopology_le_topology B))).map
          (restrictModulePullbackComparison B E h S hS p hp α (etaleTopology B)
            (etaleTopology_le_topology B) F) ≫
        restrictModulePullbackComparison B E h S hS p hp γ (etaleTopology B)
          (etaleTopology_le_topology B) F :=
    (Iso.eq_inv_comp _).2 hcomp.symm
  unfold IsLocallyBijectiveComparison
  rw [e, Functor.map_comp, Functor.map_comp]
  exact isLocallyBijective_iso_comp _ _ (isLocallyBijective_iso_comp _ _ hγ)

/-- If the comparison map at `β ≫ φ` is a local isomorphism and `β` lies over an étale morphism,
the inverse image along `β` of the comparison map at `φ` is a local isomorphism: by
**Stacks 075D (1)** it is the comparison map at `β ≫ φ` followed by the inverse of `c_β`, an
isomorphism by **Stacks 075D (2)**. -/
theorem isLocallyBijective_pullback_map_of_etale {a x y : 𝒳} (β : a ⟶ x) (φ : x ⟶ y)
    (hβ : Etale (B.inclusion.map (p.map β).left))
    (h₀ : IsLocallyBijectiveComparison B E h S hS p hp F (β ≫ φ)) :
    Presheaf.IsLocallyInjective
        (SmallEtale.topology E (p.obj a).left.1 (contains_base B E h S hS p a))
        ((PresheafOfModules.toPresheaf _).map ((PresheafOfModules.pullback.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p β))
          (smallEtaleStructureComparison B E h S hS p hp β (etaleTopology B)
            (etaleTopology_le_topology B))).map
          (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B) F))) ∧
      Presheaf.IsLocallySurjective
        (SmallEtale.topology E (p.obj a).left.1 (contains_base B E h S hS p a))
        ((PresheafOfModules.toPresheaf _).map ((PresheafOfModules.pullback.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p β))
          (smallEtaleStructureComparison B E h S hS p hp β (etaleTopology B)
            (etaleTopology_le_topology B))).map
          (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B) F))) := by
  have hcomp := restrictModulePullbackComparison_comp B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) β φ F
  have hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp β (etaleTopology B)
      (etaleTopology_le_topology B) F) :=
    isIso_restrictModulePullbackComparisonUnivLE_of_etale.{u, v, w, u} B E h S hS p hp β hβ F
  have e : (PresheafOfModules.pullback.{u} (smallEtaleStructureComparison B E h S hS p hp β
          (etaleTopology B) (etaleTopology_le_topology B))).map
          (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B) F) =
      (smallEtalePullbackComparisonCompIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) β φ).hom.app
        (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
          (etaleTopology_le_topology B) F) ≫
        restrictModulePullbackComparison B E h S hS p hp (β ≫ φ) (etaleTopology B)
          (etaleTopology_le_topology B) F ≫
        inv (restrictModulePullbackComparison B E h S hS p hp β (etaleTopology B)
          (etaleTopology_le_topology B) F) := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv _).2 hcomp
  rw [e, Functor.map_comp, Functor.map_comp]
  exact isLocallyBijective_iso_comp _ _ (isLocallyBijective_comp_iso _ _ h₀)

/-- **The flat base change property along `φ` is étale-local on the source.** Let `φ : x ⟶ y`
and let `β i : z i ⟶ x` be a jointly surjective family of arrows over étale morphisms, with
factorizations `β i ≫ φ = γ i ≫ α i` where `α i` lies over an étale morphism. If the comparison
maps at the `γ i` are local isomorphisms, so is the comparison map at `φ`. -/
theorem isLocallyBijectiveComparison_of_etaleCover {x y : 𝒳} (φ : x ⟶ y) {I : Type (u + 1)}
    (z w : I → 𝒳) (β : ∀ i, z i ⟶ x) (γ : ∀ i, z i ⟶ w i) (α : ∀ i, w i ⟶ y)
    (hβ : ∀ i, Etale (B.inclusion.map (p.map (β i)).left))
    (hα : ∀ i, Etale (B.inclusion.map (p.map (α i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (β i)).left))
    (hfac : ∀ i, γ i ≫ α i = β i ≫ φ)
    (hγ : ∀ i, IsLocallyBijectiveComparison B E h S hS p hp F (γ i)) :
    IsLocallyBijectiveComparison B E h S hS p hp F φ :=
  isLocallyBijective_of_pullback_etaleChart.{u, v, w, u} B E h S hS p hp _ z β hβ hcov fun i =>
    isLocallyBijective_pullback_map_of_etale B E h S hS p hp F (β i) φ (hβ i)
      (isLocallyBijectiveComparison_of_eq B E h S hS p hp F (hfac i)
        (isLocallyBijectiveComparison_comp_of_etale B E h S hS p hp F (γ i) (α i) (hα i) (hγ i)))

end Comparison

/-- The image under the site inclusion of the underlying morphism of an `eqToHom` is an
isomorphism. -/
private theorem isIso_inclusion_map_eqToHom_left {U V : BigFppfOver B S hS} (e : U = V) :
    IsIso (B.inclusion.map (eqToHom e).left) := by
  change IsIso ((Over.forget (B.obj hS) ⋙ B.inclusion).map (eqToHom e))
  infer_instance

/-- An arrow of a category fibred in groupoids lying over a flat morphism of the site has flat
underlying morphism of schemes. -/
theorem flat_map_left_of_isHomLift {𝒳 : Type*} [Category 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) {U V : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : Flat (B.inclusion.map k.left)) {y x : 𝒳} (φ : y ⟶ x) (hφ : p.IsHomLift k φ) :
    Flat (B.inclusion.map (p.map φ).left) := by
  have := hφ
  have hfac := IsHomLift.fac' p k φ
  have hleft : (p.map φ).left =
      (eqToHom (IsHomLift.domain_eq p k φ)).left ≫ k.left ≫
        (eqToHom (IsHomLift.codomain_eq p k φ).symm).left := by
    rw [hfac]; rfl
  rw [hleft]
  have := isIso_inclusion_map_eqToHom_left B S hS (IsHomLift.domain_eq p k φ)
  have := isIso_inclusion_map_eqToHom_left B S hS (IsHomLift.codomain_eq p k φ).symm
  have := hk
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **Stacks 0764 (3)**, with the flat base change property of **Stacks 0762** read on sheaves.
Let `f j : 𝒵 j ⟶ 𝒳` be a family of smooth 1-morphisms of algebraic stacks with
`|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be an étale sheaf of modules on `𝒳`. If every inverse
image `f j^{-1} F` has the flat base change property, so does `F`.

As in the source: for an arrow `φ : x ⟶ y` over a flat morphism of schemes, **Stacks 06XH** gives
an étale covering of the scheme below `y` over whose members `y` lifts to the `𝒵 j`; the base
changes of `φ` to these lifts are arrows `ψ_i` of the `𝒵 j` over flat morphisms, the comparison
maps of `f j^{-1} F` at the `ψ_i` are those of `F` at `f j ψ_i` (**Stacks 0764 (1)**, through
**Stacks 075D (3)**), and those are the restrictions of the comparison map at `φ` to an étale
covering of the scheme below `x` (**Stacks 075D (1)** and **(2)**). -/
theorem hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hfbc : ∀ j, HasSheafFlatBaseChangeProperty B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) (etaleTopology B)
      (etaleTopology_le_topology B) ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F)) :
    HasSheafFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F := by
  classical
  intro x y φ hflat
  let p := 𝒳.val.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  obtain ⟨I, W, e, a, hetale, hcov, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS f hsmooth hjs (p.obj y) (Functor.Fiber.mk rfl)
  choose zz αα hαα using hlift
  have hαe : ∀ i, Etale (B.inclusion.map (p.map (αα i)).left) := fun i =>
    etale_map_left_of_isHomLift B S hS p _ (hetale i) (αα i) (hαα i)
  have hlift' : ∀ i, ∃ (a₀ : (𝒵 (a i)).val.val.obj) (τ : a₀ ⟶ zz i),
      (CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p).IsHomLift
        (pullback.snd (p.map φ) (p.map (αα i))) τ := fun i =>
    (isFiberedInGroupoids_homFunctor_comp B S hS (f (a i)).hom).exists_lift _ (zz i) rfl
  choose a₀ τ hτ using hlift'
  let G := fun i => CatFiberedInGroupoids.homFunctor (f (a i)).hom
  let γ : ∀ i, (G i).obj (a₀ i) ⟶ (G i).obj (zz i) := fun i => (G i).map (τ i)
  have hsq : ∀ i, IsPullback (B.inclusion.map (pullback.fst (p.map φ) (p.map (αα i))).left)
      (B.inclusion.map (pullback.snd (p.map φ) (p.map (αα i))).left)
      (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (αα i)).left) := fun i =>
    (IsPullback.of_hasPullback (p.map φ) (p.map (αα i))).map (Over.forget _ ⋙ B.inclusion)
  have hβex : ∀ i, ∃ β : (G i).obj (a₀ i) ⟶ x,
      p.map β = eqToHom (IsHomLift.domain_eq (CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p)
          (pullback.snd (p.map φ) (p.map (αα i))) (τ i)) ≫
        pullback.fst (p.map φ) (p.map (αα i)) ∧ β ≫ φ = (γ i ≫ αα i) ≫ 𝟙 y := by
    intro i
    refine Functor.IsFiberedInGroupoids.exists_hom_of_commSq hp (𝟙 y) (γ i ≫ αα i) φ _ ?_
    have := hτ i
    have hfacτ := IsHomLift.fac' (CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p)
      (pullback.snd (p.map φ) (p.map (αα i))) (τ i)
    have hγmap : p.map (γ i) = (CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p).map (τ i) :=
      rfl
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    refine Eq.trans ?_ (p.map_comp _ _).symm
    rw [hγmap, hfacτ, Category.assoc, pullback.condition]
    simp
  choose β hβmap hβfac using hβex
  have hiso : ∀ i, IsIso (B.inclusion.map (eqToHom (IsHomLift.domain_eq
      (CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p)
      (pullback.snd (p.map φ) (p.map (αα i))) (τ i))).left) := fun i =>
    isIso_inclusion_map_eqToHom_left B S hS _
  have hβleft : ∀ i, B.inclusion.map (p.map (β i)).left =
      B.inclusion.map (eqToHom (IsHomLift.domain_eq
        (CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p)
        (pullback.snd (p.map φ) (p.map (αα i))) (τ i))).left ≫
      B.inclusion.map (pullback.fst (p.map φ) (p.map (αα i))).left := fun i => by
    rw [hβmap i, Over.comp_left, Functor.map_comp]
  have hβe : ∀ i, Etale (B.inclusion.map (p.map (β i)).left) := fun i => by
    rw [hβleft i]
    have : Etale (B.inclusion.map (pullback.fst (p.map φ) (p.map (αα i))).left) :=
      MorphismProperty.of_isPullback (P := @Etale) (hsq i).flip (hαe i)
    have := hiso i
    infer_instance
  have hcov' : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (β i)).left) := by
    intro t
    obtain ⟨i, hi⟩ := hcov ((B.inclusion.map (p.map φ).left) t)
    obtain ⟨s', hs'⟩ := range_map_left_of_isHomLift B S hS p (αα i) (hαα i) hi
    obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback (hsq i) t s' hs'.symm
    refine ⟨i, inv (B.inclusion.map (eqToHom (IsHomLift.domain_eq
      (CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p)
      (pullback.snd (p.map φ) (p.map (αα i))) (τ i))).left) q, ?_⟩
    rw [hβleft i, ← Scheme.Hom.comp_apply, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
    exact hq
  refine isLocallyBijectiveComparison_of_etaleCover B E h S hS p hp F φ
    (fun i => (G i).obj (a₀ i)) (fun i => (G i).obj (zz i)) β γ αα hβe hαe hcov'
    (fun i => ((hβfac i).trans (Category.comp_id _)).symm) (fun i => ?_)
  have hflatτ : Flat (B.inclusion.map
      ((CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ p).map (τ i)).left) :=
    flat_map_left_of_isHomLift B S hS _ _
      (MorphismProperty.of_isPullback (P := @Flat) (hsq i) hflat) (τ i) (hτ i)
  exact (isLocallyBijective_pullbackComparison_modulePresheafPullback_iff B E h S hS p hp (G i)
    (isFiberedInGroupoids_homFunctor_comp B S hS (f (a i)).hom) F hF (τ i)).1
    (hfbc (a i) (τ i) hflatτ)

/-- **Stacks 0764 (1) and (3)** together: along a jointly surjective family of smooth 1-morphisms
of algebraic stacks, an étale sheaf of modules has the flat base change property of **Stacks 0762**
if and only if all its inverse images do. -/
theorem hasSheafFlatBaseChangeProperty_iff_of_isSmooth_jointlySurjective
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      F.presheaf) :
    HasSheafFlatBaseChangeProperty B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B) F ↔
      ∀ j, HasSheafFlatBaseChangeProperty B E h S hS
        (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) (etaleTopology B)
        (etaleTopology_le_topology B)
        ((stackModulePresheafPullback.{u, w, u} B S hS (f j)).obj F) :=
  ⟨fun hfbc j => hasSheafFlatBaseChangeProperty_modulePresheafPullback B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor (f j).hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom) F hF hfbc,
    hasSheafFlatBaseChangeProperty_of_isSmooth_jointlySurjective B E h S hS f hsmooth hjs F hF⟩

end AlgebraicGeometry.Stack

end
