module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackCompositionPullbackData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineUnitObject
public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystemThick

/-!
# Morphisms between shifts of the structure sheaf along a directed system of affine representables

Let `V₀` be an affine object of the big fppf site over `S`, and let `j ↦ V_j` be a directed system
of affine objects over `V₀`, with a cone `V ⟶ V_j` over `V₀` whose rings of global functions are
the filtered colimit of those of the `V_j`.  Write `k_j : h_{V_j} ⟶ h_{V₀}` and
`k : h_V ⟶ h_{V₀}` for the induced morphisms of algebraic spaces, and `Lk^*` for derived
pullback, with its canonical pseudofunctoriality.  This file proves that for the structure sheaf
`𝒪[p]` and `𝒪[q]` of `h_{V₀}` in two degrees,

`Hom_{D(𝒪_{h_V})}(Lk^*𝒪[p], Lk^*𝒪[q]) = colim_j Hom_{D(𝒪_{h_{V_j}})}(Lk_j^*𝒪[p], Lk_j^*𝒪[q])`.

For `p ≠ q` all these groups vanish.  For `p = q` each of them is identified with the ring of
global functions, by
`AlgebraicGeometry.Space.bijective_representedAffineUnitSmul` read through the isomorphism
`Lk_j^*𝒪[p] ≅ 𝒪[p]`; the identification does not depend on that isomorphism because the
endomorphisms of `𝒪[p]` commute, and under it the transition maps of the system become the maps
of rings of global functions (`AlgebraicGeometry.Space.representedAffineUnitPullbackIso_conj`).
This is the affine case of Stacks 09RI for the structure sheaf.

## Main definitions

* `AlgebraicGeometry.Space.RepresentedAffineSystem`: a directed system of affine representables
  over an affine representable, with a cone.
* `AlgebraicGeometry.Space.RepresentedAffineSystem.toLimitSystem`: the induced system of algebraic
  spaces.

## Main results

* `AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_unitObj`: the colimit statement for the
  structure sheaf in any two degrees.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

/-- **Conjugating a conjugate by a comparison.**  For a comparison `e : P₂ ≅ P₁ ⋙ L`,
isomorphisms `ν₁ : P₁ M ≅ Y` and `ν₂ : P₂ M ≅ Z` and `μ : L Y ≅ Z` with `Z` having commutative
endomorphisms, reading the conjugate by `e` of `ν₁ ∘ x ∘ ν₁⁻¹` through `ν₂` is reading `L x`
through `μ`. -/
theorem CategoryTheory.Functor.conjHom_conj_of_end_comm {C D₁ D₂ : Type*} [Category C]
    [Category D₁] [Category D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L)
    {M : C} {Y : D₁} {Z : D₂} (hZ : ∀ a b : Z ⟶ Z, a ≫ b = b ≫ a) (ν₁ : P₁.obj M ≅ Y)
    (ν₂ : P₂.obj M ≅ Z) (μ : L.obj Y ≅ Z) (x : Y ⟶ Y) :
    ν₂.inv ≫ Functor.conjHom e (ν₁.hom ≫ x ≫ ν₁.inv) ≫ ν₂.hom = μ.inv ≫ L.map x ≫ μ.hom := by
  have key : ν₂.inv ≫ Functor.conjHom e (ν₁.hom ≫ x ≫ ν₁.inv) ≫ ν₂.hom =
      ((L.mapIso ν₁).symm ≪≫ (e.app M).symm ≪≫ ν₂).inv ≫ L.map x ≫
        ((L.mapIso ν₁).symm ≪≫ (e.app M).symm ≪≫ ν₂).hom := by
    simp only [Functor.conjHom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
      Category.assoc]
  rw [key]
  exact conj_eq_conj_of_end_comm hZ _ _ _

/-- An endomorphism is determined by its conjugate through an isomorphism. -/
theorem CategoryTheory.Iso.eq_hom_comp_comp_inv_of_conj {C : Type*} [Category C] {A B : C}
    (ν : A ≅ B) {x : A ⟶ A} {y : B ⟶ B} (h : ν.inv ≫ x ≫ ν.hom = y) :
    x = ν.hom ≫ y ≫ ν.inv := by
  rw [← h]
  simp

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A directed system of affine representables over an affine representable, with a cone.**
The stages `V_j` with their structure morphisms to `V₀` and transition morphisms over `V₀`, which
compose, and a vertex `V` with a structure morphism and projections over `V₀` compatible with the
transition morphisms; all of these have affine underlying schemes. -/
structure RepresentedAffineSystem (V₀ : BigFppfOver B S hS) (J : Type w) [Preorder J] where
  /-- The stage `V_j`. -/
  obj : J → BigFppfOver B S hS
  /-- The underlying scheme of each stage `V_j` is affine. -/
  isAffine_obj : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (obj j))
  /-- The structure morphism `V_j ⟶ V₀`. -/
  toBase : ∀ j, obj j ⟶ V₀
  /-- The transition morphism `V_j ⟶ V_i` for `i ≤ j`. -/
  map : ∀ {i j : J}, i ≤ j → (obj j ⟶ obj i)
  map_toBase : ∀ {i j : J} (h : i ≤ j), map h ≫ toBase i = toBase j
  map_comp : ∀ {i j k : J} (h : i ≤ j) (h' : j ≤ k), map h' ≫ map h = map (h.trans h')
  /-- The vertex `V`. -/
  lim : BigFppfOver B S hS
  /-- The underlying scheme of the vertex `V` is affine. -/
  isAffine_lim : IsAffine ((BigFppfOver.toScheme B S hS).obj lim)
  /-- The structure morphism `V ⟶ V₀`. -/
  limToBase : lim ⟶ V₀
  /-- The projection `V ⟶ V_j`. -/
  proj : ∀ j, lim ⟶ obj j
  proj_toBase : ∀ j, proj j ≫ toBase j = limToBase
  proj_map : ∀ {i j : J} (h : i ≤ j), proj j ≫ map h = proj i

namespace RepresentedAffineSystem

attribute [instance] isAffine_obj isAffine_lim

variable {V₀ : BigFppfOver B S hS} {J : Type w} [Preorder J] (Sys : RepresentedAffineSystem V₀ J)

/-- The rings of global functions of the vertex are the filtered colimit of those of the stages,
in the elementwise form `Stacks.IsStagesColimit`. -/
def IsRingColimit : Prop :=
  Stacks.IsStagesColimit (fun _ _ h => (representedAffineCommRingCatHom B S hS (Sys.map h)).hom)
    (fun j => (representedAffineCommRingCatHom B S hS (Sys.proj j)).hom)

/-- **The induced system of algebraic spaces** over `h_{V₀}`. -/
def toLimitSystem : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS)
    (⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩ : AlgebraicSpaces B S hS) J where
  stage j := ⟨yoneda.obj (Sys.obj j), isAlgebraicSpace_yoneda B S hS _⟩
  toBase j := representedSpaceMap B S hS (Sys.toBase j)
  transition h := representedSpaceMap B S hS (Sys.map h)
  transition_toBase h := ObjectProperty.hom_ext _ (by
    change yoneda.map _ ≫ yoneda.map _ = yoneda.map _
    rw [← Functor.map_comp, Sys.map_toBase])
  transition_comp h h' := ObjectProperty.hom_ext _ (by
    change yoneda.map _ ≫ yoneda.map _ = yoneda.map _
    rw [← Functor.map_comp, Sys.map_comp])
  limit := ⟨yoneda.obj Sys.lim, isAlgebraicSpace_yoneda B S hS _⟩
  limitToBase := representedSpaceMap B S hS Sys.limToBase
  proj j := representedSpaceMap B S hS (Sys.proj j)
  proj_toBase j := ObjectProperty.hom_ext _ (by
    change yoneda.map _ ≫ yoneda.map _ = yoneda.map _
    rw [← Functor.map_comp, Sys.proj_toBase])
  proj_transition h := ObjectProperty.hom_ext _ (by
    change yoneda.map _ ≫ yoneda.map _ = yoneda.map _
    rw [← Functor.map_comp, Sys.proj_map])

end RepresentedAffineSystem

/-! ### The endomorphisms of the pulled back structure sheaf -/

section Endomorphisms

variable {V₀ V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]

/-- **The endomorphisms of the pulled back structure sheaf are the global functions**: an
endomorphism of `Lg^*𝒪[p]`, read through `Lg^*𝒪[p] ≅ 𝒪[p]`, is the multiplication by a unique
global function of `V'`. -/
def pullbackUnitEndEquiv (g : V' ⟶ V₀) (p : ℤ) :
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        (representedAffineUnitObj B S hS V₀ p) ⟶
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        (representedAffineUnitObj B S hS V₀ p)) ≃ Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) :=
  ((representedAffineUnitPullbackIso B S hS g p).homCongr
      (representedAffineUnitPullbackIso B S hS g p)).trans
    (Equiv.ofBijective _ (bijective_representedAffineUnitSmul B S hS V' p)).symm

/-- The endomorphism of `Lg^*𝒪[p]` attached to a global function `s` of `V'` is the
multiplication by `s` on `𝒪[p]`, conjugated by `Lg^*𝒪[p] ≅ 𝒪[p]`. -/
theorem pullbackUnitEndEquiv_symm_apply (g : V' ⟶ V₀) (p : ℤ)
    (s : Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)) :
    (pullbackUnitEndEquiv g p).symm s = (representedAffineUnitPullbackIso B S hS g p).hom ≫
      representedAffineUnitSmul B S hS V' p s ≫ (representedAffineUnitPullbackIso B S hS g p).inv :=
  rfl

/-- **The transition maps become the maps of rings of global functions.**  For a factorisation
`f ≫ g = k` of morphisms of affine representables, the map of endomorphism sets of the pulled back
structure sheaf attached to it by the canonical pseudofunctoriality of derived pullback is, under
`AlgebraicGeometry.Space.pullbackUnitEndEquiv`, the map of rings of global functions of `f`. -/
theorem pullbackUnitEndEquiv_factorHom_symm {V'' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V'')] (f : V'' ⟶ V') (g : V' ⟶ V₀)
    (k : V'' ⟶ V₀)
    (h : representedSpaceMap B S hS f ≫ representedSpaceMap B S hS g = representedSpaceMap B S hS k)
    (p : ℤ) (ψ : Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)) :
    pullbackUnitEndEquiv k p
        ((DerivedPullbackComposition.canonical B S hS).toPullbackData.factorHom h
          ((pullbackUnitEndEquiv g p).symm ψ)) =
      (representedAffineCommRingCatHom B S hS f).hom ψ := by
  refine (Equiv.eq_symm_apply _).1 ?_
  have key := Functor.conjHom_conj_of_end_comm
    ((DerivedPullbackComposition.canonical B S hS).toPullbackData.triangle h)
    (representedAffineUnitObj_end_comm B S hS V'' p) (representedAffineUnitPullbackIso B S hS g p)
    (representedAffineUnitPullbackIso B S hS k p) (representedAffineUnitPullbackIso B S hS f p)
    (representedAffineUnitSmul B S hS V' p ψ)
  have key' := key.trans (representedAffineUnitPullbackIso_conj B S hS f p ψ)
  change Functor.conjHom ((DerivedPullbackComposition.canonical B S hS).toPullbackData.triangle h)
      ((representedAffineUnitPullbackIso B S hS g p).hom ≫ representedAffineUnitSmul B S hS V' p ψ ≫
        (representedAffineUnitPullbackIso B S hS g p).inv) =
    (representedAffineUnitPullbackIso B S hS k p).hom ≫
      representedAffineUnitSmul B S hS V'' p ((representedAffineCommRingCatHom B S hS f).hom ψ) ≫
      (representedAffineUnitPullbackIso B S hS k p).inv
  exact Iso.eq_hom_comp_comp_inv_of_conj _ key'

/-- **There are no nonzero morphisms between the pullbacks of the structure sheaf in two distinct
degrees.** -/
theorem subsingleton_pullback_hom_representedAffineUnitObj (g : V' ⟶ V₀) {p q : ℤ} (hpq : p ≠ q) :
    Subsingleton ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        (representedAffineUnitObj B S hS V₀ p) ⟶
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
        (representedAffineUnitObj B S hS V₀ q)) := by
  have := subsingleton_hom_representedAffineUnitObj B S hS V' hpq
  exact ((representedAffineUnitPullbackIso B S hS g p).homCongr
    (representedAffineUnitPullbackIso B S hS g q)).subsingleton

end Endomorphisms

namespace RepresentedAffineSystem

variable {V₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
  {J : Type w} [Preorder J] (Sys : RepresentedAffineSystem V₀ J)

/-- **The affine case of Stacks 09RI for the structure sheaf.**  Along a directed system of affine
representables over `V₀` with a cone whose rings of global functions form a filtered colimit,
`Hom(Lk^*𝒪[p], Lk^*𝒪[q])` is the filtered colimit of the `Hom(Lk_j^*𝒪[p], Lk_j^*𝒪[q])`. -/
theorem isColim_unitObj [Nonempty J] (hring : Sys.IsRingColimit) (p q : ℤ) :
    Sys.toLimitSystem.IsColim (DerivedPullbackComposition.canonical B S hS).toPullbackData
      (representedAffineUnitObj B S hS V₀ p) (representedAffineUnitObj B S hS V₀ q) := by
  have hP := (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  by_cases hpq : p = q
  · subst hpq
    refine Stacks.IsStagesColimit.ofEquiv _ _
      (fun j => pullbackUnitEndEquiv (Sys.toBase j) p) (pullbackUnitEndEquiv Sys.limToBase p)
      (fun i j h x => ?_) (fun j x => ?_) hring
    · obtain ⟨ψ, rfl⟩ := (pullbackUnitEndEquiv (Sys.toBase i) p).symm.surjective x
      exact (pullbackUnitEndEquiv_factorHom_symm (Sys.map h) (Sys.toBase i) (Sys.toBase j)
        (Sys.toLimitSystem.transition_toBase h) p ψ).trans
          (congrArg _ (Equiv.apply_symm_apply _ ψ).symm)
    · obtain ⟨ψ, rfl⟩ := (pullbackUnitEndEquiv (Sys.toBase j) p).symm.surjective x
      exact (pullbackUnitEndEquiv_factorHom_symm (Sys.proj j) (Sys.toBase j) Sys.limToBase
        (Sys.toLimitSystem.proj_toBase j) p ψ).trans
          (congrArg _ (Equiv.apply_symm_apply _ ψ).symm)
  · refine ⟨fun i j h x => ?_, fun ψ => ?_, fun i x x' _ => ?_⟩
    · exact (subsingleton_pullback_hom_representedAffineUnitObj Sys.limToBase hpq).elim _ _
    · obtain ⟨j⟩ := (inferInstance : Nonempty J)
      exact ⟨j, 0, (subsingleton_pullback_hom_representedAffineUnitObj Sys.limToBase hpq).elim
        _ _⟩
    · exact ⟨i, le_refl i,
        (subsingleton_pullback_hom_representedAffineUnitObj (Sys.toBase i) hpq).elim _ _⟩

end RepresentedAffineSystem

end AlgebraicGeometry.Space

end
