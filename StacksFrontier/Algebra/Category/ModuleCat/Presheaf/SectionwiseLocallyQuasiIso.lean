module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso

/-!
# Sheafification inverts a map of presheaves of modules which is locally bijective sectionwise

`PresheafOfModules.quasiIso_sheafification_map_of_exists_mem_sieve` of `LocallyQuasiIso.lean`
asks for **one covering sieve per object**, above which the map of homology presheaves is
invertible. That hypothesis is unavailable whenever the two presheaves agree only after a
covering that depends on the *section* being compared — which is the situation of a presheaf
defined as a colimit over an index that varies with the object, where a section comes from one
stage of the colimit and only that stage can be controlled by a covering.

This file records the same conclusions under the weaker, sectionwise hypothesis: the map of
homology presheaves is locally injective and locally surjective, each witness sieve being
allowed to depend on the sections it is produced for. That is exactly Mathlib's
`CategoryTheory.Presheaf.IsLocallyInjective` and `IsLocallySurjective`, and it is already what
the proof of the sieve-uniform statement passes to
`CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective`; the uniform hypothesis is only
a convenient way of producing it.

## Main results

* `CategoryTheory.Presheaf.isLocallyInjective_of_forall_exists_mem_sieve` and
  `CategoryTheory.Presheaf.isLocallySurjective_of_forall_exists_mem_sieve`: the sectionwise
  criteria, in the shape a covering sieve is usually produced in.
* `PresheafOfModules.isIso_sheafification_map_of_isLocallyBijective`: **sheafification inverts a
  locally bijective map of presheaves of modules.**
* `PresheafOfModules.quasiIso_sheafification_map_of_isLocallyBijective`: **sheafification
  carries a map of complexes of presheaves of modules whose homology presheaves are locally
  bijective to a quasi-isomorphism.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  {F₁ F₂ : Cᵒᵖ ⥤ D} (φ : F₁ ⟶ F₂)

/-- **The sectionwise criterion for local injectivity**: for each pair of sections with the same
image there is a covering sieve, depending on that pair, above which they already agree. -/
theorem isLocallyInjective_of_forall_exists_mem_sieve
    (h : ∀ (X : C) (x y : ToType (F₁.obj (op X))), φ.app (op X) x = φ.app (op X) y →
      ∃ S : Sieve X, S ∈ J X ∧ ∀ ⦃Y : C⦄ (a : Y ⟶ X), S a →
        F₁.map a.op x = F₁.map a.op y) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y hxy := by
    obtain ⟨S, hS, heq⟩ := h X.unop x y hxy
    exact J.superset_covering (fun _ a ha => heq a ha) hS

/-- **The sectionwise criterion for local surjectivity**: for each section of the target there is
a covering sieve, depending on that section, above which it is in the image. -/
theorem isLocallySurjective_of_forall_exists_mem_sieve
    (h : ∀ (X : C) (s : ToType (F₂.obj (op X))), ∃ S : Sieve X, S ∈ J X ∧
      ∀ ⦃Y : C⦄ (a : Y ⟶ X), S a →
        ∃ t : ToType (F₁.obj (op Y)), φ.app (op Y) t = F₂.map a.op s) :
    IsLocallySurjective J φ where
  imageSieve_mem {X} s := by
    obtain ⟨S, hS, him⟩ := h X s
    exact J.superset_covering (fun _ a ha => him a ha) hS

end CategoryTheory.Presheaf

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- **Sheafification inverts a locally bijective map of presheaves of modules.**

This is `PresheafOfModules.isIso_sheafification_map_of_exists_mem_sieve` with the hypothesis
weakened to what its proof actually uses: the underlying map of presheaves of abelian groups is
locally bijective, hence belongs to the class of maps sheafification inverts, and a map of
sheaves of modules is invertible as soon as its underlying map of sheaves of abelian groups
is. -/
theorem isIso_sheafification_map_of_isLocallyBijective {M N : PresheafOfModules.{v} R₀}
    (u : M ⟶ N)
    (hinj : Presheaf.IsLocallyInjective J ((toPresheaf.{v} R₀).map u))
    (hsurj : Presheaf.IsLocallySurjective J ((toPresheaf.{v} R₀).map u)) :
    IsIso ((sheafification.{v} α).map u) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective ((toPresheaf.{v} R₀).map u))

variable [HasSheafify J AddCommGrpCat.{v}]

/-- **Sheafification carries a map of complexes of presheaves of modules whose homology
presheaves are locally bijective to a quasi-isomorphism.**

Sheafification preserves homology, so the conclusion is that it inverts each map of homology
presheaves, which is `PresheafOfModules.isIso_sheafification_map_of_isLocallyBijective`. Unlike
`PresheafOfModules.quasiIso_sheafification_map_of_exists_mem_sieve` the covering sieves are
allowed to depend on the sections, which is what a presheaf given as a colimit over an index
varying with the object forces. -/
theorem quasiIso_sheafification_map_of_isLocallyBijective {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (PresheafOfModules.{v} R₀) cs} (φ : K ⟶ L)
    (hinj : ∀ n : ι, Presheaf.IsLocallyInjective J
      ((toPresheaf.{v} R₀).map (HomologicalComplex.homologyMap φ n)))
    (hsurj : ∀ n : ι, Presheaf.IsLocallySurjective J
      ((toPresheaf.{v} R₀).map (HomologicalComplex.homologyMap φ n))) :
    QuasiIso (((sheafification.{v} α).mapHomologicalComplex cs).map φ) := by
  rw [quasiIso_iff]
  intro n
  rw [HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap]
  exact isIso_sheafification_map_of_isLocallyBijective α _ (hinj n) (hsurj n)

end PresheafOfModules

end
