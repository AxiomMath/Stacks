module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# Exactness of a complex of sheaves of modules is local on a covering family

Let `R` be a sheaf of rings on a site `(C, J)`. A short complex of sheaves of `R`-modules is
exact as soon as it is *locally* exact: every section of the middle term annihilated by the
second map is, after restriction along the arrows of some covering sieve, in the image of the
first map. In particular, if a family of objects covers the terminal object, it is enough to
know that the complex of sections is exact over every object admitting a morphism to a member
of the family.

For `C` the lattice of open sets of a topological space this reads: *a complex of sheaves of
modules which is exact on sections over the open sets contained in the members of an open
cover is exact.*

## Main results

* `exact_of_locallyExact`: the local criterion, over an arbitrary site.
* `exact_of_coversTop`: the criterion for a family of objects covering the terminal object
  (`CategoryTheory.GrothendieckTopology.CoversTop`).
* `exactAt_of_coversTop` and `exactAt_of_coversTop'`: the same for one degree of a
  homological complex, the primed version taking the neighbouring indices as data.
* `exact_of_isOpenCover`, `exactAt_of_isOpenCover` and `acyclic_of_isOpenCover`: the
  specialisations to an open cover of a topological space.

## Implementation notes

Exactness is read off the kernel of the second map: by
`CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift`, a short complex in an abelian
category is exact exactly when the canonical map from the first term to that kernel is an
epimorphism. Epimorphisms of sheaves of modules are the locally surjective morphisms, and the
covering sieve witnessing local surjectivity at a section of the kernel is the one the
hypothesis provides for the image of that section in the middle term. Nothing here uses
sheafification directly and no stalks are taken, so the criterion holds over an arbitrary
site and not only over a topological space; the topological statements are specialisations
through `TopologicalSpace.Opens.coversTop_iff`.

Two facts make the section-level bookkeeping work. Sections of the kernel inject into sections
of the middle term, because `SheafOfModules.forget` preserves finite limits and hence
monomorphisms, and a monomorphism of presheaves of modules is injective on sections
(`PresheafOfModules.injective_of_mono`). And membership of an arrow in
`CategoryTheory.Sieve.ofObjects` is literally the datum of a morphism to a member of the
covering family, which is exactly what the hypothesis consumes — so the covering sieve of the
local criterion can be taken to be the sieve of the family itself, with no bind and no
transitivity step.

`epi_of_isLocallySurjective` restates
`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective` with the universe of the modules
independent of the universe of the rings. The library version is stated only for
`SheafOfModules.{u} R` with `R : Sheaf J RingCat.{u}`, and nothing in its three-line proof
needs the two universes to agree; the statement that wants this criterion
(`Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`) has `R : Sheaf _ RingCat.{v}` and
  modules in
`max u v w t`, so the equal-universe form does not apply to it. Once the library lemma is
relaxed, the restatement here can be deleted.

No `@[stacks]` tag is attached. This is infrastructure: it is one of the inputs still owed to
the `quasiIso` field of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`, whose
  single unlabelled label covers
all nine field obligations of that structure, three of which remain open, so nothing proved
here earns that statement's tag.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe w v u u'

namespace Stacks.SheafOfModules.ComplexLocality

section Site

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Applying a composite of morphisms of sheaves of modules to a section is applying the two
factors in turn. -/
lemma comp_val_app_apply {M N P : SheafOfModules.{w} R} (φ : M ⟶ N) (ψ : N ⟶ P) (V : Cᵒᵖ)
    (x : ToType (M.val.obj V)) :
    ψ.val.app V (φ.val.app V x) = (φ ≫ ψ).val.app V x := rfl

/-- Sections of the kernel of a morphism of sheaves of modules inject into sections of the
source. -/
lemma injective_kernel_ι_app {M N : SheafOfModules.{w} R} (φ : M ⟶ N) (V : Cᵒᵖ) :
    Function.Injective ((kernel.ι φ).val.app V) := by
  have : Mono (kernel.ι φ).val := (SheafOfModules.forget R).map_mono (kernel.ι φ)
  exact PresheafOfModules.injective_of_mono (kernel.ι φ).val V

/-- A section of the kernel of a morphism of sheaves of modules is annihilated by that
morphism. -/
lemma app_kernel_ι_app {M N : SheafOfModules.{w} R} (φ : M ⟶ N) (V : Cᵒᵖ)
    (y : ToType ((kernel φ).val.obj V)) :
    φ.val.app V ((kernel.ι φ).val.app V y) = 0 := by
  have h0 : (0 : kernel φ ⟶ N).val.app V = 0 := rfl
  rw [comp_val_app_apply, kernel.condition, h0]
  simp

/-- A morphism of sheaves of modules whose underlying morphism of presheaves of abelian groups
is locally surjective is an epimorphism. This is
`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective` with the universe of the modules
independent of the universe of the rings. -/
theorem epi_of_isLocallySurjective {M N : SheafOfModules.{w} R}
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] (φ : M ⟶ N)
    (hφ : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map φ.val)) :
    Epi φ := by
  have h1 : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map φ) := hφ
  have h2 : Epi ((SheafOfModules.toSheaf R).map φ) := Sheaf.epi_of_isLocallySurjective _
  exact (SheafOfModules.toSheaf R).epi_of_epi_map h2

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Exactness of a short complex of sheaves of modules is a local condition.** If every
section of the middle term killed by the second map becomes, along the arrows of some covering
sieve, a section in the image of the first map, then the complex is exact. -/
theorem exact_of_locallyExact (S : ShortComplex (SheafOfModules.{w} R))
    (h : ∀ ⦃V : C⦄ (z : ToType (S.X₂.val.obj (op V))), S.g.val.app (op V) z = 0 →
      ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (p : W ⟶ V), T p →
        ∃ x : ToType (S.X₁.val.obj (op W)),
          S.f.val.app (op W) x = S.X₂.val.map p.op z) :
    S.Exact := by
  rw [S.exact_iff_epi_kernel_lift]
  refine epi_of_isLocallySurjective (kernel.lift S.g S.f S.zero) ⟨fun {V} y => ?_⟩
  have key : ∀ (w : ToType ((kernel S.g).val.obj (op V))),
      Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map
        (kernel.lift S.g S.f S.zero).val) w ∈ J V := by
    intro w
    obtain ⟨T, hT, hlift⟩ :=
      h ((kernel.ι S.g).val.app (op V) w) (app_kernel_ι_app S.g (op V) w)
    refine J.superset_covering (fun W p hp => ?_) hT
    obtain ⟨x, hx⟩ := hlift p hp
    have hgoal : (kernel.lift S.g S.f S.zero).val.app (op W) x
        = (kernel S.g).val.map p.op w := by
      refine injective_kernel_ι_app S.g (op W) ?_
      rw [comp_val_app_apply, kernel.lift_ι, hx,
        PresheafOfModules.naturality_apply (kernel.ι S.g).val p.op w]
    exact ⟨x, hgoal⟩
  exact key y

/-- **A short complex of sheaves of modules exact on a covering family is exact.** If `Y` is a
family of objects covering the terminal object of the site, and the complex of sections is
exact over every object admitting a morphism to a member of `Y`, then the complex of sheaves
is exact. -/
theorem exact_of_coversTop {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (S : ShortComplex (SheafOfModules.{w} R))
    (h : ∀ (i : I) ⦃W : C⦄ (_ : W ⟶ Y i) (z : ToType (S.X₂.val.obj (op W))),
      S.g.val.app (op W) z = 0 →
      ∃ x : ToType (S.X₁.val.obj (op W)), S.f.val.app (op W) x = z) :
    S.Exact := by
  refine exact_of_locallyExact S fun {V} z hz => ⟨Sieve.ofObjects Y V, hY V, ?_⟩
  rintro W p ⟨i, ⟨q⟩⟩
  refine h i q (S.X₂.val.map p.op z) ?_
  rw [PresheafOfModules.naturality_apply S.g.val p.op z, hz]
  exact map_zero _

/-- A homological complex of sheaves of modules which is exact on sections over a covering
family is exact in the corresponding degree, with the neighbouring indices given as data. -/
theorem exactAt_of_coversTop' {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex (SheafOfModules.{w} R) c) {i j k : κ}
    (hi : c.prev j = i) (hk : c.next j = k)
    {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (h : ∀ (l : I) ⦃W : C⦄ (_ : W ⟶ Y l) (z : ToType ((K.X j).val.obj (op W))),
      (K.d j k).val.app (op W) z = 0 →
      ∃ x : ToType ((K.X i).val.obj (op W)), (K.d i j).val.app (op W) x = z) :
    K.ExactAt j := by
  rw [K.exactAt_iff' i j k hi hk]
  exact exact_of_coversTop hY _ h

/-- A homological complex of sheaves of modules which is exact on sections over a covering
family is exact in that degree. -/
theorem exactAt_of_coversTop {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex (SheafOfModules.{w} R) c) (j : κ)
    {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (h : ∀ (l : I) ⦃W : C⦄ (_ : W ⟶ Y l) (z : ToType ((K.X j).val.obj (op W))),
      (K.d j (c.next j)).val.app (op W) z = 0 →
      ∃ x : ToType ((K.X (c.prev j)).val.obj (op W)),
        (K.d (c.prev j) j).val.app (op W) x = z) :
    K.ExactAt j :=
  exactAt_of_coversTop' K rfl rfl hY h

end Site

section Space

variable {X : TopCat.{u'}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A short complex of sheaves of modules exact on an open cover is exact.** If the open sets
`U i` cover `X` and the complex of sections is exact over every open set contained in some
`U i`, then the complex of sheaves of modules is exact. -/
theorem exact_of_isOpenCover {ι : Type*} (U : ι → Opens X) (hU : IsOpenCover U)
    (S : ShortComplex (SheafOfModules.{w} R))
    (h : ∀ (i : ι) ⦃W : Opens X⦄ (_ : W ≤ U i) (z : ToType (S.X₂.val.obj (op W))),
      S.g.val.app (op W) z = 0 →
      ∃ x : ToType (S.X₁.val.obj (op W)), S.f.val.app (op W) x = z) :
    S.Exact :=
  exact_of_coversTop ((Opens.coversTop_iff _ U).2 hU) S
    fun i _ q z hz => h i (leOfHom q) z hz

/-- A homological complex of sheaves of modules which is exact on sections over the open sets
contained in the members of an open cover is exact in that degree. -/
theorem exactAt_of_isOpenCover {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex (SheafOfModules.{w} R) c) (j : κ)
    {ι : Type*} (U : ι → Opens X) (hU : IsOpenCover U)
    (h : ∀ (i : ι) ⦃W : Opens X⦄ (_ : W ≤ U i) (z : ToType ((K.X j).val.obj (op W))),
      (K.d j (c.next j)).val.app (op W) z = 0 →
      ∃ x : ToType ((K.X (c.prev j)).val.obj (op W)),
        (K.d (c.prev j) j).val.app (op W) x = z) :
    K.ExactAt j :=
  exactAt_of_coversTop K j ((Opens.coversTop_iff _ U).2 hU)
    fun i _ q z hz => h i (leOfHom q) z hz

/-- A homological complex of sheaves of modules which is exact on sections over the open sets
contained in the members of an open cover is acyclic. -/
theorem acyclic_of_isOpenCover {κ : Type*} {c : ComplexShape κ}
    (K : HomologicalComplex (SheafOfModules.{w} R) c)
    {ι : Type*} (U : ι → Opens X) (hU : IsOpenCover U)
    (h : ∀ (j : κ) (i : ι) ⦃W : Opens X⦄ (_ : W ≤ U i) (z : ToType ((K.X j).val.obj (op W))),
      (K.d j (c.next j)).val.app (op W) z = 0 →
      ∃ x : ToType ((K.X (c.prev j)).val.obj (op W)),
        (K.d (c.prev j) j).val.app (op W) x = z) :
    K.Acyclic :=
  fun j => exactAt_of_isOpenCover K j U hU (h j)

end Space

end Stacks.SheafOfModules.ComplexLocality
