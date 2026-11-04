module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CechAmitsur
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FiniteDisjointSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.SheafBaseChange

/-!
# Sections of the presheaf cokernel of a presentation

A global presentation of a sheaf of modules exhibits it as the cokernel, *in sheaves of modules*,
of a map `a` between two coproducts of copies of the structure sheaf.  That cokernel is a
sheafification, so none of its sections is computable from the presentation.  The cokernel of the
same map taken *in presheaves of modules* has, by construction, the sections
`coker (a.val.app X)` at every object, and this file computes those sections.

The reason this is the useful object is that a presheaf cokernel is a presheaf while its two
*sources* are sheaves.  Every tool applies to the sources — the sections of a coproduct of copies
of the structure sheaf over an object with the finite subcovering property
(`SheafOfModules.tautBasis`), the sheaf condition for a family of disjoint subobjects
(`SheafOfModules.surjective_restrict`) — and no sheaf property of the cokernel is used before it
is proved.  The three computations below are, in that order:

*Base change.*  Over a morphism `h : W ⟶ T` between two objects with the finite subcovering
property the sections of the presheaf cokernel over `W` are the base change of its sections over
`T` along the corresponding map of rings.  This is
`SheafOfModules.exists_baseChangeEquiv_of_presentation` with its four exactness hypotheses
discharged: that the presenting map is surjective on sections over either object, kills the
composite with the relation map, and has for kernel the values of the relation map, is exactly
what being a presheaf cokernel says.  No flatness and no cohomology are involved; what the two
objects must be is the two objects over which the tautological generators are a basis.

*Finite disjoint unions.*  Restriction to the members of a covering family of pairwise disjoint
subobjects is bijective on the sections of the presheaf cokernel.  Both halves are the
corresponding statement for the two *sheaves* of the presentation plus the cokernel property:
surjectivity lifts a family of sections through the presenting map, glues the lifts on the
sources, and pushes the result forward; injectivity corrects a lift whose restrictions are values
of the relation map by a section of the relation sheaf glued from those values.

*The sheaf condition for a single covering morphism.*  Given the base-change comparison over `W`
and an injection of the degree-one term of the Amitsur complex into the sections over a double
self-product, degree-zero exactness of that complex
(`PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero`) makes a compatible section over
`W` the restriction of a section over `T`, and faithful flatness makes that section unique.  Both
halves together are `CategoryTheory.Presieve.IsSheafFor` for the one-element covering.

## Main definitions

* `PresheafOfModules.IsPresheafCokernel`: a morphism of presheaves of modules is surjective on the
  sections over every object and has for kernel there the values of a given morphism.

## Main results

* `PresheafOfModules.isPresheafCokernel_cokernelπ`: **the cokernel of a morphism of presheaves of
  modules is a presheaf cokernel**, that is, it is computed object by object.
* `SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel`: **the sections of the presheaf
  cokernel of a presentation over a covering object are the base change of its sections over the
  base**, with no exactness hypothesis.
* `SheafOfModules.eq_zero_of_restrict_eq_zero_of_isPresheafCokernel` and
  `SheafOfModules.bijective_restrict_of_isPresheafCokernel`: **restriction to the members of a
  covering family of pairwise disjoint subobjects is bijective on the sections of the presheaf
  cokernel of a presentation.**
* `PresheafOfModules.injective_restrictₛₗ_of_bijective_baseChange`: restriction along a
  faithfully flat covering morphism is injective on sections once the sections over the covering
  object are a base change.
* `PresheafOfModules.isSheafFor_ofArrows_of_cechDiff₀`: **the sheaf condition for a one-element
  covering**, from the base-change comparison and degree-zero exactness of the Amitsur complex.

## Implementation notes

`PresheafOfModules.IsPresheafCokernel` is a property of a morphism the caller already has, not a
construction: a caller may use the categorical cokernel, for which
`PresheafOfModules.isPresheafCokernel_cokernelπ` supplies the property, or any pointwise quotient
it finds more convenient.  The property is stated with `Function.Exact`, from which the two
inclusions are read off by `PresheafOfModules.IsPresheafCokernel.app_app_eq_zero` and
`PresheafOfModules.IsPresheafCokernel.mem_range_of_app_eq_zero`.

The commutative rings, the module structures on the sections and the readings of the morphisms of
the presentation as maps of those modules are taken as explicit data, as in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.SheafBaseChange`: a
`SheafOfModules.{m} R` has `R : Sheaf J RingCat`, so its sections carry a ring and nothing more,
while a base change needs a commutative ring and an algebra, and on a big site of schemes those
are present only through `CategoryTheory.forget₂ CommRingCat RingCat`, which instance search does
not unfold.

The last two results need no topology and no sheaf among their data, so they are stated for a
presheaf of rings rather than for a sheaf of rings.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w u v r m t

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{r}}

/-- A morphism `π : N ⟶ Q` of presheaves of modules is a *presheaf cokernel* of `f : M ⟶ N` when
over every object it is surjective and its kernel is the set of values of `f`.  Equivalently, `Q`
is the cokernel of `f` computed object by object, with no sheafification.

This is weaker than being the cokernel of `f` in a category of *sheaves* of modules, and it is
the property under which the sections of a presentation are computable: exactness of the sections
of the presentation is part of the definition rather than something to be proved. -/
structure IsPresheafCokernel {M N Q : PresheafOfModules.{m} R} (f : M ⟶ N) (π : N ⟶ Q) :
    Prop where
  /-- `π` is surjective on the sections over every object. -/
  surjective (X : Cᵒᵖ) : Function.Surjective (π.app X)
  /-- The kernel of `π` over an object is the set of values of `f` there. -/
  exact (X : Cᵒᵖ) : Function.Exact (f.app X).hom (π.app X).hom

namespace IsPresheafCokernel

variable {M N Q : PresheafOfModules.{m} R} {f : M ⟶ N} {π : N ⟶ Q}

/-- A presheaf cokernel of `f` kills the values of `f`. -/
lemma app_app_eq_zero (hπ : IsPresheafCokernel f π) (X : Cᵒᵖ) (x : M.obj X) :
    π.app X (f.app X x) = 0 :=
  (hπ.exact X).apply_apply_eq_zero x

/-- A section killed by a presheaf cokernel of `f` is a value of `f`. -/
lemma mem_range_of_app_eq_zero (hπ : IsPresheafCokernel f π) (X : Cᵒᵖ) {y : N.obj X}
    (hy : π.app X y = 0) : y ∈ LinearMap.range (f.app X).hom :=
  (hπ.exact X y).1 hy

end IsPresheafCokernel

/-- **The cokernel of a morphism of presheaves of modules is computed object by object.**
Evaluation at an object preserves finite colimits, so it carries the cokernel cofork to a
cokernel cofork of modules; the projection onto a cokernel of modules is surjective with kernel
the range of the map. -/
theorem isPresheafCokernel_cokernelπ {M N : PresheafOfModules.{m} R} (f : M ⟶ N) :
    IsPresheafCokernel f (cokernel.π f) := by
  refine ⟨fun X => surjective_of_epi _ X, fun X => ?_⟩
  have hc := CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) (evaluation.{m} R X)
  have hz : (evaluation.{m} R X).map f ≫ (evaluation.{m} R X).map (cokernel.π f) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have hex := (ShortComplex.mk _ _ hz).exact_of_g_is_cokernel hc
  rw [ShortComplex.moduleCat_exact_iff] at hex
  intro y
  refine ⟨fun hy => hex y hy, ?_⟩
  rintro ⟨x, hx⟩
  rw [← hx]
  exact congr($hz x)

section SingleCovering

open Module.Descent

variable {N : PresheafOfModules.{m} R} {T W V : C} (h : W ⟶ T)
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
  [Module A (N.obj (op T))]
  (eW : B ⊗[A] N.obj (op T) →+ N.obj (op W)) (heW : Function.Bijective eW)
  (heWone : ∀ n, eW ((1 : B) ⊗ₜ[A] n) = N.restrictₛₗ h.op n)

include heW heWone in
/-- **Restriction along a faithfully flat covering morphism is injective on sections**, as soon as
the sections over the covering object are identified with a base change of the sections over the
base in such a way that restriction is the augmentation.  This is the separatedness half of the
sheaf condition for a one-element covering, and it uses of faithful flatness only that
`m ↦ 1 ⊗ₜ m` is injective. -/
theorem injective_restrictₛₗ_of_bijective_baseChange :
    Function.Injective (N.restrictₛₗ h.op) := by
  intro n n' hnn'
  have h1 : (1 : B) ⊗ₜ[A] (n - n') = 0 := by
    rw [TensorProduct.tmul_sub, sub_eq_zero]
    exact heW.1 ((heWone n).trans (hnn'.trans (heWone n').symm))
  exact sub_eq_zero.1
    ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (A := B) A _ (n - n')).1 h1)

include heW heWone in
/-- **The sheaf condition for a one-element covering of a presheaf of modules**, from the
base-change comparison over the covering object and degree-zero exactness of the Amitsur complex.

A compatible family for the one-element covering `{h}` is a single section over `W` which the two
projections of a double self-product agree on, hence one killed by the degree-zero Čech
differential; `PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero` makes it the
restriction of a section over `T`, and
`PresheafOfModules.injective_restrictₛₗ_of_bijective_baseChange` makes that section unique.  The
two hypotheses left open are the ones that describe the double self-product: an injection of the
degree-one term of the Amitsur complex into the sections there, and the identification of the
degree-zero Čech differential with the degree-zero Amitsur differential, for which
`PresheafOfModules.cechDiff₀_eq_amitsurDiff₀` reduces the work to one description per
projection. -/
theorem isSheafFor_ofArrows_of_cechDiff₀ (q₁ q₂ : V ⟶ W) (hq : q₁ ≫ h = q₂ ≫ h)
    (eV : B ⊗[A] (B ⊗[A] N.obj (op T)) →+ N.obj (op V)) (heV : Function.Injective eV)
    (hd₀ : ∀ x, N.cechDiff₀ q₁ q₂ (eW x) = eV (amitsurDiff₀ A B (N.obj (op T)) x)) :
    Presieve.IsSheafFor (N.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
      (Presieve.ofArrows (fun _ : Unit => W) fun _ => h) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hcomp : N.cechDiff₀ q₁ q₂ (show N.obj (op W) from x ()) = 0 := by
    rw [cechDiff₀_apply, sub_eq_zero]
    exact hx () () V q₁ q₂ hq
  obtain ⟨n, hn⟩ := N.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero A B (N.obj (op T)) h q₁ q₂
    (AddMonoidHom.id _) eW eV heW.2 heV (fun m => (heWone m).symm) hd₀ hcomp
  refine ⟨n, fun _ => hn, fun n' hn' => ?_⟩
  exact injective_restrictₛₗ_of_bijective_baseChange h A B eW heW heWone
    ((hn' ()).trans hn.symm)

end SingleCovering

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- A morphism of presheaves of modules commutes with restriction. -/
private theorem app_restrictₛₗ {M N : PresheafOfModules.{m} R.obj} (f : M ⟶ N) {X Y : Cᵒᵖ}
    (g : X ⟶ Y) (x : M.obj X) : f.app Y (M.restrictₛₗ g x) = N.restrictₛₗ g (f.app X x) :=
  PresheafOfModules.naturality_apply f g x

section Presentation

variable {T W : C} {K I : Type w} {Q P : SheafOfModules.{max t r} R}
  {N : PresheafOfModules.{max t r} R.obj}
  (κ : ∀ _ : K, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ Q)
  (ι : ∀ _ : I, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ P)
  (h : W ⟶ T) (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module A (Q.val.obj (op T))] [Module A (P.val.obj (op T))] [Module A (N.obj (op T))]
  [Module A (Q.val.obj (op W))] [Module B (Q.val.obj (op W))]
  [IsScalarTower A B (Q.val.obj (op W))]
  [Module A (P.val.obj (op W))] [Module B (P.val.obj (op W))]
  [IsScalarTower A B (P.val.obj (op W))]
  [Module A (N.obj (op W))] [Module B (N.obj (op W))]
  [IsScalarTower A B (N.obj (op W))]
  (basQT : Module.Basis K A (Q.val.obj (op T))) (basQW : Module.Basis K B (Q.val.obj (op W)))
  (basPT : Module.Basis I A (P.val.obj (op T))) (basPW : Module.Basis I B (P.val.obj (op W)))
  (hbasQT : ∀ k, basQT k = tautGen κ k (op T)) (hbasQW : ∀ k, basQW k = tautGen κ k (op W))
  (hbasPT : ∀ i, basPT i = tautGen ι i (op T)) (hbasPW : ∀ i, basPW i = tautGen ι i (op W))
  (rQ : Q.val.obj (op T) →ₗ[A] Q.val.obj (op W))
  (hrQ : ∀ x, rQ x = Q.val.restrictₛₗ h.op x)
  (rP : P.val.obj (op T) →ₗ[A] P.val.obj (op W))
  (hrP : ∀ x, rP x = P.val.restrictₛₗ h.op x)
  (rN : N.obj (op T) →ₗ[A] N.obj (op W))
  (hrN : ∀ x, rN x = N.restrictₛₗ h.op x)

include hbasQT hbasQW hbasPT hbasPW hrQ hrP hrN in
/-- **The sections of the presheaf cokernel of a presentation over a covering object are the base
change of its sections over the base.**  This is
`SheafOfModules.exists_baseChangeEquiv_of_exact_sections` for the presheaf cokernel, where the
four exactness conditions on the sections of the presentation are not hypotheses: they are what
`PresheafOfModules.IsPresheafCokernel` says.  What remains asked for is the data identifying the
sections of the two coproducts of the presentation over the two objects with free modules, which
is `SheafOfModules.tautBasis` at an object with the finite subcovering property, and the readings
of the two morphisms and of the three restriction maps over the commutative rings the caller has
identified the rings of sections with.

No flatness of `B` over `A` is used, and nothing compares the sections of the presheaf cokernel
at two different objects: the conclusion is produced from statements about one presentation at one
object. -/
theorem exists_baseChangeEquiv_of_isPresheafCokernel (a : Q ⟶ P) (π : P.val ⟶ N)
    (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    (aT : Q.val.obj (op T) →ₗ[A] P.val.obj (op T))
    (haT : ∀ q, aT q = a.val.app (op T) q)
    (bT : P.val.obj (op T) →ₗ[A] N.obj (op T))
    (hbT : ∀ p, bT p = π.app (op T) p)
    (aW : Q.val.obj (op W) →ₗ[B] P.val.obj (op W))
    (haW : ∀ q, aW q = a.val.app (op W) q)
    (bW : P.val.obj (op W) →ₗ[B] N.obj (op W))
    (hbW : ∀ p, bW p = π.app (op W) p) :
    ∃ e : B ⊗[A] N.obj (op T) ≃ₗ[B] N.obj (op W),
      ∀ n, e ((1 : B) ⊗ₜ[A] n) = N.restrictₛₗ h.op n := by
  have hsqa : ∀ q, rP (aT q) = aW (rQ q) := fun q => by
    rw [haT, hrP, haW, hrQ, app_restrictₛₗ]
  have hsqb : ∀ p, rN (bT p) = bW (rP p) := fun p => by
    rw [hbT, hrN, hbW, hrP, app_restrictₛₗ]
  have hsurjT : Function.Surjective bT := by
    rw [show ⇑bT = π.app (op T) from funext hbT]
    exact hπ.surjective _
  have hsurjW : Function.Surjective bW := by
    rw [show ⇑bW = π.app (op W) from funext hbW]
    exact hπ.surjective _
  have hzero : ∀ q, bT (aT q) = 0 := fun q => by
    rw [hbT, haT]
    exact hπ.app_app_eq_zero (op T) q
  have hexW : ∀ p, bW p = 0 → p ∈ LinearMap.range aW := fun p hp => by
    obtain ⟨q, hq⟩ := hπ.mem_range_of_app_eq_zero (op W) (y := p) (by rw [← hbW]; exact hp)
    exact ⟨q, by rw [haW]; exact hq⟩
  exact ⟨Module.BaseChange.baseChangeEquivOfPresentation aT bT aW bW rQ rP rN hsqa hsqb
      (bijective_liftBaseChange_of_tautBasis κ h A B basQT basQW hbasQT hbasQW rQ hrQ)
      (bijective_liftBaseChange_of_tautBasis ι h A B basPT basPW hbasPT hbasPW rP hrP)
      hsurjT hsurjW hzero hexW,
    fun n => (Module.BaseChange.baseChangeEquivOfPresentation_one_tmul aT bT aW bW rQ rP rN
      hsqa hsqb _ _ hsurjT hsurjW hzero hexW n).trans (hrN n)⟩

end Presentation

section Disjoint

variable {Q P : SheafOfModules.{m} R} {N : PresheafOfModules.{m} R.obj}

/-- **A section of the presheaf cokernel of a presentation whose restrictions to the members of a
covering family of pairwise disjoint subobjects vanish is zero.**  A lift of the section through
the presenting map restricts on each member to a value of the relation map; the values glue, by
`SheafOfModules.surjective_restrict` for the relation sheaf, to one section over the base; and the
lift agrees with its image, by `SheafOfModules.injective_restrict` for the generator sheaf.  So
the lift is a value of the relation map, and the section it covers is zero. -/
theorem eq_zero_of_restrict_eq_zero_of_isPresheafCokernel (a : Q ⟶ P) (π : P.val ⟶ N)
    (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    {W : C} {I : Type w} {V : I → C} (g : ∀ i, V i ⟶ W)
    (hg : Sieve.ofArrows V g ∈ J W) (hmono : ∀ i, Mono (g i))
    (hdisj : ∀ ⦃Z : C⦄ ⦃i j : I⦄ (gi : Z ⟶ V i) (gj : Z ⟶ V j), i ≠ j →
      gi ≫ g i = gj ≫ g j → (⊥ : Sieve Z) ∈ J Z)
    {n : N.obj (op W)} (hn : ∀ i, N.restrictₛₗ (g i).op n = 0) : n = 0 := by
  obtain ⟨p, rfl⟩ := hπ.surjective (op W) n
  have hres : ∀ i, π.app (op (V i)) (P.val.restrictₛₗ (g i).op p) = 0 := fun i => by
    rw [app_restrictₛₗ]
    exact hn i
  choose q hq using fun i => hπ.mem_range_of_app_eq_zero (op (V i)) (hres i)
  obtain ⟨q₀, hq₀⟩ := Q.surjective_restrict g hg hmono hdisj q
  have key : p = a.val.app (op W) q₀ := by
    refine P.injective_restrict g hg (funext fun i => ?_)
    change P.val.restrictₛₗ (g i).op p = P.val.restrictₛₗ (g i).op (a.val.app (op W) q₀)
    rw [← app_restrictₛₗ a.val, show Q.val.restrictₛₗ (g i).op q₀ = q i from congrFun hq₀ i]
    exact (hq i).symm
  rw [key]
  exact hπ.app_app_eq_zero (op W) q₀

/-- **Restriction to the members of a covering family of pairwise disjoint subobjects is bijective
on the sections of the presheaf cokernel of a presentation.**  For the members of a finite
disjoint union and the union itself this says that the sections of the presheaf cokernel over the
union are the product of its sections over the pieces, which is the sheaf condition for that
decomposition.

Injectivity is `SheafOfModules.eq_zero_of_restrict_eq_zero_of_isPresheafCokernel`.  Surjectivity
needs only the generator sheaf: an arbitrary family of sections over the members lifts member by
member through the presenting map, the lifts glue by
`SheafOfModules.surjective_restrict`, and the image of the glued lift restricts to the given
family. -/
theorem bijective_restrict_of_isPresheafCokernel (a : Q ⟶ P) (π : P.val ⟶ N)
    (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    {W : C} {I : Type w} {V : I → C} (g : ∀ i, V i ⟶ W)
    (hg : Sieve.ofArrows V g ∈ J W) (hmono : ∀ i, Mono (g i))
    (hdisj : ∀ ⦃Z : C⦄ ⦃i j : I⦄ (gi : Z ⟶ V i) (gj : Z ⟶ V j), i ≠ j →
      gi ≫ g i = gj ≫ g j → (⊥ : Sieve Z) ∈ J Z) :
    Function.Bijective
      fun n : N.obj (op W) => fun i => N.restrictₛₗ (g i).op n := by
  refine ⟨fun n n' hnn' => ?_, fun y => ?_⟩
  · have h0 : ∀ i, N.restrictₛₗ (g i).op (n - n') = 0 := fun i => by
      have h : N.restrictₛₗ (g i).op n = N.restrictₛₗ (g i).op n' := congrFun hnn' i
      rw [map_sub, h, sub_self]
    exact sub_eq_zero.1
      (eq_zero_of_restrict_eq_zero_of_isPresheafCokernel a π hπ g hg hmono hdisj h0)
  · choose p hp using fun i => hπ.surjective (op (V i)) (y i)
    obtain ⟨p₀, hp₀⟩ := P.surjective_restrict g hg hmono hdisj p
    refine ⟨π.app (op W) p₀, funext fun i => ?_⟩
    change N.restrictₛₗ (g i).op (π.app (op W) p₀) = y i
    rw [← app_restrictₛₗ π, show P.val.restrictₛₗ (g i).op p₀ = p i from congrFun hp₀ i]
    exact hp i

end Disjoint

end SheafOfModules

end
