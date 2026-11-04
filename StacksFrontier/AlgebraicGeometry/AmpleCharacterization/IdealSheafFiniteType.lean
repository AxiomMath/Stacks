module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ComplementIdeal
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# Finite generation of an ideal sheaf, and what a quotient of a direct sum gives on stalks

`AlgebraicGeometry.Scheme.IdealSheafData` presents a quasi-coherent sheaf of ideals by its ideal
on every affine open, so "finitely generated" for it is the affine-local statement that each of
those ideals is finitely generated — which is the form [Stacks, Tag 01PG] is available in
(`Stacks.IdealSheaf.exists_fg_le_of_mem`, `Stacks.IdealSheaf.le_iSup_fg`). The clauses (7), (8)
and (9) of [Stacks, Tag 01Q3] instead quantify over modules carrying
`SheafOfModules.IsFiniteType`. This file converts the first into the second, and provides the two
further facts a consumer of clause (8) or (9) needs in order to use the epimorphism those clauses
produce: an epimorphism of `𝒪_X`-modules is surjective on stalks, and a section of a finite
direct sum is the sum of its components.

## Main definitions

* `Stacks.IdealSheafModules.sectionsMap`: the inclusion of the ideal sheaf into the structure
  sheaf, on the sections over an open set, as a `Γ(X, V)`-linear map.

## Main results

* `Stacks.IdealSheafModules.range_sectionsMap`: **over an affine open the sections of the ideal
  sheaf are the ideal**, as a submodule of `Γ(X, V)`.
* `Stacks.IdealSheafModules.moduleFinite_sections`: the sections of the ideal sheaf over an
  affine open on which the ideal is finitely generated form a finite module.
* `Stacks.IdealSheafModules.isFiniteType_sheaf`: **an ideal sheaf finitely generated on every
  affine open is of finite type**, the conversion the clauses of [Stacks, Tag 01Q3] need.
* `Stacks.ModuleStalk.surjective_mapFun_of_epi`: **an epimorphism of `𝒪_X`-modules is surjective
  on every stalk.**
* `Stacks.ModuleBicone.eq_sum_app`: **a section of a finite direct sum is the sum of its
  components**, and `Stacks.ModuleBicone.exists_germ_sum_of_epi`: **a germ in the target of an
  epimorphism from a finite direct sum is a sum of germs pushed forward from the summands.**

## Implementation notes

**Finite type is read off the sections, not from generators.** The criterion used is
`Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections`, the
implication (4) ⇒ (2) of [Stacks, Tag 01XZ] for a quasi-coherent module: it suffices that the
sections over every affine open form a finite module. For the ideal sheaf those sections are the
ideal itself, by the section-level dictionary
`Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection`, so finite generation of the ideal is
exactly what is wanted and no local generating family has to be built.

**The two spellings of an epimorphism.** `AlgebraicGeometry.Scheme.Modules` copies the category
instance of `SheafOfModules X.ringCatSheaf` without being syntactically equal to it, so the two
`Epi` propositions differ and the one wanted is transported across by the cancellation property,
exactly as `Stacks.SheafOfModules.StalkEpiMono` records.

**Why the direct sum is decomposed on sections and not on stalks.** `Stacks.ModuleStalk.mapFun`
is additive in its *argument*, not visibly in its morphism, so the identity
`∑ i, b.π i ≫ b.ι i = 𝟙` of `CategoryTheory.Limits.IsBilimit.total` is applied where
`AlgebraicGeometry.Scheme.Modules.Hom.add_app` makes additivity in the morphism a definitional
statement: on sections. A germ of the resulting decomposition is then taken by `map_sum`, which
is all a stalk argument needs.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.IdealSheafModules

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The sections of an ideal sheaf over an affine open -/

/-- The inclusion of the ideal sheaf into the structure sheaf, on the sections over an open set,
as a `Γ(X, V)`-linear map. -/
def sectionsMap (V : X.Opens) : Γ(sheaf I, V) →ₗ[Γ(X, V)] Γ(X, V) where
  toFun s := (ι I).app V s
  map_add' s t := map_add ((ι I).app V).hom s t
  map_smul' c s := Scheme.Modules.Hom.app_smul (ι I) c s

/-- The map `sectionsMap I V` sends a section `s` to its image under the inclusion `ι I`. -/
@[simp] theorem sectionsMap_apply (V : X.Opens) (s : Γ(sheaf I, V)) :
    sectionsMap I V s = (ι I).app V s :=
  rfl

/-- The inclusion of the ideal sheaf is injective on sections. -/
theorem injective_sectionsMap (V : X.Opens) : Function.Injective (sectionsMap I V) :=
  Stacks.Divisors.idealSheafSection_injective I

/-- **Over an affine open the sections of the ideal sheaf are the ideal.** -/
theorem range_sectionsMap (V : X.affineOpens) :
    LinearMap.range (sectionsMap I (V : X.Opens)) = I.ideal V := by
  ext r
  rw [LinearMap.mem_range]
  exact (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection I V r).symm

/-- **The sections of a finitely generated ideal sheaf over an affine open form a finite
module.** They are the ideal, by `Stacks.IdealSheafModules.range_sectionsMap`, and the inclusion
is injective. -/
theorem moduleFinite_sections (V : X.affineOpens) (hfg : (I.ideal V).FG) :
    Module.Finite Γ(X, (V : X.Opens)) Γ(sheaf I, (V : X.Opens)) := by
  have : Module.Finite Γ(X, (V : X.Opens))
      (LinearMap.range (sectionsMap I (V : X.Opens))) :=
    Module.Finite.iff_fg.mpr (by rwa [range_sectionsMap])
  exact Module.Finite.equiv
    (LinearEquiv.ofInjective _ (injective_sectionsMap I (V : X.Opens))).symm

/-- **An ideal sheaf finitely generated on every affine open is of finite type.** This is the
conversion the clauses of [Stacks, Tag 01Q3] that quantify over finite-type sheaves of ideals
need in order to be applied to the subsheaves [Stacks, Tag 01PG] produces, which are finitely
generated affine-locally. -/
theorem isFiniteType_sheaf (hfg : ∀ V : X.affineOpens, (I.ideal V).FG) :
    SheafOfModules.IsFiniteType.{u, u, u} (sheaf I) :=
  Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections
    (sheaf I) fun V => moduleFinite_sections I V (hfg V)

end Stacks.IdealSheafModules

namespace Stacks.ModuleStalk

/-- **An epimorphism of `𝒪_X`-modules is surjective on every stalk.** This is
`Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi` in the
`AlgebraicGeometry.Scheme.Modules` spelling, the epimorphism transported across the two category
instances by the cancellation property. -/
theorem surjective_mapFun_of_epi {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N) (hp : Epi p)
    (x : X) : Function.Surjective (Stacks.ModuleStalk.mapFun p x) := by
  have key : ∀ {A B : SheafOfModules.{u} X.ringCatSheaf} (q : A ⟶ B), Epi q →
      ∀ m : TopCat.Presheaf.stalk (C := Ab.{u}) B.val.presheaf x,
        ∃ v, Stacks.SheafOfModules.StalkEpiMono.stalkMap q x v = m := by
    intro A B q hq m
    exact Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi q x m
  exact fun m => key (A := M) (B := N) p ⟨fun g₁ g₂ hg => hp.left_cancellation g₁ g₂ hg⟩ m

end Stacks.ModuleStalk

namespace Stacks.ModuleBicone

/-- **A section of a finite direct sum of `𝒪_X`-modules is the sum of its components.** This is
the identity `∑ i, b.π i ≫ b.ι i = 𝟙 b.pt` of `CategoryTheory.Limits.IsBilimit.total`
evaluated on sections, where additivity in the morphism is definitional. -/
theorem eq_sum_app {X : Scheme.{u}} {ι : Type*} [Fintype ι] {f : ι → X.Modules}
    {b : Bicone f} (hb : b.IsBilimit) (W : X.Opens) (s : Γ(b.pt, W)) :
    s = ∑ i, (b.ι i).app W ((b.π i).app W s) := by
  classical
  let ev : (b.pt ⟶ b.pt) →+ Γ(b.pt, W) :=
    { toFun := fun φ => φ.app W s
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h : ev (∑ i : ι, b.π i ≫ b.ι i) = ∑ i : ι, ev (b.π i ≫ b.ι i) :=
    map_sum ev _ Finset.univ
  rwa [IsBilimit.total hb] at h

/-- **A germ in the target of an epimorphism from a finite direct sum is the sum of germs pushed
forward from the summands.** This is what a consumer of clause (8) or (9) of [Stacks, Tag 01Q3]
gets out of the epimorphism those clauses produce: the germ it is interested in is accounted for
by finitely many morphisms out of the single module `L ^⊗ (-n)`. -/
theorem exists_germ_sum_of_epi {X : Scheme.{u}} {ι : Type*} [Fintype ι] {f : ι → X.Modules}
    {b : Bicone f} (hb : b.IsBilimit) {N : X.Modules} (p : b.pt ⟶ N) (hp : Epi p) (x : X)
    (g : TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x) :
    ∃ v : ∀ i, TopCat.Presheaf.stalk (C := Ab.{u}) (f i).presheaf x,
      g = ∑ i, Stacks.ModuleStalk.mapFun (b.ι i ≫ p) x (v i) := by
  classical
  obtain ⟨w, hw⟩ := Stacks.ModuleStalk.surjective_mapFun_of_epi p hp x g
  obtain ⟨W, hxW, s, hs⟩ := TopCat.Presheaf.exists_germ_eq b.pt.presheaf w
  refine ⟨fun i => ((f i).presheaf.germ W x hxW).hom ((b.π i).app W s), ?_⟩
  have h1 : p.app W s = ∑ i : ι, (b.ι i ≫ p).app W ((b.π i).app W s) := by
    conv_lhs => rw [eq_sum_app hb W s]
    exact map_sum (p.app W).hom _ _
  calc g = Stacks.ModuleStalk.mapFun p x ((b.pt.presheaf.germ W x hxW).hom s) := by rw [hs, hw]
    _ = (N.presheaf.germ W x hxW).hom (p.app W s) := Stacks.ModuleStalk.mapFun_germ p x W hxW s
    _ = (N.presheaf.germ W x hxW).hom
          (∑ i : ι, (b.ι i ≫ p).app W ((b.π i).app W s)) := by rw [h1]
    _ = ∑ i : ι, (N.presheaf.germ W x hxW).hom ((b.ι i ≫ p).app W ((b.π i).app W s)) :=
        map_sum _ _ _
    _ = ∑ i : ι, Stacks.ModuleStalk.mapFun (b.ι i ≫ p) x
          (((f i).presheaf.germ W x hxW).hom ((b.π i).app W s)) :=
        Finset.sum_congr rfl fun i _ => (Stacks.ModuleStalk.mapFun_germ _ x W hxW _).symm

end Stacks.ModuleBicone

end
